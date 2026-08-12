#!/usr/bin/env python3
# Requirements: pip install aiogram==3.x telethon aiosqlite pyaes
"""
╔═══════════════════════════════════════════════════════════════════════════╗
║                         AKAZA x Reffer                                     ║
║              MTProto Edition — Full Overhaul                                 ║
║  Tdata Validator | Global Pool | Auto-Referral | Admin Panel                ║
║  Multi-Session ZIP | Parallel Validation | 16-Chunk Download              ║
╚═══════════════════════════════════════════════════════════════════════════╝
"""

import os
import io
import re
import sys
import json
import time
import shutil
import asyncio
import hashlib
import struct
import zipfile
import logging
from datetime import datetime, timedelta
from urllib.parse import urlparse, parse_qs
from typing import Optional, Dict, Any, List, Tuple

import aiosqlite
from aiogram import Bot, Dispatcher, F
from aiogram.exceptions import TelegramBadRequest, TelegramNetworkError
from aiogram.types import (
    Message, CallbackQuery, InlineKeyboardMarkup,
    InlineKeyboardButton, FSInputFile
)
from aiogram.filters import Command, CommandStart
from aiogram.fsm.context import FSMContext
from aiogram.fsm.state import State, StatesGroup
from aiogram.fsm.storage.memory import MemoryStorage

from pyaes import AESModeOfOperationECB as _AES_ECB
from telethon import TelegramClient, utils as telethon_utils
from telethon.crypto import AuthKey
from telethon.sessions import MemorySession
from telethon.tl.functions.account import GetPasswordRequest
from telethon.tl.functions.channels import JoinChannelRequest
from telethon.tl.functions.messages import StartBotRequest
from telethon.tl.types import Channel, Chat

# ═══════════════════════════════════════════════════════════════════════════
# CONFIGURATION
# ═══════════════════════════════════════════════════════════════════════════
BOT_TOKEN = os.getenv("BOT_TOKEN", "YOUR_BOT_TOKEN_HERE").strip()
if BOT_TOKEN == "YOUR_BOT_TOKEN_HERE":
    logger.warning("BOT_TOKEN not set! Using placeholder.")

ADMIN_ID = int(os.getenv("ADMIN_ID", "5944410248"))

TG_API_ID    = int(os.getenv("TG_API_ID", "33462430"))
TG_API_HASH  = os.getenv("TG_API_HASH", "c55be1d2cb63e058d9c64bae4f0c4ec3").strip()

FORCE_JOIN_CHANNEL = os.getenv("FORCE_JOIN_CHANNEL", "").strip()

MTPROTO_WORKERS   = 16
MTPROTO_CHUNK_KB   = 1024
SESSION_TIMEOUT     = 15
PAGE_SIZE           = 8

DB_PATH        = "akaza_database.db"
TDATA_STORAGE  = "tdata_storage"
GLOBAL_TDATA_DIR = "global_tdata"
TEMP_DIR        = "temp_uploads"

REFERRAL_LIMITS = {"free": 5, "premium": 15, "premium_plus": 999_999}
GLOBAL_USE_LIMITS = {"free": 1, "premium": 3, "premium_plus": 999_999}

logging.basicConfig(level=logging.INFO, format="%(asctime)s | %(levelname)s | %(message)s")
logger = logging.getLogger(__name__)

# Load .env file for local development (Railway env vars override this automatically)
try:
    from dotenv import load_dotenv
    load_dotenv()
except ImportError:
    pass


# ═══════════════════════════════════════════════════════════════════════════
# SHARED MTPROTO CLIENT
# ═══════════════════════════════════════════════════════════════════════════
_mtproto_client: Optional[TelegramClient] = None


async def get_mtproto_client() -> TelegramClient:
    global _mtproto_client
    if _mtproto_client is None:
        raise RuntimeError("MTProto client not initialized. Call init_mtproto() first.")
    return _mtproto_client


async def init_mtproto():
    global _mtproto_client
    _mtproto_client = TelegramClient(
        MemorySession(), TG_API_ID, TG_API_HASH,
        timeout=60, connection_retries=3, retry_delay=1
    )
    await _mtproto_client.start(bot_token=BOT_TOKEN)
    logger.info("MTProto client connected (16 workers, %dKB chunks)", MTPROTO_CHUNK_KB)


# ═══════════════════════════════════════════════════════════════════════════
# FSM STATES
# ═══════════════════════════════════════════════════════════════════════════
class AdminState(StatesGroup):
    waiting_link_name   = State()
    waiting_link_url    = State()
    waiting_broadcast   = State()
    waiting_fwd_broadcast = State()
    waiting_ban_id      = State()
    waiting_unban_id    = State()
    waiting_settier     = State()
    waiting_global_tdata = State()
    waiting_toggle_link  = State()


class UserState(StatesGroup):
    waiting_tdata_choice     = State()
    waiting_tdata_upload     = State()
    waiting_user_link_name   = State()
    waiting_user_link_url    = State()
    waiting_referral_target  = State()


# ═══════════════════════════════════════════════════════════════════════════
# TDATA CRYPTO & PARSER
# ═══════════════════════════════════════════════════════════════════════════
_DC_IPS = {
    1: "149.154.175.53", 2: "149.154.167.51",
    3: "149.154.175.100", 4: "149.154.167.91", 5: "91.108.56.130"
}


def _aes_ige_decrypt(data, key, iv):
    aes = _AES_ECB(key)
    bs = 16
    iv1, iv2 = iv[:bs], iv[bs:]
    out = bytearray()
    for i in range(0, len(data), bs):
        block = data[i:i+bs]
        xored = bytes(a ^ b for a, b in zip(block, iv2))
        dec = aes.decrypt(xored)
        plain = bytes(a ^ b for a, b in zip(dec, iv1))
        out.extend(plain)
        iv1, iv2 = block, plain
    return bytes(out)


def _tdata_local_key(salt, passcode=b''):
    h = hashlib.sha512(salt + passcode + salt).digest()
    return hashlib.pbkdf2_hmac('sha512', h, salt, 1 if not passcode else 100000, dklen=256)


def _tdata_read_qt_bytes(s):
    l = struct.unpack('>i', s.read(4))[0]
    return b'' if l < 0 else s.read(l)


def _tdata_prepare_aes(ak, mk):
    x = 8
    a = hashlib.sha1(mk[:16]+ak[x:x+32]).digest()
    b = hashlib.sha1(ak[x+32:x+48]+mk[:16]+ak[x+48:x+64]).digest()
    c = hashlib.sha1(ak[x+64:x+96]+mk[:16]).digest()
    d = hashlib.sha1(mk[:16]+ak[x+96:x+128]).digest()
    return a[:8]+b[8:20]+c[4:16], a[8:20]+b[:8]+c[16:20]+d[:8]


def _tdata_decrypt(enc, lk):
    if len(enc) <= 16 or len(enc) % 16 != 0:
        raise ValueError("Bad size")
    mk, ed = enc[:16], enc[16:]
    k, iv = _tdata_prepare_aes(lk, mk)
    dec = _aes_ige_decrypt(ed, k, iv)
    if hashlib.sha1(dec).digest()[:16] != mk:
        raise ValueError("Bad decrypt key")
    dl = struct.unpack('<I', dec[:4])[0]
    return dec[4:4+dl]


def _tdata_read_file(fp):
    with open(fp, 'rb') as f:
        f.read(8)
        d = f.read()
        return d[:-16]


def parse_tdata_session(tdata_path: str):
    raw = _tdata_read_file(os.path.join(tdata_path, "key_datas"))
    s = io.BytesIO(raw)
    salt = _tdata_read_qt_bytes(s)
    key_enc = _tdata_read_qt_bytes(s)
    local_key = _tdata_local_key(salt)
    actual_key = _tdata_decrypt(key_enc, local_key)
    mtp_file = None
    for f in os.listdir(tdata_path):
        if f.lower().startswith("d877f783d5d3ef8c") and f.endswith("s") and not os.path.isdir(os.path.join(tdata_path, f)):
            mtp_file = os.path.join(tdata_path, f)
            break
    if not mtp_file:
        raise FileNotFoundError("MTP data file not found")
    mtp_raw = _tdata_read_file(mtp_file)
    mtp_enc = _tdata_read_qt_bytes(io.BytesIO(mtp_raw))
    mtp_dec = _tdata_decrypt(mtp_enc, actual_key)
    ms = io.BytesIO(mtp_dec)
    if struct.unpack('>i', ms.read(4))[0] != 75:
        raise ValueError("Bad block ID")
    mtp_auth = _tdata_read_qt_bytes(ms)
    ms2 = io.BytesIO(mtp_auth)
    first = struct.unpack('>i', ms2.read(4))[0]
    if first == -1:
        ms2.read(4)
        user_id = struct.unpack('>q', ms2.read(8))[0]
        main_dc = struct.unpack('>i', ms2.read(4))[0]
    else:
        main_dc = first
        user_id = struct.unpack('>i', ms2.read(4))[0]
    count = struct.unpack('>i', ms2.read(4))[0]
    dc_keys = {}
    for _ in range(min(count, 5)):
        dc_id = struct.unpack('>i', ms2.read(4))[0]
        key = ms2.read(256)
        if len(key) == 256:
            dc_keys[dc_id] = key
    return main_dc, user_id, dc_keys


def parse_referral_link(raw_link: str):
    if not raw_link:
        return None, None
    raw_link = raw_link.strip()
    bot_username, start_param = None, ""
    if "t.me/" in raw_link or "telegram.me/" in raw_link:
        parsed = urlparse(raw_link)
        bot_username = parsed.path.strip("/")
        qs = parse_qs(parsed.query)
        if "start" in qs:
            start_param = qs["start"][0]
    else:
        clean = raw_link.replace("@", "").strip()
        if "?start=" in clean:
            parts = clean.split("?start=")
            bot_username, start_param = parts[0], parts[1]
        elif " " in clean:
            parts = clean.split(" ", 1)
            bot_username, start_param = parts[0], parts[1]
        else:
            bot_username = clean
    if bot_username:
        bot_username = bot_username.replace("@", "").strip()
    return bot_username, start_param


# ═══════════════════════════════════════════════════════════════════════════
# MULTI-SESSION ZIP HANDLER + MTPROTO DOWNLOAD
# ═══════════════════════════════════════════════════════════════════════════
def find_all_tdata_dirs(base_path: str) -> List[str]:
    """Walk entire extracted tree and find ALL directories with valid tdata files."""
    found = []
    for root, dirs, files in os.walk(base_path):
        if 'key_datas' not in files:
            continue
        has_mtp = any(
            f.lower().startswith('d877f783d5d3ef8c') and f.endswith('s')
            for f in files if not os.path.isdir(os.path.join(root, f))
        )
        if has_mtp:
            found.append(root)
    return found


async def download_file_mtproto(document, destination_path: str) -> Tuple[bool, Optional[str]]:
    """Download file via MTProto with 16 parallel workers (supports up to 2GB)."""
    client = await get_mtproto_client()
    input_location = telethon_utils.resolve_bot_file_id(document.file_id)
    if not input_location:
        return False, "Cannot resolve file_id to MTProto location"
    try:
        await client.download_file(
            input_location,
            file=destination_path,
            part_size_kb=MTPROTO_CHUNK_KB,
            workers=MTPROTO_WORKERS
        )
        return True, None
    except Exception as e:
        return False, str(e)[:200]


async def download_zip_document(document, destination_path: str) -> Tuple[bool, Optional[str]]:
    """Download ZIP — MTProto primary (handles >200MB), Bot API fallback for small files."""
    file_size_mb = (document.file_size or 0) / (1024 * 1024)

    # Always try MTProto first — it handles all sizes with 16 parallel workers
    ok, err = await download_file_mtproto(document, destination_path)
    if ok:
        return True, None

    # Bot API fallback only for small files (<20MB)
    if file_size_mb < 20:
        try:
            bot_instance = Bot(token=BOT_TOKEN)
            await bot_instance.download(document, destination=destination_path)
            return True, None
        except Exception as e2:
            return False, f"MTProto: {err} | BotAPI: {e2}"

    return False, f"MTProto failed: {err}"


# ═══════════════════════════════════════════════════════════════════════════
# SESSION VALIDATION (parallel-ready)
# ═══════════════════════════════════════════════════════════════════════════
async def validate_tdata_session(tdata_path: str, timeout: int = SESSION_TIMEOUT) -> dict:
    try:
        main_dc, user_id, dc_keys = parse_tdata_session(tdata_path)
        if not dc_keys:
            return {"status": "DEAD", "error": "No auth keys"}
        dc_order = [main_dc] if main_dc in dc_keys else list(dc_keys.keys())[:1]
        for dc_id in dc_order:
            ip = _DC_IPS.get(dc_id, f"149.154.167.{50+dc_id*2}")
            sess = MemorySession()
            sess.set_dc(dc_id, ip, 443)
            sess.auth_key = AuthKey(dc_keys[dc_id])
            client = TelegramClient(sess, TG_API_ID, TG_API_HASH,
                                    timeout=timeout, connection_retries=2, retry_delay=1)
            try:
                await asyncio.wait_for(client.connect(), timeout=timeout)
                auth = await asyncio.wait_for(client.is_user_authorized(), timeout=timeout)
                if not auth:
                    await client.disconnect()
                    continue
                me = await asyncio.wait_for(client.get_me(), timeout=timeout)
                if not me:
                    await client.disconnect()
                    return {"status": "DEAD", "error": "get_me returned None"}
                if getattr(me, 'deleted', False):
                    await client.disconnect()
                    return {"status": "FROZEN", "error": "Account deleted"}
                has_2fa = False
                try:
                    pwd = await asyncio.wait_for(client(GetPasswordRequest()), timeout=timeout)
                    has_2fa = pwd.has_password
                except Exception:
                    pass
                premium = bool(getattr(me, 'premium', False))
                channels_count, groups_count, stars = 0, 0, 0
                try:
                    dialogs = await asyncio.wait_for(client.get_dialogs(limit=30), timeout=timeout)
                    for d in dialogs:
                        ent = d.entity
                        if isinstance(ent, Channel):
                            if ent.megagroup:
                                groups_count += 1
                            else:
                                channels_count += 1
                        elif isinstance(ent, Chat):
                            groups_count += 1
                except Exception:
                    pass
                try:
                    stars = getattr(me, 'stars_count', 0) or 0
                except Exception:
                    pass
                await client.disconnect()
                return {
                    "status": "VALID", "dc": dc_id, "user_id": me.id,
                    "username": f"@{me.username}" if me.username else "",
                    "phone": f"+{me.phone}" if me.phone else "",
                    "first_name": me.first_name or "", "last_name": me.last_name or "",
                    "2fa": "2FA" if has_2fa else "NO2FA", "premium": premium,
                    "channels": channels_count, "groups": groups_count, "stars": stars
                }
            except Exception as e:
                try:
                    await client.disconnect()
                except Exception:
                    pass
                err_str = str(e).strip()
                if not err_str:
                    await asyncio.sleep(3)
                    continue
                return {"status": "DEAD", "error": err_str[:120]}
        return {"status": "DEAD", "error": "Session expired"}
    except Exception as e:
        return {"status": "ERROR", "error": str(e)[:120]}


async def validate_batch(tdata_paths: List[str], timeout: int = SESSION_TIMEOUT) -> List[dict]:
    """Validate multiple tdata sessions in PARALLEL using asyncio.gather."""
    results = await asyncio.gather(
        *[validate_tdata_session(p, timeout) for p in tdata_paths],
        return_exceptions=True
    )
    out = []
    for path, result in zip(tdata_paths, results):
        if isinstance(result, Exception):
            out.append({"path": path, "status": "ERROR", "error": str(result)[:120]})
        else:
            out.append({"path": path, **result})
    return out


# ═══════════════════════════════════════════════════════════════════════════
# REFERRAL EXECUTION
# ═══════════════════════════════════════════════════════════════════════════
async def execute_referral(tdata_path: str, bot_username: str, start_param: str,
                           timeout: int = SESSION_TIMEOUT) -> dict:
    try:
        main_dc, user_id, dc_keys = parse_tdata_session(tdata_path)
        if not dc_keys:
            return {"success": False, "error": "No auth keys"}
        dc_order = [main_dc] if main_dc in dc_keys else list(dc_keys.keys())[:1]
        for dc_id in dc_order:
            ip = _DC_IPS.get(dc_id, f"149.154.167.{50+dc_id*2}")
            sess = MemorySession()
            sess.set_dc(dc_id, ip, 443)
            sess.auth_key = AuthKey(dc_keys[dc_id])
            client = TelegramClient(sess, TG_API_ID, TG_API_HASH,
                                    timeout=timeout, connection_retries=2, retry_delay=1)
            try:
                await asyncio.wait_for(client.connect(), timeout=timeout)
                auth = await asyncio.wait_for(client.is_user_authorized(), timeout=timeout)
                if not auth:
                    await client.disconnect()
                    continue
                if FORCE_JOIN_CHANNEL:
                    try:
                        await asyncio.wait_for(client(JoinChannelRequest(FORCE_JOIN_CHANNEL)), timeout=10)
                    except Exception:
                        pass
                bot_entity = await client.get_input_entity(bot_username)
                await asyncio.wait_for(
                    client(StartBotRequest(bot=bot_entity, peer=bot_entity,
                                           start_param=start_param or "")),
                    timeout=10
                )
                await client.disconnect()
                return {"success": True}
            except Exception as e:
                try:
                    await client.disconnect()
                except Exception:
                    pass
                err_str = str(e).strip()
                if not err_str:
                    await asyncio.sleep(2)
                    continue
                try:
                    sess2 = MemorySession()
                    sess2.set_dc(dc_id, ip, 443)
                    sess2.auth_key = AuthKey(dc_keys[dc_id])
                    client2 = TelegramClient(sess2, TG_API_ID, TG_API_HASH, timeout=timeout)
                    await client2.connect()
                    cmd = f"/start {start_param}".strip() if start_param else "/start"
                    await client2.send_message(bot_username, cmd)
                    await client2.disconnect()
                    return {"success": True}
                except Exception:
                    pass
                return {"success": False, "error": err_str[:120]}
        return {"success": False, "error": "Failed to execute referral"}
    except Exception as e:
        return {"success": False, "error": str(e)[:120]}


# ═══════════════════════════════════════════════════════════════════════════
# MULTI-SESSION ZIP PROCESSOR
# ═══════════════════════════════════════════════════════════════════════════
async def process_zip_sessions(zip_path: str, added_by: int) -> dict:
    """Extract ZIP, find ALL tdata dirs, validate in PARALLEL, add valid to global pool."""
    extract_dir = zip_path.rsplit('.', 1)[0] + "_extracted"
    os.makedirs(extract_dir, exist_ok=True)
    try:
        with zipfile.ZipFile(zip_path, 'r') as z:
            z.extractall(extract_dir)
    except Exception as e:
        shutil.rmtree(extract_dir, ignore_errors=True)
        return {"total": 0, "valid": 0, "dead": 0, "sessions": [], "error": f"Bad ZIP: {e}"}

    tdata_dirs = find_all_tdata_dirs(extract_dir)
    if not tdata_dirs:
        shutil.rmtree(extract_dir, ignore_errors=True)
        return {"total": 0, "valid": 0, "dead": 0, "sessions": [], "error": "No tdata sessions found in ZIP"}

    # Validate ALL sessions in PARALLEL
    results = await validate_batch(tdata_dirs)

    valid_sessions = []
    dead_count = 0
    for item in results:
        path = item["path"]
        if item.get("status") == "VALID":
            ts = int(time.time())
            safe_name = f"sess_{item['user_id']}_{ts}"
            global_path = os.path.join(GLOBAL_TDATA_DIR, safe_name)
            counter = 0
            while os.path.exists(global_path):
                counter += 1
                global_path = os.path.join(GLOBAL_TDATA_DIR, f"{safe_name}_{counter}")
            try:
                shutil.move(path, global_path)
            except Exception:
                shutil.copytree(path, global_path)
            sid = await db.add_global_tdata(global_path, item, added_by)
            valid_sessions.append({"id": sid, **item})
        else:
            dead_count += 1

    # Clean up extracted directory
    shutil.rmtree(extract_dir, ignore_errors=True)
    return {
        "total": len(tdata_dirs),
        "valid": len(valid_sessions),
        "dead": dead_count,
        "sessions": valid_sessions
    }


# ═══════════════════════════════════════════════════════════════════════════
# DATABASE
# ═══════════════════════════════════════════════════════════════════════════
class Database:
    def __init__(self, path: str):
        self.path = path

    async def init(self):
        os.makedirs(TDATA_STORAGE, exist_ok=True)
        os.makedirs(GLOBAL_TDATA_DIR, exist_ok=True)
        os.makedirs(TEMP_DIR, exist_ok=True)
        async with aiosqlite.connect(self.path) as db:
            await db.executescript("""
                CREATE TABLE IF NOT EXISTS users (
                    user_id INTEGER PRIMARY KEY,
                    username TEXT, first_name TEXT,
                    tier TEXT DEFAULT 'free',
                    referral_count INTEGER DEFAULT 0,
                    global_uses_today INTEGER DEFAULT 0,
                    last_reset_date TEXT DEFAULT '',
                    banned INTEGER DEFAULT 0,
                    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
                );
                CREATE TABLE IF NOT EXISTS referral_links (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    name TEXT, url TEXT,
                    bot_username TEXT, start_param TEXT,
                    added_by INTEGER, active INTEGER DEFAULT 1,
                    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
                );
                CREATE TABLE IF NOT EXISTS referrals (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    user_id INTEGER, referral_link_id INTEGER,
                    target_bot_username TEXT UNIQUE,
                    start_param TEXT, global_session_id INTEGER,
                    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
                );
                CREATE TABLE IF NOT EXISTS global_tdata (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    file_path TEXT UNIQUE,
                    main_dc INTEGER, tg_user_id INTEGER,
                    tg_username TEXT, tg_phone TEXT,
                    tg_first_name TEXT, tg_last_name TEXT,
                    has_2fa TEXT, is_premium INTEGER,
                    channels INTEGER, groups INTEGER, stars INTEGER,
                    status TEXT DEFAULT 'valid',
                    last_checked TIMESTAMP, added_by INTEGER,
                    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
                );
            """)
            await db.commit()
            cur = await db.execute("SELECT COUNT(*) FROM referral_links")
            if (await cur.fetchone())[0] == 0:
                await db.execute(
                    "INSERT INTO referral_links (name, url, bot_username, start_param, added_by) VALUES (?,?,?,?,?)",
                    ("Default Referral", "https://t.me/MyReferrall_bot?start=5944410248",
                     "MyReferrall_bot", "5944410248", ADMIN_ID)
                )
                await db.commit()

    async def get_user(self, user_id: int):
        async with aiosqlite.connect(self.path) as db:
            db.row_factory = aiosqlite.Row
            cur = await db.execute("SELECT * FROM users WHERE user_id = ?", (user_id,))
            row = await cur.fetchone()
            return dict(row) if row else None

    async def register_user(self, user_id: int, username: str, first_name: str):
        async with aiosqlite.connect(self.path) as db:
            await db.execute(
                "INSERT OR IGNORE INTO users (user_id, username, first_name, last_reset_date) VALUES (?,?,?,?)",
                (user_id, username, first_name, datetime.now().strftime("%Y-%m-%d"))
            )
            await db.commit()

    async def reset_daily_limits_if_needed(self, user_id: int):
        today = datetime.now().strftime("%Y-%m-%d")
        async with aiosqlite.connect(self.path) as db:
            cur = await db.execute("SELECT last_reset_date FROM users WHERE user_id = ?", (user_id,))
            row = await cur.fetchone()
            if row and row[0] != today:
                await db.execute(
                    "UPDATE users SET global_uses_today=0, last_reset_date=? WHERE user_id=?",
                    (today, user_id)
                )
                await db.commit()

    async def increment_global_use(self, user_id: int):
        async with aiosqlite.connect(self.path) as db:
            await db.execute("UPDATE users SET global_uses_today=global_uses_today+1 WHERE user_id=?", (user_id,))
            await db.commit()

    # ─── Links ───
    async def get_links(self, active_only: bool = True, user_id: int = None):
        async with aiosqlite.connect(self.path) as db:
            db.row_factory = aiosqlite.Row
            if user_id is not None:
                cur = await db.execute("SELECT * FROM referral_links WHERE added_by=? ORDER BY id DESC", (user_id,))
            elif active_only:
                cur = await db.execute("SELECT * FROM referral_links WHERE active=1 ORDER BY id DESC")
            else:
                cur = await db.execute("SELECT * FROM referral_links ORDER BY id DESC")
            return [dict(r) for r in await cur.fetchall()]

    async def get_links_paginated(self, page: int = 0, per_page: int = PAGE_SIZE, user_id: int = None):
        async with aiosqlite.connect(self.path) as db:
            db.row_factory = aiosqlite.Row
            offset = page * per_page
            if user_id is not None:
                where = "WHERE added_by=?"
                args = (user_id, per_page, offset)
            else:
                where = ""
                args = (per_page, offset)
            cur = await db.execute(f"SELECT * FROM referral_links {where} ORDER BY id DESC LIMIT ? OFFSET ?", args)
            rows = [dict(r) for r in await cur.fetchall()]
            cur2 = await db.execute(f"SELECT COUNT(*) FROM referral_links {where}", (user_id,) if user_id else ())
            total = (await cur2.fetchone())[0]
            return rows, total

    async def add_link(self, name: str, url: str, added_by: int):
        bot_user, sp = parse_referral_link(url)
        async with aiosqlite.connect(self.path) as db:
            cur = await db.execute(
                "INSERT INTO referral_links (name,url,bot_username,start_param,added_by) VALUES (?,?,?,?,?)",
                (name, url, bot_user, sp, added_by)
            )
            await db.commit()
            return cur.lastrowid

    async def delete_link(self, link_id: int):
        async with aiosqlite.connect(self.path) as db:
            await db.execute("DELETE FROM referral_links WHERE id=?", (link_id,))
            await db.commit()

    async def toggle_link(self, link_id: int):
        async with aiosqlite.connect(self.path) as db:
            await db.execute("UPDATE referral_links SET active = CASE WHEN active=1 THEN 0 ELSE 1 END WHERE id=?", (link_id,))
            await db.commit()

    async def get_link_by_id(self, link_id: int):
        async with aiosqlite.connect(self.path) as db:
            db.row_factory = aiosqlite.Row
            cur = await db.execute("SELECT * FROM referral_links WHERE id=?", (link_id,))
            row = await cur.fetchone()
            return dict(row) if row else None

    # ─── Referrals ───
    async def is_bot_referred(self, bot_username: str):
        async with aiosqlite.connect(self.path) as db:
            db.row_factory = aiosqlite.Row
            cur = await db.execute(
                """SELECT r.*, u.username as referrer_username, u.user_id as referrer_id
                   FROM referrals r JOIN users u ON r.user_id=u.user_id
                   WHERE r.target_bot_username=?""", (bot_username,))
            row = await cur.fetchone()
            return dict(row) if row else None

    async def add_referral(self, user_id: int, link_id: int, bot_username: str,
                           start_param: str, session_id: int):
        async with aiosqlite.connect(self.path) as db:
            await db.execute(
                "INSERT INTO referrals (user_id,referral_link_id,target_bot_username,start_param,global_session_id) VALUES (?,?,?,?,?)",
                (user_id, link_id, bot_username, start_param, session_id)
            )
            await db.execute("UPDATE users SET referral_count=referral_count+1 WHERE user_id=?", (user_id,))
            await db.commit()

    async def get_all_referrals_paginated(self, page: int = 0, per_page: int = PAGE_SIZE):
        async with aiosqlite.connect(self.path) as db:
            db.row_factory = aiosqlite.Row
            offset = page * per_page
            cur = await db.execute(
                """SELECT r.*, u.username as user_username, u.first_name as user_first_name,
                          rl.name as link_name
                   FROM referrals r
                   JOIN users u ON r.user_id=u.user_id
                   JOIN referral_links rl ON r.referral_link_id=rl.id
                   ORDER BY r.created_at DESC LIMIT ? OFFSET ?""", (per_page, offset))
            rows = [dict(r) for r in await cur.fetchall()]
            cur2 = await db.execute("SELECT COUNT(*) FROM referrals")
            total = (await cur2.fetchone())[0]
            return rows, total

    # ─── Global Tdata ───
    async def add_global_tdata(self, file_path: str, info: dict, added_by: int):
        async with aiosqlite.connect(self.path) as db:
            cur = await db.execute(
                """INSERT INTO global_tdata
                   (file_path,main_dc,tg_user_id,tg_username,tg_phone,
                    tg_first_name,tg_last_name,has_2fa,is_premium,channels,groups,stars,last_checked,added_by)
                   VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?)""",
                (file_path, info.get("dc"), info.get("user_id"),
                 info.get("username"), info.get("phone"), info.get("first_name"),
                 info.get("last_name"), info.get("2fa"), int(info.get("premium", False)),
                 info.get("channels", 0), info.get("groups", 0), info.get("stars", 0),
                 datetime.now().isoformat(), added_by))
            await db.commit()
            return cur.lastrowid

    async def get_valid_global_sessions(self):
        async with aiosqlite.connect(self.path) as db:
            db.row_factory = aiosqlite.Row
            cur = await db.execute("SELECT * FROM global_tdata WHERE status='valid' ORDER BY RANDOM()")
            return [dict(r) for r in await cur.fetchall()]

    async def get_all_global_sessions_paginated(self, page: int = 0, per_page: int = PAGE_SIZE):
        async with aiosqlite.connect(self.path) as db:
            db.row_factory = aiosqlite.Row
            offset = page * per_page
            cur = await db.execute(
                "SELECT * FROM global_tdata ORDER BY created_at DESC LIMIT ? OFFSET ?", (per_page, offset))
            rows = [dict(r) for r in await cur.fetchall()]
            cur2 = await db.execute("SELECT COUNT(*) FROM global_tdata")
            total = (await cur2.fetchone())[0]
            return rows, total

    async def get_global_session_by_id(self, sid: int):
        async with aiosqlite.connect(self.path) as db:
            db.row_factory = aiosqlite.Row
            cur = await db.execute("SELECT * FROM global_tdata WHERE id=?", (sid,))
            row = await cur.fetchone()
            return dict(row) if row else None

    async def update_global_session_status(self, session_id: int, status: str):
        async with aiosqlite.connect(self.path) as db:
            await db.execute(
                "UPDATE global_tdata SET status=?, last_checked=? WHERE id=?",
                (status, datetime.now().isoformat(), session_id))
            await db.commit()

    async def delete_global_session(self, session_id: int):
        async with aiosqlite.connect(self.path) as db:
            cur = await db.execute("SELECT file_path FROM global_tdata WHERE id=?", (session_id,))
            row = await cur.fetchone()
            if row and row[0] and os.path.exists(row[0]):
                try:
                    shutil.rmtree(row[0], ignore_errors=True)
                except Exception:
                    pass
            await db.execute("DELETE FROM global_tdata WHERE id=?", (session_id,))
            await db.commit()

    async def get_valid_count(self):
        async with aiosqlite.connect(self.path) as db:
            cur = await db.execute("SELECT COUNT(*) FROM global_tdata WHERE status='valid'")
            return (await cur.fetchone())[0]

    async def get_total_users_count(self):
        async with aiosqlite.connect(self.path) as db:
            cur = await db.execute("SELECT COUNT(*) FROM users")
            return (await cur.fetchone())[0]

    async def get_total_refs_count(self):
        async with aiosqlite.connect(self.path) as db:
            cur = await db.execute("SELECT COUNT(*) FROM referrals")
            return (await cur.fetchone())[0]

    # ─── User Management ───
    async def ban_user(self, user_id: int):
        async with aiosqlite.connect(self.path) as db:
            await db.execute("UPDATE users SET banned=1 WHERE user_id=?", (user_id,))
            await db.commit()

    async def unban_user(self, user_id: int):
        async with aiosqlite.connect(self.path) as db:
            await db.execute("UPDATE users SET banned=0 WHERE user_id=?", (user_id,))
            await db.commit()

    async def set_tier(self, user_id: int, tier: str):
        async with aiosqlite.connect(self.path) as db:
            await db.execute("UPDATE users SET tier=? WHERE user_id=?", (tier, user_id))
            await db.commit()

    async def get_all_users_paginated(self, page: int = 0, per_page: int = PAGE_SIZE):
        async with aiosqlite.connect(self.path) as db:
            db.row_factory = aiosqlite.Row
            offset = page * per_page
            cur = await db.execute(
                "SELECT * FROM users ORDER BY created_at DESC LIMIT ? OFFSET ?", (per_page, offset))
            rows = [dict(r) for r in await cur.fetchall()]
            cur2 = await db.execute("SELECT COUNT(*) FROM users")
            total = (await cur2.fetchone())[0]
            return rows, total


# ═══════════════════════════════════════════════════════════════════════════
# BOT SETUP
# ═══════════════════════════════════════════════════════════════════════════
bot = Bot(token=BOT_TOKEN)
dp = Dispatcher(storage=MemoryStorage())
db = Database(DB_PATH)


def is_admin(user_id: int) -> bool:
    return user_id == ADMIN_ID


# ═══════════════════════════════════════════════════════════════════════════
# KEYBOARDS
# ═══════════════════════════════════════════════════════════════════════════
def main_menu(user_id: int):
    kb = [
        [InlineKeyboardButton(text="🚀 Start Referral", callback_data="menu:refer")],
        [InlineKeyboardButton(text="➕ Add My Link", callback_data="menu:addlink"),
         InlineKeyboardButton(text="📋 My Links", callback_data="menu:mylinks")],
        [InlineKeyboardButton(text="📊 My Stats", callback_data="menu:stats"),
         InlineKeyboardButton(text="💎 Tier Info", callback_data="menu:tier")],
    ]
    if is_admin(user_id):
        kb.append([InlineKeyboardButton(text="🔧 Admin Panel", callback_data="menu:admin")])
    return InlineKeyboardMarkup(inline_keyboard=kb)


def back_to_main():
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="⬅️ Main Menu", callback_data="menu:main")]
    ])


def back_btn(target: str = "menu:main"):
    return InlineKeyboardButton(text="⬅️ Back", callback_data=target)


def pagination_kb(prefix: str, page: int, total: int, back_target: str = "menu:admin") -> List[List[InlineKeyboardButton]]:
    """Build pagination row: < Page N/M >  Returns list of rows."""
    total_pages = max(1, (total + PAGE_SIZE - 1) // PAGE_SIZE)
    row = []
    if page > 0:
        row.append(InlineKeyboardButton(text="◀ Prev", callback_data=f"{prefix}:{page-1}"))
    row.append(InlineKeyboardButton(text=f"{page+1}/{total_pages}", callback_data="noop"))
    if page < total_pages - 1:
        row.append(InlineKeyboardButton(text="Next ▶", callback_data=f"{prefix}:{page+1}"))
    return [row] if row else []


def admin_panel():
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🌍 Add Global Tdata", callback_data="admin:addglobal"),
         InlineKeyboardButton(text="🌐 Global Pool", callback_data="admin:globalpool")],
        [InlineKeyboardButton(text="➕ Add Link", callback_data="admin:addlink"),
         InlineKeyboardButton(text="📋 All Links", callback_data="admin:links")],
        [InlineKeyboardButton(text="👥 Users", callback_data="admin:users"),
         InlineKeyboardButton(text="📈 Referrals", callback_data="admin:refs")],
        [InlineKeyboardButton(text="🔨 Ban", callback_data="admin:ban"),
         InlineKeyboardButton(text="✅ Unban", callback_data="admin:unban")],
        [InlineKeyboardButton(text="⭐ Set Tier", callback_data="admin:settier"),
         InlineKeyboardButton(text="📢 Broadcast", callback_data="admin:broadcast")],
        [back_btn("menu:main")]
    ])


def tdata_choice_kb():
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🌍 Use Global Tdata", callback_data="tdchoice:global")],
        [InlineKeyboardButton(text="📁 Upload My Tdata (ZIP)", callback_data="tdchoice:upload")],
        [back_btn("menu:main")]
    ])


def broadcast_choice_kb():
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="✍️ Send Text Message", callback_data="bcast:text")],
        [InlineKeyboardButton(text="↩️ Forward a Message", callback_data="bcast:forward")],
        [back_btn("menu:admin")]
    ])


# ═══════════════════════════════════════════════════════════════════════════
# USER HANDLERS
# ═══════════════════════════════════════════════════════════════════════════
@dp.message(CommandStart())
async def cmd_start(message: Message):
    user = message.from_user
    await db.register_user(user.id, user.username or "", user.first_name or "")
    total_users = await db.get_total_users_count()
    valid_sessions = await db.get_valid_count()
    await message.answer(
        f"⚡ <b>AKAZA x Reffer</b> ⚡\n\n"
        f"👋 Welcome, <b>{user.first_name}</b>!\n\n"
        f"🤖 <b>What I do:</b>\n\n"
        f"  • Upload tdata <b>ZIP files</b> (all sessions extracted automatically)\n\n"
        f"  • Use <b>Global Pool</b> of pre-validated sessions\n\n"
        f"  • <b>Auto-execute</b> referral joins via MTProto\n\n"
        f"  • Supports files <b>>200MB</b> with parallel downloads\n\n"
        f"📊 <b>Your Limits:</b>\n\n"
        f"  🆓 Free: 5 refs | 1 global/day\n\n"
        f"  ⭐ Premium: 15 refs | 3 global/day\n\n"
        f"  👑 Premium+: Unlimited\n\n"
        f"🌐 Pool: <b>{valid_sessions}</b> sessions | Users: <b>{total_users}</b>\n\n"
        f"<i>24h reset cycle • Multi-session ZIP support • MTProto powered</i>",
        reply_markup=main_menu(user.id), parse_mode="HTML"
    )


@dp.callback_query(F.data == "noop")
async def cb_noop(callback: CallbackQuery):
    await callback.answer()


@dp.callback_query(F.data == "menu:main")
async def cb_main(callback: CallbackQuery):
    await callback.message.edit_text(
        "⚡ <b>AKAZA x Reffer — Home</b>",
        reply_markup=main_menu(callback.from_user.id), parse_mode="HTML"
    )


@dp.callback_query(F.data == "menu:tier")
async def cb_tier(callback: CallbackQuery):
    text = (
        "💎 <b>AKAZA Tier System</b>\n\n"
        "🆓 <b>Free</b>\n"
        "   Referrals: 5 max\n"
        "   Global Tdata: 1/day\n\n"
        "⭐ <b>Premium</b>\n"
        "   Referrals: 15 max\n"
        "   Global Tdata: 3/day\n\n"
        "   Referrals: \u221e\n\n"
        "   Global Tdata: \u221e\n\n"
        "<i>Contact admin to upgrade your tier.</i>"
    )
    await callback.message.edit_text(text, reply_markup=back_to_main(), parse_mode="HTML")


# ═══════════════════════════════════════════════════════════════════════════
# USER HANDLERS (continued)
# ═══════════════════════════════════════════════════════════════════════════
@dp.callback_query(F.data == "menu:stats")
async def cb_stats(callback: CallbackQuery):
    user_id = callback.from_user.id
    await db.reset_daily_limits_if_needed(user_id)
    u = await db.get_user(user_id)
    if not u:
        await callback.answer("User not found", show_alert=True)
        return
    ref_limit = REFERRAL_LIMITS.get(u['tier'], 5)
    glob_limit = GLOBAL_USE_LIMITS.get(u['tier'], 1)
    ref_str = str(ref_limit) if u['tier'] != 'premium_plus' else "\u221e"
    glob_str = str(glob_limit) if u['tier'] != 'premium_plus' else "\u221e"
    text = (
        f"\U0001f4ca <b>AKAZA Stats</b>\n\n"
        f"\U0001f464 Name: <code>{u['first_name']}</code>\n"
        f"\U0001f530 Tier: <code>{u['tier'].upper()}</code>\n"
        f"\U0001f4e4 Referrals: <code>{u['referral_count']} / {ref_str}</code>\n"
        f"\U0001f30d Global Today: <code>{u['global_uses_today']} / {glob_str}</code>\n"
        f"\U0001f6ab Banned: <code>{'YES' if u['banned'] else 'NO'}</code>"
    )
    await callback.message.edit_text(text, reply_markup=back_to_main(), parse_mode="HTML")


# ─── My Links ───
@dp.callback_query(F.data.startswith("menu:mylinks"))
async def cb_my_links(callback: CallbackQuery):
    user_id = callback.from_user.id
    # Parse page from callback data if present
    parts = callback.data.split(":")
    page = int(parts[2]) if len(parts) > 2 else 0
    links, total = await db.get_links_paginated(page=page, user_id=user_id)
    if not links:
        await callback.message.edit_text(
            "\U0001f4cb <b>My Links</b>\n\nNo links yet. Add one!",
            reply_markup=InlineKeyboardMarkup(inline_keyboard=[
                [InlineKeyboardButton(text="\u2795 Add Link", callback_data="menu:addlink")],
                [back_btn()]
            ]), parse_mode="HTML"
        )
        return
    text = f"\U0001f4cb <b>My Links</b> ({total} total)\n\n"
    kb = []
    for link in links:
        status = "\U0001f7e2" if link['active'] else "\U0001f534"
        text += f"{status} <code>{link['id']}</code> | <b>{link['name']}</b> \u2192 @{link['bot_username']}\n"
        kb.append([InlineKeyboardButton(
            text=f"\U0001f5d1 Delete #{link['id']}", callback_data=f"myld:{link['id']}:{page}"
        )])
    kb.extend(pagination_kb("mylk", page, total))
    kb.append([back_btn()])
    await callback.message.edit_text(text, reply_markup=InlineKeyboardMarkup(inline_keyboard=kb), parse_mode="HTML")


@dp.callback_query(F.data.startswith("mylk:"))
async def cb_my_links_page(callback: CallbackQuery):
    page = int(callback.data.split(":")[1])
    await callback.message.edit_text("\u23f3 Loading...")
    # Reuse mylinks handler by editing callback data
    callback.data = f"menu:mylinks:{page}"
    await cb_my_links(callback)


@dp.callback_query(F.data.startswith("myld:"))
async def cb_my_link_delete_ask(callback: CallbackQuery):
    parts = callback.data.split(":")
    link_id = int(parts[1])
    page = int(parts[2]) if len(parts) > 2 else 0
    link = await db.get_link_by_id(link_id)
    if not link or link['added_by'] != callback.from_user.id:
        await callback.answer("Not your link", show_alert=True)
        return
    await callback.message.edit_text(
        f"\u26a0\ufe0f <b>Delete this link?</b>\n\n"
        f"\U0001f517 <b>{link['name']}</b> \u2192 @{link['bot_username']}\n\n"
        f"This cannot be undone.",
        reply_markup=InlineKeyboardMarkup(inline_keyboard=[
            [InlineKeyboardButton(text="\u2705 Yes, Delete", callback_data=f"myld_y:{link_id}:{page}"),
             InlineKeyboardButton(text="\u274c Cancel", callback_data=f"mylk:{page}")]
        ]), parse_mode="HTML"
    )


@dp.callback_query(F.data.startswith("myld_y:"))
async def cb_my_link_delete_confirm(callback: CallbackQuery):
    parts = callback.data.split(":")
    link_id = int(parts[1])
    page = int(parts[2]) if len(parts) > 2 else 0
    link = await db.get_link_by_id(link_id)
    if link and link['added_by'] == callback.from_user.id:
        await db.delete_link(link_id)
    await callback.answer("Deleted!")
    callback.data = f"menu:mylinks:{page}"
    await cb_my_links(callback)


# ─── Add User Link ───
@dp.callback_query(F.data == "menu:addlink")
async def cb_add_user_link(callback: CallbackQuery, state: FSMContext):
    user_id = callback.from_user.id
    u = await db.get_user(user_id)
    if not u:
        await callback.answer("Register first", show_alert=True)
        return
    if u['banned']:
        await callback.answer("Banned", show_alert=True)
        return
    ref_limit = REFERRAL_LIMITS.get(u['tier'], 5)
    user_links = await db.get_links(user_id=user_id)
    if len(user_links) >= ref_limit:
        await callback.answer(f"Link limit reached ({len(user_links)}/{ref_limit}). Upgrade tier.", show_alert=True)
        return
    await state.set_state(UserState.waiting_user_link_name)
    await callback.message.edit_text(
        "\u2795 <b>Add Your Referral Link</b>\n\nStep 1/2: Send the <b>name</b> for this link:",
        reply_markup=back_to_main(), parse_mode="HTML"
    )


@dp.message(UserState.waiting_user_link_name)
async def user_link_name(message: Message, state: FSMContext):
    await state.update_data(link_name=message.text.strip())
    await state.set_state(UserState.waiting_user_link_url)
    await message.answer("Step 2/2: Send the referral URL:", parse_mode="HTML")


@dp.message(UserState.waiting_user_link_url)
async def user_link_url(message: Message, state: FSMContext):
    data = await state.get_data()
    name = data.get("link_name", "My Link")
    url = message.text.strip()
    bot_u, sp = parse_referral_link(url)
    if not bot_u:
        await message.answer("\u274c Invalid URL. Format: t.me/bot?start=param or @bot start_param")
        return
    lid = await db.add_link(name, url, message.from_user.id)
    await message.answer(
        f"\u2705 <b>Link Added!</b>\n\nID: <code>{lid}</code>\nName: <code>{name}</code>\nBot: @{bot_u}",
        reply_markup=main_menu(message.from_user.id), parse_mode="HTML"
    )
    await state.clear()


# ─── Start Referral Flow ───
@dp.callback_query(F.data == "menu:refer")
async def cb_refer(callback: CallbackQuery, state: FSMContext):
    user_id = callback.from_user.id
    u = await db.get_user(user_id)
    if not u:
        await callback.answer("Register first with /start", show_alert=True)
        return
    if u['banned']:
        await callback.answer("\U0001f6ab Banned!", show_alert=True)
        return
    await db.reset_daily_limits_if_needed(user_id)
    u = await db.get_user(user_id)
    ref_limit = REFERRAL_LIMITS.get(u['tier'], 5)
    if u['referral_count'] >= ref_limit:
        await callback.answer(f"Referral limit ({u['referral_count']}/{ref_limit}). Upgrade tier.", show_alert=True)
        return
    await state.set_state(UserState.waiting_tdata_choice)
    await callback.message.edit_text(
        "\U0001f680 <b>Start Referral</b>\n\nChoose how to provide tdata session:",
        reply_markup=tdata_choice_kb(), parse_mode="HTML"
    )


@dp.callback_query(F.data == "tdchoice:global")
async def cb_use_global(callback: CallbackQuery, state: FSMContext):
    user_id = callback.from_user.id
    await db.reset_daily_limits_if_needed(user_id)
    u = await db.get_user(user_id)
    glob_limit = GLOBAL_USE_LIMITS.get(u['tier'], 1)
    if u['global_uses_today'] >= glob_limit:
        await callback.answer(f"Daily global limit ({u['global_uses_today']}/{glob_limit}). Try tomorrow.", show_alert=True)
        return
    links = await db.get_links(active_only=True)
    if not links:
        await callback.answer("No referral links available.", show_alert=True)
        return
    kb = [[InlineKeyboardButton(text=f"\U0001f517 {l['name']}", callback_data=f"refg:{l['id']}")] for l in links]
    kb.append([back_btn("menu:refer")])
    await callback.message.edit_text(
        "\U0001f3af <b>Select target (Global Tdata):</b>",
        reply_markup=InlineKeyboardMarkup(inline_keyboard=kb), parse_mode="HTML"
    )


@dp.callback_query(F.data.startswith("refg:"))
async def cb_global_pick_link(callback: CallbackQuery, state: FSMContext):
    link_id = int(callback.data.split(":")[1])
    link = await db.get_link_by_id(link_id)
    if not link or not link['active']:
        await callback.answer("Link not found", show_alert=True)
        return
    existing = await db.is_bot_referred(link['bot_username'])
    if existing:
        await callback.message.edit_text(
            f"\u26a0\ufe0f <b>Already Referred!</b>\n\n"
            f"\U0001f916 Bot: @{link['bot_username']}\n"
            f"\U0001f464 By: <code>@{existing['referrer_username'] or existing['referrer_id']}</code>\n"
            f"\U0001f550 {existing['created_at']}",
            reply_markup=back_to_main(), parse_mode="HTML"
        )
        return
    sessions = await db.get_valid_global_sessions()
    if not sessions:
        await callback.message.edit_text(
            "\u274c <b>No global tdata available.</b>\n\nTry again later or upload your own.",
            reply_markup=back_to_main(), parse_mode="HTML"
        )
        return
    session = sessions[0]
    await callback.message.edit_text(
        f"\U0001f30d <b>Using Global Tdata</b>\n\n"
        f"\U0001f464 <code>{session['tg_first_name'] or 'Unknown'}</code>\n"
        f"\U0001f4f1 {session['tg_phone'] or 'N/A'}\n\n"
        f"\U0001f680 Executing referral to <b>@{link['bot_username']}</b>...",
        parse_mode="HTML"
    )
    ref_res = await execute_referral(session['file_path'], link['bot_username'], link['start_param'] or "")
    if not ref_res.get("success"):
        await callback.message.edit_text(
            f"\u274c <b>Referral Failed!</b>\n\nReason: <code>{ref_res.get('error')}</code>",
            reply_markup=back_to_main(), parse_mode="HTML"
        )
        return
    await db.add_referral(callback.from_user.id, link_id, link['bot_username'],
                          link['start_param'] or "", session['id'])
    await db.increment_global_use(callback.from_user.id)
    await callback.message.edit_text(
        f"\U0001f389 <b>Referral Successful!</b>\n\n"
        f"\U0001f916 Referred to: @{link['bot_username']}\n"
        f"\U0001f30d Used: Global Tdata\n"
        f"\u2705 Count updated.",
        reply_markup=main_menu(callback.from_user.id), parse_mode="HTML"
    )


@dp.callback_query(F.data == "tdchoice:upload")
async def cb_upload_tdata(callback: CallbackQuery, state: FSMContext):
    await state.set_state(UserState.waiting_tdata_upload)
    await callback.message.edit_text(
        "\U0001f4c1 <b>Upload Tdata ZIP</b>\n\n"
        "Send me your <b>tdata as a ZIP file</b>.\n\n"
        "\U0001f4a1 <b>Multi-session:</b> All tdata sessions inside the ZIP will be\n"
        "extracted, validated in <b>parallel</b>, and valid ones added to the Global Pool.\n\n"
        "\U0001f4e6 Supports files <b>>200MB</b> via MTProto (16 parallel chunks).",
        reply_markup=back_to_main(), parse_mode="HTML"
    )


@dp.message(UserState.waiting_tdata_upload, F.document)
async def process_user_tdata(message: Message, state: FSMContext):
    user_id = message.from_user.id
    u = await db.get_user(user_id)
    if not u or u['banned']:
        await message.answer("\U0001f6ab Banned or not registered.")
        return
    doc = message.document
    file_name = (doc.file_name or "").lower()
    if not file_name.endswith(".zip"):
        await message.answer("\u274c Send a valid ZIP file.", parse_mode="HTML")
        return
    size_mb = (doc.file_size or 0) / (1024 * 1024)
    status_msg = await message.answer(
        f"\u23f3 Downloading ({size_mb:.1f}MB via MTProto 16 workers)..."
    )
    ts = int(time.time())
    temp_base = os.path.join(TEMP_DIR, f"{user_id}_{ts}")
    os.makedirs(temp_base, exist_ok=True)
    zip_path = os.path.join(temp_base, "upload.zip")
    ok, error = await download_zip_document(doc, zip_path)
    if not ok:
        logger.error(f"Download error: {error}")
        await status_msg.edit_text(f"\u274c Download failed: <code>{error}</code>", parse_mode="HTML")
        shutil.rmtree(temp_base, ignore_errors=True)
        await state.clear()
        return
    await status_msg.edit_text("\U0001f4e6 Extracting ZIP & scanning for sessions...")
    result = await process_zip_sessions(zip_path, user_id)
    shutil.rmtree(temp_base, ignore_errors=True)
    if result.get("error"):
        await status_msg.edit_text(f"\u274c <b>Error:</b> <code>{result['error']}</code>", parse_mode="HTML")
        await state.clear()
        return
    total = result['total']
    valid = result['valid']
    dead = result['dead']
    if valid == 0:
        await status_msg.edit_text(
            f"\u274c <b>No Valid Sessions</b>\n\n"
            f"Scanned: <code>{total}</code> | Valid: <code>0</code> | Dead: <code>{dead}</code>\n\n"
            f"<i>All sessions were invalid or expired.</i>",
            reply_markup=back_to_main(), parse_mode="HTML"
        )
        await state.clear()
        return
    # Build results text
    text = (
        f"\u2705 <b>ZIP Processed!</b>\n\n"
        f"\U0001f4c2 Scanned: <code>{total}</code> sessions\n"
        f"\U0001f7e2 Valid: <code>{valid}</code>\n"
        f"\U0001f534 Dead: <code>{dead}</code>\n\n"
        f"\U0001f30d All valid sessions added to <b>Global Pool</b>!\n\n"
    )
    for s in result['sessions'][:10]:
        text += (
            f"\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\n"
            f"\U0001f464 <code>{s.get('first_name','')} {s.get('last_name','')}</code>\n"
            f"\U0001f4f1 <code>{s.get('phone','N/A')}</code> | "
            f"\U0001f512 <code>{s.get('2fa','')}</code> | "
            f"\U0001f48e <code>{'Yes' if s.get('premium') else 'No'}</code>\n"
        )
    if valid > 10:
        text += f"\n...and {valid - 10} more."
    # Ask if user wants to execute referral now
    links = await db.get_links(active_only=True)
    if not links:
        text += "\n\n<i>No referral links available.</i>"
        await status_msg.edit_text(text, reply_markup=back_to_main(), parse_mode="HTML")
        await state.clear()
        return
    kb = [[InlineKeyboardButton(text=f"\U0001f517 {l['name']}", callback_data=f"refu:{l['id']}")] for l in links]
    kb.append([InlineKeyboardButton(text="\u23ed Skip", callback_data="menu:main")])
    text += "\n\n\U0001f3af <b>Execute referral now?</b>"
    await status_msg.edit_text(text, reply_markup=InlineKeyboardMarkup(inline_keyboard=kb), parse_mode="HTML")


@dp.callback_query(F.data.startswith("refu:"))
async def cb_user_upload_refer(callback: CallbackQuery, state: FSMContext):
    user_id = callback.from_user.id
    link_id = int(callback.data.split(":")[1])
    link = await db.get_link_by_id(link_id)
    if not link:
        await callback.answer("Link not found", show_alert=True)
        return
    existing = await db.is_bot_referred(link['bot_username'])
    if existing:
        await callback.message.edit_text(
            f"\u26a0\ufe0f <b>Already Referred!</b>\n\n"
            f"\U0001f916 @{link['bot_username']} by <code>@{existing['referrer_username'] or existing['referrer_id']}</code>",
            reply_markup=back_to_main(), parse_mode="HTML"
        )
        await state.clear()
        return
    sessions = await db.get_valid_global_sessions()
    if not sessions:
        await callback.message.edit_text(
            "\u274c <b>No global tdata available.</b>", reply_markup=back_to_main(), parse_mode="HTML"
        )
        await state.clear()
        return
    session = sessions[0]
    await callback.message.edit_text(
        f"\U0001f680 <b>Executing referral...</b>\n\U0001f916 @{link['bot_username']}", parse_mode="HTML"
    )
    ref_res = await execute_referral(session['file_path'], link['bot_username'], link['start_param'] or "")
    if not ref_res.get("success"):
        await callback.message.edit_text(
            f"\u274c <b>Failed!</b>\n\n<code>{ref_res.get('error')}</code>",
            reply_markup=back_to_main(), parse_mode="HTML"
        )
        await state.clear()
        return
    await db.add_referral(user_id, link_id, link['bot_username'],
                          link['start_param'] or "", session['id'])
    await db.increment_global_use(user_id)
    await callback.message.edit_text(
        f"\U0001f389 <b>Referral Successful!</b>\n\n"
        f"\U0001f916 @{link['bot_username']}\n\U0001f30d Global Tdata\n\u2705 Done!",
        reply_markup=main_menu(user_id), parse_mode="HTML"
    )
    await state.clear()


@dp.message(UserState.waiting_tdata_upload)
async def wrong_tdata_upload(message: Message):
    await message.answer("\u274c Please send a ZIP file containing your tdata folder.")


# ═══════════════════════════════════════════════════════════════════════════
# ADMIN HANDLERS
# ═══════════════════════════════════════════════════════════════════════════
@dp.callback_query(F.data == "menu:admin")
async def cb_admin(callback: CallbackQuery):
    if not is_admin(callback.from_user.id):
        await callback.answer("\U0001f512 Admin only", show_alert=True)
        return
    valid_count = await db.get_valid_count()
    total_users = await db.get_total_users_count()
    total_refs = await db.get_total_refs_count()
    await callback.message.edit_text(
        f"\U0001f527 <b>AKAZA Admin Panel</b>\n\n"
        f"\U0001f46b Users: <code>{total_users}</code>\n"
        f"\U0001f30d Valid Sessions: <code>{valid_count}</code>\n"
        f"\U0001f4c8 Total Referrals: <code>{total_refs}</code>",
        reply_markup=admin_panel(), parse_mode="HTML"
    )


# ─── Add Global Tdata ───
@dp.callback_query(F.data == "admin:addglobal")
async def cb_add_global(callback: CallbackQuery, state: FSMContext):
    if not is_admin(callback.from_user.id):
        return
    await state.set_state(AdminState.waiting_global_tdata)
    await callback.message.edit_text(
        "\U0001f30d <b>Add Global Tdata</b>\n\n"
        "Send me a <b>tdata ZIP</b> (multi-session supported).\n\n"
        "\U0001f4a1 All sessions in the ZIP will be extracted & validated in parallel.",
        reply_markup=back_to_main(), parse_mode="HTML"
    )


@dp.message(AdminState.waiting_global_tdata, F.document)
async def admin_process_global_tdata(message: Message, state: FSMContext):
    if not is_admin(message.from_user.id):
        return
    doc = message.document
    if not (doc.file_name or "").lower().endswith(".zip"):
        await message.answer("\u274c Send a ZIP file.")
        return
    size_mb = (doc.file_size or 0) / (1024 * 1024)
    status_msg = await message.answer(f"\u23f3 Downloading ({size_mb:.1f}MB, MTProto 16 workers)...")
    ts = int(time.time())
    temp_base = os.path.join(TEMP_DIR, f"admin_{ts}")
    os.makedirs(temp_base, exist_ok=True)
    zip_path = os.path.join(temp_base, "upload.zip")
    ok, error = await download_zip_document(doc, zip_path)
    if not ok:
        await status_msg.edit_text(f"\u274c Download failed: <code>{error}</code>", parse_mode="HTML")
        shutil.rmtree(temp_base, ignore_errors=True)
        return
    await status_msg.edit_text("\U0001f4e6 Extracting & validating all sessions in parallel...")
    result = await process_zip_sessions(zip_path, ADMIN_ID)
    shutil.rmtree(temp_base, ignore_errors=True)
    if result.get("error"):
        await status_msg.edit_text(f"\u274c <code>{result['error']}</code>", parse_mode="HTML")
        await state.clear()
        return
    text = (
        f"\U0001f4e6 <b>ZIP Processed!</b>\n\n"
        f"\U0001f4c2 Scanned: <code>{result['total']}</code>\n"
        f"\U0001f7e2 Valid: <code>{result['valid']}</code>\n"
        f"\U0001f534 Dead: <code>{result['dead']}</code>\n\n"
    )
    for s in result['sessions'][:15]:
        text += (
            f"\U0001f7e2 <code>#{s.get('id','')}</code> "
            f"<code>{s.get('first_name','')} {s.get('last_name','')}</code> "
            f"{s.get('phone','')} {s.get('2fa','')}\n"
        )
    if result['valid'] > 15:
        text += f"\n...+{result['valid'] - 15} more"
    await status_msg.edit_text(text, reply_markup=admin_panel(), parse_mode="HTML")
    await state.clear()


@dp.message(AdminState.waiting_global_tdata)
async def wrong_admin_global(message: Message):
    await message.answer("\u274c Send a ZIP file.")


# ─── Global Pool (paginated) ───
@dp.callback_query(F.data.startswith("admin:globalpool"))
async def cb_global_pool(callback: CallbackQuery):
    if not is_admin(callback.from_user.id):
        return
    parts = callback.data.split(":")
    page = int(parts[2]) if len(parts) > 2 else 0
    sessions, total = await db.get_all_global_sessions_paginated(page=page)
    if not sessions:
        await callback.message.edit_text(
            "\U0001f310 <b>Global Pool is empty.</b>",
            reply_markup=admin_panel(), parse_mode="HTML"
        )
        return
    text = f"\U0001f310 <b>Global Tdata Pool</b> ({total} total)\n\n"
    kb = []
    for s in sessions:
        emoji = "\U0001f7e2" if s['status'] == 'valid' else "\U0001f534"
        prem = "\U0001f48e" if s['is_premium'] else "  "
        text += (
            f"{emoji} <code>#{s['id']}</code> {prem} "
            f"<code>{s['tg_first_name'] or '-'}</code> | "
            f"{s['tg_phone'] or 'N/A'} | {s['status']}\n"
        )
        kb.append([InlineKeyboardButton(
            text=f"\U0001f5d1 Del #{s['id']}", callback_data=f"cfm_dg:{s['id']}:{page}"
        )])
    kb.extend(pagination_kb("admgp", page, total))
    kb.append([back_btn("menu:admin")])
    await callback.message.edit_text(text, reply_markup=InlineKeyboardMarkup(inline_keyboard=kb), parse_mode="HTML")


@dp.callback_query(F.data.startswith("admgp:"))
async def cb_global_pool_page(callback: CallbackQuery):
    page = int(callback.data.split(":")[1])
    callback.data = f"admin:globalpool:{page}"
    await cb_global_pool(callback)


@dp.callback_query(F.data.startswith("cfm_dg:"))
async def cb_confirm_del_global(callback: CallbackQuery):
    parts = callback.data.split(":")
    sid = int(parts[1])
    page = int(parts[2]) if len(parts) > 2 else 0
    session = await db.get_global_session_by_id(sid)
    if not session:
        await callback.answer("Not found", show_alert=True)
        return
    await callback.message.edit_text(
        f"\u26a0\ufe0f <b>Delete session #{sid}?</b>\n\n"
        f"\U0001f464 <code>{session['tg_first_name']} {session['tg_last_name']}</code>\n"
        f"\U0001f4f1 <code>{session['tg_phone'] or 'N/A'}</code>\n\n"
        f"<i>This will also delete the tdata files from disk.</i>",
        reply_markup=InlineKeyboardMarkup(inline_keyboard=[
            [InlineKeyboardButton(text="\u2705 Yes, Delete", callback_data=f"dg_yes:{sid}:{page}"),
             InlineKeyboardButton(text="\u274c Cancel", callback_data=f"admgp:{page}")]
        ]), parse_mode="HTML"
    )


@dp.callback_query(F.data.startswith("dg_yes:"))
async def cb_del_global_confirmed(callback: CallbackQuery):
    parts = callback.data.split(":")
    sid = int(parts[1])
    page = int(parts[2]) if len(parts) > 2 else 0
    await db.delete_global_session(sid)
    await callback.answer("Deleted")
    callback.data = f"admin:globalpool:{page}"
    await cb_global_pool(callback)


# ─── Links (admin, paginated) ───
@dp.callback_query(F.data.startswith("admin:links"))
async def cb_admin_links(callback: CallbackQuery):
    if not is_admin(callback.from_user.id):
        return
    parts = callback.data.split(":")
    page = int(parts[2]) if len(parts) > 2 else 0
    links, total = await db.get_links_paginated(page=page)
    if not links:
        await callback.message.edit_text(
            "\U0001f4cb <b>No links.</b>", reply_markup=admin_panel(), parse_mode="HTML"
        )
        return
    text = f"\U0001f4cb <b>All Links</b> ({total})\n\n"
    kb = []
    for link in links:
        status = "\U0001f7e2" if link['active'] else "\U0001f534"
        owner = "\U0001f451Admin" if link['added_by'] == ADMIN_ID else f"\U0001f464{link['added_by']}"
        text += f"{status} <code>#{link['id']}</code> {owner} | <b>{link['name']}</b> \u2192 @{link['bot_username']}\n"
        toggle_emoji = "🔴" if link['active'] else "🟢"
        toggle_label = "Disable" if link['active'] else "Enable"
        row = [
            InlineKeyboardButton(text=f"❌ Del #{link['id']}", callback_data=f"cfm_dl:{link['id']}:{page}"),
            InlineKeyboardButton(text=f"{toggle_emoji} {toggle_label} #{link['id']}",
                               callback_data=f"tgl_lk:{link['id']}:{page}")
        ]
        kb.append(row)
    kb.extend(pagination_kb("admlk", page, total))
    kb.append([back_btn("menu:admin")])
    await callback.message.edit_text(text, reply_markup=InlineKeyboardMarkup(inline_keyboard=kb), parse_mode="HTML")


@dp.callback_query(F.data.startswith("admlk:"))
async def cb_admin_links_page(callback: CallbackQuery):
    page = int(callback.data.split(":")[1])
    callback.data = f"admin:links:{page}"
    await cb_admin_links(callback)


@dp.callback_query(F.data.startswith("tgl_lk:"))
async def cb_toggle_link(callback: CallbackQuery):
    parts = callback.data.split(":")
    link_id = int(parts[1])
    page = int(parts[2]) if len(parts) > 2 else 0
    await db.toggle_link(link_id)
    await callback.answer("Toggled!")
    callback.data = f"admin:links:{page}"
    await cb_admin_links(callback)


@dp.callback_query(F.data.startswith("cfm_dl:"))
async def cb_confirm_del_link(callback: CallbackQuery):
    parts = callback.data.split(":")
    link_id = int(parts[1])
    page = int(parts[2]) if len(parts) > 2 else 0
    link = await db.get_link_by_id(link_id)
    if not link:
        await callback.answer("Not found", show_alert=True)
        return
    await callback.message.edit_text(
        f"\u26a0\ufe0f <b>Delete link?</b>\n\n"
        f"\U0001f517 <b>{link['name']}</b> \u2192 @{link['bot_username']}",
        reply_markup=InlineKeyboardMarkup(inline_keyboard=[
            [InlineKeyboardButton(text="\u2705 Delete", callback_data=f"dl_yes:{link_id}:{page}"),
             InlineKeyboardButton(text="\u274c Cancel", callback_data=f"admlk:{page}")]
        ]), parse_mode="HTML"
    )


@dp.callback_query(F.data.startswith("dl_yes:"))
async def cb_del_link_confirmed(callback: CallbackQuery):
    parts = callback.data.split(":")
    link_id = int(parts[1])
    page = int(parts[2]) if len(parts) > 2 else 0
    await db.delete_link(link_id)
    await callback.answer("Deleted")
    callback.data = f"admin:links:{page}"
    await cb_admin_links(callback)


# ─── Add Link (admin) ───
@dp.callback_query(F.data == "admin:addlink")
async def cb_admin_addlink(callback: CallbackQuery, state: FSMContext):
    if not is_admin(callback.from_user.id):
        return
    await state.set_state(AdminState.waiting_link_name)
    await callback.message.edit_text(
        "\u2795 <b>Add Link (Admin)</b>\n\nStep 1/2: Send the name:",
        reply_markup=back_to_main(), parse_mode="HTML"
    )


@dp.message(AdminState.waiting_link_name)
async def admin_link_name(message: Message, state: FSMContext):
    await state.update_data(link_name=message.text.strip())
    await state.set_state(AdminState.waiting_link_url)
    await message.answer("Step 2/2: Send the URL:", parse_mode="HTML")


@dp.message(AdminState.waiting_link_url)
async def admin_link_url(message: Message, state: FSMContext):
    data = await state.get_data()
    name = data.get("link_name", "Unnamed")
    url = message.text.strip()
    bot_u, sp = parse_referral_link(url)
    if not bot_u:
        await message.answer("\u274c Invalid URL.")
        return
    lid = await db.add_link(name, url, ADMIN_ID)
    await message.answer(
        f"\u2705 Link Added!\nID: <code>{lid}</code>\nBot: @{bot_u}",
        reply_markup=admin_panel(), parse_mode="HTML"
    )
    await state.clear()


# ─── Users (paginated) ───
@dp.callback_query(F.data.startswith("admin:users"))
async def cb_admin_users(callback: CallbackQuery):
    if not is_admin(callback.from_user.id):
        return
    parts = callback.data.split(":")
    page = int(parts[2]) if len(parts) > 2 else 0
    users, total = await db.get_all_users_paginated(page=page)
    if not users:
        await callback.message.edit_text(
            "\U0001f465 <b>No users.</b>", reply_markup=admin_panel(), parse_mode="HTML"
        )
        return
    text = f"\U0001f465 <b>Users</b> ({total})\n\n"
    for u in users:
        ban_icon = "\U0001f6ab" if u['banned'] else "\u2705"
        text += (
            f"{ban_icon} <code>{u['user_id']}</code> @{u['username'] or '-'} | "
            f"<b>{u['tier']}</b> | Refs:{u['referral_count']} | Global:{u['global_uses_today']}\n"
        )
    kb = pagination_kb("admup", page, total)
    kb.append([back_btn("menu:admin")])
    await callback.message.edit_text(text, reply_markup=InlineKeyboardMarkup(inline_keyboard=kb), parse_mode="HTML")


@dp.callback_query(F.data.startswith("admup:"))
async def cb_admin_users_page(callback: CallbackQuery):
    page = int(callback.data.split(":")[1])
    callback.data = f"admin:users:{page}"
    await cb_admin_users(callback)


# ─── Referrals (paginated) ───
@dp.callback_query(F.data.startswith("admin:refs"))
async def cb_admin_refs(callback: CallbackQuery):
    if not is_admin(callback.from_user.id):
        return
    parts = callback.data.split(":")
    page = int(parts[2]) if len(parts) > 2 else 0
    refs, total = await db.get_all_referrals_paginated(page=page)
    if not refs:
        await callback.message.edit_text(
            "\U0001f4c8 <b>No referrals yet.</b>", reply_markup=admin_panel(), parse_mode="HTML"
        )
        return
    text = f"\U0001f4c8 <b>Referrals</b> ({total})\n\n"
    for r in refs:
        text += (
            f"\U0001f464 <code>{r['user_id']}</code> (@{r['user_username'] or '-'})\n"
            f"   \u2192 \U0001f916 @{r['target_bot_username']} | {r['link_name']}\n"
            f"   \U0001f550 {r['created_at']}\n"
        )
    kb = pagination_kb("admrf", page, total)
    kb.append([back_btn("menu:admin")])
    await callback.message.edit_text(text, reply_markup=InlineKeyboardMarkup(inline_keyboard=kb), parse_mode="HTML")


@dp.callback_query(F.data.startswith("admrf:"))
async def cb_admin_refs_page(callback: CallbackQuery):
    page = int(callback.data.split(":")[1])
    callback.data = f"admin:refs:{page}"
    await cb_admin_refs(callback)


# ─── Ban / Unban ───
@dp.callback_query(F.data == "admin:ban")
async def cb_ban(callback: CallbackQuery, state: FSMContext):
    if not is_admin(callback.from_user.id):
        return
    await state.set_state(AdminState.waiting_ban_id)
    await callback.message.edit_text(
        "\U0001f528 Send <code>user_id</code> to ban:", reply_markup=back_to_main(), parse_mode="HTML"
    )


@dp.message(AdminState.waiting_ban_id)
async def admin_ban(message: Message, state: FSMContext):
    try:
        uid = int(message.text.strip())
    except ValueError:
        await message.answer("\u274c Invalid ID")
        return
    await db.ban_user(uid)
    await message.answer(f"\U0001f6ab Banned <code>{uid}</code>.", reply_markup=admin_panel(), parse_mode="HTML")
    await state.clear()


@dp.callback_query(F.data == "admin:unban")
async def cb_unban(callback: CallbackQuery, state: FSMContext):
    if not is_admin(callback.from_user.id):
        return
    await state.set_state(AdminState.waiting_unban_id)
    await callback.message.edit_text(
        "\u2705 Send <code>user_id</code> to unban:", reply_markup=back_to_main(), parse_mode="HTML"
    )


@dp.message(AdminState.waiting_unban_id)
async def admin_unban(message: Message, state: FSMContext):
    try:
        uid = int(message.text.strip())
    except ValueError:
        await message.answer("\u274c Invalid ID")
        return
    await db.unban_user(uid)
    await message.answer(f"\u2705 Unbanned <code>{uid}</code>.", reply_markup=admin_panel(), parse_mode="HTML")
    await state.clear()


# ─── Set Tier ───
@dp.callback_query(F.data == "admin:settier")
async def cb_settier(callback: CallbackQuery, state: FSMContext):
    if not is_admin(callback.from_user.id):
        return
    await state.set_state(AdminState.waiting_settier)
    await callback.message.edit_text(
        "\u2b50 Send: <code>user_id tier</code>\n\n"
        "Tiers: <code>free</code>, <code>premium</code>, <code>premium_plus</code>",
        reply_markup=back_to_main(), parse_mode="HTML"
    )


@dp.message(AdminState.waiting_settier)
async def admin_settier(message: Message, state: FSMContext):
    parts = message.text.strip().split()
    if len(parts) != 2 or parts[1] not in GLOBAL_USE_LIMITS:
        await message.answer("\u274c Format: <code>123456789 premium</code>", parse_mode="HTML")
        return
    try:
        uid = int(parts[0])
    except ValueError:
        await message.answer("\u274c Invalid ID")
        return
    await db.set_tier(uid, parts[1])
    await message.answer(f"\u2705 Tier set to <code>{parts[1]}</code> for <code>{uid}</code>.",
                         reply_markup=admin_panel(), parse_mode="HTML")
    await state.clear()


# ─── Broadcast ───
@dp.callback_query(F.data == "admin:broadcast")
async def cb_broadcast(callback: CallbackQuery, state: FSMContext):
    if not is_admin(callback.from_user.id):
        return
    await callback.message.edit_text(
        "\U0001f4e2 <b>Broadcast</b>\n\nChoose broadcast type:",
        reply_markup=broadcast_choice_kb(), parse_mode="HTML"
    )


@dp.callback_query(F.data == "bcast:text")
async def cb_broadcast_text(callback: CallbackQuery, state: FSMContext):
    if not is_admin(callback.from_user.id):
        return
    await state.set_state(AdminState.waiting_broadcast)
    await callback.message.edit_text(
        "\U0001f4dd Send the message to broadcast to all users:",
        reply_markup=back_to_main(), parse_mode="HTML"
    )


@dp.callback_query(F.data == "bcast:forward")
async def cb_broadcast_forward(callback: CallbackQuery, state: FSMContext):
    if not is_admin(callback.from_user.id):
        return
    await state.set_state(AdminState.waiting_fwd_broadcast)
    await callback.message.edit_text(
        "\u21a9\ufe0f <b>Forward Broadcast</b>\n\n"
        "Forward any message to me and it will be forwarded to all users.",
        reply_markup=back_to_main(), parse_mode="HTML"
    )


@dp.message(AdminState.waiting_broadcast)
async def admin_broadcast_text(message: Message, state: FSMContext):
    if not is_admin(message.from_user.id):
        return
    users = await db.get_all_users_paginated(page=0, per_page=99999)
    users = users[0]
    sent, failed, blocked = 0, 0, 0
    status = await message.answer(f"\U0001f4e2 Broadcasting to {len(users)} users...")
    for i, u in enumerate(users):
        if u['banned']:
            continue
        try:
            await bot.send_message(
                u['user_id'],
                f"\U0001f4e2 <b>AKAZA Broadcast</b>\n\n{message.text}",
                parse_mode="HTML"
            )
            sent += 1
        except TelegramBadRequest as e:
            if "blocked" in str(e).lower():
                blocked += 1
            failed += 1
        except Exception:
            failed += 1
        if (i + 1) % 20 == 0:
            try:
                await status.edit_text(
                    f"\U0001f4e2 Progress: {i+1}/{len(users)} | Sent: {sent} | Failed: {failed}"
                )
            except Exception:
                pass
    await status.edit_text(
        f"\u2705 <b>Broadcast Complete!</b>\n\n"
        f"\u2705 Sent: <code>{sent}</code>\n"
        f"\u274c Failed: <code>{failed}</code>\n"
        f"\U0001f6ab Blocked: <code>{blocked}</code>",
        reply_markup=admin_panel(), parse_mode="HTML"
    )
    await state.clear()


@dp.message(AdminState.waiting_fwd_broadcast, F.forward_from or F.forward_from_chat)
async def admin_broadcast_forward(message: Message, state: FSMContext):
    if not is_admin(message.from_user.id):
        return
    users = await db.get_all_users_paginated(page=0, per_page=99999)
    users = users[0]
    sent, failed = 0, 0
    status = await message.answer(f"\u21a9\ufe0f Forwarding to {len(users)} users...")
    for i, u in enumerate(users):
        if u['banned']:
            continue
        try:
            await message.forward(u['user_id'])
            sent += 1
        except Exception:
            failed += 1
        if (i + 1) % 20 == 0:
            try:
                await status.edit_text(f"\u21a9\ufe0f {i+1}/{len(users)} | Sent: {sent} | Failed: {failed}")
            except Exception:
                pass
    await status.edit_text(
        f"\u2705 <b>Forward Broadcast Done!</b>\n\n"
        f"\u2705 Sent: <code>{sent}</code>\n\u274c Failed: <code>{failed}</code>",
        reply_markup=admin_panel(), parse_mode="HTML"
    )
    await state.clear()


@dp.message(AdminState.waiting_fwd_broadcast)
async def admin_broadcast_fwd_wrong(message: Message):
    await message.answer("\u274c Please <b>forward</b> a message (don't send a new one).")


# ═══════════════════════════════════════════════════════════════════════════
# BACKGROUND TASKS
# ═══════════════════════════════════════════════════════════════════════════
async def hourly_validator():
    await asyncio.sleep(60)
    while True:
        try:
            logger.info("[Validator] Starting cycle...")
            sessions, total = await db.get_all_global_sessions_paginated(page=0, per_page=99999)
            cleaned, kept = 0, 0
            for sess in sessions:
                sid = sess['id']
                path = sess['file_path']
                if not os.path.exists(path):
                    await db.update_global_session_status(sid, "deleted")
                    cleaned += 1
                    continue
                res = await validate_tdata_session(path, timeout=12)
                if res.get("status") != "VALID":
                    try:
                        shutil.rmtree(path, ignore_errors=True)
                    except Exception:
                        pass
                    await db.update_global_session_status(sid, "dead")
                    cleaned += 1
                else:
                    await db.update_global_session_status(sid, "valid")
                    kept += 1
            logger.info(f"[Validator] Kept:{kept} Cleaned:{cleaned}")
        except Exception as e:
            logger.error(f"[Validator] Error: {e}")
        await asyncio.sleep(3600)


async def daily_reset_task():
    await asyncio.sleep(120)
    while True:
        try:
            now = datetime.now()
            next_reset = (now + timedelta(days=1)).replace(hour=0, minute=0, second=0, microsecond=0)
            wait_seconds = (next_reset - now).total_seconds()
            logger.info(f"[DailyReset] Waiting {wait_seconds/3600:.1f}h until midnight...")
            await asyncio.sleep(wait_seconds)
            async with aiosqlite.connect(DB_PATH) as adb:
                await adb.execute("UPDATE users SET global_uses_today=0, referral_count=0")
                await adb.commit()
            logger.info("[DailyReset] All daily limits reset!")
            await asyncio.sleep(60)
        except Exception as e:
            logger.error(f"[DailyReset] Error: {e}")
            await asyncio.sleep(300)


# ═══════════════════════════════════════════════════════════════════════════
# MAIN
# ═══════════════════════════════════════════════════════════════════════════
async def main():
    await db.init()
    await init_mtproto()
    asyncio.create_task(hourly_validator())
    asyncio.create_task(daily_reset_task())
    logger.info("\u26a1 AKAZA x Reffer starting... (MTProto 16 workers)")
    try:
        await dp.start_polling(bot)
    finally:
        global _mtproto_client
        if _mtproto_client:
            try:
                await _mtproto_client.disconnect()
            except Exception:
                pass


if __name__ == "__main__":
    try:
        asyncio.run(main())
    except (KeyboardInterrupt, SystemExit):
        logger.info("AKAZA x Reffer stopped.")
