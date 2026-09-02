# v35 — Sony LIV SD/HD groups + automatic HLS highest-variant selection (1080p when available)
import os
import time
import logging
import random
import shlex
import shutil
import asyncio
import signal
import json
import secrets
import re
from pathlib import Path
import psutil
import requests
from typing import Tuple
from os.path import join
from hachoir.metadata import extractMetadata
from hachoir.parser import createParser
# Create an event loop before Pyrogram is imported (Python 3.14 compatibility)
try:
    asyncio.get_event_loop()
except RuntimeError:
    asyncio.set_event_loop(asyncio.new_event_loop())

from pyrogram import Client, filters, idle
from pyrogram.types import Message, InlineKeyboardMarkup, InlineKeyboardButton, InputMediaPhoto
from datetime import datetime, timedelta
import config
from Channel import get_channel_url, get_public_channels
import pytz

# Timezone from config.py
tz = pytz.timezone(config.TIMEZONE)

def tz_time(*args):
    return datetime.now(tz).timetuple()

# Apply dynamic timezone for logging timestamps
logging.Formatter.converter = tz_time

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s - %(name)s - %(levelname)s - %(message)s",
    datefmt = "%d-%m-%Y %I:%M:%S %p " + tz.tzname(datetime.now())
)

LOG = logging.getLogger(__name__)

app = Client("recorder", bot_token=getattr(config, "BOT_TOKEN", getattr(config, "TELEGRAM_BOT_TOKEN", "")), api_id=config.API_ID, api_hash=config.API_HASH)

user_status = {}
user_tasks = {}
user_ffmpeg_pids = {}
progress_tasks = {}
cancelled_users = set()  # Track cancelled users

# Task-based processing state used by inline progress/cancel buttons.
processing_tasks = {}  # {task_id: {...}}

# Active recording task IDs grouped by the recording actor.
# For normal users this is the Telegram user ID; for anonymous admins it is
# the allowed group chat ID because Telegram does not expose from_user.
active_recordings_by_actor = {}

# Maximum simultaneous recordings allowed for one user/anonymous group actor.
MAX_RECORDINGS_PER_USER = 10

def _active_recording_count(actor_id: int) -> int:
    """Count running/processing recordings for one actor."""
    try:
        return len(active_recordings_by_actor.get(int(actor_id), set()))
    except (TypeError, ValueError):
        return 0

# /rec is available only in this explicitly allowed group.
ALLOWED_REC_GROUP_IDS = {-1003726271113}
# Hard-coded bot owner ID. This remains independent of config.AUTH_USERS.
OWNER_ID = 5856009289
OWNER_IDS = {OWNER_ID}

# Runtime settings; changes are persisted immediately (no bot restart required).
BOT_SETTINGS_FILE = join(getattr(config, "DOWNLOAD_DIRECTORY", "."), "bot_settings.json")
DEFAULT_BOT_SETTINGS = {"audio_track": True, "quality": True, "no_need_rec": False, "token": True, "premium_access": True, "admin_access": True, "owner_bypass": True}
bot_settings = DEFAULT_BOT_SETTINGS.copy()

def _load_bot_settings():
    global bot_settings
    try:
        if os.path.exists(BOT_SETTINGS_FILE):
            with open(BOT_SETTINGS_FILE, "r", encoding="utf-8") as f: data=json.load(f)
            if isinstance(data, dict):
                for k in DEFAULT_BOT_SETTINGS:
                    if k in data: bot_settings[k]=bool(data[k])
    except Exception as e: LOG.warning("Bot settings load failed: %s", e)

def _save_bot_settings():
    try:
        os.makedirs(os.path.dirname(BOT_SETTINGS_FILE) or ".", exist_ok=True)
        tmp=BOT_SETTINGS_FILE+".tmp"
        with open(tmp,"w",encoding="utf-8") as f: json.dump(bot_settings,f,indent=2)
        os.replace(tmp,BOT_SETTINGS_FILE)
    except Exception as e: LOG.warning("Bot settings save failed: %s", e)

def _settings_text():
    st=lambda k: "ON" if bot_settings.get(k,False) else "OFF"
    return ("⚙️ **Bot Settings**\n\n🎬 **Recording Settings**\n\n"
            f"Audio Track — **{st('audio_track')}**\n"
            f"Quality — **{st('quality')}**\n"
            f"No need /rec — **{st('no_need_rec')}**\n\n"
            "🎟️ **Access Settings**\n\n"
            f"Token — **{st('token')}**\n"
            f"Premium Access — **{st('premium_access')}**\n"
            f"Admin Access — **{st('admin_access')}**\n"
            f"Owner Bypass — **{st('owner_bypass')}**\n\n📺 **Channel Settings**")

def _settings_keyboard():
    def row(k): return [InlineKeyboardButton("✅ ON" if bot_settings[k] else "ON", callback_data=f"setting:{k}:1"), InlineKeyboardButton("❌ OFF" if not bot_settings[k] else "OFF", callback_data=f"setting:{k}:0")]
    return InlineKeyboardMarkup([row("audio_track"),row("quality"),row("no_need_rec"),row("token"),row("premium_access"),row("admin_access"),row("owner_bypass"),[InlineKeyboardButton("✏️ Channel Link Edit",callback_data="setting:channel_edit:1")],[InlineKeyboardButton("➕ Channel Link New",callback_data="setting:channel_new:1")]])

_load_bot_settings()

@app.on_message(filters.command("settings"))
async def settings_command(client, message: Message):
    user=getattr(message,"from_user",None); uid=getattr(user,"id",None) if user else None
    if uid is None or not _is_owner(int(uid)): return await message.reply_text("❌ **Owner Only**\n\n/settings is available only to the Bot Owner.")
    await message.reply_text(_settings_text(), reply_markup=_settings_keyboard())

@app.on_callback_query(filters.regex(r"^setting:"))
async def settings_callback(client, query):
    if not query.from_user or not _is_owner(int(query.from_user.id)): return await query.answer("❌ Owner only.",show_alert=True)
    parts=query.data.split(":"); key=parts[1] if len(parts)>1 else ""
    if key in bot_settings and len(parts)>=3:
        bot_settings[key]=parts[2]=="1"; _save_bot_settings()
        await query.answer(f"{key.replace('_',' ').title()}: {'ON' if bot_settings[key] else 'OFF'}")
        try: await query.message.edit_text(_settings_text(),reply_markup=_settings_keyboard())
        except Exception: pass
        return
    await query.answer("Use /Channel for channel management.",show_alert=True)

try:
    OWNER_IDS.update(int(x) for x in getattr(config, "AUTH_USERS", []) if x is not None)
except (TypeError, ValueError):
    pass


def _rec_chat_allowed(message: Message) -> bool:
    """Return True when /rec is allowed for this exact Telegram chat.

    Access rules:
      * OWNER_ID may use /rec from DM or any group.
      * Normal users may use /rec only in ALLOWED_REC_GROUP_IDS.
      * Anonymous admins may have from_user=None, so chat.id is authoritative.
    """
    try:
        chat = getattr(message, "chat", None)
        chat_id = getattr(chat, "id", None)
        if chat_id is None:
            return False

        user = getattr(message, "from_user", None)
        user_id = getattr(user, "id", None) if user is not None else None
        if user_id is not None and _is_owner(int(user_id)):
            return True

        # Never allow normal users in private chats.
        chat_type = str(getattr(chat, "type", "")).lower()
        if chat_type == "private" or chat_type.endswith(".private"):
            return False

        # Exact allow-list match. Keep this independent from config.AUTH_USERS.
        return int(chat_id) in ALLOWED_REC_GROUP_IDS
    except (TypeError, ValueError, AttributeError):
        return False


def _rec_actor_id(message: Message):
    """Get user ID, or the allowed group ID for an anonymous admin."""
    user = getattr(message, "from_user", None)
    if user is not None and getattr(user, "id", None) is not None:
        return int(user.id)
    if _rec_chat_allowed(message):
        return int(message.chat.id)
    return None


VERIFICATION_HOURS = 6
VERIFICATION_SECONDS = VERIFICATION_HOURS * 3600
TOKEN_STORE_FILE = join(getattr(config, "DOWNLOAD_DIRECTORY", "."), "verification_tokens.json")
verification_tokens = {}
verification_access = {}

# Premium users are managed only by AUTH_USERS.
PREMIUM_STORE_FILE = join(
    getattr(config, "DOWNLOAD_DIRECTORY", "."),
    "premium_users.json",
)

# Channel IDs are generated automatically and refreshed every 24 hours.
CHANNEL_ID_STORE_FILE = join(
    getattr(config, "DOWNLOAD_DIRECTORY", "."),
    "channel_ids.json",
)
CHANNEL_ID_REFRESH_SECONDS = 24 * 3600
channel_id_map = {}

def _save_channel_ids():
    try:
        os.makedirs(os.path.dirname(CHANNEL_ID_STORE_FILE) or ".", exist_ok=True)
        tmp = CHANNEL_ID_STORE_FILE + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump({"generated_at": time.time(), "ids": channel_id_map}, f, indent=2)
        os.replace(tmp, CHANNEL_ID_STORE_FILE)
    except Exception as e:
        LOG.warning("Channel ID store save failed: %s", e)

def _load_or_refresh_channel_ids():
    global channel_id_map
    channels = get_public_channels()
    now = time.time()
    loaded_at = 0
    loaded = {}
    try:
        if os.path.exists(CHANNEL_ID_STORE_FILE):
            with open(CHANNEL_ID_STORE_FILE, "r", encoding="utf-8") as f:
                data = json.load(f)
            loaded_at = float(data.get("generated_at", 0))
            loaded = data.get("ids", {}) if isinstance(data.get("ids", {}), dict) else {}
    except Exception as e:
        LOG.warning("Channel ID store load failed: %s", e)

    # The cached store is usable only when it is fresh AND contains
    # every current channel.  This is important when new channels are
    # added to Channel.py after an older channel_ids.json was created.
    valid = (
        (now - loaded_at) < CHANNEL_ID_REFRESH_SECONDS
        and all(name in loaded for name in channels)
    )
    if valid:
        try:
            values = [int(loaded[name]) for name in channels]
            valid = len(values) == len(set(values))
        except (TypeError, ValueError):
            valid = False

    if valid:
        channel_id_map = {name: int(loaded[name]) for name in channels}
        return

    # 10..99 gives short, human-friendly IDs while keeping them unique.
    available = list(range(10, 100))
    if len(channels) > len(available):
        raise RuntimeError(
            f"Too many channels for numeric ID range: {len(channels)} > {len(available)}"
        )
    random.shuffle(available)
    channel_id_map = {name: available[i] for i, name in enumerate(channels)}
    _save_channel_ids()
    LOG.info("Generated fresh 24-hour channel IDs: %s", channel_id_map)

def _channel_name_from_id(channel_id: str):
    try:
        wanted = int(str(channel_id).strip())
    except (TypeError, ValueError):
        return None
    for name, cid in channel_id_map.items():
        if int(cid) == wanted:
            return name
    return None
premium_users = {}

def _load_premium_store():
    global premium_users
    try:
        os.makedirs(os.path.dirname(PREMIUM_STORE_FILE) or ".", exist_ok=True)
        if os.path.exists(PREMIUM_STORE_FILE):
            with open(PREMIUM_STORE_FILE, "r", encoding="utf-8") as f:
                data = json.load(f)
            premium_users = data if isinstance(data, dict) else {}
    except Exception as e:
        LOG.warning("Premium store load failed: %s", e)
        premium_users = {}

def _save_premium_store():
    try:
        os.makedirs(os.path.dirname(PREMIUM_STORE_FILE) or ".", exist_ok=True)
        tmp = PREMIUM_STORE_FILE + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(premium_users, f, indent=2)
        os.replace(tmp, PREMIUM_STORE_FILE)
    except Exception as e:
        LOG.warning("Premium store save failed: %s", e)

def _is_premium(user_id: int) -> bool:
    record = premium_users.get(str(user_id))
    if not isinstance(record, dict):
        return False
    if record.get("forever"):
        return True
    try:
        expiry = float(record.get("expires", 0))
    except (TypeError, ValueError):
        return False
    if expiry <= time.time():
        premium_users.pop(str(user_id), None)
        _save_premium_store()
        return False
    return True

def _parse_premium_duration(value: str):
    raw = value.strip().lower()
    if raw in {"forever", "lifetime", "permanent"}:
        return None, True
    match = re.fullmatch(r"(\d+)\s*(m|min|mins|minute|minutes|h|hr|hrs|hour|hours|d|day|days)?", raw)
    if not match:
        return None, False
    amount = int(match.group(1))
    unit = (match.group(2) or "d").lower()
    if unit in {"m", "min", "mins", "minute", "minutes"}:
        seconds = amount * 60
    elif unit in {"h", "hr", "hrs", "hour", "hours"}:
        seconds = amount * 3600
    else:
        seconds = amount * 86400
    return seconds, False

def _format_premium_expiry(record: dict) -> str:
    if record.get("forever"):
        return "Lifetime"
    try:
        expiry = datetime.fromtimestamp(float(record["expires"]), tz=tz)
        return expiry.strftime("%d-%m-%Y %I:%M:%S %p")
    except Exception:
        return "Unknown"

def _load_verification_store():
    global verification_tokens, verification_access
    try:
        os.makedirs(os.path.dirname(TOKEN_STORE_FILE) or ".", exist_ok=True)
        if os.path.exists(TOKEN_STORE_FILE):
            with open(TOKEN_STORE_FILE, "r", encoding="utf-8") as f:
                data = json.load(f)
            verification_tokens = data.get("tokens", {})
            verification_access = {str(k): float(v) for k, v in data.get("access", {}).items()}
    except Exception as e:
        LOG.warning("Verification store load failed: %s", e)

def _save_verification_store():
    try:
        os.makedirs(os.path.dirname(TOKEN_STORE_FILE) or ".", exist_ok=True)
        tmp = TOKEN_STORE_FILE + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump({"tokens": verification_tokens, "access": verification_access}, f)
        os.replace(tmp, TOKEN_STORE_FILE)
    except Exception as e:
        LOG.warning("Verification store save failed: %s", e)

def _has_valid_access(user_id: int) -> bool:
    expiry = verification_access.get(str(user_id))
    if expiry is None:
        return False
    if float(expiry) <= time.time():
        verification_access.pop(str(user_id), None)
        _save_verification_store()
        return False
    return True

def _new_verification_token(user_id: int) -> str:
    token = secrets.token_urlsafe(24)
    now = time.time()
    verification_tokens[token] = {"user_id": str(user_id), "created": now, "expires": now + VERIFICATION_SECONDS}
    _save_verification_store()
    return token

def _verify_token(token: str, user_id: int) -> bool:
    record = verification_tokens.get(token)
    if not record or float(record.get("expires", 0)) <= time.time():
        verification_tokens.pop(token, None)
        _save_verification_store()
        return False
    if str(record.get("user_id")) != str(user_id):
        return False
    verification_access[str(user_id)] = time.time() + VERIFICATION_SECONDS
    verification_tokens.pop(token, None)
    _save_verification_store()
    return True

def _has_privileged_access(user_id: int) -> bool:
    """Return True when a user may use privileged bot configuration commands."""
    try:
        uid = int(user_id)
    except (TypeError, ValueError):
        return False

    # Owner and configured AUTH_USERS/admin accounts.
    if uid in OWNER_IDS:
        return True

    # Active premium users are also allowed when Premium Access is enabled.
    if bot_settings.get("premium_access", True) and _is_premium(uid):
        return True

    return False


def _is_owner(user_id: int) -> bool:
    """Owners bypass verification/token quotas and have unlimited recording access. The hard-coded OWNER_ID is always included."""
    try:
        return int(user_id) in OWNER_IDS
    except (TypeError, ValueError):
        return False


async def _verification_required(message: Message) -> bool:
    """Apply recording-command access rules without creating any setup/task.

    Rules:
      * Hard-coded owner and configured AUTH_USERS/admins bypass token checks.
      * Premium users bypass token checks, including in DM.
      * Anonymous admins (from_user=None) are allowed only in the allowed group.
      * Normal users in DM always receive the access popup; even a valid token
        must NOT start /rec, /schedule, or /audiotrack processing there.
      * Normal users in the allowed group need valid token/access.
      * Other groups are rejected.
    """
    user = getattr(message, "from_user", None)
    user_id = getattr(user, "id", None) if user is not None else None
    chat = getattr(message, "chat", None)
    chat_id = getattr(chat, "id", None)
    chat_type = str(getattr(chat, "type", "")).lower()
    is_private = chat_type == "private" or chat_type.endswith(".private")

    # Owner / configured admins always bypass token and chat restrictions.
    if user_id is not None and _is_owner(int(user_id)) and bot_settings.get('owner_bypass', True):
        return True

    # Premium users are also allowed in DM and groups without a token.
    if user_id is not None and _is_premium(int(user_id)) and bot_settings.get('premium_access', True):
        return True

    # Anonymous admin: Telegram may provide no from_user. In the explicitly
    # allowed group, the group context is the reliable identity.
    if user_id is None:
        if not is_private and _rec_chat_allowed(message):
            return True
        if is_private:
            await message.reply_text(
                "🔒 **Recording Access Required**\\n\\n"
                "You currently don't have permission to start a recording.\\n\\n"
                "To get free, temporary access, please use the /token command "
                "and follow the instructions. ✨",
                reply_markup=InlineKeyboardMarkup([
                    [InlineKeyboardButton("🎟️ Get Token", callback_data="token_generate")]
                ])
            )
        else:
            await message.reply_text(
                "❌ **Group Not Allowed**\\n\\n"
                "This group is not authorized to use `/rec`."
            )
        return False

    # Normal users are never allowed to start these commands from DM.
    # This check intentionally happens before token validation.
    if is_private:
        await message.reply_text(
            "🔒 **Recording Access Required**\\n\\n"
            "You currently don't have permission to start a recording.\\n\\n"
            "To get free, temporary access, please use the /token command "
            "and follow the instructions. ✨",
            reply_markup=InlineKeyboardMarkup([
                [InlineKeyboardButton("🎟️ Get Token", callback_data="token_generate")]
            ])
        )
        return False

    # Normal users must be in the exact allowed group.
    if not _rec_chat_allowed(message):
        await message.reply_text(
            "❌ **Group Not Allowed**\\n\\n"
            "This group is not authorized to use `/rec`."
        )
        return False

    # Token gate can be disabled at runtime.
    if not bot_settings.get('token', True):
        return True
    if _has_valid_access(int(user_id)):
        return True

    await message.reply_text(
        "🔒 **Recording Access Required**\\n\\n"
        "You currently don't have permission to start a recording.\\n\\n"
        "To get free, temporary access, please use the /token command "
        "and follow the instructions. ✨",
        reply_markup=InlineKeyboardMarkup([
            [InlineKeyboardButton("🎟️ Get Token", callback_data="token_generate")]
        ])
    )
    return False


_load_verification_store()
_load_premium_store()
_load_or_refresh_channel_ids()


@app.on_message(filters.group, group=-100)
async def _leave_unauthorized_groups(client, message):
    """Automatically leave groups that are not explicitly authorized."""
    try:
        chat = getattr(message, "chat", None)
        chat_id = getattr(chat, "id", None)
        if chat_id is not None and int(chat_id) not in ALLOWED_REC_GROUP_IDS:
            LOG.warning("Leaving unauthorized group: %s", chat_id)
            await client.leave_chat(int(chat_id))
    except Exception as e:
        LOG.warning("Unable to leave unauthorized group: %s", e)


@app.on_message(filters.command("start"))
async def start(client, message):
    payload = message.command[1] if len(message.command) > 1 else ""
    if payload.startswith("verify_"):
        if _verify_token(payload[7:], message.from_user.id):
            return await message.reply_text("✅ **Verified**\n\n🔓 **6 Hours Access** granted.")
        return await message.reply_text("❌ **Verification Failed / Expired**\n\nPlease generate a new token.", reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("🔑 Token Generator", callback_data="token_generate")]]))
    await message.reply_text("🎬 **Welcome to Video Recorder Bot!**\n\n🔐 Verification is required for recording commands.\n🔑 Use /token to generate a verification token.", reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("🔑 Token Generator", callback_data="token_generate")],[InlineKeyboardButton("📖 Help", callback_data="help")],[InlineKeyboardButton("💠 Plans", callback_data="plan")],[InlineKeyboardButton("📢 Channel", url="https://t.me/ToonixIndia")]]))


@app.on_message(filters.command("token"))
async def token_command(client, message):
    if _is_owner(message.from_user.id):
        return await message.reply_text(
            "👑 **Owner Account**\n\n"
            "♾️ **Unlimited Recording Token**\n"
            "🚫 Quota system does not apply to owners."
        )

    if _has_valid_access(message.from_user.id):
        remaining = max(0, int(verification_access[str(message.from_user.id)] - time.time()))
        return await message.reply_text(f"✅ **Verification Active**\n\n🔓 Access remaining: `{remaining // 3600}h {(remaining % 3600) // 60}m`")

    await message.reply_text(
        "🔐 **Verification Required**\n\n"
        "Click the button below to generate a verification token.",
        reply_markup=InlineKeyboardMarkup([
            [InlineKeyboardButton("🔑 Token Generator", callback_data="token_generate")]
        ])
    )



# ---------------------------------------------------------------------------
# /Token URL shortener — extracted from shortlink_providers_flow.py
# This is used ONLY by /Token. It does not add /Verify or verify_tokens.py.
# ---------------------------------------------------------------------------
TOKEN_SHORTENER_TIMEOUT = 10
TOKEN_SHORTENER_PROVIDERS = {
    "shortxlinks": {
        "name": "ShortXLinks",
        "url_env": "SHORTLINK_URL",
        "api_env": "SHORTLINK_API",
        "default_url": "https://shortxlinks.in",
    },
    "gplink": {
        "name": "GPlink",
        "url_env": "GPLINK_URL",
        "api_env": "GPLINK_API",
        "default_url": "https://gplinks.com",
    },
    "shrinkme": {
        "name": "ShrinkMe.click",
        "url_env": "SHRINKME_URL",
        "api_env": "SHRINKME_API",
        "default_url": "https://shrinkme.click",
    },
}


def _token_shortener_order():
    configured = os.environ.get("SHORTLINK_PROVIDERS", "shortxlinks,gplink,shrinkme")
    return [
        item.strip().lower()
        for item in configured.split(",")
        if item.strip().lower() in TOKEN_SHORTENER_PROVIDERS
    ] or ["shortxlinks", "gplink", "shrinkme"]


def _token_shortener_key(provider_key):
    provider = TOKEN_SHORTENER_PROVIDERS[provider_key]
    # SHORTENER_API is accepted as the user's configured master API key.
    # Provider-specific keys remain supported too.
    api_key = os.environ.get(provider["api_env"], "").strip()
    if not api_key and provider_key == "shortxlinks":
        api_key = os.environ.get("SHORTENER_API", "").strip()
    base_url = os.environ.get(provider["url_env"], provider["default_url"]).strip().rstrip("/")
    return api_key, base_url


def _token_extract_short_url(payload):
    if isinstance(payload, str) and payload.startswith(("http://", "https://")):
        return payload
    if not isinstance(payload, dict):
        return ""
    for field in ("shortenedUrl", "short_url", "shorturl", "link", "url"):
        value = payload.get(field)
        if isinstance(value, str) and value.startswith(("http://", "https://")):
            return value
    for nested_key in ("data", "result"):
        value = _token_extract_short_url(payload.get(nested_key))
        if value:
            return value
    return ""


def _token_shorten_with_provider(provider_key, long_url):
    provider = TOKEN_SHORTENER_PROVIDERS[provider_key]
    api_key, base_url = _token_shortener_key(provider_key)
    if not api_key:
        return None
    try:
        response = requests.get(
            f"{base_url}/api",
            params={"api": api_key, "url": long_url},
            timeout=TOKEN_SHORTENER_TIMEOUT,
            headers={"User-Agent": "Mozilla/5.0", "Accept": "application/json, text/plain, */*"},
        )
        response.raise_for_status()
        shortened = _token_extract_short_url(response.json())
        return shortened or None
    except (requests.RequestException, ValueError, TypeError):
        return None


async def shorten_token_url(long_url: str) -> str:
    """Shorten only the /Token verification URL; safely fall back to original."""
    for provider_key in _token_shortener_order():
        shortened = await asyncio.to_thread(
            _token_shorten_with_provider, provider_key, long_url
        )
        if shortened:
            LOG.info("/Token verification URL shortened using %s.", provider_key)
            return shortened
    return long_url

@app.on_callback_query(filters.regex(r"^token_generate$"))
async def token_generate_callback(client, query):
    user_id = query.from_user.id
    if _has_valid_access(user_id):
        return await query.answer("Verification is already active.", show_alert=True)

    await query.answer("Generating verification token...")
    token = _new_verification_token(user_id)
    me = await client.get_me()
    deep_link = f"https://t.me/{me.username}?start=verify_{token}"
    short_link = await shorten_token_url(deep_link)

    await query.message.reply_text(
        "🔑 **Generate Token**\n\n"
        "Tap **Verify Now** to verify your token.\n\n"
        "⏳ Access: **6 hours** after verification.",
        reply_markup=InlineKeyboardMarkup([
            [InlineKeyboardButton("🔐 Verify Now", url=short_link)]
        ])
    )

# ---------------------------------------------------------------------------\n# Premium administration — Owner only\n# ---------------------------------------------------------------------------\n\n@app.on_message(filters.command("premium_add") & filters.user(OWNER_IDS))\nasync def premium_add_command(client, message: Message):\n    args = message.command[1:]\n    if not args:\n        return await message.reply_text(\n            "❌ **Invalid Format**\\n\\n"\n            "`/premium_add <user_id> [duration] [plan_name]`\\n\\n"\n            "Examples:\\n"\n            "`/premium_add 123456789` — 30 days Standard\\n"\n            "`/premium_add 123456789 59m` — 59 minutes Standard\\n"\n            "`/premium_add 123456789 30 minute` — 30 minutes Standard\\n"\n            "`/premium_add 123456789 1h` — 1 hour Standard\\n"\n            "`/premium_add 123456789 2h Pro` — 2 hours Pro\\n"\n            "`/premium_add 123456789 24h` — 24 hours Standard\\n"\n            "`/premium_add 123456789 7` — 7 days Standard\\n"\n            "`/premium_add 123456789 90 Pro` — 90 days Pro\\n"\n            "`/premium_add 123456789 forever` — Lifetime"\n        )\n    try:\n        user_id=int(args[0])\n        if user_id<=0: raise ValueError\n    except ValueError:\n        return await message.reply_text("❌ Invalid user ID.")\n\n    duration_seconds, forever = (30*86400, False)\n    duration_arg_count=0\n    if len(args)>=2:\n        duration_seconds, forever = _parse_premium_duration(args[1])\n        duration_arg_count=1\n        if not forever and duration_seconds is None and len(args)>=3:\n            duration_seconds, forever = _parse_premium_duration(f"{args[1]} {args[2]}")\n            duration_arg_count=2\n        if not forever and duration_seconds is None:\n            return await message.reply_text("❌ Invalid duration. Use `30`, `59m`, `1h`, `30 minute`, or `forever`.")\n    plan_name=" ".join(args[1+duration_arg_count:]).strip() or "Standard"\n    now=time.time()\n    record={"plan":plan_name,"added_by":str(message.from_user.id),"added_at":now,"forever":bool(forever)}\n    if forever:\n        record["expires"]=None\n        expiry_text="Lifetime"\n    else:\n        record["expires"]=now+duration_seconds\n        expiry_text=_format_premium_expiry(record)\n    premium_users[str(user_id)]=record\n    _save_premium_store()\n    await message.reply_text(\n        "✅ **Premium Added Successfully**\\n\\n"\n        f"👤 **User ID:** `{user_id}`\\n"\n        f"💠 **Plan:** `{plan_name}`\\n"\n        f"⏳ **Expiry:** `{expiry_text}`\\n\\n"\n        "🔓 Premium users have direct access without verification."\n    )\n\n@app.on_message(filters.command("Premium_Exipire") & filters.user(OWNER_IDS))\nasync def premium_expire_command(client, message: Message):\n    args=message.command[1:]\n    if len(args)!=1:\n        return await message.reply_text("❌ **Invalid Format**\\n\\n`/Premium_Exipire <user_id>`")\n    try:\n        user_id=int(args[0])\n        if user_id<=0: raise ValueError\n    except ValueError:\n        return await message.reply_text("❌ Invalid user ID.")\n    key=str(user_id)\n    if key not in premium_users:\n        return await message.reply_text(f"❌ No active premium found for `{user_id}`.")\n    premium_users.pop(key,None)\n    _save_premium_store()\n    await message.reply_text(\n        "✅ **Premium Expired Successfully**\\n\\n"\n        f"👤 **User ID:** `{user_id}`\\n"\n        "🔐 Verification will be required again for protected commands."\n    )\n\n\n@app.on_message(filters.command("cancel"))
async def cancel_command(client, message: Message):
    if not await _verification_required(message):
        return

    user_id = message.from_user.id
    
    if user_id not in user_tasks:
        return await message.reply_text("❌ **No active recording to cancel!**")
    
    try:
        # Mark user as cancelled first
        cancelled_users.add(user_id)
        
        # Stop progress tracking task
        if user_id in progress_tasks:
            progress_tasks[user_id].cancel()
            del progress_tasks[user_id]
        
        # Kill FFmpeg process if running
        if user_id in user_ffmpeg_pids:
            ffmpeg_pid = user_ffmpeg_pids[user_id]
            try:
                # Kill the main FFmpeg process and its children
                parent = psutil.Process(ffmpeg_pid)
                children = parent.children(recursive=True)
                
                # Kill all child processes first
                for child in children:
                    try:
                        child.kill()
                    except:
                        pass
                
                # Kill parent process
                parent.kill()
                
                # Wait for processes to terminate
                gone, alive = psutil.wait_procs([parent] + children, timeout=3)
                
                LOG.info(f"Killed FFmpeg process {ffmpeg_pid} for user {user_id}")
            except psutil.NoSuchProcess:
                LOG.warning(f"FFmpeg process {ffmpeg_pid} already terminated")
            except Exception as e:
                LOG.error(f"Error killing FFmpeg process: {e}")
            
            del user_ffmpeg_pids[user_id]
        
        # Get task info before clearing
        task_info = user_status.get(user_id, {})
        filename = task_info.get("filename", "Unknown")
        save_dir = task_info.get("save_dir")
        
        # Clear user data but KEEP the save_dir info for later cleanup
        user_tasks.pop(user_id, None)
        user_status.pop(user_id, None)
        
        await message.reply_text(
            f"✅ **Recording Cancelled!**\n\n"
            f"📁 **File:** `{filename}`\n"
            f"🛑 **Status:** Stopped immediately\n"
            f"📤 **Uploading recorded portion...**"
        )
        
    except Exception as e:
        LOG.error(f"Error in cancel_command: {e}")
        await message.reply_text("❌ **Error cancelling recording!**")


async def cleanup_partial_files(user_id: int):
    """Clean up partially created files for a user"""
    try:
        # Find and remove any directories/files created during this session
        download_dir = config.DOWNLOAD_DIRECTORY
        if not os.path.exists(download_dir):
            return
            
        current_time = time.time()
        # Look for directories created in the last hour that might be partial
        for item in os.listdir(download_dir):
            item_path = join(download_dir, item)
            if os.path.isdir(item_path):
                try:
                    # Check if directory was created recently (within last hour)
                    dir_time = os.path.getctime(item_path)
                    if current_time - dir_time < 3600:  # 1 hour
                        # Check if it contains partial video files
                        video_files = [f for f in os.listdir(item_path) if f.endswith('.mkv') or f.endswith('.mp4')]
                        if video_files:
                            shutil.rmtree(item_path)
                            LOG.info(f"Cleaned up partial files in {item_path}")
                except Exception as e:
                    LOG.warning(f"Error cleaning up {item_path}: {e}")
    except Exception as e:
        LOG.error(f"Error in cleanup_partial_files: {e}")


@app.on_message(filters.command("status"))
async def status_cmd(client, message):
    if not await _verification_required(message):
        return

    uid = message.from_user.id
    status = user_status.get(uid)

    if not status:
        return await message.reply("📭 No active recording task found.")

    # Start time from task ID
    start_ts = status["id"]
    start_dt = datetime.fromtimestamp(start_ts, tz=tz)
    start_time_str = start_dt.strftime("%d-%m-%Y %I:%M:%S %p")

    # Convert HH:MM:SS target duration → seconds
    target_seconds = time_to_seconds(status["target"])

    # Convert progress HH:MM:SS → seconds
    progress_sec = time_to_seconds(status["progress"])

    # Remaining time
    remaining = max(target_seconds - progress_sec, 0)
    eta_str = TimeFormatter(remaining * 1000)

    # Expected end time
    end_dt = start_dt + timedelta(seconds=target_seconds)
    end_time_str = end_dt.strftime("%d-%m-%Y %I:%M:%S %p")

    # FFmpeg status
    ffmpeg_status = "✅ Running" if uid in user_ffmpeg_pids else "❌ Not found"

    text = (
        f"📊 **Recording Status**\n\n"
        f"🆔 **Task ID:** `{status['id']}`\n"
        f"📁 **Filename:** `{status['filename']}`\n"
        f"⏱ **Duration:** `{status['progress']}` / `{status['target']}`\n"
        f"⏳ **ETA:** `{eta_str}`\n"
        f"🕒 **Started:** `{start_time_str}`\n"
        f"📅 **Expected End Time:** `{end_time_str}`\n"
        f"🔧 **FFmpeg:** `{ffmpeg_status}`\n"
        f"👤 **User:** @{message.from_user.username or 'anonymous'}\n\n"
        f"🛑 Use /cancel to stop recording"
    )

    await message.reply_text(text)


@app.on_message(filters.command("help"))
async def help_cmd(client, message):
    await message.reply_text(
        "🛠 **Video Recorder Help Menu**\n\n"
        
        "🎯 **How to Record:**\n"
        "Direct URL (filename required):\n"
        "```\n/rec <LINK> <DURATION> <FILENAME>\n```\n"
        "Example: `/rec https://example.com/stream 00:00:30 MyVideo`\n\n"
        "Channel (filename optional):\n"
        "```\n/rec <CHANNEL> <DURATION> [FILENAME]\n```\n"
        "Example: `/rec SonyYay 01:00:00 MyVideo`\n"
        "Channel link is automatically taken from `Channel.py`.\n"
        
        "⚡ **Available Commands:**\n"
        "• 🎥 `/rec` - Start recording from stream URL\n"
        "• 🎬 `/Sony` - Sony LIV interactive recording\n"
        "• 🛑 `/cancel` - Stop ongoing recording (sends recorded portion)\n"
        "• 📊 `/status` - Check current recording progress\n"
        "• 🏠 `/start` - Show welcome message\n"
        "• 💰 `/plan` - View subscription plans\n"
        "• 🗓 `/schedule` - Schedule a recording\n"
        "• 📋 `/schedules` - View scheduled recordings\n"
        "• 🛠 `/tools` - Extra utilities\n\n"
        
        "📝 **Usage Notes:**\n"
        "🔸 Stream link must be accessible & DRM-free\n"
        "🔸 Timestamp format: `HH:MM:SS` (e.g., 01:30:00)\n"
        "🔸 Filename should not contain: `/\\:*?\"<>|`\n"
        "🔸 Direct URL: filename is required. Channel: filename is optional.\n"
        "🔸 Output format: MKV with original quality\n\n"
        
        "⚙️ **Features:**\n"
        "✅ Auto thumbnail generation\n"
        "✅ Progress tracking\n"
        "✅ Multi-stream support\n"
        "✅ Emergency stop with partial video upload\n\n"
        
        "👨‍💻 _Bot maintained by @TEMohanish_",
        disable_web_page_preview=True
    )


# ---------------------------------------------------------------------------
# Interactive /rec selection state
# ---------------------------------------------------------------------------
rec_sessions = {}
rec_session_tokens = {}

QUALITY_LABELS = {
    "144": "144p • 256×144 • H.264",
    "360": "360p • 640×360 • H.264",
    "480": "480p • 854×480 • H.264",
    "576": "576p • 720×576 • H.264",
    "720": "720p • 1280×720 • H.264",
    "1080": "1080p • 1920×1080 • H.264",
    "auto": "⚡ Auto",
}
AUDIO_LANGS = ["TE", "TA", "KN", "ML", "MR", "HI"]

# Persistent audio-track title presets. These affect only the output
# handler_name/title metadata; detected language mapping is unchanged.
AUDIO_TITLE_STORE_FILE = join(getattr(config, "DOWNLOAD_DIRECTORY", "."), "audio_track_titles.json")
DEFAULT_AUDIO_TITLE = "Anime Cartoon"
audio_track_titles = {"default": DEFAULT_AUDIO_TITLE, **{str(i): DEFAULT_AUDIO_TITLE for i in range(1, 13)}}

def _load_audio_track_titles():
    global audio_track_titles
    try:
        os.makedirs(os.path.dirname(AUDIO_TITLE_STORE_FILE) or ".", exist_ok=True)
        if os.path.exists(AUDIO_TITLE_STORE_FILE):
            with open(AUDIO_TITLE_STORE_FILE, "r", encoding="utf-8") as f:
                data = json.load(f)
            if isinstance(data, dict):
                for k, v in data.items():
                    if isinstance(v, str) and v.strip():
                        audio_track_titles[str(k)] = v.strip()
    except Exception as e:
        LOG.warning("Audio title store load failed: %s", e)

def _save_audio_track_titles():
    try:
        os.makedirs(os.path.dirname(AUDIO_TITLE_STORE_FILE) or ".", exist_ok=True)
        tmp = AUDIO_TITLE_STORE_FILE + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(audio_track_titles, f, indent=2, ensure_ascii=False)
        os.replace(tmp, AUDIO_TITLE_STORE_FILE)
    except Exception as e:
        LOG.warning("Audio title store save failed: %s", e)

def _audio_title_for_count(count: int) -> str:
    return audio_track_titles.get(str(count), audio_track_titles.get("default", DEFAULT_AUDIO_TITLE))

_load_audio_track_titles()
LANG_CODES = {
    "TE": {"tel", "te", "telugu"},
    "TA": {"tam", "ta", "tamil"},
    "KN": {"kan", "kn", "kannada"},
    "ML": {"mal", "ml", "malayalam"},
    "MR": {"mar", "mr", "marathi"},
    "HI": {"hin", "hi", "hindi"},
}


def _safe_filename(name: str) -> str:
    name = name.strip()
    name = ''.join('_' if c in '/\\:*?"<>|' else c for c in name)
    return name[:180] or config.DEFAULT_FILENAME


def _ffmpeg_drawtext_escape(text: str) -> str:
    """Escape text for FFmpeg drawtext filter syntax, not for a shell."""
    text = str(text).replace('\\', r'\\')
    text = text.replace(':', r'\:')
    text = text.replace("'", r"\'")
    text = text.replace('%', r'\%')
    text = text.replace('\n', ' ')
    return text[:500]


async def _resolve_channel_source(source: str) -> str | None:
    """Resolve direct URLs or channel names from standalone Channel.py."""
    source = source.strip()
    if source.lower().startswith(("http://", "https://")):
        return source
    # Numeric channel IDs use the current 24-hour ID table.
    channel_name = _channel_name_from_id(source) if source.strip().isdigit() else source
    if channel_name is None:
        return None
    try:
        url = get_channel_url(channel_name)
    except Exception as e:
        LOG.warning("Channel.py lookup failed for '%s': %s", source, e)
        return None
    if isinstance(url, str) and url.strip().lower().startswith(("http://", "https://")):
        LOG.info("Channel '%s' URL loaded from Channel.py", source)
        return url.strip()
    return None

async def _probe_streams(url: str):
    """Probe video/audio streams and return (video_heights, language_indexes).

    HLS probing rule:
      - URL ending exactly in .m3u8 -> let ffprobe auto-detect the M3U8 input.
      - Any other URL -> force the HLS demuxer with ``-f hls``.

    Every FFprobe audio stream is valid regardless of language metadata.
    Unknown/missing language metadata is stored separately while preserving
    the real FFprobe stream index for later FFmpeg mapping.
    """
    is_m3u8 = str(url).strip().lower().endswith('.m3u8')

    cmd = ['ffprobe', '-v', 'error', '-print_format', 'json']
    if not is_m3u8:
        cmd += ['-f', 'hls']
    cmd += ['-show_streams', '-probesize', '10000000', '-analyzeduration', '15000000', url]

    try:
        proc = await asyncio.create_subprocess_exec(
            *cmd, stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.PIPE
        )
        out, err = await proc.communicate()
        if proc.returncode != 0:
            LOG.warning('ffprobe failed (%s): %s',
                        'm3u8-auto' if is_m3u8 else 'forced-hls',
                        err.decode(errors='ignore')[-1000:])
            # Probe failure means the source itself could not be opened/reached.
            # Keep this distinct from a successful probe with no audio streams.
            return [], None

        data = json.loads(out.decode(errors='ignore'))
        video_streams = []
        for stream in data.get('streams', []):
            if stream.get('codec_type') != 'video' or not stream.get('height'):
                continue
            try:
                video_streams.append((int(stream.get('height')), int(stream.get('index'))))
            except (TypeError, ValueError):
                continue

        heights = sorted({h for h, _idx in video_streams}, reverse=True)
        # IMPORTANT for HLS master playlists: ffmpeg's 0:v:0 is often the
        # first/lowest variant (for example 144p). Remember the FFprobe stream
        # index of the highest variant so Sony Auto can explicitly map it.
        selected_video_index = None
        if video_streams:
            selected_video_index = max(video_streams, key=lambda item: item[0])[1]

        # Every codec_type == audio stream is real audio, even when tags == {}.
        # UNKNOWN contains the actual FFprobe indexes for missing/unknown language.
        lang_indexes = {lang: [] for lang in AUDIO_LANGS}
        lang_indexes['UNKNOWN'] = []

        for stream in data.get('streams', []):
            if stream.get('codec_type') != 'audio':
                continue

            try:
                stream_index = int(stream['index'])
            except (KeyError, TypeError, ValueError):
                LOG.warning('Audio stream has no valid FFprobe index: %r', stream)
                continue

            tags = stream.get('tags') or {}
            raw = str(
                tags.get('language') or tags.get('LANGUAGE') or tags.get('title') or ''
            ).strip().lower()

            matched_lang = None
            if raw:
                normalized_parts = raw.replace('_', '-').split('-')
                for lang, codes in LANG_CODES.items():
                    if raw in codes or any(part in codes for part in normalized_parts):
                        matched_lang = lang
                        break

            if matched_lang:
                lang_indexes[matched_lang].append(stream_index)
            else:
                lang_indexes['UNKNOWN'].append(stream_index)

        return heights, lang_indexes, selected_video_index
    except Exception as e:
        LOG.warning('Stream probe failed: %s', e)
        return [], None



async def _probe_sony_quality_variants(url: str):
    """Return available Sony HLS video variants as (height, width, stream_index)."""
    is_m3u8 = str(url).strip().lower().endswith('.m3u8')
    cmd = ['ffprobe', '-v', 'error', '-print_format', 'json']
    if not is_m3u8:
        cmd += ['-f', 'hls']
    cmd += ['-show_streams', '-probesize', '10000000', '-analyzeduration', '15000000', url]
    try:
        proc = await asyncio.create_subprocess_exec(
            *cmd, stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.PIPE
        )
        out, err = await proc.communicate()
        if proc.returncode != 0:
            LOG.warning('Sony quality probe failed: %s', err.decode(errors='ignore')[-1200:])
            return []
        data = json.loads(out.decode(errors='ignore'))
        variants = []
        for st in data.get('streams', []):
            if st.get('codec_type') != 'video':
                continue
            try:
                w = int(st.get('width') or 0)
                h = int(st.get('height') or 0)
                idx = int(st.get('index'))
            except (TypeError, ValueError):
                continue
            if w > 0 and h > 0:
                variants.append((h, w, idx))
        # Keep the best stream index for each displayed height.
        best = {}
        for h, w, idx in variants:
            old = best.get(h)
            if old is None or w > old[1]:
                best[h] = (h, w, idx)
        return sorted(best.values(), key=lambda x: (x[0], x[1]), reverse=True)
    except Exception as e:
        LOG.warning('Sony quality probe exception: %s', e)
        return []


def _sony_quality_keyboard(session):
    """Dynamic Sony quality buttons from the actual HLS master variants."""
    variants = session.get('sony_quality_variants') or []
    token = session.get('callback_token', '')
    rows = []
    for h, w, idx in sorted(variants, key=lambda x: x[0]):
        label = f'{h}p'
        # 540p is represented by 960x540, etc. Use the real dimensions in text.
        label = f'{h}p • {w}×{h}'
        rows.append([InlineKeyboardButton(label, callback_data=f'sonyq:{token}:{h}:{idx}')])
    rows.append([InlineKeyboardButton('⬅️ Back: Audio Tracks', callback_data=f'recs:{token}:audio')])
    return InlineKeyboardMarkup(rows)



def _audio_keyboard(session):
    selected = session['audio']
    detected = session.get('lang_indexes', {})
    token = session.get('callback_token', '')
    rows = []

    for i in range(0, len(AUDIO_LANGS), 2):
        row = []
        for lang in AUDIO_LANGS[i:i+2]:
            mark = '✅' if lang in selected else '❌'
            row.append(InlineKeyboardButton(
                f'{mark} {lang} (AAC)',
                callback_data=f'reca:{token}:lang:{lang}'
            ))
        rows.append(row)

    unknown_indexes = detected.get('UNKNOWN', [])
    for track_no, _stream_index in enumerate(unknown_indexes, 1):
        track_key = f'UNKNOWN:{track_no - 1}'
        mark = '✅' if track_key in selected else '❌'
        rows.append([InlineKeyboardButton(
            f'{mark} Unknown Track {track_no} (AAC)',
            callback_data=f'reca:{token}:unknown:{track_no - 1}'
        )])

    rows.append([InlineKeyboardButton('🎵 All Tracks', callback_data=f'reca:{token}:all')])
    if _is_sony_source_name(session.get('raw_source_name', '')) and session.get('sony_new_command'):
        rows.append([
            InlineKeyboardButton('⬅️ Cancel', callback_data=f'recs:{token}:cancel'),
            InlineKeyboardButton('🎥 Select Quality', callback_data=f'recs:{token}:quality'),
        ])
    else:
        rows.append([
            InlineKeyboardButton('⬅️ Back', callback_data=f'recs:{token}:cancel'),
            InlineKeyboardButton('➡️ Quality', callback_data=f'recs:{token}:quality'),
        ])
        rows.append([InlineKeyboardButton('▶️ Start Recording', callback_data=f'recs:{token}:start')])
    return InlineKeyboardMarkup(rows)


def _audio_text(session):
    return (
        "🎵 **Select Audio Tracks**\n\n"
        "Select the audio tracks you want to record.\n"
        "Use **All Tracks** to select every detected track."
    )


def _quality_keyboard(session):
    if session.get('sony_new_command'):
        return _sony_quality_keyboard(session)
    selected = session["quality"]
    def btn(key, label):
        return InlineKeyboardButton(
            ("✅ " if selected == key else "") + label,
            callback_data=f"recq:{session.get('callback_token', '')}:{key}"
        )
    return InlineKeyboardMarkup([
        [btn("auto", "⚡ Auto")],
        [btn("480", "480p"), btn("576", "576p")],
        [btn("720", "720p"), btn("1080", "1080p")],
        [InlineKeyboardButton("⬅️ Back: Audio Tracks", callback_data=f"recs:{session.get('callback_token', '')}:audio")],
        [InlineKeyboardButton("▶️ Start Recording", callback_data=f"recs:{session.get('callback_token', '')}:start")],
    ])

def _quality_text(session):
    if session.get('sony_new_command'):
        return "🎥 **Select Quality**\n\n🔍 **Detecting...**\n\nChoose one of the available HLS qualities below."
    if _is_sony_source_name(session.get('raw_source_name', '')):
        return "🎥 **Sony LIV Quality**\n\n⚡ **Automatic**\n\nHighest available HLS quality will be selected automatically.\n1080p is selected when available."
    return "🎥 **Select Video Quality**\n\nChoose the recording quality."


async def _show_audio_menu(query, session):
    session["step"] = "audio"
    try:
        await query.message.edit_caption(_audio_text(session), reply_markup=_audio_keyboard(session))
    except Exception as e:
        if "MESSAGE_NOT_MODIFIED" not in str(e).upper():
            raise


async def _show_quality_menu(query, session):
    session["step"] = "quality"
    try:
        await query.message.edit_caption(_quality_text(session), reply_markup=_quality_keyboard(session))
    except Exception as e:
        if "MESSAGE_NOT_MODIFIED" not in str(e).upper():
            raise


def _format_bytes(value):
    try:
        value = float(value or 0)
    except Exception:
        value = 0.0
    units = ("B", "KB", "MB", "GB", "TB")
    for unit in units:
        if value < 1024 or unit == units[-1]:
            return f"{value:.1f} {unit}" if unit != "B" else f"{int(value)} B"
        value /= 1024


async def _apply_audiotrack_to_replied_video(client, message: Message, title: str):
    """Remux a replied video/document and update every audio track title.

    Reply mode is deliberately separate from the bot-wide /Audiotrack settings.
    Temporary progress/status messages are removed after 10 seconds; the output
    video/document is never auto-deleted.
    """
    reply = getattr(message, "reply_to_message", None)
    if not reply:
        return False

    media = getattr(reply, "video", None) or getattr(reply, "document", None)
    if not media:
        return False

    filename = getattr(media, "file_name", None) or "input.mkv"
    safe_name = _safe_filename(filename)
    work_dir = join(getattr(config, "DOWNLOAD_DIRECTORY", "/tmp"), f"audiotrack_{secrets.token_hex(6)}")
    os.makedirs(work_dir, exist_ok=True)
    input_path = join(work_dir, safe_name)
    stem, ext = os.path.splitext(safe_name)
    ext = ext.lower() or ".mkv"
    # Always produce an MP4 so Telegram receives the result as a direct video,
    # even when the replied media was uploaded as a document/MKV.
    output_path = join(work_dir, f"{stem}.audiotrack.mp4")

    status = None
    cleanup_status = None

    async def _schedule_status_delete(msg, delay=10):
        if not msg:
            return
        try:
            await asyncio.sleep(delay)
            await msg.delete()
        except Exception:
            pass

    def _pct(current, total):
        try:
            if not total:
                return 0
            return max(0, min(100, int(current * 100 / total)))
        except Exception:
            return 0

    def _progress_bar(pct, width=10):
        try:
            pct = max(0, min(100, int(pct)))
        except Exception:
            pct = 0
        filled = min(width, int(pct * width / 100))
        return "🟩" * filled + "⬜" * (width - filled)

    async def _download_progress(current, total, *_args):
        pct = _pct(current, total)
        try:
            await status.edit_text(
                "📥 **Download progress**\n"
                f"{_progress_bar(pct)} **{pct}%**"
            )
        except Exception:
            pass

    async def _upload_progress(current, total, *_args):
        pct = _pct(current, total)
        try:
            await status.edit_text(
                "📤 **Uploading progress**\n"
                f"{_progress_bar(pct)} **{pct}%**"
            )
        except Exception:
            pass

    try:
        status = await message.reply_text(
            "📥 **Download progress**\n"
            f"{_progress_bar(0)} **0%**"
        )

        # Download progress is shown in the temporary status message.
        await client.download_media(
            reply,
            file_name=input_path,
            progress=_download_progress,
        )
        if not os.path.isfile(input_path) or os.path.getsize(input_path) <= 0:
            raise RuntimeError("Video download failed.")

        probe_cmd = [
            "ffprobe", "-v", "error", "-select_streams", "a",
            "-show_entries", "stream=index", "-of", "csv=p=0", input_path,
        ]
        probe = await asyncio.create_subprocess_exec(
            *probe_cmd,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE,
        )
        probe_out, probe_err = await probe.communicate()
        if probe.returncode != 0:
            raise RuntimeError(probe_err.decode(errors="ignore")[-1200:] or "ffprobe failed")

        audio_indexes = [
            x.strip() for x in probe_out.decode(errors="ignore").splitlines()
            if x.strip().isdigit()
        ]
        if not audio_indexes:
            raise RuntimeError("No audio tracks found in the replied video.")

        args = [
            "ffmpeg", "-hide_banner", "-loglevel", "error", "-y",
            "-i", input_path,
            "-map", "0",
            "-map_metadata", "0",
            "-map_chapters", "0",
            "-c", "copy",
        ]
        for out_audio_index in range(len(audio_indexes)):
            # Only title/handler_name are changed. Existing language metadata
            # stays untouched.
            args += [
                f"-metadata:s:a:{out_audio_index}", f"handler_name={title}",
                f"-metadata:s:a:{out_audio_index}", f"title={title}",
            ]
        args.append(output_path)

        await status.edit_text(
            "🎵 **Audiotrack Processing...**\n\n"
            f"🏷️ **Your_title:** `{title}`\n"
            f"🎧 **Tracks:** `{len(audio_indexes)}`\n\n"
            "⚙️ Updating audio metadata..."
        )

        proc = await asyncio.create_subprocess_exec(
            *args,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE,
        )
        _, err = await proc.communicate()
        if proc.returncode != 0 or not os.path.isfile(output_path):
            raise RuntimeError(err.decode(errors="ignore")[-1800:] or "FFmpeg failed")

        verify_cmd = [
            "ffprobe", "-v", "error", "-select_streams", "a",
            "-show_entries", "stream_tags=title:stream_tags=handler_name",
            "-of", "default=noprint_wrappers=1", output_path,
        ]
        verify = await asyncio.create_subprocess_exec(
            *verify_cmd,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE,
        )
        verify_out, verify_err = await verify.communicate()
        verify_text = verify_out.decode(errors="ignore")
        if verify.returncode != 0:
            raise RuntimeError(verify_err.decode(errors="ignore")[-1200:] or "Output verification failed")
        if title not in verify_text:
            raise RuntimeError("Output audio metadata verification failed.")

        await status.edit_text(
            "📤 **Uploading progress**\n"
            f"{_progress_bar(0)} **0%**"
        )

        # IMPORTANT: Always send the processed file as a Telegram VIDEO.
        # The input may have been a Telegram document (for example MKV), but
        # the output is always MP4 so it is delivered directly as video.
        await client.send_video(
            chat_id=message.chat.id,
            video=output_path,
            caption=None,
            supports_streaming=True,
            reply_to_message_id=getattr(reply, "id", None),
            progress=_upload_progress,
        )

        # Completion is a separate temporary message, matching the requested
        # flow. It is deleted after 10 seconds; the video is not deleted.
        completed_msg = await message.reply_text(
            "🎵 **Audiotrack Updated**\n\n"
            f"🏷️ **Your_title:** `{title}`\n"
            f"🎧 **Tracks:** `{len(audio_indexes)}`\n\n"
            "✅ **Video sent successfully!**"
        )
        cleanup_status = asyncio.create_task(_schedule_status_delete(status, 10))
        asyncio.create_task(_schedule_status_delete(completed_msg, 10))
        # Also remove the /Audiotrack command after 10 seconds when Telegram
        # permissions allow it. This does NOT affect the output video.
        asyncio.create_task(_schedule_status_delete(message, 10))
        return True

    except Exception as e:
        LOG.exception("Reply video Audiotrack failed")
        try:
            if status:
                await status.edit_text(f"❌ **Audiotrack Failed**\n\n`{str(e)[:1500]}`")
                cleanup_status = asyncio.create_task(_schedule_status_delete(status, 10))
            else:
                err_msg = await message.reply_text(f"❌ **Audiotrack Failed**\n\n`{str(e)[:1500]}`")
                cleanup_status = asyncio.create_task(_schedule_status_delete(err_msg, 10))
            asyncio.create_task(_schedule_status_delete(message, 10))
        except Exception:
            pass
        return True
    finally:
        shutil.rmtree(work_dir, ignore_errors=True)


@app.on_message(filters.command("audiotrack"))
async def audiotrack_command(client, message: Message):
    args = message.command[1:] if getattr(message, "command", None) else []
    replied = getattr(message, "reply_to_message", None)
    replied_media = (
        getattr(replied, "video", None) or getattr(replied, "document", None)
    ) if replied else None

    # ================================================================
    # VIDEO REPLY MODE
    # Reply to a video/document and use:
    #   /Audiotrack Your_title
    # The existing bot-wide settings menu is NOT changed.
    # ================================================================
    if replied_media:
        if not args:
            return await message.reply_text(
                "🎵 **Video Reply Audiotrack**\n\n"
                "You replied to a video. Send the title you want to apply to "
                "all audio tracks:\n\n"
                "`/Audiotrack Your_title`\n\n"
                "Example:\n"
                "`/Audiotrack Anime Cartoon`"
            )

        title_from_reply = " ".join(args).strip()
        # Also accept the settings-style `count|title` syntax in reply mode,
        # but ignore the count because reply mode updates every audio track.
        if "|" in title_from_reply:
            _count, title_from_reply = title_from_reply.split("|", 1)
            title_from_reply = title_from_reply.strip()
        if not title_from_reply:
            return await message.reply_text("❌ Your_title cannot be empty.")
        if len(title_from_reply) > 100:
            return await message.reply_text("❌ Your_title is too long. Maximum 100 characters.")

        handled = await _apply_audiotrack_to_replied_video(
            client, message, title_from_reply
        )
        if handled:
            return

    # ================================================================
    # EXISTING BOT-WIDE SETTINGS MODE
    # No replied media -> keep the current 1–6 Tracks menu exactly.
    # ================================================================
    user_id = getattr(getattr(message, "from_user", None), "id", None)
    if user_id is None or not _has_privileged_access(user_id):
        return await message.reply_text(
            "🔒 **Audio Track Settings**\n\n"
            "Only Admin/Owner/Premium users can change audio-track titles."
        )

    if not args:
        rows = [[InlineKeyboardButton(f"{i} Tracks", callback_data=f"atitle:{i}")] for i in range(1, 7)]
        rows.append([InlineKeyboardButton("✏️ Edit Default Title", callback_data="atitle:default")])
        return await message.reply_text(
            "🎵 **Audio Track Title Settings**\n\n"
            "Set the `Your_title` metadata used for the selected number of audio tracks.\n"
            "Detected language mapping is not changed.",
            reply_markup=InlineKeyboardMarkup(rows),
        )

    raw = " ".join(args).strip()
    if "|" in raw:
        count_text, title = raw.split("|", 1)
        key = count_text.strip()
        title = title.strip()
        if key != "default" and (not key.isdigit() or int(key) < 1 or int(key) > 12):
            return await message.reply_text("❌ Use `default` or a track count from 1 to 12.")
    else:
        key, title = "default", raw
    if not title:
        return await message.reply_text("❌ Title cannot be empty.")
    if len(title) > 100:
        return await message.reply_text("❌ Title is too long. Maximum 100 characters.")
    audio_track_titles[key] = title
    _save_audio_track_titles()
    label = "default" if key == "default" else f"{key} audio tracks"
    return await message.reply_text(f"✅ **Audio title updated**\n\n🎵 {label}: `{title}`")


@app.on_callback_query(filters.regex(r"^atitle:(default|[1-6])$"))
async def audiotrack_title_callback(client, query):
    user_id = getattr(query.from_user, "id", None)
    if user_id is None or not _has_privileged_access(user_id):
        return await query.answer("Not allowed.", show_alert=True)
    key = query.data.split(":", 1)[1]
    current = audio_track_titles.get(key, audio_track_titles.get("default", DEFAULT_AUDIO_TITLE))
    await query.answer()
    await query.message.reply_text(
        f"🎵 **Current title for {key}:**\n`{current}`\n\n"
        f"Use `/Audiotrack {key}|Your_title` to change it."
    )


@app.on_callback_query(filters.regex(r'^reca:'))
async def rec_audio_callback(client, query):
    parts = query.data.split(':')
    if len(parts) < 3:
        return await query.answer('Recording setup expired. Run /rec again.', show_alert=True)
    token = parts[1]
    session_key = rec_session_tokens.get(token)
    session = rec_sessions.get(session_key) if session_key is not None else None
    if not session:
        return await query.answer('Recording setup expired. Run /rec again.', show_alert=True)

    action = parts[2]
    if action == 'all':
        selected = {lang for lang in AUDIO_LANGS if session.get('lang_indexes', {}).get(lang)}
        selected.update(f'UNKNOWN:{i}' for i, _ in enumerate(session.get('lang_indexes', {}).get('UNKNOWN', [])))
        session['audio'] = selected
        await query.answer('All tracks selected')
    elif action == 'unknown' and len(parts) == 4:
        try:
            pos = int(parts[3])
            unknown = session.get('lang_indexes', {}).get('UNKNOWN', [])
            if pos < 0 or pos >= len(unknown):
                return await query.answer('Unknown audio track not found.', show_alert=True)
        except ValueError:
            return await query.answer('Invalid audio track.', show_alert=True)
        key = f'UNKNOWN:{pos}'
        if key in session['audio']:
            session['audio'].remove(key)
        else:
            session['audio'].add(key)
        await query.answer(f'Unknown Track {pos + 1}: ' + ('selected' if key in session['audio'] else 'not selected'))
    elif action == 'lang' and len(parts) == 4:
        value = parts[3]
        if value not in AUDIO_LANGS:
            return await query.answer('Invalid audio track.', show_alert=True)
        if value in session['audio']:
            session['audio'].remove(value)
        else:
            session['audio'].add(value)
        await query.answer(f"{value}: {'selected' if value in session['audio'] else 'not selected'}")
    else:
        return await query.answer('Invalid audio selection.', show_alert=True)
    await _show_audio_menu(query, session)



@app.on_callback_query(filters.regex(r"^sonyq:"))
async def sony_quality_callback(client, query):
    parts = query.data.split(':', 3)
    if len(parts) != 4:
        return await query.answer('Recording setup expired. Run /Sony again.', show_alert=True)
    token, height_text, index_text = parts[1], parts[2], parts[3]
    session_key = rec_session_tokens.get(token)
    session = rec_sessions.get(session_key) if session_key is not None else None
    if not session or not session.get('sony_new_command'):
        return await query.answer('Recording setup expired. Run /Sony again.', show_alert=True)
    try:
        height = int(height_text)
        index = int(index_text)
    except ValueError:
        return await query.answer('Invalid Sony quality.', show_alert=True)
    valid = any(int(h) == height and int(idx) == index for h, _w, idx in session.get('sony_quality_variants', []))
    if not valid:
        return await query.answer('That quality is no longer available.', show_alert=True)
    session['quality'] = str(height)
    session['quality_video_index'] = index
    await query.answer(f'Selected {height}p')
    # Start immediately after quality selection.
    session['process_message'] = query.message
    try:
        await query.message.edit_caption(
            f"🎬 **Processing Video...**\\n\\n📄 **File:** `{session['raw_filename']}`\\n"
            f"🎥 **Quality:** `{height}p`\\n⚡ **Speed:** Calculating...\\nStatus: Starting Recording",
            reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton('❌ Cancel', callback_data=f'recs:{token}:cancel')]])
        )
    except Exception:
        pass
    asyncio.create_task(handle_record(client, session['message'], selection=session))

@app.on_callback_query(filters.regex(r"^recq:"))
async def rec_quality_callback(client, query):
    parts = query.data.split(':', 2)
    if len(parts) != 3:
        return await query.answer('Recording setup expired. Run /rec again.', show_alert=True)
    token, quality = parts[1], parts[2]
    session_key = rec_session_tokens.get(token)
    session = rec_sessions.get(session_key) if session_key is not None else None
    if not session:
        return await query.answer('Recording setup expired. Run /rec again.', show_alert=True)
    if quality not in QUALITY_LABELS:
        return await query.answer('Invalid quality.', show_alert=True)
    session['quality'] = quality
    await query.answer(f'Video quality: {QUALITY_LABELS[quality]}')
    await _show_quality_menu(query, session)


@app.on_callback_query(filters.regex(r"^recs:"))
async def rec_setup_callback(client, query):
    parts = query.data.split(':', 2)
    if len(parts) != 3:
        return await query.answer('Recording setup expired. Run /rec again.', show_alert=True)
    token, action = parts[1], parts[2]
    session_key = rec_session_tokens.get(token)
    session = rec_sessions.get(session_key) if session_key is not None else None
    if not session:
        return await query.answer('Recording setup expired. Run /rec again.', show_alert=True)

    if action == 'cancel':
        rec_sessions.pop(session_key, None)
        rec_session_tokens.pop(token, None)
        await query.answer('Cancelled')
        return await query.message.edit_caption('❌ **Recording setup cancelled.**')

    if action == 'quality':
        if not session['audio']:
            return await query.answer('Select at least one audio track.', show_alert=True)
        if session.get('sony_new_command'):
            await query.answer('Detecting Sony qualities...')
            variants = await _probe_sony_quality_variants(session['url'])
            if not variants:
                return await query.message.edit_caption('❌ **No video qualities detected from Sony HLS stream.**')
            session['sony_quality_variants'] = variants
            session['step'] = 'quality'
            try:
                await query.message.edit_caption(
                    "🎥 **Select Quality**\n\n🔍 **Detected qualities:**\n\n" +
                    "\n".join(f"{w}×{h} → {h}p" for h, w, _idx in sorted(variants, key=lambda x: x[0])),
                    reply_markup=_sony_quality_keyboard(session)
                )
            except Exception:
                pass
            return
        await query.answer()
        return await _show_quality_menu(query, session)

    if action == 'audio':
        await query.answer()
        return await _show_audio_menu(query, session)

    if action == 'start':
        if not session['audio']:
            return await query.answer('Select at least one audio track.', show_alert=True)
        buttons = InlineKeyboardMarkup([[InlineKeyboardButton('❌ Cancel', callback_data=f'recs:{token}:cancel')]])
        try:
            await query.message.edit_caption(
                '🎬 **Processing Video...**\n\n📄 **File:** `' + session['raw_filename'] +
                '`\n⚡ **Speed:** Calculating...\nStatus: Starting Recording',
                reply_markup=buttons)
        except Exception:
            try:
                await query.message.edit_text(
                    '🎬 **Processing Video...**\n\n📄 **File:** `' + session['raw_filename'] +
                    '`\n⚡ **Speed:** Calculating...\nStatus: Starting Recording',
                    reply_markup=buttons)
            except Exception:
                pass
        session['process_message'] = query.message
        asyncio.create_task(handle_record(client, session['message'], selection=session))
        return
    await query.answer('Unknown option', show_alert=True)


def _sony_display_name(name: str):
    """Collapse Sony SD/HD catalog entries into one display channel name."""
    import re
    n = name.strip()
    if not n.casefold().startswith("sony "):
        return n
    return re.sub(r"\s+(?:SD|HD)$", "", n, flags=re.IGNORECASE).strip()

def _sony_preferred_channel_name(display_name: str):
    """Prefer an HD Sony source when both SD and HD catalog entries exist."""
    channels = get_public_channels()
    target = display_name.strip().casefold()
    matches = [name for name in channels if _sony_display_name(name).casefold() == target]
    if not matches:
        return None
    for name in matches:
        if name.casefold().endswith(" hd"):
            return name
    return matches[0]

def _is_sony_source_name(name: str) -> bool:
    return str(name or "").strip().casefold().startswith("sony ")

def _channel_group_key(name: str):
    """Return the automatic /Channel group for a channel name."""
    n = name.strip().casefold()
    if n.startswith("pogo"):
        return "POGO"
    if n.startswith("discovery kids"):
        return "DISCOVERY KIDS"
    if n.startswith("nick"):
        return "NICK"
    if n.startswith("sony "):
        return "SONY LIV"
    if n.startswith("cartoon network"):
        return "CARTOON NETWORK & HD+"
    return None

def _channel_groups(channels):
    """Build All groups automatically; no manual All entries are required."""
    groups = {}
    singles = []
    for name in channels:
        group = _channel_group_key(name)
        if group:
            groups.setdefault(group, []).append(name)
        else:
            singles.append(name)
    for names in groups.values():
        names.sort(key=lambda x: (x.casefold() != x.split()[0].casefold(), x.casefold()))
    return groups, singles

@app.on_message(filters.command("Channel"))
async def channel_command(client, message: Message):
    if not await _verification_required(message):
        return

    channels = get_public_channels()
    if not channels:
        return await message.reply_text("📭 **No channels available.**")

    groups, singles = _channel_groups(channels)
    rows = []
    for group_name, names in groups.items():
        if group_name == "SONY LIV":
            rows.append([InlineKeyboardButton("📺 Sony LIV All SD", callback_data="chgrp:SONY LIV SD")])
            rows.append([InlineKeyboardButton("📺 Sony LIV All HD", callback_data="chgrp:SONY LIV HD")])
        else:
            rows.append([InlineKeyboardButton(f"📺 {group_name} All", callback_data=f"chgrp:{group_name}")])
    for name in singles:
        cid = channel_id_map.get(name)
        rows.append([InlineKeyboardButton(f"📺 {name}", callback_data=f"ch:{cid}")])

    rows.append([InlineKeyboardButton("🔄 Refresh Channel IDs", callback_data="chrefresh")])
    text = (
        "📺 **Available Channels**\n\n"
        "Select a channel group or channel.\n"
        "🆔 Channel IDs automatically refresh every 24 hours.\n\n"
        "🎬 **Record:** `/Rec <CHANNEL_ID> <DURATION> [FILENAME]`"
    )
    await message.reply_text(text, reply_markup=InlineKeyboardMarkup(rows))

@app.on_callback_query(filters.regex(r"^chgrp:"))
async def channel_group_callback(client, query):
    group_name = query.data.split(":", 1)[1]
    channels = get_public_channels()
    groups, _ = _channel_groups(channels)
    if group_name in ("SONY LIV SD", "SONY LIV HD"):
        want_hd = group_name.endswith("HD")
        names = [
            name for name in channels
            if name.strip().casefold().startswith("sony ")
            and name.strip().casefold().endswith(" hd") == want_hd
        ]
    else:
        names = groups.get(group_name)
    if not names:
        return await query.answer("Channel group not found.", show_alert=True)

    rows = []
    seen = set()
    for name in names:
        display_name = _sony_display_name(name) if group_name in ("SONY LIV", "SONY LIV SD", "SONY LIV HD") else name
        key = display_name.casefold()
        if key in seen:
            continue
        seen.add(key)
        if group_name == "SONY LIV SD":
            preferred = next((n for n in names if _sony_display_name(n).casefold() == key and n.casefold().endswith(" sd")), name)
        elif group_name == "SONY LIV HD":
            preferred = next((n for n in names if _sony_display_name(n).casefold() == key and n.casefold().endswith(" hd")), name)
        elif group_name == "SONY LIV":
            preferred = _sony_preferred_channel_name(display_name)
        else:
            preferred = name
        cid = channel_id_map.get(preferred)
        if cid is None:
            continue
        rows.append([InlineKeyboardButton(
            f"📺 {display_name}", callback_data=f"ch:{cid}"
        )])
    rows.append([InlineKeyboardButton("⬅️ Back", callback_data="chback")])
    await query.answer()
    try:
        await query.message.edit_text(
            f"📺 **{group_name} All**\n\nSelect a channel:",
            reply_markup=InlineKeyboardMarkup(rows),
        )
    except Exception:
        pass

@app.on_callback_query(filters.regex(r"^ch:\d+$"))
async def channel_info_callback(client, query):
    cid = query.data.split(":", 1)[1]
    name = _channel_name_from_id(cid)
    if not name:
        return await query.answer("❌ Invalid Channel ID", show_alert=True)
    await query.answer(
        f"📺 Channel Name: {name}\n🆔 Channel ID: {cid}",
        show_alert=True,
    )

@app.on_callback_query(filters.regex(r"^chback$"))
async def channel_back_callback(client, query):
    channels = get_public_channels()
    groups, singles = _channel_groups(channels)
    rows = []
    for group_name in groups:
        if group_name == "SONY LIV":
            rows.append([InlineKeyboardButton("📺 Sony LIV All SD", callback_data="chgrp:SONY LIV SD")])
            rows.append([InlineKeyboardButton("📺 Sony LIV All HD", callback_data="chgrp:SONY LIV HD")])
        else:
            rows.append([InlineKeyboardButton(f"📺 {group_name} All", callback_data=f"chgrp:{group_name}" )])
    for name in singles:
        rows.append([InlineKeyboardButton(f"📺 {name}", callback_data=f"ch:{channel_id_map.get(name)}")])
    rows.append([InlineKeyboardButton("🔄 Refresh Channel IDs", callback_data="chrefresh")])
    await query.answer()
    try:
        await query.message.edit_text(
            "📺 **Available Channels**\n\nSelect a channel group or channel.",
            reply_markup=InlineKeyboardMarkup(rows),
        )
    except Exception:
        pass

@app.on_callback_query(filters.regex(r"^chrefresh$"))
async def channel_refresh_callback(client, query):
    global channel_id_map
    # Force a fresh 24-hour ID set. Existing links/names remain unchanged.
    available = list(range(10, 100))
    random.shuffle(available)
    channels = get_public_channels()
    channel_id_map = {name: available[i] for i, name in enumerate(channels)}
    _save_channel_ids()
    await query.answer("Channel IDs refreshed for the next 24 hours.")
    return await channel_back_callback(client, query)


async def _capture_live_preview(url: str, output_path: str) -> bool:
    """Capture one current frame from a live HLS source."""
    try:
        proc = await asyncio.create_subprocess_exec(
            "ffmpeg", "-y", "-loglevel", "error",
            "-f", "hls", "-i", url,
            "-frames:v", "1", "-q:v", "3", output_path,
            stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.PIPE,
        )
        try:
            _, err = await asyncio.wait_for(proc.communicate(), timeout=20)
        except asyncio.TimeoutError:
            proc.kill()
            await proc.communicate()
            return False
        return proc.returncode == 0 and os.path.exists(output_path) and os.path.getsize(output_path) > 0
    except Exception as e:
        LOG.warning("Live preview capture failed: %s", e)
        return False



# ---------------------------------------------------------------------------
# Scheduled recordings
# ---------------------------------------------------------------------------
SCHEDULE_STORE_FILE = join(
    getattr(config, "DOWNLOAD_DIRECTORY", "."),
    "recording_schedules.json",
)
scheduled_recordings = {}
schedule_worker_task = None


def _load_schedules():
    global scheduled_recordings
    try:
        os.makedirs(os.path.dirname(SCHEDULE_STORE_FILE) or ".", exist_ok=True)
        if os.path.exists(SCHEDULE_STORE_FILE):
            with open(SCHEDULE_STORE_FILE, "r", encoding="utf-8") as f:
                data = json.load(f)
            scheduled_recordings = data if isinstance(data, dict) else {}
    except Exception as e:
        LOG.warning("Schedule store load failed: %s", e)
        scheduled_recordings = {}


def _save_schedules():
    try:
        os.makedirs(os.path.dirname(SCHEDULE_STORE_FILE) or ".", exist_ok=True)
        tmp = SCHEDULE_STORE_FILE + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(scheduled_recordings, f, indent=2)
        os.replace(tmp, SCHEDULE_STORE_FILE)
    except Exception as e:
        LOG.warning("Schedule store save failed: %s", e)


def _parse_schedule_datetime(date_text: str, time_text: str):
    for fmt in ("%d-%m-%Y %I:%M:%S%p", "%d-%m-%Y %I:%M:%S %p", "%d-%m-%Y %H:%M:%S"):
        try:
            return tz.localize(datetime.strptime(f"{date_text} {time_text}", fmt))
        except ValueError:
            continue
    return None


def _schedule_usage():
    return (
        "❌ **Invalid Format**\n\n"
        "📅 **Direct Link:**\n"
        "`/schedule <LINK> <START> <END> <DATE>`\n\n"
        "Example:\n"
        "`/schedule https://example.com/live.m3u8 06:00:00PM 07:00:00PM 01-09-2026`\n\n"
        "📺 **Channel ID:**\n"
        "`/schedule <ID> <START> <END> <DATE>`\n\n"
        "Example:\n"
        "`/schedule 56 06:00:00PM 07:00:00PM 01-09-2026`\n\n"
        "⏰ Channel IDs automatically refresh every 24 hours."
    )


async def _run_scheduled_recording(client, item):
    try:
        url = item["url"]
        duration = item["duration"]
        chat_id = int(item["chat_id"])
        actor_id = int(item["actor_id"])
        filename = item.get("filename") or "Scheduled"

        # Re-probe at start time so the actual stream/audio indexes are current.
        heights, lang_indexes, selected_video_index = await _probe_streams(url)
        if lang_indexes is None:
            LOG.warning("Scheduled source unavailable during FFprobe: %s", url)
            return
        detected_audio = {lang for lang, indexes in lang_indexes.items() if indexes}
        if not detected_audio:
            await client.send_message(chat_id, "❌ Scheduled recording skipped: no real audio tracks detected by FFprobe.")
            return

        status_msg = await client.send_message(
            chat_id,
            f"⏰ **Scheduled Recording Started**\n\n📄 `{filename}`\n⏱ `{duration}`"
        )
        selection = {
            "message": status_msg,
            "actor_id": actor_id,
            "chat_id": chat_id,
            "url": url,
            "timestamp": duration,
            "raw_filename": _safe_filename(filename),
            "quality": "auto",
            "audio": set(detected_audio),
            "lang_indexes": lang_indexes,
            "watermark": "off",
            "step": "audio",
            "detected_heights": heights,
            "selected_video_index": selected_video_index,
            "sony_quality_mode": ("hd" if str(item.get("source_name", "")).strip().casefold().endswith(" hd") else "sd" if str(item.get("source_name", "")).strip().casefold().endswith(" sd") else "auto"),
            "process_message": status_msg,
            "task_id": secrets.token_hex(8),
        }
        await handle_record(client, status_msg, selection=selection)
    except Exception as e:
        LOG.error("Scheduled recording failed: %s", e)
        try:
            await client.send_message(int(item["chat_id"]), f"❌ Scheduled recording failed.\n`{str(e)[:800]}`")
        except Exception:
            pass


async def _schedule_worker(client):
    global scheduled_recordings
    while True:
        try:
            now = datetime.now(tz)
            due = []
            for sid, item in list(scheduled_recordings.items()):
                if item.get("status") != "scheduled":
                    continue
                try:
                    run_at = datetime.fromisoformat(item["run_at"])
                except Exception:
                    continue
                if now >= run_at:
                    due.append((sid, item))

            for sid, item in due:
                # Mark before starting so a slow loop/restart cannot start the same item twice.
                scheduled_recordings[sid]["status"] = "running"
                scheduled_recordings[sid]["started_at"] = now.isoformat()
                _save_schedules()
                asyncio.create_task(_finish_schedule_item(client, sid, item))

            await asyncio.sleep(1)
        except asyncio.CancelledError:
            raise
        except Exception as e:
            LOG.warning("Schedule worker error: %s", e)
            await asyncio.sleep(2)


async def _finish_schedule_item(client, sid, item):
    try:
        await _run_scheduled_recording(client, item)
        scheduled_recordings[sid]["status"] = "completed"
    except Exception as e:
        scheduled_recordings[sid]["status"] = "failed"
        LOG.error("Schedule %s failed: %s", sid, e)
    finally:
        scheduled_recordings[sid]["finished_at"] = datetime.now(tz).isoformat()
        _save_schedules()


_load_schedules()


@app.on_message(filters.command("schedule"))
async def schedule_command(client, message: Message):
    if not await _verification_required(message):
        return

    args = message.command[1:]
    if len(args) not in (4, 5):
        return await message.reply_text(_schedule_usage())

    # Supported forms:
    #   /schedule <LINK> <START> <END> <DATE>
    #   /schedule <CHANNEL_ID> <START> <END> <DATE>
    #   /schedule <ID> <LINK> <START> <END> <DATE>  (explicit schedule ID)
    schedule_id = secrets.token_hex(4)
    if len(args) == 4:
        source, start_text, end_text, date_text = args
    else:
        schedule_id, source, start_text, end_text, date_text = args
        schedule_id = str(schedule_id).strip() or secrets.token_hex(4)

    if source.isdigit() and not source.startswith(("http://", "https://")):
        channel_name = _channel_name_from_id(source)
        if not channel_name:
            return await message.reply_text(
                f"❌ **Invalid Channel ID:** `{source}`\n\nUse `/Channel` to get the current 24-hour IDs."
            )
        url = await _resolve_channel_source(source)
        display_source = f"{channel_name} (ID {source})"
    else:
        url = await _resolve_channel_source(source)
        display_source = source

    if not url:
        return await message.reply_text("❌ **Channel/Link not found.**\n\nUse `/Channel` to view current Channel IDs.")

    start_dt = _parse_schedule_datetime(date_text, start_text)
    end_dt = _parse_schedule_datetime(date_text, end_text)
    if not start_dt or not end_dt:
        return await message.reply_text("❌ Invalid date/time. Use `01-09-2026` and `06:00:00PM` format.")
    if end_dt <= start_dt:
        end_dt += timedelta(days=1)
    if end_dt <= datetime.now(tz):
        return await message.reply_text("❌ This schedule time has already passed.")

    duration_seconds = int((end_dt - start_dt).total_seconds())
    if duration_seconds <= 0:
        return await message.reply_text("❌ Invalid schedule duration.")

    # Avoid accidental duplicate schedule IDs.
    if schedule_id in scheduled_recordings:
        schedule_id = secrets.token_hex(4)

    user = getattr(message, "from_user", None)
    actor_id = _rec_actor_id(message)
    if actor_id is None:
        return await message.reply_text("❌ Unable to identify the scheduling session.")

    scheduled_recordings[schedule_id] = {
        "id": schedule_id,
        "url": url,
        "source": display_source,
        "start": start_text,
        "end": end_text,
        "date": date_text,
        "run_at": start_dt.isoformat(),
        "duration": f"{duration_seconds // 3600:02}:{(duration_seconds % 3600) // 60:02}:{duration_seconds % 60:02}",
        "chat_id": int(message.chat.id),
        "actor_id": int(actor_id),
        "user_id": int(user.id) if user is not None else None,
        "filename": f"Scheduled-{display_source}",
        "status": "scheduled",
        "created_at": datetime.now(tz).isoformat(),
    }
    _save_schedules()

    global schedule_worker_task
    if schedule_worker_task is None or schedule_worker_task.done():
        schedule_worker_task = asyncio.create_task(_schedule_worker(client))

    await message.reply_text(
        "✅ **Recording Scheduled**\n\n"
        f"🆔 **Schedule ID:** `{schedule_id}`\n"
        f"📺 **Source:** `{display_source}`\n"
        f"🕒 **Start:** `{start_text}`\n"
        f"🕒 **End:** `{end_text}`\n"
        f"📅 **Date:** `{date_text}`\n"
        f"⏱ **Duration:** `{duration_seconds // 3600:02}:{(duration_seconds % 3600) // 60:02}:{duration_seconds % 60:02}`"
    )


@app.on_message(filters.command("schedules"))
async def schedules_command(client, message: Message):
    if not await _verification_required(message):
        return
    # /schedules shows only pending/upcoming schedules.
    # Completed/failed historical entries remain in storage but are hidden here.
    items = [
        item for item in scheduled_recordings.values()
        if item.get("status") == "scheduled"
    ]
    if not items:
        return await message.reply_text(
            "📅 **Scheduled Recordings**\n\n"
            "ℹ️ No pending or upcoming schedules."
        )

    lines = ["📅 **Scheduled Recordings**", "", "🟡 **Pending / Upcoming**", ""]
    for item in sorted(items, key=lambda x: x.get("run_at", "")):
        lines.extend([
            f"🆔 `{item.get('id')}`",
            f"📺 `{item.get('source', item.get('url', 'Unknown'))}`",
            f"📅 `{item.get('date')}`",
            f"🕒 `{item.get('start')} - {item.get('end')}`",
            "",
        ])
    await message.reply_text("\n".join(lines))




async def _delete_message_after(message, delay=0):
    """Best-effort automatic deletion for temporary messages."""
    try:
        if delay > 0:
            await asyncio.sleep(delay)
        await message.delete()
    except Exception:
        pass

@app.on_message(filters.text & ~filters.command(["rec","Sony","start","help","token","schedule","schedules","Channel","settings"]), group=10)
async def no_need_rec_command(client, message: Message):
    if not bot_settings.get("no_need_rec",False): return
    parts=(getattr(message,"text","") or "").strip().split()
    if len(parts)<2: return
    if not (parts[0].startswith(("http://","https://")) or parts[0].isdigit()): return
    await rec_command(client,message)


@app.on_message(filters.command("Sony"))
async def sony_command(client, message: Message):
    """Interactive Sony LIV recorder: channel -> preview/audio -> detected quality."""
    try:
        await message.delete()
    except Exception:
        pass
    if not await _verification_required(message):
        return
    args = list(getattr(message, 'command', []) or [])[1:]
    if len(args) < 2:
        return await message.reply_text(
            "❌ **Invalid Format**\\n\\n"
            "`/Sony <DURATION> <FILENAME>`\\n\\n"
            "Example: `/Sony 00:00:30 SonyYAY`"
        )
    duration = args[0].strip()
    if time_to_seconds(duration) <= 0:
        return await message.reply_text('❌ Invalid duration. Use `HH:MM:SS`.')
    filename = _safe_filename(' '.join(args[1:]).strip())
    uid = _rec_actor_id(message)
    if uid is None:
        return await message.reply_text('❌ Unable to identify the recording session.')
    active_count = _active_recording_count(uid)
    setup_count = 1 if uid in rec_sessions else 0
    if active_count + setup_count >= MAX_RECORDINGS_PER_USER:
        return await message.reply_text(f'❌ **Recording Limit Reached!**\\n\\nMaximum allowed: `{MAX_RECORDINGS_PER_USER}`.')
    token = secrets.token_hex(8)
    session = {
        'message': message,
        'actor_id': uid,
        'chat_id': getattr(getattr(message, 'chat', None), 'id', None),
        'timestamp': duration,
        'raw_filename': filename,
        'callback_token': token,
        'quality': 'auto',
        'audio': set(),
        'lang_indexes': {},
        'watermark': 'off',
        'step': 'channel',
        'sony_new_command': True,
        'sony_quality_variants': [],
        'selected_video_index': None,
        'quality_video_index': None,
        'sony_quality_mode': 'auto',
    }
    rec_sessions[uid] = session
    rec_session_tokens[token] = uid
    rows = [
        [InlineKeyboardButton('📺 Sony Channels SD', callback_data=f'sonycat:{token}:sd')],
        [InlineKeyboardButton('📺 Sony Channels HD', callback_data=f'sonycat:{token}:hd')],
        [InlineKeyboardButton('❌ Cancel', callback_data=f'recs:{token}:cancel')],
    ]
    await message.reply_text(
        f"🎬 **Sony Live Channels**\\n\\n⏱ **Duration:** `{duration}`\\n📄 **Filename:** `{filename}`\\n\\nSelect channel group:",
        reply_markup=InlineKeyboardMarkup(rows)
    )


@app.on_callback_query(filters.regex(r'^sonycat:'))
async def sony_category_callback(client, query):
    parts = query.data.split(':', 2)
    if len(parts) != 3:
        return await query.answer('Sony setup expired.', show_alert=True)
    token, category = parts[1], parts[2].lower()
    uid = rec_session_tokens.get(token)
    session = rec_sessions.get(uid) if uid is not None else None
    if not session or not session.get('sony_new_command'):
        return await query.answer('Sony setup expired. Run /Sony again.', show_alert=True)
    channels = get_public_channels()
    want_hd = category == 'hd'
    names = [n for n in channels if str(n).strip().casefold().startswith('sony ') and str(n).strip().casefold().endswith(' hd') == want_hd]
    display = {}
    for n in names:
        display.setdefault(_sony_display_name(n).casefold(), _sony_display_name(n))
    rows = []
    for key, label in sorted(display.items(), key=lambda x: x[1].casefold()):
        rows.append([InlineKeyboardButton(f'📺 {label}', callback_data=f'sonych:{token}:{channel_id_map.get(next((n for n in names if _sony_display_name(n).casefold()==key), ""), "")}')])
    rows = [r for r in rows if r[0].callback_data.rsplit(':',1)[-1].isdigit()]
    rows.append([InlineKeyboardButton('⬅️ Back', callback_data=f'sonyback:{token}')])
    await query.answer()
    try:
        await query.message.edit_text(
            f"📺 **Sony Channels {'HD' if want_hd else 'SD'}**\\n\\nSelect channel:",
            reply_markup=InlineKeyboardMarkup(rows)
        )
    except Exception:
        pass


@app.on_callback_query(filters.regex(r'^sonyback:'))
async def sony_back_callback(client, query):
    token = query.data.split(':',1)[1]
    uid = rec_session_tokens.get(token)
    session = rec_sessions.get(uid) if uid is not None else None
    if not session:
        return await query.answer('Sony setup expired.', show_alert=True)
    rows = [
        [InlineKeyboardButton('📺 Sony Channels SD', callback_data=f'sonycat:{token}:sd')],
        [InlineKeyboardButton('📺 Sony Channels HD', callback_data=f'sonycat:{token}:hd')],
        [InlineKeyboardButton('❌ Cancel', callback_data=f'recs:{token}:cancel')],
    ]
    await query.answer()
    try:
        await query.message.edit_text('🎬 **Sony Live Channels**\\n\\nSelect channel group:', reply_markup=InlineKeyboardMarkup(rows))
    except Exception:
        pass


@app.on_callback_query(filters.regex(r'^sonych:'))
async def sony_channel_callback(client, query):
    parts = query.data.split(':', 2)
    if len(parts) != 3 or not parts[2].isdigit():
        return await query.answer('Invalid Sony channel.', show_alert=True)
    token, cid = parts[1], parts[2]
    uid = rec_session_tokens.get(token)
    session = rec_sessions.get(uid) if uid is not None else None
    name = _channel_name_from_id(cid)
    if not session or not name or not _is_sony_source_name(name):
        return await query.answer('Sony setup expired or channel not found.', show_alert=True)
    url = await _resolve_channel_source(name)
    if not url:
        return await query.answer('Sony channel link not found.', show_alert=True)
    session['url'] = url
    session['raw_source_name'] = name
    session['selected_video_index'] = None
    session['quality_video_index'] = None
    await query.answer('Detecting Sony stream...')
    heights, lang_indexes, selected_video_index = await _probe_streams(url)
    async def _sony_error(text):
        # Callback messages can become invalid/deleted while preview probing is running.
        # Never let MESSAGE_ID_INVALID hide the real Sony error.
        try:
            return await query.message.edit_text(text)
        except Exception:
            try:
                return await client.send_message(query.message.chat.id, text)
            except Exception:
                return None

    if lang_indexes is None:
        return await _sony_error('❌ **Sony channel link is unavailable.**')
    detected_audio = {lang for lang, indexes in lang_indexes.items() if indexes}
    if not detected_audio:
        return await _sony_error('❌ **No audio tracks detected.**')
    session['lang_indexes'] = lang_indexes
    session['audio'] = set(detected_audio)
    session['selected_video_index'] = selected_video_index
    preview_root = join(config.DOWNLOAD_DIRECTORY, '_sony_previews')
    preview_dir = join(preview_root, f"sony_preview_{uid}_{secrets.token_hex(4)}")
    os.makedirs(preview_dir, exist_ok=True)
    preview_path = join(preview_dir, 'preview.jpg')
    if not await _capture_live_preview(url, preview_path):
        shutil.rmtree(preview_dir, ignore_errors=True)
        return await _sony_error('❌ **Unable to capture live stream preview.**')
    caption = (
        f"🎬 **Stream Preview**\\n\\n"
        f"📺 **Channel:** `{_sony_display_name(name)}`\\n\\n"
        "🖼️ Screenshot captured from the live stream.\\n\\n" + _audio_text(session)
    )
    try:
        await query.message.delete()
    except Exception:
        pass
    process_message = await client.send_photo(query.message.chat.id, photo=preview_path, caption=caption, reply_markup=_audio_keyboard(session))
    session['process_message'] = process_message
    session['preview_path'] = preview_path
    shutil.rmtree(preview_dir, ignore_errors=True)

@app.on_message(filters.command("rec"))
async def rec_command(client, message: Message):
    # Delete the user's /rec command immediately (0s).
    try:
        await message.delete()
    except Exception:
        pass

    if not await _verification_required(message):
        return

    """
    /rec has two modes:

    Direct URL:
        /rec <URL> <DURATION> <FILENAME>
        Filename is REQUIRED.

    Channel:
        /rec <CHANNEL> <DURATION> [FILENAME]
        /rec <CHANNEL> <VARIANT> <DURATION> [FILENAME]
        Filename is OPTIONAL; DEFAULT_FILENAME is used when omitted.
    """
    raw_args=list(getattr(message,"command",[]) or [])
    if not raw_args:
        raw_args=(getattr(message,"text","") or "").strip().split()
    if raw_args and str(raw_args[0]).lstrip("/").casefold()=="rec":
        args=raw_args[1:]
    else:
        args=raw_args
        if not bot_settings.get("no_need_rec",False):
            return await message.reply_text("❌ **No need /rec is currently OFF.**")
    if len(args) < 2:
        return await message.reply_text(
            "❌ **Invalid Format!**\n\n"
            "📌 **Direct URL:**\n"
            "```\n/rec <LINK> <DURATION> <FILENAME>\n```\n"
            "Example: `/rec https://example.com/stream 00:00:30 MyVideo`\n\n"
            "📺 **Channel:**\n"
            "```\n/rec <CHANNEL> <DURATION> [FILENAME]\n```\n"
            "Example: `/rec SonyYay 01:00:00 MyVideo`\n"
            "Filename can be omitted for channels."
        )

    uid = _rec_actor_id(message)
    if uid is None:
        return await message.reply_text("❌ **Unable to identify the recording session.**")
    # A user may have up to MAX_RECORDINGS_PER_USER simultaneous recordings.
    # A setup session counts as one slot, but an existing recording must NOT
    # block a new /rec request. This is intentionally based on processing_tasks
    # rather than user_tasks, because user_tasks stores only legacy/latest state.
    active_count = _active_recording_count(uid)
    setup_count = 1 if uid in rec_sessions else 0
    if active_count + setup_count >= MAX_RECORDINGS_PER_USER:
        return await message.reply_text(
            f"❌ **Recording Limit Reached!**\n\n"
            f"You already have `{active_count + setup_count}` active recording/setup(s).\n"
            f"Maximum allowed: `{MAX_RECORDINGS_PER_USER}`."
        )

    source_name = args[0].strip()
    raw_source_name = source_name

    # Channel mode supports both:
    #   /rec Nick 00:00:30 ls
    #   /rec pogo 3 00:00:30 ls
    # The optional numeric value after the channel name is treated as a
    # channel/stream variant and is resolved through Channel.py.
    channel_variant = None
    if (
        not source_name.lower().startswith(("http://", "https://"))
        and len(args) >= 3
        and str(args[1]).strip().isdigit()
        and time_to_seconds(args[2].strip()) > 0
    ):
        channel_variant = str(args[1]).strip()
        duration = args[2].strip()
        filename_start_index = 3
    else:
        duration = args[1].strip()
        filename_start_index = 2

    if time_to_seconds(duration) <= 0:
        return await message.reply_text("❌ Invalid duration. Use `HH:MM:SS`.")

    # Direct HTTP(S) URL mode.
    is_direct_url = source_name.lower().startswith(("http://", "https://"))

    if is_direct_url:
        # Direct URLs MUST have an explicit filename.
        if len(args) < 3:
            return await message.reply_text(
                "❌ **Filename is required for direct URLs.**\n\n"
                "📌 **Correct Usage:**\n"
                "```\n/rec <LINK> <DURATION> <FILENAME>\n```\n"
                "💡 Example:\n"
                "`/rec https://example.com/stream 00:00:30 MyVideo`"
            )

        raw_filename = " ".join(args[2:]).strip()
        if not raw_filename:
            return await message.reply_text(
                "❌ **Filename is required for direct URLs.**"
            )

        url = source_name

    else:
        # Channel mode: filename is optional.
        raw_filename = (
            " ".join(args[filename_start_index:]).strip()
            if len(args) > filename_start_index
            else config.DEFAULT_FILENAME
        )

        # Sony LIV special: a base Sony name resolves to the HD source when
        # both SD and HD entries exist. The menu still shows one channel name.
        if channel_variant is None and _is_sony_source_name(source_name):
            preferred_sony = _sony_preferred_channel_name(source_name)
            if preferred_sony:
                source_name = preferred_sony

        # Channel URL is automatically obtained from Channel.py.
        if channel_variant is not None:
            # Channel.py installations commonly expose variants as either
            # "channel 3" or "channel_3". Try the explicit variant key first.
            variant_candidates = [
                f"{source_name} {channel_variant}",
                f"{source_name}_{channel_variant}",
                f"{source_name}-{channel_variant}",
            ]
            url = None
            for candidate in variant_candidates:
                url = await _resolve_channel_source(candidate)
                if url:
                    break

            # If Channel.py exposes get_channel_url(name, variant), support
            # that form too without breaking the normal one-argument API.
            if not url:
                try:
                    candidate_url = get_channel_url(source_name, int(channel_variant))
                    if isinstance(candidate_url, str) and candidate_url.strip().lower().startswith(("http://", "https://")):
                        url = candidate_url.strip()
                except TypeError:
                    pass
                except Exception as e:
                    LOG.warning("Channel variant lookup failed for '%s %s': %s", source_name, channel_variant, e)
        else:
            url = await _resolve_channel_source(source_name)

        if not url:
            return await message.reply_text(
                "❌ **Next channel link not found.**\n\n"
                f"📺 **Channel:** `{source_name}`\n\n"
                "Use `/Channel` to view available channels."
            )

    raw_filename = _safe_filename(raw_filename)

    detect_msg = await message.reply_text("🔍 **Auto Detecting video/audio streams...**")
    # Temporary detection message is removed automatically after 10 seconds.
    asyncio.create_task(_delete_message_after(detect_msg, 10))
    heights, lang_indexes, selected_video_index = await _probe_streams(url)

    # A failed/unreachable URL must show the dedicated invalid-link popup.
    # Do not misreport a connection/HTTP/probe failure as 'no audio tracks'.
    if lang_indexes is None:
        invalid_msg = await message.reply_text(
            "❌ **Link 404 / Invalid Link**\n\n"
            "The provided link is invalid or unavailable.\n\n"
            "Please check the link and try again."
        )
        # Keep the invalid-link popup visible for 30 seconds, then remove it.
        asyncio.create_task(_delete_message_after(invalid_msg, 30))
        return

    detected_audio = {lang for lang, indexes in lang_indexes.items() if indexes}
    if not detected_audio:
        return await message.reply_text("❌ **No real audio tracks detected by FFprobe.**")

    # Termux/Android may not allow writing to /tmp.
    # Keep temporary preview files inside the bot's configured download directory.
    preview_root = join(config.DOWNLOAD_DIRECTORY, "_rec_previews")
    preview_dir = join(preview_root, f"rec_preview_{uid}_{secrets.token_hex(4)}")
    os.makedirs(preview_dir, exist_ok=True)
    preview_path = join(preview_dir, "preview.jpg")
    if not await _capture_live_preview(url, preview_path):
        shutil.rmtree(preview_dir, ignore_errors=True)
        return await message.reply_text("❌ **Unable to capture live preview from this stream.**")

    callback_token = secrets.token_hex(8)
    session = {
        "message": message,
        "actor_id": uid,
        "chat_id": getattr(getattr(message, "chat", None), "id", None),
        "url": url,
        "raw_source_name": raw_source_name,
        "callback_token": callback_token,
        "timestamp": duration,
        "raw_filename": raw_filename,
        "quality": "auto",  # Sony quality is automatic; highest HLS variant is selected
        "audio": set(detected_audio),
        "lang_indexes": lang_indexes,
        "watermark": "off",
        "step": "audio",
        "detected_heights": heights,
        "selected_video_index": selected_video_index,
        "sony_quality_mode": ("hd" if str(raw_source_name).strip().casefold().endswith(" hd") else "sd" if str(raw_source_name).strip().casefold().endswith(" sd") else "auto"),
        "preview_path": preview_path,
    }

    caption = "🎬 **Stream Preview**\n\n🖼️ Screenshot captured from the live stream.\n\n" + _audio_text(session)
    process_message = await client.send_photo(
        message.chat.id, photo=preview_path, caption=caption,
        reply_markup=_audio_keyboard(session)
    )
    session["process_message"] = process_message
    rec_sessions[uid] = session
    rec_session_tokens[callback_token] = uid
    shutil.rmtree(preview_dir, ignore_errors=True)


async def handle_record(client, message, selection=None):
    # Anonymous admins have no from_user. The setup stores actor_id, which is
    # the allowed group chat ID for anonymous-admin recordings.
    user_obj = getattr(message, "from_user", None)
    user_id = selection.get("actor_id") if isinstance(selection, dict) else None
    if user_id is None and user_obj is not None:
        user_id = getattr(user_obj, "id", None)
    if user_id is None:
        chat_obj = getattr(message, "chat", None)
        user_id = getattr(chat_obj, "id", None)
    if user_id is None:
        raise ValueError("Unable to identify recording actor")
    msg = None
    save_dir = None
    ffmpeg_process = None
    video_path = None
    thumb_path = None
    preview_task = None

    try:
        if selection is None:
            raise Exception("Recording selection was not provided")
        url = selection["url"]
        timestamp = selection["timestamp"]
        raw_filename = selection["raw_filename"]
        recording_start_dt = datetime.now(tz)
        recording_start_label = recording_start_dt.strftime("%I:%M:%S%p")
        recording_date_label = recording_start_dt.strftime("%d-%m-%Y")
        quality_label = selection["quality"] if selection["quality"] != "auto" else "Auto"
        selected_count = len(selection.get("audio", []))
        audio_type = {
            1: "Single", 2: "Dual", 3: "Triple", 4: "Quad"
        }.get(selected_count, "Multi")
        filename = (
            f"{raw_filename.strip()}.[{recording_date_label}].[{recording_start_label}]."
            f"{quality_label}.WEB-DL.{audio_type}.UNK.-namebot.mkv"
        )
        process_message = selection.get("process_message")
        save_dir = join(config.DOWNLOAD_DIRECTORY, str(int(time.time())))
        os.makedirs(save_dir, exist_ok=True)
        video_path = join(save_dir, filename)

        task_id = selection.get("task_id") or secrets.token_hex(8)
        active_recordings_by_actor.setdefault(user_id, set()).add(task_id)
        user_tasks[user_id] = task_id
        user_status[user_id] = {
            "id": task_id,
            "filename": raw_filename.strip(),
            "target": timestamp,
            "progress": "00:00:00",
            "save_dir": save_dir,
            "username": getattr(getattr(message, "from_user", None), "username", None) or "anonymous",
            "user_id": user_id,
            "process_message": process_message,
            "status": "Recording",
            "start_ts": time.time(),
            "speed": "Calculating...",
            "remaining": timestamp,
            "cancelled": False,
            "output_filename": filename,
        }
        processing_tasks[task_id] = {
            "owner_id": user_id,
            "task_id": task_id,
            "filename": filename,
            "status": "Recording",
            "start_ts": time.time(),
            "target_seconds": time_to_seconds(timestamp),
            "process": None,
            "updater": None,
            "preview_task": None,
            "save_dir": save_dir,
            "video_path": video_path,
            "message": process_message,
            "user_message": message,
            "selection": selection,
        }

        recording_start = time.time()
        duration = time_to_seconds(timestamp)

        def processing_keyboard(kind="recording"):
            if kind == "upload":
                first = InlineKeyboardButton("📦 Uploading", callback_data=f"progress:{task_id}")
            else:
                first = InlineKeyboardButton("⚡ Rec Progress", callback_data=f"progress:{task_id}")
            return InlineKeyboardMarkup([[
                first,
                InlineKeyboardButton("❌ Cancel", callback_data=f"cancel:{task_id}")
            ]])

        async def update_recording_progress():
            while task_id in active_recordings_by_actor.get(user_id, set()) and task_id in processing_tasks:
                state = processing_tasks[task_id]
                if state.get("cancelled"):
                    break
                elapsed = max(time.time() - recording_start, 0)
                remaining = max(duration - elapsed, 0)
                pct = min((elapsed / duration) * 100, 100) if duration else 0
                if user_status.get(user_id, {}).get("id") == task_id:
                    user_status[user_id]["progress"] = TimeFormatter(int(elapsed * 1000))
                    user_status[user_id]["remaining"] = TimeFormatter(int(remaining * 1000))
                state["progress"] = pct
                state["elapsed"] = elapsed
                state["remaining"] = remaining
                await asyncio.sleep(2)

        progress_task = asyncio.create_task(update_recording_progress())
        progress_tasks[user_id] = progress_task
        processing_tasks[task_id]["updater"] = progress_task
        if process_message:
            try:
                await process_message.edit_caption(
                    f"🎬 **Processing Video...**\n\n"
                    f"📄 **File:**\n`{filename}`\n\n"
                    f"⚡ **Speed:**\nCalculating...\n\n"
                    f"Status:\nRecording",
                    reply_markup=processing_keyboard("recording")
                )
            except Exception:
                pass

        # Build FFmpeg args as a list. Never concatenate untrusted user input into a shell command.
        args = [
            "ffmpeg", "-y", "-probesize", "10000000", "-analyzeduration", "15000000",
            "-f", "hls", "-i", url,
        ]

        is_sony = _is_sony_source_name(selection.get("raw_source_name", ""))
        sony_video_index = (selection.get("quality_video_index") if is_sony and selection.get("quality_video_index") is not None
                            else selection.get("selected_video_index") if is_sony else None)

        # Select video and the user-selected audio languages.
        # Sony HLS master playlists expose multiple video programs. Never use
        # 0:v:0 for Sony because that can select the 144p first variant.
        # FFprobe has already identified the highest-resolution stream index.
        if is_sony and sony_video_index is not None:
            args += ["-map", f"0:{int(sony_video_index)}"]
        else:
            args += ["-map", "0:v:0"]
        selected_audio_indexes = []
        lang_indexes = selection.get("lang_indexes", {})
        for audio_key in selection["audio"]:
            if audio_key.startswith("UNKNOWN:"):
                try:
                    unknown_pos = int(audio_key.split(":", 1)[1])
                    unknown_indexes = lang_indexes.get("UNKNOWN", [])
                    if 0 <= unknown_pos < len(unknown_indexes):
                        selected_audio_indexes.append(int(unknown_indexes[unknown_pos]))
                except (ValueError, TypeError):
                    continue
            else:
                selected_audio_indexes.extend(lang_indexes.get(audio_key, []))

        if not selected_audio_indexes:
            raise Exception("Selected audio track(s) were not found in the detected stream metadata.")
        selected_audio_indexes = sorted(set(int(idx) for idx in selected_audio_indexes))
        for idx in selected_audio_indexes:
            args += ["-map", f"0:{idx}"]

        # Dynamic audio metadata: first 3 selected real tracks share the Premium handler;
        # remaining tracks use the detected language name.
        index_to_lang = {}
        for lang, indexes in selection.get("lang_indexes", {}).items():
            for idx in indexes:
                index_to_lang[int(idx)] = lang
        for output_index, source_index in enumerate(selected_audio_indexes):
            lang_name = index_to_lang.get(source_index, "UNKNOWN")
            handler = _audio_title_for_count(len(selected_audio_indexes))
            lang_code = next((code for code in LANG_CODES.get(lang_name, set()) if len(code) == 3), None)
            args += [f"-metadata:s:a:{output_index}", f"handler_name={handler}"]
            args += [f"-metadata:s:a:{output_index}", f"title={handler}"]
            if lang_code:
                args += [f"-metadata:s:a:{output_index}", f"language={lang_code}"]

        quality = selection["quality"]

        # Automatic quality detector:
        # - Sony LIV: automatically target the highest detected source quality,
        #   preferring 1080p whenever a 1080p stream is available.
        # - Other channels: keep the existing Auto behavior unchanged.
        if quality == "auto" and is_sony:
            detected_heights = selection.get("detected_heights") or []
            numeric_heights = []
            for h in detected_heights:
                try:
                    numeric_heights.append(int(h))
                except (TypeError, ValueError):
                    pass
            max_height = max(numeric_heights, default=0)
            sony_quality_mode = str(selection.get("sony_quality_mode", "auto")).casefold()
            if sony_quality_mode == "hd":
                # Sony LIV HD: choose the highest master-playlist variant;
                # 1080p is selected automatically whenever available.
                if max_height >= 1080:
                    quality = "1080"
                elif max_height >= 720:
                    quality = "720"
                elif max_height >= 576:
                    quality = "576"
                elif max_height >= 480:
                    quality = "480"
                else:
                    quality = "auto"
            elif sony_quality_mode == "sd":
                # Sony LIV SD: stay at or below SD range; never promote an
                # SD catalog entry to a 720p/1080p output.
                sd_heights = [h for h in numeric_heights if h <= 576]
                max_sd = max(sd_heights, default=0)
                if max_sd >= 576:
                    quality = "576"
                elif max_sd >= 480:
                    quality = "480"
                elif max_sd >= 360:
                    quality = "360" if "360" in QUALITY_LABELS else "auto"
                else:
                    quality = "auto"
            else:
                if max_height >= 1080:
                    quality = "1080"
                elif max_height >= 720:
                    quality = "720"
                elif max_height >= 576:
                    quality = "576"
                elif max_height >= 480:
                    quality = "480"
                else:
                    quality = "auto"

        wm = "off"  # Watermark feature disabled
        vf = None
        target_height = {"360": 360, "480": 480, "576": 576, "720": 720, "1080": 1080}.get(quality)
        # Scale to the requested maximum size while preserving the source
        # aspect ratio. No 16:9 canvas or black bars are added.
        if target_height:
            target_width = {360: 640, 480: 854, 576: 1024, 720: 1280, 1080: 1920}[target_height]
            scale = f"scale={target_width}:{target_height}:force_original_aspect_ratio=decrease"
        elif wm in ("wm1", "wm2", "text"):
            scale = "scale=1920:1080:force_original_aspect_ratio=decrease"
        else:
            scale = None
        if scale:
            if wm == "wm1":
                vf = scale + ",drawtext=text='Join Our Telegram - AnimeCartoonPremium':fontfile=/system/fonts/Roboto-Regular.ttf:fontsize=24:fontcolor=white:x=(w-tw)/2:y=h-th-140:shadowcolor=black:shadowx=2:shadowy=2:enable='between(t,10,50)+between(t,1200,1260)'"
            elif wm == "wm2":
                vf = scale + ",drawtext=text='Join Our Telegram - AnimeCartoonPremium':fontfile=/system/fonts/Roboto-Regular.ttf:fontsize=24:fontcolor=white:x=(w-tw)/2:y=130:shadowcolor=black:shadowx=2:shadowy=2"
            elif wm == "text":
                text = selection.get("watermark_text", "")
                vf = scale + f",drawtext=text='{text}':fontfile=/system/fonts/Roboto-Regular.ttf:fontsize=24:fontcolor=white:x=(w-tw)/2:y=130:shadowcolor=black:shadowx=2:shadowy=2"
            else:
                vf = scale

        if vf:
            args += ["-vf", vf, "-c:v", "libx264", "-crf", "23", "-preset", "ultrafast", "-threads", "2"]
        else:
            args += ["-c:v", "copy"]
        args += ["-c:a", "aac", "-t", timestamp, video_path]

        # Auto quality: keep the source video dimensions/aspect ratio unchanged.
        # No 16:9 canvas and no black bars are added.
        if wm == "off" and quality == "auto":
            auto_video_map = (f"0:{int(sony_video_index)}" if is_sony and sony_video_index is not None else "0:v:0")
            args = ["ffmpeg", "-y", "-probesize", "10000000", "-analyzeduration", "15000000", "-f", "hls", "-i", url, "-map", auto_video_map]
            for idx in sorted(set(selected_audio_indexes)):
                args += ["-map", f"0:{idx}"]
            for output_index, source_index in enumerate(sorted(set(selected_audio_indexes))):
                lang_name = index_to_lang.get(source_index, "UNKNOWN")
                handler = _audio_title_for_count(len(selected_audio_indexes))
                args += [f"-metadata:s:a:{output_index}", f"handler_name={handler}", f"-metadata:s:a:{output_index}", f"title={handler}"]
                lang_code = next((code for code in LANG_CODES.get(lang_name, set()) if len(code) == 3), None)
                if lang_code:
                    args += [f"-metadata:s:a:{output_index}", f"language={lang_code}"]
            args += ["-c:v", "copy", "-c:a", "copy", "-t", timestamp, video_path]

        async def preview_updater():
            preview_dir = join(save_dir, "live_preview")
            os.makedirs(preview_dir, exist_ok=True)
            try:
                while user_id in user_tasks and user_tasks.get(user_id) == task_id and user_id not in cancelled_users:
                    await asyncio.sleep(10)
                    if user_id not in user_tasks or user_id in cancelled_users:
                        break
                    latest = join(preview_dir, f"preview_{int(time.time())}.jpg")
                    if await _capture_live_preview(url, latest):
                        try:
                            if process_message:
                                elapsed = max(time.time() - recording_start, 0)
                                remaining = max(duration - elapsed, 0)
                                preview_caption = (
                                    f"🎬 **Processing Video...**\n\n"
                                    f"📄 **File:**\n`{filename}`\n\n"
                                    f"⚡ **Speed:**\nCalculating...\n\n"
                                    f"Status:\nRecording"
                                )
                                await process_message.edit_media(
                                    InputMediaPhoto(media=latest, caption=preview_caption),
                                    reply_markup=processing_keyboard("recording")
                                )
                        except Exception as e:
                            LOG.debug("Preview edit failed: %s", e)
                        try:
                            os.remove(latest)
                        except OSError:
                            pass
            finally:
                shutil.rmtree(preview_dir, ignore_errors=True)

        preview_task = asyncio.create_task(preview_updater())
        processing_tasks[task_id]["preview_task"] = preview_task

        ffmpeg_process = await asyncio.create_subprocess_exec(
            *args, stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.PIPE
        )
        user_ffmpeg_pids[user_id] = ffmpeg_process.pid
        processing_tasks[task_id]["process"] = ffmpeg_process
        LOG.info("Started FFmpeg process %s for user %s", ffmpeg_process.pid, user_id)
        stdout, stderr = await ffmpeg_process.communicate()
        retcode = ffmpeg_process.returncode
        user_ffmpeg_pids.pop(user_id, None)
        if preview_task:
            preview_task.cancel()
            try:
                await preview_task
            except asyncio.CancelledError:
                pass
            preview_task = None
        if user_id in progress_tasks:
            progress_tasks[user_id].cancel()
            progress_tasks.pop(user_id, None)

        was_cancelled = user_id in cancelled_users
        if retcode != 0 and not was_cancelled:
            raise Exception(f"🚫 FFmpeg Error:\n{stderr.decode(errors='ignore')[-3500:]}")
        if was_cancelled:
            if save_dir and os.path.exists(save_dir):
                shutil.rmtree(save_dir, ignore_errors=True)
            if process_message:
                try:
                    await process_message.edit_caption(
                        "❌ **Process Cancelled**\n⚠️ **Partial Output Deleted**",
                        reply_markup=None
                    )
                except Exception:
                    try:
                        await process_message.edit_text(
                            "❌ **Process Cancelled**\n⚠️ **Partial Output Deleted**",
                            reply_markup=None
                        )
                    except Exception:
                        pass
            return

        if not os.path.exists(video_path) or os.path.getsize(video_path) == 0:
            raise Exception("🚫 No video file created or file is empty")

        msg = process_message
        if msg:
            processing_tasks[task_id]["status"] = "Uploading"
            try:
                await msg.edit_caption(
                    f"📦 **Uploading:**\n`{filename}`\n\n⏳ Preparing upload...",
                    reply_markup=processing_keyboard("upload")
                )
            except Exception:
                pass

        dur = await get_duration_ffmpeg(video_path)
        if dur == 0:
            dur = time_to_seconds(timestamp)
        fixed_video_path = join(save_dir, f"fixed_{filename}")
        fix_args = ["ffmpeg", "-y", "-i", video_path, "-map", "0", "-c", "copy",
                    "-metadata", f"creation_time={time.strftime('%Y-%m-%dT%H:%M:%S')}", fixed_video_path]
        fix_process = await asyncio.create_subprocess_exec(*fix_args, stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.PIPE)
        _, fix_err = await fix_process.communicate()
        if fix_process.returncode == 0:
            os.replace(fixed_video_path, video_path)
        else:
            LOG.warning("Metadata fix failed: %s", fix_err.decode(errors="ignore")[-1000:])

        rand_sec = random.randint(5, max(dur - 5, 6))
        thumb_path = join(save_dir, "thumb.jpg")
        thumb_args = ["ffmpeg", "-y", "-ss", str(rand_sec), "-i", video_path, "-vframes", "1", "-q:v", "2", thumb_path]
        thumb_process = await asyncio.create_subprocess_exec(*thumb_args, stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.PIPE)
        await thumb_process.communicate()

        # Final output name includes actual recording end time.
        recording_end_label = datetime.now(tz).strftime("%I:%M:%S%p")
        final_filename = (
            f"{raw_filename.strip()}.[{recording_date_label}]."
            f"[{recording_start_label}-{recording_end_label}]."
            f"{quality_label}.WEB-DL.{audio_type}.UNK.-namebot.mkv"
        )
        final_video_path = join(save_dir, final_filename)
        if video_path != final_video_path and os.path.exists(video_path):
            os.replace(video_path, final_video_path)
            video_path = final_video_path
            filename = final_filename
            processing_tasks[task_id]["filename"] = filename
            user_status[user_id]["output_filename"] = filename

        # Upload through the existing system.  The completion caption uses the
        # actual final filename and task ID; bot username is resolved automatically.
        try:
            _bot_me = await app.get_me()
            _bot_username = getattr(_bot_me, "username", None) or "unknown"
        except Exception:
            _bot_username = "unknown"

        caption = (
            f"🎬 **{filename}**\n\n"
            f"⏱ **Duration:** `{TimeFormatter(dur * 1000)}`\n"
            f"📁 **Format:** MKV\n"
            f"🆔 **Task ID:** `{task_id}`\n"
            f"🤖 **Bot:** @{_bot_username}\n\n"
            f"{'⚠️ _Recording was cancelled, but recorded portion is sent_' if was_cancelled else '✅ _Recording completed successfully!_'}"
        )
        start_time = time.time()
        processing_tasks[task_id]["status"] = "Uploading"
        processing_tasks[task_id]["upload_start"] = start_time
        await message.reply_video(
            video=video_path, caption=caption, duration=dur,
            thumb=thumb_path if os.path.exists(thumb_path) else None,
            progress=progress_for_pyrogram,
            progress_args=(message, start_time, msg, save_dir, was_cancelled)
        )
        # Files are removed after upload. Uploaded Telegram video is not affected.
        if save_dir and os.path.exists(save_dir):
            shutil.rmtree(save_dir, ignore_errors=True)

    except Exception as e:
        LOG.error("Error in handle_record: %s", e)
        try:
            err_text = str(e)
            if len(err_text) > 1500:
                err_text = err_text[:1500] + "... [truncated]"
            # Keep any partial output so it can be inspected/recovered.
            # Do not delete save_dir on processing failure.
            target_msg = msg or process_message
            if target_msg:
                partial_name = raw_filename.strip()
                try:
                    if save_dir and os.path.isdir(save_dir):
                        candidates = [
                            x for x in os.listdir(save_dir)
                            if os.path.isfile(os.path.join(save_dir, x))
                        ]
                        if candidates:
                            # Prefer the newest/largest media-like file when available.
                            media = [x for x in candidates if x.lower().endswith((".mkv", ".mp4", ".ts", ".m4v"))]
                            if media:
                                partial_name = max(
                                    media,
                                    key=lambda x: os.path.getsize(os.path.join(save_dir, x))
                                )
                            else:
                                partial_name = candidates[0]
                except Exception:
                    pass
                failure_text = (
                    f"❌ **Processing Failed**\n"
                    f"⚠️ **Partial Output Available**\n"
                    f"📄 **File:**\n`{partial_name}`\n"
                    f"🆔 **Task ID:** `{task_id}`"
                )
                try:
                    await target_msg.edit_caption(failure_text, reply_markup=None)
                except Exception:
                    try:
                        await target_msg.edit_text(failure_text, reply_markup=None)
                    except Exception:
                        pass
        except Exception as exc:
            LOG.error("Failed to handle recording error: %s", exc)
    finally:
        if user_status.get(user_id, {}).get("id") == task_id:
            user_status.pop(user_id, None)
        if user_tasks.get(user_id) == task_id:
            user_tasks.pop(user_id, None)
        if user_ffmpeg_pids.get(user_id) == task_id:
            user_ffmpeg_pids.pop(user_id, None)
        if progress_tasks.get(user_id) == task_id:
            progress_tasks.pop(user_id, None)
        processing_tasks.pop(task_id, None)
        actor_tasks = active_recordings_by_actor.get(user_id)
        if actor_tasks is not None:
            actor_tasks.discard(task_id)
            if not actor_tasks:
                active_recordings_by_actor.pop(user_id, None)
        cancelled_users.discard(user_id)


async def progress_for_pyrogram(current, total, message, start, msg, save_dir=None, was_cancelled=False):
    if not msg or total <= 0:
        return

    now = time.time()
    elapsed = max(now - start, 0.001)
    percentage = min(current * 100 / total, 100)
    speed = current / elapsed
    remaining = (total - current) / speed if speed > 0 else 0
    uploaded_mb = current / (1024 * 1024)
    total_mb = total / (1024 * 1024)
    speed_mb = speed / (1024 * 1024)

    task_id = None
    for tid, state in processing_tasks.items():
        if state.get("message") is msg:
            task_id = tid
            state["status"] = "Uploading"
            state["upload_progress"] = percentage
            state["upload_speed"] = speed_mb
            state["upload_remaining"] = remaining
            state["uploaded_mb"] = uploaded_mb
            state["total_mb"] = total_mb
            break

    bar_len = 10
    filled = int(bar_len * percentage / 100)
    bar = "🟩" * filled + "⬜" * (bar_len - filled)
    filename = "output_file"
    if task_id and task_id in processing_tasks:
        filename = processing_tasks[task_id].get("filename", filename)

    text = (
        f"📦 **Uploading:**\n`{filename}`\n\n"
        f"[{bar}] {percentage:.2f}%\n"
        f"{uploaded_mb:.2f} MB of {total_mb:.2f} MB\n\n"
        f"Speed:\n{speed_mb:.2f} MB/s\n\n"
        f"Time Left:\n{int(remaining)}s"
    )

    try:
        if msg.photo:
            await msg.edit_caption(
                text,
                reply_markup=InlineKeyboardMarkup([[
                    InlineKeyboardButton("📦 Uploading", callback_data=f"progress:{task_id}"),
                    InlineKeyboardButton("❌ Cancel", callback_data=f"cancel:{task_id}")
                ]]) if task_id else None
            )
        else:
            await msg.edit_text(text)
    except Exception:
        pass

    if current == total:
        completion = (
            "📦 **Upload Completed! Successfully!**\n\n"
            "🗑️ **Temporary files cleaned up!**\n\n"
            f"`{filename}`"
        )
        try:
            if msg.photo:
                await msg.edit_caption(completion, reply_markup=None)
            else:
                await msg.edit_text(completion, reply_markup=None)
        except Exception:
            pass

        async def delete_processing_message():
            await asyncio.sleep(20)
            try:
                await msg.delete()
            except Exception:
                pass

        asyncio.create_task(delete_processing_message())


@app.on_callback_query(filters.regex(r"^progress:"))
async def task_progress_callback(client, query):
    task_id = query.data.split(":", 1)[1]
    state = processing_tasks.get(task_id)
    if not state:
        return await query.answer("❌ Process is no longer active.", show_alert=True, cache_time=0)

    owner_id = state.get("owner_id")
    if query.from_user.id != owner_id and not _is_owner(query.from_user.id):
        return await query.answer("❌ You do not have permission.", show_alert=True, cache_time=0)

    status = state.get("status", "Recording")
    username = query.from_user.username or "anonymous"
    user_id = query.from_user.id

    if status == "Uploading":
        pct = state.get("upload_progress", 0)
        speed = state.get("upload_speed", 0)
        remaining = state.get("upload_remaining", 0)
        up = state.get("uploaded_mb", 0)
        total = state.get("total_mb", 0)
        bar_len = 10
        bar = "🟩" * int(bar_len * pct / 100) + "⬜" * (bar_len - int(bar_len * pct / 100))
        text = (
            f"📦 Uploading\n\n{state.get('filename')}\n\n"
            f"[{bar}] {pct:.2f}%\n"
            f"Size {up:.2f} MB of {total:.2f} MB\n\n"
            f"Speed:\n{speed:.2f} MB/s\n\n"
            f"Time Left:\n{int(remaining)}s\n\n"
            f"👤 @{username}\n🆔 {user_id}"
        )
    else:
        elapsed = max(time.time() - state.get("start_ts", time.time()), 0)
        remaining = max(state.get("target_seconds", 0) - elapsed, 0)
        pct = min((elapsed / state["target_seconds"]) * 100, 100) if state.get("target_seconds") else 0
        bar_len = 10
        bar = "🟩" * int(bar_len * pct / 100) + "⬜" * (bar_len - int(bar_len * pct / 100))
        text = (
            f"📦 Rec\n\n{state.get('filename')}\n\n"
            f"[{bar}] {pct:.2f}%\n\n"
            f"Status:\n{status}\n\n"
            f"Elapsed:\n{TimeFormatter(int(elapsed * 1000))}\n"
            f"Remaining:\n{TimeFormatter(int(remaining * 1000))}\n"
            f"Speed:\nCalculating...\n\n"
            f"👤 @{username}\n🆔 {user_id}"
        )

    return await query.answer(text[:190], show_alert=True, cache_time=0)


@app.on_callback_query(filters.regex(r"^cancel:"))
async def task_cancel_callback(client, query):
    task_id = query.data.split(":", 1)[1]
    state = processing_tasks.get(task_id)
    if not state:
        return await query.answer("❌ Process is no longer active.", show_alert=True, cache_time=0)

    owner_id = state.get("owner_id")
    if query.from_user.id != owner_id and not _is_owner(query.from_user.id):
        return await query.answer("❌ You do not have permission to cancel.", show_alert=True, cache_time=0)

    await query.answer("Cancelling process...", show_alert=True, cache_time=0)
    state["cancelled"] = True
    cancelled_users.add(owner_id)

    updater = state.get("updater")
    if updater and not updater.done():
        updater.cancel()

    preview_task = state.get("preview_task")
    if preview_task and not preview_task.done():
        preview_task.cancel()

    process = state.get("process")
    if process and process.returncode is None:
        try:
            process.terminate()
            await asyncio.wait_for(process.wait(), timeout=3)
        except Exception:
            try:
                process.kill()
            except Exception:
                pass

    save_dir = state.get("save_dir")
    if save_dir and os.path.exists(save_dir):
        shutil.rmtree(save_dir, ignore_errors=True)

    msg = state.get("message")
    if msg:
        try:
            if msg.photo:
                await msg.edit_caption(
                    "❌ **Process Cancelled**\n⚠️ **Partial Output Deleted**",
                    reply_markup=None
                )
            else:
                await msg.edit_text(
                    "❌ **Process Cancelled**\n⚠️ **Partial Output Deleted**",
                    reply_markup=None
                )
        except Exception:
            pass


async def runcmd(cmd: str) -> Tuple[int, str, str]:
    args = shlex.split(cmd)
    process = await asyncio.create_subprocess_exec(
        *args,
        stdout=asyncio.subprocess.PIPE,
        stderr=asyncio.subprocess.PIPE
    )
    stdout, stderr = await process.communicate()
    return process.returncode, stdout.decode(), stderr.decode()


async def get_video_duration(input_file: str) -> int:
    try:
        parser = createParser(input_file)
        if not parser:
            return 0
        metadata = extractMetadata(parser)
        if not metadata or not metadata.has("duration"):
            return 0
        duration = metadata.get("duration")
        return int(duration.seconds)
    except Exception as e:
        LOG.warning(f"Hachoir failed: {e}")
        return 0


async def get_duration_ffmpeg(input_file: str) -> int:
    try:
        cmd = f'ffprobe -v error -show_entries format=duration -of default=noprint_wrappers=1:nokey=1 "{input_file}"'
        retcode, out, err = await runcmd(cmd)
        if retcode == 0:
            return int(float(out.strip()))
    except Exception as e:
        LOG.warning(f"FFprobe failed: {e}")
    return 0


def time_to_seconds(time_str: str) -> int:
    """Convert a strict HH:MM:SS duration to seconds."""
    try:
        value = str(time_str).strip()
        match = re.fullmatch(r"(\d+):(\d{2}):(\d{2})", value)
        if not match:
            return 0
        h, m, s = map(int, match.groups())
        if m >= 60 or s >= 60:
            return 0
        return h * 3600 + m * 60 + s
    except (TypeError, ValueError):
        return 0


def TimeFormatter(milliseconds: int) -> str:
    seconds, ms = divmod(milliseconds, 1000)
    minutes, sec = divmod(seconds, 60)
    hours, min_ = divmod(minutes, 60)
    
    if hours > 0:
        return f"{hours:02}:{min_:02}:{sec:02}"
    else:
        return f"{min_:02}:{sec:02}"


# ============================================================================
# Video Tools Menu (v23)
# Shown automatically when a video/video-document is uploaded or forwarded.
# ============================================================================
VIDEO_TOOL_STATES = {}
WATERMARK_IMAGE_URL = "https://iili.io/CuMJCjn.md.png"
WATERMARK_MAX_SECONDS = 30
VIDEO_TOOL_DELETE_SECONDS = 20


def _video_tool_keyboard():
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("🎵 Audio Track", callback_data="vtool:audio")],
        [InlineKeyboardButton("✂️ Trim Video", callback_data="vtool:trim")],
        [InlineKeyboardButton("💧 Watermark", callback_data="vtool:watermark")],
        [InlineKeyboardButton("📸 Screenshot", callback_data="vtool:screenshot")],
    ])


def _video_media_info(message):
    if not message:
        return None
    media = getattr(message, "video", None)
    if media:
        return {
            "file_id": media.file_id,
            "file_name": media.file_name or "video.mp4",
            "file_size": media.file_size or 0,
        }
    media = getattr(message, "document", None)
    if media:
        name = media.file_name or "video.mp4"
        mime = (media.mime_type or "").lower()
        if mime.startswith("video/") or name.lower().endswith((".mp4", ".mkv", ".mov", ".webm", ".avi", ".ts", ".m4v")):
            return {
                "file_id": media.file_id,
                "file_name": name,
                "file_size": media.file_size or 0,
            }
    return None


async def _delete_later(message, delay=VIDEO_TOOL_DELETE_SECONDS):
    try:
        await asyncio.sleep(delay)
        await message.delete()
    except Exception:
        pass


def _tool_bar(percent):
    pct = max(0, min(100, int(percent)))
    filled = min(10, int(pct / 10))
    return "🟩" * filled + "⬜" * (10 - filled)


def _tool_status(title, percent, extra=""):
    text = f"{title}\n[{_tool_bar(percent)}] {int(percent)}%"
    return text + (f"\n\n{extra}" if extra else "")


def _parse_range(value):
    m = re.fullmatch(r"\s*(\d{1,2}:\d{2}:\d{2})\s+to\s+(\d{1,2}:\d{2}:\d{2})\s*", value or "", re.I)
    if not m:
        return None
    start = time_to_seconds(m.group(1))
    end = time_to_seconds(m.group(2))
    if end <= start:
        return None
    return start, end


def _escape_drawtext(text):
    # FFmpeg drawtext escaping for user-provided watermark text.
    return (str(text).replace("\\", r"\\").replace(":", r"\\:")
            .replace("'", r"\\'").replace("%", r"\\%"))


async def _download_tool_media(client, info, path, status):
    await client.download_media(
        info["file_id"],
        file_name=str(path),
        progress=lambda current, total: _tool_download_progress(status, current, total),
    )


async def _tool_download_progress(status, current, total):
    try:
        pct = (current * 100 / total) if total else 0
        await status.edit_text(_tool_status("📥 Downloading...", pct))
    except Exception:
        pass


async def _tool_upload_progress(status, current, total):
    try:
        pct = (current * 100 / total) if total else 0
        await status.edit_text(_tool_status("📤 Uploading...", pct))
    except Exception:
        pass


async def _run_tool_ffmpeg(command, progress_path, duration, status, processing_title="⚙️ Processing / Watermarking..."):
    proc = await asyncio.create_subprocess_exec(
        *command,
        stdout=asyncio.subprocess.DEVNULL,
        stderr=asyncio.subprocess.PIPE,
    )

    async def updater():
        while proc.returncode is None:
            pct = 0
            try:
                values = {}
                if os.path.exists(progress_path):
                    for line in Path(progress_path).read_text(errors="ignore").splitlines():
                        if "=" in line:
                            k, v = line.split("=", 1)
                            values[k] = v
                current = float(values.get("out_time_ms", "0") or 0) / 1_000_000
                if duration:
                    pct = min(100, current * 100 / duration)
            except Exception:
                pass
            try:
                await status.edit_text(_tool_status(processing_title, pct))
            except Exception:
                pass
            await asyncio.sleep(2)

    task = asyncio.create_task(updater())
    _, stderr = await proc.communicate()
    task.cancel()
    await asyncio.gather(task, return_exceptions=True)
    if proc.returncode != 0:
        raise RuntimeError(stderr.decode(errors="replace")[-1500:] or "FFmpeg failed")


async def _process_video_tool(client, message, info, mode, params):
    user = getattr(message, "from_user", None)
    uid = getattr(user, "id", 0) if user else 0
    task_dir = Path(getattr(config, "DOWNLOAD_DIRECTORY", "/tmp")) / f"video_tool_{uid}_{secrets.token_hex(6)}"
    task_dir.mkdir(parents=True, exist_ok=True)
    source_name = _safe_filename(info["file_name"]) if "_safe_filename" in globals() else info["file_name"]
    input_path = task_dir / source_name
    stem = Path(source_name).stem or "video"
    output_name = _safe_filename(params.get("name", f"{stem}_processed.mp4")) if "_safe_filename" in globals() else params.get("name", f"{stem}_processed.mp4")
    if not output_name.lower().endswith(".mp4"):
        output_name += ".mp4"
    output_path = task_dir / output_name
    progress_path = task_dir / "progress.txt"
    status = await message.reply_text(_tool_status("📥 Downloading...", 0))
    try:
        await _download_tool_media(client, info, input_path, status)
        duration = await get_duration_ffmpeg(str(input_path))
        if duration <= 0:
            raise RuntimeError("Unable to read video duration.")

        if mode == "trim":
            start, end = params["range"]
            duration = end - start
            command = [
                "ffmpeg", "-hide_banner", "-nostdin", "-y", "-ss", str(start), "-i", str(input_path),
                "-t", str(duration), "-map", "0:v:0", "-map", "0:a?",
                "-vf", "scale=1920:1080", "-c:v", "libx264", "-preset", "ultrafast",
                "-crf", "23", "-pix_fmt", "yuv420p", "-c:a", "aac", "-b:a", "128k",
                "-movflags", "+faststart", "-progress", str(progress_path), "-nostats", str(output_path),
            ]
            processing_title = "⚙️ Processing / Trimming..."
        elif mode.startswith("watermark"):
            start, end = params["range"]
            duration = end - start
            if mode == "watermark1":
                text = _escape_drawtext(params["watermark_text"])
                vf = (
                    "scale=1920:1080,drawtext="
                    f"text='{text}':fontfile=/system/fonts/Roboto-Regular.ttf:fontsize=24:"
                    "fontcolor=white:x=(w-tw)/2:y=h-th-140:shadowcolor=black:shadowx=2:shadowy=2:"
                    "enable='between(t,10,30)'"
                )
                command = [
                    "ffmpeg", "-hide_banner", "-nostdin", "-y", "-ss", str(start), "-i", str(input_path),
                    "-t", str(duration), "-map", "0:v:0", "-map", "0:a?", "-vf", vf,
                    "-c:v", "libx264", "-preset", "ultrafast", "-crf", "23", "-pix_fmt", "yuv420p",
                    "-c:a", "aac", "-b:a", "128k", "-movflags", "+faststart", "-progress", str(progress_path),
                    "-nostats", str(output_path),
                ]
            else:
                image_path = task_dir / "watermark.png"
                urllib_request = __import__("urllib.request", fromlist=["urlopen"])
                with urllib_request.urlopen(WATERMARK_IMAGE_URL, timeout=30) as resp:
                    image_path.write_bytes(resp.read())
                if mode == "watermark2":
                    overlay = "[base][watermark]overlay=20:main_h-overlay_h-60:enable='between(t,10,30)'[outv]"
                else:
                    overlay = "[base][watermark]overlay=(main_w-overlay_w)/2:(main_h-overlay_h)/2:enable='between(t,10,30)'[outv]"
                command = [
                    "ffmpeg", "-hide_banner", "-nostdin", "-y", "-ss", str(start), "-i", str(input_path),
                    "-i", str(image_path), "-t", str(duration), "-filter_complex",
                    "[0:v]scale=1920:1080,setsar=1[base];[1:v]scale=240:-1[watermark];" + overlay,
                    "-map", "[outv]", "-map", "0:a?", "-c:v", "libx264", "-crf", "23", "-preset", "ultrafast",
                    "-threads", "2", "-c:a", "aac", "-b:a", "128k", "-movflags", "+faststart",
                    "-progress", str(progress_path), "-nostats", str(output_path),
                ]
            processing_title = "⚙️ Processing / Watermarking..."
        else:
            raise RuntimeError("Unknown video tool.")

        # Use the requested processing label while FFmpeg runs.
        try:
            await status.edit_text(_tool_status(processing_title, 0))
        except Exception:
            pass
        await _run_tool_ffmpeg(command, progress_path, duration, status, processing_title)
        if not output_path.exists() or output_path.stat().st_size < 1024:
            raise RuntimeError("FFmpeg produced an empty output file.")
        await status.edit_text(_tool_status("📤 Uploading...", 0))
        with output_path.open("rb") as fh:
            await client.send_video(
                message.chat.id,
                fh,
                caption=f"📄 File: {output_name}",
                supports_streaming=True,
                reply_to_message_id=message.id,
                progress=lambda current, total: _tool_upload_progress(status, current, total),
            )
        await status.edit_text(f"✅ Update Complete\n📄 File: {output_name}")
        asyncio.create_task(_delete_later(status, VIDEO_TOOL_DELETE_SECONDS))
        asyncio.create_task(_delete_later(message, VIDEO_TOOL_DELETE_SECONDS))
    except Exception as exc:
        try:
            await status.edit_text(f"❌ Processing Failed\n\n{str(exc)[:1200]}")
            asyncio.create_task(_delete_later(status, VIDEO_TOOL_DELETE_SECONDS))
        except Exception:
            pass
    finally:
        shutil.rmtree(task_dir, ignore_errors=True)


@app.on_message((filters.video | filters.document) & ~filters.command(["rec", "drec", "reclink"]))
async def video_tools_menu(client, message: Message):
    if not _video_media_info(message):
        return
    # Keep an explicit reference to the uploaded/forwarded video.  Do not
    # depend only on Telegram's reply_to_message relation when a button is
    # pressed; some forwarded/media layouts can lose that relation.
    menu = await message.reply_text(
        "🎬 **Video Tools**\n\nChoose an action:",
        reply_markup=_video_tool_keyboard(),
    )
    menu_key = (int(message.from_user.id) if message.from_user else 0, int(message.chat.id), int(message.id))
    VIDEO_TOOL_STATES[menu_key] = {
        "mode": "menu",
        "info": _video_media_info(message),
        "original_id": int(message.id),
        "menu_id": int(menu.id),
    }


@app.on_callback_query(filters.regex(r"^vtool:(audio|trim|watermark|screenshot)$"))
async def video_tools_callback(client, query):
    if not query.message:
        return await query.answer("Message unavailable.", show_alert=True)
    # First recover the exact original video from the state saved when the
    # four-button menu was created.  This fixes "Original video not found"
    # when Telegram does not expose the bot menu's reply_to_message relation.
    uid = int(query.from_user.id)
    menu_state = None
    menu_key = None
    for candidate_key, candidate_state in list(VIDEO_TOOL_STATES.items()):
        if (candidate_key[0] == uid and
                candidate_state.get("menu_id") == int(query.message.id) and
                candidate_state.get("mode") == "menu"):
            menu_key = candidate_key
            menu_state = candidate_state
            break

    if menu_state and menu_state.get("info") and menu_state.get("original_id"):
        info = menu_state["info"]
        original_id = int(menu_state["original_id"])
        chat_id = int(menu_key[1]) if menu_key else int(query.message.chat.id)
    else:
        original = query.message.reply_to_message
        info = _video_media_info(original) if original else None
        original_id = int(original.id) if original else 0
        chat_id = int(original.chat.id) if original else int(query.message.chat.id)

    if not info or not original_id:
        return await query.answer("Original video not found. Please upload/forward the video again.", show_alert=True)

    action = query.data.split(":", 1)[1]
    # Use one stable state key for all follow-up replies.
    key = (uid, chat_id, original_id)
    if action == "audio":
        await query.answer()
        await query.message.reply_text(
            "🎵 **Audio Track**\n\nReply to the original video with:\n`/Audiotrack Your_title`"
        )
        return
    if action == "trim":
        VIDEO_TOOL_STATES[key] = {"mode": "trim", "info": info, "original_id": original_id}
        await query.answer()
        prompt = await query.message.reply_text(
            "✂️ **Trim Video**\n\nReply to this video with time range:\n\n`00:00:30 to 00:00:50`"
        )
        VIDEO_TOOL_STATES[key]["prompt_id"] = int(prompt.id)
        return
    if action == "screenshot":
        VIDEO_TOOL_STATES[key] = {"mode": "screenshot", "info": info, "original_id": original_id}
        await query.answer()
        await query.message.reply_text(
            "📸 **Screenshot**\n\nReply to this video with the number of screenshots.\n\nExample:\n`10`"
        )
        return
    VIDEO_TOOL_STATES[key] = {"mode": "watermark_menu", "info": info, "original_id": original_id}
    await query.answer()
    await query.message.reply_text(
        "💧 **Watermark**\n\nChoose watermark:",
        reply_markup=InlineKeyboardMarkup([
            [InlineKeyboardButton("💧 Watermark 1", callback_data="vwm:1")],
            [InlineKeyboardButton("💧 Watermark 2", callback_data="vwm:2")],
            [InlineKeyboardButton("💧 Watermark 3", callback_data="vwm:3")],
        ])
    )


@app.on_callback_query(filters.regex(r"^vwm:[123]$"))
async def video_watermark_callback(client, query):
    if not query.message:
        return await query.answer("Message unavailable.", show_alert=True)
    wm = query.data.split(":", 1)[1]
    uid = int(query.from_user.id)
    # The Watermark 1/2/3 buttons are inside a bot message that is itself a
    # reply to the menu message, so recover the original video from the
    # pending Watermark-menu state rather than assuming query.message is it.
    key = None
    state = None
    for candidate_key, candidate_state in list(VIDEO_TOOL_STATES.items()):
        if candidate_key[0] == uid and candidate_state.get("mode") == "watermark_menu":
            key = candidate_key
            state = candidate_state
            break
    if not state:
        return await query.answer("Watermark session expired. Click Watermark again.", show_alert=True)
    info = state.get("info")
    original_id = state.get("original_id")
    if not info or not original_id:
        return await query.answer("Original video not found.", show_alert=True)
    VIDEO_TOOL_STATES[key] = {"mode": f"watermark{wm}", "info": info, "original_id": original_id}
    await query.answer()
    prompt = await query.message.reply_text(
        f"💧 **Watermark {wm}**\n\nReply to this video with time range:\n\n`00:00:10 to 00:00:30`"
    )
    VIDEO_TOOL_STATES[key]["prompt_id"] = int(prompt.id)


@app.on_message(filters.text & ~filters.command("Audiotrack"))
async def video_tools_text_input(client, message: Message):
    if not message.reply_to_message or not message.from_user:
        return

    # Accept replies to either the original video OR the bot's active prompt.
    # This is important because users naturally reply to the Trim/Screenshot/
    # Watermark prompt after clicking the button, rather than reopening the
    # original media message.
    uid = int(message.from_user.id)
    replied = message.reply_to_message
    key = None
    state = None

    original = replied
    if _video_media_info(original):
        candidate_key = (uid, int(original.chat.id), int(original.id))
        candidate_state = VIDEO_TOOL_STATES.get(candidate_key)
        if candidate_state:
            key, state = candidate_key, candidate_state

    if state is None:
        replied_id = int(replied.id)
        for candidate_key, candidate_state in list(VIDEO_TOOL_STATES.items()):
            if candidate_key[0] != uid:
                continue
            if int(candidate_state.get("prompt_id", 0) or 0) == replied_id:
                key, state = candidate_key, candidate_state
                break

    if not state or not key:
        return

    mode = state.get("mode")
    text = (message.text or "").strip()

    if mode in ("trim", "watermark1", "watermark2", "watermark3") and "range" not in state:
        rng = _parse_range(text)
        if not rng:
            return await message.reply_text("❌ Use this format: `00:00:30 to 00:00:50`")
        state["range"] = rng
        if mode == "trim":
            state["name_pending"] = True
            prompt = await message.reply_text("✏️ **Rename File**\n\nReply with the new filename.")
            state["prompt_id"] = int(prompt.id)
            return
        state["name_pending"] = True
        prompt = await message.reply_text("✏️ **Rename File**\n\nReply with the new filename.")
        state["prompt_id"] = int(prompt.id)
        return

    if state.get("name_pending"):
        name = text.strip()
        if not name:
            return await message.reply_text("❌ Filename cannot be empty.")
        state["name"] = name
        state.pop("name_pending", None)
        if mode.startswith("watermark"):
            state["watermark_text_pending"] = True
            prompt = await message.reply_text("💧 **Watermark Text**\n\nReply with the watermark text.")
            state["prompt_id"] = int(prompt.id)
            return
        VIDEO_TOOL_STATES.pop(key, None)
        asyncio.create_task(_process_video_tool(client, message, state["info"], mode, state))
        return

    if state.get("watermark_text_pending"):
        if not text:
            return await message.reply_text("❌ Watermark text cannot be empty.")
        state["watermark_text"] = text
        VIDEO_TOOL_STATES.pop(key, None)
        asyncio.create_task(_process_video_tool(client, message, state["info"], mode, state))
        return

    if mode == "screenshot":
        try:
            count = int(text)
        except ValueError:
            return await message.reply_text("❌ Please send a number, for example `10`.")
        if count < 1 or count > 20:
            return await message.reply_text("❌ Screenshot count must be between 1 and 20.")
        VIDEO_TOOL_STATES.pop(key, None)
        task_dir = Path(getattr(config, "DOWNLOAD_DIRECTORY", "/tmp")) / f"screenshots_{message.from_user.id}_{secrets.token_hex(6)}"
        task_dir.mkdir(parents=True, exist_ok=True)
        status = await message.reply_text(_tool_status("📥 Downloading...", 0))
        try:
            input_path = task_dir / _safe_filename(state["info"]["file_name"])
            await _download_tool_media(client, state["info"], input_path, status)
            duration = await get_duration_ffmpeg(str(input_path))
            if duration <= 0:
                raise RuntimeError("Unable to read video duration.")
            await status.edit_text("⚙️ **Processing / Screenshot...**")
            sent = 0
            for i in range(count):
                ts = duration * (i + 1) / (count + 1)
                shot = task_dir / f"screenshot_{i+1:02d}.jpg"
                proc = await asyncio.create_subprocess_exec(
                    "ffmpeg", "-hide_banner", "-loglevel", "error", "-y", "-ss", str(ts), "-i", str(input_path),
                    "-frames:v", "1", "-q:v", "2", str(shot),
                    stdout=asyncio.subprocess.DEVNULL, stderr=asyncio.subprocess.PIPE,
                )
                await proc.communicate()
                if proc.returncode == 0 and shot.exists():
                    await client.send_photo(message.chat.id, str(shot), caption=f"📸 Screenshot {i+1}/{count}", reply_to_message_id=original.id)
                    sent += 1
            await status.edit_text(f"✅ Update Complete\n📸 Screenshots: {sent}")
            asyncio.create_task(_delete_later(status, VIDEO_TOOL_DELETE_SECONDS))
            asyncio.create_task(_delete_later(message, VIDEO_TOOL_DELETE_SECONDS))
        except Exception as exc:
            try:
                await status.edit_text(f"❌ Screenshot Failed\n\n{str(exc)[:1200]}")
                asyncio.create_task(_delete_later(status, VIDEO_TOOL_DELETE_SECONDS))
            except Exception:
                pass
        finally:
            shutil.rmtree(task_dir, ignore_errors=True)


async def _bot_main():
    global schedule_worker_task
    await app.start()
    if schedule_worker_task is None or schedule_worker_task.done():
        schedule_worker_task = asyncio.create_task(_schedule_worker(app))
    try:
        await idle()
    finally:
        if schedule_worker_task and not schedule_worker_task.done():
            schedule_worker_task.cancel()
        await app.stop()


if __name__ == "__main__":
    print("🎬 Starting Video Recorder Bot...")
    print("⚡ Bot is now running!")
    app.run(_bot_main())
