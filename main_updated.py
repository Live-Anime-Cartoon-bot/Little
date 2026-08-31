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
from urllib.parse import urlencode
from urllib.request import urlopen
import psutil
from typing import Tuple
from os.path import join
from hachoir.metadata import extractMetadata
from hachoir.parser import createParser
from pyrogram import Client, filters, idle
from pyrogram.types import Message, InlineKeyboardMarkup, InlineKeyboardButton
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

app = Client("recorder", bot_token=config.BOT_TOKEN, api_id=config.API_ID, api_hash=config.API_HASH)

user_status = {}
user_tasks = {}
user_ffmpeg_pids = {}
progress_tasks = {}
cancelled_users = set()  # Track cancelled users

# Maximum simultaneous recordings allowed for one user.
MAX_RECORDINGS_PER_USER = 9

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

def _is_owner(user_id: int) -> bool:
    """Owners bypass verification/token quotas and have unlimited recording access."""
    try:
        return int(user_id) in {int(owner_id) for owner_id in config.AUTH_USERS}
    except (TypeError, ValueError):
        return False


async def _verification_required(message: Message) -> bool:
    # Owner accounts have unlimited recording access; token/quota rules do not apply.
    if _is_owner(message.from_user.id):
        return True

    # Premium users have direct access and do not need the 6-hour token.
    if _is_premium(message.from_user.id):
        return True
    if _has_valid_access(message.from_user.id):
        return True
    await message.reply_text("🔐 **Verification Required**\n\nVerification is required to use this command.", reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("🔑 Token Generator", callback_data="token_generate")]]))
    return False

_load_verification_store()
_load_premium_store()


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



async def shorten_url(url: str) -> str:
    """Shorten a URL with the configured ShrinkMe API.

    Falls back to the original URL if the API key is missing or shortening fails.
    """
    api_key = getattr(config, "SHORTENER_API", "")
    shortener = getattr(config, "SHORTENER", "shrinkme.io")

    if not api_key:
        LOG.warning("Shortener API key missing; using original verification URL.")
        return url

    api_url = f"https://{shortener}/api?" + urlencode({
        "api": api_key,
        "url": url
    })

    def _request():
        with urlopen(api_url, timeout=15) as response:
            return json.loads(response.read().decode("utf-8"))

    try:
        data = await asyncio.to_thread(_request)
        short_url = data.get("shortenedUrl") if isinstance(data, dict) else None

        if isinstance(short_url, str) and short_url.startswith(("http://", "https://")):
            LOG.info("Verification URL shortened successfully.")
            return short_url

        LOG.warning("Shortener returned an invalid response: %s", data)

    except Exception as e:
        LOG.error("URL shortening failed: %s", e)

    return url

@app.on_callback_query(filters.regex(r"^token_generate$"))
async def token_generate_callback(client, query):
    user_id = query.from_user.id
    if _has_valid_access(user_id):
        return await query.answer("Verification is already active.", show_alert=True)

    await query.answer("Generating verification token...")
    token = _new_verification_token(user_id)
    me = await client.get_me()
    deep_link = f"https://t.me/{me.username}?start=verify_{token}"

    await query.message.reply_text(
        "🔑 **Generate Token**\n\n"
        "Tap **Verify Now** to verify your token.\n\n"
        "⏳ Access: **6 hours** after verification.",
        reply_markup=InlineKeyboardMarkup([
            [InlineKeyboardButton("🔐 Verify Now", url=short_link)]
        ])
    )

# ---------------------------------------------------------------------------\n# Premium administration — Owner only\n# ---------------------------------------------------------------------------\n\n@app.on_message(filters.command("premium_add") & filters.user(config.AUTH_USERS))\nasync def premium_add_command(client, message: Message):\n    args = message.command[1:]\n    if not args:\n        return await message.reply_text(\n            "❌ **Invalid Format**\\n\\n"\n            "`/premium_add <user_id> [duration] [plan_name]`\\n\\n"\n            "Examples:\\n"\n            "`/premium_add 123456789` — 30 days Standard\\n"\n            "`/premium_add 123456789 59m` — 59 minutes Standard\\n"\n            "`/premium_add 123456789 30 minute` — 30 minutes Standard\\n"\n            "`/premium_add 123456789 1h` — 1 hour Standard\\n"\n            "`/premium_add 123456789 2h Pro` — 2 hours Pro\\n"\n            "`/premium_add 123456789 24h` — 24 hours Standard\\n"\n            "`/premium_add 123456789 7` — 7 days Standard\\n"\n            "`/premium_add 123456789 90 Pro` — 90 days Pro\\n"\n            "`/premium_add 123456789 forever` — Lifetime"\n        )\n    try:\n        user_id=int(args[0])\n        if user_id<=0: raise ValueError\n    except ValueError:\n        return await message.reply_text("❌ Invalid user ID.")\n\n    duration_seconds, forever = (30*86400, False)\n    duration_arg_count=0\n    if len(args)>=2:\n        duration_seconds, forever = _parse_premium_duration(args[1])\n        duration_arg_count=1\n        if not forever and duration_seconds is None and len(args)>=3:\n            duration_seconds, forever = _parse_premium_duration(f"{args[1]} {args[2]}")\n            duration_arg_count=2\n        if not forever and duration_seconds is None:\n            return await message.reply_text("❌ Invalid duration. Use `30`, `59m`, `1h`, `30 minute`, or `forever`.")\n    plan_name=" ".join(args[1+duration_arg_count:]).strip() or "Standard"\n    now=time.time()\n    record={"plan":plan_name,"added_by":str(message.from_user.id),"added_at":now,"forever":bool(forever)}\n    if forever:\n        record["expires"]=None\n        expiry_text="Lifetime"\n    else:\n        record["expires"]=now+duration_seconds\n        expiry_text=_format_premium_expiry(record)\n    premium_users[str(user_id)]=record\n    _save_premium_store()\n    await message.reply_text(\n        "✅ **Premium Added Successfully**\\n\\n"\n        f"👤 **User ID:** `{user_id}`\\n"\n        f"💠 **Plan:** `{plan_name}`\\n"\n        f"⏳ **Expiry:** `{expiry_text}`\\n\\n"\n        "🔓 Premium users have direct access without verification."\n    )\n\n@app.on_message(filters.command("Premium_Exipire") & filters.user(config.AUTH_USERS))\nasync def premium_expire_command(client, message: Message):\n    args=message.command[1:]\n    if len(args)!=1:\n        return await message.reply_text("❌ **Invalid Format**\\n\\n`/Premium_Exipire <user_id>`")\n    try:\n        user_id=int(args[0])\n        if user_id<=0: raise ValueError\n    except ValueError:\n        return await message.reply_text("❌ Invalid user ID.")\n    key=str(user_id)\n    if key not in premium_users:\n        return await message.reply_text(f"❌ No active premium found for `{user_id}`.")\n    premium_users.pop(key,None)\n    _save_premium_store()\n    await message.reply_text(\n        "✅ **Premium Expired Successfully**\\n\\n"\n        f"👤 **User ID:** `{user_id}`\\n"\n        "🔐 Verification will be required again for protected commands."\n    )\n\n\n@app.on_message(filters.command("cancel"))
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
        "• 🛑 `/cancel` - Stop ongoing recording (sends recorded portion)\n"
        "• 📊 `/status` - Check current recording progress\n"
        "• 🏠 `/start` - Show welcome message\n"
        "• 💰 `/plan` - View subscription plans\n"
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
text_watermark_pending = set()

QUALITY_LABELS = {
    "480": "480p",
    "576": "576p",
    "720": "720p",
    "1080": "1080p",
    "auto": "⚡ Auto",
}
AUDIO_LANGS = ["Hindi", "Tamil", "Telugu", "Kannada", "Malayalam", "Marathi", "English"]
LANG_CODES = {
    "Hindi": {"hin", "hi", "hindi"},
    "Tamil": {"tam", "ta", "tamil"},
    "Telugu": {"tel", "te", "telugu"},
    "Kannada": {"kan", "kn", "kannada"},
    "Malayalam": {"mal", "ml", "malayalam"},
    "Marathi": {"mar", "mr", "marathi"},
    "English": {"eng", "en", "english"},
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
    try:
        url = get_channel_url(source)
    except Exception as e:
        LOG.warning("Channel.py lookup failed for '%s': %s", source, e)
        return None
    if isinstance(url, str) and url.strip().lower().startswith(("http://", "https://")):
        LOG.info("Channel '%s' URL loaded from Channel.py", source)
        return url.strip()
    return None

async def _probe_streams(url: str):
    """Probe video/audio streams and return (video_heights, language_indexes)."""
    cmd = [
        "ffprobe", "-v", "error", "-print_format", "json",
        "-show_streams", "-probesize", "10000000", "-analyzeduration", "15000000", url
    ]
    try:
        proc = await asyncio.create_subprocess_exec(
            *cmd, stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.PIPE
        )
        out, err = await proc.communicate()
        if proc.returncode != 0:
            LOG.warning("ffprobe failed: %s", err.decode(errors="ignore")[-1000:])
            return [], {}
        import json
        data = json.loads(out.decode(errors="ignore"))
        heights = sorted({int(x["height"]) for x in data.get("streams", [])
                          if x.get("codec_type") == "video" and x.get("height")}, reverse=True)
        lang_indexes = {lang: [] for lang in AUDIO_LANGS}
        for stream in data.get("streams", []):
            if stream.get("codec_type") != "audio":
                continue
            tags = stream.get("tags") or {}
            raw = str(tags.get("language") or tags.get("LANGUAGE") or tags.get("title") or "").strip().lower()
            for lang, codes in LANG_CODES.items():
                if raw in codes or any(code in raw.split('-') for code in codes):
                    lang_indexes[lang].append(int(stream.get("index", 0)))
                    break
        return heights, lang_indexes
    except Exception as e:
        LOG.warning("Stream probe failed: %s", e)
        return [], {}


def _quality_buttons(selected: str):
    return [
        [InlineKeyboardButton(("✅ " if selected == "480" else "") + "480p", callback_data="recq:480"),
         InlineKeyboardButton(("✅ " if selected == "576" else "") + "576p", callback_data="recq:576")],
        [InlineKeyboardButton(("✅ " if selected == "720" else "") + "720p", callback_data="recq:720"),
         InlineKeyboardButton(("✅ " if selected == "1080" else "") + "1080p", callback_data="recq:1080")],
        [InlineKeyboardButton(("✅ " if selected == "auto" else "") + "⚡ Auto", callback_data="recq:auto")],
    ]


def _audio_buttons(selected: set):
    rows = []
    for lang in AUDIO_LANGS:
        mark = "✅" if lang in selected else "❎"
        rows.append([InlineKeyboardButton(f"{lang} {mark}", callback_data=f"reca:{lang}")])
    return rows


def _watermark_buttons(selected: str):
    return [
        [InlineKeyboardButton(("✅ " if selected == "wm1" else "") + "1️⃣ Watermark", callback_data="recw:wm1"),
         InlineKeyboardButton(("✅ " if selected == "wm2" else "") + "2️⃣ Watermark", callback_data="recw:wm2")],
        [InlineKeyboardButton(("✅ " if selected == "text" else "") + "📝 Text Watermark", callback_data="recw:text")],
        [InlineKeyboardButton(("✅ " if selected == "recording" else "") + "🎥 Recording", callback_data="recw:recording"),
         InlineKeyboardButton(("✅ " if selected == "off" else "") + "🚫 OFF", callback_data="recw:off")],
    ]


def _selection_keyboard(session):
    rows = _quality_buttons(session["quality"])
    rows += _audio_buttons(session["audio"])
    rows += _watermark_buttons(session["watermark"])
    rows.append([
        InlineKeyboardButton("✅ Continue", callback_data="recs:continue"),
        InlineKeyboardButton("❌ Cancel", callback_data="recs:cancel"),
    ])
    return InlineKeyboardMarkup(rows)


def _selection_text(session):
    selected_audio = ', '.join(sorted(session["audio"])) or "None"
    wm = {
        "wm1": "1️⃣ Watermark",
        "wm2": "2️⃣ Watermark",
        "text": f"📝 Text: `{session.get('watermark_text', '')}`",
        "recording": "🎥 Recording (no watermark)",
        "off": "🚫 OFF (copy/remux)",
    }.get(session["watermark"], "Not selected")
    return (
        "🔍 **Auto Detect**\n"
        "🎥 Video Quality\n"
        f"Selected: **{QUALITY_LABELS[session['quality']]}**\n\n"
        "🔊 Audio Track\n"
        f"Selected: **{selected_audio}**\n\n"
        "💧 Watermark\n"
        f"Selected: **{wm}**\n\n"
        "❗ Audio `✅` = selected/recorded\n"
        "Audio `❎` = not selected\n\n"
        "Choose your options, then press **Continue**."
    )


@app.on_callback_query(filters.regex(r"^recq:"))
async def rec_quality_callback(client, query):
    uid = query.from_user.id
    session = rec_sessions.get(uid)
    if not session:
        return await query.answer("Recording setup expired. Run /rec again.", show_alert=True)
    session["quality"] = query.data.split(":", 1)[1]
    await query.answer(f"Video quality: {QUALITY_LABELS[session['quality']]}")
    await query.message.edit_text(_selection_text(session), reply_markup=_selection_keyboard(session))


@app.on_callback_query(filters.regex(r"^reca:"))
async def rec_audio_callback(client, query):
    uid = query.from_user.id
    session = rec_sessions.get(uid)
    if not session:
        return await query.answer("Recording setup expired. Run /rec again.", show_alert=True)
    lang = query.data.split(":", 1)[1]
    if lang in session["audio"]:
        session["audio"].remove(lang)
    else:
        session["audio"].add(lang)
    await query.answer(f"{lang}: {'selected' if lang in session['audio'] else 'not selected'}")
    await query.message.edit_text(_selection_text(session), reply_markup=_selection_keyboard(session))


@app.on_callback_query(filters.regex(r"^recw:"))
async def rec_watermark_callback(client, query):
    uid = query.from_user.id
    session = rec_sessions.get(uid)
    if not session:
        return await query.answer("Recording setup expired. Run /rec again.", show_alert=True)
    wm = query.data.split(":", 1)[1]
    if wm == "text":
        session["watermark"] = "text"
        text_watermark_pending.add(uid)
        await query.answer()
        await query.message.reply_text("📝 **Enter watermark text:**")
        return
    session["watermark"] = wm
    await query.answer("Watermark option selected")
    await query.message.edit_text(_selection_text(session), reply_markup=_selection_keyboard(session))


@app.on_message(filters.text & ~filters.command(["start", "cancel", "status", "help", "rec"]))
async def watermark_text_message(client, message: Message):
    uid = message.from_user.id
    if uid not in text_watermark_pending or uid not in rec_sessions:
        return
    session = rec_sessions[uid]
    text = message.text.strip()
    if not text:
        return await message.reply_text("❌ Watermark text cannot be empty. Enter it again:")
    session["watermark_text"] = _ffmpeg_drawtext_escape(text)
    text_watermark_pending.discard(uid)
    await message.reply_text(_selection_text(session), reply_markup=_selection_keyboard(session))


@app.on_callback_query(filters.regex(r"^recs:"))
async def rec_setup_callback(client, query):
    uid = query.from_user.id
    session = rec_sessions.get(uid)
    if not session:
        return await query.answer("Recording setup expired. Run /rec again.", show_alert=True)
    action = query.data.split(":", 1)[1]
    if action == "cancel":
        rec_sessions.pop(uid, None)
        text_watermark_pending.discard(uid)
        await query.answer("Cancelled")
        return await query.message.edit_text("❌ **Recording setup cancelled.**")

    if session["watermark"] == "text" and not session.get("watermark_text"):
        return await query.answer("Enter the text watermark first.", show_alert=True)
    if not session["audio"]:
        return await query.answer("Select at least one audio track (✅).", show_alert=True)

    await query.answer("Starting FFmpeg...")
    rec_sessions.pop(uid, None)
    await query.message.edit_text("🎬 **FFmpeg Recording Starting...**")
    await handle_record(client, session["message"], selection=session)


@app.on_message(filters.command("Channel"))
async def channel_command(client, message: Message):
    if not await _verification_required(message):
        return

    channels = get_public_channels()
    if not channels:
        return await message.reply_text("📭 **No channels available.**")

    lines = ["📺 **Available Channels**", ""]
    for name in channels:
        lines.append(f"• `{name}`")

    lines.append("")
    lines.append("🎬 **Record:** `/Rec <CHANNEL> <DURATION>`")
    lines.append("Example: `/Rec POGO 00:00:30`")
    await message.reply_text("\n".join(lines))


@app.on_message(filters.command("rec"))
async def rec_command(client, message: Message):
    if not await _verification_required(message):
        return

    """
    /rec has two modes:

    Direct URL:
        /rec <URL> <DURATION> <FILENAME>
        Filename is REQUIRED.

    Channel:
        /rec <CHANNEL> <DURATION> [FILENAME]
        Filename is OPTIONAL; DEFAULT_FILENAME is used when omitted.
    """
    if len(message.command) < 3:
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

    uid = message.from_user.id
    if uid in user_tasks or uid in rec_sessions:
        return await message.reply_text("❌ **You already have an active recording/setup!**")

    source_name = message.command[1].strip()
    duration = message.command[2].strip()

    if time_to_seconds(duration) <= 0:
        return await message.reply_text("❌ Invalid duration. Use `HH:MM:SS`.")

    # Direct HTTP(S) URL mode.
    is_direct_url = source_name.lower().startswith(("http://", "https://"))

    if is_direct_url:
        # Direct URLs MUST have an explicit filename.
        if len(message.command) < 4:
            return await message.reply_text(
                "❌ **Filename is required for direct URLs.**\n\n"
                "📌 **Correct Usage:**\n"
                "```\n/rec <LINK> <DURATION> <FILENAME>\n```\n"
                "💡 Example:\n"
                "`/rec https://example.com/stream 00:00:30 MyVideo`"
            )

        raw_filename = " ".join(message.command[3:]).strip()
        if not raw_filename:
            return await message.reply_text(
                "❌ **Filename is required for direct URLs.**"
            )

        url = source_name

    else:
        # Channel mode: filename is optional.
        raw_filename = (
            " ".join(message.command[3:]).strip()
            if len(message.command) > 3
            else config.DEFAULT_FILENAME
        )

        # Channel URL is automatically obtained from Channel.py.
        url = await _resolve_channel_source(source_name)

        if not url:
            return await message.reply_text(
                "❌ **Next channel link not found.**\n\n"
                f"📺 **Channel:** `{source_name}`\n\n"
                "Use `/Channel` to view available channels."
            )

    raw_filename = _safe_filename(raw_filename)

    await message.reply_text("🔍 **Auto Detecting video/audio streams...**")
    heights, lang_indexes = await _probe_streams(url)

    session = {
        "message": message,
        "url": url,
        "timestamp": duration,
        "raw_filename": raw_filename,
        "quality": "auto",
        "audio": set(),
        "lang_indexes": lang_indexes,
        "watermark": "off",
        "watermark_text": "",
        "detected_heights": heights,
    }

    rec_sessions[uid] = session
    await message.reply_text(
        _selection_text(session),
        reply_markup=_selection_keyboard(session)
    )


async def handle_record(client, message, selection=None):
    user_id = message.from_user.id
    msg = await message.reply_text("🔄 **Initializing recording...**")
    save_dir = None
    ffmpeg_process = None
    video_path = None
    thumb_path = None

    try:
        if selection is None:
            raise Exception("Recording selection was not provided")
        url = selection["url"]
        timestamp = selection["timestamp"]
        raw_filename = selection["raw_filename"]
        filename = f"{raw_filename.strip()}.mkv"
        save_dir = join(config.DOWNLOAD_DIRECTORY, str(int(time.time())))
        os.makedirs(save_dir, exist_ok=True)
        video_path = join(save_dir, filename)

        user_tasks[user_id] = time.time()
        user_status[user_id] = {
            "id": int(user_tasks[user_id]),
            "filename": raw_filename.strip(),
            "target": timestamp,
            "progress": "00:00:00",
            "save_dir": save_dir,
        }

        recording_start = time.time()
        duration = time_to_seconds(timestamp)

        async def update_recording_progress():
            while user_id in user_tasks:
                if user_id in cancelled_users:
                    break
                elapsed = time.time() - recording_start
                progress_formatted = TimeFormatter(int(elapsed * 1000))
                if user_id in user_status:
                    user_status[user_id]["progress"] = progress_formatted
                percentage = min((elapsed / duration) * 100, 100) if duration > 0 else 0
                eta = (duration - elapsed) if percentage < 100 else 0
                bar_length = 20
                filled_length = int(bar_length * percentage // 100)
                bar = '█' * filled_length + '░' * (bar_length - filled_length)
                progress_text = (
                    f"🎬 **Recording Progress**\n"
                    f"`[{bar}]` {percentage:.1f}%\n"
                    f"⏱️ **Time:** `{progress_formatted} / {TimeFormatter(duration * 1000)}`\n"
                    f"⏳ **ETA:** `{TimeFormatter(int(eta * 1000))}`\n\n"
                    f"🛑 Use /cancel to stop recording"
                )
                try:
                    await msg.edit_text(progress_text)
                except Exception:
                    pass
                await asyncio.sleep(5)

        progress_task = asyncio.create_task(update_recording_progress())
        progress_tasks[user_id] = progress_task
        await msg.edit_text("📥 **Starting FFmpeg recording...**")

        # Build FFmpeg args as a list. Never concatenate untrusted user input into a shell command.
        args = [
            "ffmpeg", "-y", "-probesize", "10000000", "-analyzeduration", "15000000",
            "-i", url,
        ]

        # Select video and the user-selected audio languages.
        args += ["-map", "0:v:0"]
        selected_audio_indexes = []
        for lang in selection["audio"]:
            selected_audio_indexes.extend(selection.get("lang_indexes", {}).get(lang, []))
        if not selected_audio_indexes:
            raise Exception("Selected audio language(s) were not found in the detected stream metadata.")
        for idx in sorted(set(selected_audio_indexes)):
            args += ["-map", f"0:{idx}"]

        quality = selection["quality"]
        wm = selection["watermark"]
        vf = None
        target_height = {"480": 480, "576": 576, "720": 720, "1080": 1080}.get(quality)
        if wm in ("wm1", "wm2", "text") or target_height:
            if target_height:
                scale = f"scale=-2:{target_height}:force_original_aspect_ratio=decrease,pad=iw:ih:(ow-iw)/2:(oh-ih)/2:black"
            else:
                scale = "scale=1920:1080:force_original_aspect_ratio=decrease,pad=1920:1080:(ow-iw)/2:(oh-ih)/2:black"
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

        # OFF means copy/remux mode when possible. If a quality/watermark requires encoding,
        # the selected processing mode takes precedence.
        if wm == "off" and quality == "auto":
            args = ["ffmpeg", "-y", "-probesize", "10000000", "-analyzeduration", "15000000", "-i", url, "-map", "0:v:0"]
            for idx in sorted(set(selected_audio_indexes)):
                args += ["-map", f"0:{idx}"]
            args += ["-c:v", "copy", "-c:a", "copy", "-t", timestamp, video_path]

        ffmpeg_process = await asyncio.create_subprocess_exec(
            *args, stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.PIPE
        )
        user_ffmpeg_pids[user_id] = ffmpeg_process.pid
        LOG.info("Started FFmpeg process %s for user %s", ffmpeg_process.pid, user_id)
        stdout, stderr = await ffmpeg_process.communicate()
        retcode = ffmpeg_process.returncode
        user_ffmpeg_pids.pop(user_id, None)
        if user_id in progress_tasks:
            progress_tasks[user_id].cancel()
            progress_tasks.pop(user_id, None)

        was_cancelled = user_id in cancelled_users
        if retcode != 0 and not was_cancelled:
            raise Exception(f"🚫 FFmpeg Error:\n{stderr.decode(errors='ignore')[-3500:]}")
        if not os.path.exists(video_path) or os.path.getsize(video_path) == 0:
            if was_cancelled:
                await msg.edit_text("❌ **Recording cancelled - no video recorded**")
                return
            raise Exception("🚫 No video file created or file is empty")

        thumbnail_msg = await message.reply_text("🖼 **Generating thumbnail...**")
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
        await thumbnail_msg.delete()

        caption = (
            f"🎬 **{raw_filename.strip()}**\n\n"
            f"⏱ **Duration:** `{TimeFormatter(dur * 1000)}`\n"
            f"📁 **Format:** MKV\n"
            f"👤 **Recorded by:** @{message.from_user.username or 'anonymous'}\n\n"
            f"{'⚠️ _Recording was cancelled, but recorded portion is sent_' if was_cancelled else '✅ _Recording completed successfully!_'}"
        )
        start_time = time.time()
        await message.reply_video(
            video=video_path, caption=caption, duration=dur,
            thumb=thumb_path if os.path.exists(thumb_path) else None,
            progress=progress_for_pyrogram,
            progress_args=(message, start_time, msg, save_dir, was_cancelled)
        )
        if save_dir and os.path.exists(save_dir):
            shutil.rmtree(save_dir)

    except Exception as e:
        LOG.error("Error in handle_record: %s", e)
        try:
            if user_id not in cancelled_users:
                err_text = str(e)
                if len(err_text) > 4000:
                    err_text = err_text[:4000] + "... [truncated]"
                await msg.edit_text(f"❌ **Recording Failed!**\n\n`{err_text}`")
            if user_id not in cancelled_users and save_dir and os.path.exists(save_dir):
                shutil.rmtree(save_dir)
        except Exception as exc:
            LOG.error("Failed to handle recording error: %s", exc)
    finally:
        user_status.pop(user_id, None)
        user_tasks.pop(user_id, None)
        user_ffmpeg_pids.pop(user_id, None)
        progress_tasks.pop(user_id, None)
        cancelled_users.discard(user_id)


async def progress_for_pyrogram(current, total, message, start, msg, save_dir=None, was_cancelled=False):
    now = time.time()
    diff = now - start
    if diff == 0:
        diff = 1
    percentage = current * 100 / total
    speed = current / diff
    
    # Calculate file sizes in MB
    uploaded_mb = current / (1024 * 1024)
    total_mb = total / (1024 * 1024)
    speed_mb = speed / (1024 * 1024)
    
    # Upload progress bar
    bar_length = 15
    filled_length = int(bar_length * percentage // 100)
    bar = '█' * filled_length + '░' * (bar_length - filled_length)
    
    # Update at major milestones
    update_points = [0, 10, 25, 50, 75, 90, 95, 99, 100]
    current_percent = int(percentage)
    
    if current_percent in update_points or current == total:
        eta = TimeFormatter(int((total - current) / speed * 1000)) if speed > 0 else "00:00:00"
        
        status_prefix = "📤 **Uploading Partial Recording**" if was_cancelled else "📤 **Uploading Video**"
        
        text = (
            f"{status_prefix}\n"
            f"`[{bar}]` {percentage:.1f}%\n"
            f"📊 **Progress:** `{uploaded_mb:.1f} / {total_mb:.1f} MB`\n"
            f"⚡ **Speed:** `{speed_mb:.1f} MB/s`\n"
            f"⏳ **ETA:** `{eta}`"
        )
        try:
            await msg.edit_text(text)
        except Exception:
            pass
        
        # Final completion message and cleanup
        if current == total:
            if was_cancelled:
                completion_text = "✅ **Partial Recording Sent!**\n🗑️ **Cleaning up temporary files...**"
            else:
                completion_text = "✅ **Upload Completed Successfully!**\n🗑️ **Cleaning up temporary files...**"
            
            try:
                await msg.edit_text(completion_text)
                
                # Clean up files after upload is complete
                if save_dir and os.path.exists(save_dir):
                    try:
                        shutil.rmtree(save_dir)
                        LOG.info(f"Cleaned up files after upload: {save_dir}")
                        # Update message to show cleanup complete
                        await asyncio.sleep(2)
                        if was_cancelled:
                            await msg.edit_text("✅ **Partial Recording Sent!**\n🗑️ **Temporary files cleaned up!**")
                        else:
                            await msg.edit_text("✅ **Upload Completed Successfully!**\n🗑️ **Temporary files cleaned up!**")
                    except Exception as cleanup_err:
                        LOG.warning(f"Cleanup failed after upload: {cleanup_err}")
                        if was_cancelled:
                            await msg.edit_text("✅ **Partial Recording Sent!**\n⚠️ **Cleanup failed, but video was sent.**")
                        else:
                            await msg.edit_text("✅ **Upload Completed Successfully!**\n⚠️ **Cleanup failed, but video was sent.**")
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
    """Convert HH:MM:SS to seconds"""
    try:
        h, m, s = time_str.split(':')
        return int(h) * 3600 + int(m) * 60 + int(s)
    except:
        return 0


def TimeFormatter(milliseconds: int) -> str:
    seconds, ms = divmod(milliseconds, 1000)
    minutes, sec = divmod(seconds, 60)
    hours, min_ = divmod(minutes, 60)
    
    if hours > 0:
        return f"{hours:02}:{min_:02}:{sec:02}"
    else:
        return f"{min_:02}:{sec:02}"


if __name__ == "__main__":
    print("🎬 Starting Video Recorder Bot...")
    print("⚡ Bot is now running!")
    app.run()
