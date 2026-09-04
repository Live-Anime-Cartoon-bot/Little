from os import environ

# 🔧 Bot Configuration Settings
# ⚙️ Get values from environment variables or use defaults

API_ID = int(environ.get("API_ID", "29481626"))
API_HASH = environ.get("API_HASH", "4892185769903521077c4cea97808b8c")
BOT_TOKEN = environ.get("BOT_TOKEN", "8787494799:AAE1qRO_HmSVpKeCrQKSJNoypUQ9tqOBpho")

# 👥 Authorized Users - Bot will work only with these users
AUTH_USERS = list(map(int, environ.get("AUTH_USERS", "5856009289 87654321").split()))

# 👑 Owner/Admin ID - Multiple owners supported
OWNER_ID = list(map(int, environ.get("OWNER_IDS", "5856009289").split()))

# 📁 Download Directory - Where temporary files are stored
DOWNLOAD_DIRECTORY = environ.get("DOWNLOAD_DIRECTORY", "./downloads")

# 🏷️ Default Metadata - Video file metadata title
DEFAULT_METADATA = environ.get("DEFAULT_METADATA", "")

# 📄 Default Filename - Used when no filename is provided
DEFAULT_FILENAME = environ.get("DEFAULT_FILENAME", "Little Singham Bot")

# 🌍 Timezone Configuration
TIMEZONE = environ.get("TIMEZONE", "Asia/Kolkata")


# 🔗 Link Shortener Configuration
SHORTENER = environ.get("SHORTENER", "shrinkme.io")
SHORTENER_API = environ.get("SHORTENER_API", "9503d9bf87c90aa9e0aab35d4dec7d1ce24c0a23")
