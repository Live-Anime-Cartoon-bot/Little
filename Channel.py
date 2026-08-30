# Channel.py
# Public channel catalog for the existing Telegram bot.
# NOTE: URLs are retained exactly as supplied by the project owner.
# Only use sources you are authorized/permitted to access.

PUBLIC_CHANNELS = {
    "POGO": "https://ranapkx.site/RANAPK33k/TVD/play.php?id=372993",
    "DISCOVERY KIDS": "https://ranapkx.site/RANAPK33k/TVD/play.php?id=372928",
    "Pogo 1": "http://202.70.146.135:8000/play/a0a7/index.m3u8",
    "Wow kidz": "https://yuppparoriglin.akamaized.net/181224/smil:wowkidzhindi.smil/playlist.m3u8?hdnts=st=1735898689~exp=1835898688~acl=*~hmac=f5fe24724fe05481e3841f9eb5ab8efdee0a3dd83645ae9dcf45703f525bab7b",
    "MINIX": "https://vodzong.mjunoon.tv:8087/streamtest/157-1M/chunks.m3u8",
    "POGO 2": "https://bdix.spidy.online/MAC/SBHGOLD/play.php?id=281410",
    "DISCOVERY KIDS 2": "http://line.sweetv.xyz/play/live.php?mac=00:1A:79:00:03:B2&stream=1540017&extension=ts&play_token=eFCOqzrsPI",
    "DISNEY CHANNEL": "http://103.155.18.191:8000/play/a01q/index.m3u8",
    "NICK 2": "http://103.155.18.191:8000/play/a04c/index.m3u8",
    "CARTOON NETWORK 2": "http://202.70.146.135:8000/play/a0a8/index.m3u8",
    "CARTOON NETWORK HD+": "http://202.70.146.135:8000/play/a0a3/index.m3u8",
    "DISCOVERY KIDS 3": "http://202.70.146.135:8000/play/a0a6/index.m3u8",
    "Epic kids": "https://cc-t8lqe1o99pszu.akamaized.net/v1/master/3722c60a815c199d9c0ef36c5b73da68a62b09d1/cc-t8lqe1o99pszu/playlist.m3u8",
    "Pogo 3": "http://66.102.126.10:8000/play/a00d/index.m3u8",
    "Pogo 4": "http://202.70.146.135:8000/play/a0a7/index.m3u8",
}

def get_public_channels():
    """Return a copy so callers cannot mutate the catalog accidentally."""
    return dict(PUBLIC_CHANNELS)

def get_channel_url(name: str):
    """Return a channel URL by case-insensitive name, or None."""
    if not isinstance(name, str):
        return None
    key = name.strip().casefold()
    if not key:
        return None
    for channel, url in PUBLIC_CHANNELS.items():
        if channel.casefold() == key:
            return url
    return None
