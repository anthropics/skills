import re

_CITIES = (
    r"seattle|brooklyn|nyc|new york|san francisco|los angeles|chicago|"
    r"boston|austin|portland|denver|miami"
)

_PROCESSOR_PREFIX = re.compile(r"^(sq\s*\*|tst\s*\*|paypal\s*\*|sp\s*\*)\s*", re.IGNORECASE)
_AMZN_SUFFIX = re.compile(r"\s*\*[a-z0-9]+$", re.IGNORECASE)
_STORE_NUM = re.compile(r"\s*#\d+\b|\s+store\s+\d+\b|\s+t-?\d+\b", re.IGNORECASE)
_DATE = re.compile(r"\s*\b\d{2}/\d{2}\b")
_LONG_DIGITS = re.compile(r"\s*\b\d{4,}\b")
_CITY_STATE = re.compile(rf"\s+(?:{_CITIES})\s+[a-z]{{2}}$", re.IGNORECASE)
_TRAILING_CITY = re.compile(rf"\s+(?:{_CITIES})$", re.IGNORECASE)
_WHITESPACE = re.compile(r"\s+")


def normalize_merchant(raw: str) -> str:
    s = (raw or "").strip().lower()
    s = _PROCESSOR_PREFIX.sub("", s)
    s = _AMZN_SUFFIX.sub("", s)
    s = _STORE_NUM.sub("", s)
    s = _DATE.sub("", s)
    s = _LONG_DIGITS.sub("", s)
    s = _CITY_STATE.sub("", s)
    s = _TRAILING_CITY.sub("", s)
    s = _WHITESPACE.sub(" ", s).strip()
    return s
