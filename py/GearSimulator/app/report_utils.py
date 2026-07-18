import re


REPORT_CODE_PATTERN = re.compile(r"^[A-Za-z0-9]+$")


def extract_report_code(value: str) -> str:
    """Return a validated FFLogs report code or an empty string."""
    text = str(value or "").strip()
    if "reports/" in text:
        match = re.search(r"reports/([A-Za-z0-9]+)", text)
        text = match.group(1) if match else ""
    if not REPORT_CODE_PATTERN.fullmatch(text):
        return ""
    return text
