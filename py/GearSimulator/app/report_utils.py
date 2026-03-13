import re


def extract_report_code(value: str) -> str:
    """
    Accepts either a plain report code or a full FFLogs report URL.
    Returns the code (e.g., AbC123xYz7890).
    """
    value = value.strip()
    if "reports/" in value:
        m = re.search(r"reports/([A-Za-z0-9]+)", value)
        if m:
            return m.group(1)
    return value
