"""CSL JSON export for Zotero and citation processors."""

from __future__ import annotations

import json
import re
from typing import Any


def build_csl_json(records: list[dict[str, Any]]) -> str:
    return json.dumps([_record_to_csl(record) for record in records], ensure_ascii=False, indent=2) + "\n"


def _record_to_csl(record: dict[str, Any]) -> dict[str, Any]:
    year = _year(record.get("year"))
    item = {
        "type": "article-journal",
        "id": record.get("doi") or record.get("title") or "",
        "title": record.get("title") or "",
        "container-title": record.get("journal") or "",
        "author": [{"literal": str(author)} for author in record.get("authors") or []],
    }
    if year:
        item["issued"] = {"date-parts": [[year]]}
    if record.get("doi"):
        item["DOI"] = record["doi"]
    if record.get("url"):
        item["URL"] = record["url"]
    for source, target in (("volume", "volume"), ("issue", "issue"), ("pages", "page")):
        if record.get(source):
            item[target] = str(record[source])
    return item


def _year(value: Any) -> int | None:
    match = re.search(r"\d{4}", str(value or ""))
    return int(match.group(0)) if match else None
