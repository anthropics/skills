#!/usr/bin/env python3
"""Turn exported application emails into candidates.json and cleaned resume text.

Usage: extract.py EXPORT_DIR OUT_JSON

EXPORT_DIR/<message_id>/ holds body.txt (subject + email body) and the attachments,
as written by export_mail.applescript. For every message this writes
<message_id>/resume_clean.txt and one JSON record (BOSS直聘 metadata, phones, emails,
resume path). Repeat applications under the same name keep only the newest message.
"""
import json
import re
import subprocess
import sys
from pathlib import Path

PHONE = re.compile(r"(?<!\d)1[3-9]\d-?\d{4}-?\d{4}(?!\d)")
EMAIL = re.compile(r"[A-Za-z0-9._%+-]+@[A-Za-z0-9-]+(?:\.[A-Za-z0-9-]+)*\.[A-Za-z]{2,}")
# BOSS直聘 notification line: "张三 男 27岁 重庆 硕士 1年"
META = re.compile(r"^(\S+)\s+(男|女)\s+(\d+)岁\s+(\S+)\s+(\S+)\s+(\S+)\s*$")
IGNORED_EMAIL_DOMAINS = ("zhipin.com",)
RESUME_EXTS = (".pdf", ".docx", ".doc", ".rtf")


def uniq(items):
    return list(dict.fromkeys(items))


def resume_file(d):
    files = [f for f in d.iterdir() if f.suffix.lower() in RESUME_EXTS]
    if not files:
        return None
    pdfs = [f for f in files if f.suffix.lower() == ".pdf"]
    return max(pdfs or files, key=lambda f: f.stat().st_size)


def to_text(f):
    if f.suffix.lower() == ".pdf":
        cmd = ["pdftotext", str(f), "-"]
    else:
        cmd = ["textutil", "-convert", "txt", "-stdout", str(f)]
    return subprocess.run(cmd, capture_output=True, text=True).stdout


def clean(text):
    """Drop the short alphanumeric watermark fragments BOSS直聘 sprinkles through PDFs."""
    out = []
    for line in text.splitlines():
        s = re.sub(r"\s+", " ", line).strip()
        if len(s) <= 2:
            continue
        if re.fullmatch(r"[A-Za-z0-9_-]{30,}", s):
            continue
        if re.fullmatch(r"[A-Za-z0-9_ -]{1,12}", s) and not re.search(r"\d{4}", s):
            continue
        out.append(s)
    return "\n".join(out)


def contacts(text):
    nospace = re.sub(r"[ \t　]+", "", text)
    phones = uniq(p.replace("-", "") for p in PHONE.findall(nospace))
    emails = uniq(e for e in EMAIL.findall(nospace) if not e.lower().endswith(IGNORED_EMAIL_DOMAINS))
    return phones, emails


def parse_body(body):
    lines = [l.strip() for l in body.splitlines()]
    subject = lines[0] if lines else ""
    info = {"subject": subject}
    m = re.search(r"应聘\s*(.+?)\s*(?:\||【|$)", subject)
    if m:
        info["position"] = m.group(1)
    for i, line in enumerate(lines):
        mm = META.match(line)
        if mm:
            info.update(name=mm.group(1), gender=mm.group(2), age=int(mm.group(3)),
                        city=mm.group(4), education=mm.group(5), years=mm.group(6))
            rest = [x for x in lines[i + 1:] if x and x != "￼"]
            if rest:
                info["expect"] = rest[0]
            if len(rest) > 1 and "·" in rest[1]:
                info["current"] = rest[1]
            break
    if "name" not in info:
        nm = re.match(r"^(?:(?:Fw|Fwd|Re|转发|回复)\s*[:：]\s*)*(.+?)\s*(?:\||，|,|应聘)", subject, re.I)
        if nm:
            info["name"] = nm.group(1).strip()
    return info


def main():
    if len(sys.argv) != 3:
        sys.exit(__doc__)
    export, out = Path(sys.argv[1]), Path(sys.argv[2])
    dirs = sorted((p for p in export.iterdir() if p.is_dir() and (p / "body.txt").exists()),
                  key=lambda p: int(p.name) if p.name.isdigit() else 0, reverse=True)
    kept, by_name = [], {}
    for d in dirs:
        rec = {"id": d.name, **parse_body((d / "body.txt").read_text(errors="ignore"))}
        key = rec.get("name") or rec["id"]
        if key in by_name:
            by_name[key].setdefault("duplicates", []).append(rec["id"])
            continue
        f = resume_file(d)
        if f:
            raw = to_text(f)
            text_path = d / "resume_clean.txt"
            text_path.write_text(clean(raw), encoding="utf-8")
            rec["phones"], rec["emails"] = contacts(raw)
            rec["resume"] = str(f.resolve())
            rec["pdf"] = str(f.resolve()) if f.suffix.lower() == ".pdf" else None
            rec["text"] = str(text_path.resolve())
            rec["chars"] = len(raw.strip())
        by_name[key] = rec
        kept.append(rec)
    out.write_text(json.dumps(kept, ensure_ascii=False, indent=2), encoding="utf-8")
    for r in kept:
        flag = ""
        if not r.get("text"):
            flag = "  [无简历附件]"
        elif r["chars"] < 200:
            flag = "  [文本过少，可能是图片型简历，需直接读原文件]"
        print(f"{r['id']}\t{r.get('name', '?')}\t{r.get('position', '')}\t{r.get('years', '')}\t"
              f"{r.get('expect', '')}\t{' / '.join(r.get('phones', []))}{flag}")
    print(f"\n{len(kept)} candidates -> {out}", file=sys.stderr)


if __name__ == "__main__":
    main()
