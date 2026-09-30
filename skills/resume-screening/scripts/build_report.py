#!/usr/bin/env python3
"""Render the HR-facing screening report as PDF and append the original resumes.

Usage: build_report.py CANDIDATES_JSON EVALUATION_JSON OUT_PDF [--no-attach]

CANDIDATES_JSON comes from extract.py; EVALUATION_JSON is written by Claude (schema in
SKILL.md). Fields in an evaluation entry override the extracted record with the same id.
Needs Google Chrome (HTML -> PDF) and poppler's pdfinfo/pdfunite.
"""
import html
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path

CHROME = os.environ.get("CHROME_BIN", "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome")
TIER_LABEL = {"A": "A 档 · 优先面试", "B": "B 档 · 备选", "C": "C 档 · 不推荐"}

CSS = """
@page { size: A4; margin: 14mm 13mm 16mm; }
* { box-sizing: border-box; }
body { font-family: "PingFang SC", "Hiragino Sans GB", "Microsoft YaHei", sans-serif; font-size: 10pt;
  color: #1f2328; line-height: 1.55; margin: 0; -webkit-print-color-adjust: exact; print-color-adjust: exact; }
header { border-bottom: 2px solid #1f2328; padding-bottom: 8px; margin-bottom: 12px; }
h1 { font-size: 20pt; margin: 0 0 2px; }
.sub { font-size: 12pt; font-weight: 600; }
.muted { color: #656d76; font-size: 9pt; }
h2 { font-size: 13pt; margin: 18px 0 8px; padding-left: 8px; border-left: 4px solid #1f2328; break-after: avoid; }
h2.tA { border-color: #1a7f37; } h2.tB { border-color: #0969da; } h2.tC { border-color: #8c959f; }
.stats { display: flex; gap: 8px; margin: 10px 0; }
.stat { flex: 1; border: 1px solid #d0d7de; border-radius: 6px; padding: 6px 10px; }
.stat b { font-size: 16pt; display: block; line-height: 1.2; }
.stat span { font-size: 9pt; color: #656d76; }
.stat.tA b { color: #1a7f37; } .stat.tB b { color: #0969da; } .stat.tC b { color: #8c959f; }
table { width: 100%; border-collapse: collapse; font-size: 8.8pt; }
th, td { border: 1px solid #d0d7de; padding: 4px 6px; text-align: left; vertical-align: top; }
th { background: #f6f8fa; white-space: nowrap; }
tr { break-inside: avoid; }
.nowrap { white-space: nowrap; }
.badge { display: inline-block; min-width: 18px; text-align: center; border-radius: 4px; color: #fff;
  font-weight: 700; font-size: 8.5pt; padding: 0 4px; }
.badge.tA { background: #1a7f37; } .badge.tB { background: #0969da; } .badge.tC { background: #8c959f; }
.card { border: 1px solid #d0d7de; border-left: 4px solid #8c959f; border-radius: 6px; padding: 8px 12px;
  margin: 0 0 10px; break-inside: avoid; }
.card.tA { border-left-color: #1a7f37; } .card.tB { border-left-color: #0969da; }
.card-head { display: flex; flex-wrap: wrap; align-items: baseline; gap: 10px; }
.name { font-size: 13pt; font-weight: 700; }
.expect { margin-left: auto; font-weight: 600; }
.contact { font-size: 9pt; color: #57606a; margin: 2px 0 6px; }
.row { display: flex; gap: 10px; margin-top: 3px; }
.row label { flex: 0 0 64px; font-weight: 600; color: #57606a; }
.row > div { flex: 1; }
ul { margin: 0; padding-left: 1.2em; }
li { margin: 1px 0; }
"""


def esc(v):
    return html.escape(str(v if v is not None else ""))


def rich(v):
    if isinstance(v, list):
        return "<ul>" + "".join(f"<li>{esc(x)}</li>" for x in v) + "</ul>"
    return esc(v)


def joined(values):
    return " / ".join(values or []) or "—"


def basic(r):
    if r.get("headline"):
        return r["headline"]
    parts = [r.get("gender"), f"{r['age']}岁" if r.get("age") else None, r.get("city"),
             r.get("education"), r.get("years"), r.get("current")]
    return " · ".join(str(p) for p in parts if p)


def page_count(pdf):
    out = subprocess.run(["pdfinfo", str(pdf)], capture_output=True, text=True, check=True).stdout
    return int(re.search(r"^Pages:\s+(\d+)", out, re.M).group(1))


def render_pdf(html_text, pdf_path, workdir, timeout=120):
    html_file = workdir / "report.html"
    html_file.write_text(html_text, encoding="utf-8")
    pdf_path = Path(pdf_path)
    pdf_path.unlink(missing_ok=True)
    proc = subprocess.Popen([CHROME, "--headless=new", "--disable-gpu", "--no-first-run",
                             "--no-default-browser-check", f"--user-data-dir={workdir / 'chrome-profile'}",
                             "--no-pdf-header-footer", f"--print-to-pdf={pdf_path}", html_file.as_uri()],
                            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    # Chrome often writes the PDF but never exits (its updater keeps the process alive),
    # so wait for the file size to settle and then kill it.
    deadline, last_size, stable = time.time() + timeout, -1, 0
    try:
        while time.time() < deadline:
            if proc.poll() is not None and not pdf_path.exists():
                raise RuntimeError("Chrome exited without writing the PDF")
            size = pdf_path.stat().st_size if pdf_path.exists() else -1
            stable = stable + 1 if size > 0 and size == last_size else 0
            if stable >= 3:
                return
            last_size = size
            time.sleep(0.5)
        raise TimeoutError(f"Chrome did not produce {pdf_path} within {timeout}s")
    finally:
        if proc.poll() is None:
            proc.kill()
            proc.wait()


def load(cands_path, eval_path):
    cands = {str(c["id"]): c for c in json.loads(Path(cands_path).read_text(encoding="utf-8"))}
    ev = json.loads(Path(eval_path).read_text(encoding="utf-8"))
    rows = []
    for e in ev["candidates"]:
        e = {**e, "id": str(e["id"])}
        rows.append({**cands.get(e["id"], {}), **{k: v for k, v in e.items() if v not in (None, "")}})
    return ev, rows


def card(r, starts):
    page = starts.get(r["id"])
    page_note = f"　原简历见第 {page} 页" if page else ""
    return f"""<section class="card t{r['tier']}">
<div class="card-head"><span class="name">{esc(r.get('name'))}</span><span>{esc(basic(r))}</span>
<span class="expect">期望 {esc(r.get('expect') or '—')}</span></div>
<div class="contact">电话 {esc(joined(r.get('phones')))}　邮箱 {esc(joined(r.get('emails')))}{page_note}</div>
<div class="row"><label>亮点</label><div>{rich(r.get('highlights'))}</div></div>
<div class="row"><label>风险/核实</label><div>{rich(r.get('risks'))}</div></div>
</section>"""


def build_html(ev, rows, starts):
    tiers = {t: [r for r in rows if r.get("tier") == t] for t in "ABC"}
    p = [f"""<header><h1>{esc(ev.get('title', '简历评估报告'))}</h1>
<div class="sub">{esc(ev.get('role', ''))}</div>
<div class="muted">{esc(ev.get('source', ''))}{' · 生成日期 ' + esc(ev['generated']) if ev.get('generated') else ''}</div></header>"""]
    p.append('<div class="stats">'
             + "".join(f'<div class="stat t{t}"><b>{len(tiers[t])}</b><span>{TIER_LABEL[t]}</span></div>' for t in "ABC")
             + f'<div class="stat"><b>{len(rows)}</b><span>简历总数</span></div></div>')
    if ev.get("criteria"):
        p.append(f'<p class="muted">评估维度：{esc(ev["criteria"])}</p>')
    if ev.get("recommendations"):
        p.append("<h2>结论与建议</h2>" + rich(ev["recommendations"]))
    shortlist = tiers["A"] + tiers["B"]
    if shortlist:
        p.append("<h2>联系方式速查（A/B 档）</h2><table><thead><tr><th>档</th><th>姓名</th><th>基本情况</th>"
                 "<th>期望</th><th>电话</th><th>邮箱</th><th>简历页</th></tr></thead><tbody>")
        for r in shortlist:
            p.append(f'<tr><td><span class="badge t{r["tier"]}">{r["tier"]}</span></td><td class="nowrap"><b>{esc(r.get("name"))}</b></td>'
                     f'<td>{esc(basic(r))}</td><td class="nowrap">{esc(r.get("expect") or "—")}</td>'
                     f'<td class="nowrap">{esc(joined(r.get("phones")))}</td><td>{esc(joined(r.get("emails")))}</td>'
                     f'<td class="nowrap">{esc(starts.get(r["id"], "—"))}</td></tr>')
        p.append("</tbody></table>")
    for t in "AB":
        if tiers[t]:
            p.append(f'<h2 class="t{t}">{TIER_LABEL[t]}</h2>')
            p.extend(card(r, starts) for r in tiers[t])
    if tiers["C"]:
        p.append(f'<h2 class="tC">{TIER_LABEL["C"]}</h2><table><thead><tr><th>姓名</th><th>基本情况</th>'
                 '<th>期望</th><th>不推荐原因</th></tr></thead><tbody>')
        for r in tiers["C"]:
            reason = r.get("risks") or r.get("highlights")
            p.append(f'<tr><td class="nowrap"><b>{esc(r.get("name"))}</b></td><td>{esc(basic(r))}</td>'
                     f'<td class="nowrap">{esc(r.get("expect") or "—")}</td><td>{rich(reason)}</td></tr>')
        p.append("</tbody></table>")
    if ev.get("interview_questions"):
        p.append("<h2>建议面试问题</h2>" + rich(ev["interview_questions"]))
    if starts:
        p.append('<p class="muted">附件：以上 A/B 档候选人的原始简历按表中页码附在本报告之后。</p>')
    return (f'<!doctype html><html lang="zh-CN"><head><meta charset="utf-8"><title>{esc(ev.get("title", ""))}</title>'
            f"<style>{CSS}</style></head><body>{''.join(p)}</body></html>")


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    if len(args) != 3:
        sys.exit(__doc__)
    ev, rows = load(args[0], args[1])
    out = Path(args[2]).resolve()
    out.parent.mkdir(parents=True, exist_ok=True)
    attachments = []
    if "--no-attach" not in sys.argv:
        for t in ev.get("attach_tiers", ["A", "B"]):
            attachments += [r for r in rows if r.get("tier") == t and r.get("pdf") and Path(r["pdf"]).exists()]
    with tempfile.TemporaryDirectory() as tmp:
        tmp = Path(tmp)
        report = tmp / "report.pdf"
        starts = {}
        for _ in range(3):  # page numbers can shift the report length; re-render until stable
            render_pdf(build_html(ev, rows, starts), report, tmp)
            page, new = page_count(report) + 1, {}
            for r in attachments:
                new[r["id"]] = page
                page += page_count(r["pdf"])
            if new == starts:
                break
            starts = new
        if attachments:
            subprocess.run(["pdfunite", str(report), *[r["pdf"] for r in attachments], str(out)],
                           check=True, stderr=subprocess.DEVNULL)  # poppler warns noisily on BOSS PDFs
        else:
            shutil.copy(report, out)
    print(f"{out}\n{page_count(out)} pages, report + {len(attachments)} resumes")


if __name__ == "__main__":
    main()
