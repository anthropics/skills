---
name: pdf-review
description: Turn any HTML file into a clean, print-ready PDF. Generates the PDF via Chrome CDP, renders every page to PNG, visually inspects each page with Claude's vision, fixes CSS issues, and iterates until all pages pass quality checks. Trigger when the user wants to convert an HTML file to PDF, export a document as PDF, or fix PDF layout/print issues.
argument-hint: [path/to/file.html]
license: MIT
---

# HTML → PDF Visual Review

Generate a print-ready PDF from any HTML file. Render every page to PNG, inspect visually, fix CSS, repeat until clean.

**Loop:** Generate → Screenshot all pages → Read every page with vision → Fix CSS → Repeat until done.

---

## Step 1 — Generate PDF via Chrome CDP

Use Chrome CDP (not `--print-to-pdf` CLI — it doesn't reliably suppress headers/footers).

```python
import subprocess, json, time, urllib.request, base64

def print_to_pdf(html_path, pdf_path):
    chrome = '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome'
    proc = subprocess.Popen([
        chrome, '--headless=new', '--disable-gpu',
        '--remote-debugging-port=9222',
        '--remote-allow-origins=*',
        '--no-sandbox', '--disable-extensions',
        'about:blank'
    ], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    time.sleep(2)
    try:
        import websocket
        targets = json.loads(urllib.request.urlopen('http://localhost:9222/json').read())
        page_target = next(t for t in targets if t.get('type') == 'page')
        ws = websocket.create_connection(page_target['webSocketDebuggerUrl'], timeout=60)
        def send(id, method, params={}):
            ws.send(json.dumps({"id": id, "method": method, "params": params}))
        send(1, "Page.enable"); ws.recv()
        send(2, "Page.navigate", {"url": f"file://{html_path}"})
        for _ in range(30):
            msg = json.loads(ws.recv())
            if msg.get('method') == 'Page.loadEventFired':
                break
        time.sleep(1)
        send(3, "Page.printToPDF", {
            "displayHeaderFooter": False,
            "printBackground": True,
            "paperWidth": 8.27, "paperHeight": 11.69,
            "marginTop": 0, "marginBottom": 0,
            "marginLeft": 0, "marginRight": 0,
            "preferCSSPageSize": True
        })
        for _ in range(20):
            msg = json.loads(ws.recv())
            if msg.get('id') == 3:
                break
        ws.close()
        with open(pdf_path, 'wb') as f:
            f.write(base64.b64decode(msg['result']['data']))
    finally:
        proc.kill()
    time.sleep(1)
```

- PDF goes in the same directory as the HTML, same basename
- Kill any lingering Chrome first: `pkill -f "remote-debugging-port=9222"`

---

## Step 2 — Render all pages to PNG

```bash
mkdir -p /tmp/pdf-review-$BASENAME
pdftoppm -r 150 -png "$PDF_PATH" /tmp/pdf-review-$BASENAME/page
```

`pdftoppm` requires poppler: `brew install poppler`. Produces `page-01.png`, `page-02.png`, etc.

---

## Step 3 — Inspect every page with vision

Use the Read tool on each PNG. Check for:

| Issue | What to look for |
|---|---|
| Orphaned header | Section title alone at page bottom, content on next page |
| Blank page | Nearly empty — usually a stray `page-break-after: always` |
| Clipped content | Text or table cut at page edge |
| Mid-paragraph break | Sentence splits across pages |
| Column collapse | Two-column grid collapsed to one |
| Font overflow | Headlines blowing out the page |

---

## Step 4 — Fix CSS in `@media print {}`

All fixes go inside `@media print {}`. Never touch screen CSS.

| Problem | Fix |
|---|---|
| Orphaned header | `page-break-after: avoid` on the heading element |
| Section split | `page-break-before: always` on that section div |
| Blank page | Remove `page-break-after: always` on the offending element |
| Content overflow | Replace px padding with pt values (80px → 20pt) |
| Table row split | `page-break-inside: avoid` on `tr` |
| Column collapse | `display: grid !important; grid-template-columns: 1fr 1fr !important;` |
| Font too large | `font-size: Xpt !important` override |
| Mid-paragraph break | `page-break-inside: avoid` on the paragraph container |

---

## Step 5 — Iterate

Regenerate → re-render → re-inspect → fix → repeat. Stop when every page is clean. After 3 rounds with no improvement on a persistent issue, report the specific blocker to the user.

---

## Step 6 — Ship

```bash
open "$PDF_PATH"
```

Report: page count, output path, any remaining notes.

---

## `@media print` Baseline Template

```css
@media print {
  @page { size: A4 portrait; margin: 14mm 16mm; }
  * { -webkit-print-color-adjust: exact !important; print-color-adjust: exact !important; }
  body { font-size: 10pt; background: #fff !important; }

  .cover {
    page-break-after: always;
    min-height: 0 !important; height: auto !important;
    padding: 36pt 48pt !important;
  }
  .cover h1 { font-size: 30pt !important; }
  .cover p  { font-size: 11pt !important; }

  .section { padding: 20pt 28pt !important; margin-bottom: 12pt !important; }
  h2 { font-size: 16pt !important; page-break-after: avoid; }
  h3 { font-size: 13pt !important; page-break-after: avoid; }
  p, li { font-size: 9.5pt !important; line-height: 1.45 !important; }

  table { page-break-inside: avoid; }
  tr    { page-break-inside: avoid; }
  .card, .callout { page-break-inside: avoid; padding: 10pt 14pt !important; }
  .signature-block { page-break-inside: avoid; page-break-before: always; }
  .no-print { display: none !important; }
}
```

## Principles

- Read the HTML first — grep for actual class names before writing selectors
- If `@media print` already exists, edit it in place
- Preserve all screen CSS untouched
- `page-break-before: always` is the nuclear option — use when softer hints fail
