#!/usr/bin/env python3
"""html_validator.py — Post-generation structural check on landing HTML output.

Stdlib-only. Validates a generated landing page against the megaprompt-mandated
structure. The skill runs this AFTER writing the .html file; FAIL means
regenerate the failing sections.

Checks:

  1. Has <!DOCTYPE html> + <html lang="...">
  2. Has <meta name="viewport">
  3. Has <title>
  4. CDN deps present:
     - Google Fonts link (fonts.googleapis.com)
     - GSAP CDN script (cdnjs / unpkg)
     - ScrollTrigger CDN script
  5. NO external CSS files (no <link rel="stylesheet"> other than Google Fonts)
  6. NO external JS files (no <script src=...> other than GSAP CDN)
  7. Has 3 required sections:
     - .hero (or <header class="hero">)
     - .features (or <section class="features">)
     - .closing-cta (or <section class="closing-cta">)
  8. Has gsap.set() somewhere BEFORE gsap.timeline() or gsap.to() (FOUC prevention)
  9. Has responsive @media at 900px AND 580px
  10. Has <h1> (exactly one) and <h2> (one or more)
  11. CTA uses <button> or <a> (not <div> with onclick)

NO LLM CALLS. Pure regex + line scan.

Usage:
    python html_validator.py --file ./landing-pages/quill-ai.html
    python html_validator.py --file ./output.html --output json
    python html_validator.py --sample-pass
    python html_validator.py --sample-fail
"""

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any, Dict, List


SAMPLE_PASS_HTML = """<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>Quill AI — Async Standup Tool</title>
  <link href="https://fonts.googleapis.com/css2?family=Inter:wght@400;500;600;700;800&display=swap" rel="stylesheet">
  <style>
    :root { --navy: #0A1628; --teal: #00D4AA; }
    body { background: var(--navy); color: white; font-family: Inter, sans-serif; }
    .hero { min-height: 100vh; }
    .features { padding: 120px 24px; }
    .closing-cta { padding: 120px 24px; background: var(--navy); }
    @media (max-width: 900px) { .features-grid { grid-template-columns: repeat(2, 1fr); } }
    @media (max-width: 580px) { .features-grid { grid-template-columns: 1fr; } }
  </style>
</head>
<body>
  <header class="hero">
    <span class="eyebrow">Async</span>
    <h1>Stop the Zoom standup spiral</h1>
    <p class="subtitle">Quill AI is the async standup tool for remote engineering teams.</p>
    <a class="btn-primary" href="#cta">Get started</a>
  </header>
  <section class="features">
    <h2>Built for engineers</h2>
    <div class="features-grid">
      <div class="feature-card">Auto-reminders</div>
      <div class="feature-card">Slack integration</div>
      <div class="feature-card">Markdown export</div>
    </div>
  </section>
  <section class="closing-cta">
    <h2>Stop scheduling. Start shipping.</h2>
    <a class="btn-primary" href="/signup">Start free</a>
  </section>
  <script src="https://cdnjs.cloudflare.com/ajax/libs/gsap/3.12.2/gsap.min.js"></script>
  <script src="https://cdnjs.cloudflare.com/ajax/libs/gsap/3.12.2/ScrollTrigger.min.js"></script>
  <script>
    gsap.set([".eyebrow", ".hero h1", ".subtitle", ".btn-primary"], { opacity: 0, y: 30 });
    const tl = gsap.timeline({ defaults: { ease: "power3.out" } });
    tl.to(".eyebrow", { opacity: 1, y: 0, duration: 0.6 })
      .to(".hero h1", { opacity: 1, y: 0, duration: 0.8 }, "-=0.3");
  </script>
</body>
</html>
"""

SAMPLE_FAIL_HTML = """<!DOCTYPE html>
<html>
<head>
  <link rel="stylesheet" href="./styles.css">
  <script src="./app.js"></script>
</head>
<body>
  <div class="hero">
    <h1>Hello</h1>
    <h1>Another H1</h1>
    <div onclick="alert('cta')">Click me</div>
  </div>
  <script>
    gsap.timeline().to(".hero h1", { opacity: 1 });
  </script>
</body>
</html>
"""


def validate(html: str) -> Dict[str, Any]:
    findings: List[Dict[str, str]] = []

    def add(rule: str, level: str, message: str) -> None:
        findings.append({"rule": rule, "level": level, "message": message})

    # Rule 1: DOCTYPE + html lang
    if "<!DOCTYPE html>" not in html and "<!doctype html>" not in html.lower():
        add("doctype", "FAIL", "Missing <!DOCTYPE html> declaration")
    else:
        add("doctype", "PASS", "DOCTYPE present")
    if re.search(r"<html\s+[^>]*lang=", html, re.IGNORECASE):
        add("html-lang", "PASS", "<html> has lang attribute")
    else:
        add("html-lang", "WARN", "<html> missing lang attribute (accessibility)")

    # Rule 2: viewport meta
    if re.search(r'<meta\s+[^>]*name=["\']viewport["\']', html, re.IGNORECASE):
        add("viewport", "PASS", "Viewport meta present")
    else:
        add("viewport", "FAIL", "Missing <meta name='viewport'> (responsive will break)")

    # Rule 3: title
    if re.search(r"<title>.*?</title>", html, re.IGNORECASE | re.DOTALL):
        add("title", "PASS", "<title> present")
    else:
        add("title", "WARN", "<title> missing")

    # Rule 4: CDN deps
    if "fonts.googleapis.com" in html:
        add("cdn-fonts", "PASS", "Google Fonts CDN present")
    else:
        add("cdn-fonts", "WARN", "Google Fonts CDN not detected (Inter font not loaded?)")
    if re.search(r"gsap[\w\-/.]*\.min\.js", html, re.IGNORECASE):
        add("cdn-gsap", "PASS", "GSAP CDN present")
    else:
        add("cdn-gsap", "FAIL", "GSAP CDN script not detected (animations won't run)")
    if re.search(r"ScrollTrigger[\w\-/.]*\.min\.js", html, re.IGNORECASE):
        add("cdn-scrolltrigger", "PASS", "ScrollTrigger CDN present")
    else:
        add("cdn-scrolltrigger", "WARN", "ScrollTrigger CDN not detected (scroll-triggered reveals won't work)")

    # Rule 5: no external CSS (other than Google Fonts)
    css_links = re.findall(r'<link[^>]+rel=["\']stylesheet["\'][^>]*>', html, re.IGNORECASE)
    external_css = [l for l in css_links if "fonts.googleapis.com" not in l and "fonts.gstatic.com" not in l]
    if external_css:
        add("no-external-css", "FAIL", f"External stylesheet(s) detected (not allowed): {external_css}")
    else:
        add("no-external-css", "PASS", f"No external stylesheets ({len(css_links)} link(s), all Google Fonts)")

    # Rule 6: no external JS (other than GSAP CDN)
    js_scripts = re.findall(r'<script[^>]+src=["\']([^"\']+)["\']', html, re.IGNORECASE)
    external_js = [s for s in js_scripts if "cdnjs.cloudflare.com" not in s and "unpkg.com/gsap" not in s and "fonts.googleapis.com" not in s]
    if external_js:
        add("no-external-js", "FAIL", f"External script(s) not from allowed CDN: {external_js}")
    else:
        add("no-external-js", "PASS", f"No external JS files outside allowed CDN ({len(js_scripts)} script(s))")

    # Rule 7: 3 required sections
    if re.search(r'class=["\'][^"\']*\bhero\b', html, re.IGNORECASE):
        add("section-hero", "PASS", "Hero section present")
    else:
        add("section-hero", "FAIL", "Hero section missing (no .hero class found)")
    if re.search(r'class=["\'][^"\']*\bfeatures\b', html, re.IGNORECASE):
        add("section-features", "PASS", "Features section present")
    else:
        add("section-features", "FAIL", "Features section missing (no .features class found)")
    if re.search(r'class=["\'][^"\']*\bclosing-cta\b', html, re.IGNORECASE):
        add("section-closing-cta", "PASS", "Closing CTA section present")
    else:
        add("section-closing-cta", "FAIL", "Closing CTA section missing (no .closing-cta class found)")

    # Rule 8: gsap.set() before gsap.timeline / gsap.to (FOUC prevention)
    has_gsap_set = bool(re.search(r"gsap\.set\s*\(", html))
    has_gsap_animation = bool(re.search(r"gsap\.(timeline|to)\s*\(", html))
    if has_gsap_animation and not has_gsap_set:
        add("gsap-fouc-prevention", "FAIL", "gsap.timeline / gsap.to used but no gsap.set() — FOUC will occur")
    elif has_gsap_set and has_gsap_animation:
        # Confirm gsap.set() appears BEFORE first gsap.timeline / gsap.to in source order
        set_idx = html.find("gsap.set")
        anim_match = re.search(r"gsap\.(timeline|to)", html)
        anim_idx = anim_match.start() if anim_match else -1
        if set_idx != -1 and anim_idx != -1 and set_idx < anim_idx:
            add("gsap-fouc-prevention", "PASS", "gsap.set() appears before gsap.timeline/to — FOUC prevented")
        else:
            add("gsap-fouc-prevention", "WARN", "gsap.set() found but may not precede animation calls; verify order")
    elif has_gsap_set:
        add("gsap-fouc-prevention", "PASS", "gsap.set() present (no animations to flash)")
    else:
        add("gsap-fouc-prevention", "WARN", "No GSAP animations detected (skill may not have rendered them)")

    # Rule 9: responsive breakpoints at 900px AND 580px
    has_900 = bool(re.search(r"@media[^{]*max-width:\s*900px", html, re.IGNORECASE))
    has_580 = bool(re.search(r"@media[^{]*max-width:\s*580px", html, re.IGNORECASE))
    if has_900 and has_580:
        add("responsive-breakpoints", "PASS", "Both 900px + 580px breakpoints present")
    elif has_900 or has_580:
        present = "900px" if has_900 else "580px"
        missing = "580px" if has_900 else "900px"
        add("responsive-breakpoints", "WARN", f"Only {present} breakpoint present; missing {missing}")
    else:
        add("responsive-breakpoints", "FAIL", "Neither 900px nor 580px media query present")

    # Rule 10: H1 + H2
    h1_count = len(re.findall(r"<h1\b", html, re.IGNORECASE))
    h2_count = len(re.findall(r"<h2\b", html, re.IGNORECASE))
    if h1_count == 1:
        add("h1-singleton", "PASS", "Exactly one <h1>")
    elif h1_count == 0:
        add("h1-singleton", "FAIL", "No <h1> (accessibility + SEO)")
    else:
        add("h1-singleton", "WARN", f"{h1_count} <h1> tags (should be exactly 1 for accessibility/SEO)")
    if h2_count >= 1:
        add("h2-present", "PASS", f"{h2_count} <h2> tag(s)")
    else:
        add("h2-present", "WARN", "No <h2> tags (features + CTA sections should each have one)")

    # Rule 11: CTA semantic — buttons or links, not divs with onclick
    div_onclick = re.findall(r"<div[^>]+onclick=", html, re.IGNORECASE)
    if div_onclick:
        add("cta-semantic", "FAIL", f"<div> with onclick detected ({len(div_onclick)} found) — use <button> or <a>")
    else:
        add("cta-semantic", "PASS", "No <div onclick> patterns (buttons/links used semantically)")

    return finalize(findings)


def finalize(findings: List[Dict[str, str]]) -> Dict[str, Any]:
    counts = {"PASS": 0, "WARN": 0, "FAIL": 0}
    for f in findings:
        counts[f["level"]] += 1
    if counts["FAIL"] > 0:
        verdict = "FAIL"
    elif counts["WARN"] > 0:
        verdict = "WARN"
    else:
        verdict = "PASS"
    return {"verdict": verdict, "counts": counts, "findings": findings}


def render_human(result: Dict[str, Any]) -> str:
    out: List[str] = []
    out.append(f"HTML structural verdict: {result['verdict']}")
    c = result["counts"]
    out.append(f"  PASS: {c['PASS']}  WARN: {c['WARN']}  FAIL: {c['FAIL']}")
    out.append("")
    out.append("Findings:")
    for f in result["findings"]:
        marker = {"PASS": "[ok]", "WARN": "[warn]", "FAIL": "[FAIL]"}[f["level"]]
        out.append(f"  {marker} {f['rule']}: {f['message']}")
    return "\n".join(out)


def main(argv: List[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--file", help="Path to .html file to validate")
    parser.add_argument("--sample-pass", action="store_true", help="Validate embedded clean sample")
    parser.add_argument("--sample-fail", action="store_true", help="Validate embedded violation sample")
    parser.add_argument("--output", choices=["human", "json"], default="human")
    args = parser.parse_args(argv)

    if args.sample_pass:
        html = SAMPLE_PASS_HTML
    elif args.sample_fail:
        html = SAMPLE_FAIL_HTML
    elif args.file:
        p = Path(args.file)
        if not p.exists():
            print(f"error: {args.file} not found", file=sys.stderr); return 2
        html = p.read_text(encoding="utf-8")
    else:
        parser.print_help(); return 0

    result = validate(html)
    if args.output == "json":
        print(json.dumps(result, indent=2))
    else:
        print(render_human(result))
    return 0 if result["verdict"] != "FAIL" else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
