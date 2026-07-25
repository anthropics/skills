#!/usr/bin/env python3
"""interactivity_injector.py - Inject vanilla-JS interactivity into rendered HTML.

Stdlib-only. Takes an HTML file produced by html_renderer.py and injects a
<script> block (immediately before </body>) that wires up:

  - search       Client-side filter on the search input — hides H2 sections
                 whose heading or body text doesn't match the query. Esc clears.
  - copycode     Click handler on every .code-copy button. Copies the <code>
                 text to clipboard, toggles a "copied" state for 1.2s.
  - smoothscroll Click handler on TOC links — smooth-scrolls to the target
                 anchor. Complements CSS scroll-behavior: smooth as a fallback.
  - scrollspy    IntersectionObserver on every <h2 id="..."> — sets
                 aria-current="location" on the matching TOC link as the user
                 reads. Foundation for "you are here" navigation.

NO LLM CALLS. Pure script template + HTML insertion.

The injected JS:
  - Uses no frameworks (vanilla DOM API + IntersectionObserver only)
  - Total payload ~3 KB minified-ish
  - Degrades gracefully: if IntersectionObserver is missing (very old browsers),
    scrollspy is silently skipped; the rest still works.

Idempotent: if the script block is already present (by ID), the file is
left unchanged.

Usage:
    python interactivity_injector.py --file report.html \\
        --features search,copycode,smoothscroll,scrollspy
    python interactivity_injector.py --sample
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

INJECT_MARKER_ID = "md-document-interactivity-v1"


# JavaScript payload. Indented carefully so the produced HTML is still readable.
JS_PAYLOAD_TEMPLATE = """\
<script id="__MARKER__">
(function () {
  "use strict";
  var ENABLED = __FEATURES__;

  // ----- Section grouping (used by search) -----
  // Each H2 + everything until the next H2 forms a "section" for filter purposes.
  function groupSections(root) {
    var groups = [];
    var current = null;
    Array.prototype.forEach.call(root.children, function (el) {
      if (el.tagName === "H2") {
        if (current) groups.push(current);
        current = { heading: el, elements: [el], text: el.textContent.toLowerCase() };
      } else if (current) {
        current.elements.push(el);
        current.text += " " + (el.textContent || "").toLowerCase();
      }
    });
    if (current) groups.push(current);
    return groups;
  }

  // ----- Search -----
  function wireSearch(root) {
    var input = document.getElementById("md-search-input");
    if (!input || !ENABLED.search) return;
    var groups = groupSections(root);
    function apply() {
      var q = input.value.trim().toLowerCase();
      groups.forEach(function (g) {
        var visible = !q || g.text.indexOf(q) !== -1;
        g.elements.forEach(function (el) { el.hidden = !visible; });
      });
    }
    input.addEventListener("input", apply);
    input.addEventListener("keydown", function (e) {
      if (e.key === "Escape") { input.value = ""; apply(); }
    });
  }

  // ----- Code-copy -----
  function wireCopy() {
    if (!ENABLED.copycode) return;
    Array.prototype.forEach.call(
      document.querySelectorAll("pre .code-copy"),
      function (btn) {
        btn.addEventListener("click", function () {
          var pre = btn.parentElement;
          var code = pre.querySelector("code");
          if (!code) return;
          var text = code.textContent;
          var done = function () {
            btn.classList.add("copied");
            var original = btn.textContent;
            btn.textContent = "Copied";
            setTimeout(function () {
              btn.classList.remove("copied");
              btn.textContent = original === "Copied" ? "Copy" : original;
            }, 1200);
          };
          if (navigator.clipboard && navigator.clipboard.writeText) {
            navigator.clipboard.writeText(text).then(done, function () {
              // Fallback to execCommand on older browsers
              fallbackCopy(text);
              done();
            });
          } else {
            fallbackCopy(text);
            done();
          }
        });
      }
    );
  }

  function fallbackCopy(text) {
    var ta = document.createElement("textarea");
    ta.value = text;
    ta.style.position = "fixed";
    ta.style.opacity = "0";
    document.body.appendChild(ta);
    ta.select();
    try { document.execCommand("copy"); } catch (e) {}
    document.body.removeChild(ta);
  }

  // ----- Smooth-scroll for TOC links -----
  function wireSmoothScroll() {
    if (!ENABLED.smoothscroll) return;
    Array.prototype.forEach.call(
      document.querySelectorAll("nav.toc a[href^=\\\"#\\\"]"),
      function (a) {
        a.addEventListener("click", function (e) {
          var id = a.getAttribute("href").slice(1);
          var target = document.getElementById(id);
          if (!target) return;
          e.preventDefault();
          target.scrollIntoView({ behavior: "smooth", block: "start" });
          history.replaceState(null, "", "#" + id);
        });
      }
    );
  }

  // ----- Scrollspy -----
  function wireScrollSpy() {
    if (!ENABLED.scrollspy || !("IntersectionObserver" in window)) return;
    var tocLinks = {};
    Array.prototype.forEach.call(
      document.querySelectorAll("nav.toc a[href^=\\\"#\\\"]"),
      function (a) {
        var id = a.getAttribute("href").slice(1);
        tocLinks[id] = a;
      }
    );
    var headings = document.querySelectorAll("main h2[id], main h3[id]");
    if (!headings.length) return;

    function clearActive() {
      Object.keys(tocLinks).forEach(function (k) {
        tocLinks[k].removeAttribute("aria-current");
      });
    }

    var observer = new IntersectionObserver(function (entries) {
      // Pick the topmost entry currently intersecting
      var visible = entries.filter(function (e) { return e.isIntersecting; });
      if (visible.length === 0) return;
      visible.sort(function (a, b) { return a.boundingClientRect.top - b.boundingClientRect.top; });
      var id = visible[0].target.id;
      var link = tocLinks[id];
      if (link) { clearActive(); link.setAttribute("aria-current", "location"); }
    }, { rootMargin: "-20% 0px -70% 0px", threshold: 0 });

    Array.prototype.forEach.call(headings, function (h) { observer.observe(h); });
  }

  // ----- Boot -----
  function init() {
    var main = document.querySelector("main");
    if (!main) return;
    wireSearch(main);
    wireCopy();
    wireSmoothScroll();
    wireScrollSpy();
  }

  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", init);
  } else {
    init();
  }
})();
</script>
"""

ALL_FEATURES = ("search", "copycode", "smoothscroll", "scrollspy")


def _features_dict(features: list[str]) -> str:
    enabled = set(features)
    parts = ",".join(f'"{f}": {"true" if f in enabled else "false"}' for f in ALL_FEATURES)
    return "{" + parts + "}"


def inject(html_text: str, features: list[str]) -> tuple[str, bool]:
    """Return (new_text, was_modified). Idempotent: no-op if marker already present."""
    if f'id="{INJECT_MARKER_ID}"' in html_text:
        return (html_text, False)

    payload = (JS_PAYLOAD_TEMPLATE
               .replace("__MARKER__", INJECT_MARKER_ID)
               .replace("__FEATURES__", _features_dict(features)))

    # Inject immediately before </body>
    closing = re.compile(r"</body\s*>", re.IGNORECASE)
    m = closing.search(html_text)
    if not m:
        # No </body> tag — append at end
        return (html_text + "\n" + payload, True)
    new_text = html_text[:m.start()] + payload + html_text[m.start():]
    return (new_text, True)


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--file", help="Path to HTML file to modify in place")
    parser.add_argument("--features",
                        default="search,copycode,smoothscroll,scrollspy",
                        help="Comma-separated subset of: search, copycode, smoothscroll, scrollspy")
    parser.add_argument("--output",
                        help="Write to this path instead of in-place. '-' for stdout.")
    parser.add_argument("--sample", action="store_true",
                        help="Inject into a fresh render of the built-in sample doc")
    args = parser.parse_args(argv)

    feats = [f.strip() for f in args.features.split(",") if f.strip()]
    invalid = [f for f in feats if f not in ALL_FEATURES]
    if invalid:
        print(f"error: unknown feature(s): {invalid}. "
              f"Valid: {list(ALL_FEATURES)}", file=sys.stderr)
        return 2

    if args.sample:
        # Render the sample on the fly so the injector can be exercised standalone
        sys.path.insert(0, str(Path(__file__).resolve().parent))
        import html_renderer
        import markdown_parser
        sections = markdown_parser.parse_markdown(markdown_parser.SAMPLE_MARKDOWN)
        sample_html = html_renderer.render(sections, {})
        modified, was = inject(sample_html, feats)
        out = args.output or "-"
        if out == "-":
            print(modified)
        else:
            Path(out).write_text(modified, encoding="utf-8")
            print(f"wrote {out}: {len(modified):,} bytes "
                  f"(injected: {feats})")
        return 0

    if not args.file:
        parser.print_help()
        return 0

    src = Path(args.file)
    if not src.exists():
        print(f"error: file not found: {src}", file=sys.stderr)
        return 2
    original = src.read_text(encoding="utf-8")
    modified, was = inject(original, feats)

    if args.output:
        if args.output == "-":
            print(modified)
            return 0
        Path(args.output).write_text(modified, encoding="utf-8")
        target = args.output
    else:
        src.write_text(modified, encoding="utf-8")
        target = str(src)

    if was:
        print(f"injected: {feats} -> {target} "
              f"({len(modified) - len(original):+,} bytes)")
    else:
        print(f"no-op: marker '{INJECT_MARKER_ID}' already present in {target}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
