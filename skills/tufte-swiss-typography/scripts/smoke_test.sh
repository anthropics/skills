#!/usr/bin/env bash
# smoke_test.sh — Compile example-onepager.tex and verify output.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
ASSETS_DIR="$(cd "$SCRIPT_DIR/../assets" && pwd)"
TMPDIR="$(mktemp -d)"
trap 'rm -rf "$TMPDIR"' EXIT

# Copy assets to tmpdir
cp "$ASSETS_DIR"/tufte-swiss.sty "$TMPDIR"/
cp "$ASSETS_DIR"/tufte-swiss-grid.lua "$TMPDIR"/
cp "$ASSETS_DIR"/example-onepager.tex "$TMPDIR"/

# Compile
cd "$TMPDIR"
/Library/TeX/texbin/lualatex -interaction=nonstopmode example-onepager.tex > compile.log 2>&1
EXIT_CODE=$?

# Check exit code
if [ "$EXIT_CODE" -ne 0 ]; then
    echo "FAIL: lualatex exited with code $EXIT_CODE"
    cat compile.log
    exit 1
fi

# Check for tufte-swiss summary line
if ! grep -q "tufte-swiss:" compile.log; then
    echo "FAIL: no tufte-swiss summary in log"
    cat compile.log
    exit 1
fi

# Check PDF exists
if [ ! -f example-onepager.pdf ]; then
    echo "FAIL: no PDF generated"
    exit 1
fi

# Report
echo "PASS: PDF generated, callbacks fired."
grep "tufte-swiss:" compile.log
echo "PDF: $TMPDIR/example-onepager.pdf"
