#!/bin/sh
# Self-test for the functional-qa-engineer skill. Run from the project root after any change to the skill.
#   sh <skill>/selftest/selftest.sh        -> runs the non-browser half, stages fixtures + builds the browser harness,
#                                             starts the fixture server on :3101, and tells you the one call to make
#   sh <skill>/selftest/selftest.sh stop   -> stops the fixture server
set -e
SK="$(cd "$(dirname "$0")/.." && pwd)"
QA=".playwright-mcp/qa"
if [ "$1" = "stop" ]; then [ -f "$QA/fixtures.pid" ] && kill "$(cat "$QA/fixtures.pid")" 2>/dev/null; rm -f "$QA/fixtures.pid"; echo "fixture server stopped"; exit 0; fi
python3 -I "$SK/selftest/selftest.py"
sh "$SK/scripts/stage.sh" "$QA" >/dev/null
rm -rf "$QA/fixtures" && cp -r "$SK/selftest/fixtures" "$QA/fixtures"
python3 -I "$SK/selftest/build_selftest.py" "$QA/selftest.js"
if ! curl -s -o /dev/null http://127.0.0.1:3101/cta.html; then
  nohup python3 -I -m http.server 3101 --bind 127.0.0.1 --directory "$QA/fixtures" > "$QA/fixtures.log" 2>&1 &
  echo $! > "$QA/fixtures.pid"; sleep 1
fi
echo "fixture server: http://127.0.0.1:3101/ (stop with: sh $SK/selftest/selftest.sh stop)"
echo "NEXT: browser_run_code_unsafe with filename $QA/selftest.js  -> every lesson must report pass:true"
