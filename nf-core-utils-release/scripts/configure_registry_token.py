#!/usr/bin/env python3
"""Write the Nextflow Plugin Registry token to the user's global Gradle config.

Usage:
  TOKEN="$(op read 'op://Employee/Nextflow Plugin Registry Token/credential')"
  python configure_registry_token.py "$TOKEN"
"""
from pathlib import Path
import sys

if len(sys.argv) != 2 or not sys.argv[1].strip():
    raise SystemExit("usage: configure_registry_token.py <token>")

token = sys.argv[1].strip()
path = Path.home() / ".gradle" / "gradle.properties"
keys = {
    "npr.apiKey": token,
    # Compatibility with older local notes; Gradle release uses npr.apiKey.
    "pluginRegistry.accessToken": token,
}
lines = path.read_text().splitlines() if path.exists() else []
seen = set()
out = []
for line in lines:
    matched = False
    for key, value in keys.items():
        if line.startswith(key + "="):
            out.append(f"{key}={value}")
            seen.add(key)
            matched = True
            break
    if not matched:
        out.append(line)
for key, value in keys.items():
    if key not in seen:
        out.append(f"{key}={value}")
path.parent.mkdir(parents=True, exist_ok=True)
path.write_text("\n".join(out) + "\n")
print(f"Updated {path} with npr.apiKey=<redacted> and pluginRegistry.accessToken=<redacted>")
