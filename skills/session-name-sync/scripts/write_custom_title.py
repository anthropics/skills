"""Write custom-title entry to Claude Code session JSONL."""
import json, os, sys
from resolve_paths import resolve_paths

cc_project_dir, _ = resolve_paths()
name = sys.argv[1] if len(sys.argv) > 1 else None
session_uuid = sys.argv[2] if len(sys.argv) > 2 else None

if not name or not session_uuid:
    print("Usage: write_custom_title.py <name> <session_uuid>")
    sys.exit(1)

entry = json.dumps({'type': 'custom-title', 'customTitle': name, 'sessionId': session_uuid})
jsonl_path = os.path.join(cc_project_dir, f'{session_uuid}.jsonl')
with open(jsonl_path, 'a') as f:
    f.write(entry + '\n')
print(f'Claude Code title set: {name}')