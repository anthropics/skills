"""Read Claude Code session title from JSONL (priority: custom-title > ai-title)."""
import json, os, sys
from resolve_paths import resolve_paths

cc_project_dir, _ = resolve_paths()
session_uuid = sys.argv[1] if len(sys.argv) > 1 else None

if not session_uuid:
    print("Usage: read_title.py <session_uuid>")
    sys.exit(1)

jsonl_path = os.path.join(cc_project_dir, f'{session_uuid}.jsonl')
title = None
try:
    with open(jsonl_path) as f:
        for line in f:
            try:
                d = json.loads(line)
                if d.get('type') == 'custom-title' and d.get('sessionId') == session_uuid:
                    title = d.get('customTitle')
                elif d.get('type') == 'ai-title' and d.get('sessionId') == session_uuid:
                    if title is None: title = d.get('aiTitle')
            except: pass
except FileNotFoundError:
    print('(session not found)')
    sys.exit(0)

print(title if title else '(unnamed)')