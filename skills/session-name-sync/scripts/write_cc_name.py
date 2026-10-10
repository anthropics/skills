"""Write session name to cc-connect JSON (atomic, updates both locations)."""
import json, os, sys
from resolve_paths import resolve_paths

_, cc_file = resolve_paths()
session_uuid = sys.argv[1] if len(sys.argv) > 1 else None
name = sys.argv[2] if len(sys.argv) > 2 else None

if not session_uuid or not name or not cc_file:
    print("Usage: write_cc_name.py <session_uuid> <name>")
    sys.exit(1)

with open(cc_file, 'r') as f: data = json.load(f)

session_key = None
for key, sess in data['sessions'].items():
    if sess.get('agent_session_id') == session_uuid:
        session_key = key
        break

if session_key:
    data['sessions'][session_key]['name'] = name
    data['session_names'][session_uuid] = name
    tmp = cc_file + '.tmp'
    with open(tmp, 'w') as f: json.dump(data, f, indent=2, ensure_ascii=False)
    os.replace(tmp, cc_file)
    print(f'cc-connect name set: {name} (session {session_key})')
else:
    print(f'WARNING: No cc-connect session found for UUID {session_uuid}')
    print('Name set only in Claude Code (JSONL)')