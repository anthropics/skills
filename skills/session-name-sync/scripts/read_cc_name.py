"""Read session name from cc-connect JSON by agent_session_id."""
import json, os, sys
from resolve_paths import resolve_paths

_, cc_file = resolve_paths()
session_uuid = sys.argv[1] if len(sys.argv) > 1 else None

if not session_uuid or not cc_file:
    print("Usage: read_cc_name.py <session_uuid>")
    sys.exit(1)

with open(cc_file) as f: data = json.load(f)

for key, sess in data['sessions'].items():
    if sess.get('agent_session_id') == session_uuid:
        name = sess.get('name', '') or data.get('session_names', {}).get(session_uuid, '')
        print(name if name else '(unnamed)')
        break
else:
    print('(not in cc-connect)')