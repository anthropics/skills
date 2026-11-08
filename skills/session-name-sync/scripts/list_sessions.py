"""List all sessions with names from both systems side by side."""
import json, os, glob
from resolve_paths import resolve_paths

cc_project_dir, cc_file = resolve_paths()

cc_sessions = {}
for f in glob.glob(os.path.join(cc_project_dir, '*.jsonl')):
    sid = os.path.basename(f).replace('.jsonl', '')
    title = None
    with open(f) as fh:
        for line in fh:
            try:
                d = json.loads(line)
                if d.get('type') == 'custom-title' and d.get('sessionId') == sid: title = d.get('customTitle')
                elif d.get('type') == 'ai-title' and d.get('sessionId') == sid:
                    if title is None: title = d.get('aiTitle')
            except: pass
    cc_sessions[sid] = title or '(unnamed)'

with open(cc_file) as f: cc_data = json.load(f)

cc_connect_sessions = {}
unlinked_sessions = []
for key, sess in cc_data['sessions'].items():
    aid = sess.get('agent_session_id', '')
    if aid:
        name = sess.get('name', '') or cc_data.get('session_names', {}).get(aid, '')
        cc_connect_sessions[aid] = (key, name or '(unnamed)')
    else:
        unlinked_sessions.append((key, sess.get('name', '(unnamed)')))

all_uuids = set(cc_sessions.keys()) | set(cc_connect_sessions.keys())
print('| UUID | CLI/VSCode Title | cc-connect Name | Status |')
print('|------|-----------------|----------------|--------|')
for uuid in sorted(all_uuids):
    cc_title = cc_sessions.get(uuid, '—')
    cc_key, cc_name = cc_connect_sessions.get(uuid, ('—', '—'))
    if cc_title == cc_name and cc_title != '(unnamed)': status = 'SYNC'
    elif cc_title != '—' and cc_name != '—' and cc_title != cc_name: status = 'MISMATCH'
    elif cc_title == '(unnamed)' and cc_name == '(unnamed)': status = 'both unnamed'
    else: status = 'partial'
    print(f'| {uuid[:8]}... | {cc_title} | {cc_name} | {status} |')

if unlinked_sessions:
    print('\ncc-connect only (no Claude Code session):')
    for key, name in unlinked_sessions: print(f'  {key}: {name}')

for uuid in cc_sessions:
    if uuid not in cc_connect_sessions:
        print(f'\nClaude Code only: {uuid[:8]}... = {cc_sessions[uuid]}')