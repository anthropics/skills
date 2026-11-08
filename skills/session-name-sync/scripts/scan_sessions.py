"""Scan Claude Code sessions vs cc-connect, output register summary."""
import json, os, glob
from datetime import datetime, timezone
from resolve_paths import resolve_paths

cc_project_dir, cc_file = resolve_paths()

cc_sessions = {}
for f in glob.glob(os.path.join(cc_project_dir, '*.jsonl')):
    sid = os.path.basename(f).replace('.jsonl', '')
    title = None; msg_count = 0
    with open(f) as fh:
        for line in fh:
            try:
                d = json.loads(line)
                if d.get('type') == 'custom-title' and d.get('sessionId') == sid: title = d.get('customTitle')
                elif d.get('type') == 'ai-title' and d.get('sessionId') == sid and title is None: title = d.get('aiTitle')
                elif d.get('type') in ('human', 'user', 'assistant'): msg_count += 1
            except: pass
    if title and title != 'None': cc_sessions[sid] = {'title': title, 'msg_count': msg_count}

with open(cc_file) as f: data = json.load(f)
existing_aids = {sess.get('agent_session_id','') for sess in data['sessions'].values() if sess.get('agent_session_id','')}

registered = []; restored = []; mismatches = []; history_drifts = []

for sid, info in cc_sessions.items():
    if sid not in existing_aids: registered.append((sid[:12], info['title'], info['msg_count']))

for key, sess in data['sessions'].items():
    aid = sess.get('agent_session_id', '')
    if not aid: continue
    info = cc_sessions.get(aid)
    if not info: continue
    current_name = sess.get('name', '')
    if not current_name: restored.append((key, aid[:12], info['title']))
    elif current_name != info['title']: mismatches.append((key, aid[:12], current_name, info['title']))
    current_hlen = len(sess.get('history') or []) if sess.get('history') else 0
    if current_hlen != info['msg_count']: history_drifts.append((key, current_name or info['title'], current_hlen, info['msg_count']))

print(f"=== Register Summary ===")
print(f"New sessions to register: {len(registered)}")
for sid, title, count in registered: print(f"  {sid}... -> \"{title}\" ({count} msgs)")
print(f"Cleared names to restore: {len(restored)}")
for key, aid, title in restored: print(f"  {key}: {aid}... -> \"{title}\"")
print(f"Name mismatches: {len(mismatches)}")
for key, aid, cc_name, jsonl_name in mismatches: print(f"  {key}: cc=\"{cc_name}\" vs jsonl=\"{jsonl_name}\"")
print(f"History count drifts: {len(history_drifts)}")
for key, name, old, new in history_drifts: print(f"  {key} \"{name}\": {old} -> {new}")

needs_restart = len(registered) > 0 or len(restored) > 0 or len(mismatches) > 0
print(f"\nDaemon restart required: {needs_restart}")
if not needs_restart and history_drifts:
    print("NOTE: History drifts are cosmetic only (affects /list display numbers).")
    print("Skipping daemon restart — Feishu connection preserved.")