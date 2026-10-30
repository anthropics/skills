"""Apply register mode changes: register new, restore cleared, resolve mismatches, update history."""
import json, os, glob, sys
from datetime import datetime, timezone
from resolve_paths import resolve_paths

def build_history(msg_count, timestamp):
    return [{'role': 'user' if i%2==0 else 'assistant', 'content': '.', 'timestamp': timestamp} for i in range(msg_count)]

cc_project_dir, cc_file = resolve_paths()

# Parse command-line args for mismatch resolutions: --resolve s2=cc-connect-name
resolutions = {}
for arg in sys.argv[1:]:
    if arg.startswith('--resolve='):
        parts = arg[len('--resolve='):].split('=')
        if len(parts) == 2: resolutions[parts[0]] = parts[1]

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
now = datetime.now(timezone.utc).isoformat()
counter = data['counter']

registered = []; restored = []; mismatches_resolved = []; history_updated = []

for sid, info in cc_sessions.items():
    if sid not in existing_aids:
        counter += 1
        new_key = f's{counter}'
        data['sessions'][new_key] = {
            'id': new_key, 'name': info['title'], 'agent_session_id': sid,
            'agent_type': 'claudecode', 'history': build_history(info['msg_count'], now),
            'created_at': now, 'updated_at': now
        }
        data['session_names'][sid] = info['title']
        for user_id in data['user_sessions']:
            data['user_sessions'][user_id].append(new_key)
        registered.append((new_key, sid[:12], info['title'], info['msg_count']))

for key, sess in data['sessions'].items():
    aid = sess.get('agent_session_id', '')
    if not aid: continue
    info = cc_sessions.get(aid)
    if not info: continue
    current_name = sess.get('name', '')

    if not current_name:
        data['sessions'][key]['name'] = info['title']
        data['session_names'][aid] = info['title']
        restored.append((key, aid[:12], info['title']))
    elif current_name != info['title']:
        chosen = resolutions.get(key, current_name)
        data['sessions'][key]['name'] = chosen
        data['session_names'][aid] = chosen
        # Sync chosen name to JSONL
        entry = json.dumps({'type': 'custom-title', 'customTitle': chosen, 'sessionId': aid})
        jsonl_path = os.path.join(cc_project_dir, f'{aid}.jsonl')
        with open(jsonl_path, 'a') as f: f.write(entry + '\n')
        mismatches_resolved.append((key, aid[:12], info['title'], chosen))

    current_hlen = len(sess.get('history') or []) if sess.get('history') else 0
    if current_hlen != info['msg_count']:
        data['sessions'][key]['history'] = build_history(info['msg_count'], sess.get('created_at', now))
        history_updated.append((key, current_name or info['title'], current_hlen, info['msg_count']))

data['counter'] = counter
data['past_id_tracking'] = False

tmp = cc_file + '.tmp'
with open(tmp, 'w') as f: json.dump(data, f, indent=2, ensure_ascii=False)
os.replace(tmp, cc_file)

print(f"=== Changes Applied ===")
print(f"Registered: {len(registered)}")
for key, sid, title, count in registered: print(f"  {key}: {sid}... -> \"{title}\" ({count} msgs)")
print(f"Restored: {len(restored)}")
for key, aid, title in restored: print(f"  {key}: {aid}... -> \"{title}\"")
print(f"Mismatches resolved: {len(mismatches_resolved)}")
for key, aid, jsonl_name, chosen in mismatches_resolved: print(f"  {key}: jsonl=\"{jsonl_name}\" -> kept \"{chosen}\"")
print(f"History updated: {len(history_updated)}")
for key, name, old, new in history_updated: print(f"  {key} \"{name}\": {old} -> {new}")
print(f"\npast_id_tracking = False")