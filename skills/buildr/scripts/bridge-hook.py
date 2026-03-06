#!/usr/bin/env python3
"""
Buildr Bridge Hook - PreToolUse hook for CC <> Telegram bridge

Runs before every Claude Code tool call:
1. Auto-heartbeat (keeps relay daemon informed CC is alive)
2. STOP flag → block CC, auto-enter await mode
3. Await flag → notify user on TG, poll until they respond (NO TIMEOUT)
4. New unread messages → inject into CC context (block once)
5. Otherwise → allow tool call

Zero API calls. Pure file-based IPC.
"""
import json, os, sys, time

# --- Paths ---
BUILDR_HOME = os.environ.get('BUILDR_HOME', os.path.join(os.path.expanduser('~'), '.buildr'))

STOP_FLAG    = os.path.join(BUILDR_HOME, 'stop-flag')
AWAIT_FLAG   = os.path.join(BUILDR_HOME, 'await-flag')
INBOX        = os.path.join(BUILDR_HOME, 'inbox.jsonl')
OUTBOX       = os.path.join(BUILDR_HOME, 'outbox.jsonl')
SHOWN_FILE   = os.path.join(BUILDR_HOME, 'hook-shown')
HEARTBEAT    = os.path.join(BUILDR_HOME, 'heartbeat')

# --- Auto-heartbeat on every tool call ---
try:
    with open(HEARTBEAT, 'w') as f:
        f.write(str(int(time.time() * 1000)))
except:
    pass

# --- Helpers ---
def read_inbox():
    msgs = []
    if os.path.exists(INBOX):
        with open(INBOX) as f:
            for line in f:
                line = line.strip()
                if line:
                    try:
                        msgs.append(json.loads(line))
                    except:
                        pass
    return msgs

def get_last_shown():
    try:
        with open(SHOWN_FILE) as f:
            return int(f.read().strip())
    except:
        return 0

def set_last_shown(uid):
    with open(SHOWN_FILE, 'w') as f:
        f.write(str(uid))

def write_outbox(text):
    with open(OUTBOX, 'a') as f:
        f.write(json.dumps({'text': text}) + '\n')

def output(decision, reason=None):
    result = {"decision": decision}
    if reason:
        result["reason"] = reason
    print(json.dumps(result))
    sys.exit(0)

# --- 1. STOP check ---
if os.path.exists(STOP_FLAG):
    try:
        os.unlink(STOP_FLAG)
    except:
        pass
    # Auto-create await flag so CC enters wait mode on next tool call
    with open(AWAIT_FLAG, 'w') as f:
        f.write('stop')
    msgs = read_inbox()
    recent = msgs[-5:]
    lines = [f"  - {m.get('from','User')}: {m.get('text','')[:200]}" for m in recent]
    reason = (
        "\U0001f6d1 STOP received from Telegram. Halting current work.\n\n"
        "Recent messages:\n" + "\n".join(lines) + "\n\n"
        "Await mode auto-created. Make any tool call to wait for user input.\n"
        "The hook will notify the user on Telegram and wait for their response."
    )
    output("block", reason)

# --- 2. Await mode (poll TG until user responds - NO TIMEOUT) ---
if os.path.exists(AWAIT_FLAG):
    try:
        os.unlink(AWAIT_FLAG)
    except:
        pass

    # Clean up stale permission files so relay doesn't intercept await messages
    for f in ['perm-reqid', 'perm-response']:
        p = os.path.join(BUILDR_HOME, f)
        if os.path.exists(p):
            try: os.unlink(p)
            except: pass

    # Notify user on TG
    write_outbox(
        "CC is waiting for you.\n\n"
        "Reply:\n"
        "\u2022 YES - continue\n"
        "\u2022 Or send any message with instructions\n\n"
        "(No timeout - waiting until you respond)"
    )

    # Baseline: current max update_id
    msgs = read_inbox()
    baseline = max((m.get('update_id', 0) for m in msgs), default=0)

    # Poll forever
    while True:
        time.sleep(2)
        # Keep heartbeat alive during polling
        try:
            with open(HEARTBEAT, 'w') as f:
                f.write(str(int(time.time() * 1000)))
        except:
            pass
        msgs = read_inbox()
        for m in msgs:
            uid = m.get('update_id', 0)
            text = m.get('text', '').strip()
            if uid > baseline and text.lower() != 'stop':
                set_last_shown(uid)
                if text.lower() in ('yes', 'y'):
                    output("allow")
                else:
                    reason = (
                        "User responded on Telegram:\n\n"
                        f"  [{m.get('from','User')}]: {text[:500]}\n\n"
                        "Process this message and respond.\n"
                        "Mirror your reply to TG via outbox:\n"
                        f"python3 -c \"import json; open('{OUTBOX}','a').write(json.dumps({{'text':'YOUR REPLY'}}) + '\\n')\""
                    )
                    output("block", reason)

# --- 3. New unread messages → inject once ---
last_shown = get_last_shown()
msgs = read_inbox()
new_msgs = []
max_uid = last_shown

SKIP = {'yes', 'y', 'no', 'n', 'stop'}
for m in msgs:
    uid = m.get('update_id', 0)
    text = m.get('text', '').strip().lower()
    if uid > last_shown and text not in SKIP:
        new_msgs.append(m)
        max_uid = max(max_uid, uid)

if new_msgs:
    set_last_shown(max_uid)
    lines = []
    for m in new_msgs:
        sender = m.get('from', 'User')
        text = m.get('text', '')[:500]
        lines.append(f"  [{sender}]: {text}")

    reason = (
        "New Telegram message(s):\n\n" +
        "\n".join(lines) + "\n\n"
        "Respond to these, then mirror reply to TG via outbox:\n"
        f"python3 -c \"import json; open('{OUTBOX}','a').write(json.dumps({{'text':'YOUR REPLY'}}) + '\\n')\"\n\n"
        "After responding, continue with your current task."
    )
    output("block", reason)

# --- 4. All clear ---
output("allow")
