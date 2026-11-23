#!/usr/bin/env python3
"""Pre-report gate: nothing is reported until every bug passes these checks.

Bugs live in the project: ./qa-bugs/<feature>.json  (a list of bug objects; see `template`).
  prereport.py template                 print an empty bug object with every field explained
  prereport.py check <feature>          validate all bugs; exits 1 if any rule fails
Each rule comes from a real mistake (see knowledge/graph.json):
  R1 required fields          R2 evidence (screenshot + backend confirmation)   R3 reproduced >= 2 times
  R4 probe verified (real mouse/keyboard action + screenshot looked at)         R5 reachability caps severity
  R6 status rules (verified build; 'not-reproduced' -> 'fixed' only if a person confirmed)
  R7 forced trigger needs user approval   R8 likely duplicates   R9 root cause stated as fact without proof
  R10 intermittent: a flaky bug is filed with status 'intermittent' instead of failing R3 — it needs >= 5 attempts,
      >= 1 reproduction, the observed rate, and evidence of a failing occurrence
  R11 blocked: a bug that can't be verified/retested right now needs blocked_by (what blocks it, who unblocks it)
"""
import json, os, re, sys, difflib

SEV = ['Critical', 'High', 'Medium', 'Low']
STATUS = ['open', 'intermittent', 'blocked', 'fixed', 'partly', 'not-fixed', 'not-reproduced', 'not-retested', 'expected', 'duplicate']
MIN_FLAKY_ATTEMPTS = 5
TEMPLATE = {
    "id": "B-01", "title": "One sentence: the wrong behaviour, with the number that proves it",
    "severity": "High", "priority": "P1 (optional: urgency, separate from severity)",
    "status": "open  # one of " + "/".join(STATUS),
    "steps": "Numbered steps from a named project/page", "expected": "What should happen (cite oracle/spec)", "actual": "What happens, measured",
    "evidence": {"screenshots": ["img/b01.jpg"], "backend": "API response / session state / job log line that confirms it", "ids": {"project": "", "run": "", "job": ""}},
    "repro": {"count": 2, "attempts": 2, "real_action": True, "screenshot_checked": True, "conditions": "intermittent only: what seems to make it happen (load, timing, data)"},
    "blocked_by": "status blocked only: what blocks verification/retest and who or what unblocks it",
    "user_path": "ui  # ui | cli | api-only | race",
    "reachability_note": "required when user_path is api-only or race",
    "verified_build": "required for fixed/partly/not-fixed, e.g. 'post-PR123 (deploy 17:08Z)'",
    "status_history": ["open"], "confirmed_by": "person who confirmed a not-reproduced bug is fixed",
    "forced_trigger": False, "user_approved_force": False,
    "root_cause": {"text": "", "proven": False},
}

def check(feature):
    p = os.path.join(os.getcwd(), 'qa-bugs', re.sub(r'[^A-Za-z0-9._-]+', '-', feature) + '.json')
    if not os.path.exists(p):
        sys.exit(f'no bugs file {p}; create it as a JSON list of bug objects (prereport.py template)')
    bugs = json.load(open(p)); fails = []; warns = []
    def F(b, rule, msg): fails.append(f"{b.get('id','?')} {rule}: {msg}")
    def W(b, rule, msg): warns.append(f"{b.get('id','?')} {rule}: {msg}")
    for b in bugs:
        st = (b.get('status') or '').split()[0]
        for k in ('id', 'title', 'severity', 'status', 'steps', 'expected', 'actual'):
            if not b.get(k): F(b, 'R1', f'missing {k}')
        if b.get('severity') not in SEV: F(b, 'R1', f"severity must be one of {SEV}")
        if st not in STATUS: F(b, 'R1', f"status must be one of {STATUS}")
        if st in ('open', 'not-fixed', 'partly', 'intermittent'):
            ev = b.get('evidence') or {}
            if not ev.get('screenshots'): F(b, 'R2', 'no screenshot (for an intermittent bug: a screenshot or recording of a failing occurrence)')
            if not ev.get('backend'): F(b, 'R2', 'no backend confirmation (API/session/log) — could be a probe artefact')
            r = b.get('repro') or {}
            if st == 'intermittent':
                att, cnt = r.get('attempts') or 0, r.get('count') or 0
                if cnt < 1: F(b, 'R10', 'intermittent bug never reproduced by you — record at least one failing occurrence')
                if att < MIN_FLAKY_ATTEMPTS: F(b, 'R10', f'intermittent: record attempts (>= {MIN_FLAKY_ATTEMPTS}) so the rate is known; have {att}')
                elif cnt > att: F(b, 'R10', 'repro.count is larger than repro.attempts')
                elif cnt == att: W(b, 'R10', f'reproduced {cnt}/{att} — that is not intermittent; use status open')
            elif (r.get('count') or 0) < 2:
                F(b, 'R3', 'reproduced fewer than 2 times (if it is flaky, file it as status intermittent with attempts)')
            if not r.get('real_action'): F(b, 'R4', 'not re-checked with a real mouse/keyboard action')
            if not r.get('screenshot_checked'): F(b, 'R4', 'screenshot not looked at before filing')
        path = (b.get('user_path') or 'ui').split()[0]
        if path in ('api-only', 'race'):
            if b.get('severity') in ('Critical', 'High'): F(b, 'R5', f'user path is {path}: severity must be Medium or lower')
            if not b.get('reachability_note'): F(b, 'R5', 'explain how a user reaches it (reachability_note)')
        if st in ('fixed', 'partly', 'not-fixed') and not b.get('verified_build'): F(b, 'R6', f'{st} needs verified_build')
        hist = b.get('status_history') or []
        if st == 'fixed' and 'not-reproduced' in hist and not b.get('confirmed_by'):
            F(b, 'R6', "moved from not-reproduced to fixed without confirmed_by (only the user/dev closes it)")
        if st == 'blocked' and not (b.get('blocked_by') or '').strip():
            F(b, 'R11', 'blocked needs blocked_by: what blocks verification and who or what unblocks it')
        if b.get('forced_trigger') and not b.get('user_approved_force'): F(b, 'R7', 'artificial trigger used without user approval')
        rc = b.get('root_cause') or {}
        if rc.get('text') and not rc.get('proven') and not re.search(r'hypothes|likely|may|might|suspect', rc['text'], re.I):
            W(b, 'R9', 'root cause stated as fact without proof — label it a hypothesis')
    titles = [(b.get('id'), (b.get('title') or '').lower()) for b in bugs]
    for i in range(len(titles)):
        for j in range(i + 1, len(titles)):
            if difflib.SequenceMatcher(None, titles[i][1], titles[j][1]).ratio() > 0.8:
                W({'id': titles[i][0]}, 'R8', f'possible duplicate of {titles[j][0]}')
    print(f'pre-report gate {feature}: {len(bugs)} bugs, {len(fails)} failures, {len(warns)} warnings')
    for f in fails: print('  FAIL', f)
    for w in warns: print('  WARN', w)
    if fails: print('BLOCKED: fix the failures before reporting'); sys.exit(1)
    for b in bugs:
        st = (b.get('status') or '').split()[0]
        r = b.get('repro') or {}
        if st == 'intermittent': print(f"  NOTE {b.get('id')}: intermittent, reproduced {r.get('count')}/{r.get('attempts')} — state the rate in the report")
        if st == 'blocked': print(f"  NOTE {b.get('id')}: blocked — {b.get('blocked_by')}")
    print('PASS: ready to report')

if __name__ == '__main__':
    if len(sys.argv) >= 2 and sys.argv[1] == 'template':
        print(json.dumps(TEMPLATE, indent=1))
    elif len(sys.argv) >= 3 and sys.argv[1] == 'check':
        check(sys.argv[2])
    else:
        print(__doc__); sys.exit(2)
