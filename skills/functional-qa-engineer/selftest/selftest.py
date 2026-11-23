#!/usr/bin/env python3
"""Self-test, non-browser half: proves the gates and generators still enforce the lessons.
  P1 prereport gate blocks each recorded judgement/probe mistake and passes a good bug;
     a flaky bug can be filed as intermittent (attempts + rate); a blocked bug needs blocked_by
  P2 testgen: BVA includes max+1 and the multi-byte case; pairwise covers every pair
  P3 coverage: a new KB check applies retroactively to an existing matrix (temp KB, real KB untouched);
     blocked cells need a reason and give 'complete except blocked' (exit 3), not a dead end
  P4 knowledge-graph integrity: every miss -> cause, lesson -> check -> surface; no dangling checks
Exit 1 if anything fails. Run: python3 selftest/selftest.py   (from anywhere)
"""
import json, os, shutil, subprocess, sys, tempfile
SKILL = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SC = os.path.join(SKILL, 'scripts'); KB = os.path.join(SKILL, 'knowledge', 'graph.json')
results = []
def rec(name, ok, detail=''):
    results.append((name, ok, detail)); print(('PASS ' if ok else 'FAIL ') + name + (f' — {detail}' if detail else ''))
def run(args, cwd=None, env=None):
    p = subprocess.run([sys.executable, '-I'] + args, cwd=cwd, env=env, capture_output=True, text=True)
    return p.returncode, p.stdout + p.stderr

tmp = tempfile.mkdtemp(prefix='qa-selftest-')
try:
    # P1 prereport gate
    os.makedirs(os.path.join(tmp, 'qa-bugs'))
    good = {"id": "G1", "title": "Notes over 2,000 chars are cut on read", "severity": "Medium", "status": "open", "steps": "s", "expected": "e", "actual": "a",
            "evidence": {"screenshots": ["x.jpg"], "backend": "GET length 2000"}, "repro": {"count": 2, "real_action": True, "screenshot_checked": True}, "user_path": "ui"}
    cases = {
        'R5 api-only rated High (M10)': dict(good, id='M10', user_path='api-only', severity='High'),
        'R6 not-reproduced closed without confirmation (M11)': dict(good, id='M11', status='fixed', status_history=['open', 'not-reproduced'], verified_build='x'),
        'R7 forced trigger without approval (M11 forced)': dict(good, id='M11F', forced_trigger=True),
        'R2/R4 probe artefact: no backend, no real action (M12)': dict(good, id='M12', evidence={"screenshots": ["x.jpg"]}, repro={"count": 1, "real_action": False, "screenshot_checked": False}),
        'R10 intermittent without attempts': dict(good, id='I1', status='intermittent', repro={"count": 1, "real_action": True, "screenshot_checked": True}),
        'R11 blocked without blocked_by': dict(good, id='K1', status='blocked'),
    }
    for name, bug in cases.items():
        json.dump([bug], open(os.path.join(tmp, 'qa-bugs', 'c.json'), 'w'))
        code, out = run([os.path.join(SC, 'prereport.py'), 'check', 'c'], cwd=tmp)
        rec('P1 gate blocks ' + name, code == 1, out.strip().splitlines()[1] if code == 1 and len(out.strip().splitlines()) > 1 else out.strip()[:120])
    json.dump([good], open(os.path.join(tmp, 'qa-bugs', 'g.json'), 'w'))
    code, out = run([os.path.join(SC, 'prereport.py'), 'check', 'g'], cwd=tmp)
    rec('P1 gate passes a well-evidenced bug', code == 0)
    flaky = dict(good, id='I2', status='intermittent', repro={"count": 2, "attempts": 10, "real_action": True, "screenshot_checked": True})
    blocked = dict(good, id='K2', status='blocked', blocked_by='stage DB down; ops restoring it')
    json.dump([flaky, blocked], open(os.path.join(tmp, 'qa-bugs', 'f.json'), 'w'))
    code, out = run([os.path.join(SC, 'prereport.py'), 'check', 'f'], cwd=tmp)
    rec('P1 gate accepts a flaky bug filed as intermittent (2/10) and a blocked bug with blocked_by', code == 0 and '2/10' in out, out.strip().splitlines()[0] if out else '')

    # P2 testgen
    code, out = run([os.path.join(SC, 'testgen.py'), 'bva', '--min', '0', '--max', '10000'])
    rec('P2 BVA has max+1 and multi-byte boundary', '10001 chars | invalid' in out and 'multi-byte' in out)
    code, out = run([os.path.join(SC, 'testgen.py'), 'pairwise', '--param', 'a=1,2,3', '--param', 'b=x,y,z', '--param', 'c=p,q', '--param', 'd=m,n,o'])
    rec('P2 pairwise covers all pairs', 'all pairs covered: True' in out, out.splitlines()[0] if out else '')

    # P3 coverage retroactive with a temp KB
    tkb = os.path.join(tmp, 'graph.json'); shutil.copy(KB, tkb)
    env = dict(os.environ, QA_KB_GRAPH=tkb)
    run([os.path.join(SC, 'coverage.py'), 'init', 'st'], cwd=tmp, env=env)
    _, o1 = run([os.path.join(SC, 'coverage.py'), 'report', 'st', '--gaps', '0'], cwd=tmp, env=env)
    run([os.path.join(SC, 'kb.py'), 'add-check', '--id', 'selftest-probe', '--text', 'temp', '--surface', 'overview'], env=env)
    _, o2 = run([os.path.join(SC, 'coverage.py'), 'report', 'st', '--gaps', '0'], cwd=tmp, env=env)
    n = lambda o: int(o.split('/')[1].split()[0]) if '/' in o else -1
    rec('P3 new lesson applies retroactively to an existing matrix', n(o2) == n(o1) + 1, f'{n(o1)} -> {n(o2)} required cells')
    _, o3 = run([os.path.join(SC, 'coverage.py'), 'report', 'st', '--gaps', '0'], cwd=tmp, env=env)
    rec('P3 gate refuses sign-off below 100%', 'NOT COMPLETE' in o3)
    cov = os.path.join(SC, 'coverage.py')
    code_nr, _ = run([cov, 'mark', 'st', '--id', 'feature/api', '--check', 'reachability', '--result', 'blocked'], cwd=tmp, env=env)
    rec('P3 blocked cell needs a reason', code_nr != 0)
    m = json.load(open(os.path.join(tmp, 'qa-coverage', 'st.json')))
    for iid, it in m['items'].items():
        for c in it['required']:
            if iid == 'feature/api': it['done'][c] = {'result': 'blocked', 'reason': 'API gateway down on stage'}
            else: it['done'][c] = {'result': 'pass'}
    json.dump(m, open(os.path.join(tmp, 'qa-coverage', 'st.json'), 'w'))
    code4, o4 = run([cov, 'report', 'st', '--gaps', '0'], cwd=tmp, env=env)
    rec('P3 only blocked cells left -> COMPLETE EXCEPT BLOCKED (exit 3), not stuck', code4 == 3 and 'COMPLETE EXCEPT BLOCKED' in o4 and 'API gateway down' in o4, o4.splitlines()[1] if len(o4.splitlines()) > 1 else o4)

    # P4 KB integrity
    g = json.load(open(KB)); N = g['nodes']; E = g['edges']
    out_ = lambda s, r: [d for a, rr, d in E if a == s and rr == r]
    bad = []
    for k, v in N.items():
        if v['type'] == 'bug' and not v.get('caught'):
            if not out_(k, 'missed_because'): bad.append(k + ' has no cause')
            les = out_(k, 'taught')
            if not les: bad.append(k + ' taught nothing')
            for l in les:
                chks = out_(l, 'enforced_by')
                if not chks: bad.append(l + ' has no check')
                for c in chks:
                    if not N[c].get('mandatory'): bad.append(c + ' (from a miss) is not mandatory')
                    if not out_(c, 'applies_to'): bad.append(c + ' applies to no surface')
    rec('P4 every miss -> cause -> lesson -> mandatory check -> surface', not bad, '; '.join(bad[:5]))
finally:
    shutil.rmtree(tmp, ignore_errors=True)

failed = [r for r in results if not r[1]]
print(f'\nself-test (non-browser): {len(results) - len(failed)}/{len(results)} passed')
sys.exit(1 if failed else 0)
