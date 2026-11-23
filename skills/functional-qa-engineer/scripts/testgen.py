#!/usr/bin/env python3
"""Compute test values instead of improvising them.

  testgen.py bva --min 1 --max 60 [--type text|int] [--unit chars]
        boundary values (min-1, min, min+1, max-1, max, max+1) + empty/zero/huge, with expected valid/invalid
  testgen.py ep --spec spec.json
        equivalence classes -> one representative per class; spec: {"field": {"valid": {"class": "value"...}, "invalid": {...}}}
  testgen.py pairwise --param policy=allow,readonly --param concurrency=1,3 --param signin=none,steps ...
        a small all-pairs set (greedy) covering every pair of values at least once
  testgen.py states --spec states.json
        spec: {"states": [...], "transitions": [["from","event","to"],...], "events": [...]}
        prints every valid transition, every 2-step path from the start, and every invalid (state,event) pair
"""
import argparse, itertools, json, sys

def bva(a):
    lo, hi, t = a.min, a.max, a.type
    rows = []
    seen = set()
    def add(v, valid, why):
        if v in seen: return
        seen.add(v); rows.append((v, None if valid is None else ('valid' if valid else 'invalid'), why))
    if t == 'int':
        for v, ok, why in [(lo - 1, False, 'below min'), (lo, True, 'min'), (lo + 1, True, 'min+1'), (hi - 1, True, 'max-1'), (hi, True, 'max'), (hi + 1, False, 'above max'),
                           (0, lo <= 0 <= hi, 'zero'), (-1, lo <= -1 <= hi, 'negative'), (2**31, False, 'int overflow'), ('', False, 'empty'), ('1.5', False, 'non-integer'), ('abc', False, 'non-numeric')]:
            add(v, ok, why)
    else:
        unit = a.unit
        for n, ok, why in [(0, lo == 0, 'empty'), (lo - 1, False, 'below min') if lo > 0 else (None, None, None), (lo, True, 'min'), (lo + 1, True, 'min+1'),
                           (hi - 1, True, 'max-1'), (hi, True, 'max'), (hi + 1, False, 'above max'), (hi * 10, False, 'far above max')]:
            if n is None or n < 0: continue
            add(f'{n} {unit}', ok, why)
        add(f'{hi - 1} {unit} + 1 emoji (multi-byte at the boundary)', None, 'unit mismatch (chars vs bytes vs UTF-16)')
        add('whitespace only', lo == 0, 'trimmed?')
        add('leading/trailing spaces', True, 'trimmed or kept consistently')
    print('value | expected | why'); print('---|---|---')
    for v, e, w in rows: print(f'{v} | {e if e is not None else "decide (spec?)"} | {w}')
    print('\nCheck each in the UI, the API directly, and after reload (round-trip).')

def ep(a):
    spec = json.load(open(a.spec))
    for field, cls in spec.items():
        print(f'## {field}')
        for kind in ('valid', 'invalid'):
            for name, val in cls.get(kind, {}).items():
                print(f'- [{kind}] {name}: {val!r}')
        print('  (one invalid class per test case)')

def pairwise(a):
    params = []
    for p in a.param:
        k, v = p.split('=', 1); params.append((k, v.split(',')))
    names = [k for k, _ in params]; vals = [v for _, v in params]
    uncovered = set()
    for (i, vi), (j, vj) in itertools.combinations(list(enumerate(vals)), 2):
        for x in vi:
            for y in vj: uncovered.add((i, x, j, y))
    tests = []
    while uncovered:
        best, best_cov = None, -1
        # greedy: try candidates seeded from an uncovered pair, fill the rest to maximise new pairs
        seeds = list(uncovered)[:50]
        for (i, x, j, y) in seeds:
            row = [None] * len(vals); row[i] = x; row[j] = y
            for k in range(len(vals)):
                if row[k] is not None: continue
                row[k] = max(vals[k], key=lambda v: sum(1 for m in range(len(vals)) if row[m] is not None and m != k and
                                                        ((min(k, m), v if k < m else row[m], max(k, m), row[m] if k < m else v) in uncovered)))
            cov = sum(1 for (p, q) in itertools.combinations(range(len(vals)), 2) if (p, row[p], q, row[q]) in uncovered)
            if cov > best_cov: best, best_cov = row, cov
        tests.append(best)
        for (p, q) in itertools.combinations(range(len(vals)), 2): uncovered.discard((p, best[p], q, best[q]))
    # self-check: every pair of values appears in at least one case
    missing = [(names[i], x, names[j], y) for (i, vi), (j, vj) in itertools.combinations(list(enumerate(vals)), 2) for x in vi for y in vj
               if not any(t[i] == x and t[j] == y for t in tests)]
    full = 1
    for v in vals: full *= len(v)
    print(f'{len(tests)} pairwise cases (vs {full} full combinations); all pairs covered: {not missing}\n')
    print(' | '.join(['#'] + names)); print('|'.join(['---'] * (len(names) + 1)))
    for n, t in enumerate(tests, 1): print(' | '.join([str(n)] + t))

def states(a):
    s = json.load(open(a.spec)); T = s['transitions']; events = s.get('events') or sorted({e for _, e, _ in T})
    start = s.get('start', s['states'][0])
    print('## Valid transitions (0-switch: test each once)')
    for f, e, t in T: print(f'- {f} --{e}--> {t}')
    print(f'\n## Two-step paths from {start} (1-switch, critical paths)')
    for f, e, t in T:
        for f2, e2, t2 in T:
            if f2 == t: print(f'- {f} --{e}--> {t} --{e2}--> {t2}')
    print('\n## Invalid events (must be blocked in UI and refused by API)')
    allowed = {(f, e) for f, e, _ in T}
    for st in s['states']:
        bad = [e for e in events if (st, e) not in allowed]
        if bad: print(f'- in {st}: {", ".join(bad)}')

def main():
    p = argparse.ArgumentParser(); sp = p.add_subparsers(dest='cmd', required=True)
    b = sp.add_parser('bva'); b.add_argument('--min', type=int, required=True); b.add_argument('--max', type=int, required=True)
    b.add_argument('--type', default='text', choices=['text', 'int']); b.add_argument('--unit', default='chars')
    e = sp.add_parser('ep'); e.add_argument('--spec', required=True)
    pw = sp.add_parser('pairwise'); pw.add_argument('--param', action='append', required=True)
    st = sp.add_parser('states'); st.add_argument('--spec', required=True)
    a = p.parse_args(); {'bva': bva, 'ep': ep, 'pairwise': pairwise, 'states': states}[a.cmd](a)

if __name__ == '__main__':
    main()
