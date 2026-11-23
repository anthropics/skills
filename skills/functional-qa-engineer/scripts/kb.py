#!/usr/bin/env python3
"""QA knowledge graph: bugs, why they were missed, the rules learned, and the checks that enforce them.

Stored at <skill>/knowledge/graph.json. Node types:
  surface  - a kind of UI/API surface (cta, column, loading, live-view, form-field, run-state, ...)
  oracle   - a judging rule from references/oracles.md (O1..O21)
  check    - a concrete, executable check ("click every CTA on every state and verify the landing page")
  lesson   - a generalised rule learned from a miss ("hidden options must be enabled once")
  bug      - a real bug (with product, who found it, whether the process caught it)
  cause    - why a bug was missed: coverage-gap | oracle-gap | baseline-gap | probe-error | instrument-gap | judgement
Edges: (src, rel, dst) e.g. bug -missed_because-> cause, bug -taught-> lesson, lesson -enforced_by-> check,
       check -applies_to-> surface, check -uses-> oracle, bug -found_on-> surface, bug -caught_by-> check.

Usage:
  kb.py stats
  kb.py checks [--surface S ...]           list mandatory checks (all, or for given surface types)
  kb.py add-miss --bug ID --title T --product P --found-by WHO --surface S --cause C
                 --lesson "rule" --check "concrete check" [--oracle O17] [--check-id ID]
                                            record a bug the process missed and what now prevents it
  kb.py add-caught --bug ID --title T --product P --surface S --check CHECK_ID
                                            record a bug the process caught (strengthens the check)
  kb.py add-check --id ID --text T [--surface S ...] [--oracle O ...]   add a standard check
  kb.py misses                              list all missed bugs, cause, and the check that now covers them
  kb.py render [--out FILE.md]              write a Mermaid graph + tables (default: knowledge/GRAPH.md)
"""
import argparse, json, os, re, sys, datetime

HERE = os.path.dirname(os.path.abspath(__file__))
KDIR = os.path.join(os.path.dirname(HERE), 'knowledge')
GRAPH = os.path.join(KDIR, 'graph.json')
GRAPH = os.environ.get('QA_KB_GRAPH', GRAPH)  # override for the self-test
CAUSES = {
    'coverage-gap': 'the surface/state was never exercised',
    'oracle-gap': 'it was exercised but nothing judged it wrong',
    'baseline-gap': 'the expectation was not in the checklist (new or unread requirement)',
    'probe-error': 'the test script measured the wrong thing',
    'instrument-gap': 'the tool could not observe it (e.g. DOM vs pixels)',
    'judgement': 'it was seen but wrongly dismissed or mis-rated',
}

def load():
    if not os.path.exists(GRAPH):
        return {'nodes': {}, 'edges': []}
    with open(GRAPH) as f:
        return json.load(f)

def save(g):
    os.makedirs(os.path.dirname(GRAPH), exist_ok=True)
    with open(GRAPH, 'w') as f:
        json.dump(g, f, indent=1, ensure_ascii=False, sort_keys=True)

def slug(s):
    return re.sub(r'[^a-z0-9]+', '-', s.lower()).strip('-')[:48]

def node(g, nid, ntype, **attrs):
    n = g['nodes'].setdefault(nid, {'type': ntype})
    for k, v in attrs.items():
        if v is not None:
            n[k] = v
    return nid

def edge(g, s, rel, d):
    e = [s, rel, d]
    if e not in g['edges']:
        g['edges'].append(e)

def out(g, s, rel):
    return [d for (a, r, d) in g['edges'] if a == s and r == rel]

def inn(g, d, rel):
    return [a for (a, r, b) in g['edges'] if b == d and r == rel]

def cmd_stats(g, a):
    from collections import Counter
    c = Counter(n['type'] for n in g['nodes'].values())
    print(json.dumps({'nodes': dict(c), 'edges': len(g['edges'])}, indent=1))

def cmd_checks(g, a):
    checks = [k for k, n in g['nodes'].items() if n['type'] == 'check']
    if a.surface:
        want = {'surface:' + s for s in a.surface}
        checks = [c for c in checks if want & set(out(g, c, 'applies_to')) or not out(g, c, 'applies_to')]
    for c in sorted(checks):
        n = g['nodes'][c]
        surf = ', '.join(x.split(':', 1)[1] for x in out(g, c, 'applies_to')) or 'all'
        orc = ', '.join(x.split(':', 1)[1] for x in out(g, c, 'uses'))
        learned = ', '.join(x.split(':', 1)[1] for x in inn(g, c, 'enforced_by'))
        print(f"- [{c.split(':',1)[1]}] {n['text']}\n    surfaces: {surf}" + (f" | oracle: {orc}" if orc else '') + (f" | from lesson: {learned}" if learned else ''))

def cmd_add_miss(g, a):
    if a.cause not in CAUSES:
        sys.exit(f"cause must be one of {list(CAUSES)}")
    b = node(g, 'bug:' + a.bug, 'bug', title=a.title, product=a.product, found_by=a.found_by, caught=False,
             date=datetime.date.today().isoformat())
    s = node(g, 'surface:' + a.surface, 'surface')
    cz = node(g, 'cause:' + a.cause, 'cause', text=CAUSES[a.cause])
    lid = 'lesson:' + slug(a.lesson)
    l = node(g, lid, 'lesson', text=a.lesson)
    cid = 'check:' + (a.check_id or slug(a.check))
    c = node(g, cid, 'check', text=a.check, mandatory=True)
    edge(g, b, 'found_on', s); edge(g, b, 'missed_because', cz); edge(g, b, 'taught', l)
    edge(g, l, 'enforced_by', c); edge(g, c, 'applies_to', s)
    for o in (a.oracle or []):
        edge(g, c, 'uses', node(g, 'oracle:' + o, 'oracle'))
    save(g)
    print(f"recorded {b}: cause={a.cause} lesson={lid} check={cid}")

def cmd_add_caught(g, a):
    b = node(g, 'bug:' + a.bug, 'bug', title=a.title, product=a.product, caught=True,
             date=datetime.date.today().isoformat())
    s = node(g, 'surface:' + a.surface, 'surface')
    c = 'check:' + a.check
    if c not in g['nodes']:
        sys.exit(f"unknown check {c}; list with: kb.py checks")
    edge(g, b, 'found_on', s); edge(g, b, 'caught_by', c)
    save(g); print(f"recorded {b} caught by {c}")

def cmd_add_check(g, a):
    c = node(g, 'check:' + a.id, 'check', text=a.text, mandatory=True)
    for s in (a.surface or []):
        edge(g, c, 'applies_to', node(g, 'surface:' + s, 'surface'))
    for o in (a.oracle or []):
        edge(g, c, 'uses', node(g, 'oracle:' + o, 'oracle'))
    save(g); print('added', c)

def cmd_set_optional(g, a):
    for cid in a.ids:
        k = 'check:' + cid
        if k not in g['nodes']:
            sys.exit(f'unknown check {k}')
        g['nodes'][k]['mandatory'] = bool(a.mandatory)
        g['nodes'][k]['note'] = a.reason
    save(g); print(('mandatory' if a.mandatory else 'optional') + ':', ', '.join(a.ids))

def cmd_misses(g, a):
    for k, n in sorted(g['nodes'].items()):
        if n['type'] != 'bug' or n.get('caught'):
            continue
        cause = ', '.join(x.split(':', 1)[1] for x in out(g, k, 'missed_because'))
        checks = [c for l in out(g, k, 'taught') for c in out(g, l, 'enforced_by')]
        print(f"- {k.split(':',1)[1]} ({n.get('product','')}, found by {n.get('found_by','?')}): {n.get('title','')}\n"
              f"    missed because: {cause} | now covered by: {', '.join(c.split(':',1)[1] for c in checks)}")

def cmd_render(g, a):
    path = a.out or os.path.join(KDIR, 'GRAPH.md')
    ids = {k: f"n{i}" for i, k in enumerate(sorted(g['nodes']))}
    shape = {'bug': ('[', ']'), 'cause': ('{{', '}}'), 'lesson': ('([', '])'), 'check': ('[[', ']]'),
             'surface': ('((', '))'), 'oracle': ('>', ']')}
    L = ['# QA knowledge graph', '', f"_Generated {datetime.datetime.now():%Y-%m-%d %H:%M}. Source: knowledge/graph.json — edit with scripts/kb.py, not by hand._", '',
         '```mermaid', 'graph LR']
    for k, n in sorted(g['nodes'].items()):
        o, c = shape.get(n['type'], ('[', ']'))
        label = (k.split(':', 1)[1] if n['type'] in ('surface', 'oracle', 'cause') else (n.get('title') or n.get('text') or k))
        label = label.replace('"', "'")[:60]
        L.append(f'  {ids[k]}{o}"{n["type"]}: {label}"{c}')
    for s, r, d in g['edges']:
        L.append(f'  {ids[s]} -- {r} --> {ids[d]}')
    L += ['```', '', '## Mandatory checks', '']
    for c in sorted(k for k, n in g['nodes'].items() if n['type'] == 'check'):
        L.append(f"- **{c.split(':',1)[1]}** — {g['nodes'][c]['text']} (surfaces: {', '.join(x.split(':',1)[1] for x in out(g, c, 'applies_to')) or 'all'})")
    L += ['', '## Missed bugs and what now prevents them', '', '| Bug | Product | Found by | Cause | Lesson | Check |', '|---|---|---|---|---|---|']
    for k, n in sorted(g['nodes'].items()):
        if n['type'] == 'bug' and not n.get('caught'):
            les = out(g, k, 'taught')
            L.append(f"| {k.split(':',1)[1]} {n.get('title','')} | {n.get('product','')} | {n.get('found_by','')} | "
                     f"{', '.join(x.split(':',1)[1] for x in out(g, k, 'missed_because'))} | "
                     f"{'; '.join(g['nodes'][l]['text'] for l in les)} | "
                     f"{', '.join(c.split(':',1)[1] for l in les for c in out(g, l, 'enforced_by'))} |")
    with open(path, 'w') as f:
        f.write('\n'.join(L) + '\n')
    print('wrote', path)

def main():
    p = argparse.ArgumentParser()
    sp = p.add_subparsers(dest='cmd', required=True)
    sp.add_parser('stats')
    c = sp.add_parser('checks'); c.add_argument('--surface', nargs='*')
    m = sp.add_parser('add-miss')
    for k in ('bug', 'title', 'product', 'found-by', 'surface', 'cause', 'lesson', 'check'):
        m.add_argument('--' + k, required=True)
    m.add_argument('--oracle', nargs='*'); m.add_argument('--check-id')
    cc = sp.add_parser('add-caught')
    for k in ('bug', 'title', 'product', 'surface', 'check'):
        cc.add_argument('--' + k, required=True)
    ac = sp.add_parser('add-check'); ac.add_argument('--id', required=True); ac.add_argument('--text', required=True)
    ac.add_argument('--surface', nargs='*'); ac.add_argument('--oracle', nargs='*')
    so = sp.add_parser('set-optional'); so.add_argument('ids', nargs='+'); so.add_argument('--reason', required=True)
    so.add_argument('--mandatory', action='store_true', help='switch back to mandatory')
    sp.add_parser('misses')
    r = sp.add_parser('render'); r.add_argument('--out')
    a = p.parse_args()
    g = load()
    {'stats': cmd_stats, 'checks': cmd_checks, 'add-miss': cmd_add_miss, 'add-caught': cmd_add_caught,
     'add-check': cmd_add_check, 'set-optional': cmd_set_optional, 'misses': cmd_misses, 'render': cmd_render}[a.cmd](g, a)

if __name__ == '__main__':
    main()
