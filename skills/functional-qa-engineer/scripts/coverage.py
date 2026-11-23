#!/usr/bin/env python3
"""Coverage matrix for one feature: every surface item x every check the knowledge base requires for it.

The matrix lives in the working project (not the skill): ./qa-coverage/<feature>.json
Required checks come from knowledge/graph.json: a check applies to an item when the check's `applies_to`
surfaces include the item's surface type. So every lesson learned from a miss automatically becomes a
required cell on every matching item in every future feature.

Usage:
  coverage.py init <feature>
  coverage.py add-inventory <feature> <inventory.json> --page P [--state S]
        inventory.json = output of scripts/surface_inventory.js (list of {kind, label, ...})
  coverage.py add <feature> --id ID --surface SURFACE --label L [--page P] [--state S]
        manual items: states, actors, entry surfaces, environments, flows from the baseline
  coverage.py mark <feature> --id ID --check CHECK --result pass|fail|na|intermittent|blocked [--evidence E] [--build B] [--reason R]
        --id may be a prefix ending in * to mark many items (e.g. "flows/*")
        intermittent = tested, behaves inconsistently (counts as tested, listed like a failure; file it as an intermittent bug)
        blocked      = can't be tested right now (env down, no access, an upstream bug); --reason is required:
                       what blocks it and who/what unblocks it. Blocked cells are not counted as tested.
  coverage.py exclude <feature> --id ID [--check CHECK] --reason R
  coverage.py report <feature> [--gaps N]
        prints % done; exit 1 = NOT COMPLETE (untested cells remain)
                       exit 3 = COMPLETE EXCEPT BLOCKED (everything testable is tested; sign off only as
                                Go-with-conditions that lists each blocker, and retest those cells when unblocked)
                       exit 0 = COMPLETE
"""
import argparse, json, os, re, sys, fnmatch

HERE = os.path.dirname(os.path.abspath(__file__))
GRAPH = os.path.join(os.path.dirname(HERE), 'knowledge', 'graph.json')
GRAPH = os.environ.get('QA_KB_GRAPH', GRAPH)  # override for the self-test
KIND_TO_SURFACE = {  # inventory element kind -> surface type in the knowledge graph
    'button': 'cta', 'link': 'cta', 'menuitem': 'cta',
    'tab': 'navigation',
    'textbox': 'form-field', 'textarea': 'form-field', 'combobox': 'form-field', 'spinbutton': 'form-field', 'searchbox': 'form-field',
    'checkbox': 'hidden-option', 'menuitemcheckbox': 'hidden-option', 'switch': 'hidden-option', 'radio': 'form-field',
    'option': 'hidden-option', 'menuitemradio': 'hidden-option', 'row': 'list',
}
# every feature also gets one item per feature-level surface, so global checks can't be skipped
FEATURE_SURFACES = ['overview', 'list', 'run-state', 'error-state', 'copy', 'actor', 'integration', 'theme',
                    'loading', 'live-view', 'api', 'settings', 'planning', 'signals']
# Optional areas (security, performance, accessibility, compatibility, i18n, reliability, data): add with
#   coverage.py add <feature> --id feature/<area> --surface <area> --label ... and kb.py set-optional --mandatory <checks>
# only when the user asks for them.

def kb_checks_for(surface):
    if not os.path.exists(GRAPH):
        return []
    g = json.load(open(GRAPH))
    out = []
    for k, n in g['nodes'].items():
        if n['type'] != 'check' or not n.get('mandatory'):
            continue
        targets = [d for (s, r, d) in g['edges'] if s == k and r == 'applies_to']
        if 'surface:' + surface in targets:
            out.append(k.split(':', 1)[1])
    return sorted(out)

def path(feature):
    return os.path.join(os.getcwd(), 'qa-coverage', re.sub(r'[^A-Za-z0-9._-]+', '-', feature) + '.json')

def load(feature):
    p = path(feature)
    if not os.path.exists(p):
        sys.exit(f'no matrix for {feature}; run: coverage.py init "{feature}"')
    return json.load(open(p))

def save(feature, m):
    os.makedirs(os.path.dirname(path(feature)), exist_ok=True)
    json.dump(m, open(path(feature), 'w'), indent=1, ensure_ascii=False)

def add_item(m, iid, surface, label, page=None, state=None):
    it = m['items'].setdefault(iid, {'surface': surface, 'label': label, 'page': page, 'state': state, 'done': {}, 'excluded': {}})
    it['required'] = sorted(set(it.get('required', [])) | set(kb_checks_for(surface)))
    return it

def cmd_init(a):
    m = {'feature': a.feature, 'items': {}}
    for s in FEATURE_SURFACES:
        add_item(m, f'feature/{s}', s, f'feature-level: {s}')
    save(a.feature, m); print('created', path(a.feature))

def cmd_add_inventory(a):
    m = load(a.feature); inv = json.load(open(a.inventory)); n = 0
    if isinstance(inv, dict): inv = inv.get('items', [])
    for el in inv:
        surface = KIND_TO_SURFACE.get(el.get('kind'), 'cta')
        iid = f"{a.page}/{a.state + '/' if a.state else ''}{el.get('kind')}:{el.get('label','')[:60]}"
        add_item(m, iid, surface, el.get('label', ''), a.page, a.state); n += 1
    save(a.feature, m); print(f'added {n} items from {a.inventory}')

def cmd_add(a):
    m = load(a.feature); add_item(m, a.id, a.surface, a.label, a.page, a.state); save(a.feature, m); print('added', a.id)

def match(m, pattern):
    ids = [i for i in m['items'] if fnmatch.fnmatch(i, pattern)]
    if not ids:
        sys.exit(f'no item matches {pattern}')
    return ids

def cmd_mark(a):
    if a.result == 'blocked' and not (a.reason or '').strip():
        sys.exit('--result blocked needs --reason: what blocks it and who/what unblocks it')
    m = load(a.feature)
    for i in match(m, a.id):
        m['items'][i]['done'][a.check] = {'result': a.result, 'evidence': a.evidence, 'build': a.build, 'reason': a.reason}
    save(a.feature, m); print('marked', a.check, 'on', len(match(m, a.id)), 'item(s)')

def cmd_exclude(a):
    m = load(a.feature)
    for i in match(m, a.id):
        m['items'][i]['excluded'][a.check or '*'] = a.reason
    save(a.feature, m); print('excluded', a.id)

def cmd_report(a):
    m = load(a.feature)
    # refresh required checks from the KB (new lessons apply retroactively)
    for it in m['items'].values():
        it['required'] = sorted(set(it.get('required', [])) | set(kb_checks_for(it['surface'])))
    save(a.feature, m)
    total = done = 0; gaps = []; fails = []; flaky = []; blocked = []
    for iid, it in sorted(m['items'].items()):
        for c in it['required']:
            total += 1
            res = it['done'].get(c, {})
            if '*' in it['excluded'] or c in it['excluded']:
                done += 1
            elif res.get('result') == 'blocked':
                blocked.append(f'{iid} :: {c} :: {res.get("reason")}')
            elif c in it['done']:
                done += 1
                if res.get('result') == 'fail':
                    fails.append(f'{iid} :: {c} :: {res.get("evidence")}')
                elif res.get('result') == 'intermittent':
                    flaky.append(f'{iid} :: {c} :: {res.get("evidence")}')
            else:
                gaps.append(f'{iid} :: {c}')
    pct = 100.0 * done / total if total else 0.0
    testable = total - len(blocked)
    tpct = 100.0 * done / testable if testable else 0.0
    print(f'coverage {a.feature}: {done}/{total} required cells = {pct:.1f}%  ({len(m["items"])} items)')
    if blocked:
        print(f'  of the testable cells: {done}/{testable} = {tpct:.1f}%  ·  blocked: {len(blocked)}')
    print(f'failing cells: {len(fails)}'); [print('  FAIL', f) for f in fails[:50]]
    if flaky:
        print(f'intermittent cells: {len(flaky)}'); [print('  FLAKY', f) for f in flaky[:50]]
    if blocked:
        print(f'blocked cells: {len(blocked)}'); [print('  BLOCKED', b) for b in blocked[:a.gaps or 50]]
    if gaps:
        print(f'NOT COMPLETE — {len(gaps)} untested cells:'); [print('  GAP ', g) for g in gaps[:a.gaps]]
        if len(gaps) > a.gaps: print(f'  ... {len(gaps) - a.gaps} more')
        sys.exit(1)
    if blocked:
        print('COMPLETE EXCEPT BLOCKED: every testable cell is tested or excluded. Sign off only as Go-with-conditions,')
        print('  list each blocked cell and its blocker in the report, and retest those cells when they are unblocked.')
        sys.exit(3)
    print('COMPLETE: every required cell is tested or excluded with a reason')

def main():
    p = argparse.ArgumentParser(); sp = p.add_subparsers(dest='cmd', required=True)
    i = sp.add_parser('init'); i.add_argument('feature')
    ai = sp.add_parser('add-inventory'); ai.add_argument('feature'); ai.add_argument('inventory'); ai.add_argument('--page', required=True); ai.add_argument('--state')
    ad = sp.add_parser('add'); ad.add_argument('feature')
    for k in ('id', 'surface', 'label'): ad.add_argument('--' + k, required=True)
    ad.add_argument('--page'); ad.add_argument('--state')
    mk = sp.add_parser('mark'); mk.add_argument('feature')
    for k in ('id', 'check'): mk.add_argument('--' + k, required=True)
    mk.add_argument('--result', required=True, choices=['pass', 'fail', 'na', 'intermittent', 'blocked']); mk.add_argument('--evidence'); mk.add_argument('--build')
    mk.add_argument('--reason', help='required for --result blocked: what blocks it and who/what unblocks it')
    ex = sp.add_parser('exclude'); ex.add_argument('feature'); ex.add_argument('--id', required=True); ex.add_argument('--check'); ex.add_argument('--reason', required=True)
    r = sp.add_parser('report'); r.add_argument('feature'); r.add_argument('--gaps', type=int, default=40)
    a = p.parse_args()
    {'init': cmd_init, 'add-inventory': cmd_add_inventory, 'add': cmd_add, 'mark': cmd_mark, 'exclude': cmd_exclude, 'report': cmd_report}[a.cmd](a)

if __name__ == '__main__':
    main()
