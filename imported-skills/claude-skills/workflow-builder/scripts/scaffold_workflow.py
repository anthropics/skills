#!/usr/bin/env python3
"""Scaffold a starter Claude Code workflow (.js) file for a chosen topology.

Emits a runnable skeleton with the meta block, a schema, phase()/log() calls,
a guarded loop where relevant, and the correct parallel-thunk / pipeline shape.
Pipe to a file under .claude/workflows/ and then edit the agent prompts.

Stdlib only. Deterministic.
"""
import argparse
import re
import sys

TOPOLOGIES = ("fan-out", "pipeline", "barrier", "loop", "judge-panel")


def _slug(name):
    s = re.sub(r"[^a-z0-9-]+", "-", name.strip().lower()).strip("-")
    return s or "my-workflow"


def _meta(name, description, phases):
    phase_lines = ",\n".join(f"    {{ title: '{p}' }}" for p in phases)
    return (
        "export const meta = {\n"
        f"  name: '{_slug(name)}',\n"
        f"  description: '{description}',\n"
        "  phases: [\n"
        f"{phase_lines}\n"
        "  ]\n"
        "}\n"
    )


SCHEMA = """const FINDINGS_SCHEMA = {
  type: 'object',
  properties: {
    findings: {
      type: 'array',
      items: {
        type: 'object',
        properties: {
          title: { type: 'string' },
          severity: { type: 'string', enum: ['low', 'medium', 'high'] }
        },
        required: ['title']
      }
    }
  },
  required: ['findings']
}
"""


def body_fan_out():
    return """// Fan-out: independent units in parallel, then one synthesis.
const ITEMS = args?.items ?? ['item one', 'item two', 'item three']

phase('Fan out')
const results = await parallel(
  ITEMS.map((item, i) => () =>
    agent(`Do the unit of work for:\\n${item}`,
          { label: `unit:${i + 1}`, model: 'haiku', schema: FINDINGS_SCHEMA }))
)

phase('Synthesize')
const clean = results.filter(Boolean)
const report = await agent(
  `Synthesize these results into one report:\\n${JSON.stringify(clean)}`,
  { model: 'opus' }
)
log(`Done: synthesized ${clean.length} results.`)
return report
"""


def body_pipeline():
    return """// Pipeline: each item flows through stages independently (no barrier).
const ITEMS = args?.items ?? ['item one', 'item two', 'item three']

const results = await pipeline(
  ITEMS,
  // Stage 1 — triage / extract (cheap, high volume).
  (item, _orig, i) =>
    agent(`Triage:\\n${item}`, { label: `triage:${i + 1}`, phase: 'Triage', model: 'haiku', schema: FINDINGS_SCHEMA }),
  // Stage 2 — verify / refine each finding (fewer items, more judgement).
  (prev) =>
    parallel((prev?.findings ?? []).map(f => () =>
      agent(`Verify and refine: ${f.title}`, { phase: 'Verify', model: 'sonnet' })))
)

log(`Done: processed ${results.filter(Boolean).length} items through the pipeline.`)
return results.filter(Boolean)
"""


def body_barrier():
    return """// Barrier: collect the whole set first, then dedup/merge before the next step.
const SOURCES = args?.sources ?? ['source A', 'source B', 'source C']

phase('Collect')
const all = await parallel(SOURCES.map((s, i) => () =>
  agent(`Gather findings from:\\n${s}`, { label: `collect:${i + 1}`, model: 'haiku', schema: FINDINGS_SCHEMA })))

// Merge across the full result set (this is why we need a barrier, not a pipeline).
const merged = all.filter(Boolean).flatMap(r => r.findings ?? [])
const seen = new Set()
const deduped = merged.filter(f => (seen.has(f.title) ? false : (seen.add(f.title), true)))

phase('Synthesize')
const summary = await agent(
  `Summarize these ${deduped.length} unique findings:\\n${JSON.stringify(deduped)}`,
  { model: 'opus' }
)
log(`Done: ${deduped.length} unique findings after dedup.`)
return summary
"""


def body_loop():
    return """// Loop: discover an unknown number of items. GUARDED against the agent cap.
const found = []
const seen = new Set()
let dryRounds = 0
const HARD_CAP = 100

phase('Discover')
while (
  dryRounds < 2 &&
  found.length < HARD_CAP &&
  (!budget.total || budget.remaining() > 50_000)
) {
  const r = await agent(
    `Find items NOT already found:\\n${JSON.stringify([...seen])}`,
    { model: 'sonnet', schema: FINDINGS_SCHEMA }
  )
  const fresh = (r?.findings ?? []).filter(f => !seen.has(f.title))
  fresh.forEach(f => seen.add(f.title))
  found.push(...fresh)
  dryRounds = fresh.length === 0 ? dryRounds + 1 : 0
  log(`Round complete: ${fresh.length} new, ${found.length} total.`)
}
return found
"""


def body_judge_panel():
    return """// Judge panel: diverse drafts, scored in parallel, synthesize the winner.
const ANGLES = args?.angles ?? ['conservative', 'aggressive', 'contrarian']

phase('Draft')
const drafts = (await parallel(ANGLES.map((a, i) => () =>
  agent(`Produce a plan. Take a strictly ${a} approach.`, { label: `draft:${i + 1}`, model: 'sonnet' })))).filter(Boolean)

phase('Score')
const SCORE_SCHEMA = { type: 'object', properties: { score: { type: 'number' } }, required: ['score'] }
const scored = await parallel(drafts.map((d, i) => () =>
  agent(`Score this plan 1-10 with reasons:\\n${d}`, { label: `judge:${i + 1}`, model: 'haiku', schema: SCORE_SCHEMA })))

let best = 0
scored.forEach((s, i) => { if ((s?.score ?? 0) > (scored[best]?.score ?? 0)) best = i })

phase('Refine')
const final = await agent(`Refine the winning plan:\\n${drafts[best]}`, { model: 'opus' })
log(`Done: winner was angle "${ANGLES[best]}".`)
return final
"""


PHASES = {
    "fan-out": ["Fan out", "Synthesize"],
    "pipeline": ["Triage", "Verify"],
    "barrier": ["Collect", "Synthesize"],
    "loop": ["Discover"],
    "judge-panel": ["Draft", "Score", "Refine"],
}
BODIES = {
    "fan-out": body_fan_out,
    "pipeline": body_pipeline,
    "barrier": body_barrier,
    "loop": body_loop,
    "judge-panel": body_judge_panel,
}


def scaffold(topology, name, description):
    parts = [_meta(name, description, PHASES[topology]), "", SCHEMA, "", BODIES[topology]()]
    return "\n".join(parts)


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--topology", choices=TOPOLOGIES, help="orchestration shape to scaffold")
    p.add_argument("--name", help="workflow name (slugified for meta.name)")
    p.add_argument("--description", help="one-line meta.description")
    p.add_argument("--sample", action="store_true", help="emit a built-in pipeline sample")
    args = p.parse_args(argv)

    if args.sample or not args.topology:
        if not args.topology and not args.sample:
            print("No --topology given; emitting --sample (pipeline). Use --help for options.\n", file=sys.stderr)
        out = scaffold("pipeline", "pr-triage", "Triage open PRs for bugs before merge")
    else:
        out = scaffold(args.topology, args.name or args.topology,
                       args.description or f"A {args.topology} workflow")
    print(out)
    return 0


if __name__ == "__main__":
    sys.exit(main())
