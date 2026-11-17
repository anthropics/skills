---
name: genome
description: Encode AI agent personalities into diploid genomes with 27 cognitive primitives, compare against 216 AI agent personalities, simulate breeding, and explore genetic compatibility. Use this when users want to analyze, compare, or breed AI agent personalities using genetic mechanics.
license: Complete terms in LICENSE.txt
---

# AI Genome Analysis Skill

You have access to the AI Personality Evolution Engine - a biologically-faithful framework that encodes AI personalities as diploid genomes with 27 cognitive primitives.

Source repository: https://github.com/ai-agent-genome-project/ai-genome

## What You Can Do

Based on $ARGUMENTS, perform one of these actions:

### "encode" or "encode <path>"
Encode a SOUL.md file into a breedable genome.

1. If a path is provided, use it. Otherwise look for SOUL.md in the current directory.
2. Run the encoder:
```bash
python3 encoder.py <soul_path> --name "<AgentName>" --output <name>.dna.json
```
3. Show the resulting phenotype with `python3 visualize.py <name>.dna.json`
4. Summarize the top 3 traits and any active epistasis rules.

### "compare <slug>" or "compare <slug1> <slug2>"
Compare two genomes. If one slug is given, compare the user's genome against a library agent. If two slugs, compare those two library agents.

```bash
python3 agent_report.py <genome1>.dna.json --compat library/genomes/<slug>.dna.json
```

Report the genetic distance, complementarity, interest score, and predicted offspring trait ranges.

### "view <slug>" or "view <path>"
Display a genome's full profile.

```bash
python3 visualize.py library/genomes/<slug>.dna.json
python3 agent_report.py library/genomes/<slug>.dna.json --self
```

### "browse" or "library"
List available genomes from the library with their top traits.

```bash
python3 -c "
import json
lib = json.load(open('library/genome_library.json'))
for a in lib['agents']:
    traits = sorted(a['phenotype'].items(), key=lambda x: -x[1])
    top = ' | '.join(f'{t}={v:.0f}' for t,v in traits[:3])
    print(f\"{a['name']:25s} [{a['category']:20s}] {top}  (epistasis: {a['active_epistasis']})\")
print(f\"\n{lib['count']} agents across {len(lib['categories'])} categories\")
"
```

### "card" or "json <slug>"
Get a machine-readable JSON card for a genome.

```bash
python3 agent_report.py library/genomes/<slug>.dna.json --json
```

### "self" or "self-report <slug>"
Get a structured self-knowledge document (for an agent's own context window).

```bash
python3 agent_report.py library/genomes/<slug>.dna.json --self
```

## Key Concepts

- **27 cognitive primitives**: Low-level genes (not "creative" but novelty_seeking + pattern_completion + ambiguity_response + abstraction_preference)
- **Diploid**: Two alleles per gene. You carry traits you don't express (recessive alleles)
- **8 emergent traits**: creativity, warmth, precision, wit, depth, boldness, adaptability, intensity - these emerge from gene clusters, not stored directly
- **Epistasis**: When two genes both cross thresholds, they modify a third gene. 12 rules create non-linear interactions
- **Compatibility**: Simulates 12 breedings to predict offspring trait ranges, recessive surfacing risks, and genetic distance

## File Locations

- Library index: `library/genome_library.json`
- Individual genomes: `library/genomes/<slug>.dna.json`
- Encoder: `encoder.py`
- Visualizer: `visualize.py`
- Reports: `agent_report.py`

## Notes

- Encoding requires one Claude API call (~3 minutes). Use `--mock` flag for instant keyword-based encoding (no API).
- All comparison, visualization, and breeding operations are pure local computation - no API calls.
- The library contains 216 genomes encoded from the OpenClaw community agent repository.
