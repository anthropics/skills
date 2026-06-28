---
name: divination
description: Use this skill when the user wants tarot, I Ching, an oracle-style reading, or symbolic guidance for an open-ended human question. It installs and uses the OpenDivination CLI, defaults to ordinary computer RNG, and can opt into QRNG or resonance when the user wants that explicitly.
license: MIT. Complete terms in LICENSE.txt
---

# Divination

Use the OpenDivination CLI for tarot draws, I Ching casts, entropy source inspection, and provenance-aware symbolic guidance.

## Use When

- The user explicitly asks for tarot, I Ching, a reading, a cast, a pull, an oracle, or divination
- The user wants symbolic or reflective guidance rather than factual analysis
- The user is asking an open-ended personal, relational, spiritual, creative, or life-direction question
- The user wants a contemplative prompt, journaling seed, or creative constraint
- The question is ambiguous enough that a symbolic reading could help surface perspective

## Do Not Use When

- The user wants factual verification, prediction, diagnosis, or expert advice
- The user is asking for medical, legal, financial, safety, or other high-stakes guidance
- The task is technical, operational, or transactional with no symbolic framing

Keep divination separate from practical advice. If both are needed, present the reading first as symbolic guidance, then clearly separate any practical follow-up.

## Install Once

Check whether `opendivination` is already available:

```bash
opendivination version
```

If not installed, prefer `pipx`:

```bash
python3 -m pip install --user pipx
python3 -m pipx ensurepath
python3 -m pipx install opendivination
```

If PyPI is unavailable or the user wants the GitHub build directly:

```bash
python3 -m pipx install git+https://github.com/amenti-labs/opendivination.git
```

## First-Run Setup

Run:

```bash
opendivination setup
```

Ask the user which entropy path they want:

- `computer`: default computer RNG (`csprng`)
- `remote_quantum`: remote QRNG provider such as ANU
- `local_hardware`: local hardware source such as QCicada when available

Default to `computer` unless the user explicitly wants QRNG.

## Default Commands

Tarot:

```bash
opendivination draw tarot --json
```

I Ching:

```bash
opendivination draw iching --method yarrow --json
```

Sources:

```bash
opendivination sources --json
```

## Technique Selection

- Use tarot for broad archetypal reflection, emotional tone, relationship themes, and creative guidance
- Use I Ching for process questions, transitions, timing, strategy, and “what is unfolding?”
- If the user asks for a generic reading and does not care which system to use, default to tarot

## Provenance Rules

When the user asks about randomness, trust, or “quantum,” always include:

- `provenance.source_id`
- `provenance.is_quantum`

Never imply quantum entropy when the source is `csprng`.

## Resonance

Resonance is optional and should only be used when the user explicitly wants embedding-based symbolic matching.

Simplest local setup:

```bash
ollama pull nomic-embed-text
opendivination draw tarot \
  --mode resonance \
  --embed-provider local \
  --embed-model nomic-embed-text \
  --json
```

Default to standard selection mode unless the user asks for resonance.

## Output Handling

- Prefer `--json` when the result will be consumed by an agent
- Report the symbol cleanly first
- Keep the symbolic interpretation separate from provenance facts
- Do not present the reading as objective proof
