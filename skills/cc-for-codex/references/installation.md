# Installation and first run

This skill is intentionally portable: it is a `SKILL.md` plus references,
not a second copy of the bridge runtime. Install the maintained implementation
from the standalone repository, then copy or symlink this skill into the
Codex skill directory if it is not already discoverable.

## Install the bridge

Requirements are Node.js 20+, a local Claude Code CLI, and a Claude login or
provider configuration. Clone the source into a user-selected directory:

```sh
git clone https://github.com/sanchitmonga22/cc-for-codex.git
cd cc-for-codex/plugins/cc-for-codex
npm run check
```

The check is local and uses a fake Claude executable; it does not make a
model request. Run the bridge's doctor command from the checkout:

```sh
./scripts/cc-for-codex doctor --json
```

For a live smoke test, ask the user to approve the request and its billing.
Use the bridge's `ask` or `review` command rather than a hand-written raw
`claude` invocation.

## Copy this skill into Codex

Copy the `skills/cc-for-codex` directory into the user's Codex skills folder
(commonly `~/.codex/skills/cc-for-codex`) or install it through the Codex
skill/plugin mechanism used by the host. From a checkout of this repository,
the direct copy is:

```sh
mkdir -p ~/.codex/skills
cp -R skills/cc-for-codex ~/.codex/skills/cc-for-codex
```

Do not overwrite an existing skill without checking its provenance first.

After installation, start a new Codex task and ask explicitly:

```text
Use $cc-for-codex to ask Claude Code for a read-only second opinion on my current changes.
```

If the full plugin package is installed, prefer its specialized
`$claude-review`, `$claude-delegate`, `$claude-sessions`, `$claude-setup`, and
`$claude-verify` skills; this portable skill remains the single-file entry
point for hosts that only load Agent Skills.
