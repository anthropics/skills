# Tamper-Evident Proof via Git Notes

## The Problem with Markdown-Only Evidence

A DECISIONS.md file in a git repo can be backdated, edited, or fabricated. Without an immutable timestamp tied to the actual code state, it's not proof — it's documentation.

## Git Notes: Metadata Without File Tree Pollution

Git notes (`git notes`) attach arbitrary text to any git object (commit, blob, tree) without modifying the object itself. Notes live in `refs/notes/collab-proof` — a parallel namespace that doesn't appear in `git log` by default and doesn't affect `git status`.

```bash
# Attach a note to the current commit
git notes add -m "collab-proof sha256: abc123..." HEAD

# View notes on a commit
git notes show HEAD
git log --show-notes

# Share notes with collaborators
git push origin refs/notes/collab-proof

# Fetch collaborators' notes
git fetch origin refs/notes/collab-proof:refs/notes/collab-proof
```

Source: [Git Notes documentation](https://git-scm.com/docs/git-notes), [Pro Git: Git Notes](https://git-scm.com/book/en/v2/Git-Internals-The-Refspec)

## Why SHA-256 of the HTML File

The HTML proof file contains the full session narrative, decision records, and AI contribution analysis. Hashing it and attaching the hash to a specific commit creates a verifiable chain:

```
commit abc1234  (code state at session end)
  └── git note: collab-proof sha256: f7a3...
                file: 2026-06-01-1422-proof.html

→ Anyone with the HTML file can verify:
  python3 -c "import hashlib; print(hashlib.sha256(open('proof.html','rb').read()).hexdigest())"
  # must match the hash in the git note
```

This is structurally similar to software release signing (GPG-signed tags) but using stdlib Python and git's built-in notes system.

Source: [Git tag signing](https://git-scm.com/book/en/v2/Git-Tools-Signing-Your-Work), NIST SP 800-107 Rev 1 (SHA-256 collision resistance)

## Collaboration Safety

Git notes don't cause merge conflicts the way file edits do. Multiple contributors can append notes to the same commit independently:

```bash
# Both developers can run this without conflict:
git notes append -m "reviewer: approved" HEAD
```

The `append` subcommand concatenates to existing notes; `add` replaces them. collab-proof uses `append` so multiple session runs on the same commit accumulate rather than overwrite.

Source: [git-notes man page](https://git-scm.com/docs/git-notes#_commands)

## Limitations

- Notes are not included in a standard `git clone` — collaborators must explicitly `git fetch origin refs/notes/collab-proof`
- Notes can still be deleted with `git notes remove` — they are tamper-evident, not tamper-proof
- The proof is only as strong as the git history itself (rebasing changes commit hashes)

Source: [Stack Overflow: Are git notes included in clone?](https://stackoverflow.com/questions/13935467/are-git-notes-included-in-a-git-clone)

## Why Not GPG Signing?

GPG signing would require key management infrastructure. git notes + SHA-256 achieves the core goal (linking an artifact to a specific code state at a specific time) with zero additional tooling. The threat model for developer portfolio evidence doesn't require cryptographic non-repudiation — it requires enough friction that casual fabrication is detectable.

Source: Schneier, B. (2003). *Beyond Fear*. Copernicus Books. (threat modeling: cost of attack vs. cost of defense)
