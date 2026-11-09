---
name: oss-ready
description: Audits a code repository for open-source readiness and generates the missing community files (README sections, LICENSE, CONTRIBUTING.md, CODE_OF_CONDUCT.md, SECURITY.md, issue and pull request templates, CI, .gitignore), tailored to the project's real language, build and test commands. Use when the user wants to open-source a project, make a repo contributor-friendly, prepare for Hacktoberfest or first-time contributors, add community health files, or asks "is my repo ready to be public?"
license: Apache-2.0. Complete terms in LICENSE.txt
---

# OSS Ready

Make a repository ready for outside contributors. Find out what is missing, then
generate only what is missing, using facts from the repo itself rather than
generic boilerplate.

## Workflow

### 1. Audit

Run the audit script against the repo root. It uses only the Python standard
library and never modifies files.

```bash
python scripts/audit.py <repo-path>                 # Markdown report
python scripts/audit.py <repo-path> --format json   # machine-readable
```

Run `python scripts/audit.py --help` first if unsure of options. Treat the
script as a black box: read its output, not its source.

The report contains:
- a readiness score (0-100) and grade
- every check with pass / partial / missing status
- the detected stack (languages, package manager) and the real commands for
  install, build, test, lint and format, taken from manifest files
- the repo name and remote URL if found in `.git/config`

### 2. Report and agree on scope

Show the user the score and the list of missing or partial items, grouped as
**Essential**, **Community** and **Tooling**. Then ask which items to
generate. Default suggestion: all missing Essential and Community items.

Never overwrite an existing file. If a file exists but is weak (partial
status), propose specific additions and apply them only with approval.

### 3. Ask for facts you must not invent

Some content is the maintainer's decision or private information. Ask, and
leave a clearly marked `TODO` placeholder if the user does not answer:

| Needed for | Ask for |
|---|---|
| LICENSE | Which license. **Never choose one for the user.** See [references/licenses.md](references/licenses.md) for a neutral summary to help them decide. |
| SECURITY.md | Private contact for vulnerability reports (email or "use GitHub private vulnerability reporting"), and which versions are supported |
| CODE_OF_CONDUCT.md | Enforcement contact |
| Templates | Anything project-specific the user wants contributors to include |

Never invent email addresses, maintainer names, URLs, response times or
version numbers.

### 4. Generate

Use the templates in `assets/` as the starting point. Replace every
`{{PLACEHOLDER}}` with facts from the audit or from the user. See
[references/checklist.md](references/checklist.md) for what a good version of
each file contains.

| File | Template | Location |
|---|---|---|
| CONTRIBUTING.md | `assets/CONTRIBUTING.md` | repo root |
| CODE_OF_CONDUCT.md | `assets/CODE_OF_CONDUCT.md` | repo root |
| SECURITY.md | `assets/SECURITY.md` | repo root or `.github/` |
| Bug report form | `assets/ISSUE_TEMPLATE/bug_report.yml` | `.github/ISSUE_TEMPLATE/` |
| Feature request form | `assets/ISSUE_TEMPLATE/feature_request.yml` | `.github/ISSUE_TEMPLATE/` |
| Issue chooser config | `assets/ISSUE_TEMPLATE/config.yml` | `.github/ISSUE_TEMPLATE/` |
| PR template | `assets/PULL_REQUEST_TEMPLATE.md` | `.github/` |
| CI workflow | `assets/ci/<stack>.yml` | `.github/workflows/ci.yml` |

Rules while generating:
- **Commands must be real.** Only write a build, test or lint command into
  CONTRIBUTING.md or CI if the audit detected it or you verified it in the
  manifest. If the project has no tests, say so honestly in CONTRIBUTING.md
  instead of inventing a test command.
- **Match the project.** Use the existing package manager (the audit reports
  it from the lockfile), the existing default branch name, and the tone of the
  existing README.
- **Remove what does not apply.** Delete template sections that make no sense
  for this project rather than leaving them empty.
- **README:** do not rewrite an existing README. If sections are missing
  (install, usage, contributing, license), propose short additions and insert
  them only with approval. Create a README from scratch only if none exists.
- **LICENSE:** write the full, unmodified official license text with the
  correct year and copyright holder. Do not paraphrase a license.
- **CI:** for stacks without a template in `assets/ci/`, write a minimal
  workflow that runs only the detected commands.

### 5. Suggest labels (optional)

Recommend these GitHub labels so newcomers can find work:
`good first issue`, `help wanted`, `bug`, `enhancement`, `documentation`.
If the GitHub CLI is available, offer the commands, for example:

```bash
gh label create "good first issue" --color 7057ff --description "Good for newcomers"
```

Creating labels changes a remote repository, so run these only after the user
says yes.

### 6. Re-audit

Run the audit again and show the before and after score, plus any remaining
`TODO` placeholders the user still needs to fill in:

```bash
grep -rn "TODO(oss-ready)" <repo-path> --include=*.md --include=*.yml
```

## Edge cases

- **Monorepo:** the audit reports every manifest it finds within two directory
  levels. Ask which package is the public one, or write commands per package.
- **No git repository:** the audit still works; repo name falls back to the
  folder name and the remote URL is reported as unknown.
- **Not on GitHub (GitLab, Codeberg, etc.):** community files still apply.
  Issue and PR templates go in that platform's folder (for GitLab,
  `.gitlab/issue_templates/` and `.gitlab/merge_request_templates/`, as
  Markdown rather than YAML forms). Skip GitHub-only CI and labels.
- **Private or internal code:** if the repo looks like it contains secrets
  (the audit flags `.env` files and common key filenames that are not
  gitignored), warn the user before anything else. Making a repo public is
  their decision; point out what to remove first.
