# Fix Playbook by Category

| Category | Fix | Never |
|---|---|---|
| `SECRETS` | Delete hardcoded key → `.env`/secret manager → confirm `.gitignore` → **rotate the credential** (check `inGitHistory` field — if `true`, rotation is non-negotiable even after deletion, git history still has it) | Comment out; defer rotation |
| `DEPS` | `npm install pkg@latest` or exact `.fix` field | Pin inside CVE range to pass check |
| `SAST` | Read rule message, fix root cause (injection, floating promise, unsafe `any`) | Blind `// nosemgrep` suppress |
| `AI_CODE` | 100+ AST rules for AI-agent-written flaws: silent catches, React state mutation, framework-specific bugs (Next/Express/Django/Go/Python). Treat as high-signal — these are exactly the bug class agents (including you) tend to introduce | Assume false positive by default |
| `DUPLICATION` | Extract to shared function/module, cite both locations from finding | Ignore — duplication compounds into divergent-bugfix risk over time |
| `DEP_HEALTH` | Remove unused packages from package.json | Leave "just in case" |
| `LICENSE` | Flag GPL/AGPL deps to user before replacing — may be a legal call, not a code call | Silently swap without confirming with user if package is load-bearing |
| `TYPE_SAFETY` | Fix `tsc` errors at root — add real types | Blanket `// @ts-ignore` |
| `GIT_HEALTH` | File flagged 50+ modifications = architectural churn signal → mention to user as refactor candidate, don't fix unprompted | Treat as a blocking finding — it's a signal, not a bug |
| `IaC` | Dockerfile/k8s/Terraform misconfig — fix per Trivy config message | Ignore because "it's infra not app code" |
