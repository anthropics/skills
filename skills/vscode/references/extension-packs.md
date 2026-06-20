# Recommended Extension Packs

Curated extension lists for common workflows. The skill's `extensions recommend --stack <name>` command prints the matching IDs and (with `--Install`) installs them via the product CLI.

Each ID here is the canonical publisher.extension form expected by `code --install-extension` and Open VSX. The skill does not maintain or vet these extensions; recommendations are subject to change with marketplace churn. Always verify on <https://marketplace.visualstudio.com/> before committing to a stack.

## Stacks

### `frontend-web` — Modern frontend (HTML / CSS / JS / TS / React / Vue)

| ID | Purpose |
|---|---|
| `dbaeumer.vscode-eslint` | ESLint integration |
| `esbenp.prettier-vscode` | Prettier formatter |
| `EditorConfig.EditorConfig` | .editorconfig support |
| `christian-kohler.path-intellisense` | Path autocomplete |
| `formulahendry.auto-rename-tag` | Auto-rename HTML/XML tags |
| `dsznajder.es7-react-js-snippets` | React snippets |
| `styled-components.vscode-styled-components` | styled-components IntelliSense |
| `bradlc.vscode-tailwindcss` | Tailwind CSS IntelliSense |
| `ms-playwright.playwright` | Playwright test runner |

### `backend-python` — Python services

| ID | Purpose |
|---|---|
| `ms-python.python` | Python language support |
| `ms-python.vscode-pylance` | Pylance language server |
| `ms-python.debugpy` | Python debugger |
| `ms-python.black-formatter` | Black formatter |
| `njpwerner.autodocstring` | Auto-generate docstrings |
| `ms-toolsai.jupyter` | Jupyter notebook support |
| `tamasfe.even-better-toml` | TOML support for pyproject.toml |

### `backend-node` — Node.js services

| ID | Purpose |
|---|---|
| `dbaeumer.vscode-eslint` | ESLint |
| `esbenp.prettier-vscode` | Prettier |
| `ms-vscode.vscode-typescript-next` | TypeScript nightly |
| `pranaygp.vscode-css-peek` | CSS class peek |
| `humao.rest-client` | REST API testing |

### `data-science` — Jupyter / data analysis

| ID | Purpose |
|---|---|
| `ms-toolsai.jupyter` | Jupyter notebook |
| `ms-toolsai.vscode-jupyter-powertoys` | Jupyter PowerToys |
| `ms-python.vscode-pylance` | Pylance |
| `mechatroner.rainbow-csv` | Rainbow CSV |
| `randomfractalsinc.vscode-rainbow-brackets` | Rainbow brackets |
| `ms-vsliveshare.vsliveshare` | Live Share collaboration |

### `systems` — Go / Rust / C++

| ID | Purpose |
|---|---|
| `golang.go` | Go language support |
| `rust-lang.rust-analyzer` | Rust language server |
| `ms-vscode.cpptools` | C/C++ extension |
| `ms-azuretools.vscode-docker` | Docker |
| `hashicorp.terraform` | Terraform |

### `devops` — Docker / Kubernetes / CI

| ID | Purpose |
|---|---|
| `ms-azuretools.vscode-docker` | Docker |
| `ms-kubernetes-tools.vscode-kubernetes-tools` | Kubernetes |
| `redhat.vscode-yaml` | YAML with schema validation |
| `hashicorp.terraform` | Terraform |
| `github.vscode-pull-request-github` | GitHub PRs |

### `polyglot-baseline` — Universal starting pack

For users who do not know where to start:

| ID | Purpose |
|---|---|
| `EditorConfig.EditorConfig` | .editorconfig |
| `dbaeumer.vscode-eslint` | ESLint (also helps non-JS) |
| `esbenp.prettier-vscode` | Prettier |
| `eamodio.gitlens` | GitLens |
| `usernamehw.errorlens` | Inline error highlighting |
| `wayou.vscode-todo-highlight` | TODO/FIXME highlighting |
| `oderwat.indent-rainbow` | Indent colors |
| `PKief.material-icon-theme` | File icons |
| `catppuccin.catppuccin-vsc` | Theme (alt: `dracula-theme.theme-dracula`) |

### `ai-coding` — AI / LLM-assisted workflows

| ID | Purpose |
|---|---|
| `Continue.continue` | Open-source AI assistant |
| `RooVeterinaryInc.roo-cline` | AI agent inside VS Code |
| `saoudrizwan.claude-dev` | Claude Code integration |
| `github.copilot` | GitHub Copilot (paid) |
| `github.copilot-chat` | GitHub Copilot Chat (paid) |

> Some AI extensions require their own API keys, OAuth, or paid subscriptions. The skill does not read or store these credentials.

## Usage

### List a stack without installing

```bash
python scripts/vscode_skill.py extensions recommend --Stack frontend-web
```

Output: a JSON array of `{id, purpose}` entries.

### Install a stack

```bash
python scripts/vscode_skill.py extensions install --Stack backend-python
```

This calls `code --install-extension <id>` for each entry, in order. Failures are reported but do not stop the loop. Use `--ForceOpenVsx` to fall back to Open VSX when the official gallery fails.

### Pin in a project

To recommend a stack in `.vscode/extensions.json` (so VS Code prompts the user to install them):

```bash
python scripts/vscode_skill.py extensions pin --Stack frontend-web --ProjectPath /path/to/project
```

The resulting `extensions.json`:

```json
{
  "recommendations": [
    "dbaeumer.vscode-eslint",
    "esbenp.prettier-vscode",
    "..."
  ]
}
```

## Adding Your Own

Edit this file to add a new stack section. Each stack must have a unique lowercase-hyphenated name. Use the `recommendations` table format consistently so future parsers can extract IDs reliably.