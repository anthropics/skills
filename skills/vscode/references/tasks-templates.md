# VS Code Tasks Templates

Ready-to-use `tasks.json` templates for common workflows. The skill's `tasks init --template <name> --ProjectPath <path>` command copies the matching template into `<project>/.vscode/tasks.json` and never overwrites an existing file unless `--Force` is passed.

For each template, the **Variables** column lists the VS Code task variables you can edit after copying. See the live docs at <https://code.visualstudio.com/docs/editor/variables-reference>.

## Available Templates

| Template ID | Language | Purpose |
|---|---|---|
| `node-npm` | Node.js | Run `npm` scripts defined in package.json. |
| `node-tsc` | TypeScript | Watch and compile TypeScript. |
| `python-pytest` | Python | Run pytest with current file or all tests. |
| `python-flask` | Python | Run Flask development server. |
| `python-django` | Python | Run Django manage.py. |
| `go-build` | Go | Build, test, and run. |
| `rust-cargo` | Rust | Cargo build / run / test. |
| `docker-build` | Docker | Build a Docker image. |
| `docker-compose-up` | Docker | docker-compose up a stack. |
| `make-default` | Make | Run `make` with selectable target. |

## Per-Template Details

### `node-npm`

Runs npm scripts. Lists scripts defined in `package.json` and lets you pick one.

Variables:

* `script` — name of the npm script to run (e.g., `dev`, `build`, `test`).

### `node-tsc`

TypeScript compile in watch mode.

Variables:

* `tsc.path` — path to the TypeScript compiler (default: `${workspaceFolder}/node_modules/.bin/tsc`).
* `tsconfig` — path to tsconfig.json (default: `${workspaceFolder}/tsconfig.json`).

### `python-pytest`

Runs pytest. Detects whether to run the current file or the full test suite based on `${file}`.

Variables:

* `pytest.args` — extra pytest arguments (default: `-v`).

### `python-flask`

Runs `flask run` with debug mode.

Variables:

* `flask.app` — Flask app entry point (default: `app.py`).
* `flask.env` — FLASK_ENV value (default: `development`).

### `python-django`

Runs Django's `manage.py` with `runserver`.

Variables:

* `django.app` — Django app module (default: `app`).

### `go-build`, `go-test`, `go-run`

Build, test, or run Go code.

Variables:

* `go.package` — package path (default: `${workspaceFolder}`).

### `rust-cargo`

Cargo build / run / test.

Variables:

* `cargo.command` — cargo subcommand (`build`, `run`, `test`, `check`).

### `docker-build`

Builds a Docker image from a Dockerfile in the workspace root.

Variables:

* `image.name` — image tag (default: `${workspaceFolderBasename}:latest`).
* `dockerfile` — Dockerfile path (default: `${workspaceFolder}/Dockerfile`).

### `docker-compose-up`

Brings up a docker-compose stack.

Variables:

* `compose.file` — compose file path (default: `${workspaceFolder}/docker-compose.yml`).

### `make-default`

Runs `make` and prompts for a target.

Variables:

* `make.target` — make target (default: empty, will prompt).

## Usage

```powershell
# Windows / PowerShell
pwsh -File scripts/vscode-cli.ps1 tasks init --Template python-pytest --ProjectPath D:\projects\demo --Apply

# Cross-platform
python scripts/vscode_skill.py tasks init --Template python-pytest --ProjectPath /path/to/demo --Apply
```

The command:

1. Resolves the template under `references/templates/tasks/<id>.json`.
2. Substitutes placeholders with their default values.
3. Writes `<project>/.vscode/tasks.json` (creating the directory if missing).
4. Refuses to overwrite an existing file unless `--Force` is passed.

## Adding Your Own

Drop a JSON file at `references/templates/tasks/<your-id>.json` and the `tasks init --list` command will pick it up automatically. Keep the schema compatible with VS Code's `tasks.json` schema (version 2.0.0).