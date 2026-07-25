#!/usr/bin/env bash
# release-discipline-toolkit vendoring helper. v0.3.2: --version <V>; vendors
# both validators + workflows and refreshes the vendored sync-toolkit.sh itself
# (self-replacement). Cross-repo agnostic. POSIX bash.

set -euo pipefail

usage() {
  cat <<'EOF'
Usage: sync-toolkit.sh --version <V>

Vendors the release-discipline-toolkit scripts + reference workflows
into the current repository under tools/release-discipline/.

Arguments:
  --version <V>   Target toolkit tag (e.g., 0.2.4). REQUIRED.

Auth (in order of preference):
  1. `gh auth status` succeeds (uses gh CLI auth)
  2. $TOOLKIT_TOKEN environment variable set (PAT)
  Otherwise: fails with friendly message.
EOF
}

# --- parse args ---
VERSION=""
while [ $# -gt 0 ]; do
  case "$1" in
    --version)
      VERSION="$2"
      shift 2
      ;;
    -h|--help)
      usage; exit 0
      ;;
    *)
      echo "error: unknown argument: $1" >&2
      usage >&2
      exit 1
      ;;
  esac
done

if [ -z "$VERSION" ]; then
  echo "error: --version is required" >&2
  usage >&2
  exit 1
fi

# --- acquire upstream into $RDT_TMP ---
# Deliberately NOT named TMPDIR: that env var is commonly exported (always on
# macOS), so assigning it here would leak the clone dir as the temp dir of
# every child process (gh, git, mktemp).
RDT_TMP=$(mktemp -d -t rdt-sync.XXXXXX)
_ASKPASS=""
trap 'rm -rf "$RDT_TMP" "$_ASKPASS"' EXIT

if [ -n "${TOOLKIT_LOCAL_SRC:-}" ]; then
  # TEST-ONLY seam: use a local directory as the "upstream" instead of cloning.
  # No network, no auth, no git tag — a synthetic fixture dir is not a git repo.
  # --version is used only to write .toolkit-version + README on this path.
  # KNOWN GAP: this path deliberately skips the `git rev-parse v${VERSION}` tag
  # check below. If tag-existence semantics ever move out of the else branch,
  # this seam would bypass them — keep tag logic inside the else branch.
  cp -R "${TOOLKIT_LOCAL_SRC}/." "$RDT_TMP/"
else
  # --- preflight auth (probe gh once, reuse result for clone routing) ---
  if gh auth status >/dev/null 2>&1; then
    gh_authed=1
  else
    gh_authed=0
    if [ -z "${TOOLKIT_TOKEN:-}" ]; then
      echo "error: not authenticated. Run 'gh auth login' or export TOOLKIT_TOKEN=<PAT>" >&2
      exit 1
    fi
  fi

  # --- clone toolkit ---
  if [ "$gh_authed" = "1" ]; then
    gh repo clone Imbad0202/release-discipline-toolkit "$RDT_TMP" -- --quiet
  else
    # Token-auth fallback keeps the PAT out of the clone URL: a URL-embedded
    # token sits in argv (visible to every local user via `ps` while the
    # clone runs) and in the temp clone's .git/config. GIT_ASKPASS hands git
    # the password from the environment instead; the askpass helper contains
    # no secret (it reads $TOOLKIT_TOKEN at call time).
    _ASKPASS=$(mktemp -t rdt-askpass.XXXXXX)
    printf '#!/bin/sh\nprintf %%s "${TOOLKIT_TOKEN}"\n' > "$_ASKPASS"
    chmod 700 "$_ASKPASS"
    GIT_ASKPASS="$_ASKPASS" GIT_TERMINAL_PROMPT=0 git clone --quiet \
      "https://oauth2@github.com/Imbad0202/release-discipline-toolkit.git" "$RDT_TMP"
    rm -f "$_ASKPASS"
  fi

  if ! git -C "$RDT_TMP" rev-parse "v${VERSION}" >/dev/null 2>&1; then
    echo "error: toolkit tag v${VERSION} does not exist upstream" >&2
    exit 1
  fi
  git -C "$RDT_TMP" checkout --quiet "v${VERSION}"
fi

# --- copy files ---
DEST_SCRIPTS="tools/release-discipline/scripts"
DEST_WORKFLOWS=".github/workflows"
mkdir -p "$DEST_SCRIPTS" "$DEST_WORKFLOWS"

cp "$RDT_TMP/scripts/check_release_doc_alignment.py" "$DEST_SCRIPTS/"
cp "$RDT_TMP/scripts/check_command_invariants.py" "$DEST_SCRIPTS/"
cp "$RDT_TMP/scripts/_release_doc_alignment_schema.py" "$DEST_SCRIPTS/"

cp "$RDT_TMP/templates/release-discipline.yml" "$DEST_WORKFLOWS/"
cp "$RDT_TMP/templates/release-discipline-tag-only.yml" "$DEST_WORKFLOWS/"

# --- mutate pin + regenerate README ---
echo "$VERSION" > "tools/release-discipline/.toolkit-version"
TODAY=$(date +%Y-%m-%d)
cat > "tools/release-discipline/README.md" <<EOF
vendored from release-discipline-toolkit@v${VERSION} on ${TODAY}

This directory contains a snapshot of release-discipline-toolkit scripts and
GHA workflows. Do not edit; regenerate by running upstream sync-toolkit.sh.
EOF

# --- self-replace LAST, atomically ---
# Self-copy is the final side-effecting step so that if this script is run
# IN-PLACE from a downstream's vendored copy, bash's read-while-execute can only
# truncate work AFTER everything else (check/schema/workflows/pin/README) is
# already written, so there is no partial sync. The temp-then-mv keeps the
# replacement atomic so the vendored script is never left half-written.
_self_tmp="$DEST_SCRIPTS/.sync-toolkit.sh.new"
cp "$RDT_TMP/scripts/sync-toolkit.sh" "$_self_tmp"
chmod +x "$_self_tmp"
mv -f "$_self_tmp" "$DEST_SCRIPTS/sync-toolkit.sh"

# --- summary ---
echo "Synced release-discipline-toolkit@v${VERSION}. Review changes:"
echo ""
# git status/diff are review conveniences; degrade gracefully if the destination
# is not a git repo (e.g., test harness tmp dir) — never fail the sync over them.
git status 2>/dev/null || echo "(not a git repository — skipping git status)"
echo ""
git diff --stat tools/release-discipline/ \
  .github/workflows/release-discipline.yml \
  .github/workflows/release-discipline-tag-only.yml 2>/dev/null || true
echo ""
echo "Commit BOTH workflow files into .github/workflows/ if you want both available,"
echo "or delete the one you don't need before committing."
