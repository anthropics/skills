#!/usr/bin/env bash
# atlassian-helpers.sh — Shell helper library for atlassian-rovo skill
# Wraps ACLI (Jira) and curl (Confluence REST API v2) with JSON output.
# Source this file, then call the wrapper functions.
#
# Prerequisites:
#   - acli installed and authenticated (brew install acli && acli jira auth login)
#   - ATLASSIAN_EMAIL and ATLASSIAN_API_TOKEN in .env or environment
#   - ATLASSIAN_SITE set (e.g., "mysite.atlassian.net")

set -euo pipefail

# ── Configuration ──────────────────────────────────────────────────────────────

_atlassian_load_env() {
  # Load from .env if vars not already set
  if [[ -z "${ATLASSIAN_EMAIL:-}" || -z "${ATLASSIAN_API_TOKEN:-}" ]]; then
    local env_file="${ATLASSIAN_ENV_FILE:-.env}"
    if [[ -f "$env_file" ]]; then
      # shellcheck disable=SC1090
      source "$env_file"
    fi
  fi

  : "${ATLASSIAN_EMAIL:?ATLASSIAN_EMAIL not set}"
  : "${ATLASSIAN_API_TOKEN:?ATLASSIAN_API_TOKEN not set}"
  : "${ATLASSIAN_SITE:?ATLASSIAN_SITE not set (e.g. mysite.atlassian.net)}"
}

_confluence_api() {
  # Base curl wrapper for Confluence REST API v2
  local method="$1" endpoint="$2"
  shift 2
  curl -sf \
    -X "$method" \
    -u "${ATLASSIAN_EMAIL}:${ATLASSIAN_API_TOKEN}" \
    -H "Content-Type: application/json" \
    "$@" \
    "https://${ATLASSIAN_SITE}/wiki/api/v2${endpoint}"
}

# ── Jira (ACLI) ───────────────────────────────────────────────────────────────

jira_create() {
  # Create a Jira issue. All args are passed through to acli.
  # Usage: jira_create --project AW1 --type Task --summary "..." [--parent AW1-36] [--description "..."]
  acli jira workitem create --json "$@"
}

jira_edit() {
  # Edit a Jira issue.
  # Usage: jira_edit --key AW1-1 --summary "New title" [--assignee user@email.com] [--description "..."]
  acli jira workitem edit --json "$@"
}

jira_view() {
  # View a Jira issue.
  # Usage: jira_view KEY-1 [--fields "summary,status,description"]
  acli jira workitem view --json "$@"
}

jira_search() {
  # Search Jira with JQL.
  # Usage: jira_search --jql "project = AW1 ORDER BY created DESC" [--limit 10]
  acli jira workitem search --json --limit "${JIRA_MAX_RESULTS:-10}" "$@"
}

jira_transition() {
  # Transition a Jira issue to a new status.
  # Usage: jira_transition --key AW1-1 --status "Done"
  acli jira workitem transition --yes --json "$@"
}

jira_comment() {
  # Add a comment to a Jira issue.
  # Usage: jira_comment --key AW1-1 --body "Comment text"
  acli jira workitem comment create --json "$@"
}

jira_link() {
  # Create a link between two Jira issues.
  # Usage: jira_link --out AW1-1 --in AW1-2 --type Blocks
  acli jira workitem link create --yes "$@"
}

# ── Confluence (REST API v2) ──────────────────────────────────────────────────

confluence_create_page() {
  # Create a Confluence page.
  # Usage: confluence_create_page <spaceId> <title> <body> [parentId]
  local space_id="$1" title="$2" body="$3" parent_id="${4:-}"
  _atlassian_load_env

  local payload
  payload=$(python3 -c "
import json, sys
d = {'spaceId': sys.argv[1], 'status': 'current', 'title': sys.argv[2],
     'body': {'representation': 'storage', 'value': sys.argv[3]}}
if sys.argv[4]:
    d['parentId'] = sys.argv[4]
print(json.dumps(d))
" "$space_id" "$title" "$body" "$parent_id")

  _confluence_api POST "/pages" -d "$payload"
}

confluence_get_page() {
  # Get a Confluence page by ID.
  # Usage: confluence_get_page <pageId> [body-format]
  local page_id="$1" body_format="${2:-storage}"
  _atlassian_load_env
  _confluence_api GET "/pages/${page_id}?body-format=${body_format}"
}

confluence_update_page() {
  # Update a Confluence page. Requires current version number.
  # Usage: confluence_update_page <pageId> <title> <body> <version> [versionMessage]
  local page_id="$1" title="$2" body="$3" version="$4" version_msg="${5:-Updated}"
  _atlassian_load_env

  local new_version=$((version + 1))
  local payload
  payload=$(python3 -c "
import json, sys
d = {'id': sys.argv[1], 'status': 'current', 'title': sys.argv[2],
     'body': {'representation': 'storage', 'value': sys.argv[3]},
     'version': {'number': int(sys.argv[4]), 'message': sys.argv[5]}}
print(json.dumps(d))
" "$page_id" "$title" "$body" "$new_version" "$version_msg")

  _confluence_api PUT "/pages/${page_id}" -d "$payload"
}

confluence_add_footer_comment() {
  # Add a footer (page-level) comment to a Confluence page.
  # Usage: confluence_add_footer_comment <pageId> <body_html>
  local page_id="$1" body="$2"
  _atlassian_load_env

  local payload
  payload=$(python3 -c "
import json, sys
print(json.dumps({'pageId': sys.argv[1], 'body': {'representation': 'storage', 'value': sys.argv[2]}}))
" "$page_id" "$body")

  _confluence_api POST "/footer-comments" -d "$payload"
}

confluence_add_inline_comment() {
  # Add an inline comment anchored to specific text on a Confluence page.
  # Usage: confluence_add_inline_comment <pageId> <body_html> <textSelection>
  local page_id="$1" body="$2" selection="$3"
  _atlassian_load_env

  local payload
  payload=$(python3 -c "
import json, sys
print(json.dumps({
  'pageId': sys.argv[1],
  'body': {'representation': 'storage', 'value': sys.argv[2]},
  'inlineCommentProperties': {
    'textSelection': sys.argv[3],
    'textSelectionMatchCount': 1,
    'textSelectionMatchIndex': 0
  }
}))
" "$page_id" "$body" "$selection")

  _confluence_api POST "/inline-comments" -d "$payload"
}

confluence_list_comments() {
  # List footer or inline comments on a Confluence page.
  # Usage: confluence_list_comments <pageId> [footer|inline]
  local page_id="$1" type="${2:-footer}"
  _atlassian_load_env
  _confluence_api GET "/pages/${page_id}/${type}-comments"
}

confluence_get_footer_comment() {
  # Read a specific footer comment by ID.
  # Usage: confluence_get_footer_comment <commentId>
  local comment_id="$1"
  _atlassian_load_env
  _confluence_api GET "/footer-comments/${comment_id}?body-format=storage"
}

confluence_get_inline_comment() {
  # Read a specific inline comment by ID.
  # Usage: confluence_get_inline_comment <commentId>
  local comment_id="$1"
  _atlassian_load_env
  _confluence_api GET "/inline-comments/${comment_id}?body-format=storage"
}

confluence_reply_to_comment() {
  # Reply to an existing comment (footer or inline). Uses v1 API.
  # Usage: confluence_reply_to_comment <pageId> <parentCommentId> <body_html>
  local page_id="$1" parent_id="$2" body="$3"
  _atlassian_load_env

  local payload
  payload=$(python3 -c "
import json, sys
print(json.dumps({
  'type': 'comment',
  'container': {'id': sys.argv[1], 'type': 'page'},
  'ancestors': [{'id': sys.argv[2]}],
  'body': {'storage': {'value': sys.argv[3], 'representation': 'storage'}}
}))
" "$page_id" "$parent_id" "$body")

  curl -sf \
    -X POST \
    -u "${ATLASSIAN_EMAIL}:${ATLASSIAN_API_TOKEN}" \
    -H "Content-Type: application/json" \
    -d "$payload" \
    "https://${ATLASSIAN_SITE}/wiki/rest/api/content"
}

confluence_list_spaces() {
  # List available Confluence spaces.
  # Usage: confluence_list_spaces [limit]
  local limit="${1:-10}"
  _atlassian_load_env
  _confluence_api GET "/spaces?limit=${limit}"
}

confluence_search() {
  # Search Confluence with CQL. Uses v1 API (v2 search doesn't support CQL for pages).
  # Usage: confluence_search <cql> [limit]
  local cql="$1" limit="${2:-10}"
  _atlassian_load_env

  local encoded_cql
  encoded_cql=$(python3 -c "import urllib.parse,sys; print(urllib.parse.quote(sys.argv[1]))" "$cql")
  curl -sf \
    -u "${ATLASSIAN_EMAIL}:${ATLASSIAN_API_TOKEN}" \
    "https://${ATLASSIAN_SITE}/wiki/rest/api/content/search?cql=${encoded_cql}&limit=${limit}"
}
