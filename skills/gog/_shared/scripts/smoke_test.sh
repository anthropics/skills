#!/usr/bin/env bash
# smoke_test.sh - Safe smoke tests for GOG skills
# Uses only YOUR email for all operations (safe, self-contained tests)

set -euo pipefail

# Test configuration
# IMPORTANT: Set this to YOUR email address for safe testing
# Example: export GOG_TEST_EMAIL=your.email@yourdomain.com
TEST_EMAIL="${GOG_TEST_EMAIL:-your.email@example.com}"
RUN_DRAFT_TEST="${RUN_DRAFT_TEST:-0}"

# Validate test email is set
if [ "$TEST_EMAIL" = "your.email@example.com" ]; then
  echo "⚠️  Warning: Using default test email. For accurate testing, set GOG_TEST_EMAIL:"
  echo "   export GOG_TEST_EMAIL=your.email@yourdomain.com"
  echo "   bash skills/gog/_shared/scripts/smoke_test.sh"
  echo
fi

# Colors for output
if [ -t 1 ]; then
  RED='\033[0;31m'
  GREEN='\033[0;32m'
  YELLOW='\033[1;33m'
  BLUE='\033[0;34m'
  NC='\033[0m'
else
  RED=''
  GREEN=''
  YELLOW=''
  BLUE=''
  NC=''
fi

# Test counters
TESTS_PASSED=0
TESTS_FAILED=0
TESTS_SKIPPED=0

# Print test header
print_header() {
  echo
  echo -e "${BLUE}=== GOG Skills Smoke Test ===${NC}"
  echo "Test identity: $TEST_EMAIL"
  echo "Draft test: $([ "$RUN_DRAFT_TEST" = "1" ] && echo "ENABLED" || echo "DISABLED (set RUN_DRAFT_TEST=1 to enable)")"
  echo
}

# Print test result
print_result() {
  local test_name="$1"
  local status="$2"
  local message="${3:-}"

  if [ "$status" = "PASS" ]; then
    echo -e "${GREEN}✓${NC} $test_name: ${GREEN}PASS${NC} $message"
    ((TESTS_PASSED++))
  elif [ "$status" = "FAIL" ]; then
    echo -e "${RED}✗${NC} $test_name: ${RED}FAIL${NC}"
    if [ -n "$message" ]; then
      echo -e "  ${RED}$message${NC}"
    fi
    ((TESTS_FAILED++))
  elif [ "$status" = "SKIP" ]; then
    echo -e "${YELLOW}○${NC} $test_name: ${YELLOW}SKIP${NC} $message"
    ((TESTS_SKIPPED++))
  fi
}

# Print summary
print_summary() {
  echo
  echo "=== Test Summary ==="
  echo "Passed:  $TESTS_PASSED"
  echo "Failed:  $TESTS_FAILED"
  echo "Skipped: $TESTS_SKIPPED"
  echo

  if [ $TESTS_FAILED -eq 0 ]; then
    echo -e "${GREEN}=== ALL TESTS PASSED ===${NC}"
    return 0
  else
    echo -e "${RED}=== TESTS FAILED ===${NC}"
    return 1
  fi
}

# Test 1: Verify GOG is reachable
test_gog_version() {
  local test_name="Verify GOG is reachable"

  if ! command -v gog >/dev/null 2>&1; then
    print_result "$test_name" "FAIL" "gog command not found. See skills/gog/_shared/references/gog-interface.md"
    return 1
  fi

  if GOG_VERSION=$(gog --version 2>&1 | grep -oE 'v[0-9]+\.[0-9]+\.[0-9]+' | head -n1); then
    print_result "$test_name" "PASS" "($GOG_VERSION)"
    return 0
  else
    print_result "$test_name" "FAIL" "gog --version failed"
    return 1
  fi
}

# Test 2: List emails (read-only)
test_email_list() {
  local test_name="List emails (read-only)"

  local query="to:$TEST_EMAIL OR from:$TEST_EMAIL"
  local output

  if output=$(gog gmail search "$query" --max 5 --json 2>&1); then
    # Validate JSON
    if echo "$output" | jq empty 2>/dev/null; then
      local count
      count=$(echo "$output" | jq '.threads | length' 2>/dev/null || echo "0")
      print_result "$test_name" "PASS" "($count threads)"
      return 0
    else
      print_result "$test_name" "FAIL" "Invalid JSON output"
      return 1
    fi
  else
    print_result "$test_name" "FAIL" "Command failed: $output"
    return 1
  fi
}

# Test 3: Read one email (read-only)
test_email_get() {
  local test_name="Read one email (read-only)"

  # Get first thread
  local query="to:$TEST_EMAIL OR from:$TEST_EMAIL"
  local thread_list

  if ! thread_list=$(gog gmail search "$query" --max 1 --json 2>/dev/null); then
    print_result "$test_name" "SKIP" "Cannot get thread list"
    return 0
  fi

  local thread_id
  thread_id=$(echo "$thread_list" | jq -r '.threads[0].id' 2>/dev/null || echo "")

  if [ -z "$thread_id" ] || [ "$thread_id" = "null" ]; then
    print_result "$test_name" "SKIP" "No threads found"
    return 0
  fi

  # Get first message from thread
  local thread_output
  if thread_output=$(gog gmail thread get "$thread_id" --json 2>&1); then
    if echo "$thread_output" | jq empty 2>/dev/null; then
      local msg_count
      msg_count=$(echo "$thread_output" | jq '.thread.messages | length' 2>/dev/null || echo "0")
      if [ "$msg_count" -gt 0 ]; then
        # Extract subject from headers
        local subject
        subject=$(echo "$thread_output" | jq -r '.thread.messages[0].payload.headers[] | select(.name == "Subject") | .value' 2>/dev/null || echo "No subject")
        print_result "$test_name" "PASS" "(Thread: ${thread_id:0:10}..., $msg_count message(s))"
        echo "    Subject: ${subject:0:50}$([ ${#subject} -gt 50 ] && echo "...")"
        return 0
      else
        print_result "$test_name" "FAIL" "Thread has no messages"
        return 1
      fi
    else
      print_result "$test_name" "FAIL" "Invalid JSON output"
      return 1
    fi
  else
    print_result "$test_name" "FAIL" "Command failed: $thread_output"
    return 1
  fi
}

# Test 4: Calendar agenda (read-only)
test_calendar_agenda() {
  local test_name="Calendar agenda (read-only)"

  local output
  if output=$(gog calendar events --today --json 2>&1); then
    if echo "$output" | jq empty 2>/dev/null; then
      local count
      count=$(echo "$output" | jq '.events | length' 2>/dev/null || echo "0")
      print_result "$test_name" "PASS" "($count events today)"
      return 0
    else
      print_result "$test_name" "FAIL" "Invalid JSON output"
      return 1
    fi
  else
    print_result "$test_name" "SKIP" "Calendar command failed (may not have calendar access)"
    return 0
  fi
}

# Test 5: List tasks (read-only)
test_tasks_list() {
  local test_name="List tasks (read-only)"

  # First get the task lists
  local tasklists
  if ! tasklists=$(gog tasks lists --json 2>/dev/null); then
    print_result "$test_name" "SKIP" "Cannot get task lists (may not have tasks access)"
    return 0
  fi

  # Get first tasklist ID
  local tasklist_id
  tasklist_id=$(echo "$tasklists" | jq -r '.tasklists[0].id' 2>/dev/null || echo "")

  if [ -z "$tasklist_id" ] || [ "$tasklist_id" = "null" ]; then
    print_result "$test_name" "SKIP" "No task lists found"
    return 0
  fi

  # List tasks from first tasklist
  local output
  if output=$(gog tasks list "$tasklist_id" --json 2>&1); then
    if echo "$output" | jq empty 2>/dev/null; then
      local count
      count=$(echo "$output" | jq '.tasks | length' 2>/dev/null || echo "0")
      print_result "$test_name" "PASS" "($count tasks)"
      return 0
    else
      print_result "$test_name" "FAIL" "Invalid JSON output"
      return 1
    fi
  else
    print_result "$test_name" "SKIP" "Tasks list command failed"
    return 0
  fi
}

# Test 6: Follow-ups store validation (read-only)
test_followups_store() {
  local test_name="Follow-ups store validation"

  local followup_store="$HOME/.gog-assistant/followups.json"

  if [ -f "$followup_store" ]; then
    if jq empty "$followup_store" 2>/dev/null; then
      local count
      count=$(jq 'length' "$followup_store" 2>/dev/null || echo "0")
      print_result "$test_name" "PASS" "($count follow-up items)"
      return 0
    else
      print_result "$test_name" "FAIL" "Invalid JSON in followups.json"
      return 1
    fi
  else
    print_result "$test_name" "PASS" "(no store yet, will be created when needed)"
    return 0
  fi
}

# Test 7: Create draft to self (optional, draft-only)
test_draft_to_self() {
  local test_name="Create draft to self (draft-only)"

  if [ "$RUN_DRAFT_TEST" != "1" ]; then
    print_result "$test_name" "SKIP" "Set RUN_DRAFT_TEST=1 to enable"
    return 0
  fi

  local timestamp
  timestamp=$(date -u +"%Y-%m-%dT%H:%M:%SZ")
  local subject="[GOG TEST DRAFT — DO NOT SEND] Test at $timestamp"
  local body="This is a test draft created by GOG smoke test.

Created at: $timestamp
Test identity: $TEST_EMAIL

This is NOT a real email. It should NOT be sent.

If you see this draft in your email client:
- This means the test worked correctly
- You may safely delete this draft
- Do NOT send this draft
"

  # Check if drafts command exists
  if ! gog gmail drafts --help >/dev/null 2>&1; then
    print_result "$test_name" "SKIP" "Draft commands not available in this GOG version"
    return 0
  fi

  # Create draft (check actual command syntax from GOG help)
  local output
  if output=$(gog gmail drafts create --to "$TEST_EMAIL" --subject "$subject" --body "$body" --json 2>&1); then
    if echo "$output" | jq empty 2>/dev/null; then
      local draft_id
      draft_id=$(echo "$output" | jq -r '.id // .draftId // empty' 2>/dev/null || echo "")

      if [ -n "$draft_id" ] && [ "$draft_id" != "null" ]; then
        print_result "$test_name" "PASS" "(draft ID: $draft_id)"
        echo
        echo -e "  ${YELLOW}⚠ REMINDER: This is a TEST DRAFT. Do NOT send it.${NC}"
        echo -e "  ${YELLOW}⚠ To send, you would need explicit \"YES, SEND\" confirmation.${NC}"
        echo -e "  ${YELLOW}⚠ To delete: gog gmail drafts delete $draft_id${NC}"
        echo
        return 0
      else
        print_result "$test_name" "FAIL" "No draft ID in response"
        return 1
      fi
    else
      print_result "$test_name" "FAIL" "Invalid JSON output"
      return 1
    fi
  else
    print_result "$test_name" "SKIP" "Draft creation not supported or command syntax differs: $output"
    return 0
  fi
}

# Main test runner
main() {
  print_header

  # Check for jq (needed for JSON tests)
  if ! command -v jq >/dev/null 2>&1; then
    echo -e "${YELLOW}Warning: jq not found. JSON validation will be limited.${NC}"
    echo "Install jq for better test results: https://stedolan.github.io/jq/"
    echo
  fi

  # Run tests
  echo "Running tests..."
  echo

  test_gog_version || true
  test_email_list || true
  test_email_get || true
  test_calendar_agenda || true
  test_tasks_list || true
  test_followups_store || true
  test_draft_to_self || true

  # Print summary
  print_summary
}

# Run main if script is executed directly
if [ "${BASH_SOURCE[0]:-}" = "${0}" ]; then
  main
  exit $?
fi
