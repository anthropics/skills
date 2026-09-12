#!/bin/bash
#
# execute-task.sh - Execute spec-flow tasks with full context
#
# Usage:
#   ./execute-task.sh <feature-name>           # Show next pending task
#   ./execute-task.sh <feature-name> <task-id> # Execute specific task
#   ./execute-task.sh <feature-name> --status  # Show progress summary
#
# Examples:
#   ./execute-task.sh user-auth
#   ./execute-task.sh user-auth T-003
#   ./execute-task.sh user-auth --status
#

set -e

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
CYAN='\033[0;36m'
BOLD='\033[1m'
NC='\033[0m'

FEATURE_NAME=$1
TASK_ID=$2

# Help
if [ -z "$FEATURE_NAME" ] || [ "$FEATURE_NAME" = "-h" ] || [ "$FEATURE_NAME" = "--help" ]; then
    echo "Usage: execute-task.sh <feature-name> [task-id|--status]"
    echo ""
    echo "Commands:"
    echo "  <feature-name>              Show next pending task with context"
    echo "  <feature-name> <task-id>    Execute specific task (e.g., T-003)"
    echo "  <feature-name> --status     Show progress summary"
    echo ""
    echo "Examples:"
    echo "  ./execute-task.sh user-auth"
    echo "  ./execute-task.sh user-auth T-003"
    echo "  ./execute-task.sh user-auth --status"
    exit 0
fi

SPEC_DIR=".spec-flow/active/$FEATURE_NAME"

if [ ! -d "$SPEC_DIR" ]; then
    echo -e "${RED}Error: Spec directory not found: $SPEC_DIR${NC}"
    echo "Available specs:"
    ls -1 .spec-flow/active/ 2>/dev/null || echo "  (none)"
    exit 1
fi

TASKS_FILE="$SPEC_DIR/tasks.md"

if [ ! -f "$TASKS_FILE" ]; then
    echo -e "${RED}Error: tasks.md not found in $SPEC_DIR${NC}"
    exit 1
fi

# Function: Parse tasks from tasks.md
parse_tasks() {
    # Extract task lines: matches patterns like "- [ ] **T-001**:" or "- [x] **T-001**:"
    grep -E "^[[:space:]]*-[[:space:]]*\[[ x]\][[:space:]]*\*\*T-[0-9]+\*\*" "$TASKS_FILE" 2>/dev/null || true
}

# Function: Count tasks by status
count_tasks() {
    local total=$(parse_tasks | wc -l | tr -d ' ')
    local completed=$(parse_tasks | grep -E "\[x\]" | wc -l | tr -d ' ')
    local pending=$((total - completed))
    echo "$completed $total $pending"
}

# Function: Get next pending task
get_next_pending_task() {
    parse_tasks | grep -E "\[ \]" | head -1 | sed -E 's/.*\*\*(T-[0-9]+)\*\*.*/\1/'
}

# Function: Get task description
get_task_description() {
    local task_id=$1
    parse_tasks | grep "$task_id" | sed -E 's/.*\*\*T-[0-9]+\*\*:[[:space:]]*//' | sed 's/[[:space:]]*$//'
}

# Function: Get task details (complexity, files, dependencies)
get_task_details() {
    local task_id=$1
    local in_task=false
    local details=""

    while IFS= read -r line; do
        if [[ "$line" =~ \*\*$task_id\*\* ]]; then
            in_task=true
            continue
        fi
        if $in_task; then
            # Stop at next task or section
            if [[ "$line" =~ ^\*\*T-[0-9]+\*\* ]] || [[ "$line" =~ ^##\  ]] || [[ "$line" =~ ^-\ \[.\]\ \*\*T- ]]; then
                break
            fi
            # Capture indented content (task details)
            if [[ "$line" =~ ^[[:space:]]+-[[:space:]] ]] || [[ "$line" =~ ^[[:space:]]+[A-Za-z] ]]; then
                details+="$line"$'\n'
            fi
        fi
    done < "$TASKS_FILE"

    echo "$details"
}

# Function: Show progress summary
show_status() {
    echo -e "${BOLD}${BLUE}=== SPEC-FLOW PROGRESS: $FEATURE_NAME ===${NC}"
    echo ""

    read -r completed total pending <<< $(count_tasks)

    if [ "$total" -eq 0 ]; then
        echo -e "${YELLOW}No tasks found in tasks.md${NC}"
        return
    fi

    local percent=$((completed * 100 / total))

    # Progress bar
    local bar_width=30
    local filled=$((percent * bar_width / 100))
    local empty=$((bar_width - filled))

    printf "${BOLD}Progress: ${NC}["
    printf "${GREEN}%0.s█${NC}" $(seq 1 $filled 2>/dev/null) || true
    printf "%0.s░" $(seq 1 $empty 2>/dev/null) || true
    printf "] ${BOLD}%d%%${NC} (%d/%d)\n" "$percent" "$completed" "$total"
    echo ""

    # Task list
    echo -e "${BOLD}Tasks:${NC}"
    parse_tasks | while read -r line; do
        if [[ "$line" =~ \[x\] ]]; then
            echo -e "  ${GREEN}✅${NC} $line" | sed 's/- \[x\] //' | sed 's/\*\*//g'
        else
            echo -e "  ${YELLOW}⏳${NC} $line" | sed 's/- \[ \] //' | sed 's/\*\*//g'
        fi
    done

    echo ""
    if [ "$pending" -gt 0 ]; then
        local next_task=$(get_next_pending_task)
        echo -e "${CYAN}Next task: ${BOLD}$next_task${NC}"
    else
        echo -e "${GREEN}${BOLD}All tasks completed! 🎉${NC}"
    fi
}

# Function: Show execution context for a task
show_task_context() {
    local task_id=$1
    local task_desc=$(get_task_description "$task_id")
    local task_details=$(get_task_details "$task_id")

    echo -e "${BOLD}${BLUE}╔════════════════════════════════════════════════════════════════╗${NC}"
    echo -e "${BOLD}${BLUE}║  SPEC-FLOW TASK EXECUTION CONTEXT                              ║${NC}"
    echo -e "${BOLD}${BLUE}╚════════════════════════════════════════════════════════════════╝${NC}"
    echo ""

    # Progress
    read -r completed total pending <<< $(count_tasks)
    echo -e "${BOLD}Feature:${NC} $FEATURE_NAME"
    echo -e "${BOLD}Progress:${NC} $completed/$total completed"
    echo ""

    # Current task
    echo -e "${BOLD}${CYAN}┌─ CURRENT TASK ─────────────────────────────────────────────────┐${NC}"
    echo -e "${BOLD}│ $task_id: $task_desc${NC}"
    echo -e "${CYAN}└────────────────────────────────────────────────────────────────┘${NC}"

    if [ -n "$task_details" ]; then
        echo ""
        echo -e "${BOLD}Task Details:${NC}"
        echo "$task_details" | sed 's/^/  /'
    fi
    echo ""

    # Relevant design section
    if [ -f "$SPEC_DIR/design.md" ]; then
        echo -e "${BOLD}${YELLOW}┌─ RELEVANT DESIGN ──────────────────────────────────────────────┐${NC}"
        # Try to find relevant section in design.md based on task keywords
        local keywords=$(echo "$task_desc" | tr ' ' '\n' | grep -E '^[A-Z]' | head -3 | tr '\n' '|' | sed 's/|$//')
        if [ -n "$keywords" ]; then
            grep -i -A 10 -E "$keywords" "$SPEC_DIR/design.md" 2>/dev/null | head -20 || echo "(No matching design section found)"
        else
            echo "(Review design.md for implementation details)"
        fi
        echo -e "${YELLOW}└────────────────────────────────────────────────────────────────┘${NC}"
        echo ""
    fi

    # Relevant requirements
    if [ -f "$SPEC_DIR/requirements.md" ]; then
        echo -e "${BOLD}${GREEN}┌─ RELEVANT REQUIREMENTS ────────────────────────────────────────┐${NC}"
        # Extract FR/NFR/AC references from task
        local refs=$(echo "$task_desc $task_details" | grep -oE "(FR|NFR|AC)-[0-9]+" | sort -u | tr '\n' ' ')
        if [ -n "$refs" ]; then
            for ref in $refs; do
                grep -A 2 "$ref" "$SPEC_DIR/requirements.md" 2>/dev/null || true
            done
        else
            echo "(No specific requirement references found in task)"
        fi
        echo -e "${GREEN}└────────────────────────────────────────────────────────────────┘${NC}"
        echo ""
    fi

    # Instructions
    echo -e "${BOLD}${RED}┌─ EXECUTION INSTRUCTIONS ───────────────────────────────────────┐${NC}"
    echo -e "│ 1. Execute ONLY this task: ${BOLD}$task_id${NC}"
    echo -e "│ 2. Follow the design specifications above"
    echo -e "│ 3. After completion, update tasks.md: [ ] → [x]"
    echo -e "│ 4. Report what was done and ask for confirmation"
    echo -e "│ 5. Do NOT proceed to next task without user saying 'continue'"
    echo -e "${RED}└────────────────────────────────────────────────────────────────┘${NC}"
}

# Main logic
if [ "$TASK_ID" = "--status" ]; then
    show_status
elif [ -n "$TASK_ID" ]; then
    # Specific task requested
    if ! parse_tasks | grep -q "$TASK_ID"; then
        echo -e "${RED}Error: Task $TASK_ID not found in tasks.md${NC}"
        echo ""
        echo "Available tasks:"
        parse_tasks | sed 's/^/  /'
        exit 1
    fi
    show_task_context "$TASK_ID"
else
    # Show next pending task
    NEXT_TASK=$(get_next_pending_task)
    if [ -z "$NEXT_TASK" ]; then
        echo -e "${GREEN}${BOLD}All tasks completed! 🎉${NC}"
        echo ""
        show_status
    else
        show_task_context "$NEXT_TASK"
    fi
fi
