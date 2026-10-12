#!/bin/bash
#
# init-spec-flow.sh - Initialize a new spec-flow directory structure
#
# Usage:
#   ./init-spec-flow.sh <feature-name> [--steering]
#
# Examples:
#   ./init-spec-flow.sh user-authentication
#   ./init-spec-flow.sh payment-integration --steering
#

set -e

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Get the directory where this script is located
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SKILL_DIR="$(dirname "$SCRIPT_DIR")"
TEMPLATES_DIR="$SKILL_DIR/templates"

# Parse arguments
FEATURE_NAME=""
INIT_STEERING=false

while [[ $# -gt 0 ]]; do
    case $1 in
        --steering)
            INIT_STEERING=true
            shift
            ;;
        -h|--help)
            echo "Usage: $0 <feature-name> [--steering]"
            echo ""
            echo "Arguments:"
            echo "  feature-name    Name of the feature (lowercase, hyphens allowed)"
            echo ""
            echo "Options:"
            echo "  --steering      Also initialize steering documents"
            echo "  -h, --help      Show this help message"
            echo ""
            echo "Examples:"
            echo "  $0 user-authentication"
            echo "  $0 payment-integration --steering"
            exit 0
            ;;
        *)
            if [[ -z "$FEATURE_NAME" ]]; then
                FEATURE_NAME="$1"
            else
                echo -e "${RED}Error: Unknown argument: $1${NC}"
                exit 1
            fi
            shift
            ;;
    esac
done

# Validate feature name
if [[ -z "$FEATURE_NAME" ]]; then
    echo -e "${RED}Error: Feature name is required${NC}"
    echo "Usage: $0 <feature-name> [--steering]"
    exit 1
fi

# Validate feature name format
if [[ ! "$FEATURE_NAME" =~ ^[a-z0-9-]+$ ]]; then
    echo -e "${RED}Error: Feature name must be lowercase with hyphens only${NC}"
    echo "Example: user-authentication, payment-integration"
    exit 1
fi

# Get current date
CURRENT_DATE=$(date +%Y-%m-%d)

# Create spec-flow directory structure
SPEC_DIR=".spec-flow"
ACTIVE_DIR="$SPEC_DIR/active/$FEATURE_NAME"
STEERING_DIR="$SPEC_DIR/steering"
ARCHIVE_DIR="$SPEC_DIR/archive"

echo -e "${BLUE}Initializing spec-flow for: ${GREEN}$FEATURE_NAME${NC}"
echo ""

# Create directories
mkdir -p "$ACTIVE_DIR"
mkdir -p "$ARCHIVE_DIR"

echo -e "${GREEN}✓${NC} Created $ACTIVE_DIR"
echo -e "${GREEN}✓${NC} Created $ARCHIVE_DIR"

# Function to copy and customize template
copy_template() {
    local template_file="$1"
    local output_file="$2"
    local feature_name="$3"
    local date="$4"

    if [[ -f "$template_file" ]]; then
        # Copy template and replace placeholders
        sed -e "s/{{FEATURE_NAME}}/$feature_name/g" \
            -e "s/{{DATE}}/$date/g" \
            -e "s/{{AUTHOR}}/$(whoami)/g" \
            -e "s/{{PROJECT_NAME}}/$(basename "$(pwd)")/g" \
            "$template_file" > "$output_file"
        echo -e "${GREEN}✓${NC} Created $output_file"
    else
        echo -e "${YELLOW}⚠${NC} Template not found: $template_file"
    fi
}

# Copy spec templates
copy_template "$TEMPLATES_DIR/proposal.md.template" "$ACTIVE_DIR/proposal.md" "$FEATURE_NAME" "$CURRENT_DATE"
copy_template "$TEMPLATES_DIR/requirements.md.template" "$ACTIVE_DIR/requirements.md" "$FEATURE_NAME" "$CURRENT_DATE"
copy_template "$TEMPLATES_DIR/design.md.template" "$ACTIVE_DIR/design.md" "$FEATURE_NAME" "$CURRENT_DATE"
copy_template "$TEMPLATES_DIR/tasks.md.template" "$ACTIVE_DIR/tasks.md" "$FEATURE_NAME" "$CURRENT_DATE"

# Create metadata file
cat > "$ACTIVE_DIR/.meta.json" << EOF
{
  "feature": "$FEATURE_NAME",
  "status": "proposal",
  "created": "$CURRENT_DATE",
  "updated": "$CURRENT_DATE",
  "author": "$(whoami)",
  "phase": "proposal"
}
EOF
echo -e "${GREEN}✓${NC} Created $ACTIVE_DIR/.meta.json"

# Initialize steering documents if requested
if [[ "$INIT_STEERING" == true ]]; then
    echo ""
    echo -e "${BLUE}Initializing steering documents...${NC}"
    mkdir -p "$STEERING_DIR"

    copy_template "$TEMPLATES_DIR/steering/constitution.md.template" "$STEERING_DIR/constitution.md" "$FEATURE_NAME" "$CURRENT_DATE"
    copy_template "$TEMPLATES_DIR/steering/product.md.template" "$STEERING_DIR/product.md" "$FEATURE_NAME" "$CURRENT_DATE"
    copy_template "$TEMPLATES_DIR/steering/tech.md.template" "$STEERING_DIR/tech.md" "$FEATURE_NAME" "$CURRENT_DATE"
    copy_template "$TEMPLATES_DIR/steering/structure.md.template" "$STEERING_DIR/structure.md" "$FEATURE_NAME" "$CURRENT_DATE"
fi

# Create .gitignore if it doesn't exist
if [[ ! -f "$SPEC_DIR/.gitignore" ]]; then
    cat > "$SPEC_DIR/.gitignore" << EOF
# Ignore backup files
*.bak
*.backup

# Keep archive in git but ignore empty directories
!archive/
archive/**/.gitkeep
EOF
    echo -e "${GREEN}✓${NC} Created $SPEC_DIR/.gitignore"
fi

echo ""
echo -e "${GREEN}✅ Spec-flow initialized successfully!${NC}"
echo ""
echo -e "${BLUE}Next steps:${NC}"
echo "  1. Edit ${YELLOW}$ACTIVE_DIR/proposal.md${NC} to define the feature"
echo "  2. Get proposal approved"
echo "  3. Fill in requirements, design, and tasks"
echo "  4. Use tasks.md to track implementation progress"
echo ""
echo -e "${BLUE}Workflow:${NC}"
echo "  Proposal → Requirements → Design → Tasks → Implementation → Archive"
