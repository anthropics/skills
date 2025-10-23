# Skill Development Guide

A comprehensive guide to creating effective, efficient, and maintainable Claude skills.

## Table of Contents

- [Core Concepts](#core-concepts)
- [Writing Effective SKILL.md](#writing-effective-skillmd)
- [Bundled Resources Patterns](#bundled-resources-patterns)
- [Progressive Disclosure](#progressive-disclosure)
- [Common Design Patterns](#common-design-patterns)
- [Performance Optimization](#performance-optimization)
- [Testing Strategies](#testing-strategies)
- [Troubleshooting](#troubleshooting)

## Core Concepts

### What Makes a Good Skill?

A good skill is:

1. **Focused** - Solves one problem well rather than many problems poorly
2. **Reusable** - Works across multiple similar situations
3. **Clear** - Instructions are unambiguous and actionable
4. **Efficient** - Minimizes context usage through progressive disclosure
5. **Reliable** - Handles errors gracefully and produces consistent results

### Skill vs. Slash Command

Choose a **Skill** when:
- Multiple steps or complex logic required
- Bundled resources needed (scripts, references, assets)
- Repeated use with different inputs
- Domain expertise or specialized workflow
- Used across different conversations

Choose a **Slash Command** when:
- Simple, one-time task
- Specific to your project/workflow
- No bundled resources needed
- Quick shortcut or template

### Skill vs. MCP Server

Choose a **Skill** when:
- Teaching Claude a workflow or methodology
- Primarily instruction-based
- Uses existing Claude tools
- Doesn't require external API calls

Choose an **MCP Server** when:
- Providing new tools/capabilities
- Integrating external services
- Real-time data access needed
- System-level operations required

## Writing Effective SKILL.md

### Frontmatter Structure

```yaml
---
name: your-skill-name           # REQUIRED: lowercase, hyphens only
description: Clear, concise description of when to use this skill and what it does  # REQUIRED
license: Apache-2.0             # OPTIONAL: default is repository license
allowed-tools: [Read, Write, Bash]  # OPTIONAL: Claude Code only
metadata:                       # OPTIONAL: custom properties
  version: "1.0"
  author: "Your Name"
  tags: ["productivity", "code-generation"]
---
```

### Description Best Practices

The description is crucial - it determines when Claude will load your skill.

**Good descriptions:**
- "Use this skill to generate p5.js algorithmic art with seeded randomness and particle systems"
- "Create animated GIFs optimized for Slack with specific dimension and file size requirements"
- "Guide users through creating high-quality MCP servers with best practices and validation"

**Poor descriptions:**
- "Art generator" (too vague)
- "Use this skill whenever you need to make things" (not specific enough)
- "This skill helps with various tasks related to..." (unclear trigger)

**Formula:** "Use this skill to [action] [specific output] [with/using] [key features/constraints]"

### Instruction Writing Principles

#### 1. Be Directive, Not Descriptive

**Bad:**
```
This skill helps create React components.
You might want to use TypeScript.
```

**Good:**
```
Create React components using TypeScript and functional syntax.
Always include prop types and JSDoc comments.
```

#### 2. Provide Clear Steps

**Bad:**
```
Figure out what the user wants and make it.
```

**Good:**
```
1. Ask the user to describe the component's purpose
2. Determine the required props and their types
3. Create the component file with the following structure:
   - Imports
   - Type definitions
   - Component implementation
   - Default export
4. Add example usage in comments
```

#### 3. Include Examples

**Bad:**
```
Use proper naming conventions.
```

**Good:**
```
Use proper naming conventions:
- Components: PascalCase (Button, UserProfile)
- Functions: camelCase (handleClick, fetchUserData)
- Constants: UPPER_SNAKE_CASE (API_URL, MAX_RETRIES)

Example:
```tsx
const MAX_RETRY_COUNT = 3;

export function UserProfile({ userId }: UserProfileProps) {
  // implementation
}
```
```

#### 4. Specify Tool Usage

**Bad:**
```
Read some files and make changes.
```

**Good:**
```
1. Use Glob to find all component files matching "*.component.tsx"
2. Use Read to examine each component's structure
3. Use Edit to update components that don't follow the pattern
4. Use Bash to run the linter: `npm run lint`
```

#### 5. Handle Edge Cases

```
Error Handling:
- If the file doesn't exist, create it in the src/components/ directory
- If TypeScript types are missing, generate them from the component usage
- If tests fail, show the user the error and ask how to proceed
- If the user's request is ambiguous, ask clarifying questions before proceeding
```

### Instruction Structure Template

```markdown
---
name: your-skill-name
description: [When to use this skill]
---

# Skill Name

## Purpose
[One paragraph: what this skill does and why it's useful]

## When to Use
- [Specific scenario 1]
- [Specific scenario 2]
- [Specific scenario 3]

## Instructions

### Step 1: [Phase Name]
[Detailed instructions for this phase]
[Examples if applicable]

### Step 2: [Phase Name]
[Detailed instructions for this phase]
[Tool usage specifications]

### Step 3: [Phase Name]
[Detailed instructions for this phase]
[Expected outputs]

## Guidelines
- [Important rule 1]
- [Important rule 2]
- [Important rule 3]

## Error Handling
- [Error condition 1]: [How to handle]
- [Error condition 2]: [How to handle]

## Examples

### Example 1: [Scenario]
Input:
```
[Example input]
```

Output:
```
[Example output]
```

### Example 2: [Scenario]
[Another example]

## Bundled Resources
- `scripts/[filename]` - [Purpose]
- `references/[filename]` - [When to load this]
- `assets/[filename]` - [How to use this]
```

## Bundled Resources Patterns

### Scripts Directory

Use scripts for:
- **Deterministic operations** - Exact formatting, complex algorithms
- **External tool integration** - Calling APIs, processing files
- **Performance-critical tasks** - Large data processing
- **Repeated operations** - Same task multiple times

#### Script Guidelines

**Make scripts executable:**
```bash
chmod +x scripts/your_script.py
```

**Include clear shebangs:**
```python
#!/usr/bin/env python3
```

**Document dependencies:**
```python
#!/usr/bin/env python3
"""
Script to process user data.

Dependencies:
- pandas>=2.0.0
- requests>=2.28.0

Install: pip install pandas requests
"""
```

**Return structured output:**
```python
import json
import sys

def main():
    try:
        result = process_data()
        print(json.dumps({"success": True, "data": result}))
        sys.exit(0)
    except Exception as e:
        print(json.dumps({"success": False, "error": str(e)}), file=sys.stderr)
        sys.exit(1)
```

**Example SKILL.md usage:**
```markdown
## Processing Data

To process the user data, execute the processing script:

```bash
python scripts/process_data.py input.csv output.json
```

The script will:
1. Validate the CSV format
2. Transform the data according to the schema
3. Output JSON in the required format

If the script fails, check the error message and verify:
- Input file exists and is valid CSV
- Required columns are present
- Output directory is writable
```

### References Directory

Use references for:
- **API documentation** - External service docs
- **Database schemas** - Table structures, relationships
- **Business logic** - Company-specific rules
- **Large examples** - Complete code samples
- **Technical specs** - Detailed format specifications

#### Reference Organization Patterns

**Pattern 1: By Topic**
```
references/
├── api-endpoints.md
├── database-schema.md
├── business-rules.md
└── examples.md
```

**Pattern 2: By Complexity**
```
references/
├── quick-reference.md      # Load frequently
├── detailed-guide.md       # Load when needed
└── complete-spec.md        # Load rarely
```

**Pattern 3: By Phase**
```
references/
├── 1-planning.md
├── 2-implementation.md
├── 3-testing.md
└── 4-deployment.md
```

#### Reference Loading Instructions

**For focused documents (<5k words):**
```markdown
When implementing authentication, read `references/auth-guide.md` for the complete authentication flow and security requirements.
```

**For large documents (>10k words):**
```markdown
The complete API documentation is in `references/api-docs.md`.
Use grep patterns to find specific endpoints:
- Authentication: grep "auth" references/api-docs.md
- User management: grep "user" references/api-docs.md
- Payments: grep "payment" references/api-docs.md

Only read the full file if you need to understand the overall API structure.
```

### Assets Directory

Use assets for:
- **Templates** - Boilerplate code, config files
- **Images** - Logos, icons, diagrams
- **Fonts** - Custom typography
- **Data files** - JSON schemas, example datasets

#### Asset Usage Patterns

**Templates:**
```markdown
## Creating a New Component

Use the React component template as a starting point:

1. Read `assets/templates/component.template.tsx`
2. Replace the placeholders:
   - `{{ComponentName}}` with the actual component name
   - `{{Props}}` with the required props
   - `{{Implementation}}` with the component logic
3. Write the completed component to the appropriate directory
```

**Images in output:**
```markdown
## Generating Branded Documents

Include the company logo in all generated documents:
- Logo file: `assets/logo.png`
- Usage: Insert at the top of each page
- Dimensions: Scale to 200px width, maintain aspect ratio
```

**Configuration templates:**
```markdown
## Setting Up Configuration

Copy the base configuration and customize:

1. Read `assets/config.template.json`
2. Update the following fields based on user input:
   - `apiUrl`: The API endpoint
   - `apiKey`: User's API key (ask user, never hardcode)
   - `environment`: dev/staging/prod
3. Write to `config.json` in the project root
```

## Progressive Disclosure

Progressive disclosure keeps context usage efficient by loading information only when needed.

### Three-Level Loading

**Level 1: Metadata (Always loaded)**
- Name and description only
- ~100 words
- Determines skill activation

**Level 2: SKILL.md Body (Loaded when skill triggers)**
- Complete instructions
- Target: <5,000 words
- Includes pointers to Level 3 resources

**Level 3: Bundled Resources (Loaded as needed)**
- Large references
- Multiple examples
- Detailed specifications
- Loaded explicitly by instructions

### Progressive Disclosure Patterns

#### Pattern 1: Basic → Advanced

**SKILL.md:**
```markdown
## Quick Start

For simple cases, follow this pattern:
[Simple instructions]

## Advanced Usage

For complex scenarios requiring [specific features], read `references/advanced-guide.md` which covers:
- [Advanced feature 1]
- [Advanced feature 2]
- [Advanced feature 3]
```

#### Pattern 2: Overview → Details

**SKILL.md:**
```markdown
## API Integration Overview

The API has four main endpoint categories:
1. Authentication - Login, logout, token refresh
2. Users - CRUD operations for user data
3. Content - Create and manage content
4. Analytics - Retrieve usage statistics

For detailed endpoint specifications, read `references/api-documentation.md`.
```

#### Pattern 3: Common Cases → Edge Cases

**SKILL.md:**
```markdown
## Standard Workflow

Most users need:
[80% use case instructions]

## Edge Cases

If the user has special requirements, consult `references/edge-cases.md` for:
- Legacy system integration
- Custom authentication flows
- High-volume optimizations
```

### When to Break Up Content

**Keep in SKILL.md:**
- Core workflow (always needed)
- Critical guidelines (always apply)
- Common patterns (frequently used)
- Tool usage instructions
- Error handling basics

**Move to references/:**
- API documentation (>1000 lines)
- Complete code examples (>100 lines)
- Detailed specifications
- Optional advanced techniques
- Historical context or background

## Common Design Patterns

### Pattern: Multi-Step Workflow

**Use case:** Complex processes with distinct phases

```markdown
## Implementation Process

### Phase 1: Discovery
1. Ask the user for [required information]
2. Use Glob to find [relevant files]
3. Analyze the current state

### Phase 2: Planning
1. Based on discovery, determine [approach]
2. Identify [required changes]
3. Ask user to confirm the plan

### Phase 3: Implementation
1. For each identified change:
   - Use Read to examine the file
   - Use Edit to make the change
   - Document what was changed
2. Verify changes are consistent

### Phase 4: Verification
1. Run tests: `npm test`
2. If tests fail, fix issues and retry
3. Confirm with user that changes meet requirements
```

### Pattern: User Configuration

**Use case:** Customizable behavior based on user preferences

```markdown
## Configuration

Before starting, ask the user for their preferences:

1. **Output format**: JSON, CSV, or YAML?
2. **Verbosity level**: Minimal, standard, or detailed?
3. **Include examples**: Yes or no?

Store these preferences and use them throughout the workflow.

Example interaction:
- Ask: "What output format would you like? (JSON/CSV/YAML)"
- Wait for response
- Proceed with the selected format
```

### Pattern: Iterative Refinement

**Use case:** Output that may need multiple revisions

```markdown
## Generation Process

1. Create initial version based on user input
2. Present to user for feedback
3. If user requests changes:
   - Apply the requested modifications
   - Present updated version
   - Repeat until user is satisfied
4. Finalize and save the result

Always ask "Would you like any changes to this?" before finalizing.
```

### Pattern: Validation and Correction

**Use case:** Ensuring output meets requirements

```markdown
## Quality Assurance

After generating the output:

1. Validate against requirements:
   - Check [requirement 1]
   - Verify [requirement 2]
   - Confirm [requirement 3]

2. If validation fails:
   - Explain what's missing or incorrect
   - Automatically fix if possible
   - Ask user for clarification if needed

3. Run automated checks:
   ```bash
   python scripts/validate.py output.json
   ```

4. Only proceed when all validations pass
```

### Pattern: Context Gathering

**Use case:** Need to understand codebase before making changes

```markdown
## Analysis Phase

Before making any changes:

1. **Understand the structure:**
   - Use Glob to find all [relevant files]
   - Use Grep to search for [key patterns]
   - Identify the main [components/modules]

2. **Analyze patterns:**
   - Read [key files] to understand conventions
   - Note the [naming patterns]
   - Identify [common approaches]

3. **Plan changes:**
   - List files that need modification
   - Describe what will change in each
   - Ensure consistency with existing patterns

4. **Confirm with user** before implementing
```

## Performance Optimization

### Minimize Context Usage

**Problem:** Loading unnecessary content into context
**Solution:** Use progressive disclosure and smart loading

**Bad:**
```markdown
Read all files in references/ to understand the system.
```

**Good:**
```markdown
For authentication issues, grep "auth" in references/ to find relevant docs, then read only those files.
```

### Batch Operations

**Problem:** Multiple small operations creating overhead
**Solution:** Batch similar operations together

**Bad:**
```markdown
For each file:
1. Read the file
2. Check if it needs updating
3. If yes, edit the file
4. Continue to next file
```

**Good:**
```markdown
1. Use Glob to find all candidate files
2. Use Grep to filter files that need updates
3. For each file needing updates:
   - Read and edit in sequence
4. Verify all changes together
```

### Smart Script Usage

**Problem:** Reading large scripts into context
**Solution:** Execute without reading when possible

**Bad:**
```markdown
Read scripts/large_processor.py to understand what it does, then execute it.
```

**Good:**
```markdown
Execute the data processor:
```bash
python scripts/large_processor.py input.json output.json
```

The script will:
- Validate input format
- Transform data according to schema
- Generate output file

[No need to read the script itself]
```

### Conditional Loading

**Problem:** Loading resources that may not be needed
**Solution:** Load based on specific conditions

```markdown
## Reference Loading

- If working with REST API: Read `references/rest-api.md`
- If working with GraphQL: Read `references/graphql-api.md`
- If working with WebSocket: Read `references/websocket-api.md`

Only load the reference relevant to the current task.
```

## Testing Strategies

### Manual Testing Checklist

- [ ] **Happy path**: Does it work with typical inputs?
- [ ] **Edge cases**: Empty inputs, very large inputs, special characters?
- [ ] **Error handling**: How does it respond to invalid inputs?
- [ ] **Instructions**: Are they clear and unambiguous?
- [ ] **Tool usage**: Does Claude use the right tools?
- [ ] **Output quality**: Is the result correct and well-formatted?
- [ ] **Performance**: Does it complete in reasonable time?
- [ ] **Context usage**: Is progressive disclosure working?

### Test Cases Template

Create a `TESTING.md` in your skill directory:

```markdown
# Test Cases for [Skill Name]

## Test Case 1: Basic Usage
**Input:** [Describe user request]
**Expected Behavior:** [What should happen]
**Expected Output:** [What should be produced]
**Status:** ✅ Pass / ❌ Fail

## Test Case 2: Edge Case - [Description]
**Input:** [Describe edge case]
**Expected Behavior:** [How it should handle this]
**Expected Output:** [Expected result]
**Status:** ✅ Pass / ❌ Fail

## Test Case 3: Error Handling - [Description]
**Input:** [Describe error condition]
**Expected Behavior:** [How it should gracefully fail]
**Expected Output:** [Error message or recovery]
**Status:** ✅ Pass / ❌ Fail
```

### Testing with Different Claude Interfaces

**Claude Code:**
```bash
# Symlink your skill for testing
ln -s /path/to/your-skill ~/.claude/skills/your-skill-name

# Test by triggering the skill
# Observe behavior, check logs
```

**Claude.ai:**
- Upload skill as ZIP file
- Test in chat interface
- Verify across multiple conversations

**Claude API:**
```python
from anthropic import Anthropic

client = Anthropic(api_key="your-api-key")

# Upload skill (if custom)
# Test with API calls
```

### Validation Script

Create automated validation for your skill:

```python
#!/usr/bin/env python3
"""Validate skill structure and content."""

import os
import yaml
import sys

def validate_skill(skill_dir):
    errors = []

    # Check SKILL.md exists
    skill_md = os.path.join(skill_dir, "SKILL.md")
    if not os.path.exists(skill_md):
        errors.append("SKILL.md is missing")
        return errors

    # Parse frontmatter
    with open(skill_md) as f:
        content = f.read()
        if not content.startswith("---"):
            errors.append("SKILL.md missing YAML frontmatter")
            return errors

        parts = content.split("---", 2)
        if len(parts) < 3:
            errors.append("SKILL.md frontmatter not properly closed")
            return errors

        try:
            frontmatter = yaml.safe_load(parts[1])
        except yaml.YAMLError as e:
            errors.append(f"Invalid YAML frontmatter: {e}")
            return errors

    # Validate required fields
    if "name" not in frontmatter:
        errors.append("Missing required field: name")
    elif not frontmatter["name"].islower() or "_" in frontmatter["name"]:
        errors.append("name must be lowercase with hyphens only")

    if "description" not in frontmatter:
        errors.append("Missing required field: description")
    elif len(frontmatter["description"]) > 200:
        errors.append("description should be under 200 characters")

    # Check directory name matches
    dir_name = os.path.basename(skill_dir.rstrip("/"))
    if "name" in frontmatter and frontmatter["name"] != dir_name:
        errors.append(f"Directory name '{dir_name}' doesn't match skill name '{frontmatter['name']}'")

    # Check for empty instruction body
    if len(parts[2].strip()) < 100:
        errors.append("SKILL.md instruction body seems too short")

    return errors

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: python validate_skill.py <skill-directory>")
        sys.exit(1)

    errors = validate_skill(sys.argv[1])

    if errors:
        print(f"❌ Validation failed with {len(errors)} error(s):")
        for error in errors:
            print(f"  - {error}")
        sys.exit(1)
    else:
        print("✅ Skill validation passed")
        sys.exit(0)
```

## Troubleshooting

### Skill Not Triggering

**Symptoms:** Claude doesn't load your skill when expected

**Causes and solutions:**
1. **Vague description**: Make description more specific about when to use
2. **Wrong trigger words**: Include terms users would naturally use
3. **Too narrow**: Skill may be too specialized to trigger often
4. **Overlapping skills**: Another skill may be triggering instead

**Fix:** Revise description to be clearer and more specific

### Skill Loads But Doesn't Work

**Symptoms:** Skill activates but Claude doesn't follow instructions

**Causes and solutions:**
1. **Ambiguous instructions**: Be more directive and specific
2. **Missing tool specifications**: Explicitly state which tools to use
3. **Conflicting guidelines**: Check for contradictory instructions
4. **Missing examples**: Add concrete examples of expected behavior

**Fix:** Rewrite instructions to be clearer and more prescriptive

### High Context Usage

**Symptoms:** Skill uses too much context, slow performance

**Causes and solutions:**
1. **Large SKILL.md**: Move detailed content to references/
2. **Loading all references**: Use conditional loading
3. **Reading scripts unnecessarily**: Execute scripts instead of reading
4. **No progressive disclosure**: Implement three-level loading pattern

**Fix:** Refactor using progressive disclosure principles

### Inconsistent Results

**Symptoms:** Skill produces different outputs for similar inputs

**Causes and solutions:**
1. **Ambiguous instructions**: Add more specific guidelines
2. **Missing validation**: Implement validation steps
3. **Unclear criteria**: Define clear success criteria
4. **No examples**: Add examples showing expected outputs

**Fix:** Add validation, examples, and clearer criteria

### Script Execution Failures

**Symptoms:** Bundled scripts fail or produce errors

**Causes and solutions:**
1. **Missing dependencies**: Document all requirements clearly
2. **Wrong paths**: Use absolute paths or proper relative paths
3. **Permission issues**: Ensure scripts are executable
4. **Environment issues**: Document required environment variables

**Fix:** Improve script robustness and documentation

---

## Additional Resources

- [Agent Skills Specification](agent_skills_spec.md) - Official specification
- [Contributing Guide](CONTRIBUTING.md) - How to contribute skills
- [skill-creator/SKILL.md](skill-creator/SKILL.md) - Meta-skill for creating skills
- [template-skill/SKILL.md](template-skill/SKILL.md) - Basic template to start from

---

**Need help?** Open an issue on GitHub or use the skill-creator skill for guidance!
