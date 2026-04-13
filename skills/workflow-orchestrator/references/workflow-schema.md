# Workflow Definition Schema

Complete JSON Schema for workflow definitions used by the workflow orchestrator.

## Table of Contents
- [Workflow Object](#workflow-object)
- [Step Object](#step-object)
- [Retry Configuration](#retry-configuration)
- [Fallback Configuration](#fallback-configuration)
- [State File Schema](#state-file-schema)
- [Template Reference Format](#template-reference-format)

---

## Workflow Object

The top-level workflow definition.

```json
{
  "type": "object",
  "required": ["workflow"],
  "properties": {
    "workflow": {
      "type": "object",
      "required": ["name", "steps"],
      "properties": {
        "name": {
          "type": "string",
          "description": "Unique identifier for the workflow. Use kebab-case (e.g., 'research-and-report').",
          "pattern": "^[a-z0-9][a-z0-9-]*[a-z0-9]$"
        },
        "description": {
          "type": "string",
          "description": "Optional human-readable description of what this workflow accomplishes."
        },
        "steps": {
          "type": "array",
          "items": { "$ref": "#/definitions/Step" },
          "minItems": 1,
          "description": "Ordered list of steps. Execution order is determined by depends_on, not array position."
        },
        "on_failure": {
          "type": "string",
          "enum": ["abort", "continue", "ask"],
          "default": "continue",
          "description": "Default failure strategy when a step fails and has no step-level failure config. 'abort' stops the workflow, 'continue' skips the failed step's dependents and continues other branches, 'ask' pauses and asks the user."
        },
        "timeout_minutes": {
          "type": "integer",
          "minimum": 1,
          "description": "Optional global timeout for the entire workflow in minutes."
        }
      }
    }
  }
}
```

## Step Object

Each step in the workflow.

```json
{
  "type": "object",
  "required": ["id", "input"],
  "properties": {
    "id": {
      "type": "string",
      "description": "Unique step identifier within the workflow. Use descriptive kebab-case names (e.g., 'fetch-api-data', 'generate-report'). Must be unique across all steps.",
      "pattern": "^[a-z0-9][a-z0-9-]*[a-z0-9]$"
    },
    "skill": {
      "type": "string",
      "description": "Name or description of the skill to invoke for this step. Can be an exact skill name (e.g., 'pdf') or a description that will trigger the right skill (e.g., 'create a PDF document'). If omitted, the step runs as a general Agent task."
    },
    "tool": {
      "type": "string",
      "description": "Alternative to 'skill' — name of a specific tool to use (e.g., 'Bash', 'Read', 'Write'). Use this for simple operations that don't need a full skill."
    },
    "input": {
      "type": "string",
      "description": "The prompt or instruction for this step. May contain {{step_id}} template references to inject output from upstream steps. These are resolved at execution time."
    },
    "depends_on": {
      "type": "array",
      "items": { "type": "string" },
      "default": [],
      "description": "List of step IDs that must complete before this step can run. An empty array (or omitted field) means the step has no dependencies and can run immediately."
    },
    "retry": {
      "$ref": "#/definitions/Retry",
      "description": "Optional retry configuration for this step."
    },
    "fallback": {
      "$ref": "#/definitions/Fallback",
      "description": "Optional fallback step to execute if this step fails after all retries."
    },
    "on_failure": {
      "type": "string",
      "enum": ["abort", "skip", "fallback", "ask"],
      "default": "skip",
      "description": "What to do when this step fails. 'abort' stops the workflow. 'skip' marks it failed and skips its dependents. 'fallback' runs the fallback config. 'ask' pauses and consults the user."
    },
    "condition": {
      "type": "string",
      "description": "Optional condition expression. If provided, the step only runs when this condition evaluates to true. Supports simple expressions like '{{step_id}}.status == completed' or '{{step_id}}.output contains \"success\"'."
    },
    "save_output_to": {
      "type": "string",
      "description": "Optional file path where the step's output should be saved, in addition to the state file."
    }
  }
}
```

## Retry Configuration

```json
{
  "type": "object",
  "properties": {
    "max_attempts": {
      "type": "integer",
      "minimum": 1,
      "maximum": 5,
      "default": 1,
      "description": "Maximum number of attempts (including the first). Set to 1 for no retries."
    },
    "modified_input": {
      "type": "string",
      "description": "Optional alternative input to use on retry. If omitted, the original input is reused. May include {{error}} to reference the previous attempt's error message."
    }
  }
}
```

## Fallback Configuration

```json
{
  "type": "object",
  "required": ["input"],
  "properties": {
    "skill": {
      "type": "string",
      "description": "Skill to use for the fallback. If omitted, runs as a general Agent task."
    },
    "input": {
      "type": "string",
      "description": "Prompt for the fallback step. May reference {{error}} from the failed step."
    }
  }
}
```

## State File Schema

The `workflow-state.json` file tracks execution progress.

```json
{
  "type": "object",
  "required": ["workflow_name", "status", "started_at", "steps"],
  "properties": {
    "workflow_name": {
      "type": "string"
    },
    "status": {
      "type": "string",
      "enum": ["pending", "running", "completed", "failed", "aborted"],
      "description": "Overall workflow status."
    },
    "started_at": {
      "type": "string",
      "format": "date-time",
      "description": "ISO 8601 timestamp when the workflow started."
    },
    "completed_at": {
      "type": ["string", "null"],
      "format": "date-time",
      "description": "ISO 8601 timestamp when the workflow finished. Null while running."
    },
    "steps": {
      "type": "object",
      "additionalProperties": {
        "type": "object",
        "properties": {
          "status": {
            "type": "string",
            "enum": ["pending", "running", "completed", "failed", "skipped"]
          },
          "started_at": { "type": ["string", "null"], "format": "date-time" },
          "completed_at": { "type": ["string", "null"], "format": "date-time" },
          "output_summary": { "type": ["string", "null"] },
          "error": { "type": ["string", "null"] },
          "attempts": { "type": "integer", "minimum": 0 }
        }
      },
      "description": "Map of step_id to step state. Keys match the step IDs from the workflow definition."
    }
  }
}
```

## Template Reference Format

Templates stored in `references/templates.md` follow this structure:

```yaml
template:
  name: template-name
  description: "What this template does"
  parameters:
    - name: param-name
      description: "What this parameter controls"
      required: true
  workflow:
    name: "{{param-name}}-workflow"
    steps:
      - id: step1
        skill: "..."
        input: "... {{param-name}} ..."
        depends_on: []
```

Parameters use the same `{{name}}` template syntax and are resolved before execution. The user provides parameter values when invoking a template.

## Validation Rules

When parsing a workflow definition, validate:

1. **Unique IDs**: Every step `id` must be unique within the workflow
2. **Valid references**: Every ID in `depends_on` must match an existing step `id`
3. **No cycles**: The dependency graph must be acyclic (use topological sort to verify)
4. **Template resolution**: All `{{step_id}}` references in `input` fields must correspond to upstream dependencies (a step cannot reference a step it doesn't depend on)
5. **Fallback validity**: If `on_failure` is `fallback`, the `fallback` object must be present
6. **At least one root**: At least one step must have an empty `depends_on` (otherwise nothing can start)
