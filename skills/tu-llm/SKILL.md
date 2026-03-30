---
name: tu-llm
description: LLM-powered tool discovery that reasons about which ToolUniverse tools to combine for complex, multi-step scientific queries. Uses Claude CLI (primary) with Ollama fallback.
---

# LLM Tool Planner

Use Claude CLI as a planning subagent to reason about which ToolUniverse tools to combine, then execute the full task end-to-end. Claude CLI reads all 1,200+ tool descriptions via your Max subscription (zero API cost), returns a tool plan as text, and the main session acts on it.

## Architecture

```
User task --> /tu-llm
  |
  +--> execute_tool("Tool_Finder_LLM", {description, limit})
  |      |
  |      +--> Claude CLI (claude --print) reasons over 1,200+ tools
  |      +--> Returns: tool names + execution order + reasoning
  |
  +--> Plan flows back as string into main context
  |
  +--> Main session executes the plan:
         1. get_tool_info(tool) for each tool in plan
         2. execute_tool(tool, args) in planned order
         3. Synthesize results into final deliverable
```

## Workflow

### Step 1: Get the tool plan

Call Tool_Finder_LLM with the user's full task description. Use a high limit to capture all relevant tools:

```
execute_tool("Tool_Finder_LLM", {"description": "<full task description>", "limit": 15})
```

The response is a JSON list of tools with relevance scores and reasoning. This is your execution plan.

### Step 2: Inspect each tool

For every tool in the plan, call `get_tool_info(tool_name)` to get the exact parameter schema. NEVER guess parameters.

### Step 3: Execute tools in order

Call `execute_tool(tool_name, {args})` for each tool following the plan's suggested order. Capture all outputs.

### Step 4: Synthesize

Combine all tool outputs into the final deliverable the user requested. This could be a research report, literature review, drug analysis, or any multi-source synthesis.

## When to Use

- Task requires data from multiple databases combined into a single output
- Embedding search (`find_tools`) returned irrelevant tools
- User needs a complete deliverable, not just tool results
- Complex multi-hop queries spanning literature, protein, drug, clinical, or genomic databases

## Backend

- **Primary**: Claude Code CLI (`claude --print`) -- Max subscription, zero marginal cost
- **Fallback**: Ollama (`deepseek-coder:6.7b`) -- offline-capable, local GPU

Selected automatically. Claude CLI is tried first; Ollama fires if CLI is unavailable.

## Rules

- ALWAYS call `get_tool_info` before `execute_tool` -- no exceptions
- Execute the FULL plan autonomously -- do not stop to ask after each tool
- If a tool fails, skip it and continue with the next tool in the plan
- Synthesize ALL results into the user's requested deliverable format
- The plan from Tool_Finder_LLM is advisory -- adapt if results suggest better tools mid-execution
