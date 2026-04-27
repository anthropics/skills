---
name: vynn
description: Self-improving AI workflows with backtesting, prompt optimization, and scheduling. Use this skill when the user wants to create, run, or optimize AI workflows, backtest trading strategies, optimize portfolios, or set up automated schedules and triggers.
---

# Vynn — AI Workflows & Backtesting

This skill provides access to 21 MCP tools for building self-improving AI workflows and running quantitative backtests.

## When to Use

- User wants to **create or run an AI workflow** (multi-step LLM pipelines)
- User wants to **backtest a trading strategy** using natural language or structured rules
- User wants to **optimize prompts** in a workflow step using AI-powered analysis
- User wants to **schedule workflows** to run on a cron schedule
- User wants to **optimize a portfolio** using mean-variance optimization
- User asks about workflow **analytics** (success rates, latency, cost)

## Prerequisites

Requires the `vynn-mcp` MCP server to be configured:

```bash
pip install vynn-mcp
export VYNN_API_KEY="your_key_here"
```

Get a free API key at https://the-vynn.com

## Available Tools

### Workflows
- `list_workflows` — List all your workflows
- `get_workflow(workflow_id)` — Get full details of a workflow
- `create_workflow(name, description, steps?)` — Create a new workflow
- `run_workflow(workflow_id, input_text)` — Execute a workflow
- `get_runs(workflow_id)` — View recent run history
- `get_run_summary(run_id)` — Detailed run results

### Self-Improving
- `optimize_prompt(workflow_id, step_id)` — Get AI-optimized prompt variants
- `apply_prompt_optimization(workflow_id, step_id, prompt)` — Apply a new prompt
- `get_model_recommendation(workflow_id, step_id)` — Get model swap suggestions
- `set_schedule(workflow_id, cron, input, timezone?)` — Schedule automatic runs
- `get_schedule(workflow_id)` / `delete_schedule(workflow_id)` — Manage schedules
- `create_trigger(workflow_id)` / `list_triggers(workflow_id)` — Webhook triggers
- `get_analytics(workflow_id)` — Performance analytics

### Backtesting
- `backtest(strategy, universe?, ...)` — Run a backtest with natural language or JSON strategies
- `batch_backtest(base_strategy, parameter_grid, ...)` — Parameter sweep
- `optimize_portfolio(universe, method?, ...)` — Portfolio optimization

### Utilities
- `list_templates` / `clone_template` — Workflow templates
- `list_available_tools` — Available step tools

## Examples

**Create and run a workflow:**
```
User: "Create a workflow that researches a company and writes an investment memo"
→ Use create_workflow with steps for research and writing
→ Use run_workflow with the company name as input
```

**Backtest a strategy:**
```
User: "Backtest buying NVDA when RSI drops below 30"
→ Use backtest with strategy="Buy when RSI(14) < 30, sell when RSI(14) > 70" and universe=["NVDA"]
```

**Optimize a workflow:**
```
User: "My workflow results aren't great, can you improve it?"
→ Use get_analytics to check performance
→ Use optimize_prompt on underperforming steps
→ Use get_model_recommendation to check if a different model would help
```

## Guidelines

- Always show backtest results clearly: total return, Sharpe ratio, max drawdown, win rate
- When creating workflows, ask the user what each step should do before creating
- For backtesting, support both natural language ("buy when RSI < 30") and structured JSON formats
- When optimizing, show the user the suggested changes before applying them
