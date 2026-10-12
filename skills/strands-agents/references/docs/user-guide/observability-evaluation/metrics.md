# Metrics

Metrics are essential for understanding agent performance, optimizing behavior, and monitoring resource usage. The Strands Agents SDK provides comprehensive metrics tracking capabilities that give you visibility into how your agents operate.

## Overview

=== "Python"

    The Strands Agents SDK automatically tracks key metrics during agent execution:

    - **Token usage**: Input tokens, output tokens, total tokens consumed, and cache metrics
    - **Performance metrics**: Latency and execution time measurements
    - **Tool usage**: Call counts, success rates, and execution times for each tool
    - **Event loop cycles**: Number of reasoning cycles and their durations

    All these metrics are accessible through the [`AgentResult`](../../api-reference/python/agent/agent_result.md#strands.agent.agent_result.AgentResult) object that's returned whenever you invoke an agent:

    ```python
    from strands import Agent
    from strands_tools import calculator

    # Create an agent with tools
    agent = Agent(tools=[calculator])

    # Invoke the agent with a prompt and get an AgentResult
    result = agent("What is the square root of 144?")

    # Access metrics through the AgentResult
    print(f"Total tokens: {result.metrics.accumulated_usage['totalTokens']}")
    print(f"Execution time: {sum(result.metrics.cycle_durations):.2f} seconds")
    print(f"Tools used: {list(result.metrics.tool_metrics.keys())}")
    
    # Cache metrics (when available)
    if 'cacheReadInputTokens' in result.metrics.accumulated_usage:
        print(f"Cache read tokens: {result.metrics.accumulated_usage['cacheReadInputTokens']}")
    if 'cacheWriteInputTokens' in result.metrics.accumulated_usage:
        print(f"Cache write tokens: {result.metrics.accumulated_usage['cacheWriteInputTokens']}")
    ```

    The `metrics` attribute of `AgentResult` (an instance of [`EventLoopMetrics`](../../api-reference/python/telemetry/metrics.md#strands.telemetry.metrics)) provides comprehensive performance metric data about the agent's execution, while other attributes like `stop_reason`, `message`, and `state` provide context about the agent's response. This document explains the metrics available in the agent's response and how to interpret them.

=== "TypeScript"

    The TypeScript SDK provides basic metrics tracking through streaming events. Metrics are available via the `ModelMetadataEvent` that is emitted during agent execution:

    - **Token usage**: Input tokens, output tokens, and total tokens consumed
    - **Performance metrics**: Latency measurements

    ```typescript
    --8<-- "user-guide/observability-evaluation/metrics.ts:basic_metrics"
    ```

    The `ModelMetadataEvent` contains two optional properties:

    - `usage`: Token usage statistics including input, output, and cache metrics
    - `metrics`: Performance metrics including latency

    ### Available Metrics

    **Usage**:

    - `inputTokens: number` - Tokens in the input
    - `outputTokens: number` - Tokens in the output  
    - `totalTokens: number` - Total tokens used
    - `cacheReadInputTokens?: number` - Tokens read from cache
    - `cacheWriteInputTokens?: number` - Tokens written to cache

    **Metrics**:

    - `latencyMs: number` - Request latency in milliseconds

    ### Detailed Tracking Example

    ```typescript
    --8<-- "user-guide/observability-evaluation/metrics.ts:detailed_tracking"
    ```

## Agent Loop Metrics

=== "Python"

    The [`EventLoopMetrics`](../../api-reference/python/telemetry/metrics.md#strands.telemetry.metrics.EventLoopMetrics) class aggregates metrics across the entire event loop execution cycle, providing a complete picture of your agent's performance. It tracks cycle counts, tool usage, execution durations, and token consumption across all model invocations.

    Key metrics include:

    - **Cycle tracking**: Number of event loop cycles and their individual durations
    - **Tool metrics**: Detailed performance data for each tool used during execution
    - **Agent invocations**: List of agent invocations, each containing cycles and usage data for that specific invocation
    - **Accumulated usage**: Aggregated token counts (input, output, total, and cache metrics) across all agent invocations
    - **Accumulated metrics**: Latency measurements in milliseconds for all model requests
    - **Execution traces**: Detailed trace information for performance analysis

    ### Agent Invocations

    The `agent_invocations` property is a list of [`AgentInvocation`](../../api-reference/python/telemetry/metrics.md#strands.telemetry.metrics.AgentInvocation) objects that track metrics for each agent invocation (request). Each `AgentInvocation` contains:

    - **cycles**: A list of `EventLoopCycleMetric` objects, each representing a single event loop cycle with its ID and token usage
    - **usage**: Accumulated token usage for this specific invocation across all its cycles

    This allows you to track metrics at both the individual invocation level and across all invocations:

    ```python
    from strands import Agent
    from strands_tools import calculator

    agent = Agent(tools=[calculator])
    
    # First invocation
    result1 = agent("What is 5 + 3?")
    
    # Second invocation
    result2 = agent("What is the square root of 144?")
    
    # Access metrics for the latest invocation
    latest_invocation = result2.metrics.latest_agent_invocation
    cycles = latest_invocation.cycles
    usage = latest_invocation.usage

    # Or access all invocations
    for invocation in response.metrics.agent_invocations:
        print(f"Invocation usage: {invocation.usage}")
        for cycle in invocation.cycles:
            print(f"  Cycle {cycle.event_loop_cycle_id}: {cycle.usage}")

    # Or print the summary (includes all invocations)
    print(result2.metrics.get_summary())
    ```

    For a complete list of attributes and their types, see the [`EventLoopMetrics` API reference](../../api-reference/python/telemetry/metrics.md#strands.telemetry.metrics.EventLoopMetrics).

{{ ts_not_supported_code() }}

## Tool Metrics

=== "Python"

    For each tool used by the agent, detailed metrics are collected in the `tool_metrics` dictionary. Each entry is an instance of [`ToolMetrics`](../../api-reference/python/telemetry/metrics.md#strands.telemetry.metrics.ToolMetrics) that tracks the tool's performance throughout the agent's execution.

    Tool metrics provide insights into:

    - **Call statistics**: Total number of calls, successful executions, and errors
    - **Execution time**: Total and average time spent executing the tool
    - **Success rate**: Percentage of successful tool invocations
    - **Tool reference**: Information about the specific tool being tracked

    These metrics help you identify performance bottlenecks, tools with high error rates, and opportunities for optimization. For complete details on all available properties, see the [`ToolMetrics` API reference](../../api-reference/python/telemetry/metrics.md#strands.telemetry.metrics.ToolMetrics).

{{ ts_not_supported_code() }}

## Example Metrics Summary Output

=== "Python"

    The Strands Agents SDK provides a convenient `get_summary()` method on the `EventLoopMetrics` class that gives you a comprehensive overview of your agent's performance in a single call. This method aggregates all the metrics data into a structured dictionary that's easy to analyze or export.

    Let's look at the output from calling `get_summary()` on the metrics from our calculator example from the beginning of this document:

    ```python
    result = agent("What is the square root of 144?")
    print(result.metrics.get_summary())
    ```
    ```python
    {
      "total_cycles": 1,
      "total_duration": 2.6939949989318848,
      "average_cycle_time": 2.6939949989318848,
      "tool_usage": {},
      "traces": [{
          "id": "e1264f67-81c9-4bd7-8cab-8f69c53e85f1",
          "name": "Cycle 1",
          "raw_name": None,
          "parent_id": None,
          "start_time": 1767110391.614767,
          "end_time": 1767110394.308762,
          "duration": 2.6939949989318848,
          "children": [{
              "id": "0de6d280-14ff-423b-af80-9cc823c8c3a1",
              "name": "stream_messages",
              "raw_name": None,
              "parent_id": "e1264f67-81c9-4bd7-8cab-8f69c53e85f1",
              "start_time": 1767110391.614809,
              "end_time": 1767110394.308734,
              "duration": 2.693924903869629,
              "children": [],
              "metadata": {},
              "message": {
                  "role": "assistant",
                  "content": [{
                      "text": "The square root of 144 is 12.\n\nThis is because 12 × 12 = 144."
                  }]
              }
          }],
          "metadata": {},
          "message": None
      }],
      "accumulated_usage": {
          "inputTokens": 16,
          "outputTokens": 29,
          "totalTokens": 45
      },
      "accumulated_metrics": {
          "latencyMs": 1799
      },
      "agent_invocations": [{
          "usage": {
              "inputTokens": 16,
              "outputTokens": 29,
              "totalTokens": 45
          },
          "cycles": [{
              "event_loop_cycle_id": "ed854916-7eca-4317-a3f3-1ffcc03ee3ab",
              "usage": {
                  "inputTokens": 16,
                  "outputTokens": 29,
                  "totalTokens": 45
              }
          }]
      }]
    }
    ```

    This summary provides a complete picture of the agent's execution, including cycle information, token usage, tool performance, and detailed execution traces.

{{ ts_not_supported_code() }}

## Best Practices

1. **Monitor Token Usage**: Keep track of token usage to ensure you stay within limits and optimize costs. Set up alerts for when token usage approaches predefined thresholds to avoid unexpected costs.

2. **Analyze Tool Performance**: Review tool metrics to identify tools with high error rates or long execution times. Consider refactoring tools with success rates below 95% or average execution times that exceed your latency requirements.

3. **Track Cycle Efficiency**: Monitor how many iterations the agent needed and how long each took. Agents that require many cycles may benefit from improved prompting or tool design.

4. **Benchmark Latency Metrics**: Monitor latency values to establish performance baselines. Compare these metrics across different agent configurations to identify optimal setups.

5. **Regular Metrics Reviews**: Schedule periodic reviews of agent metrics to identify trends and opportunities for optimization. Look for gradual changes in performance that might indicate drift in tool behavior or model responses.
