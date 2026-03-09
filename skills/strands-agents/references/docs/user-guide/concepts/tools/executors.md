# Tool Executors

!!! info "Python SDK Only"
    Tool executors are currently only exposed in the Python SDK.


Tool executors allow users to customize the execution strategy of tools executed by the agent (e.g., concurrent vs sequential). Currently, Strands is packaged with 2 executors.

## Concurrent Executor

Use `ConcurrentToolExecutor` (the default) to execute tools concurrently:

```python
from strands import Agent
from strands.tools.executors import ConcurrentToolExecutor

agent = Agent(
    tool_executor=ConcurrentToolExecutor(), 
    tools=[weather_tool, time_tool]
)
# or simply Agent(tools=[weather_tool, time_tool])

agent("What is the weather and time in New York?")
```

Assuming the model returns `weather_tool` and `time_tool` use requests, the `ConcurrentToolExecutor` will execute both concurrently.

### Sequential Behavior

On certain prompts, the model may decide to return one tool use request at a time. Under these circumstances, the tools will execute sequentially. Concurrency is only achieved if the model returns multiple tool use requests in a single response. Certain models however offer additional abilities to coerce a desired behavior. For example, Anthropic exposes an explicit parallel tool use setting ([docs](https://docs.anthropic.com/en/docs/agents-and-tools/tool-use/implement-tool-use#parallel-tool-use)).

## Sequential Executor

Use `SequentialToolExecutor` to execute tools sequentially:

```python
from strands import Agent
from strands.tools.executors import SequentialToolExecutor

agent = Agent(
    tool_executor=SequentialToolExecutor(), 
    tools=[screenshot_tool, email_tool]
)

agent("Please take a screenshot and then email the screenshot to my friend")
```

Assuming the model returns `screenshot_tool` and `email_tool` use requests, the `SequentialToolExecutor` will execute both sequentially in the order given.

## Custom Executor

Custom tool executors are not currently supported but are planned for a future release. You can track progress on this feature at [GitHub Issue #762](https://github.com/strands-agents/sdk-python/issues/762).
