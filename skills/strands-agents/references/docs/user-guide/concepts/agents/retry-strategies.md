# Retry Strategies

Model providers occasionally encounter errors such as rate limits, service unavailability, or network timeouts. By default, the agent retries `ModelThrottledException` failures automatically with exponential backoff and the `Angent.retry_strategy` parameter lets you customize this behavior.

## Default Behavior

Without configuration, agents retry `ModelThrottledException` up to 5 times (6 total attempts) with exponential backoff starting at 4 seconds:

```
Attempt 1: fails → wait 4s
Attempt 2: fails → wait 8s
Attempt 3: fails → wait 16s
Attempt 4: fails → wait 32s
Attempt 5: fails → wait 64s
Attempt 6: fails → exception raised
```

## Customizing Retry Behavior

Use `ModelRetryStrategy` to adjust the retry parameters:

=== "Python"

    ```python
    from strands import Agent, ModelRetryStrategy
    
    agent = Agent(
        retry_strategy=ModelRetryStrategy(
            max_attempts=3,      # Total attempts (including first try)
            initial_delay=2,     # Seconds before first retry
            max_delay=60         # Cap on backoff delay
        )
    )
    ```

{{ ts_not_supported_code() }}

### Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `max_attempts` | `int` | `6` | Total number of attempts including the initial call. Set to `1` to disable retries. |
| `initial_delay` | `float` | `4` | Seconds to wait before the first retry. Subsequent retries double this value. |
| `max_delay` | `float` | `128` | Maximum seconds to wait between retries. Caps the exponential growth. |

## Disabling Retries

To disable automatic retries entirely:

=== "Python"

    ```python
    from strands import Agent, ModelRetryStrategy
    
    agent = Agent(
        retry_strategy=None
    )
    ```

{{ ts_not_supported_code() }}

## When Retries Occur

`ModelRetryStrategy` handles `ModelThrottledException`, which model providers raise for rate-limiting. Other exceptions propagate immediately without retry.

## Custom Retry Logic

Built in retry constructs like `ModelRetryStrategy` are useful for customizing model rate-limiting behavior, but for more fine-grained control - like validating model responses or handling additional exception types - use a hook instead. The `AfterModelCallEvent` fires after each model call and lets you set `event.retry = True` to trigger another attempt:

=== "Python"

    ```python
    import asyncio
    from strands import Agent
    from strands.hooks import HookProvider, HookRegistry, AfterModelCallEvent
    
    class CustomRetry(HookProvider):
        def __init__(self, max_retries: int = 3, delay: float = 2.0):
            self.max_retries = max_retries
            self.delay = delay
            self.attempts = 0
    
        def register_hooks(self, registry: HookRegistry) -> None:
            registry.add_callback(AfterModelCallEvent, self.maybe_retry)
    
        async def maybe_retry(self, event: AfterModelCallEvent) -> None:
            if event.exception and self.attempts < self.max_retries:
                self.attempts += 1
                await asyncio.sleep(self.delay)
                event.retry = True
    
    agent = Agent(hooks=[CustomRetry()])
    ```

{{ ts_not_supported_code() }}

Unlike `ModelRetryStrategy`, hooks don't automatically introduce delays between retries. The example above uses `asyncio.sleep` to add a 2-second delay before each retry.

See [Hooks](hooks.md#model-call-retry) for more examples.
