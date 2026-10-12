# OpenAI Realtime [Experimental]

{{ experimental_feature_warning() }}

The [OpenAI Realtime API](https://platform.openai.com/docs/guides/realtime) is a speech-to-speech interface that enables low-latency, natural voice conversations with AI. Key features include:

- **Bidirectional Interaction**: The user and the model can provide input and output at the same time.
- **Interruptibility**: Allows users to interrupt the AI mid-response, like in human conversations.
- **Multimodal Streaming**: The API supports streaming of text and audio data.
- **Tool Use and Function Calling**: Can use external tools to perform actions and get context while maintaining a real-time connection.
- **Secure Authentication**: Uses tokens for secure client-side authentication. 

## Installation

OpenAI Realtime is configured as an optional dependency in Strands Agents.

To install it, run:

```bash
pip install 'strands-agents[bidi-openai]'
```

Or to install all bidirectional streaming providers at once:

```bash
pip install 'strands-agents[bidi-all]'
```

## Usage

After installing `strands-agents[bidi-openai]`, you can import and initialize the Strands Agents' OpenAI Realtime provider as follows:

```python
import asyncio

from strands.experimental.bidi import BidiAgent
from strands.experimental.bidi.io import BidiAudioIO, BidiTextIO
from strands.experimental.bidi.models import BidiOpenAIRealtimeModel
from strands.experimental.bidi.tools import stop_conversation

from strands_tools import calculator


async def main() -> None:
    model = BidiOpenAIRealtimeModel(
        model_id="gpt-realtime",
        provider_config={
            "audio": {
                "voice": "coral",
            },
        },
        client_config={"api_key": "<OPENAI_API_KEY>"},
    )
    # stop_conversation tool allows user to verbally stop agent execution.
    agent = BidiAgent(model=model, tools=[calculator, stop_conversation])

    audio_io = BidiAudioIO()
    text_io = BidiTextIO()
    await agent.run(inputs=[audio_io.input()], outputs=[audio_io.output(), text_io.output()])


if __name__ == "__main__":
    asyncio.run(main())
```

## Configuration

### Client Configs

| Parameter | Description | Example | Options |
| --------- | ----------- | ------- | ------- |
| `api_key` | OpenAI API key used for authentication | `sk-...` | [reference](https://platform.openai.com/docs/api-reference/authentication) |
| `organization` | Organization associated with the connection. Used for authentication if required. | `myorg` | [reference](https://platform.openai.com/docs/api-reference/authentication)
| `project` | Project associated with the connection. Used for authentication if required. | `myproj` | [reference](https://platform.openai.com/docs/api-reference/authentication)
| `timeout_s` | OpenAI documents a 60 minute limit on realtime sessions ([docs](https://platform.openai.com/docs/guides/realtime-conversations#session-lifecycle-events)). However, OpenAI does not emit any warnings when approaching the limit. As a workaround, we allow users to configure a timeout (in seconds) on the client side to gracefully handle the connection closure. | `3000` | `[1, 3000]` (in seconds)

### Provider Configs

| Parameter | Description | Example | Options |
| --------- | ----------- | ------- | ------- |
| `audio` | `AudioConfig` instance. | `{"voice": "coral"}` | [reference](../../../../api-reference/python/experimental/bidi/types/model.md#strands.experimental.bidi.types.model.AudioConfig) |
| `inference` | Dict of inference fields supported in the OpenAI `session.update` event. | `{"max_output_tokens": 4096}` | [reference](https://platform.openai.com/docs/api-reference/realtime-client-events/session/update)

For the list of supported voices, see [here](https://platform.openai.com/docs/guides/realtime-conversations#voice-options).

## Troubleshooting

### Module Not Found

If you encounter the error `ModuleNotFoundError: No module named 'websockets'`, this means the WebSocket dependency hasn't been properly installed in your environment. To fix this, run `pip install 'strands-agents[bidi-openai]'`.

### Authentication Errors

Ensure your OpenAI API key is properly configured. Set the `OPENAI_API_KEY` environment variable or pass it via the `api_key` parameter in the `client_config`.

## References

- [OpenAI Realtime API](https://platform.openai.com/docs/guides/realtime)
- [OpenAI API Reference](https://platform.openai.com/docs/api-reference/realtime)
- [Provider API Reference](../../../../api-reference/python/experimental/bidi/models/openai_realtime.md#strands.experimental.bidi.models.openai_realtime.BidiOpenAIRealtimeModel)
