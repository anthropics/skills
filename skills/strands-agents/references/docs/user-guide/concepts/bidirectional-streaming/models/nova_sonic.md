# Nova Sonic [Experimental]

{{ experimental_feature_warning() }}

[Amazon Nova Sonic](https://docs.aws.amazon.com/nova/latest/userguide/speech.html) provides real-time, conversational interactions through bidirectional audio streaming. Amazon Nova Sonic processes and responds to real-time speech as it occurs, enabling natural, human-like conversational experiences. Key capabilities and features include:

- Adaptive speech response that dynamically adjusts delivery based on the prosody of the input speech.
- Graceful handling of user interruptions without dropping conversational context.
- Function calling and agentic workflow support for building complex AI applications.
- Robustness to background noise for real-world deployment scenarios.
- Multilingual support with expressive voices and speaking styles. Expressive voices are offered, including both masculine-sounding and feminine sounding, in five languages: English (US, UK), French, Italian, German, and Spanish.
- Recognition of varied speaking styles across all supported languages.

## Installation

!!! warning "Python 3.12+ Required"
    Nova Sonic requires Python 3.12 or higher due to its experimental AWS SDK dependency.

Nova Sonic is included in the base bidirectional streaming dependencies for Strands Agents.

To install it, run:

```bash
pip install 'strands-agents[bidi]'
```

Or to install all bidirectional streaming providers at once:

```bash
pip install 'strands-agents[bidi-all]'
```

## Usage

After installing `strands-agents[bidi]`, you can import and initialize the Strands Agents' Nova Sonic provider as follows:

```python
import asyncio

from strands.experimental.bidi import BidiAgent
from strands.experimental.bidi.io import BidiAudioIO, BidiTextIO
from strands.experimental.bidi.models import BidiNovaSonicModel
from strands.experimental.bidi.tools import stop_conversation

from strands_tools import calculator


async def main() -> None:
    model = BidiNovaSonicModel(
        model_id="amazon.nova-sonic-v1:0",
        provider_config={
            "audio": {
                "voice": "tiffany",
            },
        },
        client_config={"region": "us-east-1"},  # only available in us-east-1, eu-north-1, and ap-northeast-1
    )
    # stop_conversation tool allows user to verbally stop agent execution.
    agent = BidiAgent(model=model, tools=[calculator, stop_conversation])

    audio_io = BidiAudioIO()
    text_io = BidiTextIO()
    await agent.run(inputs=[audio_io.input()], outputs=[audio_io.output(), text_io.output()])


if __name__ == "__main__":
    asyncio.run(main())
```

## Credentials

!!! warning "Nova Sonic is only available in us-east-1, eu-north-1, and ap-northeast-1."

Nova Sonic requires AWS credentials for access. Under the hook, `BidiNovaSonicModel` uses an experimental [Bedrock client](https://github.com/awslabs/aws-sdk-python/tree/develop/clients/aws-sdk-bedrock-runtime/src/aws_sdk_bedrock_runtime), which allows for credentials to be configured in the following ways:

**Option 1: Environment Variables**

```bash
export AWS_ACCESS_KEY_ID=your_access_key
export AWS_SECRET_ACCESS_KEY=your_secret_key
export AWS_SESSION_TOKEN=your_session_token  # If using temporary credentials
export AWS_REGION=your_region_name
```

**Option 2: Boto3 Session**

```python
import boto3
from strands.experimental.bidi.models import BidiNovaSonicModel


boto_session = boto3.Session(
    aws_access_key_id="your_access_key",
    aws_secret_access_key="your_secret_key",
    aws_session_token="your_session_token",  # If using temporary credentials
    region_name="your_region_name",
    profile_name="your_profile"  # Optional: Use a specific profile
)
model = BidiNovaSonicModel(client_config={"boto_session": boto_session})
```

For more details on this approach, please refer to the [boto3 session docs](https://boto3.amazonaws.com/v1/documentation/api/latest/reference/core/session.html).

## Configuration

### Client Configs

| Parameter | Description | Default |
| --------- | ----------- | ------- |
| `boto3_session` | A `boto3.Session` instance under which AWS credentials are configured. | `None` |
| `region` | Region under which credentials are configured. Cannot use if providing `boto3_session`. | `us-east-1` |

### Provider Configs

| Parameter | Description | Example | Options |
| --------- | ----------- | ------- | ------- |
| `audio` | `AudioConfig` instance. | `{"voice": "tiffany"}` | [reference](../../../../api-reference/python/experimental/bidi/types/model.md#strands.experimental.bidi.types.model.AudioConfig) |
| `inference` | Session start `inferenceConfiguration`'s (as snake_case). | `{"top_p": 0.9}` | [reference](https://docs.aws.amazon.com/nova/latest/userguide/input-events.html)

## Troubleshooting

### Module Not Found

If you encounter the error `ModuleNotFoundError: No module named 'aws_sdk_bedrock_runtime'`, this means the experimental Bedrock runtime dependency hasn't been properly installed in your environment. To fix this, run `pip install 'strands-agents[bidi]'`.

!!! note "Python Version Requirement"
    Nova Sonic requires Python 3.12+ due to the experimental AWS SDK dependency. If you're using an older Python version, you'll need to upgrade.

### Hanging

When credentials are misconfigured, the model provider does not throw an exception (a quirk of the underlying experimental Bedrock client). As a result, the provider allows the user to proceed forward with a call to `receive`, which emits no events and thus presents an indefinite hanging behavior.

As a reminder, Nova Sonic is only available in us-east-1, eu-north-1, and ap-northeast-1.

## References

- [Nova Sonic](https://docs.aws.amazon.com/nova/latest/userguide/speech.html)
- [Experimental Bedrock Client](https://github.com/awslabs/aws-sdk-python/tree/develop/clients/aws-sdk-bedrock-runtime)
- [Provider API Reference](../../../../api-reference/python/experimental/bidi/models/nova_sonic.md#strands.experimental.bidi.models.nova_sonic.BidiNovaSonicModel)
