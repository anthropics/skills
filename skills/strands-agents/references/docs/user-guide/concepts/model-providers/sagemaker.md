# Amazon SageMaker

!!! info "Language Support"
    This provider is only supported in Python.

[Amazon SageMaker](https://aws.amazon.com/sagemaker/) is a fully managed machine learning service that provides infrastructure and tools for building, training, and deploying ML models at scale. The Strands Agents SDK implements a SageMaker provider, allowing you to run agents against models deployed on SageMaker inference endpoints, including both pre-trained models from SageMaker JumpStart and custom fine-tuned models. The provider is designed to work with models that support OpenAI-compatible chat completion APIs.

For example, you can expose models like [Mistral-Small-24B-Instruct-2501](https://aws.amazon.com/blogs/machine-learning/mistral-small-24b-instruct-2501-is-now-available-on-sagemaker-jumpstart-and-amazon-bedrock-marketplace/) on SageMaker, which has demonstrated reliable performance for conversational AI and tool calling scenarios.

## Installation

SageMaker is configured as an optional dependency in Strands Agents. To install, run:

```bash
pip install 'strands-agents[sagemaker]' strands-agents-tools
```

## Usage

After installing the SageMaker dependencies, you can import and initialize the Strands Agents' SageMaker provider as follows:

```python
from strands import Agent
from strands.models.sagemaker import SageMakerAIModel
from strands_tools import calculator

model = SageMakerAIModel(
    endpoint_config={
        "endpoint_name": "my-llm-endpoint",
        "region_name": "us-west-2",
    },
    payload_config={
        "max_tokens": 1000,
        "temperature": 0.7,
        "stream": True,
    }
)

agent = Agent(model=model, tools=[calculator])
response = agent("What is the square root of 64?")
```

**Note**: Tool calling support varies by model. Models like [Mistral-Small-24B-Instruct-2501](https://aws.amazon.com/blogs/machine-learning/mistral-small-24b-instruct-2501-is-now-available-on-sagemaker-jumpstart-and-amazon-bedrock-marketplace/) have demonstrated reliable tool calling capabilities, but not all models deployed on SageMaker support this feature. Verify your model's capabilities before implementing tool-based workflows.


## Configuration

### Endpoint Configuration

The `endpoint_config` configures the SageMaker endpoint connection:

| Parameter | Description | Required | Example |
|-----------|-------------|----------|---------|
| `endpoint_name` | Name of the SageMaker endpoint | Yes | `"my-llm-endpoint"` |
| `region_name` | AWS region where the endpoint is deployed | Yes | `"us-west-2"` |
| `inference_component_name` | Name of the inference component | No | `"my-component"` |
| `target_model` | Specific model to invoke (multi-model endpoints) | No | `"model-a.tar.gz"` |
| `target_variant` | Production variant to invoke | No | `"variant-1"` |

### Payload Configuration

The `payload_config` configures the model inference parameters:

| Parameter | Description | Default | Example |
|-----------|-------------|---------|---------|
| `max_tokens` | Maximum number of tokens to generate | Required | `1000` |
| `stream` | Enable streaming responses | `True` | `True` |
| `temperature` | Sampling temperature (0.0 to 2.0) | Optional | `0.7` |
| `top_p` | Nucleus sampling parameter (0.0 to 1.0) | Optional | `0.9` |
| `top_k` | Top-k sampling parameter | Optional | `50` |
| `stop` | List of stop sequences | Optional | `["Human:", "AI:"]` |

## Model Compatibility

The SageMaker provider is designed to work with models that support OpenAI-compatible chat completion APIs. During development and testing, the provider has been validated with [Mistral-Small-24B-Instruct-2501](https://aws.amazon.com/blogs/machine-learning/mistral-small-24b-instruct-2501-is-now-available-on-sagemaker-jumpstart-and-amazon-bedrock-marketplace/), which demonstrated reliable performance across various conversational AI tasks.

### Important Considerations

- **Model Performance**: Results and capabilities vary significantly depending on the specific model deployed to your SageMaker endpoint
- **Tool Calling Support**: Not all models deployed on SageMaker support function/tool calling. Verify your model's capabilities before implementing tool-based workflows
- **API Compatibility**: Ensure your deployed model accepts and returns data in the OpenAI chat completion format

For optimal results, we recommend testing your specific model deployment with your use case requirements before production deployment.

## Troubleshooting

### Module Not Found

If you encounter `ModuleNotFoundError: No module named 'boto3'` or similar, install the SageMaker dependencies:

```bash
pip install 'strands-agents[sagemaker]'
```

### Authentication

The SageMaker provider uses standard AWS authentication methods (credentials file, environment variables, IAM roles, or AWS SSO). Ensure your AWS credentials have the necessary SageMaker invoke permissions.

### Model Compatibility

Ensure your deployed model supports OpenAI-compatible chat completion APIs and verify tool calling capabilities if needed. Refer to the [Model Compatibility](#model-compatibility) section above for detailed requirements and testing recommendations.

## References

- [API Reference](../../../api-reference/python/models/model.md)
- [Amazon SageMaker Documentation](https://docs.aws.amazon.com/sagemaker/)
- [SageMaker Runtime API](https://docs.aws.amazon.com/sagemaker/latest/APIReference/API_runtime_InvokeEndpoint.html)
