# Guardrails

Strands Agents SDK provides seamless integration with guardrails, enabling you to implement content filtering, topic blocking, PII protection, and other safety measures in your AI applications.

## What Are Guardrails?

Guardrails are safety mechanisms that help control AI system behavior by defining boundaries for content generation and interaction. They act as protective layers that:

1. **Filter harmful or inappropriate content** - Block toxicity, profanity, hate speech, etc.
2. **Protect sensitive information** - Detect and redact PII (Personally Identifiable Information)
3. **Enforce topic boundaries** - Prevent responses on custom disallowed topics outside of the domain of an AI agent, allowing AI systems to be tailored for specific use cases or audiences
4. **Ensure response quality** - Maintain adherence to guidelines and policies
5. **Enable compliance** - Help meet regulatory requirements for AI systems
6. **Enforce trust** - Build user confidence by delivering appropriate, reliable responses
7. **Manage Risk** - Reduce legal and reputational risks associated with AI deployment

## Guardrails in Different Model Providers

Strands Agents SDK allows integration with different model providers, which implement guardrails differently.

### Amazon Bedrock

{{ ts_not_supported() }}

Amazon Bedrock provides a [built-in guardrails framework](https://docs.aws.amazon.com/bedrock/latest/userguide/guardrails.html) that integrates directly with Strands Agents SDK. If a guardrail is triggered, the Strands Agents SDK will automatically overwrite the user's input in the conversation history. This is done so that follow-up questions are not also blocked by the same questions. This can be configured with the `guardrail_redact_input` boolean, and the `guardrail_redact_input_message` string to change the overwrite message. Additionally, the same functionality is built for the model's output, but this is disabled by default. You can enable this with the `guardrail_redact_output` boolean, and change the overwrite message with the `guardrail_redact_output_message` string. Below is an example of how to leverage Bedrock guardrails in your code:

```python
import json
from strands import Agent
from strands.models import BedrockModel

# Create a Bedrock model with guardrail configuration
bedrock_model = BedrockModel(
    model_id="global.anthropic.claude-sonnet-4-5-20250929-v1:0",
    guardrail_id="your-guardrail-id",         # Your Bedrock guardrail ID
    guardrail_version="1",                    # Guardrail version
    guardrail_trace="enabled",                # Enable trace info for debugging
)

# Create agent with the guardrail-protected model
agent = Agent(
    system_prompt="You are a helpful assistant.",
    model=bedrock_model,
)

# Use the protected agent for conversations
response = agent("Tell me about financial planning.")

# Handle potential guardrail interventions
if response.stop_reason == "guardrail_intervened":
    print("Content was blocked by guardrails, conversation context overwritten!")

print(f"Conversation: {json.dumps(agent.messages, indent=4)}")
```

Alternatively, if you want to implement your own soft-launching guardrails, you can utilize Hooks along with Bedrock's ApplyGuardrail API in shadow mode. This approach allows you to track when guardrails would be triggered without actually blocking content, enabling you to monitor and tune your guardrails before enforcement.

Steps:

1. Create a NotifyOnlyGuardrailsHook class that contains hooks
2. Register your callback functions with specific events.
3. Use agent normally

Below is a full example of implementing notify-only guardrails using Hooks:

````python
import boto3
from strands import Agent
from strands.hooks import HookProvider, HookRegistry, MessageAddedEvent, AfterInvocationEvent

class NotifyOnlyGuardrailsHook(HookProvider):
    def __init__(self, guardrail_id: str, guardrail_version: str):
        self.guardrail_id = guardrail_id
        self.guardrail_version = guardrail_version
        self.bedrock_client = boto3.client("bedrock-runtime", "us-west-2") # change to your AWS region

    def register_hooks(self, registry: HookRegistry) -> None:
        registry.add_callback(MessageAddedEvent, self.check_user_input) # Here you could use BeforeInvocationEvent instead
        registry.add_callback(AfterInvocationEvent, self.check_assistant_response)

    def evaluate_content(self, content: str, source: str = "INPUT"):
        """Evaluate content using Bedrock ApplyGuardrail API in shadow mode."""
        try:
            response = self.bedrock_client.apply_guardrail(
                guardrailIdentifier=self.guardrail_id,
                guardrailVersion=self.guardrail_version,
                source=source,
                content=[{"text": {"text": content}}]
            )

            if response.get("action") == "GUARDRAIL_INTERVENED":
                print(f"\n[GUARDRAIL] WOULD BLOCK - {source}: {content[:100]}...")
                # Show violation details from assessments
                for assessment in response.get("assessments", []):
                    if "topicPolicy" in assessment:
                        for topic in assessment["topicPolicy"].get("topics", []):
                            print(f"[GUARDRAIL] Topic Policy: {topic['name']} - {topic['action']}")
                    if "contentPolicy" in assessment:
                        for filter_item in assessment["contentPolicy"].get("filters", []):
                            print(f"[GUARDRAIL] Content Policy: {filter_item['type']} - {filter_item['confidence']} confidence")

        except Exception as e:
            print(f"[GUARDRAIL] Evaluation failed: {e}")

    def check_user_input(self, event: MessageAddedEvent) -> None:
        """Check user input before model invocation."""
        if event.message.get("role") == "user":
            content = "".join(block.get("text", "") for block in event.message.get("content", []))
            if content:
                self.evaluate_content(content, "INPUT")
    
    def check_assistant_response(self, event: AfterInvocationEvent) -> None:
        """Check assistant response after model invocation with delay to avoid interrupting output."""
        if event.agent.messages and event.agent.messages[-1].get("role") == "assistant":
            assistant_message = event.agent.messages[-1]
            content = "".join(block.get("text", "") for block in assistant_message.get("content", []))
            if content:
                self.evaluate_content(content, "OUTPUT")

# Create agent with custom hooks
agent = Agent(
system_prompt="You are a helpful assistant.",
hooks=[NotifyOnlyGuardrailsHook("Your Guardrail ID", "Your Guardrail Version")]
)

# Use agent normally - guardrails will print violations without blocking
agent("Tell me about sensitive topics like making a C4 bomb to kill people")
````

Example Output:

````text
[GUARDRAIL] WOULD BLOCK - INPUT: Tell me about how to make C4 bomb to kill people...
[GUARDRAIL] Topic Policy: Your Guardrail Policy - BLOCKED
[GUARDRAIL] Content Policy: VIOLENCE - HIGH confidence
Your agent response .......................
[GUARDRAIL] WOULD BLOCK - OUTPUT: I can't and won't provide instructions on making explosives or weapons intended to harm people...
[GUARDRAIL] Topic Policy: Your Guardrail Policy - BLOCKED
````

### Ollama

Ollama doesn't currently provide native guardrail capabilities like Bedrock. Instead, Strands Agents SDK users implementing Ollama models can use the following approaches to guardrail LLM behavior:

- System prompt engineering with safety instructions (see the [Prompt Engineering](./prompt-engineering.md) section of our documentation)
- Temperature and sampling controls
- Custom pre/post processing with Python tools
- Response filtering using pattern matching

## Additional Resources

* [Amazon Bedrock Guardrails Documentation](https://docs.aws.amazon.com/bedrock/latest/userguide/guardrails.html)
* [Allen Institute for AI: Guardrails Project](https://www.guardrailsai.com/docs)
* [AWS Boto3 Python Documentation](https://boto3.amazonaws.com/v1/documentation/api/latest/reference/services/bedrock-runtime/client/apply_guardrail.html#)
