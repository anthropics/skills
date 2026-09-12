# PII Redaction 
PII redaction is a critical aspect of protecting personal information. This document provides clear instructions and recommended practices for safely handling PII, including guidance on integrating third-party redaction solutions with Strands SDK.

## What is PII Redaction
Personally Identifiable Information (PII) is defined as: Information that can be used to distinguish or trace an individual’s identity, either alone or when combined with other information that is linked or linkable to a specific individual.

PII Redaction is the process of identifying, removing, or obscuring sensitive information from telemetry data before storage or transmission to prevent potential privacy violations and to ensure regulatory compliance.

## Why do you need PII redaction?
Integrating PII redaction is crucial for:

* **Privacy Compliance**: Protecting users' sensitive information and ensuring compliance with global data privacy regulations.

* **Security: Reducing**: the risk of data breaches and unauthorized exposure of personal information.

* **Operational Safety**: Maintaining safe data handling practices within applications and observability platforms.

## How to implement PII Redaction

Strands SDK does not natively perform PII redaction within its core telemetry generation but recommends two effective ways to achieve PII masking:

### Option 1: Using Third-Party Specialized Libraries [Recommended]
Leverage specialized external libraries like Langfuse, LLM Guard, Presidio, or AWS Comprehend for high-quality PII detection and redaction:

#### Step-by-Step Integration Guide

##### Step 1: Install your chosen PII Redaction Library.
Example with [LLM Guard](https://protectai.com/llm-guard):

````bash
pip install llm-guard
````

##### Step 2: Import necessary modules and initialize the Vault and Anonymize scanner.

```python
from llm_guard.vault import Vault
from llm_guard.input_scanners import Anonymize
from llm_guard.input_scanners.anonymize_helpers import BERT_LARGE_NER_CONF

vault = Vault()

# Create anonymize scanner
def create_anonymize_scanner():
    scanner = Anonymize(
        vault,
        recognizer_conf=BERT_LARGE_NER_CONF,
        language="en"
    )
    return scanner
```
##### Step 3: Define a masking function using the anonymize scanner.

```python
def masking_function(data, **kwargs):
    if isinstance(data, str):
        scanner = create_anonymize_scanner()
        # Scan and redact the data
        sanitized_data, is_valid, risk_score = scanner.scan(data)
        return sanitized_data
    return data
```

##### Step 4: Configure the masking function in Observability platform, eg., Langfuse.

```python
from langfuse import Langfuse

langfuse = Langfuse(mask=masking_function)
```

##### Step 5: Create a sample function with PII.

```python
from langfuse import observe
@observe()
def generate_report():
    report = "John Doe met with Jane Smith to discuss the project."
    return report

result = generate_report()
print(result)
# Output: [REDACTED_PERSON] met with [REDACTED_PERSON] to discuss the project.

langfuse.flush()
```

#### Complete example with a Strands agent

```python
from strands import Agent
from llm_guard.vault import Vault
from llm_guard.input_scanners import Anonymize
from llm_guard.input_scanners.anonymize_helpers import BERT_LARGE_NER_CONF
from langfuse import Langfuse, observe

vault = Vault()

def create_anonymize_scanner():
    """Creates a reusable anonymize scanner."""
    return Anonymize(vault, recognizer_conf=BERT_LARGE_NER_CONF, language="en")

def masking_function(data, **kwargs):
    """Langfuse masking function to recursively redact PII."""
    if isinstance(data, str):
        scanner = create_anonymize_scanner()
        sanitized_data, _, _ = scanner.scan(data)
        return sanitized_data
    elif isinstance(data, dict):
        return {k: masking_function(v) for k, v in data.items()}
    elif isinstance(data, list):
        return [masking_function(item) for item in data]
    return data

langfuse = Langfuse(mask=masking_function)


class CustomerSupportAgent:
    def __init__(self):
        self.agent = Agent(
            system_prompt="You are a helpful customer service agent. Respond professionally to customer inquiries."
        )

    @observe
    def process_sanitized_message(self, sanitized_payload):
        """Processes a pre-sanitized payload and expects sanitized input."""
        sanitized_content = sanitized_payload.get("prompt", "empty input")

        conversation = f"Customer: {sanitized_content}"

        response = self.agent(conversation)
        return response


def process():
    support_agent = CustomerSupportAgent()
    scanner = create_anonymize_scanner()

    raw_payload = {
        "prompt": "Hi, I'm Jonny Test. My phone number is 123-456-7890 and my email is john@example.com. I need help with my order #123456789."
    }

    sanitized_prompt, _, _ = scanner.scan(raw_payload["prompt"])
    sanitized_payload = {"prompt": sanitized_prompt}

    response = support_agent.process_sanitized_message(sanitized_payload)

    print(f"Response: {response}")
    langfuse.flush()
    
    #Example input: prompt:
        # "Hi, I'm [REDACTED_PERSON_1]. My phone number is [REDACTED_PHONE_NUMBER_1] and my email is [REDACTED_EMAIL_ADDRESS_1]. I need help with my order #123456789."
    #Example output: 
        # #Hello! I'd be happy to help you with your order #123456789. 
        # To better assist you, could you please let me know what specific issue you're experiencing with this order? For example:
        # - Are you looking for a status update?
        # - Need to make changes to the order?
        # - Having delivery issues?
        # - Need to process a return or exchange?
        # 
        # Once I understand what you need help with, I'll be able to provide you with the most relevant assistance."

if __name__ == "__main__":
    process()
```

### Option 2: Using OpenTelemetry Collector Configuration [Collector-level Masking]
Implement PII masking directly at the collector level, which is ideal for centralized control.

#### Example code:
1. Edit your collector configuration (eg., otel-collector-config.yaml):

```yaml
processors:
  attributes/pii:
    actions:
      - key: user.email
        action: delete
      - key: http.url
        regex: '(\?|&)(token|password)=([^&]+)'
        action: update
        value: '[REDACTED]'

service:
  pipelines:
    traces:
      processors: [attributes/pii]
```

2. Deploy or restart your OTEL collector with the updated configuration.

#### Example:

##### Before:

```json
{
  "user.email": "user@example.com",
  "http.url": "https://example.com?token=abc123"
}
```

#### After:

```json
{
  "http.url": "https://example.com?token=[REDACTED]"
}
```

## Additional Resources
* [PII definition](https://www.dol.gov/general/ppii)
* [OpenTelemetry official docs](https://opentelemetry.io/docs/collector/transforming-telemetry/)
* [LLM Guard](https://protectai.com/llm-guard)