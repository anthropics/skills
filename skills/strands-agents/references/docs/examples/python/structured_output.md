# Structured Output Example

This example demonstrates how to use Strands' structured output feature to get type-safe, validated responses from language models using [Pydantic](https://docs.pydantic.dev/latest/concepts/models/) models. Instead of raw text that you need to parse manually, you define the exact structure you want and receive a validated Python object.

## What You'll Learn

- How to define Pydantic models for structured output
- Extracting structured information from text
- Using conversation history with structured output
- Working with complex nested models

## Code Example

The example covers four key use cases:

1. Basic structured output
2. Using existing conversation context
3. Working with complex nested models

```python
#!/usr/bin/env python3
"""
Structured Output Example

This example demonstrates how to use structured output with Strands Agents to
get type-safe, validated responses using Pydantic models.
"""
import asyncio
import tempfile
from typing import List, Optional
from pydantic import BaseModel, Field
from strands import Agent

def basic_example():
    """Basic example extracting structured information from text."""
    print("\n--- Basic Example ---")

    class PersonInfo(BaseModel):
        name: str
        age: int
        occupation: str

    agent = Agent()
    result = agent.structured_output(
        PersonInfo,
        "John Smith is a 30-year-old software engineer"
    )

    print(f"Name: {result.name}")      # "John Smith"
    print(f"Age: {result.age}")        # 30
    print(f"Job: {result.occupation}") # "software engineer"


def multimodal_example():
    """Basic example extracting structured information from a document."""
    print("\n--- Multi-Modal Example ---")

    class PersonInfo(BaseModel):
        name: str
        age: int
        occupation: str

    with tempfile.NamedTemporaryFile(delete=False) as person_file:
        person_file.write(b"John Smith is a 30-year old software engineer")
        person_file.flush()

        with open(person_file.name, "rb") as fp:
            document_bytes = fp.read()

    agent = Agent()
    result = agent.structured_output(
        PersonInfo,
        [
            {"text": "Please process this application."},
            {
                "document": {
                    "format": "txt",
                    "name": "application",
                    "source": {
                        "bytes": document_bytes,
                    },
                },
            },
        ]
    )

    print(f"Name: {result.name}")      # "John Smith"
    print(f"Age: {result.age}")        # 30
    print(f"Job: {result.occupation}") # "software engineer"


def conversation_history_example():
    """Example using conversation history with structured output."""
    print("\n--- Conversation History Example ---")

    agent = Agent()

    # Build up conversation context
    print("Building conversation context...")
    agent("What do you know about Paris, France?")
    agent("Tell me about the weather there in spring.")

    # Extract structured information with a prompt
    class CityInfo(BaseModel):
        city: str
        country: str
        population: Optional[int] = None
        climate: str

    # Uses existing conversation context with a prompt
    print("Extracting structured information from conversation context...")
    result = agent.structured_output(CityInfo, "Extract structured information about Paris")

    print(f"City: {result.city}")
    print(f"Country: {result.country}")
    print(f"Population: {result.population}")
    print(f"Climate: {result.climate}")


def complex_nested_model_example():
    """Example handling complex nested data structures."""
    print("\n--- Complex Nested Model Example ---")

    class Address(BaseModel):
        street: str
        city: str
        country: str
        postal_code: Optional[str] = None

    class Contact(BaseModel):
        email: Optional[str] = None
        phone: Optional[str] = None

    class Person(BaseModel):
        """Complete person information."""
        name: str = Field(description="Full name of the person")
        age: int = Field(description="Age in years")
        address: Address = Field(description="Home address")
        contacts: List[Contact] = Field(default_factory=list, description="Contact methods")
        skills: List[str] = Field(default_factory=list, description="Professional skills")

    agent = Agent()
    result = agent.structured_output(
        Person,
        "Extract info: Jane Doe, a systems admin, 28, lives at 123 Main St, New York, USA. Email: jane@example.com"
    )

    print(f"Name: {result.name}")                    # "Jane Doe"
    print(f"Age: {result.age}")                      # 28
    print(f"Street: {result.address.street}")        # "123 Main St" 
    print(f"City: {result.address.city}")            # "New York"
    print(f"Country: {result.address.country}")      # "USA"
    print(f"Email: {result.contacts[0].email}")      # "jane@example.com"
    print(f"Skills: {result.skills}")                # ["systems admin"]


async def async_example():
    """Basic example extracting structured information from text asynchronously."""
    print("\n--- Async Example ---")

    class PersonInfo(BaseModel):
        name: str
        age: int
        occupation: str

    agent = Agent()
    result = await agent.structured_output_async(
        PersonInfo,
        "John Smith is a 30-year-old software engineer"
    )

    print(f"Name: {result.name}")      # "John Smith"
    print(f"Age: {result.age}")        # 30
    print(f"Job: {result.occupation}") # "software engineer"


if __name__ == "__main__":
    print("Structured Output Examples\n")

    basic_example()
    multimodal_example()
    conversation_history_example()
    complex_nested_model_example()
    asyncio.run(async_example())

    print("\nExamples completed.")
```

## How It Works

1. **Define a Schema**: Create a Pydantic model that defines the structure you want
2. **Call structured_output()**: Pass your model and optionally a prompt to the agent
   - If running async, call `structured_output_async()` instead.
3. **Get Validated Results**: Receive a properly typed Python object matching your schema

The `structured_output()` method ensures that the language model generates a response that conforms to your specified schema. It handles converting your Pydantic model into a format the model understands and validates the response.

## Key Benefits

- Type-safe responses with proper Python types
- Automatic validation against your schema
- IDE type hinting from LLM-generated responses
- Clear documentation of expected output
- Error prevention for malformed responses

## Learn More

For more details on structured output, see the [Structured Output documentation](../../user-guide/concepts/agents/structured-output.md).
