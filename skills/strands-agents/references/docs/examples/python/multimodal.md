# Multi-modal - Strands Agents for Image Generation and Evaluation

This [example][example_code] demonstrates how to create a multi-agent system for generating and evaluating images. It shows how Strands agents can work with multimodal content through a workflow between specialized agents.

## Overview

| Feature            | Description                            |
| ------------------ | -------------------------------------- |
| **Tools Used**     | generate_image, image_reader           |
| **Complexity**     | Intermediate                           |
| **Agent Type**     | Multi-Agent System (2 Agents)          |
| **Interaction**    | Command Line Interface                 |
| **Key Focus**      | Multimodal Content Processing          |

## Tool Overview

The multimodal example utilizes two tools to work with image content.

1. The [`generate_image`](https://github.com/strands-agents/tools/blob/main/src/strands_tools/generate_image.py) tool enables the creation of images based on text prompts, allowing the agent to generate visual content from textual descriptions.
2. The [`image_reader`](https://github.com/strands-agents/tools/blob/main/src/strands_tools/image_reader.py) tool provides the capability to analyze and interpret image content, enabling the agent to "see" and describe what's in the images.

Together, these tools create a complete pipeline for both generating and evaluating visual content through natural language interactions.

## Code Structure and Implementation

### Agent Initialization

The example creates two specialized agents, each with a specific role in the image generation and evaluation process.

```python
from strands import Agent, tool
from strands_tools import generate_image, image_reader

# Artist agent that generates images based on prompts
artist = Agent(tools=[generate_image],system_prompt=(
    "You will be instructed to generate a number of images of a given subject. Vary the prompt for each generated image to create a variety of options."
    "Your final output must contain ONLY a comma-separated list of the filesystem paths of generated images."
))

# Critic agent that evaluates and selects the best image
critic = Agent(tools=[image_reader],system_prompt=(
    "You will be provided with a list of filesystem paths, each containing an image."
    "Describe each image, and then choose which one is best."
    "Your final line of output must be as follows:"
    "FINAL DECISION: <path to final decision image>"
))
```

### Using the Multimodal Agents

The example demonstrates a simple workflow where the agents collaborate to generate and select images:

```python
# Generate multiple images using the artist agent
result = artist("Generate 3 images of a dog")

# Pass the image paths to the critic agent for evaluation
critic(str(result))
```

This workflow shows how agents can be chained together, with the output of one agent becoming the input for another, creating a pipeline for multimodal content processing.

## Key Features and Capabilities

### 1. Image Generation

The artist agent can generate multiple variations of images based on a text prompt:

- **Basic Generation**:
  ```
  Generate 3 images of a dog
  ```

- **Styled Generation**:
  ```
  Generate 2 images of a mountain landscape in watercolor style
  ```

- **Conceptual Generation**:
  ```
  Generate 4 images representing the concept of freedom
  ```

### 2. Image Evaluation

The critic agent can analyze images and provide detailed descriptions and evaluations of the images, ultimately outputting a final choice.

### Example Command and Results

**Command**:

```
Generate 3 images of a whale
```

**Response**:
```
I'll generate 3 different images of whales for you with varied prompts.
Tool #1: generate_image

Tool #2: generate_image

Tool #3: generate_image
output/a_majestic_blue_whale_swimming.png, output/humpback_whale_breaching_from_the.png, output/orca_whale_pod_swimming_together.png

I'll describe each of these whale images and determine which is best. Let me examine them one by one.
Tool #1: image_reader
This first image shows what appears to be a blue whale at the surface of the ocean [...]
Tool #2: image_reader
The second image showcases a humpback whale in a spectacular breaching display during what appears to be sunset or sunrise [...]
Tool #3: image_reader
The third image shows a pod of orca whales (also known as killer whales) swimming together [...]

Comparison and final decision:

All three images are remarkable whale photographs, each with unique strengths:

1. The blue whale image offers an intimate, close-up perspective with beautiful atmospheric lighting and a serene mood.

2. The humpback whale breaching image captures a dynamic, powerful moment with spectacular sunset colors creating an extraordinary visual impact.

3. The orca pod image showcases multiple whales in their social grouping against a dramatic arctic backdrop, emphasizing their habitat and community.

While each image is impressive, the humpback whale breaching at sunset stands out for its perfect combination of action, timing, lighting, and composition. The contrast between the dark whale and the golden sky, the dynamic motion captured at precisely the right moment, and the breathtaking sunset setting make this image particularly remarkable.

FINAL DECISION: output/humpback_whale_breaching_from_the.png
```

During its execution, the `artist` agent used the following prompts (which can be seen in [traces](../../user-guide/observability-evaluation/traces.md) or [logs](../../user-guide/observability-evaluation/logs.md)) to generate each image:

"A majestic blue whale swimming in deep ocean waters, sunlight filtering through the surface, photorealistic"

![output/a_majestic_blue_whale_swimming.png](../../assets/multimodal/whale_1.png)

"Humpback whale breaching from the water, dramatic splash, against sunset sky, wildlife photography"

![output/humpback_whale_breaching_from_the.png](../../assets/multimodal/whale_2.png)

"Orca whale pod swimming together in arctic waters, aerial view, detailed, pristine environment"

![output/orca_whale_pod_swimming_together.png](../../assets/multimodal/whale_3.png)

And the `critic` agent selected the humpback whale as the best image:

![output/humpback_whale_breaching_from_the.png](../../assets/multimodal/whale_2_large.png)


## Extending the Example

Here are some ways you could extend this example:

1. **Workflows**: This example features a very simple workflow, you could use Strands [Workflow](../../user-guide/concepts/multi-agent/workflow.md) capabilities for more elaborate media production pipelines.
2. **Image Editing**: Extend the `generate_image` tool to accept and modify input images.
3. **User Feedback Loop**: Allow users to provide feedback on the selection to improve future generations
4. **Integration with Other Media**: Extend the system to work with other media types, such as video with Amazon Nova models.

[example_code]: {{ docs_repo }}/docs/examples/python/multimodal.py