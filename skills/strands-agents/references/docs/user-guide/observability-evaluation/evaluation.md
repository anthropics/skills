# Evaluation

This guide covers approaches to evaluating agents. Effective evaluation is essential for measuring agent performance, tracking improvements, and ensuring your agents meet quality standards.

When building AI agents, evaluating their performance is crucial during this process. It's important to consider various qualitative and quantitative factors, including response quality, task completion, success, and inaccuracies or hallucinations. In evaluations, it's also important to consider comparing different agent configurations to optimize for specific desired outcomes. Given the dynamic and non-deterministic nature of LLMs, it's also important to have rigorous and frequent evaluations to ensure a consistent baseline for tracking improvements or regressions. 


## Creating Test Cases

### Basic Test Case Structure

```json
[
  {
    "id": "knowledge-1",
    "query": "What is the capital of France?",
    "expected": "The capital of France is Paris.",
    "category": "knowledge"
  },
  {
    "id": "calculation-1",
    "query": "Calculate the total cost of 5 items at $12.99 each with 8% tax.",
    "expected": "The total cost would be $70.15.",
    "category": "calculation"
  }
]
```

### Test Case Categories

When developing your test cases, consider building a diverse suite that spans multiple categories. 

Some common categories to consider include:
1. **Knowledge Retrieval** - Facts, definitions, explanations
2. **Reasoning** - Logic problems, deductions, inferences
3. **Tool Usage** - Tasks requiring specific tool selection
4. **Conversation** - Multi-turn interactions
5. **Edge Cases** - Unusual or boundary scenarios
6. **Safety** - Handling of sensitive topics

## Metrics to Consider

Evaluating agent performance requires tracking multiple dimensions of quality; consider tracking these metrics in addition to any domain-specific metrics for your industry or use case:

1. **Accuracy** - Factual correctness of responses
2. **Task Completion** - Whether the agent successfully completed the tasks
3. **Tool Selection** - Appropriateness of tool choices
4. **Response Time** - How long the agent took to respond
5. **Hallucination Rate** - Frequency of fabricated information
6. **Token Usage** - Efficiency of token consumption
7. **User Satisfaction** - Subjective ratings of helpfulness

## Continuous Evaluation

Implementing a continuous evaluation strategy is crucial for ongoing success and improvements. It's crucial to establish baseline testing for initial performance tracking and comparisons for improvements. Some important things to note about establishing a baseline: given LLMs are non-deterministic, the same question asked 10 times could yield different responses. So it's important to establish statistically significant baselines to compare.
Once a clear baseline is established, this can be used to identify regressions as well as longitudinal analysis to track performance over time.


## Evaluation Approaches

### Manual Evaluation

The simplest approach is direct manual testing:

```python
from strands import Agent
from strands_tools import calculator

# Create agent with specific configuration
agent = Agent(
    model="us.anthropic.claude-sonnet-4-20250514-v1:0",
    system_prompt="You are a helpful assistant specialized in data analysis.",
    tools=[calculator]
)

# Test with specific queries
response = agent("Analyze this data and create a summary: [Item, Cost 2024, Cost 2025\n Apple, $0.47, $0.55, Banana, $0.13, $0.47\n]")
print(str(response))

# Manually analyze the response for quality, accuracy, and task completion
```

### Structured Testing

Create a more structured testing framework with predefined test cases:

```python
from strands import Agent
import json
import pandas as pd

# Load test cases from JSON file
with open("test_cases.json", "r") as f:
    test_cases = json.load(f)

# Create agent
agent = Agent(model="us.anthropic.claude-sonnet-4-20250514-v1:0")

# Run tests and collect results
results = []
for case in test_cases:
    query = case["query"]
    expected = case.get("expected")

    # Execute the agent query
    response = agent(query)

    # Store results for analysis
    results.append({
        "test_id": case.get("id", ""),
        "query": query,
        "expected": expected,
        "actual": str(response),
        "timestamp": pd.Timestamp.now()
    })

# Export results for review
results_df = pd.DataFrame(results)
results_df.to_csv("evaluation_results.csv", index=False)
# Example output:
# |test_id    |query                         |expected                       |actual                          |timestamp                 |
# |-----------|------------------------------|-------------------------------|--------------------------------|--------------------------|
# |knowledge-1|What is the capital of France?|The capital of France is Paris.|The capital of France is Paris. |2025-05-13 18:37:22.673230|
#

```

### LLM Judge Evaluation

Leverage another LLM to evaluate your agent's responses:

```python
from strands import Agent
import json

# Create the agent to evaluate
agent = Agent(model="anthropic.claude-3-5-sonnet-20241022-v2:0")

# Create an evaluator agent with a stronger model
evaluator = Agent(
    model="us.anthropic.claude-sonnet-4-20250514-v1:0",
    system_prompt="""
    You are an expert AI evaluator. Your job is to assess the quality of AI responses based on:
    1. Accuracy - factual correctness of the response
    2. Relevance - how well the response addresses the query
    3. Completeness - whether all aspects of the query are addressed
    4. Tool usage - appropriate use of available tools

    Score each criterion from 1-5, where 1 is poor and 5 is excellent.
    Provide an overall score and brief explanation for your assessment.
    """
)

# Load test cases
with open("test_cases.json", "r") as f:
    test_cases = json.load(f)

# Run evaluations
evaluation_results = []
for case in test_cases:
    # Get agent response
    agent_response = agent(case["query"])

    # Create evaluation prompt
    eval_prompt = f"""
    Query: {case['query']}

    Response to evaluate:
    {agent_response}

    Expected response (if available):
    {case.get('expected', 'Not provided')}

    Please evaluate the response based on accuracy, relevance, completeness, and tool usage.
    """

    # Get evaluation
    evaluation = evaluator(eval_prompt)

    # Store results
    evaluation_results.append({
        "test_id": case.get("id", ""),
        "query": case["query"],
        "agent_response": str(agent_response),
        "evaluation": evaluation.message['content']
    })

# Save evaluation results
with open("evaluation_results.json", "w") as f:
    json.dump(evaluation_results, f, indent=2)
```

### Tool-Specific Evaluation

For agents using tools, evaluate their ability to select and use appropriate tools:

```python
from strands import Agent
from strands_tools import calculator, file_read, current_time
# Create agent with multiple tools
agent = Agent(
    model="us.anthropic.claude-sonnet-4-20250514-v1:0",
    tools=[calculator, file_read, current_time],
    record_direct_tool_call = True
)

# Define tool-specific test cases
tool_test_cases = [
    {"query": "What is 15% of 230?", "expected_tool": "calculator"},
    {"query": "Read the content of data.txt", "expected_tool": "file_read"},
    {"query": "Get the time in Seattle", "expected_tool": "current_time"},
]

# Track tool usage
tool_usage_results = []
for case in tool_test_cases:
    response = agent(case["query"])

    # Extract used tools from the response metrics
    used_tools = []
    if hasattr(response, 'metrics') and hasattr(response.metrics, 'tool_metrics'):
        for tool_name, tool_metric in response.metrics.tool_metrics.items():
            if tool_metric.call_count > 0:
                used_tools.append(tool_name)

    tool_usage_results.append({
        "query": case["query"],
        "expected_tool": case["expected_tool"],
        "used_tools": used_tools,
        "correct_tool_used": case["expected_tool"] in used_tools
    })

# Analyze tool usage accuracy
correct_usage_count = sum(1 for result in tool_usage_results if result["correct_tool_used"])
accuracy = correct_usage_count / len(tool_usage_results)
print('\n Results:\n')
print(f"Tool selection accuracy: {accuracy:.2%}")
```

## Example: Building an Evaluation Workflow

Below is a simplified example of a comprehensive evaluation workflow:

```python
from strands import Agent
import json
import pandas as pd
import matplotlib.pyplot as plt
import datetime
import os


class AgentEvaluator:
    def __init__(self, test_cases_path, output_dir="evaluation_results"):
        """Initialize evaluator with test cases"""
        with open(test_cases_path, "r") as f:
            self.test_cases = json.load(f)

        self.output_dir = output_dir
        os.makedirs(output_dir, exist_ok=True)

    def evaluate_agent(self, agent, agent_name):
        """Run evaluation on an agent"""
        results = []
        start_time = datetime.datetime.now()

        print(f"Starting evaluation of {agent_name} at {start_time}")

        for case in self.test_cases:
            case_start = datetime.datetime.now()
            response = agent(case["query"])
            case_duration = (datetime.datetime.now() - case_start).total_seconds()

            results.append({
                "test_id": case.get("id", ""),
                "category": case.get("category", ""),
                "query": case["query"],
                "expected": case.get("expected", ""),
                "actual": str(response),
                "response_time": case_duration
            })

        total_duration = (datetime.datetime.now() - start_time).total_seconds()

        # Save raw results
        timestamp = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
        results_path = os.path.join(self.output_dir, f"{agent_name}_{timestamp}.json")
        with open(results_path, "w") as f:
            json.dump(results, f, indent=2)

        print(f"Evaluation completed in {total_duration:.2f} seconds")
        print(f"Results saved to {results_path}")

        return results

    def analyze_results(self, results, agent_name):
        """Generate analysis of evaluation results"""
        df = pd.DataFrame(results)

        # Calculate metrics
        metrics = {
            "total_tests": len(results),
            "avg_response_time": df["response_time"].mean(),
            "max_response_time": df["response_time"].max(),
            "categories": df["category"].value_counts().to_dict()
        }

        # Generate charts
        plt.figure(figsize=(10, 6))
        df.groupby("category")["response_time"].mean().plot(kind="bar")
        plt.title(f"Average Response Time by Category - {agent_name}")
        plt.ylabel("Seconds")
        plt.tight_layout()

        chart_path = os.path.join(self.output_dir, f"{agent_name}_response_times.png")
        plt.savefig(chart_path)

        return metrics


# Usage example
if __name__ == "__main__":
    # Create agents with different configurations
    agent1 = Agent(
        model="anthropic.claude-3-5-sonnet-20241022-v2:0",
        system_prompt="You are a helpful assistant."
    )

    agent2 = Agent(
        model="anthropic.claude-3-5-haiku-20241022-v1:0",
        system_prompt="You are a helpful assistant."
    )

    # Create evaluator
    evaluator = AgentEvaluator("test_cases.json")

    # Evaluate agents
    results1 = evaluator.evaluate_agent(agent1, "claude-sonnet")
    metrics1 = evaluator.analyze_results(results1, "claude-sonnet")

    results2 = evaluator.evaluate_agent(agent2, "claude-haiku")
    metrics2 = evaluator.analyze_results(results2, "claude-haiku")

    # Compare results
    print("\nPerformance Comparison:")
    print(f"Sonnet avg response time: {metrics1['avg_response_time']:.2f}s")
    print(f"Haiku avg response time: {metrics2['avg_response_time']:.2f}s")
```


## Best Practices

### Evaluation Strategy

1. **Diversify test cases** - Cover a wide range of scenarios and edge cases
2. **Use control questions** - Include questions with known answers to validate evaluation
3. **Blind evaluations** - When using human evaluators, avoid biasing them with expected answers
4. **Regular cadence** - Implement a consistent evaluation schedule 

### Using Evaluation Results

1. **Iterative improvement** - Use results to inform agent refinements
2. **System prompt engineering** - Adjust prompts based on identified weaknesses
3. **Tool selection optimization** - Improve tool names, descriptions, and tool selection strategies
4. **Version control** - Track agent configurations alongside evaluation results
