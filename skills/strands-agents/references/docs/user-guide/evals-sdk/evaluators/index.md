# Evaluators

## Overview

Evaluators assess the quality and performance of conversational agents by analyzing their outputs, behaviors, and goal achievement. The Strands Evals SDK provides a comprehensive set of evaluators that can assess different aspects of agent performance, from individual response quality to multi-turn conversation success.

## Why Evaluators?

Evaluating conversational agents requires more than simple accuracy metrics. Agents must be assessed across multiple dimensions:

**Traditional Metrics:**

- Limited to exact match or similarity scores
- Don't capture subjective qualities like helpfulness
- Can't assess multi-turn conversation flow
- Miss goal-oriented success patterns

**Strands Evaluators:**

- Assess subjective qualities using LLM-as-a-judge
- Evaluate multi-turn conversations and trajectories
- Measure goal completion and user satisfaction
- Provide structured reasoning for evaluation decisions
- Support both synchronous and asynchronous evaluation

## When to Use Evaluators

Use evaluators when you need to:

- **Assess Response Quality**: Evaluate helpfulness, faithfulness, and appropriateness
- **Measure Goal Achievement**: Determine if user objectives were met
- **Analyze Tool Usage**: Evaluate tool selection and parameter accuracy
- **Track Conversation Success**: Assess multi-turn interaction effectiveness
- **Compare Agent Configurations**: Benchmark different prompts or models
- **Monitor Production Performance**: Continuously evaluate deployed agents

## Evaluation Levels

Evaluators operate at different levels of granularity:

| Level | Scope | Use Case |
|-------|-------|----------|
| **OUTPUT_LEVEL** | Single response | Quality of individual outputs |
| **TRACE_LEVEL** | Single turn | Turn-by-turn conversation analysis |
| **SESSION_LEVEL** | Full conversation | End-to-end goal achievement |

## Built-in Evaluators

### Response Quality Evaluators

**[OutputEvaluator](output_evaluator.md)**

- **Level**: OUTPUT_LEVEL
- **Purpose**: Flexible LLM-based evaluation with custom rubrics
- **Use Case**: Assess any subjective quality (safety, relevance, tone)

**[HelpfulnessEvaluator](helpfulness_evaluator.md)**

- **Level**: TRACE_LEVEL  
- **Purpose**: Evaluate response helpfulness from user perspective
- **Use Case**: Measure user satisfaction and response utility

**[FaithfulnessEvaluator](faithfulness_evaluator.md)**

- **Level**: TRACE_LEVEL
- **Purpose**: Assess factual accuracy and groundedness
- **Use Case**: Verify responses are truthful and well-supported

### Tool Usage Evaluators

**[ToolSelectionEvaluator](tool_selection_evaluator.md)**

- **Level**: TRACE_LEVEL
- **Purpose**: Evaluate whether correct tools were selected
- **Use Case**: Assess tool choice accuracy in multi-tool scenarios

**[ToolParameterEvaluator](tool_parameter_evaluator.md)**

- **Level**: TRACE_LEVEL
- **Purpose**: Evaluate accuracy of tool parameters
- **Use Case**: Verify correct parameter values for tool calls

### Conversation Flow Evaluators

**[TrajectoryEvaluator](trajectory_evaluator.md)**

- **Level**: SESSION_LEVEL
- **Purpose**: Assess sequence of actions and tool usage patterns
- **Use Case**: Evaluate multi-step reasoning and workflow adherence

**[InteractionsEvaluator](interactions_evaluator.md)**

- **Level**: SESSION_LEVEL
- **Purpose**: Analyze conversation patterns and interaction quality
- **Use Case**: Assess conversation flow and engagement patterns

### Goal Achievement Evaluators

**[GoalSuccessRateEvaluator](goal_success_rate_evaluator.md)**

- **Level**: SESSION_LEVEL
- **Purpose**: Determine if user goals were successfully achieved
- **Use Case**: Measure end-to-end task completion success

## Custom Evaluators

Create domain-specific evaluators by extending the base `Evaluator` class:

**[CustomEvaluator](custom_evaluator.md)**

- **Purpose**: Implement specialized evaluation logic
- **Use Case**: Domain-specific requirements not covered by built-in evaluators

## Evaluators vs Simulators

Understanding when to use evaluators versus simulators:

| Aspect | Evaluators | Simulators |
|--------|-----------|-----------|
| **Role** | Assess quality | Generate interactions |
| **Timing** | Post-conversation | During conversation |
| **Purpose** | Score/judge | Drive/participate |
| **Output** | Evaluation scores | Conversation turns |
| **Use Case** | Quality assessment | Interaction generation |

**Use Together:**
Evaluators and simulators complement each other. Use simulators to generate realistic multi-turn conversations, then use evaluators to assess the quality of those interactions.

## Integration with Simulators

Evaluators work seamlessly with simulator-generated conversations:

!!! warning "Required: Session ID Trace Attributes"
    When using `StrandsInMemorySessionMapper`, you **must** include session ID trace attributes in your agent configuration. This prevents spans from different test cases from being mixed together in the memory exporter.

```python
from strands import Agent
from strands_evals import Case, Experiment, ActorSimulator
from strands_evals.evaluators import HelpfulnessEvaluator, GoalSuccessRateEvaluator
from strands_evals.mappers import StrandsInMemorySessionMapper
from strands_evals.telemetry import StrandsEvalsTelemetry

def task_function(case: Case) -> dict:
    # Generate multi-turn conversation with simulator
    simulator = ActorSimulator.from_case_for_user_simulator(case=case, max_turns=10)
    agent = Agent(trace_attributes={"session.id": case.session_id})
    
    # Collect conversation data
    all_spans = []
    user_message = case.input
    
    while simulator.has_next():
        agent_response = agent(user_message)
        turn_spans = list(memory_exporter.get_finished_spans())
        all_spans.extend(turn_spans)
        
        user_result = simulator.act(str(agent_response))
        user_message = str(user_result.structured_output.message)
    
    # Map to session for evaluation
    mapper = StrandsInMemorySessionMapper()
    session = mapper.map_to_session(all_spans, session_id=case.session_id)
    
    return {"output": str(agent_response), "trajectory": session}

# Use multiple evaluators to assess different aspects
evaluators = [
    HelpfulnessEvaluator(),           # Response quality
    GoalSuccessRateEvaluator(),       # Goal achievement
    ToolSelectionEvaluator(),         # Tool usage
    TrajectoryEvaluator(rubric="...") # Action sequences
]

experiment = Experiment(cases=test_cases, evaluators=evaluators)
reports = experiment.run_evaluations(task_function)
```

## Best Practices

### 1. Choose Appropriate Evaluation Levels

Match evaluator level to your assessment needs:

```python
# For individual response quality
evaluators = [OutputEvaluator(rubric="Assess response clarity")]

# For turn-by-turn analysis  
evaluators = [HelpfulnessEvaluator(), FaithfulnessEvaluator()]

# For end-to-end success
evaluators = [GoalSuccessRateEvaluator(), TrajectoryEvaluator(rubric="...")]
```

### 2. Combine Multiple Evaluators

Assess different aspects comprehensively:

```python
evaluators = [
    HelpfulnessEvaluator(),      # User experience
    FaithfulnessEvaluator(),     # Accuracy
    ToolSelectionEvaluator(),    # Tool usage
    GoalSuccessRateEvaluator()   # Success rate
]
```

### 3. Use Clear Rubrics

For custom evaluators, define specific criteria:

```python
rubric = """
Score 1.0 if the response:
- Directly answers the user's question
- Provides accurate information
- Uses appropriate tone

Score 0.5 if the response partially meets criteria
Score 0.0 if the response fails to meet criteria
"""

evaluator = OutputEvaluator(rubric=rubric)
```

### 4. Leverage Async Evaluation

For better performance with multiple evaluators:

```python
import asyncio

async def run_evaluations():
    evaluators = [HelpfulnessEvaluator(), FaithfulnessEvaluator()]
    tasks = [evaluator.aevaluate(data) for evaluator in evaluators]
    results = await asyncio.gather(*tasks)
    return results
```

## Common Patterns

### Pattern 1: Quality Assessment Pipeline

```python
def assess_response_quality(case: Case, agent_output: str) -> dict:
    evaluators = [
        HelpfulnessEvaluator(),
        FaithfulnessEvaluator(),
        OutputEvaluator(rubric="Assess professional tone")
    ]
    
    results = {}
    for evaluator in evaluators:
        result = evaluator.evaluate(EvaluationData(
            input=case.input,
            output=agent_output
        ))
        results[evaluator.__class__.__name__] = result.score
    
    return results
```

### Pattern 2: Tool Usage Analysis

```python
def analyze_tool_usage(session: Session) -> dict:
    evaluators = [
        ToolSelectionEvaluator(),
        ToolParameterEvaluator(),
        TrajectoryEvaluator(rubric="Assess tool usage efficiency")
    ]
    
    results = {}
    for evaluator in evaluators:
        result = evaluator.evaluate(EvaluationData(trajectory=session))
        results[evaluator.__class__.__name__] = {
            "score": result.score,
            "reasoning": result.reasoning
        }
    
    return results
```

### Pattern 3: Comparative Evaluation

```python
def compare_agent_versions(cases: list, agents: dict) -> dict:
    evaluators = [HelpfulnessEvaluator(), GoalSuccessRateEvaluator()]
    results = {}
    
    for agent_name, agent in agents.items():
        agent_scores = []
        for case in cases:
            output = agent(case.input)
            for evaluator in evaluators:
                result = evaluator.evaluate(EvaluationData(
                    input=case.input,
                    output=output
                ))
                agent_scores.append(result.score)
        
        results[agent_name] = {
            "average_score": sum(agent_scores) / len(agent_scores),
            "scores": agent_scores
        }
    
    return results
```

## Next Steps

- [OutputEvaluator](output_evaluator.md): Start with flexible custom evaluation
- [HelpfulnessEvaluator](helpfulness_evaluator.md): Assess response helpfulness
- [CustomEvaluator](custom_evaluator.md): Create domain-specific evaluators

## Related Documentation

- [Quickstart Guide](../quickstart.md): Get started with Strands Evals
- [Simulators Overview](../simulators/index.md): Learn about simulators
- [Experiment Generator](../experiment_generator.md): Generate test cases automatically
