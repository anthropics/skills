# Simulators

## Overview

Simulators enable dynamic, multi-turn evaluation of conversational agents by generating realistic interaction patterns. Unlike static evaluators that assess single outputs, simulators actively participate in conversations, adapting their behavior based on agent responses to create authentic evaluation scenarios.

## Why Simulators?

Traditional evaluation approaches have limitations when assessing conversational agents:

**Static Evaluators:**

- Evaluate single input/output pairs
- Cannot test multi-turn conversation flow
- Miss context-dependent behaviors
- Don't capture goal-oriented interactions

**Simulators:**

- Generate dynamic, multi-turn conversations
- Adapt responses based on agent behavior
- Test goal completion in realistic scenarios
- Evaluate conversation flow and context maintenance
- Enable testing without predefined scripts

## When to Use Simulators

Use simulators when you need to:

- **Evaluate Multi-turn Conversations**: Test agents across multiple conversation turns
- **Assess Goal Completion**: Verify agents can achieve user objectives through dialogue
- **Test Conversation Flow**: Evaluate how agents handle context and follow-up questions
- **Generate Diverse Interactions**: Create varied conversation patterns automatically
- **Evaluate Without Scripts**: Test agents without predefined conversation paths
- **Simulate Real Users**: Generate realistic user behavior patterns

## ActorSimulator

The `ActorSimulator` is the core simulator class in Strands Evals. It's a general-purpose simulator that can simulate any type of actor in multi-turn conversations. An "actor" is any conversational participant - users, customer service representatives, domain experts, adversarial testers, or any other entity that engages in dialogue.

The simulator maintains actor profiles, generates contextually appropriate responses based on conversation history, and tracks goal completion. By configuring different actor profiles and system prompts, you can simulate diverse interaction patterns.

### User Simulation

The most common use of `ActorSimulator` is **user simulation** - simulating realistic end-users interacting with your agent during evaluation. This is the primary use case covered in our documentation.

[Complete User Simulation Guide →](user_simulation.md)

### Other Actor Types

While user simulation is the primary use case, `ActorSimulator` can simulate other actor types by providing custom actor profiles:

- **Customer Support Representatives**: Test agent-to-agent interactions
- **Domain Experts**: Simulate specialized knowledge conversations  
- **Adversarial Actors**: Test robustness and edge cases
- **Internal Staff**: Evaluate internal tooling workflows

## Extensibility

The simulator framework is designed to be extensible. While `ActorSimulator` provides a general-purpose foundation, additional specialized simulators can be built for specific evaluation patterns as needs emerge.

## Simulators vs Evaluators

Understanding when to use simulators versus evaluators:

| Aspect | Evaluators | Simulators |
|--------|-----------|-----------|
| **Interaction** | Passive assessment | Active participation |
| **Turns** | Single turn | Multi-turn |
| **Adaptation** | Static criteria | Dynamic responses |
| **Use Case** | Output quality | Conversation flow |
| **Goal** | Score responses | Drive interactions |

**Use Together:**
Simulators and evaluators complement each other. Use simulators to generate multi-turn conversations, then use evaluators to assess the quality of those interactions.

## Integration with Evaluators

Simulators work seamlessly with trace-based evaluators:

```python
from strands import Agent
from strands_evals import Case, Experiment, ActorSimulator
from strands_evals.evaluators import HelpfulnessEvaluator, GoalSuccessRateEvaluator
from strands_evals.mappers import StrandsInMemorySessionMapper
from strands_evals.telemetry import StrandsEvalsTelemetry

# Setup telemetry
telemetry = StrandsEvalsTelemetry().setup_in_memory_exporter()
memory_exporter = telemetry.in_memory_exporter

def task_function(case: Case) -> dict:
    # Create simulator to drive conversation
    simulator = ActorSimulator.from_case_for_user_simulator(
        case=case,
        max_turns=10
    )
    
    # Create agent to evaluate
    agent = Agent(
        trace_attributes={
            "gen_ai.conversation.id": case.session_id,
            "session.id": case.session_id
        },
        callback_handler=None
    )
    
    # Run multi-turn conversation
    user_message = case.input
    
    while simulator.has_next():
        agent_response = agent(user_message)
        turn_spans = list(memory_exporter.get_finished_spans())
        
        user_result = simulator.act(str(agent_response))
        user_message = str(user_result.structured_output.message)
    
    all_spans = memory_exporter.get_finished_spans()
    # Map to session for evaluation
    mapper = StrandsInMemorySessionMapper()
    session = mapper.map_to_session(all_spans, session_id=case.session_id)
    
    return {"output": str(agent_response), "trajectory": session}

# Use evaluators to assess simulated conversations
evaluators = [
    HelpfulnessEvaluator(),
    GoalSuccessRateEvaluator()
]

# Setup test cases
test_cases = [
    Case(
        input="I need to book a flight to Paris",
        metadata={"task_description": "Flight booking confirmed"}
    ),
    Case(
        input="Help me write a Python function to sort a list",
        metadata={"task_description": "Programming assistance"}
    )
]

experiment = Experiment(cases=test_cases, evaluators=evaluators)
reports = experiment.run_evaluations(task_function)
```

## Best Practices

### 1. Define Clear Goals

Simulators work best with well-defined objectives:

```python
case = Case(
    input="I need to book a flight",
    metadata={
        "task_description": "Flight booked with confirmation number and email sent"
    }
)
```

### 2. Set Appropriate Turn Limits

Balance thoroughness with efficiency:

```python
# Simple tasks: 3-5 turns
simulator = ActorSimulator.from_case_for_user_simulator(case=case, max_turns=5)

# Complex tasks: 8-15 turns
simulator = ActorSimulator.from_case_for_user_simulator(case=case, max_turns=12)
```

### 3. Combine with Multiple Evaluators

Assess different aspects of simulated conversations:

```python
evaluators = [
    HelpfulnessEvaluator(),      # User experience
    GoalSuccessRateEvaluator(),  # Task completion
    FaithfulnessEvaluator()      # Response accuracy
]
```

### 4. Log Conversations for Analysis

Capture conversation details for debugging:

```python
conversation_log = []
while simulator.has_next():
    # ... conversation logic ...
    conversation_log.append({
        "turn": turn_number,
        "agent": agent_message,
        "simulator": simulator_message,
        "reasoning": simulator_reasoning
    })
```

## Common Patterns

### Pattern 1: Goal Completion Testing

```python
def test_goal_completion(case: Case) -> bool:
    simulator = ActorSimulator.from_case_for_user_simulator(case=case)
    agent = Agent(system_prompt="Your prompt")
    
    user_message = case.input
    while simulator.has_next():
        agent_response = agent(user_message)
        user_result = simulator.act(str(agent_response))
        user_message = str(user_result.structured_output.message)
        
        if "<stop/>" in user_message:
            return True
    
    return False
```

### Pattern 2: Conversation Flow Analysis

```python
def analyze_conversation_flow(case: Case) -> dict:
    simulator = ActorSimulator.from_case_for_user_simulator(case=case)
    agent = Agent(system_prompt="Your prompt")
    
    metrics = {
        "turns": 0,
        "agent_questions": 0,
        "user_clarifications": 0
    }
    
    user_message = case.input
    while simulator.has_next():
        agent_response = agent(user_message)
        if "?" in str(agent_response):
            metrics["agent_questions"] += 1
        
        user_result = simulator.act(str(agent_response))
        user_message = str(user_result.structured_output.message)
        metrics["turns"] += 1
    
    return metrics
```

### Pattern 3: Comparative Evaluation

```python
def compare_agent_configurations(case: Case, configs: list) -> dict:
    results = {}
    
    for config in configs:
        simulator = ActorSimulator.from_case_for_user_simulator(case=case)
        agent = Agent(**config)
        
        # Run conversation and collect metrics
        # ... evaluation logic ...
        
        results[config["name"]] = metrics
    
    return results
```

## Next Steps

- [User Simulator Guide](./user_simulation.md): Learn about user simulation
- [Evaluators](../evaluators/output_evaluator.md): Combine with evaluators

## Related Documentation

- [Quickstart Guide](../quickstart.md): Get started with Strands Evals
- [Evaluators Overview](../evaluators/output_evaluator.md): Learn about evaluators
- [Experiment Generator](../experiment_generator.md): Generate test cases automatically
