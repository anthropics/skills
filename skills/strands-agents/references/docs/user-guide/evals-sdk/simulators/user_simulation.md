# User Simulation

## Overview

User simulation enables realistic multi-turn conversation evaluation by simulating end-users interacting with your agents. Using the `ActorSimulator` class configured for user simulation, you can generate dynamic, goal-oriented conversations that test your agent's ability to handle real user interactions.

The `from_case_for_user_simulator()` factory method automatically configures the simulator with user-appropriate profiles and behaviors:

```python
from strands_evals import ActorSimulator, Case

case = Case(
    input="I need to book a flight to Paris",
    metadata={"task_description": "Flight booking confirmed"}
)

# Automatically configured for user simulation
user_sim = ActorSimulator.from_case_for_user_simulator(
    case=case,
    max_turns=10
)
```

## Key Features

- **Realistic Actor Simulation**: Generates human-like responses based on actor profiles
- **Multi-turn Conversations**: Maintains context across multiple conversation turns
- **Automatic Profile Generation**: Creates actor profiles from test cases
- **Goal-Oriented Behavior**: Tracks and evaluates goal completion
- **Flexible Configuration**: Supports custom profiles, prompts, and tools
- **Conversation Control**: Automatic stopping based on goal completion or turn limits
- **Integration with Evaluators**: Works seamlessly with trace-based evaluators

## When to Use

Use user simulation when you need to:

- Evaluate agents in multi-turn user conversations
- Test how agents handle realistic user behavior
- Assess goal completion from the user's perspective
- Generate diverse user interaction patterns
- Evaluate agents without predefined conversation scripts
- Test conversational flow and context maintenance with users

## Basic Usage

### Simple User Simulation

```python
from strands import Agent
from strands_evals import Case, ActorSimulator

# Create test case
case = Case(
    name="flight-booking",
    input="I need to book a flight to Paris next week",
    metadata={"task_description": "Flight booking confirmed"}
)

# Create user simulator
user_sim = ActorSimulator.from_case_for_user_simulator(
    case=case,
    max_turns=5  # Limits conversation length; simulator may stop earlier if goal is achieved
)

# Create target agent to evaluate
agent = Agent(
    system_prompt="You are a helpful travel assistant.",
    callback_handler=None
)

# Run multi-turn conversation
user_message = case.input
conversation_log = []

while user_sim.has_next():
    # Agent responds
    agent_response = agent(user_message)
    agent_message = str(agent_response)
    conversation_log.append({"role": "agent", "message": agent_message})
    
    # User simulator generates next message
    user_result = user_sim.act(agent_message)
    user_message = str(user_result.structured_output.message)
    conversation_log.append({"role": "user", "message": user_message})

print(f"Conversation completed in {len(conversation_log) // 2} turns")
```

## Actor Profiles

Actor profiles define the characteristics, context, and goals of the simulated actor.

### Automatic Profile Generation

The simulator can automatically generate realistic profiles from test cases:

```python
from strands_evals import Case, ActorSimulator

case = Case(
    input="My order hasn't arrived yet",
    metadata={"task_description": "Order status resolved and customer satisfied"}
)

# Profile is automatically generated from input and task_description
user_sim = ActorSimulator.from_case_for_user_simulator(case=case)

# Access the generated profile
print(user_sim.actor_profile.traits)
print(user_sim.actor_profile.context)
print(user_sim.actor_profile.actor_goal)
```

### Custom Actor Profiles

For more control, create custom profiles:

```python
from strands_evals.simulation import ActorSimulator
from strands_evals.types.simulation import ActorProfile

# Define custom profile
profile = ActorProfile(
    traits={
        "expertise_level": "expert",
        "communication_style": "technical",
        "patience_level": "low",
        "detail_preference": "high"
    },
    context="A software engineer debugging a production memory leak issue.",
    actor_goal="Identify the root cause and get actionable steps to resolve the memory leak."
)

# Create simulator with custom profile
simulator = ActorSimulator(
    actor_profile=profile,
    initial_query="Our service is experiencing high memory usage in production.",
    system_prompt_template="You are simulating: {actor_profile}",
    max_turns=10
)
```

## Integration with Evaluators

### With Trace-Based Evaluators

```python
from strands import Agent
from strands_evals import Case, Experiment, ActorSimulator
from strands_evals.evaluators import HelpfulnessEvaluator
from strands_evals.mappers import StrandsInMemorySessionMapper
from strands_evals.telemetry import StrandsEvalsTelemetry

# Setup telemetry
telemetry = StrandsEvalsTelemetry().setup_in_memory_exporter()
memory_exporter = telemetry.in_memory_exporter

def task_function(case: Case) -> dict:
    # Create simulator
    user_sim = ActorSimulator.from_case_for_user_simulator(
        case=case,
        max_turns=5
    )
    
    # Create target agent
    agent = Agent(
        trace_attributes={
            "gen_ai.conversation.id": case.session_id,
            "session.id": case.session_id
        },
        system_prompt="You are a helpful assistant.",
        callback_handler=None
    )
    
    # Collect spans across all turns
    all_spans = []
    user_message = case.input
    
    while user_sim.has_next():
        # Agent responds
        agent_response = agent(user_message)
        agent_message = str(agent_response)
        
        # User simulator responds
        user_result = user_sim.act(agent_message)
        user_message = str(user_result.structured_output.message)
    
    all_spans = memory_exporter.get_finished_spans()
    # Map spans to session
    mapper = StrandsInMemorySessionMapper()
    session = mapper.map_to_session(all_spans, session_id=case.session_id)
    
    return {"output": agent_message, "trajectory": session}

# Create test cases
test_cases = [
    Case(
        name="booking-1",
        input="I need to book a flight to Paris",
        metadata={"task_description": "Flight booking confirmed"}
    )
]

# Run evaluation
evaluators = [HelpfulnessEvaluator()]
experiment = Experiment(cases=test_cases, evaluators=evaluators)
reports = experiment.run_evaluations(task_function)
reports[0].run_display()
```

## Conversation Control

### Automatic Stopping

The simulator automatically stops when:

1. **Goal Completion**: Actor includes `<stop/>` token in message
2. **Turn Limit**: Maximum number of turns is reached

```python
user_sim = ActorSimulator.from_case_for_user_simulator(
    case=case,
    max_turns=10  # Stop after 10 turns
)

# Check if conversation should continue
while user_sim.has_next():
    # ... conversation logic ...
    pass
```

### Manual Turn Tracking

```python
turn_count = 0
max_turns = 5

while user_sim.has_next() and turn_count < max_turns:
    agent_response = agent(user_message)
    user_result = user_sim.act(str(agent_response))
    user_message = str(user_result.structured_output.message)
    turn_count += 1

print(f"Conversation ended after {turn_count} turns")
```

## Actor Response Structure

Each actor response includes reasoning and the actual message. The reasoning field provides insight into the simulator's decision-making process, helping you understand why it responded in a particular way and whether it's behaving realistically:

```python
user_result = user_sim.act(agent_message)

# Access structured output
reasoning = user_result.structured_output.reasoning
message = user_result.structured_output.message

print(f"Actor's reasoning: {reasoning}")
print(f"Actor's message: {message}")

# Example output:
# Actor's reasoning: "The agent provided flight options but didn't ask for my preferred time. 
#                     I should specify that I prefer morning flights to move the conversation forward."
# Actor's message: "Thanks! Do you have any morning flights available?"
```

The reasoning is particularly useful for:
- **Debugging**: Understanding why the simulator isn't reaching the goal
- **Validation**: Ensuring the simulator is behaving realistically
- **Analysis**: Identifying patterns in how users respond to agent behavior

## Advanced Usage

### Custom System Prompts

```python
custom_prompt = """
You are simulating a user with the following profile:
{actor_profile}

Guidelines:
- Be concise and direct
- Ask clarifying questions when needed
- Express satisfaction when goals are met
- Include <stop/> when your goal is achieved
"""

user_sim = ActorSimulator.from_case_for_user_simulator(
    case=case,
    system_prompt_template=custom_prompt,
    max_turns=10
)
```

### Adding Custom Tools

```python
from strands import tool

@tool
def check_order_status(order_id: str) -> str:
    """Check the status of an order."""
    return f"Order {order_id} is in transit"

user_sim = ActorSimulator.from_case_for_user_simulator(
    case=case,
    tools=[check_order_status],  # Additional tools for the simulator
    max_turns=10
)
```

### Different Model for Simulation

```python
user_sim = ActorSimulator.from_case_for_user_simulator(
    case=case,
    model="anthropic.claude-3-5-sonnet-20241022-v2:0",  # Specific model
    max_turns=10
)
```

## Complete Example: Customer Service Evaluation

```python
from strands import Agent
from strands_evals import Case, Experiment, ActorSimulator
from strands_evals.evaluators import HelpfulnessEvaluator, GoalSuccessRateEvaluator
from strands_evals.mappers import StrandsInMemorySessionMapper
from strands_evals.telemetry import StrandsEvalsTelemetry

# Setup telemetry
telemetry = StrandsEvalsTelemetry().setup_in_memory_exporter()
memory_exporter = telemetry.in_memory_exporter

def customer_service_task(case: Case) -> dict:
    """Simulate customer service interaction."""
    
    # Create user simulator
    user_sim = ActorSimulator.from_case_for_user_simulator(
        case=case,
        max_turns=8
    )
    
    # Create customer service agent
    agent = Agent(
        trace_attributes={
            "gen_ai.conversation.id": case.session_id,
            "session.id": case.session_id
        },
        system_prompt="""
        You are a helpful customer service agent.
        - Be empathetic and professional
        - Gather necessary information
        - Provide clear solutions
        - Confirm customer satisfaction
        """,
        callback_handler=None
    )
    
    # Run conversation
    all_spans = []
    user_message = case.input
    conversation_history = []
    
    while user_sim.has_next():
        memory_exporter.clear()
        
        # Agent responds
        agent_response = agent(user_message)
        agent_message = str(agent_response)
        conversation_history.append({
            "role": "agent",
            "message": agent_message
        })
        
        # Collect spans
        turn_spans = list(memory_exporter.get_finished_spans())
        all_spans.extend(turn_spans)
        
        # User responds
        user_result = user_sim.act(agent_message)
        user_message = str(user_result.structured_output.message)
        conversation_history.append({
            "role": "user",
            "message": user_message,
            "reasoning": user_result.structured_output.reasoning
        })
    
    # Map to session
    mapper = StrandsInMemorySessionMapper()
    session = mapper.map_to_session(all_spans, session_id=case.session_id)
    
    return {
        "output": agent_message,
        "trajectory": session,
        "conversation_history": conversation_history
    }

# Create diverse test cases
test_cases = [
    Case(
        name="order-issue",
        input="My order #12345 hasn't arrived and it's been 2 weeks",
        metadata={
            "category": "order_tracking",
            "task_description": "Order status checked, issue resolved, customer satisfied"
        }
    ),
    Case(
        name="product-return",
        input="I want to return a product that doesn't fit",
        metadata={
            "category": "returns",
            "task_description": "Return initiated, return label provided, customer satisfied"
        }
    ),
    Case(
        name="billing-question",
        input="I was charged twice for my last order",
        metadata={
            "category": "billing",
            "task_description": "Billing issue identified, refund processed, customer satisfied"
        }
    )
]

# Run evaluation with multiple evaluators
evaluators = [
    HelpfulnessEvaluator(),
    GoalSuccessRateEvaluator()
]

experiment = Experiment(cases=test_cases, evaluators=evaluators)
reports = experiment.run_evaluations(customer_service_task)

# Display results
for report in reports:
    print(f"\n{'='*60}")
    print(f"Evaluator: {report.evaluator_name}")
    print(f"{'='*60}")
    report.run_display()
```

## Best Practices

### 1. Clear Task Descriptions

```python
# Good: Specific, measurable goal
case = Case(
    input="I need to book a flight",
    metadata={
        "task_description": "Flight booked with confirmation number, dates confirmed, payment processed"
    }
)

# Less effective: Vague goal
case = Case(
    input="I need to book a flight",
    metadata={"task_description": "Help with booking"}
)
```

### 2. Appropriate Turn Limits

```python
# Simple queries: 3-5 turns
user_sim = ActorSimulator.from_case_for_user_simulator(
    case=simple_case,
    max_turns=5
)

# Complex tasks: 8-15 turns
user_sim = ActorSimulator.from_case_for_user_simulator(
    case=complex_case,
    max_turns=12
)
```

### 3. Clear Span Collection

```python
# Always clear before agent calls to avoid capturing simulator traces
while user_sim.has_next():
    memory_exporter.clear()  # Clear simulator traces
    agent_response = agent(user_message)
    turn_spans = list(memory_exporter.get_finished_spans())  # Only agent spans
    all_spans.extend(turn_spans)
    user_result = user_sim.act(str(agent_response))
    user_message = str(user_result.structured_output.message)
```

### 4. Conversation Logging

```python
# Log conversations for analysis
conversation_log = []

while user_sim.has_next():
    agent_response = agent(user_message)
    agent_message = str(agent_response)
    
    user_result = user_sim.act(agent_message)
    user_message = str(user_result.structured_output.message)
    
    conversation_log.append({
        "turn": len(conversation_log) // 2 + 1,
        "agent": agent_message,
        "user": user_message,
        "user_reasoning": user_result.structured_output.reasoning
    })

# Save for review
import json
with open("conversation_log.json", "w") as f:
    json.dump(conversation_log, f, indent=2)
```

## Common Patterns

### Pattern 1: Goal Completion Testing

```python
def test_goal_completion(case: Case) -> bool:
    user_sim = ActorSimulator.from_case_for_user_simulator(case=case)
    agent = Agent(system_prompt="Your agent prompt")
    
    user_message = case.input
    goal_completed = False
    
    while user_sim.has_next():
        agent_response = agent(user_message)
        user_result = user_sim.act(str(agent_response))
        user_message = str(user_result.structured_output.message)
        
        # Check for stop token
        if "<stop/>" in user_message:
            goal_completed = True
            break
    
    return goal_completed
```

### Pattern 2: Multi-Evaluator Assessment

```python
def comprehensive_evaluation(case: Case) -> dict:
    # ... run conversation with simulator ...
    
    return {
        "output": final_message,
        "trajectory": session,
        "turns_taken": turn_count,
        "goal_completed": "<stop/>" in last_user_message
    }

evaluators = [
    HelpfulnessEvaluator(),
    GoalSuccessRateEvaluator(),
    FaithfulnessEvaluator()
]

experiment = Experiment(cases=cases, evaluators=evaluators)
reports = experiment.run_evaluations(comprehensive_evaluation)
```

### Pattern 3: Conversation Analysis

```python
def analyze_conversation(case: Case) -> dict:
    user_sim = ActorSimulator.from_case_for_user_simulator(case=case)
    agent = Agent(system_prompt="Your prompt")
    
    metrics = {
        "turns": 0,
        "agent_messages": [],
        "user_messages": [],
        "user_reasoning": []
    }
    
    user_message = case.input
    while user_sim.has_next():
        agent_response = agent(user_message)
        agent_message = str(agent_response)
        metrics["agent_messages"].append(agent_message)
        
        user_result = user_sim.act(agent_message)
        user_message = str(user_result.structured_output.message)
        metrics["user_messages"].append(user_message)
        metrics["user_reasoning"].append(user_result.structured_output.reasoning)
        metrics["turns"] += 1
    
    return metrics
```

## Troubleshooting

### Issue: Simulator Stops Too Early

**Solution**: Increase max_turns or check task_description clarity

```python
user_sim = ActorSimulator.from_case_for_user_simulator(
    case=case,
    max_turns=15  # Increase limit
)
```

### Issue: Simulator Doesn't Stop

**Solution**: Ensure task_description is achievable and clear

```python
# Make goal specific and achievable
case = Case(
    input="I need help",
    metadata={
        "task_description": "Specific, measurable goal that can be completed"
    }
)
```

### Issue: Unrealistic Responses

**Solution**: Use custom profile or adjust system prompt

```python
custom_prompt = """
You are simulating a realistic user with: {actor_profile}

Be natural and human-like:
- Don't be overly formal
- Ask follow-up questions naturally
- Express emotions appropriately
- Include <stop/> only when truly satisfied
"""

user_sim = ActorSimulator.from_case_for_user_simulator(
    case=case,
    system_prompt_template=custom_prompt
)
```

### Issue: Capturing Simulator Traces

**Solution**: Always clear exporter before agent calls

```python
while user_sim.has_next():
    memory_exporter.clear()  # Critical: clear before agent call
    agent_response = agent(user_message)
    spans = list(memory_exporter.get_finished_spans())
    # ... rest of logic ...
```

## Related Documentation

- [Simulators Overview](index.md): Learn about the ActorSimulator and simulator framework
- [Quickstart Guide](../quickstart.md): Get started with Strands Evals
- [Helpfulness Evaluator](../evaluators/helpfulness_evaluator.md): Evaluate conversation helpfulness
- [Goal Success Rate Evaluator](../evaluators/goal_success_rate_evaluator.md): Assess goal completion