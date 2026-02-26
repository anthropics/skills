from strands import Agent
from strands_tools import calculator

from strands_evals import Case, Experiment
from strands_evals.evaluators import ToolParameterAccuracyEvaluator
from strands_evals.mappers import StrandsInMemorySessionMapper
from strands_evals.telemetry import StrandsEvalsTelemetry

# Setup telemetry
telemetry = StrandsEvalsTelemetry().setup_in_memory_exporter()
memory_exporter = telemetry.in_memory_exporter

# 1. Define a task function
def user_task_function(case: Case) -> dict:
    """Execute agent with tools and capture trajectory."""
    memory_exporter.clear()
    agent = Agent(
        # IMPORTANT: trace_attributes with session IDs are required when using StrandsInMemorySessionMapper
        # to prevent spans from different test cases from being mixed together in the memory exporter
        trace_attributes={"gen_ai.conversation.id": case.session_id, "session.id": case.session_id},
        tools=[calculator],
        callback_handler=None,
    )
    agent_response = agent(case.input)
    finished_spans = memory_exporter.get_finished_spans()
    mapper = StrandsInMemorySessionMapper()
    session = mapper.map_to_session(finished_spans, session_id=case.session_id)
    return {"output": str(agent_response), "trajectory": session}


# 2. Create test cases
test_cases = [
    Case[str, str](
        name="simple-calculation",
        input="Calculate the square root of 144",
        metadata={"category": "math", "difficulty": "easy"},
    ),
    Case[str, str](
        name="percentage-calculation",
        input="What's 20 percent of 250?",
        metadata={"category": "math", "difficulty": "easy"},
    ),
    Case[str, str](
        name="complex-calculation",
        input="I need to calculate 15 + 27, then multiply the result by 3, and finally subtract 10.",
        metadata={"category": "math", "difficulty": "medium"},
    ),
]

# 3. Create evaluators
# The evaluator will check if tool parameters are faithful to the context
evaluators = [ToolParameterAccuracyEvaluator()]

# 4. Create an experiment
experiment = Experiment[str, str](cases=test_cases, evaluators=evaluators)

# 5. Run evaluations
reports = experiment.run_evaluations(user_task_function)
reports[0].run_display()
