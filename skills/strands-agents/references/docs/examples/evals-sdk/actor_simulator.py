from strands import Agent

from strands_evals import ActorSimulator, Case, Experiment
from strands_evals.evaluators import HelpfulnessEvaluator
from strands_evals.mappers import StrandsInMemorySessionMapper
from strands_evals.telemetry import StrandsEvalsTelemetry


# Setup telemetry
telemetry = StrandsEvalsTelemetry().setup_in_memory_exporter()
memory_exporter = telemetry.in_memory_exporter

# 1. Define a task function
def task_function(case: Case) -> dict:
    # Create simulator
    user_sim = ActorSimulator.from_case_for_user_simulator(case=case, max_turns=3)

    # Create target agent
    agent = Agent(
        # IMPORTANT: trace_attributes with session IDs are required when using StrandsInMemorySessionMapper
        # to prevent spans from different test cases from being mixed together in the memory exporter
        trace_attributes={"gen_ai.conversation.id": case.session_id, "session.id": case.session_id},
        system_prompt="You are a helpful travel assistant.",
        callback_handler=None,
    )

    user_message = case.input
    while user_sim.has_next():
        # Clear before each target agent call to ensure we don't capture simulator traces.
        memory_exporter.clear()
        agent_response = agent(user_message)
        agent_message = str(agent_response)
        user_result = user_sim.act(agent_message)
        user_message = str(user_result.structured_output.message)

    mapper = StrandsInMemorySessionMapper()
    finished_spans = memory_exporter.get_finished_spans()
    session = mapper.map_to_session(finished_spans, session_id=case.session_id)

    return {"output": agent_message, "trajectory": session}

# 2. Create test cases
test_cases = [
    Case[str, str](
        name="booking-simple",
        input="I need to book a flight to Paris next week",
        metadata={"category": "booking", "task_description": "Flight booking confirmed"},
    )
]

# 3. Create evaluators
evaluators = [HelpfulnessEvaluator()]

# 4. Create an experiment
experiment = Experiment[str, str](cases=test_cases, evaluators=evaluators)

# 5. Run evaluations
reports = experiment.run_evaluations(task_function)
reports[0].run_display()
