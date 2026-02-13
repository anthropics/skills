import json
import asyncio
from strands import Agent
from strands_tools import calculator, retrieve, file_read, diagram, journal,generate_image, image_reader

from strands_evals import Case, Experiment
from strands_evals.evaluators import OutputEvaluator
from strands_evals.telemetry import StrandsEvalsTelemetry

telemetry = StrandsEvalsTelemetry().setup_in_memory_exporter()
memory_exporter = telemetry.in_memory_exporter

async def async_example():
    """
    Demonstrates evaluating graph-based agent workflows for research tasks.

    This example:
    1. Defines a task function with a graph of specialized research agents
    2. Creates test cases for research and report generation scenarios
    3. Creates TrajectoryEvaluator and InteractionsEvaluator to assess graph execution
    4. Creates datasets with the test cases and evaluators
    5. Runs evaluations and analyzes the reports

    Returns:
        tuple[EvaluationReport, EvaluationReport]: The trajectory and interaction evaluation results
    """

    ### Step 1: Define task ###
    def user_task_function(case: Case) -> dict:
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

    ### Step 2: Create test cases ###
    test_cases = [
        Case[str, str](name="math-1", input="Calculate the square root of 144", metadata={"category": "math"}),
        Case[str, str](
            name="math-2",
            input="What is 25 * 4? can you use that output and then divide it by 4, then the final output should be squared. Give me the final value.",
            metadata={"category": "math"},
        )
    ]

    evaluators = [ToolSelectionAccuracyEvaluator()]
    experiment = Experiment[str, str](cases=test_cases, evaluators=evaluators)
    reports = await experiment.run_evaluations_async(research_graph)
    return reports
    

if __name__ == "__main__":
    # run the file as a module: eg. python -m examples.evaluate_graph
    reports = asyncio.run(async_graph_example())

    # report.to_file("tool_selection_accuracy_async")
    reports[0].run_display(include_actual_trajectory=True)
