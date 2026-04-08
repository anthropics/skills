import asyncio

from strands import Agent

from strands_evals.case import Case
from strands_evals.evaluators.output_evaluator import OutputEvaluator
from strands_evals.generators.experiment_generator import ExperimentGenerator


async def topic_planning_experiment_generator():
    """
    Demonstrates experiment generation with topic planning for improved diversity.

    This function shows how to use the num_topics parameter to generate
    more diverse test cases through multi-step topic planning.

    Returns:
        EvaluationReport: Results of running the generated test cases
    """

    ### Step 1: Define task ###
    async def get_response(case: Case) -> str:
        """Simple task example to get a response from an agent given a query."""
        agent = Agent(system_prompt="You are a helpful travel booking assistant", callback_handler=None)
        response = await agent.invoke_async(case.input)
        return str(response)

    # Step 2: Initialize the experiment generator for string types
    generator = ExperimentGenerator[str, str](str, str)

    # Step 3: Generate experiment with topic planning for better coverage
    experiment = await generator.from_context_async(
        context="""Available tools:
        - book_flight(origin, destination, date)
        - cancel_booking(confirmation_id)
        - check_flight_status(flight_number)
        - manage_loyalty_points(customer_id)
        - request_special_assistance(needs)""",
        task_description="Travel booking assistant that helps users with flights and reservations",
        num_cases=30,
        num_topics=6,  # Generate 6 diverse topics, ~5 cases per topic
        evaluator=OutputEvaluator,
    )

    # Step 3.5: (Optional) Save the generated experiment for future use
    experiment.to_file("topic_planning_travel_experiment")

    # Step 4: Run evaluations on the generated test cases
    reports = await experiment.run_evaluations_async(get_response)
    return reports[0]


if __name__ == "__main__":
    # python -m examples.experiment_generator.topic_planning_experiment
    report = asyncio.run(topic_planning_experiment_generator())
    report.to_file("topic_planning_travel_report")
    report.run_display(include_actual_output=True)
