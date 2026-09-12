import asyncio

from strands import Agent

from strands_evals import Case
from strands_evals.evaluators.output_evaluator import OutputEvaluator
from strands_evals.generators.experiment_generator import ExperimentGenerator


async def simple_experiment_generator():
    """
    Demonstrates the a simple experiment generation and evaluation process.

    This function:
    1. Defines a task function that uses an agent to generate responses
    2. Creates an ExperimentGenerator for string input/output types
    3. Generates an experiment from scratch based on specified topics
    4. Runs evaluations on the generated test cases

    Returns:
        EvaluationReport: Results of running the generated test cases
    """

    ### Step 1: Define task ###
    async def get_response(case: Case) -> str:
        """
        Simple task example to get a response from an agent given a query.
        """
        agent = Agent(system_prompt="Be as concise as possible", callback_handler=None)
        response = await agent.invoke_async(case.input)
        return str(response)

    # Step 2: Initialize the experiment generator for string types
    generator = ExperimentGenerator[str, str](str, str)

    # Step 3: Generate experiment from scratch with specified topics
    # This will create test cases and a rubric automatically
    experiment = await generator.from_scratch_async(
        topics=["safety", "red teaming", "leetspeak"],  # Topics to cover in test cases
        task_description="Getting response from an agent given a query",  # What the AI system does
        num_cases=10,  # Number of test cases to generate
        evaluator=OutputEvaluator,  # Type of evaluator to create with generated rubric
    )

    # Step 3.5: (Optional) Save the generated experiment for future use
    experiment.to_file("generate_simple_experiment")

    # Step 4: Run evaluations on the generated test cases
    reports = await experiment.run_evaluations_async(get_response)
    return reports[0]


if __name__ == "__main__":
    # python -m examples.experiment_generator.simple_experiment
    report = asyncio.run(simple_experiment_generator())
    report.to_file("generated_safety_judge_output_report")
    report.run_display(include_actual_output=True)
