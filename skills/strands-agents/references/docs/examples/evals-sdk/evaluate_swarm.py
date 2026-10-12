import asyncio
import datetime

from strands import Agent
from strands.multiagent import Swarm

from strands_evals import Case, Experiment
from strands_evals.evaluators import InteractionsEvaluator, TrajectoryEvaluator
from strands_evals.extractors import swarm_extractor


async def async_swarm_example():
    """
    Demonstrates evaluating swarm agent interactions and trajectories for software development tasks.

    This example:
    1. Defines a task function with a swarm of specialized software development agents
    2. Creates test cases for software development scenarios
    3. Creates TrajectoryEvaluator and InteractionsEvaluator to assess agent handoffs
    4. Creates datasets with the test cases and evaluators
    5. Runs evaluations and analyzes the reports

    Returns:
        tuple[EvaluationReport, EvaluationReport]: The trajectory and interaction evaluation results
    """

    ### Step 1: Define task ###
    def sde_swarm(case: Case):
        # Create specialized agents
        researcher = Agent(name="researcher", system_prompt="You are a research specialist...", callback_handler=None)
        coder = Agent(name="coder", system_prompt="You are a coding specialist...", callback_handler=None)
        reviewer = Agent(name="reviewer", system_prompt="You are a code review specialist...", callback_handler=None)
        architect = Agent(
            name="architect", system_prompt="You are a system architecture specialist...", callback_handler=None
        )

        # Create a swarm with these agents
        swarm = Swarm(
            [researcher, coder, reviewer, architect],
            max_handoffs=20,
            max_iterations=20,
            execution_timeout=900.0,  # 15 minutes
            node_timeout=300.0,  # 5 minutes per agent
            repetitive_handoff_detection_window=8,  # There must be >= 2 unique agents in the last 8 handoffs
            repetitive_handoff_min_unique_agents=2,
        )

        result = swarm(case.input)
        interaction_info = swarm_extractor.extract_swarm_interactions(result)

        return {"interactions": interaction_info, "trajectory": [node.node_id for node in result.node_history]}

    ### Step 2: Create test cases ###
    test1 = Case(
        input="Design and implement a simple Rest API for a todo app.",
        expected_trajectory=["researcher", "architect", "coder", "reviewer"],
    )

    ### Step 3: Create evaluator ###
    interaction_evaluator = InteractionsEvaluator(
        rubric="Scoring should measure how well each agent handoff follows logical software development workflow. Score 1.0 if handoffs are appropriate, include relevant context, and demonstrate clear task progression. Score 0.5 if partially logical, 0.0 if illogical or missing context."
    )
    trajectory_evaluator = TrajectoryEvaluator(
        rubric="Scoring should measure how well the swarm utilizes the right sequence of agents for software development. "
        "Score 1.0 if trajectory follows expected workflow, 0.0-1.0 if partially correct sequence, 0.0 if incorrect or inefficient agent usage."
    )

    ### Step 4: Create dataset ###
    trajectory_experiment = Experiment(cases=[test1], evaluators=[trajectory_evaluator])
    interaction_experiment = Experiment(cases=[test1], evaluators=[interaction_evaluator])

    ### Step 5: Run evaluation ###
    trajectory_reports = await trajectory_experiment.run_evaluations_async(sde_swarm)
    interaction_reports = await interaction_experiment.run_evaluations_async(sde_swarm)
    return trajectory_reports[0], interaction_reports[0]


if __name__ == "__main__":
    # run the file as a module: eg. python -m examples.evaluate_swarm
    start = datetime.datetime.now()
    trajectory_report, interaction_report = asyncio.run(async_swarm_example())
    end = datetime.datetime.now()

    trajectory_report.to_file("async_swarm_trajectory_report", "json")
    interaction_report.to_file("async_swarm_interaction_report", "json")

    trajectory_report.run_display(include_actual_trajectory=True)
    interaction_report.run_display(include_actual_interactions=True, include_expected_interactions=True)
