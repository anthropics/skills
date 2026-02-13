import asyncio
import datetime

from strands import Agent
from strands.multiagent import GraphBuilder

from strands_evals import Case, Experiment
from strands_evals.evaluators import InteractionsEvaluator, TrajectoryEvaluator
from strands_evals.extractors import graph_extractor


async def async_graph_example():
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
    def research_graph(case: Case):
        # Create specialized agents
        researcher = Agent(name="researcher", system_prompt="You are a research specialist...")
        analyst = Agent(name="analyst", system_prompt="You are a data analysis specialist...")
        fact_checker = Agent(name="fact_checker", system_prompt="You are a fact checking specialist...")
        report_writer = Agent(name="report_writer", system_prompt="You are a report writing specialist...")

        # Create a graph with these agents
        builder = GraphBuilder()
        # Add nodes
        builder.add_node(researcher, "research")
        builder.add_node(analyst, "analysis")
        builder.add_node(fact_checker, "fact_check")
        builder.add_node(report_writer, "report")

        # Add edges (dependencies)
        builder.add_edge("research", "analysis")
        builder.add_edge("research", "fact_check")
        builder.add_edge("analysis", "report")
        builder.add_edge("fact_check", "report")

        # Set entry points (optional - will be auto-detected if not specified)
        builder.set_entry_point("research")

        # Build the graph
        graph = builder.build()

        result = graph(case.input)
        interactions = graph_extractor.extract_graph_interactions(result)

        return {"interactions": interactions, "trajectory": [node.node_id for node in result.execution_order]}

    ### Step 2: Create test cases ###
    test1 = Case(
        input="Research the impact of AI on healthcare and create a short report",
        expected_interactions=[
            {"node_name": "research", "dependencies": []},
            {"node_name": "fact_check", "dependencies": ["research"]},
            {"node_name": "analysis", "dependencies": ["research"]},
            {"node_name": "report", "dependencies": ["fact_check", "analysis"]},
        ],
    )
    test2 = Case(input="Research the impact of robotics on healthcare and create a short report")

    ### Step 2: Create evaluator ###
    rubric = {
        "research": "The research node should be the starting point and generate a query about the topic.",
        "fact_check": "The fact check node should come after research and verify the accuracy of the generated query.",
        "analysis": "The analysis node should come after research and generate a summary of the findings.",
        "report": "The report node should come after analysis"
        " and fact check and synthesize the information into a coherent report.",
    }
    # if want to use the same rubric
    basic_rubric = (
        "The graph system should ultilized the agents as expected with relevant information."
        " The actual interactions should include more information than expected."
    )
    interaction_evaluator = InteractionsEvaluator(rubric=rubric)
    trajectory_eval = TrajectoryEvaluator(rubric=basic_rubric)

    ### Step 4: Create dataset ###
    interaction_experiment = Experiment(cases=[test1, test2], evaluators=[interaction_evaluator])
    trajectory_experiment = Experiment(cases=[test1, test2], evaluators=[trajectory_eval])

    ### Step 5: Run evaluation ###
    interaction_reports = await interaction_experiment.run_evaluations_async(research_graph)
    trajectory_reports = await trajectory_experiment.run_evaluations_async(research_graph)
    interaction_report = interaction_reports[0]
    trajectory_report = trajectory_reports[0]

    return trajectory_report, interaction_report


if __name__ == "__main__":
    # run the file as a module: eg. python -m examples.evaluate_graph
    start = datetime.datetime.now()
    trajectory_report, interaction_report = asyncio.run(async_graph_example())
    end = datetime.datetime.now()
    print("Async node interactions", end - start)

    trajectory_report.to_file("research_graph_report_trajectory")
    trajectory_report.display(include_actual_trajectory=True)

    interaction_report.to_file("research_graph_report_interactions")
    interaction_report.display(include_actual_interactions=True)
