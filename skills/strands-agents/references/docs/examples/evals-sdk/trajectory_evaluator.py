import asyncio
import datetime

from strands import Agent, tool

from strands_evals import Case, Experiment
from strands_evals.evaluators import TrajectoryEvaluator
from strands_evals.extractors import tools_use_extractor
from strands_evals.types import TaskOutput

balances = {"Anna": -100, "Cindy": 800, "Brian": 300, "Hailey": 0}


@tool
def get_balance(person: str) -> int:
    """
    get the balance of a bank account.

    Args:
        person (str): The person to check the balance for.

    Returns:
        int: The balance of the bank account on the given day.
    """
    # Simple example, but real case could check the database etc.
    return balances.get(person, 0)


@tool
def modify_balance(person: str, amount: int) -> None:
    """
    Modify the balance of a bank account by a given amount.

    Args:
        person (str): The person to modify the balance for.
        amount (int): The amount to add to the balance.

    Returns:
        None
    """
    balances[person] += amount


@tool
def collect_debt() -> list[tuple]:
    """
    Check all of the bank accounts for any debt.

    Returns:
        list: A list of tuples, where each tuple contains the person and their debt.
    """
    debt = []
    for person in balances:
        if balances[person] < 0:
            debt.append((person, abs(balances[person])))

    return debt


async def async_descriptive_tools_trajectory_example():
    """
    Demonstrates evaluating tool usage trajectories in agent responses asynchronously.

    This example:
    1. Defines a task function that uses an agent with calculator tool
       and returns both the response and the tools used
    2. Creates test cases with expected outputs and tool trajectories
    3. Creates a TrajectoryEvaluator to assess tool usage
    4. Creates an experiment with the test cases and evaluator
    5. Runs evaluations and returns the report

    Returns:
        EvaluationReport: The evaluation results
    """

    # 1. Define a task function
    async def get_response(case: Case) -> dict:
        bank_prompt = (
            "You are a banker, ensure that only people with sufficient balance can spend them."
            " Collect debt from people with negative balance."
            " Be sure to report the current balance after all of the actions."
        )
        agent = Agent(
            tools=[get_balance, modify_balance, collect_debt], system_prompt=bank_prompt, callback_handler=None
        )
        response = await agent.invoke_async(case.input)
        trajectory_evaluator.update_trajectory_description(tools_use_extractor.extract_tools_description(agent))
        return TaskOutput(output=str(response), trajectory=tools_use_extractor.extract_agent_tools_used(agent.messages))

        # Or construct the trajectory based on the trace for TrajectoryEvaluator

        # agent = Agent(
        #     trace_attributes={"gen_ai.conversation.id": case.session_id, "session.id": case.session_id},
        #     tools=[get_balance, modify_balance, collect_debt],
        #     system_prompt=bank_prompt,
        #     callback_handler=None,
        # )
        # response = agent(case.input)
        # finished_spans = memory_exporter.get_finished_spans()
        # mapper = StrandsInMemorySessionMapper()
        # session = mapper.map_to_session(finished_spans, session_id=case.session_id)
        # return TaskOutput(
        #     output=str(response), trajectory=tools_use_extractor.extract_agent_tools_used(session)
        # )

    # 2. Create test cases
    case1 = Case(
        name="Negative money",
        input="Anna wants to spend $100.",
        expected_output="Anna should not be able to spend money. We need to collect $100 from him.",
        expected_trajectory=["get_balance", "collect_debt"],
        metadata={"category": "banking"},
    )
    case2 = Case(
        name="Positive money",
        input="Cindy wants to spend $100.",
        expected_output="Cindy should be able to spend the money successfully. Her balance is now $700.",
        expected_trajectory=["get_balance", "modify_balance", "get_balance"],
        metadata={"category": "banking"},
    )
    case3 = Case(
        name="Exact spending",
        input="Brian wants to spend 300.",
        expected_output="Brian spends the money successfully. Brian's balance is now 0.",
        expected_trajectory=["get_balance", "modify_balance", "get_balance"],
    )
    case4 = Case(
        name="No money",
        input="Hailey wants to spend $1.",
        expected_output="Hailey should not be able to spend money.",
        expected_trajectory=["get_balance"],
        metadata={"category": "banking"},
    )

    # 3. Create evaluators
    trajectory_evaluator = TrajectoryEvaluator(
        rubric="The trajectory should be in the correct order with all of the steps as the expected."
        "The agent should know when and what action is logical. Strictly score 0 if any step is missing.",
        include_inputs=True,
    )

    # 4. Create an experiment
    experiment = Experiment[str, str](cases=[case1, case2, case3, case4], evaluators=[trajectory_evaluator])

    # 4.5. (Optional) Save the experiment
    experiment.to_file("async_bank_tools_trajectory_experiment")

    # 5. Run evaluations
    reports = await experiment.run_evaluations_async(get_response)
    return reports[0]


if __name__ == "__main__":
    # run the file as a module: eg. python -m examples.bank_tools_trajectory
    start = datetime.datetime.now()
    report = asyncio.run(async_descriptive_tools_trajectory_example())
    end = datetime.datetime.now()
    print("Async: ", end - start)
    report.to_file("async_bank_tools_trajectory_report")
    report.run_display(include_actual_trajectory=True)
