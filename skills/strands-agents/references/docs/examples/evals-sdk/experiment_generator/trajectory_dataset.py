import asyncio

from strands import Agent, tool

from strands_evals.case import Case
from strands_evals.evaluators import TrajectoryEvaluator
from strands_evals.extractors import tools_use_extractor
from strands_evals.generators import ExperimentGenerator
from strands_evals.types import TaskOutput

# Bank account balances
balances = {"Anna": -100, "Cindy": 800, "Brian": 300, "Hailey": 0}


@tool
def get_balance(person: str) -> int:
    """Get the balance of a bank account."""
    return balances.get(person, 0)


@tool
def modify_balance(person: str, amount: int) -> None:
    """Modify the balance of a bank account by a given amount."""
    balances[person] += amount


@tool
def collect_debt() -> list[tuple]:
    """Check all bank accounts for any debt."""
    debt = []
    for person in balances:
        if balances[person] < 0:
            debt.append((person, abs(balances[person])))
    return debt


async def trajectory_experiment_generator():
    """
    Demonstrates generating an experiment for bank tools trajectory evaluation.

    This function:
    1. Defines a task function that uses banking tools
    2. Creates an ExperimentGenerator for trajectory evaluation
    3. Generates an experiment from banking-related topics
    4. Runs evaluations on the generated test cases

    Returns:
        EvaluationReport: Results of running the generated test cases
    """

    ### Step 1: Define task ###
    async def bank_task(case: Case) -> TaskOutput:
        """
        Banking task that handles spending, balance checks, and debt collection.
        """
        bank_prompt = (
            "You are a banker. Ensure only people with sufficient balance can spend money. "
            "Collect debt from people with negative balance. "
            "Report the current balance of the person of interest after all actions."
        )
        agent = Agent(
            tools=[get_balance, modify_balance, collect_debt], system_prompt=bank_prompt, callback_handler=None
        )
        response = await agent.invoke_async(case.input)
        trajectory = tools_use_extractor.extract_agent_tools_used_from_messages(agent.messages)
        return TaskOutput(output=str(response), trajectory=trajectory)

    ### Step 2: Initialize the experiment generator ###
    generator = ExperimentGenerator[str, str](str, str)

    ### Step 3: Generate experiment with tool context ###
    tool_context = """
    Available banking tools:
    - get_balance(person: str) -> int: Get the balance of a bank account for a specific person
    - modify_balance(person: str, amount: int) -> None: Modify the balance by adding/subtracting an amount
    - collect_debt() -> list[tuple]: Check all accounts and return list of people with negative balances and their debt amounts
    
    Banking rules:
    - Only allow spending if person has sufficient balance
    - Collect debt from people with negative balances
    - Always report final balance after transactions
    """

    experiment = await generator.from_context_async(
        context=tool_context,
        num_cases=5,
        evaluator=TrajectoryEvaluator,
        task_description="Banking operations with balance checks, spending, and debt collection",
    )

    ### Step 3.5: (Optional) Save the generated experiment ###
    experiment.to_file("generated_bank_trajectory_experiment")

    ### Step 4: Run evaluations on the generated test cases ###
    reports = await experiment.run_evaluations_async(bank_task)
    return reports[0]


if __name__ == "__main__":
    # python -m examples.experiment_generator.trajectory_experiment
    report = asyncio.run(trajectory_experiment_generator())
    report.to_file("generated_bank_trajectory_report")
    report.run_display(include_actual_trajectory=True)
