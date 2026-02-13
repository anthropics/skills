import asyncio
import datetime

from langchain.evaluation.criteria import CriteriaEvalChain

## Using a third party evaluator
from langchain_aws import BedrockLLM
from strands import Agent

from strands_evals import Case, Experiment
from strands_evals.evaluators import Evaluator
from strands_evals.types import EvaluationData, EvaluationOutput

## Need to install $pip install langchain langchain_aws ##


def third_party_example():
    """
    Demonstrates integrating a third-party evaluator (LangChain) with the evaluation framework.

    This example:
    1. Defines a task function that uses an agent to generate responses
    2. Creates test cases with expected outputs
    3. Creates a custom evaluator that wraps LangChain's CriteriaEvalChain
    4. Creates a dataset with the test cases and evaluator
    5. Runs evaluations and returns the report

    Returns:
        EvaluationReport: The evaluation results
    """

    # 1. Define a task function
    def get_response(case: Case) -> str:
        agent = Agent(callback_handler=None)
        return str(agent(case.input))

    # 2. Create test cases
    test_case1 = Case[str, str](
        name="knowledge-1",
        input="What is the capital of France?",
        expected_output="The capital of France is Paris.",
        metadata={"category": "knowledge"},
    )

    test_case2 = Case[str, str](
        name="knowledge-2",
        input="What color is the ocean?",
        expected_output="The ocean is blue.",
        metadata={"category": "knowledge"},
    )
    test_case3 = Case(input="When was World War 2?")
    test_case4 = Case(input="Who was the first president of the United States?")

    # 3. Create evaluators
    class LangChainCriteriaEvaluator(Evaluator[str, str]):
        def evaluate(self, evaluation_case: EvaluationData[str, str]) -> EvaluationOutput:
            ## Follow LangChain's Docs: https://python.langchain.com/api_reference/langchain/evaluation/langchain.evaluation.criteria.eval_chain.CriteriaEvalChain.html
            # Initialize Bedrock LLM
            bedrock_llm = BedrockLLM(
                model_id="anthropic.claude-v2",  # or other Bedrock models
                model_kwargs={
                    "max_tokens_to_sample": 256,
                    "temperature": 0.7,
                },
            )

            criteria = {"correctness": "Is the actual answer correct?", "relevance": "Is the response relevant?"}

            evaluator = CriteriaEvalChain.from_llm(llm=bedrock_llm, criteria=criteria)

            # Pass in required context for evaluator (look at LangChain's docs)
            result = evaluator.evaluate_strings(prediction=evaluation_case.actual_output, input=evaluation_case.input)

            # Make sure to return the correct type
            return EvaluationOutput(
                score=result["score"], test_pass=True if result["score"] > 0.5 else False, reason=result["reasoning"]
            )

    # 4. Create an experiment
    experiment = Experiment[str, str](
        cases=[test_case1, test_case2, test_case3, test_case4], evaluators=[LangChainCriteriaEvaluator()]
    )

    experiment.to_file("third_party_dataset", "json")

    # 5. Run evaluations
    reports = experiment.run_evaluations(get_response)
    return reports[0]


async def async_third_party_example():
    """
    Demonstrates integrating a third-party evaluator (LangChain) with the evaluation framework asynchronously.

    This example:
    1. Defines a task function that uses an agent to generate responses
    2. Creates test cases with expected outputs
    3. Creates a custom evaluator that wraps LangChain's CriteriaEvalChain
    4. Creates a dataset with the test cases and evaluator
    5. Runs evaluations and returns the report

    Returns:
        EvaluationReport: The evaluation results
    """

    # 1. Define a task function
    async def get_response(case: Case) -> str:
        agent = Agent(system_prompt="Be as concise as possible", callback_handler=None)
        response = await agent.invoke_async(case.input)
        return str(response)

    # 2. Create test cases
    test_case1 = Case[str, str](
        name="knowledge-1",
        input="What is the capital of France?",
        expected_output="The capital of France is Paris.",
        metadata={"category": "knowledge"},
    )

    test_case2 = Case[str, str](
        name="knowledge-2",
        input="What color is the ocean?",
        expected_output="The ocean is blue.",
        metadata={"category": "knowledge"},
    )
    test_case3 = Case(input="When was World War 2?")
    test_case4 = Case(input="Who was the first president of the United States?")

    # 3. Create evaluators
    class LangChainCriteriaEvaluator(Evaluator[str, str]):
        def evaluate(self, evaluation_case: EvaluationData[str, str]) -> EvaluationOutput:
            ## Follow LangChain's Docs: https://python.langchain.com/api_reference/langchain/evaluation/langchain.evaluation.criteria.eval_chain.CriteriaEvalChain.html
            # Initialize Bedrock LLM
            bedrock_llm = BedrockLLM(
                model_id="anthropic.claude-v2",  # or other Bedrock models
                model_kwargs={
                    "max_tokens_to_sample": 256,
                    "temperature": 0.7,
                },
            )

            criteria = {
                "correctness": "Is the actual answer correct?",
                "relevance": "Is the response relevant?",
                "conciseness": "Is the response short and to the point?",
            }

            evaluator = CriteriaEvalChain.from_llm(llm=bedrock_llm, criteria=criteria)

            # Pass in required context for evaluator (look at LangChain's docs)
            result = evaluator.evaluate_strings(prediction=evaluation_case.actual_output, input=evaluation_case.input)

            # Make sure to return the correct type
            return EvaluationOutput(
                score=result["score"], test_pass=True if result["score"] > 0.5 else False, reason=result["reasoning"]
            )

        async def evaluate_async(self, evaluation_case: EvaluationData[str, str]) -> EvaluationOutput:
            return self.evaluate(evaluation_case)

    # 4. Create an experiment
    experiment = Experiment[str, str](
        cases=[test_case1, test_case2, test_case3, test_case4], evaluators=[LangChainCriteriaEvaluator()]
    )

    # 4.5. (Optional) Save the experiment
    experiment.to_file("async_third_party_dataset")

    # 5. Run evaluations
    reports = await experiment.run_evaluations_async(get_response)
    return reports[0]


if __name__ == "__main__":
    start = datetime.datetime.now()
    report = asyncio.run(async_third_party_example())
    end = datetime.datetime.now()
    print("Async: ", end - start)  # Async:  0:00:24.050895
    report.to_file("async_third_party_report")
    report.run_display(include_actual_output=True)
