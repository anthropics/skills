# Example LlamaIndex agent — instrumented with Observe SDK
# This is the eval fixture representing a typical agent after instrumentation.

import os
import logging
import warnings

from dotenv import load_dotenv

from ioa_observe.sdk import Observe
from ioa_observe.sdk.decorators import agent, tool, graph
from ioa_observe.sdk.tracing import session_start

from llama_index.llms.openai import OpenAI
from llama_index.core.agent.workflow import AgentWorkflow
from llama_index.core import Settings
from llama_index.core.callbacks import CallbackManager, LlamaDebugHandler

load_dotenv()

Observe.init(
    app_name="math_agent_service",
    api_endpoint=os.getenv("OTLP_HTTP_ENDPOINT", "http://localhost:4318")
)

warnings.filterwarnings("ignore")

# --- Callbacks setup ---

llama_debug = LlamaDebugHandler(print_trace_on_end=True)

logging.basicConfig(level=logging.INFO)
logging.getLogger().addHandler(logging.StreamHandler())

callback_manager = CallbackManager([llama_debug])
Settings.callback_manager = callback_manager


@tool(name="multiply")
def multiply(a: float, b: float) -> float:
    """Multiply two numbers and returns the product"""
    return a * b


@tool(name="add")
def add(a: float, b: float) -> float:
    """Add two numbers and returns the sum"""
    return a + b


llm = OpenAI(model="gpt-4o-mini")


@graph(name="math_agent_graph")
@agent(name="math_agent")
class MathAgentWorkflow:
    def __init__(self, tools, llm, system_prompt):
        self.workflow = AgentWorkflow.from_tools_or_functions(
            tools, llm=llm, system_prompt=system_prompt
        )

    async def run(self, user_msg: str):
        return await self.workflow.run(user_msg=user_msg)

    def get_workflow(self):
        """Return underlying workflow for topology detection"""
        return self.workflow


async def main():
    session_start()
    workflow = MathAgentWorkflow(
        tools=[multiply, add],
        llm=llm,
        system_prompt="You are an agent that can perform basic mathematical operations using tools.",
    )

    response = await workflow.run(user_msg="What is 20+(2*4)?")
    print(response)


if __name__ == "__main__":
    import asyncio

    asyncio.run(main())
