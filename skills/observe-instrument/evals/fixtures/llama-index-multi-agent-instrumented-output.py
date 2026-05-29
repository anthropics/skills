"""
Research and Writing Pipeline — LlamaIndex Multi-Agent
NOT yet instrumented with Observe SDK

Two specialized AgentWorkflows coordinated by an async pipeline:
  - ResearchAgent: searches and summarizes topics
  - WritingAgent: turns research into polished content
"""

import os
import asyncio
from dotenv import load_dotenv

from llama_index.llms.openai import OpenAI
from llama_index.core.agent.workflow import AgentWorkflow
from llama_index.core import Settings

from ioa_observe.sdk import Observe
from ioa_observe.sdk.decorators import agent, graph, workflow
from ioa_observe.sdk.tracing import session_start

load_dotenv()

Observe.init(
    app_name="llama_index_multi_agent",
    api_endpoint=os.getenv("OTLP_HTTP_ENDPOINT", "http://localhost:4318")
)

llm = OpenAI(model=os.getenv("LLM_MODEL", "gpt-4o-mini"))
Settings.llm = llm


def search_topic(query: str) -> str:
    """Search for information about a topic."""
    return f"Research results for '{query}': Key facts and recent developments."


def summarize_research(text: str) -> str:
    """Summarize research findings into key points."""
    return f"Summary: {text[:300]}..."


def draft_article(research: str, tone: str = "professional") -> str:
    """Draft an article based on research findings."""
    return f"[{tone.upper()} ARTICLE] Based on research: {research[:400]}..."


def polish_content(draft: str) -> str:
    """Polish and refine a draft article."""
    return f"Polished: {draft}"


@graph(name="research_agent_graph")
@agent(name="research_agent")
class ResearchAgent:
    def __init__(self, llm):
        self.workflow = AgentWorkflow.from_tools_or_functions(
            [search_topic, summarize_research],
            llm=llm,
            system_prompt="You are a research specialist. Search for information and provide comprehensive summaries.",
        )

    async def run(self, topic: str) -> str:
        response = await self.workflow.run(user_msg=f"Research this topic thoroughly: {topic}")
        return str(response)

    def get_workflow(self):
        return self.workflow


@graph(name="writing_agent_graph")
@agent(name="writing_agent")
class WritingAgent:
    def __init__(self, llm):
        self.workflow = AgentWorkflow.from_tools_or_functions(
            [draft_article, polish_content],
            llm=llm,
            system_prompt="You are a writing specialist. Turn research into engaging, well-structured content.",
        )

    async def run(self, research: str) -> str:
        response = await self.workflow.run(user_msg=f"Write an article based on: {research}")
        return str(response)

    def get_workflow(self):
        return self.workflow


@workflow(name="multi_agent_pipeline")
async def run_pipeline(topic: str) -> str:
    research_agent = ResearchAgent(llm=llm)
    writing_agent = WritingAgent(llm=llm)

    research = await research_agent.run(topic)
    article = await writing_agent.run(research)
    return article


async def main():
    session_start()
    topic = input("Enter a topic: ").strip() or "the future of AI agents"
    result = await run_pipeline(topic)
    print("\nFinal Article:\n", result)


if __name__ == "__main__":
    asyncio.run(main())
