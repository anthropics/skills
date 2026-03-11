"""
Research and Writing Crew — CrewAI
NOT yet instrumented with Observe SDK

A two-agent crew that researches a topic and writes an article:
  - Researcher: uses tools to gather and summarize information
  - Writer: turns research into a readable article
"""

import os
from dotenv import load_dotenv

from crewai import Agent, Task, Crew, Process
from crewai.tools import tool
from langchain_openai import ChatOpenAI

load_dotenv()

llm = ChatOpenAI(model=os.getenv("LLM_MODEL", "gpt-4o-mini"))


@tool("search_topic")
def search_topic(query: str) -> str:
    """Search for information about a topic.

    Args:
        query: The search query
    """
    # Simulated search — replace with real implementation
    return f"Research results for '{query}': Key facts and recent developments on this subject."


@tool("summarize_findings")
def summarize_findings(text: str) -> str:
    """Summarize research findings into concise key points.

    Args:
        text: The text to summarize
    """
    return f"Key points: {text[:300]}..."


researcher = Agent(
    role="Senior Researcher",
    goal="Conduct thorough research on the given topic and gather key insights",
    backstory="An expert researcher with decades of experience finding and synthesizing information.",
    tools=[search_topic, summarize_findings],
    llm=llm,
    verbose=True,
)

writer = Agent(
    role="Content Writer",
    goal="Write compelling, clear content based on research findings",
    backstory="A skilled writer who turns complex research into engaging readable content.",
    llm=llm,
    verbose=True,
)


def run_crew(topic: str) -> str:
    research_task = Task(
        description=f"Research the following topic thoroughly: {topic}. Use tools to gather key facts.",
        expected_output="A comprehensive research summary with key facts and insights",
        agent=researcher,
    )
    write_task = Task(
        description="Based on the research, write a clear and engaging short article of 3-4 paragraphs.",
        expected_output="A well-structured article",
        agent=writer,
    )
    crew = Crew(
        agents=[researcher, writer],
        tasks=[research_task, write_task],
        process=Process.sequential,
        verbose=True,
    )
    return crew.kickoff()


def main():
    topic = input("Enter a topic to research: ").strip() or "the future of AI agents"
    result = run_crew(topic)
    print("\nResult:\n", result)


if __name__ == "__main__":
    main()
