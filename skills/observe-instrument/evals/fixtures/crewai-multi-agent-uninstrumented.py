"""
Research and Publishing Pipeline — CrewAI Multi-Agent
NOT yet instrumented with Observe SDK

Two sequential crews coordinated by a pipeline:
  - research_crew: researcher + analyst agents gather and analyze information
  - publishing_crew: editor + publisher agents refine and publish content
"""

import os
from dotenv import load_dotenv

from crewai import Agent, Task, Crew, Process
from crewai.tools import tool as crewai_tool
from langchain_openai import ChatOpenAI

load_dotenv()

llm = ChatOpenAI(model=os.getenv("LLM_MODEL", "gpt-4o-mini"))


@crewai_tool("search_web")
def search_web(query: str) -> str:
    """Search the web for information on a given topic."""
    return f"Search results for '{query}': Key facts and recent developments."


@crewai_tool("analyze_data")
def analyze_data(data: str) -> str:
    """Analyze research data and extract key insights."""
    return f"Analysis of data: Key insights extracted from {data[:200]}..."


@crewai_tool("edit_content")
def edit_content(content: str) -> str:
    """Edit and improve content for clarity and style."""
    return f"Edited content: {content[:400]}..."


@crewai_tool("format_for_publish")
def format_for_publish(content: str, format: str = "blog") -> str:
    """Format content for publishing in a specific format."""
    return f"[{format.upper()}] {content[:500]}"


researcher = Agent(
    role="Senior Researcher",
    goal="Find comprehensive information on the given topic",
    backstory="Expert at finding and gathering relevant information from multiple sources.",
    tools=[search_web],
    llm=llm,
    verbose=True,
)

analyst = Agent(
    role="Data Analyst",
    goal="Analyze research findings and extract actionable insights",
    backstory="Skilled at interpreting data and identifying key patterns and insights.",
    tools=[analyze_data],
    llm=llm,
    verbose=True,
)

editor = Agent(
    role="Content Editor",
    goal="Refine and polish content for quality and clarity",
    backstory="Experienced editor who ensures content is clear, engaging, and error-free.",
    tools=[edit_content],
    llm=llm,
    verbose=True,
)

publisher = Agent(
    role="Content Publisher",
    goal="Format and prepare content for final publication",
    backstory="Specialist in formatting content for various publishing platforms.",
    tools=[format_for_publish],
    llm=llm,
    verbose=True,
)


def run_research_crew(topic: str) -> str:
    research_task = Task(
        description=f"Research the topic: {topic}. Gather comprehensive information.",
        expected_output="Detailed research findings with key facts",
        agent=researcher,
    )
    analysis_task = Task(
        description="Analyze the research findings and extract key insights.",
        expected_output="Structured analysis with actionable insights",
        agent=analyst,
    )
    crew = Crew(
        agents=[researcher, analyst],
        tasks=[research_task, analysis_task],
        process=Process.sequential,
        verbose=True,
    )
    return crew.kickoff()


def run_publishing_crew(research: str) -> str:
    edit_task = Task(
        description=f"Edit and improve this research content: {research}",
        expected_output="Polished, well-structured content",
        agent=editor,
    )
    publish_task = Task(
        description="Format the edited content for blog publication.",
        expected_output="Publication-ready content",
        agent=publisher,
    )
    crew = Crew(
        agents=[editor, publisher],
        tasks=[edit_task, publish_task],
        process=Process.sequential,
        verbose=True,
    )
    return crew.kickoff()


def run_pipeline(topic: str) -> str:
    research = run_research_crew(topic)
    published = run_publishing_crew(str(research))
    return str(published)


def main():
    topic = input("Enter a topic: ").strip() or "the future of AI agents"
    result = run_pipeline(topic)
    print("\nPublished Content:\n", result)


if __name__ == "__main__":
    main()
