"""
Research and Writing Pipeline — LangGraph Multi-Agent
NOT yet instrumented with Observe SDK

A supervisor-routed multi-agent system:
  - supervisor: routes between researcher and writer
  - researcher: gathers information using a search tool
  - writer: formats results using a formatting tool
"""

import os
from typing import Literal
from dotenv import load_dotenv

from langchain_openai import ChatOpenAI
from langchain_core.messages import HumanMessage
from langchain_core.tools import tool as langchain_tool
from langgraph.constants import START, END
from langgraph.graph import MessagesState, StateGraph
from langgraph.prebuilt import create_react_agent
from langgraph.types import Command

load_dotenv()

llm = ChatOpenAI(model=os.getenv("LLM_MODEL", "gpt-4o-mini"))


@langchain_tool
def search_web(query: str) -> str:
    """Search the web for information on a topic."""
    return f"Search results for '{query}': Key facts and recent developments."


@langchain_tool
def format_article(content: str, style: str = "blog") -> str:
    """Format research content into a structured article."""
    return f"[{style.upper()}] {content[:500]}..."


research_agent = create_react_agent(
    llm,
    tools=[search_web],
    prompt="You are a researcher. Search for information and return detailed findings.",
)

writing_agent = create_react_agent(
    llm,
    tools=[format_article],
    prompt="You are a writer. Format the provided research into a clear article.",
)


def supervisor_node(state: MessagesState) -> Command[Literal["researcher", "writer", "__end__"]]:
    messages = state["messages"]
    last_message = messages[-1].content if messages else ""

    if "research" in last_message.lower() or len(messages) == 1:
        return Command(goto="researcher")
    elif "write" in last_message.lower() or "format" in last_message.lower():
        return Command(goto="writer")
    else:
        return Command(goto="__end__")


def research_node(state: MessagesState) -> Command[Literal["supervisor"]]:
    result = research_agent.invoke(state)
    return Command(
        update={"messages": [HumanMessage(content=result["messages"][-1].content, name="researcher")]},
        goto="supervisor",
    )


def write_node(state: MessagesState) -> Command[Literal["supervisor"]]:
    result = writing_agent.invoke(state)
    return Command(
        update={"messages": [HumanMessage(content=result["messages"][-1].content, name="writer")]},
        goto="supervisor",
    )


def build_graph():
    builder = StateGraph(MessagesState)
    builder.add_node("supervisor", supervisor_node)
    builder.add_node("researcher", research_node)
    builder.add_node("writer", write_node)
    builder.add_edge(START, "supervisor")
    return builder.compile()


def main():
    compiled = build_graph()
    while True:
        user_input = input("\nYou: ").strip()
        if not user_input:
            continue
        if user_input.lower() in ["quit", "exit", "q"]:
            print("Goodbye!")
            break
        for event in compiled.stream({"messages": [HumanMessage(content=user_input)]}):
            for value in event.values():
                if "messages" in value:
                    print("Agent:", value["messages"][-1].content)


if __name__ == "__main__":
    main()
