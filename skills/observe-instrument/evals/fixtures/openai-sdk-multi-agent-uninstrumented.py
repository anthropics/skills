"""
Research and Writing Pipeline — OpenAI SDK Multi-Agent
NOT yet instrumented with Observe SDK

An orchestrator that coordinates two specialist agents:
  - research_agent: searches and summarizes topics using tools
  - writing_agent: drafts and polishes articles using tools
  - orchestrator: decides which agent to call and combines results
"""

import os
import json
from dotenv import load_dotenv

from openai import OpenAI

load_dotenv()

client = OpenAI()
MODEL = os.getenv("LLM_MODEL", "gpt-4o-mini")


def search_web(query: str) -> str:
    """Search the web for information on a topic."""
    return f"Search results for '{query}': Key facts and recent developments on this subject."


def summarize_text(text: str) -> str:
    """Summarize a long text into key points."""
    return f"Key points: {text[:300]}..."


def draft_article(research: str, tone: str = "professional") -> str:
    """Draft an article based on research."""
    return f"[{tone.upper()}] Draft article based on: {research[:400]}..."


def polish_draft(draft: str) -> str:
    """Polish and refine a draft for publication."""
    return f"Polished: {draft}"


RESEARCH_TOOLS = [
    {
        "type": "function",
        "function": {
            "name": "search_web",
            "description": "Search the web for information on a topic",
            "parameters": {
                "type": "object",
                "properties": {"query": {"type": "string"}},
                "required": ["query"],
            },
        },
    },
    {
        "type": "function",
        "function": {
            "name": "summarize_text",
            "description": "Summarize a long text into key points",
            "parameters": {
                "type": "object",
                "properties": {"text": {"type": "string"}},
                "required": ["text"],
            },
        },
    },
]

WRITING_TOOLS = [
    {
        "type": "function",
        "function": {
            "name": "draft_article",
            "description": "Draft an article based on research",
            "parameters": {
                "type": "object",
                "properties": {
                    "research": {"type": "string"},
                    "tone": {"type": "string", "default": "professional"},
                },
                "required": ["research"],
            },
        },
    },
    {
        "type": "function",
        "function": {
            "name": "polish_draft",
            "description": "Polish and refine a draft for publication",
            "parameters": {
                "type": "object",
                "properties": {"draft": {"type": "string"}},
                "required": ["draft"],
            },
        },
    },
]

RESEARCH_FUNCTIONS = {"search_web": search_web, "summarize_text": summarize_text}
WRITING_FUNCTIONS = {"draft_article": draft_article, "polish_draft": polish_draft}


def _run_tool_loop(messages: list, tools: list, functions: dict) -> str:
    while True:
        response = client.chat.completions.create(
            model=MODEL, messages=messages, tools=tools
        )
        message = response.choices[0].message
        messages.append(message)
        if message.tool_calls:
            for tc in message.tool_calls:
                result = functions[tc.function.name](**json.loads(tc.function.arguments))
                messages.append({"role": "tool", "tool_call_id": tc.id, "content": result})
        else:
            return message.content


def run_research_agent(topic: str) -> str:
    """Research agent that searches and summarizes a topic."""
    messages = [
        {"role": "system", "content": "You are a research specialist. Search for information and provide comprehensive summaries."},
        {"role": "user", "content": f"Research this topic thoroughly: {topic}"},
    ]
    return _run_tool_loop(messages, RESEARCH_TOOLS, RESEARCH_FUNCTIONS)


def run_writing_agent(research: str) -> str:
    """Writing agent that drafts and polishes articles from research."""
    messages = [
        {"role": "system", "content": "You are a writing specialist. Turn research into engaging, well-structured content."},
        {"role": "user", "content": f"Write a polished article based on this research: {research}"},
    ]
    return _run_tool_loop(messages, WRITING_TOOLS, WRITING_FUNCTIONS)


def run_orchestrator(topic: str) -> str:
    """Orchestrator that coordinates the research and writing agents."""
    research = run_research_agent(topic)
    article = run_writing_agent(research)
    return article


def main():
    print("Research and Writing Pipeline")
    print("-" * 40)
    while True:
        user_input = input("\nEnter a topic (or 'quit'): ").strip()
        if not user_input or user_input.lower() in ["quit", "exit", "q"]:
            break
        result = run_orchestrator(user_input)
        print(f"\nArticle:\n{result}")


if __name__ == "__main__":
    main()
