"""
Currency Converter Agent — LangGraph

Tools:
  - get_exchange_rate: Fetches live rates from frankfurter.app (no API key needed)
  - convert_currency: Converts an amount between currencies

Run:
  OPENAI_API_KEY=sk-... python3 examples/currency-converter.py
"""

import os
import requests
from dotenv import load_dotenv

from langchain_openai import ChatOpenAI
from langchain_core.tools import tool as langchain_tool
from langchain_core.messages import HumanMessage
from langgraph.graph import StateGraph, MessagesState, START, END
from langgraph.prebuilt import create_react_agent

load_dotenv()

llm = ChatOpenAI(model=os.getenv("LLM_MODEL", "gpt-4o-mini"))


@langchain_tool
def get_exchange_rate(base: str, target: str) -> str:
    """Get the current exchange rate from one currency to another.

    Args:
        base: Source currency code (e.g. USD, EUR, GBP, JPY)
        target: Target currency code (e.g. USD, EUR, GBP, JPY)
    """
    try:
        resp = requests.get(
            "https://api.frankfurter.app/latest",
            params={"from": base.upper(), "to": target.upper()},
            timeout=5,
        )
        resp.raise_for_status()
        data = resp.json()
        rate = data["rates"][target.upper()]
        return f"1 {base.upper()} = {rate} {target.upper()} (as of {data['date']})"
    except Exception as e:
        return f"Error fetching exchange rate: {e}"


@langchain_tool
def convert_currency(amount: float, base: str, target: str) -> str:
    """Convert an amount from one currency to another using live rates.

    Args:
        amount: The amount to convert
        base: Source currency code (e.g. USD, EUR, GBP, JPY)
        target: Target currency code (e.g. USD, EUR, GBP, JPY)
    """
    try:
        resp = requests.get(
            "https://api.frankfurter.app/latest",
            params={"amount": amount, "from": base.upper(), "to": target.upper()},
            timeout=5,
        )
        resp.raise_for_status()
        data = resp.json()
        converted = data["rates"][target.upper()]
        return f"{amount} {base.upper()} = {converted} {target.upper()} (as of {data['date']})"
    except Exception as e:
        return f"Error converting currency: {e}"


_react_agent = create_react_agent(
    llm,
    tools=[get_exchange_rate, convert_currency],
    prompt=(
        "You are a helpful currency converter assistant. "
        "Use the available tools to answer questions about exchange rates and conversions. "
        "Always use standard 3-letter currency codes (USD, EUR, GBP, JPY, etc.)."
    ),
)


def currency_agent_node(state: MessagesState) -> dict:
    result = _react_agent.invoke(state)
    return {"messages": result["messages"]}


def build_graph():
    builder = StateGraph(MessagesState)
    builder.add_node("currency_agent", currency_agent_node)
    builder.add_edge(START, "currency_agent")
    builder.add_edge("currency_agent", END)
    return builder.compile()


def main():
    print("Currency Converter Agent")
    print("Live rates from frankfurter.app")
    print("-" * 45)
    print("Example queries:")
    print("  What is 100 USD in EUR?")
    print("  How many Japanese Yen is 50 GBP?")
    print("  Compare USD to CHF and JPY rates")
    print("-" * 45)

    compiled = build_graph()

    while True:
        user_input = input("\nYou: ").strip()
        if not user_input:
            continue
        if user_input.lower() in ["quit", "exit", "q"]:
            print("Goodbye!")
            break

        result = compiled.invoke({"messages": [HumanMessage(content=user_input)]})
        print(f"Agent: {result['messages'][-1].content}")


if __name__ == "__main__":
    main()
