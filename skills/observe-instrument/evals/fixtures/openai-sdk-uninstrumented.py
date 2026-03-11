"""
Customer Support Agent — Raw OpenAI SDK
NOT yet instrumented with Observe SDK

A tool-calling agent that helps customers check order status and process refunds.

Tools:
  - get_order_status: Look up an order by ID
  - process_refund: Process a refund for an order
"""

import os
import json
from dotenv import load_dotenv

from openai import OpenAI

load_dotenv()

client = OpenAI()


def get_order_status(order_id: str) -> str:
    """Look up the status of an order by its ID."""
    statuses = {
        "ORD-001": "shipped",
        "ORD-002": "processing",
        "ORD-003": "delivered",
    }
    status = statuses.get(order_id, "not_found")
    if status == "not_found":
        return f"Order {order_id} not found."
    return f"Order {order_id} status: {status}"


def process_refund(order_id: str, reason: str) -> str:
    """Process a refund for the given order."""
    return (
        f"Refund initiated for order {order_id}. "
        f"Reason: {reason}. "
        f"You will receive confirmation within 3-5 business days."
    )


TOOLS = [
    {
        "type": "function",
        "function": {
            "name": "get_order_status",
            "description": "Look up the status of an order by its ID",
            "parameters": {
                "type": "object",
                "properties": {
                    "order_id": {"type": "string", "description": "The order ID to look up"}
                },
                "required": ["order_id"],
            },
        },
    },
    {
        "type": "function",
        "function": {
            "name": "process_refund",
            "description": "Process a refund for an order",
            "parameters": {
                "type": "object",
                "properties": {
                    "order_id": {"type": "string", "description": "The order ID to refund"},
                    "reason": {"type": "string", "description": "Reason for the refund"},
                },
                "required": ["order_id", "reason"],
            },
        },
    },
]

TOOL_FUNCTIONS = {
    "get_order_status": get_order_status,
    "process_refund": process_refund,
}


def run_support_agent(user_message: str) -> str:
    """Run the customer support agent for a given user message."""
    messages = [
        {
            "role": "system",
            "content": "You are a helpful customer support agent. Use tools to help customers with their orders.",
        },
        {"role": "user", "content": user_message},
    ]

    while True:
        response = client.chat.completions.create(
            model=os.getenv("LLM_MODEL", "gpt-4o-mini"),
            messages=messages,
            tools=TOOLS,
        )
        message = response.choices[0].message
        messages.append(message)

        if message.tool_calls:
            for tool_call in message.tool_calls:
                fn_name = tool_call.function.name
                fn_args = json.loads(tool_call.function.arguments)
                result = TOOL_FUNCTIONS[fn_name](**fn_args)
                messages.append({
                    "role": "tool",
                    "tool_call_id": tool_call.id,
                    "content": result,
                })
        else:
            return message.content


def main():
    print("Customer Support Agent")
    print("Try: 'What is the status of order ORD-001?' or 'I want a refund for ORD-002'")
    print("-" * 50)

    while True:
        user_input = input("\nYou: ").strip()
        if not user_input:
            continue
        if user_input.lower() in ["quit", "exit", "q"]:
            print("Goodbye!")
            break
        response = run_support_agent(user_input)
        print(f"Agent: {response}")


if __name__ == "__main__":
    main()
