#!/usr/bin/env python3
"""
# 📁 File Operations Strands Agent

A specialized Strands agent focused on file operations.

## What This Example Shows

This example demonstrates:
- Creating a specialized Strands agent with selected tools
- Setting a custom system prompt for file operations
- Reading files with various modes and options
- Writing and modifying files through Strands Agents
- Using the editor tool for more complex file operations

## Key Tools

- **file_read**: Read file contents with different modes
  - View entire files
  - View specific line ranges
  - Search for patterns
  - Get file statistics

- **file_write**: Create and modify files
  - Write text to files
  - Append to existing files

- **editor**: Advanced file modifications
  - View files with syntax highlighting
  - Make targeted modifications
  - Find and replace text
  - Insert text at specific locations

## Usage Examples

Simple file reading:
```
Read the first 10 lines of /etc/hosts
```

Creating files:
```
Create a new file called hello.txt with content "Hello, Strands!"
```

Searching files:
```
Find all occurrences of "import" in my_script.py
```

Advanced editing:
```
In my_script.py, replace all instances of "old_function" with "new_function"
```

## Tips for File Operations

- Always specify the full path for files to avoid confusion
- Use relative paths when appropriate for portability
- Check file existence before attempting to read or modify
- Handle file permissions appropriately
"""

import os

from strands import Agent
from strands_tools import file_read, file_write, editor

# Define a focused system prompt for file operations
FILE_SYSTEM_PROMPT = """You are a file operations specialist. You help users read, 
write, search, and modify files. Focus on providing clear information about file 
operations and always confirm when files have been modified.

Key Capabilities:
1. Read files with various options (full content, line ranges, search)
2. Create and write to files
3. Edit existing files with precision
4. Report file information and statistics

Always specify the full file path in your responses for clarity.
"""

# Create a file-focused agent with selected tools
file_agent = Agent(
    system_prompt=FILE_SYSTEM_PROMPT,
    tools=[file_read, file_write, editor],
)


# Example usage
if __name__ == "__main__":
    print("\n📁 File Operations Strands Agent 📁\n")
    print("This agent helps with file operations using Strands Agents.")
    print("Type your request below or 'exit' to quit:\n")

    # Create a test file to play with
    test_file = os.path.join(os.path.expanduser("~"), "strands_test_file.txt")
    if not os.path.exists(test_file):
        with open(test_file, "w") as f:
            f.write("This is a test file created by Strands File Operations example.\n")
            f.write("You can read, edit, or modify this file using the agent.\n")
            f.write("Try commands like:\n")
            f.write("1. Read this file\n")
            f.write("2. Add a new line to this file\n")
            f.write("3. Replace 'test' with 'sample' in this file\n")
        print(f"Created a test file at: {test_file}")

    # Interactive loop
    while True:
        try:
            user_input = input("\n> ")
            if user_input.lower() == "exit":
                print("\nGoodbye! 👋")
                break

            # Call the file agent directly
            file_agent(user_input)
            
        except KeyboardInterrupt:
            print("\n\nExecution interrupted. Exiting...")
            break
        except Exception as e:
            print(f"\nAn error occurred: {str(e)}")
            print("Please try a different request.")
