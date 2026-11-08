# File Operations - Strands Agent for File Management

This [example](https://github.com/strands-agents/docs/blob/main/docs/examples/python/file_operations.py) demonstrates how to create a Strands agent specialized in file operations, allowing users to read, write, search, and modify files through natural language commands. It showcases how Strands agents can be configured to work with the filesystem in a safe and intuitive manner.

## Overview

| Feature            | Description                            |
| ------------------ | -------------------------------------- |
| **Tools Used**     | file_read, file_write, editor          |
| **Complexity**     | Beginner                               |
| **Agent Type**     | Single Agent                           |
| **Interaction**    | Command Line Interface                 |
| **Key Focus**      | Filesystem Operations                  |

## Tool Overview

The file operations agent utilizes three primary tools to interact with the filesystem. 

1. The `file_read` tool enables reading file contents through different modes, viewing entire files or specific line ranges, searching for patterns within files, and retrieving file statistics. 
2. The `file_write` tool allows creating new files with specified content, appending to existing files, and overwriting file contents. 
3. The `editor` tool provides capabilities for viewing files with syntax highlighting, making targeted modifications, finding and replacing text, and inserting text at specific locations. Together, these tools provide a comprehensive set of capabilities for file management through natural language commands.

## Code Structure and Implementation

### Agent Initialization

The agent is created with a specialized system prompt focused on file operations and the tools needed for those operations.

```python
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
```

### Using the File Operations Tools

The file operations agent demonstrates two powerful ways to use the available tools:


#### 1. Natural Language Instructions

For intuitive, conversational interactions:

```python
# Let the agent handle all the file operation details
response = file_agent("Read the first 10 lines of /etc/hosts")
response = file_agent("Create a new file called notes.txt with content 'Meeting notes'")
response = file_agent("Find all functions in my_script.py that contain 'data'")
```

Behind the scenes, the agent interprets the natural language query and selects the appropriate tool to execute.

#### 2. Direct Method Calls

For more autonomy over file operations, you can use this approach:

```python
# Read a file directly
file_content = file_agent.tool.file_read(
    path="/path/to/some_file.txt"
)

# Write to a file directly
result = file_agent.tool.file_write(
    path="/path/to/output.txt",
    content="This is new content for the file."
)

# Use the editor tool for more complex operations
edit_result = file_agent.tool.editor(
    command="str_replace",
    path="/path/to/code.py",
    old_str="function_name",
    new_str="new_function_name"
)
```

## Key Features and Capabilities

### 1. Reading Files

The agent can read files in various ways:

- **Full File Reading**:
  ```
  Read the file ~/strands_test_file.txt
  ```

- **Line Range Reading**:
  ```
  Show me lines 2-4 of ~/strands_test_file.txt
  ```

- **Pattern Searching**:
  ```
  Find all lines containing "commands" in the test file
  ```

- **File Statistics**:
  ```
  How many lines are in ~/strands_test_file.txt?
  ```

### 2. Writing Files

The agent can create and modify files:

- **Appending Content**:
  ```
  Add the line "This is an appended line" to ~/strands_test_file.txt
  ```

- **Overwriting Files**:
  ```
  Overwrite ~/new_file.txt with "This is new content"
  ```

### 3. Advanced Editing

The agent can perform more complex editing operations:

- **Text Replacement**:
  ```
  In ~/strands_test_file.txt, replace "test" with "sample"
  ```

- **Line Insertion**:
  ```
  Insert "New line here" after line 3 in ~/strands_test_file.txt
  ```

- **Finding Line Numbers**:
  ```
  What line contains the word "commands" in the test file?
  ```

### Example Commands and Responses

**Command 1**: Read the test file

**Response**:
```
I've read the file at ~/strands_test_file.txt:

This is a test file created by Strands File Operations example.
You can read, edit, or modify this file using the agent.
Try commands like:
1. Read this file
2. Add a new line to this file
3. Replace 'test' with 'sample' in this file

The file contains 5 lines and 207 characters.
```

**Command 2**: Add a new line saying "This is a new line I added"

**Response**:
```
I've successfully appended the new line to ~/strands_test_file.txt.

The file now contains:
This is a test file created by Strands File Operations example.
You can read, edit, or modify this file using the agent.
Try commands like:
1. Read this file
2. Add a new line to this file
3. Replace 'test' with 'sample' in this file
This is a new line I added

The file now has 6 lines.
```

**Command 3**: Replace all instances of "test" with "sample" in the file

**Response**:
```
I've successfully replaced all instances of "test" with "sample" in ~/strands_test_file.txt.

Changes made:
- Line 1: "This is a sample file created by Strands File Operations example."
- Line 3: "Try commands like:"

2 occurrences were replaced in total.
```

## Extending the Example

Here are some ways you could extend this file operations agent:

1. **Directory Operations**: Add capabilities for creating, listing, and navigating directories
2. **Batch Operations**: Enable operations on multiple files matching patterns
3. **Permission Management**: Add the ability to view and modify file permissions
4. **Content Analysis**: Implement features for analyzing file contents (word count, statistics)
5. **Version Control Integration**: Add capabilities to interact with git or other version control systems
