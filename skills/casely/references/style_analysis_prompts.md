# Test Style Analysis Methodology

This document outlines how Casely extracts formatting and stylistic rules from example test cases to ensure consistent generation.

## Analysis Process

1. **Structure Extraction:**
   - Detects all column headers from the Markdown table.
   - Identifies the order of columns to maintain the sequence in new test cases.
   - Infers data types (numeric, date, enum) from the content of the cells.

2. **Stylistic Patterns:**
   - **Preconditions:** Checks if they are numbered (1, 2, 3) or bulleted. Analyzes the level of technical detail.
   - **Steps:** Analyzes the verb tense (imperative, etc.) and punctuation style.
   - **Expected Results:** Detects if results are grouped or single sentences.

3. **Taxonomy Discovery:**
   - Identifies allowed values for Priority, Status, and other enumerated fields.
   - Detects specific prefixes or suffixes used in IDs or titles.

## Persistence

The results of this analysis are saved in the project's `test_style_guide.md`. This file serves as the strict template for all future generations.

## Language Detection

The analyzer detects the primary language of the examples. All future test cases for that project will be generated in that language by default to ensure consistency with the existing test base.
