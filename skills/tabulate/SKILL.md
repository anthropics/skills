---
name: tabulate
description: >
  Formats any information as clean, well-structured Markdown tables in the chat.
  Use this skill whenever the user provides data, a list of items, comparison info,
  research results, key-value pairs, or any structured content that could benefit
  from being presented as a table — even if they don't explicitly ask for one.
  Trigger for things like "here are the specs", "compare these options", "list the
  steps and their durations", "show me the results", or any multi-attribute data.
  Prefer tables over bullet lists or prose whenever two or more attributes exist
  per item.
---

# Tabulate

When given data of any kind, your job is to figure out the best table structure and render it as a clean Markdown table. The goal is to make information scannable and easy to compare at a glance.

## How to decide on columns and rows

Think of each *item* (person, product, event, country, option, etc.) as a row, and each *property* of that item as a column. If the data is more like a time series or sequence, the step/date/order can be the first column.

If the user provides raw or messy data, infer sensible column names. Prefer short, clear header labels. Don't over-engineer it — a simple, readable table beats a complex one.

## Formatting rules

- Use proper Markdown table syntax with header separators (`|---|`)
- Left-align text columns, right-align numbers
- Use `—` for missing or N/A values rather than leaving cells blank
- Keep cell content concise; if a value is long, summarize it
- Add a short sentence before the table if context would help the reader

## When there's too much data for one table

If the data naturally splits into groups (e.g., different categories, time periods), use multiple tables with clear headings rather than one unwieldy table. Explain the split briefly.

## Example

User gives: "apples cost $1.20, bananas $0.50, cherries $3.00 per lb — and apples last 2 weeks, bananas 5 days, cherries 1 week"

Output:

| Fruit    | Price ($/lb) | Shelf Life |
|----------|-------------:|------------|
| Apples   |         1.20 | 2 weeks    |
| Bananas  |         0.50 | 5 days     |
| Cherries |         3.00 | 1 week     |
