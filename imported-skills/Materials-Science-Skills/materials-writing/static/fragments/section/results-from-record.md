# Results (from experiment record)

When an `experiment-record.yaml` is provided, generate the Results section as follows:

1. **Design summary** — Briefly state the design type, factor ranges, and response variables.
2. **Run-level results** — For each run in `design.runs`, create a placeholder sentence such as:
   > Run [run_id] ([factor_levels]) yielded [response_variable_1] of [value] [unit] and [response_variable_2] of [value] [unit].
   Replace `[value]` with actual data if provided; otherwise use `[needs quantitative result]`.
3. **Key trends** — Summarize expected trends based on `objectives` and `factors`, using cautious language (`increased with`, `decreased with`).
4. **Data table reference** — Reference the dataset package or a table placeholder.

Do not interpret mechanisms in Results; reserve mechanism claims for the Discussion.
