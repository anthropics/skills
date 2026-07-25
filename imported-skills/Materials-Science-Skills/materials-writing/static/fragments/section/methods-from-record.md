# Methods (from experiment record)

When an `experiment-record.yaml` is provided, generate the Methods section in this order:

1. **Materials overview** — List each entry in `materials` with role, name, supplier (if known), and specification.
2. **Sample preparation** — Convert each `processing` step into a chronological paragraph, including equipment and key parameters.
3. **Experimental design** — State the design type, factors, levels, and response variables from `design` and `response_variables`.
4. **Characterization / testing** — For each entry in `characterization`, state the technique, standard, specimen geometry, conditioning, and instrument.
5. **Data analysis** — Mention replicate count and any planned statistical method.

Use placeholders such as `[needs supplier]` for missing fields. Do not invent measurements or standards.

## Example paragraph structure

> [Material name] was used as the [role]. The samples were prepared by [processing step] using [equipment] at [parameters]. A [design.type] was employed with [factors] as factors and [response_variables] as responses. [Characterization name] was performed according to [standard] using [instrument] under [conditioning]. Each test was repeated [replicate_count] times.
