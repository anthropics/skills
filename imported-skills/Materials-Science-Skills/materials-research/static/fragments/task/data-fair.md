# Task: FAIR Data Package and Data Availability

Goal: prepare a FAIR-aligned dataset package and a journal-ready data availability statement for a materials manuscript.

Required workflow:

1. Identify the data layers that must be shared: raw measurements, processed tables, analysis scripts, and metadata.
2. Choose repository/journal-compliant formats (CSV for tabular data, plain text for metadata, versioned scripts).
3. Fill in the dataset README with title, authors, license, variable dictionary, units, and instrument/method fields.
4. Write a data availability statement that states what is available, where, and under what access terms.
5. Run a FAIR audit against the evidence contract: findable, accessible, interoperable, reusable.

Default output:

- Dataset README draft.
- Data availability statement paragraph.
- Metadata checklist status.
- Recommended repository and file naming.
- Gaps or red flags (missing units, missing raw data, non-open license conflicts).

When the user provides actual data files or tables, hand off to `materials-data` to build the full FAIR package.

Do not invent values for missing metadata; flag them explicitly.
