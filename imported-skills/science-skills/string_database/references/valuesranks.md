# Values/Ranks Enrichment API

This API performs GSEA-like enrichment on full datasets (e.g., complete
differential expression analysis or ranking results) to find pathways enriched
at the top, bottom, or both ends of your value distribution. **This is an
asynchronous API process.**

## Step 1: Get an API Key (Once per session)

Generate a free, anonymous key required to submit full datasets.

```bash
uv run scripts/string_cli.py valuesranks-key --output /tmp/api_key.json
```

Read the JSON output to get the `"api_key"` value.

## Step 2: Submit the Job

Prepare a tab-separated text file. The script will automatically strip headers
and skip lines that don't have at least two tab-separated columns or lack a
valid numeric value in the second column.

*   **Column 1:** Protein identifier (STRING IDs are fastest).
*   **Column 2:** Associated value (e.g., p-value, fold-change, rank).

```bash
uv run scripts/string_cli.py valuesranks-submit \
  --api_key YOUR_EXTRACTED_KEY \
  --input_file /tmp/my_data.tsv \
  --species 10090 \
  --output /tmp/submit_response.json
```

Read the response JSON to extract the `"job_id"`.

## Step 3: Check Job Status & Download

You can either poll the status occasionally, or use the `--wait` flag to
automatically poll the job and download the final TSV result once successful.

```bash
uv run scripts/string_cli.py valuesranks-status \
  --api_key YOUR_EXTRACTED_KEY \
  --job_id EXTRACTED_JOB_ID \
  --wait \
  --output /tmp/job_results.tsv
```

Without `--wait`, wait until `"status": "success"` is returned. When completed,
the JSON will contain a `"download_url"` where you can fetch the final TSV
enrichment results.
