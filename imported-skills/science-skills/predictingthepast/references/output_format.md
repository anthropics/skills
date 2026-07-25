# Output Format Reference

The `--output_json` flag saves a combined JSON file with this top-level
structure. Fields are `null` when the corresponding task was not requested:

```json
{
  "attribution": { ... },
  "restoration": [ ... ],
  "contextualize": [ ... ],
  "embedding": [ ... ],
  "num_windows": 1
}
```

## Parsing output JSON with `jq`

The output JSON may be large (especially with contextualization and saliency
arrays). **DON'T** use `cat` to read the full JSON output into context. Always
use `jq` or write a script to extract only the fields you need.

```bash
# Attribution: top 5 locations with names and scores
jq '.attribution.locations[:5] | .[] | {location_name, score}' /tmp/results.json

# Attribution: top year and weighted average
jq '{top_year: .attribution.top_year, avg_year: .attribution.weighted_average_year}' /tmp/results.json

# Restoration: top 10 predictions with scores
jq '.restoration[0].predictions[:10] | .[] | {text, score}' /tmp/results.json

# Contextualization: top parallels with IDs, scores, and full texts
jq '.contextualize[0] | {ids, score, text}' /tmp/results.json

# Contextualization: just the IDs and scores
jq '.contextualize[] | select(. != null) | [.ids, .score] | transpose | .[] | {id: .[0], score: .[1]}' /tmp/results.json

# Contextualization: top parallel full text
jq -r '.contextualize[0].text[0]' /tmp/results.json

# Embedding: check dimensionality
jq '.embedding | length' /tmp/results.json
```

## Attribution

Present only when `--attribute` is passed.

```json
{
  "input_text": "primurudem basilia donat in ...",
  "locations": [
    {"location_id": 17, "location_name": "Britannia", "score": 0.932}
  ],
  "year_scores": [2.7e-06, "...", 0.071, "..."],
  "year_distribution": {"-795": 2.7e-06, "...", "295": 0.071, "..."},
  "date_saliency": [0.159, 0.112, "..."],
  "location_saliency": [0.082, 0.045, "..."],
  "top_year": 295,
  "weighted_average_year": 248
}
```

Field                   | Description
----------------------- | ------------------------------------------------------
`locations`             | Regions ranked by probability (`location_id`, `score`)
`year_scores`           | Raw probability over 160 bins (10-year intervals)
`year_distribution`     | Same as `year_scores`, keyed by year (−795 to 795 CE)
`top_year`              | Highest-probability year (argmax)
`weighted_average_year` | Probability-weighted mean year
`date_saliency`         | Per-character importance for chronological prediction
`location_saliency`     | Per-character importance for geographical prediction

## Restoration

Present only when `--restore` is passed and the input contains `?` or `#`.
Returned as a list (one entry per window). Each entry:

```json
{
  "input_text": "...donat in ??????????rtis...",
  "top_prediction": "...donat in templum martis...",
  "missing": [28, 29, 30, 31, 32, 33, 34, 35, 36, 37],
  "predictions": [
    {"text": "...templum martis...", "restored": [28, 29, "..."], "score": 0.049}
  ],
  "prediction_saliency": [
    {"text": "...donat in -?????????rtis...", "restored_idx": 28, "saliency": [0.0, 0.12, "..."]}
  ]
}
```

| Field                 | Description                                       |
| --------------------- | ------------------------------------------------- |
| `missing`             | Character indices where `?`/`#` markers appeared  |
| `predictions`         | Beam search results with full `text`, `restored`, |
:                       : `score`                                           :
| `prediction_saliency` | Step-by-step saliency for the greedy (top)        |
:                       : prediction                                        :

## Contextualization

Present only when `--contextualize` is passed. Returns the top K parallels
(controlled by `--contextualize_top_k`, default 10) with **full inscription
texts**. Contextualization results are only written to `--output_json` — they
are **not** printed to stdout. Use `jq` to extract them (or write your own
script if `jq` is unavailable).

Returned as a list (one entry per window). Each entry:

```json
{
  "ids": ["HD000012", "HD055268"],
  "ids_alt": [{"TMid": "199228", "geoID": "21473"}, {"TMid": "212458"}],
  "text": ["Primurudem Basilia donat in templum Martis ...", "..."],
  "location_ids": [17, 17],
  "location_names": ["Britannia", "Britannia"],
  "date_min": [301, 151],
  "date_max": [400, 270],
  "partner_link": [null, null],
  "score": [0.983, 0.838]
}
```

| Field                             | Description                              |
| --------------------------------- | ---------------------------------------- |
| `ids`                             | `record_number` from the dataset (`HD*`, |
:                                   : `EDCS-*`). Note\: this is NOT the        :
:                                   : internal numeric `id` used for           :
:                                   : train/test/valid splitting.              :
| `ids_alt`                         | Alternative IDs (Trismegistos `TMid`,    |
:                                   : `geoID`)                                 :
| `text`                            | Full text of the parallel inscription    |
| `location_ids` / `location_names` | Geographic region ID and name            |
| `date_min` / `date_max`           | Date range (CE), `null` if unknown       |
| `partner_link`                    | URL to partner database (if available)   |
| `score`                           | Cosine similarity (0–1)                  |

## Embedding

Present only when `--embedding` is passed. A flat list of 384 floats
representing the model's internal text embedding (averaged across token
positions).

```json
[0.0123, -0.456, 0.789, "... (384 floats total)"]
```
