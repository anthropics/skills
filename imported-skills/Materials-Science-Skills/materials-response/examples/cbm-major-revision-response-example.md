# CBM Major Revision Response Example

## Reviewer Comment

The manuscript requires stronger evidence to support the claimed chemical bonding mechanism between the modified asphalt binder and aggregates. Furthermore, the durability of the mixture is questionable without long-term moisture-conditioning data. Lastly, the presentation of the microstructure (SEM) lacks clear scale bars, and the mechanical test results are reported without any statistical error bars.

## Good Response

We thank the reviewer for this constructive assessment. In the revised response, each requested item is tied either to confirmed manuscript evidence or to an explicit author-input flag where the evidence is not yet supplied.

### R1.1: Chemical Bonding Mechanism
**Concern:** Strong mechanism claims lack direct chemical evidence.
**Response:**
We agree that the chemical bonding mechanism was not sufficiently supported by direct evidence in the original draft. If FTIR or another direct characterization result is available, the response should state the verified method, sample condition, and observed feature. If not, the mechanism language should be softened and marked for author input: `[AUTHOR_INPUT_NEEDED: confirm whether direct chemical evidence is available and provide the verified peak/feature assignment.]`

We have also softened the mechanism claims in the text, changing "demonstrates chemical bonding" to "indicates a temperature-dependent chemical modification at the interface."

**Manuscript Action:**
1. Revised Section [X] (Page [P], Lines [L-L]) to insert the confirmed evidence or the limitation statement.
2. Modified the conclusion phrasing (Page [P], Lines [L-L]) using more bounded claims:
```diff
-The modification reaction demonstrates a strong covalent chemical bond at all aggregate interfaces.
+The available [method] evidence suggests [bounded mechanism interpretation], indicating [limited claim supported by the verified data].
```

---

### R1.2: Moisture-Conditioning Durability
**Concern:** Durability evaluation is insufficient without moisture damage testing.
**Response:**
We agree that moisture-conditioning data is essential for assessing durability. If moisture-conditioning data are available, report the verified standard, conditioning protocol, replicate count, and retention metrics. If not, state the scope boundary and add a limitation: `[AUTHOR_INPUT_NEEDED: confirm durability dataset, protocol, replicate count, and figure/table location.]`

**Manuscript Action:**
1. Added/updated Figure/Table [X] with verified durability results, or added a limitation statement if data are unavailable.
2. Inserted durability analysis in Section [X] (Page [P], Lines [L-L]).

---

### R1.3: Microstructure Scale Bars and Statistical Error Bars
**Concern:** Blurry SEM presentation and missing statistical variation indicators.
**Response:**
We apologize for the poor presentation. We have replaced or relabeled the micrographs only where updated files are supplied, and we have added variability indicators where replicate data are available. `[AUTHOR_INPUT_NEEDED: confirm revised image files, scale bars, replicate count, and statistical summary.]`

**Manuscript Action:**
1. Replaced/relabeled Figure [X] (Page [P]) with verified scale information.
2. Updated Figure/Table [X] with error bars based on confirmed replicates.
3. Inserted statistical methodology statement in Section [X] (Page [P], Lines [L-L]).

## Why This Works

This response is effective because:
1. It preserves the reviewer's composite comment and splits it into clear, trackable sub-IDs (R1.1, R1.2, R1.3).
2. It maps every response to a concrete manuscript action, using explicit line ranges and showing markdown diffs of the changes.
3. It keeps all claims bounded by verified evidence or flags missing evidence before drafting.
4. It avoids defensive excuses about equipment or time, directly providing the requested data and statistical qualifiers.
