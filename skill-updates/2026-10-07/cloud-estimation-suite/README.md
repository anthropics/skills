# Cloud estimation skill suite

Eleven self-contained skills produce a shared Excel estimate with delivery
effort in JH (jour-homme), monthly operations effort in JH/month and cloud
costs in EUR. The primary deliverable is an editable, recalculated `.xlsx`.
The public example is completely synthetic: its suppliers, prices, workload,
capacity, topology and source statements are invented. It is a methodology
demonstration, not a provider quote or an approved production design.

## User guides

- [Guide d'utilisation en français](../../../docs/guide-cloud-estimation.md)
- [English user guide](../../../docs/cloud-estimation-guide.md)

The guides explain why and when to use each skill, which inputs to prepare,
copy-ready prompts, and how to review the XLSX/JH deliverable. Start with
`cloud-estimation-orchestrator` when two or more domains overlap.

## Install and route

Use the eleven ZIP-compatible `.skill` files in [bundles](bundles/).
Inspect [the bundle manifest](bundles/manifest.json) and compare SHA-256 hashes
before extracting each complete top-level skill folder into your assistant's
skills directory (for Codex, the `skills` directory under your Codex
configuration). Keep its `SKILL.md`, references, scripts, assets, licence and
member manifest together. Install only into an absent destination or review
an existing installation before replacing it. No skill needs this authoring
tree at runtime, and installation does not authorize cloud changes.

For work spanning several domains, start with the orchestrator. Route a
single-domain request directly to its skill. The shared registry is
[tooling/domain-registry.json](tooling/domain-registry.json).

| Request | Skill | Main responsibility |
|---|---|---|
| Consolidated estimate or overlapping estimates | [cloud-estimation-orchestrator](cloud-estimation-orchestrator/SKILL.md) | Shared intake, ownership, reconciliation and deduplication |
| Infrastructure delivery | [infra-work-estimator](infra-work-estimator/SKILL.md) | Environment, networking, compute and storage work |
| Hosting architecture options | [cloud-architecture-advisor](cloud-architecture-advisor/SKILL.md) | Suitability, recovery and operational tradeoffs |
| Kubernetes suitability or platform | [kubernetes-architect](kubernetes-architect/SKILL.md) | Explicit cluster requirements and platform operations |
| Build and delivery pipelines | [cicd-devsecops-estimator](cicd-devsecops-estimator/SKILL.md) | Promotion, rollback, runners and security evidence |
| Host security baseline | [server-hardening-estimator](server-hardening-estimator/SKILL.md) | Controls, patching and restore evidence |
| Workload sizing and overload | [hosting-capacity-simulator](hosting-capacity-simulator/SKILL.md) | CPU, memory, storage, IOPS, bandwidth, concurrency and failure reserve |
| Comparable provider alternatives | [cloud-provider-selector](cloud-provider-selector/SKILL.md) | Eligibility, dated prices, delivery effort and three-year TCO |
| Billing and usage optimisation | [finops-optimizer](finops-optimizer/SKILL.md) | Savings evidence, implementation effort, risk and reversibility |
| Source-to-target transition | [cloud-migration-estimator](cloud-migration-estimator/SKILL.md) | Preparation, transfer, integrity, cutover, rollback and hypercare |
| Inventory and flow diagram | [cloud-architecture-diagrammer](cloud-architecture-diagrammer/SKILL.md) | Evidence-backed topology embedded in Excel |

Choose the instructions needed for the scope; routing does not imply agent
delegation or permission to mutate infrastructure. All runtime copies are
materialized from [tooling](tooling/) with manifests detecting divergent
local edits. The public runtime requires Python 3.11+, openpyxl and Pillow;
pytest and PyYAML are needed for the authoring tests. Native Excel COM is available on
Windows through PowerShell or pywin32; LibreOffice is the other native engine.

## Workbook and synthetic example

Open [examples/synthetic-cloud-estimate.xlsx](examples/synthetic-cloud-estimate.xlsx).
It contains all twelve contract sheets: `00_Lisez-moi`, `01_Hypotheses`,
`02_Inventaire`, `03_Architecture`, `04_Taches_JH`, `05_Couts_cloud`,
`06_Scenarios`, `07_Phasage`, `08_Risques`, `09_Arbitrages`, `10_Sources`
and `11_Synthese`. The architecture sheet contains the final PNG plus a
machine-readable inventory/flow manifest. Inputs use blue text, formulas
black, cross-sheet formulas green, and key editable assumptions yellow.

The example has Provider A/B/C and Economique/Standard/Resilient alternatives
at the same service perimeter: production runtime, scheduled Development
and Staging runtime, and a shared managed data/platform envelope including
backup, network/egress, logging, build/registry and support. Each combination
has three cost rows. Alternatives are compared separately, never summed into
one budget. The provider prices are assumptions; there are no live SKU,
regional eligibility or service-level claims. A real estimate must replace
the envelope with a verified bill of materials and dated official quotes.

Ten uniquely identified tasks have one canonical owner, dependencies,
deliverables, acceptance criteria and low/likely/high JH. TASK-01 records
gross, evidenced existing coverage and net work; only net JH enter the
estimate. TASK-02 explicitly overrides the global scenario to Resilient.
With Standard selected, Build is 19 JH / EUR 12,350 and human Run is
1 JH/month / EUR 650/month at the illustrative EUR 650/JH rate. The
eight-hour JH convention is editable; these estimates already use JH.
The all-tasks Build scenario comparisons are 9.5/17/30 JH; the selected
19 JH includes the task override. Provider A Standard cloud is EUR
171/month, separately from human Run. The constant-demand three-year TCO
is EUR 41,906 for Provider A, including Build, human Run and that cloud alternative.
Taxes, FX, discounts, growth and non-cloud OPEX are explicitly excluded.

The separate `ComparaisonFournisseurs` table in `06_Scenarios` compares the
reference Standard scenario for all three providers over three years.
`comparison_scenario` is independent of the global task selection; explicit
task overrides are still included. Every metric except the provider label
is a formula, independently reconciled against the synthetic assertions.

| Provider | Build JH | Human Run JH/month | Cloud EUR/month | Three-year TCO EUR |
|---|---|---|---|---|
| Provider A | 19 | 1 | 171 | 41,906 |
| Provider B | 19 | 1 | 186 | 42,446 |
| Provider C | 19 | 1 | 201 | 42,986 |

At EUR 650/JH, each alternative uses `19 * 650 + 36 * (1 * 650 + cloud)`.
Changing the TJM or horizon recalculates each alternative independently;
changing the global scenario alone preserves the Standard comparison.
The generator reports this matrix as structured `provider_comparison` JSON.

The scenario deliberately retains open findings:

- Foundation Build needs 9 JH against 6 JH available in its provisional
  period, a 3 JH overload against collective capacity across Foundation roles.
  The six JH are not a per-role capacity. The delivery lead must verify
  individual role availability; DEC-SCHEDULE requires replanning before approval.
- Standard high-band CPU demand is 12 vCPU against `4 * 2 * 0.75 = 6`
  effective vCPU, an overload ratio of 2. The inputs also distinguish memory,
  shared storage, IOPS, bandwidth and concurrency. These are assumptions,
  not benchmark results; scaling ceilings and a replica reserve do not prove
  recovery across zones or regions.
- SYN-02 and SYN-03 contradict each other about one versus two replicas.
  DEC-CONFLICT keeps the selected branch provisional and prices its deltas:
  EUR 45/month cloud, 2 JH Build and 0.5 JH/month human Run.
- DEC-FINOPS schedules non-production runtime reversibly: forecast savings
  EUR 22.50–45/month, selected EUR 45/month. TASK-07 implements it and
  TASK-06 reviews it monthly. Costs already include scheduling; savings
  must not be subtracted again. Equal-scope measurements and wakeup checks
  are required to validate savings, with rollback to always-on available.
- DEC-ARCH provisionally selects a managed runtime and shared backend.
  Kubernetes is explicitly Non applicable for this scope. Backup, restore,
  isolation and regional recovery still need evidence.

The diagram shows four inventory components and the sole explicitly
evidenced HTTPS flow from production runtime to the managed backend.
Development and Staging have no inferred connections. Neutral symbols make
the diagram public and keep it independent of supplier trademarks.

The generation inputs and independent hand-derived expectations are
[synthetic-cloud-brief.json](examples/synthetic-cloud-brief.json),
[synthetic-architecture.json](examples/synthetic-architecture.json) and
[synthetic-assertions.json](examples/synthetic-assertions.json).
The generator consumes only the repository's public synthetic fixture.

## Regenerate and validate

Run from this suite directory; `rtk` is the repository's shell-command proxy.
If used outside this repository, the commands after `rtk` are ordinary Python
commands. Install dependencies into your chosen Python environment:

```powershell
rtk python -m pip install openpyxl Pillow pytest PyYAML
rtk python examples/generate_example.py --require-native
rtk python -m pytest tests/test_acceptance.py -v
rtk python -m pytest tests -v
rtk python tooling/anonymisation.py .
rtk python tooling/sync_shared.py
rtk python tooling/build_bundles.py
rtk git diff --check
```

Use `--output-dir <absent-or-reviewed-directory>` to regenerate separately.
The generator writes its named outputs in that directory. `--require-native`
fails unless Excel COM or LibreOffice actually recalculates and saves the
file. Without it, a calibrated limited Python evaluator is allowed and its
fallback warning must be disclosed. It supports this suite's arithmetic,
references, IF, SUM, SUMIF and SUMIFS equality formulas; unknown syntax fails
closed. It is not a general Excel engine or a native-opening proof.

The generator prints JSON evidence for the engine, native opening, formula
and cache counts, validation, inventory and anonymisation. Validation reloads
formulas and `data_only=True` caches, checks every formula and group total,
and compares the supplied independent assertions. The shipped example has
132 formulas and 140 numerical reconciliations, zero formula/semantic/cache
errors and a zero inventory delta. Author and revision metadata are normalized
after native saving without resaving through openpyxl or losing caches.
Never save a workbook loaded with `data_only=True`: it would lose formulas.

The end-to-end tests also regenerate in an isolated directory, require all
expected outputs, detect leftover temporary files and verify that Windows
can replace and delete the recalculated XLSX. They exercise the actual
shared scripts and public artifact. They do not prove that every declarative
skill behaves correctly under an independent agent request; that is a
separate skill-authoring forward-test gate.

For reproducibility, run `build_bundles.py` with two different output
directories and compare all eleven archives plus `manifest.json` byte for
byte. Bundle timestamps, paths, modes and entry ordering are normalized;
stored compression avoids compressor-version differences. The native-saved
XLSX is semantically regenerable, but its bytes can vary by spreadsheet
version. Only the eleven skill archives have the byte-reproducibility claim.

## Icon and public-data policy

[tooling/icon-policy.json](tooling/icon-policy.json) defaults to neutral
labelled symbols. Optional official provider PNG packs must be obtained
locally from the policy's exact official sources, include their source URL,
licence/trademark notice and asset SHA-256 hashes, and meet file/dimension
limits. Source allowlists and hashes verify the declared pack, not provider
authorship. Missing, corrupt, unsupported or undocumented packs fall back
to neutral symbols. No provider logos are bundled or generated; preserve
applicable notices when exporting diagrams.

No private workbook is read by the generator or included in public outputs.
Use reserved example domains and neutral identifiers in reusable content.
Keep client source workbooks, credentials, account/project IDs, internal
paths, quotes and actual topology outside the public tree. The scanner reads
text, filenames, binary text and nested Office/skill archives, fails closed
on incomplete scanning, and reports redacted locations. The exact Microsoft
and OpenXML schema hosts are technical allowlisted domains. Public revision
identifiers are normalized independently of local Excel metadata.

Pass a private external policy with `--policy <path>` to supplement generic
checks with private denylist terms and source-workbook names; do not publish
that policy. The sole excluded positive-control fixture deliberately contains
forbidden samples for scanner tests. A zero-match scan is necessary but does
not prove anonymity: independently review combinations of vertical, geography,
dates, amounts, counts and provider mix before releasing any real-derived
example. This example was constructed exclusively from synthetic public data.

Each skill includes the full [CC BY 4.0 licence](tooling/LICENSE).
Credit the repository maintainers when sharing or adapting the methodology.
Provider trademarks and assets remain subject to their separate terms.
