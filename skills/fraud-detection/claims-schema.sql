-- Canonical claims schema — the contract every detector reads.
-- ADDITIVE ONLY: add columns/tables, never rename or drop. A payer field that doesn't map stays
-- NULL; a payer field detectors could use becomes a new column (propose via LOAD-CLAIMS.md step 4).
-- screen.js loads small corpora into memory; large corpora are queried in-place by the detectors.

CREATE TABLE IF NOT EXISTS claims (
  claim_id            VARCHAR PRIMARY KEY,
  billing_npi         VARCHAR,
  rendering_npi       VARCHAR,
  referring_npi       VARCHAR,
  bene_id             VARCHAR,
  specialty           VARCHAR,      -- rendering provider specialty/taxonomy (cohort key for D7/D15/D16)
  claim_type          VARCHAR,      -- professional | institutional | pharmacy | dental | transport
  adjudication_status VARCHAR,      -- paid | denied | reversed | pending
  cob_paid_amount     DOUBLE,       -- D21: >0 means a primary payer already paid
  frequency_code      VARCHAR,      -- 1 original / 7 replacement / 8 void
  source_payer        VARCHAR,      -- provenance: which payer/feed this row came from
  source_format       VARCHAR       -- provenance: 837P | 837I | FHIR | CSV | SQL | ...
);

CREATE TABLE IF NOT EXISTS claim_lines (
  claim_id       VARCHAR,
  line_no        INTEGER,
  hcpcs          VARCHAR,
  modifiers      VARCHAR[],         -- e.g. ['59','95']
  units          DOUBLE,
  dos_from       DATE,
  dos_to         DATE,
  allowed_amount DOUBLE,
  pos            VARCHAR,           -- place-of-service (02/10 = telehealth) — optional
  revenue_code   VARCHAR,           -- institutional only
  ndc            VARCHAR            -- pharmacy only
);

CREATE TABLE IF NOT EXISTS claim_dx (
  claim_id VARCHAR,
  dx_code  VARCHAR,
  dx_seq   INTEGER
);

-- Payer-supplied member master + enrollment spans (from the payer's 834/member system; NOT public
-- CMS data). Program/state are properties of an ENROLLMENT span, not a claim — a member can be
-- dually enrolled (Medicaid + Medicare), which is exactly the COB/TPL signal D21 reads.
CREATE TABLE IF NOT EXISTS members (
  bene_id VARCHAR PRIMARY KEY,
  dob     DATE,
  dod     DATE,         -- date of death (D3 after-death)
  sex     VARCHAR,
  zip     VARCHAR
);

CREATE TABLE IF NOT EXISTS enrollment (
  bene_id        VARCHAR,
  plan_id        VARCHAR,
  program        VARCHAR,      -- medicare | medicaid (routes D1/D2/D11 NCCI tables via ctx.lob)
  enrolled_state VARCHAR,      -- 2-letter state (routes D3 state-exclusion list)
  effective_from DATE,
  effective_to   DATE,         -- NULL = open-ended
  term_reason    VARCHAR
);

CREATE TABLE IF NOT EXISTS inpatient_stays (
  bene_id        VARCHAR,
  admit_date     DATE,
  discharge_date DATE,
  facility_npi   VARCHAR
);

-- ─────────────────────────────────────────────────────────────────────────────
-- Payer overlay tables — payer-side rows that augment the public reference layer
-- for identity-keyed and benchmark detectors. Populate from the payer's own
-- exclusion/credentialing/benchmark feeds; leave empty when the public CMS
-- tables in reference.duckdb are sufficient.
-- ─────────────────────────────────────────────────────────────────────────────

-- Payer-side identity records that augment public reference for D3/D9/D10.
CREATE TABLE IF NOT EXISTS leie_overlay (
  npi       VARCHAR,
  excl_type VARCHAR,
  excl_date VARCHAR
);

CREATE TABLE IF NOT EXISTS revoked_overlay (
  npi                        VARCHAR,
  revocation_efctv_dt        DATE,
  reenrollment_bar_exprtn_dt DATE,
  revocation_rsn             VARCHAR
);

-- Benchmark overlay for D15–D18 — payer-supplied cohort/row augmentation.
CREATE TABLE IF NOT EXISTS nppes_overlay (
  npi             VARCHAR,
  registry_status VARCHAR,
  state           VARCHAR,
  specialty       VARCHAR
);

CREATE TABLE IF NOT EXISTS dme_cohort_overlay (
  specialty VARCHAR,
  n         INTEGER,
  median    DOUBLE,
  mad       DOUBLE
);

CREATE TABLE IF NOT EXISTS partd_row_overlay (
  npi                 VARCHAR,
  prscrbr_type        VARCHAR,
  opioid_prscrbr_rate DOUBLE,
  opioid_tot_clms     INTEGER,
  tot_clms            INTEGER
);

CREATE TABLE IF NOT EXISTS partd_cohort_overlay (
  specialty VARCHAR,
  n         INTEGER,
  median    DOUBLE,
  mad       DOUBLE
);

CREATE TABLE IF NOT EXISTS saturation_overlay (
  state                                VARCHAR,
  type_of_service                      VARCHAR,
  county                               VARCHAR,
  number_of_providers                  INTEGER,
  average_number_of_users_per_provider DOUBLE,
  number_of_providers_description      VARCHAR,
  moratorium                           VARCHAR
);

CREATE TABLE IF NOT EXISTS owner_overlay (
  owner_id   VARCHAR,
  owner_name VARCHAR,
  npi        VARCHAR
);
