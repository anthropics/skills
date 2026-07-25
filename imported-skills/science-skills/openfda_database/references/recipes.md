# openFDA Query Recipes

Common query patterns for drugs, devices, foods, tobacco, cosmetics, animal and
veterinary products, substances, transparency data, adverse events, recalls,
labeling, approvals, shortages, 510(k) clearances, NDC lookups, any FDA safety
or regulatory data query, and more.

## Drug Adverse Event Reactions (Top N)

```bash
uv run scripts/openfda_query.py count \
  --category drug --endpoint event \
  --search "patient.drug.medicinalproduct:metformin" \
  --count_field "patient.reaction.reactionmeddrapt.exact" \
  --summary 10 --output /tmp/metformin_reactions.json
```

## Drug Indication / Reasons for Use

```bash
uv run scripts/openfda_query.py count \
  --category drug --endpoint event \
  --search "patient.drug.medicinalproduct:metformin" \
  --count_field "patient.drug.drugindication.exact" \
  --summary 5 --output /tmp/metformin_indications.json
```

## Drug Route of Administration

```bash
uv run scripts/openfda_query.py count \
  --category drug --endpoint event \
  --search "patient.drug.medicinalproduct:aspirin" \
  --count_field "patient.drug.drugadministrationroute.exact" \
  --summary 5 --output /tmp/aspirin_routes.json
```

## Patient Sex Demographics Breakdown

```bash
uv run scripts/openfda_query.py count \
  --category drug --endpoint event \
  --search "patient.drug.medicinalproduct:aspirin" \
  --count_field "patient.patientsex" \
  --output /tmp/aspirin_sex.json
```

## Events by Reporter Country

```bash
uv run scripts/openfda_query.py count \
  --category drug --endpoint event \
  --search "patient.drug.medicinalproduct:ozempic" \
  --count_field "primarysource.reportercountry.exact" \
  --summary 5 --output /tmp/ozempic_countries.json
```

## Drug-Drug Co-Occurrence

```bash
uv run scripts/openfda_query.py search \
  --category drug --endpoint event \
  --search "patient.drug.openfda.generic_name:METFORMIN+AND+patient.drug.openfda.generic_name:SITAGLIPTIN" \
  --limit 3 --output /tmp/cooccurrence.json
```

## NDC by Manufacturer

```bash
uv run scripts/openfda_query.py search \
  --category drug --endpoint ndc \
  --search "openfda.manufacturer_name:pfizer" \
  --limit 10 --output /tmp/pfizer_ndc.json
```

## Voluntary vs Mandated Recalls

```bash
uv run scripts/openfda_query.py count \
  --category drug --endpoint enforcement \
  --count_field "voluntary_mandated.exact" \
  --output /tmp/voluntary_mandated.json
```

## Drug Shortages

```bash
uv run scripts/openfda_query.py search \
  --category drug --endpoint shortages \
  --limit 10 --output /tmp/shortages.json
```

## COVID-19 Serology Test Performance Data

```bash
uv run scripts/openfda_query.py search \
  --category device --endpoint covid19serology \
  --limit 3 --output /tmp/covid_serology.json
```

## Animal & Veterinary Adverse Events (Dogs, Cats, etc.)

```bash
uv run scripts/openfda_query.py search \
  --category animalandveterinary --endpoint event \
  --search "animal.species:Dog" \
  --limit 3 --output /tmp/dog_events.json
```

## Device Adverse Events

```bash
uv run scripts/openfda_query.py search \
  --category device --endpoint event \
  --limit 3 --output /tmp/device_events.json
```

## Food Adverse Events (CAERS)

```bash
uv run scripts/openfda_query.py search \
  --category food --endpoint event \
  --limit 3 --output /tmp/food_events.json
```

## Substance / UNII Lookup

```bash
uv run scripts/openfda_query.py search \
  --category other --endpoint unii \
  --limit 3 --output /tmp/unii_data.json
```

## Historical FDA Documents

```bash
uv run scripts/openfda_query.py search \
  --category other --endpoint historicaldocument \
  --limit 3 --output /tmp/historical_docs.json
```

## Download All Results (Auto-Paginate)

```bash
uv run scripts/openfda_query.py download \
  --category drug --endpoint event \
  --search "patient.drug.medicinalproduct:ozempic+AND+serious:1" \
  --limit 100 --all_results \
  --output /tmp/ozempic_serious.json
```
