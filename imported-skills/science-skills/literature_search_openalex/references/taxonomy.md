# Taxonomy Reference

The topic taxonomy has four levels: domain > field > subfield > topic.
Domains, Fields, Subfields, and SDGs are separate entity types that can be
queried independently.

## Domains

| Field                                  | Sort | Group_by | Filter |
| -------------------------------------- | :--: | :------: | :----: |
| `cited_by_count`                       |   ✓  |    ✓     |    ✓   |
| `display_name`                         |   ✓  |          |    ✓   |
| `fields.id`                            |   ✓  |    ✓     |    ✓   |
| `from_created_date`                    |   ✓  |          |    ✓   |
| `id`                                   |   ✓  |    ✓     |    ✓   |
| `works_count`                          |   ✓  |    ✓     |    ✓   |

## Fields

| Field                                  | Sort | Group_by | Filter |
| -------------------------------------- | :--: | :------: | :----: |
| `cited_by_count`                       |   ✓  |    ✓     |    ✓   |
| `display_name`                         |   ✓  |          |    ✓   |
| `domain.id`                            |   ✓  |    ✓     |    ✓   |
| `from_created_date`                    |   ✓  |          |    ✓   |
| `id`                                   |   ✓  |    ✓     |    ✓   |
| `subfields.id`                         |   ✓  |    ✓     |    ✓   |
| `works_count`                          |   ✓  |    ✓     |    ✓   |

## Subfields

| Field                                  | Sort | Group_by | Filter |
| -------------------------------------- | :--: | :------: | :----: |
| `cited_by_count`                       |   ✓  |    ✓     |    ✓   |
| `display_name`                         |   ✓  |          |    ✓   |
| `domain.id`                            |   ✓  |    ✓     |    ✓   |
| `field.id`                             |   ✓  |    ✓     |    ✓   |
| `from_created_date`                    |   ✓  |          |    ✓   |
| `id`                                   |   ✓  |    ✓     |    ✓   |
| `topics.id`                            |   ✓  |    ✓     |    ✓   |
| `works_count`                          |   ✓  |    ✓     |    ✓   |

## Sustainable Development Goals (SDGs)

| Field                                  | Sort | Group_by | Filter |
| -------------------------------------- | :--: | :------: | :----: |
| `cited_by_count`                       |   ✓  |    ✓     |    ✓   |
| `display_name`                         |   ✓  |          |    ✓   |
| `display_name.search` **(deprecated)** |      |          |    ✓   |
| `from_created_date`                    |   ✓  |          |    ✓   |
| `id`                                   |   ✓  |    ✓     |    ✓   |
| `works_count`                          |   ✓  |    ✓     |    ✓   |
