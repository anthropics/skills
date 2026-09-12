# Intuition Protocol API Reference

Complete reference documentation for the Intuition Protocol GraphQL API.

## Endpoints

| Network | URL | Status |
|---------|-----|--------|
| Mainnet | `https://mainnet.intuition.sh/v1/graphql` | Production |
| Testnet | `https://testnet.intuition.sh/v1/graphql` | Testing |

## Data Model

### Atom

The fundamental unit of the knowledge graph. Represents any entity: wallet, contract, person, concept, or project.

| Field | Type | Description |
|-------|------|-------------|
| term_id | numeric | Unique identifier |
| label | string | Human-readable name |
| type | string | Entity type classification |
| image | string | Optional image URL |
| emoji | string | Optional emoji representation |
| created_at | timestamp | Creation timestamp |
| block_number | numeric | Blockchain block of creation |
| creator | Account | Account that created the atom |
| vault | Vault | Associated staking vault |

### Triple

A claim expressed as Subject-Predicate-Object. Connects three Atoms into a semantic relationship.

| Field | Type | Description |
|-------|------|-------------|
| id | numeric | Unique identifier |
| subject | Atom | The entity being described |
| predicate | Atom | The relationship type |
| object | Atom | The target of the relationship |
| subject_id | numeric | Subject atom ID |
| predicate_id | numeric | Predicate atom ID |
| object_id | numeric | Object atom ID |
| vault | Vault | Vault for positive stakes |
| counter_vault | Vault | Vault for negative stakes |
| created_at | timestamp | Creation timestamp |
| block_number | numeric | Blockchain block of creation |
| creator | Account | Account that created the triple |

### Vault

Holds staking positions for Atoms and Triples.

| Field | Type | Description |
|-------|------|-------------|
| id | numeric | Unique identifier |
| total_shares | numeric | Total staked shares |
| current_share_price | numeric | Current price per share |
| position_count | int | Number of unique stakers |
| atom_id | numeric | Associated atom (if atom vault) |
| triple_id | numeric | Associated triple (if triple vault) |

### Position

A user's stake on an Atom or Triple.

| Field | Type | Description |
|-------|------|-------------|
| id | numeric | Unique identifier |
| account | Account | The staking account |
| vault | Vault | The vault staked in |
| shares | numeric | Number of shares held |
| created_at | timestamp | Position creation time |

### Account

A wallet address that interacts with the protocol.

| Field | Type | Description |
|-------|------|-------------|
| id | string | Wallet address |
| label | string | Optional display name |
| image | string | Optional profile image |
| atom_id | numeric | Associated identity atom |

## Query Patterns

### Filtering

Use `where` clauses with comparison operators:

```graphql
atoms(where: { label: { _ilike: "%search%" } })
atoms(where: { term_id: { _eq: 123 } })
atoms(where: { created_at: { _gte: "2024-01-01" } })
triples(where: { subject_id: { _eq: 123 }, predicate_id: { _eq: 456 } })
```

Available operators:
- `_eq` - Equal
- `_neq` - Not equal
- `_gt` - Greater than
- `_gte` - Greater than or equal
- `_lt` - Less than
- `_lte` - Less than or equal
- `_ilike` - Case-insensitive pattern match (use % as wildcard)
- `_in` - In list
- `_nin` - Not in list
- `_is_null` - Is null check

### Ordering

Sort results with `order_by`:

```graphql
atoms(order_by: { created_at: desc })
atoms(order_by: { vault: { total_shares: desc_nulls_last } })
triples(order_by: [{ vault: { total_shares: desc } }, { created_at: desc }])
```

### Pagination

Use `limit` and `offset`:

```graphql
atoms(limit: 10, offset: 0)
atoms(limit: 10, offset: 10)
```

### Aggregations

Get counts and statistics:

```graphql
atoms_aggregate(where: { type: { _eq: "wallet" } }) {
    aggregate {
        count
    }
}

positions_aggregate(where: { vault: { atom_id: { _eq: 123 } } }) {
    aggregate {
        count
        sum {
            shares
        }
    }
}
```

## Common Query Templates

### Find All Claims by a Specific Account

```graphql
query GetAccountClaims($accountId: String!) {
    triples(
        where: { creator: { id: { _eq: $accountId } } }
        order_by: { created_at: desc }
        limit: 50
    ) {
        id
        subject { label }
        predicate { label }
        object { label }
        vault { total_shares }
        created_at
    }
}
```

### Get Entity with All Related Claims

```graphql
query GetEntityFull($atomId: numeric!) {
    atom(id: $atomId) {
        term_id
        label
        type
        image
        vault {
            total_shares
            position_count
            current_share_price
        }
        as_subject_triples(limit: 20, order_by: { vault: { total_shares: desc_nulls_last } }) {
            predicate { label }
            object { label }
            vault { total_shares, position_count }
            counter_vault { total_shares, position_count }
        }
        as_object_triples(limit: 20, order_by: { vault: { total_shares: desc_nulls_last } }) {
            subject { label }
            predicate { label }
            vault { total_shares, position_count }
            counter_vault { total_shares, position_count }
        }
    }
}
```

### Search Across Multiple Fields

```graphql
query SearchAll($term: String!) {
    atoms(
        where: {
            _or: [
                { label: { _ilike: $term } },
                { creator: { label: { _ilike: $term } } }
            ]
        }
        limit: 20
    ) {
        term_id
        label
        type
        creator { id, label }
    }
}
```

### Get Top Stakers Network-Wide

```graphql
query GetTopStakers {
    accounts(
        order_by: { positions_aggregate: { sum: { shares: desc_nulls_last } } }
        limit: 20
    ) {
        id
        label
        positions_aggregate {
            aggregate {
                count
                sum { shares }
            }
        }
    }
}
```

### Find Disputed Claims

Claims with significant counter-stakes indicate disagreement:

```graphql
query GetDisputedClaims {
    triples(
        where: {
            counter_vault: { total_shares: { _gt: "0" } }
        }
        order_by: { counter_vault: { total_shares: desc } }
        limit: 20
    ) {
        subject { label }
        predicate { label }
        object { label }
        vault { total_shares, position_count }
        counter_vault { total_shares, position_count }
    }
}
```

## Trust Assessment Framework

### Signal Interpretation

| Total Shares | Position Count | Interpretation |
|--------------|----------------|----------------|
| > 1000 | > 10 | High visibility, well-attested |
| 100-1000 | 5-10 | Moderate visibility |
| 10-100 | 1-5 | Low visibility, limited attestation |
| < 10 | < 2 | Unknown or very new |

### Trust Ratio Calculation

```
trust_ratio = vault.total_shares / (vault.total_shares + counter_vault.total_shares)
```

| Ratio | Interpretation |
|-------|----------------|
| > 0.9 | Strong consensus, highly trusted |
| 0.7 - 0.9 | Generally positive, some caution |
| 0.5 - 0.7 | Mixed sentiment, disputed |
| 0.3 - 0.5 | Negative sentiment, concerns raised |
| < 0.3 | Strong negative consensus |

### Risk Indicators

Flag entities with:
- No attestations (position_count = 0)
- Only self-attestations (single staker is creator)
- High counter-vault relative to vault
- Recent creation with sudden high stakes
- Claims from low-reputation attestors only

## Error Handling

Common error responses:

| Error | Cause | Resolution |
|-------|-------|------------|
| 400 Bad Request | Malformed query | Check GraphQL syntax |
| 404 Not Found | Invalid endpoint | Verify URL |
| 429 Rate Limited | Too many requests | Implement backoff |
| 500 Server Error | Internal issue | Retry with exponential backoff |

## Rate Limits

- Standard: 100 requests per minute
- Burst: 20 requests per second
- Implement exponential backoff on 429 responses

## SDK Integration

For TypeScript/JavaScript projects, use the official package:

```bash
npm install @0xintuition/graphql
```

```typescript
import { API_URL_PROD, API_URL_DEV } from '@0xintuition/graphql'
```

## Portal Links

Generate links to the Intuition Portal for users:

- Atom: `https://portal.intuition.systems/identity/{term_id}`
- Triple: `https://portal.intuition.systems/claim/{id}`
- Account: `https://portal.intuition.systems/profile/{address}`

## Version History

| Version | Date | Changes |
|---------|------|---------|
| v1.5 | 2025 | Bonding curve vaults, batch operations, positions replace claims |
| v1.0 | 2024 | Initial release |
