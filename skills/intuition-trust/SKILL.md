# Intuition Protocol Trust Skill

Query the Intuition Protocol knowledge graph to assess trust, reputation, and claims about Web3 entities.

## Overview

Intuition is a decentralized knowledge graph where users stake ETH on claims about entities (wallets, contracts, projects, people). This skill enables Claude to query trust data for informed decision-making.

## API Endpoints

- Mainnet: `https://mainnet.intuition.sh/v1/graphql`
- Testnet: `https://testnet.intuition.sh/v1/graphql`

## Core Concepts

| Concept | Description |
|---------|-------------|
| Term | A unique entity in the knowledge graph (can be an Atom or Triple) |
| Atom | A single entity (wallet, project, concept) |
| Triple | A claim in Subject-Predicate-Object format |
| Position | A stake on a term (ETH commitment) |
| Signal | An action recording stake changes |

## Common Queries

### Search Entities

```graphql
query SearchTerms($query: String!) {
    search_term(args: { query: $query }, limit: 10) {
        id
        type
        atom {
            label
            image
            type
            creator { id label }
        }
        total_assets
        total_market_cap
        positions_aggregate {
            aggregate { count }
        }
    }
}
```

### Get Term Details

```graphql
query GetTerm($termId: String!) {
    term(id: $termId) {
        id
        type
        atom {
            label
            type
            created_at
        }
        triple {
            subject { label }
            predicate { label }
            object { label }
        }
        total_assets
        total_market_cap
    }
}
```

### Get Claims About Entity

```graphql
query GetTriples($subjectId: String!) {
    triples(where: { subject: { term_id: { _eq: $subjectId } } }, limit: 20) {
        term_id
        subject { label }
        predicate { label }
        object { label }
        term {
            total_assets
            positions_aggregate { aggregate { count } }
        }
    }
}
```

### Get Positions on Term

```graphql
query GetPositions($termId: String!) {
    positions(where: { vault: { term_id: { _eq: $termId } } }, limit: 20) {
        account { id label }
        shares
        created_at
    }
}
```

### Get Account Info

```graphql
query GetAccount($accountId: String!) {
    account(id: $accountId) {
        id
        label
        positions(limit: 10) {
            shares
            vault {
                term {
                    atom { label }
                    triple {
                        subject { label }
                        predicate { label }
                        object { label }
                    }
                }
            }
        }
    }
}
```

## Trust Assessment Framework

### Metrics to Consider

1. **Total Assets**: ETH staked on the term (in wei, divide by 10^18 for ETH)
2. **Position Count**: Number of unique stakers
3. **Market Cap**: Total value including bonding curve appreciation
4. **Staker Quality**: Are stakers reputable accounts?

### Trust Levels

| Level | Criteria |
|-------|----------|
| High | >1 ETH staked AND >10 positions |
| Medium | >0.1 ETH staked OR >5 positions |
| Low | Some stake but limited validation |
| Unverified | No stakes found |

## Use Cases

1. **Verify wallet reputation** before recommending interactions
2. **Check project claims** (audited, team doxxed, etc.)
3. **Assess contract trust** before suggesting approvals
4. **Validate identity claims** (Twitter, GitHub links)
5. **Research entity relationships** in the knowledge graph

## Python Helper

A helper script is available at `scripts/intuition_query.py`:

```bash
# Search for entities
python intuition_query.py --search "Uniswap"

# Get trust score
python intuition_query.py --trust-score "0x..." --format text

# Get account info
python intuition_query.py --account "0x..."

# Use testnet
python intuition_query.py --search "test" --testnet
```

## Best Practices

1. Always check trust data before recommending wallet interactions
2. Consider both total stake AND number of stakers
3. Look for claims from reputable accounts
4. Cross-reference multiple data points
5. Note when data is limited or entity is unverified

## Response Guidelines

When reporting trust data:
- State the entity label and type
- Report total ETH staked (convert from wei)
- Note position count
- List top stakers if notable
- Provide clear trust assessment
- Caveat when data is limited
