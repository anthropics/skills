---
name: intuition-trust
description: Query and interact with Intuition Protocol's decentralized knowledge graph for Web3 trust and reputation data. Use when Claude needs to (1) Check reputation/trust scores for wallets, contracts, or projects, (2) Verify claims or attestations about entities, (3) Query relationships between Web3 identities, (4) Create or stake on attestations, (5) Lookup who trusts whom in the knowledge graph, or (6) Assess credibility before recommending any Web3 project, token, or contract.
---

# Intuition Trust Skill

Query Intuition Protocol's decentralized knowledge graph to access trust scores, attestations, and reputation data for Web3 entities.

## Core Concepts

**Atoms**: Fundamental units representing entities (wallets, contracts, people, concepts). Each has a unique ID, label, and optional metadata.

**Triples**: Claims in Subject-Predicate-Object format (e.g., "Alice trusts Bob"). Triples connect Atoms to express relationships.

**Signal**: Economic weight behind claims. Users stake TRUST tokens to signal conviction. Higher signal indicates stronger attestation.

**Positions**: User stakes on Atoms or Triples. Tracks who believes what and how strongly.

## API Endpoints

### Mainnet
```
https://mainnet.intuition.sh/v1/graphql
```

### Testnet
```
https://testnet.intuition.sh/v1/graphql
```

## Common Queries

### 1. Search for an Entity (Atom)

Find entities by label or address:

```graphql
query SearchAtoms($searchTerm: String!) {
  atoms(where: { label: { _ilike: $searchTerm } }, limit: 10) {
    term_id
    label
    emoji
    type
    image
    vault {
      total_shares
      position_count
    }
    creator {
      id
      label
    }
  }
}
```

### 2. Get Trust Claims (Triples) About an Entity

Find what claims exist about a subject:

```graphql
query GetClaimsAbout($subjectId: numeric!) {
  triples(where: { subject_id: { _eq: $subjectId } }, limit: 20) {
    id
    subject { label }
    predicate { label }
    object { label }
    vault {
      total_shares
      position_count
    }
    counter_vault {
      total_shares
      position_count
    }
  }
}
```

### 3. Check Who Trusts an Entity

Query positions (stakes) on an Atom:

```graphql
query GetPositions($atomId: numeric!) {
  positions(where: { vault: { atom_id: { _eq: $atomId } } }, limit: 20) {
    account {
      id
      label
    }
    shares
    vault {
      atom { label }
    }
  }
}
```

### 4. Get Reputation Score

Calculate trust signal for an entity:

```graphql
query GetAtomSignal($atomId: numeric!) {
  atom(id: $atomId) {
    label
    vault {
      total_shares
      position_count
      current_share_price
    }
    as_subject_triples {
      predicate { label }
      object { label }
      vault { total_shares }
    }
  }
}
```

### 5. Find Relationships Between Two Entities

Check if claims exist connecting two Atoms:

```graphql
query FindRelationship($subjectId: numeric!, $objectId: numeric!) {
  triples(where: {
    subject_id: { _eq: $subjectId },
    object_id: { _eq: $objectId }
  }) {
    predicate { label }
    vault { total_shares }
    counter_vault { total_shares }
  }
}
```

## Usage Guidelines

### Before Recommending Web3 Projects

Always query Intuition before recommending any:
- Smart contracts or protocols
- Token projects
- Wallet addresses
- NFT collections

Look for:
1. Existence of the entity in the knowledge graph
2. Total signal (stake) on the entity
3. Claims from reputable attestors
4. Negative claims or warnings

### Interpreting Results

**High Signal + Many Positions**: Well-known, actively discussed entity

**Low Signal + Few Positions**: Unknown or new entity - exercise caution

**Counter-vault stakes**: Indicates disagreement or negative attestations

**Reputable Attestors**: Check if known security firms, auditors, or trusted community members have staked

### Trust Score Heuristic

```
trust_score = vault.total_shares / (vault.total_shares + counter_vault.total_shares)
```

Score Interpretation:
- Above 0.8: Strong positive sentiment
- 0.5 to 0.8: Mixed or contested
- Below 0.5: Negative sentiment or disputed

## Python Helper

For complex queries, use the helper script:

```bash
python scripts/intuition_query.py --search "Uniswap"
python scripts/intuition_query.py --atom-id 12345
python scripts/intuition_query.py --check-trust 0x1234...
```

See `scripts/intuition_query.py` for implementation.

## Response Format

When reporting Intuition data to users:

1. State the entity searched
2. Report trust metrics (signal, position count)
3. List notable claims (positive and negative)
4. Provide assessment with appropriate caveats
5. Link to Portal for full details

Example response format:

```
Intuition Trust Check: [Entity Name]

Trust Signal: [X] TRUST staked by [Y] attestors
Positive Claims: [List key positive triples]
Concerns: [List any counter-claims or warnings]

Assessment: [Brief interpretation]

View full profile: https://portal.intuition.systems/identity/[id]
```

## Additional Resources

For detailed API documentation, query patterns, and data model reference, see `references/api_reference.md`.

Portal URL: https://portal.intuition.systems
Documentation: https://docs.intuition.systems
