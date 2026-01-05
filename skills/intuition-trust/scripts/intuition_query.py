#!/usr/bin/env python3
"""
Intuition Protocol GraphQL Query Helper

A utility script for querying the Intuition Protocol knowledge graph.
Supports searching atoms, retrieving trust data, and checking entity reputation.

Usage:
    python intuition_query.py --search "Uniswap"
    python intuition_query.py --atom-id 12345
    python intuition_query.py --address 0x1234...
    python intuition_query.py --triples-about 12345
    python intuition_query.py --trust-score 12345
"""

import argparse
import json
import sys
from urllib.request import Request, urlopen
from urllib.error import URLError, HTTPError
from typing import Optional, Dict, Any, List

# API Endpoints
MAINNET_URL = "https://mainnet.intuition.sh/v1/graphql"
TESTNET_URL = "https://testnet.intuition.sh/v1/graphql"


def execute_query(query: str, variables: Dict[str, Any], use_testnet: bool = False) -> Dict[str, Any]:
    """Execute a GraphQL query against the Intuition API."""
    url = TESTNET_URL if use_testnet else MAINNET_URL
    
    payload = json.dumps({
        "query": query,
        "variables": variables
    }).encode("utf-8")
    
    request = Request(
        url,
        data=payload,
        headers={
            "Content-Type": "application/json",
            "Accept": "application/json"
        },
        method="POST"
    )
    
    try:
        with urlopen(request, timeout=30) as response:
            return json.loads(response.read().decode("utf-8"))
    except HTTPError as e:
        return {"error": f"HTTP Error {e.code}: {e.reason}"}
    except URLError as e:
        return {"error": f"URL Error: {e.reason}"}
    except Exception as e:
        return {"error": f"Request failed: {str(e)}"}


def search_atoms(search_term: str, limit: int = 10, use_testnet: bool = False) -> Dict[str, Any]:
    """Search for atoms by label."""
    query = """
    query SearchAtoms($searchTerm: String!, $limit: Int!) {
        atoms(
            where: { label: { _ilike: $searchTerm } }
            limit: $limit
            order_by: { vault: { total_shares: desc_nulls_last } }
        ) {
            term_id
            label
            type
            image
            created_at
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
    """
    variables = {"searchTerm": f"%{search_term}%", "limit": limit}
    return execute_query(query, variables, use_testnet)


def get_atom_by_id(atom_id: int, use_testnet: bool = False) -> Dict[str, Any]:
    """Retrieve a specific atom by its ID."""
    query = """
    query GetAtom($atomId: numeric!) {
        atom(id: $atomId) {
            term_id
            label
            type
            image
            created_at
            block_number
            vault {
                total_shares
                position_count
                current_share_price
            }
            creator {
                id
                label
            }
            as_subject_triples_aggregate {
                aggregate {
                    count
                }
            }
            as_object_triples_aggregate {
                aggregate {
                    count
                }
            }
        }
    }
    """
    variables = {"atomId": atom_id}
    return execute_query(query, variables, use_testnet)


def get_atom_by_address(address: str, use_testnet: bool = False) -> Dict[str, Any]:
    """Search for an atom by wallet address."""
    query = """
    query GetAtomByAddress($address: String!) {
        atoms(
            where: { 
                _or: [
                    { label: { _ilike: $address } },
                    { creator: { id: { _ilike: $address } } }
                ]
            }
            limit: 5
        ) {
            term_id
            label
            type
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
    """
    variables = {"address": f"%{address}%"}
    return execute_query(query, variables, use_testnet)


def get_triples_about(subject_id: int, limit: int = 20, use_testnet: bool = False) -> Dict[str, Any]:
    """Get all claims (triples) where the given atom is the subject."""
    query = """
    query GetTriplesAbout($subjectId: numeric!, $limit: Int!) {
        triples(
            where: { subject_id: { _eq: $subjectId } }
            limit: $limit
            order_by: { vault: { total_shares: desc_nulls_last } }
        ) {
            id
            subject {
                term_id
                label
            }
            predicate {
                term_id
                label
            }
            object {
                term_id
                label
            }
            vault {
                total_shares
                position_count
            }
            counter_vault {
                total_shares
                position_count
            }
            created_at
        }
    }
    """
    variables = {"subjectId": subject_id, "limit": limit}
    return execute_query(query, variables, use_testnet)


def get_positions_on_atom(atom_id: int, limit: int = 20, use_testnet: bool = False) -> Dict[str, Any]:
    """Get all positions (stakes) on a specific atom."""
    query = """
    query GetPositions($atomId: numeric!, $limit: Int!) {
        positions(
            where: { vault: { atom_id: { _eq: $atomId } } }
            limit: $limit
            order_by: { shares: desc }
        ) {
            account {
                id
                label
            }
            shares
            created_at
        }
    }
    """
    variables = {"atomId": atom_id, "limit": limit}
    return execute_query(query, variables, use_testnet)


def calculate_trust_score(atom_id: int, use_testnet: bool = False) -> Dict[str, Any]:
    """Calculate a trust score for an atom based on its claims and stakes."""
    atom_data = get_atom_by_id(atom_id, use_testnet)
    triples_data = get_triples_about(atom_id, 50, use_testnet)
    positions_data = get_positions_on_atom(atom_id, 50, use_testnet)
    
    result = {
        "atom_id": atom_id,
        "atom": None,
        "metrics": {
            "total_stake": 0,
            "position_count": 0,
            "claims_as_subject": 0,
            "claims_as_object": 0,
            "positive_signal": 0,
            "negative_signal": 0,
            "trust_ratio": None
        },
        "top_claims": [],
        "top_attestors": []
    }
    
    if "data" in atom_data and atom_data["data"].get("atom"):
        atom = atom_data["data"]["atom"]
        result["atom"] = {
            "label": atom.get("label"),
            "type": atom.get("type"),
            "created_at": atom.get("created_at")
        }
        
        vault = atom.get("vault") or {}
        result["metrics"]["total_stake"] = vault.get("total_shares", 0)
        result["metrics"]["position_count"] = vault.get("position_count", 0)
        
        subject_agg = atom.get("as_subject_triples_aggregate", {}).get("aggregate", {})
        object_agg = atom.get("as_object_triples_aggregate", {}).get("aggregate", {})
        result["metrics"]["claims_as_subject"] = subject_agg.get("count", 0)
        result["metrics"]["claims_as_object"] = object_agg.get("count", 0)
    
    if "data" in triples_data and triples_data["data"].get("triples"):
        for triple in triples_data["data"]["triples"][:5]:
            vault = triple.get("vault") or {}
            counter_vault = triple.get("counter_vault") or {}
            
            positive = float(vault.get("total_shares") or 0)
            negative = float(counter_vault.get("total_shares") or 0)
            
            result["metrics"]["positive_signal"] += positive
            result["metrics"]["negative_signal"] += negative
            
            result["top_claims"].append({
                "predicate": triple.get("predicate", {}).get("label"),
                "object": triple.get("object", {}).get("label"),
                "positive_stake": positive,
                "negative_stake": negative
            })
    
    if "data" in positions_data and positions_data["data"].get("positions"):
        for position in positions_data["data"]["positions"][:5]:
            account = position.get("account") or {}
            result["top_attestors"].append({
                "address": account.get("id"),
                "label": account.get("label"),
                "stake": position.get("shares")
            })
    
    total_signal = result["metrics"]["positive_signal"] + result["metrics"]["negative_signal"]
    if total_signal > 0:
        result["metrics"]["trust_ratio"] = round(
            result["metrics"]["positive_signal"] / total_signal, 4
        )
    
    return result


def format_output(data: Dict[str, Any], output_format: str = "json") -> str:
    """Format the output data."""
    if output_format == "json":
        return json.dumps(data, indent=2, default=str)
    
    if "error" in data:
        return f"Error: {data['error']}"
    
    lines = []
    
    if "atom" in data and data["atom"]:
        lines.append(f"Entity: {data['atom'].get('label', 'Unknown')}")
        lines.append(f"Type: {data['atom'].get('type', 'N/A')}")
        lines.append("")
    
    if "metrics" in data:
        m = data["metrics"]
        lines.append("Metrics:")
        lines.append(f"  Total Stake: {m.get('total_stake', 0)}")
        lines.append(f"  Position Count: {m.get('position_count', 0)}")
        lines.append(f"  Claims as Subject: {m.get('claims_as_subject', 0)}")
        lines.append(f"  Claims as Object: {m.get('claims_as_object', 0)}")
        if m.get("trust_ratio") is not None:
            lines.append(f"  Trust Ratio: {m['trust_ratio']:.2%}")
        lines.append("")
    
    if "top_claims" in data and data["top_claims"]:
        lines.append("Top Claims:")
        for claim in data["top_claims"]:
            pred = claim.get("predicate", "?")
            obj = claim.get("object", "?")
            pos = claim.get("positive_stake", 0)
            neg = claim.get("negative_stake", 0)
            lines.append(f"  - {pred} -> {obj} (positive: {pos}, negative: {neg})")
        lines.append("")
    
    if "top_attestors" in data and data["top_attestors"]:
        lines.append("Top Attestors:")
        for attestor in data["top_attestors"]:
            label = attestor.get("label") or attestor.get("address", "?")[:10] + "..."
            stake = attestor.get("stake", 0)
            lines.append(f"  - {label}: {stake}")
    
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(
        description="Query Intuition Protocol knowledge graph",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
    python intuition_query.py --search "Uniswap"
    python intuition_query.py --atom-id 12345
    python intuition_query.py --address 0x1234abcd...
    python intuition_query.py --triples-about 12345
    python intuition_query.py --trust-score 12345 --format text
        """
    )
    
    parser.add_argument("--search", type=str, help="Search atoms by label")
    parser.add_argument("--atom-id", type=int, help="Get atom by ID")
    parser.add_argument("--address", type=str, help="Search by wallet address")
    parser.add_argument("--triples-about", type=int, help="Get claims about an atom ID")
    parser.add_argument("--positions", type=int, help="Get positions on an atom ID")
    parser.add_argument("--trust-score", type=int, help="Calculate trust score for atom ID")
    parser.add_argument("--limit", type=int, default=10, help="Limit results (default: 10)")
    parser.add_argument("--testnet", action="store_true", help="Use testnet instead of mainnet")
    parser.add_argument("--format", choices=["json", "text"], default="json", help="Output format")
    
    args = parser.parse_args()
    
    if not any([args.search, args.atom_id, args.address, args.triples_about, args.positions, args.trust_score]):
        parser.print_help()
        sys.exit(1)
    
    result = None
    
    if args.search:
        result = search_atoms(args.search, args.limit, args.testnet)
    elif args.atom_id:
        result = get_atom_by_id(args.atom_id, args.testnet)
    elif args.address:
        result = get_atom_by_address(args.address, args.testnet)
    elif args.triples_about:
        result = get_triples_about(args.triples_about, args.limit, args.testnet)
    elif args.positions:
        result = get_positions_on_atom(args.positions, args.limit, args.testnet)
    elif args.trust_score:
        result = calculate_trust_score(args.trust_score, args.testnet)
    
    if result:
        print(format_output(result, args.format))


if __name__ == "__main__":
    main()
