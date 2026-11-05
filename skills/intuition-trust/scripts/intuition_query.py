#!/usr/bin/env python3
"""
Intuition Protocol GraphQL Query Helper

A utility script for querying the Intuition Protocol knowledge graph.
Supports searching entities, retrieving trust data, and checking reputation.

Usage:
    python intuition_query.py --search "Uniswap"
    python intuition_query.py --term-id 0x123...
    python intuition_query.py --triples-about 0x123...
    python intuition_query.py --trust-score 0x123...
"""

import argparse
import json
import sys
from urllib.request import Request, urlopen
from urllib.error import URLError, HTTPError
from typing import Dict, Any

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


def search_terms(search_term: str, limit: int = 10, use_testnet: bool = False) -> Dict[str, Any]:
    """Search for entities by label using full-text search."""
    query = """
    query SearchTerms($searchQuery: String!, $limit: Int!) {
        search_term(args: { query: $searchQuery }, limit: $limit) {
            id
            type
            atom_id
            triple_id
            atom {
                label
                image
                type
                created_at
                creator {
                    id
                    label
                }
            }
            total_assets
            total_market_cap
            positions_aggregate {
                aggregate {
                    count
                }
            }
        }
    }
    """
    variables = {"searchQuery": search_term, "limit": limit}
    return execute_query(query, variables, use_testnet)


def get_term_by_id(term_id: str, use_testnet: bool = False) -> Dict[str, Any]:
    """Retrieve a specific term by its ID."""
    query = """
    query GetTerm($termId: String!) {
        term(id: $termId) {
            id
            type
            atom_id
            triple_id
            atom {
                label
                image
                type
                created_at
                creator {
                    id
                    label
                }
            }
            triple {
                subject {
                    label
                }
                predicate {
                    label
                }
                object {
                    label
                }
            }
            total_assets
            total_market_cap
            positions_aggregate {
                aggregate {
                    count
                }
            }
        }
    }
    """
    variables = {"termId": term_id}
    return execute_query(query, variables, use_testnet)


def get_triples_about(subject_id: str, limit: int = 20, use_testnet: bool = False) -> Dict[str, Any]:
    """Get all claims (triples) where the given atom is the subject."""
    query = """
    query GetTriplesAbout($subjectId: String!, $limit: Int!) {
        triples(
            where: { subject: { term_id: { _eq: $subjectId } } }
            limit: $limit
        ) {
            term_id
            subject {
                label
            }
            predicate {
                label
            }
            object {
                label
            }
            created_at
            term {
                total_assets
                total_market_cap
                positions_aggregate {
                    aggregate {
                        count
                    }
                }
            }
        }
    }
    """
    variables = {"subjectId": subject_id, "limit": limit}
    return execute_query(query, variables, use_testnet)


def get_positions_on_term(term_id: str, limit: int = 20, use_testnet: bool = False) -> Dict[str, Any]:
    """Get all positions (stakes) on a specific term."""
    query = """
    query GetPositions($termId: String!, $limit: Int!) {
        positions(
            where: { vault: { term_id: { _eq: $termId } } }
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
    variables = {"termId": term_id, "limit": limit}
    return execute_query(query, variables, use_testnet)


def get_account_info(account_id: str, use_testnet: bool = False) -> Dict[str, Any]:
    """Get account information and their positions."""
    query = """
    query GetAccount($accountId: String!) {
        account(id: $accountId) {
            id
            label
            image
            atom {
                label
                type
            }
            positions(limit: 10, order_by: { shares: desc }) {
                shares
                vault {
                    term {
                        atom {
                            label
                        }
                        triple {
                            subject { label }
                            predicate { label }
                            object { label }
                        }
                    }
                }
            }
            signals_aggregate {
                aggregate {
                    count
                }
            }
        }
    }
    """
    variables = {"accountId": account_id}
    return execute_query(query, variables, use_testnet)


def calculate_trust_score(term_id: str, use_testnet: bool = False) -> Dict[str, Any]:
    """Calculate a trust score for a term based on positions and signals."""
    term_data = get_term_by_id(term_id, use_testnet)
    positions_data = get_positions_on_term(term_id, 50, use_testnet)
    
    result = {
        "term_id": term_id,
        "entity": None,
        "metrics": {
            "total_assets": 0,
            "total_market_cap": 0,
            "position_count": 0,
            "top_stakers": []
        },
        "trust_assessment": "Unknown"
    }
    
    if "data" in term_data and term_data["data"].get("term"):
        term = term_data["data"]["term"]
        
        if term.get("atom"):
            result["entity"] = {
                "label": term["atom"].get("label"),
                "type": term["atom"].get("type"),
                "created_at": term["atom"].get("created_at")
            }
        elif term.get("triple"):
            t = term["triple"]
            result["entity"] = {
                "label": f"{t['subject']['label']} - {t['predicate']['label']} - {t['object']['label']}",
                "type": "Triple",
                "created_at": None
            }
        
        result["metrics"]["total_assets"] = term.get("total_assets", 0)
        result["metrics"]["total_market_cap"] = term.get("total_market_cap", 0)
        
        pos_agg = term.get("positions_aggregate", {}).get("aggregate", {})
        result["metrics"]["position_count"] = pos_agg.get("count", 0)
    
    if "data" in positions_data and positions_data["data"].get("positions"):
        for position in positions_data["data"]["positions"][:5]:
            account = position.get("account") or {}
            result["metrics"]["top_stakers"].append({
                "address": account.get("id", "")[:20] + "...",
                "label": account.get("label"),
                "stake": position.get("shares")
            })
    
    # Trust assessment based on metrics
    total_assets = int(result["metrics"]["total_assets"] or 0)
    position_count = result["metrics"]["position_count"]
    
    if total_assets > 10**18 and position_count > 10:
        result["trust_assessment"] = "High - Significant stake and multiple attestors"
    elif total_assets > 10**17 or position_count > 5:
        result["trust_assessment"] = "Medium - Moderate community validation"
    elif total_assets > 0:
        result["trust_assessment"] = "Low - Limited stake"
    else:
        result["trust_assessment"] = "Unverified - No stakes found"
    
    return result


def format_output(data: Dict[str, Any], output_format: str = "json") -> str:
    """Format the output data."""
    if output_format == "json":
        return json.dumps(data, indent=2, default=str)
    
    if "error" in data:
        return f"Error: {data['error']}"
    
    lines = []
    
    if "entity" in data and data["entity"]:
        lines.append(f"Entity: {data['entity'].get('label', 'Unknown')}")
        lines.append(f"Type: {data['entity'].get('type', 'N/A')}")
        lines.append("")
    
    if "metrics" in data:
        m = data["metrics"]
        lines.append("Metrics:")
        
        # Format large numbers
        total_assets = int(m.get("total_assets") or 0)
        if total_assets > 0:
            eth_value = total_assets / 10**18
            lines.append(f"  Total Assets: {eth_value:.6f} ETH ({total_assets} wei)")
        
        lines.append(f"  Position Count: {m.get('position_count', 0)}")
        lines.append("")
    
    if "trust_assessment" in data:
        lines.append(f"Trust Assessment: {data['trust_assessment']}")
        lines.append("")
    
    if "metrics" in data and data["metrics"].get("top_stakers"):
        lines.append("Top Stakers:")
        for staker in data["metrics"]["top_stakers"]:
            label = staker.get("label") or staker.get("address", "?")
            stake = int(staker.get("stake") or 0)
            eth_stake = stake / 10**18
            lines.append(f"  - {label}: {eth_stake:.6f} ETH")
    
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(
        description="Query Intuition Protocol knowledge graph",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
    python intuition_query.py --search "Uniswap"
    python intuition_query.py --search "Ethereum" --limit 5
    python intuition_query.py --term-id 0x123...
    python intuition_query.py --account 0x123...
    python intuition_query.py --trust-score 0x123... --format text
        """
    )
    
    parser.add_argument("--search", type=str, help="Search entities by label")
    parser.add_argument("--term-id", type=str, help="Get term by ID")
    parser.add_argument("--triples-about", type=str, help="Get claims about an entity")
    parser.add_argument("--positions", type=str, help="Get positions on a term")
    parser.add_argument("--account", type=str, help="Get account info by address")
    parser.add_argument("--trust-score", type=str, help="Calculate trust score for term")
    parser.add_argument("--limit", type=int, default=10, help="Limit results (default: 10)")
    parser.add_argument("--testnet", action="store_true", help="Use testnet instead of mainnet")
    parser.add_argument("--format", choices=["json", "text"], default="json", help="Output format")
    
    args = parser.parse_args()
    
    if not any([args.search, args.term_id, args.triples_about, args.positions, args.account, args.trust_score]):
        parser.print_help()
        sys.exit(1)
    
    result = None
    
    if args.search:
        result = search_terms(args.search, args.limit, args.testnet)
    elif args.term_id:
        result = get_term_by_id(args.term_id, args.testnet)
    elif args.triples_about:
        result = get_triples_about(args.triples_about, args.limit, args.testnet)
    elif args.positions:
        result = get_positions_on_term(args.positions, args.limit, args.testnet)
    elif args.account:
        result = get_account_info(args.account, args.testnet)
    elif args.trust_score:
        result = calculate_trust_score(args.trust_score, args.testnet)
    
    if result:
        print(format_output(result, args.format))


if __name__ == "__main__":
    main()
