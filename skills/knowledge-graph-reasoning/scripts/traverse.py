#!/usr/bin/env python3
"""
Knowledge graph traversal and query engine.
Supports path finding, neighbor search, hub detection, and health metrics.

Part of knowledge-graph-reasoning skill by Swarm Labs USA
https://github.com/michaelwinczuk/knowledge-graph-reasoning
"""

import json
import sys
from collections import defaultdict, deque
from typing import Any


def load_graph(path: str) -> dict:
    with open(path, "r", encoding="utf-8") as f:
        return json.load(f)


def build_adjacency(graph: dict) -> dict[str, list[tuple[str, dict]]]:
    """Build adjacency list from graph edges."""
    adj = defaultdict(list)
    for edge in graph.get("kg:edges", []):
        src = edge.get("kg:source", "")
        tgt = edge.get("kg:target", "")
        adj[src].append((tgt, edge))
        # Add reverse for bidirectional or undirected traversal
        if edge.get("kg:bidirectional", False) or edge.get("kg:type") in ("contradicts", "similar_to"):
            adj[tgt].append((src, edge))
    return dict(adj)


def find_node_by_query(graph: dict, query: str) -> list[dict]:
    """Find nodes matching a query string (label or id)."""
    query_lower = query.lower()
    results = []
    for node in graph.get("kg:nodes", []):
        label = node.get("kg:label", "").lower()
        node_id = node.get("@id", "").lower()
        aliases = [a.lower() for a in node.get("kg:aliases", [])]

        if query_lower in label or query_lower in node_id or any(query_lower in a for a in aliases):
            results.append(node)
    return results


def get_neighbors(graph: dict, entity_id: str, max_hops: int = 1) -> dict:
    """Get all nodes within max_hops of the target entity."""
    adj = build_adjacency(graph)
    node_map = {n["@id"]: n for n in graph.get("kg:nodes", [])}

    visited = set()
    queue = deque([(entity_id, 0)])
    neighbors = {"nodes": [], "edges": [], "hops": {}}

    while queue:
        current, depth = queue.popleft()
        if current in visited or depth > max_hops:
            continue
        visited.add(current)

        if current != entity_id and current in node_map:
            neighbors["nodes"].append(node_map[current])
            neighbors["hops"][current] = depth

        for neighbor, edge in adj.get(current, []):
            if neighbor not in visited:
                neighbors["edges"].append(edge)
                queue.append((neighbor, depth + 1))

    return neighbors


def find_path(graph: dict, source_id: str, target_id: str) -> dict:
    """Find shortest path between two entities using BFS."""
    adj = build_adjacency(graph)
    # Also build reverse adjacency for undirected search
    rev_adj = defaultdict(list)
    for edge in graph.get("kg:edges", []):
        src = edge.get("kg:source", "")
        tgt = edge.get("kg:target", "")
        rev_adj[tgt].append((src, edge))

    # Merge forward and reverse
    full_adj = defaultdict(list)
    for k, v in adj.items():
        full_adj[k].extend(v)
    for k, v in rev_adj.items():
        full_adj[k].extend(v)

    visited = set()
    queue = deque([(source_id, [(source_id, None)])])

    while queue:
        current, path = queue.popleft()
        if current == target_id:
            # Calculate path confidence
            confidence = 1.0
            edges_in_path = []
            for _, edge in path:
                if edge:
                    confidence *= edge.get("kg:weight", edge.get("kg:confidence", 1.0))
                    edges_in_path.append(edge)

            return {
                "found": True,
                "path": [p[0] for p in path],
                "edges": edges_in_path,
                "hops": len(path) - 1,
                "confidence": round(confidence, 4)
            }

        if current in visited:
            continue
        visited.add(current)

        for neighbor, edge in full_adj.get(current, []):
            if neighbor not in visited:
                queue.append((neighbor, path + [(neighbor, edge)]))

    return {"found": False, "path": [], "edges": [], "hops": -1, "confidence": 0.0}


def detect_hubs(graph: dict, top_n: int = 5) -> list[dict]:
    """Find the most connected nodes (hubs)."""
    edge_count = defaultdict(int)
    for edge in graph.get("kg:edges", []):
        edge_count[edge.get("kg:source", "")] += 1
        edge_count[edge.get("kg:target", "")] += 1

    node_map = {n["@id"]: n for n in graph.get("kg:nodes", [])}
    sorted_nodes = sorted(edge_count.items(), key=lambda x: x[1], reverse=True)[:top_n]

    return [
        {"node": node_map.get(node_id, {"@id": node_id}), "edge_count": count}
        for node_id, count in sorted_nodes
    ]


def detect_orphans(graph: dict) -> list[dict]:
    """Find nodes with no edges."""
    connected = set()
    for edge in graph.get("kg:edges", []):
        connected.add(edge.get("kg:source", ""))
        connected.add(edge.get("kg:target", ""))

    return [n for n in graph.get("kg:nodes", []) if n.get("@id") not in connected]


def detect_clusters(graph: dict) -> list[list[str]]:
    """Find connected components using union-find."""
    adj = build_adjacency(graph)
    # Add reverse edges
    for edge in graph.get("kg:edges", []):
        src = edge.get("kg:source", "")
        tgt = edge.get("kg:target", "")
        if tgt not in adj:
            adj[tgt] = []
        adj[tgt].append((src, edge))

    all_nodes = {n["@id"] for n in graph.get("kg:nodes", [])}
    visited = set()
    clusters = []

    for node in all_nodes:
        if node in visited:
            continue
        cluster = []
        queue = deque([node])
        while queue:
            current = queue.popleft()
            if current in visited:
                continue
            visited.add(current)
            cluster.append(current)
            for neighbor, _ in adj.get(current, []):
                if neighbor not in visited:
                    queue.append(neighbor)
        clusters.append(cluster)

    return sorted(clusters, key=len, reverse=True)


def graph_health(graph: dict) -> dict:
    """Calculate graph health metrics."""
    nodes = graph.get("kg:nodes", [])
    edges = graph.get("kg:edges", [])
    n = len(nodes)
    e = len(edges)

    orphans = detect_orphans(graph)
    clusters = detect_clusters(graph)
    hubs = detect_hubs(graph, top_n=3)

    density = e / (n * (n - 1)) if n > 1 else 0
    avg_conn = (2 * e) / n if n > 0 else 0

    contradictions = sum(1 for edge in edges if edge.get("kg:type") == "contradicts")
    inferred = sum(1 for edge in edges if edge.get("kg:inferred", False))

    return {
        "node_count": n,
        "edge_count": e,
        "density": round(density, 4),
        "orphan_count": len(orphans),
        "orphan_nodes": [o.get("kg:label", o.get("@id")) for o in orphans],
        "avg_connectivity": round(avg_conn, 2),
        "cluster_count": len(clusters),
        "clusters": [{"size": len(c), "sample": c[:3]} for c in clusters],
        "hub_nodes": [{"label": h["node"].get("kg:label", h["node"].get("@id")), "edges": h["edge_count"]} for h in hubs],
        "contradiction_count": contradictions,
        "inferred_edge_count": inferred,
        "health": "GOOD" if len(orphans) == 0 and contradictions == 0 else "NEEDS_ATTENTION"
    }


def main():
    if len(sys.argv) < 3:
        print("Usage: python traverse.py <graph.json> <command> [args...]")
        print("Commands:")
        print("  search <query>           - Find nodes matching query")
        print("  neighbors <entity_id> [hops] - Get neighbors within N hops")
        print("  path <source> <target>   - Find shortest path")
        print("  hubs [top_n]             - Find most connected nodes")
        print("  health                   - Graph health report")
        sys.exit(1)

    graph = load_graph(sys.argv[1])
    command = sys.argv[2]

    if command == "search":
        results = find_node_by_query(graph, sys.argv[3])
        print(json.dumps(results, indent=2))
    elif command == "neighbors":
        hops = int(sys.argv[4]) if len(sys.argv) > 4 else 1
        result = get_neighbors(graph, sys.argv[3], hops)
        print(json.dumps(result, indent=2))
    elif command == "path":
        result = find_path(graph, sys.argv[3], sys.argv[4])
        print(json.dumps(result, indent=2))
    elif command == "hubs":
        top_n = int(sys.argv[3]) if len(sys.argv) > 3 else 5
        result = detect_hubs(graph, top_n)
        print(json.dumps(result, indent=2))
    elif command == "health":
        result = graph_health(graph)
        print(json.dumps(result, indent=2))
    else:
        print(f"Unknown command: {command}")
        sys.exit(1)


if __name__ == "__main__":
    main()
