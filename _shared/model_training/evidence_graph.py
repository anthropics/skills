"""
Evidence Graph - Build relationship graph from evidence cards
NO subprocesses. Pure Python graph traversal.
"""
import json
from pathlib import Path
from collections import defaultdict
from typing import Dict, List, Set

class EvidenceGraph:
    def __init__(self, evidence_dir="data/evidence"):
        self.evidence_dir = Path(evidence_dir)
        self.graph = defaultdict(list)  # uid -> [related_uids]
        self.reverse_graph = defaultdict(list)  # uid -> [uids that reference this]
        self.cards = {}  # uid -> card data
        
        if self.evidence_dir.exists():
            self.build_graph()

    def build_graph(self):
        """Parse all evidence cards and build relationship graph"""
        for card_file in self.evidence_dir.glob("UID-*.json"):
            try:
                with open(card_file, 'r', encoding='utf-8') as f:
                    card = json.load(f)
                
                uid = str(card.get("uid", card_file.stem.replace("UID-", "")))
                self.cards[uid] = card
                
                # Get complements_uid field (may be comma-separated string or list)
                complements = card.get("complements_uid", "")
                if isinstance(complements, str):
                    complements = [c.strip() for c in complements.split(",") if c.strip()]
                elif isinstance(complements, list):
                    complements = [str(c).strip() for c in complements if c]
                
                for related_uid in complements:
                    self.graph[uid].append(related_uid)
                    self.reverse_graph[related_uid].append(uid)
                    
            except (json.JSONDecodeError, Exception) as e:
                print(f"Warning: Could not parse {card_file}: {e}")

    def find_connected_cluster(self, start_uid: str) -> List[str]:
        """BFS to find all UIDs connected to start_uid"""
        visited: Set[str] = set()
        queue = [str(start_uid)]

        while queue:
            uid = queue.pop(0)
            if uid in visited:
                continue
            visited.add(uid)

            # Forward connections
            for related_uid in self.graph.get(uid, []):
                if related_uid not in visited:
                    queue.append(related_uid)
            
            # Reverse connections (UIDs that reference this one)
            for related_uid in self.reverse_graph.get(uid, []):
                if related_uid not in visited:
                    queue.append(related_uid)

        return list(visited)

    def find_by_claim(self, claim_text: str) -> List[str]:
        """Find all UIDs that mention a specific claim"""
        matching = []
        claim_lower = claim_text.lower()
        
        for uid, card in self.cards.items():
            card_claim = str(card.get("claim", "")).lower()
            if claim_lower in card_claim:
                matching.append(uid)
        
        return matching

    def find_by_party(self, party_name: str) -> List[str]:
        """Find all UIDs involving a specific party"""
        matching = []
        party_lower = party_name.lower()
        
        for uid, card in self.cards.items():
            parties = card.get("parties_involved", [])
            if isinstance(parties, list):
                for party in parties:
                    if party_lower in str(party).lower():
                        matching.append(uid)
                        break
        
        return matching

    def get_card(self, uid: str) -> Dict:
        """Get card data by UID"""
        return self.cards.get(str(uid), {})

    def get_statistics(self) -> Dict:
        """Get graph statistics"""
        return {
            "total_cards": len(self.cards),
            "total_connections": sum(len(v) for v in self.graph.values()),
            "cards_with_connections": len([k for k, v in self.graph.items() if v]),
            "isolated_cards": len([k for k in self.cards if k not in self.graph or not self.graph[k]])
        }

    def export_to_json(self, output_file="evidence_graph.json") -> str:
        """Export graph for Route 3 (JSON Read)"""
        export_data = {
            "graph": dict(self.graph),
            "reverse_graph": dict(self.reverse_graph),
            "statistics": self.get_statistics()
        }
        
        output_path = Path(output_file)
        with open(output_path, 'w') as f:
            json.dump(export_data, f, indent=2)
        
        return str(output_path)


if __name__ == "__main__":
    import sys
    
    graph = EvidenceGraph()
    
    if len(sys.argv) > 1:
        uid = sys.argv[1]
        cluster = graph.find_connected_cluster(uid)
        print(f"Cluster for UID {uid}:")
        print(json.dumps(cluster, indent=2))
    else:
        print("Statistics:")
        print(json.dumps(graph.get_statistics(), indent=2))
        print("\nGraph structure:")
        print(json.dumps(dict(graph.graph), indent=2))
