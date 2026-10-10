"""
Reflection Processor - Convert CSV logs into queryable memory
NO subprocesses. Converts past decisions into model context.
"""
import csv
import json
import time
from pathlib import Path
from collections import defaultdict
from typing import Dict, List

class ReflectionProcessor:
    def __init__(self, log_dir="data/logs"):
        self.log_dir = Path(log_dir)

    def process_recent_logs(self, last_n_hours: int = 24) -> Dict[str, List[Dict]]:
        """Convert recent CSV logs into memory chunks"""
        cutoff_epoch = int((time.time() - (last_n_hours * 3600)) * 1000)
        memories = defaultdict(list)

        if not self.log_dir.exists():
            return dict(memories)

        for csv_file in self.log_dir.glob("routing_*.csv"):
            try:
                with open(csv_file, 'r', encoding='utf-8') as f:
                    reader = csv.DictReader(f)
                    for row in reader:
                        epoch = int(row.get('epoch_ms', 0))
                        if epoch > cutoff_epoch:
                            route = row.get('route', 'unknown')
                            memories[route].append({
                                "action": row.get('action', ''),
                                "content": row.get('content_preview', row.get('content', ''))[:500],
                                "timestamp": row.get('epoch_ms', ''),
                                "status": row.get('status', '')
                            })
            except Exception as e:
                print(f"Warning: Could not process {csv_file}: {e}")

        return dict(memories)

    def summarize_session(self, session_logs: List[Dict]) -> Dict:
        """Create a summary of a session's activities"""
        if not session_logs:
            return {"summary": "No activity", "decisions": 0}
        
        decisions = len(session_logs)
        routes_used = set()
        actions = []
        
        for log in session_logs:
            routes_used.add(log.get('route', 'unknown'))
            if log.get('action'):
                actions.append(log['action'])
        
        return {
            "summary": f"Made {decisions} decisions across routes {', '.join(routes_used)}",
            "decisions": decisions,
            "routes_used": list(routes_used),
            "recent_actions": actions[-5:] if actions else []
        }

    def extract_learned_patterns(self, memories: Dict) -> Dict:
        """Extract patterns from past decisions"""
        patterns = {
            "successful_routes": [],
            "failed_routes": [],
            "common_actions": defaultdict(int)
        }
        
        for route, logs in memories.items():
            successes = [l for l in logs if l.get('status') in ['success', 'ok', 'passed']]
            failures = [l for l in logs if l.get('status') in ['fail', 'error', 'failed']]
            
            if len(successes) > len(failures):
                patterns["successful_routes"].append(route)
            elif len(failures) > len(successes):
                patterns["failed_routes"].append(route)
            
            for log in logs:
                action = log.get('action', '')
                if action:
                    patterns["common_actions"][action] += 1
        
        # Convert defaultdict to regular dict for JSON serialization
        patterns["common_actions"] = dict(patterns["common_actions"])
        
        return patterns

    def export_to_json(self, output_file="reflection_memory.json", hours: int = 24) -> str:
        """Export memories to JSON for Route 3 (JSON Read)"""
        memories = self.process_recent_logs(hours)
        
        export_data = {
            "generated_at": time.strftime("%Y-%m-%dT%H:%M:%S"),
            "hours_covered": hours,
            "memories_by_route": memories,
            "session_summary": self.summarize_session(
                [log for logs in memories.values() for log in logs]
            ),
            "learned_patterns": self.extract_learned_patterns(memories)
        }
        
        output_path = Path(output_file)
        output_path.parent.mkdir(parents=True, exist_ok=True)
        
        with open(output_path, 'w') as f:
            json.dump(export_data, f, indent=2)
        
        return str(output_path)

    def get_context_for_prompt(self, max_tokens: int = 500) -> str:
        """Generate context string for model prompt injection"""
        memories = self.process_recent_logs(last_n_hours=4)
        patterns = self.extract_learned_patterns(memories)
        
        context_parts = []
        
        if patterns["successful_routes"]:
            context_parts.append(f"Previously successful routes: {', '.join(patterns['successful_routes'])}")
        
        if patterns["failed_routes"]:
            context_parts.append(f"Previously failed routes: {', '.join(patterns['failed_routes'])}")
        
        # Add recent actions
        recent = []
        for route, logs in memories.items():
            for log in logs[-2:]:  # Last 2 from each route
                if log.get('action'):
                    recent.append(f"[{route}] {log['action']}")
        
        if recent:
            context_parts.append("Recent actions: " + "; ".join(recent[-5:]))
        
        context = "\n".join(context_parts)
        return context[:max_tokens]


if __name__ == "__main__":
    import sys
    
    processor = ReflectionProcessor()
    
    if len(sys.argv) > 1 and sys.argv[1] == "--export":
        output = processor.export_to_json()
        print(f"Exported to: {output}")
    else:
        context = processor.get_context_for_prompt()
        print("Context for next prompt:")
        print(context if context else "(No recent activity)")
