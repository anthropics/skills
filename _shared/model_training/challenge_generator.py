"""
Challenge Generator - Adaptive difficulty for model training
NO subprocesses. Generates prompts based on model skill level.
"""
import json
import random
from pathlib import Path
from typing import Dict, List, Optional

class ChallengeGenerator:
    def __init__(self, evidence_dir="data/evidence", session_state_path="session_state.json"):
        self.evidence_dir = Path(evidence_dir)
        self.session_state_path = Path(session_state_path)
        
        self.difficulty_levels = {
            "beginner": self.gen_single_uid_analysis,
            "intermediate": self.gen_multi_uid_correlation,
            "advanced": self.gen_cross_claim_synthesis,
            "expert": self.gen_counter_argument_generation
        }

    def get_all_uids(self) -> List[str]:
        """Get all UIDs from evidence directory"""
        uids = []
        if self.evidence_dir.exists():
            for f in self.evidence_dir.glob("UID-*.json"):
                # Extract UID from filename like UID-1224.json
                uid = f.stem.replace("UID-", "")
                uids.append(uid)
        
        # Fallback if no files found
        if not uids:
            uids = ["1224", "334", "456", "789", "1001"]
        
        return uids

    def gen_single_uid_analysis(self) -> Dict:
        """Beginner: Analyze one evidence card"""
        uid = random.choice(self.get_all_uids())
        return {
            "prompt": f"Analyze UID {uid}. Identify the claim, quote the key evidence, and explain its significance to the case.",
            "expected_fields": ["claim", "depiction_quote", "significance"],
            "difficulty": "beginner",
            "validation_criteria": {
                "must_contain": ["claim", "evidence", "significance"],
                "min_length": 100
            }
        }

    def gen_multi_uid_correlation(self) -> Dict:
        """Intermediate: Find relationships between 2-3 UIDs"""
        uids = random.sample(self.get_all_uids(), min(3, len(self.get_all_uids())))
        return {
            "prompt": f"Find the relationship between UIDs {', '.join(uids)}. What common claim, party, or timeline connects them?",
            "expected_fields": ["complements_uid", "parties_involved", "claim", "timeline"],
            "difficulty": "intermediate",
            "validation_criteria": {
                "must_contain": ["relationship", "connect"],
                "min_length": 200
            }
        }

    def gen_cross_claim_synthesis(self) -> Dict:
        """Advanced: Synthesis across multiple claims"""
        claims = [
            "conspiracy claim",
            "malicious prosecution",
            "Sixth Amendment violation",
            "due process violation"
        ]
        claim = random.choice(claims)
        return {
            "prompt": f"Identify all evidence supporting a {claim}. Show how UIDs link together to demonstrate the violation pattern.",
            "expected_fields": ["conspiracy_pattern", "timeline", "actors", "evidence_chain"],
            "difficulty": "advanced",
            "validation_criteria": {
                "must_contain": ["UID", "pattern", "evidence"],
                "min_length": 400
            }
        }

    def gen_counter_argument_generation(self) -> Dict:
        """Expert: Generate counter-arguments and rebuttals"""
        return {
            "prompt": "Anticipate the defendant's strongest argument against your malicious prosecution claim. Generate a rebuttal with supporting evidence UIDs.",
            "expected_fields": ["defendant_argument", "rebuttal", "supporting_uids", "caselaw"],
            "difficulty": "expert",
            "validation_criteria": {
                "must_contain": ["defendant", "rebuttal", "UID", "case"],
                "min_length": 500
            }
        }

    def get_model_skill_level(self) -> str:
        """Determine skill level from session state"""
        if not self.session_state_path.exists():
            return "beginner"
        
        try:
            with open(self.session_state_path, 'r') as f:
                state = json.load(f)
            
            scores = state.get("validation_scores", {})
            avg_score = sum(scores.values()) / len(scores) if scores else 0.5
            
            if avg_score < 0.6:
                return "beginner"
            elif avg_score < 0.75:
                return "intermediate"
            elif avg_score < 0.9:
                return "advanced"
            else:
                return "expert"
        except:
            return "beginner"

    def get_next_challenge(self, override_difficulty: Optional[str] = None) -> Dict:
        """Get next challenge based on model's current skill level"""
        if override_difficulty and override_difficulty in self.difficulty_levels:
            difficulty = override_difficulty
        else:
            difficulty = self.get_model_skill_level()
        
        challenge = self.difficulty_levels[difficulty]()
        challenge["generated_at"] = str(Path(__file__).stat().st_mtime)
        
        return challenge

    def get_all_challenges(self) -> List[Dict]:
        """Get one challenge from each difficulty level"""
        return [gen() for gen in self.difficulty_levels.values()]


if __name__ == "__main__":
    import sys
    
    gen = ChallengeGenerator()
    
    if len(sys.argv) > 1:
        # Override difficulty from command line
        challenge = gen.get_next_challenge(sys.argv[1])
    else:
        challenge = gen.get_next_challenge()
    
    print(json.dumps(challenge, indent=2))
