"""
Setup Checker - Validates everything is in place before running
ANY MODEL CAN RUN THIS. IF IT PASSES, THE SYSTEM WORKS.
"""
import json
import sys
from pathlib import Path

class SetupChecker:
    def __init__(self, base_dir=None):
        self.base_dir = Path(base_dir) if base_dir else Path(__file__).parent
        self.errors = []
        self.warnings = []
        self.fixes_applied = []

    def check_all(self) -> bool:
        """Run all checks. Returns True if ready to run."""
        print("=" * 50)
        print("  MODEL TRAINING SYSTEM - SETUP CHECK")
        print("=" * 50)
        print()

        self.check_directories()
        self.check_required_files()
        self.check_evidence_cards()
        self.check_session_state()
        self.check_python_imports()

        print()
        print("=" * 50)
        
        if self.errors:
            print("[FAIL] SETUP INCOMPLETE - Fix these issues:")
            for err in self.errors:
                print(f"   - {err}")
            print()
            print("Run with --fix to auto-repair what's possible")
            return False
        
        if self.warnings:
            print("[WARN] WARNINGS (system will still work):")
            for warn in self.warnings:
                print(f"   - {warn}")
        
        print()
        print("[OK] SETUP COMPLETE - Ready to run!")
        print()
        print("Quick start:")
        print("  python challenge_generator.py      # Get a challenge")
        print("  python validate_evidence_card.py data/evidence/UID-0001.json")
        print("  python eval_logger.py              # Test logging")
        return True

    def check_directories(self):
        """Check required directories exist"""
        print("[1/5] Checking directories...")
        
        required_dirs = [
            "data",
            "data/evidence",
            "data/logs", 
            "data/json",
            "data/output"
        ]
        
        for dir_name in required_dirs:
            dir_path = self.base_dir / dir_name
            if not dir_path.exists():
                self.errors.append(f"Missing directory: {dir_name}")
            else:
                print(f"      [OK] {dir_name}/")

    def check_required_files(self):
        """Check required Python files exist"""
        print("[2/5] Checking required files...")
        
        required_files = [
            "session_state.json",
            "eval_logger.py",
            "validate_evidence_card.py",
            "challenge_generator.py",
            "evidence_graph.py",
            "reflection_processor.py"
        ]
        
        for file_name in required_files:
            file_path = self.base_dir / file_name
            if not file_path.exists():
                self.errors.append(f"Missing file: {file_name}")
            else:
                print(f"      [OK] {file_name}")

    def check_evidence_cards(self):
        """Check evidence cards exist and are valid"""
        print("[3/5] Checking evidence cards...")
        
        evidence_dir = self.base_dir / "data" / "evidence"
        if not evidence_dir.exists():
            return
        
        cards = list(evidence_dir.glob("UID-*.json"))
        
        # Filter out template
        real_cards = [c for c in cards if "TEMPLATE" not in c.name]
        
        if not real_cards:
            self.warnings.append("No evidence cards found (only template). Add UID-*.json files to data/evidence/")
        else:
            print(f"      [OK] Found {len(real_cards)} evidence card(s)")
            
            # Validate each card
            from validate_evidence_card import validate_card
            for card_path in real_cards[:5]:  # Check first 5
                passed, errors = validate_card(card_path)
                if not passed:
                    self.warnings.append(f"{card_path.name}: {errors[0]}")
                else:
                    print(f"      [OK] {card_path.name} valid")

    def check_session_state(self):
        """Check session state is valid JSON"""
        print("[4/5] Checking session state...")
        
        state_path = self.base_dir / "session_state.json"
        if not state_path.exists():
            return
        
        try:
            with open(state_path, 'r') as f:
                state = json.load(f)
            
            required_keys = ["model_id", "session_count", "validation_scores"]
            for key in required_keys:
                if key not in state:
                    self.errors.append(f"session_state.json missing key: {key}")
            
            if not self.errors:
                print(f"      [OK] session_state.json valid")
                print(f"      [OK] Session count: {state.get('session_count', 0)}")
        except json.JSONDecodeError as e:
            self.errors.append(f"session_state.json is invalid JSON: {e}")

    def check_python_imports(self):
        """Check all required Python modules are available"""
        print("[5/5] Checking Python imports...")
        
        required_modules = ["json", "csv", "sqlite3", "pathlib", "collections"]
        
        for module in required_modules:
            try:
                __import__(module)
                print(f"      [OK] {module}")
            except ImportError:
                self.errors.append(f"Missing Python module: {module}")

    def auto_fix(self):
        """Auto-fix what's possible"""
        print("Attempting auto-fix...")
        
        # Create missing directories
        required_dirs = ["data", "data/evidence", "data/logs", "data/json", "data/output"]
        for dir_name in required_dirs:
            dir_path = self.base_dir / dir_name
            if not dir_path.exists():
                dir_path.mkdir(parents=True, exist_ok=True)
                self.fixes_applied.append(f"Created {dir_name}/")
        
        # Create session_state.json if missing
        state_path = self.base_dir / "session_state.json"
        if not state_path.exists():
            default_state = {
                "model_id": "worker_001",
                "session_count": 0,
                "phase": "initialization",
                "current_task": None,
                "decisions_made": {},
                "learned_patterns": {"successful_approaches": [], "failed_approaches": []},
                "validation_scores": {"consistency": 0.5, "citation_accuracy": 0.5, "legal_reasoning": 0.5},
                "next_action": "Run setup_check.py to verify installation"
            }
            with open(state_path, 'w') as f:
                json.dump(default_state, f, indent=2)
            self.fixes_applied.append("Created session_state.json")
        
        if self.fixes_applied:
            print("Fixes applied:")
            for fix in self.fixes_applied:
                print(f"  [OK] {fix}")
        else:
            print("No auto-fixes needed.")


if __name__ == "__main__":
    checker = SetupChecker()
    
    if "--fix" in sys.argv:
        checker.auto_fix()
        print()
    
    success = checker.check_all()
    sys.exit(0 if success else 1)
