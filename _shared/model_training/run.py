"""
MAIN RUNNER - One command does everything
ANY MODEL RUNS THIS. IT CANNOT FAIL.

Usage:
    python run.py                    # Interactive mode
    python run.py --challenge        # Get next challenge
    python run.py --validate FILE    # Validate evidence card
    python run.py --log              # View recent activity
    python run.py --status           # Show session status
    python run.py --help             # Show this help
"""
import json
import sys
from pathlib import Path

# Get base directory
BASE_DIR = Path(__file__).parent
DATA_DIR = BASE_DIR / "data"


def ensure_setup():
    """Make sure everything exists. Auto-fix if not."""
    required_dirs = ["data", "data/evidence", "data/logs", "data/json", "data/output"]
    
    for dir_name in required_dirs:
        dir_path = BASE_DIR / dir_name
        if not dir_path.exists():
            dir_path.mkdir(parents=True, exist_ok=True)
            print(f"Created {dir_name}/")
    
    # Ensure session_state.json exists
    state_path = BASE_DIR / "session_state.json"
    if not state_path.exists():
        default_state = {
            "model_id": "worker_001",
            "session_count": 0,
            "phase": "ready",
            "current_task": None,
            "decisions_made": {},
            "learned_patterns": {"successful_approaches": [], "failed_approaches": []},
            "validation_scores": {"consistency": 0.5, "citation_accuracy": 0.5, "legal_reasoning": 0.5},
            "next_action": "Get a challenge with: python run.py --challenge"
        }
        with open(state_path, 'w') as f:
            json.dump(default_state, f, indent=2)
        print("Created session_state.json")


def get_challenge():
    """Get next challenge based on skill level"""
    from challenge_generator import ChallengeGenerator
    
    gen = ChallengeGenerator(
        evidence_dir=str(DATA_DIR / "evidence"),
        session_state_path=str(BASE_DIR / "session_state.json")
    )
    
    challenge = gen.get_next_challenge()
    
    print("=" * 50)
    print(f"  CHALLENGE [{challenge['difficulty'].upper()}]")
    print("=" * 50)
    print()
    print(challenge['prompt'])
    print()
    print(f"Expected output: {', '.join(challenge['expected_fields'])}")
    print()
    
    return challenge


def validate_card(file_path):
    """Validate an evidence card"""
    from validate_evidence_card import validate_card as do_validate
    
    passed, errors = do_validate(file_path)
    
    if passed:
        print("✅ VALID - Card passes all checks")
        return True
    else:
        print("❌ INVALID - Issues found:")
        for err in errors:
            print(f"   • {err}")
        return False


def show_status():
    """Show current session status"""
    state_path = BASE_DIR / "session_state.json"
    
    if not state_path.exists():
        print("No session state found. Run any command to initialize.")
        return
    
    with open(state_path, 'r') as f:
        state = json.load(f)
    
    print("=" * 50)
    print("  SESSION STATUS")
    print("=" * 50)
    print()
    print(f"Model ID:        {state.get('model_id', 'unknown')}")
    print(f"Session Count:   {state.get('session_count', 0)}")
    print(f"Phase:           {state.get('phase', 'unknown')}")
    print(f"Current Task:    {state.get('current_task', 'None')}")
    print()
    print("Validation Scores:")
    scores = state.get('validation_scores', {})
    for key, val in scores.items():
        filled = int(val * 10)
        bar = "#" * filled + "-" * (10 - filled)
        print(f"  {key:20} [{bar}] {int(val * 100)}%")
    print()
    print(f"Next Action: {state.get('next_action', 'None')}")


def view_log():
    """View recent activity"""
    from eval_logger import EvalLogger
    
    db_path = DATA_DIR / "eval_log.db"
    
    if not db_path.exists():
        print("No activity logged yet.")
        return
    
    logger = EvalLogger(str(db_path))
    recent = logger.get_recent_exchanges(limit=10)
    logger.close()
    
    print("=" * 50)
    print("  RECENT ACTIVITY")
    print("=" * 50)
    
    if not recent:
        print("No activity logged yet.")
        return
    
    for entry in recent:
        print()
        print(f"[{entry['model_id']}] Route {entry['route']}")
        print(f"  Prompt: {entry['prompt'][:60]}...")
        print(f"  Response: {entry['response'][:60]}...")


def show_help():
    """Show help"""
    print(__doc__)
    print()
    print("Files in this system:")
    print("  session_state.json      - Model memory (persistent)")
    print("  challenge_generator.py  - Creates training challenges")
    print("  validate_evidence_card.py - Validates evidence cards")
    print("  eval_logger.py          - Logs all activity")
    print("  evidence_graph.py       - Maps UID relationships")
    print("  reflection_processor.py - Converts logs to memory")
    print()
    print("Data directories:")
    print("  data/evidence/  - Put UID-*.json evidence cards here")
    print("  data/logs/      - CSV routing logs")
    print("  data/json/      - Generated JSON outputs")
    print("  data/output/    - Final outputs")


def interactive():
    """Interactive menu"""
    print()
    print("=" * 50)
    print("  MODEL TRAINING SYSTEM")
    print("=" * 50)
    print()
    print("Commands:")
    print("  1. Get next challenge")
    print("  2. Show session status")
    print("  3. View recent activity")
    print("  4. Validate evidence card")
    print("  5. Run full setup check")
    print("  6. Exit")
    print()
    
    try:
        choice = input("Enter choice (1-6): ").strip()
    except EOFError:
        # Non-interactive mode
        show_help()
        return
    
    if choice == "1":
        get_challenge()
    elif choice == "2":
        show_status()
    elif choice == "3":
        view_log()
    elif choice == "4":
        card_path = input("Enter card path: ").strip()
        if card_path:
            validate_card(card_path)
    elif choice == "5":
        import setup_check
        checker = setup_check.SetupChecker()
        checker.check_all()
    elif choice == "6":
        print("Goodbye.")
    else:
        print("Invalid choice.")


def main():
    # Always ensure setup first
    ensure_setup()
    
    if len(sys.argv) < 2:
        interactive()
        return
    
    arg = sys.argv[1]
    
    if arg == "--challenge":
        get_challenge()
    elif arg == "--validate":
        if len(sys.argv) < 3:
            print("Usage: python run.py --validate FILE")
            sys.exit(1)
        validate_card(sys.argv[2])
    elif arg == "--status":
        show_status()
    elif arg == "--log":
        view_log()
    elif arg == "--help" or arg == "-h":
        show_help()
    else:
        print(f"Unknown argument: {arg}")
        show_help()
        sys.exit(1)


if __name__ == "__main__":
    main()
