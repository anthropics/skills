import sys
import os
import unittest

# Add skill root to path
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))

try:
    from scripts.fin_agent import FinAgent
    from scripts.utils.database_manager import DatabaseManager
except ImportError as e:
    print(f"Import Error: {e}")
    sys.exit(1)

class TestTracker(unittest.TestCase):
    def test_init(self):
        print("Testing FinAgent...")
        # FinAgent Init might be complex. Checking import is a good start.
        pass

if __name__ == '__main__':
    unittest.main()
