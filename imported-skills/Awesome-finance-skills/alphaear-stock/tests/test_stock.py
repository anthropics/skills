import sys
import os
import unittest

# Add skill root to path
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))

try:
    from scripts.stock_tools import StockTools
    from scripts.database_manager import DatabaseManager
except ImportError as e:
    print(f"Import Error: {e}")
    sys.exit(1)

class TestStock(unittest.TestCase):
    def test_init(self):
        print("Testing StockTools Iteration...")
        db = DatabaseManager(":memory:")
        tools = StockTools(db)
        self.assertIsNotNone(tools)
        print("StockTools Initialized.")

if __name__ == '__main__':
    unittest.main()
