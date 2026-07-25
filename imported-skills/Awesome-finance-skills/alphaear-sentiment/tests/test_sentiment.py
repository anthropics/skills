import sys
import os
import unittest

# Add skill root to path
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))

try:
    from scripts.sentiment_tools import SentimentTools
    from scripts.database_manager import DatabaseManager
except ImportError as e:
    print(f"Import Error: {e}")
    sys.exit(1)

class TestSentiment(unittest.TestCase):
    def test_init(self):
        print("Testing SentimentTools Iteration...")
        db = DatabaseManager(":memory:")
        # Mock mode="llm" to avoid loading large models or needing keys
        tools = SentimentTools(db, mode="llm") 
        self.assertIsNotNone(tools)
        print("SentimentTools Initialized.")

if __name__ == '__main__':
    unittest.main()
