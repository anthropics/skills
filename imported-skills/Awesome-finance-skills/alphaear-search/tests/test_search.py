import sys
import os
import unittest

# Add skill root to path
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))

try:
    from scripts.search_tools import SearchTools
    from scripts.database_manager import DatabaseManager
    from scripts.hybrid_search import InMemoryRAG
except ImportError as e:
    print(f"Import Error: {e}")
    sys.exit(1)

class TestSearch(unittest.TestCase):
    def test_init(self):
        print("Testing SearchTools Iteration...")
        db = DatabaseManager(":memory:")
        tools = SearchTools(db)
        self.assertIsNotNone(tools)
        print("SearchTools Initialized.")

    def test_rag(self):
        print("Testing InMemoryRAG...")
        rag = InMemoryRAG([])
        self.assertIsNotNone(rag)
        print("InMemoryRAG Initialized.")

if __name__ == '__main__':
    unittest.main()
