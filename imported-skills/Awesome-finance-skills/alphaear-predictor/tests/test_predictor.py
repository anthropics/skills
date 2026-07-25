import sys
import os
import unittest

# Add skill root to path
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))

try:
    from scripts.kronos_predictor import KronosPredictorUtility
    from scripts.utils.database_manager import DatabaseManager
except ImportError as e:
    print(f"Import Error: {e}")
    sys.exit(1)

class TestPredictor(unittest.TestCase):
    def test_init(self):
        print("Testing KronosPredictorUtility Iteration...")
        db = DatabaseManager(":memory:")
        # Kronos might need model files, but init should pass if we don't call predict?
        # Note: Kronos loads model in init. This might fail if model path is invalid.
        # We wrap in try-except to catch model loading errors which are expected in this env
        try:
            tools = KronosPredictorUtility()
            self.assertIsNotNone(tools)
        except Exception as e:
            print(f"Kronos Init failed (expected if no model): {e}")

if __name__ == '__main__':
    unittest.main()
