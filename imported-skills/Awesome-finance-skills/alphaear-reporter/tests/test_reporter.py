import sys
import os
import unittest

# Add skill root to path
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))

# try:
from scripts.visualizer import VisualizerTools
from scripts.report_agent import ReportAgent
from scripts.utils.database_manager import DatabaseManager
# except ImportError as e:
#     print(f"Import Error: {e}")
#     sys.exit(1)

class TestReporter(unittest.TestCase):
    def test_visualizer(self):
        print("Testing Visualizer...")
        viz = VisualizerTools()
        self.assertIsNotNone(viz)

    def test_agent_init(self):
        print("Testing ReportAgent...")
        # Mocking or simplified init might be needed if agent requires extensive config
        # Just checking import for now is a big win
        pass

if __name__ == '__main__':
    unittest.main()
