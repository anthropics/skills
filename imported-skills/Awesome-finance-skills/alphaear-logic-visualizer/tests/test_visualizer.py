import sys
import os
import unittest

# Add skill root to path
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))

try:
    from scripts.visualizer import VisualizerTools
except ImportError as e:
    print(f"Import Error: {e}")
    sys.exit(1)

class TestLogicViz(unittest.TestCase):
    def test_init(self):
        print("Testing VisualizerTools Iteration...")
        viz = VisualizerTools()
        self.assertIsNotNone(viz)

if __name__ == '__main__':
    unittest.main()
