import unittest
import os
import subprocess
from pypdf import PdfReader
from reportlab.pdfgen import canvas
from reportlab.lib.pagesizes import letter

# Get the absolute path of the current script
TESTS_DIR = os.path.dirname(os.path.abspath(__file__))
# Go up one level to the project root
PROJECT_ROOT = os.path.dirname(TESTS_DIR)

def create_dummy_pdf(filename, num_pages):
    """Creates a simple PDF with a specified number of pages."""
    c = canvas.Canvas(filename, pagesize=letter)
    for i in range(num_pages):
        c.drawString(100, 750, f"This is page {i + 1} of {filename}.")
        c.showPage()
    c.save()

class TestPdfSkills(unittest.TestCase):

    def setUp(self):
        """Set up test files."""
        self.test_files = []
        self.generated_files = []

        # Create dummy PDFs in the project root
        doc1_path = os.path.join(PROJECT_ROOT, "test_doc1.pdf")
        create_dummy_pdf(doc1_path, 1)
        self.test_files.append(doc1_path)

        doc2_path = os.path.join(PROJECT_ROOT, "test_doc2.pdf")
        create_dummy_pdf(doc2_path, 2)
        self.test_files.append(doc2_path)

    def tearDown(self):
        """Clean up generated files."""
        all_files_to_clean = self.test_files + self.generated_files

        for f in all_files_to_clean:
            if os.path.exists(f):
                os.remove(f)

    def test_merge_skill(self):
        """Test the PDF merge skill."""
        output_filename = os.path.join(PROJECT_ROOT, "merged_test.pdf")
        self.generated_files.append(output_filename)

        # Use absolute paths for input files
        doc1_path = os.path.join(PROJECT_ROOT, "test_doc1.pdf")
        doc2_path = os.path.join(PROJECT_ROOT, "test_doc2.pdf")

        cmd = [
            "python",
            os.path.join(PROJECT_ROOT, "skills/pdf-merge/merge.py"),
            doc1_path,
            doc2_path,
            "-o",
            output_filename
        ]

        result = subprocess.run(cmd, capture_output=True, text=True, cwd=PROJECT_ROOT)

        self.assertEqual(result.returncode, 0, f"Merge script failed with output:\\n{result.stdout}\\n{result.stderr}")
        self.assertTrue(os.path.exists(output_filename), f"Output file {output_filename} was not created.")

        reader = PdfReader(output_filename)
        self.assertEqual(len(reader.pages), 3, "Merged PDF does not have the correct number of pages.")

    def test_split_skill(self):
        """Test the PDF split skill."""
        input_filename = os.path.join(PROJECT_ROOT, "test_doc2.pdf")

        cmd = [
            "python",
            os.path.join(PROJECT_ROOT, "skills/pdf-split/split.py"),
            input_filename
        ]

        result = subprocess.run(cmd, capture_output=True, text=True, cwd=PROJECT_ROOT)

        self.assertEqual(result.returncode, 0, f"Split script failed with output:\\n{result.stdout}\\n{result.stderr}")

        # Check for split files in the project root
        for i in range(1, 3):
            output_filename = os.path.join(PROJECT_ROOT, f"page_{i}.pdf")
            self.generated_files.append(output_filename)
            self.assertTrue(os.path.exists(output_filename), f"Split file {output_filename} was not created.")
            reader = PdfReader(output_filename)
            self.assertEqual(len(reader.pages), 1, f"Split file {output_filename} should have 1 page.")

        # Ensure no extra files were created
        non_existent_file = os.path.join(PROJECT_ROOT, "page_3.pdf")
        self.generated_files.append(non_existent_file)
        self.assertFalse(os.path.exists(non_existent_file), "Extra split file was created.")

if __name__ == '__main__':
    unittest.main(verbosity=2)
