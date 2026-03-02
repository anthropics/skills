"""
CaselyParser — Document-to-Markdown converter for LLM analysis.

Uses docling to convert PDF, DOCX, PPTX, XLSX, HTML and other formats
to clean Markdown while preserving structure, tables and text.

Usage:
    python casely_parser.py <input_dir> <output_dir>

    Or programmatically:
        from casely_parser import DocumentParser
        dp = DocumentParser()
        result = dp.parse_folder("input/requirements", "processed/requirements")
"""

import sys
import logging
import argparse
from pathlib import Path
from typing import List, Optional, cast
from dataclasses import dataclass

try:
    from docling.document_converter import DocumentConverter
except ImportError:
    print("❌ Error: docling is not installed. Install with: pip install docling")
    sys.exit(1)

# Logger configuration
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s [%(levelname)s] %(message)s',
    handlers=[
        logging.StreamHandler()
    ]
)
logger = logging.getLogger(__name__)


@dataclass
class ParsingResult:
    """Result of a folder parsing operation"""
    processed: int
    skipped: int
    errors: List[str]


class DocumentParser:
    """
    Document parser based on docling.

    Supported formats:
        PDF, DOCX, PPTX, XLSX, HTML, HTM, MD, TXT, PNG, JPG, JPEG, TIFF, TIF
    """

    SUPPORTED_EXTENSIONS = {
        '.pdf', '.docx', '.pptx', '.xlsx', '.html',
        '.htm', '.md', '.txt', '.png', '.jpg',
        '.jpeg', '.tiff', '.tif'
    }

    def __init__(self, config: Optional[dict] = None):
        """
        Initialize the parser.

        Args:
            config: Configuration dictionary (encoding, overwrite, etc.)
        """
        logger.info("🚀 Initializing Docling parser")
        self.converter = DocumentConverter()
        self.config = config or {}

    def parse_file(self, file_path: Path, output_dir: Path) -> bool:
        """
        Parse a single file to Markdown.

        Args:
            file_path: Path to the source file
            output_dir: Directory to save the result

        Returns:
            True if file was successfully converted, False if skipped
        """
        output_file = output_dir / f"_parsed_{file_path.stem}.md"

        if output_file.exists():
            logger.info(f"⏭️ Already processed: {output_file.name}")
            return False

        try:
            logger.info(f"🔄 Parsing: {file_path.name}")
            result = self.converter.convert(str(file_path))
            md_content = result.document.export_to_markdown()
            output_file.write_text(md_content, encoding='utf-8')
            logger.info(f"✅ Success: {file_path.name} → {output_file.name}")
            return True
        except Exception as e:
            logger.error(f"❌ Error in {file_path.name}: {e}")
            raise

    def parse_folder(self, raw_dir: str, ready_dir: str) -> ParsingResult:
        """
        Parses all supported files from raw_dir into ready_dir.

        Saves as _parsed_{name}.md. Skips already processed files.

        Args:
            raw_dir: Source directory
            ready_dir: Output directory

        Returns:
            ParsingResult containing counts and errors
        """
        raw_path = Path(raw_dir)
        ready_path = Path(ready_dir)
        ready_path.mkdir(parents=True, exist_ok=True)

        if not raw_path.exists():
            logger.error(f"❌ Directory not found: {raw_dir}")
            return ParsingResult(0, 0, [f"Directory not found: {raw_dir}"])

        result = ParsingResult(processed=0, skipped=0, errors=[])

        for file_path in raw_path.iterdir():
            if not (file_path.is_file() and
                    file_path.suffix.lower() in self.SUPPORTED_EXTENSIONS):
                logger.debug(f"⏭️ Unsupported format: {file_path.name}")
                continue

            try:
                success = self.parse_file(file_path, ready_path)
                if success:
                    result.processed += 1
                else:
                    result.skipped += 1
            except Exception as e:
                result.errors.append(f"{file_path.name}: {str(e)}")

        logger.info(f"🎉 Folder complete: {raw_dir} → {ready_dir} "
                    f"({result.processed} new, {result.skipped} skipped)")
        if result.errors:
            logger.warning(f"⚠️ Errors in {len(result.errors)} files")

        return result

    @classmethod
    def get_supported_formats(cls) -> str:
        """Returns string of supported extensions"""
        return ', '.join(sorted(cls.SUPPORTED_EXTENSIONS))


def find_latest_project() -> Optional[Path]:
    """Find the most recently modified project directory."""
    projects_dir = Path("projects")
    if not projects_dir.exists():
        return None
    
    subdirs = [d for d in projects_dir.iterdir() if d.is_dir()]
    if not subdirs:
        return None
    
    return max(subdirs, key=lambda d: d.stat().st_mtime)


def main():
    """CLI interface for the parser"""
    arg_parser = argparse.ArgumentParser(
        description='CaselyParser — Document to Markdown converter'
    )
    arg_parser.add_argument('input_dir', nargs='?', help='Source directory')
    arg_parser.add_argument('output_dir', nargs='?', help='Output directory (Markdown)')
    args = arg_parser.parse_args()

    logger.info("📋 Supported formats: %s", DocumentParser.get_supported_formats())
    parser = DocumentParser()

    # Case 1: Manual paths provided
    if args.input_dir and args.output_dir:
        parser.parse_folder(args.input_dir, args.output_dir)
        return

    # Case 2: Auto-detect latest project
    latest_project_opt = find_latest_project()
    if not latest_project_opt:
        logger.error("❌ No project found and no paths provided.")
        sys.exit(1)

    latest_project = cast(Path, latest_project_opt)
    logger.info(f"📂 Auto-detected project: {latest_project.name}")

    # List of sub-folders to process
    sub_tasks = [
        ("input/requirements", "processed/requirements"),
        ("input/examples", "processed/examples")
    ]

    total_processed = 0
    for inp_sub, out_sub in sub_tasks:
        inp_path = latest_project / inp_sub
        out_path = latest_project / out_sub
        
        if inp_path.exists():
            logger.info(f"🔎 Scanning {inp_sub}...")
            result = parser.parse_folder(str(inp_path), str(out_path))
            total_processed += result.processed

    if total_processed == 0:
        logger.info("ℹ️ No new files to process.")
    else:
        logger.info(f"✅ Finished! Total new files: {total_processed}")


if __name__ == '__main__':
    main()
