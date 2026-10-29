"""Accept all tracked changes in a DOCX file using LibreOffice.

Requires LibreOffice (soffice) to be installed.
"""

import argparse
import logging
import shutil
import subprocess
import tempfile
from pathlib import Path

from office.soffice import get_soffice_env

logger = logging.getLogger(__name__)


ACCEPT_CHANGES_MACRO = """<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE script:module PUBLIC "-//OpenOffice.org//DTD OfficeDocument 1.0//EN" "module.dtd">
<script:module xmlns:script="http://openoffice.org/2000/script" script:name="Module1" script:language="StarBasic">
    Sub AcceptAllTrackedChanges()
        Dim document As Object
        Dim dispatcher As Object

        document = ThisComponent.CurrentController.Frame
        dispatcher = createUnoService("com.sun.star.frame.DispatchHelper")

        dispatcher.executeDispatch(document, ".uno:AcceptAllTrackedChanges", "", 0, Array())
        ThisComponent.store()
        ThisComponent.close(True)
    End Sub
</script:module>"""


def accept_changes(
    input_file: str,
    output_file: str,
) -> tuple[None, str]:
    input_path = Path(input_file)
    output_path = Path(output_file)

    if not input_path.exists():
        return None, f"Error: Input file not found: {input_file}"

    if not input_path.suffix.lower() == ".docx":
        return None, f"Error: Input file is not a DOCX file: {input_file}"

    try:
        output_path.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(input_path, output_path)
    except Exception as e:
        return None, f"Error: Failed to copy input file to output location: {e}"

    # Fresh private profile per run: a fixed shared-temp path could be
    # pre-created by another local user, who would then control the macro.
    with tempfile.TemporaryDirectory(prefix="lo_profile_", ignore_cleanup_errors=True) as profile:
        return _run_accept_macro(Path(profile), output_path, input_file, output_file)


def _run_accept_macro(
    profile: Path, output_path: Path, input_file: str, output_file: str
) -> tuple[None, str]:
    if not _setup_libreoffice_macro(profile):
        return None, "Error: Failed to setup LibreOffice macro"

    cmd = [
        "soffice",
        "--headless",
        f"-env:UserInstallation={profile.as_uri()}",
        "--norestore",
        "vnd.sun.star.script:Standard.Module1.AcceptAllTrackedChanges?language=Basic&location=application",
        str(output_path.absolute()),
    ]

    try:
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=30,
            check=False,
            env=get_soffice_env(),
        )
    except subprocess.TimeoutExpired:
        return (
            None,
            f"Successfully accepted all tracked changes: {input_file} -> {output_file}",
        )

    if result.returncode != 0:
        return None, f"Error: LibreOffice failed: {result.stderr}"

    return (
        None,
        f"Successfully accepted all tracked changes: {input_file} -> {output_file}",
    )


def _setup_libreoffice_macro(profile: Path) -> bool:
    macro_dir = profile / "user" / "basic" / "Standard"
    macro_file = macro_dir / "Module1.xba"

    if not macro_dir.exists():
        try:
            subprocess.run(
                [
                    "soffice",
                    "--headless",
                    f"-env:UserInstallation={profile.as_uri()}",
                    "--terminate_after_init",
                ],
                capture_output=True,
                timeout=10,
                check=False,
                env=get_soffice_env(),
            )
        except subprocess.TimeoutExpired:
            logger.warning("Timed out initializing LibreOffice profile")
            return False
        macro_dir.mkdir(parents=True, exist_ok=True)

    try:
        macro_file.write_text(ACCEPT_CHANGES_MACRO)
        return True
    except Exception as e:
        logger.warning(f"Failed to setup LibreOffice macro: {e}")
        return False


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Accept all tracked changes in a DOCX file"
    )
    parser.add_argument("input_file", help="Input DOCX file with tracked changes")
    parser.add_argument(
        "output_file", help="Output DOCX file (clean, no tracked changes)"
    )
    args = parser.parse_args()

    _, message = accept_changes(args.input_file, args.output_file)
    print(message)

    if "Error" in message:
        raise SystemExit(1)
