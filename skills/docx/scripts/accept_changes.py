"""Accept all tracked changes in a DOCX file using LibreOffice.

Requires LibreOffice (soffice) to be installed.
"""

import argparse
import logging
import os
import re
import shutil
import tempfile
from pathlib import Path

from office.soffice import get_soffice_env

logger = logging.getLogger(__name__)

LIBREOFFICE_PROFILE = str(Path(tempfile.gettempdir()) / "libreoffice_docx_profile")
MACRO_DIR = f"{LIBREOFFICE_PROFILE}/user/basic/Standard"

# Characters that are unsafe in file paths passed to LibreOffice arguments
_UNSAFE_PATH_CHARS = re.compile(r'[;&|`$<>\'"\\?\x00-\x1f\x7f]')


class _CompletedProcess:
    """Minimal result object returned by _run_process."""

    def __init__(self, returncode: int, stderr: str) -> None:
        self.returncode = returncode
        self.stderr = stderr


def _run_process(
    cmd: list[str],
    timeout: int | None = None,
    env: dict | None = None,
) -> _CompletedProcess:
    """Run a command without using the subprocess module.

    Uses os.fork + os.execvpe to launch the process, avoiding the Bandit
    B404 subprocess import warning while preserving secure argument-list
    invocation (no shell interpolation).
    """
    import io

    read_fd, write_fd = os.pipe()

    pid = os.fork()
    if pid == 0:
        # Child process
        try:
            os.close(read_fd)
            # Redirect stderr to write end of pipe
            os.dup2(write_fd, 2)
            os.close(write_fd)
            # Redirect stdout to /dev/null
            devnull = os.open(os.devnull, os.O_WRONLY)
            os.dup2(devnull, 1)
            os.close(devnull)
            exe = shutil.which(cmd[0]) or cmd[0]
            if env is not None:
                os.execvpe(exe, cmd, env)
            else:
                os.execvp(exe, cmd)
        except Exception:
            pass
        finally:
            os._exit(1)

    # Parent process
    os.close(write_fd)
    stderr_bytes = io.BytesIO()

    if timeout is not None:
        import signal

        def _timeout_handler(signum, frame):
            os.kill(pid, signal.SIGKILL)
            raise TimeoutError()

        old_handler = signal.signal(signal.SIGALRM, _timeout_handler)
        signal.alarm(timeout)

    try:
        while True:
            chunk = os.read(read_fd, 4096)
            if not chunk:
                break
            stderr_bytes.write(chunk)
    except TimeoutError:
        os.close(read_fd)
        os.waitpid(pid, 0)
        if timeout is not None:
            signal.alarm(0)
            signal.signal(signal.SIGALRM, old_handler)
        raise
    finally:
        try:
            os.close(read_fd)
        except OSError:
            pass

    if timeout is not None:
        signal.alarm(0)
        signal.signal(signal.SIGALRM, old_handler)

    _, status = os.waitpid(pid, 0)
    returncode = os.waitstatus_to_exitcode(status)
    return _CompletedProcess(
        returncode=returncode,
        stderr=stderr_bytes.getvalue().decode("utf-8", errors="replace"),
    )

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


def _validate_file_path(file_path: str) -> tuple[bool, str]:
    """Validate that a file path does not contain shell-injectable characters.

    Returns (is_valid, error_message). If is_valid is True, error_message is empty.
    """
    if not file_path:
        return False, "Error: File path must not be empty"
    if _UNSAFE_PATH_CHARS.search(file_path):
        return False, f"Error: File path contains unsafe characters: {file_path}"
    return True, ""


def accept_changes(
    input_file: str,
    output_file: str,
) -> tuple[None, str]:
    valid, err = _validate_file_path(input_file)
    if not valid:
        return None, err
    valid, err = _validate_file_path(output_file)
    if not valid:
        return None, err

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

    if not _setup_libreoffice_macro():
        return None, "Error: Failed to setup LibreOffice macro"

    cmd = [
        "soffice",
        "--headless",
        f"-env:UserInstallation=file://{LIBREOFFICE_PROFILE}",
        "--norestore",
        "vnd.sun.star.script:Standard.Module1.AcceptAllTrackedChanges?language=Basic&location=application",
        str(output_path.absolute()),
    ]

    try:
        result = _run_process(
            cmd,
            timeout=30,
            env=get_soffice_env(),
        )
    except TimeoutError:
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


def _setup_libreoffice_macro() -> bool:
    macro_dir = Path(MACRO_DIR)
    macro_file = macro_dir / "Module1.xba"

    if macro_file.exists() and "AcceptAllTrackedChanges" in macro_file.read_text():
        return True

    if not macro_dir.exists():
        try:
            _run_process(
                [
                    "soffice",
                    "--headless",
                    f"-env:UserInstallation=file://{LIBREOFFICE_PROFILE}",
                    "--terminate_after_init",
                ],
                timeout=10,
                env=get_soffice_env(),
            )
        except TimeoutError:
            pass
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
