"""
Helper for running LibreOffice (soffice) across platforms.

On Linux, AF_UNIX sockets may be blocked (e.g., sandboxed VMs).  This detects
the restriction at runtime and applies an LD_PRELOAD shim if needed.  On
Windows and macOS no shim is used: the binary is located on PATH or in the
standard install location.

Usage:
    from office.soffice import run_soffice, get_soffice_env, find_soffice

    # Option 1 - run soffice directly
    result = run_soffice(["--headless", "--convert-to", "pdf", "input.docx"])

    # Option 2 - get the binary + env for your own subprocess calls
    env = get_soffice_env()
    subprocess.run([find_soffice(), ...], env=env)
"""

import os
import shutil
import socket
import subprocess
import sys
import tempfile
from pathlib import Path

IS_WINDOWS = sys.platform == "win32"
IS_MACOS = sys.platform == "darwin"
IS_LINUX = sys.platform.startswith("linux")

# Windows Python builds do not expose socket.AF_UNIX at all, so touching it
# raises AttributeError rather than OSError.
HAS_AF_UNIX = hasattr(socket, "AF_UNIX")


class SofficeNotFound(RuntimeError):
    """Raised when the LibreOffice binary cannot be located."""


_WINDOWS_CANDIDATES = [
    r"C:\Program Files\LibreOffice\program\soffice.exe",
    r"C:\Program Files (x86)\LibreOffice\program\soffice.exe",
]

_MACOS_CANDIDATES = [
    "/Applications/LibreOffice.app/Contents/MacOS/soffice",
]


def find_soffice() -> str:
    """Locate the soffice binary.

    Checks $SOFFICE_BIN, then PATH, then the platform's standard install
    location.  The Windows installer does not put soffice on PATH, so PATH
    lookup alone is not enough there.
    """
    override = os.environ.get("SOFFICE_BIN")
    if override:
        if Path(override).is_file():
            return override
        raise SofficeNotFound(f"SOFFICE_BIN is set but is not a file: {override}")

    for name in ("soffice", "soffice.exe"):
        found = shutil.which(name)
        if found:
            return found

    candidates: list[str] = []
    if IS_WINDOWS:
        candidates = list(_WINDOWS_CANDIDATES)
        for root_var in ("ProgramFiles", "ProgramFiles(x86)", "ProgramW6432"):
            root = os.environ.get(root_var)
            if root:
                candidates.append(
                    str(Path(root) / "LibreOffice" / "program" / "soffice.exe")
                )
    elif IS_MACOS:
        candidates = list(_MACOS_CANDIDATES)

    for candidate in candidates:
        if Path(candidate).is_file():
            return candidate

    raise SofficeNotFound(
        "Could not find the LibreOffice 'soffice' binary.  Install LibreOffice, "
        "put soffice on PATH, or set the SOFFICE_BIN environment variable to its "
        "full path."
    )


def get_soffice_env() -> dict:
    env = os.environ.copy()

    # SAL_USE_VCLPLUGIN and the LD_PRELOAD shim are Linux-only.
    if IS_LINUX:
        env["SAL_USE_VCLPLUGIN"] = "svp"

        if _needs_shim():
            shim = _ensure_shim()
            env["LD_PRELOAD"] = str(shim)

    return env


def run_soffice(args: list[str], **kwargs) -> subprocess.CompletedProcess:
    """Run soffice with a private user profile.

    Without a dedicated profile, soffice hands the job to any LibreOffice
    instance the user already has open and exits 0 having converted nothing --
    a silent no-op that is harder to diagnose than a crash.
    """
    env = get_soffice_env()
    args = list(args)

    if not any(a.startswith("-env:UserInstallation") for a in args):
        profile = Path(tempfile.gettempdir()) / "lo_profile_skill"
        profile.mkdir(parents=True, exist_ok=True)
        args.insert(0, f"-env:UserInstallation={profile.as_uri()}")

    return subprocess.run([find_soffice()] + args, env=env, **kwargs)



_SHIM_SO = Path(tempfile.gettempdir()) / "lo_socket_shim.so"


def _needs_shim() -> bool:
    if not IS_LINUX or not HAS_AF_UNIX:
        return False
    try:
        s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        s.close()
        return False
    except OSError:
        return True


def _ensure_shim() -> Path:
    if _SHIM_SO.exists():
        return _SHIM_SO

    src = Path(tempfile.gettempdir()) / "lo_socket_shim.c"
    src.write_text(_SHIM_SOURCE)
    subprocess.run(
        ["gcc", "-shared", "-fPIC", "-o", str(_SHIM_SO), str(src), "-ldl"],
        check=True,
        capture_output=True,
    )
    src.unlink()
    return _SHIM_SO


_SHIM_SOURCE = r"""
#define _GNU_SOURCE
#include <dlfcn.h>
#include <errno.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/socket.h>
#include <unistd.h>

static int (*real_socket)(int, int, int);
static int (*real_socketpair)(int, int, int, int[2]);
static int (*real_listen)(int, int);
static int (*real_accept)(int, struct sockaddr *, socklen_t *);
static int (*real_close)(int);
static int (*real_read)(int, void *, size_t);

/* Per-FD bookkeeping (FDs >= 1024 are passed through unshimmed). */
static int is_shimmed[1024];
static int peer_of[1024];
static int wake_r[1024];            /* accept() blocks reading this */
static int wake_w[1024];            /* close()  writes to this      */
static int listener_fd = -1;        /* FD that received listen()    */

__attribute__((constructor))
static void init(void) {
    real_socket     = dlsym(RTLD_NEXT, "socket");
    real_socketpair = dlsym(RTLD_NEXT, "socketpair");
    real_listen     = dlsym(RTLD_NEXT, "listen");
    real_accept     = dlsym(RTLD_NEXT, "accept");
    real_close      = dlsym(RTLD_NEXT, "close");
    real_read       = dlsym(RTLD_NEXT, "read");
    for (int i = 0; i < 1024; i++) {
        peer_of[i] = -1;
        wake_r[i]  = -1;
        wake_w[i]  = -1;
    }
}

/* ---- socket ---------------------------------------------------------- */
int socket(int domain, int type, int protocol) {
    if (domain == AF_UNIX) {
        int fd = real_socket(domain, type, protocol);
        if (fd >= 0) return fd;
        /* socket(AF_UNIX) blocked – fall back to socketpair(). */
        int sv[2];
        if (real_socketpair(domain, type, protocol, sv) == 0) {
            if (sv[0] >= 0 && sv[0] < 1024) {
                is_shimmed[sv[0]] = 1;
                peer_of[sv[0]]    = sv[1];
                int wp[2];
                if (pipe(wp) == 0) {
                    wake_r[sv[0]] = wp[0];
                    wake_w[sv[0]] = wp[1];
                }
            }
            return sv[0];
        }
        errno = EPERM;
        return -1;
    }
    return real_socket(domain, type, protocol);
}

/* ---- listen ---------------------------------------------------------- */
int listen(int sockfd, int backlog) {
    if (sockfd >= 0 && sockfd < 1024 && is_shimmed[sockfd]) {
        listener_fd = sockfd;
        return 0;
    }
    return real_listen(sockfd, backlog);
}

/* ---- accept ---------------------------------------------------------- */
int accept(int sockfd, struct sockaddr *addr, socklen_t *addrlen) {
    if (sockfd >= 0 && sockfd < 1024 && is_shimmed[sockfd]) {
        /* Block until close() writes to the wake pipe. */
        if (wake_r[sockfd] >= 0) {
            char buf;
            real_read(wake_r[sockfd], &buf, 1);
        }
        errno = ECONNABORTED;
        return -1;
    }
    return real_accept(sockfd, addr, addrlen);
}

/* ---- close ----------------------------------------------------------- */
int close(int fd) {
    if (fd >= 0 && fd < 1024 && is_shimmed[fd]) {
        int was_listener = (fd == listener_fd);
        is_shimmed[fd] = 0;

        if (wake_w[fd] >= 0) {              /* unblock accept() */
            char c = 0;
            write(wake_w[fd], &c, 1);
            real_close(wake_w[fd]);
            wake_w[fd] = -1;
        }
        if (wake_r[fd] >= 0) { real_close(wake_r[fd]); wake_r[fd]  = -1; }
        if (peer_of[fd] >= 0) { real_close(peer_of[fd]); peer_of[fd] = -1; }

        if (was_listener)
            _exit(0);                        /* conversion done – exit */
    }
    return real_close(fd);
}
"""



if __name__ == "__main__":
    try:
        result = run_soffice(sys.argv[1:])
    except SofficeNotFound as exc:
        print(f"error: {exc}", file=sys.stderr)
        sys.exit(127)
    sys.exit(result.returncode)
