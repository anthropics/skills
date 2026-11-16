"""
Helper for running LibreOffice (soffice) in environments where AF_UNIX
sockets may be blocked (e.g., sandboxed VMs).  Detects the restriction
at runtime and applies an LD_PRELOAD shim if needed.

Usage:
    from office.soffice import run_soffice

    result = run_soffice(["--headless", "--convert-to", "pdf", "input.docx"])

Call soffice through run_soffice, not through subprocess with get_soffice_env():
the env dict carries the shim but names no user profile, and a non-root sandbox
cannot bootstrap the default one -- soffice aborts with "User installation could
not be completed" and converts nothing. get_soffice_env() stays public for the
callers that build their own argv (they must pass -env:UserInstallation too).
"""

from __future__ import annotations

import contextlib
import os
import re
import shutil
import socket
import subprocess
import tempfile
import zipfile
from collections.abc import Iterable
from pathlib import Path


def get_soffice_env() -> dict:
    env = os.environ.copy()
    env["SAL_USE_VCLPLUGIN"] = "svp"

    if _needs_shim():
        shim = _ensure_shim()
        env["LD_PRELOAD"] = str(shim)

    return env


def run_soffice(args: Iterable[str], **kwargs) -> subprocess.CompletedProcess:
    args = list(args)
    with contextlib.ExitStack() as stack:
        if not any(str(a).startswith("-env:UserInstallation") for a in args):
            profile = stack.enter_context(
                tempfile.TemporaryDirectory(prefix="lo_profile_", ignore_cleanup_errors=True)
            )
            args = [f"-env:UserInstallation={Path(profile).as_uri()}"] + args
        if _draws_the_document(args):
            copies = Path(stack.enter_context(
                tempfile.TemporaryDirectory(prefix="lo_input_", ignore_cleanup_errors=True)
            ))
            args = [_without_outside_links(str(a), copies / str(i)) for i, a in enumerate(args)]
        return subprocess.run(["soffice"] + args, env=get_soffice_env(), **kwargs)



_SHIM_SO = Path(tempfile.gettempdir()) / "lo_socket_shim.so"

_DRAWN_FORMATS = frozenset(
    {"pdf", "png", "jpg", "jpeg", "gif", "bmp", "tif", "tiff", "webp", "svg", "eps", "emf", "wmf"}
)
_WEB_OR_MAIL = re.compile(r"^(?:https?|mailto):", re.I)
_RELS_NS = "http://schemas.openxmlformats.org/package/2006/relationships"
_NO_RELS = f'<Relationships xmlns="{_RELS_NS}"/>'.encode()
_MAX_RELS_BYTES = 32 * 1024 * 1024


def _draws_the_document(args: list) -> bool:
    for flag, value in zip(args, args[1:]):
        if str(flag) in ("--convert-to", "-convert-to"):
            return str(value).split(":")[0].lower() in _DRAWN_FORMATS
    return False


def _cut_outside_links(rels: bytes) -> bytes | None:
    from defusedxml import ElementTree

    try:
        root = ElementTree.fromstring(rels)
    except (ElementTree.ParseError, ValueError, LookupError):
        return _NO_RELS
    cut = False
    for entry in root.iter():
        if entry.get("TargetMode", "Internal") == "Internal":
            continue
        if _WEB_OR_MAIL.match(entry.get("Target", "")):
            continue
        entry.set("TargetMode", "External")
        entry.set("Target", "about:blank")
        cut = True
    if not cut:
        return None
    for element in root.iter():
        element.tag = element.tag.rsplit("}", 1)[-1]
    root.set("xmlns", _RELS_NS)
    return ElementTree.tostring(root)


def _without_outside_links(arg: str, folder: Path) -> str:

    if not os.path.isfile(arg) or not zipfile.is_zipfile(arg):
        return arg
    with open(arg, "rb") as file:
        if file.read(4) != b"PK\x03\x04":  
            return arg
    with zipfile.ZipFile(arg) as package:
        cut = {}
        for member in package.infolist():
            if member.filename.lower().endswith(".rels"):
                try:
                    data = package.read(member) if member.file_size <= _MAX_RELS_BYTES else None
                except Exception:  
                    data = None
                rels = _NO_RELS if data is None else _cut_outside_links(data)
                if rels is not None:
                    cut[member.filename] = rels
        if not cut:
            return arg
        folder.mkdir()
        copy = folder / Path(arg).name
        with zipfile.ZipFile(copy, "w") as out:
            for member in package.infolist():
                entry = zipfile.ZipInfo(member.filename, member.date_time)
                entry.compress_type = member.compress_type
                if member.filename in cut:
                    entry.compress_type = zipfile.ZIP_DEFLATED  
                    out.writestr(entry, cut[member.filename])
                else:
                    with package.open(member) as source, out.open(entry, "w", force_zip64=True) as target:
                        shutil.copyfileobj(source, target)
    return str(copy)


def _needs_shim() -> bool:
    if not hasattr(socket, "AF_UNIX"):
        return True
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
    src.write_text(_SHIM_SOURCE, encoding="utf-8")
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
    import sys
    result = run_soffice(sys.argv[1:])
    sys.exit(result.returncode)
