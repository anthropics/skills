import socket
import unittest

from soffice import _needs_shim


class NeedsShimTests(unittest.TestCase):
    def test_returns_false_when_af_unix_is_unavailable(self) -> None:
        sentinel = object()
        original = getattr(socket, "AF_UNIX", sentinel)
        if original is not sentinel:
            delattr(socket, "AF_UNIX")

        try:
            self.assertFalse(_needs_shim())
        finally:
            if original is not sentinel:
                setattr(socket, "AF_UNIX", original)


if __name__ == "__main__":
    unittest.main()
