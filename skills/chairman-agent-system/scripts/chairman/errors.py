"""Exception hierarchy. Callers can catch :class:`ChairmanError` broadly."""

from __future__ import annotations


class ChairmanError(Exception):
    """Base class for every error this package raises."""


class PermissionDenied(ChairmanError):
    """An action was refused by the permission rules."""


class IncompleteRequest(ChairmanError):
    """A proposal or decision was missing required justification."""


class NotFound(ChairmanError):
    """The referenced agent, request, or task does not exist."""


class StateError(ChairmanError):
    """The operation is invalid for the object's current state."""
