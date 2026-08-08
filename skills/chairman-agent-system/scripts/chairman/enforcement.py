"""The enforcement point: authorization that cannot be skipped by not asking.

:mod:`chairman.permissions` is a *decision* point — it answers "is this
permitted?" for whoever bothers to ask. That leaves the obvious hole: code
that never asks is never stopped, so the rules hold only by convention.

This module closes it from both ends.

**Agents never hold callables.** They hold a :class:`Session` bound to their
identity. ``session.invoke(name, ...)`` is the only entry point, and it
authorizes before dispatching.

**Registered functions refuse when called outside an authorized invoke.**
:meth:`ToolBox.register` wraps the function in a guard that checks a
context variable set only by :meth:`Session.invoke`. Reaching around the
session to call the function directly raises
:class:`~chairman.errors.PermissionDenied`.

The guard is task-local (``contextvars``), so it behaves correctly under
threads and asyncio, and it is released even when the handler raises.

Nested calls are not free: a tool that calls another tool must go through
``session.invoke`` for the inner one too, because the guard authorizes one
name at a time. Crossing a tool boundary always costs an authorization.

    box = ToolBox()

    @box.register("ledger.balance", Tool.FINANCE, Classification.CONFIDENTIAL)
    def balance(account: str) -> float:
        return 42.0

    session = Session(registry, box, "ledger-analyst")
    session.invoke("ledger.balance", "ACME")   # authorized, returns 42.0
    balance("ACME")                            # PermissionDenied

**What this is not.** Python has no true sandbox. Someone who can edit the
process can reach ``ToolBox._specs``, reset the context variable, or import
the undecorated function from its defining module. This stops the failure
that actually happens — code paths that forgot to check — not a hostile
caller inside your own interpreter. Treat it as a seatbelt, not a vault.
"""

from __future__ import annotations

import functools
from contextvars import ContextVar
from dataclasses import dataclass
from typing import Any, Callable, Dict, FrozenSet, List, Optional, Union

from .errors import NotFound, PermissionDenied
from .models import Classification, Tool
from .permissions import authorize_action

# Names currently cleared for execution in this task/thread. Set only by
# Session.invoke, always reset in a finally block.
_ACTIVE: ContextVar[FrozenSet[str]] = ContextVar(
    "chairman_active_tools", default=frozenset()
)

Classifier = Callable[..., Classification]
ClassificationSpec = Union[Classification, Classifier]


def active_tools() -> FrozenSet[str]:
    """Tool names authorized in the current call stack. Diagnostic use."""
    return _ACTIVE.get()


@dataclass(frozen=True)
class ToolSpec:
    """A registered tool and the authorization it demands."""

    name: str
    category: Tool
    classification: ClassificationSpec
    writes: bool
    handler: Callable[..., Any]

    def classify(self, *args, **kwargs) -> Classification:
        """Sensitivity of this specific call.

        A static ``Classification`` covers the common case. A callable lets
        sensitivity depend on the arguments — ``read_file("/public/x")`` and
        ``read_file("/payroll/y")`` are not the same request, and pinning
        the tool to its most sensitive possible use would either over-refuse
        or under-protect.
        """
        if callable(self.classification):
            result = self.classification(*args, **kwargs)
            if not isinstance(result, Classification):
                raise TypeError(
                    f"classifier for {self.name} returned {type(result).__name__}, "
                    "expected Classification"
                )
            return result
        return self.classification


class ToolBox:
    """Registry of invocable tools. Registration installs the guard."""

    def __init__(self) -> None:
        self._specs: Dict[str, ToolSpec] = {}

    def register(
        self,
        name: str,
        category: Tool,
        classification: ClassificationSpec,
        writes: bool = False,
    ) -> Callable[[Callable[..., Any]], Callable[..., Any]]:
        """Decorator registering a function and returning its guarded form.

        The returned function is what the defining module binds, so the
        direct-call path is protected too — not only the session path.
        """
        if name in self._specs:
            raise ValueError(f"tool {name!r} is already registered")

        def decorator(fn: Callable[..., Any]) -> Callable[..., Any]:
            @functools.wraps(fn)
            def guarded(*args, **kwargs):
                if name not in _ACTIVE.get():
                    raise PermissionDenied(
                        f"{name} was called directly; tools must be invoked "
                        "through an authorized Session"
                    )
                return fn(*args, **kwargs)

            guarded.__chairman_tool__ = name  # type: ignore[attr-defined]
            self._specs[name] = ToolSpec(
                name=name,
                category=category,
                classification=classification,
                writes=writes,
                handler=guarded,
            )
            return guarded

        return decorator

    def require(self, name: str) -> ToolSpec:
        spec = self._specs.get(name)
        if spec is None:
            raise NotFound(f"no such tool: {name}")
        return spec

    def names(self) -> List[str]:
        return sorted(self._specs)

    def specs(self) -> List[ToolSpec]:
        return [self._specs[n] for n in self.names()]


class Session:
    """An agent's only handle on the tools. Authorizes every invocation."""

    def __init__(self, registry, toolbox: ToolBox, agent_name: str) -> None:
        # Resolve eagerly so an unknown agent fails at construction rather
        # than at the first call.
        self.registry = registry
        self.toolbox = toolbox
        self.agent_name = registry.require_agent(agent_name).name

    def __repr__(self) -> str:
        return f"<Session agent={self.agent_name!r}>"

    def available(self) -> List[str]:
        """Tools this agent may currently invoke, cheapest case only.

        Tools with a dynamic classifier are included when their *lowest*
        possible sensitivity would be permitted, since the real answer
        depends on arguments not yet supplied. Treat this as a menu, not a
        guarantee — :meth:`invoke` is still the authority.
        """
        agent = self.registry.require_agent(self.agent_name)
        out: List[str] = []
        for spec in self.toolbox.specs():
            if spec.category not in agent.tools:
                continue
            floor = (
                Classification.PUBLIC
                if callable(spec.classification)
                else spec.classification
            )
            if authorize_action(agent, spec.category, floor, spec.writes).allowed:
                out.append(spec.name)
        return out

    def invoke(self, name: str, *args, **kwargs) -> Any:
        """Authorize, then dispatch. Raises rather than returning a sentinel.

        A denial raises :class:`~chairman.errors.PermissionDenied` so it
        cannot be mistaken for a result. The permission decision and the
        execution outcome are logged separately: a call can be permitted and
        still fail, and the two are different facts about the system.
        """
        spec = self.toolbox.require(name)
        classification = spec.classify(*args, **kwargs)

        decision = self.registry.authorize(
            self.agent_name,
            spec.category,
            classification,
            write=spec.writes,
            resource=name,
        )
        if not decision.allowed:
            raise PermissionDenied(f"{name} denied for {self.agent_name}: {decision.reason}")

        token = _ACTIVE.set(_ACTIVE.get() | {name})
        try:
            result = spec.handler(*args, **kwargs)
        except Exception as exc:
            self.registry.record(
                actor=self.agent_name,
                action=f"invoke:{name}",
                resource=name,
                outcome="error",
                details={"error": type(exc).__name__, "message": str(exc)[:500]},
            )
            raise
        finally:
            # Reset before the audit write below so a failure there cannot
            # leave the guard open.
            _ACTIVE.reset(token)

        self.registry.record(
            actor=self.agent_name,
            action=f"invoke:{name}",
            resource=name,
            outcome="ok",
            details={"classification": classification.name, "write": spec.writes},
        )
        return result


__all__ = [
    "Classifier",
    "Session",
    "ToolBox",
    "ToolSpec",
    "active_tools",
]
