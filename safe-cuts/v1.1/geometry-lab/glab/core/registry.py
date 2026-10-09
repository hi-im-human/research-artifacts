"""Explicit (name, version) registry of trusted local actions and checkers. Standard library only.

Files select only a registered (name, version). Nothing from input data is
imported, evaluated, or executed. Registered callbacks are trusted local code;
this is not a sandbox.
"""
from __future__ import annotations

import hashlib
import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Callable, Mapping

from .numbers import ExactInputError, parse_exact

__all__ = ["RegistryError", "Param", "StateDraft", "Claim", "ActionSpec", "CheckerSpec", "Registry",
           "source_revision", "check_version"]

_NAME = re.compile(r"[a-z][a-z0-9_]*(\.[a-z0-9_]+)*")


class RegistryError(ValueError):
    """Unknown or invalid action/checker identity or parameters."""


def check_version(version) -> int:
    if type(version) is not int or version < 1:
        raise RegistryError(f"version must be a positive int (not bool/str), got {version!r}")
    return version


class Param:
    """Declared parameter type: int, str, exact, enum, or list(item). No other kinds exist."""

    def __init__(self, kind: str, values=None, item=None):
        self.kind, self.values, self.item = kind, tuple(values) if values is not None else None, item

    @staticmethod
    def int():
        return Param("int")

    @staticmethod
    def str():
        return Param("str")

    @staticmethod
    def exact():
        return Param("exact")

    @staticmethod
    def enum(values):
        return Param("enum", values)

    @staticmethod
    def list(item):
        """A JSON list whose every element satisfies `item` (validated recursively)."""
        if not isinstance(item, Param):
            raise RegistryError("Param.list needs a Param item declaration")
        return Param("list", item=item)

    def check(self, name, value) -> None:
        if self.kind == "list":
            if type(value) is not list:
                raise RegistryError(f"parameter {name!r} must be a list, got {type(value).__name__}")
            for i, element in enumerate(value):  # list order is semantic, so the first failure is stable
                self.item.check(f"{name}[{i}]", element)
            return
        if self.kind == "int":
            ok = type(value) is int
        elif self.kind == "str":
            ok = isinstance(value, str)
        elif self.kind == "exact":
            try:
                parse_exact(value)
                ok = True
            except ExactInputError:
                ok = False
        elif self.kind == "enum":
            ok = isinstance(value, (str, int)) and not isinstance(value, bool) and value in self.values
        else:
            ok = False
        if not ok:
            raise RegistryError(f"parameter {name!r} must be {self.kind}"
                                f"{' of ' + repr(self.values) if self.values else ''}, got {value!r}")

    def describe(self):
        return {"kind": self.kind, "values": list(self.values) if self.values else None,
                "item": self.item.describe() if self.item is not None else None}


@dataclass(frozen=True)
class StateDraft:
    kind: str
    payload: dict
    representation: str


@dataclass(frozen=True)
class Claim:
    predicate: str
    outcome: str
    method: str
    numeric_domain: str
    coverage: str = "all"
    tolerances: Any = None
    receipt: Any = None


@dataclass(frozen=True)
class ActionSpec:
    """fn(input_state_copy | None, params_copy, seed) -> StateDraft."""
    name: str
    version: int
    accepts: str | None
    params: Mapping[str, Param]
    revision: str
    fn: Callable = field(compare=False)


@dataclass(frozen=True)
class CheckerSpec:
    """fn(subject_state_copy, params_copy) -> list[Claim]; or, when uses_context is True,
    fn(subject_state_copy, params_copy, context) where context is a read-only DependencyContext
    over the subject's validated ancestor closure (declared explicitly, never guessed)."""
    name: str
    version: int
    accepts: str | None
    params: Mapping[str, Param]
    revision: str
    fn: Callable = field(compare=False)
    uses_context: bool = False


def _validate_spec(spec) -> None:
    if not isinstance(spec.name, str) or not _NAME.fullmatch(spec.name):
        raise RegistryError(f"invalid name {spec.name!r}")
    check_version(spec.version)
    if spec.accepts is not None and (not isinstance(spec.accepts, str) or not spec.accepts):
        raise RegistryError("accepts must be None or a state kind")
    if not isinstance(spec.params, Mapping) or not all(isinstance(k, str) and isinstance(v, Param)
                                                       for k, v in spec.params.items()):
        raise RegistryError("params must map names to Param declarations")
    if not isinstance(spec.revision, str) or not spec.revision:
        raise RegistryError("revision must be a nonempty string")
    if not callable(spec.fn):
        raise RegistryError("fn must be callable")
    if type(getattr(spec, "uses_context", False)) is not bool:
        raise RegistryError("uses_context must be a bool")


def validate_params(spec, params) -> None:
    if not isinstance(params, dict):
        raise RegistryError("parameters must be an object")
    # Sorted, not insertion order: canonical records sort object keys, so the reported
    # error must not depend on an order the record treats as nonsemantic (C01).
    for key in sorted(params):
        if key not in spec.params:
            raise RegistryError(f"unexpected parameter {key!r} for {spec.name} v{spec.version}")
    for key, decl in spec.params.items():
        if key not in params:
            raise RegistryError(f"missing parameter {key!r} for {spec.name} v{spec.version}")
        decl.check(key, params[key])


class Registry:
    def __init__(self):
        self._actions: dict[tuple, ActionSpec] = {}
        self._checkers: dict[tuple, CheckerSpec] = {}

    def _register(self, table, spec, kind):
        _validate_spec(spec)
        key = (spec.name, spec.version)
        if key in table:
            raise RegistryError(f"{kind} {spec.name} v{spec.version} already registered")
        table[key] = spec

    def register_action(self, spec: ActionSpec) -> None:
        self._register(self._actions, spec, "action")

    def register_checker(self, spec: CheckerSpec) -> None:
        self._register(self._checkers, spec, "checker")

    @staticmethod
    def _lookup(table, name, version, kind):
        check_version(version)
        if not isinstance(name, str) or not any(n == name for n, _ in table):
            raise RegistryError(f"unknown {kind} {name!r}")
        spec = table.get((name, version))
        if spec is None:
            raise RegistryError(f"unknown version {version} of {kind} {name!r}")
        return spec

    def action(self, name, version) -> ActionSpec:
        return self._lookup(self._actions, name, version, "action")

    def checker(self, name, version) -> CheckerSpec:
        return self._lookup(self._checkers, name, version, "checker")

    def identities(self) -> dict:
        return {"actions": {f"{n}@{v}": s.revision for (n, v), s in sorted(self._actions.items())},
                "checkers": {f"{n}@{v}": s.revision for (n, v), s in sorted(self._checkers.items())}}


def source_revision(root: Path, *relative_paths: str) -> str:
    """Hash of named source files with LF-normalized bytes; stable across checkouts."""
    h = hashlib.sha256()
    for rel in relative_paths:
        data = (Path(root) / rel).read_bytes().replace(b"\r\n", b"\n")
        h.update(rel.encode("utf-8") + b"\0" + data + b"\0")
    return "sha256:" + h.hexdigest()
