"""Canonical JSON, content hashes, strict loading, and state snapshots. Standard library only."""
from __future__ import annotations

import hashlib
import json
import math
import re

__all__ = ["RecordError", "canonical_json", "content_hash", "strict_loads", "is_hash", "validate_state",
           "StateStore", "STATE_SCHEMA", "REPRESENTATIONS"]

STATE_SCHEMA = "glab.state/1"
REPRESENTATIONS = ("exact", "approximate", "mixed")
_STATE_KEYS = {"schema", "kind", "parent", "representation", "payload"}
_HASH = re.compile(r"sha256:[0-9a-f]{64}")


class RecordError(ValueError):
    """A record is malformed, inconsistent, or references something missing."""


def _check_json(obj, path="$"):
    if obj is None or isinstance(obj, (bool, str)):
        return
    if isinstance(obj, int):
        return
    if isinstance(obj, float):
        if not math.isfinite(obj):
            raise RecordError(f"nonfinite number at {path}")
        return
    if isinstance(obj, list):
        for i, x in enumerate(obj):
            _check_json(x, f"{path}[{i}]")
        return
    if isinstance(obj, dict):
        for k, v in obj.items():
            if not isinstance(k, str):
                raise RecordError(f"non-string key {k!r} at {path}")
            _check_json(v, f"{path}.{k}")
        return
    raise RecordError(f"non-JSON value of type {type(obj).__name__} at {path}")


def canonical_json(obj) -> str:
    """Sorted keys, no whitespace, ASCII, finite numbers; floats use shortest round-trip repr."""
    _check_json(obj)
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True, allow_nan=False)


def content_hash(obj) -> str:
    return "sha256:" + hashlib.sha256(canonical_json(obj).encode("ascii")).hexdigest()


def is_hash(value) -> bool:
    return isinstance(value, str) and _HASH.fullmatch(value) is not None


def _no_duplicates(pairs):
    out = {}
    for k, v in pairs:
        if k in out:
            raise RecordError(f"duplicate key {k!r}")
        out[k] = v
    return out


def _no_constants(name):
    raise RecordError(f"nonfinite literal {name} rejected")


def strict_loads(text: str):
    """json.loads that rejects duplicate keys and NaN/Infinity literals."""
    try:
        return json.loads(text, object_pairs_hook=_no_duplicates, parse_constant=_no_constants)
    except json.JSONDecodeError as exc:
        raise RecordError(f"invalid JSON: {exc}") from None


def _contains_float(obj) -> bool:
    if isinstance(obj, float):
        return True
    if isinstance(obj, list):
        return any(_contains_float(x) for x in obj)
    if isinstance(obj, dict):
        return any(_contains_float(x) for x in obj.values())
    return False


def validate_state(record) -> None:
    """Structural validation of one state record (references are checked by StateStore)."""
    if not isinstance(record, dict):
        raise RecordError("state must be an object")
    if set(record) != _STATE_KEYS:
        raise RecordError(f"state keys {sorted(record)} != {sorted(_STATE_KEYS)}")
    if record["schema"] != STATE_SCHEMA:
        raise RecordError(f"unsupported state schema {record['schema']!r}")
    if not isinstance(record["kind"], str) or not record["kind"]:
        raise RecordError("state kind must be a nonempty string")
    if record["parent"] is not None and not is_hash(record["parent"]):
        raise RecordError(f"parent must be null or a sha256 hash, got {record['parent']!r}")
    if record["representation"] not in REPRESENTATIONS:
        raise RecordError(f"representation must be one of {REPRESENTATIONS}")
    if not isinstance(record["payload"], dict):
        raise RecordError("payload must be an object")
    _check_json(record["payload"], "$.payload")
    if record["representation"] == "exact" and _contains_float(record["payload"]):
        raise RecordError("exact representation contains a float; declare 'approximate' or 'mixed'")


class StateStore:
    """Hash -> canonical text. Readers always receive fresh copies; retained data cannot be mutated."""

    def __init__(self):
        self._texts: dict[str, str] = {}

    def put(self, record) -> str:
        validate_state(record)
        if record["parent"] is not None and record["parent"] not in self._texts:
            raise RecordError(f"parent references unknown state {record['parent']}")
        text = canonical_json(record)
        h = "sha256:" + hashlib.sha256(text.encode("ascii")).hexdigest()
        self._texts[h] = text
        return h

    def get(self, h: str) -> dict:
        if h not in self._texts:
            raise RecordError(f"unknown state {h}")
        return strict_loads(self._texts[h])

    def __contains__(self, h) -> bool:
        return h in self._texts

    def __len__(self) -> int:
        return len(self._texts)

    def hashes(self) -> list[str]:
        return sorted(self._texts)

    def as_mapping(self) -> dict:
        return {h: strict_loads(t) for h, t in sorted(self._texts.items())}

    def validate_chain(self, h: str) -> list[str]:
        """Re-hash the state and every ancestor; return [h, parent, ..., root]."""
        chain, seen = [], set()
        while h is not None:
            if h in seen:
                raise RecordError(f"cyclic parent reference at {h}")
            seen.add(h)
            if h not in self._texts:
                raise RecordError(f"reference to unknown state {h}")
            rec = strict_loads(self._texts[h])
            if content_hash(rec) != h:
                raise RecordError(f"stored state {h} does not match its hash")
            validate_state(rec)
            chain.append(h)
            h = rec["parent"]
        return chain

    @classmethod
    def from_mapping(cls, mapping: dict) -> "StateStore":
        """Import {hash: record}; every key must equal its content hash and every chain must resolve."""
        store = cls()
        if not isinstance(mapping, dict):
            raise RecordError("states must be an object")
        for h, rec in mapping.items():
            validate_state(rec)
            if not is_hash(h) or content_hash(rec) != h:
                raise RecordError(f"stored state {h} does not match its hash")
            store._texts[h] = canonical_json(rec)
        for h in mapping:
            store.validate_chain(h)
        return store

    def _tamper_for_tests(self, h: str, record) -> None:
        """Test hook only: overwrite a stored record without re-keying it."""
        self._texts[h] = canonical_json(record)
