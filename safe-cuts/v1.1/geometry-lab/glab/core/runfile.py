"""Runs: one ordered history of action and checker attempts, evidence, run files, and replay.

Standard library only. Loading validates structure and chronology and executes
nothing. Replay re-executes registered code only and compares complete records.
"""
from __future__ import annotations

import copy
import platform
from dataclasses import dataclass, field
from pathlib import Path

from .evidence import (UNSET, EvidenceError, check_evidence_structure, evidence_id, make_evidence, summarize,
                       validate_evidence)
from .records import RecordError, StateStore, canonical_json, content_hash, is_hash, strict_loads
from .registry import Claim, Registry, RegistryError, StateDraft, source_revision, validate_params

__all__ = ["Run", "ACTION_SCHEMA", "CHECK_SCHEMA", "RUN_SCHEMA", "RunIntegrityError", "LoadedRun", "load_run",
           "replay", "environment", "core_revision", "DependencyContext", "ContextError"]

ACTION_SCHEMA = "glab.action/2"
CHECK_SCHEMA = "glab.check/1"
RUN_SCHEMA = "glab.run/2"
_RUN_KEYS = {"schema", "environment", "identities", "states", "history", "evidence", "run_digest"}
_ACTION_KEYS = {"schema", "seq", "action", "version", "params", "input", "output", "status",
                "implementation_revision", "seed", "failure", "unrepresentable"}
_CHECK_KEYS = {"schema", "seq", "checker", "version", "params", "subject", "dependencies", "status",
               "checker_revision", "evidence", "failure", "unrepresentable"}
_CORE_DIR = Path(__file__).resolve().parent


class RunIntegrityError(ValueError):
    """A run file is malformed, internally inconsistent, or differs from an external anchor."""


class ContextError(ValueError):
    """A contextual checker asked for a state outside its subject's validated dependency closure."""


class DependencyContext:
    """Read-only snapshot of a subject's validated ancestor closure, for declared contextual checkers.

    It copies the canonical texts of exactly [subject, parent, ..., root] at construction and keeps
    no reference to the store, registry or any generator. Every read returns a fresh copy, so a
    checker cannot change retained states through it. The closure equals the `dependencies`
    recorded on the check attempt and on each evidence record, which bind it to integrity checks,
    reuse validation and replay.
    """

    def __init__(self, store: StateStore, subject: str):
        chain = store.validate_chain(subject)
        self._subject = subject
        self._order = tuple(chain)
        self._texts = {h: canonical_json(store.get(h)) for h in chain}

    @property
    def subject(self) -> str:
        return self._subject

    @property
    def dependencies(self) -> tuple:
        return self._order

    def get(self, h: str) -> dict:
        if h not in self._texts:
            raise ContextError(f"state {h!r} is outside the checked subject's dependency closure")
        return strict_loads(self._texts[h])

    def parent(self):
        """The subject's immediate parent (a fresh copy), or None for a root subject."""
        p = self.get(self._subject)["parent"]
        return None if p is None else self.get(p)


def core_revision() -> str:
    return source_revision(_CORE_DIR, *sorted(p.name for p in _CORE_DIR.glob("*.py")))


def environment() -> dict:
    return {"python": platform.python_version(), "implementation": platform.python_implementation(),
            "platform": platform.platform(), "core_revision": core_revision(),
            "replay_guarantee": "within this recorded environment only"}


def _capture(fields: dict):
    """Detached JSON copies with actual types; non-JSON values become inert descriptions (never evaluated)."""
    out, unrepresentable = {}, []
    for name, value in fields.items():
        try:
            out[name] = strict_loads(canonical_json({"v": value}))["v"]
        except RecordError:
            out[name] = {"python_type": type(value).__name__}
            unrepresentable.append(name)
    return out, unrepresentable


def _failure(stage, exc):
    return {"stage": stage, "type": type(exc).__name__, "message": str(exc)}


def _identities(history) -> dict:
    ids = {"actions": {}, "checkers": {}}
    for h in history:
        if h["schema"] == ACTION_SCHEMA and h["implementation_revision"] is not None:
            ids["actions"][f"{h['action']}@{h['version']}"] = h["implementation_revision"]
        elif h["schema"] == CHECK_SCHEMA and h["checker_revision"] is not None:
            ids["checkers"][f"{h['checker']}@{h['version']}"] = h["checker_revision"]
    return ids


class Run:
    def __init__(self, registry: Registry):
        self._registry = registry
        self._store = StateStore()
        self._history: list[dict] = []   # action and check attempts, one sequence
        self._evidence: list[dict] = []
        self._reproduced: set[str] = set()  # evidence ids produced or re-executed by THIS process

    # ------------------------------------------------------------ read access (copies only)

    def get(self, h: str) -> dict:
        return self._store.get(h)

    @property
    def history(self) -> list[dict]:
        return copy.deepcopy(self._history)

    @property
    def actions(self) -> list[dict]:
        return [h for h in self.history if h["schema"] == ACTION_SCHEMA]

    @property
    def checks(self) -> list[dict]:
        return [h for h in self.history if h["schema"] == CHECK_SCHEMA]

    @property
    def evidence(self) -> list[dict]:
        return copy.deepcopy(self._evidence)

    @property
    def reproduced(self) -> frozenset:
        return frozenset(self._reproduced)

    # ------------------------------------------------------------ actions

    def apply(self, name, version, params, input_hash=None, seed=None) -> dict:
        """Attempt one registered action. The attempt is always appended; a copy is returned."""
        captured, unrep = _capture({"action": name, "version": version, "params": params,
                                    "input": input_hash, "seed": seed})
        record = {"schema": ACTION_SCHEMA, "seq": len(self._history), **captured, "output": None, "status": None,
                  "implementation_revision": None, "failure": None, "unrepresentable": unrep}
        try:
            self._execute(record, name, version, params, input_hash, seed, unrep)
        finally:
            self._history.append(record)
        return copy.deepcopy(record)

    def _execute(self, record, name, version, params, input_hash, seed, unrep):
        try:
            spec = self._registry.action(name, version)
            record["implementation_revision"] = spec.revision
            if unrep:
                raise RegistryError(f"inputs are not JSON-representable: {unrep}")
            validate_params(spec, params)
            if seed is not None and type(seed) is not int:
                raise RegistryError(f"seed must be an int or null, got {seed!r}")
            parent = None
            if spec.accepts is None:
                if input_hash is not None:
                    raise RegistryError(f"{name} v{version} takes no input state")
            else:
                if not is_hash(input_hash) or input_hash not in self._store:
                    raise RegistryError(f"unknown input state {input_hash!r}")
                self._store.validate_chain(input_hash)
                parent = self._store.get(input_hash)
                if parent["kind"] != spec.accepts:
                    raise RegistryError(f"{name} v{version} accepts {spec.accepts}, got {parent['kind']}")
        except (RegistryError, RecordError) as exc:
            record.update(status="rejected", failure=_failure("validation", exc))
            return
        try:
            draft = spec.fn(parent, copy.deepcopy(params), seed)
            if not isinstance(draft, StateDraft):
                raise RecordError(f"action returned {type(draft).__name__}, not StateDraft")
            out = self._store.put({"schema": "glab.state/1", "kind": draft.kind, "parent": input_hash,
                                   "representation": draft.representation, "payload": copy.deepcopy(draft.payload)})
        except Exception as exc:  # noqa: BLE001 - a failed construction is data, recorded not raised
            record.update(status="failed", failure=_failure("execution", exc))
            return
        if input_hash is not None:
            self._store.validate_chain(input_hash)  # retained ancestors unchanged
        record.update(status="succeeded", output=out)

    # ------------------------------------------------------------ checks

    def check(self, name, version, subject, params) -> list[dict]:
        """Run one registered checker. The attempt is recorded first; rejections and failures are then raised.

        A crash or malformed output is an execution failure of this attempt, not a predicate outcome;
        earlier evidence is never altered.
        """
        captured, unrep = _capture({"checker": name, "version": version, "params": params, "subject": subject})
        attempt = {"schema": CHECK_SCHEMA, "seq": len(self._history), **captured, "dependencies": None,
                   "status": None, "checker_revision": None, "evidence": [], "failure": None, "unrepresentable": unrep}
        try:
            try:
                spec = self._registry.checker(name, version)
                attempt["checker_revision"] = spec.revision
                if unrep:
                    raise RegistryError(f"inputs are not JSON-representable: {unrep}")
                validate_params(spec, params)
                if not is_hash(subject) or subject not in self._store:
                    raise RegistryError(f"unknown subject state {subject!r}")
                chain = self._store.validate_chain(subject)
                attempt["dependencies"] = chain
                state = self._store.get(subject)
                if spec.accepts is not None and state["kind"] != spec.accepts:
                    raise RegistryError(f"{name} v{version} accepts {spec.accepts}, got {state['kind']}")
                context = DependencyContext(self._store, subject) if spec.uses_context else None
            except (RegistryError, RecordError) as exc:
                attempt.update(status="rejected", failure=_failure("validation", exc))
                raise
            try:
                claims = (spec.fn(state, copy.deepcopy(params), context) if spec.uses_context
                          else spec.fn(state, copy.deepcopy(params)))
                if not isinstance(claims, list) or not all(isinstance(c, Claim) for c in claims):
                    raise RegistryError(f"checker {name} must return a list of Claim")
                records = [make_evidence(seq=len(self._evidence) + i, attempt=attempt["seq"], claim=c,
                                         subject=subject, dependencies=chain, representation=state["representation"],
                                         checker=name, checker_version=version, checker_revision=spec.revision,
                                         params=captured["params"])
                           for i, c in enumerate(claims)]  # all built (and detached) before any is kept
            except Exception as exc:  # noqa: BLE001 - recorded, then re-raised below
                attempt.update(status="failed", failure=_failure("execution", exc))
                raise
            for rec in records:
                self._evidence.append(rec)
                self._reproduced.add(evidence_id(rec))
            attempt.update(status="completed", evidence=[evidence_id(r) for r in records])
            return copy.deepcopy(records)
        finally:
            self._history.append(attempt)

    def validate(self, record, expected_tolerances=UNSET) -> dict:
        return validate_evidence(record, self._store, self._registry, expected_tolerances=expected_tolerances,
                                 reproduced=self._reproduced)

    def summarize(self, requirements, expected_tolerances=UNSET) -> dict:
        return summarize(self._evidence, requirements, self._store, self._registry,
                         reproduced=self._reproduced, expected_tolerances=expected_tolerances)

    # ------------------------------------------------------------ run file

    def to_record(self) -> dict:
        body = {"schema": RUN_SCHEMA, "environment": environment(), "identities": _identities(self._history),
                "states": self._store.as_mapping(), "history": copy.deepcopy(self._history),
                "evidence": copy.deepcopy(self._evidence)}
        return {**body, "run_digest": content_hash(body)}

    def digest(self) -> str:
        return self.to_record()["run_digest"]

    def save(self, path) -> str:
        """Write canonical JSON with LF endings; return the run digest to retain externally."""
        record = self.to_record()
        Path(path).write_text(canonical_json(record) + "\n", encoding="ascii", newline="\n")
        return record["run_digest"]


# ================================================================ loading (never executes)

@dataclass(frozen=True)
class LoadedRun:
    """One validated snapshot. `record` and `store` are fresh copies built from the same canonical text."""
    text: str = field(repr=False)
    digest: str
    integrity: str          # "internally_consistent" (the only value a successful load can have)
    anchor: str             # "matched" against an externally retained digest, or "unanchored"
    authenticated: bool = False  # hashes give integrity, never authorship

    @property
    def record(self) -> dict:
        return strict_loads(self.text)

    @property
    def store(self) -> StateStore:
        return StateStore.from_mapping(self.record["states"])


def _fail(msg):
    raise RunIntegrityError(msg)


def _pos_int(value) -> bool:
    return type(value) is int and value >= 1


def _check_failure(where, failure, stage):
    if not isinstance(failure, dict) or set(failure) != {"stage", "type", "message"} or failure["stage"] != stage \
            or not isinstance(failure["type"], str) or not isinstance(failure["message"], str):
        _fail(f"{where}: must record a {stage} failure")


def _check_action(i, a, store, available, produced):
    where = f"history {i} (action)"
    if set(a) != _ACTION_KEYS:
        _fail(f"{where}: keys {sorted(a)} != {sorted(_ACTION_KEYS)}")
    if not isinstance(a["unrepresentable"], list) or not set(a["unrepresentable"]) <= {"action", "version", "params",
                                                                                     "input", "seed"}:
        _fail(f"{where}: invalid unrepresentable list")
    status = a["status"]
    if status in ("succeeded", "failed"):
        if not isinstance(a["action"], str) or not a["action"]:
            _fail(f"{where}: action name must be a nonempty string")
        if not _pos_int(a["version"]):
            _fail(f"{where}: executed attempt needs a positive int version (not bool), got {a['version']!r}")
        if not isinstance(a["params"], dict) or a["unrepresentable"]:
            _fail(f"{where}: executed attempt needs JSON object params")
        if a["seed"] is not None and type(a["seed"]) is not int:
            _fail(f"{where}: seed must be an int or null")
        if not isinstance(a["implementation_revision"], str) or not a["implementation_revision"]:
            _fail(f"{where}: executed attempt needs an implementation revision")
        if a["input"] is not None and a["input"] not in available:
            _fail(f"{where}: input {a['input']} is not yet available at this point in the history")
        if status == "failed":
            if a["output"] is not None:
                _fail(f"{where}: failed attempt has an output")
            _check_failure(where, a["failure"], "execution")
        else:
            if a["failure"] is not None or not is_hash(a["output"]) or a["output"] not in store:
                _fail(f"{where}: succeeded without a stored output (unknown state)")
            if store.get(a["output"])["parent"] != a["input"]:
                _fail(f"{where}: output parent differs from recorded input")
            available.add(a["output"])
            produced.add(a["output"])
    elif status == "rejected":
        if a["output"] is not None:
            _fail(f"{where}: rejected attempt has an output")
        if a["implementation_revision"] is not None and not isinstance(a["implementation_revision"], str):
            _fail(f"{where}: implementation revision must be a string or null")
        _check_failure(where, a["failure"], "validation")
    else:
        _fail(f"{where}: unknown status {status!r}")


def _check_check(i, c, store, available, ev_by_attempt, evidence_by_id):
    where = f"history {i} (check attempt)"
    if set(c) != _CHECK_KEYS:
        _fail(f"{where}: keys {sorted(c)} != {sorted(_CHECK_KEYS)}")
    if not isinstance(c["unrepresentable"], list) or not set(c["unrepresentable"]) <= {"checker", "version", "params",
                                                                                     "subject"}:
        _fail(f"{where}: invalid unrepresentable list")
    if not isinstance(c["evidence"], list):
        _fail(f"{where}: evidence must be a list")
    status = c["status"]
    if status in ("completed", "failed"):
        if not isinstance(c["checker"], str) or not c["checker"]:
            _fail(f"{where}: checker name must be a nonempty string")
        if not _pos_int(c["version"]):
            _fail(f"{where}: executed attempt needs a positive int version (not bool), got {c['version']!r}")
        if not isinstance(c["params"], dict) or c["unrepresentable"]:
            _fail(f"{where}: executed attempt needs JSON object params")
        if not isinstance(c["checker_revision"], str) or not c["checker_revision"]:
            _fail(f"{where}: executed attempt needs a checker revision")
        if c["subject"] not in available:
            _fail(f"{where}: subject {c['subject']} is not yet available at this point in the history")
        if c["dependencies"] != store.validate_chain(c["subject"]):
            _fail(f"{where}: dependency closure differs from the stored chain")
        if c["evidence"] != ev_by_attempt.get(i, []):
            _fail(f"{where}: evidence ids differ from the evidence records naming this attempt")
        if status == "failed":
            if c["evidence"]:
                _fail(f"{where}: failed attempt lists evidence")
            _check_failure(where, c["failure"], "execution")
        else:
            if c["failure"] is not None:
                _fail(f"{where}: completed attempt records a failure")
            for eid in c["evidence"]:
                e = evidence_by_id[eid]
                if (e["subject"], e["dependencies"], e["checker"], e["checker_version"], e["checker_revision"],
                        e["params"]) != (c["subject"], c["dependencies"], c["checker"], c["version"],
                                         c["checker_revision"], c["params"]):
                    _fail(f"{where}: evidence {eid} does not match its producing attempt")
    elif status == "rejected":
        if c["evidence"] or ev_by_attempt.get(i):
            _fail(f"{where}: rejected attempt has evidence")
        if c["checker_revision"] is not None and not isinstance(c["checker_revision"], str):
            _fail(f"{where}: checker revision must be a string or null")
        _check_failure(where, c["failure"], "validation")
    else:
        _fail(f"{where}: unknown status {status!r}")


def _validate_history(data, store):
    evidence, history = data["evidence"], data["history"]
    if not isinstance(history, list) or not isinstance(evidence, list):
        _fail("history and evidence must be lists")
    ev_by_attempt, evidence_by_id = {}, {}
    for i, e in enumerate(evidence):
        try:
            check_evidence_structure(e)
        except EvidenceError as exc:
            _fail(f"evidence {i}: {exc}")
        if e["seq"] != i:
            _fail(f"evidence {i}: seq {e['seq']!r} out of order (expected {i})")
        if e["subject"] not in store:
            _fail(f"evidence {i}: subject is an unknown state {e['subject']}")
        if store.get(e["subject"])["representation"] != e["representation"]:
            _fail(f"evidence {i}: representation differs from its subject")
        eid = evidence_id(e)
        evidence_by_id[eid] = e
        ev_by_attempt.setdefault(e["attempt"], []).append(eid)
    available, produced, completed = set(), set(), set()
    for i, h in enumerate(history):
        if not isinstance(h, dict) or type(h.get("seq")) is not int or h["seq"] != i:
            _fail(f"history {i}: seq must be the int {i} (not bool, not reordered)")
        if h.get("schema") == ACTION_SCHEMA:
            _check_action(i, h, store, available, produced)
        elif h.get("schema") == CHECK_SCHEMA:
            _check_check(i, h, store, available, ev_by_attempt, evidence_by_id)
            if h["status"] == "completed":
                completed.add(i)
        else:
            _fail(f"history {i}: unsupported entry schema {h.get('schema')!r}")
    stray = sorted(set(ev_by_attempt) - completed)
    if stray:
        _fail(f"evidence names attempt(s) {stray} that are not completed check attempts")
    orphans = sorted(set(store.hashes()) - produced)
    if orphans:
        _fail(f"state {orphans[0]} was not produced by any recorded action")


def load_run(path, expected_digest=None) -> LoadedRun:
    """Validate a run file structurally and chronologically. Executes nothing.

    Structural only: no registry is consulted, so action/checker existence, parameter types and
    state kinds are NOT checked here; replay() checks those by re-executing registered code.
    """
    try:
        data = strict_loads(Path(path).read_bytes().decode("ascii"))
    except (RecordError, UnicodeDecodeError) as exc:
        raise RunIntegrityError(str(exc)) from None
    if not isinstance(data, dict):
        _fail("run must be an object")
    if data.get("schema") == "glab.run/1":
        _fail("glab.run/1 is not supported: it has no check-attempt history, and none will be invented; "
              "re-create the run with this core")
    if data.get("schema") != RUN_SCHEMA:
        _fail(f"unsupported run schema {data.get('schema')!r}")
    if set(data) != _RUN_KEYS:
        _fail(f"run keys {sorted(data)} != {sorted(_RUN_KEYS)}")
    try:
        store = StateStore.from_mapping(data["states"])
        _validate_history(data, store)
    except RecordError as exc:
        raise RunIntegrityError(str(exc)) from None
    body = {k: v for k, v in data.items() if k != "run_digest"}
    digest = content_hash(body)
    if digest != data["run_digest"]:
        _fail("run digest does not match the recorded content")
    if data["identities"] != _identities(data["history"]):
        _fail("identities are inconsistent with the recorded history")
    if expected_digest is not None and digest != expected_digest:
        _fail("run digest does not match the externally retained digest")
    return LoadedRun(canonical_json(data), digest, "internally_consistent",
                     "matched" if expected_digest is not None else "unanchored")


# ================================================================ replay

def _without(d, *keys):
    return {k: v for k, v in d.items() if k not in keys}


def _comparable_check(entry, evidence_by_id):
    return {**_without(entry, "seq", "evidence"),
            "evidence": [_without(evidence_by_id[e], "seq", "attempt") for e in entry["evidence"]]}


def _available_revision(lookup, name, version):
    try:
        return lookup(name, version).revision
    except RegistryError:
        return None


def replay(loaded: LoadedRun, registry: Registry) -> dict:
    """Re-execute registered actions and checkers in recorded order and compare complete entries.

    outcome "reproduced" requires every entry to match, a matching environment, AND the full run
    digest to be reproduced. Per-entry rows are a partial comparison and are labeled as such.
    """
    data = loaded.record
    if content_hash(_without(data, "run_digest")) != loaded.digest:
        raise RunIntegrityError("loaded snapshot does not match its digest")
    recorded_ev = {evidence_id(e): e for e in data["evidence"]}
    fresh = Run(registry)
    skipped, action_rows, check_rows = set(), [], []
    for h in data["history"]:
        is_action = h["schema"] == ACTION_SCHEMA
        rows = action_rows if is_action else check_rows
        row = {"seq": h["seq"], "name": h["action"] if is_action else h["checker"], "version": h["version"]}
        dependency = h["input"] if is_action else h["subject"]
        if h["unrepresentable"]:
            rows.append({**row, "result": "not_replayable",
                         "reason": f"recorded inputs {h['unrepresentable']} are descriptions, not values"})
        elif isinstance(dependency, str) and dependency in skipped:
            rows.append({**row, "result": "not_run", "reason": "input was not reproduced"})
        elif is_action and _available_revision(registry.action, h["action"], h["version"]) != \
                h["implementation_revision"]:
            rows.append({**row, "result": "not_run", "reason": "implementation revision not available"})
        elif not is_action and _available_revision(registry.checker, h["checker"], h["version"]) != \
                h["checker_revision"]:
            rows.append({**row, "result": "not_run", "reason": "checker revision not available"})
        else:
            if is_action:
                got = fresh.apply(h["action"], h["version"], h["params"], h["input"], h["seed"])
                same = _without(got, "seq") == _without(h, "seq")
            else:
                try:
                    fresh.check(h["checker"], h["version"], h["subject"], h["params"])
                except Exception:  # noqa: BLE001 - the attempt is recorded in fresh history; compare it
                    pass
                fresh_ev = {evidence_id(e): e for e in fresh._evidence}
                same = _comparable_check(fresh._history[-1], fresh_ev) == _comparable_check(h, recorded_ev)
            rows.append({**row, "result": "reproduced" if same else "mismatch", "reason": ""})
            if same:
                continue
        if is_action and h["output"]:
            skipped.add(h["output"])
    results = [r["result"] for r in action_rows + check_rows]
    env_match = environment() == data["environment"]
    digest_same = fresh.digest() == loaded.digest
    if "mismatch" in results:
        outcome = "mismatch"
    elif "not_run" in results or "not_replayable" in results:
        outcome = "not_run"
    elif not env_match:
        outcome = "environment_mismatch"
    elif not digest_same:
        outcome = "mismatch"  # entries agreed but the whole record did not: never report reproduced
    else:
        outcome = "reproduced"
    return {"outcome": outcome, "environment_match": env_match, "run_digest_reproduced": digest_same,
            "partial_comparison": {"entries": len(results), "reproduced": results.count("reproduced")},
            "actions": action_rows, "checks": check_rows, "run": fresh}
