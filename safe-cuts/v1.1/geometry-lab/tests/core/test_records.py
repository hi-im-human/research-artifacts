"""Task 1: exact input, canonical records, content hashes, state validation."""
from fractions import Fraction

import pytest

from glab.core.numbers import ExactInputError, format_exact, parse_exact
from glab.core.records import (RecordError, StateStore, canonical_json, content_hash, strict_loads,
                               validate_state)


# ---------------------------------------------------------------- exact input

@pytest.mark.parametrize("value", [1, "1", "2/2", "1.0", "10e-1", "+1", " 1 "])
def test_equal_exact_spellings_normalize(value):
    assert parse_exact(value) == Fraction(1)
    assert format_exact(parse_exact(value)) == "1"


def test_fraction_and_decimal_agree():
    assert parse_exact("0.5") == parse_exact("1/2") == parse_exact("2/4") == Fraction(1, 2)
    assert format_exact(parse_exact("-0.125")) == "-1/8"
    assert parse_exact("1e-20") == Fraction(1, 10 ** 20)


@pytest.mark.parametrize("bad", [0.5, 1.0, True, False, None, [1], "nan", "inf", "-Infinity", "1/0", "",
                                 "1/2/3", "0x10", "1_000", "½"])
def test_nonexact_inputs_rejected(bad):
    with pytest.raises(ExactInputError):
        parse_exact(bad)


# ---------------------------------------------------------------- canonical JSON and hashes

def test_canonical_json_is_order_independent_and_compact():
    a = {"b": [1, "x", None], "a": {"d": True, "c": 2.5}}
    b = {"a": {"c": 2.5, "d": True}, "b": [1, "x", None]}
    assert canonical_json(a) == canonical_json(b) == '{"a":{"c":2.5,"d":true},"b":[1,"x",null]}'
    assert content_hash(a) == content_hash(b)
    assert content_hash(a).startswith("sha256:") and len(content_hash(a)) == 71


@pytest.mark.parametrize("bad", [{"x": float("nan")}, {"x": float("inf")}, {1: "int key"}, {"x": {1, 2}},
                                 {"x": b"bytes"}, {"x": Fraction(1, 2)}])
def test_canonical_json_rejects_non_json_values(bad):
    with pytest.raises(RecordError):
        canonical_json(bad)


def test_strict_loads_rejects_duplicates_and_nonfinite():
    assert strict_loads('{"a":1}') == {"a": 1}
    with pytest.raises(RecordError, match="duplicate"):
        strict_loads('{"a":1,"a":2}')
    for text in ('{"a":NaN}', '{"a":Infinity}', '{"a":-Infinity}'):
        with pytest.raises(RecordError, match="nonfinite"):
            strict_loads(text)


def test_float_round_trips_through_canonical_text():
    x = 0.1 + 0.2
    assert strict_loads(canonical_json({"x": x}))["x"] == x


# ---------------------------------------------------------------- states

def state(**over):
    rec = {"schema": "glab.state/1", "kind": "toy.int", "parent": None, "representation": "exact",
           "payload": {"value": "3"}}
    rec.update(over)
    return rec


def test_valid_state_passes_and_hash_excludes_nothing_semantic():
    validate_state(state())
    assert content_hash(state()) != content_hash(state(payload={"value": "4"}))
    assert content_hash(state()) != content_hash(state(representation="mixed"))


@pytest.mark.parametrize("over,msg", [
    ({"schema": "glab.state/2"}, "unsupported state schema"),
    ({"kind": ""}, "kind"),
    ({"kind": 3}, "kind"),
    ({"parent": "not-a-hash"}, "parent"),
    ({"parent": "sha256:" + "0" * 63}, "parent"),
    ({"representation": "roughly"}, "representation"),
    ({"payload": [1, 2]}, "payload"),
    ({"payload": {"value": 0.5}}, "exact representation contains a float"),
    ({"payload": {"deep": [{"x": 1.0}]}}, "exact representation contains a float"),
])
def test_invalid_states_rejected(over, msg):
    with pytest.raises(RecordError, match=msg):
        validate_state(state(**over))


def test_state_rejects_extra_or_missing_keys():
    extra = dict(state(), timestamp="2026-09-28")
    missing = {k: v for k, v in state().items() if k != "parent"}
    for rec in (extra, missing):
        with pytest.raises(RecordError, match="keys"):
            validate_state(rec)


def test_approximate_state_may_hold_floats_but_is_never_relabeled_exact():
    rec = state(representation="approximate", payload={"value": 1.5})
    validate_state(rec)
    store = StateStore()
    h = store.put(rec)
    assert store.get(h)["representation"] == "approximate"
    with pytest.raises(RecordError):
        store.put(dict(rec, representation="exact"))


def test_store_returns_defensive_copies():
    store = StateStore()
    rec = state(payload={"value": "3", "items": ["a"]})
    h = store.put(rec)
    rec["payload"]["items"].append("caller mutation")
    got = store.get(h)
    got["payload"]["items"].append("reader mutation")
    assert store.get(h)["payload"]["items"] == ["a"]
    assert content_hash(store.get(h)) == h


def test_store_chain_validation_detects_dangling_and_tampered_ancestors():
    store = StateStore()
    a = store.put(state())
    b = store.put(state(parent=a, payload={"value": "4"}))
    c = store.put(state(parent=b, payload={"value": "5"}))
    assert store.validate_chain(c) == [c, b, a]
    with pytest.raises(RecordError, match="unknown state"):
        store.put(state(parent="sha256:" + "1" * 64))
    store._tamper_for_tests(a, state(payload={"value": "999"}))
    with pytest.raises(RecordError, match="does not match its hash"):
        store.validate_chain(c)


def test_store_rejects_cyclic_references_in_imported_records():
    x = "sha256:" + "a" * 64
    y = "sha256:" + "b" * 64
    raw = {x: state(parent=y), y: state(parent=x)}
    with pytest.raises(RecordError):
        StateStore.from_mapping(raw)
