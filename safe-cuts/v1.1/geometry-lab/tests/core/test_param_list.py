"""Stage 2 task 1: Param.list(item), the one authorized core collection validator."""
import pytest

from glab.core.registry import ActionSpec, Param, Registry, RegistryError, StateDraft
from glab.core.runfile import Run, load_run, replay

RIM = Param.list(Param.list(Param.exact()))


def test_accepts_nested_exact_rows():
    RIM.check("top", [[0, 0], ["1/2", "3"], [" -2 ", "1e-20"]])
    RIM.check("top", [])  # emptiness/dimension are domain rules, not registry rules
    RIM.check("top", [[], [1, 2, 3]])


@pytest.mark.parametrize("value,where", [
    ("0,0;1,1", "top"),            # not a list
    ((0, 0), "top"),               # tuple is not a JSON list
    ({"x": 0}, "top"),
    ([[0, 0], "1,1"], "top[1]"),   # malformed row
    ([[0, 0], None], "top[1]"),
    ([[0, 0.5]], "top[0][1]"),     # float coordinate
    ([[True, 0]], "top[0][0]"),    # bool coordinate
    ([[0, "nan"]], "top[0][1]"),
    ([[0, "1/0"]], "top[0][1]"),
    ([[0, [1]]], "top[0][1]"),     # nested too deep
])
def test_rejects_with_the_first_failing_path(value, where):
    with pytest.raises(RegistryError) as err:
        RIM.check("top", value)
    assert f"'{where}'" in str(err.value)


def test_list_of_non_param_is_refused_at_declaration():
    with pytest.raises(RegistryError):
        Param.list(int)


def test_describe_is_recursive():
    assert RIM.describe() == {"kind": "list", "values": None,
                              "item": {"kind": "list", "values": None,
                                       "item": {"kind": "exact", "values": None, "item": None}}}


def _registry():
    reg = Registry()
    reg.register_action(ActionSpec("demo.rim", 1, None, {"top": RIM}, "rim-1",
                                   lambda s, p, seed: StateDraft("demo.rim", {"n": len(p["top"])}, "exact")))
    return reg


def test_rejected_list_attempt_is_recorded_and_replays(tmp_path):
    reg = _registry()
    run = Run(reg)
    ok = run.apply("demo.rim", 1, {"top": [[0, 0], [1, "1/2"]]})
    bad = run.apply("demo.rim", 1, {"top": [[0, 0], [1, 0.5]]})
    assert ok["status"] == "succeeded" and bad["status"] == "rejected"
    assert bad["params"] == {"top": [[0, 0], [1, 0.5]]} and "top[1][1]" in bad["failure"]["message"]
    p = tmp_path / "r.json"
    report = replay(load_run(p, expected_digest=run.save(p)), reg)
    assert report["outcome"] == "reproduced" and report["run_digest_reproduced"] is True
