"""C01 controls: rejected parameter errors must not depend on JSON object insertion order."""
import pytest

from glab.core.registry import Param, RegistryError, validate_params
from glab.core.runfile import Run, load_run, replay
from tests.core.test_rejection_order_c01 import make_registry


@pytest.mark.parametrize("params", [{"z": 0, "a": 0}, {"a": 0, "z": 0}])
@pytest.mark.parametrize("kind", ["action", "check"])
def test_both_insertion_orders_record_the_same_rejection_and_replay(tmp_path, kind, params):
    reg = make_registry()
    run = Run(reg)
    subject = run.apply("follow.source", 1, {})["output"]
    if kind == "action":
        rec = run.apply("follow.add", 1, params, subject)
    else:
        with pytest.raises(RegistryError):
            run.check("follow.check", 1, subject, params)
        rec = run.history[-1]
    assert rec["status"] == "rejected" and rec["params"] == {"a": 0, "z": 0}
    assert "'a'" in rec["failure"]["message"]  # first unexpected key in canonical (sorted) order
    p = tmp_path / "run.json"
    report = replay(load_run(p, expected_digest=run.save(p)), reg)
    assert report["outcome"] == "reproduced" and report["run_digest_reproduced"] is True


def test_insertion_orders_give_identical_digests(tmp_path):
    digests = []
    for params in ({"z": 0, "a": 0}, {"a": 0, "z": 0}):
        run = Run(make_registry())
        s = run.apply("follow.source", 1, {})["output"]
        run.apply("follow.add", 1, params, s)
        digests.append(run.digest())
    assert digests[0] == digests[1]


def test_validate_params_is_order_independent():
    class Spec:
        name, version, params = "x", 1, {"k": Param.int()}
    msgs = []
    for params in ({"z": 0, "a": 0, "k": 1}, {"a": 0, "k": 1, "z": 0}):
        with pytest.raises(RegistryError) as err:
            validate_params(Spec, params)
        msgs.append(str(err.value))
    assert msgs[0] == msgs[1]
