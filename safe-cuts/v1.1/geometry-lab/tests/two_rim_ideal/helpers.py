"""Stage 4B test helpers: registries with the ideal lane, specimens, run builders and test-only mutation actions.

The test-only actions (names starting with `test.`) exist only in registries built here; they create deliberately
faulty states so that the checker's refusals can be exercised. Maintained code never registers them.
"""
from __future__ import annotations

import copy
import json
from dataclasses import replace
from fractions import Fraction

from glab.check.two_rim_development import register_development_checkers
from glab.ideal_check.checker import register_ideal_checkers
from glab.check.two_rim_source import register_checkers
from glab.core.registry import ActionSpec, CheckerSpec, Claim, Param, Registry, StateDraft
from glab.core.runfile import Run
from glab.two_rim.actions import register_actions
from glab.two_rim.cut import open_cut
from glab.two_rim.dev_actions import register_development_actions
from glab.two_rim.ideal_actions import register_ideal_actions
from glab.two_rim.material import material_identity
from tests.two_rim_dev.helpers import E11, E11_DELTA  # noqa: F401  (re-exported specimen)

IDEAL_CHECKER = ("two_rim.check.ideal_trimmed_development", 1)
IDEAL_KIND = "two_rim.ideal_trimmed_development"
ORIENTATION = "outward: each face map preserves orientation with respect to that face's outward normal"
NORMALIZATION = "N0: first chain face's entry-hinge low trim point at (0, 0); that hinge along +x"

SQUARE = {"top": [[0, 0], [0, 2], [2, 2], [2, 0]], "bottom": [[0, 0], [0, 2], [2, 2], [2, 0]], "height": "3",
          "input_kind": "cyclic_boundary"}
# Non-dyadic exact prism: side 2/3, height 1/3 (every coordinate and radicand has a factor 3 in its denominator).
NONDYADIC = {"top": [[0, 0], [0, "2/3"], ["2/3", "2/3"], ["2/3", 0]],
             "bottom": [[0, 0], [0, "2/3"], ["2/3", "2/3"], ["2/3", 0]], "height": "1/3",
             "input_kind": "cyclic_boundary"}
NEAR_ZERO = "1/" + "1" + "0" * 30
NEAR_HALF = f"{5 * 10**29 - 1}/{10**30}"


# ---------------------------------------------------------------- test-only mutation actions

def _face(p, fid):
    return next(f for f in p["faces"] if f["id"] == fid)


def _hinge(p, hid):
    return next(e for e in p["hinges"] if e["id"] == hid)


def _m_plane_offset(p):
    p["faces"][0]["plane"][3] += 1


def _m_inward_normal(p):
    p["faces"][0]["plane"] = [-x for x in p["faces"][0]["plane"]]


def _m_zero_normal(p):
    p["faces"][0]["plane"] = [0, 0, 0, 0]


def _m_degenerate_hinge(p):
    h = _hinge(p, "E5")
    h["upper"] = h["lower"]


def _m_duplicate_vertex(p):
    p["vertices"].append(copy.deepcopy(p["vertices"][0]))


def _m_missing_vertex_ref(p):
    p["faces"][0]["boundary"][0] = "B99"


def _m_ring_lacks_endpoint(p):
    f = _face(p, "F5")
    lo = _hinge(p, f["entry"])["lower"]
    f["boundary"] = [v for v in f["boundary"] if v != lo]


def _m_swapped_hinge_ends(p):
    h = _hinge(p, "E5")
    h["lower"], h["upper"] = h["upper"], h["lower"]


def _m_number_domain(p):
    p["number_domain"] = "float64"


def _m_noncanonical_coordinate(p):
    x = Fraction(p["vertices"][0]["xyz"][0])
    p["vertices"][0]["xyz"][0] = f"{2 * x.numerator}/{2 * x.denominator}"


# mutation name -> (function, expected local-premise code)
MATERIAL_MUTATIONS = {
    "plane_offset": (_m_plane_offset, "ring_not_on_plane"),
    "inward_normal": (_m_inward_normal, "orientation_not_outward"),
    "zero_normal": (_m_zero_normal, "normal_zero"),
    "degenerate_hinge": (_m_degenerate_hinge, "hinge_degenerate"),
    "duplicate_vertex": (_m_duplicate_vertex, "identity_ambiguous"),
    "missing_vertex_ref": (_m_missing_vertex_ref, "reference_missing"),
    "ring_lacks_endpoint": (_m_ring_lacks_endpoint, "incidence"),
    "swapped_hinge_ends": (_m_swapped_hinge_ends, "trimmed_ring_not_convex_ccw"),
    "number_domain": (_m_number_domain, "number_domain"),
    "noncanonical_coordinate": (_m_noncanonical_coordinate, "noncanonical_number"),
}


def _mutated_material(state, params, seed):
    payload = copy.deepcopy(state["payload"])
    MATERIAL_MUTATIONS[params["mutation"]][0](payload)
    payload["identity"] = material_identity(payload)
    return StateDraft("two_rim.material", payload, "exact")


def _permuted_cut(state, params, seed):
    cut = open_cut(state["payload"], params["seam"])
    order = cut["face_order"]
    order[1], order[2] = order[2], order[1]
    return StateDraft("two_rim.cut", cut, "exact")


def _base_ideal(cut, delta):
    return {"schema": "two_rim.ideal_trim/1", "definition": "two_rim.ideal_development/1", "delta": delta,
            "orientation": ORIENTATION, "normalization": NORMALIZATION, "cut": copy.deepcopy(cut)}


def _i_nested_coordinate(p, arg):
    v = p["cut"]["material"]["vertices"][0]
    v["xyz"][0] = str(Fraction(v["xyz"][0]) + 1)


IDEAL_MUTATIONS = {
    "none": lambda p, arg: None,
    "extra_key": lambda p, arg: p.update(model={"chain": ["F0"]}),
    "missing_key": lambda p, arg: p.pop("normalization"),
    "wrong_schema": lambda p, arg: p.update(schema="two_rim.ideal_trim/2"),
    "wrong_definition": lambda p, arg: p.update(definition="two_rim.ideal_development/2"),
    "prototype_definition": lambda p, arg: p.update(definition="stage4a.ideal_development/1"),
    "wrong_orientation": lambda p, arg: p.update(orientation="inward"),
    "wrong_normalization": lambda p, arg: p.update(normalization="N1: centroid at the origin"),
    "delta_int": lambda p, arg: p.update(delta=1),
    "cut_not_object": lambda p, arg: p.update(cut="E9"),
    "other_seam_cut": lambda p, arg: p.update(cut=open_cut(p["cut"]["material"], arg["seam"])),
    "other_material_cut": lambda p, arg: p.update(cut=arg["cut"]),
    "nested_coordinate": _i_nested_coordinate,
}


def _raw_ideal(state, params, seed):
    payload = _base_ideal(state["payload"], params["delta"])
    IDEAL_MUTATIONS[params["mutation"]](payload, json.loads(params["arg"]))
    return StateDraft(IDEAL_KIND, payload, "exact")


def _ideal_on_float_parent(state, params, seed):
    return StateDraft(IDEAL_KIND, _base_ideal(state["payload"]["cut"], params["delta"]), "exact")


def _adopted_material(state, params, seed):
    """A material payload placed under an arbitrary source state (source substitution)."""
    return StateDraft("two_rim.material", json.loads(params["payload"]), "exact")


SOURCE_CLAIMS = ("two_rim.source.record_schema", "two_rim.source.height_positive",
                 "two_rim.source.rims_strictly_convex_clockwise", "two_rim.source.normalization_accounts_for_input")


def fake_source_checker():
    """Emits the real source claim names, all pass, without looking at anything: a wrong checker identity."""
    def fn(state, params):
        return [Claim(c, "pass", "exact_computation", "exact_rational") for c in SOURCE_CLAIMS]
    return CheckerSpec("test.fake.check.source", 2, "two_rim.source", {}, "test-only", fn)


class _Override(Registry):
    """A registry whose named checkers carry another revision string, or are replaced by another implementation
    under the same (name, version): a stale or foreign checker."""

    def __init__(self, revisions, replacements):
        super().__init__()
        self._revisions = dict(revisions or {})
        self._replacements = {(s.name, s.version): s for s in replacements}

    def register_checker(self, spec):
        key = (spec.name, spec.version)
        spec = self._replacements.get(key, spec)
        super().register_checker(replace(spec, revision=self._revisions[key]) if key in self._revisions else spec)


TEST_ACTIONS = (
    ActionSpec("test.material.adopted", 1, "two_rim.source", {"payload": Param.str()}, "test-only", _adopted_material),
    ActionSpec("test.material.mutated", 1, "two_rim.material", {"mutation": Param.str()}, "test-only", _mutated_material),
    ActionSpec("test.cut.permuted", 1, "two_rim.material", {"seam": Param.str()}, "test-only", _permuted_cut),
    ActionSpec("test.ideal.raw", 1, "two_rim.cut", {"mutation": Param.str(), "delta": Param.str(), "arg": Param.str()},
               "test-only", _raw_ideal),
    ActionSpec("test.ideal.on_float_parent", 1, "two_rim.development", {"delta": Param.str()}, "test-only",
               _ideal_on_float_parent),
)


# ---------------------------------------------------------------- registries and runs

def registry(*, test_actions=False, extra_checkers=(), revisions=None, replace_checkers=()):
    reg = _Override(revisions, replace_checkers)
    register_actions(reg)
    register_checkers(reg)
    register_development_actions(reg)
    register_development_checkers(reg)
    register_ideal_actions(reg)
    register_ideal_checkers(reg)
    if test_actions:
        for spec in TEST_ACTIONS:
            reg.register_action(spec)
    for spec in extra_checkers:
        reg.register_checker(spec)
    return reg


def new_run(**kw):
    return Run(registry(**kw))


def succeeded(result):
    assert result["status"] == "succeeded", result
    return result["output"]


def material(run, params):
    s = succeeded(run.apply("two_rim.source.normalize", 1, dict(params)))
    m = succeeded(run.apply("two_rim.material.build", 1, {}, s))
    return s, m


def ideal_lane(run, params, seam, delta, *, source_material=None):
    s, m = source_material or material(run, params)
    c = succeeded(run.apply("two_rim.cut.open", 1, {"seam": seam}, m))
    i = succeeded(run.apply("two_rim.ideal.define", 1, {"delta": delta}, c))
    return {"source": s, "material": m, "cut": c, "ideal": i}


def check_ideal(run, ideal_hash):
    return run.check(*IDEAL_CHECKER, ideal_hash, {})


def outcomes(evs):
    return {e["claim"]: e["outcome"] for e in evs}


def by_claim(evs):
    return {e["claim"]: e for e in evs}


def raw_ideal(run, cut_hash, mutation, delta="1/4", arg=None):
    return run.apply("test.ideal.raw", 1, {"mutation": mutation, "delta": delta, "arg": json.dumps(arg or {})},
                     cut_hash)
