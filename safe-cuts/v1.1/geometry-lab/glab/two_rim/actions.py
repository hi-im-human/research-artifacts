"""Registered two-rim actions (generator side). Callbacks call the exact source/material functions only."""
from __future__ import annotations

from pathlib import Path

from ..core.registry import ActionSpec, Param, StateDraft, source_revision
from .material import build_material
from .source import INPUT_KINDS, normalize_source

__all__ = ["register_actions", "TWO_RIM_REVISION", "RIM_PARAM"]

TWO_RIM_REVISION = source_revision(Path(__file__).resolve().parent, "source.py", "material.py", "actions.py")
RIM_PARAM = Param.list(Param.list(Param.exact()))  # point dimension and polygon rules are domain checks


def _normalize(state, params, seed):
    payload = normalize_source(params["top"], params["bottom"], params["height"], params["input_kind"])
    return StateDraft("two_rim.source", payload, "exact")


def _build(state, params, seed):
    return StateDraft("two_rim.material", build_material(state["payload"]), "exact")


def register_actions(registry) -> None:
    registry.register_action(ActionSpec(
        "two_rim.source.normalize", 1, None,
        {"top": RIM_PARAM, "bottom": RIM_PARAM, "height": Param.exact(), "input_kind": Param.enum(INPUT_KINDS)},
        TWO_RIM_REVISION, _normalize))
    registry.register_action(ActionSpec("two_rim.material.build", 1, "two_rim.source", {}, TWO_RIM_REVISION,
                                        _build))
