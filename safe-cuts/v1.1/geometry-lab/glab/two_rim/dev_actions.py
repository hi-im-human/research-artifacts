"""Registered Stage 3 actions: cut, static development, trim (generator side)."""
from __future__ import annotations

from pathlib import Path

from ..core.registry import ActionSpec, Param, StateDraft, source_revision
from .cut import open_cut
from .develop import develop_static
from .trim import apply_trim

__all__ = ["register_development_actions", "DEV_REVISION"]

DEV_REVISION = source_revision(Path(__file__).resolve().parent, "cut.py", "develop.py", "trim.py", "dev_actions.py")


def _cut(state, params, seed):
    return StateDraft("two_rim.cut", open_cut(state["payload"], params["seam"]), "exact")


def _develop(state, params, seed):
    return StateDraft("two_rim.development", develop_static(state["payload"]), "mixed")


def _trim(state, params, seed):
    return StateDraft("two_rim.trimmed_development", apply_trim(state["payload"], params["delta"]), "mixed")


def register_development_actions(registry) -> None:
    registry.register_action(ActionSpec("two_rim.cut.open", 1, "two_rim.material", {"seam": Param.str()},
                                        DEV_REVISION, _cut))
    registry.register_action(ActionSpec("two_rim.develop.static", 1, "two_rim.cut", {}, DEV_REVISION, _develop))
    registry.register_action(ActionSpec("two_rim.trim.apply", 1, "two_rim.development",
                                        {"delta": Param.exact()}, DEV_REVISION, _trim))
