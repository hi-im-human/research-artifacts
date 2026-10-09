"""Load the byte-verified historical PhysicalBridge copy for golden tests only (never production)."""
from __future__ import annotations

import hashlib
import importlib.util
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent / "pinned_bridge"
# Edition 1.1 export: the midsection_bridge.py pin identifies the export copy, in which one unused fallback
# folder name was replaced by a placeholder; the historical blob is cce8c34f29e6a8b970dc8db53db9713da659fc25.
BLOBS = {"code/midsection_bridge.py": "e73f17cdf926aeb37713d41ab17e9f473ad7e12a",
         "baseline/code/normal_fan_inputs.py": "5445ec10af581ae031cb386d1732de4a81dffee9",
         "baseline/code/cyclic_normal_splice.py": "314b1938fb80416a5c867a0e9db7807ed3e9133a"}


def git_blob(path: Path) -> str:
    data = path.read_bytes().replace(b"\r\n", b"\n")
    return hashlib.sha1(b"blob %d\0" % len(data) + data).hexdigest()


def load_bridge():
    """Exec the pinned historical module (export copy: one unused fallback folder name replaced); undo its
    sys.path insertion and module-name side effects."""
    for rel, blob in BLOBS.items():
        if git_blob(HERE / rel) != blob:
            raise RuntimeError(f"pinned {rel} differs from blob {blob}")
    saved_path = list(sys.path)
    names = ("normal_fan_inputs", "cyclic_normal_splice")
    saved_mods = {k: sys.modules.get(k) for k in names}
    try:
        spec = importlib.util.spec_from_file_location("pinned_midsection_bridge", HERE / "code" / "midsection_bridge.py")
        mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mod)
        return mod
    finally:
        sys.path[:] = saved_path
        for k, v in saved_mods.items():
            if v is None:
                sys.modules.pop(k, None)
            else:
                sys.modules[k] = v
