"""Typeset publication edition 1.1 with Pandoc and XeLaTeX.

Run: python build_pdf.py ../manuscript.md output_directory
Requires Pandoc, XeLaTeX (with graphicx and pdflscape), Latin Modern, and DejaVu Sans Mono.
Adapted from the approved v1.0 build (which is unchanged): new edition label, output name and pinned
edition source; the two Figure 1 panel images are hash-checked and figure-1-pages.tex replaces the
Markdown figure block; Pandoc writes LF line endings on every platform.
No network, manuscript edits, or mathematical verification are performed.
"""
from __future__ import annotations
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

SOURCE_SHA256 = "93b65e2eb67230b420c19d1d5df52b734f66bbda3c2a848f7ee09f24c1b44677"
PDF_NAME = "Safe_Cuts_Illustrated_v1.1.pdf"
EDITION = "Publication edition 1.1 · 2026"
FIGURE_INPUTS = {
    "figure-1-panels-a-b.png": "532bb2571d92194f6d06d4c2bf081ba91aa6fd5fc68632471cc37cf0c9214ccb",
    "figure-1-panels-c-d.png": "412bf3ddea94fabbec85079839ead12c005a386da92d3406061eb4ab8a030c93",
}
FIGURE_BLOCK = re.compile(r"<!-- figure-1:begin -->\n.*?\n<!-- figure-1:end -->\n", re.S)


def run(args: list[str], cwd: Path, env: dict[str, str]) -> str:
    completed = subprocess.run(args, cwd=cwd, env=env, text=True,
                               stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if completed.returncode:
        raise RuntimeError(f"{args[0]} failed ({completed.returncode}):\n{completed.stdout}")
    return completed.stdout


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    if len(sys.argv) != 3:
        raise SystemExit("Usage: python build_pdf.py ../manuscript.md output_directory")
    source, output = Path(sys.argv[1]).resolve(), Path(sys.argv[2]).resolve()
    here = Path(__file__).resolve().parent
    raw = source.read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    if digest != SOURCE_SHA256:
        raise SystemExit("Source fingerprint differs from the pinned edition 1.1 manuscript; no PDF written.")
    figure_dir = here.parent / "figure-1"
    for name, expected in FIGURE_INPUTS.items():
        if sha256(figure_dir / name) != expected:
            raise SystemExit(f"Figure input {name} differs from its pinned crop; no PDF written.")
    text = raw.decode("utf-8")
    body = text[text.index("# Abstract\n"):]
    # The preceding title/byline is typeset by pdf-style.tex; Figure 1 pages come from figure-1-pages.tex.
    pages = (here / "figure-1-pages.tex").read_text(encoding="utf-8")
    body, count = FIGURE_BLOCK.subn(lambda _: "```{=latex}\n" + pages + "```\n", body)
    if count != 1:
        raise SystemExit(f"Expected one Figure 1 block, found {count}; no PDF written.")
    for executable in ("pandoc", "xelatex"):
        if not shutil.which(executable):
            raise SystemExit(f"Required executable not found: {executable}")
    output.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ)
    # Fixed source date (2026-10-08T00:00:00Z) improves repeatability within the same toolchain.
    env.update(SOURCE_DATE_EPOCH="1791417600", FORCE_SOURCE_DATE="1", TZ="UTC")
    with tempfile.TemporaryDirectory(prefix="safe-cuts-pdf-") as scratch:
        work = Path(scratch)
        (work / "body.md").write_text(body, encoding="utf-8", newline="\n")
        shutil.copyfile(here / "pdf-style.tex", work / "pdf-style.tex")
        for name in FIGURE_INPUTS:
            shutil.copyfile(figure_dir / name, work / name)
        command = ["pandoc", "body.md", "--from=markdown", "--to=latex", "--standalone", "--eol=lf",
                   "--no-highlight", "--include-in-header=pdf-style.tex",
                   "--metadata=title:Safe Cuts for Two-Rim Convex Bands",
                   "--metadata=author:System (AI research agent)",
                   f"--metadata=date:{EDITION}",
                   "--variable=fontsize:11pt", "--variable=papersize:letter",
                   "--variable=geometry:left=0.9in,right=0.9in,top=0.85in,bottom=0.85in",
                   "--variable=monofont:DejaVu Sans Mono", "--variable=monofontoptions:Scale=0.85",
                   "--output=manuscript.tex"]
        pandoc_log = run(command, work, env)
        logs = [pandoc_log]
        for _ in range(2):
            logs.append(run(["xelatex", "-no-shell-escape", "-halt-on-error",
                             "-interaction=nonstopmode", "manuscript.tex"], work, env))
        shutil.copyfile(work / "manuscript.pdf", output / PDF_NAME)
        shutil.copyfile(work / "manuscript.tex", output / "manuscript.tex")
        (output / "build.log").write_text("\n".join(logs), encoding="utf-8", newline="\n")
        versions = {name: run([name, "--version"], work, env).splitlines()[0]
                    for name in ("pandoc", "xelatex")}
        report = {
            "edition": EDITION,
            "source_sha256": digest,
            "source_bytes": len(raw),
            "figure_inputs_sha256": FIGURE_INPUTS,
            "pdf_name": PDF_NAME,
            "pdf_sha256": sha256(output / PDF_NAME),
            "pdf_bytes": (output / PDF_NAME).stat().st_size,
            "tex_sha256": sha256(output / "manuscript.tex"),
            "tools": versions,
            "source_unchanged": source.read_bytes() == raw,
            "scope": "Typesetting only; no new proof verification, peer review, or publication."
        }
        (output / "build.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8", newline="\n")
        print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
