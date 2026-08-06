#!/usr/bin/env python3
"""Rebuild the manuscript deterministically and reject TeX warnings and stale PDFs.

The manuscript is built in a temporary directory from a copy of the tracked
source alone, so the result cannot depend on leftover auxiliary files. The build
is made byte-reproducible by pinning ``SOURCE_DATE_EPOCH`` and setting
``FORCE_SOURCE_DATE``, which fixes the timestamps TeX and the PDF writer would
otherwise embed. The pinned epoch is a build-normalization constant chosen so
that repeated builds agree; it is not a claim about when the manuscript was
written or released. Two builds of one source at different filesystem paths
produce identical bytes, which is what lets this repository and a
standalone copy of it carry the same PDF.

Determinism turns PDF staleness into an exact check. The rebuilt PDF must equal
the tracked PDF byte for byte, which holds exactly when the tracked PDF is the
build of the tracked source. A manuscript edit committed without refreshing the
tracked PDF therefore fails here rather than being certified downstream.

Run with ``--update`` to refresh the tracked PDF from the same deterministic
build. That is the supported way to regenerate it: building by hand without the
pinned epoch produces a PDF that differs in its embedded timestamps and fails
this check.

The TeX toolchain is resolved by the caller. Pinning it is a separate
requirement: the engine version fixes the embedded producer string and font
subset tags, so a toolchain change moves the bytes even with the epoch pinned.
"""

from __future__ import annotations

import argparse
import os
import re
import shutil
import subprocess
import tempfile
from pathlib import Path


PAPER = Path(__file__).resolve().parents[1]
SOURCE = "passant_code_q13.tex"
TRACKED_PDF = PAPER / "passant_code_q13.pdf"
EXPECTED_PAGES = 12
# 2026-01-01T00:00:00Z. Fixed so that independent builds of one source agree.
DETERMINISTIC_EPOCH = "1767225600"

WARNING_RE = re.compile(
    r"(LaTeX Warning|Package .* Warning|Overfull|Underfull|undefined references"
    r"|undefined citations)",
    re.IGNORECASE,
)
PAGES_RE = re.compile(r"Output written on .+ \((\d+) pages?,")


def fail(message: str) -> None:
    raise SystemExit(f"q13-passant-code manuscript: FAIL [{message}]")


def deterministic_environment() -> dict[str, str]:
    environment = dict(os.environ)
    environment["SOURCE_DATE_EPOCH"] = DETERMINISTIC_EPOCH
    environment["FORCE_SOURCE_DATE"] = "1"
    return environment


def build_pdf(build_root: Path) -> bytes:
    """Build the manuscript from a clean copy of the tracked source."""
    shutil.copy2(PAPER / SOURCE, build_root / SOURCE)
    for extra in PAPER.glob("*.bib"):
        shutil.copy2(extra, build_root / extra.name)

    completed = subprocess.run(
        ["latexmk", "-xelatex", "-interaction=nonstopmode", "-halt-on-error", SOURCE],
        cwd=build_root,
        check=False,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        env=deterministic_environment(),
    )
    if completed.returncode != 0:
        detail = (completed.stderr or completed.stdout).splitlines()
        fail("build failed:\n" + "\n".join(detail[-20:]))

    log = (build_root / Path(SOURCE).with_suffix(".log")).read_text(
        encoding="utf-8", errors="replace"
    )
    warnings = sorted({match.group(0) for match in WARNING_RE.finditer(log)})
    if warnings:
        fail(f"TeX warnings {warnings}")
    pages = PAGES_RE.search(log)
    if pages is None:
        fail("no page count in the TeX log")
    if int(pages.group(1)) != EXPECTED_PAGES:
        fail(f"page count {pages.group(1)}, expected {EXPECTED_PAGES}")
    return (build_root / Path(SOURCE).with_suffix(".pdf")).read_bytes()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--update",
        action="store_true",
        help="refresh the tracked PDF from the deterministic build",
    )
    args = parser.parse_args()

    with tempfile.TemporaryDirectory(prefix="q13-passant-code-build-") as scratch:
        rebuilt = build_pdf(Path(scratch))

    if args.update:
        TRACKED_PDF.write_bytes(rebuilt)
        print(f"q13-passant-code manuscript: UPDATED [{len(rebuilt)} bytes]")
        return 0

    if not TRACKED_PDF.is_file():
        fail("tracked PDF is missing; rerun with --update")
    if TRACKED_PDF.read_bytes() != rebuilt:
        fail(
            "tracked PDF differs from a deterministic build of the tracked source; "
            "rerun with --update after a manuscript edit"
        )
    print(f"q13-passant-code manuscript: PASS [{EXPECTED_PAGES} pages, warning-free]")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
