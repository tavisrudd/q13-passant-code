#!/usr/bin/env python3
"""Verify the Paper-IV q=13 evidence manifest and all exact replay entry points."""

from __future__ import annotations

import hashlib
import json
import shlex
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parent
PAPER_ROOT = ROOT.parent
MANIFEST = ROOT / "evidence_manifest.json"
FORMAL_COMPANION = "lean-certificates"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    manifest = json.loads(MANIFEST.read_text())
    assert manifest["schema"] == "q13-passant-code-structural-evidence-v2"

    # The formal companion is distributed as its own package, so a checkout of the
    # manuscript alone cannot check its digests or run its generator. Records naming
    # the companion package or the shared Lean library it builds against are skipped
    # exactly when the companion is absent, and the count of skipped checks is
    # reported rather than passed over silently.
    companion_present = (PAPER_ROOT / FORMAL_COMPANION).is_dir()
    skipped_files = 0
    skipped_commands = 0

    for record in manifest["files"]:
        entry = record["paper_iv_path"]
        formal = entry.startswith(FORMAL_COMPANION + "/") or entry.startswith("../")
        if formal and not companion_present:
            skipped_files += 1
            continue
        path = PAPER_ROOT / entry
        assert path.stat().st_size == record["bytes"], path
        assert digest(path) == record["sha256"], path

    for record in manifest["commands"]:
        if record["cwd"].split("/")[0] == FORMAL_COMPANION and not companion_present:
            skipped_commands += 1
            continue
        cwd = PAPER_ROOT / Path(record["cwd"])
        completed = subprocess.run(
            shlex.split(record["command"]),
            cwd=cwd,
            check=True,
            capture_output=True,
            text=True,
        )
        output = completed.stdout + completed.stderr
        assert record["output_contains"] in output, record["command"]
        print(output.strip())

    if not companion_present:
        print(
            f"formal companion absent from this checkout: {skipped_files} digests and "
            f"{skipped_commands} command(s) not checked"
        )

    print("Paper-IV q=13 evidence: PASS")


if __name__ == "__main__":
    main()
