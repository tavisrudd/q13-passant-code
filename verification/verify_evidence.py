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


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    manifest = json.loads(MANIFEST.read_text())
    assert manifest["schema"] == "q13-passant-code-structural-evidence-v2"
    for record in manifest["files"]:
        path = PAPER_ROOT / record["paper_iv_path"]
        assert path.stat().st_size == record["bytes"], path
        assert digest(path) == record["sha256"], path

    for record in manifest["commands"]:
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

    print("Paper-IV q=13 evidence: PASS")


if __name__ == "__main__":
    main()
