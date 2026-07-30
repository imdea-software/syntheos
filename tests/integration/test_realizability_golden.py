"""Regression test: replay a fixed set of specs (captured from the
pre-refactor CLI, see tests/golden/baseline.json) through the current CLI and
check the realizability verdict hasn't changed.

This is the primary safety net for the syntheos/ reorganization: it invokes
the real Strix backend, so it's automatically skipped if `strix` isn't
available (e.g. a checkout without the binary), and it's slow (a few minutes)
since it runs the full CEGAR loop against ~60 real specifications.
"""

import json
import subprocess
import sys
from pathlib import Path

import pytest

from tests.conftest import requires_strix

BASELINE_PATH = Path(__file__).resolve().parent.parent / "golden" / "baseline.json"
with open(BASELINE_PATH) as f:
    BASELINE = json.load(f)


def run_syntheos(repo_root, spec_path: str) -> str:
    proc = subprocess.run(
        [sys.executable, "syntheos.py", "--yaml", spec_path],
        cwd=repo_root,
        capture_output=True,
        text=True,
        timeout=120,
    )
    out = proc.stdout
    if "unrealizable" in out:
        return "unrealizable"
    if "realizable" in out:
        return "realizable"
    raise AssertionError(f"Unexpected output for {spec_path}:\nstdout={out}\nstderr={proc.stderr}")


@requires_strix
@pytest.mark.parametrize("spec_path", sorted(BASELINE))
def test_verdict_matches_baseline(repo_root, spec_path):
    assert run_syntheos(repo_root, spec_path) == BASELINE[spec_path]
