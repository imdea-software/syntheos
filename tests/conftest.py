import shutil
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT))


@pytest.fixture
def repo_root() -> Path:
    return REPO_ROOT


def strix_available() -> bool:
    return (REPO_ROOT / "strix").exists() or shutil.which("strix") is not None


requires_strix = pytest.mark.skipif(not strix_available(), reason="strix binary not available")
