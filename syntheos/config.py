"""Process-wide run configuration, set once from CLI arguments in cli.py."""

from dataclasses import dataclass
from typing import Optional


@dataclass
class Config:
    backend: str = "strix"
    strixmaxsecs: Optional[int] = None
    inconsistent_edges_tolerance: int = 0
    strix_bin: str = "./strix"
    semml_bin: str = "./semml"


CONFIG = Config()
