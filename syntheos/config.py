"""Process-wide run configuration, set once from CLI arguments in cli.py."""

from dataclasses import dataclass


@dataclass
class Config:
    backend: str = "strix"
    strixmaxsecs: int | None = None
    inconsistent_edges_tolerance: int = 0
    strix_bin: str = "./strix"
    semml_bin: str = "./semml"


CONFIG = Config()
