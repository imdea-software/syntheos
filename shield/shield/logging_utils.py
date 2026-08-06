"""Logging setup for the shield.

Uses the standard `logging` module, with `--dbglevel N` making messages
logged at severity <= N (in the dbg1/dbg2/dbg3 sense) visible.

    --dbglevel 0 (default)  -> only WARNING and above
    --dbglevel 1            -> + INFO   (was dbg1)
    --dbglevel 2            -> + DEBUG  (was dbg2)
    --dbglevel 3            -> + TRACE  (was dbg3)
"""

import logging
import sys

TRACE = 5
logging.addLevelName(TRACE, "TRACE")

logger = logging.getLogger("shield")

_LEVEL_BY_DBGLEVEL = {
    0: logging.WARNING,
    1: logging.INFO,
    2: logging.DEBUG,
    3: TRACE,
}


def configure_logging(dbglevel: int) -> None:
    """Set up the shield logger for the given --dbglevel (0-3, higher is
    more verbose; anything above 3 behaves like 3)."""
    level = _LEVEL_BY_DBGLEVEL.get(dbglevel, TRACE if dbglevel > 3 else logging.WARNING)
    logger.setLevel(level)
    if not logger.handlers:
        handler = logging.StreamHandler(sys.stdout)
        handler.setFormatter(logging.Formatter("%(message)s"))
        logger.addHandler(handler)


def trace(msg: str, *args: object) -> None:
    logger.log(TRACE, msg, *args)
