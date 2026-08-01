"""Invoking the realizability-checking backend (Strix or SeMLL) on the
current Boolean-abstracted LTL property, and parsing its HOA output into a
game graph.
"""

import datetime
import shutil
import subprocess
import sys
import time
from pathlib import Path

from .boolizer import LITTY, Booleanizer
from .config import CONFIG
from .errors import SyntheosError
from .formula import ltlt2str
from .hoa import Node, parsehoa
from .logging_utils import logger
from .reporter import CallData, Reporter


def resolve_binary(configured_path: str) -> str:
    """`configured_path` is used as-is if it exists (this keeps the documented
    default of running from the repo root with `./strix` right next to it);
    otherwise fall back to looking the bare binary name up on PATH, so an
    installed Syntheos can also work with Strix/SeMLL installed system-wide."""
    if Path(configured_path).exists():
        return configured_path
    found = shutil.which(Path(configured_path).name)
    return found or configured_path


def callstrix(boolizer: Booleanizer, reporter: Reporter) -> list[Node]:
    ltlproperty = boolizer.getboolformula()
    logger.debug("Table of literals:")
    logger.debug("\n".join(f"{l} : {f} ({k})" for l, (f, k) in boolizer.littable.items()))
    strixprop = ltlt2str(ltlproperty)
    logger.debug("LTL property:")
    logger.debug(strixprop)
    envlits = [l for l, (_, k) in boolizer.littable.items() if k == LITTY.ENV]
    envlitsstr = ",".join(envlits)
    syslits = [l for l, (_, k) in boolizer.littable.items() if k == LITTY.SYS]
    syslitsstr = ",".join(syslits)
    calldata: CallData = {
        "property": strixprop,
        "envvars": envlits,
        "sysvars": syslits,
    }
    if CONFIG.backend == "strix":
        binary = resolve_binary(CONFIG.strix_bin)
        command = [binary, "-f", strixprop, "--ins=" + envlitsstr, "--outs=" + syslitsstr, "-o", "hoa"]
    else:
        binary = resolve_binary(CONFIG.semml_bin)
        command = [binary, "-f", strixprop, "--ins=" + envlitsstr, "--outs=" + syslitsstr]
    starttime = time.time()
    logger.info("Calling at %s", datetime.datetime.fromtimestamp(starttime))
    logger.info(" ".join(command))
    try:
        backendout = subprocess.check_output(command, timeout=CONFIG.strixmaxsecs)
        stoptime = time.time()
        logger.info("Returned at %s", datetime.datetime.fromtimestamp(stoptime))
        calldata["elapsed"] = stoptime - starttime
        reporter.setcall(calldata)
    except Exception as exc:
        print(exc, file=sys.stderr)
        stoptime = time.time()
        calldata["elapsed"] = stoptime - starttime
        reporter.setcall(calldata)
        reporter.closecall("UNKNOWN")
        reporter.dump()
        raise SyntheosError(f"Backend call failed: {exc}") from exc
    hoainfo = parsehoa(backendout.decode("utf-8"), boolizer.littable)
    boolizer.realizable = hoainfo["realizable"]
    reporter.closecall(boolizer.realizable)
    return hoainfo["nodes"]
