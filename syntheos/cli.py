"""The `syntheos` command: read a YAML LTLt specification, run the CEGAR loop
to decide realizability, and optionally show/save the resulting Mealy
machine.
"""

import argparse
import signal
import sys
from types import FrameType
from typing import Optional

import yaml

from . import logging_utils
from .boolizer import Booleanizer
from .cegar import cegres
from .config import CONFIG
from .errors import SyntheosError
from .formula import getZ3, ltlt2str
from .hoa import Node, nodes2dot
from .ltl_parser import ltltparse
from .reporter import Reporter
from .spec import SpecData, readfromyaml

# The CEGAR loop's consistency checks recurse over LTLt formulas whose depth
# tracks the size of the specification; the default limit is too low for the
# larger benchmark specs.
sys.setrecursionlimit(10000)


def parse_arguments(argv: Optional[list[str]] = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser("LTL fetch")
    parser.add_argument("--yaml", help="YAML with specification", type=str, default=None)
    parser.add_argument("--dbglevel", help="Debug level", type=int, default=0)
    parser.add_argument("--strixmaxsecs", help="Maximum seconds", type=int, default=None)
    parser.add_argument("--reportdir", help="Reports root dir", type=str, default="")
    parser.add_argument("--save-mealy", nargs="?", const="", help="Save mealy machine to file", type=str, default=None)
    parser.add_argument("--show-mealy", action="store_true", help="Show mealy machine")
    parser.add_argument("--inconsistent-edges-tolerance", help="Maximum illegal edges tolerance", type=int, default=0)
    parser.add_argument("--backend", help="Backend (strix or semml)", type=str, default="strix", choices=["strix", "semml"])
    parser.add_argument("--strix-bin", help="Path to the strix binary", type=str, default="./strix")
    parser.add_argument("--semml-bin", help="Path to the semml script", type=str, default="./semml")
    return parser.parse_args(argv)


def initialize_boolizer(specdata: SpecData) -> Booleanizer:
    variables = specdata["variables"]
    boolizer = Booleanizer(variables)
    boolizer.setformula(ltltparse(specdata["property"], variables))
    for tmptauto in specdata["tmptautos"]:
        # `tmptautos` (manually-supplied temporal tautologies about y(...))
        # has been broken since it was introduced in c4e0996 ("tmptautos are
        # back"): it calls a `bparse` that was never defined anywhere in the
        # codebase. No shipped spec exercises this field. Rather than a bare
        # NameError, fail clearly if anyone relies on it.
        raise SyntheosError(
            "tmptautos is not currently implemented (missing parser for entry: "
            f"{tmptauto!r}); leave `tmptautos` unset or empty."
        )
    return boolizer


def writemealy(mealyfname: str, nodes: list[Node], specdata: SpecData) -> None:
    # AP indices Strix reported with an empty name map to None (see hoa.py's
    # TransTab) - such an AP is never referenced by any edge, so it's
    # dropped here rather than crashing on getZ3(None).
    specdata["transtab"] = {
        k: getZ3(v).sexpr() for k, v in nodes[0].edges[0].transtab.items() if v is not None
    }
    specdata["nodes"] = [
        [
            {"envplay": ltlt2str(edge.envplay), "sysplay": ltlt2str(edge.sysplay), "outnoden": edge.outnoden}
            for edge in node.edges
        ]
        for node in nodes
    ]
    with open(mealyfname, "w") as f:
        yaml.dump(specdata, f, default_flow_style=False, sort_keys=False)


def showorsave_mealy(args: argparse.Namespace, nodes: list[Node], specdata: SpecData) -> None:
    if args.show_mealy:
        print("Mealy machine:")
        print(nodes2dot(nodes))
    if args.save_mealy is not None:
        mealyfname = args.save_mealy if args.save_mealy != "" else (specdata["name"] + ".json")
        logging_utils.logger.info("Writing mealy to %s", mealyfname)
        writemealy(mealyfname, nodes, specdata)


def main(argv: Optional[list[str]] = None) -> None:
    args = parse_arguments(argv)
    CONFIG.backend = args.backend
    CONFIG.inconsistent_edges_tolerance = args.inconsistent_edges_tolerance
    CONFIG.strixmaxsecs = args.strixmaxsecs
    CONFIG.strix_bin = args.strix_bin
    CONFIG.semml_bin = args.semml_bin
    logging_utils.configure_logging(args.dbglevel)

    try:
        specdata = readfromyaml(args.yaml)
        reporter = Reporter(specdata, args.reportdir)

        def exit_gracefully(signum: int, frame: Optional[FrameType]) -> None:
            reporter.dump()

        signal.signal(signal.SIGINT, exit_gracefully)
        signal.signal(signal.SIGTERM, exit_gracefully)

        boolizer = initialize_boolizer(specdata)
        nodes = cegres(boolizer, reporter)
        print("Done. The property is %s." % ("realizable" if boolizer.realizable else "unrealizable"))
        showorsave_mealy(args, nodes, specdata)
        reporter.dump()
    except SyntheosError as exc:
        print(f"Error: {exc}", file=sys.stderr)
        raise SystemExit(1) from exc


if __name__ == "__main__":
    main()
