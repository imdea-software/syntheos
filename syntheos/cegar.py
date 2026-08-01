"""The CEGAR (counterexample-guided abstraction refinement) loop.

Strix/SeMLL synthesize a controller for the current Boolean abstraction of
the LTLt property. Two things can make that abstraction unsound:

1. Theory inconsistency: an edge's environment/system play, once expanded
   back into Z3, might be vacuous (the environment move is itself
   unsatisfiable) or might not actually respect the "system must have a
   response for every environment move" contract - i.e. the Boolean
   abstraction allowed a move that the theory doesn't actually permit.
   `theoryTauto`/`thConsistent` detect this per edge and, via
   `refinement.refinetauto`, learn a new Boolean tautology that rules it out.

2. Temporal inconsistency: literals about `y(x)` (the previous value of x)
   are only sound if "x now" and "y(x) next" agree - `tmpConsistent` checks
   that across consecutive edges and adds "fetch tautologies" when it
   doesn't hold.

`cegres` reruns the backend and re-checks both kinds of consistency until a
fixpoint (no more edges are inconsistent) is reached.
"""

import logging
import sys
from collections.abc import Callable
from enum import Enum, auto
from typing import TypeVar

from z3 import BoolRef, ExprRef

from . import z3_support as mnz3
from .boolizer import Booleanizer, mapfetch
from .config import CONFIG
from .formula import Formula, ltlDisj, ltlNeg, ltlt2str, z3getvars, z32ltlt
from .hoa import Edge, Node, nodes2dot
from .logging_utils import TRACE, logger
from .refinement import refinetauto
from .reporter import Reporter
from .strix_backend import callstrix


class EDGEKIND(Enum):
    LEGAL = auto()
    ILLEGAL = auto()
    UNREACHABLE = auto()


def envPlayNewThTauto(envz3: BoolRef) -> Formula | None:
    """If the environment's move is unsatisfiable once its own variables are
    existentially quantified away, its negation is a new theory tautology."""
    z3envvars = z3getvars(envz3)
    envexists = mnz3.make_exists(z3envvars, envz3)
    if not mnz3.isSat(envexists):
        return ltlNeg(z32ltlt(envz3))
    return None


def sysPlayNewThTauto(envz3: BoolRef, sysz3: BoolRef, boolizer: Booleanizer) -> Formula | None:
    """If it isn't the case that, for every environment move, some system
    response exists, the system's actual response (unioned with the
    partition of environment moves where a response *is* possible) is a new
    theory tautology."""
    z3envvars = z3getvars(envz3)
    sysplaysymbols = z3getvars(sysz3)
    z3envvars.extend(v for v in sysplaysymbols if not boolizer.isSysVar(v.decl().name()))
    z3sysvars = [v for v in sysplaysymbols if boolizer.isSysVar(v.decl().name())]
    sysexists = mnz3.make_exists(z3sysvars, sysz3)
    implication = mnz3.Implies(envz3, sysexists)
    sysforall = mnz3.make_forall(z3envvars, implication)
    if mnz3.isSat(sysforall):
        return None
    partition = mnz3.eliminate_quantifier(sysexists)
    return ltlDisj(ltlNeg(z32ltlt(sysz3)), z32ltlt(partition))


def theoryTauto(edge: Edge, boolizer: Booleanizer) -> tuple[EDGEKIND, Formula | None]:
    envz3 = edge.getEnvPlay()
    envtauto = envPlayNewThTauto(envz3)
    if envtauto is not None:
        return (EDGEKIND.UNREACHABLE if boolizer.realizable else EDGEKIND.ILLEGAL, envtauto)
    sysz3 = edge.getSysResponse()
    systauto = sysPlayNewThTauto(envz3, sysz3, boolizer)
    if systauto is not None:
        return (EDGEKIND.ILLEGAL if boolizer.realizable else EDGEKIND.UNREACHABLE, systauto)
    return EDGEKIND.LEGAL, None


def thConsistent(edge: Edge, boolizer: Booleanizer, nonewtautosallowed: bool) -> bool:
    edgekind, newthm = theoryTauto(edge, boolizer)
    if edgekind == EDGEKIND.ILLEGAL:
        logger.info("Found theory inconsistency")
        assert newthm is not None
        refined = refinetauto(boolizer, newthm)
        if refined is None:
            logger.info("But there was no new knowledge")
            assert nonewtautosallowed
        else:
            logger.debug("Adding theorem:")
            logger.debug(ltlt2str(refined))
            boolizer.addTauto(refined)
        return False
    return True


def isFetchedVar(var: ExprRef) -> bool:
    return var.decl().name().startswith("FETCH_")


def tmpConsistent(edges: list[Edge], boolizer: Booleanizer, nonewtautosallowed: bool) -> bool:
    """`edges` is a pair of edges taken back to back. Whatever the first
    edge's system+environment play established about "now" must remain
    possible for the second edge's `y(...)`-fetched view of "then"."""
    e0, e1 = edges
    tpre = mapfetch(mnz3.And(e0.getSysResponse(), e0.getEnvPlay()))
    e1envplay = e1.getEnvPlay()
    e1sysplay = e1.getSysResponse()
    e1envplayvars = z3getvars(e1envplay)
    prevars = list(
        dict.fromkeys(z3getvars(tpre) + [v for v in (z3getvars(e1sysplay) + e1envplayvars) if isFetchedVar(v)])
    )
    e1envvars = [v for v in e1envplayvars if not isFetchedVar(v)]
    envexists = mnz3.make_exists(e1envvars, e1envplay)
    fullformula = mnz3.make_forall(prevars, mnz3.Implies(tpre, envexists))
    if mnz3.isSat(fullformula):
        return True
    logger.info("Found temporal inconsistency")
    # unfetched vars existentially quantified out of e1envplay is exactly
    # envexists (e1envvars, computed above, already is that filter)
    fetchexpr = mnz3.eliminate_quantifier(envexists)
    renamed_expr = mnz3.rename_vars(fetchexpr, lambda x: x[6:])
    missing = boolizer.missingTautos(renamed_expr)
    if missing:
        logger.debug("Adding tmp tautos:")
        for t in missing:
            logger.debug(mnz3.z32str(t))
            boolizer.createtmpassumptionfor(t)
    else:
        logger.debug("No new temporal tautos")
        assert nonewtautosallowed
    return False


def _report_edge_progress(i: int, nodesn: int) -> None:
    sys.stdout.write("\r")
    sys.stdout.write(f"Checking edge {i}/{nodesn}. ")
    sys.stdout.flush()


T = TypeVar("T")


def checkconsistencywith(
    edges: list[T],
    boolizer: Booleanizer,
    consf: Callable[[T, Booleanizer, bool], bool],
    inconsistencies: int = 0,
) -> bool:
    """Run `consf` over every edge (or edge pair), tolerating up to
    CONFIG.inconsistent_edges_tolerance inconsistencies before giving up
    early. `inconsistencies` can be seeded by a caller sharing a counter
    between the theory and temporal checks (see cegres); its exact value
    also controls whether "no new knowledge was found" is an assertion
    failure or an accepted short-circuit."""
    nodesn = len(edges)
    allconsistent = True
    for idx, edge in enumerate(edges, 1):
        if logger.isEnabledFor(logging.INFO):
            _report_edge_progress(idx, nodesn)
        edgeconsistent = consf(edge, boolizer, inconsistencies > 0)
        if not edgeconsistent:
            inconsistencies += 1
            allconsistent = False
        if inconsistencies > CONFIG.inconsistent_edges_tolerance:
            return False
    return allconsistent


def cegres(boolizer: Booleanizer, reporter: Reporter) -> list[Node]:
    """Run backend calls and consistency checks to a fixpoint, returning the
    final (consistent) game graph."""
    while True:
        nodes = callstrix(boolizer, reporter)
        if logger.isEnabledFor(TRACE):
            print(nodes2dot(nodes))
        edges = [edge for node in nodes for edge in node.edges]
        consedges = [[edge, consedge] for node in nodes for edge in node.edges for consedge in edge.outnode.edges]
        if checkconsistencywith(edges, boolizer, thConsistent) and (
            boolizer.maxfetchdepth == 0
            or boolizer.realizable
            or checkconsistencywith(consedges, boolizer, tmpConsistent)
        ):
            return nodes
