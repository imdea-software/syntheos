"""Reading a Syntheos specification from a YAML file (or stdin)."""

import sys
from pathlib import Path
from typing import TextIO, TypedDict

import yaml

from .errors import SyntheosError
from .formula import Variable
from .logging_utils import logger


class MealyEdgeData(TypedDict):
    envplay: str
    sysplay: str
    outnoden: int


class SpecData(TypedDict, total=False):
    property: str
    name: str
    variables: list[Variable]
    tmptautos: list[str]
    # populated later, when writing a solved specification's mealy machine:
    transtab: dict[str, str]
    nodes: list[list[MealyEdgeData]]


def readfromyaml(fname: str | None) -> SpecData:
    stream: TextIO
    if fname is None:
        logger.info("Reading YAML from stdin")
        stream = sys.stdin
        specname = "UNKNOWN"
    else:
        logger.info("Reading YAML from file")
        stream = open(fname)
        specname = Path(fname).stem
    with stream:
        try:
            specraw = yaml.safe_load(stream)
        except yaml.YAMLError as exc:
            raise SyntheosError(str(exc)) from exc
    try:
        specdata: SpecData = {
            "property": specraw["property"],
            "name": specraw.get("name", specname),
            "variables": specraw.get("variables", []),
            "tmptautos": specraw.get("tmptautos", []),
        }
    except KeyError as exc:
        raise SyntheosError(str(exc)) from exc
    return specdata
