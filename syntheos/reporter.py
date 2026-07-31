"""Optional per-run report of every backend call made during a CEGAR run,
written under --reportdir/<spec name>/root.txt. A no-op when --reportdir
isn't set (the default).
"""

import json
from pathlib import Path
from typing import Optional, TypedDict, Union

from .spec import SpecData


class CallData(TypedDict, total=False):
    property: str
    envvars: list[str]
    sysvars: list[str]
    elapsed: float
    verdict: Union[bool, str]


class Reporter:
    def __init__(self, specdata: SpecData, reportdir: str):
        self.specdata = specdata
        self.reportdir = reportdir
        self.calls: list[CallData] = []
        self.currentcall: Optional[CallData] = None

    def setcall(self, calldata: CallData) -> None:
        calldata["elapsed"] = round(calldata["elapsed"], 2)
        self.currentcall = calldata

    def closecall(self, verdict: Union[bool, str]) -> None:
        if self.reportdir == "":
            return
        assert self.currentcall is not None, "closecall() called before setcall()"
        self.currentcall["verdict"] = verdict
        self.calls.append(self.currentcall)

    def dump(self) -> None:
        if self.reportdir == "":
            return
        name = self.specdata["name"]
        mydir = self.reportdir + "/" + name
        Path(mydir).mkdir(parents=True, exist_ok=True)
        with open(mydir + "/root.txt", "w+") as reportfile:
            reportfile.write(json.dumps(self.specdata) + "\n")
            reportfile.write(json.dumps(self.calls))
