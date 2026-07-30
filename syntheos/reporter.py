"""Optional per-run report of every backend call made during a CEGAR run,
written under --reportdir/<spec name>/root.txt. A no-op when --reportdir
isn't set (the default).
"""

import json
from pathlib import Path

from .spec import SpecData


class Reporter:
    def __init__(self, specdata: SpecData, reportdir: str):
        self.specdata = specdata
        self.reportdir = reportdir
        self.calls: list = []
        self.currentcall: dict | None = None

    def setcall(self, calldata: dict) -> None:
        calldata["elapsed"] = round(calldata["elapsed"], 2)
        self.currentcall = calldata

    def closecall(self, verdict) -> None:
        if self.reportdir == "":
            return
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
