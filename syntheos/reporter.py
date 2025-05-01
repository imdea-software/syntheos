import json
from pathlib import Path
import re

class Reporter:
  def __init__(self, specdata, reportdir):
    self.specdata = specdata
    self.reportdir = reportdir
    self.calls = []
    self.currentcall = None

  def setcall(self, calldata):
    calldata["elapsed"] = round(calldata["elapsed"], 2)
    self.currentcall = calldata

  def closecall(self, verdict):
    if self.reportdir == "":
      return
    self.currentcall["verdict"] = verdict
    self.calls.append(self.currentcall)

  def dump(self):
    if self.reportdir == "":
      return
    name = self.specdata["name"]
    mydir = self.reportdir + "/" + name
    Path(mydir).mkdir(parents=True, exist_ok=True)
    with open(mydir + "/root.txt", "w+") as reportfile:
      reportfile.write(json.dumps(self.specdata)+"\n")
      reportfile.write(json.dumps(self.calls))
    for i, call in enumerate(self.calls):
      fname = name + str(i) + ".tsl "
      out = ",".join(call["envvars"]) + " "
      out += ",".join(call["sysvars"]) + " "
      out += "(" + (re.sub('(l\\d+)', '"\\1"', call["property"])).replace(' ',"") + ")"
      with open(mydir + "/" + fname, "w+") as reportfile:
        reportfile.write(out)
