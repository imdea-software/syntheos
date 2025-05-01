import time
import datetime
import subprocess
from .datatypes import *
from .hoaparser import parsehoa

def callstrix(boolizer, reporter, strixmaxsecs):
  ltlproperty = boolizer.getboolformula()
  dbg1("Table of literals:")
  dbg1("\n".join([l + " : " + str(f) + " (" + str(k) + ")" for [l,[f,k]] in boolizer.littable.items()]))
  strixprop = ltlt2str(ltlproperty)
  dbg1("Strix property:")
  dbg1(strixprop)
  envlits = [l for l,[_,k] in boolizer.littable.items() if k == LITTY.ENV]
  envlitsstr = ",".join(envlits)
  syslits = [l for l,[_,k] in boolizer.littable.items() if k == LITTY.SYS]
  syslitsstr = ",".join(syslits)
  calldata = {
      "property": strixprop,
      "envvars": envlits,
      "sysvars": syslits,
  }
  starttime = time.time()
  dbg1("Calling at " + str(datetime.datetime.fromtimestamp(starttime)))
  dbg1("./strix -f '" + strixprop + "' --ins="+envlitsstr + " --outs="+syslitsstr + " -o hoa")
  try:
    strixout = subprocess.check_output(["./strix", "-f", strixprop, "--ins="+envlitsstr, "--outs="+syslitsstr, "-o", "hoa"], timeout = strixmaxsecs)
    stoptime = time.time()
    dbg1("Returned at " + str(datetime.datetime.fromtimestamp(stoptime)))
    calldata["elapsed"] = stoptime - starttime
    reporter.setcall(calldata)
  except Exception as e:
    print(e)
    stoptime = time.time()
    calldata["elapsed"] = stoptime - starttime
    reporter.setcall(calldata)
    reporter.closecall("UNKOWN")
    reporter.dump()
    exit(-1)
  hoainfo = parsehoa(strixout.decode("utf-8"), boolizer.littable)
  boolizer.realizable = hoainfo["realizable"]
  reporter.closecall(boolizer.realizable)
  return hoainfo["nodes"]
