import yaml
from .datatypes import *
from pathlib import Path

def readfromyaml(fname):
  specdata = {}
  if fname is None:
    dbg1("Reading YAML from stdin")
    stream = sys.stdin
    specname = "UNKNOWN"
  else:
    dbg1("Reading YAML from file")
    stream = open(fname)
    specname = Path(fname).stem
  with stream:
    try:
      specraw = yaml.safe_load(stream)
    except yaml.YAMLError as exc:
      error(exc)
  try:
    specdata["property"] = specraw["property"]
    specdata["name"] = specraw.get("name", specname)
    specdata["variables"] = specraw.get("variables",[])
    specdata["tmptautos"] = specraw.get("tmptautos",[])
  except KeyError as exc:
    error(exc)
  return specdata
