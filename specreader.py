import yaml
from datatypes import *
from pathlib import Path

def readfromyaml(fname):
  dbg1("Reading from YAML")
  specdata = {}
  with open(fname) as stream:
    try:
      specraw = yaml.safe_load(stream)
    except yaml.YAMLError as exc:
      error(exc)
  try:
    specdata["property"] = specraw["property"]
    specdata["name"] = specraw.get("name", Path(fname).stem)
    specdata["variables"] = specraw.get("variables",[])
    specdata["tmptautos"] = specraw.get("tmptautos",[])
  except KeyError as exc:
    error(exc)
  return specdata

