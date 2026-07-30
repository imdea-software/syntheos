import io

import pytest

from syntheos.errors import SyntheosError
from syntheos.spec import readfromyaml


def write_spec(tmp_path, content: str):
    p = tmp_path / "spec.yaml"
    p.write_text(content)
    return str(p)


def test_reads_minimal_spec_and_fills_defaults(tmp_path):
    path = write_spec(tmp_path, 'property: "G([x>0])"\n')
    spec = readfromyaml(path)
    assert spec["property"] == "G([x>0])"
    assert spec["variables"] == []
    assert spec["tmptautos"] == []
    assert spec["name"] == "spec"  # derived from filename stem


def test_explicit_name_overrides_filename_stem(tmp_path):
    path = write_spec(tmp_path, 'property: "G([x>0])"\nname: "custom"\n')
    spec = readfromyaml(path)
    assert spec["name"] == "custom"


def test_reads_variables(tmp_path):
    content = """
property: "G([x>0])"
variables:
  - name: x
    type: Int
    owner: system
"""
    path = write_spec(tmp_path, content)
    spec = readfromyaml(path)
    assert spec["variables"] == [{"name": "x", "type": "Int", "owner": "system"}]


def test_missing_property_raises(tmp_path):
    path = write_spec(tmp_path, "variables: []\n")
    with pytest.raises(SyntheosError):
        readfromyaml(path)


def test_invalid_yaml_raises(tmp_path):
    path = write_spec(tmp_path, "property: [unterminated\n")
    with pytest.raises(SyntheosError):
        readfromyaml(path)


def test_reads_from_stdin_when_fname_is_none(monkeypatch):
    monkeypatch.setattr("sys.stdin", io.StringIO('property: "G([x>0])"\n'))
    spec = readfromyaml(None)
    assert spec["name"] == "UNKNOWN"
    assert spec["property"] == "G([x>0])"
