# shield

A standalone runtime shield for a Mealy machine synthesized by
[Syntheos](../syntheos). Given a mealy machine saved via `syntheos
--save-mealy`, it reads environment/proposed-system plays from stdin (one
JSON `[env_play, sys_play]` pair per line) and prints the safe system
response to play instead, one JSON object per line.

## Usage

```
shield --mealy path/to/mealy.yaml < plays.jsonl
```

## Development

```
pip install -e '.[dev]'
pytest
```
