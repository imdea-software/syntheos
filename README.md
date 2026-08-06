# Syntheos

Syntheos is a tool for checking the realizability of specifications expressed in Linear Temporal Logic with theories (LTLt). The atomic propositions in the specification are Z3 predicates, which can refer to the previous value of a quantitative variable `x` with `y(x)`.

## Installation

To install Syntheos, clone this repository and install it (in editable mode, so
changes to the source take effect immediately) into a virtual environment:

```sh
 git clone https://github.com/imdea-software/syntheos.git
 cd syntheos
 python3 -m venv .venv
 source .venv/bin/activate
 python3 -m pip install -e .
```

This installs the `syntheos` console command, along with the pinned
dependencies declared in `pyproject.toml`.

Additionally, ensure that the [Strix](https://strix.model.in.tum.de/) tool is in the same folder as Syntheos, as it is required for execution (or pass `--strix-bin <path>` / put `strix` on your `PATH`).

## Usage

To check the realizability of an LTL specification, activate the virtual environment, then run:

```sh
syntheos --yaml <yaml_file>
```

(equivalently, without installing the package: `python3 syntheos.py --yaml <yaml_file>`, run from the repository root)

Remember to activate the virtual environment with:

```sh
 source .venv/bin/activate
```

when you start a new session.

### YAML File Format
The YAML file should contain:
- `property`: The LTLt specification, where the z3 expressions are enclosed in square brackets.
- `variables`: A list of variables, each specifying its `name`, `type`, and `owner` (either `system` or `environment`).

#### Example YAML File
```yaml
property: "XXG([x>y(y(x))])"
variables:
  - name: "x"
    type: "Int"
    owner: "system"
```

### Example Command
Given a YAML file `spec.yaml`:

```sh
syntheos --yaml spec.yaml
```

Will check the realizability of the specificaiton in `spec.yaml`.
If the `--yaml` flag is not provided, the specification will be read from standard input in YAML format.

You can provide a filename to save the mealy machine in case the specification is realizable with the flag `--save-mealy` and a filename. The output file will also be a YAML.

```sh
syntheos --save-mealy controller.yaml --yaml spec.yaml
```

## Dependencies
- Python 3.13
- Strix (must be placed in the same folder as Syntheos)

# Running with Docker (using Podman)
You can build and run a Docker image of Syntheos using Podman:

## Build the image
Build the image with tag `syntheos` using:
```bash
podman build --platform linux/amd64 -t syntheos .
```

## Run with input from stdin
You can run the image and provide the content of a YAML specification file via standard input:
```bash
podman run --platform linux/amd64 -i syntheos < spec.yaml
```

# Running a shield from the controller
The runtime shield that interprets a mealy machine saved with `--save-mealy controller.yaml` has moved out into its own standalone package - see [shield/](shield/).

# Running the test suite

```sh
python3 -m pip install -e ".[dev]"
python3 -m pytest
```

The unit tests (`tests/unit/`) don't need Strix. The regression suite
(`tests/integration/`) replays a fixed set of specifications through the real
Strix backend and checks the realizability verdict against a recorded
baseline (`tests/golden/baseline.json`); it's automatically skipped if the
`strix` binary isn't present, and takes a few minutes since it runs ~60 full
CEGAR loops.

# Type checking

The `syntheos` package (not `tests/`) is fully type-annotated and checked
with mypy:

```sh
python3 -m pip install -e ".[dev]"
python3 -m mypy
```

z3, ply and sympy ship no type stubs; `syntheos/z3_support.py` is the one
module that imports z3 names directly (everything else reaches Z3 through
`mnz3.X`), and z3/ply/sympy are configured as `ignore_missing_imports` in
`pyproject.toml` so the rest of the codebase can still be held to
`disallow_untyped_defs`.

# Linting and formatting

[Ruff](https://docs.astral.sh/ruff/) covers both linting (replacing
flake8/isort/pyupgrade/flake8-bugbear/flake8-comprehensions) and formatting
(replacing Black):

```sh
python3 -m pip install -e ".[dev]"
python3 -m ruff check .      # lint
python3 -m ruff format .     # format
```

Ruff also enforces modern syntax (pyupgrade), including `X | None`/`X | Y`
union syntax over `Optional[X]`/`Union[X, Y]`.

Config lives in `pyproject.toml`. Two pyupgrade rules (UP007, UP045) are
disabled because this codebase spells out `Optional[X]`/`Union[X, Y]` rather
than `X | None`/`X | Y`.
