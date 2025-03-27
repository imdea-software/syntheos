# Syntheos

Syntheos is a tool for checking the realizability of specifications expressed in Linear Temporal Logic with theories (LTLt). The atomic propositions in the specification are Z3 predicates, which can refer to the previous value of a quantitative variable `x` with `y(x)`.

## Installation

To install Syntheos, clone this repository and install the required dependencies:

```sh
 git clone https://github.com/imdea-software/syntheos.git
 cd syntheos
 python3 -m venv .venv
 source .venv/bin/activate
 python3 -m pip install -r requirements.txt
```

Additionally, ensure that the [Strix](https://strix.model.in.tum.de/) tool is in the same folder as Syntheos, as it is required for execution.

## Usage

To check the realizability of an LTL specification, activate the virtual environment, run the following command:

```sh
python3 syntheos.py --yaml <yaml_file>
```

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
python syntheos.py --yaml spec.yaml
```

## Dependencies
- Python 3.13
- Strix (must be placed in the same folder as Syntheos)
