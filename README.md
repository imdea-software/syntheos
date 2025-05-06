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

Will check the realizability of the specificaiton in `spec.yaml`.
If the `--yaml` flag is not provided, the specification will be read from standard input in YAML format.

You can provide a filename to save the mealy machine in case the specification is realizable with the flag `--save-mealy` and a filename. The output file will also be a YAML.

```sh
python syntheos.py --save-mealy controller.yaml --yaml spec.yaml
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
You can execute a controller that interprets the mealy machine that has been saved with `--save-mealy controller.yaml` with the program `shield.py` in this repository.

```sh
python shield.py --mealy controller.yaml
```
This controller will read lines from stdin, where each line is a list of two elements.

The first element is a dictionary that maps each input variable to a concrete value. This represents the values provided by the environment at a specific time step.

The second element is a dictionary that maps output variables to proposed values determined by the system. This entry can contain only a subset of the system variables, indicating that the rest can be any value that the controller finds suitable.

If the proposed output values do not constitute a valid system response, the shield will provide a safe move to play instead.
