"""The `syntheos-shield` command: read environment/proposed-system plays from
stdin (one JSON `[env_play, sys_play]` pair per line) and print the safe
system response to play instead, one JSON object per line.
"""

import argparse
import json
import sys
from collections import deque

from .. import logging_utils
from ..errors import SyntheosError
from ..hoa import nodes2dot
from .core import Shield, Value, read_mealy


def keep_var(v: str, n: int) -> bool:
    return not v.startswith("FETCH_" * n)


def parse_arguments(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Mealy shield")
    parser.add_argument("--mealy", help="File with Mealy machine", type=str, required=True)
    parser.add_argument("--show-mealy", action="store_true", help="Show mealy machine")
    parser.add_argument("--dbglevel", help="Debug level", type=int, default=0)
    return parser.parse_args(argv)


def process_plays(shield: Shield, max_fetch_depth: int) -> None:
    plays = (json.loads(line) for line in sys.stdin)
    prev_plays: deque[dict[str, Value]] = deque(maxlen=max_fetch_depth)

    for env_play, sys_play in plays:
        fetched_past = {
            ("FETCH_" * (i + 1) + k): v
            for i, kv in enumerate(reversed(prev_plays))
            for k, v in kv.items()
            if keep_var(k, max_fetch_depth)
        }
        full_env = env_play | fetched_past
        model = shield.protect(full_env, sys_play)

        if model is None:
            print("The proposed response was not valid", file=sys.stderr)
            model = shield.protect(full_env, {})

        print(json.dumps(model))
        full_play = env_play | model
        prev_plays.append(full_play)


def main(argv: list[str] | None = None) -> None:
    args = parse_arguments(argv)
    logging_utils.configure_logging(args.dbglevel)
    try:
        shield, max_fetch_depth, nodes = read_mealy(args.mealy)
        if args.show_mealy:
            print("Mealy machine:")
            print(nodes2dot(nodes))
        process_plays(shield, max_fetch_depth)
    except SyntheosError as exc:
        print(f"Error: {exc}", file=sys.stderr)
        raise SystemExit(1) from exc


if __name__ == "__main__":
    main()
