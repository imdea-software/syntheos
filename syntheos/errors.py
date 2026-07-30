"""Exceptions used across Syntheos.

Library code raises SyntheosError instead of printing a traceback and calling
exit() directly, so callers (the CLI entry points) can decide how to report
the failure.
"""


class SyntheosError(Exception):
    """Raised for any user-facing failure: bad spec, parse error, solver
    failure, or an internal invariant violation the algorithm doesn't expect
    to recover from."""
