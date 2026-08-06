"""Exceptions used across the shield.

Library code raises ShieldError instead of printing a traceback and calling
exit() directly, so callers (the CLI entry point) can decide how to report
the failure.
"""


class ShieldError(Exception):
    """Raised for any user-facing failure: bad mealy file, parse error, or an
    internal invariant violation the shield doesn't expect to recover from."""
