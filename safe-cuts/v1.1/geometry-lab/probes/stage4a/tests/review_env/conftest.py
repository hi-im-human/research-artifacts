"""These tests need mpmath and run only in the throwaway review environment (see receipts/repair/review-environment.json).

In any environment without mpmath (such as the maintained .venv) the directory is skipped explicitly rather than
failing at import; nothing is installed to make them run.
"""
import importlib.util

if importlib.util.find_spec("mpmath") is None:
    collect_ignore_glob = ["test_*.py"]
