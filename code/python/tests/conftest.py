"""Test configuration: make ``langlandscape`` importable without installation."""

import os
import pathlib
import sys

os.environ["OMP_NUM_THREADS"] = "1"

_PYTHON_DIR = str(pathlib.Path(__file__).resolve().parent.parent)
if _PYTHON_DIR not in sys.path:
    sys.path.insert(0, _PYTHON_DIR)
