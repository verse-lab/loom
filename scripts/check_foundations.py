"""Compile standalone foundation tests with only Loom build outputs and Lean.

Run `lake build LoomTest` first. This deliberately excludes every .lake/packages
directory from LEAN_PATH so a transitive external import cannot pass unnoticed.
"""

import os
from pathlib import Path
import subprocess

root = Path(__file__).resolve().parent.parent
env = dict(os.environ, LEAN_PATH=str(root / ".lake/build/lib/lean"))
for source in (
    "LoomTest/Control.lean", "LoomTest/Meta.lean", "LoomTest/Order.lean",
    "LoomTest/MonadUtil.lean", "LoomTest/Algebras.lean", "LoomTest/Extraction.lean",
):
    subprocess.run(["lean", source], cwd=root, env=env, check=True)
    print(f"Standalone check passed: {source}", flush=True)
