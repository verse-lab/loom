"""Resolve and build a real Git consumer of the nested integration package.

Run from a committed checkout. The Git remote is local so this also works before
publishing; mathlib downloads/builds use normal Lake resolution and caching.
"""
import os
from pathlib import Path
import subprocess
import tempfile

root = Path(__file__).resolve().parent.parent
revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip()
with tempfile.TemporaryDirectory(prefix="loom-git-adapter-") as temp:
    consumer = Path(temp)
    (consumer / "lean-toolchain").write_text((root / "lean-toolchain").read_text())
    (consumer / "lakefile.lean").write_text(f'''import Lake
open Lake DSL
package MixedConsumer
require LoomMathlib from git "{root.as_uri()}" @ "{revision}" / "integrations/mathlib"
@[default_target]
lean_lib Main
''')
    (consumer / "Main.lean").write_text('''import Loom
import LoomMathlib
open scoped Loom.Order
example [FinEnum α] (p : α → Prop) [DecidablePred p] : MultiExtractor.Candidates p := inferInstance
example (p q : Nat → Prop) : (p ≤ q) = (p ⊑ₗ q) := rfl
example (p : Nat → Prop) : wp (pure 7 : Id Nat) p = p 7 := wp_pure ..
''')
    # Reuse already-resolved integration dependencies when available. The adapter
    # and its root Loom are always fresh Git checkouts, never path substitutions.
    cache = consumer / ".lake/packages"
    cache.mkdir(parents=True)
    existing = root / "integrations/mathlib/.lake/packages"
    if existing.exists():
        for child in existing.iterdir():
            if child.is_dir() and child.name not in ("Loom", "LoomMathlib"):
                (cache / child.name).symlink_to(child.resolve(), target_is_directory=True)
    env = dict(os.environ, MATHLIB_NO_CACHE_ON_UPDATE="1")
    subprocess.run(["lake", "update"], cwd=consumer, env=env, check=True)
    subprocess.run(["lake", "build"], cwd=consumer, env=env, check=True)
    print(f"Git adapter consumer passed at {revision}")
