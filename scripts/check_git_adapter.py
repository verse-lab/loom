"""Resolve and build a real Git consumer of the nested integration package.

Run from a committed checkout. The Git remote is local so this also works before
publishing; mathlib downloads/builds use normal Lake resolution and caching.
"""
import json
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
    # Use explicit path requirements for cached external dependencies. Never
    # symlink whole Git package directories: Lake can replace their contents.
    # LoomMathlib and its relative root Loom always come from the fresh clone.
    manifest = root / "integrations/mathlib/lake-manifest.json"
    existing = root / "integrations/mathlib/.lake/packages"
    for entry in json.loads(manifest.read_text())["packages"]:
        name = entry["name"]
        cached = existing / name
        if name in ("Loom", "LoomMathlib") or not cached.is_dir():
            continue
        actual = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=cached, text=True).strip()
        if actual != entry.get("rev"):
            raise RuntimeError(f"Cached {name} does not match integration manifest")
        with (consumer / "lakefile.lean").open("a") as config:
            config.write(f'\nrequire {name} from {json.dumps(str(cached.resolve()))}\n')
    env = dict(os.environ, MATHLIB_NO_CACHE_ON_UPDATE="1")
    subprocess.run(["lake", "update"], cwd=consumer, env=env, check=True)
    subprocess.run(["lake", "build"], cwd=consumer, env=env, check=True)
    print(f"Git adapter consumer passed at {revision}")
