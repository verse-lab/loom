# Loom for Veil

This branch (`v4.32.0-for-veil`) contains the Loom core used by
[Veil](https://github.com/verse-lab/veil), on Lean 4.32.0. It provides monad
algebras, weakest-precondition semantics, nondeterministic computations, and
extraction to executable computations.

The full Loom framework and its Cashmere and Velvet case studies are available
on the [`master` branch](https://github.com/verse-lab/loom/tree/master).

## Using Loom

Add this dependency to your `lakefile.lean`:

```lean
require Loom from git "https://github.com/verse-lab/loom.git" @ "v4.32.0-for-veil"
```

Veil uses this entry point:

```lean
import Loom.MonadAlgebras.NonDetT'.ExtractList
```

`import Loom` exports the same core. The `Loom` library covers the root module
and all its submodules. CI checks the static library and a native consumer
executable; the migration's module-precompilation check remains outstanding.

Extraction accepts `MultiExtractor.Candidates` and `PartialCandidates` supplied
by the caller. Veil already supplies these through its `Enumeration` interface.
The former automatic `FinEnum` fallback now lives in the separate
`integrations/mathlib` package; clients relying on it must add that package and
`import LoomMathlib.Candidates`. See its README for the local dependency setup.

## Build

Install [Lean via elan](https://github.com/leanprover/elan), then run:

```bash
lake build
lake build Loom:static
lake test
python3 scripts/check_foundations.py
```

The toolchain is pinned in `lean-toolchain`; Mathlib and its dependencies are
pinned in `lake-manifest.json`. Loom does not download or require external SMT
solvers.

Mathlib removal is in progress. The semantics still depend on mathlib's order
hierarchy. The new `Loom.Control.Cont`, `Loom.Control.Log`, and
`Loom.Control.Writer` modules and `Loom.Util.Meta` compile without external
packages; they are the foundations for the subsequent port. The control types
are namespaced and coexist with mathlib's types.

To inspect the compiled dependency graph after a build:

```bash
lake env lean --run scripts/AuditDependencies.lean /tmp/loom-audit
```

This writes the imported module list and a declaration-level TSV inventory.
See the [migration plan](docs/mathlib-removal-plan.md) and
[implementation progress](docs/mathlib-removal-progress.md).

## Source guide

- `Loom/MonadUtil.lean` and `Loom/SpecMonad.lean`: shared monad utilities and
  specification monads.
- `Loom/Control/`: standalone continuation, writer, and logging foundations.
- `Loom/MonadAlgebras/Defs.lean` and `Instances/`: monad algebras and instances
  for the supported effects.
- `Loom/MonadAlgebras/WP/`: weakest-precondition semantics, shared attributes,
  and simplification lemmas.
- `Loom/MonadAlgebras/NonDetT'/`: nondeterministic computations and extraction
  to executable computations, including the extraction tactics used by Veil.
