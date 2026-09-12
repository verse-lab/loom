# Loom for Veil

This checkout contains the standalone Loom core for
[Veil](https://github.com/verse-lab/veil), on Lean 4.32.0. It provides monad
algebras, weakest-precondition semantics, nondeterministic computations, and
extraction to executable computations.

The full Loom framework and its Cashmere and Velvet case studies are available
on the [`master` branch](https://github.com/verse-lab/loom/tree/master).

## Using Loom

For local development, add this dependency to your `lakefile.lean`, adjusting
the path to this checkout:

```lean
require Loom from "../loom"
```

For Git consumption after publication, require a revision containing the
standalone migration. The older `v4.32.0-for-veil` revision may still depend
on mathlib.

Veil uses this entry point:

```lean
import Loom.MonadAlgebras.NonDetT'.ExtractList
```

`import Loom` exports the same core. The `Loom` library covers the root module
and all its submodules. CI checks the static library and a native consumer
executable with module precompilation enabled.

Extraction accepts `MultiExtractor.Candidates` and `PartialCandidates` supplied
by the caller. Veil already supplies these through its `Enumeration` interface.
The former automatic `FinEnum` fallback now lives in the separate
`integrations/mathlib` package; clients relying on it must add that package and
`import LoomMathlib.Candidates`. See its README for local and Git dependency setup.

Persistent logs now require `Loom.LogMonoid κ`; lists have a built-in instance.
Generic clients with a mathlib `Monoid κ` can explicitly use
`LoomMathlib.logMonoidOfMonoid κ`. Writer extraction now targets `Loom.WriterT`;
the integration package supplies conversions for mathlib writer computations.

## Build

Install [Lean via elan](https://github.com/leanprover/elan), then run:

```bash
lake build
lake build Loom:static
lake test
python3 scripts/check_foundations.py
```

The toolchain is pinned in `lean-toolchain`. The root package has no external
Lake dependencies and does not download or require external SMT solvers.

All Loom library modules, including generic algebras, WP/WLP, and extraction,
use Loom's own control and assertion interfaces. Generic complete lattices and
Boolean algebras remain supported, including proposition, dependent-function,
and continuation instances. Computational fixed points still use `Lean.Order`.

Open `Loom.Order` to use its classes and scoped assertion notation: `⊑ₗ`, `⊒ₗ`,
`⊤ₗ`, `⊥ₗ`, `⊓ₗ`, `⊔ₗ`, `⨅ₗ`, `⨆ₗ`, `⇨ₗ`, and `ᶜₗ`. In files also using
mathlib, prefer `open scoped Loom.Order` and qualified class/operation names.
`⌜p⌝` uses `Loom.Order.embed`; continuations use `Loom.Cont`/`Loom.ContT`.
Existing consumers that import mathlib themselves must require it directly;
Veil's companion migration and full downstream validation are in progress.

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
- `Loom/Order/`: standalone assertion order, lattices, Boolean laws, and models.
- `Loom/MonadAlgebras/Defs.lean` and `Instances/`: monad algebras and instances
  for the supported effects.
- `Loom/MonadAlgebras/WP/`: weakest-precondition semantics, shared attributes,
  and simplification lemmas.
- `Loom/MonadAlgebras/NonDetT'/`: nondeterministic computations and extraction
  to executable computations, including the extraction tactics used by Veil.
