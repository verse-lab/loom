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

`import Loom` exports the same core. This branch retains only that entry point
and its supporting modules. There is a single `Loom` library, covering the root
module and all its submodules, including for consumers using
`precompileModules := true`.

## Build

Install [Lean via elan](https://github.com/leanprover/elan), then run:

```bash
lake build
lake build Loom:static
```

The toolchain is pinned in `lean-toolchain`; Mathlib and its dependencies are
pinned in `lake-manifest.json`. Loom does not download or require external SMT
solvers.

## Source guide

- `Loom/MonadUtil.lean` and `Loom/SpecMonad.lean`: shared monad utilities and
  specification monads.
- `Loom/MonadAlgebras/Defs.lean` and `Instances/`: monad algebras and instances
  for the supported effects.
- `Loom/MonadAlgebras/WP/`: weakest-precondition semantics, shared attributes,
  and simplification lemmas.
- `Loom/MonadAlgebras/NonDetT'/`: nondeterministic computations and extraction
  to executable computations, including the extraction tactics used by Veil.
