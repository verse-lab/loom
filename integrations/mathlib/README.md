`LoomMathlib` provides optional mathlib integration for Loom.

For local development, add a path dependency to this package in a consumer's
lakefile, adjusting the path to the checkout:

```lean
require LoomMathlib from "../loom/integrations/mathlib"
```

This package requires the root Loom checkout and the pinned mathlib revision.
The root package does not require this integration package. The nested package also supports a Git dependency:

```lean
require LoomMathlib from git "https://github.com/verse-lab/loom.git" @
  "<published-revision-containing-this-package>" / "integrations/mathlib"
```

Use a revision containing the standalone migration after it is published.
The relative Loom dependency resolves to the root of the same Git checkout.
`python3 scripts/check_git_adapter.py` exercises this arrangement using the
local Git repository at HEAD, before publication; external dependencies use
the integration package's cache when available.

Clients that previously relied on Loom to supply `Candidates` from `FinEnum`
should import:

```lean
import LoomMathlib.Candidates
```

This restores the automatic instance and preserves `FinEnum.toList` order.
Clients supplying their own candidates, including Veil's `Enumeration`
instances, need no adapter for enumeration.

`import LoomMathlib.Control` exposes explicit conversions between mathlib's and
Loom's continuation and writer types, and `LoomMathlib.logMonoidOfMonoid` for
constructing a Loom logging algebra. These do not install global conversion
instances.

Extraction's persistent-log monad now requires `Loom.LogMonoid` instead of
mathlib's `Monoid`. For generic mathlib log types, opt in explicitly:

```lean
-- Inside a declaration with [Monoid κ]:
letI := LoomMathlib.logMonoidOfMonoid κ
-- PeDivM κ and Loom.WriterT κ m are now available.
```

Lists already have a direct `Loom.LogMonoid` instance. Loom no longer exports
its former global `Monoid (List κ)` instance. Existing mathlib writer clients
can use `writerToLoom` and apply the migrated `Loom.WriterT.wp_eq` theorem.
The root package does not provide algebra instances for mathlib's `WriterT`.

`import LoomMathlib.Order` exposes explicit conversions from mathlib complete
lattices and complete Boolean algebras, e.g.
`letI := LoomMathlib.completeLatticeOfMathlib α`. Loom uses Lean's `LE`, `Min`,
and `Max`, which mathlib shares, so `≤`, `⊓`, and `⊔` are the same operations.

`import LoomMathlib` exports all three integration modules. The adapters do
not install global conversion instances.

From the root checkout, run:

```bash
lake -d integrations/mathlib build
lake -d integrations/mathlib test
```

All root Loom modules, including generic algebras, WP/WLP, and extraction, are
independent of mathlib. This separate adapter package retains its explicit
mathlib requirement.
