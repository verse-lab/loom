`LoomMathlib` provides optional mathlib integration for Loom.

For local development, add a path dependency to this package in a consumer's
lakefile, adjusting the path to the checkout:

```lean
require LoomMathlib from "../loom/integrations/mathlib"
```

This package requires the root Loom checkout and the pinned mathlib revision.
The root package does not require this integration package. Publication of the
adapter as a Git dependency is a later migration step; the current supported
setup is a local path dependency.

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

`import LoomMathlib.Order` exposes explicit conversions from mathlib preorders,
lattices, complete lattices, Boolean algebras, and complete Boolean algebras.
For example, use `letI := LoomMathlib.completeLatticeOfMathlib α` to apply a
Loom order theorem to an existing mathlib model. All operations are preserved,
including indexed bounds. Use `open scoped Loom.Order` for `⊑ₗ`, `⊓ₗ`, and
`⊔ₗ`; qualify operation names when working with both hierarchies.

`import LoomMathlib` exports all three integration modules. The adapters do
not install global conversion instances.

From the root checkout, run:

```bash
lake -d integrations/mathlib build
lake -d integrations/mathlib test
```

The root Loom semantics still require mathlib during these migration
increments. The new namespaced control types and order hierarchy are standalone
and are not yet substituted into those semantics.
