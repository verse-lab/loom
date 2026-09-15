# Migrating clients to standalone Loom

The root Lake package now has no external dependencies. Keep any mathlib
imports in your application and add a direct mathlib requirement there; they
can coexist with Loom. The optional `integrations/mathlib` package pins mathlib
v4.32.0 and provides explicit bridges. This is an API migration, not a promise
that proofs unfolding mathlib internals remain source-compatible.

| Previous interface | Standalone interface |
| --- | --- |
| mathlib `Preorder`, `PartialOrder`, `Lattice` in Loom signatures | Lean's `LE`/`Min`/`Max` with `Std.IsPartialOrder` etc. |
| mathlib `CompleteLattice`, `CompleteBooleanAlgebra` in Loom signatures | `Loom.Order.CompleteLattice`, `Loom.Order.CompleteBooleanAlgebra` |
| assertion `⊤`, `⊥`, `⊓`, `⊔` | scoped `⊤`, `⊥`, `⊓`, `⊔` (`≤` is Lean's) |
| assertion `⨅`, `⨆`, `⇨`, complement | scoped `⨅`, `⨆`, `⇨`, `ᶜ` |
| `LE.pure`, `LE.pure_imp`, `LE.pure_intro` | `Loom.Order.embed`, `embed_imp`, `embed_intro` |
| `ContT`, `Cont`, `Cont.inv`, `Cont.monotone` | namespaced `Loom.ContT`, `Loom.Cont`, and their helpers |
| `WriterT`, `WriterT.wp_eq` | `Loom.WriterT`, `Loom.WriterT.wp_eq` |
| `[Monoid κ]` for persistent logs | `[Loom.LogMonoid κ]` |
| automatic `FinEnum` candidates from core Loom | import `LoomMathlib.Candidates` |

`⌜p⌝` needs a `Loom.Order.CompleteLattice`. Open `Loom.Order` (or
`open scoped Loom.Order`) for the notation above.
`DivM`, `PeDivM`, `W`, `wp`, `wlp`, the algebra interfaces, and extraction
interfaces retain their public names. `W.wp_montone` retains its original
spelling. Explicit `PeDivM.{logUniverse, resultUniverse}` applications and its
associated helpers retain the original universe order. `Lean.Order.CCPO` and
its computational relation are unchanged.
Arbitrary choices remain arbitrary; extraction still uses caller-supplied
candidate enumerations and preserves their order and duplicates.

Plain `MAlg` requires no order. Ordered and deterministic algebras accept
non-Boolean complete lattices; WLP and continuation inversion need a complete
Boolean algebra. See [the trade-offs](stdlib-reuse-audit.md#trade-offs-of-using-leans-order-classes)
of building on Lean's order classes.

Loom and mathlib both register `LE`/`Min`/`Max` instances for `Prop` and
functions; they agree definitionally. Loom's `iInf`, `sInf`, `compl`, and
`himp` are distinct from mathlib's, so qualify them in mixed files. Indexed
bounds normalize with `Loom.Order.prop_iInf`, `prop_iSup`, `pi_iInf_apply`,
and `pi_iSup_apply`.

For abstract mathlib models install a bridge explicitly in the relevant scope:

```lean
-- Given [CompleteLattice α]:
letI := LoomMathlib.completeLatticeOfMathlib α
-- Given [Monoid κ]:
letI := LoomMathlib.logMonoidOfMonoid κ
```

The bridge preserves mathlib operations, including indexed bounds. No global
conversion instances are installed. Complete-lattice, complete Boolean, and
log adapters remain explicit. Lists already have a direct log instance.
The adapter supplies `contToLoom`, `contFromLoom`, `writerToLoom`, and
`writerFromLoom`, with round-trip and pure/bind preservation theorems.
