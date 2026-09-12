# Migrating clients to standalone Loom

The root Lake package now has no external dependencies. Keep any mathlib
imports in your application and add a direct mathlib requirement there; they
can coexist with Loom. The optional `integrations/mathlib` package pins mathlib
v4.32.0 and provides explicit bridges. This is an API migration, not a promise
that proofs unfolding mathlib internals remain source-compatible.

| Previous interface | Standalone interface |
| --- | --- |
| mathlib `Preorder`, `CompleteLattice`, `BooleanAlgebra`, etc. in Loom signatures | corresponding `Loom.Order` classes |
| assertion `≤`, `≥`, `⊤`, `⊥`, `⊓`, `⊔` | scoped `⊑ₗ`, `⊒ₗ`, `⊤ₗ`, `⊥ₗ`, `⊓ₗ`, `⊔ₗ` |
| assertion `⨅`, `⨆`, `⇨`, complement | scoped `⨅ₗ`, `⨆ₗ`, `⇨ₗ`, `ᶜₗ` |
| `LE.pure`, `LE.pure_imp`, `LE.pure_intro` | `Loom.Order.embed`, `embed_imp`, `embed_intro` |
| `ContT`, `Cont`, `Cont.inv`, `Cont.monotone` | namespaced `Loom.ContT`, `Loom.Cont`, and their helpers |
| `WriterT`, `WriterT.wp_eq` | `Loom.WriterT`, `Loom.WriterT.wp_eq` |
| `[Monoid κ]` for persistent logs | `[Loom.LogMonoid κ]` |
| automatic `FinEnum` candidates from core Loom | import `LoomMathlib.Candidates` |

`⌜p⌝` retains its syntax. Numerical comparisons retain Lean's ordinary `≤`.
`DivM`, `PeDivM`, `W`, `wp`, `wlp`, the algebra interfaces, and extraction
interfaces retain their public names. `W.wp_montone` retains its original
spelling. `Lean.Order.CCPO` and its computational relation are unchanged.
Arbitrary choices remain arbitrary; extraction still uses caller-supplied
candidate enumerations and preserves their order and duplicates.

Plain `MAlg` requires no order. Ordered and deterministic algebras continue to
accept non-Boolean complete lattices. Continuation inversion needs only a
Boolean algebra. Complete Boolean assumptions remain on the results that
need both completeness and Boolean laws.

In mixed files use `open scoped Loom.Order` and qualified class/lemma names to
avoid name ambiguity with mathlib. Direct proposition and function instances
reduce entailment to implication and pointwise entailment; indexed bounds
normalize with `Loom.Order.prop_iInf`, `prop_iSup`, `pi_iInf_apply`, and `pi_iSup_apply`.
Update quotations that refer to old constants as well as ordinary source
references. Proofs unfolding mathlib's `Pi` order instances should instead use
Loom's order lemmas or simplify the concrete proposition/function model.

For abstract mathlib models install a bridge explicitly in the relevant scope:

```lean
-- Given [CompleteLattice α]:
letI := LoomMathlib.completeLatticeOfMathlib α
-- Given [Monoid κ]:
letI := LoomMathlib.logMonoidOfMonoid κ
```

The bridge preserves mathlib operations, including indexed bounds. No global
conversion instances are installed. Lists already have a direct log instance.
The adapter supplies `contToLoom`, `contFromLoom`, `writerToLoom`, and
`writerFromLoom`, with round-trip and pure/bind preservation theorems.
