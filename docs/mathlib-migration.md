# Migrating clients to standalone Loom

The root Lake package now has no external dependencies. Keep any mathlib
imports in your application and add a direct mathlib requirement there; they
can coexist with Loom. The optional `integrations/mathlib` package pins mathlib
v4.32.0 and provides explicit bridges. This is an API migration, not a promise
that proofs unfolding mathlib internals remain source-compatible.

| Previous interface | Standalone interface |
| --- | --- |
| mathlib `Preorder`, `CompleteLattice`, `BooleanAlgebra`, etc. in Loom signatures | corresponding `Loom.Order` classes |
| assertion `≤`, `≥`, `⊤`, `⊥`, `⊓`, `⊔` | scoped `≤`, `≥`, `⊤`, `⊥`, `⊓`, `⊔` |
| assertion `⨅`, `⨆`, `⇨`, complement | scoped `⨅`, `⨆`, `⇨`, `ᶜ` |
| `LE.pure`, `LE.pure_imp`, `LE.pure_intro` | `Loom.Order.embed`, `embed_imp`, `embed_intro` |
| `ContT`, `Cont`, `Cont.inv`, `Cont.monotone` | namespaced `Loom.ContT`, `Loom.Cont`, and their helpers |
| `WriterT`, `WriterT.wp_eq` | `Loom.WriterT`, `Loom.WriterT.wp_eq` |
| `[Monoid κ]` for persistent logs | `[Loom.LogMonoid κ]` |
| automatic `FinEnum` candidates from core Loom | import `LoomMathlib.Candidates` |

`⌜p⌝` retains its syntax and its original generality: embedding and its basic
lemmas need only `Loom.Order.LE` with `OrderTop` and `OrderBot`, without
reflexivity or transitivity. Every `Preorder` supplies that bare relation. The optional
adapter provides `leOfMathlib`, `orderTopOfMathlib`, and `orderBotOfMathlib` for
clients with the old bounded-relation assumptions.
The familiar mathematical symbols are retained through `open scoped Loom.Order`.
Within that scope, they select Loom's assertion operations, including when
mathlib is imported. Numerical comparisons retain Lean's ordinary relation;
comparison notation falls back to Lean's `LE` when Loom has no relation for
the type. This does not install global conversions of order operations. In `change` patterns
with otherwise untyped holes, annotate an operand (for example,
`change (_ : Nat) ≤ _`) so Lean can resolve the comparison.
`DivM`, `PeDivM`, `W`, `wp`, `wlp`, the algebra interfaces, and extraction
interfaces retain their public names. `W.wp_montone` retains its original
spelling. Explicit `PeDivM.{logUniverse, resultUniverse}` applications and its
associated helpers retain the original universe order. `Lean.Order.CCPO` and
its computational relation are unchanged.
Arbitrary choices remain arbitrary; extraction still uses caller-supplied
candidate enumerations and preserves their order and duplicates.

Plain `MAlg` requires no order. Ordered and deterministic algebras continue to
accept non-Boolean complete lattices. Continuation inversion needs only a
Boolean algebra. Complete Boolean assumptions remain on the results that
need both completeness and Boolean laws.

In mixed files use `open scoped Loom.Order` and qualified class/lemma names to
avoid name ambiguity with mathlib. To refer to mathlib operations within the
Loom scope, use qualified names such as `_root_.LE.le`, `_root_.Top.top`,
`_root_.Min.min`, and `_root_.iInf`. Outside that scope, mathlib notation is
unchanged. Direct proposition and function instances
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
conversion instances are installed. Complete-lattice, Boolean, and log
adapters remain explicit. Lists already have a direct log instance.
The adapter supplies `contToLoom`, `contFromLoom`, `writerToLoom`, and
`writerFromLoom`, with round-trip and pure/bind preservation theorems.

The standalone bundles now reuse Lean's standard order and operation-law
classes. Custom model constructors should use the standard field names;
see [the standard-library audit](stdlib-reuse-audit.md#constructor-migration)
for the constructor changes and the reasons for the remaining Loom code.
