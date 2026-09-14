# Standard-library reuse audit (Lean v4.32.0)

The standalone foundations were compared with the sources installed by the
repository's pinned Lean toolchain (`leanprover/lean4:v4.32.0`). The audit covers
`Loom/Order`, `Loom/Control`, `Loom/Util`, and the control helpers in
`Loom/MonadUtil.lean`. The mathlib adapter was updated to match.

## Replacements

| Loom interface | Standard implementation now reused |
| --- | --- |
| `Preorder` reflexivity and transitivity | Inherits `Std.IsPreorder` with an explicit assertion relation |
| `PartialOrder` antisymmetry | Inherits `Std.IsPartialOrder`, sharing the preorder parent |
| `Lattice` meet and join operations | Inherits `Min` and `Max`; `inf`/`sup` remain accessors |
| Six lattice bound axioms | Inherits `Std.LawfulOrderInf` and `Std.LawfulOrderSup` |
| Basic meet/join bound lemmas | Calls `Std.le_min_iff`, `Std.max_le_iff`, `Std.min_le_left`, `Std.min_le_right`, `Std.left_le_max`, and `Std.right_le_max` |
| `LogMonoid` associativity and identity laws | Stores `Std.Associative` and `Std.LawfulIdentity` instances |
| List log laws | Reuses the instances for list append from `Init.Data.List.Basic` |
| `Loom.List.flatMap_congr` | Uses `List.map_congr_left` and `congrArg List.flatten`, removing the custom induction |
| `Loom.Meta.getMainTarget` | Calls `Lean.Elab.Tactic.getMainTarget`, then cleans annotations |

The small Loom wrappers keep the existing theorem names and implicit proof
arguments. They do not redeclare the replaced laws. The standard lattice laws
are equivalent to the old six bound axioms under reflexivity and transitivity:
`a ≤ b ⊓ c ↔ a ≤ b ∧ a ≤ c` and its join dual. Neither totality nor
commutativity of log accumulation has been added.

Primary source files in the pinned toolchain:

- `Init/Data/Order/Classes.lean` and `Init/Data/Order/Lemmas.lean`
- `Init/Core.lean` (`Std.Associative`, `Std.LawfulIdentity`)
- `Init/Data/List/Basic.lean` and `Init/Data/List/Lemmas.lean`
- `Lean/Elab/Tactic/Basic.lean`

## Why some Loom code remains

- **Assertion operation selection.** `Loom.Order.LE` intentionally keeps the
  assertion relation separate from the ambient Lean/mathlib `LE`. A client can
  have different relations on the same type. Standard law instances receive
  the assertion relation explicitly. The inherited `Min`/`Max` projections are
  not registered as global instances, so importing Loom cannot replace a
  client's numeric or mathlib operations. The notation selector supports the
  familiar scoped symbols and ordinary numeric comparisons.
- **General lattices and Boolean algebras.** The pinned standard library has
  no matching bundled Boolean algebra with the explicit operations used by
  Loom. Many standard min/max results require a linear order or that the
  result is one operand (`LawfulOrderMin`/`LawfulOrderMax`); these are stronger
  than general meet/join laws. Loom retains the general lattice proofs where
  no equivalent standard theorem applies.
- **Complete lattices.** `Lean.Order.CompleteLattice` in
  `Init/Internal/Order/Basic.lean` stores existence of suprema and selects an
  operation with `Classical.choose`. `Std.Internal.Do.Order` builds on that
  hierarchy. These are not replacements preserving Loom's explicit bound
  operations and their definitional reductions. The computational
  `Lean.Order.CCPO` relation also remains independent of assertion entailment.
  Some standard indexed-bound helpers accept only `Type` indices, while Loom
  supports arbitrary `Sort` indices, including propositions.
- **Logs.** `Lean.Grind.AddCommMonoid` in `Init/Grind/Module/Basic.lean` requires
  commutativity. Ordered event lists do not satisfy it. The pinned library has
  no general bundled noncommutative monoid counterpart; `LogMonoid` remains a
  bundle of selected operations and the standard operation-law instances.
- **Continuation and writer transformers.** No corresponding `ContT` or
  `WriterT` was found in the pinned `Init`, `Std`, or `Lean` sources. Their
  implementations and lawfulness proofs remain. Existing `ReaderT`, `StateT`,
  `ExceptT`, `Id`, and monad-lift law classes already come from Lean.
- **Divergence and persistent logs.** `DivM` and `PeDivM` are Loom's preexisting
  computation types. Although `Option` has a similar sum shape to `DivM`, it is
  a different public inductive type; replacing it changes constructor,
  recursor, and computational-order APIs. `PeDivM` retains logs on divergence,
  unlike the ordinary writer-over-divergence composition. Their definitions
  remain, with log law proofs now using the standard laws.
- **Extraction-specific metaprogramming.** `getMainTarget` still removes
  annotations without normalizing source lets. `setAppArg` retains its
  zero-based, out-of-bounds-no-op contract; `Lean.Expr.updateApp!` only updates
  one application node and does not implement that contract. The custom
  application traversal is still needed.
- **Predicate transformers and candidate enumeration.** Loom's `Cont.inv`,
  monotone `W`, and ordered candidate providers express its semantics; there
  is no matching standard implementation. Existing list and monad primitives
  continue to use Lean directly.

## Constructor migration

Ordinary uses of `le_trans`, `le_antisymm`, `inf`, `sup`, lattice bound lemmas,
log lemmas, and scoped mathematical notation retain their call syntax.
Implementations of model instances use the standard fields:

- `le_trans a b c` and `le_antisymm a b` take explicit element arguments,
  matching `Std`. Existing standard law instances can instead be supplied via
  `toIsPreorder` / `toIsPartialOrder`.
- Lattice constructors use `min`, `max`, `le_min_iff`, and `max_le_iff`, or
  supply the corresponding standard parent instances directly.
- Log constructors supply `toAssociative` and `toLawfulIdentity` instead of
  three individual law fields. The public `append_assoc`, `empty_append`, and
  `append_empty` lemmas remain available.

`LoomTest.Order` and `LoomTest.Control` construct models directly from standard
instances and check that Loom exposes the matching standard laws. The existing
suite also covers a non-Boolean complete lattice, a nonreflexive bounded
relation, independent universes, ordered logs, divergence, and extraction.
The optional mathlib tests check operation preservation and coexistence of
different assertion and ambient orders.

## Validation

The cleanup passes `lake test`, `python3 scripts/check_foundations.py` (external
package directories excluded), `lake -d integrations/mathlib test`, and
`lake -d tests/native exe smoke`. The compiled dependency audit finds 1,619
Loom declarations, zero imported Mathlib modules, and zero distinct Mathlib
references; its axiom and unfinished-proof checks also pass.
