# Standard-library reuse audit (Lean v4.32.0)

The standalone foundations were compared with the sources installed by the
repository's pinned Lean toolchain (`leanprover/lean4:v4.32.0`). The audit covers
`Loom/Order`, `Loom/Control`, `Loom/Util`, and the control helpers in
`Loom/MonadUtil.lean`. The mathlib adapter was updated to match.

## Replacements

| Loom interface | Standard implementation now reused |
| --- | --- |
| `LE`, `Preorder`, `PartialOrder`, `Lattice`, `OrderTop`, `OrderBot` classes | Removed; Lean's `LE`/`Min`/`Max` with `Std.IsPartialOrder`, `Std.LawfulOrderInf`, `Std.LawfulOrderSup` |
| `le_refl`, `le_trans`, `le_antisymm`, basic meet/join bounds | `Std.le_refl` etc. (re-exported), `Std.le_min_iff`, `Std.min_le_left`, ... |
| `LogMonoid` associativity and identity laws | Stores `Std.Associative` and `Std.LawfulIdentity` instances |
| List log laws | Reuses the instances for list append from `Init.Data.List.Basic` |
| `Loom.List.flatMap_congr` | Uses `List.map_congr_left` and `congrArg List.flatten`, removing the custom induction |
| `Loom.Meta.getMainTarget` | Calls `Lean.Elab.Tactic.getMainTarget`, then cleans annotations |

The standard lattice laws are equivalent to the six bound axioms under
reflexivity and transitivity. Neither totality nor commutativity of log
accumulation has been added.

Primary source files in the pinned toolchain:

- `Init/Data/Order/Classes.lean` and `Init/Data/Order/Lemmas.lean`
- `Init/Core.lean` (`Std.Associative`, `Std.LawfulIdentity`)
- `Init/Data/List/Basic.lean` and `Init/Data/List/Lemmas.lean`
- `Lean/Elab/Tactic/Basic.lean`

## Why some Loom code remains

- **Complete lattices and Boolean algebras.** Lean's order classes have no
  bounds, complement, or implication, and most algebraic `min`/`max` laws
  require a linear order. `Lean.Order.CompleteLattice` (with
  `Std.Internal.Do.Order`) is not used because:
  - its relation is `Lean.Order.PartialOrder.rel` (`⊑`), not `LE`, so `≤` and
    the `Std` laws do not apply;
  - its operations use `Classical.choose`, so `p ⊓ q = (p ∧ q)`,
    `(⊤ : Prop) = True`, and pointwise meets are not `rfl`, which Loom's
    `loomLogicSimp` lemmas and Veil's `dsimp` calls rely on;
  - `iInf`/`iSup` accept only `Type` indices, but `⨅ x ∈ xs` needs `Sort`;
  - it has no complement, which WLP and `Cont.inv` need;
  - `Lean.Order.PartialOrder` is documented as meant only for `partial_fixpoint`,
    `Std.Internal.Do` is internal, and the class already carries the
    computational order (`CCPO`) that Loom uses.

  Its `WPMonad` bounds `wp` of `bind` only by `⊑` and has no nondeterminism,
  WLP, or partial/total correctness, so Loom's algebras are kept.
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

## Trade-offs of using Lean's order classes

An earlier version kept its own `Loom.Order.LE` so that Loom would register no
`LE Prop` or function-order instances alongside mathlib's, because Veil then
imported mathlib. That required a notation selector, scoped `≤`/`≥` at several
priorities, and explicit relations in every `Std` law. Veil's mathlib-free
branch no longer imports mathlib. The two sets of instances also agree
definitionally, and `LoomMathlibTest.Order` checks that each side's lemmas
rewrite terms built with the other's instances. So Loom now uses Lean's
classes directly, and gives up the following:

- A type cannot carry an assertion order different from its ordinary `LE`.
- `⌜p⌝` (`embed`) needs a `CompleteLattice`; it previously accepted any
  relation with top and bottom elements.
- `Cont.inv` and its lemmas need a `CompleteBooleanAlgebra`; there is no
  non-complete Boolean class.
- `MonadOrder` takes `[∀ α, LE (w α)]` directly; `PreOrderFunctor` and its
  preorder laws were removed as unused.
- All `simp`/`congr` lemmas in `Loom/Order`, including the `Std` meet/join
  lemmas, and the `refl` tag on `Std.le_refl`, are scoped: they apply only
  under `open Loom.Order`.

## Constructor migration

`CompleteLattice` instances supply `le`, `min`, `max`, the standard fields
`le_refl`, `le_trans`, `le_antisymm`, `le_min_iff`, `max_le_iff`, and then the
bounds. Log constructors supply `toAssociative` and `toLawfulIdentity`.

## Validation

The cleanup passes `lake test`, `python3 scripts/check_foundations.py` (external
package directories excluded), `lake -d integrations/mathlib test`, and
`lake -d tests/native exe smoke`. The compiled dependency audit finds 1,619
Loom declarations, zero imported Mathlib modules, and zero distinct Mathlib
references; its axiom and unfinished-proof checks also pass.
