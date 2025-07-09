import Aesop
import Batteries.Tactic.PermuteGoals
import Batteries.Tactic.Basic

def Decidable.Nat.decidableBallLT' {p : Nat → Prop} (n : Nat)
  [∀ i, Decidable (p i)] :
  ((∀ i, i < n → p i) ↔ (∀ i, p i)) → Decidable (∀ i, p i) := by
  intro h ; rw [← h] ; infer_instance

open Lean Meta Macro Parser Tactic in
def deriveDecidableNatUpperBound (tms : List <| TSyntax `term)
  : MacroM (TSyntax `Lean.Parser.Tactic.tacticSeq) := do
  match tms with
  | [] => `(Lean.Parser.Tactic.tacticSeq| (infer_instance) )
  | tm :: tms' =>
    let res ← deriveDecidableNatUpperBound tms'
    let h := mkIdent `h
    `(Lean.Parser.Tactic.tacticSeq|
      refine @$(mkIdent ``Decidable.Nat.decidableBallLT') _ ($tm) ?_ ?_
      on_goal 1=> intro _
      on_goal 1=>
        $res
      constructor
      next => (intro $h:ident ; intros ; apply $h:ident <;> (try split_ands) <;> (solve
          | omega
          | aesop))
      next => aesop)

macro "decidable_by_nat_upperbound" "[" tms:term,* "]" : term => do
  let res ← deriveDecidableNatUpperBound tms.getElems.toList
  `(term| by $res)
