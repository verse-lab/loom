import Lean

import Loom.MonadAlgebras.WP.Attr
import Loom.MonadAlgebras.WP.DoNames'

open Lean Parser Meta Elab Term Command Tactic

def findSpec (prog : Expr) : TacticM (Array (Ident × Loom.SpecType)) := do
  let specs ← specAttr.find? prog
  let grts := specs.qsort (compare · · |>.isGT) |>.map
    fun ⟨specType, specName, _⟩ => (mkIdent specName, specType)
  if grts.isEmpty then
    throwError s!"no specs found for {prog}"
  return grts

def Lean.MVarId.isWPGenGoal : MVarId → TacticM Bool
| mvarId => do
  let goalType <- mvarId.getType
  let_expr WPGen _m _mInst _α _l _lInst _mPropInst _ := goalType | return false
  return true

def isWPGenGoal : TacticM Bool := do
  (<- getMainGoal).isWPGenGoal

def hideNonWPGenGoals : TacticM Unit := do
  let goals <- getGoals
  let goals' <- goals.filterM (·.isWPGenGoal)
  setGoals goals'

elab "is_not_wpgen_goal" : tactic => do
  if ← isWPGenGoal then
    throwError "is a WPGen goal"
  else
    return

elab "hide_non_wpgen_goals" : tactic => do
  hideNonWPGenGoals

elab "show_all_goals" : tactic => do
  setGoals (← getUnassignedExprMVars).toList
  synthesizeSyntheticMVarsNoPostponing

macro "try_resolve_spec_goals" : tactic => `(tactic| try is_not_wpgen_goal; solve | rfl | solve_by_elim | simp)

def generateWPStep : TacticM (Bool × Expr) := withMainContext do
  let goalType <- getMainTarget
  let_expr WPGen _m _mInst _α _l _lInst _mPropInst x := goalType | throwError "{goalType} is not a WPGen"
  let cs <- findSpec x
  for elem in cs do
    try
      match elem with
      | (spec, .wpgen) =>
        evalTactic $ <- `(tactic| apply $spec)
      | (spec, .triple) =>
        evalTactic $ <- `(tactic|
          eapply $(mkIdent ``WPGen.spec_triple);
          apply $spec)
      return (true, x)
    catch _ => continue
  return (false, x)


elab "wpgen_app" : tactic => do
  let (found, x) ← generateWPStep
  unless found do throwError "no spec found for {x}"

macro "wpgen_step" : tactic => `(tactic| first
  | (wpgen_app <;> intros <;> try_resolve_spec_goals)
  | (intros; split <;> intros)
  )
macro "wpgen_intro" : tactic => `(tactic| (apply WPGen.intro; rotate_right))
macro "wpgen" : tactic => `(tactic| (
  wpgen_intro
  repeat' wpgen_step
  ))
def Lean.Expr.getName (e : Expr) : MetaM Name := do
  match_expr e with
  | Name.mkStr _ n =>
    match n with
    | .lit (.strVal n) => return n.toName
    | _                => throwError "expected a string literal1"
  | _ => throwError "expected a string literal3"


partial def Lean.Expr.getNamesProp (tp : Expr) : MetaM (Option (List Name)) := do
  match_expr tp with
  | WithName _ n₁ => return some [<- n₁.getName]
  | MProdWithNames _ tr n₁ =>
    let n₁ <- n₁.getName
    let some ns <- tr.getNamesProp
      | return none
    return some $ n₁ :: ns
  | _ =>
    return none

def renameOld (n : Name) : TacticM Unit := withMainContext do
  (<- getMainGoal).modifyLCtx fun hyps => Id.run do
    let mut hypsNew := hyps
    for hyp in hyps.decls.toArray.reverse do
      if hyp.isSome then
        let n' := hyp.get!.userName
        if n' == n then
          hypsNew := hyps.renameUserName n' (n'.toString ++ "Old" |>.toName)
    return hypsNew

elab "loom_split" : tactic => do
  let goalType <- getMainTarget
  match_expr goalType with
  | WithName _ _ => throwError "Cannot split on a WithName goal"
  | _ => evalTactic $ <- `(tactic| apply And.intro)


elab "loom_intro" : tactic => withMainContext do
  let goalType <- getMainTarget
  let .forallE _ tp _ _ := goalType.consumeMData
    | evalTactic $ <- `(tactic| fail)
  let some ns <- tp.getNamesProp
    | evalTactic $ <- `(tactic| try unhygienic intro) -- because sometimes it is part of an invariant and unnamed by defualt
  let ns1 ← ns.mapM getUnusedUserName
  let names := ns1 |>.map Lean.mkIdent |>.toArray
  for name in names do renameOld name.getId
  if names.size > 1 then
    evalTactic $ <- `(tactic|
      rintro ⟨$[$names],*⟩; try simp only [MProdWithNames.snd, MProdWithNames.fst])
  else
    if names.size = 0 then
      pure () --just more robust
    else
      let name₀ := names[0]!
      evalTactic $ <- `(tactic| intro $(name₀):ident)

macro "mwp" : tactic => `(tactic| (
  wpgen
  try simp only [loomLogicSimp, loomWpSimp, invariants, List.foldr, WithName.mk', WithName.erase, typeWithName.erase]
  try unfold spec WithName at *
  try unfold spec typeWithName at *
  ))

attribute [spec high, loomWpSimp] WPGen.if
attribute [spec, loomWpSimp] WPGen.bind WPGen.pure WPGen.assert WPGen.forWithInvariant WPGen.map
attribute [loomWpSimp] spec WPGen.spec_triple

@[loomLogicSimp]
lemma leE (l : Type u) [PartialOrder l] (a b : α -> l) : a ≤ b ↔ ∀ x, a x ≤ b x := by
  rfl
@[loomLogicSimp]
lemma lePropE (a b : Prop) : (a ≤ b) = (a → b) := by
  rfl

@[loomLogicSimp]
lemma pureE (l : Type u) [CompleteLattice l] (a : Prop) : (⌜a⌝ : α -> l) = fun _ => ⌜a⌝ := by
  simp [LE.pure]; split <;> rfl

@[loomLogicSimp]
lemma purePropE  : (⌜a⌝ : Prop) = a := by
  simp [LE.pure]

@[loomLogicSimp]
lemma infPropE (a b : Prop) : (a ⊓ b) = (a ∧ b) := by
  rfl

@[loomLogicSimp]
lemma infE (l : Type u) [CompleteLattice l] (a b : α -> l) : (a ⊓ b) = fun x => a x ⊓ b x := by
  rfl

@[loomLogicSimp]
lemma supE (l : Type u) [CompleteLattice l] (a b : α -> l) : (a ⊔ b) = fun x => a x ⊔ b x := by
  rfl

@[loomLogicSimp]
lemma supPropE (a b : Prop) : (a ⊔ b) = (a ∨ b) := by
  rfl

@[loomLogicSimp]
lemma iInfE (l : Type u) [CompleteLattice l] (a : ι -> α -> Prop) : (⨅ i, a i) = fun x => ⨅ i, a i x := by
  ext; simp

@[loomLogicSimp]
lemma iSupE (l : Type u) [CompleteLattice l] (a : ι -> α -> Prop) : (⨆ i, a i) = fun x => ⨆ i, a i x := by
  ext; simp

@[loomLogicSimp]
lemma himpE  (l : Type u) [CompleteBooleanAlgebra l] (a b : α -> l) :
  (a ⇨ b) = fun x => a x ⇨ b x := by rfl

@[loomLogicSimp]
lemma himpPureE (a b : Prop) :
  (a ⇨ b) = (a -> b) := by rfl

@[loomLogicSimp]
lemma topE (l : Type u) [CompleteLattice l] : (⊤ : α -> l) = fun _ => ⊤ := by rfl

@[loomLogicSimp]
lemma topPureE : (⊤ : Prop) = True := by rfl

attribute [loomLogicSimp]
  forall_const
  implies_true and_true true_and
  iInf_Prop_eq
  and_imp
attribute [simp←] Nat.mul_add_one

attribute [loomWpSplit] iInf_inf_eq himp_inf_distrib wp_and wp_iInf
