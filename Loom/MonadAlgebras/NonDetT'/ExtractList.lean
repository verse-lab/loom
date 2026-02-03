import Loom.MonadAlgebras.NonDetT'.ExtractListCore
import Mathlib.Lean.Elab.Tactic.Basic

namespace MultiExtractor

section

open Lean.Order

-- the problem is: how to construct the target monad,
-- **based on the structure of the original `NonDetT m α`**?
-- this dependency cannot be skipped in any way; otherwise we cannot
-- obtain any guarantee.

variable
  (κ : Type q)
  (m : Type u → Type v) (m' : Type u → Type w)
  [inst1 : Monad m']
  [inst2 : MonadFlatMapGo m m']
  [inst3 : MonadFlatMap' m']
  [inst4 : MonadPersistentLog κ m']
  {findable : {τ : Type u} → (τ → Prop) → Type u}
  (findOf : ∀ {τ : Type u} (p : τ → Prop), ExtCandidates findable κ p → Unit → List τ)

abbrev findOfCandidates : ∀ {τ : Type u} (p : τ → Prop), ExtCandidates Candidates κ p → Unit → List τ :=
  (fun p (ec : ExtCandidates Candidates κ p) => ec.core.find)

abbrev findOfPartialCandidates : ∀ {τ : Type u} (p : τ → Prop), ExtCandidates PartialCandidates κ p → Unit → List τ :=
  (fun p (ec : ExtCandidates PartialCandidates κ p) => ec.core.find)

-- TODO `Prop` or `Type _`?
inductive ExtractConstraint : {α : Type u} → (s : NonDetT m α) → m' α → Prop where
  | pure {α : Type u} {x : α} :
    ExtractConstraint (NonDetT.pure x) (inst1.pure x)
  | vis {α β : Type u} (x : m β) (f : β → NonDetT m α) (f' : β → m' α) :
    (∀ y, ExtractConstraint (f y) (f' y)) →
    ExtractConstraint (NonDetT.vis x f) (inst1.bind (inst2.go x) f')
  | pickCont {α : Type u} (τ : Type u) (p : τ → Prop) (f : τ → NonDetT m α) (f' : τ → m' α)
    [instec : ExtCandidates findable κ p] :
    (∀ y, ExtractConstraint (f y) (f' y)) →
    ExtractConstraint (NonDetT.pickCont τ p f)
      (inst3.op (findOf p instec () |>.map (fun x => inst1.bind
        (inst4.log (ExtCandidates.rep findable p (self := instec) x))
        (fun _ => f' x))))
  -- NOTE: without `.{u+1}`, some weird universe level will pop up
  -- NOTE: due to unknown reason, using this instead of `.assume` might cause
  -- unification failure in some cases
  | assumeCont {α : Type u} (p : PUnit.{u+1} → Prop) (f : PUnit.{u+1} → NonDetT m α) (f' : PUnit.{u+1} → m' α)
    [Decidable (p .unit)] :
    (ExtractConstraint (f .unit) (f' .unit)) →
    ExtractConstraint (NonDetT.pickCont PUnit p f)
      (if p .unit then f' .unit else inst3.op [])

/-- A "boxed" version of `ExtractConstraint`, to carry both the extracted
value and the proof that it satisfies the constraint. Used in making
extraction compositional. -/
structure ConstrainedExtractResult {α : Type u} (s : NonDetT m α) where
  val : m' α
  proof : ExtractConstraint κ m m' findOf s val

def ConstrainedExtractResult.pure {α : Type u} (x : α) :
  ConstrainedExtractResult κ m m' findOf (pure x) where
  val := inst1.pure x
  proof := ExtractConstraint.pure

def ExtractConstraint.toConstrainedExtractResult {α : Type u} {s : NonDetT m α} {s' : m' α}
  (h : ExtractConstraint κ m m' findOf s s') : ConstrainedExtractResult κ m m' findOf s := ⟨s', h⟩

open Lean Meta Elab Tactic in
/-- Try all `Decidable` instances in the context to find one to apply to
close the goal. Dedicated to be used by `ConstrainedExtractResult.assume`. -/
scoped elab "find_local_decidable_and_apply" : tactic => do
  for hyp in ← getLCtx do
    if hyp.isImplementationDetail then
      continue
    let ty ← instantiateMVars hyp.type
    if ty.getForallBody.getAppFn'.isConstOf ``Decidable then
      try
        evalTactic (← `(tactic| solve | apply $(mkIdent hyp.userName)))
        return
      catch _ =>
        pure ()
  throwError "no applicable Decidable instance found in the context"

def ConstrainedExtractResult.assume (p : Prop) [decp : Decidable p] :
  ConstrainedExtractResult κ m m' findOf (MonadNonDet.assume (m := NonDetT m) p) where
  val := (if p then inst1.pure .unit else inst3.op [])
  proof := by apply ExtractConstraint.assumeCont ; constructor

def ConstrainedExtractResult.pickList (p : τ → Prop) [instec : ExtCandidates findable κ p] :
  ConstrainedExtractResult κ m m' findOf (MonadNonDet.pickSuchThat (m := NonDetT m) τ p) where
  val := (inst3.op (findOf p instec () |>.map (fun x => inst1.bind
      (inst4.log (ExtCandidates.rep findable p (self := instec) x))
      (fun _ => inst1.pure x))))
  proof := by apply ExtractConstraint.pickCont ; intros ; constructor

def ConstrainedExtractResult.liftM [LawfulMonad m'] (x : m α) :
  ConstrainedExtractResult κ m m' findOf (liftM (n := NonDetT m) x) where
  val := (inst2.go x)
  proof := by
    dsimp [_root_.liftM, monadLift, MonadLift.monadLift]
    rw [← bind_pure (MonadFlatMapGo.go x)]
    apply ExtractConstraint.vis ; intros ; constructor

def ConstrainedExtractResult.pick [instec : ExtCandidates findable κ (fun (_ : τ) => True)] :
  ConstrainedExtractResult κ m m' findOf (MonadNonDet.pick (m := NonDetT m) τ) where
  val := (inst3.op (findOf (fun _ => True) instec () |>.map (fun x => inst1.bind
      (inst4.log (ExtCandidates.rep findable (fun _ => True) (self := instec) x))
      (fun _ => inst1.pure x))))
  proof := by apply ExtractConstraint.pickCont ; intros ; constructor

def ConstrainedExtractResult.ite {α : Type u} (p : Prop)
  (dec : Decidable p)   -- disallow synthesizing
  {s1 : NonDetT m α} {s2 : NonDetT m α}
  (h1 : ConstrainedExtractResult κ m m' findOf s1)
  (h2 : ConstrainedExtractResult κ m m' findOf s2) :
  ConstrainedExtractResult κ m m' findOf (@_root_.ite _ p dec s1 s2) where
  val := (@_root_.ite _ p dec h1.val h2.val)
  proof := by split ; exact h1.proof ; exact h2.proof

-- TODO remove this repetition
theorem ExtractConstraint.bind
  [LawfulMonad m']
  [MonadFlatMap'BindDistributive m']
  {α β : Type u} {s : NonDetT m α} {s' : m' α}
  {f : α → NonDetT m β} {f' : α → m' β}
  (hs : ExtractConstraint κ m m' findOf s s')
  (hf : ∀ x, ExtractConstraint κ m m' findOf (f x) (f' x)) :
  ExtractConstraint κ m m' findOf (s >>= f) (inst1.bind s' f') := by
  induction hs generalizing hf with
  | @pure x => simp [Bind.bind, NonDetT.bind] ; exact hf x
  | @vis β x g g' h ih =>
    simp [Bind.bind, NonDetT.bind] ; constructor
    intro y ; apply ih ; assumption
  | @pickCont τ p g g' extcd h ih =>
    simp [Bind.bind, NonDetT.bind]
    rw [← MonadFlatMap'BindDistributive.bind_distrib, List.map_map] ; simp +unfoldPartialApp [Function.comp]
    apply ExtractConstraint.pickCont
    intros ; apply ih ; assumption
  | @assumeCont p g g' _ h ih =>
    simp [Bind.bind, NonDetT.bind]
    have eq : ((if p PUnit.unit then g' PUnit.unit else MonadFlatMap'.op []) >>= f') =
      ((if p PUnit.unit then g' PUnit.unit >>= f' else MonadFlatMap'.op [])) := by
      split <;> try rfl
      rw [← MonadFlatMap'BindDistributive.bind_distrib] ; rfl
    rw [eq] ; clear eq
    -- some very weird unification failure happens here, so need to provide arguments explicitly
    apply ExtractConstraint.assumeCont (p := p) (f' := (fun _ => g' PUnit.unit >>= f'))
    apply ih ; assumption

def ConstrainedExtractResult.bind
  [LawfulMonad m']
  [MonadFlatMap'BindDistributive m']
  {α β : Type u} {s : NonDetT m α}
  {f : α → NonDetT m β}
  (hs : ConstrainedExtractResult κ m m' findOf s)
  (hf : ∀ x, ConstrainedExtractResult κ m m' findOf (f x)) :
  ConstrainedExtractResult κ m m' findOf (s >>= f) where
  val := (inst1.bind hs.val (hf · |>.val))
  proof := by
    apply ExtractConstraint.bind
    · exact hs.proof
    · intro x ; exact (hf x).proof

def ConstrainedExtractResult.filterAuxM
  (κ : Type q)
  -- NOTE: `Bool` has universe level `1`, so need to take care of the levels of `m` and `m'` here
  (m : Type → Type v) (m' : Type → Type w)
  [inst1 : Monad m']
  [inst2 : MonadFlatMapGo m m']
  [inst3 : MonadFlatMap' m']
  [inst4 : MonadPersistentLog κ m']
  {findable : {τ : Type} → (τ → Prop) → Type}
  (findOf : ∀ {τ : Type} (p : τ → Prop), ExtCandidates findable κ p → Unit → List τ)
  [LawfulMonad m']
  [MonadFlatMap'BindDistributive m']
  {α : Type _}
  {s : α → NonDetT m Bool}
  {l l' : List α}
  (h : ∀ a : α, ConstrainedExtractResult κ m m' findOf (s a)) :
  ConstrainedExtractResult κ m m' findOf (l.filterAuxM s l') where
  val := (l.filterAuxM (fun a => h a |>.val) l')
  proof := by
    induction l generalizing l' with
    | nil => dsimp ; constructor
    | cons x l ih =>
      apply ExtractConstraint.bind
      · apply (h x).proof
      · rintro ⟨_ | _⟩ <;> dsimp <;> apply ih

variable
  [Monad m]
  [CompleteBooleanAlgebra l]
  [MAlgOrdered m l]
  [LawfulMonad m]
  [MAlgOrdered m' l]
  [LawfulMonad m']
  [LawfulMonadPersistentLog κ m' l]
  {α : Type u} (s : NonDetT m α) (s' : m' α)
  (h : ExtractConstraint κ m m' findOf s s')
  (post : α → l)

open AngelicChoice

-- the proofs are taken from `Loom.MonadAlgebras.NonDetT'.ExtractList`

namespace AngelicChoice

include h

theorem extract_list_refines_wp
  [instl : LawfulMonadFlatMapGo m m' l GE.ge]
  [instl2 : LawfulMonadFlatMapSup m' l GE.ge]
  (findOf_sound : ∀ {τ : Type u} (p : τ → Prop) (ec : ExtCandidates findable κ p) x,
    x ∈ findOf p ec () → p x) :
  wp s' post ≤ wp s post := by
  induction h with
  | @pure x => simp [wp_pure]
  | @vis β x f f' h ih =>
    simp [NonDetT.wp_vis, wp_bind]
    have tmp := instl.go_sound _ x
    simp only [ge_iff_le] at tmp
    trans ; apply tmp ; apply wp_cons ; aesop (add norm inf_comm)
  | @pickCont τ p f f' extcd h ih =>
    simp [NonDetT.wp_pickCont]
    rename_i extcd
    specialize findOf_sound p extcd
    generalize (findOf p extcd ()) = lis at findOf_sound ⊢
    have tmp := @instl2.sound
    simp only [ge_iff_le] at tmp
    trans ; apply tmp ; rw [iSup_list_map] ; simp only [wp_bind, LawfulMonadPersistentLog.log_sound]
    simp
    intro a hin ; trans ; apply ih
    apply le_iSup_of_le a ; simp [findOf_sound _ hin]
  | @assumeCont p f f' _ h ih =>
    simp [NonDetT.wp_pickCont]
    split_ifs with h
    · apply le_iSup_of_le .unit ; simp [h] ; apply ih
    · have tmp := @instl2.sound α [] post
      simp [ge_iff_le] at tmp
      rw [tmp] ; simp

theorem wp_refines_extract_list
  [instl : LawfulMonadFlatMapGo m m' l LE.le]
  [instl2 : LawfulMonadFlatMapSup m' l LE.le]
  (findOf_complete : ∀ {τ : Type u} (p : τ → Prop) (ec : ExtCandidates findable κ p) x,
    p x → x ∈ findOf p ec ()) :
  wp s post ≤ wp s' post := by
  induction h with
  | @pure x => simp [wp_pure]
  | @vis β x f f' h ih =>
    simp [NonDetT.wp_vis, wp_bind]
    have tmp := instl.go_sound _ x
    trans ; (on_goal 2=> apply tmp) ; apply wp_cons ; aesop (add norm inf_comm)
  | @pickCont τ p f f' extcd h ih =>
    simp only [NonDetT.wp_pickCont]
    specialize findOf_complete p extcd
    generalize (findOf p extcd ()) = lis at findOf_complete ⊢
    have tmp := @instl2.sound
    trans ; (on_goal 2=> apply tmp) ; rw [iSup_list_map] ; simp only [wp_bind, LawfulMonadPersistentLog.log_sound]
    simp
    intro a hin ; trans ; apply ih
    apply le_iSup_of_le a ; simp [findOf_complete, hin]
  | @assumeCont p f f' _ h ih =>
    simp [NonDetT.wp_pickCont]
    rintro ⟨⟩ hp ; simp [hp] ; apply ih

omit findOf h in
theorem extract_list_eq_wp
  [instl : LawfulMonadFlatMapGo m m' l Eq]
  [instl2 : LawfulMonadFlatMapSup m' l Eq]
  (h : ExtractConstraint κ m m' (findOfCandidates κ) s s') :
  wp s post = wp s' post := by
  apply le_antisymm
  · apply wp_refines_extract_list κ <;> try assumption
    introv ; rw [Candidates.find_iff (self := ec.core)] ; exact id
  · apply extract_list_refines_wp κ <;> try assumption
    introv ; rw [Candidates.find_iff (self := ec.core)] ; exact id

end AngelicChoice

section ExtractionTactic

open Lean Meta Elab

-- NOTE: The following reuses some of the Loom infrastructure

inductive ExtractAttr.EntryKind where
  /-- Given in the form of a `ExtractConstraint` proof. -/
  | proof
  /-- Given in the form of a `ConstrainedExtractResult` structure. -/
  | struct
deriving Inhabited, BEq

structure ExtractAttr.Entry where
  kind : ExtractAttr.EntryKind
  /-- The declaration name of the theorem or structure. -/
  name : Name
deriving Inhabited, BEq

structure ExtractAttr where
  attr : AttributeImpl
  ext  : DiscrTreeExtension ExtractAttr.Entry
deriving Inhabited

private def recognizeExtractEntry (ty : Expr) : MetaM (Option (Expr × ExtractAttr.EntryKind)) := do
  let (_xs, _bis, body) ← forallMetaTelescope ty
  let fn := body.getAppFn'
  if fn.constName? == ``ConstrainedExtractResult then
    return .some (body.getRevArg!' 0, .struct)
  else if fn.constName? == ``ExtractConstraint then
    return .some (body.getRevArg!' 1, .proof)
  else
    return none

initialize extractAttr : ExtractAttr ← do
  let ext ← mkDiscrTreeExtension `multiextractionMap
  let attrImpl : AttributeImpl := {
    name := `multiextracted
    descr := ""
    add := fun declName stx attrKind => do
      -- TODO: use the attribute kind
      unless attrKind == AttributeKind.global do
        throwError "Invalid attribute 'multiextracted', must be global"
      let env ← getEnv
      -- Ignore some auxiliary definitions (see the comments for attrIgnoreMutRec)
      attrIgnoreAuxDef declName (pure ()) do
        let some constInfo := env.find? declName
          | throwError "Declaration {declName} not found"
        let (key, kind) ← MetaM.run' do
          let ty := constInfo.type
          let some (s, kind) ← recognizeExtractEntry ty
            | throwError "Declaration {declName} does not have a valid type for 'multiextracted' attribute"
          let key ← DiscrTree.mkPath s
          return (key, kind)
        let env := ext.addEntry env ⟨key, ⟨kind, declName⟩⟩
        setEnv env
  }
  registerBuiltinAttribute attrImpl
  pure { attr := attrImpl, ext := ext }

def ExtractAttr.find? (s : ExtractAttr) (e : Expr) : MetaM (Array ExtractAttr.Entry) := do
  (s.ext.getState (← getEnv)).getMatch e

open Tactic in
elab "extract_list_use_extracted" : tactic => withMainContext do
  let goal ← getMainTarget''
  let some (ty, _) ← recognizeExtractEntry goal
    | throwError "Could not recognize the goal as an extraction goal"
  let entries ← extractAttr.find? ty
  for entry in entries do
    try
      match entry.kind with
      | .proof => failure   -- for convenience, just not handle this case
      | .struct =>
        let mv ← getMainGoal
        let mvs ← mv.applyConst entry.name (cfg := { synthAssignedInstances := false })
        replaceMainGoal mvs
      trace[veil.extraction] "Applied extracted result: {entry.name}"
      return
    catch _ =>
      pure ()
  throwError "No applicable extracted result found for the goal"

/-- The fallback case for extraction, where the goal cannot be recognized by
`extract_list_use_extracted`. -/
macro "extract_list_step_fallback" : tactic =>
  `(tactic|
    first
      | eapply $(Lean.mkIdent ``ConstrainedExtractResult.bind)
      | eapply $(Lean.mkIdent ``ConstrainedExtractResult.liftM)
      | eapply $(Lean.mkIdent ``ConstrainedExtractResult.assume) _ _ _ ($(Lean.mkIdent `decp) := by first | find_local_decidable_and_apply | infer_instance)
      | eapply $(Lean.mkIdent ``ConstrainedExtractResult.pickList)
      | eapply $(Lean.mkIdent ``ExtractConstraint.toConstrainedExtractResult) <;> any_goals eapply $(Lean.mkIdent ``ExtractConstraint.vis)
      | eapply $(Lean.mkIdent ``ConstrainedExtractResult.pure)
      | eapply $(Lean.mkIdent ``ExtractConstraint.toConstrainedExtractResult) <;> any_goals eapply $(Lean.mkIdent ``ExtractConstraint.pickCont)
      | eapply $(Lean.mkIdent ``ConstrainedExtractResult.ite)
    )

macro "extract_list_step" : tactic =>
  `(tactic|
    first
      | extract_list_use_extracted
      | extract_list_step_fallback
    )

macro "extract_list_tactic" : tactic =>
  `(tactic| repeat' (intros; extract_list_step <;> try dsimp))

end ExtractionTactic

def NonDetT.extractList {α : Type u} (s : NonDetT m α)
  (h : ConstrainedExtractResult κ m m' (findOfCandidates κ) s := by extract_list_tactic)
  : m' α := h.val

def NonDetT.extractPartialList {α : Type u} (s : NonDetT m α)
  (h : ConstrainedExtractResult κ m m' (findOfPartialCandidates κ) s := by extract_list_tactic)
  : m' α := h.val

end

end MultiExtractor
