import Loom.MonadAlgebras.Defs
import Loom.MonadAlgebras.Instances.Basic

abbrev Except.getD {ε α} (default : ε -> α)  : Except ε α -> α
  | Except.ok p => p
  | Except.error e => default e

abbrev Except.bind' {m : Type u -> Type v} {ε α β} [Monad m] : Except ε α -> (α -> ExceptT ε m β) -> ExceptT ε m β :=
  fun x f => bind (m := ExceptT ε m) (pure (f := m) x) f

lemma Except.bind'_bind {m : Type u -> Type v} {ε α β} [Monad m] [LawfulMonad m] (i : m (Except ε α)) (f : α -> ExceptT ε m β) :
  (i >>= fun a => Except.bind' a f) = bind (m := ExceptT ε m) i f := by
  simp [Except.bind', bind, bind_assoc, ExceptT.bind]; rfl

noncomputable
def MAlgExcept (ε : Type u) (df : ε -> Prop) (l : Type u) (m : Type u -> Type v)
  [CompleteLattice l]
  [Monad m] [LawfulMonad m] [inst: MAlgOrdered m l] : MAlgOrdered (ExceptT ε m) l where
  μ := fun e => inst.μ $ Except.getD (⌜df ·⌝) <$> e
  μ_ord_pure := by
    intro l; simp [pure, ExceptT.pure, ExceptT.mk]
    solve_by_elim [MAlgOrdered.μ_ord_pure]
  μ_ord_bind := by
    intros α f g
    simp [Function.comp, Pi.hasLe, Pi.partialOrder, Pi.preorder, inferInstanceAs]; intros le x
    have leM := @inst.μ_ord_bind (Except ε α)
      (fun x => Except.getD (⌜df ·⌝) <$> Except.bind' x f)
      (fun x => Except.getD (⌜df ·⌝) <$> Except.bind' x g)
    simp only [Function.comp, Pi.hasLe, <-map_bind, Except.bind'_bind] at leM
    apply leM; rintro (e | p) <;> simp [Except.bind', ExceptT.instMonad, ExceptT.bind, ExceptT.bindCont]
    apply le

section ExeceptHandler

variable (ε : Type u) (l : Type u) (m : Type u -> Type v) [Monad m] [LawfulMonad m]

class IsHandler {ε : Type*} (handler : outParam (ε -> Prop)) where

set_option linter.unusedVariables false in
noncomputable
instance OfHd {hd : ε -> Prop} [hdInst : IsHandler hd]
  [CompleteLattice l] [inst: MAlgOrdered m l] : MAlgOrdered (ExceptT ε m) l := MAlgExcept ε hd l m


lemma MAlg.lift_ExceptT ε (hd : ε -> Prop) [IsHandler hd] [CompleteLattice l] [inst: MAlgOrdered m l]
   (c : ExceptT ε m α) post :
  MAlg.lift c post = MAlg.lift (m := m) c (fun | .ok x => post x | .error e => ⌜hd e⌝) := by
    simp [MAlg.lift, OfHd, MAlgExcept, Functor.map, ExceptT.map, ExceptT.mk]
    rw [map_eq_pure_bind]; apply MAlgOrdered.bind; ext a; cases a <;> simp [Except.getD]


instance MAlgExceptHdDet (hd : ε -> Prop)
  [CompleteLattice l] [inst: MAlgOrdered m l] [IsHandler hd]
  [inst': MAlgDet m l] : MAlgDet (ExceptT ε m) l where
  angelic := by
    intros α ι c p _
    simp [MAlg.lift, MAlg.μ, MAlgOrdered.μ, Functor.map, ExceptT.map, ExceptT.mk]
    simp [OfHd, MAlgExcept]
    have h := inst'.angelic (α := Except ε α) (c := c)
      (p := fun i e =>
        match e with
        | Except.ok a    => p i a
        | Except.error e => ⌜hd e⌝ )
    simp [MAlg.lift, MAlg.μ] at h
    have h₁ : ∀ p : ι -> α -> l,
      ⨆ i,
      (MAlgOrdered.μ (m := m) (do
        bind (m := m) c fun a =>
        Except.getD (⌜hd ·⌝) <$>
            match a with
            | Except.ok a => pure (Except.ok (p i a))
            | Except.error e => pure (Except.error e))) =
      ⨆ i,
      MAlgOrdered.μ (Functor.map (f := m) (α := Except ε α)
        (fun a =>
          match a with
            | Except.ok a => (p i a)
            | Except.error e => ⌜hd e⌝) c) := by
      intro p; congr; ext i; rw [map_eq_pure_bind]; apply MAlg.bind (m := m); ext a; cases a <;> simp
    (repeat erw [h₁]); clear h₁; apply le_trans'; apply h
    apply le_of_eq;rw [map_eq_pure_bind]; apply MAlg.bind (m := m); ext a; cases a <;> simp
    simp [Except.getD, MAlg.μ, iSup_const]
  demonic := by
    intros α ι c p _
    simp [MAlg.lift, MAlg.μ, MAlgOrdered.μ, Functor.map, ExceptT.map, ExceptT.mk]
    simp [OfHd, MAlgExcept]
    have h := inst'.demonic (α := Except ε α) (c := c)
      (p := fun i e =>
        match e with
        | Except.ok a    => p i a
        | Except.error e => ⌜hd e⌝ )
    simp [MAlg.lift, MAlg.μ] at h
    have h₁ : ∀ p : ι -> α -> l,
      ⨅ i,
      (MAlgOrdered.μ (m := m) (do
        bind (m := m) c fun a =>
        Except.getD (⌜hd ·⌝) <$>
            match a with
            | Except.ok a => pure (Except.ok (p i a))
            | Except.error e => pure (Except.error e))) =
      ⨅ i,
      MAlgOrdered.μ (Functor.map (f := m) (α := Except ε α)
        (fun a =>
          match a with
            | Except.ok a => (p i a)
            | Except.error e => ⌜hd e⌝) c) := by
      intro p; congr; ext i; rw [map_eq_pure_bind]; apply MAlg.bind (m := m); ext a; cases a <;> simp
    (repeat erw [h₁]); clear h₁; apply le_trans; apply h
    apply le_of_eq;rw [map_eq_pure_bind]; apply MAlg.bind (m := m); ext a; cases a <;> simp
    simp [Except.getD, MAlg.μ, iInf_const]

instance
  [CompleteLattice l] [inst: MAlgOrdered m l] [IsHandler (fun (_ : ε) => True)]
  [inst': NoFailure m] : NoFailure (ExceptT ε m) where
  noFailure := by
    rintro _ c
    rw (occs := [2]) [<-inst'.noFailure (c := c)]
    simp [MAlg.lift, MAlgOrdered.μ, Functor.map, LE.pure, ExceptT.map, ExceptT.mk, OfHd, MAlgExcept]
    rw [map_eq_pure_bind]; apply MAlgOrdered.bind; ext (_|_) <;> simp

noncomputable
instance [Monad m] [LawfulMonad m] [_root_.CompleteLattice l]
  [IsHandler (ε := ε) hd]
  [inst: MAlgOrdered m l] :
  MAlgLift m l (ExceptT ε m) l where
    cl := by exact LogicLift.refl
    μ_lift := by
      intros; simp [MAlg.lift_ExceptT];
      simp [liftM, instMonadLiftTOfMonadLift, MonadLift.monadLift]
      simp [ExceptT.map, ExceptT.lift, ExceptT.mk, MAlg.lift]

end ExeceptHandler

namespace ExceptionAsSuccess
scoped instance PartialHandler {ε} : IsHandler (ε := ε) fun _ => True where
end ExceptionAsSuccess

namespace ExceptionAsFailure
scoped instance TotalHandler {ε} : IsHandler (ε := ε) fun _ => False where
end ExceptionAsFailure

open Lean.Order

instance [Monad m] [inst : ∀ α, CCPO (m α)] : CCPO (ExceptT ε m α) := inst _
instance [Monad m] [∀ α, CCPO (m α)] [MonoBind m] : MonoBind (ExceptT ε m) where
  bind_mono_left h₁₂ := by
    apply MonoBind.bind_mono_left (m := m)
    exact h₁₂
  bind_mono_right h₁₂ := by
    apply MonoBind.bind_mono_right (m := m)
    intro x
    cases x
    · apply PartialOrder.rel_refl
    · apply h₁₂

instance [Monad m] [CCPOBot m] : CCPOBot (ExceptT ε m) where
  compBot := CCPOBot.compBot (m := m)

instance [Monad m] [inst : ∀ α, Lean.Order.CCPO (m α)] [CCPOBot m] [CCPOBotLawful m] : CCPOBotLawful (ExceptT ε m) where
  prop := CCPOBotLawful.prop (m := m)

instance (hd : ε -> _) [IsHandler hd] [_root_.CompleteLattice l] [Monad m] [LawfulMonad m] [inst: MAlgOrdered m l]
  [∀ α, CCPO (m α)] [MonoBind m]
  [MAlgPartial m] : MAlgPartial (ExceptT ε m) where
  csup_lift {α} chain := by
    intro post hchain; simp [MAlg.lift_ExceptT]
    solve_by_elim [MAlgPartial.csup_lift (m := m)]

attribute [-simp] le_bot_iff in
instance (hd : ε -> _) [IsHandler hd] [_root_.CompleteLattice l] [Monad m] [LawfulMonad m] [inst: MAlgOrdered m l]
  [∀ α, CCPO (m α)] [MonoBind m]
  [MAlgTotal m] : MAlgTotal (ExceptT ε m) where
  bot_lift := by
    intro post hchain; simp [MAlg.lift_ExceptT]
    solve_by_elim [MAlgTotal.bot_lift (m := m)]
