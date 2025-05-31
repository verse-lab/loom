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
def MPropExcept (ε : Type u) (df : ε -> Prop) (l : Type u) (m : Type u -> Type v)
  [CompleteLattice l]
  [Monad m] [LawfulMonad m] [inst: MPropOrdered m l] : MPropOrdered (ExceptT ε m) l where
  μ := fun e => inst.μ $ Except.getD (⌜df ·⌝) <$> e
  μ_ord_pure := by
    intro l; simp [pure, ExceptT.pure, ExceptT.mk]
    solve_by_elim [MPropOrdered.μ_ord_pure]
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
  [CompleteLattice l] [inst: MPropOrdered m l] : MPropOrdered (ExceptT ε m) l := MPropExcept ε hd l m


lemma MProp.lift_ExceptT ε (hd : ε -> Prop) [IsHandler hd] [CompleteLattice l] [inst: MPropOrdered m l]
   (c : ExceptT ε m α) post :
  MProp.lift c post = MProp.lift (m := m) c (fun | .ok x => post x | .error e => ⌜hd e⌝) := by
    simp [MProp.lift, OfHd, MPropExcept, Functor.map, ExceptT.map, ExceptT.mk]
    rw [map_eq_pure_bind]; apply MPropOrdered.bind; ext a; cases a <;> simp [Except.getD]


instance MPropExceptHdDet (hd : ε -> Prop)
  [CompleteLattice l] [inst: MPropOrdered m l] [IsHandler hd]
  [inst': MPropDet m l] : MPropDet (ExceptT ε m) l where
  angelic := by
    intros α c p₁ p₂
    simp [MProp.lift, MProp.μ, MPropOrdered.μ, Functor.map, ExceptT.map, ExceptT.mk]
    simp [OfHd, MPropExcept]
    have h := inst'.angelic (α := Except ε α) (c := c)
      (p₁ := fun e =>
        match e with
        | Except.ok a    => p₁ a
        | Except.error e => ⌜hd e⌝ )
      (p₂ := fun e =>
        match e with
        | Except.ok a    => p₂ a
        | Except.error e => ⌜hd e⌝ )
    simp [MProp.lift, MProp.μ] at h
    have h₁ : ∀ p₁ p₂ : α -> l,
      (MPropOrdered.μ (m := m) (do
        bind (m := m) c fun a =>
        Except.getD (⌜hd ·⌝) <$>
            match a with
            | Except.ok a => pure (Except.ok (p₁ a))
            | Except.error e => pure (Except.error e))) ⊓
      (MPropOrdered.μ (m := m) (do
        bind (m := m) c fun a =>
        Except.getD (⌜hd ·⌝) <$>
            match a with
            | Except.ok a => pure (Except.ok (p₂ a))
            | Except.error e => pure (Except.error e))) =
      MPropOrdered.μ (Functor.map (f := m) (α := Except ε α)
        (fun a =>
          match a with
            | Except.ok a => (p₁ a)
            | Except.error e => ⌜hd e⌝) c) ⊓
      MPropOrdered.μ (Functor.map (f := m) (α := Except ε α)
        (fun a =>
          match a with
            | Except.ok a => (p₂ a)
            | Except.error e => ⌜hd e⌝) c) := by
      intro p₁ p₂; congr 1 <;> rw [map_eq_pure_bind] <;> apply MProp.bind (m := m) <;> ext a <;> cases a <;> simp
    (repeat erw [h₁]); clear h₁; apply le_trans; apply h
    apply le_of_eq;rw [map_eq_pure_bind]; apply MProp.bind (m := m); ext a; cases a <;> simp
  demonic := by
    intros α c p₁ p₂
    simp [MProp.lift, MProp.μ, MPropOrdered.μ, Functor.map, ExceptT.map, ExceptT.mk]
    simp [OfHd, MPropExcept]
    have h := inst'.demonic (α := Except ε α) (c := c)
      (p₁ := fun e =>
        match e with
        | Except.ok a    => p₁ a
        | Except.error e => ⌜hd e⌝ )
      (p₂ := fun e =>
        match e with
        | Except.ok a    => p₂ a
        | Except.error e => ⌜hd e⌝ )
    simp [MProp.lift, MProp.μ] at h
    have h₁ : ∀ p₁ p₂ : α -> l,
      (MPropOrdered.μ (m := m) (do
        bind (m := m) c fun a =>
        Except.getD (⌜hd ·⌝) <$>
            match a with
            | Except.ok a => pure (Except.ok (p₁ a))
            | Except.error e => pure (Except.error e))) ⊔
      (MPropOrdered.μ (m := m) (do
        bind (m := m) c fun a =>
        Except.getD (⌜hd ·⌝) <$>
            match a with
            | Except.ok a => pure (Except.ok (p₂ a))
            | Except.error e => pure (Except.error e))) =
      MPropOrdered.μ (Functor.map (f := m) (α := Except ε α)
        (fun a =>
          match a with
            | Except.ok a => (p₁ a)
            | Except.error e => ⌜hd e⌝) c) ⊔
      MPropOrdered.μ (Functor.map (f := m) (α := Except ε α)
        (fun a =>
          match a with
            | Except.ok a => (p₂ a)
            | Except.error e => ⌜hd e⌝) c) := by
      intro p₁ p₂; congr 1 <;> rw [map_eq_pure_bind] <;> apply MProp.bind (m := m) <;> ext a <;> cases a <;> simp
    (repeat erw [h₁]); clear h₁; apply le_trans'; apply h
    apply le_of_eq;rw [map_eq_pure_bind]; apply MProp.bind (m := m); ext a; cases a <;> simp


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

instance [Monad m] [inst : ∀ α, Lean.Order.CCPO (m α)] [CCPOBot m] : CCPOBot (ExceptT ε m) where
  compBot := CCPOBot.compBot (m := m)
  prop := CCPOBot.prop (m := m)


instance (hd : ε -> _) [IsHandler hd] [_root_.CompleteLattice l] [Monad m] [LawfulMonad m] [inst: MPropOrdered m l]
  [∀ α, CCPO (m α)] [MonoBind m]
  [MPropPartial m] : MPropPartial (ExceptT ε m) where
  csup_lift {α} chain := by
    intro post hchain; simp [MProp.lift_ExceptT]
    solve_by_elim [MPropPartial.csup_lift (m := m)]

attribute [-simp] le_bot_iff in
instance (hd : ε -> _) [IsHandler hd] [_root_.CompleteLattice l] [Monad m] [LawfulMonad m] [inst: MPropOrdered m l]
  [∀ α, CCPO (m α)] [MonoBind m]
  [MPropTotal m] : MPropTotal (ExceptT ε m) where
  bot_lift := by
    intro post hchain; simp [MProp.lift_ExceptT]
    solve_by_elim [MPropTotal.bot_lift (m := m)]
