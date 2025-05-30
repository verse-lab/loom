import Loom.MonadAlgebras.Defs
universe u v w

instance : MPropOrdered Id Prop where
  μ := id
  μ_ord_pure := by simp
  μ_ord_bind := by solve_by_elim

instance : MPropDet Id Prop where
  demonic := by
    intros α c p q;
    simp [MProp.lift, MProp.μ, MPropOrdered.μ]
  angelic := by
    intros α c p q;
    simp [MProp.lift, MProp.μ, MPropOrdered.μ]

inductive DivM (α : Type u) where
  | res (x : α)
  | div

instance : Monad DivM where
  pure := DivM.res
  bind := fun x y => match x with
    | DivM.res x => y x
    | DivM.div => DivM.div

class CCPOBot (m : Type u -> Type v) [∀ α, Lean.Order.CCPO (m α)] where
  compBot {α} : m α
  prop {α} : @compBot α = Lean.Order.bot

instance : LawfulMonad DivM := by
  refine LawfulMonad.mk' _ ?_ ?_ ?_
  { introv; cases x <;> rfl }
  { introv; rfl }
  introv; cases x <;> rfl

noncomputable instance : Lean.Order.CCPO (DivM α) := inferInstanceAs (Lean.Order.CCPO (Lean.Order.FlatOrder .div))
instance : CCPOBot DivM where
  compBot := .div
  prop := by simp [Lean.Order.bot, Lean.Order.CCPO.csup,Lean.Order.flat_csup]

instance : Lean.Order.MonoBind DivM where
  bind_mono_left := by
    rintro _ _ (_|_) _ _ (_|_) <;> solve_by_elim
  bind_mono_right := by
    rintro _ _ (_|_) <;> solve_by_elim

namespace PartialCorrectness


scoped instance : MPropOrdered DivM Prop where
  μ := fun x => match x with
    | .res x => x
    | .div => ⊤
  μ_ord_pure := by simp [LE.pure]
  μ_ord_bind {α} f g := by
    rintro h (_|_) <;> simp
    solve_by_elim

scoped instance : MPropDet DivM Prop where
  demonic := by
    rintro _ (_|_) <;> simp [MProp.lift, MPropOrdered.μ, Functor.map, LE.pure]
  angelic := by
    rintro _ (_|_) <;> simp [MProp.lift, MPropOrdered.μ, Functor.map, LE.pure]

instance : MPropPartial DivM where
  csup_lift {α} chain := by
    intro post hchain
    simp [Lean.Order.CCPO.csup, Lean.Order.flat_csup]
    split_ifs with ch
    { intro h; apply h;
      rcases Classical.choose_spec ch
      solve_by_elim }
    solve_by_elim

end PartialCorrectness

namespace TotalCorrectness

scoped instance : MPropOrdered DivM Prop where
  μ := fun x => match x with
    | .res x => ⌜x⌝
    | .div => ⊥
  μ_ord_pure := by simp [LE.pure]
  μ_ord_bind {α} f g := by
    rintro h (_|_) <;> simp
    solve_by_elim

scoped instance : MPropDet DivM Prop where
  angelic := by
    rintro _ (_|_) <;> simp [MProp.lift, MPropOrdered.μ, Functor.map, LE.pure]
  demonic := by
    rintro _ (_|_) <;> simp [MProp.lift, MPropOrdered.μ, Functor.map, LE.pure]

end TotalCorrectness
