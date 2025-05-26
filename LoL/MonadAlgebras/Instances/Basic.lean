import LoL.MonadAlgebras.Defs
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

inductive DevM (α : Type u) where
  | res (x : α)
  | dev

instance : Monad DevM where
  pure := DevM.res
  bind := fun x y => match x with
    | DevM.res x => y x
    | DevM.dev => DevM.dev

instance : LawfulMonad DevM := by
  refine LawfulMonad.mk' _ ?_ ?_ ?_
  { introv; cases x <;> rfl }
  { introv; rfl }
  introv; cases x <;> rfl

noncomputable instance : Lean.Order.CCPO (DevM α) := inferInstanceAs (Lean.Order.CCPO (Lean.Order.FlatOrder .dev))

instance : Lean.Order.MonoBind DevM where
  bind_mono_left := by
    rintro _ _ (_|_) _ _ (_|_) <;> solve_by_elim
  bind_mono_right := by
    rintro _ _ (_|_) <;> solve_by_elim

namespace PartialCorrectness


scoped instance : MPropOrdered DevM Prop where
  μ := fun x => match x with
    | .res x => x
    | .dev => ⊤
  μ_ord_pure := by simp [LE.pure]
  μ_ord_bind {α} f g := by
    rintro h (_|_) <;> simp
    solve_by_elim

instance : MPropDet DevM Prop where
  demonic := by
    rintro _ (_|_) <;> simp [MProp.lift, MPropOrdered.μ, Functor.map, LE.pure]
  angelic := by
    rintro _ (_|_) <;> simp [MProp.lift, MPropOrdered.μ, Functor.map, LE.pure]

instance : MPropPartial DevM where
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

scoped instance : MPropOrdered DevM Prop where
  μ := fun x => match x with
    | .res x => ⌜x⌝
    | .dev => ⊥
  μ_ord_pure := by simp [LE.pure]
  μ_ord_bind {α} f g := by
    rintro h (_|_) <;> simp
    solve_by_elim

instance : MPropDet DevM Prop where
  angelic := by
    rintro _ (_|_) <;> simp [MProp.lift, MPropOrdered.μ, Functor.map, LE.pure]
  demonic := by
    rintro _ (_|_) <;> simp [MProp.lift, MPropOrdered.μ, Functor.map, LE.pure]

end TotalCorrectness
