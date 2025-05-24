import LoL.MonadAlgebras.Defs

instance (σ : Type u) (l : Type u) (m : Type u -> Type v)
  [PartialOrder l]
  [Monad m] [LawfulMonad m] [inst: MPropOrdered m l] : MPropOrdered (ReaderT σ m) (σ -> l) where
  μ := fun rp r => inst.μ $ (· r) <$> rp r
  μ_ord_pure := by
    intros l; simp [pure, ReaderT.pure]; ext r
    solve_by_elim [MPropOrdered.μ_ord_pure]
  μ_ord_bind := by
    intros α f g
    simp [Function.comp, Pi.hasLe, Pi.partialOrder, Pi.preorder, inferInstanceAs]; intros le x r
    have leM := @inst.μ_ord_bind (α) (fun a => (· r) <$> f a r) (fun a => (· r) <$> g a r)
    simp only [Function.comp, Pi.hasLe, <-map_bind] at leM
    apply leM; simp only [implies_true, le]


instance (σ : Type u) (l : Type u) (m : Type u -> Type v)
  [CompleteLattice l]
  [Monad m] [LawfulMonad m] [inst: MPropOrdered m l] [inst': MPropDet m l]
   : MPropDet (ReaderT σ m) (σ -> l) where
    angelic := by
      intros α c p₁ p₂ s;
      simp [MProp.lift, MProp.μ, MPropOrdered.μ, Functor.map]
      have h := inst'.angelic (α := α) (c := c s) (p₁ := fun x => p₁ x s) (p₂ := fun x => p₂ x s)
      simp [MProp.lift, MProp.μ] at h
      apply h
    demonic := by
      intros α c p₁ p₂ s;
      simp [MProp.lift, MProp.μ, MPropOrdered.μ, Functor.map]
      have h := inst'.demonic (α := α) (c := c s) (p₁ := fun x => p₁ x s) (p₂ := fun x => p₂ x s)
      simp [MProp.lift, MProp.μ] at h
      apply h


instance [Monad m] [inst : ∀ α, Lean.Order.CCPO (m α)] : Lean.Order.CCPO (ReaderT ε m α) := by
  unfold ReaderT
  infer_instance
instance [Monad m] [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] : Lean.Order.MonoBind (ReaderT ε m) where
  bind_mono_left h₁₂ _ := by
    simp [bind, ReaderT.bind]
    apply Lean.Order.MonoBind.bind_mono_left (m := m)
    apply h₁₂
  bind_mono_right h₁₂ _ := by
    simp [bind, StateT.bind]
    apply Lean.Order.MonoBind.bind_mono_right (m := m)
    intro x; apply h₁₂

lemma MProp.lift_ReaderT [Monad m] [LawfulMonad m] [PartialOrder l] [inst: MPropOrdered m l] (x : ReaderT σ m α) :
  MProp.lift x post = fun s => MProp.lift (x s) (fun xs => post xs s) := by
    simp [MProp.lift, Functor.map, MPropOrdered.μ]

open Lean.Order in
instance [Monad m] [LawfulMonad m] [_root_.CompleteLattice l] [inst: MPropOrdered m l]
  [∀ α, CCPO (m α)] [MonoBind m]
  [MPropPartial m] : MPropPartial (ReaderT σ m) where
  csup_lift {α} chain := by
    intro post hchain
    simp [instCCPOReaderTOfMonad_loL, CCPO.csup, MProp.lift_ReaderT]
    rw [@Pi.le_def]; simp; unfold fun_csup; intro s
    apply le_trans'
    apply MPropPartial.csup_lift (m := m)
    { simp [Lean.Order.chain]; rintro x y f cf rfl g cg rfl
      cases (hchain f g cf cg)
      { left; solve_by_elim }
      right; solve_by_elim }
    repeat rw [@iInf_subtype']
    refine iInf_mono' ?_; simp [Membership.mem, Set.Mem]; aesop
