import Mathlib.Order.CompleteLattice

import LoL.MonadUtil
import LoL.SpecMonad

universe u v w

variable (m : Type v -> Type u)

abbrev UProp : Type u := ULift Prop

instance : Coe Prop UProp where
  coe p := ⟨p⟩

-- instance : Coe UProp Prop where
--   coe p := p.down


class MProp [Monad m] (l : outParam (Type v)) where
  μ : m UProp -> l
  ι : l -> m UProp
  μ_surjective : μ.LeftInverse ι
  bind : ∀ {α : Type v} (x : m α) (f g : α -> m UProp),
    μ ∘ f = μ ∘ g ->
    μ (x >>= f) = μ (x >>= g)


lemma MProp.cancel {m} {l : Type u} [Monad m] [MProp m l] (x : l) : μ (MProp.ι (m := m) x) = x :=
  μ_surjective x

lemma MProp.cancelM {l} [Monad m] [MProp m l] {α : Type v} (x : m α) (f : _ -> _) :
    μ (x >>= MProp.ι ∘ μ ∘ f) = μ (x >>= f) := by
  apply MProp.bind; unfold Function.comp; simp [MProp.cancel]


abbrev MProp.lift {m : Type u -> Type v} {l : Type u} [Monad m] [MProp m l] :
  {α : Type u} -> m α -> Cont l α := fun x f => μ $ f <$> x >>= MProp.ι

instance (l : Type u) {m : Type u -> Type v} [Monad m] [MProp m l] : MonadLiftT m (Cont l) where
  monadLift := MProp.lift


instance (l : Type u) {m : Type u -> Type v} [Monad m] [LawfulMonad m] [MProp m l] : LawfulMonadLift m (Cont l) where
  lift_pure := by
    intro α x; simp [monadLift, pure]; unfold MProp.lift; simp [map_pure, MProp.cancel]
  lift_bind := by
    intros α β x f; simp [monadLift, bind]; unfold MProp.lift; ext g
    rw (config := { occs := .pos [2] }) [map_eq_pure_bind]
    simp only [bind_assoc, pure_bind]
    erw [MProp.cancelM]; simp


class MPropOrdered (l : outParam (Type v)) [Monad m] [Preorder l] extends MProp m l where
  μ_ord_bind {α : Type v} :
    ∀ (f g : α -> m UProp), μ ∘ f <= μ ∘ g -> (μ $ · >>= f) ≤ (μ $ · >>= g)

lemma Cont.monotone_lift {l : Type u} {m : Type u -> Type v} [Monad m] [LawfulMonad m] [Preorder l] [MPropOrdered m l] :
  ∀ {α : Type u} (x : m α), MProp.lift x |>.monotone := by
  unfold Cont.monotone; intros; simp [MProp.lift]
  apply MPropOrdered.μ_ord_bind; intro; simp [MProp.cancel, *]

class MPropPartialOrder (l : outParam (Type v)) [Monad m] [PartialOrder l] where
  μ : m UProp -> l
  ι : l -> m UProp
  μ_surjective : μ.LeftInverse ι
  -- μ_pure_injective : ∀ (p : Prop), ι (μ (pure p)) = pure (f := m) p
  μ_top (x : l) : x <= μ (pure True)
  μ_bot (x : l) : μ (pure False) <= x
  -- μ_nontriv : μ (pure True) ≠ μ (pure False) -- pick_outcomes
  μ_ord_pure (p₁ p₂ : Prop) : (p₁ -> p₂) -> μ (pure p₁) ≤ μ (pure p₂)
  μ_ord_bind {α : Type v} :
    ∀ (f g : α -> m UProp), μ ∘ f ≤ μ ∘ g ->
      ∀ x : m α, μ (x >>= f) ≤ μ (x >>= g)

instance OfMPropPartialOrdered {m : Type u -> Type v} {l : Type u} [Monad m] [PartialOrder l] [MPropPartialOrder m l] : MPropOrdered m l where
  μ := MPropPartialOrder.μ
  ι := MPropPartialOrder.ι
  μ_surjective := MPropPartialOrder.μ_surjective
  μ_ord_bind := MPropPartialOrder.μ_ord_bind
  bind := by intros; apply PartialOrder.le_antisymm
    <;> apply MPropPartialOrder.μ_ord_bind
    <;> simp_all only [le_refl]

def MProp.pure {l : Type u} {m : Type u -> Type v} [Monad m] [PartialOrder l] [inst : MPropPartialOrder m l]
  := MProp.μ ∘ Pure.pure (f := m)

macro "⌜" p:term "⌝" : term => `(MProp.pure (inst := by assumption) { down := $p })

@[app_unexpander MProp.pure] def unexpandPure : Lean.PrettyPrinter.Unexpander
  | `($(_) { down := $p:term }) => `(⌜$p:term⌝)
  | `($(_) $p:term) => `(⌜$p:term⌝)
  | _ => throw ()

-- notation "⌜" p "⌝" => MProp.pure { prop := p }

lemma MProp.pure_imp {l : Type u} {m : Type u -> Type v} [Monad m] [LawfulMonad m]
  [PartialOrder l] [MPropPartialOrder m l]
  (p₁ p₂ : Prop) : (p₁ -> p₂) -> ⌜p₁⌝ <= ⌜p₂⌝ := by
  apply MPropPartialOrder.μ_ord_pure

lemma MProp.pure_intro {l : Type u} {m : Type u -> Type v} [Monad m] [LawfulMonad m]
  [PartialOrder l] [MPropPartialOrder m l]
  (p : Prop) (h : l) : (⌜p⌝ <= h) = (p -> ⌜ True ⌝ <= h) := by
    by_cases hp : p = False
    { simp [hp]; apply MPropPartialOrder.μ_bot }
    simp_all

lemma MProp.μ_lift {l : Type u} {m : Type u -> Type v} [Monad m] [LawfulMonad m] [PartialOrder l] [MPropPartialOrder m l] :
  MProp.μ (m := m) = (liftM (n := Cont l) · (MProp.pure (m := m))) := by
  funext x; simp [liftM, monadLift, MProp.lift, Function.comp]
  rw [MProp.bind (g := Pure.pure)]; simp
  ext; simp [MProp.cancel, MProp.pure]

lemma MProp.lift_bind {α β} {l : Type u} {m : Type u -> Type v} [Monad m] [LawfulMonad m] [Preorder l] [MPropOrdered m l]
  (x : m α) (f g : α -> Cont l β) :
    f <= g ->
    (lift x >>= f) ≤ (lift x >>= g) := by
    intro fLg h; simp [Bind.bind]
    apply Cont.monotone_lift; intros h; apply fLg

class MPropDetertministic (l : outParam (Type v)) [Monad m] [CompleteLattice l] [MPropPartialOrder m l] where
  /-- 😈 -/
  demonic {α ι : Type v} (c : m α) (p : ι -> α -> l) [Nonempty ι] : ⨅ i, MProp.lift c (p i) ≤ MProp.lift c (fun x => ⨅ i, p i x)
  /-- 😇 -/
  angelic {α} (c : m α) (p q : α -> l) : MProp.lift c (p ⊔ q) ≤ MProp.lift c p ⊔ MProp.lift c q
