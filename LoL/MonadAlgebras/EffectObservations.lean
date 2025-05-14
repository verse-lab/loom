import Mathlib.Order.CompleteLattice.Basic

import LoL.MonadUtil
import LoL.SpecMonad

universe u v w

variable (m : Type v -> Type u)

class MProp [Monad m] (l : outParam (Type v)) where
  μ : m l -> l
  pure : ∀ l, μ (pure l) = l
  bind : ∀ {α : Type v} (x : m α) (f g : α -> m l),
    μ ∘ f = μ ∘ g ->
    μ (x >>= f) = μ (x >>= g)

abbrev MProp.lift {m : Type u -> Type v} {l : Type u} [Monad m] [MProp m l] :
  {α : Type u} -> m α -> Cont l α := fun x f => μ $ f <$> x

instance (l : Type u) {m : Type u -> Type v} [Monad m] [MProp m l] : MonadLiftT m (Cont l) where
  monadLift := MProp.lift

instance (l : Type u) {m : Type u -> Type v} [Monad m] [LawfulMonad m] [MProp m l] : LawfulMonadLift m (Cont l) where
  lift_pure := by
    intro α x; simp [monadLift, pure]; unfold MProp.lift; simp [map_pure, MProp.pure]
  lift_bind := by
    intros α β x f; simp [monadLift, bind]; unfold MProp.lift; ext g
    rw (config := { occs := .pos [2] }) [map_eq_pure_bind]
    simp only [map_bind]; apply MProp.bind
    ext; simp [MProp.pure]

class MPropOrdered (l : outParam (Type v)) [Monad m] [PartialOrder l] where
  μ : m l -> l
  μ_ord_pure : ∀ l, μ (pure l) = l
  μ_ord_bind {α : Type v} :
    ∀ (f g : α -> m l), μ ∘ f ≤ μ ∘ g ->
      ∀ x : m α, μ (x >>= f) ≤ μ (x >>= g)

@[reducible]
instance OfMPropPartialOrdered {m : Type u -> Type v} {l : Type u} [Monad m] [PartialOrder l] [mprop : MPropOrdered m l] : MProp m l where
  μ := MPropOrdered.μ
  pure := MPropOrdered.μ_ord_pure
  bind := by intros; apply PartialOrder.le_antisymm
    <;> apply MPropOrdered.μ_ord_bind
    <;> simp_all only [le_refl]

lemma MPropOrdered.bind {α : Type u} {m} {l : Type u} [Monad m] [PartialOrder l] [MPropOrdered m l] :
    ∀ (x : m α) (f g : α -> m l), μ ∘ f = μ ∘ g ->
     μ (x >>= f) = μ (x >>= g) := MProp.bind

lemma Cont.monotone_lift {l : Type u} {m : Type u -> Type v} [Monad m] [LawfulMonad m] [PartialOrder l] [MPropOrdered m l] :
  ∀ {α : Type u} (x : m α), MProp.lift x |>.monotone := by
  unfold Cont.monotone; intros; simp [MProp.lift]; rw [map_eq_pure_bind, map_eq_pure_bind]
  apply MPropOrdered.μ_ord_bind; intro; simp [MPropOrdered.μ_ord_pure, *]

open Classical in
noncomputable def LE.pure {l : Type u} [inst: LE l] [OrderTop l] [OrderBot l] : Prop -> l := fun p =>
  if p then ⊤ else ⊥

macro "⌜" p:term "⌝" : term => `(LE.pure $p)

@[app_unexpander LE.pure] def unexpandPure : Lean.PrettyPrinter.Unexpander
  | `($(_) $p:term) => `(⌜$p:term⌝)
  | _ => throw ()


lemma trueE (l : Type v) [inst: LE l] [OrderTop l] [OrderBot l] : ⌜True⌝ = (⊤ : l) := by
  simp [LE.pure]



lemma falseE (l : Type v) [inst: LE l] [OrderTop l] [OrderBot l] : ⌜False⌝ = (⊥ : l) := by
  simp [LE.pure]

open Classical in
lemma LE.pure_imp {l : Type u} [inst: LE l] [OrderTop l] [OrderBot l]
  (p₁ p₂ : Prop) : (p₁ -> p₂) -> ⌜p₁⌝ <= (⌜p₂⌝ : l) := by
  simp [LE.pure]; split <;> aesop

lemma LE.pure_intro {l : Type u} [inst: LE l] [OrderTop l] [OrderBot l]
  (p : Prop) (h : l) : (⌜p⌝ <= h) = (p -> ⊤ <= h) := by
    simp [LE.pure]; split <;> aesop

@[simp]
lemma MProp.μ_eq {m l} [Monad m] [PartialOrder l] [MPropOrdered m l] : MProp.μ (m := m) = MPropOrdered.μ (m := m) := by rfl

lemma MProp.lift_bind {α β} {l : Type u} {m : Type u -> Type v} [Monad m] [LawfulMonad m] [PartialOrder l] [MPropOrdered m l]
  (x : m α) (f g : α -> Cont l β) :
    f <= g ->
    (lift x >>= f) ≤ (lift x >>= g) := by
    intro fLg h; simp [Bind.bind]
    apply Cont.monotone_lift; intros h; apply fLg

class MPropDetertministic (l : outParam (Type v)) [Monad m] [CompleteLattice l] [MPropOrdered m l] where
  /-- 😈 -/
  demonic {α ι : Type v} (c : m α) (p : ι -> α -> l) [Nonempty ι] : ⨅ i, MProp.lift c (p i) ≤ MProp.lift c (fun x => ⨅ i, p i x)
  /-- 😇 -/
  angelic {α ι : Type v} (c : m α) (p : ι -> α -> l) [Nonempty ι] : MProp.lift c (fun x => ⨆ i, p i x) ≤ ⨆ i, MProp.lift c (p i)
