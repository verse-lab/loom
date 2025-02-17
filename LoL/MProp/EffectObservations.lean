import LoL.MonadUtil
import LoL.SpecMonad

universe u v w

variable (m : Type v -> Type u)

structure PProp : Type v where
  prop : Prop

set_option allowUnsafeReducibility true in
attribute [reducible] PProp

instance : Coe Prop PProp where
  coe p := ⟨p⟩

instance : Coe PProp Prop where
  coe p := p.prop


class MProp [Monad m] (l : outParam (Type v)) where
  μ : m PProp -> l
  μSur : { ι : l -> m PProp // μ.LeftInverse ι }
  bind : ∀ {α : Type v} (x : m α) (f g : α -> m PProp),
    μ ∘ f = μ ∘ g ->
    μ (x >>= f) = μ (x >>= g)

def MProp.ι {m} {l : Type u} [Monad m] [MProp m l] : l -> m PProp :=
  μSur.val

lemma MProp.cancel {m} {l : Type u} [Monad m] [MProp m l] (x : l) : μ (MProp.ι (m := m) x) = x :=
  μSur.property x

lemma MProp.cancelM {l} [Monad m] [MProp m l] {α : Type v} (x : m α) (f : _ -> _) :
    μ (x >>= MProp.ι ∘ μ ∘ f) = μ (x >>= f) := by
  apply MProp.bind; unfold Function.comp; simp [MProp.cancel]


abbrev MProp.lift {m : Type u -> Type v} {l : Type u} [Monad m] [LawfulMonad m] [MProp m l] :
  {α : Type u} -> m α -> Cont l α := fun x f => μ $ f <$> x >>= MProp.ι

instance (l : Type u) {m : Type u -> Type v} [Monad m] [LawfulMonad m] [MProp m l] : MonadLiftT m (Cont l) where
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
  μOrd {α : Type v} :
    ∀ (f g : α -> m PProp), μ ∘ f <= μ ∘ g -> (μ $ · >>= f) ≤ (μ $ · >>= g)

lemma Cont.monotone_lift {l : Type u} {m : Type u -> Type v} [Monad m] [LawfulMonad m] [Preorder l] [MPropOrdered m l] :
  ∀ {α : Type u} (x : m α), MProp.lift x |>.monotone := by
  unfold Cont.monotone; intros; simp [MProp.lift]
  apply MPropOrdered.μOrd; intro; simp [MProp.cancel, *]

class MPropPartialOrder (l : outParam (Type v)) [Monad m] [PartialOrder l] where
  μ : m PProp -> l
  μSur : { ι : l -> m PProp // μ.LeftInverse ι }
  μOrd {α : Type v} :
    ∀ (f g : α -> m PProp), μ ∘ f ≤ μ ∘ g -> (μ $ · >>= f) ≤ (μ $ · >>= g)

instance OfMPropPartialOrdered {m : Type -> Type} {l : Type} [Monad m] [PartialOrder l] [MPropPartialOrder m l] : MPropOrdered m l where
  μ := MPropPartialOrder.μ
  μSur := MPropPartialOrder.μSur
  μOrd := MPropPartialOrder.μOrd
  bind := by intros; apply PartialOrder.le_antisymm <;> apply MPropPartialOrder.μOrd <;> simp_all only [le_refl]

lemma MProp.μ_lift {l : Type u} {m : Type u -> Type v} [Monad m] [LawfulMonad m] [Preorder l] [MPropOrdered m l] : MProp.μ (m := m) = (liftM (n := Cont l) · (MProp.μ ∘ pure (f := m))) := by
  funext x; simp [liftM, monadLift, MProp.lift, Function.comp]
  rw [MProp.bind (g := pure)]; simp
  ext; simp [MProp.cancel]
