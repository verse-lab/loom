import Loom.Order.BooleanAlgebra

namespace Loom.Order

universe u v w

instance propPreorder : Preorder Prop where
  le p q := p → q
  le_refl _ := id
  le_trans h k := k ∘ h

instance propPartialOrder : PartialOrder Prop where
  toPreorder := propPreorder
  le_antisymm h k := propext ⟨h, k⟩

instance propOrderTop : OrderTop Prop where
  top := True
  le_top _ _ := True.intro

instance propOrderBot : OrderBot Prop where
  bot := False
  bot_le _ := False.elim

instance propLattice : Lattice Prop where
  toPartialOrder := propPartialOrder
  inf := And
  sup := Or
  inf_le_left _ _ := And.left
  inf_le_right _ _ := And.right
  le_inf h k x := ⟨h x, k x⟩
  le_sup_left _ _ := Or.inl
  le_sup_right _ _ := Or.inr
  sup_le h k := fun x => Or.elim x h k

instance propCompleteLattice : CompleteLattice Prop where
  toLattice := propLattice
  toOrderTop := propOrderTop
  toOrderBot := propOrderBot
  sInf s := ∀ p, s p → p
  sSup s := ∃ p, s p ∧ p
  sInf_le h k := k _ h
  le_sInf h ha p hp := h p hp ha
  le_sSup h ha := ⟨_, h, ha⟩
  sSup_le h := fun ⟨p, hp, ha⟩ => h p hp ha

instance propBooleanAlgebra : BooleanAlgebra Prop where
  toLattice := propLattice
  toOrderTop := propOrderTop
  toOrderBot := propOrderBot
  compl := Not
  himp p q := p → q
  inf_sup_left _ _ _ := propext and_or_left
  inf_compl_eq_bot _ := propext ⟨fun h => h.2 h.1, False.elim⟩
  sup_compl_eq_top p := propext ⟨fun _ => True.intro, fun _ => Classical.em p⟩
  himp_eq p q := by
    apply propext
    constructor
    · intro h
      exact (Classical.em p).elim (fun hp => Or.inr (h hp)) Or.inl
    · intro h hp
      exact h.elim (fun hn => (hn hp).elim) id

instance propCompleteBooleanAlgebra : CompleteBooleanAlgebra Prop :=
  { propCompleteLattice, propBooleanAlgebra with }

instance piPreorder {ι : Type u} {α : ι → Type v} [∀ i, Preorder (α i)] :
    Preorder ((i : ι) → α i) where
  le f g := ∀ i, f i ⊑ₗ g i
  le_refl _ _ := le_refl _
  le_trans h k i := le_trans (h i) (k i)

instance piPartialOrder {ι : Type u} {α : ι → Type v} [∀ i, PartialOrder (α i)] :
    PartialOrder ((i : ι) → α i) where
  toPreorder := piPreorder
  le_antisymm h k := funext fun i => le_antisymm (h i) (k i)

instance piOrderTop {ι : Type u} {α : ι → Type v}
    [∀ i, Preorder (α i)] [∀ i, OrderTop (α i)] : OrderTop ((i : ι) → α i) where
  top _ := top
  le_top _ _ := le_top _

instance piOrderBot {ι : Type u} {α : ι → Type v}
    [∀ i, Preorder (α i)] [∀ i, OrderBot (α i)] : OrderBot ((i : ι) → α i) where
  bot _ := bot
  bot_le _ _ := bot_le _

instance piLattice {ι : Type u} {α : ι → Type v} [∀ i, Lattice (α i)] :
    Lattice ((i : ι) → α i) where
  toPartialOrder := piPartialOrder
  inf f g i := f i ⊓ₗ g i
  sup f g i := f i ⊔ₗ g i
  inf_le_left _ _ _ := inf_le_left ..
  inf_le_right _ _ _ := inf_le_right ..
  le_inf h k i := le_inf (h i) (k i)
  le_sup_left _ _ _ := le_sup_left ..
  le_sup_right _ _ _ := le_sup_right ..
  sup_le h k i := sup_le (h i) (k i)

instance piCompleteLattice {ι : Type u} {α : ι → Type v} [∀ i, CompleteLattice (α i)] :
    CompleteLattice ((i : ι) → α i) where
  toLattice := piLattice
  toOrderTop := piOrderTop
  toOrderBot := piOrderBot
  sInf s i := sInf (fun a => ∃ f, s f ∧ f i = a)
  sSup s i := sSup (fun a => ∃ f, s f ∧ f i = a)
  sInf_le h _ := sInf_le ⟨_, h, rfl⟩
  le_sInf h i := le_sInf fun _ ⟨f, hf, hi⟩ => hi ▸ h f hf i
  le_sSup h _ := le_sSup ⟨_, h, rfl⟩
  sSup_le h i := sSup_le fun _ ⟨f, hf, hi⟩ => hi ▸ h f hf i

instance piBooleanAlgebra {ι : Type u} {α : ι → Type v} [∀ i, BooleanAlgebra (α i)] :
    BooleanAlgebra ((i : ι) → α i) where
  toLattice := piLattice
  toOrderTop := piOrderTop
  toOrderBot := piOrderBot
  compl f i := compl (f i)
  himp f g i := himp (f i) (g i)
  inf_sup_left _ _ _ := funext fun _ => inf_sup_left ..
  inf_compl_eq_bot _ := funext fun _ => inf_compl_eq_bot _
  sup_compl_eq_top _ := funext fun _ => sup_compl_eq_top _
  himp_eq _ _ := funext fun _ => himp_eq ..

instance piCompleteBooleanAlgebra {ι : Type u} {α : ι → Type v}
    [∀ i, CompleteBooleanAlgebra (α i)] : CompleteBooleanAlgebra ((i : ι) → α i) :=
  { piCompleteLattice, piBooleanAlgebra with }

@[simp] theorem prop_le (p q : Prop) : (p ⊑ₗ q) = (p → q) := rfl
@[simp] theorem prop_inf (p q : Prop) : (p ⊓ₗ q) = (p ∧ q) := rfl
@[simp] theorem prop_sup (p q : Prop) : (p ⊔ₗ q) = (p ∨ q) := rfl
@[simp] theorem prop_himp (p q : Prop) : himp p q = (p → q) := rfl
@[simp] theorem prop_compl (p : Prop) : compl p = ¬p := rfl
@[simp] theorem prop_top : (top : Prop) = True := rfl
@[simp] theorem prop_bot : (bot : Prop) = False := rfl

@[simp] theorem prop_iInf {ι : Sort u} (f : ι → Prop) : iInf f = (∀ i, f i) := by
  apply propext
  exact ⟨fun h i => h _ ⟨i, rfl⟩, fun h _ ⟨i, hi⟩ => hi ▸ h i⟩

@[simp] theorem prop_iSup {ι : Sort u} (f : ι → Prop) : iSup f = (∃ i, f i) := by
  apply propext
  exact ⟨fun ⟨_, ⟨i, hi⟩, h⟩ => ⟨i, hi.symm ▸ h⟩, fun ⟨i, h⟩ => ⟨_, ⟨i, rfl⟩, h⟩⟩

@[simp] theorem pi_inf_apply {ι : Type u} {α : ι → Type v} [∀ i, Lattice (α i)]
    (f g : (i : ι) → α i) (i : ι) : (f ⊓ₗ g) i = f i ⊓ₗ g i := rfl

@[simp] theorem pi_sup_apply {ι : Type u} {α : ι → Type v} [∀ i, Lattice (α i)]
    (f g : (i : ι) → α i) (i : ι) : (f ⊔ₗ g) i = f i ⊔ₗ g i := rfl

@[simp] theorem pi_iInf_apply {ι : Type u} {α : ι → Type v} [∀ i, CompleteLattice (α i)]
    {κ : Sort w} (f : κ → (i : ι) → α i) (i : ι) :
    iInf f i = iInf (fun k => f k i) := by
  apply le_antisymm
  · exact le_iInf fun k => iInf_le f k i
  · change _ ⊑ₗ sInf _
    apply le_sInf
    rintro a ⟨g, ⟨k, rfl⟩, rfl⟩
    exact iInf_le (fun k => f k i) k

@[simp] theorem pi_iSup_apply {ι : Type u} {α : ι → Type v} [∀ i, CompleteLattice (α i)]
    {κ : Sort w} (f : κ → (i : ι) → α i) (i : ι) :
    iSup f i = iSup (fun k => f k i) := by
  apply le_antisymm
  · change sSup _ ⊑ₗ _
    apply sSup_le
    rintro a ⟨g, ⟨k, rfl⟩, rfl⟩
    exact le_iSup (fun k => f k i) k
  · exact iSup_le fun k => le_iSup f k i

end Loom.Order
