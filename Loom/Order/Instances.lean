module

public import Loom.Order.BooleanAlgebra

@[expose] public section

namespace Loom.Order

universe u v w

instance propCompleteBooleanAlgebra : CompleteBooleanAlgebra Prop where
  le p q := p → q
  le_refl _ := id
  le_trans _ _ _ h k := k ∘ h
  le_antisymm _ _ h k := propext ⟨h, k⟩
  min := And
  max := Or
  le_min_iff _ _ _ := ⟨fun h => ⟨fun x => (h x).1, fun x => (h x).2⟩,
    fun ⟨h, k⟩ x => ⟨h x, k x⟩⟩
  max_le_iff _ _ _ := ⟨fun h => ⟨fun x => h (.inl x), fun x => h (.inr x)⟩,
    fun ⟨h, k⟩ x => x.elim h k⟩
  top := True
  bot := False
  le_top _ _ := True.intro
  bot_le _ := False.elim
  sInf s := ∀ p, s p → p
  sSup s := ∃ p, s p ∧ p
  sInf_le h k := k _ h
  le_sInf h ha p hp := h p hp ha
  le_sSup h ha := ⟨_, h, ha⟩
  sSup_le h := fun ⟨p, hp, ha⟩ => h p hp ha
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

instance piCompleteLattice {ι : Type u} {α : ι → Type v} [∀ i, CompleteLattice (α i)] :
    CompleteLattice ((i : ι) → α i) where
  le f g := ∀ i, f i ≤ g i
  le_refl _ _ := le_refl _
  le_trans _ _ _ h k i := le_trans (h i) (k i)
  le_antisymm _ _ h k := funext fun i => le_antisymm (h i) (k i)
  min f g i := f i ⊓ g i
  max f g i := f i ⊔ g i
  le_min_iff _ _ _ := ⟨fun h => ⟨fun i => (Std.le_min_iff.mp (h i)).1,
    fun i => (Std.le_min_iff.mp (h i)).2⟩, fun ⟨h, k⟩ i => le_inf (h i) (k i)⟩
  max_le_iff _ _ _ := ⟨fun h => ⟨fun i => (Std.max_le_iff.mp (h i)).1,
    fun i => (Std.max_le_iff.mp (h i)).2⟩, fun ⟨h, k⟩ i => sup_le (h i) (k i)⟩
  top _ := top
  bot _ := bot
  le_top _ _ := le_top _
  bot_le _ _ := bot_le _
  sInf s i := sInf (fun a => ∃ f, s f ∧ f i = a)
  sSup s i := sSup (fun a => ∃ f, s f ∧ f i = a)
  sInf_le h _ := sInf_le ⟨_, h, rfl⟩
  le_sInf h i := le_sInf fun _ ⟨f, hf, hi⟩ => hi ▸ h f hf i
  le_sSup h _ := le_sSup ⟨_, h, rfl⟩
  sSup_le h i := sSup_le fun _ ⟨f, hf, hi⟩ => hi ▸ h f hf i

instance piCompleteBooleanAlgebra {ι : Type u} {α : ι → Type v}
    [∀ i, CompleteBooleanAlgebra (α i)] : CompleteBooleanAlgebra ((i : ι) → α i) where
  toCompleteLattice := piCompleteLattice
  compl f i := compl (f i)
  himp f g i := himp (f i) (g i)
  inf_sup_left _ _ _ := funext fun _ => inf_sup_left ..
  inf_compl_eq_bot _ := funext fun _ => inf_compl_eq_bot _
  sup_compl_eq_top _ := funext fun _ => sup_compl_eq_top _
  himp_eq _ _ := funext fun _ => himp_eq ..

@[scoped simp] theorem prop_le (p q : Prop) : (p ≤ q) = (p → q) := rfl
@[scoped simp] theorem prop_inf (p q : Prop) : (p ⊓ q) = (p ∧ q) := rfl
@[scoped simp] theorem prop_sup (p q : Prop) : (p ⊔ q) = (p ∨ q) := rfl
@[scoped simp] theorem prop_himp (p q : Prop) : himp p q = (p → q) := rfl
@[scoped simp] theorem prop_compl (p : Prop) : compl p = ¬p := rfl
@[scoped simp] theorem prop_top : (top : Prop) = True := rfl
@[scoped simp] theorem prop_bot : (bot : Prop) = False := rfl

@[scoped simp] theorem prop_iInf {ι : Sort u} (f : ι → Prop) : iInf f = (∀ i, f i) := by
  apply propext
  exact ⟨fun h i => h _ ⟨i, rfl⟩, fun h _ ⟨i, hi⟩ => hi ▸ h i⟩

@[scoped simp] theorem prop_iSup {ι : Sort u} (f : ι → Prop) : iSup f = (∃ i, f i) := by
  apply propext
  exact ⟨fun ⟨_, ⟨i, hi⟩, h⟩ => ⟨i, hi.symm ▸ h⟩, fun ⟨i, h⟩ => ⟨_, ⟨i, rfl⟩, h⟩⟩

section Pi
variable {ι : Type u} {α : ι → Type v}

theorem pi_le_iff [∀ i, CompleteLattice (α i)] (f g : (i : ι) → α i) :
    (f ≤ g) ↔ ∀ i, f i ≤ g i := Iff.rfl

@[scoped simp] theorem pi_inf_apply [∀ i, CompleteLattice (α i)] (f g : (i : ι) → α i) (i : ι) :
    (f ⊓ g) i = f i ⊓ g i := rfl

@[scoped simp] theorem pi_sup_apply [∀ i, CompleteLattice (α i)] (f g : (i : ι) → α i) (i : ι) :
    (f ⊔ g) i = f i ⊔ g i := rfl

@[scoped simp] theorem pi_top_apply [∀ i, CompleteLattice (α i)] (i : ι) :
    (top : (i : ι) → α i) i = top := rfl

@[scoped simp] theorem pi_bot_apply [∀ i, CompleteLattice (α i)] (i : ι) :
    (bot : (i : ι) → α i) i = bot := rfl

@[scoped simp] theorem pi_compl_apply [∀ i, CompleteBooleanAlgebra (α i)] (f : (i : ι) → α i) (i : ι) :
    compl f i = compl (f i) := rfl

@[scoped simp] theorem pi_himp_apply [∀ i, CompleteBooleanAlgebra (α i)] (f g : (i : ι) → α i) (i : ι) :
    himp f g i = himp (f i) (g i) := rfl

@[scoped simp] theorem pi_iInf_apply [∀ i, CompleteLattice (α i)]
    {κ : Sort w} (f : κ → (i : ι) → α i) (i : ι) :
    iInf f i = iInf (fun k => f k i) := by
  apply le_antisymm
  · exact le_iInf fun k => iInf_le f k i
  · change _ ≤ sInf _
    apply le_sInf
    rintro a ⟨g, ⟨k, rfl⟩, rfl⟩
    exact iInf_le (fun k => f k i) k

@[scoped simp] theorem pi_iSup_apply [∀ i, CompleteLattice (α i)]
    {κ : Sort w} (f : κ → (i : ι) → α i) (i : ι) :
    iSup f i = iSup (fun k => f k i) := by
  apply le_antisymm
  · change sSup _ ≤ _
    apply sSup_le
    rintro a ⟨g, ⟨k, rfl⟩, rfl⟩
    exact le_iSup (fun k => f k i) k
  · exact iSup_le fun k => le_iSup f k i

end Pi

end Loom.Order
