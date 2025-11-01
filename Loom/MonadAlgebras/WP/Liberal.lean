import Mathlib.Order.CompleteBooleanAlgebra

import Loom.MonadAlgebras.Defs
import Loom.MonadAlgebras.WP.Basic

import Loom.MonadAlgebras.Instances.Basic
import Loom.MonadAlgebras.Instances.ExceptT

variable {m : Type u -> Type v} [Monad m] [LawfulMonad m] {α : Type u} {l : Type u}
variable [inst: CompleteBooleanAlgebra l] [mprop: MAlgOrdered m l]

attribute [simp] trueE falseE
@[local simp]
private lemma compl_fun {α} (x y : α -> l) :
  (fun a => x a ⊔ y a)ᶜ = (fun a => (x a)ᶜ ⊓ (y a)ᶜ) := by simp [compl]

@[local simp]
private lemma compl_fun' {α} (x y : α -> l) :
  (fun a => x a ⊓ y a)ᶜ = (fun a => (x a)ᶜ ⊔ (y a)ᶜ) := by simp [compl]

@[local simp]
private lemma compl_fun'' {α} (x : α -> l) :
  (fun a => (x a)ᶜ) = xᶜ := by simp [compl]


@[local simp]
private lemma compl_fun_true {α} :
  (fun (_ : α) => ⊤)ᶜ = fun _ => (⊥ : l) := by simp [compl]

abbrev iwp (c : m α) : Cont l α := Cont.inv (wp c)

omit [LawfulMonad m] in
@[simp]
lemma iwp_eq (c : m α) (post : α -> l) :
  iwp c post = (wp c postᶜ)ᶜ := by
    simp [iwp, Cont.inv]

def wlp (c : m α) (post : α -> l) : l := iwp c post ⊔ wp c post

@[simp]
lemma wlp_true (c : m α) : wlp c (fun _ => ⊤) = ⊤ := by
  simp [wlp]; rw [@eq_top_iff, sup_comm, <-himp_eq]; simp
  apply wp_cons; simp

@[simp]
lemma wlp_pure (x : α) (post : α -> l) :
  wlp (pure (f := m) x) post = post x := by
    simp [wlp, wp_pure]

omit [LawfulMonad m] in
lemma wp_wlp (c : m α) (post : α -> l) :
  wp c post <= wlp c post := by
    simp [wlp, wp]

section Determinism
variable [MAlgDet m l]

lemma wlp_and (c : m α) (post₁ post₂ : α -> l) :
  wlp c (fun x => post₁ x ⊓ post₂ x) = wlp c post₁ ⊓ wlp c post₂ := by
  simp [wlp]; apply le_antisymm
  { simp [wp_or, wp_and] }
  rw (occs := .pos [3]) [sup_comm]; rw [<-himp_eq]; simp
  rw [inf_inf_distrib_right]
  conv =>
    enter [1,1]
    rw [inf_sup_right, <-wp_and];
    simp [inf_sup_left]; rw [wp_or, inf_sup_left]; simp
    erw [wp_and, <-inf_sup_right]
  conv =>
    enter [1,2]
    rw [inf_sup_right, <-wp_and];
    simp [inf_sup_left]; rw [wp_or, inf_sup_left]; simp
    erw [wp_and, <-inf_sup_right]
  rw (occs := .pos [3]) [inf_comm]
  rw [inf_assoc]
  rw (occs := .pos [2]) [<-inf_assoc]
  rw (occs := .pos [3]) [inf_comm]
  repeat rw [<-inf_assoc]
  rw [inf_sup_right, <-wp_and]; simp
  apply inf_le_of_left_le
  apply inf_le_of_left_le
  apply wp_cons; simp

lemma wlp_bind {β} (x : m α) (f : α -> m β) (post : β -> l) :
  wlp (x >>= f) post = wlp x (fun x => wlp (f x) post) := by
  simp [wlp, wp_bind]; apply le_antisymm
  { simp [wp_and, wp_or]; constructor
    { repeat apply le_sup_of_le_left; simp }
    repeat apply le_sup_of_le_right; simp }
  simp [wp_and, wp_or]; constructor
  { rw [<-compl_compl (x := wp x fun a ↦ wp (f a) post)]
    rw [<-himp_eq, le_himp_iff, ← compl_sup, <-wp_or]
    simp; apply wp_cons; simp }
  rw [sup_comm]; simp [<-himp_eq, <-wp_and]
  apply wp_cons; simp


lemma wlp_himp (c : m α) (post post' : α -> l) :
  wp c (fun x => post' x ⇨ post x) = wlp c post' ⇨ wp c post := by
    rw [himp_eq, wlp]; simp [himp_eq, wp_or]
    apply le_antisymm <;> simp
    rw [<-compl_compl (x := wp c post'ᶜ ⊓ (wp c post')ᶜ)]
    rw [<-himp_eq]; simp; rw [@inf_sup_left]; simp [<-wp_and]
    apply wp_cons; simp

lemma wlp_join_wp (c : m α) (post post' : α -> l) :
  wlp c post ⊓ wp c post' = wp c (fun x => post x ⊓ post' x) := by
  apply le_antisymm
  { rw [← @le_himp_iff', <-wlp_himp];
    apply wp_cons; simp }
  simp; constructor
  { apply le_trans'; apply wp_wlp; apply wp_cons; simp }
  apply wp_cons; simp

lemma wp_top_wlp (c : m α) (post : α -> l) :
  wp c ⊤ ⊓ wlp c post = wp c post := by
  rw [inf_comm, wlp_join_wp]; simp

omit [MAlgDet m l] in
lemma wlp_cons (c : m α) (post post' : α -> l) :
  post <= post' ->
  wlp c post <= wlp c post' := by
    intro; unfold wlp iwp; simp; constructor
    { refine le_sup_of_le_left ?_; simp; apply wp_cons; simp; solve_by_elim }
    solve_by_elim [le_sup_of_le_right, wp_cons]

lemma wp_top_iwp (c : m α) (post : α -> l) :
  wp c ⊥ = ⊥ ->
  wp c ⊤ ⊓ iwp c post = wp c post := by
  intro wpb
  apply le_antisymm
  { simp; simp [<-le_himp_iff, himp_eq, <-wp_or]; rfl }
  simp; constructor
  { apply wp_cons; simp }
  rw [@le_compl_iff_disjoint_left]; intro _ _ _
  apply le_trans'; rewrite [<- wpb];
  rw [<-compl_inf_eq_bot (a := post)]
  erw [wp_and]; simp; solve_by_elim

set_option quotPrecheck false in
notation "[totl|" t "]" => open ExceptionAsFailure in t
set_option quotPrecheck false in
notation "[part|" t "]" => open ExceptionAsSuccess in t
set_option quotPrecheck false in
notation "[handler" hd "|" t "]" => have : IsHandler hd := ⟨⟩; t

lemma wp_tot_part ε (c : ExceptT ε m α) post :
  [totl| wp c ⊤] ⊓ [part| wp c post] = [totl| wp c post] := by
  rw [wp_part_eq, wp_tot_eq, wp_tot_eq, <-wp_and]
  congr; ext x; cases x <;> simp

lemma wp_compl (c : m α) post (wp_bot : ∀ α (c : m α), wp c ⊤ = ⊤) :
  (wp c postᶜ)ᶜ <= wp c post := by
    refine compl_le_iff_compl_le.mp ?_
    rw [← @codisjoint_iff_compl_le_right]; intro b
    rw [<-wp_bot (c := c)]; intros; apply le_trans
    apply wp_cons; intro a; apply BooleanAlgebra.top_le_sup_compl (x := post)
    erw [wp_or]; simp_all

lemma wp_compl'  (c : m α) post (wp_bot : ∀ α (c : m α), wp c ⊥ = ⊥) :
  wp c post <= (wp c postᶜ)ᶜ := by
  have : wp c post = ⊤ ⊓ wp c post := by simp
  rw [this, <-le_himp_iff, himp_eq]; rw [← @compl_inf, <-wp_and]; simp
  solve_by_elim

-- lemma wp_tot_eq_iwp_part ε (c : ExceptT ε m α) (post : α -> l)
--    (wp_bot : ∀ α (c : m α), wp c ⊥ = ⊥)
--    (wp_top : ∀ α (c : m α), wp c ⊤ = ⊤) :
--    [totl| wp c post] = [part| iwp c post] := by
--     simp only [iwp, wp_tot_eq, wp_part_eq]
--     apply le_antisymm <;> try simp
--     { apply le_trans; apply wp_compl'; simp [*]
--       simp; apply wp_cons (x := c); rintro (_|_) <;> simp }
--     apply le_trans'; apply wp_compl; simp [*]
--     simp; apply wp_cons; rintro (_|_) <;> simp

private lemma le_coml_sup (x y z : l) :
  y <= x ⊔ z -> xᶜ <= yᶜ ⊔ z := by
  intro h;
  rw [sup_comm, <-himp_eq]; simp
  rw [inf_comm, <-le_himp_iff, himp_eq]; simp
  rwa [sup_comm]

lemma wlp_part_wlp_handler ε (α : Type u) (c : ExceptT ε m α) (post : α → l) (hd : ε -> Prop) :
  [part| wlp c post] =
  [handler hd| wlp c post] := by
    simp [wlp, wp_part_eq, wp_except_handler_eq]
    apply le_antisymm <;> simp
    { constructor
      { apply le_coml_sup; rw [<-wp_or]; apply wp_cons
        rintro (_|_) <;> simp }
      rw [sup_comm, <-himp_eq]; simp [<-wp_and]
      apply wp_cons; rintro (_|_) <;> simp }
    constructor
    { apply le_coml_sup; rw [<-wp_or]; apply wp_cons
      rintro (_|_) <;> simp }
    rw [sup_comm, <-himp_eq]; simp [<-wp_and]
    apply wp_cons; rintro (_|_) <;> simp

lemma TotalCorrectness.DivM.wlp_eq (α : Type) (x : DivM α) (post : α -> Prop) :
  (open TotalCorrectness in wlp x post) = (open PartialCorrectness in wp x post) := by
  simp [wlp, TotalCorrectness.DivM.wp_eq, PartialCorrectness.DivM.wp_eq]
  split <;> simp

lemma PartialCorrectness.DivM.wlp_eq (α : Type) (x : DivM α) (post : α -> Prop) :
  wlp x post = wp x post := by
  simp [wlp, PartialCorrectness.DivM.wp_eq]
  split <;> simp

omit [MAlgDet m l] in
lemma StateT.wlp_eq (c : StateT σ m α) (post : α -> σ -> l) :
  wlp c post = fun s => wlp (m := m) (c s) (fun xs => post xs.1 xs.2) := by
  simp [wlp, StateT.wp_eq]; rfl

omit [MAlgDet m l] in
lemma ReaderT.wlp_eq (c : ReaderT σ m α) (post : α -> σ -> l) :
  wlp c post = fun s => wlp (m := m) (c s) (post · s) := by
  simp [wlp, ReaderT.wp_eq]; rfl

lemma ExceptT.wlp_eq (c : ExceptT ε m α) (post : α -> l) :
  [totl| wlp c post] = [part| wlp c post] := by
  rw [wlp_part_wlp_handler]
