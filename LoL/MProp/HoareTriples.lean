import Mathlib.Order.CompleteBooleanAlgebra

import LoL.MProp.EffectObservations
import LoL.MProp.Instances

universe u v w

variable {m : Type u -> Type v} [Monad m] [LawfulMonad m] {α : Type u} {l : Type u}

section
variable  [Preorder l]
section
variable [MProp m l]

def wp (c : m α) (post : α -> l) : l := liftM (n := Cont l) c post
def triple (pre : l) (c : m α) (post : α -> l) : Prop :=
  pre ≤ wp c post

abbrev mtriple (pre : m UProp) (c : m α) (post : α -> m UProp) : Prop :=
  triple (MProp.μ pre) c (MProp.μ ∘ post)

omit [Preorder l] in
lemma wp_pure (x : α) (post : α -> l) : wp (m := m) (pure x) post = post x := by
  simp [wp, liftM, lift_pure]
  rfl

lemma triple_pure (pre : l) (x : α) (post : α -> l) :
  triple pre (pure (f := m) x) post <-> pre ≤ (post x)
  := by
    rw [triple, wp]; simp [liftM, lift_pure]; rfl

lemma mtriple_pure (pre : m UProp) (x : α) (post : α -> m UProp) :
  mtriple pre (pure x) post <->
  MProp.μ pre ≤ MProp.μ (post x)
  := by exact triple_pure (MProp.μ pre) x (MProp.μ ∘ post)
end

variable [MPropOrdered m l]

lemma wp_bind {β} (x : m α) (f : α -> m β) (post : β -> l) :
    wp (x >>= f) post = wp x (fun x => wp (f x) post) := by
    simp [wp, liftM]; rw [lift_bind]; rfl

lemma wp_cons (x : m α) (post post' : α -> l) :
  (∀ y, post y ≤ post' y) ->
  wp x post ≤ wp x post' := by
    intros h; simp [wp]; apply Cont.monotone_lift; intros y
    apply h

lemma triple_bind {β} (pre : l) (x : m α) (cut : α -> l)
  (f : α -> m β) (post : β -> l) :
  triple pre x cut ->
  (∀ y, triple (cut y) (f y) post) ->
  triple pre (x >>= f) post := by
    intros; simp [triple, wp_bind]
    solve_by_elim [le_trans', wp_cons]

lemma mtriple_bind {β} (pre : m UProp) (x : m α) (cut : α -> m UProp)
  (f : α -> m β) (post : β -> m UProp) :
  mtriple pre x cut ->
  (∀ y, mtriple (cut y) (f y) post) ->
  mtriple pre (x >>= f) post := by apply triple_bind

theorem triple_forIn_list {α β}
  {xs : List α} {init : β} {f : α → β → m (ForInStep β)}
  (inv : List α → β → m UProp)
  (hstep : ∀ hd tl b,
    mtriple
      (inv (hd :: tl) b)
      (f hd b)
      (fun | .yield b' => inv tl b' | .done b' => inv [] b')) :
  mtriple (inv xs init) (forIn xs init f) (inv []) := by
    induction xs generalizing init
    { simp; rw [mtriple_pure] }
    simp only [List.forIn_cons]
    apply mtriple_bind; apply hstep; intros y
    cases y <;> simp <;> solve_by_elim [(mtriple_pure ..).mpr, le_refl]

theorem μ_bind_wp (c : m α) (mpost : α -> m UProp) :
  MProp.μ (l := l) (c >>= mpost) = wp c (MProp.μ ∘ mpost) := by
    simp [wp, liftM, monadLift, MProp.lift]; apply MProp.bind; ext; simp
    rw [MProp.μ_surjective]

end


section
variable [SemilatticeInf l] [MPropPartialOrder m l]

def spec (pre : l) (post : α -> l) : Cont l α :=
  fun p => pre ⊓ ⌜post ≤ p⌝

def mspec (pre : m UProp) (post : α -> m UProp) : Cont l α :=
  spec (m := m) (MProp.μ pre) (MProp.μ ∘ post)

lemma triple_spec (pre : l) (c : m α) (post : α -> l) :
  spec (m := m) pre post <= wp c <->
  triple pre c post := by
    constructor
    { intro h; unfold triple
      specialize h post; apply le_trans'; apply h
      unfold spec; simp
      apply MPropPartialOrder.μ_top }
    intro t p; unfold spec
    by_cases h: post ≤ p
    { apply inf_le_of_left_le; apply le_trans; apply t
      solve_by_elim [Cont.monotone_lift (x := c)] }
    apply inf_le_of_right_le; apply le_trans'; apply MPropPartialOrder.μ_bot (m := m)
    apply MPropPartialOrder.μ_ord_pure; solve_by_elim

lemma mtriple_mspec (pre : m UProp) (c : m α) (post : α -> m UProp) :
  mspec pre post ≤ wp c <-> mtriple pre c post := by apply triple_spec

-- class abbrev MonadLogic (m : Type u -> Type v) (l : Type u) [Monad m] := Logic l, MPropPartialOrder m l
end

section
variable [inst: CompleteBooleanAlgebra l] [MPropPartialOrder m l]

instance : SemilatticeInf l := inst.toSemilatticeInf

omit [LawfulMonad m] in
@[simp]
lemma trueE : ⌜True⌝ = ⊤ := by
  apply le_antisymm; exact OrderTop.le_top ⌜True⌝
  apply MPropPartialOrder.μ_top

omit [LawfulMonad m] in
@[simp]
lemma falseE : ⌜False⌝ = ⊥ := by
  apply le_antisymm; apply MPropPartialOrder.μ_bot
  simp

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

def wlp (c : m α) (post : α -> l) : l := (wp c postᶜ)ᶜ ⊔ wp c post

lemma wp_and [MPropDetertministic m l] (c : m α) (post₁ post₂ : α -> l) :
  wp c (fun x => post₁ x ⊓ post₂ x) = wp c post₁ ⊓ wp c post₂ := by
  apply le_antisymm
  { simp; constructor <;> apply wp_cons <;> simp }
  have h := MPropDetertministic.demonic (l := l) (ι := ULift Bool) (c := c) (p := fun | .up true => post₁ | .up false => post₂)
  simp at h
  apply le_trans; apply le_trans'; apply h
  { simp [wp]; constructor; exact inf_le_right
    exact inf_le_left }
  apply wp_cons (m := m); simp; intros; constructor
  { refine iInf_le_of_le true ?_; simp }
  refine iInf_le_of_le false ?_; simp

lemma wp_iInf {ι : Type u} [Nonempty ι] [MPropDetertministic m l] (c : m α) (post : ι -> α -> l) :
  wp c (fun x => ⨅ i, post i x) = ⨅ i, wp c (post i) := by
    apply le_antisymm
    { refine le_iInf ?_; intros i; apply wp_cons; intro y
      exact iInf_le (fun i ↦ post i y) i }
    apply MPropDetertministic.demonic (ι := ι) (m := m) (c := c) (p := post)

lemma wp_or [MPropDetertministic m l] (c : m α) (post₁ post₂ : α -> l) :
  wp c (fun x => post₁ x ⊔ post₂ x) = wp c post₁ ⊔ wp c post₂ := by
  apply le_antisymm
  { apply MPropDetertministic.angelic }
  simp; constructor <;> apply wp_cons <;> simp

@[simp]
lemma wlp_true (c : m α) : wlp c (fun _ => ⊤) = ⊤ := by
  simp [wlp]; rw [@eq_top_iff, sup_comm, <-himp_eq]; simp
  apply wp_cons; simp

@[simp]
lemma wlp_pure (x : α) (post : α -> l) :
  wlp (pure (f := m) x) post = post x := by
    simp [wlp, wp_pure, triple_pure]

omit [LawfulMonad m] in
lemma wp_wlp (c : m α) (post : α -> l) :
  wp c post <= wlp c post := by
    simp [wlp, wp]

variable [MPropDetertministic m l]

lemma wlp_and (c : m α) (post₁ post₂ : α -> l) :
  wlp c (fun x => post₁ x ⊓ post₂ x) = wlp c post₁ ⊓ wlp c post₂ := by
  simp [wlp]; apply le_antisymm
  { simp [wp_or, wp_and]; repeat' constructor
    { apply le_sup_of_le_left; apply inf_le_of_left_le; rfl }
    { apply le_sup_of_le_right; apply inf_le_of_left_le; rfl }
    { apply le_sup_of_le_left; apply inf_le_of_right_le; rfl }
    apply le_sup_of_le_right; apply inf_le_of_right_le; rfl }
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
    { rw [<-compl_compl (x := wp c post'ᶜ ⊓ (wp c post')ᶜ)]
      rw [<-himp_eq]; simp; rw [@inf_sup_left]; simp [<-wp_and]
      apply wp_cons; simp }
    rw [<-le_himp_iff, himp_eq]; simp
    refine le_sup_of_le_left ?_
    refine le_sup_of_le_right ?_
    simp


end
