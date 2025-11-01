import Mathlib.Logic.Function.Basic
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.Lattice
import Mathlib.Order.Basic
import Mathlib.Data.W.Basic
import Mathlib.Data.FinEnum

inductive AccFrom (p : Nat -> Prop) : Nat -> Prop
    | now : p i -> AccFrom p i
    | later : ¬ p i -> AccFrom p (i + 1) -> AccFrom p i


def findNat (p : Nat -> Prop) [DecidablePred p] : Option Nat :=
  let rec aux i :=
    if p i then
      some i
    else
      aux (i + 1)
  partial_fixpoint
  aux 0

lemma AccFrom_findNat (p : Nat -> Prop) [DecidablePred p] (i : Nat) :
  AccFrom p i -> (findNat.aux p i).isSome := by
  intros h; unhygienic induction h <;> (unfold findNat.aux; aesop)

lemma AccFrom_of_p (p : Nat -> Prop) [DecidablePred p] (i : Nat) :
  p i -> ∀ j ≤ i, AccFrom p j := by
  intro pi j h
  unhygienic induction h using Nat.decreasingInduction <;> try solve_by_elim
  by_cases p k; solve_by_elim
  apply AccFrom.later <;> solve_by_elim

lemma exists_findNat (p : Nat -> Prop) [DecidablePred p] :
  (∃ x, p x) ↔ (findNat p).isSome := by
  constructor
  { rintro ⟨x, px⟩
    apply AccFrom_findNat; apply AccFrom_of_p <;> aesop }
  simp [Option.isSome_iff_exists]; intro i eq; exists i; revert eq
  unfold findNat; generalize 0 = m;
  apply findNat.aux.partial_correctness; aesop

lemma findNat_none (p : Nat -> Prop) [DecidablePred p] :
  (findNat p).isNone -> ∀ i, ¬ p i := by
  simp; rw [<-Option.not_isSome_iff_eq_none, <-exists_findNat]; simp

lemma findNat_aux_some_le (p : Nat -> Prop) [DecidablePred p] (i : Nat) :
  findNat.aux p i = some j -> ∀ k, i <= k -> k < j -> ¬ p k := by
  apply findNat.aux.partial_correctness
  intro aux ih i r; split
  { rintro ⟨⟩ ph; omega }
  intro h; have:= ih _ _ h;
  intros k _ _ pk; apply this k <;> try omega
  by_cases h : k = i; aesop; omega

lemma findNat_some_p (p : Nat -> Prop) [DecidablePred p] (i : Nat) :
  findNat p = some i -> p i := by
  simp [findNat]; generalize 0 = m;
  apply findNat.aux.partial_correctness; aesop

lemma p_findNat_some (p : Nat -> Prop) [DecidablePred p] (i : Nat) :
  p i -> ∃ j, p j ∧ j <= i ∧ findNat p = some j := by
  intro pi;
  have : (findNat p).isSome := by
    false_or_by_contra; rename_i h
    simp at h
    rw [←Option.isNone_iff_eq_none] at h
    have h := findNat_none _ h
    aesop
  revert this; simp [Option.isSome_iff_exists]
  intro x h
  have := findNat_aux_some_le p 0 h
  exists x; repeat' constructor
  { solve_by_elim [findNat_some_p] }
  { have h := fun h₁ h₂ => this _ h₁ h₂ pi
    simp at h; exact h }
  solve_by_elim

def find [Encodable α] (p : α -> Prop) [DecidablePred p] : Option α :=
  findNat (fun x => (Encodable.decode x).any (p ·)) |>.bind Encodable.decode

lemma find_none (p : α -> Prop) [DecidablePred p] [Encodable α] :
  (find p).isNone -> ∀ x, ¬ p x := by
  simp [find]; intro h a pa
  have := p_findNat_some (fun x => (Encodable.decode x).any (p ·)) (Encodable.encode a) ?_
  { rcases this with ⟨j, pj, hj, eq⟩; simp [eq] at h;
    simp [h] at pj }
  simpa

lemma find_some_p (p : α -> Prop) [DecidablePred p] [Encodable α] (x : α) :
  find p = some x -> p x := by
  simp [find, Option.bind]; split; simp
  have := findNat_some_p _ _ (by assumption)
  intro eq; rw [eq] at this; simp at this; exact this

class WeakFindable {α : Type u} (p : α -> Prop) where
  find : Unit -> Option α
  find_some_p : find () = some x -> p x

class Findable {α : Type u} (p : α -> Prop) where
  find : Unit -> Option α
  find_none : (find ()).isNone -> ∀ x, ¬ p x
  find_some_p : find () = some x -> p x

instance WeakFindable.of_Findable {α : Type u} (p : α -> Prop) [Findable p] : WeakFindable p where
  find := Findable.find p
  find_some_p := Findable.find_some_p

instance {p : α -> Prop} [Encodable α] [DecidablePred p] : Findable p where
  find := fun _ =>find p
  find_none := find_none p
  find_some_p := find_some_p p _

@[instance high]
instance {p : α -> Prop} [FinEnum α] [DecidablePred p] : Findable p where
  find := fun _ => FinEnum.toList α |>.find? p
  find_none := by simp
  find_some_p := by intro x h; have := List.find?_some h; aesop

@[instance high]
instance {α : Type u} [Inhabited α] : Findable (α := α) (fun _ => True) where
  find := fun _ => some default
  find_none := by simp
  find_some_p := by simp
