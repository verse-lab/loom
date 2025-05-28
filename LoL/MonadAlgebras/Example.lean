import Mathlib.Algebra.BigOperators.Intervals

import LoL.MonadAlgebras.NonDetT.Extract
import LoL.MonadAlgebras.WP.Tactic

import LoL.Meta

open PartialCorrectness DemonicChoice

@[spec, wpSimp]
def WPGen.modify f : WPGen (l := α -> Prop) (modify f : NonDetT (StateT α DevM) PUnit) := by
  refine ⟨fun post s => post .unit (f s), True, ?_⟩
  intro post _; apply le_of_eq; rfl

@[spec, wpSimp]
def WPGen.pickSuchThat : WPGen (pickSuchThat τ p : NonDetT (StateT α DevM) τ) := by
  refine ⟨fun post s => ∀ t, p t -> post t s, True, ?_⟩
  intro post _; apply le_of_eq;
  simp [MonadNonDet.wp_pickSuchThat, logicSimp]; aesop

attribute [aesop safe cases] Decidable
attribute [-simp] if_true_left Bool.if_true_left ite_eq_left_iff
attribute [logicSimp] ite_self

instance [Repr α] [FinEnum α] : Repr (α -> Bool) where
  reprPrec p := fun n => Repr.reprPrec (FinEnum.toList α |>.map fun x => (x, p x)) n

instance : Repr (ℕ -> Bool) where
  reprPrec p := fun n => Repr.reprPrec (List.range 10 |>.map fun x => (x, p x)) n

section
class Collection (α : outParam (Type)) (κ : Type) where
  mem : α -> κ -> Prop
  [dec : DecidableRel mem]
  del : α -> κ -> κ
  mem_del {b a} k : mem b (del a k) = (mem b k ∧ b ≠ a)
  isEmpty : κ -> Prop
  [dec_isEmpty : DecidablePred isEmpty]
  isEmpty_prop : ∀ k, isEmpty k = ∀ x, ¬ mem x k

variable {α κ} [col : Collection α κ] [DecidableEq α]

instance : DecidableRel (Collection.mem (α := α) (κ := κ)) := Collection.dec
instance : DecidablePred (Collection.isEmpty (α := α) (κ := κ)) := Collection.dec_isEmpty

instance [DecidableEq α] : Collection α (List α) where
  mem := (· ∈ ·)
  del x k := List.filter (· ≠ x) k
  mem_del := by simp
  isEmpty := (List.isEmpty ·)
  isEmpty_prop := by simp [List.eq_nil_iff_forall_not_mem]

def Collection.toSet (k₀ : κ) : NonDetT (StateT (α -> Bool) DevM) Unit := do
  let mut k := k₀
  while ¬ Collection.isEmpty k
  invariant fun (s : α -> Bool) => ∀ x, Collection.mem x k₀ <-> s x ∨ Collection.mem x k
  on_done ⌜∀ x, ¬ Collection.mem x k⌝ do
    let a :| Collection.mem a k
    k := del a k
    modify (fun s a' => if a' = a then true else s a')
    pure ()

/--
info: DevM.res
  ((),
   [(0, false),
    (1, true),
    (2, true),
    (3, false),
    (4, false),
    (5, true),
    (6, false),
    (7, false),
    (8, false),
    (9, false)])
-/
#guard_msgs in
#eval Collection.toSet [1,2,5] |>.run.run (fun _ => False)

lemma Collection.toSet_correct (k : κ) :
  triple (fun s => ∀ x, ¬ s x) (Collection.toSet k) (fun _ s => ∀ x, Collection.mem x k <-> s x) := by
  cases col;
  unfold Collection.toSet; dsimp
  mwp
  { intro k'; mwp; aesop }
  aesop
end

attribute [aesop unsafe 20% apply] le_antisymm

@[simp]
lemma Array.replicate_get (n : ℕ) [Inhabited α] (a : α) (i : ℕ) (_ : i < n := by omega) :
  (Array.replicate n a)[i]! = a := by
  rw [getElem!_pos, Array.getElem_replicate]; aesop

@[simp]
lemma Array.modify_get (a : Array α) [Inhabited α] (i j : ℕ) (f : α -> α) :
  (a.modify i f)[j]! = if j < a.size then if j = i then f a[j]! else a[j]! else default := by
  by_cases h : j < a.size
  { (repeat rw [getElem!_pos]) <;> try solve | aesop
    rw [@getElem_modify]; aesop }
  repeat rw [getElem!_neg]
  all_goals (try split) <;> solve | omega | aesop



def Array.sumUpTo [Inhabited α] [AddCommMonoid β] (a : Array α) (f : ℕ -> α -> β) (bound : ℕ) : β :=
  ∑ i ∈ Finset.range bound, f i a[i]!

@[simp]
lemma Array.sumUpToSucc [Inhabited α] [AddCommMonoid α] (a : Array α) (f : ℕ -> α -> α) (bound : ℕ) :
  a.sumUpTo f (bound + 1) = a.sumUpTo f bound + f bound a[bound]! := by
  simp [sumUpTo]
  rw [@Finset.sum_range_succ]

open DemonicChoice PartialCorrectness

variable (mInd : Array (Array ℕ))  (mVal : Array (Array ℤ))
variable (v : Array ℤ)
variable (size_eq : mInd.size = mVal.size)
variable (size_eq' : ∀ i < mInd.size, (mInd[i]!).size = (mVal[i]!).size)
include size_eq size_eq'


def spmv : NonDetT (StateT (Array ℤ) DevM) Unit := do
  let mut arrInd : Array ℕ := Array.replicate mInd.size 0
  while_some i :| i < arrInd.size ∧ arrInd[i]! < mInd[i]!.size
  invariant ⌜arrInd.size = mVal.size⌝
  invariant ⌜∀ i < arrInd.size, arrInd[i]! <= (mInd[i]!).size⌝
  invariant (·.size = mVal.size)
  invariant (∀ i < arrInd.size, ·[i]! = mVal[i]!.sumUpTo (fun j x => x * v[mInd[i]![j]!]!) arrInd[i]!)
  on_done ⌜∀ i < arrInd.size, arrInd[i]! = mInd[i]!.size⌝ do
    let ind := arrInd[i]!
    let vInd := mInd[i]![ind]!
    let mVal := mVal[i]![ind]!
    let val := mVal * v[vInd]!
    modify (·.modify i (· + val))
    arrInd := arrInd.modify i (· + 1)

lemma spmv_correct :
  triple
    (fun acc => ⌜acc.size = mVal.size ∧ ∀ i : ℕ, acc[i]! = 0⌝)
      (spmv mInd mVal v)
    (fun _ acc =>
      ⌜∀ i < mInd.size, acc[i]! = mVal[i]!.sumUpTo (fun j x => x * v[mInd[i]![j]!]!) mInd[i]!.size⌝) := by
    unfold spmv; mwp
    { intro arrInd
      mwp; aesop }
    aesop
