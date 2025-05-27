-- import LoL.Meta
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
  on_done fun (_ : α -> Bool) => ∀ x, ¬ Collection.mem x k do
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


#exit
structure Array' (α : Type u) where
  get : ℕ -> α
  size : ℕ

def Array'.replicate (n : ℕ) (a : α) : Array' α :=
  { get := fun _ => a, size := n }

lemma Array'.replicate_size (n : ℕ) (a : α) : (Array'.replicate n a).size = n := rfl

lemma Array'.replicate_get (n : ℕ) (a : α) (i : ℕ) : (Array'.replicate n a).get i = a := by
  simp [Array'.replicate]

def Array'.modify (a : Array' α) (i : ℕ) (f : α -> α) : Array' α :=
  { get := fun j => if j = i then f (a.get j) else a.get j, size := a.size }

def Array'.sum [AddCommMonoid β] (a : Array' α) (f : α -> β) : β :=
  ∑ i ∈ Finset.range a.size, f (a.get i)

def Array'.sumUpTo [AddCommMonoid α] (a : Array' α) (bound : ℕ) : α :=
  ∑ i ∈ Finset.range bound, a.get i

lemma Array'.sumUpTo_zero [AddCommMonoid α] (a : Array' α) : a.sumUpTo 0 = 0 := by
  simp [Array'.sumUpTo]

open Demonic

noncomputable
instance : MPropOrdered (NonDetT (StateT (Array' ℤ) Id)) (Array' ℤ -> Prop) := by
  apply instMPropOrderedNonDetTOfLawfulMonad



def spmv'' (x_ind : Array' (Array' ℕ)) (x_val : Array' (Array' ℤ)) : NonDetT (StateT (Array' ℤ) Id) Unit := do
  let mut arrInd : Array' ℕ := Array'.replicate x_ind.size 0
  repeat
    decreasing x_ind.sum (·.size) - arrInd.sum id do
    invariant fun acc : Array' ℤ =>
      (∀ i < arrInd.size, acc.get i = (x_val.get i).sumUpTo (arrInd.get i))
    let i :| i < arrInd.size ∧ arrInd.get i < (x_ind.get i).size
    let ind := arrInd.get i
    let val := x_val.get i |>.get ind
    modify (·.modify i (· + val))
    arrInd := arrInd.modify i (· + 1)



lemma spmv''_correct (x_ind : Array' (Array' ℕ)) (x_val : Array' (Array' ℤ)) :
  triple
    (fun acc =>
      ⌜x_ind.size = x_val.size ∧
       ∀ i, acc.get i = 0 ∧
       ∀ i < x_ind.size, (x_ind.get i).size = (x_val.get i).size⌝)
      (spmv'' x_ind x_val)
    (fun _ (acc : Array' ℤ) =>
      ⌜∀ i < x_ind.size, acc.get i = (x_val.get i).sum id⌝) := by
    unfold spmv''
    dsimp
    mwp
    { intro arr; simp; sorry }
    simp [Array'.replicate_size, Array'.replicate_get, Array'.sumUpTo_zero]



-- def spmv' (x_ind : Array' (Array' ℕ)) (x_val : Array' (Array' ℤ)) : NonDetT (StateT (Array' ℤ) Id) Unit := do
--   let mut arrInd : Array' ℕ := Array'.replicate x_ind.size 0
--   while_some i :| i < arrInd.size ∧ arrInd.get i < (x_ind.get i).size do
--     let ind := arrInd.get i
--     let val := x_val.get i |>.get ind
--     modify (·.modify i (· + val))
--     arrInd := arrInd.modify i (· + 1)


-- def spmv (x_ind : Array (Array ℕ)) (x_val : Array (Array ℤ)) : NonDetT (StateT (Array ℤ) Id) Unit := do
--   let mut arrInd : Array ℕ := Array.replicate x_ind.size 0
--   while_some i :| i < arrInd.size ∧ arrInd[i]! < x_ind[i]!.size do
--     modify (·.modify i (· + x_val[i]![arrInd[i]!]!))
--     arrInd := arrInd.modify i (· + 1)
