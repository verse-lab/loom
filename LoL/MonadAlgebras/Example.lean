-- import LoL.Meta
import LoL.MonadAlgebras.NonDetT.Extract
import LoL.MonadAlgebras.WP.Tactic

instance {α : Type u} (p : α -> Prop) [Findable p] : Decidable (∃ a, p a) := by
  apply decidable_of_bool (Findable.find p).isSome
  constructor
  { simp [Option.isSome_iff_exists]; intros x _
    exists x; solve_by_elim [Findable.find_some_p] }
  simp; intro x px
  false_or_by_contra; rename_i h
  simp [<-Option.isNone_iff_eq_none] at h
  have h := Findable.find_none (p := p) h
  aesop

open Demonic

noncomputable
instance : MPropOrdered (NonDetDevT (StateT α Option)) (α -> Prop) := by
  exact Demonic.instMPropOrderedNonDetDevTOfLawfulMonad

@[spec, wpSimp]
def WPGen.modify f : WPGen (modify f : NonDetDevT (StateT α Option) PUnit) := by
  refine ⟨fun post s => post .unit (f s), True, ?_⟩
  intro post _; apply le_of_eq; rfl

@[spec, wpSimp]
def WPGen.pickSuchThat : WPGen (pickSuchThat τ p : NonDetDevT (StateT α Option) τ) := by
  refine ⟨fun post s => ∀ t, p t -> post t s, True, ?_⟩
  intro post _; apply le_of_eq;
  simp [NonDetDevT.wp_eq_wp, MonadNonDetDev.pickSuchThat, NonDetDevT.pickSuchThat, NonDetDevT.wp]
  simp [logicSimp]; aesop

attribute [aesop safe cases] Decidable
attribute [-simp] if_true_left Bool.if_true_left ite_eq_left_iff
attribute [logicSimp] ite_self

instance [Repr α] [FinEnum α] : Repr (α -> Bool) where
  reprPrec p := fun n => Repr.reprPrec (FinEnum.toList α |>.map fun x => (x, p x)) n


class Collection (α : outParam (Type)) (κ : Type) where
  mem : α -> κ -> Prop
  [dec : DecidableRel mem]
  del : α -> κ -> κ
  mem_del {b a} k : mem b (del a k) = (mem b k ∧ b ≠ a)

variable {α κ} [col : Collection α κ] [DecidableEq α] [∀ k, Findable (Collection.mem · (α := α) (κ := κ) k)]

instance : DecidableRel (Collection.mem (α := α) (κ := κ)) := Collection.dec

instance [DecidableEq α] : Collection α (List α) where
  mem := (· ∈ ·)
  del x k := List.filter (· ≠ x) k
  mem_del := by simp

def Collection.toSet (k₀ : κ) : NonDetDevT (StateT (α -> Bool) Option) Unit := do
  let mut k := k₀
  while_some a :| Collection.mem a k
  invariant fun (s : α -> Bool) => ∀ x, Collection.mem x k₀ <-> s x ∨ Collection.mem x k
  on_done fun (_ : α -> Bool) => ∀ x, ¬ Collection.mem x k do
    k := del a k
    modify (fun s a' => if a' = a then true else s a')

/-- info: some (Except.ok (), [(0, false), (1, true), (2, true), (3, false)]) -/
#guard_msgs in
#eval Collection.toSet [(1 : Fin 4),(2 : Fin 4)] |>.run.run.run (fun _ => False)

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
