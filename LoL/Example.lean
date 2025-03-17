import LoL.MProp.HoareTriples
import LoL.Meta
import LoL.Tactic


lemma monadMap_if {α : Type} {m n} [inst: MonadLiftT m n] (t e : m α) (p : Prop) [Decidable p] :
  monadLift (n:= n) (if p then t else e) = if p then monadLift t else monadLift e := by split <;> rfl

@[wpSimp]
lemma if_app {α β} p [Decidable p] (t e : α -> β)  : (if p then t else e) = fun x => if p then t x else e x := by
  split <;> rfl
@[wpSimp]
lemma bindE {α β} : bind (α := α) (β := β) (m := Cont (Nat -> Prop)) = (fun x f g ↦ x fun a ↦ f a g) := by rfl

    -- Lean.Elab.Tactic.evalTactic `(tactic| (
    --   unfold Function.comp; dsimp
    --   rw [MProp.μ_lift]; simp only [MProp.μ_pure];
    --   unfold liftM; simp only [monadMapBind, monadMap_if]; simp only [monadLift]
    --   ))

namespace Tot
open TotalCorrectness

abbrev myM := StateT Nat (ExceptT String Id)
/-
  pre/post := Nat -> Prop

  μ : myM Prop -> pre/post
-/

#gen_spec getE                           for MProp.lift (m := myM) get
#gen_spec setE (s : Nat)                 for MProp.lift (m := myM) <| set s
#gen_spec throwE (α : Type) (e : String) for MProp.lift (m := myM) <| throw (α := α) e
#gen_spec pureE (α : Type) (x : α)       for MProp.lift (m := myM) <| pure x

#print throwE

def decr (n : Nat) : myM Unit := do
  let s <- get
  if n > s then throw "error"
  set (s - n)

lemma decr_spec (n sOld : Nat) :
  mtriple
    do { let s <- get; return n <= s ∧ s = sOld }
    (decr n)
    fun _ => do { let s <- get; return s + n = sOld } := by
    -- prepare the goal
    simp only [mtriple, triple, wp, decr]
    -- propagate the lifting into Specification monad
    simp_lift Tot.myM
    -- simplify basic monadic operations
    simp [wpSimp]
    -- simplify logic implication
    intros s; simp

    -- actual proof
    omega


lemma decr_spec' (n sOld : Nat) :
  triple
    (fun s => n <= s ∧ s = sOld)
    (decr n)
    (fun _ s => s + n = sOld) := by sorry

end Tot

export Tot (decr myM)

namespace Part
open PartialCorrectness

#gen_spec getE                           for MProp.lift (m := myM) get
#gen_spec setE (s : Nat)                 for MProp.lift (m := myM) <| set s
#gen_spec throwE (α : Type) (e : String) for MProp.lift (m := myM) <| throw (α := α) e
#gen_spec pureE (α : Type) (x : α)       for MProp.lift (m := myM) <| pure x

lemma decr_spec (n s : Nat) :
  mtriple
    do { return (<- get) = s }
    (decr n)
    fun _ => do { return (<- get) <= s } := by
    -- prepare the goal
    simp only [mtriple, triple, wp, decr]
    -- propagate the lifting into Specification monad
    simp_lift myM
    -- simplify basic monadic operations
    simp [wpSimp]
    -- simplify logic implication
    intros s; simp

    -- actual proof
    omega

end Part

namespace NonDet
open TotalCorrectness
open DemonicChoice

abbrev myM := StateT Nat (ExceptT String NonDetM)

#gen_spec getE                           for MProp.lift (m := myM) get
#gen_spec setE (s : Nat)                 for MProp.lift (m := myM) <| set s
#gen_spec throwE (α : Type) (e : String) for MProp.lift (m := myM) <| throw (α := α) e
#gen_spec pureE (α : Type) (x : α)       for MProp.lift (m := myM) <| pure x

#gen_spec moreE (α : Type) (x : α) (m : NonDetM α) for MProp.lift (m := myM) <| (StateT.lift $ ExceptT.lift $ NonDetM.more x (fun _ => m))
#gen_spec noneE (α : Type) for MProp.lift (m := myM) <| (StateT.lift $ ExceptT.lift $ NonDetM.none (α := α))
#gen_spec chooseEE (α : Type) (xs : List α) for MProp.lift <| choose (m := myM) xs
@[wpSimp high]
lemma chooseE {α} (xs : List α) : (MProp.lift <| choose (m := myM) xs) = fun f s => ∀ x ∈ xs, f x s := by
  induction xs <;> simp [choose, NonDetM.choose]
  { rfl }
  erw [moreE]; simp; ext f s; simp; intros h
  rename_i ih; simp [funext_iff] at ih; rw [<-ih]; rw [chooseEE]

def decr' (n : Nat) : myM Unit := do
  let n <- choose <| List.range <| n + 1
  let s <- get
  if n > s then throw "error"
  set (s - n)

-- myM Prop

lemma decr_spec (n s : Nat) :
  mtriple
    do { return (<- get) = s ∧ n <= s }
    (decr' n)
    fun _ => do { return (<- get) <= s } := by
    -- prepare the goal
    simp only [mtriple, triple, wp, decr']
    -- propagate the lifting into Specification monad
    simp_lift NonDet.myM
    -- simplify basic monadic operations
    simp [wpSimp]
    -- simplify logic implication
    intros s; simp

    -- actual proof
    omega
