import Mathlib.Logic.Function.Basic
import Aesop
import LoL.QuotientExtra
import LoL.Meta


universe u v w

class Sample (α : Type u) (P : α -> Prop) where
  gen : Array α
  prop : ∀ a ∈ gen, P a



structure NonDetM (α : Type u) where
  tpc : (α -> Type u) -> Type v
  pre (cont : (a : α) -> τ a -> Prop) : tpc τ -> Prop
  val {β : Type u} (cont : (a : α) -> τ a -> β) : tpc τ → β
  sample (cont : (a : α) -> τ a -> Prop) [samp : ∀ a : α, Sample (τ a) (cont a)] : Sample (tpc τ) (pre cont)



variable {α β : Type u}

def NonDetM.pure (x : α) : NonDetM α := {
  tpc := (· x),
  pre := (· x),
  val := (· x),

  sample _ samp := samp x
}

def NonDetM.bind (x : NonDetM α) (f : α → NonDetM β) : NonDetM β := {
  tpc := fun τ => x.tpc fun a => (f a).tpc τ,
  pre cont := x.pre fun a ft => (f a).pre cont ft
  val cont := x.val fun a ft => (f a).val cont ft

  sample {τ} cont samp := by 
    simp; apply @x.sample _ _ fun a => (f a).sample ..
}

instance : Monad NonDetM where
  pure := NonDetM.pure
  bind := NonDetM.bind


def Array.pairs {β : α -> Type u} (a₁ : Array α) (a₂ : (a : α) -> Array (β a)) : Array ((a : α) × β a) := Id.run do
  let mut res := #[]
  for a in a₁ do 
    for b in a₂ a do
      res := res.push ⟨a, b⟩
  return res


abbrev NonDetM.pick (α : Type u) [samp : Sample α (fun _ => True)] : NonDetM α := {
  tpc τ := (a : α) × τ a,
  pre cont t := cont t.1 t.2,
  val cont t := cont t.1 t.2,
  sample cont samp' :=  {
      gen := samp.gen.pairs fun a => samp' a |>.gen
      prop := by 
        rintro ⟨a, b⟩; simp
        sorry
    }
}
abbrev NonDetM.assume (as : Prop) [Decidable as] : NonDetM Unit := {
  tpc := fun τ => τ (),
  pre := fun cont t => as ∧ cont () t,
  val := fun cont t => cont () t,

  sample cont samp := {
      gen := if as then samp () |>.gen else #[]
      prop := by simp; intros; solve_by_elim [Sample.prop] 
    }
}

abbrev NonDetM.pick_such_that (α : Type u) (p : α -> Prop) [samp : Sample α p] : NonDetM α := { 
  tpc := fun τ => (a : α) × τ a,
  pre cont t := p t.1 ∧ cont t.1 t.2,
  val cont t := cont t.1 t.2,
  sample cont samp' := {
      gen := samp.gen.pairs fun a => samp' a |>.gen
      prop := by 
        rintro ⟨a, b⟩; simp
        sorry
    }
}

instance : Sample PUnit (fun _ => True) where
  gen := #[.unit]
  prop := by rintro ⟨⟩; simp

instance : MonadLift NonDetM Array where 
  monadLift n := 
    let x := n.sample (τ := fun _ => PUnit) (fun _ _ => True) |>.gen 
    x.map <| n.val (fun a _ => a)

instance : Monad Array where
  pure := Array.singleton
  bind x f := Array.flatMap f x

lemma lift_bind (x : NonDetM α) (f : α -> NonDetM β) : 
  monadLift (n := Array) (x >>= f) = monadLift x >>= fun a => monadLift (f a) := by 
  unfold monadLift; simp [instMonadLiftTOfMonadLift, MonadLift.monadLift]

    
  


class MonadFunctor' (m m' : semiOutParam (Type u → Type v)) (n n' : Type u → Type w) where
  /-- Lifts a monad morphism `f : {β : Type u} → m β → m β` to
  `monadMap f : {α : Type u} → n α → n α`. -/
  monadMap {α : Type u} : ({β : Type u} → m β → m' β) → n α → n' α

#check IO.rand

def liftNondet {α : Type u} 
  {sampleM : Type u -> Type (u + 1)}
  {mT : (Type u -> Type (u + 1)) -> (Type u -> Type w)}
  [MonadFunctor' NonDetM sampleM (mT NonDetM.{u, u}) (mT sampleM)] 
  (x : mT NonDetM α) : mT sampleM α := by sorry


abbrev succ (x : Int) : NonDetM Int :=
  do
    let y <- NonDetM.choose Int
    NonDetM.assume (y > x)
    let z <- NonDetM.choose Int
    NonDetM.assume (z < x)
    return y + z

example (P : _ -> Prop) i : P ((succ i)) := by
  simp [succ, bind, pure, NonDetM.choose, NonDetM.assume, NonDetM.pure, NonDetM.bind]
  -- simp [StateT.bind, StateT.get, pure, NonDetM.pure, liftM, monadLift, MonadLift.monadLift]
  -- simp [succ', bind, pure, NonDetM.choose, NonDetM.assume, NonDetM.pure, NonDetM.bind, StateT.lift, StateT.pure]


abbrev succ' : StateT Int NonDetM Int :=
  do
    let x <- get
    set (x + 1)
    let y <- NonDetM.choose Int
    NonDetM.assume (y > x)
    return y


#check Exists.choose
example (P : _ -> Prop) i : P ((succ' i)) := by
  simp [succ', bind, pure, NonDetM.choose, NonDetM.assume, NonDetM.pure, NonDetM.bind]
  -- simp [get]; simp [getThe]; simp [MonadStateOf.get]; unfold StateT.get
  simp [StateT.bind, StateT.get, pure, NonDetM.pure, liftM, monadLift, MonadLift.monadLift]
  simp [succ', bind, pure, NonDetM.choose, NonDetM.assume, NonDetM.pure, NonDetM.bind, StateT.lift, StateT.pure]
  simp [get, getThe, MonadStateOf.get, StateT.get, pure, NonDetM.pure]
  simp [set, StateT.set, pure, NonDetM.pure]

  sorry

#reduce! ((succ 5).tp)

#reduce (succ 5).val (by
  dsimp [succ, bind, pure, NonDetM.choose, NonDetM.assume, NonDetM.pure, NonDetM.bind]
  exact ⟨6, PLift.up (by omega), ()⟩)





instance NonDetM.Setoid : Setoid (NonDetM α) where
  r := fun ⟨tp₁, val₁⟩ ⟨tp₂, val₂⟩ => ∃ f : tp₁ -> tp₂, f.Bijective ∧ ∀ x, val₁ x = val₂ (f x)
  iseqv := {
    refl := by
      rintro ⟨tp, val⟩; simp; exists id; simp; exact Function.bijective_id
    symm := by
      rintro ⟨tp₁, val₁⟩ ⟨tp₂, val₂⟩; simp; intro f bij valf
      exists f.surjInv bij.2; constructor
      { refine Function.bijective_iff_has_inverse.mpr ?_; exists f; constructor
        { refine Function.RightInverse.leftInverse ?_
          exact Function.rightInverse_surjInv bij.right }
        refine Function.LeftInverse.rightInverse ?_
        exact Function.leftInverse_surjInv bij }
      simp [valf, Function.surjInv_eq]
    trans := by
      rintro ⟨tp₁, val₁⟩ ⟨tp₂, val₂⟩ ⟨tp₃, val₃⟩; simp; intros f₁ bij₁ valf₁ f₂ bij₂ valf₂
      exists f₂ ∘ f₁; constructor
      { exact Function.Bijective.comp bij₂ bij₁ }
      aesop
  }

lemma bind_eq {x y : NonDetM α} {f g : α → NonDetM β} :
  x ≈ y ->
  (∀ a, f a ≈ g a) ->
  (NonDetM.bind x f) ≈ (NonDetM.bind y g) := by
  rcases x with ⟨tp₁, val₁⟩
  rcases y with ⟨tp₂, val₂⟩
  rintro ⟨eq, bij, valf⟩
  simp [HasEquiv.Equiv, Setoid.r]; intro r
  rcases Classical.skolem.mp r with ⟨fr, fbij⟩
  simp [NonDetM.bind]
  admit


abbrev LawfullNonDetM α := Quotient (@NonDetM.Setoid α)

variable {α : Type u} {β : Type v}

abbrev LawfullNonDetM.mk : NonDetM α -> LawfullNonDetM α := Quotient.mk NonDetM.Setoid

def LawfullNonDetM.pure (x : α) := NonDetM.pure x |> LawfullNonDetM.mk

noncomputable def LawfullNonDetM.bind (x : LawfullNonDetM α) (f : α → LawfullNonDetM β) : LawfullNonDetM β :=
  Quotient.liftOn x (fun x => Quotient.liftOnFun f (fun f => NonDetM.bind x f))
  (by
   intro a b eq; simp; sorry ) |> LawfullNonDetM.mk
