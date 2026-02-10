import Loom.MonadAlgebras.NonDetT'.ExtractListBasic
import Mathlib.Control.Monad.Writer
import Mathlib.Data.Tree.Basic

open MultiExtractor

section BasicStuff

theorem iSup_list_map {l : Type w} [CompleteLattice l] {α : Type u} {β : Type v} (post : β → l) (f : α → β) (xs : List α) :
  ⨆ y ∈ xs.map f, post y = ⨆ x ∈ xs, post (f x) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.mem_cons, iSup_or, iSup_sup_eq, ih]
    simp

theorem iSup_list_flatMap {l : Type w} [CompleteLattice l] {α : Type u} {β : Type v} (post : β → l) (f : α → List β) (xs : List α) :
  ⨆ y ∈ xs.flatMap f, post y = ⨆ x ∈ xs, ⨆ x' ∈ f x, post x' := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.mem_append, List.mem_cons, iSup_or, iSup_sup_eq, ih]
    simp

def pointwiseInf {l : Type v} [CompleteLattice l] {α : Type u} (post : α → l) : List α → l :=
  fun xs => ⨅ a ∈ xs, post a

noncomputable
def pointwiseInf' {l : Type v} [CompleteBooleanAlgebra l] {α : Type u} (post : α → l) : List α → l :=
  fun xs => ⨅ a, ⌜ a ∈ xs ⌝ ⇨ post a

theorem pointwiseInf_alt {l : Type v} [CompleteBooleanAlgebra l] {α : Type u} (post : α → l) lis :
  pointwiseInf post lis = pointwiseInf' post lis := by
  unfold pointwiseInf pointwiseInf'
  apply iInf_congr ; intro a
  by_cases h : a ∈ lis <;> simp [h]

def pointwiseSup {l : Type v} [CompleteLattice l] {α : Type u} (post : α → l) : List α → l :=
  fun xs => ⨆ a ∈ xs, post a

theorem pointwiseSup_append {l : Type v} [CompleteLattice l] {α : Type u} (post : α → l) (xs ys : List α) :
  pointwiseSup post (xs ++ ys) = pointwiseSup post xs ⊔ pointwiseSup post ys := by
  simp [pointwiseSup, iSup_or, iSup_sup_eq]

noncomputable
def pointwiseSup' {l : Type v} [CompleteBooleanAlgebra l] {α : Type u} (post : α → l) : List α → l :=
  fun xs => ⨆ a, ⌜ a ∈ xs ⌝ ⊓ post a

theorem pointwiseSup_alt {l : Type v} [CompleteBooleanAlgebra l] {α : Type u} (post : α → l) lis :
  pointwiseSup post lis = pointwiseSup' post lis := by
  unfold pointwiseSup pointwiseSup'
  apply iSup_congr ; intro a
  by_cases h : a ∈ lis <;> simp [h]

@[inline] def List.flatMapTRNoSpecialize (f : α → List β) (as : List α) : List β := go as #[] where
  go : List α → Array β → List β
  | [], acc => acc.toList
  | x::xs, acc => go xs (acc ++ f x)

theorem List.flatMapTRNoSpecialize_eq_flatMap : @List.flatMapTRNoSpecialize = @List.flatMap := by
  funext α β f as
  let rec go : ∀ as acc, flatMapTRNoSpecialize.go f as acc = acc.toList ++ as.flatMap f
    | [], acc => by simp [flatMapTRNoSpecialize.go, flatMap]
    | x::xs, acc => by simp [flatMapTRNoSpecialize.go, flatMap, go xs]
  exact (go as #[])

end BasicStuff

/-!

## 1. From the First Principle

Let's infer what to do from the first principle.
For now just assume the result type is `mr α`.

In `pickCont`, by using a list, we will have
- `List τ`
- recursion and map, we have `List mr α`

Then one natural thing to do is some `flatMap`-like operation
to get `mr α`.

... So, there is nothing directly related to `ListT` here
-/

/-!

## 2. Persistency of Choices

But it is also good to keep track of the choices made,
so we can use `mr (α × List κ)`. To add the choice, we
need to "operate" inside the monad, so we need `mr` to be a monad.
- Wait, if the trace is at the position with `α`, then it is possible
  to get lost (e.g., when `α` does not appear in the result).

  So maybe `κ` should be outside the `α`? Parameterized by `mr`?
- One way to go is to use the `Writer` monad, but the log there is at
  the same position as `α`, so not very suitable?

-/

-- The point is: sometimes, when the thing to be carried over is inside `m`,
-- then it might get lost when the value with type `m α` does not depend on `α`!
-- This includes `DivM`.
-- And there is no way to remedy in a modular way.
-- So one possible way to go is to augment them with "persistent" results.

-- TODO why this is not present?
@[inline]
instance : Monoid (List κ) where
  one := []
  mul := List.append
  mul_assoc := by introv ; apply List.append_assoc
  one_mul := by introv ; rfl
  mul_one := by introv ; apply List.append_nil

def PeDivM (κ : Type w) (α : Type u) := κ × DivM α

@[inline, specialize inst]
def PeDivM.prepend {κ : Type w} [inst : Monoid κ] {α : Type u} (k : κ) : PeDivM κ α → PeDivM κ α
  | (k', a) => (k * k', a)

theorem PeDivM.prepend_snd_same {κ : Type w} [Monoid κ] {α : Type u} (k : κ) (x : PeDivM κ α) :
  (x.prepend k).2 = x.2 := by cases x ; simp [PeDivM.prepend]

-- more suitable to be inserted
@[inline]
def PeDivM.log {κ : Type w} (k : κ) : PeDivM κ PUnit :=
  (k, DivM.res PUnit.unit)

@[always_inline]
instance [Monoid κ] : Monad (PeDivM κ) where
  pure := fun x => (1, DivM.res x)
  bind := fun (k1, mx) f =>
    match mx with
    | DivM.res x => f x |>.prepend k1   -- TODO it's very bad that this is not tail-recursive ...
    | DivM.div => (k1, DivM.div)
  map  := fun f (k, mx) => (k, match mx with
    | DivM.res a => DivM.res (f a)
    | DivM.div   => DivM.div)

instance [Monoid κ] : LawfulMonad (PeDivM κ) :=
  LawfulMonad.mk' (PeDivM κ)
  (id_map := by introv ; simp [Functor.map] ; rcases x with ⟨k1, x | _⟩ <;> simp)
  (pure_bind := by introv ; simp [bind, PeDivM.prepend] ; rfl)
  (bind_assoc := by
    introv ; simp [bind, PeDivM.prepend] ; rcases x with ⟨k1, x | _⟩ <;> simp
    rcases f x with ⟨k2, y | _⟩ <;> simp
    rcases g y with ⟨k3, z | _⟩ <;> simp
    all_goals (congr! 1 ; ac_rfl))
  (bind_pure_comp := by introv ; simp [bind, Functor.map, PeDivM.prepend] ; rcases x with ⟨k1, x | _⟩ <;> simp)

theorem PeDivM.bind_snd {κ : Type w} {α β : Type u} [Monoid κ] (mx : PeDivM κ α) (f : α → PeDivM κ β) :
  (mx >>= f).2 = mx.2 >>= (Prod.snd ∘ f) := by
  rcases mx with ⟨k1, x | _⟩ <;> rfl

-- only depends on the second component
instance [Monoid κ] [CompleteLattice l] [inst : MAlgOrdered DivM l] : MAlgOrdered (PeDivM κ) l where
  μ := inst.μ ∘ Prod.snd
  μ_ord_pure := by intro ll ; apply MAlgOrdered.μ_ord_pure
  μ_ord_bind {α} f g := by
    intro h x ; simp [Function.comp] ; repeat rw [PeDivM.bind_snd]
    apply MAlgOrdered.μ_ord_bind ; exact h

theorem PeDivM.wp_eq_DivM [Monoid κ] [CompleteLattice l] [inst : MAlgOrdered DivM l]
  (x : PeDivM κ α) (post : α → l) :
  wp x post = wp x.2 post := by
  simp [wp, liftM, monadLift, MAlg.lift, Functor.map]
  rcases x with ⟨k1, x⟩ ; simp [MAlgOrdered.μ]
  cases x <;> rfl

/-!

## 3. Mapping from One Monad to Another, Morphism?

From `NonDetT m` to something else, it's in general monad lifting, but
we might as well use a dedicated typeclass.

For some commonly seen things, this "mapping" should always take the same
form, e.g., `ExceptT ε m` to `ExceptT ε n`.

TODO The proofs for the `LawfulMonadFlatMapGo` instances should be derivable
from the ordered monad algebra things?

-/

section MonadFlatMapGo

class MonadFlatMapGo (m : Type u → Type v) (n : Type u → Type w) where
  go : {α : Type u} → m α → n α

section

variable (m : Type u → Type v) (n : Type u → Type w)
  [inst : MonadFlatMapGo m n]
  [Monad m] [Monad n]
  (l : Type u)
  -- [CompleteBooleanAlgebra l]
  [CompleteLattice l]
  [MAlgOrdered m l] [MAlgOrdered n l]

class LawfulMonadFlatMapGo (p : l → l → Prop)  -- what about equality? `≤` is just one direction, so maybe parameterize it with `p`
  where
  -- must be relating the results before and after `go`;
  -- a wrong formulation is about all `b : n α`
  go_sound : ∀ α (a : m α) post,
    p (wp a post) (wp (inst.go a) post)

instance [inst : LawfulMonadFlatMapGo m n l Eq] : LawfulMonadFlatMapGo m n l LE.le where
  go_sound := by intro α a post ; rw [inst.go_sound α a post]

instance [inst : LawfulMonadFlatMapGo m n l Eq] : LawfulMonadFlatMapGo m n l GE.ge where
  go_sound := by intro α a post ; rw [inst.go_sound α a post]

end

abbrev relLift (p : l → l → Prop) : (α → l) → (α → l) → Prop :=
  fun f g => ∀ a, p (f a) (g a)

/-- Removing `relLift` under `Eq` -/
instance
  [MonadFlatMapGo m n]
  [Monad m] [Monad n]
  [CompleteLattice l]
  [MAlgOrdered m (a → l)] [MAlgOrdered n (a → l)]
  [inst : LawfulMonadFlatMapGo m n (a → l) (relLift Eq)]
  : LawfulMonadFlatMapGo m n (a → l) Eq where
  go_sound := by introv ; ext a ; apply inst.go_sound

section Instances

@[always_inline]
instance [Monoid κ] : MonadFlatMapGo DivM (PeDivM κ) where
  go := fun x => (1, x)

instance [Monoid κ] [CompleteLattice l] [inst : MAlgOrdered DivM l]
   : LawfulMonadFlatMapGo DivM (PeDivM κ) l Eq where
  go_sound := by
    intro α a post
    simp [wp, liftM, monadLift, MAlg.lift, Functor.map]
    rcases a with a | _ <;> simp [MAlgOrdered.μ]

variable [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n]
  (l : Type u) [CompleteLattice l]
  [MAlgOrdered m l] [MAlgOrdered n l]
  (p : l → l → Prop)
  [inst : MonadFlatMapGo m n]
  [instl : LawfulMonadFlatMapGo m n l p]

@[always_inline]
instance : MonadFlatMapGo (ExceptT ε m) (ExceptT ε n) where
  go := inst.go

-- CHECK now I guess this is unrelated to `MonadFlatMapGo`, but generic for monad morphism
instance {hd : ε → Prop} [IsHandler hd]
  : LawfulMonadFlatMapGo (ExceptT ε m) (ExceptT ε n) l p where
  go_sound := by
    intro α a post
    have tmp := instl.go_sound _ a
      (fun e => match e with
        | Except.ok x    => post x
        | Except.error e => ⌜hd e⌝ )
    simp [wp, liftM, monadLift] at tmp ⊢
    simp [MAlg.lift, Functor.map, ExceptT.map, ExceptT.mk] at tmp ⊢
    repeat rw [map_eq_pure_bind] at tmp
    simp only [OfHd, MAlgExcept, map_bind]
    -- not easy to rewrite
    have tmp1 : ∀ (a : Except ε α),
      ((pure
        (match a with
        | Except.ok x => post x
        | Except.error e => ⌜hd e⌝)) : m l) =
      (((Except.getD fun x ↦ ⌜hd x⌝) <$>
        match a with
        | Except.ok a => pure (Except.ok (post a))
        | Except.error e => pure (Except.error e)) : m l) := by
      intro a ; cases a <;> simp [Except.getD]
    conv at tmp => lhs ; rhs ; rhs ; intro x ; rw [tmp1]
    clear tmp1
    have tmp2 : ∀ (a : Except ε α),
      ((pure
        (match a with
        | Except.ok x => post x
        | Except.error e => ⌜hd e⌝)) : n l) =
      (((Except.getD fun x ↦ ⌜hd x⌝) <$>
        match a with
        | Except.ok a => pure (Except.ok (post a))
        | Except.error e => pure (Except.error e)) : n l) := by
      intro a ; cases a <;> simp [Except.getD]
    conv at tmp => rhs ; rhs ; rhs ; intro x ; rw [tmp2]
    clear tmp2
    exact tmp

@[always_inline]
instance : MonadFlatMapGo (ReaderT ρ m) (ReaderT ρ n) where
  go := fun a r => inst.go (a r)

instance : LawfulMonadFlatMapGo (ReaderT ρ m) (ReaderT ρ n) (ρ → l) (relLift p) where
  go_sound := by
    intro α a post r
    have tmp := instl.go_sound _ (a r) (fun a => post a r)
    simp [wp, liftM, monadLift] at tmp ⊢
    simp [MAlg.lift] at tmp ⊢
    simp [MAlgOrdered.μ, Functor.map]
    exact tmp

@[always_inline]
instance : MonadFlatMapGo (StateT σ m) (StateT σ n) where
  go := fun a s => inst.go (a s)

instance : LawfulMonadFlatMapGo (StateT σ m) (StateT σ n) (σ → l) (relLift p) where
  go_sound := by
    intro α a post s
    have tmp := instl.go_sound _ (a s) (fun (a, s) => post a s)
    simp [wp, liftM, monadLift] at tmp ⊢
    simp [MAlg.lift] at tmp ⊢
    simp [MAlgOrdered.μ, Functor.map, StateT.map]
    exact tmp

end Instances

end MonadFlatMapGo

/-!

## 4. Logging With Monad

There actually exists one in the Mathlib, `MonadWriter`. But here we only
use the most basic part, `tell`, so we re-define a minimal typeclass here.

-/

class MonadPersistentLog (κ : Type w) (m : Type u → Type v) where
  log : κ → m PUnit

@[always_inline]
instance : MonadPersistentLog κ (PeDivM κ) where
  log := PeDivM.log

@[always_inline]
instance : MonadPersistentLog κ (PeDivM (List κ)) where
  log := (PeDivM.log [·])

-- NOTE: `MonadLiftT` does not work here
@[always_inline]
instance [inst : MonadPersistentLog κ m] [lft : MonadLift m n] : MonadPersistentLog κ n where
  log := (lft.monadLift <| inst.log ·)

-- no effect that changes `wp` can be observed from the log action
class LawfulMonadPersistentLog (κ : Type w) (m : Type u → Type v)
  [inst : MonadPersistentLog κ m]
  [Monad m] (l : Type u) [CompleteLattice l] [MAlgOrdered m l] where
  log_sound : ∀ (k : κ) (post : PUnit → l), wp (inst.log k) post = post PUnit.unit

-- TODO we should be able to derive `LawfulMonadPersistentLog` systematically,
-- through some kind of lawful lifts, but it seems not very easy to do so ...?

section WriterT

variable [Monad M] [LawfulMonad M] [Monoid ω] [CompleteLattice l] [inst : MAlgOrdered M l]

@[always_inline]
instance : MonadPersistentLog ω (WriterT ω M) where
  log := fun w => WriterT.mk <| pure (⟨⟩, w)

@[always_inline]
instance : MonadFlatMapGo M (WriterT ω M) where
  go x := Functor.map (f := M) (fun a => (a, 1)) x

-- only depends on the return value component
instance : MAlgOrdered (WriterT ω M) l where
  μ x := inst.μ <| Prod.fst <$> x
  μ_ord_pure := by intro ll ; simp only [map_eq_pure_bind, pure, pure_bind] ; apply inst.μ_ord_pure
  μ_ord_bind {α} f g := by
    intro h x ; simp +unfoldPartialApp [Function.comp] at h
    simp [bind, WriterT.mk]
    apply inst.μ_ord_bind ; simp +unfoldPartialApp [Function.comp]
    intro k ; simp ; specialize h k.1 ; exact h

theorem WriterT.wp_eq (x : WriterT ω M α) (post : α → l) :
  wp x post = wp (Prod.fst <$> x) post := by
  simp [wp, liftM, monadLift, MAlg.lift, Functor.map, WriterT.mk, MAlgOrdered.μ]

instance : LawfulMonadFlatMapGo M (WriterT ω M) l Eq where
  go_sound := by
    intro α a post
    simp [wp, liftM, monadLift, MAlg.lift, Functor.map, WriterT.mk, MAlgOrdered.μ, MonadFlatMapGo.go]

end WriterT

/-!

## 5. Comments on `ListT`

Another point where the original ListT m is interesting is that it is a composite of
two monads (m and the list monad). This leads us to the study of distributive laws.
There is a canonical distributive law when m is commutative — then ListT m is a monad.

-/

/-
-- class MonadFlatMap (m : Type u → Type v) where
--   op : ∀ {α}, List (m (List α)) → m (List α)

section test

variable (σ : Type u) [Monad m] [MonadFlatMap m]

instance : MonadFlatMap (StateT σ m) where
  op := fun {α} xs s =>
    letI tmp := xs.map (· s)
    letI tmp := tmp.map ((fun (as, b) => as.map (Prod.mk · b)) <$> ·)
    letI tmp := MonadFlatMap.op tmp
    sorry

end test

-- well, `m (List α)` does not work, for example with `StateT σ m`,
-- we can only keep one copy of the state, not multiple copies.
-- so it should not be `m (List α)`, but some more general type `m' α` ...?

-- it seems that we cannot directly use `StateT σ m`, but it has to be something else
-/

/-!

## 6. Merging Computations

See Point 1.

-/

section MonadFlatMap'

section Basic

variable (m : Type u → Type v) (l : Type u) [Monad m] [CompleteLattice l]

class MonadFlatMap' where
  op : ∀ {α}, List (m α) → m α

-- TODO maybe also generalize over `⊔`?
/-- Typeclass relating the result of `MonadFlatMap'.op` to the `⊔` of results
of the individual computations. -/
class LawfulMonadFlatMapSup [MAlgOrdered m l] [inst : MonadFlatMap' m] (p : l → l → Prop) where
  sound : ∀ (xs : List (m α)) (post : α → l),
    p (⨆ a ∈ xs, wp a post) (wp (inst.op xs) post)

-- TODO this might relate to `TsilT`?
class MonadFlatMap'FMapDistributive [inst : MonadFlatMap' m] where
  fmap_distrib :
    ∀ {α β : Type u} (f : α → β) (xs : List (m α)),
      inst.op (xs.map (f <$> ·)) = f <$> (inst.op xs)

class MonadFlatMap'BindDistributive [inst : MonadFlatMap' m] where
  bind_distrib : ∀ {α β} (l : List (m α)) (f : α → m β),
    inst.op (l.map (· >>= f)) = (inst.op l) >>= f

-- NOTE: due to this implication, we do not provide `MonadFlatMap'FMapDistributive` instances
instance [LawfulMonad m] [inst : MonadFlatMap' m] [instl : MonadFlatMap'BindDistributive m] : MonadFlatMap'FMapDistributive m where
  fmap_distrib := by
    introv
    have tmp := instl.bind_distrib (l := xs) (f := fun a => pure (f a))
    simp [bind_pure_comp] at tmp
    exact tmp

variable [inst : MonadFlatMap' m]

instance [MAlgOrdered m (a → l)] [instl : LawfulMonadFlatMapSup m (a → l) (relLift Eq)]
  : LawfulMonadFlatMapSup m (a → l) Eq where
  sound := by introv ; ext a ; apply instl.sound

variable [MAlgOrdered m l] [instl : LawfulMonadFlatMapSup m l Eq]

instance : LawfulMonadFlatMapSup m l LE.le where
  sound := by intro α a post ; rw [instl.sound a post]

instance : LawfulMonadFlatMapSup m l GE.ge where
  sound := by intro α a post ; rw [instl.sound a post]

end Basic

section Instances

variable (m : Type u → Type v) (l : Type u) [Monad m] [CompleteLattice l]
  [LawfulMonad m] [MAlgOrdered m l] [inst : MonadFlatMap' m]

@[always_inline]
instance : MonadFlatMap' (ReaderT ρ m) where
  op := fun l r => inst.op <| l.map (· r)

instance (p : l → l → Prop) [instl : LawfulMonadFlatMapSup m l p]
  : LawfulMonadFlatMapSup (ReaderT ρ m) (ρ → l) (relLift p)
  where
  sound := by
    intro α xs post r
    simp [MonadFlatMap'.op]
    have tmp := instl.sound (List.map (· r) xs) (fun a => post a r)
    rw [iSup_list_map] at tmp
    simp [wp, liftM, monadLift] at tmp ⊢
    simp [MAlg.lift, Functor.map, MAlgOrdered.μ] at tmp ⊢
    exact tmp

instance [MonadFlatMap'BindDistributive m] : MonadFlatMap'BindDistributive (ReaderT ρ m) where
  bind_distrib := by
    introv ; dsimp +unfoldPartialApp [MonadFlatMap'.op, Function.comp]
    funext r
    have eq1 : (List.map (fun x ↦ x r) (List.map (fun x ↦ x >>= f) l)) =
      List.map (fun x ↦ x >>= (f · r)) (l.map (· r)) := by
      simp [Bind.bind, ReaderT.bind]
    rw [eq1, MonadFlatMap'BindDistributive.bind_distrib] ; rfl

-- the same construction as `ReaderT`
-- ... of course. or why?
@[always_inline]
instance : MonadFlatMap' (StateT σ m) where
  op := fun l r => inst.op <| l.map (· r)

instance (p : l → l → Prop) [instl : LawfulMonadFlatMapSup m l p]
  : LawfulMonadFlatMapSup (StateT σ m) (σ → l) (relLift p)
  where
  sound := by
    intro α xs post st
    simp [MonadFlatMap'.op]
    have tmp := instl.sound (List.map (· st) xs) (fun (a, s) => post a s)
    rw [iSup_list_map] at tmp
    simp [wp, liftM, monadLift] at tmp ⊢
    simp [MAlg.lift, Functor.map, MAlgOrdered.μ, StateT.map] at tmp ⊢
    exact tmp

instance [MonadFlatMap'BindDistributive m] : MonadFlatMap'BindDistributive (StateT σ m) where
  bind_distrib := by
    introv ; dsimp +unfoldPartialApp [MonadFlatMap'.op, Function.comp]
    funext s
    have eq1 : (List.map (fun x ↦ x s) (List.map (fun x ↦ x >>= f) l)) =
      List.map (fun x ↦ x >>= (fun a => f a.1 a.2)) (l.map (· s)) := by
      simp [Bind.bind, StateT.bind]
    rw [eq1, MonadFlatMap'BindDistributive.bind_distrib] ; rfl

@[always_inline]
instance : MonadFlatMap' (ExceptT ε m) where
  op := inst.op

instance {hd : ε → Prop} [IsHandler hd]
  (p : l → l → Prop) [instl : LawfulMonadFlatMapSup m l p]
  [instd : MonadFlatMap'FMapDistributive m]   -- !!
  : LawfulMonadFlatMapSup (ExceptT ε m) l p where
  sound := by
    introv
    simp [MonadFlatMap'.op]
    have tmp := instl.sound (xs.map (ExceptT.map post)) (Except.getD fun x => ⌜ hd x ⌝)
    rw [iSup_list_map] at tmp
    have tmp2 := instd.fmap_distrib (m := m) (Except.map post) xs
    have tmp3 := ExceptT.run_map (ε := ε) (m := m) post
    simp only [ExceptT.run] at tmp3
    simp [← tmp3, Functor.map] at tmp2
    rw [tmp2] at tmp ; clear tmp2
    simp [wp, liftM, monadLift, MAlg.lift, Functor.map] at tmp ⊢
    exact tmp

instance [MonadFlatMap'BindDistributive m] : MonadFlatMap'BindDistributive (ExceptT ε m) where
  bind_distrib := by
    introv ; dsimp +unfoldPartialApp [MonadFlatMap'.op, Function.comp]
    apply MonadFlatMap'BindDistributive.bind_distrib

end Instances

end MonadFlatMap'

/-!

## 7. Lists of Computations as Monad

Sometimes, a list of computations is more useful than a computation
returning a list.

-/

section TsilT

-- well it is clear that `List` is a monad, how about `List (m α)`?
abbrev TsilT (m : Type u → Type v) (α : Type u) := List (m α)

@[always_inline]
instance : MonadFlatMap' (TsilT m) where
  op := List.flatten

-- well ... to account for the logging construct
instance : MonadLift m (TsilT m) where
  monadLift := fun x => [x]

instance : MonadFlatMapGo m (TsilT m) where
  go := fun x => [x]

-- TODO this is ad-hoc, maybe adding some kind of transitivity would be better
instance [inst : MonadFlatMapGo m m'] : MonadFlatMapGo m (TsilT m') where
  go := fun x => [inst.go x]

-- the "core" might be important here: `m α → (α → TsilT m β) → TsilT m β`
-- TODO how to use it in other places? one place: for `⨅`
class TsilTCore (m : Type u → Type v) where
  op : ∀ {α β}, m α → (α → TsilT m β) → TsilT m β

@[always_inline]
instance [Pure m] : Pure (TsilT m) where
  pure x := [pure x]

@[always_inline]
instance [Functor m] : Functor (TsilT m) where
  map f xs := xs.map (Functor.map f)

@[always_inline]
instance [TsilTCore m] : Bind (TsilT m) where
  bind := fun xs f =>
    match xs with
    | [] => []
    | [x] => TsilTCore.op x f
    | _ => xs.flatMapTRNoSpecialize fun mx => TsilTCore.op mx f

theorem TsilTCore.bind_eq_flatMap [TsilTCore m] (xs : TsilT m α) (f : α → TsilT m β) :
  bind xs f = xs.flatMap fun mx => TsilTCore.op mx f := by
    rcases xs with _ | ⟨x, _ | ⟨y, xs⟩⟩ <;> (try solve | rfl | simp [bind])
    simp [bind, List.flatMapTRNoSpecialize_eq_flatMap]

@[always_inline]
instance [Monad m] [TsilTCore m] : Monad (TsilT m) where

instance [Monad m] [TsilTCore m] : MonadFlatMap'BindDistributive (TsilT m) where
  bind_distrib := by introv ; simp [MonadFlatMap'.op, TsilTCore.bind_eq_flatMap] ; induction l <;> grind

section Lawfulness

-- NOTE: The lawfulness here is very tricky to state

-- CHECK any relation with laws on monad morphism?
class LawfulTsilTCore (m : Type u → Type v) [Monad m] [TsilTCore m] where
  -- TODO can `op_single` be actually removed? i.e., does it always hold?
  op_single : ∀ {α β} (x : m α) (f : α → β),
    -- CHECK `map_pure`
    TsilTCore.op x (fun a => [pure (f a)]) = [f <$> x]
  pure_op : ∀ {α β} (x : α) (f : α → TsilT m β), TsilTCore.op (pure x) f = f x
  op_assoc : ∀ {α β γ} (x : m α) (f : α → TsilT m β) (g : β → TsilT m γ),
    List.flatMap (TsilTCore.op · g) (TsilTCore.op x f) =
    TsilTCore.op x (fun a => List.flatMap (TsilTCore.op · g) (f a))

theorem TsilTCore.bind_cons {α β : Type u} [Monad m] [TsilTCore m]
  (mx : m α) (mxs : TsilT m α) (f : α → TsilT m β) :
  letI tmp : TsilT m α := (mx :: mxs)
  (tmp >>= f) = (TsilTCore.op mx f) ++ (mxs >>= f) := by simp [TsilTCore.bind_eq_flatMap]

theorem TsilTCore.bind_append {α β : Type u} [Monad m] [TsilTCore m]
  (mx1 mx2 : TsilT m α) (f : α → TsilT m β) :
  ((mx1 ++ mx2) >>= f) = (mx1 >>= f) ++ (mx2 >>= f) := by simp [TsilTCore.bind_eq_flatMap]

-- this is required in general
instance [Monad m] [LawfulMonad m] [TsilTCore m] [LawfulTsilTCore m] : LawfulMonad (TsilT m) :=
  LawfulMonad.mk' (TsilT m)
  (map_const := by intros ; rfl)
  (id_map := by
    introv ; simp [Functor.map]
    induction x with
    | nil => simp
    | cons y xs ih => simp [ih])
  (pure_bind := by introv ; simp [bind] ; apply LawfulTsilTCore.pure_op)
  (bind_assoc := by
    introv ; simp [TsilTCore.bind_eq_flatMap] ; rw [List.flatMap_assoc]
    apply List.flatMap_congr ; intro x _ ; apply LawfulTsilTCore.op_assoc)
  (bind_pure_comp := by
    introv ; simp [TsilTCore.bind_eq_flatMap, pure, Functor.map]
    induction x with
    | nil => simp
    | cons y xs ih => simp [ih] ; rw [LawfulTsilTCore.op_single] ; simp)

-- TODO how is this related to other laws?
class LawfulTsilTCore' (m : Type u → Type v) [Monad m] [TsilTCore m] where
  -- this is too strong!!! not derivable even for `PeDivM`!!!
  -- op_map_commute : ∀ {α β γ} (x : m α) (f : α → TsilT m β) (h : m β → m γ),
  --   List.map h (TsilTCore.op x f) = TsilTCore.op x (fun a => List.map h (f a))
  op_fmap_commute : ∀ {α β γ} (x : m α) (f : α → TsilT m β) (h : β → γ),
    List.map (h <$> ·) (TsilTCore.op x f) = TsilTCore.op x (fun a => List.map (h <$> ·) (f a))

class LawfulTsilTCoreMAlgSup (m : Type u → Type v) (l : Type u)
  [Monad m] [TsilTCore m] [CompleteLattice l] [MAlgOrdered m l] where
  sup : ∀ (f g : α → TsilT m l),
    (pointwiseSup MAlgOrdered.μ ∘ f ≤ pointwiseSup MAlgOrdered.μ ∘ g) →
    ∀ (x : m α),
      pointwiseSup MAlgOrdered.μ (TsilTCore.op x f) ≤ pointwiseSup MAlgOrdered.μ (TsilTCore.op x g)

namespace AngelicChoice

variable [Monad m] [TsilTCore m]
  [CompleteLattice l] [inst : MAlgOrdered m l] [LawfulTsilTCoreMAlgSup m l]

scoped instance : MAlgOrdered (TsilT m) l where
  μ := pointwiseSup MAlgOrdered.μ
  μ_ord_pure := by intro ll ; simp [pointwiseSup, pure] ; apply MAlgOrdered.μ_ord_pure
  μ_ord_bind := by
    introv ; intro h xs
    induction xs with
    | nil => simp [pointwiseSup, bind]
    | cons x xs ih =>
      simp only [TsilTCore.bind_cons, pointwiseSup_append]
      apply sup_le_sup <;> try assumption
      -- simp only [bind, pointwiseSup, List.flatMap_singleton]
      apply LawfulTsilTCoreMAlgSup.sup ; assumption

theorem TsilT.wp_eq [LawfulMonad m] : ∀ (a : TsilT m α) (post : α → l),
  wp a post = pointwiseSup (wp · post) a := by
  introv
  simp [wp, liftM, monadLift, MAlg.lift, Functor.map, MAlgOrdered.μ]
  unfold pointwiseSup ; rw [iSup_list_map]

scoped instance : LawfulMonadFlatMapSup (TsilT m) l Eq where
  sound := by
    introv ; simp [MonadFlatMap'.op, wp, liftM, monadLift, MAlg.lift, Functor.map, MAlgOrdered.μ]
    simp only [pointwiseSup, iSup_list_map]
    rw [List.flatten_eq_flatMap] ; simp only [iSup_list_flatMap, iSup_list_map, id]

scoped instance [LawfulMonad m] [LawfulTsilTCore m] : LawfulMonadFlatMapGo m (TsilT m) l Eq where
  go_sound := by
    introv
    simp [wp, liftM, monadLift, MAlg.lift, Functor.map, MAlgOrdered.μ, MonadFlatMapGo.go, pointwiseSup]

-- TODO the proper way to do this is to have a transitivity for `LawfulMonadFlatMapGo`
scoped instance [Monad m'] [LawfulMonad m'] [TsilTCore m'] [inst' : MAlgOrdered m' l]
  [LawfulTsilTCore m'] [LawfulTsilTCoreMAlgSup m' l] [MonadFlatMapGo m m']
  {p : l → l → Prop} [LawfulMonadFlatMapGo m m' l p] : LawfulMonadFlatMapGo m (TsilT m') l p where
  go_sound := by
    introv
    simp [wp, liftM, monadLift, MAlg.lift, Functor.map, MAlgOrdered.μ, MonadFlatMapGo.go, pointwiseSup]
    apply LawfulMonadFlatMapGo.go_sound

end AngelicChoice

end Lawfulness

section Instances

-- NOTE: this function should be essentially the same as `ExceptT.bindCont`,
-- where the pure is the one of `TsilT m`, namely `fun x => [instm.pure x]`.
-- does this observation help?

-- this might indicate that the monad constructed using `TsilTCore`, and
-- the one constructed by exploiting the fact that `ExceptT` and `TsilT`
-- commute, are the same.
-- TODO can we prove this?
@[inline]
def ExceptT.TsilTCore.op {ε : Type u} {m : Type u → Type v}
  [inst : Pure m] {α β : Type u}
  (f : α → TsilT (ExceptT ε m) β) : Except ε α → TsilT (ExceptT ε m) β
  | Except.ok a    => f a
  | Except.error e => [inst.pure (Except.error e)]

@[always_inline]
instance [Pure m] [inst : TsilTCore m] : TsilTCore (ExceptT ε m) where
  op := fun x f => inst.op x (ExceptT.TsilTCore.op f)

instance [Monad m] [LawfulMonad m] [TsilTCore m] [inst : LawfulTsilTCore m] : LawfulTsilTCore (ExceptT ε m) where
  op_single := by
    introv
    simp +unfoldPartialApp [TsilTCore.op, ExceptT.mk, ExceptT.TsilTCore.op, pure, ExceptT.pure]
    have tmp := inst.op_single x (Except.map f)
    -- NOTE: This requires `LawfulMonad m`
    have tmp2 := ExceptT.run_map f x
    simp only [ExceptT.run] at tmp2
    -- kind of awkward ...
    rw [tmp2, ← tmp] ; congr! 1 ; ext1 a ; rcases a with e | a <;> rfl
  pure_op := by
    introv
    simp [TsilTCore.op, pure, ExceptT.pure, ExceptT.mk, LawfulTsilTCore.pure_op, ExceptT.TsilTCore.op]
  op_assoc := by
    introv
    simp [TsilTCore.op]
    have tmp := inst.op_assoc x (ExceptT.TsilTCore.op f) (ExceptT.TsilTCore.op g)
    trans ; apply tmp
    congr! 1 ; funext a
    unfold ExceptT.TsilTCore.op ; dsimp
    rcases a with e | a <;> simp [LawfulTsilTCore.pure_op]
    rfl

instance-- {m : Type u → Type v} {l ε : Type u}
  [monad_m : Monad m] [LawfulMonad m] [TsilTCore m] [CompleteLattice l]
  [MAlgOrdered m l] {hd : ε → Prop} [IsHandler hd]
  [inst : LawfulTsilTCoreMAlgSup m l] [LawfulTsilTCore' m]
  : LawfulTsilTCoreMAlgSup (ExceptT ε m) l where
  sup := by
    introv ; intro h x
    have tmp := @inst.sup (Except ε α)
    simp [TsilTCore.op, OfHd, MAlgExcept, MAlgOrdered.μ] at h ⊢

    -- TODO this is messy
    -- CHECK is this idea used anywhere else?
    -- generalize heq : (fun (e : ExceptT ε m l) => MAlgOrdered.μ ((Except.getD fun x ↦ ⌜hd x⌝) <$> e)) = ff at h ⊢
    simp only [pointwiseSup] at tmp ⊢
    -- NOTE: the requirement of `LawfulTsilTCore'` comes from observation here
    -- unfold ExceptT.TsilTCore.go
    -- let f' : Except ε α → TsilT m l := fun
    --   | Except.ok a    =>
    --     List.map (fun e => ((Except.getD fun x ↦ ⌜hd x⌝) <$> e))
    --     (f a)
    --   | Except.error e =>
    --     List.map (fun e => ((Except.getD fun x ↦ ⌜hd x⌝) <$> e))
    --     [pure (Except.error e)]
    --     -- [pure (⌜hd e⌝)]
    specialize tmp
      (fun a => List.map (fun e => ((Except.getD fun x ↦ ⌜hd x⌝) <$> e)) (ExceptT.TsilTCore.op f a))
      (fun a => List.map (fun e => ((Except.getD fun x ↦ ⌜hd x⌝) <$> e)) (ExceptT.TsilTCore.op g a))
    simp only [← LawfulTsilTCore'.op_fmap_commute, iSup_list_map] at tmp
    apply tmp ; clear tmp
    -- rintro (e | a)
    intro i ; simp only [Function.comp, pointwiseSup, iSup_list_map]
    rcases i with e | a
    · simp [ExceptT.TsilTCore.op]
    · dsimp only [ExceptT.TsilTCore.op] ; apply h

-- TODO is generalization to `WriterT` possible?

@[always_inline]
instance [Monoid κ] : TsilTCore (PeDivM κ) where
  op := fun (k1, mx) f =>
    match mx with
    | DivM.div => [(k1, DivM.div)]
    -- TODO give this a definition
    -- TODO an optimization: if `k1 = 1`, then no need to prepend
    | DivM.res x => f x |>.map (PeDivM.prepend k1)

instance [Monoid κ] : LawfulTsilTCore (PeDivM κ) where
  op_single := by
    introv ; simp [TsilTCore.op, Functor.map, PeDivM.prepend]
    rcases x with ⟨k1, x | _⟩ <;> rfl
  pure_op := by
    introv ; simp [TsilTCore.op]
    apply List.map_id'' ; rintro ⟨k1, x⟩ ; simp [PeDivM.prepend]
  op_assoc := by
    introv ; simp [TsilTCore.op]
    rcases x with ⟨k1, x | _⟩ <;> try rfl
    dsimp
    rw [List.map_flatMap, List.flatMap_map]
    apply List.flatMap_congr ; rintro ⟨k2, y | _⟩ _ <;> simp [PeDivM.prepend]
    intros ; ac_rfl

instance [Monoid κ] : LawfulTsilTCore' (PeDivM κ) where
  op_fmap_commute := by
    introv ; simp [TsilTCore.op]
    rcases x with ⟨k1, x | _⟩ <;> simp [Functor.map]
    rintro ⟨k2, y | _⟩ _ <;> simp [PeDivM.prepend]

instance [Monoid κ] [CompleteLattice l] [inst : MAlgOrdered DivM l]  -- only rely on the second component
  : LawfulTsilTCoreMAlgSup (PeDivM κ) l where
  sup := by
    introv ; intro h x
    simp only [TsilTCore.op, pointwiseSup, MAlgOrdered.μ] at h ⊢
    rcases x with ⟨k1, x | _⟩ <;> try trivial
    dsimp
    repeat rw [iSup_list_map]
    apply h

end Instances

end TsilT
