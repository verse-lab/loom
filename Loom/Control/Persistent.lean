module

public import Loom.Control.Div
public import Loom.Control.Log

@[expose] public section

/-! Logs outside `DivM` survive divergence. Result and log universes are independent. -/

-- Keep explicit universe arguments in their original order: log, then result.
universe w u

def PeDivM (κ : Type w) (α : Type u) := κ × DivM α

@[inline, specialize inst]
def PeDivM.prepend {κ : Type w} [inst : Loom.LogMonoid κ] {α : Type u} (k : κ) : PeDivM κ α → PeDivM κ α
  | (k', a) => (Loom.LogMonoid.append k k', a)

theorem PeDivM.prepend_snd_same {κ : Type w} [Loom.LogMonoid κ] {α : Type u} (k : κ) (x : PeDivM κ α) :
  (x.prepend k).2 = x.2 := by cases x ; simp [PeDivM.prepend]

/-- Record a log even if a subsequent computation diverges. -/
@[inline]
def PeDivM.log {κ : Type w} (k : κ) : PeDivM κ PUnit :=
  (k, DivM.res PUnit.unit)

@[always_inline]
instance [Loom.LogMonoid κ] : Monad (PeDivM κ) where
  pure := fun x => (Loom.LogMonoid.empty, DivM.res x)
  bind := fun (k1, mx) f =>
    match mx with
    | DivM.res x => f x |>.prepend k1   -- TODO it's very bad that this is not tail-recursive ...
    | DivM.div => (k1, DivM.div)
  map  := fun f (k, mx) => (k, match mx with
    | DivM.res a => DivM.res (f a)
    | DivM.div   => DivM.div)

instance [Loom.LogMonoid κ] : LawfulMonad (PeDivM κ) :=
  LawfulMonad.mk' (PeDivM κ)
  (id_map := by intro α x ; simp [Functor.map] ; rcases x with ⟨k1, x | _⟩ <;> simp)
  (pure_bind := by intro α β x f ; simp [pure, bind, PeDivM.prepend] ; rfl)
  (bind_assoc := by
    intro α β γ x f g ; simp [bind, PeDivM.prepend] ; rcases x with ⟨k1, x | _⟩ <;> simp
    rcases f x with ⟨k2, y | _⟩ <;> simp
    rcases g y with ⟨k3, z | _⟩ <;> simp
    all_goals (simp only [Loom.LogMonoid.append_assoc]))
  (bind_pure_comp := by intro α β f x ; simp [pure, bind, Functor.map, PeDivM.prepend] ; rcases x with ⟨k1, x | _⟩ <;> simp)

theorem PeDivM.bind_snd {κ : Type w} {α β : Type u} [Loom.LogMonoid κ] (mx : PeDivM κ α) (f : α → PeDivM κ β) :
  (mx >>= f).2 = mx.2 >>= (Prod.snd ∘ f) := by
  rcases mx with ⟨k1, x | _⟩ <;> rfl
