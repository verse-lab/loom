import Init.Control.Lawful

/-! A computation returns a value or records divergence. Order/CCPO semantics
are supplied separately by the algebra layer. -/

universe u

inductive DivM (α : Type u) where
  | res (x : α)
  | div

def DivM.run {α : Type u} [Inhabited α] : DivM α -> α
  | DivM.res x => x
  | DivM.div => default

instance : Monad DivM where
  pure := DivM.res
  bind := fun x y => match x with
    | DivM.res x => y x
    | DivM.div => DivM.div

instance : LawfulMonad DivM := by
  refine LawfulMonad.mk' _ ?_ ?_ ?_
  { intro α x; cases x <;> rfl }
  { intros; rfl }
  intro α β γ x f g; cases x <;> rfl
