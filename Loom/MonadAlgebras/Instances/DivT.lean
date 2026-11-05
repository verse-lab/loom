module

public import Loom.MonadAlgebras.Defs
public import Loom.MonadAlgebras.Instances.Basic

@[expose] public section

/-! # `DivT`: a diverging result inside a monad

`DivT m α := m (DivM α)`: a computation of `m` whose result may be divergence. Whatever `m`
carries (a log, say) sits outside the `DivM`, so it survives divergence: `PeDivM κ` is `DivT` of
the writer `(κ × ·)`.

The algebra of `DivT m` is built from those of `m` and of `DivM`: a result is read by `DivM`'s
algebra (`DivM.total`: divergence is `⊥`; `PartialCorrectness`: `⊤`), the rest by `m`'s. It is
`MAlgExcept` with `DivM`'s `μ` in place of the handler `Except.getD ⌜hd ·⌝`, so the reading of
divergence is the one of `DivM` in scope, independent of any `IsHandler`. -/

-- NOTE: The definitions follow `ExceptT` in `Init/Control/Except.lean`, markers included: `mk`
-- and `run` are `@[always_inline, inline]`, the monad operations are `protected` (so that `pure`
-- and `bind` inside the namespace still mean `Pure.pure` and `Bind.bind`) and inlined, the
-- `Monad` instance is `@[always_inline]`. `PeDivM` in `Loom/Control/Persistent.lean` does the same.

open Loom Loom.Order

universe u v

@[implicit_reducible] def DivT (m : Type u → Type v) (α : Type u) : Type v := m (DivM α)

namespace DivT

variable {m : Type u → Type v} {α β : Type u}

@[always_inline, inline]
def mk (x : m (DivM α)) : DivT m α := x

@[always_inline, inline]
def run (x : DivT m α) : m (DivM α) := x

@[simp] theorem run_mk (x : m (DivM α)) : (mk x).run = x := rfl

section Monad
variable [Monad m]

@[always_inline, inline]
protected def pure (a : α) : DivT m α := mk (pure (.res a))

/-- Continue after a result; stop at divergence. -/
@[always_inline, inline]
protected def bindCont (f : α → DivT m β) : DivM α → m (DivM β)
  | .res a => (f a).run
  | .div => pure .div

@[always_inline, inline]
protected def bind (x : DivT m α) (f : α → DivT m β) : DivT m β :=
  mk (x.run >>= DivT.bindCont f)

/-- A computation of `m` as a converging computation. -/
@[always_inline, inline]
protected def lift (x : m α) : DivT m α := mk (.res <$> x)

/-- A result of `DivM` as a computation: `DivM` lifts into every `DivT m`. -/
@[always_inline, inline]
protected def ofDivM (x : DivM α) : DivT m α := mk (pure x)

@[always_inline]
instance : Monad (DivT m) where
  pure := DivT.pure
  bind := DivT.bind

instance : MonadLift m (DivT m) := ⟨DivT.lift⟩

instance : MonadLift DivM (DivT m) := ⟨DivT.ofDivM⟩

@[simp] theorem run_pure (a : α) : (pure a : DivT m α).run = pure (.res a) := rfl
@[simp] theorem run_bind (x : DivT m α) (f : α → DivT m β) :
    (x >>= f).run = x.run >>= DivT.bindCont f := rfl
@[simp] theorem bindCont_res (f : α → DivT m β) (a : α) : DivT.bindCont f (.res a) = (f a).run :=
  rfl
@[simp] theorem bindCont_div (f : α → DivT m β) : DivT.bindCont f .div = pure .div := rfl
@[simp] theorem lift_run (x : m α) : (DivT.lift x).run = .res <$> x := rfl
@[simp] theorem ofDivM_run (x : DivM α) : (DivT.ofDivM x : DivT m α).run = pure x := rfl
@[simp] theorem run_liftM (x : m α) : (liftM (n := DivT m) x).run = .res <$> x := rfl
@[simp] theorem run_liftM_DivM (x : DivM α) : (liftM (n := DivT m) x).run = pure x := rfl

variable [LawfulMonad m]

instance : LawfulMonad (DivT m) :=
  LawfulMonad.mk' (DivT m)
    (id_map := fun x => by
      show x.run >>= DivT.bindCont (pure ∘ id) = x.run
      exact (bind_congr fun d => by cases d <;> rfl).trans (bind_pure x.run))
    (pure_bind := fun a f => by
      show pure (DivM.res a) >>= DivT.bindCont f = (f a).run
      simp only [pure_bind, bindCont_res])
    (bind_assoc := fun x f g => by
      show (x.run >>= DivT.bindCont f) >>= DivT.bindCont g = x.run >>= DivT.bindCont (f · >>= g)
      rw [bind_assoc]
      refine bind_congr fun d => ?_
      cases d
      · rfl
      · exact pure_bind _ _)

instance : LawfulMonadLift m (DivT m) where
  monadLift_pure a := by
    show DivM.res <$> pure a = pure (DivM.res a)
    exact map_pure _ _
  monadLift_bind x f := by
    show DivM.res <$> (x >>= f) = (DivM.res <$> x) >>= DivT.bindCont (fun a => DivT.lift (f a))
    simp only [map_bind, bind_map_left, bindCont_res, lift_run]

end Monad

/-! ## The algebra -/

section Algebra
variable {l : Type u} [Monad m] [LawfulMonad m] [CompleteLattice l]
  [instm : MAlgOrdered m l] [instd : MAlgOrdered DivM l]

/-- The algebra of `DivT m` from those of `m` and `DivM`: read each result by `DivM`'s algebra,
then the computation by `m`'s. -/
instance : MAlgOrdered (DivT m) l where
  μ x := instm.μ (instd.μ <$> x.run)
  μ_ord_pure a := by
    show instm.μ (instd.μ <$> pure (DivM.res a)) = a
    have h : instd.μ (DivM.res a) = a := instd.μ_ord_pure a
    rw [map_pure, h, instm.μ_ord_pure]
  μ_ord_bind f g h x := by
    show instm.μ (instd.μ <$> (x.run >>= DivT.bindCont f)) ≤
      instm.μ (instd.μ <$> (x.run >>= DivT.bindCont g))
    rw [map_bind, map_bind]
    apply instm.μ_ord_bind
    rw [pi_le_iff]
    intro d
    cases d with
    | res a => exact (pi_le_iff _ _).mp h a
    | div => exact le_refl _

theorem _root_.MAlg.lift_DivT (x : DivT m α) (post : α → l) :
    MAlg.lift x post = MAlg.lift (m := m) x.run fun d => MAlg.lift d post := by
  show instm.μ (instd.μ <$> (x.run >>= DivT.bindCont (fun a => pure (post a)))) =
    instm.μ ((fun d => instd.μ (post <$> d)) <$> x.run)
  rw [map_bind, ← bind_pure_comp]
  congr 1
  refine bind_congr fun d => ?_
  cases d
  · exact map_pure _ _
  · exact map_pure _ _

instance [instm' : MAlgDet m l] [instd' : MAlgDet DivM l] : MAlgDet (DivT m) l where
  angelic c p _ := by
    simp only [MAlg.lift_DivT]
    refine le_trans ?_ (instm'.angelic c.run fun i d => MAlg.lift d (p i))
    apply Cont.monotone_lift
    intro d
    exact instd'.angelic d p
  demonic c p _ := by
    simp only [MAlg.lift_DivT]
    refine le_trans (instm'.demonic c.run fun i d => MAlg.lift d (p i)) ?_
    apply Cont.monotone_lift
    intro d
    exact instd'.demonic d p

instance [instm' : NoFailure m] [instd' : NoFailure DivM] : NoFailure (DivT m) where
  noFailure c := by
    rw [MAlg.lift_DivT]
    simp only [instd'.noFailure]
    exact instm'.noFailure c.run

/-- Lifting from `m` keeps the values: the algebra of `DivT m` restricted to converging
computations is that of `m`. -/
instance : MAlgLift m l (DivT m) l where
  cl := by exact LogicLift.refl
  μ_lift x := by
    show MAlg.lift (DivT.lift x) _ = MAlg.lift x _
    rw [MAlg.lift_DivT]
    show instm.μ ((fun d => instd.μ (_ <$> d)) <$> (DivM.res <$> x)) = instm.μ (_ <$> x)
    rw [← comp_map]
    congr 2
    funext a
    exact instd.μ_ord_pure _

end Algebra

/-! ## Order and fixpoints, as for `ExceptT` -/

section Order
open Lean.Order

instance [inst : ∀ α, CCPO (m α)] : CCPO (DivT m α) := inst _

instance [Monad m] [∀ α, CCPO (m α)] [MonoBind m] : MonoBind (DivT m) where
  bind_mono_left h := MonoBind.bind_mono_left (m := m) h
  bind_mono_right h := by
    apply MonoBind.bind_mono_right (m := m)
    intro d
    cases d
    · exact h _
    · exact PartialOrder.rel_refl

instance [CCPOBot m] : CCPOBot (DivT m) where
  compBot := CCPOBot.compBot (m := m)

variable {l : Type u} [Monad m] [LawfulMonad m] [Loom.Order.CompleteLattice l] [MAlgOrdered m l]
  [MAlgOrdered DivM l] [∀ α, CCPO (m α)]

instance [MAlgPartial m] : MAlgPartial (DivT m) where
  csup_lift xc post hc := by
    simp only [MAlg.lift_DivT]
    exact MAlgPartial.csup_lift (m := m) xc _ hc

instance [MAlgTotal m] : MAlgTotal (DivT m) where
  bot_lift post := by
    rw [MAlg.lift_DivT]
    exact MAlgTotal.bot_lift (m := m) _

end Order

end DivT
