module

public import Loom.MonadAlgebras.NonDetT'.ExtractListCore
public meta import Loom.Util.Meta
public meta import Loom.MonadAlgebras.WP.Attr
meta import Lean.Elab.ConfigEval
import all Init.Data.List.Control

open Loom Loom.Order

@[expose] public section

namespace MultiExtractor

section

open Lean.Order

-- the problem is: how to construct the target monad,
-- **based on the structure of the original `NonDetT m α`**?
-- this dependency cannot be skipped in any way; otherwise we cannot
-- obtain any guarantee.

variable
  (κ : Type q)
  (m : Type u → Type v) (m' : Type u → Type w)
  [inst1 : Monad m']
  [inst2 : MonadFlatMapGo m m']
  [inst3 : MonadFlatMap' m']
  [inst4 : MonadPersistentLog κ m']
  {findable : {τ : Type u} → (τ → Prop) → Type u}
  (findOf : ∀ {τ : Type u} (p : τ → Prop), ExtCandidates findable κ p → Unit → List τ)

abbrev findOfCandidates : ∀ {τ : Type u} (p : τ → Prop), ExtCandidates Candidates κ p → Unit → List τ :=
  (fun p (ec : ExtCandidates Candidates κ p) => ec.core.find)

abbrev findOfPartialCandidates : ∀ {τ : Type u} (p : τ → Prop), ExtCandidates PartialCandidates κ p → Unit → List τ :=
  (fun p (ec : ExtCandidates PartialCandidates κ p) => ec.core.find)

-- TODO `Prop` or `Type _`?
inductive ExtractConstraint : {α : Type u} → (s : NonDetT m α) → m' α → Prop where
  | pure {α : Type u} {x : α} :
    ExtractConstraint (NonDetT.pure x) (inst1.pure x)
  | vis {α β : Type u} (x : m β) (f : β → NonDetT m α) (f' : β → m' α) :
    (∀ y, ExtractConstraint (f y) (f' y)) →
    ExtractConstraint (NonDetT.vis x f) (inst1.bind (inst2.go x) f')
  | pickCont {α : Type u} (τ : Type u) (p : τ → Prop) (f : τ → NonDetT m α) (f' : τ → m' α)
    [instec : ExtCandidates findable κ p] :
    (∀ y, ExtractConstraint (f y) (f' y)) →
    ExtractConstraint (NonDetT.pickCont τ p f)
      (inst3.op (findOf p instec () |>.map (fun x => inst1.bind
        (inst4.log (ExtCandidates.rep findable p (self := instec) x))
        (fun _ => f' x))))
  -- NOTE: without `.{u+1}`, some weird universe level will pop up
  -- NOTE: due to unknown reason, using this instead of `.assume` might cause
  -- unification failure in some cases
  | assumeCont {α : Type u} (p : PUnit.{u+1} → Prop) (f : PUnit.{u+1} → NonDetT m α) (f' : PUnit.{u+1} → m' α)
    [Decidable (p .unit)] :
    (ExtractConstraint (f .unit) (f' .unit)) →
    ExtractConstraint (NonDetT.pickCont PUnit p f)
      (if p .unit then f' .unit else inst3.op [])

/-- A "boxed" version of `ExtractConstraint`, to carry both the extracted
value and the proof that it satisfies the constraint. Used in making
extraction compositional. -/
structure ConstrainedExtractResult {α : Type u} (s : NonDetT m α) where
  val : m' α
  proof : ExtractConstraint κ m m' findOf s val

def ConstrainedExtractResult.pure {α : Type u} (x : α) :
  ConstrainedExtractResult κ m m' findOf (pure x) where
  val := inst1.pure x
  proof := ExtractConstraint.pure

def ExtractConstraint.toConstrainedExtractResult {α : Type u} {s : NonDetT m α} {s' : m' α}
  (h : ExtractConstraint κ m m' findOf s s') : ConstrainedExtractResult κ m m' findOf s := ⟨s', h⟩

open Lean Meta Elab Tactic in
/-- Try all `Decidable` instances in the context to find one to apply to
close the goal. Dedicated to be used by `ConstrainedExtractResult.assume`. -/
scoped elab "find_local_decidable_and_apply" : tactic => do
  for hyp in ← getLCtx do
    if hyp.isImplementationDetail then
      continue
    let ty ← instantiateMVars hyp.type
    if ty.getForallBody.getAppFn'.isConstOf ``Decidable then
      try
        evalTactic (← `(tactic| solve | apply $(mkIdent hyp.userName)))
        return
      catch _ =>
        pure ()
  throwError "no applicable Decidable instance found in the context"

def ConstrainedExtractResult.assume (p : Prop) [decp : Decidable p] :
  ConstrainedExtractResult κ m m' findOf (MonadNonDet.assume (m := NonDetT m) p) where
  val := (if p then inst1.pure .unit else inst3.op [])
  proof := by apply ExtractConstraint.assumeCont ; constructor

def ConstrainedExtractResult.pickList (p : τ → Prop) [instec : ExtCandidates findable κ p] :
  ConstrainedExtractResult κ m m' findOf (MonadNonDet.pickSuchThat (m := NonDetT m) τ p) where
  val := (inst3.op (findOf p instec () |>.map (fun x => inst1.bind
      (inst4.log (ExtCandidates.rep findable p (self := instec) x))
      (fun _ => inst1.pure x))))
  proof := by apply ExtractConstraint.pickCont ; intros ; constructor

def ConstrainedExtractResult.liftM [LawfulMonad m'] (x : m α) :
  ConstrainedExtractResult κ m m' findOf (liftM (n := NonDetT m) x) where
  val := (inst2.go x)
  proof := by
    dsimp [_root_.liftM, monadLift, MonadLift.monadLift]
    rw [← bind_pure (MonadFlatMapGo.go x)]
    apply ExtractConstraint.vis ; intros ; constructor

def ConstrainedExtractResult.pick [instec : ExtCandidates findable κ (fun (_ : τ) => True)] :
  ConstrainedExtractResult κ m m' findOf (MonadNonDet.pick (m := NonDetT m) τ) where
  val := (inst3.op (findOf (fun _ => True) instec () |>.map (fun x => inst1.bind
      (inst4.log (ExtCandidates.rep findable (fun _ => True) (self := instec) x))
      (fun _ => inst1.pure x))))
  proof := by apply ExtractConstraint.pickCont ; intros ; constructor

def ConstrainedExtractResult.ite {α : Type u} (p : Prop)
  (dec : Decidable p)   -- disallow synthesizing
  {s1 : NonDetT m α} {s2 : NonDetT m α}
  (h1 : ConstrainedExtractResult κ m m' findOf s1)
  (h2 : ConstrainedExtractResult κ m m' findOf s2) :
  ConstrainedExtractResult κ m m' findOf (@_root_.ite _ p dec s1 s2) where
  val := (@_root_.ite _ p dec h1.val h2.val)
  proof := by split ; exact h1.proof ; exact h2.proof

-- TODO remove this repetition
theorem ExtractConstraint.bind
  [LawfulMonad m']
  [MonadFlatMap'BindDistributive m']
  {α β : Type u} {s : NonDetT m α} {s' : m' α}
  {f : α → NonDetT m β} {f' : α → m' β}
  (hs : ExtractConstraint κ m m' findOf s s')
  (hf : ∀ x, ExtractConstraint κ m m' findOf (f x) (f' x)) :
  ExtractConstraint κ m m' findOf (s >>= f) (inst1.bind s' f') := by
  induction hs generalizing hf with
  | @pure x => simp [Bind.bind, NonDetT.bind] ; exact hf x
  | @vis β x g g' h ih =>
    simp [Bind.bind, NonDetT.bind] ; constructor
    intro y ; apply ih ; assumption
  | @pickCont τ p g g' extcd h ih =>
    simp [Bind.bind, NonDetT.bind]
    rw [← MonadFlatMap'BindDistributive.bind_distrib, List.map_map] ; simp +unfoldPartialApp [Function.comp]
    apply ExtractConstraint.pickCont
    intros ; apply ih ; assumption
  | @assumeCont p g g' _ h ih =>
    simp [Bind.bind, NonDetT.bind]
    have eq : ((if p PUnit.unit then g' PUnit.unit else MonadFlatMap'.op []) >>= f') =
      ((if p PUnit.unit then g' PUnit.unit >>= f' else MonadFlatMap'.op [])) := by
      split <;> try rfl
      rw [← MonadFlatMap'BindDistributive.bind_distrib] ; rfl
    rw [eq] ; clear eq
    -- some very weird unification failure happens here, so need to provide arguments explicitly
    apply ExtractConstraint.assumeCont (p := p) (f' := (fun _ => g' PUnit.unit >>= f'))
    apply ih ; assumption

def ConstrainedExtractResult.bind
  [LawfulMonad m']
  [MonadFlatMap'BindDistributive m']
  {α β : Type u} {s : NonDetT m α}
  {f : α → NonDetT m β}
  (hs : ConstrainedExtractResult κ m m' findOf s)
  (hf : ∀ x, ConstrainedExtractResult κ m m' findOf (f x)) :
  ConstrainedExtractResult κ m m' findOf (s >>= f) where
  val := (inst1.bind hs.val (hf · |>.val))
  proof := by
    apply ExtractConstraint.bind
    · exact hs.proof
    · intro x ; exact (hf x).proof

def ConstrainedExtractResult.filterAuxM
  (κ : Type q)
  -- NOTE: `Bool` has universe level `1`, so need to take care of the levels of `m` and `m'` here
  (m : Type → Type v) (m' : Type → Type w)
  [inst1 : Monad m']
  [inst2 : MonadFlatMapGo m m']
  [inst3 : MonadFlatMap' m']
  [inst4 : MonadPersistentLog κ m']
  {findable : {τ : Type} → (τ → Prop) → Type}
  (findOf : ∀ {τ : Type} (p : τ → Prop), ExtCandidates findable κ p → Unit → List τ)
  [LawfulMonad m']
  [MonadFlatMap'BindDistributive m']
  {α : Type _}
  {s : α → NonDetT m Bool}
  {l l' : List α}
  (h : ∀ a : α, ConstrainedExtractResult κ m m' findOf (s a)) :
  ConstrainedExtractResult κ m m' findOf (l.filterAuxM s l') where
  val := (l.filterAuxM (fun a => h a |>.val) l')
  proof := by
    induction l generalizing l' with
    | nil => dsimp ; constructor
    | cons x l ih =>
      apply ExtractConstraint.bind
      · apply (h x).proof
      · rintro ⟨_ | _⟩ <;> dsimp <;> apply ih

/-! ## Sharing `let`s during extraction

Loom's extraction rules are indexed by the shape of the source program, and
none of them matches a `let`. Without the rules below, `apply` whnfs the goal
and every `let` in the chain is zeta-reduced away, so the continuation shared by
a branching statement (Lean's `do` elaborator binds it to a `__do_jp` join
point) is extracted once per branch and the extracted term grows exponentially
in the number of sequential branches.

Two constructions restore the sharing. Join points need separate source and
target bindings, while ordinary values can keep the same binding on both sides.

* `shareJoinPoint` is for a `let` whose bound value returns a computation in the
  monad being extracted, with any number of arguments. Its `hbody` premise is
  stated for an arbitrary source join point `jpS` paired with an arbitrary
  extracted counterpart `jp'` and a proof relating the two, so the recursive
  extraction of the body can discharge every jump with `⟨jp' xs, hrel xs⟩`
  instead of re-extracting the continuation.
* `shareValueLet` moves an ordinary value `let` outside the extraction goal.
  Introducing it keeps its definition available to instance synthesis and
  normalisation. The extracted result retains the binding; `simpExtractedValueLet`
  then moves its `.val` projection inside the `let` without substituting the value.

### Viewing `ExtractConstraint` From the Perspective of Logical Relations

`ExtractConstraint κ m m' findOf : NonDetT m α → m' α → Prop` can be seen as
a *logical relation* between the source monad and the target monad, and
`ConstrainedExtractResult κ m m' findOf s` is its computational packaging: a
target term together with a proof that it is related to `s`.

`shareJoinPoint` below constructs the `let`/λ case of such a relation's
abstraction theorem. Its premises say: given a related pair of join points, and
a body construction that is *uniform* in the related pair, the whole `let` is related. Readers who
know parametricity will recognise the shape — the relation lifted along an
arrow, `f R→ g  iff  ∀ x, R (f x) (g x)`, is exactly the `hrel` premise.

The analogy stops in one important place. Lean's type theory has no internal
parametricity, so uniformity is not something we can *derive* as a free theorem.
It is written down as a hypothesis and then discharged constructively: the
extraction tactic runs on the body with the join point held opaque, which is
precisely what it means to build the term uniformly. Parametricity here is a
proof obligation we happen to be able to meet, not a metatheorem we appeal to.

NOTE: The following definitions are mostly for *demonstration*. They are not
actually used in the extraction.

-/

section SharedLets

open MultiExtractor

universe q u v w s

variable (κ : Type q) (m : Type u → Type v) (m' : Type u → Type w)
  [inst1 : Monad m'] [inst2 : MonadFlatMapGo m m'] [inst3 : MonadFlatMap' m']
  [inst4 : MonadPersistentLog κ m']
  {findable : {τ : Type u} → (τ → Prop) → Type u}
  (findOf : ∀ {τ : Type u} (p : τ → Prop), ExtCandidates findable κ p → Unit → List τ)

/- NOTE: Why the rule quantifies over a target-side name `jp'`.

Sharing is a property of the term this rule produces, so it has to be visible in
`val`. What we want is

```
let jp' := <extracted continuation>
<extracted body, with `jp'` written at each jump site>
```

For the second line to mention the *variable* `jp'` rather than a copy of the
first line, the extraction of the body must be a function of `jp'`. That is what
`hbody` is: the tactic builds `fun jpS jp' hrel => <extraction>`, in which `jp'`
occurs once per jump, and the `let` in `val` binds it once. After zeta/beta the
large term appears only in the `let`'s value.

Concretely, for
```
have jp : Unit → NonDetT m .. := fun r => (if flag then c := c + 2)
if flag then (c := c + 1; jp r) else jp ()
```
this rule yields
```
have jp' : Unit → m' .. := fun r => (if flag then .. c + 2 ..)
if flag then (.. c + 1 ..; jp' r) else jp' ()
```
whereas a rule that handed `hbody` a fixed target term would inline the `c + 2`
branch into both arms — one copy per branch, hence 2^n over n sequential `if`s.
-/

/- NOTE: Why the rule also quantifies over the *source* join point `jpS`.

Logically this is not needed: fixing the concrete `jp` in `hbody`,

```
hbody : ∀ (jp' : β → m' α),
    (∀ x, ExtractConstraint .. (jp x) (jp' x)) → CER .. (body jp)
```

states an equally true proposition. It fails on the tactic side. `jp` is a
concrete lambda, so `body jp` beta-reduces and every jump site turns into a
genuine copy of the source continuation. The recursive extraction reaching such
a site sees ordinary code, not a jump, and dutifully extracts it again; nothing
in the goal marks the site as one where `hrel` should be used, so sharing is
merely hoped for.

Quantifying over `jpS` makes it forced instead. After `intro`, `jpS` is an
opaque local, each jump site has the syntactic shape `jpS x`, and no extraction
rule matches an application of an opaque variable — so the only way to close
`CER .. (jpS x)` is `⟨jp' x, hrel x⟩`. This is also what makes the cheap
`subject.getAppFn.isFVar` test in `extract_let_step` a sound way to
recognise a jump.

Incidentally, `hrel` is the local counterpart of the `@[multiextracted]`
mechanism: the global attribute records "this source procedure has already been
extracted, and here is its target", to be found via a discrimination tree;
`hrel` records the same fact for a join point, scoped to the body being
extracted and found by scanning the local context.

-/

/-- Extract a join point of arity one without duplicating its body. -/
def ConstrainedExtractResult.joinPoint {α δ β : Type u}
    {jp : β → NonDetT m α} {body : (β → NonDetT m α) → NonDetT m δ}
    (hjp : ∀ x, ConstrainedExtractResult κ m m' findOf (jp x))
    (hbody : ∀ (jpS : β → NonDetT m α) (jp' : β → m' α),
        (∀ x, ExtractConstraint κ m m' findOf (jpS x) (jp' x)) →
        ConstrainedExtractResult κ m m' findOf (body jpS)) :
    ConstrainedExtractResult κ m m' findOf (let j := jp; body j) where
  val :=
    let jp' := fun x => (hjp x).val
    (hbody jp jp' (fun x => (hjp x).proof)).val
  proof := (hbody jp (fun x => (hjp x).val) (fun x => (hjp x).proof)).proof

/-- Extract a join point of arity zero without duplicating its body. -/
def ConstrainedExtractResult.joinPoint₀ {α δ : Type u}
    {jp : NonDetT m α} {body : NonDetT m α → NonDetT m δ}
    (hjp : ConstrainedExtractResult κ m m' findOf jp)
    (hbody : ∀ (jpS : NonDetT m α) (jp' : m' α),
        ExtractConstraint κ m m' findOf jpS jp' →
        ConstrainedExtractResult κ m m' findOf (body jpS)) :
    ConstrainedExtractResult κ m m' findOf (let j := jp; body j) where
  val :=
    let jp' := hjp.val
    (hbody jp jp' hjp.proof).val
  proof := (hbody jp hjp.val hjp.proof).proof

/-
NOTE: An earlier attempt handled `let` with a single rule:

```
(hs : ∀ y, CER .. (f y)) : CER .. (let x := s; f x)
val := let x := s; (hs x).val
```

One variable `y` serves both sides. That works for data, because extraction is
the identity on it: the source value and the target value are literally the same
object, so the `let` in `val` may bind the source `s`. Put differently, for data
the relation degenerates to equality, and equality needs only one name.

A join point is not data. Its source lives in `NonDetT m α` and its extracted
counterpart in `m' α` — different types. A single variable cannot play both
roles: it has to be a source in order to be extracted, and a target in order to
appear in `val`. So equality must become the extraction relation, and one
variable must become a pair of variables plus `hrel`. Applying the rule above to
a join point gets stuck immediately on `CER .. (y ())`, with `y` opaque as a
source and no target-side name in scope to close the goal with.

The rule was dropped for a second reason too: generalising the bound value
hides it from instance synthesis and from the `dsimp` normalisation extraction
relies on, which made the extracted term several times larger. `letValue` below
instead keeps the definition in its premise; `shareValueLet` introduces that
local definition, preserving access to the bound value.
-/

/-- Move an ordinary value `let` outside the extraction goal, retaining its
definition in the premise. `shareValueLet` constructs this rearrangement directly
so it also works when the body cannot be abstracted over an arbitrary value. -/
def ConstrainedExtractResult.letValue {γ : Type s} {δ : Type u} (v : γ)
    {body : γ → NonDetT m δ}
    (h : let x := v; ConstrainedExtractResult κ m m' findOf (body x)) :
    ConstrainedExtractResult κ m m' findOf (let x := v; body x) := h

end SharedLets

variable
  [Monad m]
  [CompleteBooleanAlgebra l]
  [MAlgOrdered m l]
  [LawfulMonad m]
  [MAlgOrdered m' l]
  [LawfulMonad m']
  [LawfulMonadPersistentLog κ m' l]
  {α : Type u} (s : NonDetT m α) (s' : m' α)
  (h : ExtractConstraint κ m m' findOf s s')
  (post : α → l)

open AngelicChoice

-- the proofs are taken from `Loom.MonadAlgebras.NonDetT'.ExtractList`

namespace AngelicChoice

include h

theorem extract_list_refines_wp
  [instl : LawfulMonadFlatMapGo m m' l GE.ge]
  [instl2 : LawfulMonadFlatMapSup m' l GE.ge]
  (findOf_sound : ∀ {τ : Type u} (p : τ → Prop) (ec : ExtCandidates findable κ p) x,
    x ∈ findOf p ec () → p x) :
  wp s' post ≤ wp s post := by
  induction h with
  | @pure x => simp [wp_pure]
  | @vis β x f f' h ih =>
    simp [NonDetT.wp_vis, wp_bind]
    have tmp := instl.go_sound _ x
    simp only [ge_iff_le] at tmp
    apply le_trans (tmp _)
    exact wp_cons _ _ _ ih
  | @pickCont τ p f f' extcd h ih =>
    simp [NonDetT.wp_pickCont]
    rename_i extcd
    specialize findOf_sound p extcd
    generalize (findOf p extcd ()) = lis at findOf_sound ⊢
    have tmp := @instl2.sound
    simp only [ge_iff_le] at tmp
    apply le_trans (tmp _ _) ; rw [iSup_list_map] ; simp only [wp_bind, LawfulMonadPersistentLog.log_sound]
    simp
    intro a hin ; apply le_trans (ih a)
    apply le_iSup_of_le a ; simp [findOf_sound _ hin]
  | @assumeCont p f f' _ h ih =>
    simp [NonDetT.wp_pickCont]
    split <;> rename_i h
    · simpa [h] using ih
    · have tmp := @instl2.sound α [] post
      simp [ge_iff_le] at tmp
      rw [tmp] ; simp

theorem wp_refines_extract_list
  [instl : LawfulMonadFlatMapGo m m' l LE.le]
  [instl2 : LawfulMonadFlatMapSup m' l LE.le]
  (findOf_complete : ∀ {τ : Type u} (p : τ → Prop) (ec : ExtCandidates findable κ p) x,
    p x → x ∈ findOf p ec ()) :
  wp s post ≤ wp s' post := by
  induction h with
  | @pure x => simp [wp_pure]
  | @vis β x f f' h ih =>
    simp [NonDetT.wp_vis, wp_bind]
    have tmp := instl.go_sound _ x
    apply le_trans' (tmp _)
    exact wp_cons _ _ _ ih
  | @pickCont τ p f f' extcd h ih =>
    simp only [NonDetT.wp_pickCont]
    specialize findOf_complete p extcd
    generalize (findOf p extcd ()) = lis at findOf_complete ⊢
    have tmp := @instl2.sound
    apply le_trans' (tmp _ _) ; rw [iSup_list_map] ; simp only [wp_bind, LawfulMonadPersistentLog.log_sound]
    simp
    intro a hin ; apply le_trans (ih a)
    apply le_iSup_of_le a ; simp [findOf_complete, hin]
  | @assumeCont p f f' _ h ih =>
    simp [NonDetT.wp_pickCont]
    intro hp ; simp [hp] ; apply ih

omit findOf h in
theorem extract_list_eq_wp
  [instl : LawfulMonadFlatMapGo m m' l Eq]
  [instl2 : LawfulMonadFlatMapSup m' l Eq]
  (h : ExtractConstraint κ m m' (findOfCandidates κ) s s') :
  wp s post = wp s' post := by
  apply le_antisymm
  · apply wp_refines_extract_list κ <;> try assumption
    intro τ p ec x; rw [Candidates.find_iff (self := ec.core)] ; exact id
  · apply extract_list_refines_wp κ <;> try assumption
    intro τ p ec x; rw [Candidates.find_iff (self := ec.core)] ; exact id

end AngelicChoice

end

end MultiExtractor

end

public meta section

namespace MultiExtractor

open Lean.Order AngelicChoice

section ExtractionTactic

open Lean Meta Elab

-- NOTE: The following reuses some of the Loom infrastructure

inductive ExtractAttr.EntryKind where
  /-- Given in the form of a `ExtractConstraint` proof. -/
  | proof
  /-- Given in the form of a `ConstrainedExtractResult` structure. -/
  | struct
deriving Inhabited, BEq

structure ExtractAttr.Entry where
  kind : ExtractAttr.EntryKind
  /-- The declaration name of the theorem or structure. -/
  name : Name
deriving Inhabited, BEq

structure ExtractAttr where
  attr : AttributeImpl
  ext  : DiscrTreeExtension ExtractAttr.Entry
deriving Inhabited

private def recognizeExtractEntry (ty : Expr) : MetaM (Option (Expr × ExtractAttr.EntryKind)) := do
  let (_xs, _bis, body) ← forallMetaTelescope ty
  let fn := body.getAppFn'
  if fn.constName? == ``ConstrainedExtractResult then
    return .some (body.getRevArg!' 0, .struct)
  else if fn.constName? == ``ExtractConstraint then
    return .some (body.getRevArg!' 1, .proof)
  else
    return none

initialize extractAttr : ExtractAttr ← do
  let ext ← mkDiscrTreeExtension `multiextractionMap
  let attrImpl : AttributeImpl := {
    name := `multiextracted
    descr := ""
    add := fun declName stx attrKind => do
      -- TODO: use the attribute kind
      unless attrKind == AttributeKind.global do
        throwError "Invalid attribute 'multiextracted', must be global"
      let env ← getEnv
      -- Ignore some auxiliary definitions (see the comments for attrIgnoreMutRec)
      attrIgnoreAuxDef declName (pure ()) do
        let some constInfo := env.find? declName
          | throwError "Declaration {declName} not found"
        let (key, kind) ← MetaM.run' do
          let ty := constInfo.type
          let some (s, kind) ← recognizeExtractEntry ty
            | throwError "Declaration {declName} does not have a valid type for 'multiextracted' attribute"
          let key ← DiscrTree.mkPath s
          return (key, kind)
        let env := ext.addEntry env ⟨key, ⟨kind, declName⟩⟩
        setEnv env
  }
  registerBuiltinAttribute attrImpl
  pure { attr := attrImpl, ext := ext }

def ExtractAttr.find? (s : ExtractAttr) (e : Expr) : MetaM (Array ExtractAttr.Entry) := do
  (s.ext.getState (← getEnv)).getMatch e

section ExtractionForLet

/-- Move `(let x := v; result).val` to `let x := v; result.val`.
Keeping the binder avoids substituting v at every use; reducing the projection
inside it then removes the extraction certificate from the executable term. -/
dsimproc_decl simpExtractedValueLet (_) := fun e => do
  -- Unfolding `.val` can expose the kernel projection before this post-step.
  let result? := match e with
    | .proj ``MultiExtractor.ConstrainedExtractResult 0 result => some result
    | _ => if e.isAppOfArity ``MultiExtractor.ConstrainedExtractResult.val 12 then
        some e.appArg! else none
  let some result := result? | return .continue
  let .letE nm ty val body nondep := result.consumeMData | return .continue
  -- The kernel projection needs no source index or instance arguments. Moving
  -- it under the binder leaves body's bound variables unchanged; revisiting
  -- handles nested lets and reduces the projection once it reaches a constructor.
  return .visit <| .letE nm ty val (.proj ``MultiExtractor.ConstrainedExtractResult 0 body) nondep

/-- Construct a sharing rule for the join point's actual telescope, including
the empty telescope. This is the term-level generalisation of `joinPoint` and
`joinPoint₀` above. The returned term abstracts over two extraction premises:

```
hjp   : ∀ xs, CER (jp xs)
hbody : ∀ jpS jp', (∀ xs, R (jpS xs) (jp' xs)) → CER (body jpS)
val   := let jp' := fun xs => (hjp xs).val
         (hbody jp jp' (fun xs => (hjp xs).proof)).val
proof := (hbody jp (fun xs => (hjp xs).val) (fun xs => (hjp xs).proof)).proof
```

Here `xs` denotes the whole telescope, preserving dependent parameter types.
The caller has checked that `varTy` ends in the same monadic result type as the
goal's subject. `val` is the source join point; `bodyE` is the source let-body,
with the join point represented by loose bound variable 0. -/
private def mkJoinPointSharingRule (goalType varTy val bodyE : Expr) : MetaM Expr := do
  -- Common parameters through the result type α. Keep the goal's instance
  -- arguments rather than synthesising them again. These two helpers build
  -- CER s and R s t with exactly those parameters.
  let params := goalType.getAppArgs.take 10
  let mkResultType (s : Expr) := mkAppN goalType.getAppFn (params.push s)
  let mkRelation (s t : Expr) :=
    mkAppOptM ``MultiExtractor.ExtractConstraint (params.map some ++ #[some s, some t])

  -- 1. Open the source telescope and replace only its result type:
  --    hjpType    = ∀ xs, CER (val xs)
  --    targetType = ∀ xs, m' α
  -- Rebinding the same xs preserves dependencies between their types. For
  -- arity zero, applying and rebinding the empty telescope do nothing.
  let (hjpType, targetType) ← forallTelescopeReducing varTy fun xs _ => do
    return (← mkForallFVars xs (mkResultType (mkAppN val xs)),
      ← mkForallFVars xs (mkApp params[2]! params[9]!))

  -- 2. State the body's premise for an opaque source/target pair, related at
  -- every argument list. Replacing bound variable 0 by jpS keeps jumps opaque
  -- during recursive extraction, so hrel must discharge them.
  let hbodyType ← withLocalDeclD `jpS varTy fun jpS =>
    withLocalDeclD `jp' targetType fun jp' => do
      let hrelType ← forallTelescopeReducing varTy fun xs _ => do
        mkForallFVars xs (← mkRelation (mkAppN jpS xs) (mkAppN jp' xs))
      withLocalDeclD `hrel hrelType fun hrel =>
        mkForallFVars #[jpS, jp', hrel] (mkResultType (bodyE.instantiate1 jpS))

  -- 3. Assume both premises and project the extracted continuation and its
  -- pointwise certificate from hjp. These are the concrete pair used below
  -- to instantiate hbody; no extraction is performed by this constructor.
  withLocalDeclD `hjp hjpType fun hjp =>
    withLocalDeclD `hbody hbodyType fun hbody => do
  let (jp', hrel) ← forallTelescopeReducing varTy fun xs _ => do
    let extracted := mkAppN hjp xs
    return (← mkLambdaFVars xs (mkProj ``MultiExtractor.ConstrainedExtractResult 0 extracted),
      ← mkLambdaFVars xs (mkProj ``MultiExtractor.ConstrainedExtractResult 1 extracted))

  -- 4. Build the executable value with one explicit target let. hbody's value
  -- refers to j at each jump, so later reduction retains the shared binding.
  -- hrel relates the source to j's defining value, not to an arbitrary j:
  -- this let must stay dependent so proof abstraction retains that equality.
  let target ← withLetDecl `jp' targetType jp' fun j => do
    let body := mkProj ``MultiExtractor.ConstrainedExtractResult 0 (mkAppN hbody #[val, j, hrel])
    mkLetFVars #[j] body (generalizeNondepLet := false)

  -- 5. The certificate uses the same hbody with the concrete target inlined.
  -- Its source is definitionally the original source let, and its target is
  -- definitionally the executable value above. Package both fields, then
  -- abstract the premises to return `fun hjp hbody => ⟨target, proof⟩`.
  let proof := mkProj ``MultiExtractor.ConstrainedExtractResult 1 (mkAppN hbody #[val, jp', hrel])
  let result ← mkAppOptM ``MultiExtractor.ConstrainedExtractResult.mk
    (params.map some ++ #[some goalType.appArg!, some target, some proof])
  mkLambdaFVars #[hjp, hbody] result

/-- Configuration for the `let`-handling extraction step. -/
structure ExtractLetConfig where
  /-- If true (default), an ordinary value `let` is kept shared in the extracted
  term by reassociating the goal as `let x := v; CER body`. If false, the binding
  is zeta-reduced instead. Sharing keeps the extracted term smaller, but the
  compiler's own `pullInstances` and `cse` passes run before its first `simp`
  and recover the sharing anyway, so measure before paying for it. Join points
  are shared either way: inlining those duplicates the continuation per branch
  and is exponential, which no later pass can undo. -/
  shareValueLets : Bool := true
  deriving Inhabited

declare_config_elab elabExtractLetConfig ExtractLetConfig

open Tactic in
/-- Handle an extraction goal whose subject is a `let` or a jump to a join point
that an earlier `let` step abstracted.

The two cases live in one tactic because they are decided by the same match on
the subject and are mutually exclusive: a `let`-headed subject is never an
application of a local join point, and vice versa. -/
scoped syntax (name := extractLetStep) "extract_let_step" optConfig : tactic

open Tactic in
@[tactic extractLetStep]
def evalExtractLetStep : Tactic := fun stx => withMainContext do
  let cfg ← elabExtractLetConfig stx[1]
  let goalType ← Loom.Meta.getMainTarget
  let_expr MultiExtractor.ConstrainedExtractResult eκ em em' e1 e2 e3 e4 efindable efindOf eα es :=
      goalType
    | throwError "goal is not a `ConstrainedExtractResult` application"
  -- A nested join point arrives as a beta-redex `(fun x => let j := ..; ..) x`.
  let subject := es.consumeMData.headBeta
  let subjectType ← inferType es
  match subject with
  | .letE varName varTy val bodyE _ =>
    match ← monadicLetArity varTy subjectType with
    | some n =>
      trace[veil.extraction] "[{decl_name%}]: sharing join point {varName} of arity {n}"
      shareJoinPoint goalType varTy val bodyE
    | none =>
      if cfg.shareValueLets then
        trace[veil.extraction] "[{decl_name%}]: sharing value {varName}"
        shareValueLet goalType varName varTy val bodyE
      else
        trace[veil.extraction] "[{decl_name%}]: inlining value {varName}"
        inlineValueLet goalType val bodyE
  | _ =>
    let subjectFn := subject.getAppFn
    unless subjectFn.isFVar do
      throwError "the subject is neither a `let` nor a jump to a local join point"
    let args := subject.getAppArgs
    for ldecl in ← getLCtx do
      if ldecl.isImplementationDetail then continue
      unless ldecl.type.getForallArity == args.size do continue
      let result? ← observing? do
        let h ← mkAppOptM' ldecl.toExpr (args.map some)
        let hType ← instantiateMVars (← inferType h)
        let_expr MultiExtractor.ExtractConstraint _ _ _ _ _ _ _ _ _ _ _ tgt := hType
          | throwError "hypothesis is not an extraction certificate"
        let e ← mkAppOptM ``MultiExtractor.ConstrainedExtractResult.mk
          #[some eκ, some em, some em', some e1, some e2, some e3, some e4,
            some efindable, some efindOf, some eα, some subject, some tgt, some h]
        Tactic.closeMainGoal `extract_let_step e
      if result?.isSome then return
    throwError "no join-point extraction hypothesis applies to this jump"
where
  /-- Arity of a `let` binding that is a computation in the monad being extracted,
  or `none` for an ordinary value binding. `subjectType` is the type of the goal's
  subject, so this recognises join points by type rather than by the `__do_jp`
  name the `do` elaborator happens to use. -/
  monadicLetArity (letType subjectType : Expr) : MetaM (Option Nat) :=
    forallTelescopeReducing letType fun binders resultType => do
      if ← withNewMCtxDepth (isDefEq resultType subjectType) then
        return some binders.size
      else
        return none
  /-- Apply the generated rule, leaving the continuation and body extraction
  premises as the two subgoals for the extraction loop. -/
  shareJoinPoint (goalType varTy val bodyE : Expr) : TacticM Unit := do
    let rule ← mkJoinPointSharingRule goalType varTy val bodyE
    replaceMainGoal (← (← getMainGoal).apply rule)
  /-- Reassociate `CER (let x := v; body)` as `let x := v; CER body`.
  The extraction loop's next `intros` introduces `x := v`, so its value remains
  available to type checking and instance synthesis. Unlike a lambda over an
  arbitrary x, this also handles bodies whose typing relies on x's definition. -/
  shareValueLet (goalType : Expr) (varName : Name) (varTy val bodyE : Expr) : TacticM Unit := do
    -- bodyE's loose bound variable 0 is bound by the new outer let. The other
    -- goal arguments are already closed relative to the current local context.
    let bodyGoal := Loom.Meta.setAppArg goalType 10 bodyE
    let goalType' := Expr.letE varName varTy val bodyGoal false
    replaceMainGoal [← (← getMainGoal).change goalType']
  /-- Zeta-reduce `CER (let x := v; body)` to `CER body[v]`, one binding at a time.
  This is the counterpart of `shareValueLet` for `-shareValueLets`. Reducing the
  binding here rather than letting the fallback rules' `apply` whnf the goal
  matters: whnf would reduce the whole chain of `let`s at once and take any join
  point further down with it, which is what makes extraction exponential. -/
  inlineValueLet (goalType val bodyE : Expr) : TacticM Unit := do
    let goalType' := Loom.Meta.setAppArg goalType 10 (bodyE.instantiate1 val)
    replaceMainGoal [← (← getMainGoal).change goalType']

end ExtractionForLet

open Tactic in
elab "extract_list_use_extracted" : tactic => withMainContext do
  let goal ← Loom.Meta.getMainTarget
  let some (ty, _) ← recognizeExtractEntry goal
    | throwError "Could not recognize the goal as an extraction goal"
  let entries ← extractAttr.find? ty
  for entry in entries do
    try
      match entry.kind with
      | .proof => failure   -- for convenience, just not handle this case
      | .struct =>
        let mv ← getMainGoal
        let mvs ← mv.applyConst entry.name (cfg := { synthAssignedInstances := false })
        replaceMainGoal mvs
      trace[veil.extraction] "Applied extracted result: {entry.name}"
      return
    catch _ =>
      pure ()
  throwError "No applicable extracted result found for the goal"

/-- The fallback case for extraction, where the goal cannot be recognized by
`extract_list_use_extracted`. -/
macro "extract_list_step_fallback" : tactic =>
  `(tactic|
    first
      | apply $(Lean.mkIdent ``ConstrainedExtractResult.bind)
      | apply $(Lean.mkIdent ``ConstrainedExtractResult.liftM)
      | apply $(Lean.mkIdent ``ConstrainedExtractResult.assume) _ _ _ ($(Lean.mkIdent `decp) := by first | find_local_decidable_and_apply | infer_instance)
      | apply $(Lean.mkIdent ``ConstrainedExtractResult.pickList)
      | apply $(Lean.mkIdent ``ExtractConstraint.toConstrainedExtractResult) <;> any_goals apply $(Lean.mkIdent ``ExtractConstraint.vis)
      | apply $(Lean.mkIdent ``ConstrainedExtractResult.pure)
      | apply $(Lean.mkIdent ``ExtractConstraint.toConstrainedExtractResult) <;> any_goals apply $(Lean.mkIdent ``ExtractConstraint.pickCont)
      | apply $(Lean.mkIdent ``ConstrainedExtractResult.ite)
    )

-- NOTE: The order of tactics in `extract_list_step` matters;
-- `extract_let_step` should be tried before `extract_list_use_extracted`
-- to ensure that let-bindings are handled first.
syntax "extract_list_step" optConfig : tactic

macro_rules
  | `(tactic| extract_list_step $cfg:optConfig) =>
    `(tactic|
      first
        | extract_let_step $cfg:optConfig
        | extract_list_use_extracted
        | extract_list_step_fallback
      )

syntax "extract_list_tactic" optConfig : tactic

macro_rules
  | `(tactic| extract_list_tactic $cfg:optConfig) =>
    `(tactic| repeat' (intros; extract_list_step $cfg:optConfig <;>
        try (dsimp -$(mkIdent `zeta))))

end ExtractionTactic

end MultiExtractor

end

@[expose] public section

namespace MultiExtractor

section

open Lean.Order

variable
  (κ : Type q)
  (m : Type u → Type v) (m' : Type u → Type w)
  [inst1 : Monad m']
  [inst2 : MonadFlatMapGo m m']
  [inst3 : MonadFlatMap' m']
  [inst4 : MonadPersistentLog κ m']
  {findable : {τ : Type u} → (τ → Prop) → Type u}
  (findOf : ∀ {τ : Type u} (p : τ → Prop), ExtCandidates findable κ p → Unit → List τ)

variable
  [Monad m]
  [CompleteBooleanAlgebra l]
  [MAlgOrdered m l]
  [LawfulMonad m]
  [MAlgOrdered m' l]
  [LawfulMonad m']
  [LawfulMonadPersistentLog κ m' l]
  {α : Type u} (s : NonDetT m α) (s' : m' α)
  (h : ExtractConstraint κ m m' findOf s s')
  (post : α → l)

open AngelicChoice

def NonDetT.extractList {α : Type u} (s : NonDetT m α)
  (h : ConstrainedExtractResult κ m m' (findOfCandidates κ) s := by extract_list_tactic)
  : m' α := h.val

def NonDetT.extractPartialList {α : Type u} (s : NonDetT m α)
  (h : ConstrainedExtractResult κ m m' (findOfPartialCandidates κ) s := by extract_list_tactic)
  : m' α := h.val

end

end MultiExtractor
