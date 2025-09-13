import Lean
import Loom.MonadAlgebras.WP.Gen

open Lean Meta Elab Term

/-! # Overview

Ideally, targets of this mechanism:
1. The user does not have to do anything (like running a command) before
   or during the proof
2. (Complete not done yet, but should be feasible) The `WPGen` should be
   sound and relatively complete
3. (Not fully achieved yet) The generated `WPGen` should be reusable. This
   implies that the generated `WPGen` should be parameterized (i.e.,
   not for a specific matcher)
-/

namespace Loom.Matcher

theorem simp1 {l : Type u} [CompleteBooleanAlgebra l] {p : Prop} (proof : p) {a b : l} (h : a ≤ b) :
  ⌜p⌝ ⇨ a ≤ b := by simp [proof] ; exact h

-- theorem simp2 {l : Type u} {α : Sort v} [CompleteBooleanAlgebra l] {a b : l} {c : α} (h : a ≤ b) :
--   ⨅ (x : c = c), a ≤ b := by simp ; exact h

/-- Given `e` as the `Expr` of `∀ (x₁ : t₁) ⋯ (xₙ : tₙ), ⋯`, this returns
    `[(x₁, Expr(t₁), bi₁), ⋯, (xₙ, Expr(tₙ), biₙ)]`, where `biᵢ` is the `BinderInfo` of `xᵢ`. -/
private def getForallPremises : Expr → List (Name × Expr × BinderInfo)
  | .forallE na ty body bi =>
    (na, ty, bi) :: getForallPremises body
  | _ => []

private def List.foldldM.{u, v, w} {m : Type u → Type v} [Monad m] {s : Type u} {α : Type w} (f : s → α → m s)
  (g : α → m s) (init : s) (l : List α) : m s :=
  match l with
  | [] => pure init
  | a :: l' => do
    let init' ← g a
    List.foldlM f init' l'

/-- This is a dummy definition just for providing the arguments like `m`,
    `l` and instances. -/
def WPGen.match_template.{u, v} {m : Type u → Type v} [Monad m] -- [LawfulMonad m]
  {l : Type u} [CompleteBooleanAlgebra l] [MAlgOrdered m l] := Unit.unit

private partial def withinBranch (i n : Nat) (type mainGoal : Expr) : TermElabM Expr := do
  if n <= 1 then return mainGoal
  if i = n - 1 then
    let tmp ← mainGoal.mvarId!.applyConst ``inf_le_of_right_le
    return .mvar tmp[0]!
  let tmp ← mainGoal.mvarId!.applyConst ``inf_le_of_left_le
  withinBranch i (n - 1) type <| .mvar tmp[0]!

inductive MatcherArgCase where | dropFirst | normal
deriving BEq, Repr, ToExpr, Inhabited

structure MatcherWPGen where
  lvls : Array Name
  wpgenExpr : Expr
  matcherInfo : MatcherInfo
  monadRetTypePos : Nat
  monadArgPos : Nat
  monadInstPos : Nat
  omaTypePos : Nat
  firstMonadArgPos : Nat
  -- firstWPGenArgPos : Nat
  -- firstDiscrPos : Nat

/-! # Technical Notes

Generating `WPGen` for a matcher, assumptions:
- Each match alternative results in a monadic computation `m α`.
- Some other technical assumptions, see below.

A running example for explaining the construction:
```
method test (a : Nat) (b : Nat) (c : Nat) return (res : Nat)
  ensures res > 9
  do
    match a, b, c with
    | 2, 3, 4 => pure (10 : Nat)
    | 9, .succ b', .succ c' => pure (a + b' + c' + 10)
    | _, _, _ => pure (a + b + c + 10)

#check test.match_1
/-
test.match_1.{u_1} (motive : ℕ → ℕ → ℕ → Sort u_1) (a✝ b✝ c✝ : ℕ)
  (h_1 : Unit → motive 2 3 4)
  (h_2 : (b' c' : ℕ) → motive 9 b'.succ c'.succ)
  (h_3 : (x x_1 x_2 : ℕ) → motive x x_1 x_2) : motive a✝ b✝ c✝
-/

#check test.match_1.splitter
/-
test.match_1.splitter.{u_1} (motive : ℕ → ℕ → ℕ → Sort u_1) (a✝ b✝ c✝ : ℕ)
  (h_1 : motive 2 3 4)
  (h_2 : (b' c' : ℕ) → motive 9 b'.succ c'.succ)
  (h_3 :
    (x x_1 x_2 : ℕ) →
      (x = 2 → x_1 = 3 → x_2 = 4 → False) →
        (∀ (b' c' : ℕ), x = 9 → x_1 = b'.succ → x_2 = c'.succ → False) → motive x x_1 x_2) :
  motive a✝ b✝ c✝
-/

#check test.match_1.eq_1
/-
test.match_1.eq_1.{u_1} (motive : ℕ → ℕ → ℕ → Sort u_1)
  (h_1 : Unit → motive 2 3 4)
  (h_2 : (b' c' : ℕ) → motive 9 b'.succ c'.succ)
  (h_3 : (x x_1 x_2 : ℕ) → motive x x_1 x_2) :
  (match 2, 3, 4 with
    | 2, 3, 4 => h_1 ()
    | 9, b'.succ, c'.succ => h_2 b' c'
    | x, x_1, x_2 => h_3 x x_1 x_2) =
    h_1 ()
-/

#check test.match_1.eq_3
/-
test.match_1.eq_3.{u_1} (motive : ℕ → ℕ → ℕ → Sort u_1) (x✝ x✝¹ x✝² : ℕ)
  (h_1 : Unit → motive 2 3 4)
  (h_2 : (b' c' : ℕ) → motive 9 b'.succ c'.succ)
  (h_3 : (x x_1 x_2 : ℕ) → motive x x_1 x_2) :
  (x✝ = 2 → x✝¹ = 3 → x✝² = 4 → False) →
    (∀ (b' c' : ℕ), x✝ = 9 → x✝¹ = b'.succ → x✝² = c'.succ → False) →
      (match x✝, x✝¹, x✝² with
        | 2, 3, 4 => h_1 ()
        | 9, b'.succ, c'.succ => h_2 b' c'
        | x, x_1, x_2 => h_3 x x_1 x_2) =
        h_3 x✝ x✝¹ x✝²
-/
```

Assume we are going to construct `test.match_1.WPGen`, whose type is
`fun ... => WPGen (test.match_1 ...)`. The construction is in three steps.

## Constructing the Arguments

To achieve potential reuse, the `WPGen` should be properly parameterized.

We use the matcher itself in this step. When we set `motive` to
`fun .. => m α`, then each alternative argument corresponds to the
monadic computations for which we need to construct `WPGen`s as subgoals.

For example, for the matcher `test.match_1`, we have three alternatives:
`(h_1 : Unit → motive 2 3 4)`,
`(h_2 : (b' c' : ℕ) → motive 9 b'.succ c'.succ)`,
`(h_3 : (x x_1 x_2 : ℕ) → motive x x_1 x_2)`.
So we will have three monadic computations to consider:
`(mh_1 : Unit → m α)`,
`(mh_2 : (b' c' : ℕ) → m α)`,
`(mh_3 : (x x_1 x_2 : ℕ) → m α)`.
- The `Unit` argument of `h_1` is presumably to make `h_1` be lazily
  evaluated, and we can optimize it away. This pattern can also be
  observed in alternatives where the pattern does not contain any
  holes or variables (e.g., `match x with | none => ...`). We implicitly
  assume that this pattern can be detected by checking whether the
  `motive ...` depends on the first argument. See below where
  `MatcherArgCase` is used.
- We assume `motive` will only appear in the body position; if it also appears
  in the type of an argument, then some changes might be needed.

From the types of those monadic computations, we can figure out the types
of the `WPGen` subgoals.

For example, we just obtained three monadic computations:
`(mh_1 : m α)` (we optimize the `Unit` away),
`(mh_2 : (b' c' : ℕ) → m α)`,
`(mh_3 : (x x_1 x_2 : ℕ) → m α)`.
The corresponding `WPGen` subgoals are:
`(wpgh_1 : WPGen mh_1)`,
`(wpgh_2 : ∀ b' c', WPGen (mh_2 b' c'))`,
`(wpgh_3 : ∀ x x_1 x_2, WPGen (mh_3 x x_1 x_2))`.

Finally, we can construct the body type of the `WPGen` we are constructing,
by using the monadic computation arguments.

For example, the body type of `test.match_1.WPGen` is
```
WPGen
  (match a, b, c with
  | 2, 3, 4 => mh_1
  | 9, b'.succ, c'.succ => mh_2 b' c'
  | x, x_1, x_2 => mh_3 x x_1 x_2)
```
where the matcher, after disabling pretty printing, is
`test.match_1 (fun _ _ _ ↦ m α) a b c (fun _ ↦ mh_1) mh_2 mh_3`
(note that for `mh_1` we need to make it "lazy").

## Constructing `WPGen.get`

We use the splitter in the next two steps since it contains more information.

Each alternative of the splitter corresponds to one "branch" of the
`WPGen.get`; "branches" are connected by `⊓` (in analogy to `∧`).
In one "branch", we have a series of heading `⨅ ...` (in analogy to `∀ ...`),
and then a series of heading `⌜ ... ⌝ ⇨ ...` (in analogy to `... → ...`).
The `⌜ ... ⌝`'s consist of the inner arguments of each alternative of the
splitter and also equalities on the discriminant(s) of the matcher.
The body of the branch is the `get` of the corresponding `WPGen` subgoal.
- We implicitly assume that we can use a prefix of the arguments in an
  alternative to fill in the arguments of the corresponding `WPGen` subgoal.

For example, the splitter of `test.match_1`, `test.match_1.splitter`,
has three alternatives:
```
(h_1 : motive 2 3 4)
(h_2 : (b' c' : ℕ) → motive 9 b'.succ c'.succ)
(h_3 :
  (x x_1 x_2 : ℕ) →
    (x = 2 → x_1 = 3 → x_2 = 4 → False) →
      (∀ (b' c' : ℕ), x = 9 → x_1 = b'.succ → x_2 = c'.succ → False) → motive x x_1 x_2) :
```
The corresponding branches are:
```
-- Branch 1:
⌜a = 2⌝ ⇨ ⌜b = 3⌝ ⇨ ⌜c = 4⌝ ⇨ wpgh_1.get post
-- Branch 2:
⨅ b', ⨅ c', ⌜a = 9⌝ ⇨ ⌜b = b'.succ⌝ ⇨ ⌜c = c'.succ⌝ ⇨ (wpgh_2 b' c').get post
-- Branch 3:
⨅ x, ⨅ x_1, ⨅ x_2,
  ⌜x = 2 → x_1 = 3 → x_2 = 4 → False⌝ ⇨
    ⌜∀ (b' c' : ℕ), x = 9 → x_1 = b'.succ → x_2 = c'.succ → False⌝ ⇨
      ⌜a = x⌝ ⇨ ⌜b = x_1⌝ ⇨ ⌜c = x_2⌝ ⇨ (wpgh_3 x x_1 x_2).get post
```
Note that the equalities are generated based on how `motive ...` looks
like in each alternative. For example, in the first alternative,
`motive 2 3 4`, the arguments `2`, `3`, and `4` correspond to the
discriminants `a`, `b`, and `c`, respectively, so we have the equalities
`⌜a = 2⌝`, `⌜b = 3⌝`, and `⌜c = 4⌝`. The same applies to the other alternatives.

An optimization is to remove redundant equalities. In particular,
if in `motive ...` an argument is a variable, then we do not need to
have an equality between that variable and the corresponding discriminant;
instead, we can just use the discriminant directly. For example, in the
third alternative, `motive x x_1 x_2`, we do not need to have the equalities
`⌜a = x⌝`, `⌜b = x_1⌝`, and `⌜c = x_2⌝`; instead, we can just use `a`, `b`,
and `c` directly.

TODO This optimization is not implemented yet.

The `WPGen.get` is then `fun post => ...` where `...` is the above branches
connected by `⊓`.

TODO A conjecture is that this construction is complete, if all `WPGen`
subgoals are complete.

## Constructing `WPGen.prop`

Proving `WPGen.prop` with regard to this `WPGen.get` is relatively
straightforward. To do it at the `MetaM` level (instead of using `TacticM`),
we build the proof term using the splitter as the skeleton. That is,
the proof has the form of `fun post => test.match_1.splitter ...`.
The `motive` here is in the form of
`fun [discriminants'] => [get using discriminants'] post ≤ wp [matcher using discriminants'] post`
where `get` is the expression for `WPGen.get` we constructed in the
previous step.

For example, for `test.match_1`, the motive is
```
fun a_ b_ c_ ↦
  (⌜a_ = 2⌝ ⇨ ⌜b_ = 3⌝ ⇨ ⌜c_ = 4⌝ ⇨ wpgh_1.get post ⊓
    /- ... -/) ≤
  wp
    (match a_, b_, c_ with
    | 2, 3, 4 => mh_1
    | 9, b'.succ, c'.succ => mh_2 b' c'
    | x, x_1, x_2 => mh_3 x x_1 x_2)
    post
```
where the matcher is the one appearing in the body type of the `WPGen` we
are constructing, but note that its discriminants are substituted by
the arguments of the motive `a_, b_, c_`. Similarly for the LHS of the `≤`.

Now each alternative of the splitter corresponds to one subgoal. For
the `i`-th alternative, we use `inf_le_of_left_le` or
`inf_le_of_right_le` to choose the `i`-th branch of the `get`.

For example, for the second alternative, the corresponding subgoal is
```
∀ (b' c' : ℕ),
  /- ... -/ ⊓
    (⨅ b'_1, ⨅ c'_1, ⌜9 = 9⌝ ⇨ ⌜b'.succ = b'_1.succ⌝ ⇨ ⌜c'.succ = c'_1.succ⌝ ⇨
      (wpgh_2 b'_1 c'_1).get post) ⊓
    /- ... -/  ≤
  wp
    (match 9, b'.succ, c'.succ with
    | 2, 3, 4 => mh_1
    | 9, b'.succ, c'.succ => mh_2 b' c'
    | x, x_1, x_2 => mh_3 x x_1 x_2)
    post
```
By doing something equivalent to
`intro b' c' ; refine inf_le_of_left_le (inf_le_of_right_le ?_)`, the
subgoal is reduced to
```
(⨅ b'_1, ⨅ c'_1, ⌜9 = 9⌝ ⇨ ⌜b'.succ = b'_1.succ⌝ ⇨ ⌜c'.succ = c'_1.succ⌝ ⇨
      (wpgh_2 b'_1 c'_1).get post) ≤
  wp
    (match 9, b'.succ, c'.succ with
    | 2, 3, 4 => mh_1
    | 9, b'.succ, c'.succ => mh_2 b' c'
    | x, x_1, x_2 => mh_3 x x_1 x_2)
    post
```

After that, we use the assumptions introduced by `intro` or `rfl`s
to "discharge" the heading `⌜ ... ⌝`'s. We use `iInf_le_of_le` or
`simp1` together with the assumptions, and use `simp2` with `rfl`s.
Whether to use `simp2` depends on whether the assumptions introduced by
`intro` are used up, since equalities are at the trailing positions.

For example, for the subgoal above, we can do something equivalent to
`refine iInf_le_of_le b' (iInf_le_of_le c' (simp2 (simp2 ?_)))`, where
`iInf_le_of_le` is to choose the `b'` and `c'` in the `⨅ b'_1, ⨅ c'_1, ...`.
Then the subgoal is reduced to
```
(wpgh_2 b' c').get post) ≤
  wp
    (match 9, b'.succ, c'.succ with
    | 2, 3, 4 => mh_1
    | 9, b'.succ, c'.succ => mh_2 b' c'
    | x, x_1, x_2 => mh_3 x x_1 x_2)
    post
```

Finally, we use the simplification equations for the matcher to rewrite
the matcher on the RHS to the corresponding monadic computation, and then
apply the `WPGen.prop` of the corresponding `WPGen` subgoal to close the goal.
This rewriting is necessary since the matcher may not reduce.

For example, `test.match_1.eq_1` is by `rfl`, but `test.match_1.eq_3` has a
non-trivial proof term.

TODO A potential optimization is to use tactic scripts to make the proof
more robust.

-/

/-- Construct a suitable `WPGen` term for a matcher in real time. -/
def constructWPGen (matcherName : Name) : TermElabM (Option MatcherWPGen) := do
  -- NOTE: we rely on `MatcherInfo` here, since we do not want to generate
  -- `WPGen` only for a specific matcher; but this might not work on `casesOn`.
  -- in that case, we might rely on `MatcherApp` instead
  let some matcherInfo ← getMatcherInfo? matcherName | return none
  let constInfo ← getConstInfo matcherName
  -- use level mvars to be more flexible
  let lvlMVars ← mkFreshLevelMVars constInfo.levelParams.length

  -- make up the discriminant(s) and related (type) parameter(s)
  -- NOTE: this will also introduce a fvar for `motive`, but we do not use it normally
  forallBoundedTelescope (constInfo.type.instantiateLevelParams constInfo.levelParams lvlMVars) (.some matcherInfo.getFirstAltPos) fun paramsAndDiscrs partialMatcher => do
  let discrs := paramsAndDiscrs.drop matcherInfo.getFirstDiscrPos |>.take matcherInfo.numDiscrs

  -- make up the implicit arguments of this `WPGen`
  forallTelescope (← ConstantInfo.type <$> getConstInfo ``WPGen.match_template) fun implicitArgs _ => do
  let (mExpr, monadInstExpr, lExpr, omaInstExpr) := (implicitArgs[0]!, implicitArgs[1]!, implicitArgs[2]!, implicitArgs[4]!)

  -- `α`: make up the return type of `m`
  withLocalDecl (← mkFreshUserName `α) BinderInfo.implicit (← Expr.bindingDomain! <$> inferType mExpr) fun αExpr => do
  let mαExpr := mkApp mExpr αExpr

  -- make up the monadic computations in alternatives
  let wpgenTypeBuilder x : MetaM Expr :=
    -- for convenience, here leave some arguments to be resolved by typeclass resolution
    mkAppOptM ``WPGen #[.some mExpr, .some monadInstExpr, .some αExpr, .some lExpr, .none, .some omaInstExpr, .some x]
  let branchConds ← do
    pure <| Array.map (fun x => (x.1, x.2.1)) <| List.toArray <| getForallPremises partialMatcher
  let subMonadArgsWithInfo ← branchConds.mapM fun (nm, br) => do
    -- special check: if the first argument of `br` does not appear in its body,
    -- then remove it
    -- NOTE: this is mainly for the case of `br : Unit → ...`; would it break anything?
    -- NOTE: we only change the `body` to `mαExpr`
    forallTelescope br fun xs body => do
      if xs.isEmpty then
        return ((0, MatcherArgCase.normal), (nm, mαExpr))
      let (case, xs') :=
        if xs[0]!.occurs body
        then (MatcherArgCase.normal, xs)
        else (MatcherArgCase.dropFirst, xs.drop 1)
      pure ((xs'.size, case), (nm, ← mkForallFVars xs' mαExpr))
  let (subMonadArgsInfo, subMonadArgs) := subMonadArgsWithInfo.unzip
  trace[Loom.debug] "subMonadArgs: {subMonadArgs.map Prod.snd}"
  withLocalDecls (← subMonadArgs.mapM fun (nm, t) => do
      let nm' ← mkFreshUserName nm
      pure (nm', BinderInfo.implicit, fun _ => pure t)) fun subMonadArgsFVars => do

  -- make up the sub `WPGen` goals
  -- considering the potential recursive call, need to record some equalities
  let subWPGenArgs ← subMonadArgs.mapIdxM fun i (nm, t) => do
    let nm' := nm.appendBefore "wpg"
    let ty ← forallTelescope t fun xs _ => do
      let tmp ← wpgenTypeBuilder <| mkAppN subMonadArgsFVars[i]! xs
      let motiveBody ← Expr.getForallBody <$> instantiateForall branchConds[i]!.2 xs
      let withEqs ← motiveBody.withApp fun _ args => do
        -- TODO this should have an optimization; some equalities might be redundant
        let eqs ← discrs.mapIdxM fun i lhs => mkEq lhs args[i]!
        mkArrowN eqs tmp
      -- NOTE: here `mkForallFVars (discrs ++ xs) withEqs` is too general;
      -- should stick to `discrs` (i.e., not including them into arguments)
      mkForallFVars xs withEqs
    pure (nm', ty)
  trace[Loom.debug] "subWPGenArgs: {subWPGenArgs}"
  withLocalDeclsDND (← subWPGenArgs.mapM fun (nm, t) => do
      pure (← mkFreshUserName nm, t)) fun subWPGenArgsFVars => do

  -- make up the type of the target `WPGen`
  let targetMatcher ← do
    let motivefv := paramsAndDiscrs[matcherInfo.getMotivePos]!
    let ty ← inferType motivefv
    let motiveArg ← forallTelescope ty fun xs _ =>
      mkLambdaFVars xs <| mkApp mExpr αExpr
    -- accounting for the cases
    let subMonadArgsForMatcher ← subMonadArgsInfo.mapIdxM fun i (_, case) => do
      match case with
      | .dropFirst => mkFunUnit subMonadArgsFVars[i]!
      | .normal => pure subMonadArgsFVars[i]!
    pure <| mkAppN
      (Lean.mkConst matcherName lvlMVars)
      ((paramsAndDiscrs.set! matcherInfo.getMotivePos motiveArg) ++ subMonadArgsForMatcher)
  let targetWPGenTy ← wpgenTypeBuilder targetMatcher
  trace[Loom.debug] "targetWPGenTy: {targetWPGenTy}"

  -- prepare the splitter
  let (matchEqnNames, splitter, splitterType) ← do
    let matchEqns ← Match.getEquationsFor matcherName
    -- note the difference on instantiating level params
    let splitter ← mkConstWithFreshMVarLevels matchEqns.splitterName
    let splitterType ← whnfForall (← inferType <| Lean.mkConst matchEqns.splitterName lvlMVars)
    pure (matchEqns.eqnNames, splitter, splitterType)
  trace[Loom.debug] "splitter type: {splitterType}"

  -- make up the `post`
  withLocalDeclD (← mkFreshUserName `post) (← mkArrow αExpr lExpr) fun postExpr => do

  -- make up the `WPGen.get`
  let (wpgenGet, backup) ← do
    let partialSplitterType ← instantiateForall splitterType paramsAndDiscrs
    let branchConds ← do
      pure <| List.map (fun x => x.2.1) <| getForallPremises partialSplitterType
    let wpgenGetBranches ← branchConds.mapIdxM fun i br => do
      let subWPGen := subWPGenArgsFVars[i]!
      let br' ← forallTelescope br fun xs motiveBody => do
        let newBody ← do
          let tmp ← motiveBody.withApp fun _ args => do
            -- TODO this should have an optimization; some equalities might be redundant
            let eqs ← discrs.mapIdxM fun i lhs => mkEq lhs args[i]!
            mkArrowN eqs (mkConst ``True)  -- `True` is dummy
          forallTelescope tmp fun ys _ => do
            -- NOTE: this is based on the invariant that the non-equality arguments of a sub `WPGen`
            -- are the ones of the corresponding sub monadic computation
            let numArgsRequired := subMonadArgsInfo[i]!.1
            let subWPGenGet ← mkAppM ``WPGen.get #[mkAppN subWPGen (xs.take numArgsRequired ++ ys), postExpr]
            mkForallFVars ys subWPGenGet
        mkForallFVars xs newBody
      trace[Loom.debug] "branch {i} after adding equalities: {br} ==> {br'}"
      -- `dependencies` will be used in the proof below
      let (dependencies, res) ← forallTelescope br' fun xs motiveBody' => do
        xs.foldrM (init := ([], motiveBody')) fun x (dependencies, e) => do
          let xty ← inferType x
          -- checking by dependency might be more accurate here, because
          -- even when `xty` is a `Prop`, it can be depended on
          if x.occurs e then
            let tmp ← mkLambdaFVars #[x] e
            let tmp ← mkAppOptM ``iInf #[.some lExpr, .some xty, .none, .some tmp]
            pure (true :: dependencies, tmp)
          else
            let injectedProp ← mkAppOptM ``LE.pure #[.some lExpr, .none, .none, .none, .some xty]
            let tmp ← mkAppOptM ``himp #[.some lExpr, .none, .some injectedProp, .some e]
            pure (false :: dependencies, tmp)
      trace[Loom.debug] "branch {i} after transformation: {br'} ==> {res}"
      -- `dependencies.size` should be equal to the number of arguments of
      -- `br` plus the number of equalities added
      pure (res, dependencies)
    let (wpgenGetBranchesAfter, backup) := wpgenGetBranches.unzip
    -- combine the branches together; `⊓` is left-associative
    -- NOTE: this might also be changed into another encoding, e.g., `⨅ i ∈ (Fin ..), ...`
    let topAsInit ← mkAppOptM ``Top.top #[.some lExpr, .none]
    let bundled ← List.foldldM (g := pure) (init := topAsInit) (l := wpgenGetBranchesAfter) fun infs e =>
      mkAppOptM ``Min.min #[.some lExpr, .none, .some infs, .some e]
    let res ← mkLambdaFVars #[postExpr] bundled
    pure (res, backup.toArray)
  trace[Loom.debug] "wpgenGet: {wpgenGet}"

  -- make up the proof for `WPGen.post`
  let wpgenPost ← do
    let motive ← do
      -- make another copy of `discrs`
      let (_, discrsBuilder) ← discrs.foldlM (init := (#[], #[])) fun (xspre, res) x => do
        let nm ← mkFreshUserName (← x.fvarId!.getUserName)
        let xty ← inferType x
        let ty xspre' := pure <| xty.replaceFVars xspre xspre'
        pure (xspre.push x, res.push (nm, ty))
      -- use that copy in the matcher on the RHS of `≤`
      let lhs ← instantiateLambda wpgenGet #[postExpr]
      let rhs ← mkAppOptM ``wp
        #[.some mExpr, .some monadInstExpr, .some αExpr, .some lExpr, .none,
          .some omaInstExpr, .some targetMatcher, .some postExpr]
      withLocalDeclsD discrsBuilder fun discrs' => do
        let rhs' := rhs.replaceFVars discrs discrs'
        let eqs ← discrs'.mapIdxM fun i lhs => mkEq discrs[i]! lhs
        let le ← mkAppM ``LE.le #[lhs, rhs']
        let tmp ← mkArrowN eqs le
        mkLambdaFVars discrs' tmp
    trace[Loom.debug] "motive for the splitter in proof: {motive}"
    let paramsAndDiscrs' := paramsAndDiscrs.set! matcherInfo.getMotivePos motive
    let partialSplitter := mkAppN splitter paramsAndDiscrs'
    let partialSplitterType ← inferType partialSplitter
    let numBranches := matcherInfo.numAlts    -- should be the same as `branchConds.length`
    let branchConds ← do
      pure <| List.map (fun x => x.2.1) <| List.take numBranches <| getForallPremises partialSplitterType
    let wpgenPostSubProofs ← branchConds.toArray.mapIdxM fun i br => do
      trace[Loom.debug] "subgoal {i}: {br}"
      -- `intro`
      let res ← forallTelescope br fun xs body => do
        -- instantiate the sub `WPGen` to use
        -- let subWPGen := subWPGenArgsFVars[i]!
        -- let numArgsRequired := subMonadArgsInfo[i]!.1
        -- let xsprefix := xs.take numArgsRequired
        -- let rfls ← xsprefix.mapM (mkEqRefl ·)
        -- let subWPGenProp ← mkAppM ``WPGen.prop #[mkAppN subWPGen (xsprefix ++ rfls), postExpr]
        -- trace[Loom.debug] "subWPGenProp: {subWPGenProp}"

        -- using `forallTelescope` here to avoid prematurely unfolding `body`,
        -- since `body` would be `(fun (eqs) => ...) ...`
        -- unfold it now!
        let body ← whnf body
        forallTelescope body fun eqs body => do

        -- build the proof by looking at the corresponding branch of `wpgenGet`
        let goal ← mkFreshExprMVar body
        let goals ← goal.mvarId!.casesRec fun localDecl => do
          return eqs.contains <| Expr.fvar localDecl.fvarId
        let goal := .mvar goals[0]!

        let goal_ ← withinBranch i numBranches lExpr goal
        -- do the prefix part
        let dependencies := backup[i]!.toArray
        let goal' ← xs.zip dependencies |>.foldlM (init := goal_) fun mainGoal (x, dep) => do
          let xty ← inferType x
          if !dep then
            let tmp ← mkAppOptM ``Loom.Matcher.simp1 #[.some lExpr, .none, .some xty, .some x]
            let goals ← mainGoal.mvarId!.apply tmp
            pure <| .mvar goals[0]!
          else
            let f ← mkFreshExprMVar (← mkArrow xty lExpr)
            let a ← mkFreshExprMVar lExpr
            let tmp ← mkAppOptM ``iInf_le_of_le #[.some lExpr, .some xty, .none,
              .some f /- hard to inference, so provided explicitly -/ ,
              .some a, .some x]
            let goals ← mainGoal.mvarId!.apply tmp
            pure <| .mvar goals[0]!
        -- try `rfl` in the trailing part
        -- TODO code repetition
        let goal'' ← (dependencies.size - xs.size) |>.foldM (init := goal') fun _ _ mainGoal => do
          -- let goals ← mainGoal.mvarId!.applyConst ``Loom.Matcher.simp2
          let aa ← mkFreshExprMVar none
          let eq ← mkEq aa aa
          let rfl ← mkEqRefl aa
          let f ← mkFreshExprMVar (← mkArrow eq lExpr)
          let a ← mkFreshExprMVar lExpr
          let tmp ← mkAppOptM ``iInf_le_of_le #[.some lExpr, .some eq, .none,
            .some f /- hard to inference, so provided explicitly -/ ,
            .some a, .some rfl]
          let goals ← mainGoal.mvarId!.apply tmp
          pure <| .mvar goals[0]!
        -- might need to use the matcher eqn
        let goal''' ←
          try
            let r ← goal''.mvarId!.rewrite (← goal''.mvarId!.getType) (← mkConstWithFreshMVarLevels matchEqnNames[i]!)
            let goal''' ← Expr.mvar <$> goal''.mvarId!.replaceTargetEq r.eNew r.eqProof
            for g in r.mvarIds do
              g.assumption
            pure goal'''
          catch _ => pure goal''
        -- let _ ← goal'''.mvarId!.apply subWPGenProp
        let _ ← goal'''.mvarId!.applyConst ``WPGen.prop
        let res ← instantiateMVars goal
        mkLambdaFVars (xs ++ eqs) res
      trace[Loom.debug] "sub-proof for branch {i}: {br} ==> {res}"
      pure res
    let discrsRfls ← discrs.mapM (mkEqRefl ·)
    mkLambdaFVars #[postExpr] <| mkAppN partialSplitter (wpgenPostSubProofs ++ discrsRfls)

  -- put together
  let wpgen ← mkAppM ``WPGen.mk #[wpgenGet, wpgenPost]
  check wpgen
  let wpgen ← instantiateMVars wpgen
  let arguments :=
    #[αExpr] ++
    (paramsAndDiscrs.take matcherInfo.numParams) ++
    implicitArgs ++
    subMonadArgsFVars ++
    (paramsAndDiscrs.drop matcherInfo.getFirstDiscrPos) ++
    subWPGenArgsFVars
  let wpgen ← mkLambdaFVars arguments wpgen
  trace[Loom.debug] "generated WPGen: {wpgen}"
  trace[Loom.debug] "has mvar? {wpgen.hasMVar}"

  -- NOTE: it seems that only this requires `TermElabM`; the rest can be done in `MetaM`
  let wpgen ← levelMVarToParam wpgen
  trace[Loom.debug] "has mvar? {wpgen.hasMVar}"
  let newLvls := collectLevelParams {} wpgen |>.params

  let firstMonadArgPos := 1 + matcherInfo.numParams + implicitArgs.size
  pure <| .some {
    lvls := newLvls,
    wpgenExpr := wpgen,
    matcherInfo := matcherInfo,
    monadRetTypePos := 0,
    monadArgPos := 1 + matcherInfo.numParams,
    monadInstPos := 1 + matcherInfo.numParams + 1,
    omaTypePos := 1 + matcherInfo.numParams + 2,
    firstMonadArgPos := firstMonadArgPos,
    -- firstWPGenArgPos := firstMonadArgPos + matcherInfo.numAlts,
    -- firstDiscrPos := firstMonadArgPos + 2 * matcherInfo.numAlts,
  }

def partiallyInstantiateWPGen (outerArgs : Array Expr) (a : MatcherWPGen) (b : MatcherApp) : MetaM Expr := do
  let wpgen := a.wpgenExpr.instantiateLevelParams a.lvls.toList (← mkFreshLevelMVars a.lvls.size)
  try
    -- usually providing `alts` is enough, but sometimes we need to instantiate the `Unit` argument
    let fma := a.firstMonadArgPos
    let alts' ← do
      lambdaBoundedTelescope wpgen (fma + a.matcherInfo.numAlts) fun xs _ => do
      b.alts.mapIdxM fun i alt => do
        let numArgRequired ← Expr.getNumHeadForalls <$> inferType xs[fma + i]!
        let numArgs := alt.getNumHeadLambdas
        -- only check one case
        if numArgRequired + 1 == numArgs then
          return mkApp alt (mkConst ``Unit.unit)
        pure alt
    let args : Array (Option Expr) := Array.replicate fma none
    /-
    -- also works, but providing more arguments might be better ...?
    let (α, m) ← lambdaTelescope b.motive fun _ body => do
      let .app m α := body | throwError s!"motive is not of the form `fun .. => m α`"
      pure (α, m)
    let args := args.set! a.monadRetTypePos (some α)
    let args := args.set! a.monadArgPos (some m)
    -/
    -- the position setting becomes highly bespoke
    let args := args.set! a.monadRetTypePos (some outerArgs[0]!)
    let args := args.set! a.monadArgPos (some outerArgs[1]!)
    let args := args.set! a.monadInstPos (some outerArgs[2]!)
    let args := args.set! a.omaTypePos (some outerArgs[3]!)
    -- NOTE: due to mvar depth increase and the level mvars generated above,
    -- using `mkAppOptM'` might fail, so we simulate it here
    /- mkAppOptM' wpgen (args ++ alts'.map Option.some) -/
    let partialwpgen ← args.foldlM (init := wpgen) fun e arg => do
      match arg with
      | .some v => pure <| mkApp e v
      | .none => pure <| mkApp e (← mkFreshExprMVar none)
    let res := mkAppN partialwpgen alts'
    check res   -- instantiate some mvars
    pure res
  catch ex =>
    trace[Loom.debug] m!"Error in [{decl_name%}]: {ex.toMessageData}"
    return wpgen

def defineWPGen (name : Name) : TermElabM Unit := do
  unless ← isMatcher name do
    throwError s!"{name} is not a matcher"
  let targetName := name ++ `WPGen
  if (← getEnv).find? targetName matches none then
    let some res ← constructWPGen name
      | throwError s!"cannot generate WPGen for matcher {name} due to error"
    addDecl <|
      Declaration.defnDecl <|
        mkDefinitionValEx targetName res.lvls.toList (← inferType res.wpgenExpr) res.wpgenExpr
        (Lean.ReducibilityHints.regular 0)
        (DefinitionSafety.safe) []
    enableRealizationsForConst targetName
    applyAttributes targetName (← do
      let attr1 ← `(Parser.Term.attrInstance| spec )
      let attr2 ← `(Parser.Term.attrInstance| loomWpSimp)
      elabAttrs #[attr1, attr2])

-- inspired by how `.fun_cases` works
def isMatcherWPGen (env : Environment) (name : Name) : Bool := Id.run do
  let .str p s := name | return false
  unless isMatcherCore env p do return false
  match s with
  | "WPGen" =>
    unless env.isSafeDefinition p do return false
    return true
  | _ => return false

end Loom.Matcher

-- FIXME: does not seem to actually work. why?
-- initialize
--   registerReservedNamePredicate Loom.Matcher.isMatcherWPGen

--   registerReservedNameAction fun name => do
--     if Loom.Matcher.isMatcherWPGen (← getEnv) name then
--       let .str p _ := name | return false
--       unless (← getEnv).isSafeDefinition p do return false
--       MetaM.run' <| realizeConst p name (Loom.Matcher.defineWPGen p |>.run')
--       return true
--     return false
