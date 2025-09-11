import Lean

/- import Mathlib.Algebra.BigOperators.Intervals -/
/- import Mathlib.Algebra.Ring.Int.Defs -/
/- import Mathlib.Data.Int.Bitwise -/
/- import Mathlib.Init -/
/- import Mathlib.Data.Nat.Basic -/

/- import Loom.MonadAlgebras.NonDetT.Extract -/

import Loom.MonadAlgebras.WP.Tactic
import Loom.MonadAlgebras.WP.DoNames'

import CaseStudies.Velvet.Std

open TotalCorrectness DemonicChoice Lean.Elab.Term.DoNames

set_option auto.smt.trust true
set_option auto.smt true
set_option auto.smt.timeout 4
set_option auto.smt.solver.name "cvc5"


section Match

-- def mtch (x: Option String) : VelvetM Nat := do
--   match x with
--   | none => pure 1
--   | some x => pure (x.length + 1)

-- /- set_option pp.all true -/

-- lemma match_correct : forall (x: Option String), triple True (mtch x) (fun y => y > 0) := by
--   unfold mtch

--   loom_intro
--   wpgen_intro
--   conv => {
--     congr
--     reduce
--   }
--   refine WPGen.match (m:=VelvetM) (y:=(pure 1)) (z:=(fun x => pure (x.length + 1))) x ?_ ?_
  /- /- loom_goals_intro -/ -/
  /- assumption -/



method str_id (s: String) return (ss: String)
ensures (s = ss)
do
  return s

method opt_strlen (o: Option String) return (n: Nat)
  ensures n >= 1
  do
    let res' := (match o with
    | none => 1
    | some x => (x.length  + 1))
    return res'


    /- let s <- (match o with -/
    /-   | none => pure "" -/
    /-   | some x => pure x) -/
    /- return s.1.length + 1 -/


prove_correct str_id by
    dsimp [str_id]
    loom_goals_intro
    loom_unfold
    trivial



#check (str_id_correct "")

-- set_option diagnostics true


prove_correct opt_strlen by
  unfold opt_strlen
  repeat' loom_intro
  wpgen
  -- loom_solve
  /- · simp -/
  -- · refine WPGen.match (m:=VelvetM) (y:=(pure "" )) (z:=pure) o ?_ ?_

  · sorry

set_option trace.Loom.debug true in
method cube (n : Nat) return (res : Nat)
  ensures n = res
  do
    let a (o : Option Nat) := match o with
      | none => 0
      | some x => x
    match n with
    | .zero => pure 0
    | .succ k =>
      let b ← cube k
      pure (Nat.succ b)

-- TODO when `n : β`, `β : Sort u`?

set_option trace.Loom.debug true in
method cube2 (n : α) (l : List α) return (res : Nat)
  ensures res = l.length
  do
    match l, n with
    | [], _ => pure 1
    | _ :: k, _ =>
      let b ← cube2 n k
      pure b
    -- FIXME: cannot be written like this, due to some doitem expand
    -- let aa ← match n with
    --   | .zero => pure 0
    --   | .succ k =>
    --     let a ← cube k    -- !!!
    --     pure (Nat.succ a)
    -- return aa
#print cube2.match_1
#print cube2.match_1.splitter
-- #print cube

-- def cubeId (n : Nat) : Id Nat := do
--   let a ← match n with
--     | .zero => pure 0
--     | .succ k =>
--       let b ← cubeId k
--       pure <| Nat.succ b
--   return 100

-- def kk (a : Nat) (b : Nat) (c : Option Nat) : Id Nat := match a, b, c with
--     | .zero, .zero, .some (.succ .zero) => pure (100 : Nat)
--     | _, _, _ => pure 200
-- #print kk

set_option trace.Loom.debug true in
method cube3 (a : Nat) (b : Nat) (c : Nat) return (res : Nat)
  ensures True
  do
    -- match a, b, c with
    -- | .zero, .zero, .some (.succ .zero) => pure (100 : Nat)
    -- | .zero, .zero, .none => pure (100 : Nat)
    -- | _, _, _ => pure 200
    match a, b, c with
    | 2, 3, 4 => pure (100 : Nat)
    | _, _, _ => pure 200

#check cube3.match_1
#check cube3.match_1.splitter

#check cube2.match_1.WPGen

run_meta do
  Lean.Meta.realizeConst ``cube2.match_1 `cube2.match_1.WPGen
    <| (Loom.Matcher.defineWPGen ``cube2.match_1 |>.run')

#print cube2.match_1.WPGen

set_option trace.Loom.debug true in
prove_correct cube2 by
  unfold cube2
  repeat' loom_intro
  simp
  wpgen
  all_goals try simp only [loomWpSimp]
  -- apply WPGen.pure
  -- apply WPGen.bind
  -- wpgen_step
  -- apply cube2.match_1.WPGen
  -- -- repeat' loom_intro
  -- -- wpgen_intro
  -- -- wpgen_step
  -- all_goals sorry


#print cube.match_3
#print cube.match_5
#check cube.match_3.splitter
def aa := 1

-- #check aa.fun_cases
-- set_option trace.Loom.debug true in
open Lean in
run_meta do
  let res := (← getEnv).find? <| ``aa ++ `fun_cases
  logInfo m!"res: {res.isNone}"
  pure ()
#check aa.fun_cases
open Lean in
run_meta do
  let res := (← getEnv).contains <| ``aa ++ `fun_cases
  logInfo m!"res: {res}"
  let res ← resolveGlobalConstNoOverloadCore <| ``aa ++ `fun_cases
  logInfo m!"res: {res}"
  pure ()
#check Lean.ReservedNameAction
#check Lean.registerReservedNamePredicate
set_option trace.Loom.debug true in
prove_correct cube by
  unfold cube
  repeat' loom_intro
  wpgen


set_option trace.Loom.debug true in
method cube4 (a : Nat ⊕ Bool) return (res : Nat)
  ensures True
  do
    -- match a, b, c with
    -- | .zero, .zero, .some (.succ .zero) => pure (100 : Nat)
    -- | .zero, .zero, .none => pure (100 : Nat)
    -- | _, _, _ => pure 200
    match a with
    -- | .inl 2 => pure (100 : Nat)
    | .inl xxx => pure 200
    | .inr yyy => pure 300
set_option trace.Loom.debug true in
run_meta do
  let res ← generateWPForMatcher ``cube4.match_1
  pure ()

-- #print cube

-- method add1 (mut n: Nat) return (res : Nat)
--   ensures True
--   do
--     return 100

-- method abcbbdas (mut o: Nat) return (res: Option Nat)
--   ensures (res = default ∧ o.isNone)
--   do
--     o := 100
--     -- let res <- add1 o
--     let res ← add1 o
--     return .some 100
-- #print abcbbdas

-- method abcbbdass (f : Nat → VelvetM Nat) return (res: Option Nat)
--   ensures (res = default ∧ o.isNone)
--   do
--     let res ← f 1
--     let res <- f 1
--     return res
-- #print abcbbdass

def testmatch (a b c: Nat) (xx yy : α) :=
  match a, b, c with
  | 2, 3, 4 => xx
  | _, _, _ => yy
#print testmatch.match_1

noncomputable
def WPGen.match2
  {l : Type u} {m : Type u -> Type v} [Monad m] [LawfulMonad m] [CompleteBooleanAlgebra l] [MAlgOrdered m l]
  -- The program to run if the option is 'none'
  {xx yy : m β} (a b c : Nat) (wpgxx : WPGen xx) (wpgyy : WPGen yy)
  -- {y : m β} {z : γ  → m β} (opt : Option γ ) (wpgy : WPGen y)
  -- A function that gives a program to run if the option is 'some a'
  -- (wpgz : ∀ a, WPGen (z a))
  -- The return type is parameterized by the whole match expression
  : WPGen (match a, b, c with | 2, 3, 4 => xx | _, _, _ => yy)
where
  get := fun post =>
    -- Branch 1: The 'none' case
    (⌜a = 2⌝ ⇨ ⌜b = 3⌝ ⇨ ⌜c = 4⌝ ⇨ wpgxx.get post) ⊓
    (⌜a = 2⌝ ⇨ ⌜b = 3⌝ ⇨ ⌜c = 4⌝ ⇨ wpgxx.get post) ⊓ (⊤ ⊓ ⊤ ⊓ ⊤) ⊓
    -- Branch 2: The 'some' case
    (⨅ a, ⨅ b, ⨅ c, ⌜a = 2⌝ ⇨ ⌜b = 3⌝ ⇨ ⌜c = 4⌝ ⇨ wpgyy.get post)

  prop := by
    sorry

method unwrap_nat_and_double (o: Option Nat) return (res: Option Nat)
  ensures (res = default ∧ o.isNone)
  do
    let res <- do (match o with
      | none => pure default
      | some x => pure x)
    return res
set_option trace.Loom.debug true in
prove_correct unwrap_nat_and_double by
  unfold unwrap_nat_and_double
  repeat' loom_intro
  wpgen

/- method fib (n: Nat) return (res: Nat) -/
/-   do -/
/-     let res1 <- fib (n - 1) -/
/-     let res2 <- fib (n - 2) -/
/-     return res1 + res2 -/

end Match


section Lc

-- #include <algorithm>
--
-- class Solution {
-- public:
--     vector<string> divideString(string s, int k, char fill) {
--         string_view sv{s};
--         vector<string> result{};
--         while (!sv.empty()) {
--             string res(sv.substr(0, min((size_t)k,sv.size())));
--             if (res.size() != k) {
--                 res = res + string(k - res.size(), fill);
--             }
--             result.push_back(res);
--             sv = sv.substr(min((size_t)k, sv.size()), sv.size());
--         }
--         return result;
--     }
-- };

variable {arrStr} [arr_inst_str: TArray String arrStr]

axiom take_gives_max_k_len_string :
      forall (s: Substring) (k:Nat), ( s.take k ).bsize <= k

axiom drop_drops_some_chars
:
      forall (s: Substring) (k: PNat) (h: s.bsize > 0), ( s.drop k ).bsize < s.bsize


def div_ceil a b :=
    if a % b = 0 then a / b
    else ( a / b ) + 1

-- set_option diagnostics true
method divide_string (mut s: Substring) (k: PNat) (fill: Char)
       return (res: arrStr)
       ensures arr_inst_str.size res = div_ceil s.bsize k
       ensures forall i, i < arr_inst_str.size res → (res[i].length = k)
       do
       let sz := div_ceil s.bsize k
       let mut res := TArray.replicate sz ""
       assert s.bsize > 0 -> sz >= 1
       let mut start := 0
       let mut j := 0
       while !s.isEmpty && j < size res
       invariant forall i, i < j → ((res[i]).length = k.val)
       invariant size res = sz
       invariant j <= size res
       decreasing s.bsize
       do
             let mut res' :=  (s.take k).toString
             s := s.drop k
             if res'.length != k then
                res' := res' ++ (String.replicate (k - res'.length) fill)
             res[j] := res'
             j := j + 1
       return res

/-
 -prove_correct divide_string by
 -  dsimp [divide_string]
 -  loom_goals_intro
 -  loom_unfold
 -  · case a.isTrue.left h'' =>
 -    simp[*]
 -    rw [<-Nat.dvd_iff_mod_eq_zero] at *
 -    cases h''': h''
 -    · case intro w h =>
 -      have lem := Nat.div_eq_iff_eq_mul_right (a:=s.bsize) (b:=k) (c:=w) (k.property) h''
 -      cases w
 -      · grind
 -      · simp [h,TArray.replicate_size]
 -  · simp [*] at *
 -    intro i hij
 -    rw [getElemE] at *
 -    simp [Substring.isEmpty] at if_pos
 -    have s1_size_gt_0 : s_1.bsize > 0 := by grind
 -    cases hij' : decide (i = j)
 -    · rw [TArray.get_set i j _ res (by grind)]
 -      simp at hij'
 -      simp [*]; loom_solver
 -    · simp at hij'
 -      rw [hij'] at *
 -      rw [TArray.get_set j j _ res (by grind)]
 -      simp
 -      sorry
 -  · rw [TArray.size_set]
 -    grind
 -  · rw [TArray.size_set]
 -    grind
 -  · apply drop_drops_some_chars
 -    cases Classical.em (s_1.bsize = 0)
 -    · unfold Substring.isEmpty at if_pos
 -      simp[*] at *
 -    · grind
 -  · cases Classical.em (j < size res)
 -    · intro i hij
 -      rw [getElemE] at *
 -      rw [TArray.get_set i j _ res (by grind)]
 -      by_cases h_eq_ij : i = j
 -      · simp[*]; grind
 -      · simp[*]; apply invariant_1; grind
 -    · grind
 -  · rw [TArray.size_set]
 -    assumption
 -  · rw [TArray.size_set]
 -    grind
 -  · apply drop_drops_some_chars
 -    unfold Substring.isEmpty at if_pos
 -    grind
 -  · loom_solver
 -  · loom_solver
 -  · loom_solver
 -  · loom_solver
 -  · grind
 -  · rw [TArray.replicate_size]
 -  · grind
 -  · intro i hi
 -    simp at a_1
 -    by_cases h_s_1_empty : s_1.isEmpty = true
 -    · simp[*] at * ; sorry
 -    · simp[*] at * ; grind
 -  · grind
 -  · sorry
 -
 -/
end Lc


open Lean Meta Elab Command Term

def foo ( x:α  ) := x

simproc reduceFoo (foo _) :=
  fun e => do
    let args := e.getAppArgs
    if h: args.size = 0 then return .done {expr:= e}
    else
      let match_exp := args[args.size - 1 ]!
      let univ_levels :=  e.getAppFn.constLevels!

      dbg_trace "Match Expression: {match_exp}"
      if let some e' := (← Lean.Meta.matchMatcherApp? match_exp) then
        let res <- Lean.Meta.MatcherApp.transform (onAlt := (fun a b e => do
          -- all args but last one replaced
          let args' := args.set (args.size - 1) e (by
            grind
          )
          --let args' := #[e]
          let newExpr := (mkAppN (Lean.Expr.const ``foo univ_levels)  args' )
          dbg_trace "e1: {b}, e2: {e}"
          dbg_trace "Transformed from {e} -> {newExpr}"
          pure newExpr
        )) (onMotive:= (fun _ e => do
          dbg_trace "Motive: {e}"
          pure e
        )) e'
        dbg_trace "{res.toExpr}"
        return .done { expr := res.toExpr }
      else
        return .done { expr := e }


set_option diagnostics true
