import Lean
import Lean.Parser

import Aesop

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Ring.Int.Defs

import Loom.MonadAlgebras.NonDetT.Extract
import Loom.MonadAlgebras.WP.Tactic

import CaseStudies.Theory
import CaseStudies.Tactic
import Loom.MonadAlgebras.WP.DoNames'

abbrev Balance := Int
abbrev CashmereM := NonDetT (ExceptT String (StateT Balance DivM))

open Lean Elab Command Term Meta Lean.Parser

private def _root_.Lean.EnvExtension.set (ext : EnvExtension σ) (s : σ)
  [Monad m] [MonadEnv m] : m Unit := do
  Lean.setEnv $ ext.setState (<- getEnv) s

private def _root_.Lean.EnvExtension.modify (ext : EnvExtension σ) (s : σ -> σ)
  [Monad m] [MonadEnv m] : m Unit := do
  Lean.modifyEnv (ext.modifyState · s)

private def _root_.Lean.EnvExtension.get [Inhabited σ] (ext : EnvExtension σ)
  [Monad m] [MonadEnv m] : m σ := do
  return ext.getState (<- getEnv)

private def _root_.Lean.SimpleScopedEnvExtension.get [Inhabited σ] (ext : SimpleScopedEnvExtension α σ)
  [Monad m] [MonadEnv m] : m σ := do
  return ext.getState (<- getEnv)

private def _root_.Lean.SimpleScopedEnvExtension.modify
  (ext : SimpleScopedEnvExtension α σ) (s : σ -> σ)
  [Monad m] [MonadEnv m] : m Unit := do
  Lean.modifyEnv (ext.modifyState · s)

private def _root_.Lean.SimplePersistentEnvExtension.get [Inhabited σ] (ext : SimplePersistentEnvExtension α σ)
  [Monad m] [MonadEnv m] : m σ := do
  return ext.getState (<- getEnv)

private def _root_.Lean.SimplePersistentEnvExtension.modify
  (ext : SimplePersistentEnvExtension α σ) (s : σ -> σ)
  [Monad m] [MonadEnv m] : m Unit := do
  Lean.modifyEnv (ext.modifyState · s)


abbrev doSeq := TSyntax ``Term.doSeq
abbrev doSeqItem := TSyntax ``Term.doSeqItem

declare_syntax_cat require_caluse
declare_syntax_cat ensures_caluse
declare_syntax_cat leafny_binder

def termBeforeReqEnsDo := withForbidden "require" (withForbidden "ensures" Term.termBeforeDo)

attribute [run_builtin_parser_attribute_hooks] termBeforeReqEnsDo

builtin_initialize
  register_parser_alias termBeforeReqEnsDo


syntax "(" ident ":" term ")" : leafny_binder
syntax "(mut" ident ":" term ")" : leafny_binder
syntax "require" termBeforeReqEnsDo : require_caluse
syntax "ensures" termBeforeReqEnsDo : ensures_caluse
--this can be used in more complex cases for set/get
syntax "balance_set" term : doElem

syntax "bdef" ident leafny_binder* "returns" "(" ident ":" term ")"
  (require_caluse )*
  (ensures_caluse)* "do" doSeq : command

syntax "prove_correct" ident "by" tacticSeq : command

private def toBracketedBinderArrayLeafny (stx : Array (TSyntax `leafny_binder)) : MetaM (TSyntaxArray `Lean.Parser.Term.bracketedBinder) := do
  let mut binders := #[]
  for b in stx do
    match b with
    | `(leafny_binder| ($id:ident : $tp:term)) => do
      let fb ← `(bracketedBinder| ($id : $tp:term))
      binders := binders.push fb
    | `(leafny_binder| (mut $id:ident : $tp:term)) => do
      let fb ← `(bracketedBinder| ($id : $tp:term))
      binders := binders.push fb
    | _ => throwError "unexpected syntax in leafny binder: {b}"
  return binders

def getMutTypes (stx : Array (TSyntax `leafny_binder)) : MetaM (Array (TSyntax `term)) := do
  let mut types := #[]
  for b in stx do
    match b with
    | `(leafny_binder| (mut $_:ident : $tp:term)) => do
      types := types.push tp
    | _ => pure ()
  return types

def getModIds (stx : Array (TSyntax `leafny_binder)) : MetaM (Array (Nat × Ident)) := do
  let mut ids := #[]
  let mut pos := 0
  for b in stx do
    match b with
    | `(leafny_binder| (mut $id:ident : $_:term)) => do
      ids := ids.push (pos, id)
      pos := pos + 1
    | _ => pos := pos + 1
  return ids

def getIds (stx : Array (TSyntax `leafny_binder)) : MetaM (Array Ident) := do
  let mut ids := #[]
  for b in stx do
    match b with
    | `(leafny_binder| (mut $id:ident : $_:term)) => do
      ids := ids.push id
    | `(leafny_binder| ($id:ident : $_:term)) => do
      ids := ids.push id
    | _ => throwError "unexpected syntax in leafny binder: {b}"
  return ids

mutual
partial def expandLeafnyDoSeq (modIds : Array Ident) (stx : doSeq) : TermElabM (Array doSeqItem) :=
  match stx with
  | `(doSeq| $doS:doSeqItem*) => return Array.flatten $ ← doS.mapM (expandLeafnyDoSeqItem modIds)
  | _ => throwErrorAt stx s!"unexpected syntax of Velvet `do`-notation sequence {stx}"


partial def expandLeafnyDoSeqItem (modIds : Array Ident) (stx : doSeqItem) : TermElabM (Array doSeqItem) := do
  match stx with
  -- Ignore semicolons
  | `(Term.doSeqItem| $stx ;) => expandLeafnyDoSeqItem modIds $ <- `(Term.doSeqItem| $stx:doElem)
  | `(Term.doSeqItem| return) =>
    let mut ret <- `(term| $(modIds[0]!))
    return #[<-`(Term.doSeqItem| set ($ret)), <-`(Term.doSeqItem| return ())]
  | `(Term.doSeqItem| return $t) =>
    let mut ret <- `(term| $(modIds[0]!))
    return #[<-`(Term.doSeqItem| set ($ret)), <-`(Term.doSeqItem| return $t)]
  | `(Term.doSeqItem| pure $t) =>
    let mut ret <- `(term| ())
    for modId in modIds do
      ret <- `(term| ⟨$modId, $ret⟩)
    return #[<-`(Term.doSeqItem| pure ⟨$t, $ret⟩)]
  | `(Term.doSeqItem| if $h:ident : $t:term then $thn:doSeq else $els:doSeq) =>
    let thn <- expandLeafnyDoSeq modIds thn
    let els <- expandLeafnyDoSeq modIds els
    let ret ← `(Term.doSeqItem| if $h:ident : $t then $thn* else $els*)
    return #[ret]
  | `(Term.doSeqItem| if $h:ident : $t:term then $thn) =>
    expandLeafnyDoSeqItem modIds $ <- `(Term.doSeqItem| if $h:ident : $t:term then $thn else pure ())
  | `(Term.doSeqItem| if $t:term then $thn:doSeq) =>
    expandLeafnyDoSeqItem modIds $ <- `(Term.doSeqItem| if $t then $thn:doSeq else pure ())
  | `(Term.doSeqItem| if $t:term then $thn:doSeq else $els:doSeq) =>
    let thn <- expandLeafnyDoSeq modIds thn
    let els <- expandLeafnyDoSeq modIds els
    let ret ← `(Term.doSeqItem| if $t then $thn* else $els*)
    return #[ret]
  | `(Term.doSeqItem| let $id <- $trm:term) | `(Term.doSeqItem| let $id : $_ <- $trm:term) =>
    let `($t:ident $args:term*) := trm | pure #[stx]
    -- dbg_trace s!"{t} {args}"
    let ctx <- globalMutVarsCtx.get
    let .some ids := ctx[t.getId]? | pure #[stx]
    let mut mods := #[]
    let mut modArgs := #[]
    for (pos, a) in ids do
      let .some arg := args[pos]? | throwErrorAt stx s!"{t} is not fully applied"
      -- dbg_trace s!"{arg}"
      let argName := arg.raw.getId
      if argName.isAnonymous then throwErrorAt arg s!"mutable argument {arg} is not a name"
      if argName ∈ modArgs then throwErrorAt arg s!"mutable arguments cannot alias"
      modArgs := modArgs.push argName
      mods := mods.push $ <- withRef arg `(Term.doSeqItem| $(mkIdent argName):ident := $a:ident)
    return #[<-`(Term.doSeqItem| let ⟨$id, _⟩ <- $trm:term)] ++ mods
  | `(Term.doSeqItem| $trm:term) =>
    let id := mkIdent <| <- mkFreshUserName `ret
    let `($t:ident $args:term*) := trm | pure #[stx]
    -- dbg_trace s!"{t} {args}"
    let ctx <- globalMutVarsCtx.get
    let .some ids := ctx[t.getId]? | pure #[stx]
    let mut mods := #[]
    let mut modArgs := #[]
    for (pos, a) in ids do
      let .some arg := args[pos]? | throwErrorAt stx s!"{t} is not fully applied"
      -- dbg_trace s!"{arg}"
      let argName := arg.raw.getId
      if argName.isAnonymous then throwErrorAt arg s!"mutable argument {arg} is not a name"
      if argName ∈ modArgs then throwErrorAt arg s!"mutable arguments cannot alias"
      modArgs := modArgs.push argName
      mods := mods.push $ <- withRef arg `(Term.doSeqItem| $(mkIdent argName):ident := $a:ident)
    let ret <- withRef trm `(Term.doSeqItem| pure $id)
    return #[<- withRef trm `(Term.doSeqItem| let ⟨$id, _⟩ <- $trm:term)] ++ mods.push ret
  | `(Term.doSeqItem| while_some $id :| $p:term $invs* $done do $doSeq:doSeq) =>
    let doSeq <- expandLeafnyDoSeq modIds doSeq
    return #[<-`(Term.doSeqItem| while_some $id :| $p:term $invs* $done do $doSeq*)]
  | stx => pure #[stx]
end

private def Array.andListWithName (ts : Array (TSyntax `term)) (name_prefix : TSyntax `name) : TermElabM (TSyntax `term) := do
  if ts.size = 0 then `(term| True) else
    let mut t <- `(term| with_name_prefix $name_prefix:name $(ts[0]!))
    for t' in ts[1:] do
      t <- `(term| (with_name_prefix $name_prefix:name $t') ∧ $t)
    return t

private def Array.andList (ts : Array (TSyntax `term)) : TermElabM (TSyntax `term) := do
  if ts.size = 0 then `(term| True) else
    let mut t := ts[0]!
    for t' in ts[1:] do
      t <- `(term| $t' ∧ $t)
    return t

macro_rules
  | `(tactic|loom_solver_fun) =>
    `(tactic|aesop)

macro_rules
  | `(doElem| while $t
              $[invariant $inv:term
              ]*
              $[done_with $inv_done]?
              $[decreasing $measure]?
              do $seq:doSeq) => do
      let balance := mkIdent `balance_name
      let balanceType <- `(term| Balance)
      let inv : Array Term <- inv.mapM fun (inv : Term) => withRef inv ``(fun ($(balance):ident : $balanceType)=> with_name_prefix `inv $inv)
      let invd_some <- match inv_done with
      | some invd_some => withRef invd_some ``(fun ($(balance):ident : $balanceType) => with_name_prefix `done $invd_some)
      | none => ``(fun ($(balance):ident : $balanceType) => with_name_prefix `done ¬$t:term)
      match measure with
      | some measure_some =>
        let measure_some ← withRef measure_some ``(type_with_name_prefix `decreasing ($measure_some:term))
        do
        `(doElem|
          for _ in Lean.Loop.mk do
            invariantGadget [ $[$inv:term],* ]
            onDoneGadget ($invd_some:term)
            decreasingGadget ($measure_some:term)
            if $t then
              $seq:doSeq
            else break)
      | none => do
        `(doElem|
          for _ in Lean.Loop.mk do
            invariantGadget [ $[$inv:term],* ]
            onDoneGadget ($invd_some:term)
            if $t then
              $seq:doSeq
            else break)

macro_rules
| `(doElem|balance_set $t) => do
  let balId := mkIdent `balance
  `(doElem|do
    $balId:ident := $t
    set $balId:ident
    $balId:ident ← get)

elab_rules : command
| `(command|
  bdef $name:ident $binders:leafny_binder* returns ( $retId:ident : $type:term )
  $[require $req:term]*
  $[ensures $ens:term]* do $doSeq:doSeq
  ) => do
  let (defCmd, obligation) ← Command.runTermElabM fun _vs => do
    let bindersIdents ← toBracketedBinderArrayLeafny binders
    let modIds ← getModIds binders
    globalMutVarsCtx.modify (·.insert name.getId modIds)
    let modId := (mkIdent `balance)
    let modIds := #[modId]
    let doSeq <- expandLeafnyDoSeq modIds doSeq
    let mut mods := #[]
    for modId in modIds do
      -- let modIdOld := mkIdent <| modId.getId.appendAfter "Old"
      -- let modOld <- `(Term.doSeqItem| let $modIdOld:ident := $modId:ident)
      let mod <- `(Term.doSeqItem| let mut $modId:ident ← get)
      mods := mods.push mod
    let defCmd <- `(command|
      def $name $bindersIdents* : CashmereM $type := do $mods* $doSeq*)

    let reqName <- `(name| `require)
    let ensName <- `(name| `ensures)
    let pre <- req.andListWithName reqName
    let post <- ens.andListWithName ensName

    let ret <- `(term| $modId)

    let ids ← getIds binders
    let obligation : VelvetObligation := {
      binderIdents := bindersIdents
      ids := ids
      retId := retId
      ret := ret
      pre := pre
      post := post
    }
    return (defCmd, obligation)
  elabCommand defCmd
  velvetObligations.modify (·.insert name.getId obligation)

@[incremental]
elab_rules : command
  | `(command| prove_correct $name:ident by%$tkp $proof:tacticSeq) => do
    let ctx <- velvetObligations.get
    let .some obligation := ctx[name.getId]? | throwError "no obligation found"
    let bindersIdents := obligation.binderIdents
    let ids := obligation.ids
    let retId := obligation.retId
    let ret := obligation.ret
    let pre := obligation.pre
    let post := obligation.post
    let lemmaName := mkIdent <| name.getId.appendAfter "_correct"
    let proof <- withRef tkp ``(by $proof)
    let balanceOld := mkIdent `balanceOld
    let bal := mkIdent `balance
    let thmCmd <- withRef tkp `(command| lemma $lemmaName $bindersIdents* :
      ∀ $(balanceOld) : Balance,
      triple
        (fun $(bal):ident : Balance => ($bal:ident = $(balanceOld)) ∧ $pre)
        ($name $ids*)
        (fun $retId => fun $ret : Balance => $post) := $proof)
    Command.elabCommand thmCmd
    velvetObligations.modify (·.erase name.getId)

set_option linter.unusedVariables false in
def atomicAssertion {α : Type u} (n : Name) (a : α) := a

--which is definitely a queue, not a list
structure Queue (α : Type) where
  elems : List α
deriving Inhabited

namespace Queue

def empty : Queue α :=
  { elems := [] }

def isEmpty (q : Queue α) : Prop :=
  q.elems.isEmpty

def nonEmpty (q : Queue α) : Prop :=
  ¬q.elems.isEmpty

def enqueue (x : α) (q : Queue α) : Queue α :=
  { elems := x :: q.elems}

def dequeue [AddMonoid α] (q : Queue α) : α :=
  match q.elems with
  | [] => 0
  | (x :: _) => x

def tail (q : Queue α) : Queue α :=
  match q.elems with
  | [] => { elems := [] }
  | (_ :: xs) => { elems := xs }

def sum [AddMonoid α] (q : Queue α) : α := q.elems.foldr (· + ·) 0

def length (q : Queue α) : Nat := q.elems.length

instance (q : Queue α) : Decidable q.nonEmpty :=
  inferInstanceAs (Decidable (¬q.elems.isEmpty))

@[aesop unsafe]
theorem tail_length : ∀ q : Queue Nat, q.nonEmpty → q.tail.length < q.length := by
  intro q nemp
  simp [Queue.nonEmpty] at nemp
  simp [Queue.tail]
  split
  { contradiction }
  simp [Queue.length]
  rename_i x
  simp [x]

@[aesop norm]
theorem tail_sum : ∀ q : Queue Nat, nonEmpty q → q.sum = q.tail.sum + q.dequeue := by
  intro _ q
  simp [Queue.dequeue, Queue.tail, Queue.sum]
  split <;> rename_i x <;> simp [x]
  rw [add_comm]

@[aesop norm]
theorem sum_zero : ∀ q : Queue Nat, ¬q.nonEmpty → q.sum = 0 := by
  intro q nemp
  simp [Queue.nonEmpty] at nemp
  simp [Queue.sum, nemp]

end Queue
