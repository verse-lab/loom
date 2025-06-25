import Lean
import Lean.Parser

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Ring.Int.Defs

import Loom.MonadAlgebras.NonDetT.Extract
import Loom.MonadAlgebras.WP.Tactic

import Loom.MonadAlgebras.Velvet.Extension
import Loom.MonadAlgebras.WP.DoNames'

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

syntax "method" ident leafny_binder* "return" "(" ident ":" term ")"
  (require_caluse )*
  (ensures_caluse)* "do" doSeq linebreak "correct_by" term : command

syntax (priority := high) ident noWs "[" term "]" ":=" term : doElem
syntax (priority := high) ident noWs "[" term "]" "+=" term : doElem

macro_rules
  | `(doElem|$id:ident[$idx:term] := $val:term) =>
    `(doElem| $id:term := ($id:term).modify $idx (fun _ => $val))
  | `(doElem|$id:ident[$idx:term] += $val:term) =>
    `(doElem| $id:term := ($id:term).modify $idx (· + $val))

private def toBracketedBinderArray (stx : Array (TSyntax `leafny_binder)) : MetaM (TSyntaxArray `Lean.Parser.Term.bracketedBinder) := do
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
  | `(Term.doSeqItem| return) => expandLeafnyDoSeqItem modIds $ <- `(Term.doSeqItem| return ())
  | `(Term.doSeqItem| return $t) =>
    let mut ret <- `(term| ())
    for modId in modIds do
      ret <- `(term| ⟨$modId, $ret⟩)
    return #[<-`(Term.doSeqItem| return ⟨$t, $ret⟩)]
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

private def Array.andListWithName (ts : Array (TSyntax `term)) : TermElabM (TSyntax `term) := do
  if ts.size = 0 then `(term| True) else
    let mut t <- `(term| with_name_prefix `ensures $(ts[0]!))
    for t' in ts[1:] do
      t <- `(term| (with_name_prefix `ensures $t') ∧ $t)
    return t

private def Array.andList (ts : Array (TSyntax `term)) : TermElabM (TSyntax `term) := do
  if ts.size = 0 then `(term| True) else
    let mut t := ts[0]!
    for t' in ts[1:] do
      t <- `(term| $t' ∧ $t)
    return t


elab_rules : command
  | `(command|
  method $name:ident $binders:leafny_binder* return ( $retId:ident : $type:term )
  $[require $req:term]*
  $[ensures $ens:term]* do $doSeq:doSeq
  correct_by $proof:term) => do
  let (defCmd, thmCmd) ← Command.runTermElabM fun _vs => do
    let bindersIdents ← toBracketedBinderArray binders

    let modIds ← getModIds binders
    globalMutVarsCtx.modify (·.insert name.getId modIds)
    let modIds := modIds.map (·.2)
    let doSeq <- expandLeafnyDoSeq modIds doSeq

    let mut mods := #[]
    for modId in modIds do
      -- let modIdOld := mkIdent <| modId.getId.appendAfter "Old"
      -- let modOld <- `(Term.doSeqItem| let $modIdOld:ident := $modId:ident)
      let mod <- `(Term.doSeqItem| let mut $modId:ident := $modId:ident)
      mods := mods.push mod
    let mutTypes ← getMutTypes binders
    let mut retType <- `(Unit)
    for mutType in mutTypes, modId in modIds do
      retType <- `(($modId:ident : $mutType) × $retType)
    let defCmd <- `(command|
      def $name $bindersIdents* : NonDetT DivM (($retId:ident : $type) × $retType) := do $mods* $doSeq*)
    let lemmaName := mkIdent <| name.getId.appendAfter "_correct"

    let pre <- req.andList
    let post <- ens.andListWithName

    let mut ret <- `(term| ())
    for modId in modIds do
      let modId := mkIdent <| modId.getId.appendAfter "New"
      ret <- `(term| ⟨$modId, $ret⟩)

    let ids ← getIds binders
    let thmCmd <- `(command|
      lemma $lemmaName $bindersIdents* :
      $pre ->
      triple
        True
        ($name $ids*)
        (fun ⟨$retId, $ret⟩ => $post) := $proof)
    return (defCmd, thmCmd)
  elabCommand defCmd
  trace[Loom.debug] "{thmCmd}"
  elabCommand thmCmd

set_option linter.unusedVariables false in
def atomicAssertion {α : Type u} (n : Name) (a : α) := a
