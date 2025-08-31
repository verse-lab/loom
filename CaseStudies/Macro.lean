import Mathlib.Logic.Function.Basic
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.Lattice
import Mathlib.Order.Basic

import Loom.MonadAlgebras.WP.Gen
import Loom.MonadAlgebras.NonDetT.Basic

open Lean Elab Command

macro "assert" t:term : term => `(assertGadget $t)

macro "decreasing" t:term : term => `(decreasingGadget $t)

declare_syntax_cat doneWith
declare_syntax_cat decreasingTerm
declare_syntax_cat invariantClause
declare_syntax_cat invariants
syntax "invariant" termBeforeDo linebreak : invariantClause
syntax "done_with" termBeforeDo : doneWith
syntax "decreasing" termBeforeDo : decreasingTerm
syntax (invariantClause linebreak)* : invariants

syntax "let" term ":|" term : doElem
syntax "while" term
  (invariantClause)*
  (doneWith)?
  (decreasingTerm)?
  "do" doSeq : doElem
syntax "while_some" term ":|" termBeforeDo "do" doSeq : doElem
syntax "while_some" term ":|" term
  (invariantClause)*
  doneWith
  "do" doSeq : doElem
syntax "for" ident "in" termBeforeInvariant
  (invariantClause)+
  "do" doSeq : doElem

macro_rules
  | `(doElem| let $x:term :| $t) => `(doElem| let $x:term <- pickSuchThat _ (fun $x => $t))

macro_rules
  | `(doElem| while $t
              $[invariant $inv:term
              ]*
              $[done_with $inv_done]?
              $[decreasing $measure]?
              do $seq:doSeq) => do
      let invd_some ← match inv_done with
      | some invd_some => withRef invd_some ``($invd_some)
      | none => ``(¬$t:term)
      match measure with
      | some measure_some => `(doElem|
        for _ in Lean.Loop.mk do
          invariantGadget [ $[(with_name_prefix `invariant $inv:term)],* ]
          onDoneGadget (with_name_prefix `done $invd_some:term)
          decreasingGadget (type_with_name_prefix `decreasing $measure_some:term)
          if $t then
            $seq:doSeq
          else break)
      | none => `(doElem|
        for _ in Lean.Loop.mk do
          invariantGadget [ $[(with_name_prefix `invariant $inv:term)],* ]
          onDoneGadget (with_name_prefix `done $invd_some:term)
          if $t then
            $seq:doSeq
          else break)
  | `(doElem| while_some $x:ident :| $t do $seq:doSeq) =>
    match seq with
    | `(doSeq| $[$seq:doElem]*)
    | `(doSeq| $[$seq:doElem;]*)
    | `(doSeq| { $[$seq:doElem]* }) =>
      `(doElem|
        while ∃ $x:ident, $t do
          let $x :| $t
          $[$seq:doElem]*)
    | _ => Lean.Macro.throwError "while_some expects a sequence of do-elements"
  | `(doElem| while_some $x:ident :| $t
              $[invariant $inv:term
              ]*
              done_with $inv_done do
                $seq:doSeq) =>
    match seq with
    | `(doSeq| $[$seq:doElem]*)
    | `(doSeq| $[$seq:doElem;]*)
    | `(doSeq| { $[$seq:doElem]* }) =>
      `(doElem|
        for _ in Lean.Loop.mk do
          invariantGadget [ $[(with_name_prefix `invariant $inv:term)],* ]
          onDoneGadget (with_name_prefix `done $inv_done:term)
          if ∃ $x:ident, $t then
            let $x :| $t
            $[$seq:doElem]*
          else break)
    | _ => Lean.Macro.throwError "while_some expects a sequence of do-elements"
  | `(doElem| for $x:ident in $t
            invariant $inv':term
            $[invariant $inv:term
            ]*
            do $seq:doSeq) =>
      match seq with
      | `(doSeq| $[$seq:doElem]*)
      | `(doSeq| $[$seq:doElem;]*)
      | `(doSeq| { $[$seq:doElem]* }) =>
        -- let inv := invs.push inv
        `(doElem|
          for $x:ident in $t do
            invariantGadget [ $inv':term, $[$inv:term],* ]
            $[$seq:doElem]*)
      | _ => Lean.Macro.throwError "for expects a sequence of do-elements"
