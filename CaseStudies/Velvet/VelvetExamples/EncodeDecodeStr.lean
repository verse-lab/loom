import Auto

import Loom.MonadAlgebras.NonDetT.Extract
import Loom.MonadAlgebras.WP.Tactic
import Loom.MonadAlgebras.WP.DoNames'

import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil

open PartialCorrectness DemonicChoice Lean.Elab.Term.DoNames

set_option auto.smt.trust true
set_option auto.smt true
set_option auto.smt.timeout 4
set_option auto.smt.solver.name "cvc5"

section RunLengthEncoding

structure Encoding where
  cnt: Nat
  c: Char
  deriving Inhabited

variable {velvetString} [arr_inst_int: TArray Char velvetString]
variable {arrEncoding} [arr_encoding_inst: TArray Encoding arrEncoding]

def get_cnt_sum (l: List Encoding) :=
  match l with
  | List.nil => 0
  | List.cons x xs => x.cnt + get_cnt_sum xs
  
@[grind]
lemma get_cnt_sum_hd e l : get_cnt_sum (e::l) = e.cnt + get_cnt_sum l := by
  conv  => {
    lhs
    unfold get_cnt_sum
  }


lemma get_cnt_sum_append l1 l2:  get_cnt_sum (l1 ++ l2) = get_cnt_sum l1 + get_cnt_sum l2 := by
  induction l1 with
  | nil => simp; rfl
  | cons e l1' ih =>
    simp_all
    grind

    

@[reducible]
def is_valid_run_sequence (encoded_str: Array Encoding) := 
    forall i, ( h: i < encoded_str.size ) -> (encoded_str[i]'h).cnt > 0 

method decodeStr' (encoded_str: Array Encoding) 
   return (res: Array Char)
   require is_valid_run_sequence encoded_str
   ensures (res.size = get_cnt_sum encoded_str.toList)
     do
       let mut decoded := Array.replicate 0 'x'
       let mut i := 0
       while i < encoded_str.size
          invariant 0 <= i ∧ i <= encoded_str.size
          invariant decoded.size = get_cnt_sum (encoded_str.extract 0 i).toList
          done_with i = encoded_str.size
          do
            let elem := encoded_str[i]!
            let elem_decoded := Array.replicate elem.cnt elem.c
            decoded :=  decoded ++ elem_decoded
            i := i + 1
       return decoded


prove_correct decodeStr' by
  loom_solve
  · simp[*] at *
    have : decoded.size = get_cnt_sum (List.take i encoded_str.toList) := by trivial
    rw [this] at *
    rw [List.take_succ_eq_append_getElem]
    rw [get_cnt_sum_append]
    simp[*]
    unfold get_cnt_sum
    rfl
  · simp[*]; rfl
  · simp_all


#eval (decodeStr' #[{cnt:= 10, c:= 'd'}, {cnt := 3, c:= 'e'}, {cnt := 5, c:= 'f'}]).run

def decodeStrLeanList (encoded_str: List Encoding) : List Char :=
  match encoded_str with
  | List.nil => List.nil
  | List.cons hd tl => (List.replicate hd.cnt hd.c) ++ (decodeStrLeanList tl)

def decodeStrLean' (encoded_str: Array Encoding) : Array Char :=
  Array.mk (decodeStrLeanList encoded_str.toList)

def decodeStrLean (encoded_str: Array Encoding) : Array Char := 
  let mp := Array.map (fun e => Array.replicate e.cnt e.c) encoded_str
  mp.flatten

lemma decodeStrLean_append : forall arr1 arr2,
  decodeStrLean (arr1 ++ arr2) = ( decodeStrLean arr1 ) ++ ( decodeStrLean arr2 ) := by
    intros arr1 arr2
    unfold decodeStrLean 
    simp_all


method encodeStr (str: Array Char) return (res: Array Encoding)
  ensures is_valid_run_sequence res
  ensures (decodeStrLean res = str) do
    let mut encoding : Array Encoding := #[]
    let mut i := 0
    while i < str.size 
    invariant 0 <= i  ∧ i <= str.size
    invariant decodeStrLean encoding = str.extract 0 i
    invariant is_valid_run_sequence encoding
    do
      let curChar := str[i]!
      let mut j := i+1
      while j < str.size ∧ str[j]! == curChar 
      invariant i < j ∧ j <= str.size
      invariant (forall k, i <= k ∧ k < j -> str[k]! = curChar )
      do
        j := j + 1
      let cnt := j - i
      encoding := encoding.push ({cnt:= cnt, c:=curChar})
      i:=j
    return encoding
    
lemma array_extract_split (arr : Array α) (i j : Nat) :
    i < j → j ≤ arr.size →
    arr.extract 0 j = (arr.extract 0 i) ++ (arr.extract i j) := by
  -- 1. Introduce hypotheses into the context
  intro h_lt h_le
  simp[*]
  grind

lemma array_extract_split_i_j_k (arr : Array α) (i j k: Nat) :
    i < j -> j < k -> k ≤ arr.size →
    arr.extract i k = (arr.extract i j) ++ (arr.extract j k) := by
  -- 1. Introduce hypotheses into the context
  intro h_lt h_le
  simp[*]
  grind

prove_correct encodeStr by
  loom_solve
  · intros k hik hkj
    grind
  · rw [array_extract_split str i j (by assumption) (by assumption)]
    rw [Array.push_eq_append]
    rw [decodeStrLean_append]
    have : decodeStrLean encoding = str.extract 0 i := by trivial
    rw [this]
    refine (Array.append_right_inj (str.extract 0 i)).mpr ?_
    repeat (unfold decodeStrLean ; simp_all)
    apply Array.ext
    grind
    intros l hl hl2
    rw [Array.size_replicate] at hl
    simp_all
    have inv : ∀ (k : ℕ), i ≤ k → k < j → str[k]! = str[i] := by trivial
    have inv' := inv (i+l)
    simp[*] at inv'
    have : i+l < j  := by grind
    have heq := (inv' this)
    have : i + l < str.size := by
      grind
    simp_all
  · dsimp[is_valid_run_sequence]
    intros k hk
    unfold is_valid_run_sequence at *
    simp_all
    rw [Array.getElem_push]
    split_ifs with hk <;> grind
  · assumption
  · unfold decodeStrLean 
    simp[*]
  · unfold is_valid_run_sequence 
    simp
  · grind
  · grind

end RunLengthEncoding
