import LoomMathlib

open MultiExtractor

local instance : FinEnum Bool :=
  FinEnum.ofNodupList [true, false] (by decide) (by decide)

-- Check both automatic instance synthesis and preservation of enumeration order.
example : Candidates (fun b : Bool => b = true) := inferInstance

example {α : Type u} [FinEnum α] (p : α → Prop) [DecidablePred p] :
    Candidates.find p () = (FinEnum.toList α).filter p := rfl

#guard Candidates.find (fun b : Bool => b = true) () == [true]
#guard Candidates.find (fun _ : Bool => False) () == []
#guard Candidates.find (fun _ : Bool => True) () == [true, false]
