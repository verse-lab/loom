module

public import Loom.MonadAlgebras.NonDetT'.ExtractListBasic
public import Mathlib.Data.FinEnum

/-!
Opt-in compatibility for clients that use `FinEnum` to supply candidates.
The list order is exactly `FinEnum.toList`, as in the former Loom instance.
-/

@[expose] public section

namespace LoomMathlib

instance candidatesOfFinEnum {α : Type u} {p : α → Prop}
    [FinEnum α] [DecidablePred p] : MultiExtractor.Candidates p where
  find := fun _ => (FinEnum.toList α).filter p
  find_iff x := List.mem_filter.trans
    ⟨fun h => of_decide_eq_true h.2, fun h => ⟨FinEnum.mem_toList x, decide_eq_true h⟩⟩

end LoomMathlib
