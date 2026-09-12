import Loom.MonadAlgebras.NonDetT'.ExtractListBasic
import Mathlib.Data.FinEnum

/-!
Opt-in compatibility for clients that use `FinEnum` to supply candidates.
The list order is exactly `FinEnum.toList`, as in the former Loom instance.
-/

namespace LoomMathlib

instance candidatesOfFinEnum {α : Type u} {p : α → Prop}
    [FinEnum α] [DecidablePred p] : MultiExtractor.Candidates p where
  find := fun _ => (FinEnum.toList α).filter p
  find_iff := by simp

end LoomMathlib
