import Loom.MonadAlgebras.NonDetT'.ExtractList

open MultiExtractor

abbrev NativeTarget (α : Type) := TsilT (PeDivM (List Unit)) α

def nativeSource : NonDetT DivM Nat := pure 7

def nativeExtracted : ConstrainedExtractResult Unit DivM NativeTarget
    (findOfCandidates Unit) nativeSource := by
  unfold nativeSource
  extract_list_tactic
