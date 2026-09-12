import Loom.MonadAlgebras.NonDetT'.ExtractList

open MultiExtractor

abbrev NativeTarget (α : Type) := TsilT (PeDivM (List Unit)) α

def nativeSource : NonDetT DivM Nat := pure 7

def nativeExtracted : ConstrainedExtractResult Unit DivM NativeTarget
    (findOfCandidates Unit) nativeSource := by
  unfold nativeSource
  extract_list_tactic

def nativePersistent : PeDivM (List Nat) Nat := do
  PeDivM.log [1]
  PeDivM.log [2]
  pure 7

def nativeDiverging : PeDivM (List Nat) Nat := do
  PeDivM.log [3]
  let _ ← (([], DivM.div) : PeDivM (List Nat) Unit)
  PeDivM.log [4]
  pure 7
