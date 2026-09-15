module

import Consumer

public def main : IO UInt32 :=
  match nativeExtracted.val, nativePersistent, nativeDiverging with
  | [([], .res 7)], ([1, 2], .res 7), ([3], .div) => pure 0
  | _, _, _ => pure 1
