import Consumer

def main : IO UInt32 :=
  match nativeExtracted.val with
  | [([], .res 7)] => pure 0
  | _ => pure 1
