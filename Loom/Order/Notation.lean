import Loom.Order.Instances
import Lean

namespace Loom.Order

attribute [scoped refl] Std.le_refl

scoped notation (priority := high) "⊤" => top
scoped notation (priority := high) "⊥" => bot
scoped infixr:60 (priority := high) " ⇨ " => himp
scoped postfix:max (priority := high) "ᶜ" => compl

scoped macro:60 (priority := high) "⨅ " x:ident ", " body:term:60 : term => `(iInf (fun $x => $body))
scoped macro:60 (priority := high) "⨆ " x:ident ", " body:term:60 : term => `(iSup (fun $x => $body))
scoped macro:60 (priority := high) "⨅ " x:ident " : " ty:term ", " body:term:60 : term =>
  `(iInf (fun ($x : $ty) => $body))
scoped macro:60 (priority := high) "⨆ " x:ident " : " ty:term ", " body:term:60 : term =>
  `(iSup (fun ($x : $ty) => $body))
scoped macro:60 (priority := high) "⨅ " x:ident " ∈ " xs:term ", " body:term:60 : term =>
  `(iInf (fun $x => iInf (fun (_ : $x ∈ $xs) => $body)))
scoped macro:60 (priority := high) "⨆ " x:ident " ∈ " xs:term ", " body:term:60 : term =>
  `(iSup (fun $x => iSup (fun (_ : $x ∈ $xs) => $body)))

end Loom.Order
