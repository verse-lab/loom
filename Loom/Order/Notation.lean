import Loom.Order.Instances
import Lean

namespace Loom.Order

attribute [refl] le_refl ge_refl
attribute [congr] iInf_congr_prop iSup_congr_prop

scoped notation "⊤ₗ" => top
scoped notation "⊥ₗ" => bot
scoped infix:50 " ⊒ₗ " => fun a b => Preorder.le b a
scoped infixr:60 " ⇨ₗ " => himp
scoped postfix:max "ᶜₗ" => compl

scoped macro:60 "⨅ₗ " x:ident ", " body:term:60 : term => `(iInf (fun $x => $body))
scoped macro:60 "⨆ₗ " x:ident ", " body:term:60 : term => `(iSup (fun $x => $body))
scoped macro:60 "⨅ₗ " x:ident " : " ty:term ", " body:term:60 : term =>
  `(iInf (fun ($x : $ty) => $body))
scoped macro:60 "⨆ₗ " x:ident " : " ty:term ", " body:term:60 : term =>
  `(iSup (fun ($x : $ty) => $body))
scoped macro:60 "⨅ₗ " x:ident " ∈ " xs:term ", " body:term:60 : term =>
  `(iInf (fun $x => iInf (fun (_ : $x ∈ $xs) => $body)))
scoped macro:60 "⨆ₗ " x:ident " ∈ " xs:term ", " body:term:60 : term =>
  `(iSup (fun $x => iSup (fun (_ : $x ∈ $xs) => $body)))

end Loom.Order
