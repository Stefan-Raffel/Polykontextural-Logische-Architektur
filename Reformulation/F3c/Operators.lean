import Reformulation.F3c.Symbols
import Mathlib.CategoryTheory.Functor.Basic

/-!
# F3.c.Operators — the modal operators as a structure class

This module introduces:

* `ModalOperators`: a bundle of three endo-functors `tau`, `delta`, `omega`
  on a base category `𝒯`. The class itself does not require these
  operators to be distinct or to satisfy any compatibility conditions —
  those are added in `ModalTwoCategory` (see F3c.TwoCategory).
* `ModalOperators.symbol`: dispatch from `ModalSymbol` to the corresponding
  functor field.
* `ModalOperators.interpret`: the bridge between syntactic level
  (`List ModalSymbol`, with `IsSmooth` classification) and semantic level
  (functor composition on `𝒯`).

See F3c_Klaerung_3.docx §III (invariant Bestandteile 1, 3) and
F3c_Spec.docx §III.
-/

namespace Reformulation.F3c

open CategoryTheory

variable {𝒯 : Type*} [Category 𝒯]

/-- Three endo-functors on a base category, representing the modal triad
τ, δ, ω at the level of structural form. The concrete realization of the
fields is left to the deployment (per F3c_Klaerung_3.docx §IV — the
concrete operator assignment is stage-modulated; concrete compatibility
data are local).
-/
structure ModalOperators (𝒯 : Type*) [Category 𝒯] where
  /-- The displacement / time-mode operator. -/
  tau : 𝒯 ⥤ 𝒯
  /-- The reorganization / thinking-mode operator (not self-supporting). -/
  delta : 𝒯 ⥤ 𝒯
  /-- The positing / will-mode operator. -/
  omega : 𝒯 ⥤ 𝒯

namespace ModalOperators

/-- Dispatch from `ModalSymbol` to the corresponding endo-functor.
For the three original modal operators `tau`, `delta`, `omega` the
corresponding functor field is returned. The three negation symbols
`negTau`, `negDelta`, `negOmega` (added in F3.d) fall back to `𝟭 𝒯`
here — a totality placeholder required after `ModalSymbol` was extended
to six constructors (F3d_Spec §I.1, Class-D adaptation).
Full dispatch including negation functors is available via
`Reformulation.F3d.ModalTwoCategoryWithNegations.symbolFull`. -/
def symbol (M : ModalOperators 𝒯) : ModalSymbol → (𝒯 ⥤ 𝒯)
  | .tau      => M.tau
  | .delta    => M.delta
  | .omega    => M.omega
  | .negTau   => 𝟭 𝒯
  | .negDelta => 𝟭 𝒯
  | .negOmega => 𝟭 𝒯

/-- Semantic interpretation of a symbol-list composition as a functor
on `𝒯`. The empty list goes to the identity functor; a cons-list goes
to the composition of the head's functor with the tail's interpretation.

This is the bridge between the syntactic `IsSmooth` classification and
semantic statements about endo-functors on `𝒯`.
-/
def interpret (M : ModalOperators 𝒯) : List ModalSymbol → (𝒯 ⥤ 𝒯)
  | []      => 𝟭 𝒯
  | s :: ss => M.symbol s ⋙ M.interpret ss

@[simp]
theorem interpret_nil (M : ModalOperators 𝒯) :
    M.interpret [] = 𝟭 𝒯 := rfl

@[simp]
theorem interpret_cons (M : ModalOperators 𝒯)
    (s : ModalSymbol) (ss : List ModalSymbol) :
    M.interpret (s :: ss) = M.symbol s ⋙ M.interpret ss := rfl

@[simp]
theorem symbol_tau (M : ModalOperators 𝒯) : M.symbol .tau = M.tau := rfl
@[simp]
theorem symbol_delta (M : ModalOperators 𝒯) : M.symbol .delta = M.delta := rfl
@[simp]
theorem symbol_omega (M : ModalOperators 𝒯) : M.symbol .omega = M.omega := rfl

end ModalOperators

end Reformulation.F3c
