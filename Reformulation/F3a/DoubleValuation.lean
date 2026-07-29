import Reformulation.F3a.Valuation

/-!
# F3.a.DoubleValuation — double valuation with compatibility

This module introduces Bestandteil (iv) of F3.a:

* `DoubleValuation`: the double valuation structure for stage `n`.
  Bundles two valuations on the same stage plus a compatibility
  component (placeholder Prop form, "Beck-Chevalley-related"
  per Klärung 1 §IV.1).

Per Klärung 2 §IV.3 (Wahl Option B), the form is a slim structure
class without explicit Pseudofunctor form. The "Beck-Chevalley-related"
character is documented in this doc-string but not constructed in the
type signature.

The existence of a double valuation in a domain is local-layer material
(Klärung 3 §V.3); F3.a only stores the form.

See F3a_Klaerung_1.md §IV, F3a_Klaerung_2.md §IV, F3a_Klaerung_3.md §V,
F3a_Spec.md §VI.
-/

namespace Reformulation.F3a

/-- A double valuation in stage `n`.

* `valuation₁`: the first valuation.
* `valuation₂`: the second valuation (parallel to the first, on the
  same invariant layer in the same stage).
* `compatibility`: a compatibility datum between the two valuations.
  Placeholder Prop form; the concrete "Beck-Chevalley-related" form
  (Klärung 1 §IV.1) is local-layer material per Klärung 3 §V.3.

The architectural example (D2-T11 IV) is Ethereum-Gasper, where
LMD-GHOST in the block layer and Casper-FFG in the epoch layer
form a double valuation with hybrid trade-off compatibility. -/
structure DoubleValuation (n : Stage) where
  valuation₁ : Valuation n
  valuation₂ : Valuation n
  /-- Compatibility datum between the two valuations. **Placeholder** (register
  row `S15`): the concrete Beck-Chevalley-related form (Klärung 1 §IV.1) is
  local-layer material. Exit: give the field a 2-cell that can fail; until then
  no filling of it can fail either. -/
  compatibility : True

end Reformulation.F3a
