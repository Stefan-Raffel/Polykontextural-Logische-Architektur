import Reformulation.F3c.Operators
import Mathlib.CategoryTheory.Functor.Category

/-!
# F3.c.TwoCategory — the full modal 2-category with compatibility data

This module introduces:

* `BeckChevalleyCompatibility`: the Beck-Chevalley compatibility property
  as a Prop-field placeholder (F3c_Spec.docx §IV.3 Option C). The full
  form with concrete pullback-square data is local-layer material and
  belongs in F1 or a domain study (F3c_Klaerung_3.docx §V).
* `ModalTwoCategory`: extends `ModalOperators` by three compatibility
  fields:
    - `compatTriple1`: the 2-morphism for the enforced triple `ω∘τ∘δ`,
    - `compatTriple2`: the 2-morphism for the enforced triple `τ∘ω∘δ`,
    - `beckChevalley`: the Beck-Chevalley compatibility property.

The strict 2-category form (Klärung 2 §VIII) is realized via the
strictness of functor composition itself: `(F ⋙ G) ⋙ H = F ⋙ (G ⋙ H)`
holds definitionally for endo-functors, so no additional `Strict` mixin
is imposed at this level.

See F3c_Klaerung_2.docx §I–IV, F3c_Klaerung_3.docx §III (invariant
Bestandteile 2, 5, 6, 7, 8), and F3c_Spec.docx §IV.
-/

namespace Reformulation.F3c

open CategoryTheory

/-- Beck-Chevalley compatibility for the modal operators on a base
category. Per F3c_Spec.docx §IV.3 Option C, this is captured as a
Prop placeholder; concrete pullback-square data are local-layer
material (Klärung 3 §V) and belong in F1 or a domain study. -/
structure BeckChevalleyCompatibility
    {𝒯 : Type*} [Category 𝒯]
    (tau : 𝒯 ⥤ 𝒯) (delta : 𝒯 ⥤ 𝒯) (omega : 𝒯 ⥤ 𝒯) : Prop where
  /-- Existence of the Beck-Chevalley compatibility for the modal
  operators with respect to the pullback structure of the base
  category. The full constructive form is to be supplied by F1
  or a domain study. -/
  exists_compatibility : True

/-- The full modal 2-category structure: extends `ModalOperators` with
the three compatibility data of the cyclic δ-bound entanglement and the
Beck-Chevalley compatibility.

Per F3c_Klaerung_1.docx §VI Beobachtung 2, the cyclic entanglement is
*data*, not a property — concrete compatibility components are
deployment-specific (local layer; cf. F3c_Klaerung_3.docx §V).

The compatibility 2-morphisms are written as natural transformations
from the composition to itself; in the trivial case the identity
`NatTrans.id _` is admissible, but the architecture allows non-trivial
self-naturality components. -/
structure ModalTwoCategory (𝒯 : Type*) [Category 𝒯]
    extends ModalOperators 𝒯 where
  /-- Compatibility 2-morphism for the enforced cyclic triple `ω∘τ∘δ`
  (cf. E3 in F3c_Klaerung_1.docx §IV). -/
  compatTriple1 :
    (omega ⋙ tau ⋙ delta) ⟶ (omega ⋙ tau ⋙ delta)
  /-- Compatibility 2-morphism for the enforced cyclic triple `τ∘ω∘δ`
  (cf. E4 in F3c_Klaerung_1.docx §IV). -/
  compatTriple2 :
    (tau ⋙ omega ⋙ delta) ⟶ (tau ⋙ omega ⋙ delta)
  /-- Beck-Chevalley compatibility (cf. E2; §IV.3 above). -/
  beckChevalley : BeckChevalleyCompatibility tau delta omega

end Reformulation.F3c
