import Mathlib.CategoryTheory.Topos.Sheaf
import Reformulation.PreC.SiteAnschluss

/-!
# Reformulation.PreC.ClassifierAnschluss — Phase-B connection: subobject classifier

Connects PKL contexture components to Mathlib's subobject-classifier
machinery (Phase B of the Pre-C tractability demonstration).

Demonstrates that each `ContextureComponent n` carries a subobject
classifier — the internal logical structure (truth values, propositions)
required by the PKL architecture — by inheriting Mathlib's 2026 instance
for sheaf categories over essentially small sites.

The instance chain is:
  `contextureIndex_essentiallySmall`
    → `HasSubobjectClassifier (Sheaf J (Type w))` (Mathlib, Topos.Sheaf)
      → `HasSubobjectClassifier (ContextureComponent n)`
-/

namespace Reformulation.PreC

open CategoryTheory

/-- Each `ContextureComponent n` has a subobject classifier, inherited from
    Mathlib's instance for sheaf categories on essentially small sites.

    Methodological point: this demonstrates that PKL contexture components
    carry an internal logical structure (truth values Ω, characteristic
    morphisms χ, the truth morphism), which is the Phase-B foundation
    required for the full Pre-C classifying-topos construction. -/
example (n : Nat) : HasSubobjectClassifier (ContextureComponent n) :=
  inferInstance

end Reformulation.PreC
