import Reformulation.F3a.Stage
import Reformulation.F3a.SchemaMorphism
import Reformulation.F3a.Endofunctor
import Reformulation.F3c.Operators

/-!
# F3.a.Valuation — valuation structure with F3.c connection

This module introduces Bestandteil (ii) of F3.a:

* `SubtoposChoice`: structure class for the subtopos choice family.
  Carries a choice family type and a choice parameter type. The
  concrete subtopos choice is local-layer material.
* `Valuation`: the valuation structure for stage `n`. Bundles a base
  category, modal operators (from F3.c), a schema, and a subtopos
  choice. The form is invariant; concrete realizations are stage-
  modulated and local material.

The 2-categorical bicategory structure on `Valuation n` is described
in F3a_Spec.md §V.2 but not constructed here — its full Bicategory
instance requires the five Bicategory axioms (pentagon, triangle,
whisker exchange, etc.) which would substantially expand this module.
That construction is deferred to a future revision or to F1.

See F3a_Klaerung_1.md §II, F3a_Klaerung_2.md §II, F3a_Klaerung_3.md §III,
F3a_Spec.md §V.
-/

namespace Reformulation.F3a

open CategoryTheory
open Reformulation.F3c

/-- The subtopos choice family for stage `n`.

* `choiceFamily`: the type of the family of sub-topoi.
* `choiceParameter`: the type of the choice parameter.

The form carries the structure of the choice; the concrete realization
(which sub-topoi are in the family, how the choice parameter selects
among them) is local-layer material (Klärung 3 §III.3). -/
structure SubtoposChoice (_n : Stage) where
  choiceFamily : Type*
  choiceParameter : Type*

/-- A valuation in stage `n`.

* `baseCategory`: the base category 𝒯_n.
* `baseCategoryInst`: the Category instance on baseCategory (marked as
  an instance field so that downstream uses — like `ModalOperators
  baseCategory` — can resolve the Category type-class automatically).
* `modalOps`: the modal operator structure on the base category,
  reusing F3.c's `ModalOperators`.
* `schema`: the schema (V, E, S) for stage `n`.
* `subtoposChoice`: the subtopos choice family.

The structure form is invariant; the concrete fields are stage-modulated
(modalOps, schema) and local material (subtoposChoice).

Note: `Valuation n` is the type of *objects* of the valuation
bicategory. The 1-cells (valuation morphisms) and 2-cells
(compatibility data) of the bicategory are not constructed here;
they are deferred to a future revision. -/
structure Valuation (n : Stage) where
  baseCategory : Type
  [baseCategoryInst : Category baseCategory]
  modalOps : ModalOperators baseCategory
  schema : Schema n
  subtoposChoice : SubtoposChoice n

end Reformulation.F3a
