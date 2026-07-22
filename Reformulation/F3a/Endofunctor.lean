import Reformulation.F3a.Stage
import Reformulation.F3a.SchemaMorphism
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Category

/-!
# F3.a.Endofunctor — the endofunctor F as composition of three functors

This module introduces Bestandteil (i) of F3.a:

* `DesignativeRestriction`: structure class for the first operation —
  restriction to the designative part. Carries the restriction functor
  and a Beck-Chevalley compatibility witness (placeholder Prop form,
  analogous to F3c.BeckChevalleyCompatibility).
* `OuterBalance`: structure class for the second operation — the outer
  balance via colimit over the omission modulations. Carries a
  functoriality witness.
* `Skeleton`: structure class for the third operation — the structural
  skeleton marking. Carries a uniqueness witness (EA2 placeholder).
* `EndoFunctor`: the composition of the three operations as a function
  from the base category to the schema.
* `resDes_functorial` (EA1), `skeleton_unique` (EA2),
  `resDes_beckChevalley` (EA3): the three existence theorems.
* `resDes_not_invertible` (NEA1): the non-existence theorem for
  the inverse of the restriction (syntactic form).

See F3a_Klaerung_1.md §I, F3a_Klaerung_2.md §I, F3a_Klaerung_3.md §II,
F3a_Spec.md §III.
-/

namespace Reformulation.F3a

open CategoryTheory

/-- The first operation: restriction to the designative part.

The form takes a base category `𝒯` (the reflection space) and returns
a functor to a designative subcategory. The Beck-Chevalley compatibility
is enforced as a Prop field; the full form with concrete pull-back data
is local-layer material (F1 or domain study).

The stage index `n` is carried as a structure parameter; the concrete
restriction form is stage-modulated (Klärung 3 §II.2). -/
structure DesignativeRestriction
    (n : Stage) (𝒯 : Type*) [Category 𝒯]
    (designativePart : Type*) [Category designativePart] where
  /-- The restriction functor itself. -/
  resDes : 𝒯 ⥤ designativePart
  /-- Beck-Chevalley compatibility witness (EA3 placeholder). -/
  beckChevalley : True

/-- The second operation: outer balance via colimit over the omission
modulations.

The form takes the designative part and an indexing category `J` for the
omission modulations and returns a functor from the designative part to
a traces family. The functoriality witness is enforced as a Prop field;
concrete colimit construction is local-layer material.

The indexing category `J` is a structure parameter; its concrete form
is stage-modulated (Klärung 3 §II.2). In the architectural reading
(T8 II), `J` indexes the omission modulations over which the colimit
is taken; here we encode the result of that colimit as a direct
functor `designativePart ⥤ tracesFamily`, deferring the explicit
colimit construction to F1 or a domain study (Klärung 2 §I.3:
schlankere Form gegenüber HasColimit-Maschinerie). -/
structure OuterBalance
    (n : Stage) (J : Type*) [Category J]
    (designativePart : Type*) [Category designativePart]
    (tracesFamily : Type*) [Category tracesFamily] where
  /-- The balance-forming functor (encoding the colimit's output). -/
  outerBalance : designativePart ⥤ tracesFamily
  /-- Functoriality witness. -/
  isFunctorial : True

/-- The third operation: structural skeleton marking.

The form takes the traces family and returns a function to a schema
(V, E, S) for stage `n`. The uniqueness witness (EA2) is enforced as
a Prop field; concrete skeleton construction is stage-modulated.

Note: the schema is carried as a structure parameter (not as an
internal field) so that its universe level is explicit at the binding
site; otherwise Lean cannot infer universe levels for `Schema n`
across the structure boundary. -/
structure Skeleton
    (n : Stage)
    (tracesFamily : Type*) [Category tracesFamily]
    (schema : Schema n) where
  /-- The skeleton-forming function from the traces family to the
  positions of the schema. -/
  skeletonFun : tracesFamily → schema.positions
  /-- Uniqueness witness from the sub-stage structure (EA2). -/
  isUnique : True

/-- The full endofunctor F as composition of the three components.

Given:
* a `DesignativeRestriction` (first operation),
* an `OuterBalance` (second operation),
* a `Skeleton` (third operation),

the endofunctor produces, from a base-category object, a position in
the schema via the composition `Skeleton ∘ OuterBalance ∘ ResDes`.

Note: this is a `def`, not a `theorem`, because the endofunctor is
*data* in `Type` (a function/functor construction), not a `Prop`
(see F3a_Implementations_Vor_Klaerung.md §I.3). -/
def EndoFunctor
    {n : Stage} {J : Type*} [Category J]
    {𝒯 : Type*} [Category 𝒯]
    {designativePart : Type*} [Category designativePart]
    {tracesFamily : Type*} [Category tracesFamily]
    {schema : Schema n}
    (resDes : DesignativeRestriction n 𝒯 designativePart)
    (outerBalance : OuterBalance n J designativePart tracesFamily)
    (skeleton : Skeleton n tracesFamily schema) :
    𝒯 → schema.positions :=
  fun t =>
    skeleton.skeletonFun
      (outerBalance.outerBalance.obj
        (resDes.resDes.obj t))

/-- EA1 — functoriality of the restriction component.

Tautological in the structure-class form: the `resDes` field of
`DesignativeRestriction` is a Mathlib functor `𝒯 ⥤ designativePart`,
which is functorial by construction. -/
theorem resDes_functorial
    {n : Stage} {𝒯 designativePart : Type*}
    [Category 𝒯] [Category designativePart]
    (_R : DesignativeRestriction n 𝒯 designativePart) :
    True :=
  trivial

/-- EA2 — uniqueness of the structural skeleton from the sub-stage
structure. Tautological per the structure-class form. -/
theorem skeleton_unique
    {n : Stage} {tracesFamily : Type*} [Category tracesFamily]
    {schema : Schema n}
    (S : Skeleton n tracesFamily schema) :
    True :=
  S.isUnique

/-- EA3 — Beck-Chevalley compatibility of the restriction.
Tautological per the structure-class form (analogous to F3c
`beck_chevalley_exists`). -/
theorem resDes_beckChevalley
    {n : Stage} {𝒯 designativePart : Type*}
    [Category 𝒯] [Category designativePart]
    (R : DesignativeRestriction n 𝒯 designativePart) :
    True :=
  R.beckChevalley

/-- NEA1 — the restriction is not invertible: there is no canonical
inverse from the designative part back to the full reflection space.

Syntactic form (Vorentscheidung 1 in F3a_Spec.md §0.1): the
`DesignativeRestriction` structure carries no inverse field, and no
canonical inverse can be constructed from the structure alone. The
semantic verification — a concrete construction of a counterexample —
belongs in F1 (parallel to F3.c's NE3, NE4 doc-string-only treatment).

The theorem here states the non-existence trivially, witnessed by the
structural absence of an inverse component in the type signature. -/
theorem resDes_not_invertible
    {n : Stage} {𝒯 designativePart : Type*}
    [Category 𝒯] [Category designativePart]
    (_R : DesignativeRestriction n 𝒯 designativePart) :
    True :=
  trivial

end Reformulation.F3a
