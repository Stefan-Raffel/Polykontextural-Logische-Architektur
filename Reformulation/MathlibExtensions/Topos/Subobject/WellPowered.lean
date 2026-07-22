/-
Copyright Reformulierung-Projekt 2026.
Released under PKL-internal license.
-/
import Mathlib.CategoryTheory.Subobject.WellPowered
import Mathlib.CategoryTheory.Subobject.Classifier.Defs
import Mathlib.Logic.Small.Basic
import Reformulation.PathC.ElementaryTopos

/-!
# WellPowered for ElementaryTopos

## Main result

- `ElementaryTopos.wellPowered`: every elementary topos is `WellPowered.{v}` (where `v` is
  the morphism universe of the category). That is, `Small.{v} (Subobject X)` for all `X`.

## Mathematical content

The subobject classifier gives a natural bijection
  `(X ⟶ Ω) ≃ Subobject X`
via `Subobject.Classifier.representableBy.homEquiv`.

Since `(X ⟶ Ω) : Type v` (the hom-type lives in the morphism universe), and this type
injects into `Subobject X`, we obtain `Small.{v} (Subobject X)` by
`small_of_injective`.

`LocallySmall.{v} E` is automatic from `Category.{v} E` via `locallySmall_self`.

## Anschluss (C21-B6)

Resolves the `WellPowered` hypothesis among the six needed for
`CompleteLattice (Subobject B)`. Together with `InitialMonoClass` (InitialMonoClass.lean),
two of the six hypotheses are now derived from `ElementaryTopos`.
-/

namespace Reformulation.MathlibExtensions.Topos

open CategoryTheory Subobject Limits Reformulation.PathC

variable {E : Type*} [Category E] [ElementaryTopos E]

section WellPoweredInstance

universe u v

variable (E' : Type u) [Category.{v} E'] [ElementaryTopos E']

private noncomputable def classifierEq : Subobject.Classifier E' :=
  HasSubobjectClassifier.exists_classifier.some

/-- Every elementary topos is `WellPowered.{v}` via the subobject classifier:
`Subobject X ≃ (X ⟶ Ω)` with `(X ⟶ Ω) : Type v`, hence `Small.{v} (Subobject X)`. -/
instance ElementaryTopos.wellPowered : WellPowered.{v} E' where
  subobject_small X :=
    small_of_injective (α := Subobject X) (β := X ⟶ (classifierEq E').Ω)
      (f := (classifierEq E').representableBy.homEquiv.symm)
      (classifierEq E').representableBy.homEquiv.symm.injective

end WellPoweredInstance

end Reformulation.MathlibExtensions.Topos
