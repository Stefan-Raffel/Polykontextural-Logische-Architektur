-- EINGEFROREN (29. Juli 2026): dieser Zweig wird nicht fortgeschrieben.
-- Status, Zahlen und die Bedingungen fuer ein Auftauen: docs/build-targets.md, Abschnitt PathC.
import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
import Mathlib.CategoryTheory.Monoidal.Closed.Types
import Mathlib.CategoryTheory.Subobject.Classifier.Defs
import Mathlib.CategoryTheory.Topos.Sheaf

/-!
# Reformulation.PathC.ElementaryTopos

The first gap closure of the full Path-C implementation: an `ElementaryTopos`
typeclass that bundles Mathlib's `HasFiniteLimits`, `HasSubobjectClassifier`,
`CartesianMonoidalCategory`, and `MonoidalClosed` typeclasses.

## What this module carries

- `ElementaryTopos C` — a typeclass bundling the four components of an
  elementary topos via `extends`-inheritance.

- Four instance lemmas exposing the bundled substance: terminal objects,
  pullbacks, the subobject classifier object `Ω`, and monoidal closedness.

- Three helper theorems that make the bundling substance transparent:
  the bundling of all four components yields an `ElementaryTopos` instance;
  the converse holds; the canonical presheaf topos example.

## Methodological note

This is the first module of the Path-C subdirectory `Reformulation.PathC`.
It is parallel to the F3.x sequence and to `Reformulation.PreC`, with no
imports from either. It is not aggregated into `Reformulation.lean`.

The bundling is via `extends`-inheritance, which means an instance of
`ElementaryTopos C` automatically provides instances of all four parent
typeclasses. This is methodologically central for the subsequent Path-C
lemmas (Lücken 3–6), which assume `ElementaryTopos C` as a single typeclass
condition rather than four separate conditions.

## Klasse-B finding (B-1): current Mathlib names

The spec was written against an earlier Mathlib API. Three deprecated aliases
have been replaced with their live successors:

- `HasClassifier C`        → `HasSubobjectClassifier C`   (deprecated 2026-03-06)
- `CartesianClosed C`      → `MonoidalClosed C`            (deprecated 2025-12-22)
- `ChosenFiniteProducts C` → `CartesianMonoidalCategory C` (was a constructor name, not a typeclass)

Import paths updated accordingly:
- `Mathlib.CategoryTheory.Topos.Classifier`     → `Mathlib.CategoryTheory.Subobject.Classifier.Defs`
- `Mathlib.CategoryTheory.Closed.Cartesian`     → `Mathlib.CategoryTheory.Monoidal.Closed.Types`
- `Mathlib.CategoryTheory.ChosenFiniteProducts` → `Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory`
Additional imports for the presheaf example:
- `Mathlib.CategoryTheory.Limits.FunctorCategory.Finite`
- `Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory`
- `Mathlib.CategoryTheory.Topos.Sheaf`

## Klasse-B finding (B-2): instance construction for extends with data classes

For `class ... extends CartesianMonoidalCategory C, MonoidalClosed C`,
anonymous `⟨⟩` and `where` (without explicit fields) do not synthesize the
data-carrying parent classes automatically. The correct construction pattern is

    { (h : CartesianMonoidalCategory C) with closed := (h' : MonoidalClosed C).closed }

which fills in the `CartesianMonoidalCategory` fields via struct-inheritance
syntax and provides the `MonoidalClosed.closed` field explicitly.

## Klasse-B finding (B-3): Type u example replaced by presheaf example

`HasSubobjectClassifier (Type u)` has no direct Mathlib instance. The live
instances are `HasSubobjectClassifier (Cᵒᵖ ⥤ Type w)` for `EssentiallySmall C`
(presheaves) and `HasSubobjectClassifier (Sheaf J (Type w))` for essentially
small sites. The canonical `Type u` example from the spec is therefore replaced
by the presheaf topos example `ElementaryTopos.instPresheafTopos`.

## Klasse-B finding (B-4): components theorem uses Prop conjunction only

`CartesianMonoidalCategory C` and `MonoidalClosed C` carry data (they are not
`Prop`). The spec's `components_of_elementaryTopos` theorem used `∧` over all
four components, which is only valid for `Prop`s. The adapted theorem states
the `Prop` conjunction and provides separate `example` declarations for the
data components.

## References

S. MacLane, I. Moerdijk, *Sheaves in Geometry and Logic*, Springer 1992.
Chapter IV.
-/

namespace Reformulation.PathC

open CategoryTheory CategoryTheory.Limits

/-- An elementary topos is a category that has finite limits, a subobject
classifier, a cartesian monoidal structure, and is monoidal closed.

This bundling typeclass combines four Mathlib component typeclasses via
`extends`-inheritance. An instance of `ElementaryTopos C` thereby
automatically provides instances of `HasFiniteLimits C`,
`HasSubobjectClassifier C`, `CartesianMonoidalCategory C`, and
`MonoidalClosed C`.

Methodological pointer: the four components are not independent —
`MonoidalClosed C` requires `MonoidalCategory C`, which is provided here
by `CartesianMonoidalCategory C`. Classical elementary topos theory derives
finite limits and Cartesian closedness from a more minimal axiom set
(MacLane-Moerdijk Chapter IV). The redundancy in this bundling is
methodologically chosen: explicit `extends` of all four typeclasses makes
the Path-C lemmas transparent without needing to derive components on demand.

See the module header for the three Klasse-B adaptations relative to the
spec: updated Mathlib names (B-1), construction pattern for extends with
data classes (B-2), and presheaf example replacing `Type u` (B-3). -/
class ElementaryTopos (C : Type u) [Category.{v} C]
    extends HasFiniteLimits C, HasSubobjectClassifier C,
            CartesianMonoidalCategory C, MonoidalClosed C where

section InstanceLemmas

variable {C : Type u} [Category.{v} C] [ElementaryTopos C]

/-- An elementary topos has a terminal object. -/
instance : HasTerminal C := inferInstance

/-- An elementary topos has pullbacks. -/
instance : HasPullbacks C := inferInstance

/-- An elementary topos has a chosen subobject classifier object Ω. -/
noncomputable example : C := HasSubobjectClassifier.Ω C

/-- An elementary topos is monoidal closed. -/
noncomputable example : MonoidalClosed C := inferInstance

end InstanceLemmas

section HelperTheorems

/-- Bundling theorem: given the four component typeclass instances,
    `ElementaryTopos C` is derivable.

    Construction note: the `extends` form with data-carrying parent classes
    requires the struct-inheritance syntax `{ h with ... }` rather than `⟨⟩`
    (Klasse-B finding B-2). -/
noncomputable instance elementaryTopos_of_components {C : Type u} [Category.{v} C]
    [HasFiniteLimits C] [HasSubobjectClassifier C]
    [h3 : CartesianMonoidalCategory C] [h4 : MonoidalClosed C] :
    ElementaryTopos C :=
  { h3 with closed := h4.closed }

/-- Canonical presheaf topos example: the presheaf category over an essentially
    small category is an elementary topos.

    This replaces the `Type u` example from the spec; `HasSubobjectClassifier (Type u)`
    has no direct Mathlib instance (Klasse-B finding B-3).

    The four component instances for `Cᵒᵖ ⥤ Type (max u v)` are:
    - `HasFiniteLimits`: via `FunctorCategory.Finite` + `HasFiniteLimits (Type (max u v))`
    - `HasSubobjectClassifier`: via `Topos.Sheaf` for `EssentiallySmall.{max u v} C`
    - `CartesianMonoidalCategory`: via `Monoidal.Cartesian.FunctorCategory`
    - `MonoidalClosed`: via `Monoidal.Closed.Types` -/
noncomputable instance instPresheafTopos {C : Type u} [Category.{v} C]
    [EssentiallySmall.{max u v} C] :
    ElementaryTopos (Cᵒᵖ ⥤ Type (max u v)) :=
  { (inferInstance : CartesianMonoidalCategory (Cᵒᵖ ⥤ Type (max u v))) with
    closed := (inferInstance : MonoidalClosed (Cᵒᵖ ⥤ Type (max u v))).closed }

/-- Unbundling theorem (Prop components): an elementary topos has the two
    Prop-valued component typeclass instances.

    Adaptation note: `CartesianMonoidalCategory C` and `MonoidalClosed C` carry
    data and are not `Prop`, so they cannot appear in `∧`. They are accessible
    via `inferInstance` (see the `example` declarations below), owing to the
    `extends`-inheritance of `ElementaryTopos`. (Klasse-B finding B-4.) -/
theorem prop_components_of_elementaryTopos {C : Type u} [Category.{v} C]
    [ElementaryTopos C] :
    HasFiniteLimits C ∧ HasSubobjectClassifier C :=
  ⟨inferInstance, inferInstance⟩

/-- Data component: `CartesianMonoidalCategory C` is accessible from `ElementaryTopos C`. -/
example {C : Type u} [Category.{v} C] [ElementaryTopos C] : CartesianMonoidalCategory C :=
  inferInstance

/-- Data component: `MonoidalClosed C` is accessible from `ElementaryTopos C`. -/
noncomputable example {C : Type u} [Category.{v} C] [ElementaryTopos C] : MonoidalClosed C :=
  inferInstance

end HelperTheorems

end Reformulation.PathC
