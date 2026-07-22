/-
Copyright Reformulierung-Projekt 2026.
Released under PKL-internal license.
-/
import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.Limits.Shapes.StrictInitial
import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian
import Reformulation.PathC.ElementaryTopos

/-!
# HasStrictInitialObjects and InitialMonoClass for ElementaryTopos

## Main results

- `ElementaryTopos.hasStrictInitialObjects`: every elementary topos has a strict initial
  object, i.e., every morphism into the initial object is an isomorphism.

- `ElementaryTopos.initialMonoClass`: every morphism FROM the initial object in an
  elementary topos is a monomorphism. Derived automatically from the strict initial instance.

## Mathematical content

The proof uses `CategoryTheory.strict_initial` (Mathlib/CategoryTheory/Monoidal/Closed/Cartesian.lean):
in any CCC (`CartesianMonoidalCategory` + `MonoidalClosed`), any morphism to an initial
object is an isomorphism. `ElementaryTopos` extends both, so `strict_initial` applies
directly (with `Closed A` provided by `MonoidalClosed.closed`).

`HasStrictInitialObjects` is assembled via `hasStrictInitialObjects_of_initial_is_strict`,
and `InitialMonoClass` follows from `initial_mono_of_strict_initial_objects` by the
standard Mathlib instance chain.

## Anschluss (C21-B5, C21-B6)

- Resolves: `OrderBot (Subobject X)` for `[ElementaryTopos E]` (needs `InitialMonoClass`)
- Resolves: `BoundedOrder (Subobject B)` for `[ElementaryTopos E]`
- Klasse-D-Shift C21-B5 closed.
-/

namespace Reformulation.MathlibExtensions.Topos

open CategoryTheory Limits Reformulation.PathC

-- HasInitial is NOT part of our ElementaryTopos definition (which only bundles
-- HasFiniteLimits for LIMITS, not colimits). Every topos has an initial object
-- (theorem of topos theory), but that derivation is not yet in Mathlib for our
-- ElementaryTopos typeclass. We add [HasInitial E] as a consumer hypothesis here.
-- (Klasse-B/ζ finding: matches B-3/ζ in TermSemantics.lean.)
variable {E : Type*} [Category E] [ElementaryTopos E] [HasInitial E]

/-- Every elementary topos (with [HasInitial E]) has strict initial objects: any
morphism into the initial object is an isomorphism.

Proof: `ElementaryTopos` extends `CartesianMonoidalCategory` and `MonoidalClosed`
(= CCC), so `strict_initial` (Mathlib/CategoryTheory/Monoidal/Closed/Cartesian.lean)
applies. The `[Closed A]` instance is provided by `MonoidalClosed.closed`.

Note: `[HasInitial E]` is a consumer hypothesis; every topos has an initial object
but this is not encoded in the current `ElementaryTopos` typeclass. -/
instance ElementaryTopos.hasStrictInitialObjects : HasStrictInitialObjects E :=
  hasStrictInitialObjects_of_initial_is_strict fun _A f =>
    strict_initial initialIsInitial f

/-- Every elementary topos (with [HasInitial E]) satisfies `InitialMonoClass`:
all morphisms from the initial object are monomorphisms.
Derived from `HasStrictInitialObjects` via `initial_mono_of_strict_initial_objects`. -/
instance ElementaryTopos.initialMonoClass : InitialMonoClass E := inferInstance

end Reformulation.MathlibExtensions.Topos
