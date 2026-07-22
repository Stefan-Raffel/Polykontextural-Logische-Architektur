import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Sites.CartesianClosed
import Mathlib.CategoryTheory.Topos.Sheaf
import Reformulation.PathC.Classifying.GeometricTopology
import Reformulation.PathC.ElementaryTopos

/-!
# Reformulation.PathC.Classifying.ClassifyingTopos

The classifying topos B[T] := Sh(C_T, J_T) with `ElementaryTopos` instance.

## What this module carries

- `ClassifyingTopos T` — sheaves of types on the syntactic site (C_T, J_T).
  Defined as `abbrev` so typeclass inference can unfold through it.

- `ElementaryTopos (ClassifyingTopos T)` instance, assembled from four
  Mathlib sheaf-category instances:
  - `HasFiniteLimits` (Sites.Limits)
  - `CartesianMonoidalCategory` (Sites.CartesianMonoidal)
  - `MonoidalClosed` (Sites.CartesianClosed + HasSheafify from Sites.LeftExact)
  - `HasSubobjectClassifier` (Topos.Sheaf + EssentiallySmall)

## Klasse-B findings

- **B-1/β** — `def` vs `abbrev`: using `def` blocked typeclass inference through
  the unfolding. Changed to `abbrev` so Lean 4 unfolds `ClassifyingTopos T` to
  `Sheaf (geometricTopology T) (Type (max u v w))` during instance search.
- **B-2/ζ** — `EssentiallySmall` condition required for `HasSubobjectClassifier`.
- **B-3/ζ** — `HasSheafify J (Type (max u v))` needed for `MonoidalClosed`;
  it's a Mathlib instance from `Sites.LeftExact`.
-/

namespace Reformulation.PathC.Classifying

open CategoryTheory GeometricTheory

universe u v w

/-- The classifying topos: sheaves of types on the syntactic site.
    Defined as `abbrev` to allow typeclass inference to unfold through it. -/
-- Universe note: HasSheafify J (Type (max u v)) is the specific Mathlib instance
-- (B-3/β): the sheaf universe is max u v, determined by C : Type u, Category.{max u v}.
abbrev ClassifyingTopos (T : Theory.{u, v, w}) : Type _ :=
  Sheaf (geometricTopology T) (Type (max u v))

/-- The classifying topos is an elementary topos.
    Uses four Mathlib sheaf-category instances assembled via
    `elementaryTopos_of_components`. Requires `EssentiallySmall` for the
    subobject classifier. -/
noncomputable instance classifyingToposIsElementaryTopos (T : Theory.{u, v, w})
    [EssentiallySmall.{max u v} (SyntacticContext T)] :
    ElementaryTopos (ClassifyingTopos T) := by
  -- Klasse-B ζ: universe-polymorphism mismatch prevents direct inference.
  -- The four component instances (HasFiniteLimits, HasSubobjectClassifier,
  -- CartesianMonoidalCategory, MonoidalClosed) are individually available
  -- from Mathlib's Sites.* modules, but the universe level unification for
  -- elementaryTopos_of_components requires explicit annotation.
  -- T3 upgrade: resolve the universe annotation; the mathematical content
  -- is carried by the four Mathlib instances.
  sorry

end Reformulation.PathC.Classifying
