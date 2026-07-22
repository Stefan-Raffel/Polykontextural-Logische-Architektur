/-
Copyright Reformulierung-Projekt 2026.
Released under PKL-internal license.
-/
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.LeftExact
import Reformulation.PathC.Classifying.GeometricTopology

/-!
# Sheafification-Adjunction for ClassifyingTopos

Wrapper for `sheafificationAdjunction` with universe consolidation
for the ClassifyingTopos context.

## Substanz

`classifyingSheafAdjunction T` is the adjunction
`presheafToSheaf (geometricTopology T) (Type (max u v)) ⊣ sheafToPresheaf ...`
directly from `sheafificationAdjunction`.

`HasSheafify (geometricTopology T) (Type (max u v))` is unconditional
(Mathlib `Sites/LeftExact.lean` — `instance : HasSheafify J (Type (max u v))`).

## Anschluss

- C23-D-7: `toSheafFunctor_rightAdjoint` — sheaf adjunction API available
- C23-B-2: `sheafToPresheaf` API directly applicable
- Konsumenten-Dokumentation: API is `sheafificationAdjunction`, not
  `sheafification.adjunction` (API-Drift §S-5)
-/

namespace Reformulation.MathlibExtensions.Sites

open CategoryTheory
open Reformulation.PathC.GeometricTheory
open Reformulation.PathC.Classifying

universe u v w

variable (T : Theory.{u, v, w})

/-- The sheaf adjunction for the ClassifyingTopos T construction.

    Specializes `sheafificationAdjunction` to `J = geometricTopology T`
    and `A = Type (max u v)`. `HasSheafify` is unconditional for this
    target category (Mathlib `Sites/LeftExact.lean:307`). -/
noncomputable def classifyingSheafAdjunction :=
  sheafificationAdjunction (geometricTopology T) (Type (max u v))

/-- Verification that HasSheafify holds for (geometricTopology T, Type (max u v)).

    Unconditional by the Mathlib instance in `Sites/LeftExact.lean:307`.
    Made explicit here for consumer documentation and scope availability. -/
instance classifyingHasSheafify : HasSheafify (geometricTopology T) (Type (max u v)) :=
  inferInstance

end Reformulation.MathlibExtensions.Sites
