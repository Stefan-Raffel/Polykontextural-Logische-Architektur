import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-!
# Reformulation.PreC.GeometricMorphismMin — Minimal geometric morphism structure class

Defines the minimal structure class for geometric morphisms, as Eigen-Maschinerie
for the Pre-C tractability demonstration. The full 2-categorical structure
(composition, 2-morphisms, adjunction compatibilities) is reserved for a
subsequent full Pre-C implementation; see `Reformulation.PreC.Reflexion`.

A geometric morphism `f : E → F` (in the topos-theoretic sense) consists of:
- an inverse image functor `f⁻¹ : F ⥤ E` (left adjoint),
- a direct image functor `f_* : E ⥤ F` (right adjoint),
- an adjunction `f⁻¹ ⊣ f_*`,
- the requirement that `f⁻¹` preserves finite limits (left-exactness).

This module is autonomous: no imports from other PreC modules.
-/

namespace Reformulation.PreC

open CategoryTheory Limits

/-- Minimal structure class for geometric morphisms between categories.

    A geometric morphism `E → F` (topos-theoretically: from `E` to `F`)
    consists of a left-exact left adjoint (inverse image) and its right
    adjoint (direct image). This is the minimal form: no 2-categorical
    structure, no composition laws, no compatibility theorems. -/
structure GeometricMorphismMin (E F : Type*) [Category E] [Category F] where
  /-- Inverse image functor: `F ⥤ E`, left adjoint, must preserve finite limits. -/
  inverse : F ⥤ E
  /-- Direct image functor: `E ⥤ F`, right adjoint. -/
  direct : E ⥤ F
  /-- The adjunction: `inverse ⊣ direct`. -/
  adjunction : inverse ⊣ direct
  /-- Left-exactness of the inverse image: preserves finite limits. -/
  inverse_preservesFiniteLimits : PreservesFiniteLimits inverse

/-- Identity geometric morphism on a category with finite limits.
    Both functors are the identity, the adjunction is the identity adjunction.
    Demonstrates realisability of the structure class. -/
def trivialGeometricMorphism (E : Type*) [Category E] [HasFiniteLimits E] :
    GeometricMorphismMin E E where
  inverse := 𝟭 E
  direct := 𝟭 E
  adjunction := Adjunction.id
  inverse_preservesFiniteLimits := inferInstance

end Reformulation.PreC
