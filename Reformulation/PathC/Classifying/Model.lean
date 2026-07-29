-- EINGEFROREN (29. Juli 2026): dieser Zweig wird nicht fortgeschrieben.
-- Status, Zahlen und die Bedingungen fuer ein Auftauen: docs/build-targets.md, Abschnitt PathC.
import Reformulation.PathC.Classifying.TermSemantics

/-!
# Reformulation.PathC.Classifying.Model

Models of a geometric theory in an elementary topos.

## D-4 design

`Model T E` extends `ModelInterp T E` (from TermSemantics.lean) with `satisfies`.
This avoids the `ElementaryTopos (Type ?u)` elaboration failure for `funcInterp`/`relInterp`
field types: `ModelInterp` already handles those fields correctly.

`satisfies` uses `interpretFormula toModelInterp` where `toModelInterp : ModelInterp T E`
is the auto-generated projection from `extends ModelInterp T E`.
-/

namespace Reformulation.PathC.Classifying

open CategoryTheory GeometricTheory Limits

universe u v w

attribute [local instance] has_smallest_coproducts_of_hasCoproducts

/-- A model of geometric theory T in elementary topos E.

    Extends `ModelInterp T E` with a satisfaction condition for each axiom.

    **D-4 B-3**: `funcInterp` and `relInterp` come from `ModelInterp T E`. -/
structure Model (T : Theory.{u, v, w}) (E : Type*) [Category E] [ElementaryTopos E]
    [HasColimitsOfShape (Discrete PEmpty.{1}) E]
    [HasImages E]
    [LocallySmall.{max u (max v w)} E] [HasWidePullbacks.{max u (max v w)} E]
    [HasCoproducts.{max u (max v w)} E] [WellPowered.{max u (max v w)} E]
    [InitialMonoClass E]
    extends ModelInterp T E where
  /-- Satisfaction condition: each axiom is satisfied. -/
  satisfies : ∀ ax ∈ T.axioms,
    interpretFormula toModelInterp ax.hypothesis ≤
    interpretFormula toModelInterp ax.conclusion

namespace Model

variable {T : Theory.{u, v, w}} {E : Type*} [Category E] [ElementaryTopos E]
    [HasColimitsOfShape (Discrete PEmpty.{1}) E]
    [HasImages E]
    [LocallySmall.{max u (max v w)} E] [HasWidePullbacks.{max u (max v w)} E]
    [HasCoproducts.{max u (max v w)} E] [WellPowered.{max u (max v w)} E]
    [InitialMonoClass E]

/-- A model determines a sort interpretation. -/
def toSortInterp (M : Model T E) : SortInterp T E := M.sortInterp

/-- Convenience alias: `M.interp = M.sortInterp`. -/
abbrev interp (M : Model T E) : SortInterp T E := M.sortInterp

/-- Two models are equal iff their ModelInterp components agree. -/
theorem ext (M N : Model T E)
    (h : M.toModelInterp = N.toModelInterp) :
    M = N := by
  obtain ⟨MI_M, _⟩ := M
  obtain ⟨MI_N, _⟩ := N
  simp only at h
  subst h
  simp only [eq_iff_iff]

end Model

end Reformulation.PathC.Classifying
