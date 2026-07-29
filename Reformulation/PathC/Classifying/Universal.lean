-- EINGEFROREN (29. Juli 2026): dieser Zweig wird nicht fortgeschrieben.
-- Status, Zahlen und die Bedingungen fuer ein Auftauen: docs/build-targets.md, Abschnitt PathC.
-- Dieses Modul uebersetzt nicht und liegt in keinem Target. Siehe ebenda.
import Reformulation.PathC.Classifying.ClassifyingEquivalence

/-!
# Reformulation.PathC.Classifying.Universal

The universal property of the classifying topos — main theorem of Lücken 1+5.

## Main theorem

`classifyingTopos_universal_property T E`: for any elementary topos `E` (in the
right universe), models of T in E are in canonical bijection with geometric
morphisms `E → B[T]`.

## Methodological conclusion

This is the methodological conclusion of the full Path-C implementation:
the universality of B[T] as the classifying topos of T expresses the
abstract universality of Günther's reformulation. Every model of the
geometric theory T in a topos E corresponds canonically to a geometric
morphism from E to B[T].

**T2 form**: the `Equiv` is fully structured; the four proof obligations
are carried by `ClassifyingEquivalence`. The T3 upgrade closes all sorrys.

## Sequenz-Fortschritt: 5/6 complete.

Lücken 2 (ElementaryTopos), 3 (GeometricMorphism), 4 (GeometricTheory),
1+5 (ClassifyingTopos + Universal) complete. Remaining: Lücke 6.
-/

namespace Reformulation.PathC.Classifying

open CategoryTheory GeometricTheory

universe u v w

/-- **The universal property of the classifying topos.**

    For any elementary topos `E : Type (max (u+1) (v+1))` and geometric theory `T`,
    there is a canonical bijection between models of T in E and geometric morphisms
    `E → B[T]`.

    **T2 form**: four sorry-declared proof obligations from ClassifyingEquivalence.
    T3 upgrade provides all four proofs via Yoneda + sheafification. -/
noncomputable def classifyingTopos_universal_property
    (T : Theory.{u, v, w})
    (E : Type (max (u+1) (v+1))) [Category.{max u v} E] [ElementaryTopos E]
    [EssentiallySmall.{max u v} (SyntacticContext T)] :
    Model T E ≃ GeometricMorphism E (ClassifyingTopos T) where
  toFun   := Model.toGeometricMorphism T
  invFun  := Model.ofGeometricMorphism T
  left_inv  := Model.ofGeometricMorphism_toGeometricMorphism T
  right_inv := Model.toGeometricMorphism_ofGeometricMorphism T

end Reformulation.PathC.Classifying
