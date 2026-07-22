/-
Copyright Reformulierung-Projekt 2026.
Released under PKL-internal license.
-/
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Functor.KanExtension.Basic
import Reformulation.PathC.ElementaryTopos
import Reformulation.PathC.Classifying.SyntacticSite

/-!
# Yoneda-Ulift-Adjunction for ClassifyingTopos

Wrapper for `Presheaf.uliftYonedaAdjunction` with universe consolidation
for the ClassifyingTopos construction.

## Klasse-B/β Adjustment (Spec → Implementation)

The spec declared `F : (SyntacticContext T)ᵒᵖ ⥤ E`. The correct covariant domain
for `Presheaf.uliftYoneda (C := SyntacticContext T)` requires `F : SyntacticContext T ⥤ E`.

Setting `C = SyntacticContext T` gives
`uliftYoneda : SyntacticContext T ⥤ (SyntacticContext T)ᵒᵖ ⥤ Type (max u v)`,
and `leftKanExtension F` lands in `((SyntacticContext T)ᵒᵖ ⥤ Type (max u v)) ⥤ E`
(the desired presheaf-extension domain).

The mismatch with `Model.toFunctor M : (SyntacticContext T)ᵒᵖ ⥤ E` (C23-B-β,
Kovarianz/Kontravarianz-Mismatch) remains a Klasse-D sideways item for C22.

## Substanz

`syntacticLeftKanExtension T F` — left Kan extension of `F : SyntacticContext T ⥤ E`
along `uliftYoneda.{max u v}`, giving `((SyntacticContext T)ᵒᵖ ⥤ Type (max u v)) ⥤ E`.

`syntacticUliftYonedaAdjunction T F` — adjunction
`syntacticLeftKanExtension T F ⊣ Presheaf.restrictedULiftYoneda.{max u v} F`.
Requires `[(Presheaf.uliftYoneda.{max u v}).HasPointwiseLeftKanExtension F]`
(available when E has `HasColimitsOfSize.{max u v, max u v}`, e.g.
`E = ClassifyingTopos T`).

## Anschluss

- C23-D-4: `toPresheafFunctor` — Kan-extension API available after resolution
  of the C23-B-β covariance question (requires covariant model functor)
- C23-B-1: covariance/contravariance mismatch documented here
-/

namespace Reformulation.MathlibExtensions.Sites

open CategoryTheory Limits
open Reformulation.PathC.GeometricTheory
open Reformulation.PathC.Classifying

universe u v w

variable (T : Theory.{u, v, w}) {E : Type (max (u+1) (v+1))} [Category.{max u v} E]

/-- Left Kan extension of F : SyntacticContext T ⥤ E along uliftYoneda.{max u v}.

    For a covariant functor F from the syntactic site to a test topos E, constructs
    the pointwise left Kan extension along
    `uliftYoneda : SyntacticContext T ⥤ (SyntacticContext T)ᵒᵖ ⥤ Type (max u v)`.

    Output type: `((SyntacticContext T)ᵒᵖ ⥤ Type (max u v)) ⥤ E`.

    **Klasse-B/β**: spec had `F : (SyntacticContext T)ᵒᵖ ⥤ E`; correct domain
    for the presheaf extension requires `F : SyntacticContext T ⥤ E` (covariant). -/
noncomputable def syntacticLeftKanExtension
    (F : SyntacticContext T ⥤ E)
    [(uliftYoneda.{max u v}).HasPointwiseLeftKanExtension F] :
    ((SyntacticContext T)ᵒᵖ ⥤ Type (max u v)) ⥤ E :=
  (uliftYoneda.{max u v}).leftKanExtension F

/-- Ulift-Yoneda adjunction for ClassifyingTopos-context Kan extensions.

    Wrapper for `Presheaf.uliftYonedaAdjunction` with explicit universe annotation.
    The `HasPointwiseLeftKanExtension` hypothesis is satisfied when E has
    `HasColimitsOfSize.{max u v, max u v}`, e.g. when E is a Grothendieck topos
    such as `ClassifyingTopos T = Sheaf (geometricTopology T) (Type (max u v))`. -/
noncomputable def syntacticUliftYonedaAdjunction
    (F : SyntacticContext T ⥤ E)
    [(uliftYoneda.{max u v}).HasPointwiseLeftKanExtension F] :
    syntacticLeftKanExtension T F ⊣ Presheaf.restrictedULiftYoneda.{max u v} F :=
  Presheaf.uliftYonedaAdjunction
    ((uliftYoneda.{max u v}).leftKanExtension F)
    ((uliftYoneda.{max u v}).leftKanExtensionUnit F)

end Reformulation.MathlibExtensions.Sites
