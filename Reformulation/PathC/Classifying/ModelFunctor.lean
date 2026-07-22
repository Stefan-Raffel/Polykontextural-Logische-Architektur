import Reformulation.PathC.Classifying.Model
import Reformulation.PathC.Classifying.ClassifyingTopos
import Reformulation.PathC.GeometricMorphism
import Reformulation.PathC.GeometricMorphismLaws
-- C22: HasColimitsOfShape (Discrete PEmpty.{1}) needs Category (Discrete ...) elaborated first;
-- checkBinderAnnotations is too conservative for this case.
set_option checkBinderAnnotations false

/-!
# Reformulation.PathC.Classifying.ModelFunctor

The model functor: pullback of models along geometric morphisms.

## Klasse-B finding (B-1/β)

`GeometricMorphism (E F : Type u) [Category.{v} E] [Category.{v} F]` requires
both endpoints to live in the SAME universe `u` with the SAME morphism universe `v`.
Using `{E : Type*}` failed with "stuck at solving universe constraint".
Fixed by adding explicit universe parameters `{E F G : Type u_}` throughout.

## Klasse-B finding (B-2/β)

`Model.pullback` uses a top-level `sorry` rather than a `where`-block sorry. For
`pullback_comp` (which calls `Model.pullback` twice nested), the two sorry instances
produce incompatible universe metavariables during elaboration of the equality type.
`pullback_comp` is therefore stated in weaker interp-only form to avoid the issue.
-/

namespace Reformulation.PathC.Classifying

open CategoryTheory GeometricTheory Limits

universe u v w u_

variable {T : Theory.{u, v, w}}

/-- Pullback a model along a geometric morphism.
    T2: sorry — requires f.inverse preserves the subobject order (C22 β.2). -/
noncomputable def Model.pullback
    {E F : Type u_} [Category.{v} E] [Category.{v} F]
    [ElementaryTopos E] [ElementaryTopos F]
    [HasColimitsOfShape (Discrete PEmpty.{1}) E]
    [HasColimitsOfShape (Discrete PEmpty.{1}) F]
    [HasImages E] [HasImages F]
    [LocallySmall.{max u (max v w)} E] [LocallySmall.{max u (max v w)} F]
    [HasWidePullbacks.{max u (max v w)} E] [HasWidePullbacks.{max u (max v w)} F]
    [HasCoproducts.{max u (max v w)} E] [HasCoproducts.{max u (max v w)} F]
    [WellPowered.{max u (max v w)} E] [WellPowered.{max u (max v w)} F]
    [InitialMonoClass E] [InitialMonoClass F]
    (f : GeometricMorphism E F) (M : Model T F) : Model T E := sorry

/-- Pulling back along the identity geometric morphism gives the same model. -/
theorem Model.pullback_id
    {E : Type u_} [Category.{v} E] [ElementaryTopos E]
    [HasColimitsOfShape (Discrete PEmpty.{1}) E]
    [HasImages E]
    [LocallySmall.{max u (max v w)} E]
    [HasWidePullbacks.{max u (max v w)} E]
    [HasCoproducts.{max u (max v w)} E]
    [WellPowered.{max u (max v w)} E]
    [InitialMonoClass E]
    (M : Model T E) :
    Model.pullback (GeometricMorphism.id E) M = M := by
  -- T2: sorry — follows once Model.pullback is implemented
  sorry

/-- The interp-component of pulling back along a composition equals composing pullbacks.
    C22 note: stated as interp equality to avoid double-sorry universe metavariable clash
    (Klasse-B B-2/β). Full model equality follows from Model.ext. -/
theorem Model.pullback_comp_interp
    {E F G : Type u_} [Category.{v} E] [Category.{v} F] [Category.{v} G]
    [ElementaryTopos E] [ElementaryTopos F] [ElementaryTopos G]
    [HasColimitsOfShape (Discrete PEmpty.{1}) E]
    [HasColimitsOfShape (Discrete PEmpty.{1}) F]
    [HasColimitsOfShape (Discrete PEmpty.{1}) G]
    [HasImages E] [HasImages F] [HasImages G]
    [LocallySmall.{max u (max v w)} E] [LocallySmall.{max u (max v w)} F]
    [LocallySmall.{max u (max v w)} G]
    [HasWidePullbacks.{max u (max v w)} E] [HasWidePullbacks.{max u (max v w)} F]
    [HasWidePullbacks.{max u (max v w)} G]
    [HasCoproducts.{max u (max v w)} E] [HasCoproducts.{max u (max v w)} F]
    [HasCoproducts.{max u (max v w)} G]
    [WellPowered.{max u (max v w)} E] [WellPowered.{max u (max v w)} F]
    [WellPowered.{max u (max v w)} G]
    [InitialMonoClass E] [InitialMonoClass F] [InitialMonoClass G]
    (f : GeometricMorphism E F) (g : GeometricMorphism F G)
    (M : Model T G) :
    (Model.pullback (f.comp g) M).interp =
    (fun s => f.inverse.obj (g.inverse.obj (M.interp s))) := by
  -- T2: sorry — Model.pullback is a sorry def; interp equality holds once implemented
  sorry

end Reformulation.PathC.Classifying
