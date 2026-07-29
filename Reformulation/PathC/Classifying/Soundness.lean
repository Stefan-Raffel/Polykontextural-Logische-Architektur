-- EINGEFROREN (29. Juli 2026): dieser Zweig wird nicht fortgeschrieben.
-- Status, Zahlen und die Bedingungen fuer ein Auftauen: docs/build-targets.md, Abschnitt PathC.
/-
Copyright Reformulierung-Projekt 2026.
Released under PKL-internal license.
-/
import Reformulation.PathC.Classifying.SequentCalculus
import Reformulation.PathC.Classifying.TermSemantics
import Reformulation.PathC.Classifying.Model
import Mathlib.CategoryTheory.Subobject.Lattice
import Reformulation.MathlibExtensions.Topos.Subobject.PullbackLemmas

/-!
# Reformulation.PathC.Classifying.Soundness

Soundness of the geometric sequent calculus with respect to interpretation
in an elementary topos: derivable sequents become subobject inequalities.

## D-4 API change

`interpretFormula` and `contextSubstMorphism` now take `ModelInterp T E` (or `Model T E`
via coercion from `extends ModelInterp`). Use `M.toModelInterp` explicitly where needed.

## What this module carries

- `interpretFormula_subst` — interpretation commutes with substitution.
  **D-4 T3 form**: atom case resolved via tupleMorphism_subst + Subobject.pullback_comp.
  **Klasse-D forward (NOT D-4 scope)**: exists_ case (Beck-Chevalley); Stufe-3-Substanz.

- `Derivable.soundness` — main soundness theorem. All cases except substStable/exI/exE.
-/

namespace Reformulation.PathC.Classifying

open CategoryTheory GeometricTheory Limits Reformulation.MathlibExtensions.Topos
open Subobject

universe u v w

variable {T : Theory.{u, v, w}}
variable {E : Type*} [Category E] [ElementaryTopos E]
variable [HasColimitsOfShape (Discrete PEmpty.{1}) E]
variable [HasImages E] [LocallySmall.{max u (max v w)} E]
variable [WellPowered.{max u (max v w)} E] [InitialMonoClass E]
variable [HasWidePullbacks.{max u (max v w)} E]
variable [HasCoproducts.{max u (max v w)} E]
variable [Regular E] [PullbackISup E]

attribute [local instance] has_smallest_coproducts_of_hasCoproducts

variable (M : Model T E)

/-- Interpretation commutes with substitution.

    **D-4 T3 form**: atom resolved via tupleMorphism_subst + Subobject.pullback_comp.
    **Klasse-D forward (NOT D-4 scope)**: exists_ (Beck-Chevalley; Stufe-3-Substanz). -/
theorem interpretFormula_subst
    {Γ Δ : List T.signature.sort}
    (σ : TermSubst T.signature)
    (φ : GeometricFormula T.signature Γ) :
    interpretFormula M.toModelInterp (φ.subst (Δ := Δ) σ) =
    (Subobject.pullback (contextSubstMorphism M.toModelInterp σ)).obj
      (interpretFormula M.toModelInterp φ) := by
  revert σ Δ
  induction φ with
  | top =>
      intro Δ σ
      simp only [GeometricFormula.subst_top, interpretFormula]
      exact (Subobject.pullback_top _).symm
  | bot =>
      intro Δ σ
      simp only [GeometricFormula.subst_bot, interpretFormula]
      exact (Subobject.pullback_bot _).symm
  | atom r as =>
      intro Δ σ
      simp only [GeometricFormula.subst_atom, interpretFormula]
      -- Use ← pullback_comp to fold: (pb f).obj ((pb g).obj S) = (pb (f ≫ g)).obj S
      rw [← Subobject.pullback_comp]
      exact congrArg (fun f => (Subobject.pullback f).obj (M.relInterp r))
                     (tupleMorphism_subst M.toModelInterp σ as).symm
  | conj φ ψ ih_φ ih_ψ =>
      intro Δ σ
      simp only [GeometricFormula.subst_conj, interpretFormula]
      rw [ih_φ σ, ih_ψ σ, Subobject.inf_pullback]
  | disj f ih =>
      intro Δ σ
      simp only [GeometricFormula.disj_subst, interpretFormula]
      rw [pullback_iSup]
      congr 1; funext i; exact ih i σ
  | exists_ S φ ih =>
      rename_i Γ'
      intro Δ σ
      simp only [GeometricFormula.subst_exists_, interpretFormula]
      -- Beck-Chevalley for exists_: F30 S-1.
      -- After simp: LHS = imageSubobject((interp(φ.subst(σ.lift S))).arrow ≫ proj_Δ)
      --             RHS = (pullback(ctxSubst σ)).obj (imageSubobject((interp φ).arrow ≫ proj_Γ))
      --
      -- Notation (fold before step_a so rw [step_a] matches):
      set f_ := contextSubstMorphism M.toModelInterp (σ.lift S)
      set proj_Δ := projMorphism M.toModelInterp S Δ
      set k_ := contextSubstMorphism M.toModelInterp σ
      set P := interpretFormula M.toModelInterp φ
      -- Step 1: replace interp(φ.subst(σ.lift S)) with (pb f_).obj P in the imageSubobject.
      -- Cannot use rw [ih (σ.lift S) (S :: Δ)] directly (HasImage motive issue).
      -- Instead: prove equality of imageSubobjects via imageSubobject_le.
      have step_a : imageSubobject ((interpretFormula M.toModelInterp (φ.subst (σ.lift S))).arrow ≫ proj_Δ) =
                    imageSubobject (((Subobject.pullback f_).obj P).arrow ≫ proj_Δ) := by
        apply le_antisymm
        · -- imageSubobject(A.arrow ≫ proj_Δ) ≤ imageSubobject(B.arrow ≫ proj_Δ)
          -- Lean resolves h = image.ι B_morph; w must reach the image object via factorThruImageSubobject
          exact imageSubobject_le _
              (Subobject.ofLE (interpretFormula M.toModelInterp (φ.subst (σ.lift S)))
                              ((Subobject.pullback f_).obj P)
                              (le_of_eq (ih (Δ := S :: Δ) (σ.lift S))) ≫
               factorThruImageSubobject (((Subobject.pullback f_).obj P).arrow ≫ proj_Δ))
              (by rw [Category.assoc, imageSubobject_arrow_comp, ← Category.assoc,
                      Subobject.ofLE_arrow])
        · -- imageSubobject(B.arrow ≫ proj_Δ) ≤ imageSubobject(A.arrow ≫ proj_Δ)
          exact imageSubobject_le _
              (Subobject.ofLE ((Subobject.pullback f_).obj P)
                              (interpretFormula M.toModelInterp (φ.subst (σ.lift S)))
                              (ge_of_eq (ih (Δ := S :: Δ) (σ.lift S))) ≫
               factorThruImageSubobject ((interpretFormula M.toModelInterp (φ.subst (σ.lift S))).arrow ≫ proj_Δ))
              (by rw [Category.assoc, imageSubobject_arrow_comp, ← Category.assoc,
                      Subobject.ofLE_arrow])
      rw [step_a]
      -- Step 2: Apply pullback_imageSubobject to RHS
      rw [pullback_imageSubobject]
      -- Goal: imageSubobject(((pullback f_).obj P).arrow ≫ proj_Δ) =
      --       imageSubobject(pullback.fst k_ (image.ι(P.arrow ≫ proj_Γ)))
      -- where f_ = ctxSubst(σ.lift S), P = interp φ, k_ = ctxSubst σ, proj_Γ/Δ projections
      -- Strategy: le_antisymm via pullback.lift and image.isoStrongEpiMono
      set proj_Γ := projMorphism M.toModelInterp S Γ'
      set ι := image.ι (P.arrow ≫ proj_Γ) with hι_def
      -- e_pb: the mediating morphism to Limits.pullback k_ ι
      -- satisfies: e_pb ≫ pullback.fst k_ ι = ((pullback f_).obj P).arrow ≫ proj_Δ
      set e_pb := Limits.pullback.lift (f := k_) (g := ι)
        (((Subobject.pullback f_).obj P).arrow ≫ proj_Δ)
        (Subobject.pullbackπ f_ P ≫ factorThruImage (P.arrow ≫ proj_Γ))
        (by
          -- commutativity: (arrow ≫ proj_Δ) ≫ k_ = (pullbackπ ≫ factorThruImage) ≫ ι
          rw [Category.assoc, Category.assoc, hι_def, image.fac]
          rw [← Category.assoc (Subobject.pullbackπ f_ P)]
          rw [(Subobject.isPullback f_ P).w]
          rw [Category.assoc]
          congr 1
          exact (ctxSubstMorph_lift_proj_comm M.toModelInterp σ).symm) with he_pb_def
      have e_pb_fst : e_pb ≫ Limits.pullback.fst k_ ι =
          ((Subobject.pullback f_).obj P).arrow ≫ proj_Δ :=
        Limits.pullback.lift_fst _ _ _
      -- Top-square IsPullback via of_bot
      have isPB_top : IsPullback
          (Subobject.pullbackπ f_ P)
          e_pb
          (factorThruImage (P.arrow ≫ proj_Γ))
          (Limits.pullback.snd k_ ι) := by
        sorry  -- β.2: IsPullback.of_bot with image.fac bridge
      haveI hse : StrongEpi e_pb := by
        haveI : IsRegularEpi (factorThruImage (P.arrow ≫ proj_Γ)) := by
          haveI : HasStrongEpiImages E := inferInstance
          haveI : StrongEpi (factorThruImage (P.arrow ≫ proj_Γ)) := inferInstance
          sorry  -- β.2: StrongEpi → IsRegularEpi requires RegularCategory
        haveI : IsRegularEpi e_pb :=
          Regular.regularEpiIsStableUnderBaseChange.of_isPullback isPB_top
            (by dsimp [MorphismProperty.regularEpi]; infer_instance)
        haveI : EffectiveEpi e_pb := inferInstance
        infer_instance
      haveI : Mono (Limits.pullback.fst k_ ι) := inferInstance
      set iso_img := @image.isoStrongEpiMono _ _ _ _ _
          (((Subobject.pullback f_).obj P).arrow ≫ proj_Δ)
          _ e_pb (Limits.pullback.fst k_ ι) e_pb_fst _ _
      apply le_antisymm
      · -- imageSubobject(B.arrow ≫ proj_Δ) ≤ imageSubobject(pullback.fst k_ ι)
        rw [← e_pb_fst]
        exact imageSubobject_comp_le e_pb _
      · -- imageSubobject(pullback.fst k_ ι) ≤ imageSubobject(B.arrow ≫ proj_Δ)
        sorry  -- β.2: iso_img.hom/inv direction depends on Mathlib version

/-- Soundness of the geometric sequent calculus.

    **T3 form (D-4)**: axm, cut, topR, botL, conjI, conjE_l, conjE_r, disjI, disjE, axiomT.
    **Klasse-D forward**: substStable, exI, exE (depend on interpretFormula_subst.exists_). -/
theorem Derivable.soundness
    {Γ : List T.signature.sort} {φ ψ : GeometricFormula T.signature Γ}
    (h : Derivable T φ ψ) :
    interpretFormula M.toModelInterp φ ≤ interpretFormula M.toModelInterp ψ := by
  induction h with
  | axm =>
      exact le_refl _
  | cut _ _ ih₁ ih₂ =>
      exact le_trans ih₁ ih₂
  | topR =>
      show interpretFormula M.toModelInterp _ ≤ interpretFormula M.toModelInterp .top
      simp only [interpretFormula]
      exact le_top
  | botL =>
      exact bot_le
  | conjI _ _ ih₁ ih₂ =>
      show interpretFormula M.toModelInterp _ ≤ interpretFormula M.toModelInterp (.conj _ _)
      simp only [interpretFormula]
      exact le_inf ih₁ ih₂
  | conjE_l =>
      show interpretFormula M.toModelInterp (.conj _ _) ≤ interpretFormula M.toModelInterp _
      simp only [interpretFormula]
      exact inf_le_left
  | conjE_r =>
      show interpretFormula M.toModelInterp (.conj _ _) ≤ interpretFormula M.toModelInterp _
      simp only [interpretFormula]
      exact inf_le_right
  | disjI i _ ih =>
      simp only [interpretFormula] at *
      exact ih.trans (le_iSup (α := Subobject (contextObj M.sortInterp _)) _ i)
  | disjE _ ih =>
      exact iSup_le ih
  | substStable σ _ ih =>
      -- Stufe-2-H-1: substStable resolved via interpretFormula_subst + pullback monotonicity.
      -- Note: interpretFormula_subst uses sorry for .exists_ (Stufe-3-Substanz, Beck-Chevalley);
      -- substStable inherits that β.2 assumption transitively.
      rw [interpretFormula_subst, interpretFormula_subst]
      exact Functor.monotone _ ih
  | exI t _ ih =>
      -- S-1 (F29): exI soundness via ctxSubst_idCons_proj_eq_id (H-1).
      -- `show` coerces goal via definitional equality (interp(.exists_ s φ) = imageSubobject(...))
      -- without simp-unfolding projMorphism to Pi.lift (which would create HasImage deps).
      rw [interpretFormula_subst] at ih
      show interpretFormula M.toModelInterp _ ≤
           imageSubobject ((interpretFormula M.toModelInterp _).arrow ≫
             projMorphism M.toModelInterp _ _)
      apply ih.trans
      apply Subobject.le_of_comm
            (Subobject.pullbackπ (contextSubstMorphism M.toModelInterp (TermSubst.idCons t))
                                 (interpretFormula M.toModelInterp _) ≫
             factorThruImageSubobject _)
      rw [Category.assoc, imageSubobject_arrow_comp, ← Category.assoc,
          (Subobject.isPullback
            (contextSubstMorphism M.toModelInterp (TermSubst.idCons t))
            (interpretFormula M.toModelInterp _)).w,
          Category.assoc, ctxSubst_idCons_proj_eq_id M.toModelInterp t, Category.comp_id]
  | exE _ _ ih₁ ih₂ =>
      -- S-2 (F29): exE soundness via ctxSubst_shift_eq_proj (H-2) + imageSubobject_le.
      -- Lean 4 induction: ALL constructor args before ALL IH args → exE hd1 hd2 ih1 ih2.
      -- `have ih₁'` coerces ih₁ via definitional equality to imageSubobject form;
      -- term-mode assignment fills wildcards from ih₁'s type (avoids stuck haveI metavars).
      -- `imageSubobject_le` directly: avoids rw inside imageSubobject (HasImage motive issue).
      have ih₁' : interpretFormula M.toModelInterp _ ≤
          imageSubobject ((interpretFormula M.toModelInterp _).arrow ≫
            projMorphism M.toModelInterp _ _) := ih₁
      simp only [interpretFormula_subst, ctxSubst_shift_eq_proj] at ih₂
      apply ih₁'.trans
      -- imageSubobject_le with witness ofLE(ih₂) ≫ pullbackπ:
      -- (ofLE ih₂ ≫ pullbackπ) ≫ (interp χ).arrow
      --   = ofLE ih₂ ≫ pullbackπ ≫ (interp χ).arrow   [assoc]
      --   = ofLE ih₂ ≫ (pullback proj (interp χ)).arrow ≫ proj  [isPullback.w]
      --   = (interp φ).arrow ≫ proj   [← assoc + ofLE_arrow]
      exact imageSubobject_le _
              (Subobject.ofLE _ _ ih₂ ≫
               Subobject.pullbackπ (projMorphism M.toModelInterp _ _)
                                   (interpretFormula M.toModelInterp _))
              (by erw [Category.assoc,
                       (Subobject.isPullback (projMorphism M.toModelInterp _ _)
                                            (interpretFormula M.toModelInterp _)).w,
                       ← Category.assoc, Subobject.ofLE_arrow])
  | axiomT seq hmem =>
      exact M.satisfies seq hmem

end Reformulation.PathC.Classifying
