import Reformulation.F3b.Configurations
import Reformulation.F3d.Negations
import Mathlib.CategoryTheory.NatIso

/-!
# F3.e.ModalTwoCategoryWithPullbacks — modal 2-category with pullback functors

This module introduces `ModalTwoCategoryWithPullbacks`, the central structure
class of F3.e. It extends `ModalTwoCategoryWithNegations` (F3.d) with:

* `pullBackC` (ψ*): undertopos-change functor on the 𝒞-axis of the double
  fibration 𝒯 → 𝒞 × 𝒪 (fast-discrete base of topos components).
* `pullBackO` (φ*): schema-step functor on the 𝒪-axis (morphism-rich base
  of schemata).
* Twelve `F ≅ G` compatibility fields (natural isomorphisms): six for the
  movement operators (τ, δ, ω) and six for the negation operators (¬_τ, ¬_δ,
  ¬_ω), expressing that each modal operator commutes (up to 2-iso) with each
  pullback functor.
* B5-anchoring via F3.b's `K` enumeration: `initialConfig` constrained to
  `.k1` (Class i, initial singularity, material-blind).

The compatibility data are the constructive input from which
`BeckChevalleyConstruction.beckChevalleyFromData` constructs the 2-categorical
Beck-Chevalley natural isomorphism, per the Cluster-II-argumentation (T9 II).

Note: `NatIso` is a namespace in Mathlib, not a type; natural isomorphisms
between functors are written `F ≅ G` (i.e. `CategoryTheory.Iso F G` in the
functor category with `open CategoryTheory`).

Architecture references: F3e_Spec §III, F3e_Implementation_Prompt §IV.2.
Naming: ASCII `pullBackC` / `pullBackO` (𝒞/𝒪 in architectural notation).
-/

namespace Reformulation.F3e

open CategoryTheory

/-- Modal 2-category with pullback functors and modal pullback-compatibility data.

Extends `ModalTwoCategoryWithNegations 𝒯` (F3.d) — which itself carries
τ, δ, ω, ¬_τ, ¬_δ, ¬_ω, the compatibility triples, and Beck-Chevalley
(prop-field) — by sixteen new fields:

**Pull-back functors on 𝒯 (double fibration 𝒯 → 𝒞 × 𝒪):**
- `pullBackC` (ψ*): undertopos-change functor (𝒞-axis).
- `pullBackO` (φ*): schema-step functor (𝒪-axis).

**Pull-back compatibility of movement operators (τ, δ, ω):**
Six `F ≅ G` fields, one for each of (τ, δ, ω) × (ψ*, φ*), asserting
commutativity up to 2-iso. This is the 2-categorical depth of the
Cluster-II-argumentation (T9 II / Cluster-II Rev4).

**Pull-back compatibility of negation operators (¬_τ, ¬_δ, ¬_ω):**
Six further `F ≅ G` fields for the negation layer (K2.3-decision).

**B5-anchoring:**
- `initialConfig : Reformulation.F3b.K` — the initial configuration.
- `initialConfig_isK1 : initialConfig = .k1` — K1-constraint.
  Klasse-B-Anpassung: uses `K` (enumeration type) rather than `Configuration`
  (triple structure), consistent with F3.d's `EnM2_negTau_trivial_at_K1`.
-/
structure ModalTwoCategoryWithPullbacks (𝒯 : Type*) [Category 𝒯]
    extends Reformulation.F3d.ModalTwoCategoryWithNegations 𝒯 where
  -- ——— Pull-back functors on 𝒯 ———
  /-- ψ* — undertopos-change functor (𝒞-axis of the double fibration). -/
  pullBackC : 𝒯 ⥤ 𝒯
  /-- φ* — schema-step functor (𝒪-axis of the double fibration). -/
  pullBackO : 𝒯 ⥤ 𝒯
  -- ——— Pull-back compatibility of movement operators ———
  /-- τ∘φ* ≅ φ*∘τ: τ commutes with φ* up to 2-iso (Cluster-II, T9 II step 2). -/
  modalCompatTauO   : tau ⋙ pullBackO ≅ pullBackO ⋙ tau
  /-- δ∘φ* ≅ φ*∘δ: δ commutes with φ* up to 2-iso. -/
  modalCompatDeltaO : delta ⋙ pullBackO ≅ pullBackO ⋙ delta
  /-- ω∘φ* ≅ φ*∘ω: ω commutes with φ* up to 2-iso.
  Note: carries the initializing sub-form from T5 VI; concrete form is F1. -/
  modalCompatOmegaO : omega ⋙ pullBackO ≅ pullBackO ⋙ omega
  /-- τ∘ψ* ≅ ψ*∘τ: τ commutes with ψ* up to 2-iso. -/
  modalCompatTauC   : tau ⋙ pullBackC ≅ pullBackC ⋙ tau
  /-- δ∘ψ* ≅ ψ*∘δ: δ commutes with ψ* up to 2-iso. -/
  modalCompatDeltaC : delta ⋙ pullBackC ≅ pullBackC ⋙ delta
  /-- ω∘ψ* ≅ ψ*∘ω: ω commutes with ψ* up to 2-iso. -/
  modalCompatOmegaC : omega ⋙ pullBackC ≅ pullBackC ⋙ omega
  -- ——— Pull-back compatibility of negation operators ———
  /-- ¬_τ∘φ* ≅ φ*∘¬_τ: ¬_τ commutes with φ* up to 2-iso. -/
  negCompatTauO   : negTau ⋙ pullBackO ≅ pullBackO ⋙ negTau
  /-- ¬_δ∘φ* ≅ φ*∘¬_δ: ¬_δ commutes with φ* up to 2-iso. -/
  negCompatDeltaO : negDelta ⋙ pullBackO ≅ pullBackO ⋙ negDelta
  /-- ¬_ω∘φ* ≅ φ*∘¬_ω: ¬_ω commutes with φ* up to 2-iso. -/
  negCompatOmegaO : negOmega ⋙ pullBackO ≅ pullBackO ⋙ negOmega
  /-- ¬_τ∘ψ* ≅ ψ*∘¬_τ: ¬_τ commutes with ψ* up to 2-iso. -/
  negCompatTauC   : negTau ⋙ pullBackC ≅ pullBackC ⋙ negTau
  /-- ¬_δ∘ψ* ≅ ψ*∘¬_δ: ¬_δ commutes with ψ* up to 2-iso. -/
  negCompatDeltaC : negDelta ⋙ pullBackC ≅ pullBackC ⋙ negDelta
  /-- ¬_ω∘ψ* ≅ ψ*∘¬_ω: ¬_ω commutes with ψ* up to 2-iso. -/
  negCompatOmegaC : negOmega ⋙ pullBackC ≅ pullBackC ⋙ negOmega
  -- ——— B5-anchoring ———
  /-- The initial configuration as a value of `Reformulation.F3b.K`. -/
  initialConfig : Reformulation.F3b.K
  /-- B5-anchoring: the initial configuration is K1 = (trivial, constant, absent),
  the material-free initial singularity (F3e_Spec §III.1 third observation). -/
  initialConfig_isK1 : initialConfig = .k1

end Reformulation.F3e
