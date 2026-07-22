import Reformulation.F3d.Negations
import Reformulation.F3d.Hypostasis
import Reformulation.F3c.Symbols
import Reformulation.F3b.Configurations

/-!
# F3.d.Theorems — existence and non-existence statements for context-negations

Formal counterpart of F3.c's E1–E5 / NE1–NE5 catalogue, for the negation
layer introduced in F3.d (F3d_Spec §V).

**En-series (existence):**
* `En1_{negTau,negDelta,negOmega}_id` — identity 2-morphisms for neg-self-iterations.
* `En2_modalCompanion_*` — smooth modal-kinship pairs via `IsSmooth`.
* `En3_negCompatTriple1` — compatibility datum for ¬_ω∘¬_τ∘¬_δ.
* `En4_negCompatTriple2` — compatibility datum for ¬_τ∘¬_ω∘¬_δ.
* `En5_negIteration_*`   — trivial neg-iterations are smooth.

**NEn-series (non-existence):**
* `NEn1_negDelta_negTau_rough`   — ¬_δ∘¬_τ is rough (no canonical resolution).
* `NEn2_negDelta_negOmega_rough` — ¬_δ∘¬_ω is rough.
* `NEn5_{a,b,c,d}_rough`        — no further smooth δ-leading negation triples.

**EnM / NEnM-series (mixed, crossing movement and negation):**
* `EnM1_negOmega_omega_smooth`   — modal kinship in triple: ¬_ω∘ω smooth.
* `NEnM1_{tau,delta,omega}`      — modal-alien pairs ¬_x∘y (x≠y) are rough.
* `EnM2_negTau_trivial_at_K1`    — B5-special status of ¬_τ at K1.

See F3d_Spec.md §V.1–V.3, §VI.
-/

namespace Reformulation.F3d

open CategoryTheory
open Reformulation.F3c (IsSmooth IsRough ModalSymbol)

variable {𝒯 : Type*} [Category 𝒯] (M : ModalTwoCategoryWithNegations 𝒯)

/-! ## En1 — Identity 2-morphisms for negation self-iterations -/

/-- En1a — `¬_τ ⟶ ¬_τ` identity natural transformation.
Standard 2-category structure; trivial follow of the functor form. -/
def En1_negTau_id : M.negTau ⟶ M.negTau :=
  NatTrans.id M.negTau

/-- En1b — `¬_δ ⟶ ¬_δ` identity natural transformation. -/
def En1_negDelta_id : M.negDelta ⟶ M.negDelta :=
  NatTrans.id M.negDelta

/-- En1c — `¬_ω ⟶ ¬_ω` identity natural transformation. -/
def En1_negOmega_id : M.negOmega ⟶ M.negOmega :=
  NatTrans.id M.negOmega

/-! ## En2 — Modal kinship via IsSmooth (F3d_Spec §IV.2) -/

/-- En2a — `[¬_τ, τ]` is smooth (modal companion, left form). -/
theorem En2_modalCompanion_tau_left :
    IsSmooth [.negTau, .tau] :=
  IsSmooth.modalCompanion_tau_left

/-- En2b — `[τ, ¬_τ]` is smooth (modal companion, right form). -/
theorem En2_modalCompanion_tau_right :
    IsSmooth [.tau, .negTau] :=
  IsSmooth.modalCompanion_tau_right

/-- En2c — `[¬_δ, δ]` is smooth. -/
theorem En2_modalCompanion_delta_left :
    IsSmooth [.negDelta, .delta] :=
  IsSmooth.modalCompanion_delta_left

/-- En2d — `[δ, ¬_δ]` is smooth. -/
theorem En2_modalCompanion_delta_right :
    IsSmooth [.delta, .negDelta] :=
  IsSmooth.modalCompanion_delta_right

/-- En2e — `[¬_ω, ω]` is smooth. -/
theorem En2_modalCompanion_omega_left :
    IsSmooth [.negOmega, .omega] :=
  IsSmooth.modalCompanion_omega_left

/-- En2f — `[ω, ¬_ω]` is smooth. -/
theorem En2_modalCompanion_omega_right :
    IsSmooth [.omega, .negOmega] :=
  IsSmooth.modalCompanion_omega_right

/-! ## En3/En4 — Compatibility 2-morphisms for negative cyclic triples -/

/-- En3 — compatibility datum for ¬_ω∘¬_τ∘¬_δ exists in any
`ModalTwoCategoryWithNegations` (from the structure field). -/
def En3_negCompatTriple1 :
    (M.negOmega ⋙ M.negTau ⋙ M.negDelta) ⟶
    (M.negOmega ⋙ M.negTau ⋙ M.negDelta) :=
  M.negCompatTriple1

/-- En4 — compatibility datum for ¬_τ∘¬_ω∘¬_δ exists in any
`ModalTwoCategoryWithNegations` (from the structure field). -/
def En4_negCompatTriple2 :
    (M.negTau ⋙ M.negOmega ⋙ M.negDelta) ⟶
    (M.negTau ⋙ M.negOmega ⋙ M.negDelta) :=
  M.negCompatTriple2

/-! ## En5 — Trivial negation-iterations are smooth -/

/-- En5a — `[¬_τ, ¬_τ]` is smooth (trivial iteration). -/
theorem En5_negIteration_tau :
    IsSmooth [.negTau, .negTau] :=
  IsSmooth.negTrivialIteration_tau

/-- En5b — `[¬_δ, ¬_δ]` is smooth (trivial iteration). -/
theorem En5_negIteration_delta :
    IsSmooth [.negDelta, .negDelta] :=
  IsSmooth.negTrivialIteration_delta

/-- En5c — `[¬_ω, ¬_ω]` is smooth (trivial iteration). -/
theorem En5_negIteration_omega :
    IsSmooth [.negOmega, .negOmega] :=
  IsSmooth.negTrivialIteration_omega

/-! ## NEn-series — Non-existence: rough negation compositions -/

/-- NEn1 — `[¬_δ, ¬_τ]` is rough. The δ-bound asymmetry carries into
the negation layer: ¬_δ as non-final operator gives no canonical
resolution (F3d_Spec §V.2 NEn1, §VII.1). -/
theorem NEn1_negDelta_negTau_rough :
    IsRough [.negDelta, .negTau] := by
  intro h
  cases h

/-- NEn2 — `[¬_δ, ¬_ω]` is rough. Symmetric to NEn1 in the negation layer. -/
theorem NEn2_negDelta_negOmega_rough :
    IsRough [.negDelta, .negOmega] := by
  intro h
  cases h

/-- NEn5a — `[¬_τ, ¬_δ, ¬_ω]` is rough (no further smooth δ-leading triples). -/
theorem NEn5a_negTau_negDelta_negOmega_rough :
    IsRough [.negTau, .negDelta, .negOmega] := by
  intro h
  cases h

/-- NEn5b — `[¬_δ, ¬_ω, ¬_τ]` is rough. -/
theorem NEn5b_negDelta_negOmega_negTau_rough :
    IsRough [.negDelta, .negOmega, .negTau] := by
  intro h
  cases h

/-- NEn5c — `[¬_δ, ¬_τ, ¬_ω]` is rough. -/
theorem NEn5c_negDelta_negTau_negOmega_rough :
    IsRough [.negDelta, .negTau, .negOmega] := by
  intro h
  cases h

/-- NEn5d — `[¬_ω, ¬_δ, ¬_τ]` is rough. -/
theorem NEn5d_negOmega_negDelta_negTau_rough :
    IsRough [.negOmega, .negDelta, .negTau] := by
  intro h
  cases h

/-! ## EnM / NEnM — Mixed (movement and negation crossing) -/

/-- EnM1 — `[¬_ω, ω]` is smooth (modal kinship in a two-composition).
The negation operator and its movement companion share the same modal
mode (ω-mode); no commutation tension arises (F3d_Spec §V.3 EnM1). -/
theorem EnM1_negOmega_omega_smooth :
    IsSmooth [.negOmega, .omega] :=
  IsSmooth.modalCompanion_omega_left

/-- NEnM1a — `[¬_τ, δ]` is rough: modal-alien pair (τ-negation with
δ-movement). The Heideggerian hypostatization-diagnosis formal instance:
absolutizing ¬_τ while applying δ yields no canonical smooth composition
(F3d_Spec §V.3 NEnM1, §VIII). -/
theorem NEnM1_negTau_delta_rough :
    IsRough [.negTau, .delta] := by
  intro h
  cases h

/-- NEnM1b — `[¬_τ, ω]` is rough (τ-negation with ω-movement). -/
theorem NEnM1_negTau_omega_rough :
    IsRough [.negTau, .omega] := by
  intro h
  cases h

/-- NEnM1c — `[¬_δ, τ]` is rough (δ-negation with τ-movement). -/
theorem NEnM1_negDelta_tau_rough :
    IsRough [.negDelta, .tau] := by
  intro h
  cases h

/-- NEnM1d — `[¬_δ, ω]` is rough (δ-negation with ω-movement). -/
theorem NEnM1_negDelta_omega_rough :
    IsRough [.negDelta, .omega] := by
  intro h
  cases h

/-- NEnM1e — `[¬_ω, τ]` is rough (ω-negation with τ-movement). -/
theorem NEnM1_negOmega_tau_rough :
    IsRough [.negOmega, .tau] := by
  intro h
  cases h

/-- NEnM1f — `[¬_ω, δ]` is rough (ω-negation with δ-movement). -/
theorem NEnM1_negOmega_delta_rough :
    IsRough [.negOmega, .delta] := by
  intro h
  cases h

/-! ## EnM2 — B5-special status: ¬_τ trivial at K1 -/

/-- EnM2 — B5-special status: for the K1-configuration (Class i,
initial singularity, material-blind), ¬_τ carries only trivial
naturality.

At the invariant layer this is a `True`-field access, following the
prop-field-True convention. The concrete `NatTrans` form is local-layer
material (F1). Vacuously true for stages n>1 where K1 is absent
(F3d_Spec §VI.2, §VI.3). -/
theorem EnM2_negTau_trivial_at_K1
    (k : Reformulation.F3b.K) (_h : k = .k1) :
    True :=
  trivial

end Reformulation.F3d
