import Reformulation.F3c.TwoCategory
import Mathlib.CategoryTheory.NatTrans

/-!
# F3.d.Negations — the modal 2-category extended with context-negations

This module introduces:

* `ModalTwoCategoryWithNegations`: extends `ModalTwoCategory` by three
  negation endo-functors `negTau`, `negDelta`, `negOmega` (the formal
  counterparts of ¬_τ, ¬_δ, ¬_ω in PKL terminology) together with:
  - `negCompatTriple1/2`: compatibility 2-morphisms for the two enforced
    negative cyclic triples ¬_ω∘¬_τ∘¬_δ and ¬_τ∘¬_ω∘¬_δ, analogous to
    `compatTriple1/2` in `ModalTwoCategory`;
  - `modalKinshipTau/Delta/Omega`: prop-field placeholders for the modal
    kinship between each negation operator and its modal companion;
  - `negTau_trivial_at_K1`: prop-field placeholder for the B5-special
    status of `negTau` at Class-i configurations.
* `ModalTwoCategoryWithNegations.symbolFull`: full dispatch from all six
  `ModalSymbol` constructors to the corresponding endo-functor.
* `ModalTwoCategoryWithNegations.interpretFull`: semantic interpretation
  of any six-symbol list composition as a functor on 𝒯.

The three negation operators are *aspects* of the modal triad, not
independent architecture (K2 §III.4 Konsequenz-Klassifikation).
`ModalTwoCategoryWithNegations` extends rather than parallels
`ModalTwoCategory` to reflect this dependency.

The concrete form of `modalKinship*` and `negTau_trivial_at_K1` is
deployment-specific (local layer, F1 material). Both are held as
`prop_field`-True placeholders, following the F3.a/F3.c convention
(F3d_Spec §III.1, §III.2).

See F3d_Spec.md §I.2, §III, §IV.1–IV.3.
-/

namespace Reformulation.F3d

open CategoryTheory

/-- The modal 2-category extended with the three context-negation
endo-functors and their compatibility data.

Extends `ModalTwoCategory 𝒯` (which itself carries τ, δ, ω,
`compatTriple1/2`, and `beckChevalley`) by:

* `negTau`   — temporal context-negation functor (¬_τ; zeitliche Kontextnegation).
* `negDelta` — thinking context-negation functor (¬_δ; denkende Kontextnegation).
* `negOmega` — willing context-negation functor  (¬_ω; wollende Kontextnegation).
* `negCompatTriple1` — self-naturality on ¬_ω∘¬_τ∘¬_δ (negative cyclic triple 1).
* `negCompatTriple2` — self-naturality on ¬_τ∘¬_ω∘¬_δ (negative cyclic triple 2).
* `modalKinshipTau/Delta/Omega` — `True` placeholder for modal kinship
  between negX and x for x ∈ {τ, δ, ω}; concrete form is F1-material.
* `negTau_trivial_at_K1` — `True` placeholder for B5-special status of
  ¬_τ at Class-i (K1); concrete form is F1-material (F3d_Spec §VI).
-/
structure ModalTwoCategoryWithNegations (𝒯 : Type*) [Category 𝒯]
    extends Reformulation.F3c.ModalTwoCategory 𝒯 where
  /-- Temporal context-negation functor (¬_τ — zeitliche Kontextnegation).
  Stage-relative; special status at Class i (F3d_Spec §II.4). -/
  negTau   : 𝒯 ⥤ 𝒯
  /-- Thinking context-negation functor (¬_δ — denkende Kontextnegation).
  Intra-contextural; proximal to classical negation (F3d_Spec §II.4). -/
  negDelta : 𝒯 ⥤ 𝒯
  /-- Willing context-negation functor (¬_ω — wollende Kontextnegation).
  Trans-contextural; primary context-negation in PKL sense (F3d_Spec §II.4). -/
  negOmega : 𝒯 ⥤ 𝒯
  /-- Compatibility 2-morphism for the negative cyclic triple ¬_ω∘¬_τ∘¬_δ.
  Analog of `compatTriple1` in `ModalTwoCategory`; carries the δ-bound
  entanglement datum in the negation layer (F3d_Spec §IV.1, En3). -/
  negCompatTriple1 :
    (negOmega ⋙ negTau ⋙ negDelta) ⟶ (negOmega ⋙ negTau ⋙ negDelta)
  /-- Compatibility 2-morphism for the negative cyclic triple ¬_τ∘¬_ω∘¬_δ.
  Analog of `compatTriple2` in `ModalTwoCategory` (F3d_Spec §IV.1, En4). -/
  negCompatTriple2 :
    (negTau ⋙ negOmega ⋙ negDelta) ⟶ (negTau ⋙ negOmega ⋙ negDelta)
  /-- Modal kinship between ¬_τ and τ — `True` placeholder.
  Syntactic form carried by `IsSmooth.modalCompanion_tau_{left,right}`;
  semantic content (concrete NatTrans) is local-layer material (F1). -/
  modalKinshipTau   : True
  /-- Modal kinship between ¬_δ and δ — `True` placeholder. -/
  modalKinshipDelta : True
  /-- Modal kinship between ¬_ω and ω — `True` placeholder. -/
  modalKinshipOmega : True
  /-- B5-special status: ¬_τ at Class-i configuration K1 is trivial
  (the identity natural transformation). `True` placeholder; concrete
  form is local-layer material (F1). Invariant: holds in every stage
  where K1 occurs; vacuously true for stages n>1 (F3d_Spec §VI.3). -/
  negTau_trivial_at_K1 : True

namespace ModalTwoCategoryWithNegations

variable {𝒯 : Type*} [Category 𝒯]

/-- Full dispatch from all six `ModalSymbol` constructors to the
corresponding endo-functor on `𝒯`. Extends `ModalOperators.symbol`
(which returns `𝟭 𝒯` for neg symbols) to the complete six-symbol set.

This is the semantic bridge for F3.d theorems using `interpretFull`. -/
def symbolFull (M : ModalTwoCategoryWithNegations 𝒯) :
    Reformulation.F3c.ModalSymbol → (𝒯 ⥤ 𝒯)
  | .tau      => M.tau
  | .delta    => M.delta
  | .omega    => M.omega
  | .negTau   => M.negTau
  | .negDelta => M.negDelta
  | .negOmega => M.negOmega

/-- Semantic interpretation of a full symbol-list (over all six
`ModalSymbol` constructors) as a functor on `𝒯`. The empty list
goes to `𝟭 𝒯`; a cons-list goes to the composition of the head
functor with the tail's interpretation. -/
def interpretFull (M : ModalTwoCategoryWithNegations 𝒯) :
    List Reformulation.F3c.ModalSymbol → (𝒯 ⥤ 𝒯)
  | []      => 𝟭 𝒯
  | s :: ss => M.symbolFull s ⋙ M.interpretFull ss

@[simp]
theorem interpretFull_nil (M : ModalTwoCategoryWithNegations 𝒯) :
    M.interpretFull [] = 𝟭 𝒯 := rfl

@[simp]
theorem interpretFull_cons (M : ModalTwoCategoryWithNegations 𝒯)
    (s : Reformulation.F3c.ModalSymbol)
    (ss : List Reformulation.F3c.ModalSymbol) :
    M.interpretFull (s :: ss) = M.symbolFull s ⋙ M.interpretFull ss := rfl

end ModalTwoCategoryWithNegations

end Reformulation.F3d
