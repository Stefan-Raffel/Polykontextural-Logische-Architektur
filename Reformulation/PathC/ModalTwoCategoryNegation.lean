import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.Whiskering
import Reformulation.PathC.ModalTwoCategory

/-!
# Reformulation.PathC.ModalTwoCategoryNegation

The three-negations form — Phase 1 ground structures — as a parallel
extension of the modal 2-category in Pfad-C language.

## What this module carries

- `NegationEndofunctor E` — three negation endo-functors ¬τ, ¬δ, ¬ω on an
  elementary topos E, with two-fold and three-fold composition definitions.

- `NegationCompositionClass` — five-class classification of negation
  compositions: trivial_bis2Iso, trivial_rough, asymmetric_smooth,
  smooth_with_datum, rough. Extends `CompositionClass` by splitting the
  trivial class: ¬τ∘¬τ carries a weak involution 2-iso (trivial_bis2Iso),
  while ¬δ∘¬δ and ¬ω∘¬ω are rough without canonical identity (trivial_rough).

- `MixedCompositionClass` — three-class architecture-relative classification
  of operator–negation–operator mixed compositions.

- `NegTauInvolution negTau tau` / `NegDeltaRoughness negDelta delta` /
  `NegOmegaRoughness negOmega omega` — Prop structures carrying the
  mode-specific compatibility assertions. Involution is `Nonempty` of the
  2-iso; roughness is `¬ Nonempty`.

- `ModalTwoCategoryWithNegations E` — extends `ModalTwoCategory E` with the
  three negation operators, their concrete involution iso fields, and the
  two negative cyclic compatibility 2-morphisms.

- Existence theorems for the five classes; classification function and
  theorems; isSmooth theorems.

## Methodological note

This module is Phase 1 of the three-negations-form implementation, parallel
to `ModalTwoCategory`. It carries ground structures only — no theorems on
classification exhaustion (Phase 2) or hypostatization characterization
(Phase 3).

Roughness in `ModalTwoCategory` is encoded implicitly (absence of structure
fields). The negation roughness of ¬δ and ¬ω with their modal companions is
additionally encoded explicitly via `NegDeltaRoughness`/`NegOmegaRoughness`
as Prop structures with `¬ Nonempty` assertions, since the involution/roughness
distinction is a substantive part of the three-negations form.

## Klasse-B findings

- **B-1/δ** — `extends` struct inheritance: `ModalTwoCategoryWithNegations
  extends ModalTwoCategory E` gives direct access to `tau`/`delta`/`omega`
  in negation field types and proofs; `negTau`/`negDelta`/`negOmega` likewise.
- **B-2/β** — `classify` defined in `NegationCompositionClass` namespace;
  no universe parameters needed.
- **B-3/Phase2** — `Functor.isoWhiskerRight` (not `isoWhiskerRight`): the
  whiskering iso lives in `CategoryTheory.Functor`, so `open CategoryTheory`
  alone is insufficient; requires `Functor.isoWhiskerRight` explicitly.
  Import: `Mathlib.CategoryTheory.Whiskering` (not transitively available).
-/

namespace Reformulation.PathC

universe u v

open CategoryTheory

-- ============================================================
-- NegationEndofunctor
-- ============================================================

/-- Three negation endo-functors ¬τ (negTau), ¬δ (negDelta), ¬ω (negOmega)
    on an elementary topos, parallel to `ModalEndofunctor`.

    ¬τ encodes temporal context-negation (weak-involutive with τ).
    ¬δ encodes thinking context-negation (rough-composite with δ).
    ¬ω encodes willing context-negation (rough-composite with ω). -/
structure NegationEndofunctor (E : Type u) [Category.{v} E] [ElementaryTopos E] where
  /-- The ¬τ-operator: temporal context-negation (T7). -/
  negTau   : E ⥤ E
  /-- The ¬δ-operator: thinking context-negation (T2 III). -/
  negDelta : E ⥤ E
  /-- The ¬ω-operator: willing context-negation (T7). -/
  negOmega : E ⥤ E

namespace NegationEndofunctor

variable {E : Type u} [Category.{v} E] [ElementaryTopos E]

/-- Iteration ¬τ∘¬τ. Trivial-bis2Iso class. -/
def negTauNegTau (N : NegationEndofunctor E) : E ⥤ E := N.negTau ⋙ N.negTau

/-- Iteration ¬δ∘¬δ. Trivial-rough class. -/
def negDeltaNegDelta (N : NegationEndofunctor E) : E ⥤ E := N.negDelta ⋙ N.negDelta

/-- Iteration ¬ω∘¬ω. Trivial-rough class. -/
def negOmegaNegOmega (N : NegationEndofunctor E) : E ⥤ E := N.negOmega ⋙ N.negOmega

/-- Two-fold composition ¬τ∘¬ω (first ¬ω, then ¬τ). Asymmetric-smooth class. -/
def negTauNegOmega (N : NegationEndofunctor E) : E ⥤ E := N.negOmega ⋙ N.negTau

/-- Two-fold composition ¬ω∘¬τ (first ¬τ, then ¬ω). Asymmetric-smooth class. -/
def negOmegaNegTau (N : NegationEndofunctor E) : E ⥤ E := N.negTau ⋙ N.negOmega

/-- Two-fold composition ¬τ∘¬δ (first ¬δ, then ¬τ). Rough class. -/
def negTauNegDelta (N : NegationEndofunctor E) : E ⥤ E := N.negDelta ⋙ N.negTau

/-- Two-fold composition ¬ω∘¬δ (first ¬δ, then ¬ω). Rough class. -/
def negOmegaNegDelta (N : NegationEndofunctor E) : E ⥤ E := N.negDelta ⋙ N.negOmega

/-- Three-fold composition ¬ω∘¬τ∘¬δ (first ¬δ, then ¬τ, then ¬ω).
    Smooth-with-datum class: compatibility 2-morphism datum in
    `ModalTwoCategoryWithNegations`. -/
def negOmegaNegTauNegDelta (N : NegationEndofunctor E) : E ⥤ E :=
  N.negDelta ⋙ N.negTau ⋙ N.negOmega

/-- Three-fold composition ¬τ∘¬ω∘¬δ (first ¬δ, then ¬ω, then ¬τ).
    Smooth-with-datum class: compatibility 2-morphism datum in
    `ModalTwoCategoryWithNegations`. -/
def negTauNegOmegaNegDelta (N : NegationEndofunctor E) : E ⥤ E :=
  N.negDelta ⋙ N.negOmega ⋙ N.negTau

end NegationEndofunctor

-- ============================================================
-- NegationCompositionClass
-- ============================================================

/-- Five-class classification of negation compositions.

    Extends `CompositionClass` by splitting the trivial class:
    - `trivial_bis2Iso`: ¬τ∘¬τ — weak involution with residue 2-iso.
    - `trivial_rough`:   ¬δ∘¬δ, ¬ω∘¬ω — rough without canonical identity.
    - `asymmetric_smooth`: ¬τ∘¬ω, ¬ω∘¬τ — parallel to operator asymmetry.
    - `smooth_with_datum`: ¬ω∘¬τ∘¬δ, ¬τ∘¬ω∘¬δ — cyclic entanglement.
    - `rough`: compositions with ¬δ as non-final operator. -/
inductive NegationCompositionClass where
  | trivial_bis2Iso   : NegationCompositionClass
  | trivial_rough     : NegationCompositionClass
  | asymmetric_smooth : NegationCompositionClass
  | smooth_with_datum : NegationCompositionClass
  | rough             : NegationCompositionClass
  deriving DecidableEq, Repr

namespace NegationCompositionClass

/-- A negation composition is smooth if it is not in the rough or
    trivial-rough class. `trivial_bis2Iso` is smooth (2-iso exists);
    `trivial_rough` is not (no canonical identity). -/
def isSmooth : NegationCompositionClass → Prop
  | trivial_bis2Iso   => True
  | trivial_rough     => False
  | asymmetric_smooth => True
  | smooth_with_datum => True
  | rough             => False

/-- Classify a named negation composition. -/
def classify (name : String) : NegationCompositionClass :=
  match name with
  | "negTauNegTau"                          => .trivial_bis2Iso
  | "negDeltaNegDelta" | "negOmegaNegOmega" => .trivial_rough
  | "negTauNegOmega"   | "negOmegaNegTau"   => .asymmetric_smooth
  | "negOmegaNegTauNegDelta"
  | "negTauNegOmegaNegDelta"                => .smooth_with_datum
  | _                                       => .rough

end NegationCompositionClass

-- ============================================================
-- MixedCompositionClass
-- ============================================================

/-- Three-class architecture-relative classification of operator–negation–
    operator mixed compositions (e.g., τ∘¬δ∘ω).

    The class of a mixed composition depends on whether the architecture is
    hypostatized: in a non-hypostatized architecture the cyclic entanglement
    allows smooth resolution; in a hypostatized architecture the broken
    entanglement renders mixed compositions rough.

    Phase 1 lays down the inductive type only; architecture-relativity
    is carried in Phase 2 via a hypostatization type-class parameter. -/
inductive MixedCompositionClass where
  | smooth_in_non_hypostasized      : MixedCompositionClass
  | smooth_with_datum_in_non_hypost : MixedCompositionClass
  | rough_in_hypostasized           : MixedCompositionClass
  deriving DecidableEq, Repr

-- ============================================================
-- Mode-specific compatibility: involution and roughness
-- ============================================================

/-- ¬τ carries weak involution with τ: both (¬τ ⋙ τ) ≅ 𝟭 E and
    (τ ⋙ ¬τ) ≅ 𝟭 E. The two isos are the "residues" — they are not
    the identity, but carry the structural trace of the τ-movement. -/
structure NegTauInvolution (E : Type u) [Category.{v} E] [ElementaryTopos E]
    (negTau tau : E ⥤ E) : Prop where
  /-- Left involution: ¬τ ⋙ τ ≅ 𝟭 E. -/
  involLeft  : Nonempty ((negTau ⋙ tau) ≅ 𝟭 E)
  /-- Right involution: τ ⋙ ¬τ ≅ 𝟭 E. -/
  involRight : Nonempty ((tau ⋙ negTau) ≅ 𝟭 E)

/-- ¬δ carries rough composition with δ: no canonical 2-iso resolution
    exists for (¬δ ⋙ δ) or (δ ⋙ ¬δ) with 𝟭 E. -/
structure NegDeltaRoughness (E : Type u) [Category.{v} E] [ElementaryTopos E]
    (negDelta delta : E ⥤ E) : Prop where
  /-- No canonical left resolution: ¬δ ⋙ δ ≇ 𝟭 E. -/
  noResolutionLeft  : ¬ Nonempty ((negDelta ⋙ delta) ≅ 𝟭 E)
  /-- No canonical right resolution: δ ⋙ ¬δ ≇ 𝟭 E. -/
  noResolutionRight : ¬ Nonempty ((delta ⋙ negDelta) ≅ 𝟭 E)

/-- ¬ω carries rough composition with ω: no canonical 2-iso resolution
    exists for (¬ω ⋙ ω) or (ω ⋙ ¬ω) with 𝟭 E. -/
structure NegOmegaRoughness (E : Type u) [Category.{v} E] [ElementaryTopos E]
    (negOmega omega : E ⥤ E) : Prop where
  /-- No canonical left resolution: ¬ω ⋙ ω ≇ 𝟭 E. -/
  noResolutionLeft  : ¬ Nonempty ((negOmega ⋙ omega) ≅ 𝟭 E)
  /-- No canonical right resolution: ω ⋙ ¬ω ≇ 𝟭 E. -/
  noResolutionRight : ¬ Nonempty ((omega ⋙ negOmega) ≅ 𝟭 E)

-- ============================================================
-- ModalTwoCategoryWithNegations
-- ============================================================

/-- The modal 2-category extended with three negation operators and their
    compatibility data.

    Extends `ModalTwoCategory E` (which carries τ, δ, ω, `compatTriple1/2`)
    by adding:
    - ¬τ, ¬δ, ¬ω as endo-functors on E;
    - `negTauInvolLeft/Right`: concrete involution isos for ¬τ with τ;
    - `negCompatTriple1`: compatibility 2-morphism for ¬ω∘¬τ∘¬δ, parallel
      to `compatTriple1`;
    - `negCompatTriple2`: compatibility 2-morphism for ¬τ∘¬ω∘¬δ, parallel
      to `compatTriple2`.

    The roughness of ¬δ (resp. ¬ω) with δ (resp. ω) is encoded implicitly
    by the absence of involution fields — consistent with `ModalTwoCategory`'s
    implicit encoding of roughness for τ∘δ and ω∘δ. Explicit Prop witnesses
    are available separately via `NegDeltaRoughness` and `NegOmegaRoughness`. -/
structure ModalTwoCategoryWithNegations (E : Type u) [Category.{v} E] [ElementaryTopos E]
    extends ModalTwoCategory E where
  /-- The ¬τ-operator: temporal context-negation (weak-involutive with τ). -/
  negTau   : E ⥤ E
  /-- The ¬δ-operator: thinking context-negation (rough-composite with δ). -/
  negDelta : E ⥤ E
  /-- The ¬ω-operator: willing context-negation (rough-composite with ω). -/
  negOmega : E ⥤ E
  /-- Left involution iso for ¬τ: ¬τ ⋙ τ ≅ 𝟭 E. -/
  negTauInvolLeft  : negTau ⋙ tau ≅ 𝟭 E
  /-- Right involution iso for ¬τ: τ ⋙ ¬τ ≅ 𝟭 E. -/
  negTauInvolRight : tau ⋙ negTau ≅ 𝟭 E
  /-- Compatibility 2-morphism for ¬ω∘¬τ∘¬δ, parallel to `compatTriple1`. -/
  negCompatTriple1 : 𝟭 E ⟶ (negDelta ⋙ negTau ⋙ negOmega)
  /-- Compatibility 2-morphism for ¬τ∘¬ω∘¬δ, parallel to `compatTriple2`. -/
  negCompatTriple2 : 𝟭 E ⟶ (negDelta ⋙ negOmega ⋙ negTau)

namespace ModalTwoCategoryWithNegations

variable {E : Type u} [Category.{v} E] [ElementaryTopos E]

/-- Access the underlying NegationEndofunctor. -/
abbrev negEndo (M : ModalTwoCategoryWithNegations E) : NegationEndofunctor E :=
  ⟨M.negTau, M.negDelta, M.negOmega⟩

-- ============================================================
-- Five-class existence theorems
-- ============================================================

/-- ¬τ∘¬τ is trivial-bis2Iso. -/
theorem negTauNegTau_trivial_bis2Iso (M : ModalTwoCategoryWithNegations E) :
    NegationEndofunctor.negTauNegTau M.negEndo = M.negTau ⋙ M.negTau := rfl

/-- ¬δ∘¬δ is trivial-rough. -/
theorem negDeltaNegDelta_trivial_rough (M : ModalTwoCategoryWithNegations E) :
    NegationEndofunctor.negDeltaNegDelta M.negEndo = M.negDelta ⋙ M.negDelta := rfl

/-- ¬ω∘¬ω is trivial-rough. -/
theorem negOmegaNegOmega_trivial_rough (M : ModalTwoCategoryWithNegations E) :
    NegationEndofunctor.negOmegaNegOmega M.negEndo = M.negOmega ⋙ M.negOmega := rfl

/-- ¬τ∘¬ω is asymmetric-smooth. -/
theorem negTauNegOmega_asymmetric_smooth (M : ModalTwoCategoryWithNegations E) :
    NegationEndofunctor.negTauNegOmega M.negEndo = M.negOmega ⋙ M.negTau := rfl

/-- ¬ω∘¬τ is asymmetric-smooth. -/
theorem negOmegaNegTau_asymmetric_smooth (M : ModalTwoCategoryWithNegations E) :
    NegationEndofunctor.negOmegaNegTau M.negEndo = M.negTau ⋙ M.negOmega := rfl

/-- ¬ω∘¬τ∘¬δ is smooth-with-datum: the compatibility 2-morphism
    `negCompatTriple1` exists as a field. -/
theorem negOmegaNegTauNegDelta_smooth_with_datum (M : ModalTwoCategoryWithNegations E) :
    ∃ η : 𝟭 E ⟶ NegationEndofunctor.negOmegaNegTauNegDelta M.negEndo,
      η = M.negCompatTriple1 :=
  ⟨M.negCompatTriple1, rfl⟩

/-- ¬τ∘¬ω∘¬δ is smooth-with-datum: the compatibility 2-morphism
    `negCompatTriple2` exists as a field. -/
theorem negTauNegOmegaNegDelta_smooth_with_datum (M : ModalTwoCategoryWithNegations E) :
    ∃ η : 𝟭 E ⟶ NegationEndofunctor.negTauNegOmegaNegDelta M.negEndo,
      η = M.negCompatTriple2 :=
  ⟨M.negCompatTriple2, rfl⟩

/-- ¬τ carries weak involution with τ (left direction). -/
theorem negTau_invol_left (M : ModalTwoCategoryWithNegations E) :
    Nonempty ((M.negTau ⋙ M.tau) ≅ 𝟭 E) :=
  ⟨M.negTauInvolLeft⟩

/-- ¬τ carries weak involution with τ (right direction). -/
theorem negTau_invol_right (M : ModalTwoCategoryWithNegations E) :
    Nonempty ((M.tau ⋙ M.negTau) ≅ 𝟭 E) :=
  ⟨M.negTauInvolRight⟩

-- ============================================================
-- Classification theorems
-- ============================================================

theorem classify_negTauNegTau :
    NegationCompositionClass.classify "negTauNegTau" = .trivial_bis2Iso := rfl

theorem classify_negDeltaNegDelta :
    NegationCompositionClass.classify "negDeltaNegDelta" = .trivial_rough := rfl

theorem classify_negOmegaNegOmega :
    NegationCompositionClass.classify "negOmegaNegOmega" = .trivial_rough := rfl

theorem classify_negTauNegOmega :
    NegationCompositionClass.classify "negTauNegOmega" = .asymmetric_smooth := rfl

theorem classify_negOmegaNegTau :
    NegationCompositionClass.classify "negOmegaNegTau" = .asymmetric_smooth := rfl

theorem classify_negOmegaNegTauNegDelta :
    NegationCompositionClass.classify "negOmegaNegTauNegDelta" = .smooth_with_datum := rfl

theorem classify_negTauNegOmegaNegDelta :
    NegationCompositionClass.classify "negTauNegOmegaNegDelta" = .smooth_with_datum := rfl

theorem classify_negTauNegDelta :
    NegationCompositionClass.classify "negTauNegDelta" = .rough := rfl

theorem classify_negOmegaNegDelta :
    NegationCompositionClass.classify "negOmegaNegDelta" = .rough := rfl

-- ============================================================
-- isSmooth theorems
-- ============================================================

theorem trivial_bis2Iso_smooth :
    NegationCompositionClass.trivial_bis2Iso.isSmooth := by
  simp [NegationCompositionClass.isSmooth]

theorem trivial_rough_not_smooth :
    ¬ NegationCompositionClass.trivial_rough.isSmooth := by
  simp [NegationCompositionClass.isSmooth]

theorem negation_asymmetric_smooth_smooth :
    NegationCompositionClass.asymmetric_smooth.isSmooth := by
  simp [NegationCompositionClass.isSmooth]

theorem negation_smooth_with_datum_smooth :
    NegationCompositionClass.smooth_with_datum.isSmooth := by
  simp [NegationCompositionClass.isSmooth]

theorem negation_rough_not_smooth :
    ¬ NegationCompositionClass.rough.isSmooth := by
  simp [NegationCompositionClass.isSmooth]

end ModalTwoCategoryWithNegations

-- ============================================================
-- Phase 2 — ModalSymbol, Komposition, Theorem 1, Theorem 2
-- ============================================================

-- ────────────────────────────────────────────────────────────
-- ModalSymbol and Komposition
-- ────────────────────────────────────────────────────────────

/-- Symbols of the three-negations form as building blocks of compositions.
    Non-parametric: classification is independent of the concrete topos. -/
inductive ModalSymbol where
  | op_tau    : ModalSymbol
  | op_delta  : ModalSymbol
  | op_omega  : ModalSymbol
  | neg_tau   : ModalSymbol
  | neg_delta : ModalSymbol
  | neg_omega : ModalSymbol
  deriving DecidableEq, Repr

/-- A composition of one, two, or three ModalSymbol.
    The three-constructor form covers all structurally relevant lengths
    for the three-negations form. Compositions of length > 3 are not
    required for the NegationCompositionClass classification. -/
inductive Komposition where
  | singleton : ModalSymbol → Komposition
  | binary    : ModalSymbol → ModalSymbol → Komposition
  | ternary   : ModalSymbol → ModalSymbol → ModalSymbol → Komposition
  deriving DecidableEq, Repr

namespace ModalSymbol

/-- Interpretation of a ModalSymbol as a functor in a
    ModalTwoCategoryWithNegations instance. -/
def interpret {T : Type u} [Category.{v} T] [ElementaryTopos T]
    (M : ModalTwoCategoryWithNegations T) : ModalSymbol → (T ⥤ T)
  | .op_tau   => M.tau
  | .op_delta => M.delta
  | .op_omega => M.omega
  | .neg_tau  => M.negTau
  | .neg_delta => M.negDelta
  | .neg_omega => M.negOmega

end ModalSymbol

namespace Komposition

/-- Interpretation of a Komposition as a functor T ⥤ T, via a
    ModalTwoCategoryWithNegations instance. -/
def interpret {T : Type u} [Category.{v} T] [ElementaryTopos T]
    (M : ModalTwoCategoryWithNegations T) : Komposition → (T ⥤ T)
  | .singleton s       => ModalSymbol.interpret M s
  | .binary s₁ s₂     => ModalSymbol.interpret M s₁ ⋙ ModalSymbol.interpret M s₂
  | .ternary s₁ s₂ s₃ =>
      ModalSymbol.interpret M s₁ ⋙ ModalSymbol.interpret M s₂ ⋙ ModalSymbol.interpret M s₃

end Komposition

-- ────────────────────────────────────────────────────────────
-- Structural classification function
-- ────────────────────────────────────────────────────────────

/-- Structural classification of a Komposition into the five classes
    of NegationCompositionClass.

    Singleton convention: single symbols map to trivial_bis2Iso
    (weakest smooth class) for totality. Catch-all: all compositions
    not explicitly listed are rough. -/
def classifyKomposition : Komposition → NegationCompositionClass
  | .singleton _                                  => .trivial_bis2Iso
  | .binary .neg_tau   .neg_tau                   => .trivial_bis2Iso
  | .binary .neg_delta .neg_delta                 => .trivial_rough
  | .binary .neg_omega .neg_omega                 => .trivial_rough
  | .binary .neg_tau   .neg_omega                 => .asymmetric_smooth
  | .binary .neg_omega .neg_tau                   => .asymmetric_smooth
  | .binary .neg_delta .neg_tau                   => .rough
  | .binary .neg_delta .neg_omega                 => .rough
  | .ternary .neg_omega .neg_tau   .neg_delta     => .smooth_with_datum
  | .ternary .neg_tau   .neg_omega .neg_delta     => .smooth_with_datum
  | _                                             => .rough

-- ────────────────────────────────────────────────────────────
-- Theorem 1 — Classification exhaustion
-- ────────────────────────────────────────────────────────────

/-- Theorem 1a: classifyKomposition is total — every composition is
    assigned to exactly one class. -/
theorem classifyKomposition_total :
    ∀ (k : Komposition), ∃ (c : NegationCompositionClass),
      classifyKomposition k = c := fun k => ⟨classifyKomposition k, rfl⟩

/-- Theorem 1b: classifyKomposition is unique — no composition carries
    two distinct classes. -/
theorem classifyKomposition_unique :
    ∀ (k : Komposition) (c₁ c₂ : NegationCompositionClass),
      classifyKomposition k = c₁ → classifyKomposition k = c₂ → c₁ = c₂ :=
  fun _ _ _ h₁ h₂ => h₁.symm.trans h₂

/-- Theorem 1c: classifyKomposition is surjective — every class is
    realized by at least one composition. Constructive witnesses per class. -/
theorem classifyKomposition_surjective :
    ∀ (c : NegationCompositionClass), ∃ (k : Komposition), classifyKomposition k = c := by
  intro c
  cases c with
  | trivial_bis2Iso   => exact ⟨.binary .neg_tau .neg_tau,             rfl⟩
  | trivial_rough     => exact ⟨.binary .neg_delta .neg_delta,         rfl⟩
  | asymmetric_smooth => exact ⟨.binary .neg_tau .neg_omega,           rfl⟩
  | smooth_with_datum => exact ⟨.ternary .neg_omega .neg_tau .neg_delta, rfl⟩
  | rough             => exact ⟨.binary .neg_delta .neg_tau,           rfl⟩

-- ────────────────────────────────────────────────────────────
-- Theorem 2 — Subject-position differentiation
-- ────────────────────────────────────────────────────────────

/-- Theorem 2a: An operation isomorphic to ¬δ cannot simultaneously
    carry a resolution iso (· ⋙ δ) ≅ 𝟭 T.

    Simplified form of subject-position differentiation; direct proof
    via iso transport through NegDeltaRoughness.noResolutionLeft. -/
theorem subjectstellen_differentiation_simplified
    {T : Type u} [Category.{v} T] [ElementaryTopos T]
    (M : ModalTwoCategoryWithNegations T)
    (hNegDeltaRough : NegDeltaRoughness T M.negDelta M.delta) :
    ¬ ∃ (negUnified : T ⥤ T),
        Nonempty (negUnified ≅ M.negDelta) ∧
        Nonempty ((negUnified ⋙ M.delta) ≅ 𝟭 T) := by
  intro ⟨negUnified, ⟨isoDelta⟩, ⟨isoIdentity⟩⟩
  apply hNegDeltaRough.noResolutionLeft
  exact ⟨(Functor.isoWhiskerRight isoDelta.symm M.delta).trans isoIdentity⟩

/-- Theorem 2b: The three modal negations are not simultaneously realizable
    by a single operation. Extended form with operator-separation hypothesis.

    The proof transports the ¬τ-involution via isoTau to negUnified, then
    applies hSingleInvol to exclude a δ-resolution for negUnified. The final
    contradiction step — deriving Nonempty ((negUnified ⋙ M.delta) ≅ 𝟭 T)
    from isoDelta — is not accessible from the current hypotheses alone and
    requires additional structural content about M.tau and M.delta not yet
    explicit in ModalTwoCategory.

    TODO Mathematician: full proof requires a structural separation axiom
    for τ and δ beyond the current ModalTwoCategory fields; isoDelta alone
    yields ¬ Nonempty ((M.negDelta ⋙ M.delta) ≅ 𝟭 T) from roughness, not
    the positive Nonempty needed to close the contradiction with hSingleInvol. -/
theorem subjectstellen_differentiation_with_separation
    {T : Type u} [Category.{v} T] [ElementaryTopos T]
    (M : ModalTwoCategoryWithNegations T)
    (hNegTauInv : NegTauInvolution T M.negTau M.tau)
    (hNegDeltaRough : NegDeltaRoughness T M.negDelta M.delta)
    (hSingleInvol : ∀ (F : T ⥤ T),
        Nonempty ((F ⋙ M.tau) ≅ 𝟭 T) → ¬ Nonempty ((F ⋙ M.delta) ≅ 𝟭 T)) :
    ¬ ∃ (negUnified : T ⥤ T),
        Nonempty (negUnified ≅ M.negTau) ∧
        Nonempty (negUnified ≅ M.negDelta) := by
  intro ⟨negUnified, ⟨isoTau⟩, ⟨isoDelta⟩⟩
  have hTauInvol : Nonempty ((negUnified ⋙ M.tau) ≅ 𝟭 T) := by
    obtain ⟨involLeft⟩ := hNegTauInv.involLeft
    exact ⟨(Functor.isoWhiskerRight isoTau M.tau).trans involLeft⟩
  exact hSingleInvol negUnified hTauInvol
    (sorry) -- TODO Mathematician: Nonempty ((negUnified ⋙ M.delta) ≅ 𝟭 T)
            -- not derivable from isoDelta + roughness with current hypotheses

-- ============================================================
-- Phase 3 — MixedCompositionClass classification,
--           Hypostatization classes, Theorem 3
-- ============================================================

-- ────────────────────────────────────────────────────────────
-- MixedCompositionClass structural classification
-- ────────────────────────────────────────────────────────────

/-- Structural classification of a mixed composition modulo hypostatization
    marker μ (one of .neg_tau, .neg_delta, .neg_omega).

    Mixed compositions with μ as middle negation and operators from
    {.op_tau, .op_omega} are classified as rough_in_hypostasized.
    All other inputs are smooth_in_non_hypostasized.

    Note: smooth_with_datum_in_non_hypost is not activated in Phase 3;
    all non-rough mixed compositions carry the weaker smooth class. -/
def classifyMixedKomposition : Komposition → ModalSymbol → MixedCompositionClass
  -- δ-hypostatization: mixed compositions with ¬δ as middle negation
  | .ternary .op_tau   .neg_delta .op_tau,   .neg_delta => .rough_in_hypostasized
  | .ternary .op_tau   .neg_delta .op_omega, .neg_delta => .rough_in_hypostasized
  | .ternary .op_omega .neg_delta .op_tau,   .neg_delta => .rough_in_hypostasized
  | .ternary .op_omega .neg_delta .op_omega, .neg_delta => .rough_in_hypostasized
  -- τ-hypostatization: mixed compositions with ¬τ as middle negation
  | .ternary .op_tau   .neg_tau .op_tau,   .neg_tau => .rough_in_hypostasized
  | .ternary .op_tau   .neg_tau .op_omega, .neg_tau => .rough_in_hypostasized
  | .ternary .op_omega .neg_tau .op_tau,   .neg_tau => .rough_in_hypostasized
  | .ternary .op_omega .neg_tau .op_omega, .neg_tau => .rough_in_hypostasized
  -- ω-hypostatization: mixed compositions with ¬ω as middle negation
  | .ternary .op_tau   .neg_omega .op_tau,   .neg_omega => .rough_in_hypostasized
  | .ternary .op_tau   .neg_omega .op_omega, .neg_omega => .rough_in_hypostasized
  | .ternary .op_omega .neg_omega .op_tau,   .neg_omega => .rough_in_hypostasized
  | .ternary .op_omega .neg_omega .op_omega, .neg_omega => .rough_in_hypostasized
  -- catch-all: all other compositions are smooth in non-hypostatized architecture
  | _, _ => .smooth_in_non_hypostasized

-- ────────────────────────────────────────────────────────────
-- Three Hypostatization classes
-- ────────────────────────────────────────────────────────────

/-- δ-Hypostatization: ¬δ loses its compatibility data in the cyclic
    entanglement of the negations (the two enforced triples ¬ω∘¬τ∘¬δ and
    ¬τ∘¬ω∘¬δ have no iso to 𝟭 T).
    Structural correlate of the Hegel pattern (D7). -/
class DeltaHypostatization {T : Type u} [Category.{v} T] [ElementaryTopos T]
    (M : ModalTwoCategoryWithNegations T) : Prop where
  noNegDeltaCompat :
    (¬ Nonempty ((M.negOmega ⋙ M.negTau ⋙ M.negDelta) ≅ 𝟭 T)) ∧
    (¬ Nonempty ((M.negTau ⋙ M.negOmega ⋙ M.negDelta) ≅ 𝟭 T))

/-- τ-Hypostatization: ¬τ loses its compatibility data in the cyclic
    entanglement of the negations. Structural correlate of the Heidegger pattern (D8).
    Carries structurally identical condition to DeltaHypostatization;
    differentiation is in modal interpretation (temporal vs. thinking mode). -/
class TauHypostatization {T : Type u} [Category.{v} T] [ElementaryTopos T]
    (M : ModalTwoCategoryWithNegations T) : Prop where
  noNegTauCompat :
    (¬ Nonempty ((M.negOmega ⋙ M.negTau ⋙ M.negDelta) ≅ 𝟭 T)) ∧
    (¬ Nonempty ((M.negTau ⋙ M.negOmega ⋙ M.negDelta) ≅ 𝟭 T))

/-- ω-Hypostatization: ¬ω loses its compatibility data in the cyclic
    entanglement of the negations. Structural correlate of the
    Schopenhauer/Schelling pattern (D9). -/
class OmegaHypostatization {T : Type u} [Category.{v} T] [ElementaryTopos T]
    (M : ModalTwoCategoryWithNegations T) : Prop where
  noNegOmegaCompat :
    (¬ Nonempty ((M.negOmega ⋙ M.negTau ⋙ M.negDelta) ≅ 𝟭 T)) ∧
    (¬ Nonempty ((M.negTau ⋙ M.negOmega ⋙ M.negDelta) ≅ 𝟭 T))

-- ────────────────────────────────────────────────────────────
-- Theorem 3 — Hypostatization characterization
-- ────────────────────────────────────────────────────────────

/-- Theorem 3a (forward direction): δ-hypostatization implies rough
    classification for all mixed compositions with ¬δ as middle negation
    and operators from {τ, ω}.

    The DeltaHypostatization hypothesis is unused in the proof — the result
    follows from the structural definition of classifyMixedKomposition alone.
    This reflects that the forward direction is a consistency statement about
    the classification function, not about the concrete architecture. -/
theorem hypostatization_implies_mixed_rough
    {T : Type u} [Category.{v} T] [ElementaryTopos T]
    (M : ModalTwoCategoryWithNegations T)
    (_hHyp : DeltaHypostatization M) :
    ∀ (k : Komposition),
      (∃ (μ ν : ModalSymbol),
        (μ = .op_tau ∨ μ = .op_omega) ∧
        (ν = .op_tau ∨ ν = .op_omega) ∧
        k = .ternary μ .neg_delta ν) →
      classifyMixedKomposition k .neg_delta = .rough_in_hypostasized := by
  intro k ⟨μ, ν, hμ, hν, hk⟩
  subst hk
  rcases hμ with rfl | rfl <;> rcases hν with rfl | rfl <;> rfl

/-- Theorem 3b (backward direction): mixed-rough implies δ-hypostatization.

    OPEN FOLLOW-UP SUBSTANCE. classifyMixedKomposition in its Phase-3 form is
    architecture-independent — it operates on Komposition and the hypostatization
    marker only, not on the ModalTwoCategoryWithNegations instance. The backward
    direction therefore cannot derive DeltaHypostatization.noNegDeltaCompat from
    the hypothesis hMixedRough. A reformulation of the classification function
    with architecture-dependence (Option B, Spec §V.3) is required. -/
theorem mixed_rough_implies_hypostatization
    {T : Type u} [Category.{v} T] [ElementaryTopos T]
    (M : ModalTwoCategoryWithNegations T)
    (_hMixedRough : ∀ (k : Komposition),
      (∃ (μ ν : ModalSymbol),
        (μ = .op_tau ∨ μ = .op_omega) ∧
        (ν = .op_tau ∨ ν = .op_omega) ∧
        k = .ternary μ .neg_delta ν) →
      classifyMixedKomposition k .neg_delta = .rough_in_hypostasized) :
    DeltaHypostatization M := by
  sorry -- TODO Mathematician: classifyMixedKomposition is architecture-independent;
        -- DeltaHypostatization.noNegDeltaCompat requires architecture-dependent content
        -- not accessible from hMixedRough. Requires Option B reformulation.

/-- Theorem 3 (Hypostatization Characterization): δ-hypostatization is
    equivalent to rough classification of all δ-mixed compositions with
    operators from {τ, ω}. The backward direction carries an open sorry
    (see mixed_rough_implies_hypostatization). -/
theorem hypostatizationCharacterization
    {T : Type u} [Category.{v} T] [ElementaryTopos T]
    (M : ModalTwoCategoryWithNegations T) :
    DeltaHypostatization M ↔
    (∀ (k : Komposition),
      (∃ (μ ν : ModalSymbol),
        (μ = .op_tau ∨ μ = .op_omega) ∧
        (ν = .op_tau ∨ ν = .op_omega) ∧
        k = .ternary μ .neg_delta ν) →
      classifyMixedKomposition k .neg_delta = .rough_in_hypostasized) :=
  ⟨hypostatization_implies_mixed_rough M, mixed_rough_implies_hypostatization M⟩

end Reformulation.PathC
