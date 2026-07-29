-- EINGEFROREN (29. Juli 2026): dieser Zweig wird nicht fortgeschrieben.
-- Status, Zahlen und die Bedingungen fuer ein Auftauen: docs/build-targets.md, Abschnitt PathC.
import Mathlib.CategoryTheory.Bicategory.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NatTrans
import Reformulation.PathC.ElementaryTopos

/-!
# Reformulation.PathC.ModalTwoCategory

The modal 2-category in Pfad-C language — closing substance of the Pfad-C sequence.

## What this module carries

- `ModalEndofunctor E` — three distinguished endo-functors τ, δ, ω on an
  elementary topos E, with two-fold and three-fold composition definitions.

- `CompositionClass` — four-class classification of compositions:
  trivial, asymmetric_smooth, smooth_with_data, rough.

- `ModalTwoCategory E` — extends `ModalEndofunctor E` with two compatibility
  2-morphisms (natural transformations) for the enforced three-fold compositions
  ω∘τ∘δ and τ∘ω∘δ.

- Existence theorems for the four classes; classification function and theorems.

## Methodological note

This module is the Pfad-C-language formalization of F3.c (Pre-C-language modal
2-category). The substantive content is parallel; the formal language is Pfad-C,
using `ElementaryTopos` from Lücke 2.

The cyclic interweaving is encoded as datum (compatibility 2-morphisms as structure
fields), not as a derived property — following F3.c Klärung 1 §VI Beobachtung 2.
The non-existence aspects (no canonical swap 2-iso for τ∘ω ≠ ω∘τ; no canonical
resolution for rough compositions) are implicit in the absence of corresponding
structure fields.

## Klasse-B findings

- **B-1/δ** — `extends` struct inheritance: `ModalTwoCategory extends ModalEndofunctor E`
  gives direct access to `tau`/`delta`/`omega` in field types and proofs. The
  field types use the inherited fields directly rather than `toModalEndofunctor.`.
- **B-2/β** — `classify` defined without `E`/`M` implicit arguments (no universe
  dependency); defined in `CompositionClass` namespace to avoid spurious universe params.

## Sequenz-Fortschritt: 6/6 complete. Pfad-C-Sequenz abgeschlossen.
-/

namespace Reformulation.PathC

universe u v

open CategoryTheory

-- ============================================================
-- ModalEndofunctor
-- ============================================================

/-- Three distinguished endo-functors τ (tau), δ (delta), ω (omega) on an
    elementary topos. The three operators encode the modal structure of the
    PKL reformulation: τ (reversible time-mode), δ (reorganisation within
    fixed contexture), ω (irreversible setting / new configuration). -/
structure ModalEndofunctor (E : Type u) [Category.{v} E] [ElementaryTopos E] where
  /-- The τ-operator: reversible time-mode (T7). -/
  tau   : E ⥤ E
  /-- The δ-operator: reorganisation in fixed contexture (T2 III). -/
  delta : E ⥤ E
  /-- The ω-operator: irreversible setting / new configuration (T7). -/
  omega : E ⥤ E

namespace ModalEndofunctor

variable {E : Type u} [Category.{v} E] [ElementaryTopos E]

/-- Iteration τ∘τ. Trivial class. -/
def tauTau (M : ModalEndofunctor E) : E ⥤ E := M.tau ⋙ M.tau

/-- Iteration δ∘δ. Trivial class. -/
def deltaDelta (M : ModalEndofunctor E) : E ⥤ E := M.delta ⋙ M.delta

/-- Iteration ω∘ω. Trivial class. -/
def omegaOmega (M : ModalEndofunctor E) : E ⥤ E := M.omega ⋙ M.omega

/-- Two-fold composition τ∘ω (first ω, then τ). Asymmetric-smooth class. -/
def tauOmega (M : ModalEndofunctor E) : E ⥤ E := M.omega ⋙ M.tau

/-- Two-fold composition ω∘τ (first τ, then ω). Asymmetric-smooth class. -/
def omegaTau (M : ModalEndofunctor E) : E ⥤ E := M.tau ⋙ M.omega

/-- Two-fold composition τ∘δ (first δ, then τ). Rough class. -/
def tauDelta (M : ModalEndofunctor E) : E ⥤ E := M.delta ⋙ M.tau

/-- Two-fold composition ω∘δ (first δ, then ω). Rough class. -/
def omegaDelta (M : ModalEndofunctor E) : E ⥤ E := M.delta ⋙ M.omega

/-- Three-fold composition ω∘τ∘δ (first δ, then τ, then ω).
    Smooth-with-data class: compatibility 2-morphism datum in ModalTwoCategory. -/
def omegaTauDelta (M : ModalEndofunctor E) : E ⥤ E := M.delta ⋙ M.tau ⋙ M.omega

/-- Three-fold composition τ∘ω∘δ (first δ, then ω, then τ).
    Smooth-with-data class: compatibility 2-morphism datum in ModalTwoCategory. -/
def tauOmegaDelta (M : ModalEndofunctor E) : E ⥤ E := M.delta ⋙ M.omega ⋙ M.tau

end ModalEndofunctor

-- ============================================================
-- CompositionClass
-- ============================================================

/-- The four-class structure of compositions in the modal 2-category.

    - `trivial`: iterations f∘f — smooth by functor structure alone.
    - `asymmetric_smooth`: τ∘ω, ω∘τ — smooth but no canonical swap 2-iso.
    - `smooth_with_data`: ω∘τ∘δ, τ∘ω∘δ — smooth with compatibility 2-morphism datum.
    - `rough`: compositions with δ as non-final operator — no canonical resolution. -/
inductive CompositionClass where
  | trivial
  | asymmetric_smooth
  | smooth_with_data
  | rough
  deriving DecidableEq, Repr

namespace CompositionClass

/-- A composition is smooth if it is not rough. -/
def isSmooth : CompositionClass → Prop
  | trivial           => True
  | asymmetric_smooth => True
  | smooth_with_data  => True
  | rough             => False

/-- Classify a named composition. -/
def classify (name : String) : CompositionClass :=
  match name with
  | "tauTau" | "deltaDelta" | "omegaOmega" => .trivial
  | "tauOmega" | "omegaTau"               => .asymmetric_smooth
  | "omegaTauDelta" | "tauOmegaDelta"     => .smooth_with_data
  | _                                      => .rough

end CompositionClass

-- ============================================================
-- ModalTwoCategory
-- ============================================================

/-- The modal 2-category extends ModalEndofunctor with two compatibility
    2-morphisms (natural transformations) for the enforced three-fold
    compositions.

    The fields `compatTriple1` and `compatTriple2` encode the cyclic
    interweaving as datum: they witness the smooth-with-data status of
    ω∘τ∘δ and τ∘ω∘δ respectively. The absence of corresponding fields for
    τ∘δ and ω∘δ is the structural encoding of roughness — no canonical
    resolution exists and none is asserted. -/
structure ModalTwoCategory (E : Type u) [Category.{v} E] [ElementaryTopos E]
    extends ModalEndofunctor E where
  /-- Compatibility 2-morphism (natural transformation) for ω∘τ∘δ. -/
  compatTriple1 : 𝟭 E ⟶ (delta ⋙ tau ⋙ omega)
  /-- Compatibility 2-morphism (natural transformation) for τ∘ω∘δ. -/
  compatTriple2 : 𝟭 E ⟶ (delta ⋙ omega ⋙ tau)

namespace ModalTwoCategory

variable {E : Type u} [Category.{v} E] [ElementaryTopos E]

/-- Access the underlying ModalEndofunctor. -/
abbrev endo (M : ModalTwoCategory E) : ModalEndofunctor E := M.toModalEndofunctor

-- ============================================================
-- Four-class existence theorems
-- ============================================================

/-- τ∘τ is trivial: defined as functor composition, no compatibility datum needed. -/
theorem tauTau_trivial (M : ModalTwoCategory E) :
    ModalEndofunctor.tauTau M.endo = M.tau ⋙ M.tau := rfl

/-- δ∘δ is trivial. -/
theorem deltaDelta_trivial (M : ModalTwoCategory E) :
    ModalEndofunctor.deltaDelta M.endo = M.delta ⋙ M.delta := rfl

/-- ω∘ω is trivial. -/
theorem omegaOmega_trivial (M : ModalTwoCategory E) :
    ModalEndofunctor.omegaOmega M.endo = M.omega ⋙ M.omega := rfl

/-- τ∘ω is asymmetric-smooth: no canonical swap 2-iso for τ∘ω ↔ ω∘τ. -/
theorem tauOmega_asymmetric_smooth (M : ModalTwoCategory E) :
    ModalEndofunctor.tauOmega M.endo = M.omega ⋙ M.tau := rfl

/-- ω∘τ is asymmetric-smooth. -/
theorem omegaTau_asymmetric_smooth (M : ModalTwoCategory E) :
    ModalEndofunctor.omegaTau M.endo = M.tau ⋙ M.omega := rfl

/-- ω∘τ∘δ is smooth-with-data: the compatibility 2-morphism `compatTriple1`
    exists as a field of the structure. -/
theorem omegaTauDelta_smooth_with_data (M : ModalTwoCategory E) :
    ∃ η : 𝟭 E ⟶ ModalEndofunctor.omegaTauDelta M.endo, η = M.compatTriple1 :=
  ⟨M.compatTriple1, rfl⟩

/-- τ∘ω∘δ is smooth-with-data: the compatibility 2-morphism `compatTriple2`
    exists as a field of the structure. -/
theorem tauOmegaDelta_smooth_with_data (M : ModalTwoCategory E) :
    ∃ η : 𝟭 E ⟶ ModalEndofunctor.tauOmegaDelta M.endo, η = M.compatTriple2 :=
  ⟨M.compatTriple2, rfl⟩

-- ============================================================
-- Classification theorems
-- ============================================================

theorem classify_tauTau :
    CompositionClass.classify "tauTau" = .trivial := rfl

theorem classify_deltaDelta :
    CompositionClass.classify "deltaDelta" = .trivial := rfl

theorem classify_omegaOmega :
    CompositionClass.classify "omegaOmega" = .trivial := rfl

theorem classify_tauOmega :
    CompositionClass.classify "tauOmega" = .asymmetric_smooth := rfl

theorem classify_omegaTau :
    CompositionClass.classify "omegaTau" = .asymmetric_smooth := rfl

theorem classify_omegaTauDelta :
    CompositionClass.classify "omegaTauDelta" = .smooth_with_data := rfl

theorem classify_tauOmegaDelta :
    CompositionClass.classify "tauOmegaDelta" = .smooth_with_data := rfl

theorem classify_tauDelta :
    CompositionClass.classify "tauDelta" = .rough := rfl

theorem classify_omegaDelta :
    CompositionClass.classify "omegaDelta" = .rough := rfl

-- ============================================================
-- isSmooth theorems
-- ============================================================

theorem trivial_smooth : CompositionClass.trivial.isSmooth := by
  simp [CompositionClass.isSmooth]

theorem asymmetric_smooth_smooth : CompositionClass.asymmetric_smooth.isSmooth := by
  simp [CompositionClass.isSmooth]

theorem smooth_with_data_smooth : CompositionClass.smooth_with_data.isSmooth := by
  simp [CompositionClass.isSmooth]

theorem rough_not_smooth : ¬ CompositionClass.rough.isSmooth := by
  simp [CompositionClass.isSmooth]

end ModalTwoCategory

end Reformulation.PathC
