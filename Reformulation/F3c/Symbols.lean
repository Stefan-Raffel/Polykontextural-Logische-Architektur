import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype

/-!
# F3.c.Symbols — syntactic representation of the modal triad (extended for F3.d)

This module introduces:

* `ModalSymbol`: the six-element type `{tau, delta, omega, negTau, negDelta, negOmega}`
  representing the modal operators and their context-negations syntactically,
  independent of any concrete functor realization.
  Extended in F3.d (F3d_Spec.md §I.1) to carry the three context-negation symbols.
* `IsSmooth`: an inductive predicate on `List ModalSymbol` characterising
  which symbol-list compositions are smooth in the four-class refinement.
  F3.c constructors (six):
    - `identity`                    — Klasse "trivial" (empty composition)
    - `trivialIteration`            — Klasse "trivial" (s∘s for any operator)
    - `asymmetricSmoothTauOmega`    — Klasse "asymmetrisch-glatt" (τ∘ω)
    - `asymmetricSmoothOmegaTau`    — Klasse "asymmetrisch-glatt" (ω∘τ)
    - `enforcedTriple1`             — Klasse "glatt mit Verträglichkeits-Datum" (ω∘τ∘δ)
    - `enforcedTriple2`             — Klasse "glatt mit Verträglichkeits-Datum" (τ∘ω∘δ)
  F3.d extensions (eleven):
    - `negTrivialIteration_tau/delta/omega` — trivial neg-iterations ¬_x∘¬_x
    - `modalCompanion_*_left/right`         — modal kinship pairs ¬_x∘x and x∘¬_x
    - `negEnforcedTriple1/2`                — negative cyclic entanglement triples
    - `negAsymmetricSmooth_*`               — asymmetric-smooth negative pairs
* `IsRough`: the negation of `IsSmooth`, characterising the fourth class.

See F3c_Klaerung_1.docx §IV–VI, F3c_Spec.docx §II, and F3d_Spec.md §I.1, §IV.2, §VII.
-/

namespace Reformulation.F3c

/-- Syntactic representation of the modal triad τ, δ, ω and their
context-negations ¬_τ, ¬_δ, ¬_ω.

* `tau`      — displacement, time-mode operator (T2, T7).
* `delta`    — reorganization, thinking-mode operator; not self-supporting.
* `omega`    — positing, will-mode operator; carries B5/B6 in the cyclic
               δ-bound entanglement (T6).
* `negTau`   — temporal context-negation (¬_τ), stage-relative (F3d_Spec §II.4).
* `negDelta` — thinking context-negation (¬_δ), intra-contextural; proximal to
               classical negation (F3d_Spec §II.4).
* `negOmega` — willing context-negation (¬_ω), trans-contextural; primary context-
               negation in Reformulierung_Konzept §1's sense (F3d_Spec §II.4).

Extended from three to six constructors for F3.d (F3d_Spec.md §I.1 Spec-Entscheidung 1).
`deriving Fintype` handles the six-constructor case automatically.
-/
inductive ModalSymbol : Type where
  | tau
  | delta
  | omega
  | negTau
  | negDelta
  | negOmega
  deriving DecidableEq, Repr, Fintype

/-- Smoothness predicate for symbol-list compositions, encoding the
four-class refinement of the three-class composition structure of T9
(see F3c_Klaerung_1.docx §VI Beobachtung 1), extended in F3.d to cover
negation-symbol compositions (F3d_Spec.md §I.3, §IV.2, §VII).

**F3.c constructors** (invariant layer, unchanged):
* `identity`: the empty composition (Identitäts-Funktor on 𝒯).
* `trivialIteration s`: the composition `s ∘ s` for any single operator.
* `asymmetricSmoothTauOmega`: the composition `τ ∘ ω`.
* `asymmetricSmoothOmegaTau`: the composition `ω ∘ τ`.
* `enforcedTriple1`: the cyclically-entangled composition `ω ∘ τ ∘ δ`.
* `enforcedTriple2`: the cyclically-entangled composition `τ ∘ ω ∘ δ`.

**F3.d extension constructors** (negation layer):
* `negTrivialIteration_{tau,delta,omega}`: neg-symbol self-iterations ¬_x∘¬_x.
* `modalCompanion_{tau,delta,omega}_{left,right}`: modal kinship pairs
  ¬_x∘x (left) and x∘¬_x (right) — smooth because Negation and movement
  carry the same modal mode (F3d_Spec §IV.2).
* `negEnforcedTriple1`: the negative cyclic triple ¬_ω∘¬_τ∘¬_δ.
* `negEnforcedTriple2`: the negative cyclic triple ¬_τ∘¬_ω∘¬_δ.
* `negAsymmetricSmooth_{negTauNegOmega,negOmegaNegTau}`: negative
  asymmetric-smooth pairs, analog to the τ∘ω / ω∘τ pair.

All other symbol-list compositions (including ¬_δ-non-final and
modal-alien pairs ¬_x∘y for x≠y) are rough (F3d_Spec §VII, §V.2 NEnM1).
-/
inductive IsSmooth : List ModalSymbol → Prop where
  -- F3.c constructors (unchanged)
  | identity : IsSmooth []
  | trivialIteration (s : ModalSymbol) : IsSmooth [s, s]
  | asymmetricSmoothTauOmega : IsSmooth [.tau, .omega]
  | asymmetricSmoothOmegaTau : IsSmooth [.omega, .tau]
  | enforcedTriple1 : IsSmooth [.omega, .tau, .delta]
  | enforcedTriple2 : IsSmooth [.tau, .omega, .delta]
  -- F3.d extensions: trivial neg-iterations (En5 — F3d_Spec §V.1)
  | negTrivialIteration_tau   : IsSmooth [.negTau,   .negTau]
  | negTrivialIteration_delta : IsSmooth [.negDelta, .negDelta]
  | negTrivialIteration_omega : IsSmooth [.negOmega, .negOmega]
  -- F3.d extensions: modal kinship / companion pairs (En2 — F3d_Spec §IV.2)
  | modalCompanion_tau_left    : IsSmooth [.negTau,   .tau]
  | modalCompanion_tau_right   : IsSmooth [.tau,      .negTau]
  | modalCompanion_delta_left  : IsSmooth [.negDelta, .delta]
  | modalCompanion_delta_right : IsSmooth [.delta,    .negDelta]
  | modalCompanion_omega_left  : IsSmooth [.negOmega, .omega]
  | modalCompanion_omega_right : IsSmooth [.omega,    .negOmega]
  -- F3.d extensions: negative cyclic entanglement (En3/En4 — F3d_Spec §IV.1)
  | negEnforcedTriple1 : IsSmooth [.negOmega, .negTau, .negDelta]
  | negEnforcedTriple2 : IsSmooth [.negTau,   .negOmega, .negDelta]
  -- F3.d extensions: negative asymmetric-smooth pairs (F3d_Spec §VII.1)
  | negAsymmetricSmooth_negTauNegOmega  : IsSmooth [.negTau,   .negOmega]
  | negAsymmetricSmooth_negOmegaNegTau  : IsSmooth [.negOmega, .negTau]

/-- Roughness as the negation of smoothness; the fourth class of the
four-class refinement. -/
def IsRough (composition : List ModalSymbol) : Prop :=
  ¬ IsSmooth composition

end Reformulation.F3c
