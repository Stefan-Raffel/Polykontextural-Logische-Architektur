import Reformulation.F3e.ModalTwoCategoryWithPullbacks
import Mathlib.CategoryTheory.NatIso

/-!
# F3.e.BeckChevalleyConstruction — the BC 2-iso from the structure

This module provides `beckChevalleyFromData`, which reads off the Beck-Chevalley
natural isomorphism of a `ModalTwoCategoryWithPullbacks`:
`M.pullBackC ⋙ M.pullBackO ≅ M.pullBackO ⋙ M.pullBackC`, the canonical 2-iso
between the two composites ψ*∘φ* and φ*∘ψ* on 𝒯.

## Why the BC 2-iso is a structural datum, not a derivation

One might hope to build this iso from the six `modalCompatXY` fields via whiskering:
for a bridge operator m (e.g. τ), `modalCompatTauO : τ∘φ* ≅ φ*∘τ` and
`modalCompatTauC : τ∘ψ* ≅ ψ*∘τ` chain by `Iso.trans` towards ψ*∘φ* → φ*∘ψ*.
This does **not** go through: two functors ψ* and φ* that each commute (up to 2-iso)
with a third functor m need not commute with each other. The BC condition
`ψ*∘φ* ≅ φ*∘ψ*` is therefore additional structure relative to the modal
compatibility data — which is exactly why `ModalTwoCategoryWithPullbacks` carries
it as its own field `pullBackCommute` (Cluster-II-argumentation, T9 II). At the
belegung-specific (F1) level that field is supplied via concrete pullback squares
and `NatIso.ofComponents` with explicit Iso-components.

See F3e_Implementation_Prompt §V, F3e_Spec §V.2–V.3.
-/

namespace Reformulation.F3e

open CategoryTheory

variable {𝒯 : Type*} [Category 𝒯]

/-- The Beck-Chevalley 2-iso of a `ModalTwoCategoryWithPullbacks`: the natural
isomorphism between the two composite pullback functors ψ*∘φ* and φ*∘ψ*.

It is the structure's `pullBackCommute` datum, read off directly. This is not a
proof that BC *holds* — it is the datum an instance must provide; the value of
carrying it as a field is that the structure states honestly what it needs
(the mutual commutation of the two pullback functors) instead of pretending to
derive it from the modal compatibility fields, which it cannot (see module doc). -/
def beckChevalleyFromData (M : ModalTwoCategoryWithPullbacks 𝒯) :
    M.pullBackC ⋙ M.pullBackO ≅ M.pullBackO ⋙ M.pullBackC :=
  M.pullBackCommute

-- Axiom-Wache (Whitelist-Auflösung, 24. Juli 2026): sorry-frei nach Anschluss an
-- das Strukturdatum `pullBackCommute`; Profil Ist-gebunden verwacht.
/-- info: 'Reformulation.F3e.beckChevalleyFromData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms beckChevalleyFromData

end Reformulation.F3e
