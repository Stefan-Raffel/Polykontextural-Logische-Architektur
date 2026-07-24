import Reformulation.F1.D5.IBC

/-!
# F1.D5.IBC.PullBack — commutation kernel of the cross-chain base change

This module measures whether a **non-trivial** statement can be formed at
the cross-chain-compatibility site of the IBC belegung. It does **not**
prove the full categorical pull-back (Beck-Chevalley) condition; it proves
its *commutation kernel* over an ordering of light-client header heights:
performing the base change along two different paths yields the same state.

## What this module is — and is not (Nicht-Soll-Grenzen)

1. **This is not the Beck-Chevalley condition.** What is built is its
   commutation kernel over a height-order; the full categorical form
   (functors, natural isomorphism, pentagon/triangle) does **not** follow
   from it. The four declared Class-D gaps in `F3e` are **not** closed and
   **not** touched by this module.
2. **The placeholder stays.** `CrossChainCompatibility.beckChevalleyHolds :
   True` is **not** replaced in this move and the structure is not changed.
   First measure, then wire — the substitution is a separate, later move.
3. **The cryptographic verification is still not modeled.**
   `Header.isVerifiable` stays `True`. What carries here is solely the
   ordering structure of the heights; any statement about security would be
   unbacked.
4. **No reference to polycontextural notions in this module.** Neither in
   identifiers nor in doc-strings. The interpretation is not the concern of
   this module.

## Structural note

`LightClientState` is **new modeling, not the fleshing-out of an existing
placeholder**: what is added here (a light-client state carrying an accepted
header height, its `update`, and the `deliverable` predicate) stood nowhere
in the corpus before. It is required because the repository carries no
light-client state, hence no square over which a pull-back condition could
speak.

The height-order is used in exactly one place: the monotonicity statement
`ibc_deliverable_stable`. The commutation `ibc_update_commutes` follows from
`max` alone — from the choice of client construction, not from IBC. The
counter-model (`naiveUpdate`, keeping the *last* header instead of the
*highest*) violates both, which is what makes the two statements
non-vacuous.
-/

namespace Reformulation.F1.D5.IBC

open Reformulation.F1.D5.MultiChainGeneral

/-- The state of a light client on the target chain: the highest header
height accepted so far for a given connection. -/
structure LightClientState where
  connection     : Connection
  acceptedHeight : ℕ

/-- Accepting a header: the client keeps the *highest* height seen. -/
def LightClientState.update (s : LightClientState) (h : Header) : LightClientState :=
  { s with acceptedHeight := max s.acceptedHeight h.height }

/-- A packet committed at `commitHeight` on the source chain is
deliverable once the client has accepted a header at least that high. -/
def deliverable (s : LightClientState) (p : Packet) (commitHeight : ℕ) : Prop :=
  p.connection = s.connection ∧ commitHeight ≤ s.acceptedHeight

/-! ## The two statements (commutation kernel + monotonicity) -/

/-- **Commutation kernel.** Accepting two headers commutes: the base change
along two different paths yields the same light-client state. Follows from
commutativity/associativity of `max` alone. -/
theorem ibc_update_commutes (s : LightClientState) (h₁ h₂ : Header) :
    (s.update h₁).update h₂ = (s.update h₂).update h₁ := by
  simp only [LightClientState.update]
  congr 1
  omega

/-- **Monotonicity.** Once deliverable, always deliverable: accepting a
further header can only raise the accepted height. This is the one place
where the height-*order* (`le_max_left`) is actually used. -/
theorem ibc_deliverable_stable
    (s : LightClientState) (p : Packet) (n : ℕ) (h : Header) :
    deliverable s p n → deliverable (s.update h) p n := by
  rintro ⟨hc, hn⟩
  refine ⟨hc, ?_⟩
  simp only [LightClientState.update]
  omega

/-! ## The violation witness -/

/-- A deliberately weaker client: keeps the *last* header seen. Serves
only as a counter-model; not part of the IBC belegung. -/
def naiveUpdate (s : LightClientState) (h : Header) : LightClientState :=
  { s with acceptedHeight := h.height }

/-- The `last`-header client does **not** commute: accepting two headers in
different orders yields different accepted heights. -/
theorem naive_update_not_commutative :
    ∃ (s : LightClientState) (h₁ h₂ : Header),
      ((naiveUpdate (naiveUpdate s h₁) h₂).acceptedHeight
        ≠ (naiveUpdate (naiveUpdate s h₂) h₁).acceptedHeight) := by
  refine ⟨⟨⟨⟨0, 0⟩, ⟨0, 0⟩, trivial⟩, 0⟩, ⟨⟨0, 0⟩, 0, 0⟩, ⟨⟨0, 0⟩, 1, 0⟩, ?_⟩
  decide

/-- The `last`-header client does **not** keep deliverability stable:
accepting a lower header can make a previously deliverable packet
undeliverable. -/
theorem naive_deliverable_not_stable :
    ∃ (s : LightClientState) (p : Packet) (n : ℕ) (h : Header),
      deliverable s p n ∧ ¬ deliverable (naiveUpdate s h) p n := by
  refine ⟨⟨⟨⟨0, 0⟩, ⟨0, 0⟩, trivial⟩, 5⟩, ⟨⟨⟨0, 0⟩, ⟨0, 0⟩, trivial⟩, 0, 0⟩, 3,
    ⟨⟨0, 0⟩, 0, 0⟩, ⟨rfl, by decide⟩, ?_⟩
  rintro ⟨_, hle⟩
  simp only [naiveUpdate] at hle
  omega

/-! ## Statement pins (the strength is in the statement, not the profile) -/

-- STATEMENT-PIN
example (s : LightClientState) (h₁ h₂ : Header) :
    (s.update h₁).update h₂ = (s.update h₂).update h₁ :=
  ibc_update_commutes s h₁ h₂

-- STATEMENT-PIN
example (s : LightClientState) (p : Packet) (n : ℕ) (h : Header) :
    deliverable s p n → deliverable (s.update h) p n :=
  ibc_deliverable_stable s p n h

-- STATEMENT-PIN
example :
    ∃ (s : LightClientState) (h₁ h₂ : Header),
      ((naiveUpdate (naiveUpdate s h₁) h₂).acceptedHeight
        ≠ (naiveUpdate (naiveUpdate s h₂) h₁).acceptedHeight) :=
  naive_update_not_commutative

-- STATEMENT-PIN
example :
    ∃ (s : LightClientState) (p : Packet) (n : ℕ) (h : Header),
      deliverable s p n ∧ ¬ deliverable (naiveUpdate s h) p n :=
  naive_deliverable_not_stable

/-! ## Axiom guards (measured, then frozen verbatim) -/

/-- info: 'Reformulation.F1.D5.IBC.ibc_update_commutes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ibc_update_commutes

/-- info: 'Reformulation.F1.D5.IBC.ibc_deliverable_stable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ibc_deliverable_stable

/-- info: 'Reformulation.F1.D5.IBC.naive_update_not_commutative' does not depend on any axioms -/
#guard_msgs in #print axioms naive_update_not_commutative

/-- info: 'Reformulation.F1.D5.IBC.naive_deliverable_not_stable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms naive_deliverable_not_stable

end Reformulation.F1.D5.IBC
