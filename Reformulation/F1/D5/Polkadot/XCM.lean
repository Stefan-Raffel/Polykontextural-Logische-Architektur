import Reformulation.F1.D5.Polkadot.PolkadotGeneral

/-!
# F1.D5.Polkadot.XCM — Sub-layer 2: XCM-specific types and compatibility

Introduces XCM (Cross-Consensus Messaging) as the fourth bridge form,
parallel to the three types in F1.D5.BridgeTypes (multiSig, optimistic,
lightClient). XCM operates through a shared relay-chain validator pool,
not through a client-pair verification mechanism.

Structural content:
* `XCMMessage` — cross-consensus message between two parachains, mediated
  by their shared relay-chain. `sameRelay` is a conjunctive well-formedness
  condition (both parachains share the relay-chain). Manual `DecidableEq`
  instance (Class B, Risiko-Stelle 2: Prop conjunction field).
* `XCMBridge` — XCM bridge form with a relay-soundness marker.
* `XCMBridge.isStructurallySound` — structural soundness predicate.
  Returns `True` (XCM bridges are structurally sound through relay-chain
  delegation; the `isRelaySound : True` field witnesses this).
* `XCMCompatibility` — cross-chain compatibility for XCM bridges. Hybrid
  form: `beckChevalleyHolds : True` as placeholder, plus `relayMediation`
  as a provable predicate making relay-mediation formally visible.
* `XCMCompatibility.toBeckChevalley` — connection function to F3.a
  `DesignativeRestriction.beckChevalley`. SECOND belegung of this
  placeholder (after F1.D5.IBC's `CrossChainCompatibility.toBeckChevalley`).

See F1_D5_Polkadot_Spec.md §III (Sub-Schicht 2: XCM-spezifisch), T10 IV.
-/

namespace Reformulation.F1.D5.Polkadot.XCM

open Reformulation.F1.D5.MultiChainGeneral
open Reformulation.F1.D5.Polkadot.PolkadotGeneral

/-- XCM message: cross-consensus messaging between two parachains,
mediated by their shared relay-chain. The well-formedness condition
`sameRelay` ensures source and target share the same relay-chain. -/
structure XCMMessage where
  source     : Parachain
  target     : Parachain
  relayChain : RelayChain
  /-- Well-formedness: both source and target parachains are secured by
  the same relay-chain. Provable conjunctive predicate (not a placeholder). -/
  sameRelay  : source.parentRelayChain = relayChain ∧
               target.parentRelayChain = relayChain

/-- Manual `DecidableEq` instance for `XCMMessage`.

The `source`, `target`, `relayChain` fields are decided by their
`DecidableEq` instances. The `sameRelay : Prop` conjunction is handled by
proof irrelevance (definitional in Lean 4 kernel: after `subst` of all
Type-valued fields, `rfl` closes via proof irrelevance over the Prop field).
Class B adjustment, anticipated as Risiko-Stelle 2. -/
instance : DecidableEq XCMMessage := fun m₁ m₂ =>
  if hS : m₁.source = m₂.source then
    if hT : m₁.target = m₂.target then
      if hR : m₁.relayChain = m₂.relayChain then
        isTrue (by
          obtain ⟨s₁, t₁, r₁, p₁⟩ := m₁
          obtain ⟨s₂, t₂, r₂, p₂⟩ := m₂
          subst hS; subst hT; subst hR; rfl)
      else isFalse fun h => hR (congrArg XCMMessage.relayChain h)
    else isFalse fun h => hT (congrArg XCMMessage.target h)
  else isFalse fun h => hS (congrArg XCMMessage.source h)

/-- XCM bridge form: cross-consensus messaging via the relay-chain.
Distinct from F1.D5.BridgeTypes (multiSig, optimistic, lightClient)
because XCM operates through a shared validator pool, not through
client-pair verification. `isRelaySound : True` marks the delegation
of soundness to the relay-chain consensus. -/
structure XCMBridge where
  message      : XCMMessage
  isRelaySound : True

/-- XCM bridges are structurally sound through relay-chain delegation.
The `isRelaySound : True` field in every XCMBridge witnesses this.
Returns `True` (all XCM bridges are structurally sound by construction). -/
def XCMBridge.isStructurallySound (_xcm : XCMBridge) : Prop := True

/-- 2-categorical Beck-Chevalley compatibility for XCM bridges.
Hybrid form: `beckChevalleyHolds : True` as placeholder, plus a provable
`relayMediation` predicate making relay-mediation structurally visible.

The `relayMediation` condition formalizes: XCM operates through the
relay-chain as shared verification substrate, not through separate
light-clients per parachain pair. -/
structure XCMCompatibility (xcm : XCMBridge) where
  /-- Beck-Chevalley witness for XCM cross-chain compatibility (placeholder). -/
  beckChevalleyHolds : True
  /-- Relay-mediation: the message relay-chain equals the source parachain's
  parent relay-chain. Provable from `sameRelay.1` of the XCMMessage. -/
  relayMediation : xcm.message.relayChain = xcm.message.source.parentRelayChain

/-- Connection function: XCM compatibility implies the abstract beckChevalley
placeholder used in F3.a.DesignativeRestriction.

SECOND belegung of the `beckChevalley` placeholder in the project:
- First: `CrossChainCompatibility.toBeckChevalley` (F1.D5.IBC), Light-Client form.
- Second: `XCMCompatibility.toBeckChevalley` (F1.D5.Polkadot.XCM), Relay-Chain form.

Both belegungen fill the same F3.a placeholder with structurally distinct
concrete forms — confirming the multi-belegbarkeit of the prop_field-True
convention. -/
def XCMCompatibility.toBeckChevalley
    {xcm : XCMBridge} (_c : XCMCompatibility xcm) : True :=
  trivial

end Reformulation.F1.D5.Polkadot.XCM
