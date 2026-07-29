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

The connection function to the F3.a `DesignativeRestriction.beckChevalley`
placeholder was removed in the Phase-2 sharpening; see the memorial block at the
end of this module. What this module carries is `relayMediation`, a provable
predicate, and that stays.

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
  /-- Relay-soundness marker. **Placeholder** (register row `S12`): soundness is
  delegated to the relay-chain consensus, which F1.D5 does not model. Exit:
  model relay-chain consensus and derive soundness from it. -/
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

/-! ## Memorial block: declaration removed because its statement was `True`

Removed in the Phase-2 sharpening (Setzungsregister, `docs/status-register.md`).
The name claimed content, the statement was `True`. No consumer in the aggregate;
the removal breaks nothing.

Signature quoted indented by two spaces so that the counting route `^def` does
not count the memorial quote as a declaration.

**Removed — `XCMCompatibility.toBeckChevalley`.** Register row `S45`.

```
  def XCMCompatibility.toBeckChevalley
      {xcm : XCMBridge} (_c : XCMCompatibility xcm) : True :=
    trivial
```

*What was claimed:* that XCM compatibility fills the F3.a
`DesignativeRestriction.beckChevalley` placeholder — the second of three
belegungen of that placeholder, in relay-chain form.
*What a load-bearing statement would need:* the target field
`F3a.DesignativeRestriction.beckChevalley` (register row `S14`) must carry an
actual 2-isomorphism instead of `True`; a function into `True` establishes no
connection, since every term of every type maps to `trivial`. The observation
that the belegungen differ structurally — light-client verification here,
relay-chain delegation there — is recorded once, in the memorial block of
`F1/D2/Rollups/DoubleValuation.lean`, and is not repeated across the modules.
The local material that could feed a real construction is `relayMediation`,
which stays and is provable from `XCMMessage.sameRelay`.
-/

end Reformulation.F1.D5.Polkadot.XCM
