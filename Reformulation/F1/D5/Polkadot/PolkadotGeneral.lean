import Reformulation.F1.D5.MultiChainGeneral
import Reformulation.F3a
import Mathlib.Data.Finset.Basic

/-!
# F1.D5.Polkadot.PolkadotGeneral — Sub-layer 1: Polkadot-architecture-general

Introduces the Polkadot-specific data types and the extended multi-chain
structure class. Builds on F1.D5.MultiChainGeneral (Chain, Connection,
MultiChain) via composition, not redefinition.

Structural content:
* `RelayChain` — distinguished chain with a validator pool that secures
  parachain blocks. `validatorPool : ℕ` abstracts the validator count;
  concrete validator identities are local-stratum-3 material.
* `Parachain` — sub-chain whose security is inherited from a relay-chain
  through block inclusion. `isIncluded : True` is a placeholder (full
  block-hash inclusion condition is follow-on work).
* Manual `DecidableEq Parachain` instance — `isIncluded : True` is a
  Prop field; same pattern as `Connection` in F1.D5.MultiChainGeneral
  and `Checkpoint` in F1.D2.Ethereum (Class B, anticipated Risiko-Stelle 1).
* `PolkadotMultiChain` — composition form: carries a `base : MultiChain`
  plus a `relayChain : RelayChain` plus `parachains : Finset Parachain`,
  with three well-formedness conditions (all provable predicates, no
  placeholders).
* `polkadot_relay_in_base` — well-formedness theorem, direct field access.
* `parachain_parent_is_relay` — well-formedness theorem, direct field access.
* `polkadotMultiChain_to_multiChain` — def (Type-valued, per Arbeitsdisziplin c).

Aufsetzungs-form: PolkadotMultiChain *contains* a MultiChain (base field)
rather than extending it. Same form-choice as HybridConsensus in F1.D2.Hybrid.

See F1_D5_Polkadot_Spec.md §II (Sub-Schicht 1: Polkadot-allgemein).
-/

namespace Reformulation.F1.D5.Polkadot.PolkadotGeneral

open Reformulation.F1.D5.MultiChainGeneral
open Reformulation.F3a

/-- Relay-chain: a distinguished chain that carries a validator pool and
validates parachain blocks. The validator pool is abstracted as a count;
concrete validator identities are local-stratum-3 material. -/
structure RelayChain where
  chain         : Chain
  validatorPool : ℕ
  deriving DecidableEq

/-- Parachain: a sub-chain whose security is inherited from a relay-chain
through block inclusion. Each parachain has its own genesis but its blocks
are validated by relay-chain validators. -/
structure Parachain where
  chain            : Chain
  parentRelayChain : RelayChain
  /-- Structural condition: parachain blocks are included in the relay-chain.
  Placeholder per prop_field : True convention; full form (parachain block
  hash in relay-chain block) is follow-on work. -/
  isIncluded : True

/-- Manual `DecidableEq` instance for `Parachain`.

The `chain` and `parentRelayChain` fields are decided by their derived
instances. The `isIncluded : True` field is handled by proof irrelevance
(definitional in Lean 4 kernel: any two proofs of a Prop are definitionally
equal). Class B adjustment, anticipated as Risiko-Stelle 1: same pattern
as `Connection` in F1.D5.MultiChainGeneral. -/
instance : DecidableEq Parachain := fun p₁ p₂ =>
  if hC : p₁.chain = p₂.chain then
    if hR : p₁.parentRelayChain = p₂.parentRelayChain then
      isTrue (by
        obtain ⟨c₁, r₁, t₁⟩ := p₁
        obtain ⟨c₂, r₂, t₂⟩ := p₂
        subst hC; subst hR; rfl)
    else isFalse fun h => hR (congrArg Parachain.parentRelayChain h)
  else isFalse fun h => hC (congrArg Parachain.chain h)

/-- Polkadot multi-chain: a MultiChain extended with a distinguished
relay-chain and a finite collection of parachains, with three
well-formedness conditions linking them.

Composition form: carries `base : MultiChain` rather than extending it
(Vorentscheidung 2 from Klärung 2 §I.4). All three well-formedness
conditions are provable predicates, not placeholders. -/
structure PolkadotMultiChain where
  base       : MultiChain
  relayChain : RelayChain
  parachains : Finset Parachain
  /-- Well-formedness: the relay-chain's underlying chain is in the base
  MultiChain. -/
  relayInBase : relayChain.chain ∈ base.chains
  /-- Well-formedness: every parachain's underlying chain is in the base
  MultiChain. -/
  parachainsInBase : ∀ p ∈ parachains, p.chain ∈ base.chains
  /-- Well-formedness: all parachains share the same parent relay-chain.
  This is the structural form of Polkadot's asymmetry — the relay-chain
  is the unique security provider. -/
  parachainsShareRelay : ∀ p ∈ parachains, p.parentRelayChain = relayChain

/-- Every Polkadot multi-chain has a relay-chain whose underlying chain
is in the base MultiChain. Direct from the well-formedness field. -/
theorem polkadot_relay_in_base (pm : PolkadotMultiChain) :
    pm.relayChain.chain ∈ pm.base.chains :=
  pm.relayInBase

/-- Every parachain in a Polkadot multi-chain has its parent relay-chain
equal to the distinguished relay-chain of the multi-chain.
Direct consequence of `parachainsShareRelay`. -/
theorem parachain_parent_is_relay
    (pm : PolkadotMultiChain) (p : Parachain) (hp : p ∈ pm.parachains) :
    p.parentRelayChain = pm.relayChain :=
  pm.parachainsShareRelay p hp

/-- The base MultiChain of a PolkadotMultiChain inherits the MultiChain
form. Aufsetzungs-form: PolkadotMultiChain *contains* a MultiChain.
Type-valued; must be `def` per Arbeitsdisziplin c. -/
def polkadotMultiChain_to_multiChain (pm : PolkadotMultiChain) : MultiChain :=
  pm.base

end Reformulation.F1.D5.Polkadot.PolkadotGeneral
