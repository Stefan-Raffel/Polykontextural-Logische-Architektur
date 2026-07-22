import Reformulation.F3a
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic

/-!
# F1.D5.MultiChainGeneral — Sub-layer 1: multi-chain-general types

Introduces the multi-chain-general data types and structure class
that are common to any multi-chain system. These types carry no
IBC-specific or bridge-type-specific content; they serve as the base
layer imported by F1.D5.IBC and F1.D5.BridgeTypes.

Structural content:
* `Chain` — self-sovereign reflection space: identity and genesis only.
  F1.D5 abstracts from the consensus belegung per chain (T4 IX:
  distributedness of the initial singularities).
* `Connection` — inter-chain connection with two chain endpoints.
  `isEstablished : True` is a schicht-marker (connection lifecycle
  detail is Sub-Schicht-2 material).
* Manual `DecidableEq Connection` instance — `isEstablished : True`
  is a Prop field; `proof_irrel` handles the True-equality (Class B
  adjustment, same pattern as `Checkpoint` in F1.D2.Ethereum).
* `MultiChain` — finite collection of chains plus connections, with
  a well-formedness predicate. `bicategoryStructure : True` marks the
  follow-on work (full bicategory form with chains as objects,
  connections as 1-cells).
* `connection_endpoints_in_chains` — well-formedness theorem,
  direct field access.
* `multichain_has_chains` — def returning `Finset Chain`, making the
  parallel-valuation form formally visible. Type-valued (not Prop),
  must be `def` per Arbeitsdisziplin c.

Connection to F3.a: `CrossChainCompatibility.toBeckChevalley` in
F1.D5.IBC fills the `beckChevalley` placeholder in
`F3.a.DesignativeRestriction`. The `compatibility` placeholder in
`F3.a.DoubleValuation` remains (Multi-Chain carries no double
valuation). `isFunctorial` and `markerCompat` remain.
`isUnique` is partial (per-chain skeleton uniqueness).

See F1_D5_Spec.md §II (Sub-Schicht 1: Multi-Chain-allgemein), T4 IX,
T11 V.
-/

namespace Reformulation.F1.D5.MultiChainGeneral

open Reformulation.F3a

/-- A chain: a self-sovereign reflection space with its own consensus
and genesis. F1.D5 abstracts from the consensus belegung; only identity
and genesis are modeled at this stratum. -/
structure Chain where
  id          : ℕ
  genesisHash : ℕ
  deriving DecidableEq

/-- An inter-chain connection: an established connection between two
chains, each carrying a light-client of the other. The connection
lifecycle (INIT, OPEN, etc. in IBC parlance) is not modeled at the
F1.D5 level; it is local-stratum-2 material. -/
structure Connection where
  chainA        : Chain
  chainB        : Chain
  isEstablished : True

/-- Manual `DecidableEq` instance for `Connection`.

The `chainA` and `chainB` fields are decided by the derived `Chain`
instance. The `isEstablished : True` field is handled by `proof_irrel`:
any two proofs of a `Prop` are propositionally equal (proof irrelevance
axiom). Class B adjustment: same pattern as `Checkpoint` in F1.D2. -/
instance : DecidableEq Connection := fun c₁ c₂ =>
  if hA : c₁.chainA = c₂.chainA then
    if hB : c₁.chainB = c₂.chainB then
      isTrue (by
        obtain ⟨a₁, b₁, t₁⟩ := c₁
        obtain ⟨a₂, b₂, t₂⟩ := c₂
        subst hA; subst hB; rfl)
    else isFalse fun h => hB (congrArg Connection.chainB h)
  else isFalse fun h => hA (congrArg Connection.chainA h)

/-- A multi-chain system: a finite collection of chains with their
inter-chain connections, plus a well-formedness condition. The
bicategorical structure (chains as objects, connections as 1-cells,
Beck-Chevalley as 2-cell witness) is marked as follow-on work. -/
structure MultiChain where
  chains       : Finset Chain
  connections  : Finset Connection
  /-- Well-formedness: every connection refers to chains in `chains`. -/
  connectionsCompatible : ∀ c ∈ connections,
    c.chainA ∈ chains ∧ c.chainB ∈ chains
  /-- The bicategorical structure as follow-on work
  (prop_field : True per the schicht-trennungs-konvention). -/
  bicategoryStructure : True

/-- Every connection in a MultiChain refers to chains that are in
the chain set. Direct consequence of the well-formedness field. -/
theorem connection_endpoints_in_chains
    (m : MultiChain) (c : Connection) (hc : c ∈ m.connections) :
    c.chainA ∈ m.chains ∧ c.chainB ∈ m.chains :=
  m.connectionsCompatible c hc

/-- The MultiChain form carries multiple parallel valuations of
stage 0 (one per chain). Direct from the structure form. The full
Bicategory instance is follow-on work; this def makes the
parallel-valuation form formally visible. -/
def multichain_has_chains (m : MultiChain) : Finset Chain :=
  m.chains

end Reformulation.F1.D5.MultiChainGeneral
