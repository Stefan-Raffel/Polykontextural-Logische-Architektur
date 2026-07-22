import Reformulation.F1.D5.MultiChainGeneral
import Reformulation.F1.D5.IBC
import Reformulation.F1.D5.IBC.PullBack
import Reformulation.F1.D5.BridgeTypes
import Reformulation.F1.D5.Polkadot

/-!
# F1.D5 — Multi-Chain belegung of the local layer (Cosmos-IBC pilot)

Aggregate for F1.D5 sub-modules. Re-exports the three sub-layers:

- `MultiChainGeneral` (Sub-Schicht 1: multi-chain-general types —
  Chain, Connection, MultiChain with well-formedness predicate)
- `IBC`               (Sub-Schicht 2: IBC-specific — Header, Packet,
  CrossChainCompatibility with Beck-Chevalley and replay protection)
- `BridgeTypes`       (Sub-Schicht 3: bridge-type differentiation —
  BridgeType inductive, isStructurallySound, central theorem)

Structural character: Inter-Reflexionsraum-Form with multiple parallel
valuations (one per chain), rather than the intra-Reflexionsraum double
valuation of F1.D2.

Central F1.D5 theorem: `bridge_soundness_iff_lightClient` — a non-
tautological theorem over BridgeType (unlike F1.D2's tautological
`gasper_inter_layer_compatible`).

F3.a placeholder connections from F1.D5:
- `beckChevalley` (DesignativeRestriction): filled via
  `CrossChainCompatibility.toBeckChevalley`.
- `isUnique` (Skeleton): partial (per-chain skeleton uniqueness).
- `compatibility`, `isFunctorial`, `markerCompat`: remain as
  placeholders (Multi-Chain topology does not activate these).

Folge-Aufgaben outside this spec:
- F1.D5.Polkadot (Relay-Chain asymmetry, XCM bridge classification)
- Full Bicategory form for MultiChain
- Full pull-back form for CrossChainCompatibility (Mathlib IsPullback)

See F1_D5_Spec.md, T4 IX, T10 IV, T11 V.
-/
