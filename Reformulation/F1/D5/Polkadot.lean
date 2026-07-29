import Reformulation.F1.D5.Polkadot.PolkadotGeneral
import Reformulation.F1.D5.Polkadot.XCM
import Reformulation.F1.D5.Polkadot.DoubleValuation

/-!
# F1.D5.Polkadot — Polkadot sub-belegung of F1.D5 (Multi-Chain)

Aggregate for F1.D5.Polkadot sub-modules. Re-exports the three sub-layers:

- `PolkadotGeneral` (Sub-Schicht 1: Polkadot-architecture-general —
  RelayChain, Parachain, PolkadotMultiChain with three well-formedness
  predicates)
- `XCM`             (Sub-Schicht 2: XCM-specific — XCMMessage, XCMBridge,
  XCMCompatibility with relay-mediation)
- `DoubleValuation` (Sub-Schicht 3: asymmetric double valuation —
  PolkadotDoubleValuation, central theorem)

Methodological status: first F1 sub-belegung in the project. Builds on
F1.D5.MultiChainGeneral via composition (base : MultiChain field). Does
not import F1.D5.IBC or F1.D5.BridgeTypes.

The two connection functions into the F3.a placeholders `beckChevalley`
(DesignativeRestriction) and `compatibility` (DoubleValuation) were removed in
the Phase-2 sharpening; see the memorial blocks in `Polkadot/XCM.lean` and
`Polkadot/DoubleValuation.lean`. What the series of such fillings did and did
not show is recorded once, in `F1/D2/Rollups/DoubleValuation.lean`.

Central theorem: `polkadot_doubleValuation_asymmetric` — formal expression
of "Relay-Chain trägt, Parachain hängt ab".

See F1_D5_Polkadot_Spec.md, T11 V.
-/
