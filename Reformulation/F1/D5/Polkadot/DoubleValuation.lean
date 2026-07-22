import Reformulation.F1.D5.Polkadot.PolkadotGeneral
import Reformulation.F3a

/-!
# F1.D5.Polkadot.DoubleValuation — Sub-layer 3: asymmetric double valuation

Introduces Polkadot's asymmetric double-valuation form and the central
F1.D5.Polkadot theorem: `polkadot_doubleValuation_asymmetric`.

Structural content:
* `PolkadotDoubleValuation` — asymmetric two-valuation form for relay-chain
  plus parachain. The relay-chain carries hard T7 (GRANDPA finality); the
  parachain carries softer T7 (finalized by relay-chain inclusion).
  `inclusionCompat` is the provable compatibility condition.
* `PolkadotDoubleValuation.toDoubleValuationCompat` — connection function
  to F3.a `DoubleValuation.compatibility`. SECOND belegung of this
  placeholder (after F1.D2.Ethereum's `GasperCompatibility.toDoubleValuationCompat`).
* `polkadot_doubleValuation_asymmetric` — central theorem: the selected
  parachain's parent relay-chain equals the multi-chain's relay-chain.
  Formal form of "Relay-Chain trägt, Parachain hängt ab".

F3.a multi-belegung: `compatibility` (DoubleValuation) is filled for the
second time in the project:
- First: F1.D2.Ethereum (GasperCompatibility, symmetric FFG-Lock form)
- Second: F1.D5.Polkadot.DoubleValuation (asymmetric relay-chain form)

See F1_D5_Polkadot_Spec.md §IV (Sub-Schicht 3: Doppel-Belegung), T11 V.
-/

namespace Reformulation.F1.D5.Polkadot.DoubleValuation

open Reformulation.F1.D5.MultiChainGeneral
open Reformulation.F1.D5.Polkadot.PolkadotGeneral
open Reformulation.F3a

/-- Polkadot double valuation: an asymmetric two-valuation form for
relay-chain plus parachain. The relay-chain carries the hard valuation
(GRANDPA finality); the selected parachain carries the soft valuation
(finalized only through relay-chain inclusion).

The asymmetry is captured by `inclusionCompat`: the selected parachain's
security is not independent — it is derived from the relay-chain. This
is the formal expression of "Relay-Chain trägt, Parachain hängt ab". -/
structure PolkadotDoubleValuation where
  pm                : PolkadotMultiChain
  selectedParachain : Parachain
  parachainInPm     : selectedParachain ∈ pm.parachains
  /-- Inclusion compatibility: the selected parachain's parent relay-chain
  equals the multi-chain's relay-chain. Provable from `parachainsShareRelay`.
  This is the structural form of the asymmetric double valuation. -/
  inclusionCompat   : selectedParachain.parentRelayChain = pm.relayChain

/-- Connection function: Polkadot double valuation implies the abstract
compatibility placeholder used in F3.a.DoubleValuation.

SECOND belegung of the `compatibility` placeholder in the project:
- First: F1.D2.Ethereum `GasperCompatibility.toDoubleValuationCompat`
  (symmetric FFG-Lock form within a single consensus chain).
- Second: `PolkadotDoubleValuation.toDoubleValuationCompat`
  (asymmetric relay-chain inclusion form between two chain levels).

Both belegungen fill the same F3.a placeholder with structurally
distinct concrete forms — the first multi-belegung of a F3.a
prop_field-True placeholder in the project. -/
def PolkadotDoubleValuation.toDoubleValuationCompat
    (_p : PolkadotDoubleValuation) : True :=
  trivial

/-- Central F1.D5.Polkadot theorem: Polkadot's double valuation is
asymmetric. The selected parachain's parent relay-chain equals the
multi-chain's relay-chain — formal expression of "Relay-Chain trägt,
Parachain hängt ab" (T11 V asymmetric form). Direct field access over
`inclusionCompat`. -/
theorem polkadot_doubleValuation_asymmetric (pdv : PolkadotDoubleValuation) :
    pdv.selectedParachain.parentRelayChain = pdv.pm.relayChain :=
  pdv.inclusionCompat

end Reformulation.F1.D5.Polkadot.DoubleValuation
