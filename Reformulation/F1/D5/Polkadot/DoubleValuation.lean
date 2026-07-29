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
* `polkadot_doubleValuation_asymmetric` — central theorem: the selected
  parachain's parent relay-chain equals the multi-chain's relay-chain.
  Formal form of "Relay-Chain trägt, Parachain hängt ab".

The connection function to the F3.a `DoubleValuation.compatibility` placeholder
was removed in the Phase-2 sharpening; see the memorial block at the end of this
module. The central theorem is unaffected — it states an equation over
`inclusionCompat`, not a placeholder.

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

/-- Central F1.D5.Polkadot theorem: Polkadot's double valuation is
asymmetric. The selected parachain's parent relay-chain equals the
multi-chain's relay-chain — formal expression of "Relay-Chain trägt,
Parachain hängt ab" (T11 V asymmetric form). Direct field access over
`inclusionCompat`. -/
theorem polkadot_doubleValuation_asymmetric (pdv : PolkadotDoubleValuation) :
    pdv.selectedParachain.parentRelayChain = pdv.pm.relayChain :=
  pdv.inclusionCompat

/-! ## Memorial block: declaration removed because its statement was `True`

Removed in the Phase-2 sharpening (Setzungsregister, `docs/status-register.md`).
The name claimed content, the statement was `True`. No consumer in the aggregate;
the removal breaks nothing.

Signature quoted indented by two spaces so that the counting route `^def` does
not count the memorial quote as a declaration.

**Removed — `PolkadotDoubleValuation.toDoubleValuationCompat`.** Register `S46`.

```
  def PolkadotDoubleValuation.toDoubleValuationCompat
      (_p : PolkadotDoubleValuation) : True :=
    trivial
```

*What was claimed:* that the Polkadot double valuation fills the F3.a
`DoubleValuation.compatibility` placeholder — the second of three belegungen of
that placeholder, in the spatially asymmetric relay-inclusion form.
*What a load-bearing statement would need:* the target field
`F3a.DoubleValuation.compatibility` (register row `S15`) must carry content;
a function into `True` establishes no connection, since every term of every type
maps to `trivial`. The asymmetry this module is about is already stated without
any placeholder, by `polkadot_doubleValuation_asymmetric` directly above, which
proves an equation over `inclusionCompat`. That theorem is what the module
carries, and the removed function added nothing to it.
-/

end Reformulation.F1.D5.Polkadot.DoubleValuation
