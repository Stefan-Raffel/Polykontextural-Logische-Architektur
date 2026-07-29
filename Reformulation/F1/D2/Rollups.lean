import Reformulation.F1.D2.Rollups.Families
import Reformulation.F1.D2.Rollups.RollupGeneral
import Reformulation.F1.D2.Rollups.DoubleValuation
import Reformulation.F1.D2.Rollups.Coalgebraic

/-!
# F1.D2.Rollups — Sub-belegung of F1.D2 with rollup architecture

Aggregate for F1.D2.Rollups sub-modules. Re-exports the three sub-layers:

- `Families`         (Sub-Schicht 2: four rollup families — RollupFamily
  with zkRollup, optimisticRollup, validium, sovereign; uniform soundness;
  rollup_soundness_universal as Central Theorem 1)
- `RollupGeneral`    (Sub-Schicht 1: rollup-architecture-general —
  Layer1Chain, Layer2Rollup, RollupDoubleValuation; layer2_parent_in_double_valuation)
- `DoubleValuation`  (Sub-Schicht 3: double-valuation-specific —
  RollupCompatibility; rollup_doubleValuation_inheritance as Central Theorem 2)
- `Coalgebraic`     (Schicht-Vertiefung: first F1 belegung of the coalgebraic layer —
  fromRollupDoubleValuation, Stage 1/Stage 2/StageTransition 1 instances,
  coalgebraic_inheritance consistency theorem)

Methodological status: second F1 sub-belegung in the project (after
F1.D5.Polkadot). Builds on F1.D2.Hybrid via composition (base : HybridConsensus).
Does not import F1.D5 or F1.D5.Polkadot.

The two connection functions into the F3.a placeholders `compatibility`
(DoubleValuation) and `beckChevalley` (DesignativeRestriction) were removed in
the Phase-2 sharpening; both placeholders remain unfilled. What the series of
such fillings did and did not show is recorded once, in the memorial block of
`Rollups/DoubleValuation.lean`.

Two central theorems:
- `rollup_soundness_universal`: all four rollup families are structurally sound.
- `rollup_doubleValuation_inheritance`: formal form of layer-1/layer-2
  vertical asymmetry ("Layer-1 trägt, Layer-2 baut auf").

See F1_D2_Rollups_Spec.md, T12 V.
-/

namespace Reformulation.F1.D2.Rollups

-- Re-exports occur automatically via the imports above.

end Reformulation.F1.D2.Rollups
