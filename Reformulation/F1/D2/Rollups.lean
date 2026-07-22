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
  RollupCompatibility; toDoubleValuationCompat and toBeckChevalley as
  third belegungen; rollup_doubleValuation_inheritance as Central Theorem 2)
- `Coalgebraic`     (Schicht-Vertiefung: first F1 belegung of the coalgebraic layer —
  fromRollupDoubleValuation, Stage 1/Stage 2/StageTransition 1 instances,
  coalgebraic_inheritance consistency theorem)

Methodological status: second F1 sub-belegung in the project (after
F1.D5.Polkadot). Builds on F1.D2.Hybrid via composition (base : HybridConsensus).
Does not import F1.D5 or F1.D5.Polkadot.

Three-fold belegung of F3.a placeholders (first occurrence in project):
- `compatibility` (DoubleValuation): third belegung via
  `RollupDoubleValuation.toDoubleValuationCompat` (vertical-asymmetric stage
  iteration; after F1.D2.Ethereum and F1.D5.Polkadot.DoubleValuation).
- `beckChevalley` (DesignativeRestriction): third belegung via
  `RollupCompatibility.toBeckChevalley` (stage-verification pull-back;
  after F1.D5.IBC and F1.D5.Polkadot.XCM).

Two central theorems:
- `rollup_soundness_universal`: all four rollup families are structurally sound.
- `rollup_doubleValuation_inheritance`: formal form of layer-1/layer-2
  vertical asymmetry ("Layer-1 trägt, Layer-2 baut auf").

See F1_D2_Rollups_Spec.md, T12 V.
-/

namespace Reformulation.F1.D2.Rollups

-- Re-exports occur automatically via the imports above.

end Reformulation.F1.D2.Rollups
