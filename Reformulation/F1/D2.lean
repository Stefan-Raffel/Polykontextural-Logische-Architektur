import Reformulation.F1.D2.ConsensusGeneral
import Reformulation.F1.D2.Hybrid
import Reformulation.F1.D2.Ethereum
import Reformulation.F1.D2.Rollups

/-!
# F1.D2 — aggregate for the consensus-domain belegung (Ethereum-Gasper + Rollups)

Re-exports the sub-layers of F1.D2:
- `ConsensusGeneral` (Sub-Schicht 1: consensus-general types)
- `Hybrid`           (Sub-Schicht 2: hybrid-specific structure)
- `Ethereum`         (Sub-Schicht 3: Ethereum/Gasper-specific)
- `Rollups`          (Sub-Belegung: rollup-architecture, four families,
                      layer-1/layer-2 stage iteration asymmetry)
-/
