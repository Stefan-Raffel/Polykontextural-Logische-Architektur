import Mathlib.CategoryTheory.Discrete.Basic
import Reformulation.F3f.Stage
import Reformulation.F3f.StageTransition
import Reformulation.F3b.Configurations
import Reformulation.F3c.Operators
import Reformulation.F1.D2.Rollups.RollupGeneral

/-!
# F1.D2.Rollups.Coalgebraic — Rev2: Schicht-Vertiefung with genuine domain binding

Introduces `fromRollupDoubleValuation`, the construction function that maps
any `RollupDoubleValuation` to a triple of F3.f instances:

- `Stage.{1} 1` with `Discrete Layer1Chain` as total space and K1 as initial
  config (B5-anchoring, material-free).
- `Stage.{1} 2` with `Discrete Layer2Rollup` as total space and K2 as initial
  config (B6-anchoring, material-carrying).
- `StageTransition.{1} 1` linking the two stages via a constant translate.

Also introduces `coalgebraic_inheritance`, the Schicht-Vertiefung consistency
theorem with four aspects: both stageObj values and both initialConfig values
match the `RollupDoubleValuation` inputs and the K1/K2 anchoring.

## Rev2 over Rev1

Rev1 used `Discrete Unit` (Type 0) as a Klasse-B adaptation to work around
the missing universe polymorphism in F3.f-Rev1. With F3.f-Rev2 introducing
`universe u` for `Stage` and `StageTransition`, the full `Discrete Layer1Chain`
/ `Discrete Layer2Rollup` domain binding is now directly expressible via
`Stage.{1}` and `StageTransition.{1}` (Layer1Chain and Layer2Rollup live in
Type 1 because HybridConsensus carries a softCategory : Type field).

Key improvements:
- `totalSpace := Discrete Layer1Chain` (genuine domain, not placeholder Unit).
- `stageObj := Discrete.mk rdv.layer1` (uses rdv substantively; no workaround).
- `Stage.{1}` and `StageTransition.{1}` explicit universe annotation.
- `coalgebraic_inheritance` proves four-aspect consistency (stageObj + config).

Sparse-form retained from Rev1: end-functors are identity, γ is identity
morphism, translate is a constant function. Substantial constructions
(modally differentiated translate, non-trivial end-functors) are follow-up
tasks (C11/C12).

Architecture references: F1_D2_Rollups_Coalgebraic_Rev2_Spec.md §III–IV.
-/

namespace Reformulation.F1.D2.Rollups.Coalgebraic

open CategoryTheory
open Reformulation.F1.D2.Rollups.RollupGeneral

/--
Constructs Stage 1, Stage 2, and StageTransition 1 instances from a
RollupDoubleValuation. The L1 layer becomes Stage 1 (with K1 as the
B5 anchoring); the L2 rollup becomes Stage 2 (with K2 as the B6-anchoring).

This Rev2 form realizes the full Schicht-Vertiefung: the Stage instances
carry the actual Layer1Chain and Layer2Rollup values from the
RollupDoubleValuation, not generic Unit-typed placeholders.

The construction uses `Stage.{1}` and `StageTransition.{1}` (per F3.f-Rev2 /
F3.f-K4 Möglichkeit α), since Layer1Chain and Layer2Rollup live in Type 1
(due to category-valued fields in their underlying structures).

Sparse-form retained from Rev1: end-functors are identity, γ is
identity-morphism, translate is a constant function over all six
ModalSymbol values. Substantial constructions (modally differentiated
translate, non-trivial end-functors) are follow-up tasks (C11/C12).
-/
def fromRollupDoubleValuation (rdv : RollupDoubleValuation) :
    Reformulation.F3f.Stage.{1} 1 ×
    Reformulation.F3f.Stage.{1} 2 ×
    Reformulation.F3f.StageTransition.{1} 1 :=
  let stage1 : Reformulation.F3f.Stage.{1} 1 := {
    totalSpace := Discrete Layer1Chain
    cat := inferInstance
    stageObj := Discrete.mk rdv.layer1
    endenFunktor := 𝟭 _
    γ := 𝟙 _
    initialConfig := Reformulation.F3b.K.k1
    initialConfig_at_stage_1 := fun _ => rfl
    noAlgebraExtension := trivial
  }
  let stage2 : Reformulation.F3f.Stage.{1} 2 := {
    totalSpace := Discrete Layer2Rollup
    cat := inferInstance
    stageObj := Discrete.mk rdv.layer2
    endenFunktor := 𝟭 _
    γ := 𝟙 _
    initialConfig := Reformulation.F3b.K.k2
    initialConfig_at_stage_1 := fun h => absurd h (by decide)
    noAlgebraExtension := trivial
  }
  let transition : Reformulation.F3f.StageTransition.{1} 1 := {
    current := stage1
    next := stage2
    translate := fun _ => fun _ => stage2.stageObj
  }
  ⟨stage1, stage2, transition⟩

/--
The Rev2 Schicht-Vertiefungs-Konsistenz theorem: the coalgebraic-layer
construction agrees with the categorical-layer RollupDoubleValuation
in four aspects.

Stage-1 carries:
- the rdv.layer1 value (Layer1Chain) as stageObj (Discrete.mk rdv.layer1).
- K1 as initialConfig (B5 anchoring, material-free).

Stage-2 carries:
- the rdv.layer2 value (Layer2Rollup) as stageObj (Discrete.mk rdv.layer2).
- K2 as initialConfig (B6 anchoring, material-carrying).

The conjunction expresses the Schicht-Vertiefung: both schicht
niederlegungen (categorical via DoubleValuation, coalgebraic via
Stage/StageTransition) operate on the same belegung, with mutually
consistent initialization configurations.

Rev2 over Rev1: Rev1 proved only K1/K2 config consistency (stageObj was
unprovable because `Discrete Unit` doesn't carry rdv). Rev2 proves all four
aspects because the genuine domain binding `Discrete Layer1Chain/Layer2Rollup`
makes `stageObj = Discrete.mk rdv.layer1/2` directly derivable by `rfl`.
-/
theorem coalgebraic_inheritance (rdv : RollupDoubleValuation) :
    (fromRollupDoubleValuation rdv).1.stageObj = Discrete.mk rdv.layer1 ∧
    (fromRollupDoubleValuation rdv).2.1.stageObj = Discrete.mk rdv.layer2 ∧
    (fromRollupDoubleValuation rdv).1.initialConfig = Reformulation.F3b.K.k1 ∧
    (fromRollupDoubleValuation rdv).2.1.initialConfig = Reformulation.F3b.K.k2 :=
  ⟨rfl, rfl, rfl, rfl⟩

end Reformulation.F1.D2.Rollups.Coalgebraic
