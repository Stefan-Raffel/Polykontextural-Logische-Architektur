import Reformulation.F1.D2.Hybrid
import Reformulation.F1.D2.Rollups.Families
import Reformulation.F3a

/-!
# F1.D2.Rollups.RollupGeneral — Sub-layer 1: rollup-architecture-general

Introduces Layer1Chain, Layer2Rollup, and RollupDoubleValuation as the
general architectural types for layer-1/layer-2 stage iteration.

Structural content:
* `Layer1Chain` — layer-1 chain with hybrid consensus (block + epoch layer)
  via composition (base : HybridConsensus). Analogous to PolkadotMultiChain's
  base : MultiChain composition form.
* `Layer2Rollup` — layer-2 rollup: belongs to one of the four families,
  has a parent layer-1 chain, and inherits genesis (placeholder).
* `RollupDoubleValuation` — formal form of layer-1/layer-2 stage iteration
  as a double valuation. Three fields: layer1, layer2, and a provable
  inheritanceCompat predicate.
* `layer2_parent_in_double_valuation` — direct field-access theorem.
* `rollupDoubleValuation_family` — type-valued def extracting the rollup family.

Klasse-B adaptation (Risiko-Stelle 1 and 2): HybridConsensus carries
universe-polymorphic Type fields (softCategory, hardCategory), making
DecidableEq HybridConsensus unavailable. Consequently, DecidableEq
Layer1Chain and DecidableEq Layer2Rollup cannot be provided. These
instances are not required by any downstream code in this sub-belegung.

See F1_D2_Rollups_Spec.md §III.
-/

namespace Reformulation.F1.D2.Rollups.RollupGeneral

open Reformulation.F1.D2.Hybrid
open Reformulation.F1.D2.Rollups.Families
open Reformulation.F3a

/-- Layer-1 chain: a chain with hybrid consensus (block-layer plus epoch-layer)
that serves as the base for layer-2 rollups. The hybrid form provides the
hard finality that layer-2 rollups inherit. Bitcoin-style single-layer
consensus is not modeled here (degenerate form per T11 V; follow-on work).

Composition form: carries `base : HybridConsensus` (analogous to
PolkadotMultiChain's base : MultiChain). -/
structure Layer1Chain where
  base : HybridConsensus

/-- Layer-2 rollup: a sub-stage of computation that builds on a layer-1 chain
through stage iteration. Each layer-2 rollup belongs to one of the four
families and inherits its genesis from the layer-1 chain via layer-1 inclusion. -/
structure Layer2Rollup where
  family       : RollupFamily
  parentLayer1 : Layer1Chain
  /-- Inherited genesis: layer-2 inherits the genesis-singularity from
  layer-1 via the layer-1 inclusion. Placeholder per the prop_field : True
  convention; full form is follow-on work (concrete inclusion mechanism
  per family). -/
  inheritedGenesis : True

/-- Rollup double valuation: the formal form of layer-1/layer-2 stage iteration
as a double valuation. Three fields with substantial content; inheritanceCompat
is a provable predicate (Klasse-B form-binding), not a placeholder. -/
structure RollupDoubleValuation where
  layer1 : Layer1Chain
  layer2 : Layer2Rollup
  /-- Inheritance compatibility: layer-2's parent layer-1 equals the
  layer-1 of this double valuation. The formal form of "Layer-1 trägt,
  Layer-2 baut auf" — vertical asymmetry of stage iteration. -/
  inheritanceCompat : layer2.parentLayer1 = layer1

/-- Every rollup double valuation has its layer-2's parent equal to
its layer-1. Direct from inheritanceCompat field. -/
theorem layer2_parent_in_double_valuation (rdv : RollupDoubleValuation) :
    rdv.layer2.parentLayer1 = rdv.layer1 :=
  rdv.inheritanceCompat

/-- Rollup family of the layer-2 in a double valuation.
Type-valued: def, not theorem (per Arbeitsdisziplin c). -/
def rollupDoubleValuation_family (rdv : RollupDoubleValuation) :
    Reformulation.F1.D2.Rollups.Families.RollupFamily :=
  rdv.layer2.family

end Reformulation.F1.D2.Rollups.RollupGeneral
