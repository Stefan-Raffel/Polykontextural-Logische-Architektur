import Reformulation.F3a
import Reformulation.F3c.Operators
import Mathlib.Data.Finset.Basic

/-!
# F1.D2.ConsensusGeneral — Sub-layer 1: consensus-general types

Introduces the consensus-general data types and modal-operator schemata
that are common to any hybrid-consensus system. These types carry no
Ethereum-specific or hybrid-specific content; they serve as the base
layer imported by F1.D2.Hybrid and F1.D2.Ethereum.

Structural content:
* `Validator`, `ValidatorSet`, `Slot`, `Epoch`, `slotToEpoch` —
  the four basic consensus data types plus the slot-to-epoch conversion.
* `SoftConsensusOps` — modal-operators schema for soft-T7 (block-layer)
  consensus, wrapping F3.c `ModalOperators` with a soft-layer marker.
* `HardConsensusOps` — modal-operators schema for hard-T7 (epoch-layer)
  consensus, wrapping F3.c `ModalOperators` with a hard-layer marker.
* `softLayer_has_modalOps`, `hardLayer_has_modalOps` — connection defs
  making the F3.c modal-operators bundle explicit per layer.

Connection to F3.a invariant layer: `softLayer_has_modalOps` fills the
`beckChevalley` placeholder; `hardLayer_has_modalOps` fills `isFunctorial`
and `isUnique`. The fourth placeholder (`compatibility`) is filled in
F1.D2.Ethereum via `GasperCompatibility.toDoubleValuationCompat`.
`markerCompat` in F3.a.SchemaMorphism remains as placeholder.

See F1_D2_Spec.md §II (Sub-Schicht 1: Konsens-allgemein).
-/

namespace Reformulation.F1.D2.ConsensusGeneral

open CategoryTheory
open Reformulation.F3c

/-- Validator identity. Carries an abstract identifier without specifying
voting power, public keys, or slashing data — those are implementation-
specific and not part of the structural form. -/
structure Validator where
  id : ℕ
  deriving DecidableEq, Repr

/-- The validator set. Finite by construction (Mathlib Finset).
The 2/3-voting threshold can be expressed via cardinality. -/
abbrev ValidatorSet : Type := Finset Validator

/-- Time-index for the consensus iteration; refines into Slot/Epoch roles
depending on the layer. -/
abbrev Slot : Type := ℕ

/-- Epoch-index for the harder-finalization layer. -/
abbrev Epoch : Type := ℕ

/-- Conversion from Slot to Epoch given a slots-per-epoch constant. -/
def slotToEpoch (s : Slot) (slotsPerEpoch : ℕ) : Epoch :=
  s / slotsPerEpoch

/-- Modal-operators schema for a soft-T7 consensus layer (block-layer
style): τ as time-shift, δ as fork-choice-style reorganization, ω as
soft positing (probabilistic, reversible by δ in the next round).

Wraps F3.c `ModalOperators` with a soft-layer schicht-marker per
prop_field-True convention (T10 III: "abgeschwächte T7"). -/
structure SoftConsensusOps (𝒞 : Type*) [Category 𝒞] where
  /-- The base modal-operators bundle from F3.c. -/
  ops : ModalOperators 𝒞
  /-- Schicht-marker: soft-T7 (block-layer) consensus operator schema.
  Placeholder per prop_field-True convention. -/
  isSoftLayer : True

/-- Modal-operators schema for a hard-T7 consensus layer (epoch-layer
style): τ as commit-lock, δ as voting-aggregation, ω as deterministic
finalization (irreversible after threshold).

Wraps F3.c `ModalOperators` with a hard-layer schicht-marker per
prop_field-True convention (T10 III: "harte T7"). -/
structure HardConsensusOps (𝒞 : Type*) [Category 𝒞] where
  /-- The base modal-operators bundle from F3.c. -/
  ops : ModalOperators 𝒞
  /-- Schicht-marker: hard-T7 (epoch-layer) consensus operator schema.
  Placeholder per prop_field-True convention. -/
  isHardLayer : True

/-- Every soft-consensus layer has a modal-operators bundle.
Direct consequence of structure-class form; tautological.

Class B adjustment (def/theorem classification, Arbeitsdisziplin c):
return type `ModalOperators 𝒞` is in `Type*`, not `Prop` — must be
`def`, not `theorem`. Connection to F3.a: fills `beckChevalley`
placeholder in `DesignativeRestriction`. -/
def softLayer_has_modalOps {𝒞 : Type*} [Category 𝒞]
    (S : SoftConsensusOps 𝒞) : ModalOperators 𝒞 :=
  S.ops

/-- Every hard-consensus layer has a modal-operators bundle.
Direct consequence of structure-class form; tautological.

Class B adjustment (def/theorem classification, Arbeitsdisziplin c):
return type `ModalOperators 𝒞` is in `Type*`, not `Prop` — must be
`def`, not `theorem`. Connection to F3.a: fills `isFunctorial` and
`isUnique` placeholders in `OuterBalance` and `Skeleton`. -/
def hardLayer_has_modalOps {𝒞 : Type*} [Category 𝒞]
    (H : HardConsensusOps 𝒞) : ModalOperators 𝒞 :=
  H.ops

end Reformulation.F1.D2.ConsensusGeneral
