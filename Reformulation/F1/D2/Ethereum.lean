import Reformulation.F1.D2.ConsensusGeneral
import Reformulation.F1.D2.Hybrid
import Reformulation.F3a
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic

/-!
# F1.D2.Ethereum — Sub-layer 3: Ethereum-specific (Gasper pilot)

Introduces the Ethereum/Gasper-specific types and the central F1.D2
theorem: Gasper as hybrid-consensus belegung with FFG-Lock securing
the inter-layer compatibility.

Structural content:
* `Block`, `Checkpoint`, `Vote`, `Vote.compatible` — the four Ethereum
  consensus data types; Block uses non-recursive parent form (see below).
* `GasperCompatibility` — the central Gasper inter-layer compatibility
  structure with `noConflictingVotes` (real universal condition) and
  `pullBackCompatibility` (placeholder).
* `GasperCompatibility.toDoubleValuationCompat` — connection function to
  F3.a `DoubleValuation.compatibility` placeholder (fourth of the four
  F3.a prop_field connections made explicit in F1.D2).
* `RollupFamily` — stage-2 rollup marker as Folge-Aufgabe placeholder.
* `gasper_inter_layer_compatible` — central F1.D2 theorem (True form).

Class B adjustments applied:
* `Block.parent` — spec uses recursive `Option Block`; replaced by
  `Option BlockId` (= `Option ℕ`) per spec Risiko-Stelle 1 alternative.
  Recursive structures cannot derive `DecidableEq` in Lean 4.
* Manual `DecidableEq Checkpoint` instance — `isEpochBoundary : True`
  is a Prop field; `proof_irrel` handles the True-equality in the instance.

See F1_D2_Spec.md §IV (Sub-Schicht 3: Ethereum-spezifisch), T11 IV.
-/

namespace Reformulation.F1.D2.Ethereum

open Reformulation.F3a
open Reformulation.F1.D2.ConsensusGeneral
open Reformulation.F1.D2.Hybrid

/-- Block identifier as a natural number (block-tree index).
Alternative form for `Block.parent` per spec Risiko-Stelle 1:
the recursive `parent : Option Block` structure form cannot derive
`DecidableEq` in Lean 4 (circular instance). -/
abbrev BlockId : Type := ℕ

/-- Block in Gasper. Non-recursive parent form: parent is referenced by
`BlockId` (ℕ) rather than embedded inline. `none` for the genesis block.

Spec Risiko-Stelle 1 alternative (Class B adjustment): the recursive
`parent : Option Block` would require a circular `DecidableEq` derivation
which Lean 4's `deriving` handler does not support. -/
structure Block where
  slot     : Slot
  blockId  : BlockId
  parent   : Option BlockId
  proposer : Validator
  deriving DecidableEq, Repr

/-- Checkpoint: a block at the boundary of an epoch.

`isEpochBoundary : True` is a schicht-marker per prop_field-True
convention: the full boundary condition (`block.slot % slotsPerEpoch = 0`)
requires a deployment-specific `slotsPerEpoch` parameter not modelled
in F1.D2 (Folge-Aufgabe). -/
structure Checkpoint where
  block          : Block
  epoch          : Epoch
  isEpochBoundary : True

/-- Manual `DecidableEq` instance for `Checkpoint`.

The `block` and `epoch` fields are decided by their derived instances.
The `isEpochBoundary : True` field is handled by `proof_irrel`: any two
proofs of a `Prop` are propositionally equal (proof irrelevance axiom). -/
instance : DecidableEq Checkpoint := fun c₁ c₂ =>
  if hb : c₁.block = c₂.block then
    if he : c₁.epoch = c₂.epoch then
      isTrue (by
        obtain ⟨b₁, e₁, t₁⟩ := c₁
        obtain ⟨b₂, e₂, t₂⟩ := c₂
        subst hb; subst he; rfl)
    else isFalse fun h => he (congrArg Checkpoint.epoch h)
  else isFalse fun h => hb (congrArg Checkpoint.block h)

/-- FFG attestation (vote): a validator votes for a target checkpoint with
a source checkpoint as justification reference. -/
structure Vote where
  voter  : Validator
  source : Checkpoint
  target : Checkpoint
  deriving DecidableEq

/-- Compatibility between two votes in the FFG-Lock sense.
Two votes are compatible if they avoid FFG-style conflicts:
either from different voters, or with identical source-target pair,
or with non-overlapping epoch intervals (non-surround condition). -/
def Vote.compatible (v₁ v₂ : Vote) : Prop :=
  v₁.voter ≠ v₂.voter ∨
  (v₁.source = v₂.source ∧ v₁.target = v₂.target) ∨
  (v₁.target.epoch ≤ v₂.source.epoch) ∨
  (v₂.target.epoch ≤ v₁.source.epoch)

/-- Gasper inter-layer compatibility as a hybrid form.

* `noConflictingVotes`: engineering form — no validator casts conflicting
  votes. This is the FFG-Lock guarantee from the slashing assumption.
  A real universal condition (not a True placeholder): a concrete Gasper
  instance must provide the proof from its slashing axioms.
* `pullBackCompatibility`: structural form — pull-back compatibility per
  T11 IV. Placeholder per prop_field-True convention; the full pull-back
  form (connection to the double-fibration 𝒯 → 𝒞 × 𝒪) is Folge-Aufgabe.

Parameterised by `H : HybridConsensus` to carry the layer information. -/
structure GasperCompatibility (H : HybridConsensus) where
  /-- FFG-Lock: no validator produces two mutually incompatible votes. -/
  noConflictingVotes    : ∀ v₁ v₂ : Vote, Vote.compatible v₁ v₂
  /-- Pull-back compatibility (T11 IV placeholder). -/
  pullBackCompatibility : True

/-- Connection to F3.a `DoubleValuation.compatibility` placeholder.

This is the fourth (and final) of the four F3.a prop_field connections
made explicit in F1.D2 (Spec §X):
- `softLayer_has_modalOps`      → `DesignativeRestriction.beckChevalley`
- `hardLayer_has_modalOps`      → `OuterBalance.isFunctorial`, `Skeleton.isUnique`
- `toDoubleValuationCompat`     → `DoubleValuation.compatibility`
- `markerCompat` (SchemaMorphism) remains as placeholder.

The function is trivial in the True-form but makes the schicht-transition
from F1.D2 to F3.a structurally explicit. -/
def GasperCompatibility.toDoubleValuationCompat
    {H : HybridConsensus} (_g : GasperCompatibility H) : True :=
  trivial

/-- The four rollup families, identified in T12 V as the stage-2
sub-stratum specialization for the Ethereum consensus belegung.

Marker presence only; full belegung in F1.D2.Rollups (Folge-Aufgabe).
`RollupFamily.stageIndex` marks these as Stufe-2 material (Valuation 1). -/
inductive RollupFamily : Type where
  | optimistic
  | zk
  | sovereign
  | validium
  deriving DecidableEq, Repr

/-- Rollups belong to stage 2 (`Valuation 1` in F3.a stage-form).
The concrete belegung per family is in F1.D2.Rollups (Folge-Aufgabe). -/
def RollupFamily.stageIndex : RollupFamily → Stage :=
  fun _ => 1

/-- Central F1.D2 theorem: every Gasper-style hybrid consensus (carrying
`HybridConsensus` structure plus a `GasperCompatibility` witness) satisfies
the inter-layer compatibility from T11 IV.

The True-form is tautological; the architectural content is carried by the
connection to `DoubleValuation.compatibility` via `toDoubleValuationCompat`.
The non-tautological sharpening (full pull-back form) is Folge-Aufgabe.

Central F1.D2 statement: Ethereum-Gasper realises the F3.a `DoubleValuation`
form with `GasperCompatibility` as the concrete compatibility belegung. -/
theorem gasper_inter_layer_compatible
    (H : HybridConsensus) (g : GasperCompatibility H) : True :=
  GasperCompatibility.toDoubleValuationCompat g

end Reformulation.F1.D2.Ethereum
