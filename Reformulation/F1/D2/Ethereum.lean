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
* `RollupFamily` — stage-2 rollup marker as Folge-Aufgabe placeholder.

The connection function to the F3.a `DoubleValuation.compatibility` placeholder
and the F1.D2 statement that consumed it were removed in the Phase-2 sharpening;
see the memorial block at the end of this module. The Gasper content that is
actually carried sits in `GasperCompatibility.noConflictingVotes`, a real
universal condition, and that field stays.

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

/-! ## Memorial block: declarations removed because their statement was `True`

Removed in the Phase-2 sharpening (Setzungsregister, `docs/status-register.md`).
The reason is the same in both cases: the name claimed content, the statement
was `True`. A theorem whose statement is `True` is not a false theorem, but its
name reads as a result; in a published tree that is a claim.

These two are the one measured consumer pair in the whole set: the theorem was
the only aggregate constant referencing the connection function, and it is
itself removed here. The pair goes together, and nothing else breaks.

Signatures are quoted indented by two spaces so that the counting routes
`^theorem` and `^def` do not count the memorial quote as a declaration.

**Removed 1 — `GasperCompatibility.toDoubleValuationCompat`.** Register `S43`.

```
  def GasperCompatibility.toDoubleValuationCompat
      {H : HybridConsensus} (_g : GasperCompatibility H) : True :=
    trivial
```

*What was claimed:* that Gasper compatibility fills the F3.a
`DoubleValuation.compatibility` placeholder — the fourth of the four F3.a
prop_field connections made explicit in F1.D2 (Spec §X).
*What a load-bearing statement would need:* the target field
`F3a.DoubleValuation.compatibility` (register row `S15`) must carry content
before anything can fill it; a function into `True` establishes no connection,
because every term of every type maps to `trivial`. With a contentful
`compatibility` field the connection becomes a real construction — from
`noConflictingVotes` one would have to build the datum the field demands — and
that construction can fail, which is what makes it worth writing down.

**Removed 2 — `gasper_inter_layer_compatible`.** Register `S42`.

```
  theorem gasper_inter_layer_compatible
      (H : HybridConsensus) (g : GasperCompatibility H) : True :=
    GasperCompatibility.toDoubleValuationCompat g
```

*What was claimed:* the central F1.D2 statement — that every Gasper-style hybrid
consensus satisfies the inter-layer compatibility of T11 IV.
*What a load-bearing statement would need:* an inter-layer compatibility that
can fail. The material is present and unused: `Vote.compatible` is a real
predicate, and `GasperCompatibility.noConflictingVotes` is a genuine universal
condition over it, not a placeholder. A statement with content would derive
something from that condition — for instance that no two votes of one validator
surround each other across an epoch boundary, which is the FFG-Lock property the
field is named for. The field `pullBackCompatibility : True` (register row `S04`)
is the part that remains a placeholder, and the T11 IV pull-back form remains
Folge-Aufgabe.
-/

end Reformulation.F1.D2.Ethereum
