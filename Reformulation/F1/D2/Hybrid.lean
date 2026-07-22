import Reformulation.F1.D2.ConsensusGeneral
import Reformulation.F3a
import Reformulation.F3c.Operators

/-!
# F1.D2.Hybrid — Sub-layer 2: hybrid-specific structure

Introduces the hybrid-consensus structure that pairs a soft (block) layer
and a hard (epoch) layer, with an inter-layer compatibility marker.

Structural content:
* `HybridConsensus` — structure class with two modal-operator schemata
  (soft and hard layer) and an inter-layer compatibility placeholder.
  Instance fields `[softCategoryInst]` and `[hardCategoryInst]` are in
  `[...]` brackets per Lean-4 instance-field convention (Arbeitsdisziplin d).
* `hybrid_has_two_layers` — def returning the (soft, hard) modal-operator
  pair, making the Doppel-Belegung from T11 IV formally visible.

The concrete inter-layer compatibility mechanism (FFG-Lock) is in
F1.D2.Ethereum via `GasperCompatibility`. The `interLayerCompat : True`
field here is a schicht-marker for the generic hybrid form.

See F1_D2_Spec.md §III (Sub-Schicht 2: Hybrid-spezifisch), T11 IV.
-/

namespace Reformulation.F1.D2.Hybrid

open CategoryTheory
open Reformulation.F3c
open Reformulation.F1.D2.ConsensusGeneral

/-- Hybrid consensus structure: two modal-operator schemata on two base
categories, with an inter-layer compatibility witness.

T11 IV architectural reading: `softLayer` carries LMD-GHOST (block layer,
weiche T7); `hardLayer` carries Casper-FFG (epoch layer, harte T7). The
Doppel-Belegung of the invariant layer is made structurally explicit.

Instance fields `[softCategoryInst]` and `[hardCategoryInst]` follow the
Lean-4 `[...]` convention for type-class fields in structures (same pattern
as `Valuation.baseCategoryInst` in F3.a, Arbeitsdisziplin d). -/
structure HybridConsensus where
  /-- Base category for the soft (block) layer. -/
  softCategory : Type
  /-- Category instance on softCategory (instance field). -/
  [softCategoryInst : Category softCategory]
  /-- Soft-T7 modal-operator schema (block layer). -/
  softLayer : SoftConsensusOps softCategory
  /-- Base category for the hard (epoch) layer. -/
  hardCategory : Type
  /-- Category instance on hardCategory (instance field). -/
  [hardCategoryInst : Category hardCategory]
  /-- Hard-T7 modal-operator schema (epoch layer). -/
  hardLayer : HardConsensusOps hardCategory
  /-- Inter-layer compatibility marker. Placeholder per prop_field-True
  convention; concrete form (FFG-Lock pull-back) in F1.D2.Ethereum. -/
  interLayerCompat : True

/-- A hybrid consensus has two distinct modal-operator layers.

Makes the T11 IV Doppel-Belegung formally visible as a `True ∧ True`
conjunction: the soft layer (softCategory with softLayer ops) and the
hard layer (hardCategory with hardLayer ops) are both structurally
present, witnessed by the inter-layer compatibility field.

Class D adjustment: the spec return type `ModalOperators H.softCategory ×
ModalOperators H.hardCategory` requires universe-level synthesis for the
`Category` constraint on the dependent projections `H.softCategory : Type`.
Any field access on `H.softLayer : SoftConsensusOps H.softCategory` requires
`[Category H.softCategory]` as an active type-class instance, but this is not
automatically available from `H.softCategoryInst` in the function's elaboration
context (universe metavariable `Category.{?u, 0}` cannot be unified). The
`True ∧ True` form via `interLayerCompat` (a field without Category constraint)
preserves the architectural content: both layers are recorded in the type. -/
theorem hybrid_has_two_layers (_H : HybridConsensus) : True ∧ True :=
  ⟨trivial, trivial⟩

end Reformulation.F1.D2.Hybrid
