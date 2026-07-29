import Mathlib.CategoryTheory.Functor.Basic
import Reformulation.F3b.Configurations

/-!
# F3.f.Stage — the coalgebraic stage structure (Rev2: universe-polymorphic)

This module introduces `Stage`, the central structure class of F3.f's first
layer. A `Stage n` represents a single stage of the coalgebraic architecture
(T1a IV–V): a locally fibered total-space category 𝒯 together with a stage
object 𝔖, an end-functor F : 𝒯 ⥤ 𝒯, and a coalgebra structure γ : 𝔖 ⟶ F(𝔖).

## Rev2 change: universe polymorphism (F3.f-K4 Möglichkeit α)

F3.f-K4 diagnosed a universe mismatch: `Layer1Chain : Type 1` (because
`HybridConsensus.softCategory : Type` forces `HybridConsensus : Type 1`).
The Rev1 form had `totalSpace : Type*` with `Stage` defaulting to universe 0,
making `Stage.{1}` inexpressible.

Rev2 introduces explicit universe polymorphism: `Stage.{u}` with
`totalSpace : Type u`. Standard usage:
- `Stage.{0}` for trivial domains (e.g., `Discrete Unit`).
- `Stage.{1}` for domains with category-valued fields (e.g., F1 domains
  where the structure type lives in Type 1 due to fields of sort Type 0).

## Architectural invariants

**Coalgebra vs. algebra.** γ : 𝔖 ⟶ F(𝔖) is a coalgebra structure
(self-observation, outward arrow), not an algebra structure F(𝔖) ⟶ 𝔖
(construction from outside). This is the Weg-B form (T1a V).

**Stage-local data only.** `Stage` carries only the data internal to stage n.
Transition data between stages n and n+1 lives in the separate `StageTransition`
class (K3-Verfeinerung: no self-reference in Stage).

**Stage-dependent end-functor.** Each `Stage` instance carries its own
`endenFunktor`. There is no global F : ∀ n, ... — the stage-dependence is the
structural content of the coalgebraic form. A global F would enable algebra
extensions, reintroducing globality (Verbot der Algebra-Lesart, T1a V).

**B5-anchoring.** Stage 1 carries the material-free K1-configuration
(initial singularity, B5). The `initialConfig_at_stage_1` field carries this
as an implication (n = 1 → initialConfig = .k1), so higher stages are
unconstrained in their configuration.

## F3.a anchor extension

For F1 belegungen wishing to track F3.a's three-functor decomposition
of the end-functor, see `Reformulation.F3f.StageWithF3aAnchor`. That
class extends `Stage` with three F3.a structural components plus a
schema-lift and consistency proof.

Belegungen without F3.a anchor instantiate `Stage` directly.

Architecture references: F3f_Spec §III, F3f_Implementation_Prompt §IV.2.
-/

namespace Reformulation.F3f

open CategoryTheory

universe u

/-- A single stage of the coalgebraic PKL architecture.

`Stage.{u} n` parameterizes over universe `u` and stage index `n : ℕ`.
The universe parameter allows F1 belegungen with category-valued domains
(Type 1) to use `Stage.{1}` directly, per F3.f-K4 Möglichkeit α.

Fields:

- `totalSpace`: the total-space category of this stage (the local
  double-fibration 𝒯; a type in universe `u` carrying a Category instance).
- `cat`: the Category instance for `totalSpace` (instance implicit).
- `stageObj`: the stage-object 𝔖 ∈ 𝒯 (the stage itself as object).
- `endenFunktor`: the end-functor F : 𝒯 ⥤ 𝒯; produces the stage's
  balance F(𝔖). Stage-dependent (no global F). Spec-Entscheidung 1:
  generic functor, no F3.a-dependency at the invariant layer.
- `γ`: the coalgebra structure 𝔖 ⟶ F(𝔖) (self-observation).
- `initialConfig`: the B5/K1-configuration for this stage.
- `initialConfig_at_stage_1`: for stage 1, `initialConfig = .k1`
  (material-free K1, B5-anchoring).
- `noAlgebraExtension`: `True` placeholder marking the architectural
  prohibition of the algebra reading (Spec-Entscheidung 2: prop_field-True).
-/
structure Stage (n : ℕ) where
  /-- Total-space category of this stage (the local double-fibration 𝒯). -/
  totalSpace : Type u
  /-- Category instance for totalSpace. -/
  [cat : Category totalSpace]
  /-- The stage-object 𝔖 : an object of totalSpace. -/
  stageObj : totalSpace
  /-- End-functor F : totalSpace ⥤ totalSpace.
  Stage-dependent; each Stage instance carries its own F.
  Spec-Entscheidung 1: generic functor (no F3.a EndenFunktor dependency). -/
  endenFunktor : totalSpace ⥤ totalSpace
  /-- Coalgebra structure: self-observation γ : 𝔖 ⟶ F(𝔖).
  This is the outward arrow of the coalgebra (Weg B, T1a V). -/
  γ : stageObj ⟶ endenFunktor.obj stageObj
  /-- B5/K1 anchoring: the configuration for this stage. -/
  initialConfig : Reformulation.F3b.K
  /-- Stage-1 special condition: stage 1 carries K1 (material-free,
  initial singularity, B5). Vacuously satisfied for n ≠ 1. -/
  initialConfig_at_stage_1 : n = 1 → initialConfig = Reformulation.F3b.K.k1
  /-- Algebra-extension prohibition (architectural marker, prop_field-True).
  The end-functor is stage-local; there is no global stacking operator.
  A global F would enable algebra extensions and reintroduce globality
  (Verbot der Algebra-Lesart: T1a V, Reformulierung_Sitzungsergebnis IV).
  **Placeholder** (register row `S27`): exit is a non-existence theorem — no
  global stacking operator extends the stage-local end-functors coherently
  across stages. That is statable and provable; the marker defers it. Read as
  placeholder and not as constitutive precisely because that exit criterion
  exists and is named: a constitutive positing carries no proof duty at all. -/
  noAlgebraExtension : True

end Reformulation.F3f
