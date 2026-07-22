import Reformulation.F3a.Stage
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Function.Basic

/-!
# F3.a.SchemaMorphism — schema (V, E, S) and schema morphisms

This module introduces:

* `Schema`: the data structure (V, E, S) for a schema in stage `n` —
  positions V, connections E ⊆ V × V, self-reference markers S ⊆ V.
* `SchemaMorphism`: a morphism between schemas with three compatibility
  conditions — position function, connection compatibility, marker
  compatibility (preserves the Modus-3 character).
* `schema_marker_preserved`: the marker preservation theorem (direct
  from the `markerCompatibility` field).

See F3a_Klaerung_1.md §III, F3a_Klaerung_2.md §III, F3a_Klaerung_3.md §IV,
F3a_Spec.md §IV.
-/

namespace Reformulation.F3a

/-- The schema (V, E, S) data structure for a stage `n`:

* `positions`: the set V of positions.
* `connections`: the set E ⊆ V × V of connections between positions.
* `selfReferenceMarkers`: the set S ⊆ V of positions carrying
  self-reference markers (Modus-3 character).

The stage index `n` is carried as a structure parameter; the concrete
form of the schema (size of V, structure of E, distribution of S) is
stage-modulated material (Klärung 3 §IV.2).
-/
structure Schema (n : Stage) where
  positions : Type*
  connections : Set (positions × positions)
  selfReferenceMarkers : Set positions

/-- A schema morphism from `S₁` (in stage `n`) to `S₂` (in stage `m`)
consists of:

* `positionFun`: a function from `S₁.positions` to `S₂.positions`.
* `connectionFunCompatible`: connections are mapped consistently —
  if `(p, q) ∈ S₁.connections`, then
  `(positionFun p, positionFun q) ∈ S₂.connections`.
* `markerCompatibility`: marker compatibility — a position is a marker
  in `S₁` if and only if its image under `positionFun` is a marker in
  `S₂`. This biconditional enforces preservation of the Modus-3
  character (Klärung 1 §III.1).
-/
structure SchemaMorphism {n m : Stage} (S₁ : Schema n) (S₂ : Schema m) where
  positionFun : S₁.positions → S₂.positions
  connectionFunCompatible :
    ∀ p q, (p, q) ∈ S₁.connections →
      (positionFun p, positionFun q) ∈ S₂.connections
  markerCompatibility :
    ∀ p, p ∈ S₁.selfReferenceMarkers ↔
      positionFun p ∈ S₂.selfReferenceMarkers

/-- Marker preservation under a schema morphism. Direct consequence of
the `markerCompatibility` field of `SchemaMorphism`. -/
theorem schema_marker_preserved
    {n m : Stage} {S₁ : Schema n} {S₂ : Schema m}
    (φ : SchemaMorphism S₁ S₂) (p : S₁.positions) :
    p ∈ S₁.selfReferenceMarkers ↔
      φ.positionFun p ∈ S₂.selfReferenceMarkers :=
  φ.markerCompatibility p

end Reformulation.F3a
