import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype

/-
Reformulation Günthers — F3.b Variables

The three Boolean variables σ, β, υ determining a configuration in the
combinatorial tableau of T8 III.

Imports are limited to the minimum needed for `deriving Fintype` on
finite inductive types.
-/

namespace Reformulation.F3b

/--
Schema shape (σ).

A schema (V, E, S) is `trivial` when V is a singleton and E, S are empty.
Otherwise it is `nonTrivial`.

Architecture reference: clarification session §I, first variable.
-/
inductive SchemaShape where
  /-- Schema (V, E, S) is trivial: V singleton, E and S empty. -/
  | trivial
  /-- Schema (V, E, S) is non-trivial: at least one component carries
      structure beyond the trivial baseline. -/
  | nonTrivial
  deriving DecidableEq, Repr, Fintype

/--
Valuation profile (β).

A valuation ι is `constant` when all three of its components (vertex
valuation, edge valuation, marker resolution) carry the minimal,
designatively empty value. Otherwise it is `nonConstant`.

Architecture reference: clarification session §I, second variable.
-/
inductive Valuation where
  /-- Valuation is constant: all three components designatively empty. -/
  | constant
  /-- Valuation is non-constant: at least one component carries
      designative content. -/
  | nonConstant
  deriving DecidableEq, Repr, Fintype

/--
Sub-topos selection (υ).

A sub-topos selection is `present` when a proper sub-structure within
the contexture 𝒦 is chosen (sheaves over a distinguished site, locally
required compatibility conditions). Otherwise it is `absent` (𝒦 taken
as a whole topos component, without sub-selection).

Architecture reference: clarification session §I, third variable.
-/
inductive Subtopos where
  /-- No sub-topos selection: 𝒦 taken as whole topos component. -/
  | absent
  /-- Sub-topos selection made: a proper sub-structure within 𝒦
      is chosen. -/
  | present
  deriving DecidableEq, Repr, Fintype

end Reformulation.F3b
