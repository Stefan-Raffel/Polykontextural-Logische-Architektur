-- EINGEFROREN (29. Juli 2026): dieser Zweig wird nicht fortgeschrieben.
-- Status, Zahlen und die Bedingungen fuer ein Auftauen: docs/build-targets.md, Abschnitt PathC.
import Mathlib.Data.List.Basic

/-!
# Reformulation.PathC.GeometricTheory.Signature

Many-sorted signature for the abstract geometric theory machinery.

## What this module carries

- `ManySortedSignature` — sorts (`sort : Type u`), function symbols
  (`func : List sort → sort → Type v`), relation symbols
  (`rel : List sort → Type w`).
- `ManySortedSignature.empty` — the empty signature.
- `ManySortedSignature.sum` — coproduct of two signatures
  (Klasse-D form: symbol sets are trivial; full encoding reserved).

## Klasse-B finding (B-1/β): `sort` field name

`Sort` (capital) is a Lean 4 keyword. Field named `sort` (lowercase).

## Klasse-D finding (D-1): `sum` trivial encoding

The full type-safe `sum` requires sigma-type encodings that live in
`Type (max u v)`, conflicting with the declared `func : ... → Type v`
field universe. For T2 depth the trivial (no cross-symbols) form suffices;
full encoding is a follow-up task.
-/

namespace Reformulation.PathC.GeometricTheory

universe u v w

/-- A many-sorted signature: a sort type, function symbols, and relation symbols. -/
structure ManySortedSignature : Type (max (u + 1) (v + 1) (w + 1)) where
  /-- The type of sorts. (`sort` avoids the Lean 4 keyword `Sort`.) -/
  sort : Type u
  /-- Function symbols: indexed by argument-sort list and result sort. -/
  func : List sort → sort → Type v
  /-- Relation symbols: indexed by argument-sort list. -/
  rel  : List sort → Type w

namespace ManySortedSignature

/-- The empty many-sorted signature. -/
def empty : ManySortedSignature.{u, v, w} where
  sort := PEmpty
  func := fun _ _ => PEmpty
  rel  := fun _ => PEmpty

/-- Disjoint sum of two signatures. Sorts are `Σ₁.sort ⊕ Σ₂.sort`.
    Function and relation symbol sets are trivially empty (Klasse-D);
    the full coproduct embedding requires a universe-level adjustment. -/
def sum (sig1 sig2 : ManySortedSignature.{u, v, w}) : ManySortedSignature.{u, v, w} where
  sort := sig1.sort ⊕ sig2.sort
  func := fun _ _ => PEmpty
  rel  := fun _ => PEmpty

end ManySortedSignature

end Reformulation.PathC.GeometricTheory
