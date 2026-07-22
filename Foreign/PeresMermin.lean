import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card

-- Full enumeration over the 512 assignments needs a deeper reduction stack than
-- the default; this affects compilation only, not the axiom profile.
set_option maxRecDepth 100000

/-!
# Foreign.PeresMermin — the Peres–Mermin square, smallest case

This is a self-contained formalization of a small, long-known result: the
**Peres–Mermin square** from the theory of quantum contextuality. Nine
observables are arranged in a 3×3 grid; six *contexts* (three rows, three
columns) each fix a target product of their three entries. The classical fact,
known for decades, is that **no single global assignment of ±1 values to the
nine observables can meet all six context conditions at once**, even though each
context is individually satisfiable and any five of the six can be met together.

This module builds that fact in its smallest deterministic (`±1`-valued) case. It
is **not** a contribution to the quantum-foundations debate, and it draws **no**
connection to any theory beyond the Peres–Mermin square itself. It is a plain
enumeration result over the 512 assignments.

## Encoding

Values are `Bool`, with `true` carrying the sign `-1` and `false` the sign `+1`.
The product of three observables is `+1` iff the exclusive-or of their three bits
is `false`, and `-1` iff the exclusive-or is `true`. An assignment is therefore a
function `Fin 9 → Bool`, of which there are exactly 512.

The grid indices:
```
0  1  2
3  4  5
6  7  8
```
-/

namespace Foreign.PeresMermin

/-- A context: three grid positions and the required exclusive-or of their bits.
`target = false` encodes a required product of `+1`; `target = true` encodes `-1`. -/
structure Context where
  a : Fin 9
  b : Fin 9
  c : Fin 9
  target : Bool
  deriving DecidableEq

/-- The six contexts of the square, indexed by `Fin 6`: three rows (products `+1`)
then three columns (products `+1`, `+1`, `-1`). -/
def context : Fin 6 → Context
  | 0 => ⟨0, 1, 2, false⟩   -- row 1
  | 1 => ⟨3, 4, 5, false⟩   -- row 2
  | 2 => ⟨6, 7, 8, false⟩   -- row 3
  | 3 => ⟨0, 3, 6, false⟩   -- column 1
  | 4 => ⟨1, 4, 7, false⟩   -- column 2
  | 5 => ⟨2, 5, 8, true⟩    -- column 3

/-- An assignment satisfies a context when the exclusive-or of the three assigned
bits equals the context's target. -/
def sat (v : Fin 9 → Bool) (ctx : Context) : Bool :=
  (v ctx.a ^^ v ctx.b ^^ v ctx.c) == ctx.target

/-- The number of contexts that an assignment satisfies (between `0` and `6`). -/
def numSat (v : Fin 9 → Bool) : Nat :=
  ((List.finRange 6).filter (fun i => sat v (context i))).length

/-- An assignment is *global* when it satisfies every one of the six contexts.
Reducible so that the `Decidable` instance for the bounded quantifier is found. -/
@[reducible] def satisfiesAll (v : Fin 9 → Bool) : Prop :=
  ∀ i : Fin 6, sat v (context i) = true

-- ============================================================
-- The theorems
-- ============================================================

/-- **(a) No global assignment.** No assignment of bits to the nine positions
satisfies all six context conditions simultaneously. -/
theorem no_global_assignment : ¬ ∃ v : Fin 9 → Bool, satisfiesAll v := by
  decide

/-- **(b) Local satisfiability.** Each individual context is, on its own,
satisfiable by some assignment. -/
theorem each_context_satisfiable :
    ∀ i : Fin 6, ∃ v : Fin 9 → Bool, sat v (context i) = true := by
  decide

/-- **(c) Nontriviality.** There is an assignment satisfying **five** of the six
contexts. The all-`+1` assignment meets every row and the first two columns,
failing only the third column. -/
theorem five_of_six_satisfiable : ∃ v : Fin 9 → Bool, numSat v = 5 :=
  ⟨fun _ => false, by decide⟩

/-- **The ceiling.** No assignment satisfies more than five contexts. Together
with `five_of_six_satisfiable` this pins the maximum simultaneously satisfiable
count at exactly five. -/
theorem numSat_le_five : ∀ v : Fin 9 → Bool, numSat v ≤ 5 := by
  decide

/-- **(d) The count.** Exactly 96 of the 512 assignments satisfy precisely five
of the six contexts. -/
theorem count_five_of_six :
    (Finset.univ.filter (fun v : Fin 9 → Bool => numSat v = 5)).card = 96 := by
  decide

-- ============================================================
-- (e) The local family and (f) its non-gluability
-- ============================================================

/-- **(e) A local family — one assignment per context, each meeting its own.**
For the five `+1`-target contexts the all-`+1` assignment works; for the third
column (target `-1`) the assignment that flips position `2` alone works.
Constructed explicitly, not postulated. -/
def localFamily : Fin 6 → (Fin 9 → Bool)
  | 0 => fun _ => false
  | 1 => fun _ => false
  | 2 => fun _ => false
  | 3 => fun _ => false
  | 4 => fun _ => false
  | 5 => fun j => j == 2

/-- Each member of the local family satisfies its own context. -/
theorem local_family_satisfies :
    ∀ i : Fin 6, sat (localFamily i) (context i) = true := by
  decide

/-- A candidate global assignment *agrees with* the `i`-th local assignment on
the `i`-th context when it matches it on that context's three positions. -/
def AgreesWith (v : Fin 9 → Bool) (i : Fin 6) : Prop :=
  v (context i).a = localFamily i (context i).a ∧
  v (context i).b = localFamily i (context i).b ∧
  v (context i).c = localFamily i (context i).c

/-- Agreement on a context's three positions transfers that context's
satisfaction from the local assignment to the global candidate. -/
theorem sat_of_agrees {v : Fin 9 → Bool} {i : Fin 6} (h : AgreesWith v i) :
    sat v (context i) = true := by
  have : sat v (context i) = sat (localFamily i) (context i) := by
    simp only [sat, h.1, h.2.1, h.2.2]
  rw [this]; exact local_family_satisfies i

/-- **(f) Non-gluability.** No global assignment agrees with every member of the
local family on that member's context. Immediate from `no_global_assignment`:
agreement everywhere would make the candidate global. -/
theorem local_family_not_gluable :
    ¬ ∃ v : Fin 9 → Bool, ∀ i : Fin 6, AgreesWith v i := by
  rintro ⟨v, hv⟩
  exact no_global_assignment ⟨v, fun i => sat_of_agrees (hv i)⟩

-- ============================================================
-- Calibration checks (full enumeration over the 512 assignments)
-- ============================================================

/-- There are exactly 512 assignments. -/
theorem card_assignments : Fintype.card (Fin 9 → Bool) = 512 := by
  decide

/-- Exactly 0 assignments satisfy all six contexts. -/
theorem count_six_satisfiable :
    (Finset.univ.filter (fun v : Fin 9 → Bool => numSat v = 6)).card = 0 := by
  decide

end Foreign.PeresMermin

-- ============================================================
-- Guards — measured axiom profile per theorem (kept separate from the
-- aggregate guard inventory; this module is outside the aggregate).
-- ============================================================

open Foreign.PeresMermin in
section

/-- info: 'Foreign.PeresMermin.no_global_assignment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms no_global_assignment

/-- info: 'Foreign.PeresMermin.each_context_satisfiable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms each_context_satisfiable

/-- info: 'Foreign.PeresMermin.five_of_six_satisfiable' depends on axioms: [propext] -/
#guard_msgs in #print axioms five_of_six_satisfiable

/-- info: 'Foreign.PeresMermin.numSat_le_five' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms numSat_le_five

/-- info: 'Foreign.PeresMermin.count_five_of_six' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms count_five_of_six

/-- info: 'Foreign.PeresMermin.local_family_satisfies' depends on axioms: [propext] -/
#guard_msgs in #print axioms local_family_satisfies

/-- info: 'Foreign.PeresMermin.sat_of_agrees' depends on axioms: [propext] -/
#guard_msgs in #print axioms sat_of_agrees

/-- info: 'Foreign.PeresMermin.local_family_not_gluable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms local_family_not_gluable

/-- info: 'Foreign.PeresMermin.card_assignments' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms card_assignments

/-- info: 'Foreign.PeresMermin.count_six_satisfiable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms count_six_satisfiable

end
