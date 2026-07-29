import Mathlib.CategoryTheory.Functor.Basic
import Reformulation.F3c.Operators
import Reformulation.F3f.StageTransition
import Reformulation.F3g.Availability

/-!
# F3.g.Classification — StageTransitionWithB6Trace and B6-derivability from B2

Introduces `StageTransitionWithB6Trace`: an extension of `StageTransition`
with an explicit B6-trace field `omega_initialises_next`, formalising that
the next stage's stageObj arises via ω-translation from the predecessor
stage's balance.

Carries Theorem 4 (`b6_from_b2`: trivial replay of the field) and one
characterisation theorem for ω-transitions in the extended structure. A second
characterisation statement was removed in the Phase-2 sharpening; see the
memorial block at the end of this module.

## Klasse-B adaptation: `stageBalance` helper

The spec's `omega_initialises_next` field writes
`current.endenFunktor.obj current.stageObj` directly. Lean fails to
synthesize `Category current.totalSpace` at field-type elaboration time
because `current.cat` (stored inside `Stage`) is not in the local
instance context. Fix: private helper `stageBalance` brings `s.cat` in
scope via `letI` (tactic mode), producing the balance `s.endenFunktor.obj
s.stageObj`. Definitionally transparent; the semantic form is unchanged.

Architecture reference: F3g_Spec §IV, §VI.3.
-/

namespace Reformulation.F3g

open CategoryTheory Reformulation.F3f Reformulation.F3c

universe u

/-- The balance of a stage: end-functor applied to the stage object.

`stageBalance s = s.endenFunktor.obj s.stageObj : s.totalSpace`.

Private helper needed because `s.cat : Category s.totalSpace` is a
record field of `s`, not in the local typeclass instance context.
`letI` brings it in scope so `.obj` can be elaborated. -/
private def stageBalance {n : ℕ} (s : Stage.{u} n) : s.totalSpace := by
  letI : Category s.totalSpace := s.cat
  exact s.endenFunktor.obj s.stageObj

/-- Extension of `StageTransition` with an explicit B6-trace field.

The `omega_initialises_next` field formally carries the B6 content
(iterated initialisation from B2): the successor stage's stageObj is
ω-initialised from the balance of the current stage.

F1 belegungen that substantively carry B6 instantiate this structure
instead of `StageTransition` directly.

Architecture reference: F3g_Spec §IV.1.
-/
structure StageTransitionWithB6Trace (n : ℕ) extends StageTransition.{u} n where
  /-- B6-trace: the next stage's stageObj arises by ω-translation from
  the end-functor image of the current stage's stageObj.

  Form: `next.stageObj = translate ω (stageBalance current)`, where
  `stageBalance current = current.endenFunktor.obj current.stageObj`.
  The Klasse-B helper `stageBalance` is needed to bring `current.cat`
  into the instance context for field-type elaboration. -/
  omega_initialises_next :
    next.stageObj =
      translate ModalSymbol.omega (stageBalance current)

-- Theorem 4 — B6 from B2

/-- B6 from B2: the `omega_initialises_next` field carries the full content.
The proof is a replay of the field; the mathematical substance is in the
field's form, not in this theorem. -/
theorem b6_from_b2 (n : ℕ) (t : StageTransitionWithB6Trace.{u} n) :
    t.next.stageObj =
      t.translate ModalSymbol.omega (stageBalance t.current) :=
  t.omega_initialises_next

-- Characterisation theorems

/-- Every ω-transition formalised by a `StageTransitionWithB6Trace` is
initialising: `ClassIVSubtype.initialising` is in the available ClassIV
subtypes for the successor stage (n + 1). -/
theorem classifyOmegaTransition_initialising
    (n : ℕ) (h : n ≥ 1) (_t : StageTransitionWithB6Trace.{u} n) :
    ClassIVSubtype.initialising ∈ (classIVSubtype (n + 1)).getD ∅ := by
  cases n with
  | zero  => omega
  | succ k => simp [classIVSubtype]

/-! ## Memorial block: declaration removed because its statement was `True`

Removed in the Phase-2 sharpening (Setzungsregister, `docs/status-register.md`).
The name claimed content, the statement was `True`. A theorem whose statement is
`True` is not a false theorem, but its name reads as a result; in a published
tree that is a claim. No consumer in the aggregate; the removal breaks nothing.

Signature quoted indented by two spaces so that the counting route `^theorem`
does not count the memorial quote as a declaration.

**Removed — `continuing_not_in_stage_transition`.** Register row `S41`.

```
  theorem continuing_not_in_stage_transition (_n : ℕ) : True := True.intro
```

*What was claimed:* that the continuing ω-transition does not live in a
`StageTransitionWithB6Trace` but inside a stage, in the total-space category —
a placement claim, and the distinction it draws is the point of the section.
*What a load-bearing statement would need:* the removed version said so only in
its doc-string, and its own doc-string admitted as much. What is missing is the
link from the structure to the classification. `classIVSubtype (n+1)` returns
`{initialising, continuing}` — both subtypes are available at every stage above
1, so no membership statement can carry the claim; the neighbouring theorem
`classifyOmegaTransition_initialising` states such a membership and does not
use its `StageTransitionWithB6Trace` argument either. A load-bearing form needs
a classifying function `StageTransitionWithB6Trace n → ClassIVSubtype`, read off
the `omega_initialises_next` datum, and then says: that function never returns
`continuing`. Only with the function in place does the placement claim become
an equation that can fail.
-/

end Reformulation.F3g
