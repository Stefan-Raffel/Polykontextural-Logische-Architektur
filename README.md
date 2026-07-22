# Reformulation — Lean 4 / Mathlib formalisation

This is the Lean-4 formal accompaniment to the Günther reformulation
project. It now contains both completed F3 sub-modules:

* **F3.b** — Combinatorial tableau of the four-class transition
  classification. Eight configurations over three Boolean variables
  (σ, β, υ); four canonical bearers, four degeneration/combination
  cases; three exhaustion theorems plus a combined statement.
  Verified previously with 621 build jobs on Lean v4.13.0; carried
  over here unchanged in v2 form (Equiv-based Fintype instance for
  `Configuration`).

* **F3.c** — Modal 2-category. Five sub-modules:
    - `Symbols`: `ModalSymbol` (τ, δ, ω) and the `IsSmooth` predicate
      on `List ModalSymbol`.
    - `Operators`: `ModalOperators` structure (three endo-functors on
      a base category), with `symbol` dispatch and `interpret` bridge
      from syntactic to semantic level.
    - `TwoCategory`: `BeckChevalleyCompatibility` (Prop placeholder)
      and `ModalTwoCategory` (extends `ModalOperators` by three
      compatibility data fields).
    - `Existence`: five existence theorems (E1–E5).
    - `NonExistence`: NE1, NE2, NE5 as Lean theorems (six rough-cases
      proved); NE3 and NE4 are documented as follow-up tasks for F1.

## Build

```
lake update
lake build
```

The toolchain is `leanprover/lean4:v4.30.0-rc2`. Mathlib is required.

## Project document references

The sources for the formalisation are:

* F3c_Klaerung_1.docx — existence and non-existence statements;
  four-class refinement; cyclic entanglement as datum.
* F3c_Klaerung_2.docx — Bicategory vs. strict 2-category in
  Mathlib; choice of strict form.
* F3c_Klaerung_3.docx — layer placement of F3.c constituents.
* F3c_Spec.docx — full Lean specification with three spec-decisions:
  compatibility data as structure-class fields; Beck-Chevalley as
  Prop placeholder; non-existence primarily syntactic.

For the F3.b material:

* F3b_Klaerung.docx, F3b_Spec.docx, F3b_Spec_Rev2.docx,
  F3b_Implementation.docx, F3b_Implementation_Rev2.docx.
