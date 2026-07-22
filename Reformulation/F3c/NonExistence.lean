import Reformulation.F3c.Symbols

/-!
# F3.c.NonExistence — the five non-existence statements NE1–NE5

Per F3c_Klaerung_1.docx §V and F3c_Spec.docx §VI, the five canonical
non-existence statements:

* `NE1` — no canonical resolution for raw `δ∘τ`.
* `NE2` — no canonical resolution for raw `δ∘ω`.
* `NE3` — no canonical commutation `τ∘ω ⇔ ω∘τ`.
* `NE4` — no canonical commutation between the enforced triples.
* `NE5` — no further smooth triple compositions besides the two
  enforced ones (and the trivial iterations).

NE1, NE2, NE5 are formalized syntactically as `IsRough` theorems —
proven by exhausting the six `IsSmooth` constructors via `cases`.

NE3 and NE4 are *not* formalized as Lean theorems (cf. F3c_Spec.docx
§VI.2). They require semantic arguments at the level of functor
naturality, which depend on a concrete deployment; in F3.c, the
syntactic level alone admits both `[.tau, .omega]` and `[.omega, .tau]`
as smooth (asymmetricSmooth*), but says nothing about their isomorphism.
A theorem statement requires constructing a `ModalTwoCategory` instance
in which the two compositions are not 2-isomorphic — that is local-layer
material, belonging in F1.

Below, NE3 and NE4 appear only in the documentation; no Lean declarations
are made for them. Cf. F3c_Spec.docx §VI.5 for the marked follow-up
task on semantic non-existence.
-/

namespace Reformulation.F3c

/-! ## NE1 — no canonical resolution for raw `δ∘τ` -/

/-- NE1 — `δ∘τ` is rough. Proven by exhausting the six `IsSmooth`
constructors; none of them matches `[.delta, .tau]`. -/
theorem delta_tau_rough : IsRough [.delta, .tau] := by
  intro h
  cases h

/-! ## NE2 — no canonical resolution for raw `δ∘ω` -/

/-- NE2 — `δ∘ω` is rough. Symmetric to NE1. -/
theorem delta_omega_rough : IsRough [.delta, .omega] := by
  intro h
  cases h

/-! ## NE3, NE4 — no canonical commutations

These are *not* formalized as Lean theorems at the F3.c level.
See F3c_Spec.docx §VI.2 / §VI.3 for the rationale: the syntactic
level (via `IsSmooth`) admits both compositions as smooth and says
nothing about their 2-isomorphism. A semantic non-existence theorem
requires a concrete deployment in which the compositions are not
2-isomorphic — local-layer material, belonging in F1.

Marked as a follow-up task per F3c_Spec.docx §VI.5.
-/

/-! ## NE5 — no further smooth triple compositions -/

/-- NE5 (a) — `τ∘δ∘ω` is rough. -/
theorem tau_delta_omega_rough : IsRough [.tau, .delta, .omega] := by
  intro h
  cases h

/-- NE5 (b) — `δ∘ω∘τ` is rough. -/
theorem delta_omega_tau_rough : IsRough [.delta, .omega, .tau] := by
  intro h
  cases h

/-- NE5 (c) — `δ∘τ∘ω` is rough. -/
theorem delta_tau_omega_rough : IsRough [.delta, .tau, .omega] := by
  intro h
  cases h

/-- NE5 (d) — `ω∘δ∘τ` is rough. -/
theorem omega_delta_tau_rough : IsRough [.omega, .delta, .tau] := by
  intro h
  cases h

/-- NE5 (e) — `τ∘δ∘δ` is rough. (δ as non-final operator with another δ
following.) -/
theorem tau_delta_delta_rough : IsRough [.tau, .delta, .delta] := by
  intro h
  cases h

/-- NE5 (f) — `ω∘δ∘δ` is rough. -/
theorem omega_delta_delta_rough : IsRough [.omega, .delta, .delta] := by
  intro h
  cases h

end Reformulation.F3c
