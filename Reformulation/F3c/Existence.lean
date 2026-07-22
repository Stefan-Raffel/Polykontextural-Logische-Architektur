import Reformulation.F3c.TwoCategory

/-!
# F3.c.Existence — the five existence statements E1–E5

Per F3c_Klaerung_1.docx §IV and F3c_Spec.docx §V, the five canonical
existence statements:

* `E1` — identity 2-morphisms (standard 2-category structure).
* `E2` — Beck-Chevalley 2-iso (from `ModalTwoCategory.beckChevalley`).
* `E3` — compatibility 2-morphism for `ω∘τ∘δ`.
* `E4` — compatibility 2-morphism for `τ∘ω∘δ`.
* `E5` — trivial iterations carry the identity compatibility.

E3 and E4 are tautological w.r.t. the structure-class form chosen in
`ModalTwoCategory` — this reflects the architectural distinction
between *invariant existence* (carried by the structure class) and
*local form* (the concrete components, supplied by deployments).
See F3c_Spec.docx §V.3 Spec-Beobachtung.
-/

namespace Reformulation.F3c

open CategoryTheory

variable {𝒯 : Type*} [Category 𝒯]

/-- E1 — every 1-cell carries a canonical identity 2-morphism. Standard
2-category structure (Mathlib: `NatTrans.id`); included here for
completeness of the existence catalogue.

Note: this is a `def`, not a `theorem`, because the identity 2-morphism
is *data* in `Type`, not a `Prop`. -/
def identity_two_morphism (f : 𝒯 ⥤ 𝒯) : f ⟶ f :=
  NatTrans.id f

/-- E2 — the Beck-Chevalley compatibility holds for any
`ModalTwoCategory`, by direct field access. -/
theorem beck_chevalley_exists (M : ModalTwoCategory 𝒯) :
    BeckChevalleyCompatibility M.tau M.delta M.omega :=
  M.beckChevalley

/-- E3 — the compatibility 2-morphism for the enforced cyclic triple
`ω∘τ∘δ` exists in any `ModalTwoCategory`. Tautological per the
structure-class form (cf. F3c_Spec.docx §V.3).

Note: `def` rather than `theorem` because a 2-morphism is *data* in
`Type` (cf. F3c_Klaerung_1.docx §VI Beobachtung 2 — the cyclic
entanglement is a datum, not a property). -/
def compat_triple1_exists (M : ModalTwoCategory 𝒯) :
    (M.omega ⋙ M.tau ⋙ M.delta) ⟶ (M.omega ⋙ M.tau ⋙ M.delta) :=
  M.compatTriple1

/-- E4 — the compatibility 2-morphism for the enforced cyclic triple
`τ∘ω∘δ` exists in any `ModalTwoCategory`. Tautological per the
structure-class form (cf. F3c_Spec.docx §V.3).

Note: `def` rather than `theorem`; cf. note on `compat_triple1_exists`. -/
def compat_triple2_exists (M : ModalTwoCategory 𝒯) :
    (M.tau ⋙ M.omega ⋙ M.delta) ⟶ (M.tau ⋙ M.omega ⋙ M.delta) :=
  M.compatTriple2

/-- E5a — every trivial iteration `[s, s]` is smooth. -/
theorem trivial_iteration_smooth (s : ModalSymbol) :
    IsSmooth [s, s] :=
  IsSmooth.trivialIteration s

/-- E5b — the identity natural transformation supplies the trivial
compatibility for trivial iterations. The semantic counterpart of
`trivial_iteration_smooth`.

Note: `def` rather than `theorem`; cf. note on `compat_triple1_exists`. -/
def trivial_iteration_compat (M : ModalOperators 𝒯) (s : ModalSymbol) :
    (M.symbol s ⋙ M.symbol s) ⟶ (M.symbol s ⋙ M.symbol s) :=
  NatTrans.id _

end Reformulation.F3c
