import Reformulation.F3e.BeckChevalleyAxioms
import Reformulation.F3e.BeckChevalleyConstruction
import Mathlib.CategoryTheory.NatIso

/-!
# F3.e.Theorems — existence, uniqueness, and modal compatibility of BC

Companion theorems to `beckChevalleyFromData`:

* `beckChevalley_exists`: a BC natural isomorphism satisfying
  `BeckChevalleyAxioms` exists in any `ModalTwoCategoryWithPullbacks`.
* (`beckChevalley_unique` — gestrichen, Whitelist-Auflösung 24. Juli 2026;
  Memorial-Block unten. In dieser Form falsch gegen die `True`-Axiome.)
* (`beckChevalley_modalCompat` — gestrichen, Phase-2-Zuspitzung 29. Juli 2026;
  zweiter Memorial-Block unten. Aussage war `True`.)
* `beckChevalley_b5_anchored`: the structure carries K1 as initial config.

Architecture references: F3e_Spec §VI, F3e_Implementation_Prompt §IV.5.
-/

namespace Reformulation.F3e

open CategoryTheory

variable {𝒯 : Type*} [Category 𝒯]

/-! ## Existence -/

/-- Existence: from the data of `ModalTwoCategoryWithPullbacks`, a BC natural
isomorphism satisfying `BeckChevalleyAxioms` exists.

`beckChevalleyFromData M` witnesses the existential; the three axiom fields
are `True` placeholders, satisfied trivially. -/
theorem beckChevalley_exists (M : ModalTwoCategoryWithPullbacks 𝒯) :
    ∃ (BC : M.pullBackC ⋙ M.pullBackO ≅ M.pullBackO ⋙ M.pullBackC),
      BeckChevalleyAxioms M BC := by
  refine ⟨beckChevalleyFromData M, ?_⟩
  exact ⟨trivial, trivial, trivial⟩

/-! ## Uniqueness — gestrichen (Whitelist-Auflösung, 24. Juli 2026)

Gestrichen: `beckChevalley_unique` behauptete `Nonempty (BC = beckChevalleyFromData M)`
für **jedes** `BC`, das `BeckChevalleyAxioms` erfüllt. Da `BeckChevalleyAxioms` drei
`True`-Felder trägt, erfüllt **jeder** natürliche Isomorphismus die Axiome; die
Eindeutigkeits-Aussage ist damit nicht bloß unbewiesen, sondern **in dieser Form
falsch**, sobald der Iso-Typ mehr als ein Element hat. Leere Axiome diskriminieren
nicht. Eine tragfähige Fassung braucht Axiome mit Inhalt — dann wäre es ein anderer
Satz. Kein Konsument im Aggregat; die Streichung bricht nichts.

**Entfernte Aussage** (stand hier mit `sorry`; Signatur eingerückt zitiert, damit
die Satz-Zählroute `^theorem` das Memorial-Zitat nicht als Satz mitzählt):

```
  theorem beckChevalley_unique (M : ModalTwoCategoryWithPullbacks 𝒯)
      (BC : M.pullBackC ⋙ M.pullBackO ≅ M.pullBackO ⋙ M.pullBackC)
      (h : BeckChevalleyAxioms M BC) :
      Nonempty (BC = beckChevalleyFromData M) :=
    ⟨sorry⟩
```
-/

/-! ## B5-anchoring -/

/-- B5-anchoring: the initial configuration of any `ModalTwoCategoryWithPullbacks`
is K1 (Class i, trivial-constant-absent).

Direct read-off from `M.initialConfig_isK1`. Formalizes the B5-component of
the enforcement claim: the pull-back structure is anchored to the initial
singularity (B5 in PKL architecture). -/
theorem beckChevalley_b5_anchored (M : ModalTwoCategoryWithPullbacks 𝒯) :
    M.initialConfig = .k1 :=
  M.initialConfig_isK1

-- Axiom-Wache (Whitelist-Auflösung, 24. Juli 2026): sorry-frei, erbt die
-- Schließung von `beckChevalleyFromData`; Profil Ist-gebunden verwacht.
/-- info: 'Reformulation.F3e.beckChevalley_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms beckChevalley_exists

/-! ## Memorial-Block: gestrichene Deklaration mit der Aussage `True`

Streichung nach Phase-2-Zuspitzung (Setzungsregister, `docs/status-register.md`).
Der Grund: der Name behauptete Gehalt, die Aussage war `True`. Ein Satz mit
Aussage `True` ist kein falscher Satz, aber sein Name liest sich als Ergebnis;
im veroeffentlichten Baum ist das eine Behauptung. Kein Konsument im Aggregat;
die Streichung bricht nichts. Deutschsprachig gehalten wie der aeltere
Memorial-Block dieser Datei (Uniqueness, oben) — die Doc-Strings der Datei sind
englisch, ihre Memorial-Bloecke sind es nicht, und zwei Sprachen in derselben
Rubrik waeren schlechter als eine.

**Entfernte Deklaration** (Signatur eingerueckt zitiert, damit die Zaehlroute
`^theorem` das Memorial-Zitat nicht mitzaehlt). Registerzeile `S40`.

```
  theorem beckChevalley_modalCompat (_ : ModalTwoCategoryWithPullbacks 𝒯) :
      True :=
    trivial
```

*Was dort behauptet war:* dass die Beck-Chevalley-2-Iso mit allen sechs
Modaloperatoren (τ, δ, ω, ¬_τ, ¬_δ, ¬_ω) vertraeglich ist.
*Was ein tragfaehiger Satz braeuchte:* eine Vertraeglichkeit, die scheitern
kann. Der Satz nahm sein Argument nicht einmal entgegen (`_`), konnte also
ueber die Struktur nichts aussagen. Tragfaehig waere: fuer jeden der sechs
Operatoren `X` kommutiert das Quadrat aus `pullBackC`, `pullBackO` und `X` bis
auf die BC-2-Iso — eine Gleichung natuerlicher Transformationen, die man
hinschreiben und beweisen muss. Dazu muessen die Modaloperatoren als Funktoren
auf demselben `𝒯` vorliegen und die BC-Iso mit ihnen komponierbar sein; das
ist vorhanden, seit `beckChevalleyFromData` die Iso aus `pullBackCommute`
liest. Die Felder `BeckChevalleyAxioms.modalCompatible`, `.pentagon` und
`.triangle` (Registerzeilen `S24` bis `S26`) bleiben derweil Platzhalter.
-/

end Reformulation.F3e
