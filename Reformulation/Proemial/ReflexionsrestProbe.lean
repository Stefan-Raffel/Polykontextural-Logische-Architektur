import Reformulation.Proemial.TransjunctionCloneBound

/-!
# ReflexionsrestProbe — Satz A: der Reflexionsrest ist real (Intension ≠ Extension)

STANDALONE, NICHT im Aggregat (wie `A1DescentProbe`/`TransjunctionCloneBound`). Erster
term-fester Schritt des intensionalen Programms (vgl. `Proemieller_Kern_Intension_Extension_Vorschlag.md`):
der proemielle **Kern** (proemielle Typinversion, Funktion/Totalität-Differenz) lebt nicht
auf dem extensionalen RGS-Substrat (Liste = Totalität ihrer Stellen), sondern auf dem
**intensionalen** Substrat `L.Term` — wo Intension (der syntaktische Term) und Extension
(seine Denotation `Term.realize`) getrennt sind.

**Die scharfe Frage:** Trägt das syntaktische Substrat einen echten *Reflexionsrest* —
zwei strukturell **verschiedene** Terme mit **gleicher** Denotation —, der NICHT durch
`propext`/`funext` kollabiert (anders als auf `X → Prop`, wo die Differenz sofort
verschwände)?

- **Sonde-P (Reflexionsrest real):** `realize_not_injective` — es gibt `s ≠ t : L.Term (Fin 2)`
  mit `∀ v, s.realize v = t.realize v`. Zeuge: `s = ∨(x₀,x₀)` (syntaktisch eine Komposition),
  `t = x₀` (syntaktisch eine Projektion); beide denotieren `v ↦ v 0` (Idempotenz von `max`).
  Verschiedene **Intension** (`func` vs. `var`, strukturell), gleiche **Extension**. Die
  Verschiedenheit ist `Term`-Konstruktor-Disjunktheit, NICHT Prop-Gleichheit — `propext`
  greift nicht.
- **Sonde-N (die andere Hälfte der Schere):** `T_not_in_clone` (konsumiert aus
  `TransjunctionCloneBound`) trägt die Gegenrichtung — eine **semantische** Funktion (`T`)
  ohne **syntaktische** Intension im Klon. P + N = beide Richtungen der Funktion/Totalität-
  Schere: Intension ohne eindeutige Extension (P) und Extension ohne Intension (N).

Reichweite: term-belegt ist, dass die Denotation `realize` nicht injektiv ist (der
Reflexionsrest existiert auf dem intensionalen Substrat) — die `propext`-Falle des
Vorschlags ist damit ausgeschlossen, weil `Term`-Gleichheit strukturell ist. NICHT berührt:
der γ-Kollaps und seine Identität mit der Extensionalität (Satz B — quert die Werkmeister-
Achse, eigener Bauplatz, siehe `LawvereVorSonde`); die Kopplung an den Relator→Relatum-
Typsprung (Satz C). Dass dieser Reflexionsrest Günthers proemielle Typinversion IST, bleibt
Doc-Deutung, nicht Lean-Satz.

Kein `sorry`, kein `axiom`, kein `: True`-Feld, kein `native_decide`.
-/

open FirstOrder Language

namespace Reformulation.Proemial.ReflexionsrestProbe

open Reformulation.Proemial.TransjunctionCloneBound

-- ============================================================
-- §I — Sonde-P: die Denotation ist nicht injektiv (Reflexionsrest real)
-- ============================================================

/-- Die Intension `s`: die syntaktische Komposition `∨(x₀, x₀)` (`func`-Konstruktor). -/
def s : L.Term (Fin 2) :=
  Term.func (l := 2) (BinaryFun.or : L.Functions 2) ![Term.var 0, Term.var 0]

/-- Die Intension `t`: die syntaktische Projektion `x₀` (`var`-Konstruktor). -/
def t : L.Term (Fin 2) := Term.var 0

/-- **Sonde-P.** Die Denotation `Term.realize` ist nicht injektiv: `s = ∨(x₀,x₀)` und
`t = x₀` sind strukturell verschiedene Terme (`func` vs. `var`), denotieren aber dieselbe
Funktion `v ↦ v 0` (`max (v 0) (v 0) = v 0`). Der Reflexionsrest — verschiedene Intension,
gleiche Extension — ist real, und die Verschiedenheit ist `Term`-Konstruktor-Disjunktheit,
nicht durch `propext` kollabierbar. -/
theorem realize_not_injective :
    ∃ (s t : L.Term (Fin 2)), s ≠ t ∧ ∀ v : Fin 2 → Fin 3, s.realize v = t.realize v := by
  refine ⟨s, t, ?_, ?_⟩
  · -- Verschiedene Konstruktoren: func ≠ var. Strukturell (Bool-Diskriminator), nicht
    -- propositional — `propext` greift nicht.
    simp only [s, t]
    intro h
    have := congrArg
      (fun u : L.Term (Fin 2) => match u with | Term.var _ => false | Term.func _ _ => true) h
    simp at this
  · -- Gleiche Denotation: max (v 0) (v 0) = v 0.
    intro v
    simp [s, t]

-- ============================================================
-- §II — Sonde-N: die andere Schere-Hälfte (Extension ohne Intension)
-- ============================================================

/-- **Sonde-N.** Die Gegenrichtung der Funktion/Totalität-Schere, konsumiert aus
`TransjunctionCloneBound`: die semantische Funktion `T` (eine *Totalität* von Argument-Wert-
Paaren) wird von **keinem** Term realisiert — Extension ohne Intension im Klon. Zusammen mit
Sonde-P (Intension ohne eindeutige Extension) ist die Schere beidseitig term-belegt. -/
theorem extension_without_intension :
    ¬ ∃ u : L.Term (Fin 2), ∀ v : Fin 2 → Fin 3, u.realize v = T (v 0) (v 1) :=
  T_not_in_clone

-- ============================================================
-- §III — Verifikation (kein `sorryAx`)
-- ============================================================

#print axioms realize_not_injective
#print axioms extension_without_intension

end Reformulation.Proemial.ReflexionsrestProbe
