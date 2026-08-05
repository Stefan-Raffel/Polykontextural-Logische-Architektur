import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Basic

/-!
# LawvereVorSonde — testet die Konvergenz-Hypothese „γ-Kollaps = realize-Kollaps via Lawvere"

STANDALONE, NICHT im Aggregat. Vor-Sonde zur Brücken-Frage der strukturtheoretischen
Bilanz (vgl. `Mathematiker_Bilanz_Phase_Heuristik_Strukturtheoretisch.md`,
`Proemieller_Kern_Intension_Extension_Vorschlag.md`): die drei Stimmen konvergieren auf die
Hypothese, **beide Kollapse** (γ kategorientheoretisch, `realize` modelltheoretisch) seien
Kontrapositive **eines** fixpunktfreien Ω-Endomorphismus (Lawvere im Topos). Diese Vor-Sonde
prüft die Hypothese auf dem **billigsten** Boden zuerst — Type-Ebene, vor PathC —, ganz in
der Konvergenz-Verfehlungs-Disziplin: gerade *weil* die Konvergenz schön ist, soll sie auf
Reinraum-Boden falsifiziert werden, bevor man auf sie baut.

**Die scharfe Frage:** Typt ein fixpunktfreier Endomorphismus die beiden Kollapse zusammen —
auf sauberem Boden, ohne PathC-Sorries und ohne topos-internes Lawvere?

- **Sonde-P (das Schema ist real):** Lawveres Fixpunktsatz (`exists_fixed_point_of_surjective`,
  aus Mathlib konsumiert), der fixpunktfreie Endomorphismus `¬ : Prop → Prop` (P2), die
  generische Kontrapositive (P3: jeder fixpunktfreie `g` widerlegt Punkt-Surjektivität), und
  die **extensionale** Seite als `g = ¬`-Instanz (P4: kein universelles `α → Set α` — Cantor).
  Der extensionale Kollaps IST term-fest eine Lawvere-Instanz des fixpunktfreien `¬`.
- **Sonde-N (Nicht-Vakuanz):** mit Fixpunkt verschwindet die Schranke (`surjection_when_fixpoint`)
  — die Fixpunktfreiheit leistet echte Arbeit, das Schema ist nicht trivial.

**Befund (Doc, der eigentliche Vor-Sonden-Ertrag, KEIN Lean-Satz):** Auf sauberem Boden
instanziiert **nur eine** Seite — die extensionale (`realize`/`Set`, Totalitäts-Seite, P4).
Die γ-Seite (Funktor-Iso, Funktions-Seite) ist **nicht einspeisbar**: `exists_fixed_point_of_surjective`
verlangt eine Punkt-Surjektion `α → (α → β)`; γ ist ein Morphismus-Iso, kein Punkt-Pfeil auf
ein Funktionsobjekt — derselbe Typ-Spalt (Werkmeister-Achse) wie bei Satz B. Die Vereinigung
beider Kollapse zu *einem* Endomorphismus braucht ein **topos-internes** Lawvere mit Ω als
Subobjekt-Klassifikator — und das trägt Mathlib NICHT (`CategoryTheory/Topos/Classifier`
ist Defs-only, kein Diagonal- bzw. Fixpunkt-Satz; nur das mengentheoretische Lawvere hier auf
Type). Befund also: die Konvergenz ist auf Reinraum-Boden **nicht stageable**; was vorliegt
ist ein Grundlagenbau (topos-internes Lawvere von nahe Null), keine Brücken-Klärung. Die
Wachsamkeit der Bilanz ist bestätigt: term-fest ist allein die *eine* (extensionale) Hälfte.

Kein `sorry`, kein `axiom`, kein `: True`-Feld, kein `native_decide`.
-/

open Function

namespace Reformulation.Proemial.LawvereVorSonde

-- ============================================================
-- §I — Sonde-P: das Lawvere-Schema ist real und term-fest
-- ============================================================

/-- **Sonde-P1 (Schema).** Lawveres Fixpunktsatz, aus Mathlib konsumiert: ist
`f : α → α → β` punkt-surjektiv, so hat JEDER Endomorphismus `g : β → β` einen Fixpunkt.
Das ist die gemeinsame Wurzel von Cantor, Russell, Gödel. -/
theorem lawvere_fixpoint {α β : Type*} (f : α → α → β) (hf : Surjective f) (g : β → β) :
    ∃ x, g x = x :=
  exists_fixed_point_of_surjective f hf g

/-- **Sonde-P2 (der fixpunktfreie Endomorphismus).** `¬ : Prop → Prop` hat keinen Fixpunkt:
`(¬p) = p` ist widersprüchlich. Dies ist der eine Endomorphismus, der die Diagonale treibt. -/
theorem not_ne_self : ∀ p : Prop, (¬ p) ≠ p :=
  fun _ h => not_iff_self (iff_of_eq h)

/-- **Sonde-P3 (generische Kontrapositive).** Jeder fixpunktfreie `g : β → β` widerlegt jede
Punkt-Surjektion `α → (α → β)`. Das abstrakte Lawvere-Diagonal-Argument, vom Endomorphismus
abhängig gemacht — die Fixpunktfreiheit ist die einzige Voraussetzung. -/
theorem no_point_surjection_of_fixpoint_free {α β : Type*} (g : β → β) (hg : ∀ b, g b ≠ b) :
    ∀ f : α → (α → β), ¬ Surjective f := by
  intro f hf
  obtain ⟨x, hx⟩ := lawvere_fixpoint f hf g
  exact hg x hx

/-- **Sonde-P4 (die extensionale Seite als `g = ¬`-Instanz).** Kein `f : α → Set α` ist
surjektiv — die extensionale Explosion (keine universelle Totalitäts-Vertretung) ist genau
die `g = ¬`-Instanz des generischen Lawvere. Der `realize`/Totalitäts-seitige Kollaps ist
term-fest von dem einen fixpunktfreien `¬` getrieben. (`Set α` ist `α → Prop`.) -/
theorem no_universal_extension {α : Type*} : ∀ f : α → Set α, ¬ Surjective f :=
  no_point_surjection_of_fixpoint_free Not not_ne_self

-- ============================================================
-- §II — Sonde-N: Nicht-Vakuanz (mit Fixpunkt keine Schranke)
-- ============================================================

/-- **Sonde-N.** Hat der Endomorphismus einen Fixpunkt, verschwindet die Schranke: über
`β = Unit` (wo `id` einen Fixpunkt hat) existiert eine Punkt-Surjektion. Die Fixpunktfreiheit
in P3/P4 leistet also echte Arbeit — das Schema ist nicht vakuant, der Kollaps hängt am
fixpunktfreien Endomorphismus, nicht an der bloßen Form. -/
theorem surjection_when_fixpoint :
    ∃ (α β : Type) (f : α → (α → β)), Surjective f :=
  ⟨Unit, Unit, fun _ _ => (), fun _ => ⟨(), funext fun _ => Subsingleton.elim _ _⟩⟩

-- ============================================================
-- §III — Wachen: Axiom-Profile
-- ============================================================

/-! **Wachen (Zug B).** Ist-Ausgabe des grünen Builds (v4.30.0-rc2), pro Satz
eingefroren; sie ersetzen die vier vormals nackten Aufrufe.

Diese Datei trägt die schmalsten Profile des Zuges: **drei ihrer vier Sätze sind
axiomfrei** und drucken darum den anderen der beiden Ausgabe-Wortlaute (`CLAUDE.md` §8
Fallstrick 15). Der vierte trägt `[Quot.sound]` **ohne** `propext` — im Bestand eine
seltene Form; sie stammt aus dem `funext`/`Subsingleton.elim`-Zeugen und ist gemessen,
nicht erklärt.

`not_ne_self` bleibt nach der Vorgabe ungewacht: kein Aufruf, kein fremdes Zitat. -/

/-- info: 'Reformulation.Proemial.LawvereVorSonde.lawvere_fixpoint' does not depend on any axioms -/
#guard_msgs in #print axioms lawvere_fixpoint

/-- info: 'Reformulation.Proemial.LawvereVorSonde.no_point_surjection_of_fixpoint_free' does not depend on any axioms -/
#guard_msgs in #print axioms no_point_surjection_of_fixpoint_free

/-- info: 'Reformulation.Proemial.LawvereVorSonde.no_universal_extension' does not depend on any axioms -/
#guard_msgs in #print axioms no_universal_extension

/-- info: 'Reformulation.Proemial.LawvereVorSonde.surjection_when_fixpoint' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms surjection_when_fixpoint

end Reformulation.Proemial.LawvereVorSonde
