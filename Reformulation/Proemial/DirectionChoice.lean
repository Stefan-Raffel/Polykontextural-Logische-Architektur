import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.DeriveFintype

/-!
# Reformulation.Proemial.DirectionChoice — die Drehrichtungs-Wahl (fünfzehnte Schicht)

## (1) Quellen-fest

Günther 1979 (*Identität, Gegenidentität und Negativsprache*): „Die Wahl ist im
hierarchischen Sinn irreversibel, im heterarchischen Sinn vertauschbar." — die
Drehrichtungs-Wahl in der Heterarchie.

Günther 1971 (*Erkennen und Wollen*): „Ein Wille, der nichts als sich selbst will,
hätte nichts Konkretes, das ihn in Bewegung bringen könnte." — das Unit-Verbot:
das leere Argument trägt nur Konstanten.

## (2) Term-fest werden hiermit

* die **gesetzte Wahl-Funktion** `directionChoice : CompositionSite → Turn`
  (dritte Wille-Funktion, Rev3-Signatur eingelöst; Konkordanz Stellung ≙
  `CompositionSite`, KompositionsRichtung ≙ `Turn`, choose ≙ `directionChoice`);
* das **Faktorisierungs-Differential**: Kern-Lemma `factorsThroughUnit_iff_constant`
  als volle Äquivalenz (durch `Unit` faktorisieren ↔ konstant sein), Nicht-Konstanz
  des Zeugen (`directionChoice_not_constant`), keine Unit-Faktorisierung
  (`directionChoice_no_unit_factorization`).

## (3) Richtungs-Marke (Pflicht)

Eingelöst ist **Richtung 1** der E&W-Reziprozität — kein Wollen ohne Vorstellung
(das Unit-Verbot: die gesetzte Wahl kann sich nicht durch das leere Argument
faktorisieren). **Richtung 2** (kein Denken ohne Vollzugs-Träger) bleibt offen;
die proemielle Fassung (V2) ist Folge-Paket.

## (4) Marke 3 — Deutung, nicht Behauptung

Dass `directionChoice` „Wille" und „Wahl" *ist*, bleibt Deutung; term-fest ist
allein die Form (stellungs-abhängige, nicht Unit-faktorisierbare Auswahl).

## (5) Abgrenzung

Kein PathC-Import; kein Satz über τ/δ/ω — die Stellen-Namen der `CompositionSite`
sind semantische Verweise auf die Kompositions-Stellen der Pfad-C-Triade, tragen
KEINE Funktor-Substanz. Der Swap-Satz bleibt eigenes Paket (AP7).

## (6) Sorry-Bilanz und Axiom-Stand

0 Sorries. Das Kern-Lemma `factorsThroughUnit_iff_constant` hängt von KEINEM Axiom
ab; die negative Hälfte (`directionChoice_not_constant`,
`directionChoice_no_unit_factorization`) ist per Hand-Beweis geführt und zieht nur
`propext`. Die Kür-Zähl-Sätze gehen über `decide` und ziehen darum die üblichen
Kern-Axiome `propext, Classical.choice, Quot.sound` (`#print axioms` am Datei-Ende).
-/

namespace Reformulation.Proemial.DirectionChoice

/-! ## Teil 1 — Die Typen (M1) -/

/-- Die zwei Drehsinne der heterarchischen Vertauschbarkeit eines
    Kompositions-Paares (f,g): erst f, dann g — oder erst g, dann f.
    Konkordanz: „KompositionsRichtung" (Gestalt, Apparat C; Rev3-Vorschlag). -/
inductive Turn where
  | left
  | right
  deriving DecidableEq, Repr, Fintype

/-- Die drei ungeordneten Paar-Stellen der modalen Triade, an denen eine
    Drehrichtung zu wählen ist. Konkordanz: „Stellung" (Rev3-Vorschlag).
    Die Konstruktor-Namen verweisen semantisch auf die Kompositions-Stellen
    der Pfad-C-Triade (τ/δ, δ/ω, ω/τ); sie tragen KEINE Funktor-Substanz —
    diese Schicht enthält keinen Satz über τ/δ/ω. -/
inductive CompositionSite where
  | tauDelta
  | deltaOmega
  | omegaTau
  deriving DecidableEq, Repr, Fintype

/-! ## Teil 2 — Das generische Kern-Lemma (M2) -/

/-- KERN-LEMMA (typunabhängig, volle Äquivalenz): eine Funktion faktorisiert
    genau dann durch `Unit`, wenn sie konstant ist. Das arme Modell des
    Differentials — die Wahl mit leerem Argument — ist damit EXAKT
    charakterisiert: `Unit`-Wahlen sind die Konstanten, nicht mehr. -/
theorem factorsThroughUnit_iff_constant {α β : Type*} (c : α → β) :
    (∃ g : Unit → β, ∀ a, c a = g ()) ↔ (∃ b, ∀ a, c a = b) := by
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g (), hg⟩
  · rintro ⟨b, hb⟩
    exact ⟨fun _ => b, hb⟩

/-! ## Teil 3 — Zeuge, Ehrlichkeit, negative Hälfte (M3/M4) -/

/-- DIE GESETZTE WAHL-FUNKTION (dritte Wille-Funktion, Rev3-Signatur
    eingelöst): echte Stellungs-Variation — an der ω/τ-Stelle links,
    sonst rechts. Dass dies „Wille" und „Wahl" IST, bleibt Deutung
    (Marke 3); term-fest ist die Form. -/
def directionChoice : CompositionSite → Turn :=
  fun s => match s with
  | .omegaTau => .left
  | _ => .right

/-- EHRLICHKEIT: die gesetzte Wahl ist nicht konstant — sie variiert
    wirklich mit der Stellung. -/
theorem directionChoice_not_constant :
    ¬ ∃ d : Turn, ∀ s, directionChoice s = d := by
  rintro ⟨d, hd⟩
  -- an der ω/τ-Stelle wählt `directionChoice` links, an der τ/δ-Stelle rechts;
  -- eine Konstante `d` müsste beide sein: `Turn.left = Turn.right`.
  have hl : Turn.left = d := hd .omegaTau
  have hr : Turn.right = d := hd .tauDelta
  exact Turn.noConfusion (hl.trans hr.symm)

/-- NEGATIVE HÄLFTE (Günther 1971 als Beweis-Spiegel): die gesetzte Wahl
    faktorisiert NICHT durch `Unit` — „ein Wille, der nichts als sich
    selbst will, hätte nichts Konkretes, das ihn in Bewegung bringen
    könnte": das leere Argument trägt nur Konstanten (Kern-Lemma), und
    die Stellungs-Variation ist ihm darum unerreichbar. -/
theorem directionChoice_no_unit_factorization :
    ¬ ∃ g : Unit → Turn, ∀ s, directionChoice s = g () := fun h =>
  directionChoice_not_constant
    ((factorsThroughUnit_iff_constant directionChoice).mp h)

/-! ## Teil 4 — Kür: der Zähl-Satz (K1) -/

/-- KÜR — die Verarmung als Kardinalität: das arme Modell trägt genau
    die zwei Konstanten … -/
theorem card_unit_choices : Fintype.card (Unit → Turn) = 2 := by
  rw [Fintype.card_fun]; decide

/-- … die reiche Seite alle 2³ Stellungs-Wahlen. -/
theorem card_site_choices : Fintype.card (CompositionSite → Turn) = 8 := by
  rw [Fintype.card_fun]; decide

end Reformulation.Proemial.DirectionChoice

/-! ## Axiom-Stand (Regressions-Wachen)

Ist-Ausgabe des grünen Builds (v4.30.0-rc2), pro Satz eingefroren (Zug „Wachen-Vollzug",
Datei-Vollständigkeit); ab hier bricht jede Axiom-Drift den Build. -/

/-- info: 'Reformulation.Proemial.DirectionChoice.factorsThroughUnit_iff_constant' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Proemial.DirectionChoice.factorsThroughUnit_iff_constant

/-- info: 'Reformulation.Proemial.DirectionChoice.directionChoice_not_constant' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.DirectionChoice.directionChoice_not_constant

/-- info: 'Reformulation.Proemial.DirectionChoice.directionChoice_no_unit_factorization' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.DirectionChoice.directionChoice_no_unit_factorization

/-- info: 'Reformulation.Proemial.DirectionChoice.card_unit_choices' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.DirectionChoice.card_unit_choices

/-- info: 'Reformulation.Proemial.DirectionChoice.card_site_choices' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.DirectionChoice.card_site_choices
