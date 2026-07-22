import Reformulation.Proemial.IntervalBackbone
import Reformulation.Proemial.RecurringGround

/-!
# Reformulation.Proemial.ReversibleExchange — der reversible Umtausch (zweiundzwanzigste Schicht)

Die **erste Mittelstelle** der achtfachen Thematik: das zweite Intervall, in dem
„die Zeit ausschließlich in ihrer reversiblen Form" auftritt, bekommt seine
Fassung als Involution — zweimaliger Tausch ist Rückkehr. Der eine Satz mit
eigenem Beweis-Gehalt ist die Brücke (reversibel → punktweise periodisch); alles
Weitere ist benannter Konsum: die Rückkehr jedes erreichten Zustands, die
Unmöglichkeit des Erschöpfungs-Übergangs, die geteilten Zeugen `swap`/`collapse`,
der Rückgrat-Ort.

**Erste Schicht auf beiden Strängen** (belegt am Import-Graph dieser Lieferung):
sie importiert das Substrat `IntervalBackbone` (21.) und die Ketten-Spitze
`RecurringGround` (20., transitiv `ExhaustionTransition` und `IrreversibleAscent`)
— die Kette wird 16→19→20→22. Term-identisch konsumiert werden `PointwisePeriodic`,
`reach_returns`, `no_exhaustion_in_periodic` (16.), `Exhausts`, `collapse` (19.),
`swap` (20.), `intervalStart`/`intervalEnd` (21.). Nichts wird dupliziert.

## (1) Quellen

Der Anker im Wortlaut: „Im zweiten Intervall tritt die Zeit ausschließlich in
ihrer reversiblen Form auf" (Lille Z. 486–487, **Volltext-verifiziert**). Die
Zeit-Dreiheit reversibel / irreversibel / Komplementarität als Rolle der drei
Mittelstellen: Z. 484–486. „Mechanik": Z. 512–513. Der Ort (Intervall II als
Abschnitt des 14-wertigen Systems): Z. 517–519. Härte-Ökonomie: einmal geeicht
(Beiträge III, S. 160, druck-verifiziert), verlängerbar.

## (2) HEGEL-RELATIVITÄTS-MARKE

Die Zuordnung „Mechanik = Intervall II" ist **Lesart der Hegel-Stufe**, nicht
Satz dieser Schicht: Günther selbst meldet „ernsthafte Zweifel" (Z. 921–922) an
und nennt die Zuordnung „nur relativ" (Z. 936–938); gesichert ist allein die
Gliederung „je drei Intervalle". Term-fest wird hier keine Zuordnung, sondern
das Umtausch-Merkmal und seine Lage in der armen Klasse.

## (3) Substrat-Erbe

Der Ort (`interval_II_start`, `interval_II_end`) kommt aus dem Rückgrat (21.) —
**das Rückgrat zählt, diese Schicht deutet**. Die Orts-Sätze sind der erste
Stellen-Konsum des Substrats; ihre Arithmetik ist dort term-fest, hier wird sie
nur an der Stelle 2 abgerufen.

## (4) Term-fest werden hiermit

`reversible_pointwise_periodic` (die Brücke), `reversible_returns`,
`reversible_no_exhaustion`, `swap_reversible`, `collapse_not_reversible`,
`interval_II_start`, `interval_II_end`, Kür `reversible_bijective`.

**KONSUM-EHRLICHKEIT:** eigener Beweis-Gehalt liegt **allein in der Brücke**.
`reversible_returns` und `reversible_no_exhaustion` sind benannter Konsum der
16. Schicht über die Brücke; die Zeugen sind die geteilten Zeugen der 20./19.;
die Orts-Sätze sind Substrat-Abrufe. Das ist die **Bauform-These der
Mittelstellen**: Merkmal + Ort + Anschlüsse, **kein neuer Apparat**. Die Stelle
*liegt in* einer bestehenden armen Klasse — das ist ihr Befund, kein
Differential-Ersatz.

## (5) Deutungs-Marken

Involution als Lesart von „Umtauschverhältnis" ist **Deutung**; die Zuordnung der
Formalisierung zur Stelle 2 ist **strukturanalytisch**; der Fin-2-Träger der
Zeugen ist **Modellwahl**, keine Werte-Semantik; „zweiwertig" ist Themen-Rede
(die Zahl der Themen des zweiten Intervalls), keine Werte-Semantik;
**Designation ≠ Denotation** gilt fort.

## (6) Abgrenzung

Kein Vorgriff auf St.3 (Irreversibilität) oder St.4 (Komplementarität) — eigene
Pakete. Keine Zeit-Metaphysik. Die U5-Figuren bleiben benannte Posten.

## (7) Sorry-Bilanz und Axiom-Ist

**0 Sorries.** Axiom-Ist (erster grüner Build, v4.30.0-rc2), je Satz
`#guard_msgs`-verwacht am Datei-Ende:

* **axiom-frei:** `reversible_pointwise_periodic`, `reversible_no_exhaustion`,
  `interval_II_start`, `interval_II_end`, `reversible_bijective`.
* **`[propext]`:** `reversible_returns` (geerbt von `reach_returns`, 16.),
  `swap_reversible`, `collapse_not_reversible` (`decide`-Hülle über `Fin 2`).

**Abweichung, Verschärfung:** die Erwartung der Spec (Brücke/Konsum im geerbten
`propext`-Bereich, decide-Sätze axiom-frei) trifft **nicht**, und zwar in beide
Richtungen — Erwartungs-Wachen sind Rate-Wachen, der Fehlschlag ist ein Fund:
die Brücke und `reversible_no_exhaustion` sind **axiom-frei** (die
Perioden-2-Route braucht kein `propext`, und `no_exhaustion_in_periodic` ist in
der 19. selbst axiom-frei), während die `decide`-Sätze über `Fin 2` `propext`
tragen (Hüllen-Profil der Taktik, nicht Substanz — dasselbe Ist wie
`collapse_ground`/`swap_no_exhaustion` in der 20.). **Kein neues `Classical`**;
die Schicht importiert kein Mathlib-Modul über die transitive Hülle hinaus.

**KÜR-MESSUNG (Routen-Regel, Rückgrat-Lehre — beide gebaut, beide gemessen):**
Kandidat A `Function.Involutive.bijective h` (`Reversible` ist defeq zu
`Function.Involutive`) — **axiom-frei**; Kandidat B (Eigenbeweis: injektiv via
zweifacher Anwendung, surjektiv via `⟨f b, h b⟩`) — **ebenfalls axiom-frei**.
**Gleichstand → Kandidat A** (Ökonomie, Konsum schlägt Neubeweis).
-/

namespace Reformulation.Proemial.ReversibleExchange

open Reformulation.Proemial.IntervalBackbone
open Reformulation.Proemial.RecurringGround
open Reformulation.Proemial.ExhaustionTransition
open Reformulation.Proemial.IrreversibleAscent

-- ============================================================
-- Teil 1 — Das Merkmal (M1)
-- ============================================================

/-- Das Umtauschverhältnis: zweimaliger Tausch ist Rückkehr. Die Zuordnung zum
    „reversiblen" zweiten Intervall (Stelle 2) ist strukturanalytisch; Involution
    als Lesart von „Umtausch" ist Deutung. -/
def Reversible {α : Type*} (f : α → α) : Prop := ∀ x, f (f x) = x

-- ============================================================
-- Teil 2 — Die Brücke (M2)
-- ============================================================

/-- BRÜCKE (der eine Satz der Schicht mit eigenem Beweis-Gehalt): die reversible
    Welt ist punktweise periodisch — Stelle 2 liegt beweisbar in der armen
    Klasse, gegen die Aufstieg (16.) und Erschöpfung (19.) unmöglich sind.
    Muster: `swap_pointwise_periodic` (20.), Periode 2; `f^[2] x` ist defeq zu
    `f (f x)`, `h x` schließt direkt. -/
theorem reversible_pointwise_periodic {α : Type*} {f : α → α}
    (h : Reversible f) : PointwisePeriodic f := by
  intro x
  exact ⟨2, Nat.zero_lt_two, h x⟩

-- ============================================================
-- Teil 3 — Die Quell-Sätze des „ausschließlich" (M3; benannter Konsum)
-- ============================================================

/-- UMTAUSCH AM TERM: jeder erreichte Zustand kehrt zurück. Benannter Konsum von
    `reach_returns` (16.) über die Brücke; die Signatur ist von `reach_returns`
    geerbt: `(hf : PointwisePeriodic f) (x : α) (k : ℕ) : ∃ m, f^[m] (f^[k] x) = x`. -/
theorem reversible_returns {α : Type*} {f : α → α}
    (h : Reversible f) (x : α) (k : ℕ) : ∃ m : ℕ, f^[m] (f^[k] x) = x :=
  reach_returns (reversible_pointwise_periodic h) x k

/-- „AUSSCHLIESSLICH REVERSIBEL": in der reversiblen Zeit geschieht kein
    Erschöpfungs-Übergang — die achte Stelle liegt nicht im zweiten Intervall.
    Benannter Konsum von `no_exhaustion_in_periodic` (19.) über die Brücke. -/
theorem reversible_no_exhaustion {α : Type*} {f : α → α}
    (h : Reversible f) : ∀ x b, ¬ Exhausts f x b :=
  no_exhaustion_in_periodic (reversible_pointwise_periodic h)

-- ============================================================
-- Teil 4 — Geteilte Zeugen und Orts-Sätze (M4/M5)
-- ============================================================

/-- Der positive Zeuge: `swap` (20.) ist reversibel — kein neuer Zeuge. -/
theorem swap_reversible : Reversible swap := by
  show ∀ x : Fin 2, swap (swap x) = x
  decide

/-- Der negative Zeuge: `collapse` (19.) ist es nicht — die Welt der Erschöpfung
    ist nicht die des Umtauschs. Mit `reversible_no_exhaustion` steht die
    Trennung St.2 ↔ St.8 in beiden Richtungen am Term. -/
theorem collapse_not_reversible : ¬ Reversible collapse := by
  show ¬ ∀ x : Fin 2, collapse (collapse x) = x
  decide

/-- Der Ort aus dem Rückgrat (21.; Lille Z. 517–519): Intervall II beginnt bei 3 … -/
theorem interval_II_start : intervalStart 2 = 3 := by decide

/-- … und endet bei 5 — erster Stellen-Konsum des Substrats. -/
theorem interval_II_end : intervalEnd 2 = 5 := by decide

-- ============================================================
-- Teil 5 — Kür (K1; Routen-Regel: gemessene Route)
-- ============================================================

/-- KÜR: der Umtausch verliert nichts — Reversibilität erzwingt Bijektivität.
    Route nach Profil-Messung (Doc-Rubrik (7)): Kandidat A (Konsum von
    `Function.Involutive.bijective`, defeq-Anwendung auf `h`) und Kandidat B
    (Eigenbeweis) sind **beide axiom-frei** — Gleichstand, daher A (Ökonomie). -/
theorem reversible_bijective {α : Type*} {f : α → α}
    (h : Reversible f) : Function.Bijective f :=
  Function.Involutive.bijective h

end Reformulation.Proemial.ReversibleExchange

-- ============================================================
-- Teil 6 — Die `#guard_msgs`-Wachen (M7; Ist-gebunden)
-- ============================================================

-- Ist-Ausgabe des ersten grünen Builds (v4.30.0-rc2), pro Satz als Wache.
open Reformulation.Proemial.ReversibleExchange in
section

/-- info: 'Reformulation.Proemial.ReversibleExchange.reversible_pointwise_periodic' does not depend on any axioms -/
#guard_msgs in #print axioms reversible_pointwise_periodic

/-- info: 'Reformulation.Proemial.ReversibleExchange.reversible_returns' depends on axioms: [propext] -/
#guard_msgs in #print axioms reversible_returns

/-- info: 'Reformulation.Proemial.ReversibleExchange.reversible_no_exhaustion' does not depend on any axioms -/
#guard_msgs in #print axioms reversible_no_exhaustion

/-- info: 'Reformulation.Proemial.ReversibleExchange.swap_reversible' depends on axioms: [propext] -/
#guard_msgs in #print axioms swap_reversible

/-- info: 'Reformulation.Proemial.ReversibleExchange.collapse_not_reversible' depends on axioms: [propext] -/
#guard_msgs in #print axioms collapse_not_reversible

/-- info: 'Reformulation.Proemial.ReversibleExchange.interval_II_start' does not depend on any axioms -/
#guard_msgs in #print axioms interval_II_start

/-- info: 'Reformulation.Proemial.ReversibleExchange.interval_II_end' does not depend on any axioms -/
#guard_msgs in #print axioms interval_II_end

/-- info: 'Reformulation.Proemial.ReversibleExchange.reversible_bijective' does not depend on any axioms -/
#guard_msgs in #print axioms reversible_bijective

end
