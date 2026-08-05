import Reformulation.Kenogram.Basic

/-!
# K3CouplingProbe — K3′-Sonde für die Kopplung des proemialen Aufsatzes

STANDALONE, NICHT im Aggregat (wie `CartesianProbe`/`A1DescentProbe`). Diese Sonde
steht *vor* dem proemialen Entwurf ρ und ist ihr *minimaler ρ-Kern*: sie prüft
maschinell, dass die Umtausch-Achse (A2) mit der Stufen-Ordnung (A1) *selektiv und
nicht-entkoppelbar* verschränkt ist.

- **K3-P (`coupling_fires`):** der Relator-Umtausch (Stelle 2 = letzte, stufen-
  definierend) erzwingt eine Änderung der unteren Stufe (`descent`/`dropLast`).
- **K3-N (`decoupled_commutes`, Falsifikator):** der Relata-Umtausch (Stellen 0,1;
  letzte Stelle fix) kommutiert mit `descent` — er bewegt die Umtausch-Achse, ohne
  die Inversion zu erzwingen. Genau die von K3′ ausgeschlossene Konstruktion.
- **`coupling_selective` (Nicht-Vakuanz):** beide zusammen — die Kopplung ist eine
  echte Unterscheidung, keine Eigenschaft aller Umtausche.

Reichweite: eingelöst ist der NOTWENDIGE K3′-Kern (selektive, nicht-entkoppelbare
Verschränkung; Kollaps zur Entkopplung abgewehrt). NICHT berührt: die Treue zu
E&W S. 26 (Vier-Relata-Simultaneität), die S_n-Allgemeinheit, das volle ρ.

Kein `sorry`, kein `: True`-Feld, kein `axiom`, kein `native_decide`.
-/

namespace Reformulation.Proemial.K3CouplingProbe

open Reformulation.Kenogram

-- ============================================================
-- §B.1 — Bau-Bestandteile
-- ============================================================

/-- Werte-Vertauschung an zwei Stellen — beide `getD` beziehen sich auf das
Original `l` (nicht auf das nach dem ersten `set` modifizierte). -/
def swapVals (i j : ℕ) (l : List ℕ) : List ℕ :=
  (l.set i (l.getD j 0)).set j (l.getD i 0)

/-- A2-Umtausch-Involution: Stellen-Tausch, re-kanonisiert in RGS-Normalform.
Ohne `relabel` verlöre der Tausch die Stufe. -/
def exchange (i j : ℕ) (l : List ℕ) : List ℕ := relabel (swapVals i j l)

-- ============================================================
-- §B.2 — Die Sätze
-- ============================================================

/-- RGS-Verankerung des Zeugen: `[0,1,1]` ist ein echtes Kenogramm (RGS 3). -/
example : IsRGS [0, 1, 1] := by decide

/-- **K3-P (Kopplung feuert).** Der Relator-Umtausch (Stelle 2 = letzte) erzwingt
eine Änderung der unteren Stufe: `exchange 0 2 [0,1,1] = [0,0,1]`, dessen
`dropLast = [0,0] ≠ [0,1]`. Die symmetrische Bewegung erzwingt die gerichtete
Inversion. -/
theorem coupling_fires :
    (exchange 0 2 [0, 1, 1]).dropLast ≠ ([0, 1, 1] : List ℕ).dropLast := by decide

/-- **K3-N (Falsifikator).** Der Relata-Umtausch (Stellen 0,1; letzte Stelle fix)
kommutiert mit `descent`: `exchange 0 1 [0,1,1] = [0,1,0]`, dessen
`dropLast = [0,1] = [0,1]`. Er bewegt sich, ohne die Inversion zu erzwingen. -/
theorem decoupled_commutes :
    (exchange 0 1 [0, 1, 1]).dropLast = ([0, 1, 1] : List ℕ).dropLast := by decide

/-- **Selektivität (Nicht-Vakuanz der Kopplung).** Beide Umtausch-Arten existieren
und unterscheiden sich im `descent`-Effekt: der Relator-Umtausch feuert, der
Relata-Umtausch nicht. Die Kopplung ist eine echte Unterscheidung, keine
Eigenschaft aller Umtausche — nicht vakuant, nicht tot. -/
theorem coupling_selective :
    (exchange 0 2 [0, 1, 1]).dropLast ≠ ([0, 1, 1] : List ℕ).dropLast
    ∧ (exchange 0 1 [0, 1, 1]).dropLast = ([0, 1, 1] : List ℕ).dropLast := by decide

-- ============================================================
-- §III — Wachen: Axiom-Profile
-- ============================================================

/-! **Wachen.** Ist-Ausgabe des grünen Builds (v4.30.0-rc2), pro Satz eingefroren.
Alle drei Sätze der Datei tragen eine Wache; gewacht ist damit auch der
Falsifikator `decoupled_commutes`, der bisher als einziger der drei ohne
`#print axioms` stand.

Die Profile sind `[propext]` — die schmalsten des ρ-Sonden-Vierers. Kein
`Quot.sound`: die Sätze rechnen über `List ℕ` und `dropLast`, nicht über
`Multiset` wie `A3CoarseningProbe` und nicht über den `RGS`-Subtyp wie
`A1DescentProbe`. -/

/-- info: 'Reformulation.Proemial.K3CouplingProbe.coupling_fires' depends on axioms: [propext] -/
#guard_msgs in #print axioms coupling_fires

/-- info: 'Reformulation.Proemial.K3CouplingProbe.decoupled_commutes' depends on axioms: [propext] -/
#guard_msgs in #print axioms decoupled_commutes

/-- info: 'Reformulation.Proemial.K3CouplingProbe.coupling_selective' depends on axioms: [propext] -/
#guard_msgs in #print axioms coupling_selective

end Reformulation.Proemial.K3CouplingProbe
