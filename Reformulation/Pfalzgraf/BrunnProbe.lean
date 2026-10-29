import Reformulation.Pfalzgraf.Faserung   -- Faser, Wert, global, liest, kohaerent, vec, auswFrei, trenn, trennfall_inkohaerent, all_mp, all_mpr, mem3

/-!
# Pfalzgraf.BrunnProbe — je zwei Fasern immer kohärent, alle drei nicht immer;  die Stelle ist Kaehrs Trennfall

STANDALONE, NICHT im Aggregat;  Target `Probes`.  AxiomGate unberührt.  Sonde nach `KorpusRev2/Prompt_Instanz_Sonde_Brunnsche_Form.md`
(Mathematiker, 29.10.2026 06:23).  Herkunft der Zahlen:  `T_Vorprobe_Skripte/Brunn_Kohaerenz.py` (gerechnet, Mathematiker).  Konsumiert
`Pfalzgraf/Faserung` (`Faser`, `Wert`, `global`, `liest`, `kohaerent`, `vec`, `auswFrei`, `trenn`, `trennfall_inkohaerent`, `all_mp`,
`all_mpr`, `mem3`);  ändert nichts davon.

## Die Form

Die „brunnsche Form" einer Eigenschaft P von Fasermengen heisst hier nur:  **P gilt für jede Menge aus zwei Fasern, aber nicht für alle
drei.**  Eine Quantorengestalt, kein Satz über Knoten.  Eigenschaften der Gestalt „für jede Faser" oder „für je zwei Fasern" (`zulaessig`,
`gueltigFrei`) können sie nicht haben, weil sie Konjunktionen sind;  sie tritt nur bei einer EXISTENZ auf — hier bei einem globalen Wert,
mit dem ein freier Vektor kohärent ist.

## WAS

```text
kohaerentAuf S x g   wie `kohaerent`, nur über die Fasern der Liste S
B0  kohaerentAuf_alle   UMBENENNUNG (rfl)     kohaerentAuf [0, 1, 2] x g = kohaerent x g, für alle x, g
B1  je_zwei_immer       FOLGERUNG (decide)    für jeden freien Vektor vec b0 b1 b2 und jedes der drei Faserpaare gibt es einen Wert,
                                              mit dem der Vektor auf dem Paar kohärent ist
B2  drei_nicht_genau    FOLGERUNG (decide)    kein Wert ist mit vec b0 b1 b2 auf allen drei Fasern kohärent
                                              ⟺ (b0, b1, b2) = (T, T, F) ∨ (b0, b1, b2) = (F, F, T)
B3  brunn_trennfall     FOLGERUNG             die freie Belegung p ↦ vec b0 b1 b2 falsifiziert trenn ⟺ je zwei Fasern kohärent,
                                              alle drei nicht.  Beweis aus trennfall_inkohaerent und B1 (B2 wird nicht gebraucht)
B4  drei_werte          EICHUNG (decide)      an den zwei Vektoren aus B2 ist der kohärente Wert je Paar eindeutig, und die drei Werte
                                              sind verschieden:  (T, T, F):  {0,1} → 0, {1,2} → 1, {0,2} → 2;
                                              (F, F, T):  {0,1} → 2, {1,2} → 0, {0,2} → 1
```

Hilfssätze:  `all_iff`, `any_iff` (die Bool-Faltungen über `[0, 1, 2]` als Quantoren über `Fin 3`, ohne `List.all_eq_true`, das
`Quot.sound` zieht — Faserung K7).  Definitionen:  `kohaerentAuf`, `faserPaare`.  Kein `native_decide`, kein `sorry`, kein True-Feld.

## Marken

QUELLE — Kaehr 1981 (der Trennfall, über `Faserung` K1).  ZUORDNUNG — `kohaerent` (Faserung K4) zu Pfalzgrafs Restklassenabbildung.
UNSER — der Name „brunnsche Form" für die Quantorengestalt.

## NICHT

Kein Satz über Knoten oder Topologie.  Die Form ist an EINEM Modell gezeigt (drei Fasern, Pfalzgrafs Restklassen), nicht für
Polykontexturalität.  „Je zwei immer verträglich" gilt für `kohaerent`, nicht für die Wertüberlappung — die ist ein anderer Begriff
(`ContextureOverlap.three_contextures_overlap`:  paarweise nicht leer).
-/

namespace Reformulation.Pfalzgraf.BrunnProbe

open Reformulation.Pfalzgraf

/-- **Kohärenz auf einer Fasermenge:**  jede Faser aus S, die g liest, liest ihn so. -/
def kohaerentAuf (S : List Faser) (x : Faser → Bool) (g : Wert) : Bool :=
  S.all fun i => !liest i g || global i (x i) == g

/-- die drei Faserpaare -/
def faserPaare : List (List Faser) := [[0, 1], [1, 2], [0, 2]]

/-! ## B0 — auf allen drei Fasern ist es `kohaerent` -/

/-- (B0) **Auf allen drei Fasern ist die eingeschränkte Kohärenz die Kohärenz des Bestands.** -/
theorem kohaerentAuf_alle (x : Faser → Bool) (g : Wert) : kohaerentAuf [0, 1, 2] x g = kohaerent x g := rfl

/-! ## B1, B2 — je zwei immer, alle drei genau an zwei Vektoren nicht -/

/-- (B1) **Je zwei Fasern sind immer verträglich:**  zu jedem freien Vektor und jedem Faserpaar gibt es einen Wert, mit dem der Vektor
    auf dem Paar kohärent ist. -/
theorem je_zwei_immer :
    ∀ b0 b1 b2 : Bool, ∀ S ∈ faserPaare, ∃ g : Wert, kohaerentAuf S (vec b0 b1 b2) g = true := by
  decide

/-- (B2) **Alle drei Fasern sind genau an zwei Vektoren unverträglich:**  an (T, T, F) und (F, F, T). -/
theorem drei_nicht_genau :
    ∀ b0 b1 b2 : Bool, (¬ ∃ g : Wert, kohaerent (vec b0 b1 b2) g = true) ↔
      ((b0, b1, b2) = (true, true, false) ∨ (b0, b1, b2) = (false, false, true)) := by
  decide

/-! ## B3 — die brunnsche Form ist Kaehrs Trennfall -/

theorem all_iff {p : Faser → Bool} : ([0, 1, 2] : List Faser).all p = true ↔ ∀ i : Faser, p i = true :=
  ⟨fun h i => all_mp h i (mem3 i), fun h => all_mpr fun i _ => h i⟩

theorem any_iff {p : Wert → Bool} : ([0, 1, 2] : List Wert).any p = true ↔ ∃ g : Wert, p g = true := by
  constructor
  · intro h
    cases h0 : p 0
    · cases h1 : p 1
      · cases h2 : p 2
        · exact absurd h (by show (p 0 || (p 1 || (p 2 || false))) ≠ true; rw [h0, h1, h2]; decide)
        · exact ⟨2, h2⟩
      · exact ⟨1, h1⟩
    · exact ⟨0, h0⟩
  · rintro ⟨g, hg⟩
    show (p 0 || (p 1 || (p 2 || false))) = true
    match g, hg with
    | ⟨0, _⟩, hg => have h : p 0 = true := hg; rw [h]; rfl
    | ⟨1, _⟩, hg => have h : p 1 = true := hg; rw [h]; cases p 0 <;> rfl
    | ⟨2, _⟩, hg => have h : p 2 = true := hg; rw [h]; cases p 0 <;> cases p 1 <;> rfl

/-- (B3) **Die freie Belegung p ↦ vec b0 b1 b2 falsifiziert Kaehrs Trennfall genau dann, wenn der Vektor auf je zwei Fasern mit einem
    Wert kohärent ist, auf allen drei mit keinem.** -/
theorem brunn_trennfall (b0 b1 b2 : Bool) :
    (¬ ∀ i : Faser, auswFrei (fun _ => vec b0 b1 b2) trenn i = true) ↔
      ((∀ S ∈ faserPaare, ∃ g : Wert, kohaerentAuf S (vec b0 b1 b2) g = true) ∧
        ¬ ∃ g : Wert, kohaerent (vec b0 b1 b2) g = true) := by
  have t := all_mp (all_mp (all_mp trennfall_inkohaerent b0 (by cases b0 <;> decide)) b1 (by cases b1 <;> decide)) b2
    (by cases b2 <;> decide)
  have e : ([0, 1, 2].all fun (i : Faser) => auswFrei (fun _ => vec b0 b1 b2) trenn i) =
      ([0, 1, 2].any fun (g : Wert) => kohaerent (vec b0 b1 b2) g) := by
    revert t
    cases ([0, 1, 2].all fun (i : Faser) => auswFrei (fun _ => vec b0 b1 b2) trenn i) <;>
      cases ([0, 1, 2].any fun (g : Wert) => kohaerent (vec b0 b1 b2) g) <;> decide
  constructor
  · intro h
    refine ⟨je_zwei_immer b0 b1 b2, fun hg => h (all_iff.mp ?_)⟩
    rw [e]
    exact any_iff.mpr hg
  · intro h ha
    exact h.2 (any_iff.mp (e ▸ all_iff.mpr ha))

/-! ## B4 — an den zwei Vektoren drei verschiedene Werte -/

/-- (B4) **An den zwei unverträglichen Vektoren verlangen die drei Paare drei verschiedene Werte, je einen.** -/
theorem drei_werte :
    (∀ g : Wert, kohaerentAuf [0, 1] (vec true true false) g = true ↔ g = 0) ∧
    (∀ g : Wert, kohaerentAuf [1, 2] (vec true true false) g = true ↔ g = 1) ∧
    (∀ g : Wert, kohaerentAuf [0, 2] (vec true true false) g = true ↔ g = 2) ∧
    (∀ g : Wert, kohaerentAuf [0, 1] (vec false false true) g = true ↔ g = 2) ∧
    (∀ g : Wert, kohaerentAuf [1, 2] (vec false false true) g = true ↔ g = 0) ∧
    (∀ g : Wert, kohaerentAuf [0, 2] (vec false false true) g = true ↔ g = 1) := by
  decide

end Reformulation.Pfalzgraf.BrunnProbe

/-! ## Axiom-Wachen (gemessen, verbatim) -/

/-- info: 'Reformulation.Pfalzgraf.BrunnProbe.kohaerentAuf_alle' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.BrunnProbe.kohaerentAuf_alle

/-- info: 'Reformulation.Pfalzgraf.BrunnProbe.je_zwei_immer' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.BrunnProbe.je_zwei_immer

/-- info: 'Reformulation.Pfalzgraf.BrunnProbe.drei_nicht_genau' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.BrunnProbe.drei_nicht_genau

/-- info: 'Reformulation.Pfalzgraf.BrunnProbe.all_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.BrunnProbe.all_iff

/-- info: 'Reformulation.Pfalzgraf.BrunnProbe.any_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.BrunnProbe.any_iff

/-- info: 'Reformulation.Pfalzgraf.BrunnProbe.brunn_trennfall' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.BrunnProbe.brunn_trennfall

/-- info: 'Reformulation.Pfalzgraf.BrunnProbe.drei_werte' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.BrunnProbe.drei_werte
