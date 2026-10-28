import Reformulation.Proemial.GegenidentitaetProbe   -- umkehr, dreh;  über ThreeCycle:  stations_append_list, endpoint_append_list

/-!
# Proemial.DrehsinnUmkehrProbe — Drehsinn und Umkehr am zweiten Kreis;  die Stationen des rückwärts gelesenen Worts

STANDALONE, NICHT im Aggregat;  Target `Probes`.  AxiomGate unberührt.  Sonde nach `KorpusRev2/Prompt_Instanz_Drehsinn_Umkehr_kreis2.md`
(Mathematiker, 28.10.2026 20:58;  Fragen 16, 17 zu Kapitel 8).  Herkunft der Zahlen:  `T_Vorprobe_Skripte/Kanten_Kreis2_Umkehr_Drehsinn.py`
(gerechnet, Mathematiker).  Konsumiert `NegationCycle` (`kreis2`, `stations`, `endpoint`, `negate`, `origin`, `endpoint_reverse`),
`GegenidentitaetProbe` (`umkehr`, `dreh`), `NegationCycleThreeCycle` (`stations_append_list`);  ändert nichts davon.

## WAS

```text
D1  kreis2_drehungen       EICHUNG (decide)      umkehr kreis2 = kreis2.rotate 4 ∧ dreh kreis2 = kreis2.rotate 7.  Per decide, NICHT aus
                                                 sjt3_mirror_kreis2 und SpurProbe.sjt_vier_drehungen (der Weg ginge auch;  decide ist
                                                 kürzer und hängt an keiner Fremdeichung)
D2  stations_reverse_allg  SATZ, jede Wertzahl   stations w.reverse (endpoint w l) = ((stations w l ++ [endpoint w l]).drop 1).reverse —
                                                 die gleichwertige Form OHNE Schließbedingung:  das rückwärts gelesene Wort durchläuft vom
                                                 Endpunkt aus dieselben Stationen in umgekehrter Folge
    stations_reverse       SATZ, jede Wertzahl   die Form des Auftrags:  endpoint w l = l → w ≠ [] →
                                                 stations w.reverse l = l :: ((stations w l).drop 1).reverse.  `w ≠ []` ist NÖTIG:  das
                                                 leere Wort schließt, hat aber keine Station (links [], rechts [l])
D3  kanten_kreis2          EICHUNG (decide)      kreis2 und umkehr kreis2, beide ab dem Ausgang, teilen 14 ihrer 24 Kanten (ohne Richtung);
                                                 die Kanten der Umkehr ab dem Ausgang sind genau die von kreis2 ab der Anordnung 1, 2, 3, 0
```

In Worten:  **Am zweiten Kreis sind Umkehr und Drehsinn Drehungen des Kreises selbst;  der Drehsinn läuft dieselben Stationen in umgekehrter
Folge (jedes schließende Wort);  die Umkehr läuft ab dem Ausgang einen anderen Weg über das Permutoeder — 14 von 24 Kanten gemeinsam —,
nämlich den Weg des Kreises ab einer anderen Anordnung.**

Hilfssatz:  `stations_kopf`.  Definitionen:  `kanten`, `gemeinsam`.  Profile:  alle fünf Sätze ohne `Classical.choice` (Wachen unten).
Kein `native_decide`, kein `sorry`, kein True-Feld.

## NICHT

Kein Bezug der Kanten auf Günthers Begriffe (Gegenidentität, Ich/Du);  D3 ist eine Eichung an EINEM Kreis, kein Satz über die 88.
-/

namespace Reformulation.Proemial.DrehsinnUmkehrProbe

open Reformulation.Proemial.NegationCycle
open Reformulation.Proemial.GegenidentitaetProbe (umkehr dreh)
open Reformulation.Proemial.NegationCycleThreeCycle (stations_append_list endpoint_append_list)

/-! ## D1 — am zweiten Kreis sind Umkehr und Drehsinn Drehungen -/

/-- (D1) **Am emendierten zweiten Kreis sind Umkehr und Drehsinn Drehungen des Kreises selbst:**  die Umkehr um vier Wechsel, der
    Drehsinn um sieben. -/
theorem kreis2_drehungen : umkehr kreis2 = kreis2.rotate 4 ∧ dreh kreis2 = kreis2.rotate 7 := by
  decide

/-! ## D2 — die Stationen des rückwärts gelesenen Worts -/

theorem stations_kopf {m : ℕ} : ∀ (w : List (Fin m)) (x : List (Fin (m + 1))),
    ∃ Y, stations w x ++ [endpoint w x] = x :: Y
  | [], _ => ⟨[], rfl⟩
  | _ :: _, _ => ⟨_, rfl⟩

/-- (D2, allgemein) **Das rückwärts gelesene Wort durchläuft dieselben Stationen in umgekehrter Folge:**  vom Endpunkt aus gelesen, ohne
    Schließbedingung. -/
theorem stations_reverse_allg {m : ℕ} : ∀ (w : List (Fin m)) (l : List (Fin (m + 1))),
    stations w.reverse (endpoint w l) = ((stations w l ++ [endpoint w l]).drop 1).reverse
  | [], _ => rfl
  | a :: w, l => by
    have ih := stations_reverse_allg w (negate a l)
    obtain ⟨Y, hY⟩ := stations_kopf w (negate a l)
    rw [List.reverse_cons, stations_append_list]
    show stations w.reverse (endpoint w (negate a l)) ++ stations [a] (endpoint w.reverse (endpoint w (negate a l))) =
      ((l :: (stations w (negate a l) ++ [endpoint w (negate a l)])).drop 1).reverse
    rw [ih, endpoint_reverse, hY, List.drop_one, List.tail_cons, List.drop_one, List.tail_cons, List.reverse_cons]
    rfl

/-- (D2) **Für ein schließendes, nicht leeres Wort:**  die Stationen des rückwärts gelesenen Worts sind dieselben, in umgekehrter Folge.
    (`w ≠ []` ist nötig:  das leere Wort schließt, hat aber keine Station.) -/
theorem stations_reverse {m : ℕ} (w : List (Fin m)) (l : List (Fin (m + 1))) (h : endpoint w l = l) (hw : w ≠ []) :
    stations w.reverse l = l :: ((stations w l).drop 1).reverse := by
  have e := stations_reverse_allg w l
  rw [h] at e
  rw [e]
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hw
  show ((l :: stations t (negate a l) ++ [l]).drop 1).reverse = _
  rw [List.cons_append, List.drop_one, List.tail_cons, List.reverse_append]
  rfl

/-! ## D3 — die Kanten:  Umkehr und Drehsinn am Permutoeder -/

/-- **Die Kanten eines Worts ab x:**  die Paare aufeinanderfolgender Stationen, mit der schließenden Kante. -/
def kanten {m : ℕ} (w : List (Fin m)) (x : List (Fin (m + 1))) : List (List (Fin (m + 1)) × List (Fin (m + 1))) :=
  let S := stations w x ++ [endpoint w x]
  S.zip S.tail

/-- Wie viele Kanten von E₁ (ohne Richtung) auch Kanten von E₂ sind. -/
def gemeinsam {α : Type} [DecidableEq α] (E₁ E₂ : List (α × α)) : ℕ :=
  (E₁.filter (fun e => decide (e ∈ E₂ ∨ (e.2, e.1) ∈ E₂))).length

/-- (D3) **Der zweite Kreis und seine Umkehr, beide ab dem Ausgang, teilen 14 ihrer 24 Kanten;  die Kanten der Umkehr ab dem Ausgang
    sind (ohne Richtung) genau die Kanten des zweiten Kreises ab der Anordnung 1, 2, 3, 0.** -/
theorem kanten_kreis2 :
    gemeinsam (kanten kreis2 (origin 3)) (kanten (umkehr kreis2) (origin 3)) = 14 ∧
    (∀ e ∈ kanten (umkehr kreis2) (origin 3), e ∈ kanten kreis2 [1, 2, 3, 0] ∨ (e.2, e.1) ∈ kanten kreis2 [1, 2, 3, 0]) ∧
    (∀ e ∈ kanten kreis2 [1, 2, 3, 0], e ∈ kanten (umkehr kreis2) (origin 3) ∨ (e.2, e.1) ∈ kanten (umkehr kreis2) (origin 3)) := by
  decide +kernel

end Reformulation.Proemial.DrehsinnUmkehrProbe

/-! ## Axiom-Wachen (gemessen, verbatim) -/

/-- info: 'Reformulation.Proemial.DrehsinnUmkehrProbe.kreis2_drehungen' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.DrehsinnUmkehrProbe.kreis2_drehungen

/-- info: 'Reformulation.Proemial.DrehsinnUmkehrProbe.stations_kopf' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Proemial.DrehsinnUmkehrProbe.stations_kopf

/-- info: 'Reformulation.Proemial.DrehsinnUmkehrProbe.stations_reverse_allg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.DrehsinnUmkehrProbe.stations_reverse_allg

/-- info: 'Reformulation.Proemial.DrehsinnUmkehrProbe.stations_reverse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.DrehsinnUmkehrProbe.stations_reverse

/-- info: 'Reformulation.Proemial.DrehsinnUmkehrProbe.kanten_kreis2' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.DrehsinnUmkehrProbe.kanten_kreis2
