import Reformulation.Proemial.NegationCycleTable   -- gerichtet, gerichtet_length; über NegationCycle: negate, origin, tafelVI4/5

/-!
# Proemial.VollzugDurchlaufProbe — der Baum der Anfangsstücke der Vollkreise, bei drei und vier Werten (Eichung)

STANDALONE, NICHT im Aggregat;  Target `Probes`.  AxiomGate unberührt.  Bau nach `KorpusRev2/Prompt_Instanz_Vollzug_Durchlauf_Eichung.md`
(Mathematiker, 25.10.2026 17:49;  Architekt 17:48:  „Eine kleine Eichungs-Sonde mit den Zahlen bei drei und vier Werten per decide.").
Grundlage:  `KorpusRev2/Vollzug_als_Durchlauf_Papier_Mathematiker.md` (17:42) und die Referenzrechnung
`KorpusRev2/T_Vorprobe_Skripte/Vollzug_Durchlauf_v.py`, `…_d.py` (Python).  Konsumiert `NegationCycle` (`negate`, `origin`, `tafelVI4`,
`tafelVI5`) und `NegationCycleTable` (`gerichtet`, die 88 gerichteten Vollkreise bei vier Werten);  ändert nichts davon.

## WAS — die Begriffe (alle berechenbar;  Vergleich über `.val`, choice-frei)

Für eine Liste `K` von Vollkreis-Wörtern (drei Werte:  `[tafelVI4, tafelVI5]`;  vier Werte:  `gerichtet`), N = Länge (6 bzw. 24):

```text
anfang K p          p ist Anfangsstück eines Wortes in K (`pref`)
lebendig            Anfangsstück mit |p| < N  — die Knoten des Baumes
opts K p            die Buchstaben i, für die p ++ [i] Anfangsstück ist;  Vielfachheit vollend K (p ++ [i]) = Zahl der Wörter dazu
Entscheidung        |opts K p| ≥ 2;  entscheidungenWort:  die Zahl der k < N mit Entscheidung an w.take k
Buridan-Lage        Entscheidung, p.map Fin.rev = p, und Fin.rev vertauscht zwei Optionen (i ≠ rev i, beide in opts)
zählgleich          Entscheidung, alle Optionen mit derselben Vollendungszahl (so die Referenzrechnung)
zulässiger Schritt  aus einem Knoten p mit Buchstabe i:  die neue Station (negate i der letzten) ist noch nicht besucht, oder |p| = N − 1
                    und sie ist der Ausgang (origin)
Sackgasse           zulässig, aber p ++ [i] kein Anfangsstück
```

`walk` geht den Baum ab der Wurzel durch und zählt das alles in einem Durchgang (`Stat`);  `entscheidungenWort` zählt die Entscheidungen
eines Wortes direkt an seinen Anfangsstücken — ein zweiter Weg für dieselben Knoten.

## Die Sätze (alle EICHUNG, `decide` bzw. `decide +kernel`)

```text
eich_drei                drei Werte:  2 Wörter;  je Wort 1 Entscheidung;  11 Knoten, 1 Entscheidungsknoten (an der Wurzel, |p| = 0);
                         Buridan-Lagen genau [ [] ];  1 zählgleiche Entscheidung, davon 1 Buridan;  12 zulässige Schritte, 0 Sackgassen;
                         an der Wurzel N1: 1, N2: 1;  an ω-festen Knoten haben i und rev i dieselbe Vollendungszahl
eich_vier_woerter        vier Werte:  88 Wörter (gerichtet_length, Bestand);  Entscheidungen je Wort:  5 bei 34, 6 bei 10, 7 bei 28, 8 bei 16
eich_vier_baum           1494 Knoten, 86 Entscheidungsknoten, die tiefste bei |p| = 13 (ab |p| = 14 keine);  59 zählgleiche
                         Entscheidungen, davon 1 Buridan;  2017 zulässige Schritte, 436 Sackgassen;  an ω-festen Knoten haben i und
                         rev i dieselbe Vollendungszahl
eich_vier_buridan        die Buridan-Lagen genau [ [], [N2] ]
eich_vier_sackgassen     die Sackgassen nach Tiefe |p| = 3 … 20:  2, 6, 16, 18, 26, 34, 30, 32, 36, 40, 34, 38, 34, 34, 20, 20, 8, 8
eich_vier_wurzel         an der Wurzel N1: 26, N2: 36, N3: 26;  an [N2]:  N1: 18, N3: 18
```

Die Zahlen sind gemessen, nicht eingesetzt:  der Prototyp (`#eval`, 25.10., nach 17:50, vor dem Bau) hat jede Zahl der Referenzrechnung des Mathematikers
getroffen, bevor sie hier als Satz steht.  Die Knotenzahlen (11, 1494) nennt die Referenz nicht;  sie sind zusätzlich gemessen.

## QUELLE, am Bild (Hermeneutes)

- „Als Wille" PDF 4:  *„Da in einer heterarchischen Kreisordnung jeder Anfang eine Willkürwahl darstellt (und, ist einmal ein Anfangspunkt
  gewählt, es keinen originären Grund gibt, zu entscheiden, ob der Kreis links- oder rechtsläufig durchlaufen werden soll) …"*
- IGN S. 31:  *„das noch nicht in einer Entscheidung vollzogene Umtauschverhältnis"* (SETZUNG des Architekten 25.10. 16:59:  das Haus bindet
  „Vollzug" an diese Stelle).
- IGN S. 32:  *„jeder Schritt von links nach rechts durch eine der beiden Tauschoperationen vollzogen"*;  S. 41:  *„die Prozeduren in einer
  Reihenfolge vollzogen"* — der Kreis wird DURCHLAUFEN, seine Schritte werden VOLLZOGEN (Hermeneutes AWV-7).

## ZUORDNUNG

Baum der Anfangsstücke = der Vollzug eines Durchlaufs;  Entscheidung = Knoten mit ≥ 2 Fortsetzungen;  Buridan-Lage = Alternativen durch ω
vertauscht (ω ist neben der Identität die Symmetrie des Negatorsystems:  `OrdnungAusUmtauschProbe.ordnung_aus_umtausch_zwei`).
**Ungeprüft an der Quelle.**

## MARKE

EICHUNG von „Als Wille" PDF 4 (drei Werte:  eine Entscheidung, Buridan, danach erzwungen) und von IGN S. 31 f.

## LESART (getrennt, aus dem Papier §3, nicht als Satz)

Ab vier Werten hat der Vollzug Gestalt (Entscheidungen am Anfang, Ende erzwungen), nur zwei Buridan-Lagen, und ein Schritt ohne Voraussicht
kann den Kreis verfehlen.  C&V Druck S. 214 (*„a volitive system needs an image of the world in order to make decisions"*, am Bild) nur als
ZUSAMMENSCHAU-Hinweis.

## NICHT

Kein Träger für §20;  keine Verbindung zum Turm (die Beobachtung „der Turm kennt keine Sackgasse" bleibt im Papier);  kein Text in Rev11.
**Verboten:**  „Vollzug formalisiert";  „der Akt ist gebaut";  „Buridan bewiesen" (statt:  an drei Werten nachgerechnet);  „der Wille
scheitert";  „Willkürwahl bewiesen" ohne „bei drei Werten, Eichung".

## Bauweise

Ein Durchgang `walk` über den Baum bei vier Werten kostet im Kernel rund 18 s (gemessen 25.10.);  die Zahlen eines Durchgangs stehen darum in
einem Tupel (`zahlen`) und werden in EINEM `decide +kernel` geprüft.  Kein `native_decide`.

Kein `sorry`, kein `Classical.choice`, kein `native_decide`, kein True-Feld.
-/

namespace Reformulation.Proemial.VollzugDurchlaufProbe

open Reformulation.Proemial.NegationCycle Reformulation.Proemial.NegationCycleTable

variable {m : ℕ}

/-! ## Die Begriffe -/

/-- p ist Anfangsstück von w (Vergleich über `.val`) -/
def pref : List (Fin m) → List (Fin m) → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: p, b :: w => Nat.beq a.val b.val && pref p w

/-- Gleichheit zweier Listen über `.val` -/
def gleichL {k : ℕ} : List (Fin k) → List (Fin k) → Bool
  | [], [] => true
  | a :: p, b :: w => Nat.beq a.val b.val && gleichL p w
  | _, _ => false

/-- die Zahl der Wörter in K mit dem Anfangsstück q -/
def vollend (K : List (List (Fin m))) (q : List (Fin m)) : ℕ := K.countP (pref q)

/-- die Optionen an p:  die Buchstaben, nach denen p Anfangsstück bleibt -/
def opts (K : List (List (Fin m))) (p : List (Fin m)) : List (Fin m) :=
  (List.finRange m).filter fun i => K.any (pref (p ++ [i]))

/-- Entscheidung:  mindestens zwei Optionen -/
def entscheidung (K : List (List (Fin m))) (p : List (Fin m)) : Bool := Nat.blt 1 (opts K p).length

/-- die Entscheidungen eines Wortes:  an wie vielen seiner Anfangsstücke der Länge k < N entschieden wird -/
def entscheidungenWort (K : List (List (Fin m))) (N : ℕ) (w : List (Fin m)) : ℕ :=
  (List.range N).countP fun k => entscheidung K (w.take k)

/-- Buridan-Lage:  Entscheidung an einem ω-festen Anfangsstück, und ω vertauscht zwei Optionen -/
def istBuridan (K : List (List (Fin m))) (p : List (Fin m)) : Bool :=
  entscheidung K p && gleichL (p.map Fin.rev) p &&
    (opts K p).any fun i => !(Nat.beq (Fin.rev i).val i.val) && (opts K p).any fun j => Nat.beq j.val (Fin.rev i).val

/-- zählgleich:  Entscheidung, alle Optionen mit derselben Vollendungszahl -/
def istZaehlgleich (K : List (List (Fin m))) (p : List (Fin m)) : Bool :=
  entscheidung K p && match opts K p with
    | [] => true
    | i :: r => r.all fun j => Nat.beq (vollend K (p ++ [j])) (vollend K (p ++ [i]))

/-- an einem ω-festen Anfangsstück:  i und rev i haben dieselbe Vollendungszahl -/
def omegaGleich (K : List (List (Fin m))) (p : List (Fin m)) : Bool :=
  !(gleichL (p.map Fin.rev) p) ||
    (List.finRange m).all fun i => Nat.beq (vollend K (p ++ [i])) (vollend K (p ++ [Fin.rev i]))

/-! ## Der Durchgang durch den Baum -/

/-- die Zahlen eines Durchgangs -/
structure Stat (m : ℕ) where
  knoten : ℕ
  entsch : ℕ
  tiefsteEntsch : ℕ
  buridan : List (List (Fin m))
  zaehlgleich : ℕ
  zaehlgleichBuridan : ℕ
  zul : ℕ
  sack : ℕ
  sackTiefen : List ℕ
  omegaUngleich : ℕ

def Stat.null : Stat m := ⟨0, 0, 0, [], 0, 0, 0, 0, [], 0⟩

def Stat.plus (a b : Stat m) : Stat m :=
  ⟨a.knoten + b.knoten, a.entsch + b.entsch, max a.tiefsteEntsch b.tiefsteEntsch, a.buridan ++ b.buridan,
   a.zaehlgleich + b.zaehlgleich, a.zaehlgleichBuridan + b.zaehlgleichBuridan, a.zul + b.zul, a.sack + b.sack,
   a.sackTiefen ++ b.sackTiefen, a.omegaUngleich + b.omegaUngleich⟩

/-- **der Durchgang** ab dem Knoten p, mit der Station st und den besuchten Stationen;  Brennstoff = verbleibende Tiefe -/
def walk (K : List (List (Fin m))) (N : ℕ) : ℕ → List (Fin m) → List (Fin (m + 1)) → List (List (Fin (m + 1))) → Stat m
  | 0, _, _, _ => Stat.null
  | f + 1, p, st, seen =>
    let hier : Stat m := ⟨1, if entscheidung K p then 1 else 0, if entscheidung K p then p.length else 0,
      if istBuridan K p then [p] else [], if istZaehlgleich K p then 1 else 0,
      if istZaehlgleich K p && istBuridan K p then 1 else 0, 0, 0, [], if omegaGleich K p then 0 else 1⟩
    (List.finRange m).foldl (fun acc i =>
      let q := negate i st
      let zul := (Nat.beq (p.length + 1) N && gleichL q (origin m)) || (Nat.blt (p.length + 1) N && !(seen.any (gleichL q)))
      if !zul then acc else
      let lebt := K.any (pref (p ++ [i]))
      let acc := acc.plus ⟨0, 0, 0, [], 0, 0, 1, if lebt then 0 else 1, if lebt then [] else [p.length], 0⟩
      if lebt && Nat.blt (p.length + 1) N then acc.plus (walk K N f (p ++ [i]) q (q :: seen)) else acc) hier

/-- die Zahlen eines Durchgangs als Liste (für einen gemeinsamen `decide`):  Knoten, Entscheidungen, tiefste Entscheidung, zählgleich,
    davon Buridan, zulässige Schritte, Sackgassen, ω-Ungleichheiten -/
def zahlen (s : Stat m) : List ℕ :=
  [s.knoten, s.entsch, s.tiefsteEntsch, s.zaehlgleich, s.zaehlgleichBuridan, s.zul, s.sack, s.omegaUngleich]

/-- die Buridan-Lagen als Listen von Zahlen (Lean-Index:  0 = N1, 1 = N2, …) -/
def buridanLagen (s : Stat m) : List (List ℕ) := s.buridan.map (·.map Fin.val)

/-- die Vollkreise bei drei Werten -/
def kreise3 : List (List (Fin 2)) := [tafelVI4, tafelVI5]

/-! ## Eichungen -/

/-- **Drei Werte.**  Zwei Wörter, je eine Entscheidung;  der Baum:  11 Knoten, eine Entscheidung (an der Wurzel), Buridan an der Wurzel,
    eine zählgleiche Entscheidung (Buridan), 12 zulässige Schritte, keine Sackgasse, ω-Gleichheit überall;  an der Wurzel 1 : 1. -/
theorem eich_drei :
    kreise3.length = 2 ∧ kreise3.map (entscheidungenWort kreise3 6) = [1, 1] ∧
    zahlen (walk kreise3 6 6 [] (origin 2) [origin 2]) = [11, 1, 0, 1, 1, 12, 0, 0] ∧
    buridanLagen (walk kreise3 6 6 [] (origin 2) [origin 2]) = [[]] ∧
    (List.finRange 2).map (fun i => vollend kreise3 [i]) = [1, 1] := by
  decide

/-- **Vier Werte, die Wörter.**  88 gerichtete Vollkreise;  Entscheidungen je Wort:  5 bei 34, 6 bei 10, 7 bei 28, 8 bei 16. -/
theorem eich_vier_woerter :
    gerichtet.length = 88 ∧
    ((gerichtet.map (entscheidungenWort gerichtet 24)).count 5, (gerichtet.map (entscheidungenWort gerichtet 24)).count 6,
     (gerichtet.map (entscheidungenWort gerichtet 24)).count 7, (gerichtet.map (entscheidungenWort gerichtet 24)).count 8) =
      (34, 10, 28, 16) := by
  decide +kernel

/-- **Vier Werte, der Baum.**  1494 Knoten, 86 Entscheidungsknoten, der tiefste bei |p| = 13;  Buridan-Lagen genau an `[]` und `[N2]`;
    59 zählgleiche Entscheidungen, davon eine Buridan;  2017 zulässige Schritte, 436 Sackgassen;  ω-Gleichheit an jedem ω-festen Knoten. -/
theorem eich_vier_baum :
    zahlen (walk gerichtet 24 24 [] (origin 3) [origin 3]) = [1494, 86, 13, 59, 1, 2017, 436, 0] := by
  decide +kernel

/-- **Vier Werte, die Buridan-Lagen:**  genau `[]` (N1 | N3) und `[N2]` (N1 | N3). -/
theorem eich_vier_buridan : buridanLagen (walk gerichtet 24 24 [] (origin 3) [origin 3]) = [[], [1]] := by
  decide +kernel

/-- **Vier Werte, die Sackgassen nach Tiefe** |p| = 3 … 20 (keine bei 0 … 2 und 21 … 23). -/
theorem eich_vier_sackgassen :
    (List.range 24).map (fun d => (walk gerichtet 24 24 [] (origin 3) [origin 3]).sackTiefen.count d) =
      [0, 0, 0, 2, 6, 16, 18, 26, 34, 30, 32, 36, 40, 34, 38, 34, 34, 20, 20, 8, 8, 0, 0, 0] := by
  decide +kernel

/-- **Vier Werte, die Wurzel und `[N2]`:**  N1 : N2 : N3 = 26 : 36 : 26;  nach N2:  N1 : N3 = 18 : 18 (N2 ist dort keine Option). -/
theorem eich_vier_wurzel :
    (List.finRange 3).map (fun i => vollend gerichtet [i]) = [26, 36, 26] ∧
    (List.finRange 3).map (fun i => vollend gerichtet [1, i]) = [18, 0, 18] := by
  decide

end Reformulation.Proemial.VollzugDurchlaufProbe

/-! ## Axiom-Wachen (gemessen, verbatim) -/

/-- info: 'Reformulation.Proemial.VollzugDurchlaufProbe.eich_drei' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.VollzugDurchlaufProbe.eich_drei

/-- info: 'Reformulation.Proemial.VollzugDurchlaufProbe.eich_vier_woerter' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.VollzugDurchlaufProbe.eich_vier_woerter

/-- info: 'Reformulation.Proemial.VollzugDurchlaufProbe.eich_vier_baum' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.VollzugDurchlaufProbe.eich_vier_baum

/-- info: 'Reformulation.Proemial.VollzugDurchlaufProbe.eich_vier_buridan' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.VollzugDurchlaufProbe.eich_vier_buridan

/-- info: 'Reformulation.Proemial.VollzugDurchlaufProbe.eich_vier_sackgassen' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.VollzugDurchlaufProbe.eich_vier_sackgassen

/-- info: 'Reformulation.Proemial.VollzugDurchlaufProbe.eich_vier_wurzel' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.VollzugDurchlaufProbe.eich_vier_wurzel
