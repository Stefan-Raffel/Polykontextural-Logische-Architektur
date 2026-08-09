import Reformulation.Kenogram.PairStageBound

/-!
# Reformulation.Kenogram.PartitionCount — die Zahl der Mengenpartitionen von `Fin n`

**Ertrag, mit benannter Grenze.** Die Saetze dieses Moduls stehen so nicht in Mathlib;
gewonnen sind sie aber nicht hier, sondern in der Berechnungs-Reihe ueber `RGS n`
(`Kenogram/Basic.lean`, `Kenogram/Fillability.lean`, `Kenogram/PairStageBound.lean`). Dieses
Modul **transportiert** sie laengs des Repraesentations-Theorems `rgs_equiv_partition` auf
den Mathlib-Typ. Der PKL-Begriff, ohne den es die Zahlen nicht gaebe, ist die RGS-Normalform;
die Aussage selbst kaeme auch ohne ihn aus.

## Was diese Saetze nicht sagen

Die Bell-Zahl kommt in ihnen nicht vor. Dass `Nat.bell n` die Partitionen einer `n`-Menge
zaehlt, ist **nicht** bewiesen — weder hier noch in Mathlib, das diese Aussage in
`Combinatorics/Enumerative/Bell.lean` als offenen Posten fuehrt. Bewiesen ist allein, dass
zwei Typen gleich viele Elemente haben, und fuer kleine `n`, wie viele.

## Woher die Zahlen kommen

Aus der Berechnungs-Reihe ueber `RGS`, nicht aus einer Zaehlung der Partitionen. Die vier
Traeger sind `KPS.card_rgs_two`, `KPS.card_rgs_three`, `KF.card_rgs_four` und
`KPS.card_rgs_five`; hier wird nichts neu ausgerechnet und keine Marke gedoppelt. **Der Satz
transportiert die Zahlen, er gewinnt sie nicht.**

Gesetzt sind darum genau die vier Werte, fuer die ein benannter Traeger vorliegt. `n = 0` und
`n = 1` fehlen nicht aus einem sachlichen Grund, sondern weil es fuer sie keinen Traeger gibt
— in `Kenogram/Basic.lean` stehen sie als `example` ohne Namen. Eine neue `decide`-Marke
dafuer waere eine gedoppelte Rechnung.

## Warum der Weg der interessantere ist

Mathlib traegt fuer `Finpartition s` eine `Fintype`-Instanz
(`Order/Partition/Finpartition.lean`), und sie laeuft ueber `s.powerset.powerset`: bei
`n = 5` sind das `2 ^ (2 ^ 5) = 4294967296` Kandidaten. Die Instanz selbst fuehrt dazu einen
TODO-Vermerk zur Laufzeit. Der Weg ueber `RGS` geht statt dessen ueber den Generator
`rgsList`. Beide Male ist dieselbe Zahl das Ergebnis; verschieden ist, was durchsucht wird.

## Was hier nicht steht

Kein Zielsatz der Bell-Bruecke, auch nicht teilweise, und keine Vorbereitung dazu. Was dafuer
fehlt, steht mit Bausteinliste ausserhalb des Korpus in der Merkliste zur achten Ausgabe.

## Zur Benennung

`card_...` heisst hier `Fintype.card` — die Zahl der Partitionen. **In Mathlibs
`Finpartition`-Namensraum heisst `card_...` etwas anderes**: dort zaehlen `card_bot`,
`card_extend`, `card_bind` und `card_mono` die **Bloecke einer** Partition (`#P.parts`). Die
Namen hier stehen in einem eigenen Namensraum und schreiben `Fintype.card` aus; die
Doppeldeutigkeit ist gemessen und benannt, nicht beseitigt.

## Profile

`rgs_equiv_partition` traegt `[propext, Classical.choice, Quot.sound]`, und die Wachen unten
erben es. Gemessen, nicht erwartet.

Kein `sorry`, kein `axiom`, kein `: True`-Feld.
-/

open Finset

namespace Reformulation.Kenogram.PartitionCount

/-- **Z1 — die halbe Bruecke.** Die RGS-Reihen der Laenge `n` und die Mengenpartitionen von
`Fin n` sind gleich viele. Unmittelbar aus dem Repraesentations-Theorem; die Bell-Zahl kommt
darin nicht vor (siehe Dateikopf). -/
theorem card_rgs_eq_card_finpartition (n : ℕ) :
    Fintype.card (RGS n) = Fintype.card (Finpartition (univ : Finset (Fin n))) :=
  Fintype.card_congr (rgs_equiv_partition n)

/-- Zwei Partitionen von `Fin 2`; Traeger `KPS.card_rgs_two`. -/
theorem card_finpartition_fin_two :
    Fintype.card (Finpartition (univ : Finset (Fin 2))) = 2 := by
  rw [← card_rgs_eq_card_finpartition 2]; exact PairStageBound.card_rgs_two

/-- Fuenf Partitionen von `Fin 3`; Traeger `KPS.card_rgs_three`. -/
theorem card_finpartition_fin_three :
    Fintype.card (Finpartition (univ : Finset (Fin 3))) = 5 := by
  rw [← card_rgs_eq_card_finpartition 3]; exact PairStageBound.card_rgs_three

/-- Fuenfzehn Partitionen von `Fin 4`; Traeger `KF.card_rgs_four`. -/
theorem card_finpartition_fin_four :
    Fintype.card (Finpartition (univ : Finset (Fin 4))) = 15 := by
  rw [← card_rgs_eq_card_finpartition 4]; exact Fillability.card_rgs_four

/-- **Z2 — der Fall, an dem der Unterschied sitzt.** Zweiundfuenfzig Partitionen von `Fin 5`;
Traeger `KPS.card_rgs_five`. Ueber den Generator gerechnet statt ueber die
`powerset.powerset`-Aufzaehlung der Mathlib-Instanz (siehe Dateikopf). -/
theorem card_finpartition_fin_five :
    Fintype.card (Finpartition (univ : Finset (Fin 5))) = 52 := by
  rw [← card_rgs_eq_card_finpartition 5]; exact PairStageBound.card_rgs_five

/-! ## Statement-Pins -/

-- STATEMENT-PIN
example (n : ℕ) :
    Fintype.card (RGS n) = Fintype.card (Finpartition (univ : Finset (Fin n))) :=
  card_rgs_eq_card_finpartition n

-- STATEMENT-PIN
example : Fintype.card (Finpartition (univ : Finset (Fin 5))) = 52 :=
  card_finpartition_fin_five

/-! ## Verifikation -/

/-- info: 'Reformulation.Kenogram.PartitionCount.card_rgs_eq_card_finpartition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms card_rgs_eq_card_finpartition

/-- info: 'Reformulation.Kenogram.PartitionCount.card_finpartition_fin_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms card_finpartition_fin_two

/-- info: 'Reformulation.Kenogram.PartitionCount.card_finpartition_fin_three' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms card_finpartition_fin_three

/-- info: 'Reformulation.Kenogram.PartitionCount.card_finpartition_fin_four' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms card_finpartition_fin_four

/-- info: 'Reformulation.Kenogram.PartitionCount.card_finpartition_fin_five' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms card_finpartition_fin_five

end Reformulation.Kenogram.PartitionCount
