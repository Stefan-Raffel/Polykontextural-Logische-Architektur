import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.EquivFin
import Reformulation.Kenogram.Fillability

/-!
# Kenogram.PairStageBound — die Paare einer Stufe und die nächste Stufe

**Ertrag.** Drei Kardinalitätsaussagen über den RGS-Stufen, dazu die drei
benannten Träger der Stufenzahlen, die dem Bestand bisher fehlten.

* **Z1** (`no_injective_pair_three`) — keine Abbildung der **geordneten Paare**
  von `RGS 3` nach `RGS 4` ist injektiv. Der Abstand ist `25 > 15`.
* **Z2** (`no_injective_pair_four`) — dasselbe eine Stufe höher, `225 > 52`.
* **Z3** (`exists_injective_pair_two`) — unterhalb gibt es eine injektive
  Abbildung: `RGS 2 × RGS 2` nach `RGS 3`, `4 ≤ 5`. Nichtkonstruktiv; eine
  explizite Abbildung ist nicht gebaut, weil kein Satz sie fordert.

**Z3 ist nicht Zierat.** Ohne ihn wäre Z1 eine Aussage über eine Stufe; mit ihm
ist es eine Aussage über einen **Umschlag**. Die Schwelle ist damit gemessen und
nicht bloss der kleinste geprüfte Fall.

## Die Grenzformel

**Bewiesen ist eine Kardinalitätsschranke zwischen den RGS-Stufen; dass die
Vier-Relata-Bewegung diese Gestalt hat, ist Lesart und nicht Gegenstand des
Satzes.**

Und was Z1 sagt, sagt er wörtlich: **es gibt keine injektive Abbildung** — mehr
nicht. Kein Satz dieses Moduls redet von einer Bewegung, von einem Aufstieg oder
von etwas, das verlorenginge.

## Die Präzedenz, benannt und nicht in Anspruch genommen

`Proemial.ArrowAscent.arrow_left_not_injective` trägt dieselbe **Gestalt** im
kategorialen Strang: eine Ordnung höher wird ein Morphismus zum Objekt, und die
Abbildung zurück auf die Quelle ist nicht injektiv. Hier steht die
kenogrammatische Entsprechung.

**Der eine Satz stützt den anderen nicht.** Sie teilen die Form `¬ Injective`
und sonst nichts: der eine läuft über die Pfeilkategorie von `Type`, dieser über
endliche Kardinalitäten. Es geht kein Term des einen in den anderen ein, und aus
keinem folgt der andere.

## Der Vermerk zur Koinzidenz — Apparat, kein Satz

Die Sätze lesen das Paar als **geordnetes** Paar. Das ist eine **Setzung über
die Lesart**, getroffen ausserhalb dieses Moduls; die Quelle entscheidet die
Frage an der einschlägigen Stelle nicht.

Unter der **ungeordneten** Lesart stünde bei `n = 3` nicht `25 > 15`, sondern
`B(3)·(B(3)+1)/2 = 15 = B(4)` — Injektivität wäre dort möglich, aber nur als
Bijektion, und der Umschlag läge zwischen `n = 3` und `n = 4`. Die Gleichung
`B(n)·(B(n)+1)/2 = B(n+1)` gilt für `n = 3` und **für kein weiteres `n ≤ 9`**;
sie ist ein Einzelfall und kein Gesetz.

**Beide Zahlen sind ausserhalb des Korpus gerechnet und bleiben draussen**
(`CLAUDE.md` §6): sie stehen hier als Apparat zur Lesart und nicht als Aussage.
Der Vermerk sagt, dass die Schwelle lesartabhängig ist und welche Lesart dieses
Modul setzt. Er sagt **nicht**, dass die andere Lesart widerlegt wäre.

## Die zwei Dreien — sie meinen nicht dasselbe

An zwei Stellen des Korpus kippt etwas bei einer Drei, und die beiden Dreien
gehören verschiedenen Grössen:

* **`n` ist die Länge** — die Stellenzahl einer Reihe, also die Stufe `RGS n`.
  Hier kippt es zwischen `n = 2` und `n = 3` (Z1 gegen Z3).
* **`m` ist die Wertzahl** — die Grösse des Trägers, auf dem Operationen
  laufen. Dort kippt das diskonturale Regime zwischen `m = 3` und `m = 4`
  (`Proemial.RegimeThreshold`).

**Verschiedene Grössen, verschiedene Übergänge, keine gemeinsame Aussage.** Wer
die Ziffern nebeneinanderstellt, stellt zwei Dinge nebeneinander, die nichts
miteinander zu tun haben.

## Deutungsgrenzen

**Eine Kopplung ist kein Grund.** Diese Sätze konstituieren **keine**
Proemialrelation.

Die Rede vom **Vergessen** ist Lesart und kommt in keiner Aussage dieses Moduls
vor. Bewiesen ist die Nichtexistenz einer injektiven Abbildung zwischen zwei
endlichen Typen; dass eine Bewegung von Relatoren und Relata diese Gestalt habe,
steht hier nicht und folgt hieraus nicht.

## Was die drei Stufenzahlen hier sollen

`Fintype.card (RGS n)` stand für `n = 1, 2, 3, 4, 5` bisher als anonyme
Berechnungs-Reihe in `Kenogram/Basic.lean` und für `n = 4` zusätzlich als
benannter Satz in `Kenogram/Fillability.lean`. Ein anonymes Beispiel ist keine
konsumierbare Quelle; darum tragen `card_rgs_two`, `card_rgs_three` und
`card_rgs_five` die drei hier gebrauchten Zahlen unter einem Namen, und
`card_rgs_four` wird aus `Fillability` **konsumiert** statt neu bewiesen.

Alle drei laufen per `decide` über den korrekt bewiesenen Generator `rgsList`
(`mem_rgsList_iff`), wie die Reihe in `Basic.lean`. Das ist keine importierte
Kardinalzahl, sondern eine aus der Definition gerechnete — dieselbe Rubrik, in
der `Fillability` seine Zählungen führt.

## Profil

Alle sechs Sätze tragen `[propext, Classical.choice, Quot.sound]`, und der
`Classical.choice` ist **geerbt**: die `Fintype`-Instanz `instFintypeRGS` trägt
ihn (gemessen, Wache in `Basic.lean`), und jedes `decide` über ihr erbt ihn.
Ein choice-freier Weg wurde nicht gesucht; er bräuchte eine andere
`Fintype`-Instanz und damit einen Eingriff in `Basic.lean`.

**Gemessen und nicht erwartet, gegen die Vorlage der Berechnungs-Reihe:** die
Marken in `Basic.lean` setzen für `n = 4` und `n = 5` `maxRecDepth` auf 4000
beziehungsweise 8000. Am HEAD trägt `decide` für `n = 2, 3, 4, 5` je in einer
eigenen Datei **ohne** die Option; dieses Modul setzt sie darum nicht. Die
Marken in `Basic.lean` sind nicht angefasst und nicht nachgemessen.

## Warum das Modul im Kenogram-Zweig liegt

Gemessen an den Kopfzeilen: der Proemial-Zweig importiert `Kenogram`, der
Kenogram-Zweig importiert **nie** `Proemial`. Dieses Modul konsumiert
`Kenogram.Fillability` und aus Mathlib die Produkt- und Einbettungs-Lemmata;
nichts aus `Proemial` geht ein — die Präzedenz oben ist im Text genannt und
nicht importiert. Der Ort ist damit durch die Importrichtung bestimmt.

## Aggregat-Reife

Konsumiert `Kenogram.Fillability` — Aggregat — sowie Mathlib. Keine Sonde, keine
Setzung.

Kein `sorry`, kein `axiom`, kein `: True`-Feld.
-/

namespace Reformulation.Kenogram.PairStageBound

open Reformulation.Kenogram
open Reformulation.Kenogram.Fillability (card_rgs_four)

/-! ## Teil 1 — die Stufenzahlen als benannte Träger

Gerechnet aus der Definition über den Generator, nicht zitiert. -/

/-- Zwei Reihen der Länge zwei. -/
theorem card_rgs_two : Fintype.card (RGS 2) = 2 := by decide

/-- Fünf Reihen der Länge drei. -/
theorem card_rgs_three : Fintype.card (RGS 3) = 5 := by decide

/-- Zweiundfünfzig Reihen der Länge fünf. -/
theorem card_rgs_five : Fintype.card (RGS 5) = 52 := by decide

/-! ## Teil 2 — die Schranke und ihre Schärfe -/

/-- **Z1.** Keine Abbildung der geordneten Paare von `RGS 3` in `RGS 4` ist
injektiv: es gibt `5 · 5 = 25` Paare und `15` Ziele. Der Satz sagt die
Nichtexistenz einer injektiven Abbildung und nichts darüber hinaus. -/
theorem no_injective_pair_three (F : RGS 3 × RGS 3 → RGS 4) :
    ¬ Function.Injective F := by
  intro hF
  have h := Fintype.card_le_of_injective F hF
  rw [Fintype.card_prod, card_rgs_three, card_rgs_four] at h
  omega

/-- **Z2.** Dieselbe Aussage eine Stufe höher: `15 · 15 = 225` Paare, `52`
Ziele. Die Schranke bleibt, sie war kein Randfall der Stufe drei. -/
theorem no_injective_pair_four (F : RGS 4 × RGS 4 → RGS 5) :
    ¬ Function.Injective F := by
  intro hF
  have h := Fintype.card_le_of_injective F hF
  rw [Fintype.card_prod, card_rgs_four, card_rgs_five] at h
  omega

/-- **Z3.** Unterhalb der Schwelle gibt es eine injektive Abbildung: `2 · 2 = 4`
Paare, `5` Ziele. Die Existenz ist nichtkonstruktiv gewonnen; **welche**
Abbildung es ist, sagt der Satz nicht, und keine Aussage dieses Moduls braucht
es zu wissen. -/
theorem exists_injective_pair_two :
    ∃ F : RGS 2 × RGS 2 → RGS 3, Function.Injective F := by
  have h : Fintype.card (RGS 2 × RGS 2) ≤ Fintype.card (RGS 3) := by
    rw [Fintype.card_prod, card_rgs_two, card_rgs_three]
    decide
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le h
  exact ⟨e, e.injective⟩

/-! ## Teil 3 — Statement-Pins

Voller Wortlaut links, Satz rechts — jede Drift des *Statements* bricht den Bau. -/

-- STATEMENT-PIN
example (F : RGS 3 × RGS 3 → RGS 4) : ¬ Function.Injective F :=
  no_injective_pair_three F

-- STATEMENT-PIN
example (F : RGS 4 × RGS 4 → RGS 5) : ¬ Function.Injective F :=
  no_injective_pair_four F

-- STATEMENT-PIN
example : ∃ F : RGS 2 × RGS 2 → RGS 3, Function.Injective F :=
  exists_injective_pair_two

/-! ## Teil 4 — die Axiom-Wachen (Ist-gebunden)

Ist-Ausgabe des grünen Builds. `Classical.choice` ist über `instFintypeRGS`
geerbt, siehe Kopf. -/

/-- info: 'Reformulation.Kenogram.PairStageBound.card_rgs_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms card_rgs_two

/-- info: 'Reformulation.Kenogram.PairStageBound.card_rgs_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms card_rgs_three

/-- info: 'Reformulation.Kenogram.PairStageBound.card_rgs_five' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms card_rgs_five

/-- info: 'Reformulation.Kenogram.PairStageBound.no_injective_pair_three' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms no_injective_pair_three

/-- info: 'Reformulation.Kenogram.PairStageBound.no_injective_pair_four' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms no_injective_pair_four

/-- info: 'Reformulation.Kenogram.PairStageBound.exists_injective_pair_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms exists_injective_pair_two

end Reformulation.Kenogram.PairStageBound
