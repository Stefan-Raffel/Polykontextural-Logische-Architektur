import Reformulation.Pfalzgraf.Faserung
import Reformulation.Proemial.NonUniformCloneBound
import Reformulation.Proemial.TransjunctionCloneBound

/-!
# Reformulation.Proemial.ImplicationTransjunction — Günthers Implikationen als Transjunktionen

**Was das Modul ist (CLAUDE.md §4):** ERTRAG. Gebaut nach `KorpusRev2/Spec_B5_Anfang_Implikationen_Transjunktion.md`
(Fassung 3, Mathematiker; Ort und Ledger nach Custos IT2, IT3). Günthers acht Standardimplikationen aus
*Cognition and Volition* brechen im Teilsystem 2-3 an genau einer Stelle aus dem Teilsystem aus: an (3, 2),
wo p den negativen Wert trägt, nie an (2, 3). Das ist sein eigenes Beispiel für den dritten Grad der
Transjunktion von 1970. Dazu: Seine junktionalen Tafeln sind genau die kontexturtreuen.

## Die Zählung der Werte

```text
in Lean      0          1          2
Günther      1          2          3
```

Jeder Wert, den dieser Kopf nennt, steht in Günthers Zählung; die Sätze rechnen in der Lean-Zählung (wie
`Pfalzgraf/Faserung`). Teilsysteme in Günthers Reihenfolge 1-2, 2-3, 1-3; in jedem ist der kleinere Wert
der positive.

## K1 · Die Herkünfte, Zeile für Zeile

```text
GÜNTHER          die Implikationsregel und die acht Tafeln — C&V S. 29 f., Abb. 20–27 (am Bild:  Hermeneutes und
                 die Instanz, alle acht);  die K/D-Tafeln — C&V S. 25 f.;  die drei Grade, der Einbruch an der
                 schwachen Stelle, die Verwerfung in 2↔3 durch 1, die totale Transjunktion Tr — HKN 1970,
                 gg_category.pdf PDF-S. 20 (Edition A/1 — 4;  am Bild)
NACH PFALZGRAF   der Quotient, die Fasern, die Zulässigkeit (über Pfalzgraf/Faserung);  die Zerlegung einer Tafel in
                 drei Teiltafeln entlang der Diagonale und ihr Zusammenfügen (1991 S. 180 f.;  2004 S. 219–223, K8)
BESTAND          die Kontexturtreue `ContextureFaithful` und die Wahlvektoren `ofChoices` (NonUniformCloneBound);
                 die Transjunktion `T` (TransjunctionCloneBound)
UNSER            die Prädikate für die drei Grade;  die Benennung "kontextural";  die Gleichheit I4 mit
                 `ContextureFaithful` und ihre Zahl;  die Diagonal-Unterscheidung I5;  die Lean-Gestalt
ZUSAMMENSCHAU    "die Implikationen sind intrakontexturell-partielle Transjunktionen" — zweier Günther-Schriften,
                 Übergang gerechnet und am Bild bestätigt;  Günther nennt sie nirgends selbst so (Hermeneutes I4,
                 Nullbefund über sechs Schriften)
```

## K2 · Günther stellt zurück, er schliesst nicht aus (C&V S. 29, am Bild)

*„a three-valued systems has even more implications which can be derived from functors which are totally
or partially transjunctive. However, within the scope of this essay we must ignore the problem of
transjunctivity.“* „Partially“ gehört hier zu den Funktoren **anderer** Implikationen. Kein Widerspruch zur
Bestimmung von 1970 (Hermeneutes B1, B2).

## K3 · Die drei Grade (HKN, PDF-S. 20, am Bild)

* **total:** *„Sie tritt ausnahmslos an allen Stellen auf, an denen die Möglichkeit besteht, eine auf p und q
  verteilte Wertalternative zu verwerfen.“*
* **zweiter Grad:** *„Funktionen, in denen eine solche Verwerfung nur für eine oder für zwei Kontexturen
  auftritt.“* Die Benennung „kontextural“ ist die des Hauses (Definitionen §8).
* **dritter Grad:** *„dass die Verwerfung intrakontexturell-partiell ist; d.h., sie mag auftreten, wenn z.B. p
  den negativen Wert hat, aber nicht, wenn der negative Wert von q getragen wird.“*

„Partiell“ steht nur beim dritten. Dazu Günthers Ort: *„In dem System 2↔3 wird die Verwerfung sinngemäß durch
den Wert 1 … geleistet.“*

## K4 · Der Einbruch kommt aus der Regel, nicht aus den Funktoren

*„In order to produce implication we always write down value 1 if the variables p and q offer the same value.
And we do exactly the same when the value of the first variable (normally p) is higher than that of the second
variable.“* (C&V S. 29, am Bild.) Die acht K/D-Funktoren selbst brechen nirgends ein (`kd_einbruchfrei`).

## K5 · Was bewiesen ist, und was nicht

Bewiesen ist, dass Günthers Tafeln das Kriterium erfüllen, das er 1970 gibt (`impl_dritter_grad`): Teilsystem
2-3 partiell, 1-2 und 1-3 frei, der Einbruch dort, wo p den negativen Wert trägt. Dass die Implikationen
Transjunktionen **sind**, sagt Günther nicht; das ist die Zusammenschau (K1).

## K6 · Die Diagonale: warum Pfalzgraf drei Zellen zählt und Günther eine

In 2-3 liegt jede Implikation an drei Zellen ausserhalb des Teilsystems: (2,2), (3,2), (3,3). Pfalzgrafs Sicht
zählt alle drei als auf andere Fasern verteilte Ergebnisse. Günthers Einbruch steht nur an der schwachen
Stelle (3,2). Die zwei übrigen sind Diagonalzellen; dort steht 1, der Wahrwert einer **anderen** Faser, die
die Zelle liest (1-2 liest (2,2), 1-3 liest (3,3)). Beide zählen richtig (`diagonale`).
*Hinweis, 5. Oktober 2026:* Pfalzgraf 2004 zeigt an einem IMPLY seines Beispiels, dass es im zweiten
Teilsystem unverträglich ist (S. 221), und repariert es durch eine Transjunktion dort (S. 222); an der
Textschicht gelesen. Ob das Günthers Implikationstafel ist, ist nicht geprüft (Leseauftrag an Hermeneutes,
Register O2).

## K7 · Grenzen

* Die Rejektion ist bei Günther nach oben offen, *„by '3' or '4' or by any higher value“* (cyb 1962, S. 53;
  nach Hermeneutes, von der Instanz nicht am Bild). Hier gibt es nur drei Werte.
* **Editionsbefund** (nach Hermeneutes B3, nicht am Bild geprüft): E&W S. 36 übersetzt „three-valued“ mit
  „dreistellig“.

## K8 · I4, die Bauzeit, und TCB.T

* **I4 (`junktional_iff`):** Eine Tafel ist genau dann kontexturtreu (`ContextureFaithful`, die älteste
  Klonschicht des Bestands), wenn sie die Quotiententafel eines zulässigen Tripels ist (Faserung). Das Lemma
  `contextureFaithful_iff` bindet die Kontexturtreue an Günthers Einbruch: Diagonale fest und kein Einbruch.
  Zahl: 64 von 19 683.
* **Was Pfalzgrafs ist.** Zerlegung und Zusammenfügen beschreibt Pfalzgraf als Verfahren: 1991, S. 180 f. (die
  drei 2×2-Tafeln setzen sich zu einem 3×3-Schema zusammen; nach der Lesung des Mathematikers), und 2004 (RACSAM
  98(1)): *„Method of decomposition“* über die drei Teiltafeln entlang der Diagonale (S. 219), das Verfahren in
  drei Schritten (S. 222 f.) und der Remark (S. 222), die Teiltafeln seien *„merged … along the diagonal … such
  that the corresponding diagonal elements match“* (an der Textschicht gelesen, nicht am Bild). Von uns sind die Gleichheit
  mit `ContextureFaithful` aus dem Bestand, die Zahl und der Beweis ohne Aufzählung: Was Pfalzgraf als Bedingung
  und Verfahren beschreibt, steht hier bewiesen. *Nachgeführt am 5. Oktober 2026 (Regel 7; Register O1): Bis dahin
  stand I4 als UNSER ohne diese Fundstellen.*
* **Bewiesen zellweise, aus dem Grund** (nach `KorpusRev2/Spec_I4_Struktureller_Beweis.md`, Fassung 2). Der
  Grund in zwei Sätzen: Jede Diagonalzelle (v, v) wird von den zwei Teilsystemen gelesen, die v enthalten, und
  ihre Wertmengen teilen genau v; darum ist die Diagonale fest. Jede schwache Stelle (p, q) gehört genau einem
  Teilsystem {p, q}, und dort bleiben genau dessen zwei Werte (`cf_treu`). Aus einer kontexturtreuen Tafel
  werden die drei lokalen Operationen abgelesen (`ab0`, `ab1`, `ab2`: die Diagonale aus der Idempotenz, die zwei
  übrigen Einträge aus den zwei schwachen Stellen), und ihre Quotiententafel ist die Tafel (`treu_qop`);
  umgekehrt erfüllt jede Quotiententafel eines idempotenten Tripels den Grund (`qop_treu`). Die sechs Bits
  stehen in der Tafel und werden zurückgelesen (`ab_qop`): Die Zerlegung ist eindeutig.
* **Die Zahl folgt** (`zahl`): eine Bedingung je Zelle, gezählt als Produkt (`zaehl`), drei Diagonalzellen mit
  einem Wert, sechs schwache Stellen mit zwei, 1·2·2·2·1·2·2·2·1 = 2⁶ = 64. Die 19 683 Tafeln werden dabei
  nicht durchlaufen.
* **Ganz strukturell** *(seit 4. Oktober 2026, Regel 7; zuvor „strukturell bis auf Faserung Z1“)*. Die
  Zulässigkeit kommt aus Faserungs `zulaessig_eq_idempotent` (Z1′, dort aus demselben Grund eine Schicht tiefer:
  zwei Fasern lesen dieselbe Diagonalzelle und teilen genau einen Wert). Dafür sind hier `zul_of_idem` (inhaltlich
  Z1′), `idem_form` (eine Dublette, jetzt aus Faserung) und `bool_beq` (ohne Konsumenten) entfernt, nach
  `KorpusRev2/Spec_Z1_Struktureller_Beweis.md`, Fassung 2, P3 (a).
* **Bauzeit**, `lake env lean` auf dem Modul: vorher 77 s (real; die Aufzählung in `cf_alle`, `rechts_links`,
  `links_rechts`, `zahl` mit `decide +kernel`), nachher 2,6 s.
* **Was es vorbereitet:** Die Gestalt des Arguments hängt nicht an drei Werten. Bei m Werten liest jedes Paar
  ein Teilsystem und jede Diagonalzelle m − 1 Teilsysteme. Ob der Satz dort in derselben Gestalt gilt, ist für
  Rev11 offen; die Aufzählung ginge dort nicht mehr (4¹⁶ Tafeln schon bei vier Werten).
* *Ersetzt am 4. Oktober 2026 (Regel 7):* Bis dahin war I4 über die Aufzählung aller 3⁹ Tafeln bewiesen
  (`decide +kernel`, etwa 80 s Bauzeit), mit den Hilfssätzen `cf_alle`, `rechts_links`, `links_rechts`,
  `ofFun_mem_alle` und der Liste `links`. Sie sind entfernt. Aussage und Name von `junktional_iff`,
  `contextureFaithful_iff` und `zahl` sind unverändert; `alle` ist jetzt rekursiv definiert (`tafeln 9`),
  dieselben Tafeln.
* **`TCB.T`**, die Transjunktion der älteren Schicht, ist vom dritten Grad (`tcb_dritter_grad`). In der
  Wertzählung dieses Moduls bricht sie dort ein, wo p den **positiven** Wert trägt, spiegelbildlich zu Günthers
  Beispiel. Unter der Spiegelung `Fin.rev`, die `localOp` verwendet, liegt der Einbruch an Günthers Ort
  (`tcb_gespiegelt_guenther`). **TCB selbst nennt keine Wertzuordnung**; welche gemeint ist, entscheidet dieses
  Modul nicht.
* **Die acht K/D-Tafeln** stehen dreimal im Bestand und sind jetzt verbunden: `localOp` (`guenther_acht_localOp`),
  `ofChoices` (`kd_ofChoices`), die Quotiententafeln von Faserung (`kd_ist_guenther_acht`).
* **I2:** Einbruch und Grade sind entscheidbar, weil sie als `abbrev` über entscheidbare Aussagen definiert
  sind; jede Allaussage läuft über Listen, nicht über `Fin.fintype` (Fallstrick 10).

## Stufen (Ertrags-Skala, CLAUDE.md §4)

```text
impl_tafeln                         EICHUNG an C&V S. 29 f., Abb. 20–27
kd_ist_guenther_acht, kd_ofChoices  FOLGERUNG:  Brücken zwischen den Darstellungen der K/D-Tafeln
impl_einbruch_genau,                FOLGERUNG:  die Implikationen erfüllen Günthers Kriterium von 1970 (Zusammenschau)
  impl_dritter_grad
kd_einbruchfrei                     FOLGERUNG
tr_total                            EICHUNG an HKN PDF-S. 20
diagonale                           FOLGERUNG, UNSER
junktional_iff,                     FOLGERUNG:  die Brücke von der ältesten Klonschicht zu Pfalzgrafs Quotienten;  die
                                    Zerlegung NACH PFALZGRAF, die Gleichheit mit ContextureFaithful und die Zahl UNSER (K8)
  contextureFaithful_iff
tcb_dritter_grad,                   FOLGERUNG:  die ältere Transjunktion nach den Graden
  tcb_gespiegelt_guenther
cf_treu                             FOLGERUNG:  der Grund — Diagonale von zwei Teilsystemen gelesen, schwache Stelle von einem
zahl                                FOLGERUNG:  64 = 2⁶, als Produkt über die Zellen
ab_qop                              FOLGERUNG:  die Zerlegung ist eindeutig
treu_iff_bool, treu_qop, qop_treu, fin3_all, laenge_tafeln, laenge_mem, filter_fin3,
  zaehl, treu_stellen, rechts_passt, mem_ops, mem_fin3, ofList_ofFun
                                    Hilfssätze
```

0 Sorries. Gemessene Profile verbatim in den Wachen am Dateiende.
-/

namespace Reformulation.Proemial.ImplicationTransjunction

open Reformulation.Pfalzgraf

/-! ## Das Modell -/

/-- eine dreiwertige Tafel;  Lean 0, 1, 2 = Günthers 1, 2, 3 -/
abbrev Tafel := Fin 3 → Fin 3 → Fin 3

/-- die drei Werte als Liste (für entscheidbare Allaussagen ohne `Fin.fintype`, Fallstrick 10) -/
def fin3 : List (Fin 3) := [0, 1, 2]

/-- **I2.** Einbruch an der schwachen Stelle (p, q):  p ≠ q und der Wert liegt nicht in {p, q} -/
abbrev einbruch (f : Tafel) (p q : Fin 3) : Prop := p ≠ q ∧ f p q ≠ p ∧ f p q ≠ q

/-- die Teilsysteme in Günthers Reihenfolge 1-2, 2-3, 1-3 -/
def teil : Fin 3 → Fin 3 × Fin 3
  | ⟨0, _⟩ => (0, 1) | ⟨1, _⟩ => (1, 2) | ⟨2, _⟩ => (0, 2)

/-- die Zahl der Einbrüche an den zwei schwachen Stellen des Teilsystems s -/
def anzahl (f : Tafel) (s : Fin 3) : ℕ :=
  (if einbruch f (teil s).1 (teil s).2 then 1 else 0) + (if einbruch f (teil s).2 (teil s).1 then 1 else 0)
/-- das Teilsystem bricht an beiden schwachen Stellen ein -/
abbrev voll (f : Tafel) (s : Fin 3) : Prop := anzahl f s = 2
/-- an genau einer -/
abbrev partiell (f : Tafel) (s : Fin 3) : Prop := anzahl f s = 1
/-- an keiner -/
abbrev frei (f : Tafel) (s : Fin 3) : Prop := anzahl f s = 0
/-- erster Grad (HKN):  total -/
abbrev total (f : Tafel) : Prop := voll f 0 ∧ voll f 1 ∧ voll f 2
/-- zweiter Grad (HKN;  die Benennung UNSER):  einige Teilsysteme voll, keines partiell, nicht alle -/
abbrev kontextural (f : Tafel) : Prop :=
  (¬ partiell f 0 ∧ ¬ partiell f 1 ∧ ¬ partiell f 2) ∧ (voll f 0 ∨ voll f 1 ∨ voll f 2) ∧ ¬ total f
/-- dritter Grad (HKN):  intrakontexturell-partiell -/
abbrev intrakontexturellPartiell (f : Tafel) : Prop := partiell f 0 ∨ partiell f 1 ∨ partiell f 2

/-- nirgends ein Einbruch -/
def einbruchfrei (f : Tafel) : Bool := fin3.all fun p => fin3.all fun q => !decide (einbruch f p q)
/-- die Diagonale fest -/
def diagfest (f : Tafel) : Bool := fin3.all fun v => decide (f v v = v)

/-- Günthers K/D-Tafeln (C&V S. 25 f.):  l = (1-2, 2-3, 1-3), true = D;  K wählt den höheren Wert (Lean:  max) -/
def kd (l0 l1 l2 : Bool) : Tafel := fun p q =>
  if p = q then p else
    let l := if p.val + q.val = 1 then l0 else if p.val + q.val = 3 then l1 else l2
    if l then (if p.val ≤ q.val then p else q) else (if p.val ≤ q.val then q else p)
/-- **Günthers Implikationsregel** (C&V S. 29):  1, wo p ≥ q;  sonst der Wert des K- bzw. D-Funktors -/
def impl (l0 l1 l2 : Bool) : Tafel := fun p q => if q.val ≤ p.val then 0 else kd l0 l1 l2 p q

/-- Günthers totale Transjunktion Tr (HKN PDF-S. 20, die Tafel am Bild) -/
def tr : Tafel
  | ⟨0, _⟩, ⟨0, _⟩ => 0 | ⟨0, _⟩, ⟨1, _⟩ => 2 | ⟨0, _⟩, ⟨2, _⟩ => 1
  | ⟨1, _⟩, ⟨0, _⟩ => 2 | ⟨1, _⟩, ⟨1, _⟩ => 1 | ⟨1, _⟩, ⟨2, _⟩ => 0
  | ⟨2, _⟩, ⟨0, _⟩ => 1 | ⟨2, _⟩, ⟨1, _⟩ => 0 | ⟨2, _⟩, ⟨2, _⟩ => 2

/-- eine Tafel als neun Werte, zeilenweise -/
def ofFun (f : Tafel) : List (Fin 3) := [f 0 0, f 0 1, f 0 2, f 1 0, f 1 1, f 1 2, f 2 0, f 2 1, f 2 2]
/-- die Tafel zu neun Werten -/
def ofList (t : List (Fin 3)) : Tafel := fun p q => t.getD (3 * p.val + q.val) 0

def bools : List Bool := [false, true]
/-- die acht Wahlen von K oder D -/
def wahlen : List (Bool × Bool × Bool) :=
  bools.flatMap fun a => bools.flatMap fun b => bools.map fun c => (a, b, c)

/-- Abb. 20–27 (C&V S. 30 f., am Bild), Lean-Zählung -/
def abb : List ((Bool × Bool × Bool) × List (Fin 3)) :=
  [((false, false, false), [0,1,2, 0,0,2, 0,0,0]),   -- Abb. 20  KKK
   ((false, true,  false), [0,1,2, 0,0,1, 0,0,0]),   -- Abb. 21  KDK
   ((true,  false, false), [0,0,2, 0,0,2, 0,0,0]),   -- Abb. 22  DKK
   ((false, false, true ), [0,1,0, 0,0,2, 0,0,0]),   -- Abb. 23  KKD
   ((true,  true,  false), [0,0,2, 0,0,1, 0,0,0]),   -- Abb. 24  DDK
   ((false, true,  true ), [0,1,0, 0,0,1, 0,0,0]),   -- Abb. 25  KDD
   ((true,  false, true ), [0,0,0, 0,0,2, 0,0,0]),   -- Abb. 26  DKD
   ((true,  true,  true ), [0,0,0, 0,0,1, 0,0,0])]   -- Abb. 27  DDD

/-! ## (I1) Die Tafeln -/

/-- **I1a.** Günthers Regel erzeugt seine acht Implikationstafeln Abb. 20–27, Zelle für Zelle -/
theorem impl_tafeln : abb.all (fun e => decide (ofFun (impl e.1.1 e.1.2.1 e.1.2.2) = e.2)) = true := by decide

/-- **I1b.** Günthers K/D-Tafeln sind die Quotiententafeln aus Faserung (`guenther_acht`) -/
theorem kd_ist_guenther_acht : wahlen.all (fun l => decide (ofFun (kd l.1 l.2.1 l.2.2) =
    ofFun (qop (if l.1 then opD else opK) (if l.2.1 then opD else opK) (if l.2.2 then opD else opK)))) = true := by
  decide

/-- Brücke zur dritten Darstellung im Bestand:  `NonUniformCloneBound.ofChoices` (dort ∧ = min) unter `Fin.rev`;
    die zwei ersten Buchstaben tauschen, wie bei `guenther_acht_localOp` -/
theorem kd_ofChoices : wahlen.all (fun l => fin3.all fun p => fin3.all fun q =>
    decide (kd l.1 l.2.1 l.2.2 p q =
      Fin.rev (Reformulation.Proemial.NonUniformCloneBound.ofChoices l.2.1 l.1 l.2.2 (Fin.rev p) (Fin.rev q)))) = true := by
  decide

/-! ## (I3) Die Grade -/

/-- **I3a.** Jede der acht Implikationen bricht genau an Günthers (3, 2) ein (Lean (2, 1)), nirgends sonst -/
theorem impl_einbruch_genau : wahlen.all (fun l =>
    decide ((fin3.flatMap fun p => (fin3.filter fun q => decide (einbruch (impl l.1 l.2.1 l.2.2) p q)).map fun q => (p, q))
      = [((2 : Fin 3), (1 : Fin 3))])) = true := by decide

/-- **I3b.** Jede der acht ist vom dritten Grad:  2-3 partiell, 1-2 und 1-3 frei;  der Einbruch, wo p den negativen Wert von 2-3
    trägt (Günthers 3 ist dort F) -/
theorem impl_dritter_grad : wahlen.all (fun l => let f := impl l.1 l.2.1 l.2.2
    decide (partiell f 1 ∧ frei f 0 ∧ frei f 2 ∧ intrakontexturellPartiell f ∧ ¬ kontextural f ∧ ¬ total f)) = true ∧
    lokal 1 2 = false := by decide

/-- **I3c.** Günthers acht K/D-Tafeln brechen nirgends ein, die Diagonale ist fest -/
theorem kd_einbruchfrei : wahlen.all (fun l => einbruchfrei (kd l.1 l.2.1 l.2.2) && diagfest (kd l.1 l.2.1 l.2.2)) = true := by
  decide

/-- **I3d.** Günthers Tr (HKN PDF-S. 20) bricht an allen sechs schwachen Stellen ein:  total -/
theorem tr_total : total tr ∧ diagfest tr = true := by decide

/-! ## (I5) Die Diagonale -/

/-- **I5.** In 2-3 (Lean {1, 2}) liegt jede Implikation an genau drei Zellen ausserhalb:  (2,2), (3,2), (3,3) bei Günther.  An (2,2) und
    (3,3) steht 1, der Wahrwert einer ANDEREN Faser, die die Zelle liest (1-2 bzw. 1-3);  (3,2) liest keine andere Faser -/
theorem diagonale : wahlen.all (fun l => let f := impl l.1 l.2.1 l.2.2
    decide (([((1 : Fin 3), (1 : Fin 3)), (1, 2), (2, 1), (2, 2)].filter fun c => decide (f c.1 c.2 ≠ 1 ∧ f c.1 c.2 ≠ 2))
      = [(1, 1), (2, 1), (2, 2)]) && decide (f 1 1 = 0 ∧ f 2 2 = 0)) = true ∧
    (global 0 true = 0 ∧ liest 0 1 = true) ∧ (global 2 true = 0 ∧ liest 2 2 = true) ∧
    (liest 0 2 = false ∧ liest 2 1 = false) := by decide

/-! ## TCB.T nach den Graden -/

/-- `TCB.T` (die Transjunktion der älteren Schicht) ist vom dritten Grad:  einziger Einbruch an Lean (0, 2), partiell in 1-3.
    In der Wertzählung dieses Moduls trägt p dort den POSITIVEN Wert der Faser 1-3 (Lean 0 = Günthers 1) -/
theorem tcb_dritter_grad : let f := Reformulation.Proemial.TransjunctionCloneBound.T
    decide ((fin3.flatMap fun p => (fin3.filter fun q => decide (einbruch f p q)).map fun q => (p, q))
      = [((0 : Fin 3), (2 : Fin 3))]) = true ∧ partiell f 2 ∧ frei f 0 ∧ frei f 1 ∧ intrakontexturellPartiell f ∧
    lokal 2 0 = true := by decide

/-- unter der Spiegelung `Fin.rev` (der Zuordnung von `localOp`) liegt der Einbruch an Lean (2, 0) = Günthers (3, 1):  p trägt den
    NEGATIVEN Wert von 1-3, wie in Günthers Beispiel -/
theorem tcb_gespiegelt_guenther :
    let f : Tafel := fun p q => Fin.rev (Reformulation.Proemial.TransjunctionCloneBound.T (Fin.rev p) (Fin.rev q))
    decide ((fin3.flatMap fun p => (fin3.filter fun q => decide (einbruch f p q)).map fun q => (p, q))
      = [((2 : Fin 3), (0 : Fin 3))]) = true ∧ partiell f 2 ∧ intrakontexturellPartiell f ∧ lokal 2 2 = false := by decide

/-! ## (I4) Junktional ⟺ kontexturtreu — zellweise, aus dem Grund -/

theorem mem_ops (o : Op) : o ∈ ops := by
  obtain ⟨a, b, c, d⟩ := o
  cases a <;> cases b <;> cases c <;> cases d <;> decide

theorem mem_fin3 (v : Fin 3) : v ∈ fin3 := by
  match v with
  | ⟨0, _⟩ => exact List.mem_cons_self
  | ⟨1, _⟩ => exact List.mem_cons_of_mem _ List.mem_cons_self
  | ⟨2, _⟩ => exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

theorem ofList_ofFun (f : Tafel) : ofList (ofFun f) = f := by
  funext p q
  match p, q with
  | ⟨0,_⟩, ⟨0,_⟩ | ⟨0,_⟩, ⟨1,_⟩ | ⟨0,_⟩, ⟨2,_⟩ | ⟨1,_⟩, ⟨0,_⟩ | ⟨1,_⟩, ⟨1,_⟩ | ⟨1,_⟩, ⟨2,_⟩
  | ⟨2,_⟩, ⟨0,_⟩ | ⟨2,_⟩, ⟨1,_⟩ | ⟨2,_⟩, ⟨2,_⟩ => rfl

/-- drei Fälle statt `fin_cases` (das Classical zieht) -/
theorem fin3_all {P : Fin 3 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) : ∀ v, P v
  | ⟨0, _⟩ => h0 | ⟨1, _⟩ => h1 | ⟨2, _⟩ => h2

/-- der Grund, zellweise:  die Diagonale fest, jede schwache Stelle in ihrem Teilsystem {p, q} -/
def treu (f : Tafel) : Prop := (∀ v, f v v = v) ∧ ∀ p q, p ≠ q → (f p q = p ∨ f p q = q)

/-- **Der Grund.** Kontexturtreu heisst:  die Diagonale fest — die zwei Teilsysteme, die (v, v) lesen, teilen genau den
    Wert v —, und jede schwache Stelle bleibt in dem einen Teilsystem, dem sie gehört -/
theorem cf_treu (f : Tafel) : Reformulation.Proemial.NonUniformCloneBound.ContextureFaithful f ↔ treu f := by
  constructor
  · rintro ⟨h01, h12, h02⟩
    refine ⟨fin3_all ?_ ?_ ?_, fin3_all (fin3_all ?_ ?_ ?_) (fin3_all ?_ ?_ ?_) (fin3_all ?_ ?_ ?_)⟩
    · have a := h01 0 0 (.inl rfl) (.inl rfl); have b := h02 0 0 (.inl rfl) (.inl rfl)
      revert a b; generalize f 0 0 = w; revert w; exact fin3_all (by decide) (by decide) (by decide)
    · have a := h01 1 1 (.inr rfl) (.inr rfl); have b := h12 1 1 (.inl rfl) (.inl rfl)
      revert a b; generalize f 1 1 = w; revert w; exact fin3_all (by decide) (by decide) (by decide)
    · have a := h12 2 2 (.inr rfl) (.inr rfl); have b := h02 2 2 (.inr rfl) (.inr rfl)
      revert a b; generalize f 2 2 = w; revert w; exact fin3_all (by decide) (by decide) (by decide)
    · intro h; exact absurd rfl h
    · intro _; exact h01 0 1 (.inl rfl) (.inr rfl)
    · intro _; exact h02 0 2 (.inl rfl) (.inr rfl)
    · intro _; exact (h01 1 0 (.inr rfl) (.inl rfl)).symm
    · intro h; exact absurd rfl h
    · intro _; exact h12 1 2 (.inl rfl) (.inr rfl)
    · intro _; exact (h02 2 0 (.inr rfl) (.inl rfl)).symm
    · intro _; exact (h12 2 1 (.inr rfl) (.inl rfl)).symm
    · intro h; exact absurd rfl h
  · rintro ⟨hd, ho⟩
    refine ⟨?_, ?_, ?_⟩ <;>
    · intro a b ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
        first
        | exact .inl (hd _) | exact .inr (hd _)
        | exact ho _ _ (by decide) | exact (ho _ _ (by decide)).symm

/-- die Bool-Seite (Diagonale fest, einbruchfrei) ist derselbe Grund -/
theorem treu_iff_bool (f : Tafel) : treu f ↔ (diagfest f && einbruchfrei f) = true := by
  have hz : ∀ p q w : Fin 3, ¬ (p ≠ q ∧ w ≠ p ∧ w ≠ q) ↔ (p ≠ q → w = p ∨ w = q) :=
    fin3_all (fin3_all (fin3_all (by decide) (by decide) (by decide)) (fin3_all (by decide) (by decide) (by decide))
      (fin3_all (by decide) (by decide) (by decide))) (fin3_all (fin3_all (by decide) (by decide) (by decide))
      (fin3_all (by decide) (by decide) (by decide)) (fin3_all (by decide) (by decide) (by decide)))
      (fin3_all (fin3_all (by decide) (by decide) (by decide)) (fin3_all (by decide) (by decide) (by decide))
      (fin3_all (by decide) (by decide) (by decide)))
  rw [Bool.and_eq_true]
  unfold treu diagfest einbruchfrei
  constructor
  · rintro ⟨hd, ho⟩
    refine ⟨List.all_eq_true.mpr fun v _ => decide_eq_true (hd v), List.all_eq_true.mpr fun p _ =>
      List.all_eq_true.mpr fun q _ => ?_⟩
    rw [Bool.not_eq_true', decide_eq_false_iff_not]
    exact (hz p q (f p q)).mpr (ho p q)
  · rintro ⟨hd, ho⟩
    refine ⟨fun v => of_decide_eq_true (List.all_eq_true.mp hd v (mem_fin3 v)), fun p q => ?_⟩
    have h := List.all_eq_true.mp (List.all_eq_true.mp ho p (mem_fin3 p)) q (mem_fin3 q)
    rw [Bool.not_eq_true', decide_eq_false_iff_not] at h
    exact (hz p q (f p q)).mp h

/-- das Lemma:  kontexturtreu ⟺ Diagonale fest und einbruchfrei — für jede Tafel -/
theorem contextureFaithful_iff (f : Tafel) :
    Reformulation.Proemial.NonUniformCloneBound.ContextureFaithful f ↔ (diagfest f && einbruchfrei f) = true :=
  (cf_treu f).trans (treu_iff_bool f)

/-- die lokalen Operationen ablesen:  die Diagonale aus der Idempotenz (T, …, F), die zwei übrigen Einträge aus den
    zwei schwachen Stellen des Teilsystems -/
def ab0 (f : Tafel) : Op := (true, lokal 0 (f 0 1), lokal 0 (f 1 0), false)
/-- Teilsystem 1 (Günthers 2-3) -/
def ab1 (f : Tafel) : Op := (true, lokal 1 (f 1 2), lokal 1 (f 2 1), false)
/-- Teilsystem 2 (Günthers 1-3) -/
def ab2 (f : Tafel) : Op := (true, lokal 2 (f 0 2), lokal 2 (f 2 0), false)

/-- (→) die abgelesenen Operationen geben die Tafel zurück, Zelle für Zelle -/
theorem treu_qop (f : Tafel) (h : treu f) : ∀ p q, f p q = qop (ab0 f) (ab1 f) (ab2 f) p q := by
  obtain ⟨hd, ho⟩ := h
  refine fin3_all (fin3_all ?_ ?_ ?_) (fin3_all ?_ ?_ ?_) (fin3_all ?_ ?_ ?_)
  · rw [hd 0]; rfl
  · have h := ho 0 1 (by decide); revert h; unfold ab0; generalize f 0 1 = w; revert w
    refine fin3_all ?_ ?_ ?_ <;> intro h <;> first | rfl | exact absurd h (by decide)
  · have h := ho 0 2 (by decide); revert h; unfold ab2; generalize f 0 2 = w; revert w
    refine fin3_all ?_ ?_ ?_ <;> intro h <;> first | rfl | exact absurd h (by decide)
  · have h := ho 1 0 (by decide); revert h; unfold ab0; generalize f 1 0 = w; revert w
    refine fin3_all ?_ ?_ ?_ <;> intro h <;> first | rfl | exact absurd h (by decide)
  · rw [hd 1]; rfl
  · have h := ho 1 2 (by decide); revert h; unfold ab1; generalize f 1 2 = w; revert w
    refine fin3_all ?_ ?_ ?_ <;> intro h <;> first | rfl | exact absurd h (by decide)
  · have h := ho 2 0 (by decide); revert h; unfold ab2; generalize f 2 0 = w; revert w
    refine fin3_all ?_ ?_ ?_ <;> intro h <;> first | rfl | exact absurd h (by decide)
  · have h := ho 2 1 (by decide); revert h; unfold ab1; generalize f 2 1 = w; revert w
    refine fin3_all ?_ ?_ ?_ <;> intro h <;> first | rfl | exact absurd h (by decide)
  · rw [hd 2]; rfl

/-- (←) die Quotiententafel jedes idempotenten Tripels erfüllt den Grund -/
theorem qop_treu (a0 b0 a1 b1 a2 b2 : Bool) :
    treu (qop (true, a0, b0, false) (true, a1, b1, false) (true, a2, b2, false)) := by
  refine ⟨fin3_all rfl rfl rfl, fin3_all (fin3_all ?_ ?_ ?_) (fin3_all ?_ ?_ ?_) (fin3_all ?_ ?_ ?_)⟩ <;> intro h <;>
    first
    | exact absurd rfl h
    | (cases a0 <;> first | exact .inl rfl | exact .inr rfl)
    | (cases b0 <;> first | exact .inl rfl | exact .inr rfl)
    | (cases a1 <;> first | exact .inl rfl | exact .inr rfl)
    | (cases b1 <;> first | exact .inl rfl | exact .inr rfl)
    | (cases a2 <;> first | exact .inl rfl | exact .inr rfl)
    | (cases b2 <;> first | exact .inl rfl | exact .inr rfl)

/-- die Zerlegung ist eindeutig:  die sechs Bits stehen in der Tafel und werden zurückgelesen -/
theorem ab_qop (a0 b0 a1 b1 a2 b2 : Bool) :
    let g := qop (true, a0, b0, false) (true, a1, b1, false) (true, a2, b2, false)
    ab0 g = (true, a0, b0, false) ∧ ab1 g = (true, a1, b1, false) ∧ ab2 g = (true, a2, b2, false) := by
  refine ⟨?_, ?_, ?_⟩
  · cases a0 <;> cases b0 <;> rfl
  · cases a1 <;> cases b1 <;> rfl
  · cases a2 <;> cases b2 <;> rfl

/-- **I4.** Eine Tafel ist genau dann kontexturtreu, wenn sie die Quotiententafel eines zulässigen Tripels ist (Faserung) -/
theorem junktional_iff (f : Tafel) :
    Reformulation.Proemial.NonUniformCloneBound.ContextureFaithful f ↔
      ∃ o0 o1 o2 : Op, zulaessig o0 o1 o2 = true ∧ ofFun f = ofFun (qop o0 o1 o2) := by
  rw [cf_treu]
  constructor
  · intro h
    refine ⟨ab0 f, ab1 f, ab2 f, by rw [zulaessig_eq_idempotent]; rfl, ?_⟩
    exact congrArg ofFun (funext fun p => funext fun q => treu_qop f h p q)
  · rintro ⟨o0, o1, o2, hz, he⟩
    rw [zulaessig_eq_idempotent, Bool.and_eq_true, Bool.and_eq_true] at hz
    obtain ⟨⟨h0, h1⟩, h2⟩ := hz
    obtain ⟨a0, b0, rfl⟩ := idem_form o0 h0
    obtain ⟨a1, b1, rfl⟩ := idem_form o1 h1
    obtain ⟨a2, b2, rfl⟩ := idem_form o2 h2
    have hf : f = qop (true, a0, b0, false) (true, a1, b1, false) (true, a2, b2, false) := by
      rw [← ofList_ofFun f, he, ofList_ofFun]
    rw [hf]; exact qop_treu a0 b0 a1 b1 a2 b2

/-! ## Die Zahl:  64 = 1·2·2·2·1·2·2·2·1 — eine Bedingung je Zelle, gezählt als Produkt -/

/-- die Tafeln als Listen der Länge n -/
def tafeln : ℕ → List (List (Fin 3))
  | 0 => [[]]
  | n + 1 => fin3.flatMap fun a => (tafeln n).map (a :: ·)
/-- alle 19 683 Tafeln, zeilenweise -/
def alle : List (List (Fin 3)) := tafeln 9
/-- die rechte Seite von I4 an einer Liste -/
def rechts (t : List (Fin 3)) : Bool := diagfest (ofList t) && einbruchfrei (ofList t)

/-- eine Bedingung je Stelle -/
def passt : List (Fin 3 → Bool) → List (Fin 3) → Bool
  | p :: ps, a :: t => p a && passt ps t
  | [], [] => true
  | _, _ => false

/-- die neun Zellen:  eine Diagonalzelle lässt einen Wert zu, eine schwache Stelle zwei -/
def dia (v : Fin 3) (w : Fin 3) : Bool := decide (w = v)
/-- die schwache Stelle (p, q):  der Wert in {p, q} -/
def zwei (p q : Fin 3) (w : Fin 3) : Bool := decide (w = p ∨ w = q)
/-- die Bedingungen in der Reihenfolge der Zellen -/
def stellen : List (Fin 3 → Bool) :=
  [dia 0, zwei 0 1, zwei 0 2, zwei 1 0, dia 1, zwei 1 2, zwei 2 0, zwei 2 1, dia 2]

theorem laenge_tafeln : ∀ n, (tafeln n).length = 3 ^ n
  | 0 => rfl
  | n + 1 => by
    simp only [tafeln, fin3, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append,
      List.length_map, laenge_tafeln n, Nat.pow_succ]
    omega

theorem laenge_mem : ∀ (n : ℕ) (t : List (Fin 3)), t ∈ tafeln n → t.length = n
  | 0, t, h => by simp only [tafeln, List.mem_singleton] at h; rw [h]; rfl
  | n + 1, t, h => by
    obtain ⟨a, -, ht⟩ := List.mem_flatMap.mp h
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
    exact congrArg (· + 1) (laenge_mem n s hs)

theorem filter_fin3 (p : Fin 3 → Bool) :
    (fin3.filter p).length = (if p 0 then 1 else 0) + (if p 1 then 1 else 0) + (if p 2 then 1 else 0) := by
  cases h0 : p 0 <;> cases h1 : p 1 <;> cases h2 : p 2 <;> simp only [fin3, List.filter_cons, h0, h1, h2] <;> rfl

/-- gezählt wird als Produkt:  je Stelle die Zahl der zugelassenen Werte -/
theorem zaehl : ∀ (n : ℕ) (ps : List (Fin 3 → Bool)), ps.length = n →
    ((tafeln n).filter (passt ps)).length = (ps.map fun p => (fin3.filter p).length).prod
  | 0, [], _ => rfl
  | n + 1, p :: ps, h => by
    have ih := zaehl n ps (Nat.succ.inj h)
    have hA : ∀ a, (((tafeln n).map (a :: ·)).filter (passt (p :: ps))).length =
        (if p a then 1 else 0) * ((tafeln n).filter (passt ps)).length := by
      intro a
      rw [List.filter_map, List.length_map]
      cases ha : p a
      · have : (passt (p :: ps) ∘ (a :: ·)) = fun _ => false := by
          funext t; show (p a && passt ps t) = false; rw [ha]; rfl
        rw [this, List.filter_false]; exact (Nat.zero_mul _).symm
      · have : (passt (p :: ps) ∘ (a :: ·)) = passt ps := by
          funext t; show (p a && passt ps t) = passt ps t; rw [ha]; rfl
        rw [this]; exact (Nat.one_mul _).symm
    simp only [tafeln, fin3, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.filter_append,
      List.length_append, hA, List.map_cons, List.prod_cons, ih]
    rw [show (List.filter p [0, 1, 2]).length = _ from filter_fin3 p, ← Nat.add_assoc, ← Nat.add_mul, ← Nat.add_mul]
  | 0, _ :: _, h => absurd h (Nat.succ_ne_zero _)
  | _ + 1, [], h => absurd h (Nat.succ_ne_zero _).symm

/-- der Grund an einer Liste ist die Bedingung je Zelle -/
theorem treu_stellen (a b c d e f g h i : Fin 3) :
    treu (ofList [a, b, c, d, e, f, g, h, i]) ↔ passt stellen [a, b, c, d, e, f, g, h, i] = true := by
  simp only [passt, stellen, dia, zwei, Bool.and_true, Bool.and_eq_true, decide_eq_true_iff]
  constructor
  · rintro ⟨hd, ho⟩
    exact ⟨hd 0, ho 0 1 (by decide), ho 0 2 (by decide), ho 1 0 (by decide), hd 1, ho 1 2 (by decide),
      ho 2 0 (by decide), ho 2 1 (by decide), hd 2⟩
  · rintro ⟨ha, hb, hc, hd, he, hf, hg, hh, hi⟩
    exact ⟨fin3_all ha he hi, fin3_all (fin3_all (fun h => absurd rfl h) (fun _ => hb) (fun _ => hc))
      (fin3_all (fun _ => hd) (fun h => absurd rfl h) (fun _ => hf))
      (fin3_all (fun _ => hg) (fun _ => hh) (fun h => absurd rfl h))⟩

theorem rechts_passt (t : List (Fin 3)) (ht : t.length = 9) : rechts t = passt stellen t := by
  rcases t with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, _ | ⟨g, _ | ⟨h, _ | ⟨i, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    simp only [List.length_cons, List.length_nil] at ht <;> try omega
  apply Bool.eq_iff_iff.mpr
  rw [← treu_stellen, treu_iff_bool]; rfl

/-- **64 von 19 683**:  drei Diagonalzellen mit einem Wert, sechs schwache Stellen mit zwei — 2⁶ -/
theorem zahl : alle.length = 19683 ∧ (alle.filter rechts).length = 64 := by
  refine ⟨laenge_tafeln 9, ?_⟩
  have hc : alle.filter rechts = alle.filter (passt stellen) :=
    List.filter_congr fun t ht => rechts_passt t (laenge_mem 9 t ht)
  rw [hc]; exact (zaehl 9 stellen rfl).trans (by decide)

end Reformulation.Proemial.ImplicationTransjunction

/-! ## Axiom-Stand — als Regressions-Wachen gesetzt (alle Sätze des Moduls) -/

/-- info: 'Reformulation.Proemial.ImplicationTransjunction.impl_tafeln' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.ImplicationTransjunction.impl_tafeln

/-- info: 'Reformulation.Proemial.ImplicationTransjunction.kd_ist_guenther_acht' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.ImplicationTransjunction.kd_ist_guenther_acht

/-- info: 'Reformulation.Proemial.ImplicationTransjunction.kd_ofChoices' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.ImplicationTransjunction.kd_ofChoices

/-- info: 'Reformulation.Proemial.ImplicationTransjunction.impl_einbruch_genau' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.ImplicationTransjunction.impl_einbruch_genau

/-- info: 'Reformulation.Proemial.ImplicationTransjunction.impl_dritter_grad' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.ImplicationTransjunction.impl_dritter_grad

/-- info: 'Reformulation.Proemial.ImplicationTransjunction.kd_einbruchfrei' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.ImplicationTransjunction.kd_einbruchfrei

/-- info: 'Reformulation.Proemial.ImplicationTransjunction.tr_total' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.ImplicationTransjunction.tr_total

/-- info: 'Reformulation.Proemial.ImplicationTransjunction.diagonale' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.ImplicationTransjunction.diagonale

/-- info: 'Reformulation.Proemial.ImplicationTransjunction.tcb_dritter_grad' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.ImplicationTransjunction.tcb_dritter_grad

/-- info: 'Reformulation.Proemial.ImplicationTransjunction.tcb_gespiegelt_guenther' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.ImplicationTransjunction.tcb_gespiegelt_guenther

/-- info: 'Reformulation.Proemial.ImplicationTransjunction.mem_ops' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.ImplicationTransjunction.mem_ops

/-- info: 'Reformulation.Proemial.ImplicationTransjunction.mem_fin3' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.ImplicationTransjunction.mem_fin3

/-- info: 'Reformulation.Proemial.ImplicationTransjunction.ofList_ofFun' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ImplicationTransjunction.ofList_ofFun

/-- info: 'Reformulation.Proemial.ImplicationTransjunction.fin3_all' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.ImplicationTransjunction.fin3_all

/-- info: 'Reformulation.Proemial.ImplicationTransjunction.cf_treu' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.ImplicationTransjunction.cf_treu

/-- info: 'Reformulation.Proemial.ImplicationTransjunction.treu_iff_bool' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ImplicationTransjunction.treu_iff_bool

/-- info: 'Reformulation.Proemial.ImplicationTransjunction.contextureFaithful_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ImplicationTransjunction.contextureFaithful_iff

/-- info: 'Reformulation.Proemial.ImplicationTransjunction.treu_qop' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.ImplicationTransjunction.treu_qop

/-- info: 'Reformulation.Proemial.ImplicationTransjunction.qop_treu' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.ImplicationTransjunction.qop_treu

/-- info: 'Reformulation.Proemial.ImplicationTransjunction.ab_qop' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.ImplicationTransjunction.ab_qop

/-- info: 'Reformulation.Proemial.ImplicationTransjunction.junktional_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ImplicationTransjunction.junktional_iff

/-- info: 'Reformulation.Proemial.ImplicationTransjunction.laenge_tafeln' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ImplicationTransjunction.laenge_tafeln

/-- info: 'Reformulation.Proemial.ImplicationTransjunction.laenge_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ImplicationTransjunction.laenge_mem

/-- info: 'Reformulation.Proemial.ImplicationTransjunction.filter_fin3' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.ImplicationTransjunction.filter_fin3

/-- info: 'Reformulation.Proemial.ImplicationTransjunction.zaehl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ImplicationTransjunction.zaehl

/-- info: 'Reformulation.Proemial.ImplicationTransjunction.treu_stellen' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.ImplicationTransjunction.treu_stellen

/-- info: 'Reformulation.Proemial.ImplicationTransjunction.rechts_passt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ImplicationTransjunction.rechts_passt

/-- info: 'Reformulation.Proemial.ImplicationTransjunction.zahl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ImplicationTransjunction.zahl
