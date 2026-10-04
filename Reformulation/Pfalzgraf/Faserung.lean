import Reformulation.Proemial.TournamentInseparability

/-!
# Reformulation.Pfalzgraf.Faserung — das freie System und sein Quotient, die Zulässigkeit, der Trennfall

**Was das Modul ist (CLAUDE.md §4):** ERTRAG. Gebaut nach `KorpusRev2/Spec_B_Teil_I_Faserung_Quotient.md`
(Fassung 2, Mathematiker; Ort nach Custos DK1, DK2). Nach Pfalzgraf 1991 ist Günthers dreiwertiges System
der Quotient ℒ⁽³⁾ eines freien Parallelsystems ℒ³ aus drei zweiwertigen Fasern. Das Modul baut beide
Semantiken und die Abbildung zwischen ihnen und beweist, wann ein Junktor im Quotienten wohldefiniert ist,
dass Günthers acht Tafeln darin liegen, und Kaehrs Trennfall.

## K1 · Die Herkünfte, Zeile für Zeile

```text
NACH PFALZGRAF   das freie Parallelsystem, die Restklassen, die Negatoren, die Zulässigkeit als Begriff:
                 J. Pfalzgraf, "Logical fiberings and polycontextural systems", LNAI 535, Springer 1991,
                 S. 172–182 (am Bild);  N₅ = N₁ ∘ N₂ ∘ N₁ "using the notational convention of PCL" (S. 177)
GÜNTHER          das Schema (Teilsysteme 1-2, 2-3, 1-3;  "value 1 to be positive and 2 and 3 being subsequent
                 negations"), die acht K/D-Tafeln Abb. 7–14, die Implikationsregel — Cognition and Volition,
                 S. 25 f., 29 (am Bild);  tml S. 10
NACH KAEHR       der Trennfall N5(p ∧∧∧ N3p ∧∧∧ N4p) — Kaehr 1981, S. 3 und 17 (am Bild:  Konjunktionen)
UNSER            die Designation {1, 2}, der Gültigkeitsbegriff, die Kennzeichnung der Zulässigkeit durch
                 Idempotenz (vom Mathematiker gefunden), die Kohärenz, die Lean-Gestalt, die Brücke zu localOp
```

## Die Zählung der Werte

```text
in Lean      0          1          2
Günther      1          2          3
```

**Jeder Wert, den dieser Kopf nennt, steht in Günthers Zählung**; die Sätze rechnen in der Lean-Zählung. Die
Fasern stehen in Günthers Reihenfolge: Faser 0 = 1-2, Faser 1 = 2-3, Faser 2 = 1-3 (Pfalzgrafs L₁, L₂, L₃).
In jeder Faser ist der kleinere Wert der positive. Die Restklassen (Pfalzgraf S. 172): 1 = [T₁] = [T₃],
2 = [F₁] = [T₂], 3 = [F₂] = [F₃].

## K2 · Die Designation gegen 1959

Im Quotienten gelten die Werte {1, 2} als designiert, das Bild der lokalen Wahrheitswerte unter der
Restklassenabbildung (T₁ ↦ 1, T₂ ↦ 2, T₃ ↦ 1). **Das ist UNSERE Wahl, und sie geht gegen Günthers Grundsatz.**
In *Idee und Grundriss* (1959, S. 105) nennt er es *„Dieses verzweifelte Anhängen an der Tradition des
klassischen Formalismus“*, wenn man die Werte in designierte und nicht-designierte teilt und stipuliert,
*„dass die designierten Werte Wahrheit anzeigen sollen“*. Günthers Tafeln in C&V stützen weder {1} noch {1, 2}
rein. `gegenbeispiel_designation` zeigt, was {1} kosten würde; es motiviert die Wahl, es beweist sie nicht.

Gültig im freien System heisst: wahr in allen drei Fasern, unter jeder freien Belegung. Auch das ist UNSER;
Günther gibt keinen Gültigkeitsbegriff für dreiwertige Formeln (Hermeneutes D3, Nullbefund über acht Schriften).
Die Anknüpfung, nicht der Grund: cyb 1962, *„valid on three different levels“*.

## K3 · Der Quotient trägt Günthers Junktionen, nicht seine Implikationen

Die acht K/D-Tafeln liegen im junktionalen Quotienten (`guenther_acht`, Befund am Bild). Die acht Implikationen
(C&V S. 29) liegen nicht darin. In den Fasern 1-2 und 1-3 sind sie klassisch, in 2-3 setzen sie an drei Stellen
den Wert 1, der dort nicht gelesen wird: nach Pfalzgraf Transjunktionen. Sie gehören darum nach B5.

Nach Günthers eigener Bestimmung von 1970 sind sie es auch. *Die historische Kategorie des Neuen*
(`gg_category.pdf` PDF-S. 20, Seitenzählung der Edition „A/1 — 4“, am Bild) nennt als dritten Grad die
Verwerfung, die *„intrakontexturell-partiell ist; d.h., sie mag auftreten, wenn z.B. p den negativen Wert hat,
aber nicht, wenn der negative Wert von q getragen wird“*, und dazu *„In dem System 2↔3 wird die Verwerfung
sinngemäß durch den Wert 1 … geleistet“*. In 2-3 trägt an (3, 2) p den negativen Wert, und dort steht 1;
an (2, 3) nicht. **OFFEN** bleibt, was C&V S. 29 mit *„partially transjunctive“* meint, wenn Günther dort seine
*„standard implications“* gegen solche Funktoren setzt. Eine Spannung in der Quelle, gebucht, nicht aufgelöst.
*Nachgeführt am 4. Oktober 2026:* gebaut in `Proemial/ImplicationTransjunction.lean` (`impl_einbruch_genau`,
`impl_dritter_grad`). Dort ist auch die Spannung gelesen: Günther stellt die Implikationen aus transjunktiven
Funktoren zurück, er schliesst sie nicht aus; „partially“ gehört zu jenen Funktoren (Hermeneutes B1, B2).

## K4 · Die Partialität

Ein Wert wird nicht in jeder Faser gelesen: Faser 1-2 liest die 3 nicht, 2-3 nicht die 1, 1-3 nicht die 2.
Kohärenz ist darum über die lesenden Fasern definiert (`kohaerent`), eine ZUORDNUNG zu Pfalzgrafs
Restklassenabbildung.

**Die Vermutung V, nicht gebaut.** *Für jede zulässige Formel folge aus der Gültigkeit im freien System die
im Quotienten.* Die Umkehrung ist falsch (`trennfall`). V ist weder bewiesen noch widerlegt. Die naheliegende
Invariante — *unter einer Hebung der Quotientenbelegung stimmt jede Faser, die den Quotientenwert liest, mit ihm
überein* — **trägt nicht**. Sie fällt bei Grösse 4, an einem Junktor über p und N₁p. Der Mechanismus: Die
zweite Faser, die das Ergebnis liest, liest ein Argument nicht, und ∧ bzw. ∨ übernehmen dessen beliebigen
Wert. Keine der acht festen Ergänzungen der ungelesenen Koordinate rettet sie. Die abgeschlossene Relation
auf Paaren (freier Vektor, Quotientenwert) umfasst alle 24 Paare und ist zu grob. Ein Beweis müsste über
BEIDE Hebungen der ungelesenen Koordinate zugleich argumentieren. Stand der Suche (Python, alle 64 Tripel,
3.10.2026): kein Gegenbeispiel mit einer Variable bis Grösse 10 und mit zwei bis Grösse 6
(`KorpusRev2/Vorproben_Spec_B_Teil_I_Impl.md` §5). *Damit niemand die Invariante ein zweites Mal versucht.*

## K5 · Kaehrs Trennfall ohne Kaehrs Gültigkeit

„Allgemeingültig nach Günthers Tafeln“ (Kaehr 1981, S. 3) setzt einen Gültigkeitsbegriff voraus, den Günther
nicht hat. Am Trennfall ist das gleichgültig: Der Quotientenwert ist konstant 1, gültig unter jeder
Designation, die 1 enthält.

## K6 · Nicht gebaut, und warum

Die Transjunktionen (B5, dort Günthers Implikationen als erster Eichfall), Kaehrs Tableau (B3; seine gedruckte
Beweisbarkeit prüft Teilsystem 3 zweimal und 2 nie — gebaut seit dem 3. Oktober 2026 in
`Kaehr/Tableau.lean`, korrekt und vollständig für das freie System), der Generator (B4), die Vermutung V (K4).

## K7 · Die Zulässigkeit aus ihrem Grund

`zulaessig` vergleicht nur dort, wo zwei Fasern dasselbe Paar lesen. Für a ≠ b liest genau eine Faser das Paar, für
a = b lesen genau zwei, und ihre Wertmengen teilen genau den Wert a ({1,2} ∩ {1,3} = {1}, {1,2} ∩ {2,3} = {2},
{2,3} ∩ {1,3} = {3}). Darum zwingt die Zulässigkeit die Diagonaleinträge, aus T, T wird T und aus F, F wird F,
und sonst nichts: `zulaessig_eq_idempotent` (Z1′). Z1 (`zulaessig_iff_idempotent`) folgt daraus mit
unveränderter Aussage, Z2 (`zulaessig_zahl`) als Produkt: idempotent legt zwei der vier Einträge fest, also 4,
drei Operationen unabhängig, 4 · 4 · 4 = 64. Nach `KorpusRev2/Spec_Z1_Struktureller_Beweis.md`, Fassung 2.

* *Ersetzt am 4. Oktober 2026 (Regel 7):* Z1 und Z2 waren durch `decide` über die 4096 Tripel bewiesen. Bauzeit von
  Faserung (`lake env lean`, real): vorher 19,5 s, nachher 3,9 s.
* Drei Profilfallen umgangen, gemessen: `beq_self_eq_true` auf `Fin` zieht `Classical.choice` (Ersatz `beq_rfl`);
  `List.all_eq_true` zieht `Quot.sound` (Ersatz `all_mp`, `all_mpr`); `simp` unter Bindern geht über `funext`
  und zieht `Quot.sound` (Ersatz `filter_kongr`). Mit ihnen hätten Z1 und Z2 ihre Wachen geändert.

## K8 · Die Prüfung im Quotienten, und eine Konvention

*Nachgeführt am 4. Oktober 2026 (Regel 7), nach `KorpusRev2/Spec_Beispiele_und_Quotientenpruefung.md`, Fassung 3.*
`entscheideQuot` prüft jede Belegung der vorkommenden Variablen mit Günthers drei Werten; `entscheideQuot_iff`
sagt, dass das genau `gueltigQuot` ist (UNSER, über die Semantik NACH PFALZGRAF und die Designation {1, 2}). Die
Aufzählung läuft über eine eigene Liste, nicht über `Fintype` (Fallstrick 10, Choice).

**Eine Konvention des Bestands.** `auswQuot` ist total: Ein Junktor wird über `qop` gelesen, und `qop` nimmt die
erste Faser, die beide Argumente liest. Für ein unzulässiges Tripel liefert das einen Wert, ohne Meldung; gemessen
an `p ⊃⊃⊃ p`: unzulässig, und `entscheideQuot` sagt `true`. Für unzulässige Formeln ist der Wert im Quotienten
darum eine **Konvention des Bestands**, keine Aussage über Pfalzgrafs Quotienten. Ob eine Formel zulässig ist,
sagt `zulaessigFm` (`zulaessigFm_iff`). Die Sätze dieses Moduls über den Quotienten sprechen nur über zulässige
Formeln: `guenther_acht` über die Tafeln zulässiger Tripel, `trennfall` und `gegenbeispiel_designation` über
`trenn` und `gegen`, beide zulässig (`trenn_gegen_zulaessig`). Die Beispiele für den Leser stehen in
`Beispiele/KaehrPfalzgraf.lean`.

## Stufen (Ertrags-Skala, CLAUDE.md §4)

```text
zulaessig_iff_idempotent     FOLGERUNG — Grund:  jedes Diagonalpaar (v, v) lesen zwei Fasern, deren Wertmengen genau
                             einen Wert gemeinsam haben;  das zwingt die Diagonale, die übrigen Einträge liest nur eine
zulaessig_eq_idempotent      FOLGERUNG:  Z1′, der Grund in Allform (K7)
zulaessig_zahl               ZUSAMMENSTELLUNG (Zählung):  16 Operationen, 4 idempotent (∧, ∨, zwei Projektionen), 64 Tripel,
                             als Produkt 4 · 4 · 4
guenther_acht                EICHUNG an C&V S. 25 f., Abb. 7–14, Zelle für Zelle
guenther_acht_localOp        FOLGERUNG:  dieselben acht Tafeln wie localOp (TournamentInseparability) unter Fin.rev;  die
                             bisher ausserhalb des Korpus gerechnete Zuordnung dort wird ein Satz
unzulaessig_faelle           EICHUNG an Pfalzgraf S. 173, 180 (∧∨∧ zulässig, ∧∨→ nicht);  ⊃⊃⊃ nicht
negatoren_induziert          FOLGERUNG:  Pfalzgrafs freie Negatoren tragen Günthers dreiwertige
trennfall                    EICHUNG an Kaehr 1981, S. 3, 17
trennfall_inkohaerent        FOLGERUNG an EINER Formel:  falsifiziert ⟺ inkohärent (Kaehrs zwei offene Äste)
gegenbeispiel_designation    FOLGERUNG:  frei gültig, im Quotienten unter {1, 2} gültig, unter {1} nicht
entscheideQuot_iff           FOLGERUNG, UNSER:  die Gültigkeit im Quotienten, ausführbar (K8)
zulaessigFm_iff              FOLGERUNG:  die Prüfung der Zulässigkeit einer Formel sagt, was sie sagt
trenn_gegen_zulaessig        FOLGERUNG:  die zwei Formeln von T1 und G sind zulässig
all3, mem3, all_mp, all_mpr, beq_rfl, bool_rfl, diag0, diag1, diag2, idem_form, filter_nichts, filter_kongr,
  laenge_flatMap, laenge_filter_und, auswQuot_lokal, belegungen_vollstaendig
                             Hilfssätze
```

0 Sorries. Gemessene Profile verbatim in den Wachen am Dateiende.
-/

namespace Reformulation.Pfalzgraf

open Reformulation.Proemial.TournamentInseparability

/-! ## Das Modell -/

/-- eine Faser:  0 = Günthers 1-2, 1 = 2-3, 2 = 1-3 -/
abbrev Faser := Fin 3
/-- ein globaler Wert:  0, 1, 2 = Günthers 1, 2, 3 -/
abbrev Wert := Fin 3

/-- eine zweistellige Boolesche Operation als ihre Tafel (TT, TF, FT, FF) -/
abbrev Op := Bool × Bool × Bool × Bool
/-- die Anwendung einer Operation -/
def ap (o : Op) : Bool → Bool → Bool
  | true, true => o.1 | true, false => o.2.1 | false, true => o.2.2.1 | false, false => o.2.2.2
/-- idempotent:  aus T, T wird T und aus F, F wird F -/
def idempotent (o : Op) : Bool := o.1 && !o.2.2.2
/-- Konjunktion -/
def opK : Op := (true, false, false, false)
/-- Disjunktion -/
def opD : Op := (true, true, true, false)
/-- Implikation -/
def opI : Op := (true, false, true, true)
/-- die sechzehn Operationen -/
def ops : List Op :=
  [true, false].flatMap fun a => [true, false].flatMap fun b => [true, false].flatMap fun c =>
    [true, false].map fun d => (a, b, c, d)

/-- die Restklassen (Pfalzgraf S. 172):  der globale Wert eines lokalen Werts der Faser -/
def global : Faser → Bool → Wert
  | ⟨0, _⟩, true => 0 | ⟨0, _⟩, false => 1
  | ⟨1, _⟩, true => 1 | ⟨1, _⟩, false => 2
  | ⟨2, _⟩, true => 0 | ⟨2, _⟩, false => 2
/-- die Faser liest den Wert (die Kopplung ist partiell) -/
def liest : Faser → Wert → Bool
  | ⟨0, _⟩, v => v.val != 2
  | ⟨1, _⟩, v => v.val != 0
  | ⟨2, _⟩, v => v.val != 1
/-- die lokale Lesung eines Werts:  der positive Wert der Faser -/
def lokal (i : Faser) (v : Wert) : Bool := global i true == v

/-- die Operation der Faser i aus einem Tripel -/
def oAt (o0 o1 o2 : Op) : Faser → Op
  | ⟨0, _⟩ => o0 | ⟨1, _⟩ => o1 | ⟨2, _⟩ => o2
/-- die Lesung der Faser i für das Paar (a, b) -/
def faserWert (o0 o1 o2 : Op) (i : Faser) (a b : Wert) : Wert :=
  global i (ap (oAt o0 o1 o2 i) (lokal i a) (lokal i b))
/-- zulässig:  jede zwei Fasern, die beide Argumente lesen, liefern denselben globalen Wert -/
def zulaessig (o0 o1 o2 : Op) : Bool :=
  [0, 1, 2].all fun (a : Wert) => [0, 1, 2].all fun (b : Wert) =>
    [0, 1, 2].all fun (i : Faser) => [0, 1, 2].all fun (j : Faser) =>
      !(liest i a && liest i b && liest j a && liest j b) || faserWert o0 o1 o2 i a b == faserWert o0 o1 o2 j a b
/-- die Quotientenoperation:  die erste Faser, die beide Argumente liest -/
def qop (o0 o1 o2 : Op) (a b : Wert) : Wert :=
  if liest 0 a && liest 0 b then faserWert o0 o1 o2 0 a b
  else if liest 1 a && liest 1 b then faserWert o0 o1 o2 1 a b
  else faserWert o0 o1 o2 2 a b
/-- die Quotiententafel, Zeilen p, Spalten q -/
def tafel (o0 o1 o2 : Op) : List (List Wert) :=
  [0, 1, 2].map fun a => [0, 1, 2].map fun b => qop o0 o1 o2 a b

/-- die Formeln:  Variablen, die zwei Negatoren, Junktoren mit einer Operation je Faser -/
inductive Fm
  | var (n : ℕ)
  | neg₁ (a : Fm)
  | neg₂ (a : Fm)
  | junk (o0 o1 o2 : Op) (a b : Fm)

/-- freie Belegung:  je Variable ein Wahrheitswert je Faser -/
abbrev FreieBelegung := ℕ → Faser → Bool
/-- Belegung des Quotienten -/
abbrev Belegung := ℕ → Wert

/-- N₁ frei (Pfalzgraf S. 176):  verneint in Faser 1-2, tauscht 2-3 und 1-3 -/
def fneg₁ (x : Faser → Bool) : Faser → Bool
  | ⟨0, _⟩ => !x 0 | ⟨1, _⟩ => x 2 | ⟨2, _⟩ => x 1
/-- N₂ frei (Pfalzgraf S. 177):  verneint in Faser 2-3, tauscht 1-2 und 1-3 -/
def fneg₂ (x : Faser → Bool) : Faser → Bool
  | ⟨0, _⟩ => x 2 | ⟨1, _⟩ => !x 1 | ⟨2, _⟩ => x 0
/-- die Auswertung im freien System -/
def auswFrei (f : FreieBelegung) : Fm → Faser → Bool
  | .var n => f n
  | .neg₁ a => fneg₁ (auswFrei f a)
  | .neg₂ a => fneg₂ (auswFrei f a)
  | .junk o0 o1 o2 a b => fun i => ap (oAt o0 o1 o2 i) (auswFrei f a i) (auswFrei f b i)
/-- N₁ im Quotienten:  Günthers 1 ↔ 2, 3 fest -/
def qneg₁ (v : Wert) : Wert := if v = 0 then 1 else if v = 1 then 0 else 2
/-- N₂ im Quotienten:  Günthers 2 ↔ 3, 1 fest -/
def qneg₂ (v : Wert) : Wert := if v = 1 then 2 else if v = 2 then 1 else 0
/-- die Auswertung im Quotienten (für zulässige Formeln die gemeinsame Lesung) -/
def auswQuot (v : Belegung) : Fm → Wert
  | .var n => v n
  | .neg₁ a => qneg₁ (auswQuot v a)
  | .neg₂ a => qneg₂ (auswQuot v a)
  | .junk o0 o1 o2 a b => qop o0 o1 o2 (auswQuot v a) (auswQuot v b)

/-- designiert:  Günthers 1 und 2 (UNSER, K2) -/
def designiert (v : Wert) : Bool := v.val != 2
/-- gültig im Quotienten -/
def gueltigQuot (φ : Fm) : Prop := ∀ v : Belegung, designiert (auswQuot v φ) = true
/-- gültig im freien System:  wahr in allen drei Fasern, unter jeder freien Belegung (UNSER, K2) -/
def gueltigFrei (φ : Fm) : Prop := ∀ (f : FreieBelegung) (i : Faser), auswFrei f φ i = true

/-- ein freier Vektor ist kohärent mit dem Wert g:  jede Faser, die g liest, liest ihn so (K4) -/
def kohaerent (x : Faser → Bool) (g : Wert) : Bool :=
  [0, 1, 2].all fun (i : Faser) => !liest i g || global i (x i) == g
/-- ein freier Vektor aus drei Wahrheitswerten -/
def vec (b0 b1 b2 : Bool) : Faser → Bool
  | ⟨0, _⟩ => b0 | ⟨1, _⟩ => b1 | ⟨2, _⟩ => b2

/-! ## (Z) Die Zulässigkeit -/

/-- drei Fälle statt `fin_cases` (das Classical zieht) -/
theorem all3 {P : Wert → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) : ∀ v, P v
  | ⟨0, _⟩ => h0 | ⟨1, _⟩ => h1 | ⟨2, _⟩ => h2

theorem mem3 : ∀ v : Wert, v ∈ ([0, 1, 2] : List Wert)
  | ⟨0, _⟩ => List.mem_cons_self
  | ⟨1, _⟩ => List.mem_cons_of_mem _ List.mem_cons_self
  | ⟨2, _⟩ => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

/-- `List.all` ohne `List.all_eq_true` (das zieht `Quot.sound`) -/
theorem all_mp {α} {p : α → Bool} : ∀ {l : List α}, l.all p = true → ∀ x ∈ l, p x = true
  | [], _, x, hx => absurd hx List.not_mem_nil
  | a :: l, h, x, hx => by
    cases ha : p a
    · rw [List.all_cons, ha] at h; exact absurd h Bool.false_ne_true
    · rw [List.all_cons, ha] at h
      cases hx with
      | head => exact ha
      | tail _ hx => exact all_mp h x hx

theorem all_mpr {α} {p : α → Bool} : ∀ {l : List α}, (∀ x ∈ l, p x = true) → l.all p = true
  | [], _ => rfl
  | a :: l, h => by
    rw [List.all_cons, h a List.mem_cons_self, all_mpr fun x hx => h x (List.mem_cons_of_mem a hx)]; rfl

/-- Selbstvergleich auf `Wert`, ohne `beq_self_eq_true` (dessen `LawfulBEq`-Auflösung zieht auf `Fin` Choice) -/
theorem beq_rfl (x : Wert) : (x == x) = true := decide_eq_true rfl

/-- Selbstvergleich auf `Bool` -/
theorem bool_rfl (x : Bool) : (x == x) = true := by cases x <;> rfl

/-- das Diagonalpaar (1, 1) in Günthers Zählung:  Fasern 1-2 und 1-3, gemeinsamer Wert 1 — beide liefern T -/
theorem diag0 : ∀ a b : Bool, (global 0 a == global 2 b) = true → a = true ∧ b = true := by decide
/-- (2, 2):  Fasern 1-2 (dort F) und 2-3 (dort T) -/
theorem diag1 : ∀ a b : Bool, (global 0 a == global 1 b) = true → a = false ∧ b = true := by decide
/-- (3, 3):  Fasern 2-3 und 1-3, beide dort F -/
theorem diag2 : ∀ a b : Bool, (global 1 a == global 2 b) = true → a = false ∧ b = false := by decide

/-- idempotent heisst:  die Gestalt (T, a, b, F) -/
theorem idem_form (o : Op) (h : idempotent o = true) : ∃ a b, o = (true, a, b, false) := by
  obtain ⟨x, a, b, y⟩ := o
  cases x <;> cases y
  · exact absurd h Bool.false_ne_true
  · exact absurd h Bool.false_ne_true
  · exact ⟨a, b, rfl⟩
  · exact absurd h Bool.false_ne_true

/-- **Z1′, der Grund.** Zulässig heisst idempotent in jeder Faser.  `zulaessig` vergleicht nur, wo zwei Fasern dasselbe
    Paar lesen, und das sind nur die Diagonalpaare;  dort teilen ihre Wertmengen genau einen Wert, und der zwingt die
    Diagonaleinträge (`diag0`–`diag2`).  Die übrigen Einträge liest nur eine Faser. -/
theorem zulaessig_eq_idempotent (o0 o1 o2 : Op) :
    zulaessig o0 o1 o2 = (idempotent o0 && idempotent o1 && idempotent o2) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    have inst := fun a b i j => all_mp (all_mp (all_mp (all_mp h a (mem3 a)) b (mem3 b)) i (mem3 i)) j (mem3 j)
    have e0 : (global 0 o0.1 == global 2 o2.1) = true := inst 0 0 0 2
    have e1 : (global 0 o0.2.2.2 == global 1 o1.1) = true := inst 1 1 0 1
    have e2 : (global 1 o1.2.2.2 == global 2 o2.2.2.2) = true := inst 2 2 1 2
    obtain ⟨t0, x0, y0, f0⟩ := o0; obtain ⟨t1, x1, y1, f1⟩ := o1; obtain ⟨t2, x2, y2, f2⟩ := o2
    obtain ⟨rfl, rfl⟩ := diag0 _ _ e0
    obtain ⟨rfl, rfl⟩ := diag1 _ _ e1
    obtain ⟨rfl, rfl⟩ := diag2 _ _ e2
    rfl
  · intro h
    rw [Bool.and_eq_true, Bool.and_eq_true] at h
    obtain ⟨⟨h0, h1⟩, h2⟩ := h
    obtain ⟨x0, y0, rfl⟩ := idem_form o0 h0
    obtain ⟨x1, y1, rfl⟩ := idem_form o1 h1
    obtain ⟨x2, y2, rfl⟩ := idem_form o2 h2
    have key : ∀ a b i j : Wert, (!(liest i a && liest i b && liest j a && liest j b) ||
        faserWert (true, x0, y0, false) (true, x1, y1, false) (true, x2, y2, false) i a b ==
        faserWert (true, x0, y0, false) (true, x1, y1, false) (true, x2, y2, false) j a b) = true := by
      refine all3 ?_ ?_ ?_ <;> refine all3 ?_ ?_ ?_ <;> refine all3 ?_ ?_ ?_ <;> refine all3 ?_ ?_ ?_ <;>
        first | rfl | exact beq_rfl _
    exact all_mpr fun a _ => all_mpr fun b _ => all_mpr fun i _ => all_mpr fun j _ => key a b i j

/-- **Z1.** Ein Tripel ist im Quotienten genau dann wohldefiniert, wenn jede seiner drei Operationen idempotent
    ist — über alle 16³ Tripel, aus Z1′. -/
theorem zulaessig_iff_idempotent :
    ops.all (fun o0 => ops.all fun o1 => ops.all fun o2 =>
      zulaessig o0 o1 o2 == (idempotent o0 && idempotent o1 && idempotent o2)) = true :=
  all_mpr fun o0 _ => all_mpr fun o1 _ => all_mpr fun o2 _ => by
    rw [zulaessig_eq_idempotent]; exact bool_rfl _

theorem filter_nichts (l : List Op) : l.filter (fun _ => false) = [] := by
  induction l with
  | nil => rfl
  | cons _ _ ih => exact ih

/-- Filter-Kongruenz ohne `funext` (das zieht `Quot.sound`) -/
theorem filter_kongr {p q : Op → Bool} : ∀ {l : List Op}, (∀ x ∈ l, p x = q x) → l.filter p = l.filter q
  | [], _ => rfl
  | a :: l, h => by
    rw [List.filter_cons, List.filter_cons, h a List.mem_cons_self,
      filter_kongr fun x hx => h x (List.mem_cons_of_mem a hx)]

/-- die Länge eines `flatMap`, wenn jedes Stück k oder 0 Elemente hat -/
theorem laenge_flatMap (l : List Op) (p : Op → Bool) (k : ℕ) (g : Op → List Op)
    (h : ∀ o, (g o).length = if p o then k else 0) : (l.flatMap g).length = (l.filter p).length * k := by
  induction l with
  | nil => exact (Nat.zero_mul k).symm
  | cons o l ih =>
    rw [List.flatMap_cons, List.length_append, ih, h o, List.filter_cons]
    cases p o
    · exact Nat.zero_add _
    · show k + (List.filter p l).length * k = ((List.filter p l).length + 1) * k
      rw [Nat.succ_mul, Nat.add_comm]

theorem laenge_filter_und (b : Bool) (l : List Op) (p : Op → Bool) :
    (l.filter fun o => b && p o).length = if b then (l.filter p).length else 0 := by
  cases b
  · exact congrArg List.length (filter_nichts l)
  · rfl

/-- **Z2.** 16 Operationen, davon 4 idempotent;  64 zulässige Tripel von 4096 — als Produkt 4 · 4 · 4, aus Z1′. -/
theorem zulaessig_zahl :
    ops.length = 16 ∧ (ops.filter idempotent).length = 4 ∧
    (ops.flatMap fun o0 => ops.flatMap fun o1 => ops.filter fun o2 => zulaessig o0 o1 o2).length = 64 := by
  have h4 : (ops.filter idempotent).length = 4 := by decide
  refine ⟨by decide, h4, ?_⟩
  have filt : ∀ o0 o1, ops.filter (fun o2 => zulaessig o0 o1 o2) =
      ops.filter (fun o2 => idempotent o0 && idempotent o1 && idempotent o2) := fun o0 o1 =>
    filter_kongr fun o2 _ => zulaessig_eq_idempotent o0 o1 o2
  have inner : ∀ o0, (ops.flatMap fun o1 => ops.filter fun o2 => zulaessig o0 o1 o2).length =
      if idempotent o0 then 16 else 0 := by
    intro o0
    cases h0 : idempotent o0
    · rw [laenge_flatMap ops (fun _ => false) 16 _ fun o1 => by
          rw [filt, h0]; exact laenge_filter_und (false && idempotent o1) ops idempotent,
        filter_nichts]; rfl
    · rw [laenge_flatMap ops idempotent 4 _ fun o1 => by
          rw [filt, h0, laenge_filter_und (true && idempotent o1) ops idempotent, h4]; rfl, h4]; rfl
  rw [laenge_flatMap ops idempotent 16 _ inner, h4]

/-- **Z3.** Günthers acht Konjunktionen und Disjunktionen (C&V S. 25 f., Abb. 7–14, am Bild) sind zulässig, und
    ihre Quotiententafeln sind seine Tafeln, Zelle für Zelle (Lean-Zählung:  Günthers Wert − 1). -/
theorem guenther_acht :
    tafel opK opK opK = [[0, 1, 2], [1, 1, 2], [2, 2, 2]] ∧      -- Abb. 7   KKK
    tafel opK opD opK = [[0, 1, 2], [1, 1, 1], [2, 1, 2]] ∧      -- Abb. 8   KDK
    tafel opD opK opK = [[0, 0, 2], [0, 1, 2], [2, 2, 2]] ∧      -- Abb. 9   DKK
    tafel opK opD opD = [[0, 1, 0], [1, 1, 1], [0, 1, 2]] ∧      -- Abb. 10  KDD
    tafel opD opK opD = [[0, 0, 0], [0, 1, 2], [0, 2, 2]] ∧      -- Abb. 11  DKD
    tafel opD opD opD = [[0, 0, 0], [0, 1, 1], [0, 1, 2]] ∧      -- Abb. 12  DDD
    tafel opK opK opD = [[0, 1, 0], [1, 1, 2], [0, 2, 2]] ∧      -- Abb. 13  KKD
    tafel opD opD opK = [[0, 0, 2], [0, 1, 1], [2, 1, 2]] ∧      -- Abb. 14  DDK
    zulaessig opK opK opK = true ∧ zulaessig opK opD opK = true ∧ zulaessig opD opK opK = true ∧
    zulaessig opK opD opD = true ∧ zulaessig opD opK opD = true ∧ zulaessig opD opD opD = true ∧
    zulaessig opK opK opD = true ∧ zulaessig opD opD opK = true := by decide

/-- **Z3′.** Dieselben acht Tafeln wie `localOp` (TournamentInseparability), dort in der anderen Wertzuordnung
    (K = Minimum):  unter der Spiegelung `Fin.rev` wird Günthers Tripel (X₀, X₁, X₂) über 1-2, 2-3, 1-3 zum
    Muster (X₁, X₀, X₂) über `{0,1}`, `{1,2}`, `{0,2}` — die zwei ersten Buchstaben tauschen, die Namen K und D
    bleiben. -/
theorem guenther_acht_localOp :
    [0, 1, 2].all (fun (a : Wert) => [0, 1, 2].all fun (b : Wert) =>
      qop opK opK opK a b == Fin.rev (KKK (Fin.rev a) (Fin.rev b)) &&
      qop opK opD opK a b == Fin.rev (DKK (Fin.rev a) (Fin.rev b)) &&
      qop opD opK opK a b == Fin.rev (KDK (Fin.rev a) (Fin.rev b)) &&
      qop opK opD opD a b == Fin.rev (DKD (Fin.rev a) (Fin.rev b)) &&
      qop opD opK opD a b == Fin.rev (KDD (Fin.rev a) (Fin.rev b)) &&
      qop opD opD opD a b == Fin.rev (DDD (Fin.rev a) (Fin.rev b)) &&
      qop opK opK opD a b == Fin.rev (KKD (Fin.rev a) (Fin.rev b)) &&
      qop opD opD opK a b == Fin.rev (DDK (Fin.rev a) (Fin.rev b))) = true := by decide

/-- **Z4.** Pfalzgraf S. 173, 180:  ∧∨∧ zulässig, ∧∨→ nicht;  dazu ⊃⊃⊃ nicht (aus F, F wird T). -/
theorem unzulaessig_faelle :
    zulaessig opK opD opK = true ∧ zulaessig opK opD opI = false ∧ zulaessig opI opI opI = false := by
  decide

/-! ## (N) Die Negatoren -/

/-- **N1.** Die freien Negatoren erhalten die Kohärenz:  ein Vektor, kohärent mit g, geht unter N₁ bzw. N₂ in
    einen Vektor über, kohärent mit Günthers N₁ g bzw. N₂ g. -/
theorem negatoren_induziert :
    [true, false].all (fun b0 => [true, false].all fun b1 => [true, false].all fun b2 =>
      [0, 1, 2].all fun (g : Wert) =>
        (!kohaerent (vec b0 b1 b2) g || kohaerent (fneg₁ (vec b0 b1 b2)) (qneg₁ g)) &&
        (!kohaerent (vec b0 b1 b2) g || kohaerent (fneg₂ (vec b0 b1 b2)) (qneg₂ g))) = true := by decide

/-! ## (T, G) Der Trennfall und das Gegenbeispiel -/

/-- die Variable p -/
def p : Fm := .var 0
/-- ∧∧∧ -/
def kon (a b : Fm) : Fm := .junk opK opK opK a b
/-- ∨∨∨ -/
def dis (a b : Fm) : Fm := .junk opD opD opD a b
/-- N₃ := N₂ ∘ N₁ -/
def N3 (a : Fm) : Fm := .neg₂ (.neg₁ a)
/-- N₄ := N₁ ∘ N₂ -/
def N4 (a : Fm) : Fm := .neg₁ (.neg₂ a)
/-- N₅ := N₁ ∘ N₂ ∘ N₁ (Pfalzgraf S. 177) -/
def N5 (a : Fm) : Fm := .neg₁ (.neg₂ (.neg₁ a))
/-- Kaehrs Trennfall N5(p ∧∧∧ N3p ∧∧∧ N4p) -/
def trenn : Fm := N5 (kon (kon p (N3 p)) (N4 p))
/-- das Gegenbeispiel G = p ∨∨∨ (N₁p ∨∨∨ N₂(p ∨∨∨ N₁p)) -/
def gegen : Fm := dis p (dis (.neg₁ p) (.neg₂ (dis p (.neg₁ p))))

/-- **T1.** Im Quotienten hat der Trennfall unter jeder Belegung Günthers Wert 1;  im freien System ist er nicht
    gültig. -/
theorem trennfall : (∀ v : Belegung, auswQuot v trenn = 0) ∧ ¬ gueltigFrei trenn := by
  refine ⟨fun v => ?_, fun h => ?_⟩
  · show qneg₁ (qneg₂ (qneg₁ (qop opK opK opK (qop opK opK opK (v 0) (qneg₂ (qneg₁ (v 0))))
      (qneg₁ (qneg₂ (v 0)))))) = 0
    generalize v 0 = g
    match g with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨2, _⟩ => rfl
  · exact absurd (h (fun _ => vec true true false) 0) (by decide)

/-- **T2.** An dieser Formel:  eine freie Belegung von p falsifiziert sie genau dann, wenn sie mit keinem Wert
    kohärent ist — Kaehrs zwei offene Äste (T, T, F) und (F, F, T). -/
theorem trennfall_inkohaerent :
    [true, false].all (fun b0 => [true, false].all fun b1 => [true, false].all fun b2 =>
      (!([0, 1, 2].all fun (i : Faser) => auswFrei (fun _ => vec b0 b1 b2) trenn i)) ==
      !([0, 1, 2].any fun (g : Wert) => kohaerent (vec b0 b1 b2) g)) = true := by decide

/-- **G.** Das Gegenbeispiel zur Designation {1}:  G ist im freien System gültig, im Quotienten unter {1, 2}
    gültig, und unter p = 3 hat es den Wert 2 — unter {1} wäre es nicht gültig. -/
theorem gegenbeispiel_designation :
    gueltigFrei gegen ∧ gueltigQuot gegen ∧ auswQuot (fun _ => 2) gegen = 1 := by
  refine ⟨fun f i => ?_, fun v => ?_, by decide⟩
  · show ap (oAt opD opD opD i) (f 0 i) (ap (oAt opD opD opD i) (fneg₁ (f 0) i)
      (fneg₂ (fun j => ap (oAt opD opD opD j) (f 0 j) (fneg₁ (f 0) j)) i)) = true
    generalize f 0 = x
    have hx : x = vec (x 0) (x 1) (x 2) := funext fun j => match j with
      | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl | ⟨2, _⟩ => rfl
    rw [hx]
    generalize x 0 = b0
    generalize x 1 = b1
    generalize x 2 = b2
    match i with
    | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ => cases b0 <;> cases b1 <;> cases b2 <;> rfl
  · show designiert (qop opD opD opD (v 0) (qop opD opD opD (qneg₁ (v 0))
      (qneg₂ (qop opD opD opD (v 0) (qneg₁ (v 0)))))) = true
    generalize v 0 = g
    match g with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨2, _⟩ => rfl


/-! ## (Q) Die Prüfung im Quotienten, ausführbar -/

/-- die Variablen einer Formel (mit Wiederholung) -/
def vars : Fm → List ℕ
  | .var n => [n]
  | .neg₁ a => vars a
  | .neg₂ a => vars a
  | .junk _ _ _ a b => vars a ++ vars b

/-- eine Belegung an einer Stelle umsetzen (über `Nat.decEq`, nicht über `Function.update`) -/
def setze (v : Belegung) (n : ℕ) (k : Wert) : Belegung := fun m => if m = n then k else v m

/-- alle Belegungen der Variablen einer Liste mit Günthers drei Werten, rekursiv — keine `Fintype`-Aufzählung -/
def belegungen : List ℕ → List Belegung
  | [] => [fun _ => 0]
  | n :: ns => (belegungen ns).flatMap fun v => ([0, 1, 2] : List Wert).map fun k => setze v n k

/-- Lokalität:  der Wert im Quotienten hängt nur von den Variablen der Formel ab -/
theorem auswQuot_lokal : ∀ (φ : Fm) (v w : Belegung), (∀ n ∈ vars φ, v n = w n) → auswQuot v φ = auswQuot w φ
  | .var n, v, w, h => h n List.mem_cons_self
  | .neg₁ a, v, w, h => congrArg qneg₁ (auswQuot_lokal a v w h)
  | .neg₂ a, v, w, h => congrArg qneg₂ (auswQuot_lokal a v w h)
  | .junk o0 o1 o2 a b, v, w, h => by
    show qop o0 o1 o2 (auswQuot v a) (auswQuot v b) = qop o0 o1 o2 (auswQuot w a) (auswQuot w b)
    rw [auswQuot_lokal a v w fun n hn => h n (List.mem_append_left _ hn),
      auswQuot_lokal b v w fun n hn => h n (List.mem_append_right _ hn)]

/-- die Aufzählung ist vollständig:  jede Belegung stimmt auf den Variablen mit einer aufgezählten überein -/
theorem belegungen_vollstaendig : ∀ (ns : List ℕ) (v : Belegung), ∃ w ∈ belegungen ns, ∀ n ∈ ns, w n = v n
  | [], _ => ⟨fun _ => 0, List.mem_cons_self, fun _ h => absurd h List.not_mem_nil⟩
  | n :: ns, v => by
    obtain ⟨w, hw, hag⟩ := belegungen_vollstaendig ns v
    refine ⟨setze w n (v n), List.mem_flatMap.mpr ⟨w, hw, List.mem_map.mpr ⟨v n, mem3 (v n), rfl⟩⟩, ?_⟩
    intro m hm
    unfold setze
    match Nat.decEq m n with
    | isTrue e => rw [if_pos e, e]
    | isFalse e =>
      rw [if_neg e]
      cases hm with
      | head => exact absurd rfl e
      | tail _ hm => exact hag m hm

/-- die Prüfung:  jede Belegung der vorkommenden Variablen, je drei Werte — 3^(Zahl der Variablen) Fälle -/
def entscheideQuot (φ : Fm) : Bool := (belegungen (vars φ)).all fun w => designiert (auswQuot w φ)

/-- **Q1.** Die Prüfung entscheidet die Gültigkeit im Quotienten, für jede Formel.  Für eine unzulässige Formel ist
    `gueltigQuot` eine Konvention des Bestands (K8). -/
theorem entscheideQuot_iff (φ : Fm) : entscheideQuot φ = true ↔ gueltigQuot φ := by
  constructor
  · intro h v
    obtain ⟨w, hw, hag⟩ := belegungen_vollstaendig (vars φ) v
    rw [auswQuot_lokal φ v w fun n hn => (hag n hn).symm]
    exact all_mp h w hw
  · intro h
    exact all_mpr fun w _ => h w

/-- die Junktoren einer Formel, je als Tripel -/
def junktoren : Fm → List (Op × Op × Op)
  | .var _ => []
  | .neg₁ a => junktoren a
  | .neg₂ a => junktoren a
  | .junk o0 o1 o2 a b => (o0, o1, o2) :: (junktoren a ++ junktoren b)

/-- zulässig als Formel:  jeder Junktor ein zulässiges Tripel -/
def zulaessigFm : Fm → Bool
  | .var _ => true
  | .neg₁ a => zulaessigFm a
  | .neg₂ a => zulaessigFm a
  | .junk o0 o1 o2 a b => zulaessig o0 o1 o2 && zulaessigFm a && zulaessigFm b

/-- **Q2.** `zulaessigFm` sagt, was ihr Name sagt:  jeder Junktor der Formel ist zulässig -/
theorem zulaessigFm_iff : ∀ φ : Fm, zulaessigFm φ = true ↔ ∀ t ∈ junktoren φ, zulaessig t.1 t.2.1 t.2.2 = true
  | .var _ => ⟨fun _ _ h => absurd h List.not_mem_nil, fun _ => rfl⟩
  | .neg₁ a => zulaessigFm_iff a
  | .neg₂ a => zulaessigFm_iff a
  | .junk o0 o1 o2 a b => by
    show (zulaessig o0 o1 o2 && zulaessigFm a && zulaessigFm b) = true ↔ _
    rw [Bool.and_eq_true, Bool.and_eq_true, zulaessigFm_iff a, zulaessigFm_iff b]
    constructor
    · rintro ⟨⟨h0, ha⟩, hb⟩ t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact h0
      · rcases List.mem_append.mp ht with ht | ht
        · exact ha t ht
        · exact hb t ht
    · intro h
      exact ⟨⟨h _ List.mem_cons_self, fun t ht => h t (List.mem_cons_of_mem _ (List.mem_append_left _ ht))⟩,
        fun t ht => h t (List.mem_cons_of_mem _ (List.mem_append_right _ ht))⟩

/-- **Q3.** Die zwei Formeln, über die `trennfall` und `gegenbeispiel_designation` im Quotienten sprechen, sind zulässig -/
theorem trenn_gegen_zulaessig : zulaessigFm trenn = true ∧ zulaessigFm gegen = true := by decide

end Reformulation.Pfalzgraf

/-! ## Axiom-Stand — als Regressions-Wachen gesetzt (alle Sätze des Moduls) -/

/-- info: 'Reformulation.Pfalzgraf.all3' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.all3

/-- info: 'Reformulation.Pfalzgraf.mem3' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.mem3

/-- info: 'Reformulation.Pfalzgraf.all_mp' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.all_mp

/-- info: 'Reformulation.Pfalzgraf.all_mpr' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.all_mpr

/-- info: 'Reformulation.Pfalzgraf.beq_rfl' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.beq_rfl

/-- info: 'Reformulation.Pfalzgraf.bool_rfl' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.bool_rfl

/-- info: 'Reformulation.Pfalzgraf.diag0' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.diag0

/-- info: 'Reformulation.Pfalzgraf.diag1' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.diag1

/-- info: 'Reformulation.Pfalzgraf.diag2' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.diag2

/-- info: 'Reformulation.Pfalzgraf.idem_form' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.idem_form

/-- info: 'Reformulation.Pfalzgraf.zulaessig_eq_idempotent' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.zulaessig_eq_idempotent

/-- info: 'Reformulation.Pfalzgraf.zulaessig_iff_idempotent' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.zulaessig_iff_idempotent

/-- info: 'Reformulation.Pfalzgraf.filter_nichts' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.filter_nichts

/-- info: 'Reformulation.Pfalzgraf.filter_kongr' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.filter_kongr

/-- info: 'Reformulation.Pfalzgraf.laenge_flatMap' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.laenge_flatMap

/-- info: 'Reformulation.Pfalzgraf.laenge_filter_und' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.laenge_filter_und

/-- info: 'Reformulation.Pfalzgraf.zulaessig_zahl' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.zulaessig_zahl

/-- info: 'Reformulation.Pfalzgraf.guenther_acht' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.guenther_acht

/-- info: 'Reformulation.Pfalzgraf.guenther_acht_localOp' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.guenther_acht_localOp

/-- info: 'Reformulation.Pfalzgraf.unzulaessig_faelle' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.unzulaessig_faelle

/-- info: 'Reformulation.Pfalzgraf.negatoren_induziert' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.negatoren_induziert

/-- info: 'Reformulation.Pfalzgraf.trennfall' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.trennfall

/-- info: 'Reformulation.Pfalzgraf.trennfall_inkohaerent' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.trennfall_inkohaerent

/-- info: 'Reformulation.Pfalzgraf.gegenbeispiel_designation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.gegenbeispiel_designation

/-- info: 'Reformulation.Pfalzgraf.auswQuot_lokal' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.auswQuot_lokal

/-- info: 'Reformulation.Pfalzgraf.belegungen_vollstaendig' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.belegungen_vollstaendig

/-- info: 'Reformulation.Pfalzgraf.entscheideQuot_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.entscheideQuot_iff

/-- info: 'Reformulation.Pfalzgraf.zulaessigFm_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.zulaessigFm_iff

/-- info: 'Reformulation.Pfalzgraf.trenn_gegen_zulaessig' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.trenn_gegen_zulaessig
