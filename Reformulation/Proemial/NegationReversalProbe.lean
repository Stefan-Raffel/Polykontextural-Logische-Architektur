import Reformulation.Proemial.NegationCycleLength   -- origin, sw, endpoint; words, rueckwaerts_vier

/-!
# Proemial.NegationReversalProbe — Tafel XXI/XXII: die Umkehrung der Wertfolge

STANDALONE, NICHT im Aggregat; Target `Probes`. AxiomGate unberührt. Sonde nach
`KorpusRev2/Sondierung_Tafel_XXII_Umkehrung_Prompt.md` (Mathematiker, 17. Oktober 2026, auf
Anordnung des Architekten). Konsumiert `NegationCycle` (`origin`, `endpoint`) und
`NegationCycleLength` (`words`, `rueckwaerts_vier`); ändert keines von beiden.

## Die Quelle

G. Günther, „Identität, Gegenidentität und Negativsprache" (1979; vordenker-Edition März 2000),
S. 52–54, Textschicht (`KorpusRev1/gunther_identitaet.pdf`). Im Bestand trägt diese Schrift das
Kürzel **IGN** (Register, Custos 5. Oktober, GL12; so auch `NegationCycleCatalog`,
„IGN S. 26", und `NegationCycle`, „IGN S. 41").
S. 52 f.:

> „Durch die Vertauschung des niedrigsten Wertes 1 mit dem höchsten wird nämlich das Aufwärtszählen
> der Werte als arithmetische Ordnung in ein Abwärtszählen verwandelt. Aber diese Idee […] ist nur im
> Fall der Dyadik und der Triadik wirksam. […] Wählen wir aber eine limitierte Arithmetik modulo 4,
> dann lässt sich die quantitative Ordnung durch Auswechseln der kleinsten Wertzahl mit der größten
> nicht mehr in ihr einfaches Gegenteil verkehren. Es müssen vielmehr sechs Negationsoperationen
> durchgeführt werden, ehe das gewünschte Ziel, die Umkehrung der Viererfolge, erreicht ist. Dabei
> existiert relative Freiheit in der Ordnung der Operatoren. Die nächste Tafel XXII gibt nur ein
> Beispiel: p ≡ N 1.2.3.1.2.1 p"

## Was bewiesen ist, mit Marke

- **(G1) BESTÄTIGUNG.** Tausch des kleinsten mit dem größten Wert kehrt die Wertfolge um, bei zwei
  und drei Werten: `swapEnds_rev_two`, `swapEnds_rev_three`.
- **(G2) BESTÄTIGUNG.** Bei vier Werten nicht mehr: `swapEnds_not_rev_four`.
- **FOLGERUNG.** `swapEnds_rev_iff`: für **jede** Wertzahl, und **genau dann**, wenn es höchstens
  drei Werte sind. Günther sagt „Dyadik und Triadik"; die Sonde sagt „genau dann". Der Grund ist
  einfach: ab vier Werten bleibt der zweite Wert unter dem Tausch stehen (`swapEnds_one`), die
  Umkehrung setzt an seine Stelle den vorletzten.
- **(G3) BESTÄTIGUNG.** Günthers Wort `N1·2·3·1·2·1` (Tafel XXII) kehrt die Viererfolge um:
  `guentherWord_rev`. Gelesen wie `endpoint` liest (der erste Buchstabe wirkt zuerst). Das
  rückwärts gelesene Wort tut es ebenso (`guentherWord_reverse_rev`); eine Entscheidung über die
  Leserichtung ist also nicht nötig.
- **(G3′) VERSCHÄRFUNG, aus dem Bestand.** Sechs ist das Minimum: `no_shorter_word`. Günther sagt
  „sechs müssen", nicht „mindestens sechs". Der Beweis zählt nicht neu auf, sondern liest
  `NegationCycleLength.rueckwaerts_vier` (gewacht seit dem NegationCycleLength-Zug).
- **(G4′) VERSCHÄRFUNG, aus dem Bestand.** Die „relative Freiheit" hat genau **sechzehn** Wörter
  der Länge sechs: `sixteen_words`, die erste Hälfte von `rueckwaerts_vier` in der Gestalt des
  Prompts (Ziel als `(origin 3).reverse` statt als Literal).

**Abweichungen vom Prompt, mit Grund.** (1) Die Wertfolge heisst hier `origin m`, nicht `pos m`:
`NegationCycle.origin m := List.finRange (m + 1)` ist genau sie; ein zweiter Name für dasselbe
wäre eine Dublette. (2) G3′ und G4′ stehen im Bestand schon als Satz (`rueckwaerts_vier`, per
`decide +kernel`, Profil `[propext]`). Eine zweite Aufzählung über 364 und 729 Wörter wäre
dieselbe Rechnung noch einmal; die Sätze hier verbrauchen jene. Eine Kernelzeit für die zwei
Aufzählungen gibt es darum in dieser Datei nicht.

**Was die Sonde nicht baut.** Den allgemeinen Satz „die kürzeste Länge der Umkehrung ist
`m(m+1)/2`" — er folgte aus `inv_is_min_length` und der Inversionszahl der umgekehrten Folge,
ist aber nicht Gegenstand von Tafel XXII.

## ZUORDNUNG (nur hier, in keinem Satz)

S. 54 knüpft die Vermittlung von Wollen und Denken an die Bedingung, „dass die Folge der
natürlichen Zahlen identisch ist mit der Folge der Negationen und ein ontologisches
Zugehörigkeitsverhältnis besteht zwischen einer gegebenen natürlichen Zahl n und dem
Negationsoperator N_n". Im Bestand ist das die Zuordnung `i ↦ sw i` (`NegationCycle.sw`; als
Permutation `NegationCycleGenerators.sw_eq_swap`, HEBUNG). Dass das Günthers „ontologisches
Zugehörigkeitsverhältnis" **ist**, sagt kein Satz.

**ZUORDNUNG — zwei Achsen in einer Datei.** Günther trennt Positiv- und Negativsprache „ab ovo"
durch orthogonale Sprachachsen (IGN S. 12). Die Positivsprache beschreibt den „Raum dessen, was
schon da ist" (S. 3); bei den Äquivalenzen seines Kalküls geht es „um Handlungsanweisungen, also
um abstrakte Schemata, die nur im Medium der Technik erfüllt werden können" (S. 29 f.); jeder
Negationszyklus ist „eine spezifische Anweisung …, wie gehandelt bzw. wie etwas konstruiert werden
kann" (S. 50); die Rede ist „vom Umtausch, vom Ordnen und von Kreisbewegungen. Alles Namen für
Tätigkeiten" (S. 51). In diesem Sinn ist `guentherWord` ein Wort der Negativsprache: die
Anweisung, die Viererfolge umzukehren. Die Sätze dieser Datei (`guentherWord_rev` usw.) sind
dagegen Positivsprache: sie beschreiben, was die Anweisung bewirkt. Bei Günther ist die Äquivalenz
`p ≡ N 1.2.3.1.2.1 p` selbst die Anweisung (S. 29 f.); er trennt nicht zwischen der Anweisung und
der Aussage über ihre Wirkung. Lean trennt: `def guentherWord` ist die Anweisung, `theorem
guentherWord_rev` die Beschreibung ihrer Wirkung. Diese Trennung ist Leans, nicht Günthers; dass
beide Achsen in einer Datei stehen, ist darum eine Eigenschaft des Werkzeugs, mit der sich Günthers
Orthogonalität (S. 12) **abbilden**, nicht beweisen lässt. Dass diese Zuordnung Günthers Unterscheidung **ist**, sagt kein Satz; dass
die Sätze nur die Arithmetik beweisen, die er der Negativsprache zugrunde legt, bleibt richtig.
Nichts hier ist die zweite Negation (L07-4 offen).

Kein `sorry`, kein `native_decide`, kein `: True`-Feld, kein `axiom`.
-/

namespace Reformulation.Proemial.NegationReversalProbe

open Reformulation.Proemial.NegationCycle (origin endpoint)
open Reformulation.Proemial.NegationCycleLength (words mem_words rueckwaerts_vier)

-- ============================================================
-- §I — Der Tausch der Enden (G1, G2)
-- ============================================================

/-- **Tausch des kleinsten mit dem größten Wert.** Kein Negator des Bestandes (die Negatoren
tauschen Nachbarn), ausser bei zwei Werten, wo die Enden Nachbarn sind. -/
def swapEnds (m : ℕ) (v : Fin (m + 1)) : Fin (m + 1) :=
  if v = 0 then Fin.last m else if v = Fin.last m then 0 else v

/-- **(G1)** Bei zwei Werten kehrt der Tausch der Enden die Folge um. -/
theorem swapEnds_rev_two : (origin 1).map (swapEnds 1) = (origin 1).reverse := by decide

/-- **(G1)** Bei drei Werten ebenso. -/
theorem swapEnds_rev_three : (origin 2).map (swapEnds 2) = (origin 2).reverse := by decide

/-- **(G2)** Bei vier Werten nicht mehr. -/
theorem swapEnds_not_rev_four : (origin 3).map (swapEnds 3) ≠ (origin 3).reverse := by decide

/-- Ab vier Werten bleibt der zweite Wert unter dem Tausch der Enden stehen. -/
theorem swapEnds_one (k : ℕ) : swapEnds (k + 3) ⟨1, by omega⟩ = ⟨1, by omega⟩ := by
  have h0 : (⟨1, by omega⟩ : Fin (k + 3 + 1)) ≠ 0 :=
    fun h => absurd (congrArg Fin.val h) (by show 1 ≠ 0; decide)
  have hl : (⟨1, by omega⟩ : Fin (k + 3 + 1)) ≠ Fin.last (k + 3) :=
    fun h => absurd (congrArg Fin.val h) (by show 1 ≠ k + 3; omega)
  unfold swapEnds
  rw [if_neg h0, if_neg hl]

/-- **FOLGERUNG.** Der Tausch der Enden kehrt die Wertfolge genau dann um, wenn es höchstens
drei Werte sind. Richtung ←: die drei Fälle. Richtung →: an der zweiten Stelle steht nach dem
Tausch der Wert 1 (`swapEnds_one`), nach der Umkehrung der Wert `m − 1`; gleich nur für `m = 2`. -/
theorem swapEnds_rev_iff (m : ℕ) : (origin m).map (swapEnds m) = (origin m).reverse ↔ m ≤ 2 := by
  match m with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | k + 3 =>
    refine ⟨fun h => ?_, fun h => absurd h (by omega)⟩
    exfalso
    have hl : 1 < ((origin (k + 3)).map (swapEnds (k + 3))).length := by
      rw [List.length_map]; show 1 < (List.finRange (k + 3 + 1)).length
      rw [List.length_finRange]; omega
    have hr : 1 < (origin (k + 3)).reverse.length := by
      rw [List.length_reverse]; show 1 < (List.finRange (k + 3 + 1)).length
      rw [List.length_finRange]; omega
    have h1 : ((origin (k + 3)).map (swapEnds (k + 3)))[1] = ((origin (k + 3)).reverse)[1] := by
      simp only [h]
    rw [List.getElem_map, List.getElem_reverse] at h1
    have hv := congrArg Fin.val h1
    simp only [origin, List.getElem_finRange, List.length_finRange, Fin.cast_mk] at hv
    rw [swapEnds_one k] at hv
    exact absurd hv (by show 1 ≠ k + 3 + 1 - 1 - 1; omega)

-- ============================================================
-- §II — Günthers Wort, Tafel XXII (G3)
-- ============================================================

/-- **Günthers Wort, Tafel XXII:** `N1·2·3·1·2·1`, nullbasiert. -/
def guentherWord : List (Fin 3) := [0, 1, 2, 0, 1, 0]

/-- **(G3)** Sechs Negationen kehren die Viererfolge um — mit Günthers Wort. -/
theorem guentherWord_rev : endpoint guentherWord (origin 3) = (origin 3).reverse := by decide

/-- **(G3), andere Leserichtung.** Rückwärts gelesen tut das Wort dasselbe; die Leserichtung
von `endpoint` ist für Tafel XXII darum keine Entscheidung. -/
theorem guentherWord_reverse_rev :
    endpoint guentherWord.reverse (origin 3) = (origin 3).reverse := by decide

-- ============================================================
-- §III — Minimum und Freiheit (G3′, G4′), aus dem Bestand
-- ============================================================

/-- **(G3′)** Sechs ist das Minimum: kein kürzeres Wort kehrt die Viererfolge um. Aus
`rueckwaerts_vier` (zweite Hälfte), über `mem_words`. -/
theorem no_shorter_word (w : List (Fin 3)) (hw : w.length < 6) :
    endpoint w (origin 3) ≠ (origin 3).reverse := by
  intro h
  have hall := rueckwaerts_vier.2 w.length hw
  rw [List.all_eq_true] at hall
  have h2 := hall w ((mem_words 3 _ w).2 rfl)
  have hrev : (origin 3).reverse = [3, 2, 1, 0] := by decide
  simp_all

/-- **(G4′)** Die „relative Freiheit": genau sechzehn Wörter der Länge sechs kehren um. Die
erste Hälfte von `rueckwaerts_vier`, mit dem Ziel als Umkehrung geschrieben. -/
theorem sixteen_words :
    ((words 3 6).filter (fun w => endpoint w (origin 3) == (origin 3).reverse)).length = 16 := by
  have hrev : (origin 3).reverse = [3, 2, 1, 0] := by decide
  rw [hrev]
  exact rueckwaerts_vier.1

-- ============================================================
-- Wachen — Axiom-Profile
-- ============================================================

/-! **Wachen.** Ist-Ausgabe des grünen Builds (v4.30.0-rc2), alle elf Deklarationen. Kein
`Classical.choice`: `decide` über konkrete `Fin`-Listen, und die Richtung → von
`swapEnds_rev_iff` ohne offenes `simp` (ein erster Beweis mit `simp` zog Choice). -/

/-- info: 'Reformulation.Proemial.NegationReversalProbe.swapEnds' depends on axioms: [propext] -/
#guard_msgs in #print axioms swapEnds

/-- info: 'Reformulation.Proemial.NegationReversalProbe.swapEnds_rev_two' depends on axioms: [propext] -/
#guard_msgs in #print axioms swapEnds_rev_two

/-- info: 'Reformulation.Proemial.NegationReversalProbe.swapEnds_rev_three' depends on axioms: [propext] -/
#guard_msgs in #print axioms swapEnds_rev_three

/-- info: 'Reformulation.Proemial.NegationReversalProbe.swapEnds_not_rev_four' depends on axioms: [propext] -/
#guard_msgs in #print axioms swapEnds_not_rev_four

/-- info: 'Reformulation.Proemial.NegationReversalProbe.swapEnds_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms swapEnds_one

/-- info: 'Reformulation.Proemial.NegationReversalProbe.swapEnds_rev_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms swapEnds_rev_iff

/-- info: 'Reformulation.Proemial.NegationReversalProbe.guentherWord' depends on axioms: [propext] -/
#guard_msgs in #print axioms guentherWord

/-- info: 'Reformulation.Proemial.NegationReversalProbe.guentherWord_rev' depends on axioms: [propext] -/
#guard_msgs in #print axioms guentherWord_rev

/-- info: 'Reformulation.Proemial.NegationReversalProbe.guentherWord_reverse_rev' depends on axioms: [propext] -/
#guard_msgs in #print axioms guentherWord_reverse_rev

/-- info: 'Reformulation.Proemial.NegationReversalProbe.no_shorter_word' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms no_shorter_word

/-- info: 'Reformulation.Proemial.NegationReversalProbe.sixteen_words' depends on axioms: [propext] -/
#guard_msgs in #print axioms sixteen_words
end Reformulation.Proemial.NegationReversalProbe
