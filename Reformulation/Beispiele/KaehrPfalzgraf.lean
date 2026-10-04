import Reformulation.Pfalzgraf.Faserung
import Reformulation.Kaehr.Tableau

/-!
# Reformulation.Beispiele.KaehrPfalzgraf — der Beweiser und die Prüfung im Quotienten, an Beispielen

**Was diese Datei ist:** Beispiele, keine Ansprüche. Gebaut nach `KorpusRev2/Spec_Beispiele_und_Quotientenpruefung.md`
(Fassung 3, Mathematiker; Ort nach Custos BQ1). Sie gibt dem Leser eine Schreibweise für Formeln und rechnet Kaehrs
Beispiele, den Trennfall, das Gegenbeispiel G und eine Vorlage für eigene Formeln beim Bau durch: Jede Antwort
steht als `#guard`, eine falsche bricht den Bau. Zum Ansehen der Antworten gibt es die Lesedatei
`Beispiele/Lesen.lean` (eigenes Ziel `lake build Beispiele`, ausserhalb der Defaults); sie definiert nichts und
zeigt nur, was hier definiert und geprüft ist.

## K1 · Worauf die Antworten stehen

- **Frei gültig** heisst `beweisbar φ` (Kaehrs Tableau, `Kaehr/Tableau.lean`). `beweisbar_iff` sagt, dass das
  genau die Gültigkeit im freien System ist; `widerlege_some` sagt, dass eine gelieferte Belegung die Formel in
  der genannten Faser falsch macht.
- **Im Quotienten gültig** heisst `entscheideQuot φ` (`Pfalzgraf/Faserung.lean`, K8); `entscheideQuot_iff` sagt,
  dass das genau `gueltigQuot` ist.
- **Zulässig** heisst `zulaessigFm φ` (`zulaessigFm_iff`). Die Antwort im Quotienten fragt zuerst danach.

## K2 · Die Schreibweise ist UNSERE

Sie folgt Kaehrs Junktorzeichen (`∧∧∧`, `∨∨∨`, `⊃⊃⊃`: dieselbe Operation in allen drei Fasern) und Pfalzgrafs
Negatornamen (`N₁` … `N₅`, S. 176 f.; `N₅ = N₁ N₂ N₁`). Ein gemischter Junktor heisst `mix o₀ o₁ o₂ φ ψ`, die
Fasern in Günthers Reihenfolge 1-2, 2-3, 1-3. Die Junktorzeichen sind `scoped`: sichtbar nach
`open Reformulation.Beispiele.KaehrPfalzgraf`. Sie binden `∧∧∧` vor `∨∨∨` vor `⊃⊃⊃` (rechtsassoziativ).
Dass die Schreibweise dieselben Formeln baut wie der Bestand, sagen `trenn_schreibweise` und `G_schreibweise`.

Werte des Quotienten stehen in **Günthers Zählung** 1, 2, 3 (intern Lean 0, 1, 2). Eine Gegenbelegung des freien
Systems steht je Variable als Tripel lokaler Werte, T oder F, in der Faserreihenfolge 1-2, 2-3, 1-3.

## K3 · Eine Konvention, sichtbar gemacht

Der Bestand wertet auch unzulässige Formeln im Quotienten aus, still über die erste lesende Faser (Faserung, K8).
Die Antwort `quotAntwort` meldet darum zuerst „unzulässig“ und zeigt dann keinen Wert. Beispiel B6:
`p₀ ⊃⊃⊃ p₀` ist frei gültig und im Quotienten unzulässig.

## K4 · Was der Leser damit kann, und was nicht

An jeder eigenen Formel beide Semantiken nebeneinander sehen, den Trennfall selbst nachstellen und Kaehrs zwei
offene Äste ablesen. **Nicht:** die Vermutung V beweisen (Faserung, K4). Die Prüfung macht V an einzelnen
Formeln nachrechenbar, nicht allgemein.
-/

namespace Reformulation.Beispiele.KaehrPfalzgraf

open Reformulation.Pfalzgraf
open Reformulation.Kaehr.Tableau (beweisbar beweisbarGedruckt widerlege groesse H1 K)

/-! ## Die Schreibweise -/

/-- die Variablen -/
def p₀ : Fm := .var 0
def p₁ : Fm := .var 1
def p₂ : Fm := .var 2

/-- die Negatoren nach Pfalzgraf (S. 176 f.) -/
def N₁ (a : Fm) : Fm := .neg₁ a
def N₂ (a : Fm) : Fm := .neg₂ a
def N₃ (a : Fm) : Fm := N₂ (N₁ a)
def N₄ (a : Fm) : Fm := N₁ (N₂ a)
def N₅ (a : Fm) : Fm := N₁ (N₂ (N₁ a))

/-- ein gemischter Junktor, Fasern in Günthers Reihenfolge 1-2, 2-3, 1-3 -/
def mix (o0 o1 o2 : Op) (a b : Fm) : Fm := .junk o0 o1 o2 a b

scoped infixl:35 " ∧∧∧ " => fun a b => Fm.junk opK opK opK a b
scoped infixl:30 " ∨∨∨ " => fun a b => Fm.junk opD opD opD a b
scoped infixr:25 " ⊃⊃⊃ " => fun a b => Fm.junk opI opI opI a b

/-! ## Die Ausgabe -/

/-- ein lokaler Wert -/
def tf (b : Bool) : String := if b then "T" else "F"

/-- die Fasern in Günthers Benennung -/
def faserName (i : Faser) : String := ["1-2", "2-3", "1-3"].getD i.val "?"

/-- ein Wert des Quotienten in Günthers Zählung -/
def guenther (v : Wert) : ℕ := v.val + 1

/-- die Variablen einer Formel, ohne Wiederholung, aufsteigend -/
def variablen (φ : Fm) : List ℕ := ((vars φ).eraseDups).mergeSort (fun a b => decide (a ≤ b))

/-- die Gegenbelegung des freien Systems in der Faser i, je Variable das Tripel ihrer lokalen Werte -/
def gegenbelegungText (φ : Fm) (i : Faser) : String :=
  match widerlege (groesse φ) [] [(false, i, φ)] with
  | none => s!"Faser {faserName i}: geschlossen"
  | some g => s!"Faser {faserName i}: " ++ String.intercalate ", " ((variablen φ).map fun n =>
      s!"p{n} ↦ ({tf (g n 0)}, {tf (g n 1)}, {tf (g n 2)})")

/-- die Antwort im freien System -/
def freiAntwort (φ : Fm) : String :=
  if beweisbar φ then "frei gültig"
  else "frei nicht gültig — " ++ String.intercalate "; "
    ((([0, 1, 2] : List Faser).filter fun i => (widerlege (groesse φ) [] [(false, i, φ)]).isSome).map
      (gegenbelegungText φ))

/-- die Antwort im Quotienten:  zuerst die Zulässigkeit (K3) -/
def quotAntwort (φ : Fm) : String :=
  if !zulaessigFm φ then "im Quotienten unzulässig"
  else if entscheideQuot φ then "im Quotienten gültig (Designation {1, 2})"
  else "im Quotienten nicht gültig (Designation {1, 2})"

/-- der Wert im Quotienten, wenn jede Variable den Wert g hat (Günthers Zählung) -/
def wertBei (φ : Fm) (g : ℕ) : ℕ := guenther (auswQuot (fun _ => (⟨(g - 1) % 3, Nat.mod_lt _ (by decide)⟩ : Wert)) φ)

/-! ## Die Beispiele -/

/-- B2:  Kaehrs Trennfall (1981, S. 3, 17), in der Schreibweise -/
def trennfall : Fm := N₅ (p₀ ∧∧∧ N₃ p₀ ∧∧∧ N₄ p₀)

/-- B4:  das Gegenbeispiel G zur Designation {1} -/
def G : Fm := p₀ ∨∨∨ (N₁ p₀ ∨∨∨ N₂ (p₀ ∨∨∨ N₁ p₀))

/-- B5:  eine Formel des Lesers, als Vorlage zum Ändern -/
def eigene : Fm := p₀ ∨∨∨ N₁ p₀

/-- B6:  ein unzulässiger Junktor -/
def unzulaessig : Fm := p₀ ⊃⊃⊃ p₀

/-- eine Formel mit zwei Variablen:  die Gegenbelegung nennt jede Variable -/
def zweiVariablen : Fm := p₁ ∨∨∨ N₁ p₀

/-- die Schreibweise baut den Trennfall des Bestands -/
theorem trenn_schreibweise : trennfall = trenn := rfl

/-- die Schreibweise baut G des Bestands -/
theorem G_schreibweise : G = gegen := rfl

end Reformulation.Beispiele.KaehrPfalzgraf

/-! ## Die Antworten, beim Bau geprüft -/

open Reformulation.Beispiele.KaehrPfalzgraf
open Reformulation.Kaehr.Tableau (beweisbar beweisbarGedruckt H1 K)

-- B1  Kaehrs H1 (1981, S. 16):  beweisbar
#guard beweisbar H1
#guard freiAntwort H1 == "frei gültig"
-- B2  der Trennfall:  frei nicht gültig, mit Kaehrs zwei offenen Ästen — (T, T, F) in 1-2 und 2-3, (F, F, T) in 1-3, wie
--     `kaehr_H2`;  im Quotienten gültig, Wert 1 für p = 1, 2, 3
#guard freiAntwort trennfall ==
  "frei nicht gültig — Faser 1-2: p0 ↦ (T, T, F); Faser 2-3: p0 ↦ (T, T, F); Faser 1-3: p0 ↦ (F, F, T)"
#guard quotAntwort trennfall == "im Quotienten gültig (Designation {1, 2})"
#guard [1, 2, 3].map (wertBei trennfall) == [1, 1, 1]
-- B3  Kaehrs K:  nach der gedruckten Beweisbarkeit ja, nach der Fassung von H1 nein
#guard beweisbarGedruckt K && !beweisbar K
-- B4  G:  frei gültig;  im Quotienten gültig unter {1, 2}, für p = 3 der Wert 2 — unter {1} nicht gültig
#guard freiAntwort G == "frei gültig"
#guard quotAntwort G == "im Quotienten gültig (Designation {1, 2})"
#guard wertBei G 3 == 2
-- B5  die Vorlage:  p₀ ∨∨∨ N₁p₀
#guard freiAntwort eigene == "frei nicht gültig — Faser 2-3: p0 ↦ (T, F, F); Faser 1-3: p0 ↦ (T, F, F)"
#guard quotAntwort eigene == "im Quotienten nicht gültig (Designation {1, 2})"
-- B6  ⊃⊃⊃:  frei gültig, im Quotienten unzulässig — nicht still ausgewertet
#guard freiAntwort unzulaessig == "frei gültig"
#guard quotAntwort unzulaessig == "im Quotienten unzulässig"
-- zwei Variablen:  die Gegenbelegung nennt jede Variable, aufsteigend, in jeder Faser, in der eine gefunden wird
#guard freiAntwort zweiVariablen ==
  "frei nicht gültig — Faser 1-2: p0 ↦ (T, T, T), p1 ↦ (F, T, T); Faser 2-3: p0 ↦ (T, T, F), p1 ↦ (T, F, T); " ++
  "Faser 1-3: p0 ↦ (T, F, T), p1 ↦ (T, T, F)"

/-! ## Axiom-Stand — als Regressions-Wachen gesetzt (alle Sätze des Moduls) -/

/-- info: 'Reformulation.Beispiele.KaehrPfalzgraf.trenn_schreibweise' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Beispiele.KaehrPfalzgraf.trenn_schreibweise

/-- info: 'Reformulation.Beispiele.KaehrPfalzgraf.G_schreibweise' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Beispiele.KaehrPfalzgraf.G_schreibweise
