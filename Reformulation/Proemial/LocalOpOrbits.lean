import Reformulation.Proemial.TournamentSplitThree
import Reformulation.Proemial.NegationCycle

/-!
# Proemial.LocalOpOrbits — Günthers Tafel XIII (1962): acht Folgen, zwei Bahnen

**EICHUNG** an Günthers Auswahlregel und Aussonderung (*Cybernetic Ontology and
Transjunctional Operations*, 1962, `KorpusRev1/gg_cyb_ontology.pdf`, S. 37 und S. 39, am
Seitenbild gelesen), dazu **ein Brückensatz** zu `TournamentInseparability.transitive_iff`.
Gebaut auf Anordnung des Architekten vom 26. September 2026 (Register §41, N3) nach
`KorpusRev2/Prompt_Impl_TafelXIII_Anker.md`; die Probe steht in
`KorpusRev2/Fund_CybOntology_TafelXIII_Impl.md`.

* **K1 — die Quelle.** Cyb. Ontology S. 37: „We select our value-sequences with the
  stipulation that they shall represent only compounds of the morphograms `[1]` and `[4]`. This
  limits us to exactly eight sequences." Darunter Tafel XIII, acht Spalten zu je neun Werten.
  S. 39: „[4,4,1] as well as [1,1,4] have specific properties which set them apart from the
  other value-sequences." *QUELLENFEST.*
* **K2 — die Tafel ist der Bestand.** `tafel_XIII`: jede der acht Spalten ist, Wert für Wert,
  eine der acht lokal klassischen Operationen `localOp` aus `TournamentInseparability`. Die
  Stellen der Etikette `[a,b,c]` sind die Elementarkontexturen {1,2}, {2,3}, {1,3} (im Bestand
  `{0,1}`, `{1,2}`, `{0,2}`), Günthers `[4]` ist D (`max`), `[1]` ist K (`min`). Die
  Zuordnung der Stellen ist an den Spalten abgelesen, nicht gesetzt.
* **K3 — zwei Bahnen unter Umbenennung der Werte.** Konjugiert man eine Operation mit einem
  Negator, `x, y ↦ N (o (N x) (N y))` (die Umbenennung der Werte durch `N1`, `N2`), so bleibt
  man in der Tafel. Die Tafel zerfällt dabei in genau zwei Bahnen: die von `[4,4,4]` mit
  sechs Folgen (`bahn_max`) und die von `[4,4,1]` mit zwei, `[4,4,1]` und `[1,1,4]`
  (`bahn_zyklisch`). Beide Mengen sind unter beiden Negatoren abgeschlossen und darin
  zusammenhängend. **Die zwei, die Günther auf S. 39 aussondert, sind genau die zweite Bahn.**
* **K4 — die Brücke.** `sechs_iff_transitive`: eine Folge liegt genau dann in der Bahn von
  `[4,4,4]`, wenn das Turnier ihrer Operation transitiv ist. Damit ist Günthers Aussonderung
  von 1962 dieselbe Teilung wie `TournamentSplitThree.cyclic_iff` (KKD, DDK).
* **K5 — das Vokabular.** `bahn_zyklisch` ist unser Name: Die zwei Folgen bilden ein
  zyklisches Turnier. Günther nennt sie 1962 **nicht** zyklisch oder heterarchisch (in der
  Schrift kommen „cyclic", „circular" und „Kreis" nicht vor). Er sondert sie aus und sagt,
  sie hätten „specific properties". Die Gleichsetzung von heterarchisch und zyklisch steht
  bei ihm erst in C&V (S. 27).
* **K6 — Nicht:** der ℜ-Operator (Reflexion auf Morphogrammen, S. 33 f.) ist nicht gebaut; die
  Probe misst nur die Umbenennung der Werte (Günthers η, die Formeln (9) bis (13) auf S. 39).
  „Monoform" (S. 39) ist eine andere Einteilung und nicht gebaut. Kein Anspruch an einen
  Paragraphen von `Definitionen.md`, keine Ledger-Zeile.

## Axiomprofil

Gemessen am grünen Bau, verbatim in den Wachen am Dateiende. **Kein Satz trägt
`Classical.choice`.** `tafel_XIII` und `bahn_zyklisch` tragen `[propext]`, `bahn_max` und
`sechs_iff_transitive` `[propext, Quot.sound]`. Alle vier sind entschieden (`decide`).
-/

namespace Reformulation.Proemial.LocalOpOrbits

open Reformulation.Proemial.NegationCycle
open Reformulation.Proemial.TournamentInseparability

/-- Die neun Argumentpaare in Günthers Reihenfolge (p aussen, q innen). -/
def pairs : List (Fin 3 × Fin 3) :=
  [(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)]

/-- Die Wertfolge einer Operation in Günthers Schreibweise (Werte 1 bis 3). -/
def seqOf (o : Fin 3 → Fin 3 → Fin 3) : List ℕ := pairs.map (fun p => (o p.1 p.2).val + 1)

/-- Günthers Tafel XIII (cyb S. 37), Spalte für Spalte: Etikette, die drei Bits
(`true` = `[4]` = D, `false` = `[1]` = K) und die gedruckte Folge. -/
def tafel : List (String × Bool × Bool × Bool × List ℕ) :=
  [ ("[4,4,4]", true,  true,  true,  [1,2,3,2,2,3,3,3,3]),
    ("[1,4,4]", false, true,  true,  [1,1,3,1,2,3,3,3,3]),
    ("[4,1,4]", true,  false, true,  [1,2,3,2,2,2,3,2,3]),
    ("[4,4,1]", true,  true,  false, [1,2,1,2,2,3,1,3,3]),
    ("[1,1,4]", false, false, true,  [1,1,3,1,2,2,3,2,3]),
    ("[1,4,1]", false, true,  false, [1,1,1,1,2,3,1,3,3]),
    ("[4,1,1]", true,  false, false, [1,2,1,2,2,2,1,2,3]),
    ("[1,1,1]", false, false, false, [1,1,1,1,2,2,1,2,3]) ]

/-- **Tafel XIII ist der Bestand:** jede gedruckte Spalte ist die Folge der lokal klassischen
Operation mit denselben drei Wahlen. -/
theorem tafel_XIII :
    tafel.all (fun e => seqOf (localOp e.2.1 e.2.2.1 e.2.2.2.1) == e.2.2.2.2) = true := by
  decide

/-- Konjugation einer Operation mit dem Negator `N_{i+1}`: die Umbenennung der Werte. -/
def conjOp (i : Fin 2) (o : Fin 3 → Fin 3 → Fin 3) (x y : Fin 3) : Fin 3 :=
  sw i (o (sw i x) (sw i y))

/-- Die Bahn der Ordnung: die sechs Folgen, die aus `[4,4,4]` durch Umbenennung entstehen. -/
def sechs : List (List ℕ) :=
  [seqOf DDD, seqOf KDD, seqOf DKD, seqOf KDK, seqOf DKK, seqOf KKK]

/-- Die zweite Bahn: `[4,4,1]` und `[1,1,4]`. -/
def zwei : List (List ℕ) := [seqOf DDK, seqOf KKD]

/-- Die acht lokal klassischen Operationen. -/
def acht : List (Fin 3 → Fin 3 → Fin 3) := [DDD, KDD, DKD, KKD, DDK, KDK, DKK, KKK]

/-- **Die Bahn von `[4,4,4]`:** sechs verschiedene Folgen; unter Konjugation mit beiden
Negatoren abgeschlossen; jede aus `[4,4,4]` mit höchstens drei Negatoren erreichbar; und
`[4,4,1]`, `[1,1,4]` nicht darunter. -/
theorem bahn_max :
    sechs.Nodup ∧
    (acht.all fun o => (seqOf o ∈ sechs) ==
      ((seqOf (conjOp 0 o) ∈ sechs) && (seqOf (conjOp 1 o) ∈ sechs))) = true ∧
    seqOf KDD = seqOf (conjOp 0 DDD) ∧ seqOf DKD = seqOf (conjOp 1 DDD) ∧
    seqOf KDK = seqOf (conjOp 0 (conjOp 1 DDD)) ∧ seqOf DKK = seqOf (conjOp 1 (conjOp 0 DDD)) ∧
    seqOf KKK = seqOf (conjOp 0 (conjOp 1 (conjOp 0 DDD))) ∧
    seqOf DDK ∉ sechs ∧ seqOf KKD ∉ sechs := by
  decide

/-- **Die Bahn von `[4,4,1]`:** genau `[4,4,1]` und `[1,1,4]`, verschieden, unter beiden
Negatoren abgeschlossen, und jeder Negator vertauscht die zwei. -/
theorem bahn_zyklisch :
    zwei.Nodup ∧
    seqOf (conjOp 0 DDK) = seqOf KKD ∧ seqOf (conjOp 1 DDK) = seqOf KKD ∧
    seqOf (conjOp 0 KKD) = seqOf DDK ∧ seqOf (conjOp 1 KKD) = seqOf DDK := by
  decide

/-- **Die Brücke zu den Turnieren:** eine lokal klassische Operation liegt genau dann in der
Bahn von `[4,4,4]`, wenn ihr Turnier transitiv ist. -/
theorem sechs_iff_transitive :
    ∀ d01 d12 d02 : Bool,
      seqOf (localOp d01 d12 d02) ∈ sechs ↔ TransitiveOp (localOp d01 d12 d02) := by
  decide

-- ============================================================
-- Wachen
-- ============================================================

/-- info: 'Reformulation.Proemial.LocalOpOrbits.tafel_XIII' depends on axioms: [propext] -/
#guard_msgs in #print axioms tafel_XIII

/-- info: 'Reformulation.Proemial.LocalOpOrbits.bahn_max' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms bahn_max

/-- info: 'Reformulation.Proemial.LocalOpOrbits.bahn_zyklisch' depends on axioms: [propext] -/
#guard_msgs in #print axioms bahn_zyklisch

/-- info: 'Reformulation.Proemial.LocalOpOrbits.sechs_iff_transitive' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sechs_iff_transitive

end Reformulation.Proemial.LocalOpOrbits
