import Reformulation.Proemial.TournamentInseparability

/-!
# Proemial.TournamentSplitThree — die Turniere auf drei Knoten: acht, davon sechs transitiv und zwei zyklisch (Q4a)

**BENENNUNG mit einem Brückensatz**, gebaut als Teil **Q4a** von
`KorpusRev2/Spec_Q4_Zaehlung.md` (Anker `5b1ac08`) nach Entscheid des Architekten vom
16. September 2026: die Zählung für `n = 3` in **Bijektions- und Iff-Form**, ohne
`Fintype.card`. Die allgemeine Fassung (`n!` transitive Turniere auf `n` Knoten, Teil Q4b)
ist **nicht** Gegenstand dieses Moduls.

Ein Turnier auf `Fin 3` ist hier eine Bool-Relation `T` mit `T x x = false` und
`T y x = !T x y` für `x ≠ y` (`IsTournament`). Die Sätze:

* `tournament_eq_opTournament` — **die Brücke**: jedes Turnier ist punktweise das Turnier
  einer der acht lokal-klassischen Operationen aus `TournamentInseparability`, und zwar
  der mit den Bits `(!T 0 1, !T 1 2, !T 0 2)`; `opTournament_injective` — verschiedene
  Bits geben verschiedene Turniere.
* `tournamentEquiv` — die Turniere auf `Fin 3` stehen in Bijektion mit `Bool × Bool × Bool`
  (die **Acht** als Bijektion).
* `transitiveT_iff` — **Günthers Kriterium auf Turnieren**: ein Turnier ist genau dann
  transitiv, wenn nicht `T 0 1 = T 1 2 ∧ T 1 2 ≠ T 0 2`. Bewiesen über die Brücke und
  `TournamentInseparability.transitive_iff`, nicht neu gerechnet.
* `transitiveEquiv` — die transitiven Turniere stehen in Bijektion mit den Bit-Vektoren
  außerhalb des zyklischen Musters (die **Sechs** als Bijektion); `cyclic_iff` — ein
  Turnier ist genau dann nicht transitiv, wenn es das Turnier von `KKD` oder von `DDK` ist
  (die **Zwei** als Iff).

Die Zahlen `8`, `6`, `2` selbst stehen nur als `#eval`-Eichung am Dateiende (CLAUDE.md §6:
Zählungen in den Korpus nur in Bijektions- oder Iff-Form).

**Warum Benennung:** Mathlib führt keine Turniere (gemessen, Spec §6 P1), aber für drei
Knoten ist die Zählung eine endliche Fallarbeit. Neuer Satzgehalt ist allein die Brücke
Turnier ↔ Wahlvektor; das Kriterium ist `transitive_iff`, hierher transportiert.

## Quellenlage

*Cognition and Volition*, am Original geprüft (`KorpusRev1/c_and_v.pdf`, Prüfsumme wie im
Quellenanker; PDF-Seite = Druckseite für S. 24–28):

* S. 25: *„six hierarchical patterns of preference possible"* — die Sechs.
* S. 27: *„exhausted all hierarchical orders of preference. They will be heterarchical
  (or cyclic)."* — die Zwei, und die Gleichsetzung heterarchisch/zyklisch ist Günthers.
* S. 28: das Kriterium, das `transitiveT_iff` auf Turnieren trägt (siehe den Kopf von
  `TournamentInseparability`).

*Cybernetic Ontology and Transjunctional Operations* (1962), am Seitenbild:
* S. 39: „`[4,4,1]` as well as `[1,1,4]` have specific properties which set them apart from the
  other value-sequences" — die Aussonderung, *QUELLENFEST*. Getragen durch
  `LocalOpOrbits` (*EICHUNG*): die zwei ausgesonderten Folgen sind DDK und KKD, eine eigene
  Bahn unter Umbenennung (`bahn_zyklisch`), und die übrigen sechs sind genau die transitiven
  (`sechs_iff_transitive`). Günther nennt die zwei 1962 **nicht** zyklisch; das Wort ist
  unseres, die Gleichsetzung heterarchisch = zyklisch steht bei ihm erst in C&V (S. 27).

## Was dieses Modul NICHT sagt

* **Nicht, dass Günthers Präferenzmuster Turniere SIND — im Wort.** Günther legt je
  Zweiersystem einen bevorzugten Wert fest (S. 25) und zeichnet die zyklischen als Pfeile
  (S. 27, Fig. 15/16); Lesart bleibt das **Wort** „Turnier".
* **Nichts für eine andere Wertezahl als drei.** Günther rechnet nur mit drei Werten; die
  allgemeine Zählung ist Q4b und trägt keine Quellenstelle.
* **Nicht die Trennbarkeit** (C2, `TournamentInseparability`) und **nicht die
  Erzeugbarkeit** (E-Reihe). Die E-Reihe teilt dieselben acht 4 : 4, dieses Modul 6 : 2;
  die zwei Teilungen schneiden sich quer.
* **Keine Aussage über Günthers Buchstaben.** `KKD` und `DDK` sind die Namen von
  `TournamentInseparability` (K = `min` auf `0, 1, 2`); wie sie Günthers Buchstaben
  entsprechen, hängt an der Wertzuordnung und steht dort im Kopf.
* **Keine Ledger-Zeile.** Ob Q4 eine Zeile für Paragraph 20 rechtfertigt, entscheidet
  Custos (Spec §7 N4).

## Axiomprofil

Gemessen und am Dateiende gewacht, vierzehn Wachen. **Kein Satz trägt
`Classical.choice`** — die Zählung läuft nicht über `Fintype.card`, darum steht kein
`Fin.fintype` im Term (dort trüge es Choice, gemessen an `Fin.fintype` und
`Fintype.card_perm`, Spec A5).

* **axiomfrei:** `opTournament_isTournament`, `tableOf_eq_opTournament`,
  `opTournament_injective`, `transitiveT_congr`, `opTournament_transitive_iff`,
  `not_cyclic_neg`, `bits_of_cyclic` — alles, was auf Bits und festen Stellen rechnet.
* **`[propext]`:** `opTournament_bits`.
* **`[propext, Quot.sound]`:** `tournament_eq_tableOf` und alles, was über ein beliebiges
  Turnier `T` spricht — `tournament_eq_opTournament`, `transitiveT_iff`, `cyclic_iff` und
  die zwei Bijektionen. Die Quelle ist die Handzerlegung von `Fin 3` (`by_cases` und
  `omega` in `fin3_cases`), in den Bijektionen zusätzlich `funext`.

0 Sorries.
-/

namespace Reformulation.Proemial.TournamentSplitThree

open Reformulation.Proemial.TournamentInseparability

/-! ## Teil 1 — Turniere auf `Fin 3` -/

/-- Ein Turnier auf `Fin 3` als Bool-Relation: `T x y = true` heisst „`x` schlägt `y`".
Irreflexiv, und für `x ≠ y` gilt genau eine Richtung. -/
abbrev IsTournament (T : Fin 3 → Fin 3 → Bool) : Prop :=
  ∀ x y : Fin 3, (x = y → T x y = false) ∧ (x ≠ y → T y x = !T x y)

/-- Transitivität eines Turniers. -/
abbrev TransitiveT (T : Fin 3 → Fin 3 → Bool) : Prop :=
  ∀ x y z : Fin 3, T x y = true → T y z = true → T x z = true

/-- Das Turnier der lokal-klassischen Operation `localOp d01 d12 d02` als Bool-Relation. -/
def opTournament (d01 d12 d02 : Bool) (x y : Fin 3) : Bool :=
  decide (beats (localOp d01 d12 d02) x y)

/-- Das Turnier, das durch seine drei Werte auf `(0,1)`, `(1,2)`, `(0,2)` bestimmt ist. -/
def tableOf (a b c : Bool) (x y : Fin 3) : Bool :=
  if x.val = 0 then (if y.val = 1 then a else if y.val = 2 then c else false)
  else if x.val = 1 then (if y.val = 0 then !a else if y.val = 2 then b else false)
  else (if y.val = 0 then !c else if y.val = 1 then !b else false)

/-- Choice-freie Handzerlegung von `Fin 3` über `.val`. -/
private theorem fin3_cases (x : Fin 3) : x = 0 ∨ x = 1 ∨ x = 2 := by
  have h := x.isLt
  by_cases h0 : x.val = 0
  · exact Or.inl (Fin.ext h0)
  · by_cases h1 : x.val = 1
    · exact Or.inr (Or.inl (Fin.ext h1))
    · exact Or.inr (Or.inr (Fin.ext (by omega)))

/-! ## Teil 2 — Die Brücke -/

/-- Jedes Operationsturnier ist ein Turnier. -/
theorem opTournament_isTournament :
    ∀ d01 d12 d02 : Bool, IsTournament (opTournament d01 d12 d02) := by
  decide

/-- Die Tafel mit den drei Werten ist das Operationsturnier mit den negierten Bits. -/
theorem tableOf_eq_opTournament :
    ∀ a b c : Bool, ∀ x y : Fin 3, tableOf a b c x y = opTournament (!a) (!b) (!c) x y := by
  decide

/-- Ein Turnier stimmt punktweise mit der Tafel seiner drei Werte überein. -/
theorem tournament_eq_tableOf (T : Fin 3 → Fin 3 → Bool) (hT : IsTournament T) :
    ∀ x y : Fin 3, T x y = tableOf (T 0 1) (T 1 2) (T 0 2) x y := by
  intro x y
  rcases fin3_cases x with rfl | rfl | rfl <;> rcases fin3_cases y with rfl | rfl | rfl
  · exact (hT 0 0).1 rfl
  · rfl
  · rfl
  · exact (hT 0 1).2 (by decide)
  · exact (hT 1 1).1 rfl
  · rfl
  · exact (hT 0 2).2 (by decide)
  · exact (hT 1 2).2 (by decide)
  · exact (hT 2 2).1 rfl

/-- **Die Brücke.** Jedes Turnier auf `Fin 3` ist punktweise das Turnier der
lokal-klassischen Operation mit den Bits `(!T 0 1, !T 1 2, !T 0 2)`. -/
theorem tournament_eq_opTournament (T : Fin 3 → Fin 3 → Bool) (hT : IsTournament T) :
    ∀ x y : Fin 3, T x y = opTournament (!T 0 1) (!T 1 2) (!T 0 2) x y :=
  fun x y => (tournament_eq_tableOf T hT x y).trans (tableOf_eq_opTournament _ _ _ x y)

/-- Verschiedene Bits geben verschiedene Turniere. -/
theorem opTournament_injective :
    ∀ a b c a' b' c' : Bool,
      (∀ x y : Fin 3, opTournament a b c x y = opTournament a' b' c' x y) →
        a = a' ∧ b = b' ∧ c = c' := by
  decide

/-- Die Bits eines Operationsturniers lassen sich an drei Stellen ablesen. -/
theorem opTournament_bits :
    ∀ d01 d12 d02 : Bool,
      (!opTournament d01 d12 d02 0 1) = d01 ∧ (!opTournament d01 d12 d02 1 2) = d12 ∧
        (!opTournament d01 d12 d02 0 2) = d02 := by
  decide

/-! ## Teil 3 — Die Acht als Bijektion -/

/-- **Die Acht.** Die Turniere auf `Fin 3` stehen in Bijektion mit `Bool × Bool × Bool`. -/
def tournamentEquiv :
    { T : Fin 3 → Fin 3 → Bool // IsTournament T } ≃ Bool × Bool × Bool where
  toFun T := (!T.1 0 1, !T.1 1 2, !T.1 0 2)
  invFun d := ⟨opTournament d.1 d.2.1 d.2.2, opTournament_isTournament _ _ _⟩
  left_inv T := Subtype.ext (funext fun x => funext fun y =>
    (tournament_eq_opTournament T.1 T.2 x y).symm)
  right_inv d := by
    obtain ⟨d01, d12, d02⟩ := d
    obtain ⟨h1, h2, h3⟩ := opTournament_bits d01 d12 d02
    exact Prod.ext h1 (Prod.ext h2 h3)

/-! ## Teil 4 — Günthers Kriterium auf Turnieren, die Sechs und die Zwei -/

/-- Transitivität überträgt sich auf ein punktweise gleiches Turnier. -/
theorem transitiveT_congr {T T' : Fin 3 → Fin 3 → Bool} (e : ∀ x y, T x y = T' x y) :
    TransitiveT T ↔ TransitiveT T' := by
  constructor
  · intro h x y z hxy hyz
    rw [← e] at hxy hyz ⊢
    exact h x y z hxy hyz
  · intro h x y z hxy hyz
    rw [e] at hxy hyz ⊢
    exact h x y z hxy hyz

/-- Die Transitivität des Operationsturniers ist die Transitivität aus
`TournamentInseparability`. -/
theorem opTournament_transitive_iff :
    ∀ d01 d12 d02 : Bool,
      TransitiveT (opTournament d01 d12 d02) ↔ TransitiveOp (localOp d01 d12 d02) := by
  decide

/-- **Günthers Kriterium auf Turnieren** (C&V S. 28, dort für die Wertordnung). Ein
Turnier auf `Fin 3` ist genau dann transitiv, wenn nicht `(0,1)` und `(1,2)` gleich und
`(0,2)` anders orientiert sind. -/
theorem transitiveT_iff (T : Fin 3 → Fin 3 → Bool) (hT : IsTournament T) :
    TransitiveT T ↔ ¬ (T 0 1 = T 1 2 ∧ T 1 2 ≠ T 0 2) := by
  refine (transitiveT_congr (tournament_eq_opTournament T hT)).trans ?_
  refine (opTournament_transitive_iff _ _ _).trans ?_
  refine (transitive_iff _ _ _).trans ?_
  cases T 0 1 <;> cases T 1 2 <;> cases T 0 2 <;> decide

/-- Das Kriterium ist unter Negation aller drei Werte stabil. -/
theorem not_cyclic_neg :
    ∀ a b c : Bool, ¬ (a = b ∧ b ≠ c) → ¬ ((!a) = (!b) ∧ (!b) ≠ (!c)) := by
  decide

/-- Die zwei zyklischen Wertmuster, als Bits der Operation gelesen: `KKD` oder `DDK`. -/
theorem bits_of_cyclic :
    ∀ a b c : Bool, a = b ∧ b ≠ c →
      ((!a) = false ∧ (!b) = false ∧ (!c) = true) ∨ ((!a) = true ∧ (!b) = true ∧ (!c) = false) := by
  decide

/-- Das zyklische Muster auf Bit-Vektoren, in der Schreibweise von `transitive_iff`. -/
abbrev CyclicBits (d : Bool × Bool × Bool) : Prop := d.1 = d.2.1 ∧ d.2.1 ≠ d.2.2

/-- **Die Sechs.** Die transitiven Turniere auf `Fin 3` stehen in Bijektion mit den
Bit-Vektoren außerhalb des zyklischen Musters. -/
def transitiveEquiv :
    { T : Fin 3 → Fin 3 → Bool // IsTournament T ∧ TransitiveT T }
      ≃ { d : Bool × Bool × Bool // ¬ CyclicBits d } where
  toFun T := ⟨tournamentEquiv ⟨T.1, T.2.1⟩, by
    exact not_cyclic_neg _ _ _ ((transitiveT_iff T.1 T.2.1).mp T.2.2)⟩
  invFun d := ⟨opTournament d.1.1 d.1.2.1 d.1.2.2,
    opTournament_isTournament _ _ _,
    (opTournament_transitive_iff _ _ _).mpr ((transitive_iff _ _ _).mpr d.2)⟩
  left_inv T := Subtype.ext (funext fun x => funext fun y =>
    (tournament_eq_opTournament T.1 T.2.1 x y).symm)
  right_inv d := by
    obtain ⟨⟨d01, d12, d02⟩, hd⟩ := d
    obtain ⟨h1, h2, h3⟩ := opTournament_bits d01 d12 d02
    exact Subtype.ext (Prod.ext h1 (Prod.ext h2 h3))

/-- **Die Zwei.** Ein Turnier auf `Fin 3` ist genau dann nicht transitiv, wenn es
punktweise das Turnier von `KKD` oder von `DDK` ist. -/
theorem cyclic_iff (T : Fin 3 → Fin 3 → Bool) (hT : IsTournament T) :
    ¬ TransitiveT T ↔
      ((∀ x y : Fin 3, T x y = opTournament false false true x y) ∨
        (∀ x y : Fin 3, T x y = opTournament true true false x y)) := by
  rw [transitiveT_iff T hT]
  have e := tournament_eq_opTournament T hT
  constructor
  · intro h
    rcases bits_of_cyclic _ _ _ (Decidable.of_not_not h) with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · rw [h1, h2, h3] at e
      exact Or.inl e
    · rw [h1, h2, h3] at e
      exact Or.inr e
  · rintro (h | h) <;> intro hn <;> apply hn <;>
      rw [h 0 1, h 1 2, h 0 2] <;> decide

/-! ## Eichung: 8 = 6 + 2 (§5 der Spec, Zeile n = 3) -/

/-- Die acht Bit-Vektoren. -/
def allBits : List (Bool × Bool × Bool) :=
  [false, true].flatMap fun a => [false, true].flatMap fun b => [false, true].map fun c =>
    (a, b, c)

/-- info: 8 -/
#guard_msgs in #eval allBits.length
/-- info: 6 -/
#guard_msgs in #eval (allBits.filter fun d =>
  decide (TransitiveT (opTournament d.1 d.2.1 d.2.2))).length
/-- info: 2 -/
#guard_msgs in #eval (allBits.filter fun d =>
  !decide (TransitiveT (opTournament d.1 d.2.1 d.2.2))).length


/-! ## Wachen -/

/-- info: 'Reformulation.Proemial.TournamentSplitThree.opTournament_isTournament' does not depend on any axioms -/
#guard_msgs in #print axioms opTournament_isTournament

/-- info: 'Reformulation.Proemial.TournamentSplitThree.tableOf_eq_opTournament' does not depend on any axioms -/
#guard_msgs in #print axioms tableOf_eq_opTournament

/-- info: 'Reformulation.Proemial.TournamentSplitThree.tournament_eq_tableOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms tournament_eq_tableOf

/-- info: 'Reformulation.Proemial.TournamentSplitThree.tournament_eq_opTournament' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms tournament_eq_opTournament

/-- info: 'Reformulation.Proemial.TournamentSplitThree.opTournament_injective' does not depend on any axioms -/
#guard_msgs in #print axioms opTournament_injective

/-- info: 'Reformulation.Proemial.TournamentSplitThree.opTournament_bits' depends on axioms: [propext] -/
#guard_msgs in #print axioms opTournament_bits

/-- info: 'Reformulation.Proemial.TournamentSplitThree.tournamentEquiv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms tournamentEquiv

/-- info: 'Reformulation.Proemial.TournamentSplitThree.transitiveT_congr' does not depend on any axioms -/
#guard_msgs in #print axioms transitiveT_congr

/-- info: 'Reformulation.Proemial.TournamentSplitThree.opTournament_transitive_iff' does not depend on any axioms -/
#guard_msgs in #print axioms opTournament_transitive_iff

/-- info: 'Reformulation.Proemial.TournamentSplitThree.transitiveT_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms transitiveT_iff

/-- info: 'Reformulation.Proemial.TournamentSplitThree.not_cyclic_neg' does not depend on any axioms -/
#guard_msgs in #print axioms not_cyclic_neg

/-- info: 'Reformulation.Proemial.TournamentSplitThree.bits_of_cyclic' does not depend on any axioms -/
#guard_msgs in #print axioms bits_of_cyclic

/-- info: 'Reformulation.Proemial.TournamentSplitThree.transitiveEquiv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms transitiveEquiv

/-- info: 'Reformulation.Proemial.TournamentSplitThree.cyclic_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms cyclic_iff

end Reformulation.Proemial.TournamentSplitThree
