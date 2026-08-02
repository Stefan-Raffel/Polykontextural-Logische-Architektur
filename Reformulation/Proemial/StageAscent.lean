import Reformulation.Proemial.GeneralCloneBound

/-!
# Proemial.StageAscent — der Stufenaufstieg als Probe

Die erste Probe des Stufen-Strangs (Plan Rev. 3 §8, Ansatz A): ein **gerichteter
Stufenaufstieg** mit einem negativen und einem positiven Satz auf einem Träger.

* **Negativ, uniform in m:** für jedes `m ≥ 4` ist die Lücke der E3-Charakterisierung
  bewohnt — es existiert eine lokal klassische Operation auf `Fin m`, die nicht im Klon
  von `{∧, ∨, ¬}` liegt (`exists_locally_classical_not_in_clone`), und sie liegt auch
  nicht im um alle Konstanten erweiterten Klon (`w_not_in_constant_clone`).
* **Positiv, entlang der Stufen:** das Merkmal bleibt bei der Einbettung erhalten — auf
  dem eingebetteten Quadrat stimmt die Stufe `m+1` mit der Stufe `m` überein
  (`w_castSucc`) —, und jede Stufe bringt Elementarkontexturen hinzu, die im Bild der
  Vorstufe nicht liegen (`ascent_proper`, mit der Zählform `choose_two_succ`).

## Ertrag und Konsum, getrennt

**Ertrag** ist die Zeugenfamilie `w` samt ihren Stufensätzen: dass **eine** Regel auf allen
Stufen zugleich der Zeuge ist, dass sie sich unter der Einbettung selbst reproduziert und
dass der Aufstieg echt ist.

**Konsum** ist der Klon-Ausschluss. `w_not_in_clone` ist die Kontraposition von
`GeneralCloneBound.locally_classical_in_clone_iff`, `w_not_in_constant_clone` die von
`constant_clone_min_or_max`. Keine eigene Invariante, kein kopiertes Kantenlemma, keine
eigene Terminduktion — die Schranke ist E3, und dieses Modul zeigt nur, dass sie bewohnt
ist.

## Der Zeuge

```text
w m a b  =  max a b   falls {a, b} als Werte {0, 1} sind
            min a b   sonst
```

Eine Max-Insel auf dem untersten Paar, sonst durchgehend Minimum. Auf jedem Paar wirkt
`w` klassisch; global ist `w` weder `min` (Widerlegungspunkt `w 0 1 = 1 ≠ 0`) noch `max`
(Widerlegungspunkt `w 0 2 = 0 ≠ 2`). Die Bedingung läuft über `.val`-Gleichungen, nicht
über die `Fin`-Subtraktion (Fallstrick 1); es wird nirgends über einen Funktionsraum
quantifiziert (Fallstrick 3).

**Die Max-Insel `{0,1}` ist gewählt, nicht gefunden.** Jedes andere Paar gäbe einen
anderen Zeugen mit denselben Eigenschaften; die Wahl des untersten ist die, die sich unter
`Fin.castSucc` selbst reproduziert, weil die Einbettung die kleinen Werte festhält.
Rubrik „canonical is the procedure, chosen is the basis".

## Instanzlage — die harte Frage der M3-Datei stellt sich hier nicht

Diese Datei arbeitet auf `GeneralCloneBound.strucM`, der globalen
`L.Structure (Fin m)`-Instanz. **Kein eigener Träger, keine zweite Instanz.** Das ist der
Gegensatz zu `M3CloneWitness`: dort war ein eigener induktiver Typ nötig, weil eine zweite
`L.Structure (Fin 5)`-Instanz neben `strucM` eine stille Instanz-Ambiguität erzeugt hätte.
Hier gibt es nichts zu entscheiden — die Probe bleibt auf dem Träger, den E3 ohnehin
trägt, und konsumiert genau dessen Instanz.

## Deutungs-Marken (verbindlich)

1. **Die Stufen-Lesung ist Deutung, nicht Wortlaut.** Dass sich hier „Kontexturen
   erweitern" und „struktureller Reichtum bei gleichbleibender Erreichbarkeit wächst", ist
   eine Lesart der Sätze S1 bis S3 und steht in keinem Satz und in keinem Namen. Der
   Dateiname sagt, was bewiesen ist: ein Stufenaufstieg.
2. **„Unendlich" erscheint nur als `∀` über Stufen.** Ein Grenzobjekt wird weder gebaut
   noch behauptet; es gibt keinen Kolimes, keinen Strom, keinen M-Typ.
3. **Die Max-Insel ist gewählte Basis** (oben).
4. **Was offen bleibt:** diese Probe schließt keine Ledger-Zeile. Die weltbildhafte
   Totalität, um die es in der Vorlage geht, bleibt ohne Träger; getragen ist ein
   Stufenaufstieg mit zwei Sätzen.

## Robustheit (`CLAUDE.md` §9)

**Die Probe zieht keine neue Schranke** — sie konsumiert eine. Eine Reflexivitätsprüfung
hätte hier nichts zu prüfen. Die konsumierte Schranke besitzt ihre Konstanten-Fassung
(`R m` ist reflexiv, `GeneralCloneBound.R_diag`), und diese Datei konsumiert sie
ausdrücklich: `w_not_in_constant_clone` hält den Ausschluss auch dann, wenn beliebige
konstante Bausteine hinzukommen. Das steht hier, damit niemand eine Prüfung vermisst, die
gegenstandslos wäre.

**Ablage:** setzungsfrei, ohne offene Stelle, konsumiert nur Aggregat-Inhalt — Aggregat.
-/

open FirstOrder Language

namespace Reformulation.Proemial.StageAscent

open Reformulation.Proemial.TransjunctionCloneBound (L)
open Reformulation.Proemial.GeneralCloneBound

variable {m : ℕ}

/-! ## Teil 1 — die Zeugenfamilie

Eine Definition, uniform in `m`. Die Fallunterscheidung läuft über `.val`-Gleichungen auf
`ℕ`; die Beweise unten führen sie von Hand, ohne Auswertung über alle Punkte — die Datei
kommt ohne Entscheidungsverfahren aus und braucht darum keine `Decidable`-Instanzen. -/

/-- **Der Zeuge, uniform in `m`:** Maximum auf dem untersten Paar `{0,1}`, sonst Minimum.
Die Max-Insel ist gewählte Basis (Dateikopf). -/
def w (m : ℕ) (a b : Fin m) : Fin m :=
  if (a.val = 0 ∧ b.val = 1) ∨ (a.val = 1 ∧ b.val = 0) then max a b else min a b

/-- Auf der Diagonale ist `w` die Identität: die Bedingung verlangt zwei verschiedene
Werte an derselben Stelle und ist darum nie erfüllt. Arbeitsstück der Fallzüge unten. -/
lemma w_diag (m : ℕ) (a : Fin m) : w m a a = a := by
  unfold w
  rw [if_neg (by omega)]
  exact min_self a

/-! ## Teil 2 — S1: der negative Kern

Lokale Klassizität von Hand: genau ein Paar enthält beide Inselwerte, nämlich `{0,1}`;
auf ihm wirkt `w` als Maximum, auf jedem anderen Paar ist die Bedingung an allen vier
Punkten falsch. Die Wahl zwischen den beiden Disjunkten wird am Konstruktor getroffen,
nicht über `omega` (Fallstrick 7: ein Disjunktions-Ziel zöge `Classical.choice`). -/

/-- **S1 — `w` ist lokal klassisch**, für jedes `m` und ohne Schranke: auf jedem Paar
`x ≠ y` wirkt `w` wie das Minimum oder wie das Maximum. Bei `m ≤ 1` ist die Aussage leer,
bei `m = 2` wirkt `w` auf dem einen Paar, das es dort gibt, als Maximum. -/
theorem w_locally_classical (m : ℕ) : LocallyClassical (w m) := by
  intro x y hxy
  by_cases h : (x.val = 0 ∧ y.val = 1) ∨ (x.val = 1 ∧ y.val = 0)
  · refine Or.inr ?_
    intro a b ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · rw [w_diag]; exact (max_self _).symm
    · unfold w; rw [if_pos h]
    · unfold w
      rw [if_pos (h.elim (fun hh => Or.inr ⟨hh.2, hh.1⟩) (fun hh => Or.inl ⟨hh.2, hh.1⟩))]
    · rw [w_diag]; exact (max_self _).symm
  · refine Or.inl ?_
    intro a b ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · rw [w_diag]; exact (min_self _).symm
    · unfold w; rw [if_neg h]
    · unfold w
      rw [if_neg (fun hc =>
        h (hc.elim (fun hh => Or.inr ⟨hh.2, hh.1⟩) (fun hh => Or.inl ⟨hh.2, hh.1⟩)))]
    · rw [w_diag]; exact (min_self _).symm

/-- **S1 — `w` ist nicht das Minimum.** Widerlegungspunkt `w 0 1 = 1`, während
`min 0 1 = 0` ist; die Punkte existieren ab zwei Werten. Punktweise über `congrFun`, ohne
`funext`-Umweg. -/
theorem w_ne_min (hm : 2 ≤ m) : w m ≠ fun a b => min a b := by
  intro hEq
  have h := congrFun (congrFun hEq ⟨0, by omega⟩) ⟨1, by omega⟩
  unfold w at h
  rw [if_pos (by simp)] at h
  have hval := congrArg Fin.val h
  simp at hval

/-- **S1 — `w` ist nicht das Maximum.** Widerlegungspunkt `w 0 2 = 0`, während
`max 0 2 = 2` ist; die Punkte existieren ab drei Werten. -/
theorem w_ne_max (hm : 3 ≤ m) : w m ≠ fun a b => max a b := by
  intro hEq
  have h := congrFun (congrFun hEq ⟨0, by omega⟩) ⟨2, by omega⟩
  unfold w at h
  rw [if_neg (by simp)] at h
  have hval := congrArg Fin.val h
  simp at hval

/-- **S1 — der Klon-Ausschluss, als Konsum.** `w m` liegt für kein `m ≥ 4` im Klon von
`{∧, ∨, ¬}`. Reine Kontraposition der E3-Iff: läge `w m` im Klon, so wäre es `min` oder
`max`, und beides ist widerlegt. Kein eigener Beweismittelbau. -/
theorem w_not_in_clone (hm : 4 ≤ m) :
    ¬ ∃ t : L.Term (Fin 2), ∀ v : Fin 2 → Fin m, t.realize v = w m (v 0) (v 1) := by
  intro h
  rcases (locally_classical_in_clone_iff hm (w m) (w_locally_classical m)).mp h with h1 | h1
  · exact w_ne_min (by omega) h1
  · exact w_ne_max (by omega) h1

/-- **S1 — der Ausschluss überlebt beliebige konstante Bausteine.** Dieselbe Aussage über
der um alle `m` Konstanten erweiterten Sprache `Lc m`; Konsum der Konstanten-Fassung von
E3, die an der Reflexivität von `R m` hängt. -/
theorem w_not_in_constant_clone (hm : 4 ≤ m) :
    ¬ ∃ t : (Lc m).Term (Fin 2), ∀ v : Fin 2 → Fin m, t.realize v = w m (v 0) (v 1) := by
  intro h
  rcases constant_clone_min_or_max hm (w m) (w_locally_classical m) h with h1 | h1
  · exact w_ne_min (by omega) h1
  · exact w_ne_max (by omega) h1

/-- **S1 — die zitierbare Form.** Für jedes `m ≥ 4` ist die Lücke der
E3-Charakterisierung bewohnt: es existiert eine lokal klassische Operation auf `Fin m`,
die nicht im Klon liegt. Zeuge ist `w m`. -/
theorem exists_locally_classical_not_in_clone (hm : 4 ≤ m) :
    ∃ f : Fin m → Fin m → Fin m, LocallyClassical f ∧
      ¬ ∃ t : L.Term (Fin 2), ∀ v : Fin 2 → Fin m, t.realize v = f (v 0) (v 1) :=
  ⟨w m, w_locally_classical m, w_not_in_clone hm⟩

/-! ## Teil 3 — S2: der Stufenschritt

Die Erhaltungshälfte. `Fin.castSucc` hält den `.val` fest, und die Bedingung von `w`
läuft über `.val` — darum fallen die Zweige auf beiden Stufen zusammen, und der Rest ist
die `.val`-Gleichheit von Minimum und Maximum unter der Einbettung. -/

/-- **S2 — der Stufenschritt.** Auf dem eingebetteten Quadrat stimmt die Stufe `m+1` mit
der Stufe `m` überein. Das Merkmal aus S1 wandert nicht nur mit — es ist auf beiden Stufen
dieselbe Regel. -/
theorem w_castSucc (m : ℕ) (a b : Fin m) :
    w (m + 1) a.castSucc b.castSucc = (w m a b).castSucc := by
  unfold w
  by_cases h : (a.val = 0 ∧ b.val = 1) ∨ (a.val = 1 ∧ b.val = 0)
  · rw [if_pos (by simpa using h), if_pos h]; exact (Fin.eq_of_val_eq rfl).symm
  · rw [if_neg (by simpa using h), if_neg h]; exact (Fin.eq_of_val_eq rfl).symm

/-! ## Teil 4 — S3: das Wachstum

Die positive Hälfte. Der Aufstieg ist echt: das Bild der Vorstufe verfehlt das neue
Element, und die Zahl der Paare wächst um genau `m`. Die Lesung — jedes Paar mit dem neuen
Element ist eine Elementarkontextur außerhalb des Bildes — steht hier und nicht im
Satz. -/

/-- **S3 — der Aufstieg ist echt.** Kein eingebettetes Element ist das neue: das Bild der
Stufe `m` verfehlt `Fin.last m`. Jedes Paar mit `Fin.last m` liegt darum außerhalb des
Bildes der Vorstufe. -/
theorem ascent_proper (m : ℕ) (a : Fin m) : a.castSucc ≠ Fin.last m :=
  Fin.castSucc_ne_last a

/-- **S3 — die Zählform des Zuwachses.** Jeder Stufenschritt bringt genau `m` neue Paare.
Reine `Nat`-Arithmetik, aus `Nat.choose_succ_succ` und `Nat.choose_one_right` bewiesen und
nicht als Formel zitiert. -/
theorem choose_two_succ (m : ℕ) : (m + 1).choose 2 = m.choose 2 + m := by
  rw [Nat.choose_succ_succ, Nat.choose_one_right, Nat.add_comm]

/-! **Statement-Pins.** Voller Wortlaut links, Satz rechts — jede Drift des *Statements*
bricht den Build. Namenlose `example`s, keine Axiom-Wache. -/

-- STATEMENT-PIN
example (m : ℕ) (hm : 4 ≤ m) :
    ∃ f : Fin m → Fin m → Fin m, LocallyClassical f ∧
      ¬ ∃ t : L.Term (Fin 2), ∀ v : Fin 2 → Fin m, t.realize v = f (v 0) (v 1) :=
  exists_locally_classical_not_in_clone hm
-- STATEMENT-PIN
example (m : ℕ) (a b : Fin m) :
    w (m + 1) a.castSucc b.castSucc = (w m a b).castSucc := w_castSucc m a b
-- STATEMENT-PIN
example (m : ℕ) (hm : 4 ≤ m) :
    ¬ ∃ t : (Lc m).Term (Fin 2), ∀ v : Fin 2 → Fin m, t.realize v = w m (v 0) (v 1) :=
  w_not_in_constant_clone hm

/-! ## Teil 5 — die Axiom-Wachen (Ist-gebunden)

Ist-Ausgabe des grünen Builds (v4.30.0-rc2), pro Satz eingefroren
(Datei-Vollständigkeits-Regel, einschließlich des Hilfslemmas). -/

/-- info: 'Reformulation.Proemial.StageAscent.w_diag' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms w_diag

/-- info: 'Reformulation.Proemial.StageAscent.w_locally_classical' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms w_locally_classical

/-- info: 'Reformulation.Proemial.StageAscent.w_ne_min' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms w_ne_min

/-- info: 'Reformulation.Proemial.StageAscent.w_ne_max' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms w_ne_max

/-- info: 'Reformulation.Proemial.StageAscent.w_not_in_clone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms w_not_in_clone

/-- info: 'Reformulation.Proemial.StageAscent.w_not_in_constant_clone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms w_not_in_constant_clone

/-- info: 'Reformulation.Proemial.StageAscent.exists_locally_classical_not_in_clone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms exists_locally_classical_not_in_clone

/-- info: 'Reformulation.Proemial.StageAscent.w_castSucc' depends on axioms: [propext] -/
#guard_msgs in #print axioms w_castSucc

/-- info: 'Reformulation.Proemial.StageAscent.ascent_proper' does not depend on any axioms -/
#guard_msgs in #print axioms ascent_proper

/-- info: 'Reformulation.Proemial.StageAscent.choose_two_succ' depends on axioms: [propext] -/
#guard_msgs in #print axioms choose_two_succ

end Reformulation.Proemial.StageAscent
