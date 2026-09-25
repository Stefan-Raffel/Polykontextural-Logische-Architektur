import Reformulation.Proemial.NegationCycleLength

/-!
# Proemial.NegationCycleCatalog — Günthers Katalog (8)–(13) als Satz

**EICHUNG** bei drei Werten (Teil 1 und Teil 3); dazu ein Satz für jede Wertzahl
(`stationen_abstand`, Teil 2), eine **HEBUNG**: `inv_is_min_length`, über die Brücke
`endpoint_eq_map`/`map_eq_iff` vom Ausgang auf jede Anordnung als Bezugspunkt getragen
(entschieden in der Abnahme, `KorpusRev2/Abnahme_N4_Katalog.md` §2). Gebaut auf Anordnung des Architekten vom
25. September 2026 nach `KorpusRev2/Spec_N4_Katalog.md` (Fassung 3, Mathematiker) und den
Vorab-Proben P1–P8 (`KorpusRev2/Begutachtung_Spec_N4_Katalog_Impl.md`). Die Katalog-Probe
stand zuerst in `KorpusRev2/Evaluation_Traeger_1979_Impl.md`, Anhang A.

* **K1 — die Quelle.** IGN 1979 (*Identität, Gegenidentität und Negativsprache*), S. 26 f.
  und S. 37, am Seitenbild geprüft. Auf der Basis der Äquivalenzen (4) und (5) ergibt sich
  „ein Katalog von Strukturen im Sinne von Handlungsanweisungen, die folgende Gestalt hat"
  (S. 26): (8) für die erste Äquivalenz, dann (9) bis (13), die „sich jeweilig um eine Linie
  verkürzen". Die Legende: „Dabei bedeuten U Umtausch, K l Kreis mit Linksdrall, O
  Ordnungsverhältnis, K r Kreis mit Rechtsdrall und I s Identität in Spiegelung." Auf S. 37:
  „Wollen wir die Zahlenwerte dieser zusätzlichen Operationen von Ordnung (O) und Kreis (K)
  aus der Zählung der Umtauschverhältnisse ermitteln", ergeben sich zwei Tabulierungen, und
  mit der anderen Negation begonnen ist die „einzig relevante Änderung, dass durch den Wechsel
  von N 1 und N 2 ein Vertausch der Drehrichtung im Kreis bewirkt wird". Die 21 Einträge und
  die Tabulierungen sind Günthers, nummeriert wie bei ihm. **Die Tabulierungen haben drei
  Spalten**: die Art, die Stelle 1 bis 6 und eine Spalte, die in jeder Zeile „U" trägt.
  Gebaut ist die Art-Spalte (`tab1`, `tab2`). Was die dritte Spalte meint, ist eine Frage an
  Hermeneutes; dieses Modul sagt über sie nichts.
* **K2 — die Einordnung ist nicht Günthers.** `kat` ordnet einer Wertabbildung eine Art zu:
  Identität `I`, Vertauschung zweier benachbarter Werte `U`, Vertauschung von 1 und 3 `O`, die
  zwei Dreierzyklen `Kl` und `Kr`. Die Drehrichtung ist an Günthers erstem Eintrag geeicht
  (`p K l N1·2 p`); dass danach alle übrigen zwanzig stimmen, ist gemessen (`katalog_true`).
  Das „s" in `I s` („Identität in Spiegelung") bildet `kat` nicht ab. *Marke: ZUORDNUNG.*
* **K3 — zwei Kreise.** Der Katalog steht **auf** dem Hamiltonkreis: der Wechselweg beginnt
  mit Günthers Folgen (4) und (5) (`alt1_basis`, `alt2_basis`), im Bestand Vollkreise
  (`NegationCycle.IsFullCycle`). Sein `K` ist dagegen die **Kreisrelation** zwischen zwei
  Stationen, eine Wertabbildung (ein Dreierzyklus), **nicht** der Vollkreis. Beide heissen bei
  Günther „Kreis" (Definitionen §21, Abschnitt 8).
* **K4 — Stelle und Minimum.** Günthers „Zahlenwerte" sind die Stellen 1 bis 6 entlang des
  Weges. `zahlenwerte` sagt: Die Inversionszahl der Wertabbildung zwischen Station `j` und
  Station `j + k` ist `min k (6 − k)`. Stelle und Zahl werden nicht gleichgesetzt; sie fallen
  auf den Stellen 1 bis 3 zusammen und trennen sich danach. Dass diese Zahl auch die kürzeste
  Wortlänge **zwischen** den Stationen ist, sagt erst `stationen_zahl`, zusammengesetzt aus
  `rel_relates`, `zahlenwerte` und `stationen_abstand`.
* **K5 — die Ordnung ist der verbotene Tausch, vermittelt.** `O` ist als Wertabbildung die
  Vertauschung von 1 und 3, die S. 25 als Negation ausschliesst („keinen rein logischen
  Vorgang"); hier wird sie in drei erlaubten Schritten erreicht. Dass Günther die beiden
  Stellen verbindet, sagt er nicht (Hermeneutes F1). *Marke: ZUORDNUNG, gerechnet.*
* **K6 — Nicht:** keine Verallgemeinerung des Katalogs auf `m` Werte (`stationen_abstand`
  gilt für jedes `m`, spricht aber über Abstände von Anordnungen, nicht über Günthers
  Relationsarten); nicht die Kreisrelation im Vollkreis ab zwei Negatoren; nicht Günthers
  These über „jeden Begriff"; kein Anspruch über die Ledger-Zeile hinaus.

**Wie Teil 2 läuft.** `endpoint w l = l.map (valMap w)`, weil jeder Negator ein `map` ist
(`endpoint_eq_map`). Eine Anordnung enthält jeden Wert (`mem_of_perm`); zwei Abbildungen, die
auf ihr übereinstimmen, stimmen überall überein (`map_eq_iff`). Also erreicht ein Wort von
`A` aus `A.map τ` genau dann, wenn es vom Ausgang aus `(origin m).map τ` erreicht, und
`inv_is_min_length` gibt die kürzeste Länge. Voraussetzung: `(origin m).map τ` ist selbst
eine Anordnung, `τ` also bijektiv; ohne sie ist der Satz leer.

## Axiomprofil

Gemessen am grünen Bau, verbatim in den Wachen am Dateiende. **Kein Satz trägt
`Classical.choice`.** Die Eichungen von Teil 1 und Teil 3 tragen `[propext]`; Teil 2 und
`stationen_zahl` tragen `[propext, Quot.sound]`.
-/

namespace Reformulation.Proemial.NegationCycleCatalog

open Reformulation.Proemial.NegationCycle
open Reformulation.Proemial.NegationCycleLength

-- ============================================================
-- Teil 1 — der Katalog bei drei Werten
-- ============================================================

/-- Günthers fünf Relationsarten (IGN S. 26): `U` Umtausch, `Kl`/`Kr` Kreis mit Links- bzw.
Rechtsdrall, `O` Ordnungsverhältnis, `I` Identität in Spiegelung. -/
inductive Kat | U | Kl | Kr | O | I
  deriving DecidableEq, Repr

/-- Der Wechselweg mit `N1` begonnen (`N1 = sw 0`, `N2 = sw 1`), zwei Umläufe. -/
def alt1 : List (Fin 2) := [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]

/-- Der Wechselweg mit `N2` begonnen, zwei Umläufe. -/
def alt2 : List (Fin 2) := [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]

/-- Die Wertabbildung, die Station `j` in Station `j + k` überführt. -/
def rel (w : List (Fin 2)) (j k : ℕ) (v : Fin 3) : Fin 3 :=
  ((w.drop j).take k).foldl (fun x i => sw i x) v

/-- Die Einordnung einer Wertabbildung auf drei Werten — **nicht Günthers** (K2). Die
Kreisrichtung ist an seinem ersten Eintrag geeicht (`p K l N1·2 p`). -/
def kat (σ : Fin 3 → Fin 3) : Option Kat :=
  match σ 0, σ 1, σ 2 with
  | 0, 1, 2 => some .I
  | 1, 0, 2 => some .U
  | 0, 2, 1 => some .U
  | 2, 1, 0 => some .O
  | 2, 0, 1 => some .Kl
  | 1, 2, 0 => some .Kr
  | _, _, _ => none

/-- `rel` verbindet wirklich die Stationen des Wechselwegs. -/
theorem rel_relates : ∀ j < 6, ∀ k ≤ 6,
    endpoint (alt1.take (j + k)) (origin 2) =
      (endpoint (alt1.take j) (origin 2)).map (rel alt1 j k) := by
  decide

/-- **Günthers Katalog (8)–(13), wie gedruckt** (IGN S. 26 f.): Station `j`, Abstand `k`,
Relationsart. (8): `p`; (9): `N1 p`; (10): `N1·2 p`; (11): `N1·2·1 p`; (12): `N1·2·1·2 p`;
(13): `N1·2·1·2·1 p`. -/
def katalog : List (ℕ × ℕ × Kat) :=
  [ (0,1,.U), (0,2,.Kl), (0,3,.O), (0,4,.Kr), (0,5,.U), (0,6,.I),
    (1,1,.U), (1,2,.Kr), (1,3,.O), (1,4,.Kl), (1,5,.U),
    (2,1,.U), (2,2,.Kl), (2,3,.O), (2,4,.Kr),
    (3,1,.U), (3,2,.Kr), (3,3,.O),
    (4,1,.U), (4,2,.Kl),
    (5,1,.U) ]

/-- Alle 21 gedruckten Einträge stimmen. -/
theorem katalog_true :
    katalog.all (fun e => kat (rel alt1 e.1 e.2.1) == some e.2.2) = true := by
  decide

/-- Die Art in Abhängigkeit von Startlage und Abstand. -/
def soll (j k : ℕ) : Kat :=
  match k % 6 with
  | 0 => .I | 1 => .U | 5 => .U | 3 => .O
  | 2 => if j % 2 = 0 then .Kl else .Kr
  | _ => if j % 2 = 0 then .Kr else .Kl

/-- Jede Station, jeder Abstand: die Art hängt nur vom Abstand ab, beim Kreis — und nur dort —
zusätzlich von der Startlage. -/
theorem katalog_general : ∀ j < 6, ∀ k ≤ 6, kat (rel alt1 j k) = some (soll j k) := by
  decide

/-- Mit `N2` begonnen ist die „einzig relevante Änderung … ein Vertausch der Drehrichtung"
(S. 37): `Kl` und `Kr` tauschen, alles andere bleibt. -/
theorem drall_swap : ∀ j < 6, ∀ k ≤ 6,
    kat (rel alt2 j k) = (kat (rel alt1 j k)).map (fun c => match c with
      | .Kl => .Kr | .Kr => .Kl | c => c) := by
  decide

/-- Der Katalog steht auf Günthers Folge (4), dem Hamiltonkreis mit `N1` begonnen. -/
theorem alt1_basis : alt1.take 6 = tafelVI4 := by decide

/-- … und mit `N2` begonnen auf Folge (5). -/
theorem alt2_basis : alt2.take 6 = tafelVI5 := by decide

/-- Die Art-Spalte der Tabulierung zu `N1` (S. 37). -/
def tab1 : List Kat := [.U, .Kl, .O, .Kr, .U, .I]

/-- Die Art-Spalte der Tabulierung zu `N2` (S. 37). -/
def tab2 : List Kat := [.U, .Kr, .O, .Kl, .U, .I]

/-- Die Tabulierung zu `N1`, Art-Spalte, wie gedruckt. -/
theorem tabulierung1 :
    (List.range 6).map (fun k => kat (rel alt1 0 (k + 1))) = tab1.map some := by
  decide

/-- Die Tabulierung zu `N2`, Art-Spalte, wie gedruckt. -/
theorem tabulierung2 :
    (List.range 6).map (fun k => kat (rel alt2 0 (k + 1))) = tab2.map some := by
  decide

/-- **Stelle und Minimum** (K4): die Inversionszahl der Wertabbildung zwischen Station `j` und
Station `j + k` ist `min k (6 − k)`. -/
theorem zahlenwerte : ∀ j < 6, ∀ k ≤ 6,
    inv ((origin 2).map (rel alt1 j k)) = min k (6 - k) := by
  decide

/-- Dasselbe mit `N2` begonnen. -/
theorem zahlenwerte_N2 : ∀ j < 6, ∀ k ≤ 6,
    inv ((origin 2).map (rel alt2 j k)) = min k (6 - k) := by
  decide

-- ============================================================
-- Teil 2 — der Abstand zweier Anordnungen, für jede Wertzahl
-- ============================================================

section Abstand

variable {m : ℕ}

/-- Die Wertabbildung eines Negatorworts. -/
def valMap : List (Fin m) → Fin (m + 1) → Fin (m + 1)
  | [], v => v
  | i :: is, v => valMap is (sw i v)

/-- Jedes Negatorwort wirkt als `map` seiner Wertabbildung. -/
theorem endpoint_eq_map : ∀ (w : List (Fin m)) (l : List (Fin (m + 1))),
    endpoint w l = l.map (valMap w)
  | [], l => (List.map_id' l).symm
  | i :: is, l => by
    rw [endpoint, endpoint_eq_map is, negate, List.map_map]; rfl

/-- Eine Anordnung enthält jeden Wert. -/
theorem mem_of_perm {A : List (Fin (m + 1))} (hA : A ∈ (origin m).permutations')
    (v : Fin (m + 1)) : v ∈ A :=
  (List.mem_permutations'.1 hA).symm.mem_iff.1 (by simp only [origin, List.mem_finRange])

/-- Auf einer Anordnung stimmen zwei Abbildungen genau dann überein, wenn sie überall
übereinstimmen. -/
theorem map_eq_iff {A : List (Fin (m + 1))} (hA : A ∈ (origin m).permutations')
    (f g : Fin (m + 1) → Fin (m + 1)) : A.map f = A.map g ↔ ∀ v, f v = g v :=
  ⟨fun h v => List.map_inj_left.1 h v (mem_of_perm hA v),
   fun h => List.map_inj_left.2 fun v _ => h v⟩

/-- Der Ausgang ist eine Anordnung. -/
theorem origin_perm : origin m ∈ (origin m).permutations' :=
  List.mem_permutations'.2 (List.Perm.refl _)

/-- **Der Abstand hängt nur von der Relation ab** (Z6): Von jeder Anordnung `A` aus hat der
kürzeste Weg nach `A.map τ` die Länge `inv ((origin m).map τ)`, für jede Wertzahl. -/
theorem stationen_abstand (A : List (Fin (m + 1))) (hA : A ∈ (origin m).permutations')
    (τ : Fin (m + 1) → Fin (m + 1)) (hτ : (origin m).map τ ∈ (origin m).permutations') :
    (∃ w : List (Fin m), w.length = inv ((origin m).map τ) ∧ endpoint w A = A.map τ) ∧
      ∀ w : List (Fin m), endpoint w A = A.map τ → inv ((origin m).map τ) ≤ w.length := by
  have key : ∀ w : List (Fin m), endpoint w A = A.map τ ↔
      endpoint w (origin m) = (origin m).map τ := fun w => by
    rw [endpoint_eq_map, endpoint_eq_map, map_eq_iff hA, map_eq_iff origin_perm]
  obtain ⟨⟨w, hl, he⟩, hmin⟩ := inv_is_min_length _ hτ
  exact ⟨⟨w, hl, (key w).2 he⟩, fun w h => hmin w ((key w).1 h)⟩

end Abstand

-- ============================================================
-- Teil 3 — zusammengesetzt bei drei Werten
-- ============================================================

/-- Jede Station des Wechselwegs ist eine Anordnung. -/
theorem station_perm : ∀ j < 6,
    endpoint (alt1.take j) (origin 2) ∈ (origin 2).permutations' := by
  decide

/-- Jede Relation des Katalogs ist bijektiv. -/
theorem rel_perm : ∀ j < 6, ∀ k ≤ 6,
    (origin 2).map (rel alt1 j k) ∈ (origin 2).permutations' := by
  decide

/-- **Die kürzeste Wortlänge zwischen Station `j` und Station `j + k` ist `min k (6 − k)`**
(E3): aus `rel_relates`, `zahlenwerte` und `stationen_abstand`. -/
theorem stationen_zahl : ∀ j < 6, ∀ k ≤ 6,
    (∃ w : List (Fin 2), w.length = min k (6 - k) ∧
        endpoint w (endpoint (alt1.take j) (origin 2)) = endpoint (alt1.take (j + k)) (origin 2)) ∧
      ∀ w : List (Fin 2),
        endpoint w (endpoint (alt1.take j) (origin 2)) = endpoint (alt1.take (j + k)) (origin 2) →
          min k (6 - k) ≤ w.length := by
  intro j hj k hk
  rw [rel_relates j hj k hk, ← zahlenwerte j hj k hk]
  exact stationen_abstand _ (station_perm j hj) _ (rel_perm j hj k hk)

-- ============================================================
-- Wachen
-- ============================================================

/-- info: 'Reformulation.Proemial.NegationCycleCatalog.rel_relates' depends on axioms: [propext] -/
#guard_msgs in #print axioms rel_relates

/-- info: 'Reformulation.Proemial.NegationCycleCatalog.katalog_true' depends on axioms: [propext] -/
#guard_msgs in #print axioms katalog_true

/-- info: 'Reformulation.Proemial.NegationCycleCatalog.katalog_general' depends on axioms: [propext] -/
#guard_msgs in #print axioms katalog_general

/-- info: 'Reformulation.Proemial.NegationCycleCatalog.drall_swap' depends on axioms: [propext] -/
#guard_msgs in #print axioms drall_swap

/-- info: 'Reformulation.Proemial.NegationCycleCatalog.alt1_basis' depends on axioms: [propext] -/
#guard_msgs in #print axioms alt1_basis

/-- info: 'Reformulation.Proemial.NegationCycleCatalog.alt2_basis' depends on axioms: [propext] -/
#guard_msgs in #print axioms alt2_basis

/-- info: 'Reformulation.Proemial.NegationCycleCatalog.tabulierung1' depends on axioms: [propext] -/
#guard_msgs in #print axioms tabulierung1

/-- info: 'Reformulation.Proemial.NegationCycleCatalog.tabulierung2' depends on axioms: [propext] -/
#guard_msgs in #print axioms tabulierung2

/-- info: 'Reformulation.Proemial.NegationCycleCatalog.zahlenwerte' depends on axioms: [propext] -/
#guard_msgs in #print axioms zahlenwerte

/-- info: 'Reformulation.Proemial.NegationCycleCatalog.zahlenwerte_N2' depends on axioms: [propext] -/
#guard_msgs in #print axioms zahlenwerte_N2

/-- info: 'Reformulation.Proemial.NegationCycleCatalog.endpoint_eq_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms endpoint_eq_map

/-- info: 'Reformulation.Proemial.NegationCycleCatalog.mem_of_perm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms mem_of_perm

/-- info: 'Reformulation.Proemial.NegationCycleCatalog.map_eq_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms map_eq_iff

/-- info: 'Reformulation.Proemial.NegationCycleCatalog.origin_perm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms origin_perm

/-- info: 'Reformulation.Proemial.NegationCycleCatalog.stationen_abstand' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms stationen_abstand

/-- info: 'Reformulation.Proemial.NegationCycleCatalog.station_perm' depends on axioms: [propext] -/
#guard_msgs in #print axioms station_perm

/-- info: 'Reformulation.Proemial.NegationCycleCatalog.rel_perm' depends on axioms: [propext] -/
#guard_msgs in #print axioms rel_perm

/-- info: 'Reformulation.Proemial.NegationCycleCatalog.stationen_zahl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms stationen_zahl

end Reformulation.Proemial.NegationCycleCatalog
