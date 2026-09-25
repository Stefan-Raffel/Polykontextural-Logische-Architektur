import Reformulation.Proemial.NegationCycle

/-!
# Proemial.NegationCycleSJT — die Steinhaus–Johnson–Trotter-Konstruktion der Vollkreise

**FOLGERUNG und EICHUNG.** Gebaut auf Anordnung des Architekten vom 25. September 2026 nach
`KorpusRev2/Spec_SJT_Zug.md` (Mathematiker), Teil A. Sondiert in
`KorpusRev2/Sondierung_SJT_Listenfassung_Impl.md`, begutachtet in
`KorpusRev2/Begutachtung_Spec_SJT_Zug_Impl.md`. **Teil B**, der Beweis für jede Wertzahl ab
zwei, ist am selben Tag auf eigene Anordnung nach `KorpusRev2/Spec_SJT_TeilB.md`
(Mathematiker) gebaut; er steht unten als Teil 2 des Moduls.

**Die Konstruktion** (`blocks`, `sjtNat`, `sjt`): Der neue Wert fegt abwechselnd nach links
(Indizes `k−2 … 0`) und nach rechts (`0 … k−2`). Zwischen zwei Fegegängen steht ein Schritt
des kleineren Kreises, um eins verschoben, wenn der neue Wert links steht. „Steinhaus–
Johnson–Trotter" ist der Name der Konstruktion in der Mathematik, kein Günther-Wort.

* **K1 — Günthers Voraussetzung.** Günther setzt einen Vollkreis für jede Wertzahl voraus:
  Er spricht vom „Wörterbuch einer fünfwertigen Negativsprache", dessen Termini „schon in
  die Milliarden" gehen (1980 S. 21). Die Wörter dieses Wörterbuchs sind die vollständigen
  Hamiltonkreise (1980 S. 20). Dieses Modul baut die Konstruktion, die solche Kreise liefert,
  und beweist sie als Vollkreis **für jede Wertzahl ab zwei** (`sjt_full`, Teil 2). Die
  Sätze `sjt1_full`, `sjt2_full` und `sjt3_full` für zwei bis vier Werte sind seither
  Spezialfälle und stehen als Eichung.
* **K2 — bei einem Wert gibt es keinen Vollkreis** (`no_full_at_one_value`). Das einzige Wort
  ist das leere, es hat keine Stationen, und die eine Anordnung müsste Station sein. Ein Satz
  über jede Wertzahl beginnt darum bei zwei Werten.
* **K3 — die Listen-Fassung aus einem Vollkreis** (`reach_of_full`, für jedes `m`). Gibt es
  einen Vollkreis, so ist jede Anordnung Endpunkt eines Negatorworts, konstruktiv: Das Wort
  ist das Anfangsstück des Kreises bis zu ihrer Station (`mem_stations_endpoint`). Für jede
  Wertzahl steht sie seit Teil 2 als `reach_all`.
* **K4 — die Konstruktion, die Günther nicht hatte.** `sjt_full` formalisiert nicht
  Günthers Methode; es liefert, was ihm fehlte (Hermeneutes, 25.9.; Entscheid des
  Architekten für Rev9). Die Konstruktion trifft bei drei und vier Werten seine eigenen
  Kreise: Bei drei Werten ist `sjt` Günthers Folge (5) (`sjt2_eq`, IGN S. 18), bei vier
  Werten Negator für Negator sein **emendierter** zweiter Kreis, gespiegelt
  (`sjt3_mirror_kreis2`). Das ist ein Zeuge der Emendation von ausserhalb des Textes: Eine
  Konstruktion, die von Günther nichts weiss, setzt dasselbe `·1·3` an dieselbe Stelle wie
  `kreis2_emendation` und `janus1974`. Bei vier Werten ist es einer von drei Kreisen (der
  erste und der dritte gehören anderen Familien an).
* **K5 — Stellensicht und Wertsicht.** Die Negatoren wirken auf Werte; die Stationen sind
  darum die Inversen der Stationen, die dasselbe Indexwort als Stellentausch erzeugt. Weil
  jeder Negator seine eigene Umkehrung ist, ist ein Wort im einen Sinn genau dann ein
  Vollkreis, wenn es einer im anderen ist. Die Sätze hier sprechen direkt über `IsFullCycle`.

**Teil 2 — ein Vollkreis für jede Wertzahl ab zwei** (Spec Teil B):

* **K-B1 — `sjt_full`.** Die SJT-Folge ist für jede Wertzahl ab zwei ein Vollkreis. Mit
  `no_full_at_one_value` gilt: Ein Vollkreis existiert **genau** ab zwei Werten.
* **K-B2 — `full_exists`** ist Günthers stille Voraussetzung (1980 S. 21, das „Wörterbuch"
  der Negativsprache). `full_length` spricht damit ab zwei Werten über eine **nichtleere**
  Klasse.
* **K-B3 — `reach_all`.** Die Listen-Fassung von N-a für jedes `m`: Jede Anordnung ist
  Endpunkt eines Negatorworts, konstruktiv und **choice-frei**. Daneben steht die
  Perm-Fassung in `NegationCycleGenerators` (`negators_generate_all`); sie trägt Choice aus
  `Equiv.swap` und dem Submonoid-Abschluss.
* **K-B4 — die Projektion.** Der Kern `stations_blocks` sagt: Die Stationen des grossen
  Kreises sind die des kleinen, mit dem neuen Wert an der letzten Stelle in allen Höhen,
  abwechselnd ab- und aufsteigend (`planN`). Streicht man die letzte Stelle und
  standardisiert die Werte, bleibt der kleinere Kreis. Ob das Günthers „enthält" (IGN S. 45,
  „Kreis von Kreisen") ist, bleibt eine Frage an Hermeneutes. IGN S. 29 nennt dazu eine
  Bedingung: „Kreisen von Kreisen" seien „nur dann produzierbar, wenn man mindestens noch
  eine dritte Negation – und damit ein Minimum von Vierwertigkeit – einführt". Sie gilt für
  Günthers Kreis ab zwei Negatoren (Vermerk an `IsFullCycle`) und entscheidet zwischen den
  Lesarten nicht (`KorpusRev2/Antwort_B7_S29_Impl.md` §3).

**Wie der Beweis läuft.** Er wird ganz auf der Ebene der natürlichen Zahlen geführt (`swN`,
`stationsN`, `endpointN`, `insertLast`), wo `omega` arbeitet. `Fin` erscheint nur in der
Brücke (`stations_val`, `endpoint_val`, `toFin_val`, `sjt_val`, `origin_val`) und in der
Übertragung auf die vier Felder (`perm_of_val`, `sjt_full`). Die Reihenfolge ist: die
Blocklemmata (`sweep_step`, `shifted_step`, `top_step`, `sweep_down`, `sweep_up`,
`block_true`, `block_false`), dann der Kern `stations_blocks` mit Endpunkt und Parität
(`flipN`, `length_blocks`, `flipN_even`), dann die Felder (`nodup_planN` über die
Injektivität der Einfügung `insertLast_inj`; `insertLast_perm`; `perm_decompose`), dann die
Induktion über die Wertzahl `sjtN_props`.

**Nicht:** Hegels „Kreis von Kreisen", Tafel XX, kein §20-Anspruch, keine Ledger-Zeile.

## Axiomprofil

Gemessen nach grünem Bau und am Dateiende gewacht, 53 Sätze: Teil A trägt durchweg
`[propext]`. In Teil 2 tragen 37 Sätze `[propext, Quot.sound]`, darunter `sjt_full`,
`full_exists` und `reach_all`; 5 tragen `[propext]`, 3 sind axiomfrei. **Kein
`Classical.choice`** — auch nicht dort, wo Mathlib es anböte. `List.nodup_range` trägt Choice
und ist durch den eigenen `nodupRange` ersetzt. Ein offenes `simp at hlen` in
`perm_decompose` zog Choice (Fallstrick 21) und ist durch einen expliziten Schritt ersetzt.
Kein `set_option maxRecDepth` nötig.
-/

namespace Reformulation.Proemial.NegationCycleSJT

open Reformulation.Proemial.NegationCycle

/-- Die Blöcke: der neue Wert fegt abwechselnd nach links und nach rechts, dazwischen ein
Schritt des kleineren Kreises (um eins verschoben, wenn der neue Wert links steht). -/
def blocks (k : ℕ) : Bool → List ℕ → List ℕ
  | _, [] => []
  | true, s :: ss => (List.range (k - 1)).reverse ++ [s + 1] ++ blocks k false ss
  | false, s :: ss => List.range (k - 1) ++ [s] ++ blocks k true ss

/-- Steinhaus–Johnson–Trotter als Indexwort über `ℕ`, für `n` Werte. -/
def sjtNat : ℕ → List ℕ
  | 0 => []
  | 1 => []
  | 2 => [0, 0]
  | n + 3 => blocks (n + 3) true (sjtNat (n + 2))

/-- Ein Indexwort über `ℕ` als Negatorwort. -/
def toFin (m : ℕ) (l : List ℕ) : List (Fin m) :=
  l.filterMap (fun k => if h : k < m then some ⟨k, h⟩ else none)

/-- Die SJT-Folge als Negatorwort über `m + 1` Werten. -/
def sjt (m : ℕ) : List (Fin m) := toFin m (sjtNat (m + 1))

/-- Jede Station ist Endpunkt eines Anfangsstücks. -/
theorem mem_stations_endpoint {m : ℕ} (w : List (Fin m)) (x l : List (Fin (m + 1)))
    (h : l ∈ stations w x) : ∃ k, endpoint (w.take k) x = l := by
  induction w generalizing x with
  | nil => simp [stations] at h
  | cons i is ih =>
    simp only [stations, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨0, rfl⟩
    · obtain ⟨k, hk⟩ := ih _ h
      exact ⟨k + 1, by simpa [endpoint] using hk⟩

/-- **Die Listen-Fassung aus einem Vollkreis**: gibt es einen Vollkreis, so ist jede
Anordnung Endpunkt eines Negatorworts — für jedes `m`. -/
theorem reach_of_full {m : ℕ} {w : List (Fin m)} (hw : IsFullCycle w)
    (a : List (Fin (m + 1))) (ha : a ∈ (origin m).permutations') :
    ∃ v : List (Fin m), endpoint v (origin m) = a := by
  obtain ⟨k, hk⟩ := mem_stations_endpoint w _ a (hw.all_arrangements a ha)
  exact ⟨_, hk⟩

/-- **Bei einem Wert gibt es keinen Vollkreis.** -/
theorem no_full_at_one_value : ¬ ∃ w : List (Fin 0), IsFullCycle w := by
  rintro ⟨w, hw⟩
  cases w with
  | nil => exact absurd hw (by decide)
  | cons i _ => exact i.elim0

/-- Eichung: zwei Werte. -/
theorem sjt1_full : IsFullCycle (sjt 1) := by decide

/-- Eichung: bei drei Werten ist `sjt` Günthers Folge (5), `N2·1·2·1·2·1` (IGN S. 18). -/
theorem sjt2_eq : sjt 2 = tafelVI5 := by decide

/-- Eichung: drei Werte. -/
theorem sjt2_full : IsFullCycle (sjt 2) := by decide

/-- Eichung: vier Werte. -/
theorem sjt3_full : IsFullCycle (sjt 3) := by decide

/-- **Bei vier Werten ist die SJT-Folge der gespiegelte emendierte zweite Kreis Günthers**,
Negator für Negator. -/
theorem sjt3_mirror_kreis2 : sjt 3 = kreis2.map Fin.rev := by decide

-- ============================================================
-- Teil 2 (Teil B des SJT-Zugs) — ein Vollkreis für jede Wertzahl ab zwei
-- ============================================================

def swN (i v : ℕ) : ℕ := if v = i then i + 1 else if v = i + 1 then i else v
def stationsN : List ℕ → List ℕ → List (List ℕ)
  | [], _ => []
  | i :: is, l => l :: stationsN is (l.map (swN i))
def endpointN : List ℕ → List ℕ → List ℕ
  | [], l => l
  | i :: is, l => endpointN is (l.map (swN i))
def insertLast (g : List ℕ) (j : ℕ) : List ℕ := g.map (fun v => if v ≥ j then v + 1 else v) ++ [j]

theorem stationsN_append (a b l : List ℕ) :
    stationsN (a ++ b) l = stationsN a l ++ stationsN b (endpointN a l) := by
  induction a generalizing l with
  | nil => rfl
  | cons i is ih => simp only [List.cons_append, stationsN, endpointN, ih]

theorem endpointN_append (a b l : List ℕ) :
    endpointN (a ++ b) l = endpointN b (endpointN a l) := by
  induction a generalizing l with
  | nil => rfl
  | cons i is ih => simp only [List.cons_append, endpointN, ih]

theorem swN_swN (i v : ℕ) : swN i (swN i v) = v := by
  unfold swN; split_ifs <;> omega

theorem sweep_step (g : List ℕ) (j : ℕ) :
    (insertLast g (j + 1)).map (swN j) = insertLast g j := by
  unfold insertLast
  rw [List.map_append, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro v _
    simp only [Function.comp_apply, swN]
    split_ifs <;> omega
  · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
    unfold swN; split_ifs <;> omega

theorem sweep_up_step (g : List ℕ) (j : ℕ) :
    (insertLast g j).map (swN j) = insertLast g (j + 1) := by
  rw [← sweep_step g j, List.map_map]
  conv => rhs; rw [← List.map_id (insertLast g (j + 1))]
  apply List.map_congr_left; intro v _; exact swN_swN j v

theorem shifted_step (g : List ℕ) (s : ℕ) :
    (insertLast g 0).map (swN (s + 1)) = insertLast (g.map (swN s)) 0 := by
  unfold insertLast
  rw [List.map_append, List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro v _
  simp only [Function.comp_apply, swN]
  split_ifs <;> omega

theorem top_step (g : List ℕ) (n s : ℕ) (hs : s + 1 < n) (hg : ∀ v ∈ g, v < n) :
    (insertLast g n).map (swN s) = insertLast (g.map (swN s)) n := by
  unfold insertLast
  rw [List.map_append, List.map_map, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro v hv
    have := hg v hv
    simp only [Function.comp_apply, swN]
    split_ifs <;> omega
  · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
    unfold swN; split_ifs <;> omega

/-- Fegegang abwärts. -/
theorem sweep_down (g : List ℕ) : ∀ j,
    stationsN (List.range j).reverse (insertLast g j) =
      (List.range j).reverse.map (fun t => insertLast g (t + 1)) ∧
    endpointN (List.range j).reverse (insertLast g j) = insertLast g 0
  | 0 => ⟨rfl, rfl⟩
  | j + 1 => by
    obtain ⟨h1, h2⟩ := sweep_down g j
    rw [List.range_succ, List.reverse_append]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      stationsN, endpointN, sweep_step, List.map_cons, h1, h2]
    exact ⟨trivial, trivial⟩

/-- Fegegang aufwärts. -/
theorem sweep_up (g : List ℕ) : ∀ j,
    stationsN (List.range j) (insertLast g 0) = (List.range j).map (insertLast g) ∧
    endpointN (List.range j) (insertLast g 0) = insertLast g j
  | 0 => ⟨rfl, rfl⟩
  | j + 1 => by
    obtain ⟨h1, h2⟩ := sweep_down g 0
    obtain ⟨u1, u2⟩ := sweep_up g j
    rw [List.range_succ, stationsN_append, endpointN_append, u1, u2]
    simp only [stationsN, endpointN, List.map_append, List.map_cons, List.map_nil,
      sweep_up_step]
    exact ⟨trivial, trivial⟩


theorem range_succ_rev_map {α : Type} (f : ℕ → α) (n : ℕ) :
    (List.range (n + 1)).reverse.map f = (List.range n).reverse.map (fun t => f (t + 1)) ++ [f 0] := by
  rw [List.range_succ_eq_map, List.reverse_cons, List.map_append, List.map_reverse,
    List.map_reverse, List.map_map]
  rfl

/-- Ein Block abwärts. -/
theorem block_true (g : List ℕ) (n s : ℕ) :
    stationsN ((List.range n).reverse ++ [s + 1]) (insertLast g n) =
      (List.range (n + 1)).reverse.map (insertLast g) ∧
    endpointN ((List.range n).reverse ++ [s + 1]) (insertLast g n) =
      insertLast (g.map (swN s)) 0 := by
  obtain ⟨h1, h2⟩ := sweep_down g n
  rw [stationsN_append, endpointN_append, h1, h2, range_succ_rev_map]
  simp only [stationsN, endpointN, shifted_step]
  exact ⟨trivial, trivial⟩

/-- Ein Block aufwärts. -/
theorem block_false (g : List ℕ) (n s : ℕ) (hs : s + 1 < n) (hg : ∀ v ∈ g, v < n) :
    stationsN (List.range n ++ [s]) (insertLast g 0) =
      (List.range (n + 1)).map (insertLast g) ∧
    endpointN (List.range n ++ [s]) (insertLast g 0) = insertLast (g.map (swN s)) n := by
  obtain ⟨h1, h2⟩ := sweep_up g n
  rw [stationsN_append, endpointN_append, h1, h2, List.range_succ, List.map_append]
  simp only [stationsN, endpointN, top_step g n s hs hg]
  exact ⟨rfl, trivial⟩

def topN (n : ℕ) : Bool → ℕ
  | true => n
  | false => 0

def planN (n : ℕ) : Bool → List (List ℕ) → List (List ℕ)
  | _, [] => []
  | true, g :: gs => (List.range (n + 1)).reverse.map (insertLast g) ++ planN n false gs
  | false, g :: gs => (List.range (n + 1)).map (insertLast g) ++ planN n true gs

def flipN : Bool → ℕ → Bool
  | b, 0 => b
  | b, k + 1 => flipN (!b) k

theorem swN_lt {n s v : ℕ} (hs : s + 1 < n) (hv : v < n) : swN s v < n := by
  unfold swN; split_ifs <;> omega

theorem blocks_true_cons (n s : ℕ) (ss : List ℕ) :
    blocks (n + 1) true (s :: ss) = ((List.range n).reverse ++ [s + 1]) ++ blocks (n + 1) false ss := by
  simp [blocks]

theorem blocks_false_cons (n s : ℕ) (ss : List ℕ) :
    blocks (n + 1) false (s :: ss) = (List.range n ++ [s]) ++ blocks (n + 1) true ss := by
  simp [blocks]

/-- **P2, der Kern**: die Stationen der Blöcke sind die Einfügungen in die Stationen des
kleinen Wortes; dazu der Endpunkt mit der Parität. -/
theorem stations_blocks (n : ℕ) : ∀ (S : List ℕ) (b : Bool) (g : List ℕ),
    (∀ s ∈ S, s + 1 < n) → (∀ v ∈ g, v < n) →
    stationsN (blocks (n + 1) b S) (insertLast g (topN n b)) = planN n b (stationsN S g) ∧
    endpointN (blocks (n + 1) b S) (insertLast g (topN n b)) =
      insertLast (endpointN S g) (topN n (flipN b S.length))
  | [], b, g, _, _ => by cases b <;> exact ⟨rfl, rfl⟩
  | s :: ss, b, g, hS, hg => by
    have hs : s + 1 < n := hS s List.mem_cons_self
    have hss : ∀ t ∈ ss, t + 1 < n := fun t ht => hS t (List.mem_cons_of_mem _ ht)
    have hg' : ∀ v ∈ g.map (swN s), v < n := by
      intro v hv
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
      exact swN_lt hs (hg u hu)
    cases b with
    | true =>
      obtain ⟨b1, b2⟩ := block_true g n s
      obtain ⟨i1, i2⟩ := stations_blocks n ss false (g.map (swN s)) hss hg'
      rw [show topN n false = 0 from rfl] at i1 i2
      rw [blocks_true_cons, show topN n true = n from rfl,
        stationsN_append ((List.range n).reverse ++ [s + 1]),
        endpointN_append ((List.range n).reverse ++ [s + 1]), b1, b2, i1, i2]
      exact ⟨rfl, rfl⟩
    | false =>
      obtain ⟨b1, b2⟩ := block_false g n s hs hg
      obtain ⟨i1, i2⟩ := stations_blocks n ss true (g.map (swN s)) hss hg'
      rw [show topN n true = n from rfl] at i1 i2
      rw [blocks_false_cons, show topN n false = 0 from rfl,
        stationsN_append (List.range n ++ [s]),
        endpointN_append (List.range n ++ [s]), b1, b2, i1, i2]
      exact ⟨rfl, rfl⟩


/-- `range` ist duplikatfrei — ohne `List.nodup_range`, das `Classical.choice` trägt. -/
theorem nodupRange : ∀ n, (List.range n).Nodup
  | 0 => List.nodup_nil
  | n + 1 => by
    rw [List.range_succ, List.nodup_append]
    refine ⟨nodupRange n, List.nodup_singleton n, ?_⟩
    intro a ha b hb
    rw [List.mem_singleton] at hb
    rw [List.mem_range] at ha
    omega

def upN (j v : ℕ) : ℕ := if v ≥ j then v + 1 else v

theorem upN_inj (j : ℕ) : Function.Injective (upN j) := by
  intro a b h; unfold upN at h; split_ifs at h <;> omega

theorem insertLast_eq (g : List ℕ) (j : ℕ) : insertLast g j = g.map (upN j) ++ [j] := rfl

/-- Die Einfügung ist injektiv. -/
theorem insertLast_inj {g g' : List ℕ} {j j' : ℕ} (h : insertLast g j = insertLast g' j') :
    g = g' ∧ j = j' := by
  rw [insertLast_eq, insertLast_eq] at h
  have hl : (g.map (upN j)).length = (g'.map (upN j')).length := by
    have := congrArg List.length h
    simp only [List.length_append, List.length_singleton] at this
    omega
  obtain ⟨h1, h2⟩ := List.append_inj h hl
  have hj : j = j' := by simpa using h2
  subst hj
  exact ⟨(List.map_injective_iff.mpr (upN_inj j)) h1, rfl⟩

theorem mem_planN (n : ℕ) : ∀ (b : Bool) (gs : List (List ℕ)) (l : List ℕ),
    l ∈ planN n b gs ↔ ∃ g ∈ gs, ∃ j, j < n + 1 ∧ insertLast g j = l
  | _, [], l => by simp [planN]
  | true, g :: gs, l => by
    rw [planN, List.mem_append, mem_planN n false gs l]
    simp only [List.mem_map, List.mem_reverse, List.mem_range, List.mem_cons]
    constructor
    · rintro (⟨j, hj, rfl⟩ | ⟨g', hg', j, hj, rfl⟩)
      · exact ⟨g, Or.inl rfl, j, hj, rfl⟩
      · exact ⟨g', Or.inr hg', j, hj, rfl⟩
    · rintro ⟨g', (rfl | hg'), j, hj, rfl⟩
      · exact Or.inl ⟨j, hj, rfl⟩
      · exact Or.inr ⟨g', hg', j, hj, rfl⟩
  | false, g :: gs, l => by
    rw [planN, List.mem_append, mem_planN n true gs l]
    simp only [List.mem_map, List.mem_range, List.mem_cons]
    constructor
    · rintro (⟨j, hj, rfl⟩ | ⟨g', hg', j, hj, rfl⟩)
      · exact ⟨g, Or.inl rfl, j, hj, rfl⟩
      · exact ⟨g', Or.inr hg', j, hj, rfl⟩
    · rintro ⟨g', (rfl | hg'), j, hj, rfl⟩
      · exact Or.inl ⟨j, hj, rfl⟩
      · exact Or.inr ⟨g', hg', j, hj, rfl⟩

theorem insertLast_inj_right (g : List ℕ) : Function.Injective (insertLast g) :=
  fun _ _ h => (insertLast_inj h).2

theorem nodup_planN (n : ℕ) : ∀ (b : Bool) (gs : List (List ℕ)), gs.Nodup → (planN n b gs).Nodup
  | _, [], _ => by simp [planN]
  | b, g :: gs, hgs => by
    have hg : g ∉ gs := (List.nodup_cons.mp hgs).1
    have hrest : gs.Nodup := (List.nodup_cons.mp hgs).2
    have hblock : ∀ l, l ∈ (if b then (List.range (n + 1)).reverse.map (insertLast g)
        else (List.range (n + 1)).map (insertLast g)) → ∃ j, insertLast g j = l := by
      intro l hl
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, List.mem_map] at hl <;>
        obtain ⟨j, _, rfl⟩ := hl <;> exact ⟨j, rfl⟩
    have hdisj : ∀ l, (∃ j, insertLast g j = l) → l ∉ planN n (!b) gs := by
      rintro l ⟨j, rfl⟩ hl
      obtain ⟨g', hg', j', _, he⟩ := (mem_planN n (!b) gs _).mp hl
      exact hg ((insertLast_inj he).1 ▸ hg')
    cases b with
    | true =>
      rw [planN, List.nodup_append]
      refine ⟨(List.nodup_reverse.mpr (nodupRange _)).map (insertLast_inj_right g),
        nodup_planN n false gs hrest, ?_⟩
      intro a ha c hc hac
      subst hac
      exact hdisj a (hblock a (by simpa using ha)) hc
    | false =>
      rw [planN, List.nodup_append]
      refine ⟨(nodupRange _).map (insertLast_inj_right g), nodup_planN n true gs hrest, ?_⟩
      intro a ha c hc hac
      subst hac
      exact hdisj a (hblock a (by simpa using ha)) hc


theorem mem_insertLast_range (n j x : ℕ) (hj : j ≤ n) :
    x ∈ insertLast (List.range n) j ↔ x < n + 1 := by
  rw [insertLast_eq, List.mem_append, List.mem_map, List.mem_singleton]
  constructor
  · rintro (⟨v, hv, rfl⟩ | rfl)
    · rw [List.mem_range] at hv; unfold upN; split_ifs <;> omega
    · omega
  · intro hx
    by_cases hxj : x = j
    · exact Or.inr hxj
    · left
      by_cases hlt : x < j
      · exact ⟨x, List.mem_range.mpr (by omega), by unfold upN; split_ifs <;> omega⟩
      · exact ⟨x - 1, List.mem_range.mpr (by omega), by unfold upN; split_ifs <;> omega⟩

theorem nodup_insertLast_range (n j : ℕ) : (insertLast (List.range n) j).Nodup := by
  rw [insertLast_eq, List.nodup_append]
  refine ⟨(nodupRange n).map (upN_inj j), List.nodup_singleton j, ?_⟩
  intro a ha b hb hab
  rw [List.mem_singleton] at hb
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp ha
  subst hb
  unfold upN at hab; split_ifs at hab <;> omega

/-- **P5**: eine Einfügung in eine Anordnung ist eine Anordnung. -/
theorem insertLast_perm {g : List ℕ} {n j : ℕ} (hg : g.Perm (List.range n)) (hj : j ≤ n) :
    (insertLast g j).Perm (List.range (n + 1)) := by
  have h1 : (insertLast g j).Perm (insertLast (List.range n) j) := by
    rw [insertLast_eq, insertLast_eq]
    exact (hg.map (upN j)).append_right [j]
  refine h1.trans ?_
  refine (List.perm_ext_iff_of_nodup (nodup_insertLast_range n j) (nodupRange _)).mpr ?_
  intro x
  rw [mem_insertLast_range n j x hj, List.mem_range]

def downN (j v : ℕ) : ℕ := if j < v then v - 1 else v

/-- **P4**: jede Anordnung von `n + 1` Werten ist eine Einfügung in eine Anordnung von `n`. -/
theorem perm_decompose {l : List ℕ} {n : ℕ} (hl : l.Perm (List.range (n + 1))) :
    ∃ g j, g.Perm (List.range n) ∧ j ≤ n ∧ insertLast g j = l := by
  have hlen : l.length = n + 1 := by rw [hl.length_eq, List.length_range]
  have hne : l ≠ [] := by
    intro h; rw [h, List.length_nil] at hlen; exact absurd hlen (Nat.succ_ne_zero n).symm
  have hnd : l.Nodup := hl.nodup_iff.mpr (nodupRange _)
  have hmem : ∀ x, x ∈ l ↔ x < n + 1 := fun x => by rw [hl.mem_iff, List.mem_range]
  set j := l.getLast hne with hjdef
  set d := l.dropLast with hddef
  have hsplit : d ++ [j] = l := List.dropLast_append_getLast hne
  have hjmem : j ∈ l := List.getLast_mem hne
  have hjn : j ≤ n := by have := (hmem j).mp hjmem; omega
  have hdnd : (d ++ [j]).Nodup := hsplit ▸ hnd
  have hdj : ∀ v ∈ d, v ≠ j := by
    intro v hv hvj
    rw [List.nodup_append] at hdnd
    exact hdnd.2.2 v hv j (List.mem_singleton_self j) hvj
  have hdl : ∀ v ∈ d, v < n + 1 := fun v hv =>
    (hmem v).mp (hsplit ▸ List.mem_append_left [j] hv)
  refine ⟨d.map (downN j), j, ?_, hjn, ?_⟩
  · have hdnd' : d.Nodup := (List.nodup_append.mp hdnd).1
    have hgnd : (d.map (downN j)).Nodup := by
      refine hdnd'.map_on ?_
      intro a ha b hb hab
      have := hdj a ha; have := hdj b hb
      unfold downN at hab; split_ifs at hab <;> omega
    refine (List.perm_ext_iff_of_nodup hgnd (nodupRange n)).mpr ?_
    intro x
    rw [List.mem_range, List.mem_map]
    constructor
    · rintro ⟨v, hv, rfl⟩
      have := hdj v hv; have := hdl v hv
      unfold downN; split_ifs <;> omega
    · intro hx
      refine ⟨upN j x, ?_, ?_⟩
      · have hux : upN j x < n + 1 := by unfold upN; split_ifs <;> omega
        have hul : upN j x ∈ l := (hmem _).mpr hux
        rw [← hsplit, List.mem_append, List.mem_singleton] at hul
        rcases hul with h | h
        · exact h
        · exfalso; unfold upN at h; split_ifs at h <;> omega
      · unfold upN downN; split_ifs <;> omega
  · rw [insertLast_eq, List.map_map]
    conv => rhs; rw [← hsplit]
    congr 1
    conv => rhs; rw [← List.map_id d]
    apply List.map_congr_left
    intro v hv
    have := hdj v hv
    simp only [Function.comp_apply, id]
    unfold upN downN; split_ifs <;> omega


theorem blocks_lt (k : ℕ) (b : Bool) (ss : List ℕ) (hk : 2 ≤ k)
    (hs : ∀ s ∈ ss, s + 2 < k) : ∀ j ∈ blocks k b ss, j < k - 1 := by
  induction ss generalizing b with
  | nil => cases b <;> simp [blocks]
  | cons s ss ih =>
    have h0 := hs s (List.mem_cons_self)
    have h1 : ∀ t ∈ ss, t + 2 < k := fun t ht => hs t (List.mem_cons_of_mem _ ht)
    cases b <;> intro j hj <;> simp only [blocks, List.mem_append, List.mem_range,
      List.mem_reverse, List.mem_singleton] at hj
    · rcases hj with (hj | hj) | hj
      · omega
      · omega
      · exact ih true h1 j hj
    · rcases hj with (hj | hj) | hj
      · omega
      · omega
      · exact ih false h1 j hj

theorem sjtNat_lt : ∀ n, ∀ j ∈ sjtNat (n + 2), j < n + 1
  | 0 => by intro j hj; simp [sjtNat] at hj; omega
  | n + 1 => by
    intro j hj
    have ih := sjtNat_lt n
    have := blocks_lt (n + 3) true (sjtNat (n + 2)) (by omega)
      (fun s hs => by have := ih s hs; omega) j (by simpa [sjtNat] using hj)
    omega

theorem length_blocks (k : ℕ) (hk : 1 ≤ k) : ∀ (b : Bool) (S : List ℕ),
    (blocks k b S).length = k * S.length
  | _, [] => by cases ‹Bool› <;> rfl
  | true, s :: ss => by
    rw [blocks, List.length_append, List.length_append, length_blocks k hk false ss,
      List.length_reverse, List.length_range, List.length_singleton, List.length_cons,
      Nat.mul_succ]
    omega
  | false, s :: ss => by
    rw [blocks, List.length_append, List.length_append, length_blocks k hk true ss,
      List.length_range, List.length_singleton, List.length_cons, Nat.mul_succ]
    omega

theorem flipN_even (b : Bool) : ∀ t, flipN b (2 * t) = b
  | 0 => rfl
  | t + 1 => by
    rw [show 2 * (t + 1) = 2 * t + 1 + 1 by omega]
    show flipN (!!b) (2 * t) = b
    rw [Bool.not_not]; exact flipN_even b t

theorem insertLast_range (k : ℕ) : insertLast (List.range k) k = List.range (k + 1) := by
  rw [insertLast_eq, List.range_succ]
  congr 1
  conv => rhs; rw [← List.map_id (List.range k)]
  apply List.map_congr_left
  intro v hv
  rw [List.mem_range] at hv
  unfold upN; split_ifs <;> first | omega | rfl

/-- **Der allgemeine Satz auf der ℕ-Ebene**: für jede Wertzahl `n + 2` kehrt das SJT-Wort
zurück, seine Stationen sind duplikatfrei, jede ist eine Anordnung, und jede Anordnung ist
Station; dazu die gerade Länge, die die Parität des letzten Fegegangs trägt. -/
theorem sjtN_props : ∀ n,
    endpointN (sjtNat (n + 2)) (List.range (n + 2)) = List.range (n + 2) ∧
    (stationsN (sjtNat (n + 2)) (List.range (n + 2))).Nodup ∧
    (∀ l ∈ stationsN (sjtNat (n + 2)) (List.range (n + 2)), l.Perm (List.range (n + 2))) ∧
    (∀ l, l.Perm (List.range (n + 2)) → l ∈ stationsN (sjtNat (n + 2)) (List.range (n + 2))) ∧
    2 ∣ (sjtNat (n + 2)).length
  | 0 => by
    refine ⟨rfl, by decide, ?_, ?_, ⟨1, rfl⟩⟩
    · intro l hl
      have : l ∈ [[0, 1], [1, 0]] := hl
      rcases List.mem_cons.mp this with rfl | h
      · exact List.Perm.refl _
      · rw [List.mem_singleton] at h; subst h; exact (List.Perm.swap 0 1 [] : [1, 0].Perm [0, 1])
    · intro l hl
      have h := List.mem_permutations'.mpr hl
      clear hl
      revert l
      decide
  | n + 1 => by
    obtain ⟨hc, hnd, honly, hall, hev⟩ := sjtN_props n
    have hS : ∀ s ∈ sjtNat (n + 2), s + 1 < n + 2 := fun s hs => by
      have := sjtNat_lt n s hs; omega
    have hg : ∀ v ∈ List.range (n + 2), v < n + 2 := fun v hv => List.mem_range.mp hv
    obtain ⟨h1, h2⟩ := stations_blocks (n + 2) (sjtNat (n + 2)) true (List.range (n + 2)) hS hg
    rw [show topN (n + 2) true = n + 2 from rfl, insertLast_range] at h1 h2
    have hsj : sjtNat (n + 1 + 2) = blocks (n + 2 + 1) true (sjtNat (n + 2)) := rfl
    obtain ⟨t, ht⟩ := hev
    rw [hc, ht, flipN_even, show topN (n + 2) true = n + 2 from rfl, insertLast_range] at h2
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hsj, h2]
    · rw [hsj, h1]; exact nodup_planN _ true _ hnd
    · intro l hl
      rw [hsj, h1, mem_planN] at hl
      obtain ⟨g, hgm, j, hj, rfl⟩ := hl
      exact insertLast_perm (honly g hgm) (by omega)
    · intro l hl
      obtain ⟨g, j, hgp, hj, rfl⟩ := perm_decompose hl
      rw [hsj, h1, mem_planN]
      exact ⟨g, hall g hgp, j, by omega, rfl⟩
    · rw [hsj, length_blocks _ (by omega), ht]
      exact ⟨(n + 3) * t, Nat.mul_left_comm _ _ _⟩


theorem sw_val_N {m : ℕ} (i : Fin m) (v : Fin (m + 1)) : (sw i v).val = swN i.val v.val := by
  rw [sw_val]; rfl

theorem stations_val {m : ℕ} (w : List (Fin m)) (l : List (Fin (m + 1))) :
    (stations w l).map (List.map Fin.val) = stationsN (w.map Fin.val) (l.map Fin.val) := by
  induction w generalizing l with
  | nil => rfl
  | cons i is ih =>
    simp only [stations, stationsN, List.map_cons, List.map_map]
    congr 1
    rw [ih]; congr 1
    simp only [negate, List.map_map]
    exact List.map_congr_left (fun v _ => sw_val_N i v)

theorem endpoint_val {m : ℕ} (w : List (Fin m)) (l : List (Fin (m + 1))) :
    (endpoint w l).map Fin.val = endpointN (w.map Fin.val) (l.map Fin.val) := by
  induction w generalizing l with
  | nil => rfl
  | cons i is ih =>
    simp only [endpoint, endpointN, List.map_cons]
    rw [ih]; congr 1
    simp only [negate, List.map_map]
    exact List.map_congr_left (fun v _ => sw_val_N i v)

theorem toFin_val {m : ℕ} (l : List ℕ) (h : ∀ k ∈ l, k < m) : (toFin m l).map Fin.val = l := by
  induction l with
  | nil => rfl
  | cons k ks ih =>
    have hk : k < m := h k (List.mem_cons_self)
    have hks : ∀ j ∈ ks, j < m := fun j hj => h j (List.mem_cons_of_mem _ hj)
    simp only [toFin, List.filterMap_cons, dif_pos hk, List.map_cons] at *
    rw [ih hks]

theorem sjt_val (m : ℕ) : (sjt (m + 1)).map Fin.val = sjtNat (m + 2) :=
  toFin_val _ (sjtNat_lt m)

theorem origin_val (m : ℕ) : (origin m).map Fin.val = List.range (m + 1) :=
  List.map_coe_finRange_eq_range

theorem map_val_inj {k : ℕ} : Function.Injective (List.map (Fin.val (n := k))) :=
  List.map_injective_iff.mpr (fun _ _ h => Fin.ext h)

theorem origin_nodup (m : ℕ) : (origin m).Nodup :=
  List.Nodup.of_map Fin.val (origin_val m ▸ nodupRange (m + 1))

/-- Anordnung auf der `Fin`-Ebene aus der `ℕ`-Ebene. -/
theorem perm_of_val {m : ℕ} {l : List (Fin (m + 1))} (h : (l.map Fin.val).Perm (List.range (m + 1))) :
    l.Perm (origin m) := by
  have hnd : l.Nodup := List.Nodup.of_map Fin.val (h.nodup_iff.mpr (nodupRange _))
  refine (List.perm_ext_iff_of_nodup hnd (origin_nodup m)).mpr ?_
  intro x
  have e : ∀ l' : List (Fin (m + 1)), x ∈ l' ↔ x.val ∈ l'.map Fin.val := fun l' => by
    constructor
    · intro hx; exact List.mem_map_of_mem hx
    · intro hx
      obtain ⟨y, hy, hyx⟩ := List.mem_map.mp hx
      exact (Fin.ext hyx) ▸ hy
  rw [e l, e (origin m), h.mem_iff, origin_val]

/-- **Z: die SJT-Folge ist für jede Wertzahl ab zwei ein Vollkreis.** -/
theorem sjt_full (m : ℕ) : IsFullCycle (sjt (m + 1)) := by
  obtain ⟨hc, hnd, honly, hall, _⟩ := sjtN_props m
  have hst : (stations (sjt (m + 1)) (origin (m + 1))).map (List.map Fin.val) =
      stationsN (sjtNat (m + 2)) (List.range (m + 2)) := by
    rw [stations_val, sjt_val, origin_val]
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply map_val_inj
    rw [endpoint_val, sjt_val, origin_val]; exact hc
  · exact List.Nodup.of_map _ (hst ▸ hnd)
  · intro l hl
    apply List.mem_permutations'.mpr
    apply perm_of_val
    exact honly _ (hst ▸ List.mem_map_of_mem hl)
  · intro l hl
    have hp := (List.mem_permutations'.mp hl).map Fin.val
    rw [origin_val] at hp
    have := hall _ hp
    rw [← hst] at this
    obtain ⟨l', hl', he⟩ := List.mem_map.mp this
    exact (map_val_inj he) ▸ hl'

/-- **F1: für jede Wertzahl ab zwei gibt es einen Vollkreis** — Günthers stille
Voraussetzung. -/
theorem full_exists (m : ℕ) : ∃ w : List (Fin (m + 1)), IsFullCycle w := ⟨_, sjt_full m⟩

/-- **F2: die Listen-Fassung von N-a, für jedes `m`**: jede Anordnung ist Endpunkt eines
Negatorworts. -/
theorem reach_all (m : ℕ) (a : List (Fin (m + 2))) (ha : a ∈ (origin (m + 1)).permutations') :
    ∃ v : List (Fin (m + 1)), endpoint v (origin (m + 1)) = a :=
  reach_of_full (sjt_full m) a ha

-- ============================================================
-- Wachen
-- ============================================================

/-- info: 'Reformulation.Proemial.NegationCycleSJT.mem_stations_endpoint' depends on axioms: [propext] -/
#guard_msgs in #print axioms mem_stations_endpoint

/-- info: 'Reformulation.Proemial.NegationCycleSJT.reach_of_full' depends on axioms: [propext] -/
#guard_msgs in #print axioms reach_of_full

/-- info: 'Reformulation.Proemial.NegationCycleSJT.no_full_at_one_value' depends on axioms: [propext] -/
#guard_msgs in #print axioms no_full_at_one_value

/-- info: 'Reformulation.Proemial.NegationCycleSJT.sjt1_full' depends on axioms: [propext] -/
#guard_msgs in #print axioms sjt1_full

/-- info: 'Reformulation.Proemial.NegationCycleSJT.sjt2_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms sjt2_eq

/-- info: 'Reformulation.Proemial.NegationCycleSJT.sjt2_full' depends on axioms: [propext] -/
#guard_msgs in #print axioms sjt2_full

/-- info: 'Reformulation.Proemial.NegationCycleSJT.sjt3_full' depends on axioms: [propext] -/
#guard_msgs in #print axioms sjt3_full

/-- info: 'Reformulation.Proemial.NegationCycleSJT.sjt3_mirror_kreis2' depends on axioms: [propext] -/
#guard_msgs in #print axioms sjt3_mirror_kreis2

/-- info: 'Reformulation.Proemial.NegationCycleSJT.stationsN_append' depends on axioms: [propext] -/
#guard_msgs in #print axioms stationsN_append

/-- info: 'Reformulation.Proemial.NegationCycleSJT.endpointN_append' depends on axioms: [propext] -/
#guard_msgs in #print axioms endpointN_append

/-- info: 'Reformulation.Proemial.NegationCycleSJT.swN_swN' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms swN_swN

/-- info: 'Reformulation.Proemial.NegationCycleSJT.sweep_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sweep_step

/-- info: 'Reformulation.Proemial.NegationCycleSJT.sweep_up_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sweep_up_step

/-- info: 'Reformulation.Proemial.NegationCycleSJT.shifted_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms shifted_step

/-- info: 'Reformulation.Proemial.NegationCycleSJT.top_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms top_step

/-- info: 'Reformulation.Proemial.NegationCycleSJT.sweep_down' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sweep_down

/-- info: 'Reformulation.Proemial.NegationCycleSJT.sweep_up' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sweep_up

/-- info: 'Reformulation.Proemial.NegationCycleSJT.range_succ_rev_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms range_succ_rev_map

/-- info: 'Reformulation.Proemial.NegationCycleSJT.block_true' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms block_true

/-- info: 'Reformulation.Proemial.NegationCycleSJT.block_false' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms block_false

/-- info: 'Reformulation.Proemial.NegationCycleSJT.swN_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms swN_lt

/-- info: 'Reformulation.Proemial.NegationCycleSJT.blocks_true_cons' depends on axioms: [propext] -/
#guard_msgs in #print axioms blocks_true_cons

/-- info: 'Reformulation.Proemial.NegationCycleSJT.blocks_false_cons' depends on axioms: [propext] -/
#guard_msgs in #print axioms blocks_false_cons

/-- info: 'Reformulation.Proemial.NegationCycleSJT.stations_blocks' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms stations_blocks

/-- info: 'Reformulation.Proemial.NegationCycleSJT.nodupRange' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms nodupRange

/-- info: 'Reformulation.Proemial.NegationCycleSJT.upN_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms upN_inj

/-- info: 'Reformulation.Proemial.NegationCycleSJT.insertLast_eq' does not depend on any axioms -/
#guard_msgs in #print axioms insertLast_eq

/-- info: 'Reformulation.Proemial.NegationCycleSJT.insertLast_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms insertLast_inj

/-- info: 'Reformulation.Proemial.NegationCycleSJT.mem_planN' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms mem_planN

/-- info: 'Reformulation.Proemial.NegationCycleSJT.insertLast_inj_right' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms insertLast_inj_right

/-- info: 'Reformulation.Proemial.NegationCycleSJT.nodup_planN' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms nodup_planN

/-- info: 'Reformulation.Proemial.NegationCycleSJT.mem_insertLast_range' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms mem_insertLast_range

/-- info: 'Reformulation.Proemial.NegationCycleSJT.nodup_insertLast_range' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms nodup_insertLast_range

/-- info: 'Reformulation.Proemial.NegationCycleSJT.insertLast_perm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms insertLast_perm

/-- info: 'Reformulation.Proemial.NegationCycleSJT.perm_decompose' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms perm_decompose

/-- info: 'Reformulation.Proemial.NegationCycleSJT.blocks_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms blocks_lt

/-- info: 'Reformulation.Proemial.NegationCycleSJT.sjtNat_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sjtNat_lt

/-- info: 'Reformulation.Proemial.NegationCycleSJT.length_blocks' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms length_blocks

/-- info: 'Reformulation.Proemial.NegationCycleSJT.flipN_even' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms flipN_even

/-- info: 'Reformulation.Proemial.NegationCycleSJT.insertLast_range' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms insertLast_range

/-- info: 'Reformulation.Proemial.NegationCycleSJT.sjtN_props' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sjtN_props

/-- info: 'Reformulation.Proemial.NegationCycleSJT.sw_val_N' does not depend on any axioms -/
#guard_msgs in #print axioms sw_val_N

/-- info: 'Reformulation.Proemial.NegationCycleSJT.stations_val' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms stations_val

/-- info: 'Reformulation.Proemial.NegationCycleSJT.endpoint_val' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms endpoint_val

/-- info: 'Reformulation.Proemial.NegationCycleSJT.toFin_val' does not depend on any axioms -/
#guard_msgs in #print axioms toFin_val

/-- info: 'Reformulation.Proemial.NegationCycleSJT.sjt_val' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sjt_val

/-- info: 'Reformulation.Proemial.NegationCycleSJT.origin_val' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms origin_val

/-- info: 'Reformulation.Proemial.NegationCycleSJT.map_val_inj' depends on axioms: [propext] -/
#guard_msgs in #print axioms map_val_inj

/-- info: 'Reformulation.Proemial.NegationCycleSJT.origin_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms origin_nodup

/-- info: 'Reformulation.Proemial.NegationCycleSJT.perm_of_val' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms perm_of_val

/-- info: 'Reformulation.Proemial.NegationCycleSJT.sjt_full' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sjt_full

/-- info: 'Reformulation.Proemial.NegationCycleSJT.full_exists' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms full_exists

/-- info: 'Reformulation.Proemial.NegationCycleSJT.reach_all' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms reach_all

end Reformulation.Proemial.NegationCycleSJT
