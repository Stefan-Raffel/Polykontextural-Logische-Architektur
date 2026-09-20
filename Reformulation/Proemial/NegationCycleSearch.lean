import Reformulation.Proemial.NegationCycleTable
import Mathlib.Data.Nat.Bitwise

/-!
# Proemial.NegationCycleSearch — die Vollzähligkeit: es gibt genau vierundvierzig (Stufe 2b)

**ERTRAG.** Gebaut auf Anordnung des Architekten vom 21. September 2026 nach
`KorpusRev2/Spec_NegationCycle_Stufe2.md` (Fassung 2), Stufe **2b**. Stufe 2a hat 44 Kreise
ausgeschrieben und gezeigt, dass es **mindestens** 44 sind; dieses Modul schliesst die
andere Hälfte: **es sind genau 44.** Damit steht Günthers Zahl als Satz —
*„Von diesen Kreisen gibt es, wenn man Drehsinn und Gegen-Drehsinn als einen Kreis rechnet,
44 Exemplare"* (1980, S. 20; IGN S. 41).

## Die Bauform, und warum sie diese ist

Der Gegenstand ist eine **Suche**: `searchB` durchläuft die 24 Wertfolgen von der
Ausgangsfolge aus, führt die besuchten in einer **Bitmaske** und baut die Negatorfolge beim
Rücklauf durch `cons`. Der Zustand ist ein Index und eine Zahl — nicht die Folge selbst.

**Das ist keine Bequemlichkeit, sondern die Bedingung der Machbarkeit** (gemessen,
`KorpusRev2/Sondierung_2b_Kodierung_Impl.md`): dieselbe Suche mit Präfixen als Listen bricht
im Kernel nach 3:42 min ab, mit den besuchten Stationen als Liste nach 2:45 — **mit der
Bitmaske läuft sie in 17,6 s.** Nicht der Suchbaum ist zu gross (50154 Knoten), sondern die
Kodierung des Zustands.

**Die Suche ist strukturell rekursiv über einen Zähler**, nicht wohlfundiert: eine
wohlfundierte Definition reduziert unter `decide` nicht (gemessen an `List.permutations`,
siehe `NegationCycle`).

## Die Sätze

* `search_complete` — **der Kern**: jede Folge, die von `cur` aus über unbesuchte, paarweise
  verschiedene Stationen zum Ausgang zurückkehrt, steht in der Ausgabe der Suche. Induktion
  über die Suchtiefe; die Invariante ist *„die Maske kodiert die besuchten Stationen"*, und
  der Schritt ist zweimal ein Bit-Lemma (`bit_set`, `bit_keep`) über `ix_inj`.
* `alleB_complete` — der Anschluss: **jeder Vollkreis steht in `alleB`**, über `full_length`
  und `IsFullCycle.closes`.
* `full_iff_mem` — **der Zielsatz in Iff-Form**: eine Negationsfolge ist genau dann ein
  Vollkreis, wenn sie in `alleB` steht.
* `alleB_perm_gerichtet` — **die Suche und die Tafel aus 2a sind dieselbe Liste**, bis auf
  Reihenfolge. Bewiesen, nicht entschieden: aus `alleB_complete`, `gerichtet_full` und der
  Gleichheit der Längen.
* `exactly_fortyfour` — **Günthers Zahl**: eine Folge ist genau dann ein Vollkreis, wenn sie
  in der Tafel der 44 steht oder ihre Umkehrung es tut. Mit `alleKreise_length` (= 44) und
  `alleKreise_no_reverse` ist das die Aussage „genau 44 Kreise, 88 Folgen".

## Der Brückenkopf — warum die Index-Kodierung keine Setzung ist

`tab` und `werte` sind **erzeugt** (Tiefensuche ausserhalb, Quelltext in der Sondierung),
aber sie sind nicht gesetzt: `nb_0`, `nb_1`, `nb_2` entscheiden über **alle 24 Wertfolgen**,
dass die Nachbartafel `negate` abbildet, und `ix_inj` entscheidet die Injektivität des
Index. Was die Suche für Nachbarschaft hält, ist damit gegen den Begriff geprüft.

## Was dieses Modul NICHT sagt

* **Nicht Tafel XX** (IGN S. 50). Die neun Kreiszahlen der kleineren Umfänge sind
  ausserhalb nachgerechnet und richtig, hier kein Satz — und dort wäre *modulo Rotation und
  Drehsinn* die richtige Konvention, anders als hier.
* **Nicht Günthers Unmöglichkeitssatz im Wortlaut.** Dass keine der 44 die Verteilung 8-8-8
  trägt, steht in `NegationCycleTable`; mit `exactly_fortyfour` folgt daraus jetzt zwar, dass
  **kein** Vollkreis sie trägt — aber als Satz ausgeschrieben ist das hier nicht.
* **Nicht, dass die 44 Folgen Günthers 44 sind.** Gleich ist die Zahl; über seine Liste sagt
  die Quelle nichts.
* **Kein `§20`-Anspruch, keine Ledger-Zeile.**

## Axiomprofil

Gemessen und am Dateiende gewacht. Die `decide`-Sätze tragen `[propext]`. **`search_complete`
und alles, was es konsumiert, trägt zusätzlich `Classical.choice`** — die Gattung ist
Taktikwahl, nicht Sache: die Hilfssätze sind sämtlich choice-frei, und die Heilung aus
Fallstrick 21 (`simp only` statt `simp`) greift hier **nicht**, gemessen. Der Posten ist
benannt und nicht geheilt.

**Bauzeit:** rund 40 s — die beiden Kernel-Auswertungen der Suche sind der Posten.
-/

namespace Reformulation.Proemial.NegationCycleSearch

open Reformulation.Proemial.NegationCycle Reformulation.Proemial.NegationCycleTable

-- ============================================================
-- Teil 1 — die Suche
-- ============================================================

/-- Nachbartafel der 24 Wertfolgen: Eintrag `i` ist die Wirkung des Negators `i`.
Erzeugt; durch `nb_0`, `nb_1`, `nb_2` gegen `negate` geprüft. -/
def tab : List (Nat × Nat × Nat) := [(6,2,1), (7,3,0), (8,0,4), (9,1,5), (10,5,2), (11,4,3), (0,12,7), (1,13,6), (2,14,10), (3,15,11), (4,16,8), (5,17,9), (14,6,18), (15,7,19), (12,8,20), (13,9,21), (17,10,22), (16,11,23), (20,19,12), (21,18,13), (18,22,14), (19,23,15), (23,20,16), (22,21,17)]

def nb (v : Nat) : Nat × Nat × Nat := tab.getD v (0, 0, 0)

/-- Die Suche: Zustand ist (Index der Wertfolge, Bitmaske der besuchten); die Negatorfolge
entsteht beim Rücklauf. Strukturell rekursiv über den Zähler. -/
def searchB : ℕ → Nat → Nat → List (List (Fin 3))
  | 0, v, _ =>
      let (a, b, c) := nb v
      (if a = 0 then [[0]] else []) ++ (if b = 0 then [[1]] else []) ++
        (if c = 0 then [[2]] else [])
  | n + 1, v, m =>
      let (a, b, c) := nb v
      (if m.testBit a then [] else (searchB n a (m ||| (1 <<< a))).map (0 :: ·)) ++
      (if m.testBit b then [] else (searchB n b (m ||| (1 <<< b))).map (1 :: ·)) ++
      (if m.testBit c then [] else (searchB n c (m ||| (1 <<< c))).map (2 :: ·))

/-- Die Ausgabe: alle Vollkreise vom Ausgang aus. -/
def alleB : List (List (Fin 3)) := searchB 23 0 1

-- ============================================================
-- Teil 2 — der Brückenkopf
-- ============================================================

/-- Die 24 Wertfolgen in der Reihenfolge, die `tab` indiziert. -/
def werte : List (List (Fin 4)) := [[0,1,2,3], [0,1,3,2], [0,2,1,3], [0,2,3,1], [0,3,1,2], [0,3,2,1], [1,0,2,3], [1,0,3,2], [1,2,0,3], [1,2,3,0], [1,3,0,2], [1,3,2,0], [2,0,1,3], [2,0,3,1], [2,1,0,3], [2,1,3,0], [2,3,0,1], [2,3,1,0], [3,0,1,2], [3,0,2,1], [3,1,0,2], [3,1,2,0], [3,2,0,1], [3,2,1,0]]

def ix (l : List (Fin 4)) : Nat := werte.idxOf l

theorem origin_mem : origin 3 ∈ werte := by decide
theorem ix_origin : ix (origin 3) = 0 := by decide
theorem nb_0 : ∀ l ∈ werte, (nb (ix l)).1 = ix (negate 0 l) := by decide
theorem nb_1 : ∀ l ∈ werte, (nb (ix l)).2.1 = ix (negate 1 l) := by decide
theorem nb_2 : ∀ l ∈ werte, (nb (ix l)).2.2 = ix (negate 2 l) := by decide
theorem negate_mem : ∀ l ∈ werte, ∀ i : Fin 3, negate i l ∈ werte := by decide
theorem ix_inj : ∀ l ∈ werte, ∀ l' ∈ werte, ix l = ix l' → l = l' := by decide

theorem bit_set (m a : Nat) : (m ||| (1 <<< a)).testBit a = true := by
  simp [Nat.testBit_or, Nat.testBit_shiftLeft]

theorem bit_keep (m a b : Nat) (h : a ≠ b) : (m ||| (1 <<< a)).testBit b = m.testBit b := by
  rw [Nat.testBit_or, Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow, decide_eq_false h,
    Bool.or_false]

theorem testBit_one (j : Nat) (h : j ≠ 0) : (1 : Nat).testBit j = false := by
  rw [show (1 : Nat) = 2 ^ 0 from rfl, Nat.testBit_two_pow, decide_eq_false]
  exact fun he => h he.symm

theorem stations_mem_werte : ∀ (seq : List (Fin 3)) (cur : List (Fin 4)), cur ∈ werte →
    ∀ l ∈ stations seq cur, l ∈ werte := by
  intro seq
  induction seq with
  | nil => intro cur _ l hl; simp [stations] at hl
  | cons i is ih =>
    intro cur hcur l hl
    rcases List.mem_cons.mp hl with rfl | h
    · exact hcur
    · exact ih _ (negate_mem cur hcur i) l h

-- ============================================================
-- Teil 3 — der Vollständigkeitssatz
-- ============================================================

/-- **Der Vollständigkeitssatz der Suche**, in der Form, die die Induktion trägt. -/
theorem search_complete : ∀ (n : ℕ) (cur : List (Fin 4)) (m : Nat) (seq : List (Fin 3)),
    cur ∈ werte → seq.length = n + 1 →
    (∀ l ∈ (stations seq cur).tail, m.testBit (ix l) = false) →
    ((stations seq cur).tail).Nodup →
    endpoint seq cur = origin 3 →
    seq ∈ searchB n (ix cur) m := by
  intro n
  induction n with
  | zero =>
    intro cur m seq hcur hlen _ _ hend
    cases seq with
    | nil => simp at hlen
    | cons i rest =>
      have hr : rest = [] := by
        cases rest with
        | nil => rfl
        | cons _ _ => simp at hlen
      subst hr
      have h : ix (negate i cur) = 0 := by
        rw [show negate i cur = origin 3 from hend, ix_origin]
      obtain ⟨v, hv⟩ : ∃ v, v = i.val := ⟨i.val, rfl⟩
      match i, hv with
      | 0, _ => simp only [searchB, nb_0 cur hcur, h]; simp
      | 1, _ => simp only [searchB, nb_1 cur hcur, h]; simp
      | 2, _ => simp only [searchB, nb_2 cur hcur, h]; simp
  | succ n ih =>
    intro cur m seq hcur hlen hmask hnd hend
    cases seq with
    | nil => simp at hlen
    | cons i rest =>
      have hrl : rest.length = n + 1 := by simpa using hlen
      set cur' := negate i cur with hcur'
      have hcm : cur' ∈ werte := negate_mem cur hcur i
      have hrne : rest ≠ [] := by intro h; simp [h] at hrl
      have htail : stations rest cur' = cur' :: (stations rest cur').tail := by
        cases rest with
        | nil => exact absurd rfl hrne
        | cons j js => rfl
      have hst : (stations (i :: rest) cur).tail = stations rest cur' := rfl
      have h0 : m.testBit (ix cur') = false := by
        apply hmask; rw [hst, htail]; exact List.mem_cons_self
      have hnd' : (cur' :: (stations rest cur').tail).Nodup := by
        rw [← htail, ← hst]; exact hnd
      have hmask' : ∀ l ∈ (stations rest cur').tail,
          (m ||| (1 <<< ix cur')).testBit (ix l) = false := by
        intro l hl
        have hlw : l ∈ werte := by
          apply stations_mem_werte rest cur' hcm
          rw [htail]; exact List.mem_cons_of_mem _ hl
        have hne : ix cur' ≠ ix l := by
          intro he
          exact (List.nodup_cons.mp hnd').1 ((ix_inj cur' hcm l hlw he) ▸ hl)
        rw [bit_keep m _ _ hne]
        apply hmask; rw [hst, htail]; exact List.mem_cons_of_mem _ hl
      have hrec : rest ∈ searchB n (ix cur') (m ||| (1 <<< ix cur')) :=
        ih cur' _ rest hcm hrl hmask' (List.nodup_cons.mp hnd').2 hend
      obtain ⟨v, hv⟩ : ∃ v, v = i.val := ⟨i.val, rfl⟩
      match i, hv with
      | 0, _ =>
        simp only [searchB, nb_0 cur hcur, ← hcur', h0, Bool.false_eq_true, if_false,
          List.mem_append, List.mem_map]
        exact Or.inl (Or.inl ⟨rest, hrec, rfl⟩)
      | 1, _ =>
        simp only [searchB, nb_1 cur hcur, ← hcur', h0, Bool.false_eq_true, if_false,
          List.mem_append, List.mem_map]
        exact Or.inl (Or.inr ⟨rest, hrec, rfl⟩)
      | 2, _ =>
        simp only [searchB, nb_2 cur hcur, ← hcur', h0, Bool.false_eq_true, if_false,
          List.mem_append, List.mem_map]
        exact Or.inr ⟨rest, hrec, rfl⟩




/-- **Der Zielsatz von Stufe 2b**: jeder Vollkreis steht in der Ausgabe der Suche. -/
theorem alleB_complete : ∀ seq, IsFullCycle seq → seq ∈ alleB := by
  intro seq h
  have hlen : seq.length = 24 := by
    have := full_length h
    simpa using this
  have hst : stations seq (origin 3) = origin 3 :: (stations seq (origin 3)).tail := by
    cases seq with
    | nil => simp at hlen
    | cons j js => rfl
  have hnd : (stations seq (origin 3)).Nodup := h.nodup
  have hmask : ∀ l ∈ (stations seq (origin 3)).tail, (1 : Nat).testBit (ix l) = false := by
    intro l hl
    have hlw : l ∈ werte := by
      apply stations_mem_werte seq (origin 3) origin_mem
      rw [hst]; exact List.mem_cons_of_mem _ hl
    have hne : l ≠ origin 3 := by
      intro he; subst he
      exact (List.nodup_cons.mp (hst ▸ hnd)).1 hl
    refine testBit_one _ fun h0 => hne ?_
    exact ix_inj l hlw (origin 3) origin_mem (by rw [h0, ix_origin])
  have : seq ∈ searchB 23 (ix (origin 3)) 1 :=
    search_complete 23 (origin 3) 1 seq origin_mem hlen hmask
      (List.nodup_cons.mp (hst ▸ hnd)).2 h.closes
  simpa [alleB, ix_origin] using this

-- ============================================================
-- Teil 4 — die Vollzähligkeit
-- ============================================================

set_option maxRecDepth 4000000 in
/-- Die Suche liefert 88 Folgen. -/
theorem alleB_card : alleB.length = 88 := by decide +kernel

set_option maxRecDepth 4000000 in
/-- Keine zweimal. -/
theorem alleB_nodup : alleB.Nodup := by decide +kernel

/-- **Die Suche und die Tafel aus 2a sind dieselbe Liste, bis auf die Reihenfolge.**
Bewiesen, nicht entschieden. -/
theorem alleB_perm_gerichtet : gerichtet.Perm alleB := by
  have hsub : gerichtet ⊆ alleB := fun s hs => alleB_complete s (gerichtet_full s hs)
  have hsp : gerichtet.Subperm alleB := List.subperm_of_subset gerichtet_nodup hsub
  exact hsp.perm_of_length_le (by rw [alleB_card, gerichtet_length])

/-- Jede gefundene Folge ist ein Vollkreis — aus der Tafel, ohne neue Rechnung. -/
theorem alleB_full : ∀ s ∈ alleB, IsFullCycle s := fun s hs =>
  gerichtet_full s (alleB_perm_gerichtet.mem_iff.mpr hs)

/-- **Der Zielsatz in Iff-Form.** -/
theorem full_iff_mem (seq : List (Fin 3)) : IsFullCycle seq ↔ seq ∈ alleB :=
  ⟨alleB_complete seq, fun h => alleB_full seq h⟩

/-- **Günthers Zahl.** Eine Negationsfolge ist genau dann ein Vollkreis, wenn sie in der
Tafel der 44 steht oder ihre Umkehrung es tut. Mit `alleKreise_length` (44) und
`alleKreise_no_reverse` ist das die Aussage: **genau 44 Kreise, 88 Folgen.** -/
theorem exactly_fortyfour (seq : List (Fin 3)) :
    IsFullCycle seq ↔ (seq ∈ alleKreise ∨ seq.reverse ∈ alleKreise) := by
  rw [full_iff_mem, ← alleB_perm_gerichtet.mem_iff]
  constructor
  · intro h
    rcases List.mem_append.mp h with h | h
    · exact Or.inl h
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp h
      exact Or.inr (by rwa [List.reverse_reverse])
  · rintro (h | h)
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (List.mem_map.mpr ⟨seq.reverse, h, List.reverse_reverse _⟩)

-- ============================================================
-- Wachen
-- ============================================================

/-- info: 'Reformulation.Proemial.NegationCycleSearch.origin_mem' depends on axioms: [propext] -/
#guard_msgs in #print axioms origin_mem

/-- info: 'Reformulation.Proemial.NegationCycleSearch.ix_origin' depends on axioms: [propext] -/
#guard_msgs in #print axioms ix_origin

/-- info: 'Reformulation.Proemial.NegationCycleSearch.nb_0' depends on axioms: [propext] -/
#guard_msgs in #print axioms nb_0

/-- info: 'Reformulation.Proemial.NegationCycleSearch.nb_1' depends on axioms: [propext] -/
#guard_msgs in #print axioms nb_1

/-- info: 'Reformulation.Proemial.NegationCycleSearch.nb_2' depends on axioms: [propext] -/
#guard_msgs in #print axioms nb_2

/-- info: 'Reformulation.Proemial.NegationCycleSearch.negate_mem' depends on axioms: [propext] -/
#guard_msgs in #print axioms negate_mem

/-- info: 'Reformulation.Proemial.NegationCycleSearch.ix_inj' depends on axioms: [propext] -/
#guard_msgs in #print axioms ix_inj

/-- info: 'Reformulation.Proemial.NegationCycleSearch.bit_set' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms bit_set

/-- info: 'Reformulation.Proemial.NegationCycleSearch.bit_keep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms bit_keep

/-- info: 'Reformulation.Proemial.NegationCycleSearch.testBit_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms testBit_one

/-- info: 'Reformulation.Proemial.NegationCycleSearch.stations_mem_werte' depends on axioms: [propext] -/
#guard_msgs in #print axioms stations_mem_werte

/-- info: 'Reformulation.Proemial.NegationCycleSearch.search_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms search_complete

/-- info: 'Reformulation.Proemial.NegationCycleSearch.alleB_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms alleB_complete

/-- info: 'Reformulation.Proemial.NegationCycleSearch.alleB_card' depends on axioms: [propext] -/
#guard_msgs in #print axioms alleB_card

/-- info: 'Reformulation.Proemial.NegationCycleSearch.alleB_nodup' depends on axioms: [propext] -/
#guard_msgs in #print axioms alleB_nodup

/-- info: 'Reformulation.Proemial.NegationCycleSearch.alleB_perm_gerichtet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms alleB_perm_gerichtet

/-- info: 'Reformulation.Proemial.NegationCycleSearch.alleB_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms alleB_full

/-- info: 'Reformulation.Proemial.NegationCycleSearch.full_iff_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms full_iff_mem

/-- info: 'Reformulation.Proemial.NegationCycleSearch.exactly_fortyfour' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms exactly_fortyfour

end Reformulation.Proemial.NegationCycleSearch
