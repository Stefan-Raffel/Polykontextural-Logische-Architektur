import Reformulation.Proemial.LocalOpInseparability
import Reformulation.Kenogram.Morphogram
import Mathlib.Data.List.Dedup

/-!
# Proemial.PatternInvariance — die Kenogramme als Invarianten der Wert-Permutationen

**Der Zielsatz.** Eine Menge von Tupeln `Fin n → Fin m` ist **genau dann** unter allen
Permutationen der Werte invariant, wenn sie mit jedem Tupel dessen ganze **Musterklasse**
enthält (`pattern_characterization`). Das sagt, **woran** das Kenogramm auf der Wertseite
zu erkennen ist: es ist, was die Wert-Permutationen invariant lassen.

**Die Naht.** Diese Datei verbindet den **Klon-Strang** (`Preserves` aus
`Proemial.LocalOpInseparability`) mit dem **kenogrammatischen Grund** (`canonicalize`,
`relabel` aus `Kenogram`). Die zwei Stränge berührten sich vorher nicht. Sie ist damit die
**vierte** Datei mit dieser Naht; `Proemial.RelabelInvariance` ist ihre unmittelbare
Präzedenz — dieselben zwei Seiten, dieselbe Importrichtung.

## Was diese Datei NICHT beansprucht

**Sie löst `A20-1` nicht ein.** Der Anspruch verlangt zweierlei: *(a)* über Kenogrammen
und *(b)* **Stelligkeit zwei**. Diese Datei trifft (a) und nicht (b) — eine Stelligkeit
kommt in keinem ihrer Sätze vor. Sie legt die Brücke zu A20-1 und geht sie nicht.

**Ebenso nicht beansprucht:** `A20-2`, `A20-4`, ein Träger für `§20`, eine Ledger-Zeile.
Der Ledger hält die Trägerspalte der Paragraphen; diese Datei trägt keinen. **Die vierte
Grenze des Papiers — *eine Kopplung ist kein Grund* — bleibt unberührt.**

**Und sie sagt nichts über Günther.** Die Aussage ist ein Satz über Musterklassen; dass
Kenogramme Musterklassen *sind*, ist die Definitionswahl dieses Baus
(`rgs_equiv_partition`, `canonicalize_eq_iff`) und keine Quellenaussage.

**Vermerk (1962).** Günther trennt in *Cybernetic Ontology and Transjunctional Operations*
selbst zwei Ebenen: Der Reflektor ℜ operiert auf **Morphogrammen** („If "ℜ" operates on a
morphogram, it is placed before it", S. 34), die Negationen η auf **Werten** („the operator of
reflection will always be written in index form after "η"", S. 34), und ℜ ist „completely
indifferent to the actual value-occupancy" (S. 37). Dieselbe Unterscheidung macht diese Datei
zwischen den Wertpermutationen und den unter ihnen invarianten Musterklassen. *ZUORDNUNG, nah*
— ein Vermerk, kein Satz über Günther.

## Axiomprofil — keine Choice-Freiheit, und das ist gemessen

Der Strang trägt `Classical.choice` schon in der **gebauten** Richtung: `relabel_isRGS`
und `canonicalize_eq_iff` tragen es, und `relabel_map_of_injective` erbt es. Dazu tragen
die zwei `dedup`-Fallunterscheidungen (`List.dedup_cons_of_mem`, `_of_notMem`) es
ebenfalls. **Choice ist hier keine Auswahlfrage**, sondern die Lage des Trägers; nur
`preserves_unary` ist axiomfrei.

**Warum ein `decide`-Satz Choice trägt:** `orbit_witness_three` entscheidet über
`Function.Bijective` und zieht es über die `Decidable`-Instanz, die auf `Fintype` ruht
(Fallstrick-Familie `Fin.fintype`). Wer „`decide`" liest und „axiomfrei" erwartet, findet
sonst einen Widerspruch, der keiner ist.

## Zwei Sätze, die einander ähneln, und ihr Unterschied

`canonicalize_perm` sagt: **Permutationen** lassen das Muster fest, über **Tupel**.
`Kenogram`s `relabel_map_of_injective` (S1, in `Proemial.RelabelInvariance`) sagt:
**injektive** Abbildungen lassen es fest, über **Listen**. Das ist nicht dieselbe Aussage,
aber dieselbe Sache in zwei Trägern — eine Permutation ist injektiv, und `canonicalize`
ist `relabel ∘ List.ofFn`. **Der Weg über `List.ofFn` wird hier nicht gesucht:** der
direkte Beweis über `canonicalize_eq_iff` ist kürzer als die Übersetzung, und der
Unterschied steht in diesem Absatz statt in einem Umweg.

## Die Muster-Form trägt den Beweis, nicht `SamePattern`

`Pat l r` (`∀ i j, l[i]? = l[j]? ↔ r[i]? = r[j]?`) überträgt sich durch
Indexverschiebung auf **Teillisten** — genau das macht die Induktion in
`dedup_idxOf_congr` möglich. `SamePattern` ist die Fassung für die *Aussage*, `Pat` die
für den *Beweis*; `Kenogram.Morphogram.samePattern_iff_pattern` ist die Brücke.

## Aggregat-Reife

Drei Importe: `Proemial.LocalOpInseparability`, `Kenogram.Morphogram`,
`Mathlib.Data.List.Dedup`. Kein Import einer Sonde. Keine Setzung, keine Definition mit
Ledger-Anspruch; `viaLists` und `marksFull` sind Werkzeug.
-/

namespace Reformulation.Proemial.PatternInvariance

open Reformulation.Kenogram
open Reformulation.Proemial.LocalOpInseparability (Preserves)

-- ============================================================
-- §I — die Muster-Form und ihre Induktion
-- ============================================================

section Muster
variable {α β : Type} [DecidableEq α] [DecidableEq β]

/-- Die Muster-Hypothese in der Form, die sich auf Teillisten uebertraegt. -/
abbrev Pat (l : List α) (r : List β) : Prop := ∀ i j : ℕ, l[i]? = l[j]? ↔ r[i]? = r[j]?

omit [DecidableEq α] [DecidableEq β] in
/-- Aus dem Muster: gleiche Stellen tragen korrespondierende Gleichheiten. -/
theorem eq_transfer {l : List α} {r : List β} (h : Pat l r) {i j : ℕ}
    (hi : i < l.length) (hj : j < l.length) (hir : i < r.length) (hjr : j < r.length)
    (he : l[i] = l[j]) : r[i] = r[j] := by
  have h1 : l[i]? = l[j]? := by
    rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj, he]
  have h2 := (h i j).mp h1
  rw [List.getElem?_eq_getElem hir, List.getElem?_eq_getElem hjr] at h2
  exact Option.some.inj h2

omit [DecidableEq α] [DecidableEq β] in
/-- Der Kopf wiederholt sich auf der einen Seite genau dann, wenn er es auf der
anderen tut. -/
theorem head_mem_transfer {x : α} {l' : List α} {y : β} {r' : List β}
    (hlen : l'.length = r'.length) (hpat : Pat (x :: l') (y :: r')) :
    x ∈ l' ↔ y ∈ r' := by
  constructor
  · intro hx
    obtain ⟨j, hj, hjx⟩ := List.getElem_of_mem hx
    have : r'[j]'(by omega) = y := by
      have := eq_transfer (l := x :: l') (r := y :: r') hpat
        (i := j + 1) (j := 0) (by simpa using hj) (by simp)
        (by simpa [hlen] using hj) (by simp) (by simpa using hjx)
      simpa using this
    exact this ▸ List.getElem_mem (by omega)
  · intro hy
    obtain ⟨j, hj, hjy⟩ := List.getElem_of_mem hy
    have : l'[j]'(by omega) = x := by
      have := eq_transfer (l := y :: r') (r := x :: l') (fun a b => (hpat a b).symm)
        (i := j + 1) (j := 0) (by simpa using hj) (by simp)
        (by simpa [← hlen] using hj) (by simp) (by simpa using hjy)
      simpa using this
    exact this ▸ List.getElem_mem (by omega)

/-- **Das uebersehene fuenfte Stueck:** die Markenzahl ist musterbestimmt. -/
theorem dedup_length_congr : ∀ (l : List α) (r : List β), l.length = r.length → Pat l r →
    l.dedup.length = r.dedup.length := by
  intro l
  induction l with
  | nil => intro r hlen _; cases r with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons x l' ih =>
    intro r hlen hpat
    match r with
    | [] => simp at hlen
    | y :: r' =>
      have hlen' : l'.length = r'.length := by simpa using hlen
      have hpat' : Pat l' r' := by intro a b; simpa using hpat (a + 1) (b + 1)
      have hmem := head_mem_transfer hlen' hpat
      by_cases hx : x ∈ l'
      · rw [List.dedup_cons_of_mem hx, List.dedup_cons_of_mem (hmem.mp hx)]
        exact ih r' hlen' hpat'
      · have hy : y ∉ r' := fun h => hx (hmem.mpr h)
        rw [List.dedup_cons_of_notMem hx, List.dedup_cons_of_notMem hy]
        simpa using ih r' hlen' hpat'

/-- **Der Kern.**  Gleiches Muster ⇒ korrespondierende Markenpositionen. -/
theorem dedup_idxOf_congr : ∀ (l : List α) (r : List β), l.length = r.length → Pat l r →
    ∀ i : ℕ, ∀ (hl : i < l.length) (hr : i < r.length),
      l.dedup.idxOf l[i] = r.dedup.idxOf r[i] := by
  intro l
  induction l with
  | nil => intro r _ _ i hl; exact absurd hl (by simp)
  | cons x l' ih =>
    intro r hlen hpat i hl hr
    match r with
    | [] => exact absurd hr (by simp)
    | y :: r' =>
      have hlen' : l'.length = r'.length := by simpa using hlen
      have hpat' : Pat l' r' := by
        intro a b
        have := hpat (a + 1) (b + 1)
        simpa using this
      have hmem := head_mem_transfer hlen' hpat
      by_cases hx : x ∈ l'
      · -- beide Koepfe sind Wiederholungen:  dedup faellt weg
        have hy : y ∈ r' := hmem.mp hx
        rw [List.dedup_cons_of_mem hx, List.dedup_cons_of_mem hy]
        match i with
        | 0 =>
          -- der Kopf:  ueber eine Stelle im Rest, an der er wieder auftritt
          obtain ⟨j, hj, hjx⟩ := List.getElem_of_mem hx
          have hjy : r'[j] = y := by
            have := eq_transfer (l := x :: l') (r := y :: r') hpat
              (i := j + 1) (j := 0) (by simpa using hj) (by simp)
              (by simpa [hlen'] using hj) (by simp) (by simpa using hjx)
            simpa using this
          have := ih r' hlen' hpat' j hj (by omega)
          simpa [hjx, hjy] using this
        | Nat.succ i' =>
          have := ih r' hlen' hpat' i' (by simpa using hl) (by simpa using hr)
          simpa using this
      · -- beide Koepfe sind neu
        have hy : y ∉ r' := fun h => hx (hmem.mpr h)
        rw [List.dedup_cons_of_notMem hx, List.dedup_cons_of_notMem hy]
        match i with
        | 0 => simp
        | Nat.succ i' =>
          have hl' : i' < l'.length := by simpa using hl
          have hr' : i' < r'.length := by simpa using hr
          have hne : l'[i'] ≠ x := fun h => hx (h ▸ List.getElem_mem hl')
          have hne' : r'[i'] ≠ y := fun h => hy (h ▸ List.getElem_mem hr')
          simp only [List.getElem_cons_succ]
          rw [List.idxOf_cons_ne _ (Ne.symm hne), List.idxOf_cons_ne _ (Ne.symm hne')]
          simpa using ih r' hlen' hpat' i' hl' hr'


end Muster

-- ============================================================
-- (3) die Bijektion aus zwei Listen
-- ============================================================

section Bij
variable {m : ℕ}

def viaLists (A B : List (Fin m)) (v : Fin m) : Fin m := B.getD (A.idxOf v) v

theorem viaLists_inv {A B : List (Fin m)} (hB : B.Nodup)
    (hAall : ∀ v : Fin m, v ∈ A) (hlen : A.length = B.length) (v : Fin m) :
    viaLists B A (viaLists A B v) = v := by
  have hiA : A.idxOf v < A.length := List.idxOf_lt_length_iff.mpr (hAall v)
  have hiB : A.idxOf v < B.length := hlen ▸ hiA
  have h1 : viaLists A B v = B[A.idxOf v] := by
    rw [viaLists, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hiB]; rfl
  rw [h1, viaLists, List.Nodup.idxOf_getElem hB]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hiA, Option.getD_some,
    List.getElem_idxOf hiA]

-- ============================================================
-- (6) DAS ZUSAMMENSETZEN — die vollstaendige Markenliste
-- ============================================================

/-- Erst die Marken in `dedup`-Reihenfolge, dann das Komplement. -/
def marksFull (l : List (Fin m)) : List (Fin m) :=
  l.dedup ++ (List.finRange m).filter (fun v => !(decide (v ∈ l)))

theorem marksFull_nodup (l : List (Fin m)) : (marksFull l).Nodup := by
  refine List.Nodup.append (List.nodup_dedup l)
    (List.Nodup.filter _ (List.nodup_finRange m)) ?_
  intro x hx hx'
  have h1 : x ∈ l := List.mem_dedup.mp hx
  have h2 : x ∉ l := by
    have := List.of_mem_filter hx'
    simpa using this
  exact h2 h1

theorem marksFull_mem (l : List (Fin m)) (v : Fin m) : v ∈ marksFull l := by
  rw [marksFull, List.mem_append]
  by_cases h : v ∈ l
  · exact Or.inl (List.mem_dedup.mpr h)
  · refine Or.inr (List.mem_filter.mpr ⟨List.mem_finRange v, ?_⟩)
    simpa using h

theorem marksFull_length (l : List (Fin m)) : (marksFull l).length = m := by
  have hnd := marksFull_nodup l
  have huniv : (marksFull l).toFinset = Finset.univ :=
    Finset.eq_univ_iff_forall.mpr fun v => List.mem_toFinset.mpr (marksFull_mem l v)
  have hcard := List.toFinset_card_of_nodup hnd
  rw [huniv, Finset.card_univ, Fintype.card_fin] at hcard
  exact hcard.symm

theorem dedup_prefix_idxOf {l : List (Fin m)} {v : Fin m} (h : v ∈ l) :
    (marksFull l).idxOf v = l.dedup.idxOf v :=
  List.idxOf_append_of_mem (List.mem_dedup.mpr h)

/-- **Die Schluesselgleichung.**  Der Tausch, den die zwei Markenlisten stiften,
traegt `l[i]` auf `r[i]`. -/
theorem viaLists_marks {l r : List (Fin m)} (hlen : l.length = r.length) (hpat : Pat l r)
    {i : ℕ} (hl : i < l.length) (hr : i < r.length) :
    viaLists (marksFull l) (marksFull r) l[i] = r[i] := by
  have hmem_r : r[i] ∈ r := List.getElem_mem hr
  have hk : (marksFull l).idxOf l[i] = l.dedup.idxOf l[i] :=
    dedup_prefix_idxOf (List.getElem_mem hl)
  have hkern : l.dedup.idxOf l[i] = r.dedup.idxOf r[i] :=
    dedup_idxOf_congr l r hlen hpat i hl hr
  have hklt : r.dedup.idxOf r[i] < r.dedup.length :=
    List.idxOf_lt_length_iff.mpr (List.mem_dedup.mpr hmem_r)
  rw [viaLists, hk, hkern, marksFull, List.getD_eq_getElem?_getD,
    List.getElem?_append_left hklt, List.getElem?_eq_getElem hklt, Option.getD_some,
    List.getElem_idxOf hklt]

-- ============================================================
-- (0) der Uebergang Tupel → Liste
-- ============================================================

theorem pat_ofFn {n : ℕ} {α β : Type} [DecidableEq α] [DecidableEq β]
    (a : Fin n → α) (b : Fin n → β) (h : canonicalize a = canonicalize b) :
    Pat (List.ofFn a) (List.ofFn b) :=
  ofFn_getElem?_pattern a b ((canonicalize_eq_iff a b).mp h)

-- ============================================================
-- L — die BAHN-AUSSAGE
-- ============================================================

/-- **L.**  Gleiches Muster gibt eine Permutation der Werte, die das eine Tupel
ins andere traegt. -/
theorem orbit_of_same_pattern {n : ℕ} (a b : Fin n → Fin m)
    (h : canonicalize a = canonicalize b) :
    ∃ σ : Equiv.Perm (Fin m), b = fun i => σ (a i) := by
  have hlenAB : (marksFull (List.ofFn a)).length = (marksFull (List.ofFn b)).length := by
    rw [marksFull_length, marksFull_length]
  refine ⟨⟨viaLists (marksFull (List.ofFn a)) (marksFull (List.ofFn b)),
           viaLists (marksFull (List.ofFn b)) (marksFull (List.ofFn a)),
           fun v => viaLists_inv (marksFull_nodup _) (marksFull_mem _) hlenAB v,
           fun v => viaLists_inv (marksFull_nodup _) (marksFull_mem _) hlenAB.symm v⟩, ?_⟩
  funext i
  have hl : (i : ℕ) < (List.ofFn a).length := by simp
  have hr : (i : ℕ) < (List.ofFn b).length := by simp
  have key := viaLists_marks (l := List.ofFn a) (r := List.ofFn b)
    (by simp) (pat_ofFn a b h) hl hr
  simpa using key.symm

-- ============================================================
-- Die Erhaltungsseite und der ZIELSATZ
-- ============================================================

/-- Die binaere Erhaltung des Bestandes enthaelt den unaeren Fall woertlich —
auch fuer leeres `R`.  Kein zweiter Erhaltungsbegriff. -/
theorem preserves_unary {ι : Type} (R : Set (ι → Fin m)) (σ : Fin m → Fin m) :
    Preserves R (fun a _ => σ a) ↔ ∀ a ∈ R, (fun i => σ (a i)) ∈ R := by
  constructor
  · intro h a ha; exact h a ha a ha
  · intro h a ha b _; exact h a ha

/-- Eine Permutation der Werte laesst das Muster fest. -/
theorem canonicalize_perm {n : ℕ} (σ : Equiv.Perm (Fin m)) (a : Fin n → Fin m) :
    canonicalize (fun i => σ (a i)) = canonicalize a := by
  rw [canonicalize_eq_iff]
  exact fun i j => ⟨fun h => σ.injective h, fun h => congrArg σ h⟩

/-- **Z — der Zielsatz.**  `R` ist genau dann unter allen Wert-Permutationen
invariant, wenn `R` mit jedem Tupel dessen ganze Musterklasse enthaelt. -/
theorem pattern_characterization {n : ℕ} (R : Set (Fin n → Fin m)) :
    (∀ σ : Equiv.Perm (Fin m), Preserves R (fun a _ => σ a)) ↔
      (∀ a ∈ R, ∀ b : Fin n → Fin m, canonicalize a = canonicalize b → b ∈ R) := by
  constructor
  · intro h a ha b hab
    obtain ⟨σ, rfl⟩ := orbit_of_same_pattern a b hab
    exact h σ a ha a ha
  · intro h σ a ha b _
    exact h a ha _ (canonicalize_perm σ a).symm

end Bij



-- ============================================================
-- §VI — Eichwerte
-- ============================================================

/-- Der Zeuge, vollständig über alle `27 × 27` Paare: gleiches Muster gibt eine
Bijektion, die das eine Tupel ins andere trägt. **Zur Choice-Quelle siehe den
Dateikopf.** -/
theorem orbit_witness_three : ∀ a b : Fin 3 → Fin 3,
    relabel (List.ofFn a) = relabel (List.ofFn b) →
      ∃ f : Fin 3 → Fin 3, Function.Bijective f ∧ b = f ∘ a := by decide

/-- **Die Gegenprobe.** Ohne `Bijective` wäre der Zeuge keine Auskunft: es gibt `a`, `b`
mit `b = f ∘ a` und **verschiedenem** Muster. Sie fällt, wenn jemand die
Bijektivität aus der Bahn-Aussage streicht. -/
theorem orbit_needs_bijective : ∃ a b : Fin 3 → Fin 3,
    (∃ f : Fin 3 → Fin 3, b = f ∘ a) ∧ relabel (List.ofFn a) ≠ relabel (List.ofFn b) := by
  decide

-- ============================================================
-- §VII — Statement-Pins
-- ============================================================

-- STATEMENT-PIN
example {m n : ℕ} (R : Set (Fin n → Fin m)) :
    (∀ σ : Equiv.Perm (Fin m), Preserves R (fun a _ => σ a)) ↔
      (∀ a ∈ R, ∀ b : Fin n → Fin m, canonicalize a = canonicalize b → b ∈ R) :=
  pattern_characterization R

-- STATEMENT-PIN
example {m n : ℕ} (a b : Fin n → Fin m) (h : canonicalize a = canonicalize b) :
    ∃ σ : Equiv.Perm (Fin m), b = fun i => σ (a i) :=
  orbit_of_same_pattern a b h

-- ============================================================
-- §VIII — Wachen
-- ============================================================

/-- info: 'Reformulation.Proemial.PatternInvariance.eq_transfer' depends on axioms: [propext] -/
#guard_msgs in #print axioms eq_transfer

/-- info: 'Reformulation.Proemial.PatternInvariance.head_mem_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms head_mem_transfer

/-- info: 'Reformulation.Proemial.PatternInvariance.dedup_length_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms dedup_length_congr

/-- info: 'Reformulation.Proemial.PatternInvariance.dedup_idxOf_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms dedup_idxOf_congr

/-- info: 'Reformulation.Proemial.PatternInvariance.viaLists_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms viaLists_inv

/-- info: 'Reformulation.Proemial.PatternInvariance.marksFull_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms marksFull_nodup

/-- info: 'Reformulation.Proemial.PatternInvariance.marksFull_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms marksFull_mem

/-- info: 'Reformulation.Proemial.PatternInvariance.marksFull_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms marksFull_length

/-- info: 'Reformulation.Proemial.PatternInvariance.dedup_prefix_idxOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms dedup_prefix_idxOf

/-- info: 'Reformulation.Proemial.PatternInvariance.viaLists_marks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms viaLists_marks

/-- info: 'Reformulation.Proemial.PatternInvariance.pat_ofFn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pat_ofFn

/-- info: 'Reformulation.Proemial.PatternInvariance.orbit_of_same_pattern' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms orbit_of_same_pattern

/-- info: 'Reformulation.Proemial.PatternInvariance.preserves_unary' does not depend on any axioms -/
#guard_msgs in #print axioms preserves_unary

/-- info: 'Reformulation.Proemial.PatternInvariance.canonicalize_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms canonicalize_perm

/-- info: 'Reformulation.Proemial.PatternInvariance.pattern_characterization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms pattern_characterization

/-- info: 'Reformulation.Proemial.PatternInvariance.orbit_witness_three' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms orbit_witness_three

/-- info: 'Reformulation.Proemial.PatternInvariance.orbit_needs_bijective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms orbit_needs_bijective

end Reformulation.Proemial.PatternInvariance
