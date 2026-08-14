import Reformulation.Proemial.A3CoarseningProbe

/-!
# Reformulation.Proemial.DeuteroCollapse — die Vergröberung vergisst die Stellung

**Ertrag.** Die Vergröberung `deutero` ist **auf jeder Stufe ab drei** nicht
injektiv, allgemein in `n`:

```text
3 ≤ n  →  ∃ a b : RGS n, a ≠ b ∧ deutero a = deutero b
```

`A3CoarseningProbe` führt dieselbe Aussage als Sonde mit einem `decide`-Zeugen
bei `n = 3`. **Hier steht sie für alle Stufen**, mit einer Konstruktion.

## Wo die Beweislast sitzt

**Die zwei Zeugen sind Permutationen voneinander**, und daraus folgt die
Gleichheit der Vergröberung. Gebaut werden sie mit `grow`, das an eine Normalform
`k`-mal die jeweils nächste neue Marke anhängt:

```text
wA n := grow (n-3) [0,0,1]        wB n := grow (n-3) [0,1,0]
```

**Vier der fünf Hilfssätze sind neu; geliehen ist allein `isRGS_concat`.**

* `foldr_max_perm` — das Präfix-Maximum ist permutationsinvariant. Der
  `swap`-Fall läuft mit `simp` in die Rekursionsgrenze und ist von Hand geführt
  (`simp only [← max_assoc]`, dann `rw [max_comm]`).
* `grow_perm` — die Konstruktion erhält Permutationen, **weil** sie über
  `foldr max` anhängt.
* `deutero_of_perm` — Permutationen haben dieselbe Vergröberung; über die
  Gleichheit von `proto` und `(h.filter _).length_eq`.
* `grow_append` — `grow` hängt nur hinten an; daraus `w_ne` über die Stelle 1.

## Die Schranke und ihr Grund

`3 ≤ n` ist notwendig, nicht bequem: bei `n = 1` und `n = 2` ist `deutero`
**injektiv**. Am Bestand gemessen — `RGS 1` hat ein Element, `RGS 2` zwei mit
verschiedener Vergröberung.

## Grenze

Kein Paragraph-20-Anspruch. Der Satz sagt, dass die Vergröberung **Stellung**
vergisst, und sagt nichts über die Proemialrelation. **Insbesondere ist er kein
Träger für eine Stufenbewegung: `deutero` lässt die Länge fest.** Das hält die
Messung vom 12. August fest, an der die Vergröberung als Kandidat für eine
Bewegung auf der Stufen-Achse gefallen ist.

## Ablage

Das Modul liegt im Proemial-Zweig, **weil `deutero` dort steht**. Eine zweite
Definition derselben Abbildung im Kenogram-Zweig wäre eine Zutat; ein
Kenogram-Modul, das `Proemial` importiert, wäre ein Bruch der Zweigrichtung.
**Beides ist vermieden, indem die Datei dorthin geht, wo ihr Gegenstand liegt.**

Damit konsumiert ein Aggregat-Satz die Sonde `A3CoarseningProbe`, und sie tritt
nach `CLAUDE.md` §10 in die Aggregathülle ein — das ist der dort genannte
legitime Auslöser und keine Statusänderung nebenbei.
-/

namespace Reformulation.Proemial.DeuteroCollapse

open Reformulation.Kenogram
open Reformulation.Proemial.A3CoarseningProbe

/-- Anhängen von `k` jeweils neuen Marken. -/
def grow : ℕ → List ℕ → List ℕ
  | 0,     l => l
  | (k+1), l => grow k (l ++ [l.foldr max 0 + 1])

/-- `grow` verlängert um genau `k`. -/
theorem grow_length : ∀ (k : ℕ) (l : List ℕ), (grow k l).length = l.length + k := by
  intro k
  induction k with
  | zero => intro l; simp [grow]
  | succ m ih => intro l; simp [grow, ih]; omega

/-- `grow` erhält die Normalform: jede angehängte Marke überschreitet das
Präfix-Maximum um genau eins. -/
theorem grow_isRGS : ∀ (k : ℕ) {l : List ℕ}, l ≠ [] → IsRGS l → IsRGS (grow k l) := by
  intro k
  induction k with
  | zero => intro l _ h; simpa [grow] using h
  | succ m ih =>
      intro l hne h
      refine ih ?_ (isRGS_concat l _ h (le_refl _) (fun he => absurd he hne))
      simp

/-- Das Präfix-Maximum ist permutationsinvariant. Der `swap`-Fall ist von Hand
geführt: `simp` läuft dort mit `max_assoc` und `max_comm` in die
Rekursionsgrenze. -/
theorem foldr_max_perm {l l' : List ℕ} (h : List.Perm l l') :
    l.foldr max 0 = l'.foldr max 0 := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp [ih]
  | swap x y t =>
      simp only [List.foldr_cons, ← max_assoc]
      rw [max_comm x y]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- `grow` erhält Permutationen — weil die angehängte Marke über `foldr max`
bestimmt ist und dieses permutationsinvariant ist. -/
theorem grow_perm : ∀ (k : ℕ) {l l' : List ℕ}, List.Perm l l' →
    List.Perm (grow k l) (grow k l') := by
  intro k
  induction k with
  | zero => intro l l' h; simpa [grow] using h
  | succ m ih =>
      intro l l' h
      refine ih ?_
      rw [foldr_max_perm h]
      exact h.append_right _

/-- `grow` hängt nur hinten an. -/
theorem grow_append : ∀ (k : ℕ) (l : List ℕ), ∃ t, grow k l = l ++ t := by
  intro k
  induction k with
  | zero => intro l; exact ⟨[], by simp [grow]⟩
  | succ m ih =>
      intro l
      obtain ⟨t, ht⟩ := ih (l ++ [l.foldr max 0 + 1])
      exact ⟨(l.foldr max 0 + 1) :: t, by simp [grow, ht]⟩

/-- **Permutationen haben dieselbe Vergröberung.** Die Klassenzahl stimmt überein,
weil das Präfix-Maximum es tut; die Klassengrössen, weil `filter` und `length`
permutationsinvariant sind. -/
theorem deutero_of_perm {n : ℕ} {a b : RGS n} (h : List.Perm a.val b.val) :
    deutero a = deutero b := by
  have hp : proto a = proto b := by
    simp only [proto, foldr_max_perm h]
  simp only [deutero, hp]
  congr 1
  funext v
  exact (h.filter _).length_eq

/-- Der erste Zeuge. -/
def wA (n : ℕ) : List ℕ := grow (n - 3) [0, 0, 1]

/-- Der zweite Zeuge. -/
def wB (n : ℕ) : List ℕ := grow (n - 3) [0, 1, 0]

theorem wA_length {n : ℕ} (h : 3 ≤ n) : (wA n).length = n := by
  rw [wA, grow_length]; simp; omega

theorem wB_length {n : ℕ} (h : 3 ≤ n) : (wB n).length = n := by
  rw [wB, grow_length]; simp; omega

theorem wA_isRGS (n : ℕ) : IsRGS (wA n) := grow_isRGS _ (by simp) (by decide)

theorem wB_isRGS (n : ℕ) : IsRGS (wB n) := grow_isRGS _ (by simp) (by decide)

theorem w_perm (n : ℕ) : List.Perm (wA n) (wB n) := grow_perm _ (by decide)

/-- **Die zwei Zeugen sind verschieden.** Sie unterscheiden sich an der Stelle 1,
und `grow` rührt das Anfangsstück nicht an. -/
theorem w_ne (n : ℕ) : wA n ≠ wB n := by
  obtain ⟨tA, hA⟩ := grow_append (n - 3) [0, 0, 1]
  obtain ⟨tB, hB⟩ := grow_append (n - 3) [0, 1, 0]
  intro h
  rw [wA, hA, wB, hB] at h
  have h1 : ([0, 0, 1] ++ tA)[1]? = ([0, 1, 0] ++ tB)[1]? := by rw [h]
  rw [List.getElem?_append_left (by simp), List.getElem?_append_left (by simp)] at h1
  simp at h1

/-- **Die Vergröberung vergisst die Stellung.** Auf jeder Stufe `n ≥ 3` gibt es
zwei verschiedene Kenogramme mit derselben Vergröberung. -/
theorem deutero_not_injective_general {n : ℕ} (h : 3 ≤ n) :
    ∃ a b : RGS n, a ≠ b ∧ deutero a = deutero b := by
  refine ⟨⟨wA n, wA_length h, wA_isRGS n⟩, ⟨wB n, wB_length h, wB_isRGS n⟩, ?_, ?_⟩
  · intro hc
    exact w_ne n (congrArg Subtype.val hc)
  · exact deutero_of_perm (w_perm n)

/-! ## Wachen -/

-- STATEMENT-PIN
example {n : ℕ} (h : 3 ≤ n) : ∃ a b : RGS n, a ≠ b ∧ deutero a = deutero b :=
  deutero_not_injective_general h

/-- info: 'Reformulation.Proemial.DeuteroCollapse.grow' does not depend on any axioms -/
#guard_msgs in #print axioms grow

/-- info: 'Reformulation.Proemial.DeuteroCollapse.grow_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms grow_length

/-- info: 'Reformulation.Proemial.DeuteroCollapse.grow_isRGS' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms grow_isRGS

/-- info: 'Reformulation.Proemial.DeuteroCollapse.foldr_max_perm' depends on axioms: [propext] -/
#guard_msgs in #print axioms foldr_max_perm

/-- info: 'Reformulation.Proemial.DeuteroCollapse.grow_perm' depends on axioms: [propext] -/
#guard_msgs in #print axioms grow_perm

/-- info: 'Reformulation.Proemial.DeuteroCollapse.grow_append' depends on axioms: [propext] -/
#guard_msgs in #print axioms grow_append

/-- info: 'Reformulation.Proemial.DeuteroCollapse.deutero_of_perm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms deutero_of_perm

/-- info: 'Reformulation.Proemial.DeuteroCollapse.w_ne' depends on axioms: [propext] -/
#guard_msgs in #print axioms w_ne

/--
info: 'Reformulation.Proemial.DeuteroCollapse.deutero_not_injective_general' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms deutero_not_injective_general

end Reformulation.Proemial.DeuteroCollapse
