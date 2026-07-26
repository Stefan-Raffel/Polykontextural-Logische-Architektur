import Reformulation.Kenogram.Basic
import Mathlib.Logic.Relation

/-!
# Reformulation.Kenogram.Operational — die Operationssemantik der Kenogrammatik (C)

Vierte Kenogram-Schicht. Erste Niederlegung nach dem Methodenwechsel (Lesart 2):
**Theorem vor Deutung, bottom-up am Term erprobt.** Sie macht aus der schon
bewiesenen Normalform-*Funktion* `relabel` (Basic.lean) eine *Operationssemantik
im Plotkin-SOS-Sinn*: eine kleinschritt-Reduktionsrelation `Step` (`↝`) auf
Wert-Folgen `List ℕ`, deren Normalformen *genau* die RGS sind, mit Soundness
(`relabel` berechnet die Normalform), Konfluenz (eindeutige Normalform) und
starker Normalisierung (Terminierung).

## Die Step-Form (am Code erprobt, nicht gesetzt — Abschnitt II des Prompts)

Erprobt wurden zwei Kandidaten:

* **Kandidat A (Einweg-Overwrite):** an der ersten RGS-Verletzung den Wert durch
  seinen kanonischen Klassen-Index *ersetzen*. **Falsifiziert** (per `#eval`):
  `[0,2,2] ↝ [0,1,2]`, Normalform `[0,1,2]`, aber `relabel [0,2,2] = [0,1,1]`.
  Der Einweg-Overwrite bricht Soundness (Falsifikationskriterium 2) und kann bei
  Wert-Kollision (`[0,2,1]`) steckenbleiben (Normalform kein RGS, Kriterium 1).

* **Kandidat C (Transposition) — GEWÄHLT:** an der ersten Verletzung `i` werden
  die zwei Werte `v = l[i]` und `c = canonAt l i` (der kanonische Klassen-Index)
  *vertauscht* (`swapVals v c`). Eine Transposition ist *immer* eine Bijektion
  auf den Werten, erhält also das Gleichheits-Muster *ohne* Freiheits-Bedingung —
  daher gibt es keine Kollision. Per `#eval` über 15 Testfolgen: Normalform `==`
  `relabel`, Normalform stets RGS. Echt kleinschrittig (`[0,3,3,1,2,1] ↝
  [0,1,1,3,2,3] ↝ … ↝ [0,1,1,2,3,2]`), keine bloße Umetikettierung von `relabel`.

## Warum die drei Sätze tragen (Deutungsdichte)

Jeder Schritt ist eine Transposition ⇒ erhält das Gleichheits-Muster (`Step` →
gleiche Muster). Eine Normalform ist ein RGS (`isNormalForm_iff_isRGS`). `relabel l`
ist das *eindeutige* RGS mit dem Muster von `l` (`rgs_unique_of_pattern` +
`relabel_getElem?_eq_iff`, beide in Basic schon bewiesen). Daraus folgen Soundness
**und** Konfluenz ohne neue harte Arbeit; der harte Teil (Eindeutigkeit) ist in
Basic erledigt. Die einzige genuin neue Arbeit ist die Terminierung: der Index
der ersten Verletzung *wächst* bei jedem Schritt (`step_no_bad_le`, `step_mu_lt`), also fällt
das Maß `mu = length - firstBad-Index`.

## „ruht auf"-Audit (am Beweis-Körper, nicht nur Doc)

* `isNormalForm_iff_isRGS` ⟸ `isRGS_iff`.
* `step_preserves_pattern` ⟸ `swapVals` injektiv (Transposition).
* `soundness` (`l ↝* relabel l`) ⟸ `relabel_eq_self_of_isRGS`, `relabel_swapVals`
  (⟸ `rgs_unique_of_pattern`, `relabel_isRGS`, `relabel_getElem?_eq_iff`).
* `confluence`/`nf_unique` ⟸ `rgs_unique_of_pattern`, `relabel_getElem?_eq_iff`.
* `step_no_bad_le` (Terminierung) ⟸ `le_foldr_max`, `swapVals_take_eq`, prefix-Werte-Schranke; `step_mu_lt` ⟸ `Nat.find` Minimalität.

## Was C NICHT tut

Keine Neuheit der RGS↔Partition-Bijektion (Lehrbuch-Kombinatorik). Keine Deutung
über den Term hinaus (keine „kenogrammatische Akkretion", kein Günther-Anspruch,
den `↝` nicht einlöst). Kein `True`-Feld, kein Zeuge-außerhalb-einer-Familie. Die
Strom-`↝`-Form (ko-induktiv) ist nachgelagert und nicht Teil von C.
-/

namespace Reformulation.Kenogram

open List

/-! ## Teil 0 — Transposition (swap) und ihre Muster-Treue -/

/-- Vertauschung zweier Werte: eine Involution auf `ℕ`. -/
def swap (a b : ℕ) : ℕ → ℕ := fun x => if x = a then b else if x = b then a else x

/-- `swap a b` ist injektiv (Involution). -/
theorem swap_injective (a b : ℕ) : Function.Injective (swap a b) := by
  intro x y h
  unfold swap at h
  by_cases hxa : x = a <;> by_cases hxb : x = b <;>
    by_cases hya : y = a <;> by_cases hyb : y = b <;>
    simp_all

/-- Vertauschung zweier Werte überall in einer Liste. -/
def swapVals (a b : ℕ) (l : List ℕ) : List ℕ := l.map (swap a b)

@[simp] theorem swapVals_length (a b : ℕ) (l : List ℕ) :
    (swapVals a b l).length = l.length := by simp [swapVals]

theorem swapVals_getElem? (a b : ℕ) (l : List ℕ) (k : ℕ) :
    (swapVals a b l)[k]? = (l[k]?).map (swap a b) := by
  simp [swapVals, List.getElem?_map]

/-- **Muster-Treue der Transposition**: `swapVals` erhält das Gleichheits-Muster,
weil `swap a b` injektiv ist. Das ist die Stelle, an der die Transposition
Soundness und Konfluenz *frei* liefert. -/
theorem swapVals_pattern (a b : ℕ) (l : List ℕ) (i j : ℕ) :
    (swapVals a b l)[i]? = (swapVals a b l)[j]? ↔ l[i]? = l[j]? := by
  rw [swapVals_getElem?, swapVals_getElem?]
  constructor
  · intro h
    rcases hi : l[i]? with _ | x
    · rcases hj : l[j]? with _ | y
      · rfl
      · rw [hi, hj] at h; simp at h
    · rcases hj : l[j]? with _ | y
      · rw [hi, hj] at h; simp at h
      · rw [hi, hj] at h
        simp only [Option.map_some, Option.some.injEq] at h
        rw [swap_injective a b h]
  · intro h; rw [h]

/-! ## Teil 1 — Die Reduktionsrelation -/

/-- Der kanonische Klassen-Index an Position `i`: `0` an Position `0`, sonst das
Präfix-Maximum plus eins (für ein RGS-Präfix die Zahl der bisherigen Klassen). -/
def canonAt (l : List ℕ) (i : ℕ) : ℕ := if i = 0 then 0 else (l.take i).foldr max 0 + 1

/-- `badAt l i`: Position `i` verletzt die RGS-Bedingung — entweder das erste
Zeichen ist nicht `0`, oder ein späteres Zeichen überschreitet das Präfix-Maximum
um mehr als eins. -/
def badAt (l : List ℕ) (i : ℕ) : Prop :=
  (l[i]! > (l.take i).foldr max 0 + 1) ∨ (i = 0 ∧ l[i]! ≠ 0)

instance (l : List ℕ) (i : ℕ) : Decidable (badAt l i) := by unfold badAt; infer_instance

/-- Index der *ersten* RGS-Verletzung (least via `Nat.find`), `none` falls keine. -/
noncomputable def firstBad (l : List ℕ) : Option ℕ :=
  if h : ∃ i, i < l.length ∧ badAt l i then some (Nat.find h) else none

/-- Ein Reduktionsschritt: vertausche an der ersten Verletzung `i` den Wert
`l[i]` mit dem kanonischen Index `canonAt l i`. -/
noncomputable def stepFn (l : List ℕ) : List ℕ :=
  match firstBad l with
  | none => l
  | some i => swapVals (l[i]!) (canonAt l i) l

/-- Die kleinschritt-Reduktionsrelation `↝`: `l` ist nicht in Normalform (es gibt
eine Verletzung), und `l'` ist der Transpositions-Schritt. -/
def Step (l l' : List ℕ) : Prop :=
  (∃ i, i < l.length ∧ badAt l i) ∧ l' = stepFn l

@[inherit_doc] infixr:50 " ↝ " => Step

/-- Reflexiv-transitive Hülle `↝*`. -/
def Reduces : List ℕ → List ℕ → Prop := Relation.ReflTransGen Step

@[inherit_doc] infixr:50 " ↝* " => Reduces

/-- Normalform-Prädikat: kein Schritt geht von `l` aus. -/
def isNormalForm (l : List ℕ) : Prop := ¬ ∃ l', Step l l'

/-! ## Teil 2 — Normalform = RGS (Falsifikationskriterium 1) -/

/-- `badAt` in `getElem`-Form für gültige Indizes (ersetzt `l[i]!` durch `l[i]`). -/
theorem badAt_of_lt {l : List ℕ} {i : ℕ} (h : i < l.length) :
    badAt l i ↔ (l[i] > (l.take i).foldr max 0 + 1) ∨ (i = 0 ∧ l[i] ≠ 0) := by
  unfold badAt; rw [getElem!_pos l i h]

/-- Keine Verletzung an irgendeiner Position ⟺ RGS. Brücke zu `isRGS_iff`.

**Classical-Vermeidung (B2).** Die drei früheren `push Not`-Schritte zogen
`Classical.not_not` und damit `Classical.choice` in die ganze Naht (`badAt` ist
über `instDecidableBadAt` entscheidbar, die Negationen brauchen also keine
klassische Logik). Ersetzt durch `not_or` (intuitionistisch), `Nat.not_lt` und
`Decidable.not_not` — alle drei axiomfrei. -/
theorem no_badAt_iff_isRGS (l : List ℕ) :
    (∀ i, i < l.length → ¬ badAt l i) ↔ IsRGS l := by
  rw [isRGS_iff]
  constructor
  · intro H
    refine ⟨fun h0 => ?_, fun i hi => ?_⟩
    · have := H 0 h0
      rw [badAt_of_lt h0] at this
      simp only [List.get_eq_getElem]
      exact Decidable.not_not.mp (fun hne => this (Or.inr ⟨rfl, hne⟩))
    · have hlt : i + 1 < l.length := hi
      have := H (i + 1) hlt
      rw [badAt_of_lt hlt] at this
      simp only [List.get_eq_getElem]
      exact Nat.not_lt.mp (fun hgt => this (Or.inl hgt))
  · rintro ⟨h0, hrest⟩ i hi
    rw [badAt_of_lt hi, not_or]
    constructor
    · refine Nat.not_lt.mpr ?_
      cases i with
      | zero =>
        have : l[0] = 0 := by simpa [List.get_eq_getElem] using h0 hi
        simp [this]
      | succ k =>
        have := hrest k hi
        simpa [List.get_eq_getElem] using this
    · rintro ⟨rfl, hne⟩
      exact hne (by simpa [List.get_eq_getElem] using h0 hi)

/-- `firstBad l = none` ⟺ keine Verletzung ⟺ RGS. -/
theorem firstBad_none_iff (l : List ℕ) : firstBad l = none ↔ IsRGS l := by
  rw [← no_badAt_iff_isRGS]
  unfold firstBad
  split
  · rename_i h
    constructor
    · intro hcon; exact absurd hcon (Option.some_ne_none _)
    · intro H; exfalso; obtain ⟨i, hi, hb⟩ := h; exact H i hi hb
  · rename_i h
    push Not at h
    simp only [true_iff]
    intro i hi
    exact h i hi

/-- Ein Schritt existiert genau dann, wenn `l` kein RGS ist. -/
theorem step_exists_iff (l : List ℕ) : (∃ l', Step l l') ↔ ¬ IsRGS l := by
  constructor
  · rintro ⟨l', hb, -⟩ hrgs
    rw [← firstBad_none_iff] at hrgs
    unfold firstBad at hrgs
    rw [dif_pos hb] at hrgs
    exact (Option.some_ne_none _ hrgs)
  · intro hrgs
    rw [← firstBad_none_iff] at hrgs
    have hb : ∃ i, i < l.length ∧ badAt l i := by
      by_contra h
      unfold firstBad at hrgs
      rw [dif_neg h] at hrgs
      exact hrgs rfl
    exact ⟨stepFn l, hb, rfl⟩

/-- **Normalform = RGS** (Falsifikationskriterium 1, eingelöst): die Step-Form hat
*genau* die RGS als Normalformen. -/
theorem isNormalForm_iff_isRGS (l : List ℕ) : isNormalForm l ↔ IsRGS l := by
  unfold isNormalForm
  rw [step_exists_iff]
  -- `Decidable.not_not` statt `not_not` (B2): `IsRGS` ist über
  -- `instDecidablePredListNatIsRGS` entscheidbar, die Doppelnegation braucht
  -- keine klassische Logik.
  exact Decidable.not_not

/-! ## Teil 3a — Muster-Erhaltung, `relabel`-Invarianz, Konfluenz -/

/-- `firstBad` liefert bei vorhandener Verletzung `some (Nat.find …)`. -/
theorem firstBad_eq_some {l : List ℕ} (hb : ∃ i, i < l.length ∧ badAt l i) :
    firstBad l = some (Nat.find hb) := by
  unfold firstBad; rw [dif_pos hb]

/-- Der Schritt ist die Transposition an der ersten Verletzung. -/
theorem stepFn_eq_swap {l : List ℕ} (hb : ∃ i, i < l.length ∧ badAt l i) :
    stepFn l = swapVals (l[Nat.find hb]!) (canonAt l (Nat.find hb)) l := by
  unfold stepFn; rw [firstBad_eq_some hb]

/-- Jeder Schritt ist eine Transposition: `l' = swapVals a b l` für ein `a, b`. -/
theorem step_is_swap {l l' : List ℕ} (h : Step l l') :
    ∃ a b, l' = swapVals a b l := by
  obtain ⟨hb, hl'⟩ := h
  exact ⟨l[Nat.find hb]!, canonAt l (Nat.find hb), by rw [hl', stepFn_eq_swap hb]⟩

/-- Ein Schritt erhält die Länge. -/
theorem step_length {l l' : List ℕ} (h : Step l l') : l'.length = l.length := by
  obtain ⟨a, b, rfl⟩ := step_is_swap h; exact swapVals_length a b l

/-- **Ein Schritt erhält das Gleichheits-Muster** (Transposition ist injektiv). -/
theorem step_preserves_pattern {l l' : List ℕ} (h : Step l l') (i j : ℕ) :
    l'[i]? = l'[j]? ↔ l[i]? = l[j]? := by
  obtain ⟨a, b, rfl⟩ := step_is_swap h; exact swapVals_pattern a b l i j

/-- **`relabel` ist invariant unter Transposition**: ruht auf `rgs_unique_of_pattern`,
`relabel_isRGS`, `relabel_getElem?_eq_iff` (alle Basic). -/
theorem relabel_swapVals (a b : ℕ) (l : List ℕ) :
    relabel (swapVals a b l) = relabel l := by
  apply rgs_unique_of_pattern (relabel_isRGS _) (relabel_isRGS _)
  · rw [relabel_length, relabel_length, swapVals_length]
  · intro i j
    rw [relabel_getElem?_eq_iff, relabel_getElem?_eq_iff, swapVals_pattern]

/-- `relabel` ist invariant unter einem Schritt. -/
theorem relabel_step {l l' : List ℕ} (h : Step l l') : relabel l' = relabel l := by
  obtain ⟨a, b, rfl⟩ := step_is_swap h; exact relabel_swapVals a b l

/-- `relabel` ist invariant unter `↝*`. -/
theorem reduces_relabel_eq {l r : List ℕ} (h : l ↝* r) : relabel r = relabel l := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => rw [relabel_step hstep]; exact ih

/-- **Jede erreichbare Normalform ist `relabel l`** (Konfluenz-Kern, Soundness-Ziel):
ruht auf `relabel_eq_self_of_isRGS` und der `relabel`-Invarianz. -/
theorem nf_eq_relabel {l r : List ℕ} (hred : l ↝* r) (hnf : IsRGS r) : r = relabel l := by
  rw [← reduces_relabel_eq hred, relabel_eq_self_of_isRGS hnf]

/-- **Konfluenz / Eindeutigkeit der Normalform**: zwei aus `l` erreichbare
Normalformen sind gleich. -/
theorem nf_unique {l r₁ r₂ : List ℕ}
    (h₁ : l ↝* r₁) (hn₁ : IsRGS r₁) (h₂ : l ↝* r₂) (hn₂ : IsRGS r₂) : r₁ = r₂ := by
  rw [nf_eq_relabel h₁ hn₁, nf_eq_relabel h₂ hn₂]

/-! ## Teil 4 — Starke Normalisierung (Terminierung) -/

/-- Jedes Element einer Liste ist `≤` dem `foldr max 0`. -/
theorem le_foldr_max {x : ℕ} {L : List ℕ} (h : x ∈ L) : x ≤ L.foldr max 0 := by
  induction L with
  | nil => simp at h
  | cons a t ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h'
    · exact le_max_left _ _
    · exact le_trans (ih h') (le_max_right _ _)

/-- `swap` lässt Werte fest, die weder `v` noch `c` sind. -/
theorem swap_fixed {v c x : ℕ} (hv : x ≠ v) (hc : x ≠ c) : swap v c x = x := by
  unfold swap; rw [if_neg hv, if_neg hc]

/-- `swap v c v = c`. -/
theorem swap_left (v c : ℕ) : swap v c v = c := by unfold swap; simp

/-- `getElem!` von `map` für gültige Indizes. -/
theorem map_getElem!_of_lt {g : ℕ → ℕ} {l : List ℕ} {k : ℕ} (h : k < l.length) :
    (l.map g)[k]! = g (l[k]!) := by
  rw [getElem!_pos (l.map g) k (by simpa using h), getElem!_pos l k h,
      List.getElem_map]

/-- Wird jedes Präfix-Element von `swap a b` festgelassen, so ist das `j`-Präfix
unter `swapVals` unverändert. -/
theorem swapVals_take_eq {a b : ℕ} {l : List ℕ} {j : ℕ}
    (h : ∀ x ∈ l.take j, swap a b x = x) : (swapVals a b l).take j = l.take j := by
  unfold swapVals
  rw [← List.map_take]
  rw [List.map_congr_left (g := id) h, List.map_id]

/-- `l[j]!` liegt im `i`-Präfix, sofern `j < i ≤ length`. -/
theorem getElem!_mem_take {l : List ℕ} {j i : ℕ} (hj : j < i) (hi : i ≤ l.length) :
    l[j]! ∈ l.take i := by
  have hjl : j < l.length := lt_of_lt_of_le hj hi
  rw [getElem!_pos l j hjl]
  have hji : j < (l.take i).length := by rw [List.length_take]; omega
  have heq : (l.take i)[j]'hji = l[j]'hjl := List.getElem_take
  rw [← heq]
  exact List.getElem_mem hji

/-- **Das Maß**: `length` minus Index der ersten Verletzung (`length` falls keine). -/
noncomputable def mu (l : List ℕ) : ℕ := l.length - (firstBad l).getD l.length

/-- **Kern-Lemma der Terminierung**: nach einem Schritt ist keine Position `≤ i`
mehr verletzt (`i` = erste Verletzung), d.h. der Verletzungs-Index wächst. -/
theorem step_no_bad_le {l : List ℕ} (hb : ∃ i, i < l.length ∧ badAt l i) :
    ∀ j, j ≤ Nat.find hb → ¬ badAt (stepFn l) j := by
  obtain ⟨hi_lt, hi_bad⟩ := Nat.find_spec hb
  have hmin : ∀ j, j < Nat.find hb → ¬ badAt l j := by
    intro j hj hbad
    exact Nat.find_min hb hj ⟨lt_trans hj hi_lt, hbad⟩
  have hstep : stepFn l = swapVals (l[Nat.find hb]!) (canonAt l (Nat.find hb)) l :=
    stepFn_eq_swap hb
  -- abbreviations
  set i := Nat.find hb with hidef
  set v := l[i]! with hvdef
  set c := canonAt l i with hcdef
  -- v > c (for i > 0) resp. v ≠ c (= 0, for i = 0)
  have hprefix_fix : ∀ x ∈ l.take i, swap v c x = x := by
    intro x hx
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · rw [hi0] at hx; simp at hx
    · have hcc : c = (l.take i).foldr max 0 + 1 := by
        rw [hcdef]; unfold canonAt; rw [if_neg hipos.ne']
      have hxle : x ≤ (l.take i).foldr max 0 := le_foldr_max hx
      have hvgt : v > (l.take i).foldr max 0 + 1 := by
        rcases hi_bad with h1 | ⟨h0, _⟩
        · exact h1
        · exact absurd h0 hipos.ne'
      apply swap_fixed <;> omega
  have htake : ∀ j, j ≤ i → (swapVals v c l).take j = l.take j := by
    intro j hj
    apply swapVals_take_eq
    intro x hx
    apply hprefix_fix x
    have hxeq : l.take j = (l.take i).take j := by rw [List.take_take, Nat.min_eq_left hj]
    rw [hxeq] at hx
    exact List.mem_of_mem_take hx
  have hvali : (swapVals v c l)[i]! = c := by
    unfold swapVals
    rw [map_getElem!_of_lt (g := swap v c) (l := l) hi_lt]
    exact swap_left v c
  rw [hstep]
  intro j hj
  rcases lt_or_eq_of_le hj with hlt | heq
  · -- j < i : badAt l' j = badAt l j (false)
    intro hbad
    apply hmin j hlt
    have hvj : (swapVals v c l)[j]! = l[j]! := by
      unfold swapVals
      rw [map_getElem!_of_lt (g := swap v c) (l := l) (lt_trans hlt hi_lt)]
      exact hprefix_fix (l[j]!) (getElem!_mem_take hlt (le_of_lt hi_lt))
    unfold badAt at hbad ⊢
    rwa [hvj, htake j (le_of_lt hlt)] at hbad
  · -- j = i : badAt l' i is false
    subst heq
    intro hbad
    unfold badAt at hbad
    rw [hvali, htake i le_rfl] at hbad
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · rw [hcdef, hi0] at hbad
      simp [canonAt] at hbad
    · have hcc : c = (l.take i).foldr max 0 + 1 := by
        rw [hcdef]; unfold canonAt; rw [if_neg hipos.ne']
      rcases hbad with h1 | ⟨h0, _⟩
      · rw [hcc] at h1; omega
      · exact absurd h0 hipos.ne'

/-- **Das Maß fällt bei jedem Schritt** — die starke Normalisierung in nutzbarer
Form. Der Verletzungs-Index wächst (`step_no_bad_le`), also fällt `mu`. -/
theorem step_mu_lt {l l' : List ℕ} (h : Step l l') : mu l' < mu l := by
  obtain ⟨hb, rfl⟩ := h
  have hi_lt : Nat.find hb < l.length := (Nat.find_spec hb).1
  have hlen : (stepFn l).length = l.length := by
    rw [stepFn_eq_swap hb]; exact swapVals_length _ _ _
  have hmu_l : mu l = l.length - Nat.find hb := by
    unfold mu; rw [firstBad_eq_some hb]; rfl
  set X := (firstBad (stepFn l)).getD (stepFn l).length with hX
  have hge : X ≥ Nat.find hb + 1 := by
    by_cases hb' : ∃ k, k < (stepFn l).length ∧ badAt (stepFn l) k
    · rw [hX, firstBad_eq_some hb', Option.getD_some]
      by_contra hle
      have hle' : Nat.find hb' ≤ Nat.find hb := by omega
      exact step_no_bad_le hb (Nat.find hb') hle' (Nat.find_spec hb').2
    · have hnone : firstBad (stepFn l) = none := by unfold firstBad; rw [dif_neg hb']
      rw [hX, hnone, Option.getD_none, hlen]; omega
  have hmu' : mu (stepFn l) = (stepFn l).length - X := rfl
  rw [hmu', hlen, hmu_l]
  omega

/-- **Starke Normalisierung**: die Reduktion `↝` ist wohlfundiert (terminiert).
Ruht auf `step_mu_lt` über `InvImage` des `<` auf `ℕ`. -/
theorem step_wf : WellFounded (fun a b => Step b a) :=
  Subrelation.wf (fun {_ _} h => step_mu_lt h) (InvImage.wf mu Nat.lt_wfRel.wf)

/-! ## Teil 3b — Soundness (`relabel` berechnet die Normalform) -/

/-- **Soundness**: jede Folge reduziert zu ihrer `relabel`-Normalform. Beweis per
wohlfundierter Induktion über `step_wf`; jeder Schritt erhält `relabel`. -/
theorem soundness (l : List ℕ) : l ↝* relabel l := by
  refine step_wf.induction (C := fun l => l ↝* relabel l) l ?_
  intro l ih
  by_cases hrgs : IsRGS l
  · rw [relabel_eq_self_of_isRGS hrgs]; exact Relation.ReflTransGen.refl
  · obtain ⟨l', hstep⟩ := (step_exists_iff l).mpr hrgs
    rw [← relabel_step hstep]
    exact Relation.ReflTransGen.head hstep (ih l' hstep)

/-! ## Teil 5 — Die Operationssemantik (Zusammenfassung der Kern-Resultate) -/

/-- **`relabel l` IST die Normalform von `l`**: erreichbar (`soundness`) und in
Normalform (`isNormalForm_iff_isRGS` + `relabel_isRGS`). Hier wird `relabel` von
einer *Funktion* zu einer *operationalen Semantik*. -/
theorem relabel_is_normalForm (l : List ℕ) :
    l ↝* relabel l ∧ isNormalForm (relabel l) :=
  ⟨soundness l, (isNormalForm_iff_isRGS _).mpr (relabel_isRGS l)⟩

/-- **Charakterisierung der Operationssemantik**: `r` ist die Normalform von `l`
(erreichbar und in Normalform) genau dann, wenn `r = relabel l`. -/
theorem normalForm_iff_eq_relabel (l r : List ℕ) :
    (l ↝* r ∧ isNormalForm r) ↔ r = relabel l := by
  constructor
  · rintro ⟨hred, hnf⟩
    exact nf_eq_relabel hred ((isNormalForm_iff_isRGS r).mp hnf)
  · rintro rfl
    exact relabel_is_normalForm l

/-! ## Teil 6 — Deutungs-Tests (die Deutung am Term geprüft, kein interpretatorischer Rest)

Analog zu `target_depends_only_on_second` (Transjunktions-Aufnahme): wo eine Deutung
gemacht wird, steht ein Lean-Satz, der sie am Term belegt. -/

/-- **Deutungs-Test (Falsifikation von Kandidat A am Term):** `relabel [0,2,2] =
[0,1,1]`. Der Einweg-Overwrite an der ersten Verletzung liefert dagegen `[0,1,2]`
(ein RGS!), also eine Normalform `≠ relabel` — Soundness-Bruch. Belegt, dass die
Wahl der Transpositions-Form nicht kosmetisch ist. -/
example : relabel [0, 2, 2] = [0, 1, 1] := by decide
example : ([0, 1, 2] : List ℕ) ≠ relabel [0, 2, 2] := by decide

/-- **Deutungs-Test (die Step-Form ist deutungsdicht):** ein Schritt ist eine
Transposition, also injektiv auf den Werten — er erhält das Gleichheits-Muster
ohne Freiheits-Bedingung. Das ist `step_preserves_pattern`; hier als Kontrast-Test
explizit: `swap` ist eine Involution (kein bloßes Überschreiben). -/
example (a b x : ℕ) : swap a b (swap a b x) = x := by
  unfold swap
  by_cases hxa : x = a <;> by_cases hxb : x = b <;> simp_all

/-! ## Teil 7 — Die zwei Beleg-Nähte (F-C.1 / F-C.2, additiver Nachtrag)

Additive Anfügung *nach* der C-Bewertung; der bestehende Bestand (Teil 0–6) bleibt
unberührt. Diese zwei Sätze reparieren nichts Gebrochenes (C trägt bereits), sie
machen die Schicht *lückenlos* deutungsdicht, indem sie die zwei am Code gefundenen
Beleg-Nähte schließen:

* **Naht 1 (F-C.1):** Die `#eval`-Form-Erprobung lief auf einer *computable*
  Spiegelung, nicht auf dem in-file `noncomputable stepFn` (`firstBad`/`stepFn`/`mu`
  sind über `Nat.find` noncomputable). Hier wird diese Spiegelung in-file niedergelegt
  (`firstBad'`/`stepFn'`, computable über `List.find?`/`List.range` mit dem schon
  vorhandenen `Decidable (badAt l i)`) **und** ihre Koinzidenz mit `stepFn` bewiesen
  (`stepFn'_eq_stepFn`, ruht auf `firstBad'_eq_firstBad` ⟸ `Nat.find_spec`/`Nat.find_min`
  gegen die `List.find?_range`-Spezifikation). Die niedergelegte Reduktion *ist* damit
  die erprobte. SOS-Nebenbefund eingelöst: die Reduktionssemantik ist nun ausführbar
  (`#eval stepFn'`), `noncomputable stepFn` als koinzident bewiesen.

* **Naht 2 (F-C.2):** „Echt kleinschrittig" ruhte allein auf der `#eval`-Spur. Hier
  steht der ≥2-Schritt-Zeuge am Term (`step_two_step_witness`): eine Reduktion mit
  *nicht-normaler* Zwischenform, geführt über die computable `stepFn'` per `decide`
  plus Koinzidenz.

## „ruht auf"-Audit (Teil 7)

* `firstBad'_eq_firstBad` ⟸ `List.find?_range_eq_some`/`_none`, `Nat.find_spec`,
  `Nat.find_min` (Minimalität von `Nat.find` gegen die `find?`-Spezifikation),
  `badAt`-`Decidable` (über `decide`).
* `stepFn'_eq_stepFn` ⟸ `firstBad'_eq_firstBad` (Fallunterscheidung am gemeinsamen
  `firstBad l`).
* `step_two_step_witness` ⟸ `stepFn'_eq_stepFn` (hebt die computable Reduktion auf
  `Step`), `decide` (`badAt`/`relabel`).

`firstBad'`/`stepFn'` sind computable (Axiome: nur `propext`). Die Koinzidenz- und
Zeugen-Sätze referenzieren das noncomputable `firstBad`/`stepFn`/`Step` und tragen
darum `Classical.choice` mit — unvermeidbar und hier vermerkt; die *berechenbare*
Variante selbst bleibt Classical-frei. -/

/-- **F-C.1 — computable Spiegelung von `firstBad`**: der Index der ersten
RGS-Verletzung, gesucht per `List.find?` über `List.range l.length` mit dem schon
vorhandenen `Decidable (badAt l i)` statt über `Nat.find`. Berechenbar. -/
def firstBad' (l : List ℕ) : Option ℕ :=
  (List.range l.length).find? (fun i => decide (badAt l i))

/-- **Koinzidenz (Naht 1)**: die computable `firstBad'` stimmt mit dem in-file
`noncomputable firstBad` überein. Ruht auf der Minimalität von `Nat.find`
(`Nat.find_spec`/`Nat.find_min`) gegen die `List.find?_range`-Spezifikation. -/
theorem firstBad'_eq_firstBad (l : List ℕ) : firstBad' l = firstBad l := by
  unfold firstBad' firstBad
  split
  · rename_i h
    rw [List.find?_range_eq_some]
    refine ⟨decide_eq_true (Nat.find_spec h).2, List.mem_range.mpr (Nat.find_spec h).1, ?_⟩
    intro j hj
    have hjlt : j < l.length := lt_trans hj (Nat.find_spec h).1
    have : ¬ badAt l j := fun hb => Nat.find_min h hj ⟨hjlt, hb⟩
    simp [this]
  · rename_i h
    rw [List.find?_range_eq_none]
    intro i hi
    have : ¬ badAt l i := fun hb => h ⟨i, hi, hb⟩
    simp [this]

/-- **F-C.1 — computable Spiegelung von `stepFn`** (analog zu `stepFn`, aber über
`firstBad'`). Berechenbar: `#eval stepFn' …` läuft. -/
def stepFn' (l : List ℕ) : List ℕ :=
  match firstBad' l with
  | none => l
  | some i => swapVals (l[i]!) (canonAt l i) l

/-- **Koinzidenz (Naht 1), gehoben auf `stepFn`**: die erprobte (computable)
Reduktion *ist* die niedergelegte. Damit ist `stepFn'` per `decide`/`rfl` als
Berechnungsmittel für `Step l l'` (= `… ∧ l' = stepFn l`) nutzbar. -/
theorem stepFn'_eq_stepFn (l : List ℕ) : stepFn' l = stepFn l := by
  unfold stepFn' stepFn
  rw [firstBad'_eq_firstBad]

/-- **In-file-Tests über `stepFn'`** (vorher nur in der gelöschten Scratch-Spiegelung):
die Step-Form-Erprobungs-Beispiele, nun `by decide` am in-file-Term. Der erste ist
zugleich der erste Schritt des ≥2-Schritt-Zeugen unten. -/
example : stepFn' [0, 2, 4] = [0, 1, 4] := by decide
example : stepFn' [0, 1, 4] = [0, 1, 2] := by decide
/-- Das Doc-Beispiel aus Teil II (`[0,3,3,1,2,1] ↝ … ↝ [0,1,1,2,3,2]`), nun
ausführbar und am Term belegt: zwei Schritte zur Normalform. -/
example : stepFn' [0, 3, 3, 1, 2, 1] = [0, 1, 1, 3, 2, 3] := by decide
example : stepFn' [0, 1, 1, 3, 2, 3] = [0, 1, 1, 2, 3, 2] := by decide
#eval stepFn' [0, 3, 3, 1, 2, 1]            -- [0, 1, 1, 3, 2, 3]
#eval stepFn' (stepFn' [0, 3, 3, 1, 2, 1])  -- [0, 1, 1, 2, 3, 2]

/-- **F-C.2 — ≥2-Schritt-Zeuge (Naht 2)**: eine echte Zweischritt-Reduktion mit
*nicht-normaler* Zwischenform. `[0,2,4] ↝ [0,1,4] ↝ [0,1,2] = relabel [0,2,4]`;
die Zwischenform `[0,1,4]` ist *kein* RGS (Position 2 überschreitet das Präfix-Maximum),
also `m ≠ relabel l` — die Reduktion ist nach *einem* Schritt noch nicht fertig. Damit
ist „echt kleinschrittig" am Term belegt, nicht per `#eval`-Spur. Über die computable
`stepFn'` (F-C.1) sind beide Schritte per `decide` plus Koinzidenz geführt. -/
theorem step_two_step_witness :
    ∃ l m r, Step l m ∧ Step m r ∧ m ≠ relabel l := by
  refine ⟨[0, 2, 4], [0, 1, 4], [0, 1, 2], ?_, ?_, ?_⟩
  · exact ⟨⟨1, by decide, by decide⟩, by rw [← stepFn'_eq_stepFn]; decide⟩
  · exact ⟨⟨2, by decide, by decide⟩, by rw [← stepFn'_eq_stepFn]; decide⟩
  · decide

/-! ## Axiom-Wachen (B2)

Die gemessenen Profile der 23 tragenden Deklarationen dieser Datei, eingefroren.
Sie ersetzen die elf frueheren nackten `#print axioms`-Aufrufe, die Profile
erzeugten, aber nichts sicherten.

**Classical-Vermeidung.** `no_badAt_iff_isRGS` und `isNormalForm_iff_isRGS` zogen
`Classical.choice` ueber `push Not` bzw. `not_not`. Beide Praedikate sind
entscheidbar (`instDecidableBadAt`, `instDecidablePredListNatIsRGS`); ersetzt durch
`not_or`, `Nat.not_lt` und `Decidable.not_not` (alle drei axiomfrei). Vier Saetze
sind dadurch klassikfrei geworden: die beiden geheilten sowie `firstBad_none_iff`
und `step_exists_iff`, die ihren Choice ausschliesslich geerbt hatten.
`soundness`, `relabel_is_normalForm` und `normalForm_iff_eq_relabel` bleiben
klassisch — sie haben zusaetzlich externe Traeger (`Classical.choose` ueber
`Nat.find`-Umgebung, `List.findIdx?_eq_some_iff_getElem`, `lt_or_eq_of_le`). -/

/-- info: 'Reformulation.Kenogram.swapVals' does not depend on any axioms -/
#guard_msgs in #print axioms swapVals

/-- info: 'Reformulation.Kenogram.Step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Step

/-- info: 'Reformulation.Kenogram.no_badAt_iff_isRGS' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms no_badAt_iff_isRGS

/-- info: 'Reformulation.Kenogram.firstBad_none_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms firstBad_none_iff

/-- info: 'Reformulation.Kenogram.step_exists_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms step_exists_iff

/-- info: 'Reformulation.Kenogram.isNormalForm_iff_isRGS' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms isNormalForm_iff_isRGS

/-- info: 'Reformulation.Kenogram.step_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms step_length

/-- info: 'Reformulation.Kenogram.step_preserves_pattern' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms step_preserves_pattern

/-- info: 'Reformulation.Kenogram.relabel_swapVals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms relabel_swapVals

/-- info: 'Reformulation.Kenogram.nf_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nf_unique

/-- info: 'Reformulation.Kenogram.le_foldr_max' depends on axioms: [propext] -/
#guard_msgs in #print axioms le_foldr_max

/-- info: 'Reformulation.Kenogram.swapVals_take_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms swapVals_take_eq

/-- info: 'Reformulation.Kenogram.step_no_bad_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms step_no_bad_le

/-- info: 'Reformulation.Kenogram.step_mu_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms step_mu_lt

/-- info: 'Reformulation.Kenogram.step_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms step_wf

/-- info: 'Reformulation.Kenogram.soundness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms soundness

/-- info: 'Reformulation.Kenogram.relabel_is_normalForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms relabel_is_normalForm

/-- info: 'Reformulation.Kenogram.normalForm_iff_eq_relabel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms normalForm_iff_eq_relabel

/-- info: 'Reformulation.Kenogram.firstBad'' depends on axioms: [propext] -/
#guard_msgs in #print axioms firstBad'

/-- info: 'Reformulation.Kenogram.firstBad'_eq_firstBad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms firstBad'_eq_firstBad

/-- info: 'Reformulation.Kenogram.stepFn'' depends on axioms: [propext] -/
#guard_msgs in #print axioms stepFn'

/-- info: 'Reformulation.Kenogram.stepFn'_eq_stepFn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stepFn'_eq_stepFn

/-- info: 'Reformulation.Kenogram.step_two_step_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms step_two_step_witness

end Reformulation.Kenogram
