import Reformulation.Proemial.ChoiceVectors
import Mathlib.Data.Fin.VecNotation

/-!
# Proemial.LocalOpInseparability — keine Relation trennt die zyklischen von den transitiven lokal-klassischen Operationen, für jedes m

**ERTRAG**, gebaut nach `KorpusRev2/Spec_C2_fuer_alle_m.md` (Anker `f354b5e`), Entscheid des
Architekten vom 16. September 2026 für N3 (a). Grundlage ist die Sondierung „C2 für alle
m" derselben Instanz.

Eine lokal-klassische Operation auf `Fin m` ist ein Wahlvektor `c : Pairs m → Bool`
(`ChoiceVectors.ofChoices`, `true` = `max`). Die Sätze:

* `preserves_all_of_basis` — **der Zielsatz Z**: erhält eine Relation `R : Set (ι → Fin m)`
  beliebiger Stelligkeit `min`, `max` und alle Verschiebungen `shiftBefore p`,
  `shiftAfter p`, so erhält sie **jede** lokal-klassische Operation.
* `no_relation_separates_general` — **Z'**, das Korollar: erhält `R` alle transitiven
  lokal-klassischen Operationen, so alle. Keine Relation trennt die zyklischen von den
  transitiven, für jedes `m`.
* `divergence_from_clone_basis` — **A8**: für `m ≥ 4` wird die Invariante `R m` der E-Reihe
  von `min` und `max` erhalten, aber nicht von allen Verschiebungen.

## Der Beweis

* **Das Mehrheitsgesetz** `comp_eq_maj` (H1): auf jedem Paar wählt `f (g x y) (h x y)` wie
  `g` und `h`, wenn die gleich wählen, sonst wie `f`.
* **Die Basis ist transitiv** (`basis_transitive`, A3): `min`, `max` und beide
  Verschiebungen sind `ofChoices m (ofKey k)` für eine injektive Schlüsselfunktion `k`, und
  jede solche ist transitiv (`ofKey_transitive`) — die Transitivität ist die von `<` auf
  `ℕ`. Das ist der dritte Weg aus P1 der Spec; die „Hauptarbeit" A3 fällt damit auf ein
  Lemma.
* **Der Anfang** `base_eq` (H2): die Operation mit genau dem `max`-Paar `(i, j)` ist `min`
  der Verschiebungen `M₁` (`j` unmittelbar vor `i`) und `M₂` (`i` unmittelbar hinter `j`).
* **Der Schritt** `step_eq` (H3): mit zwei `max`-Paaren ist die Operation `max` der zwei
  Operationen, in denen je eines auf `min` zurückgesetzt ist.
* **Die Induktion** über die Zahl der `max`-Paare, gezählt in einer expliziten Liste
  `pairList m` (`maxCount_resetC_lt`).

Kein Klon-Begriff; Erhaltung wird nur durch Einsetzung übertragen (`preserves_comp`, hier
über `Fin m` neu — das C2-Modul hat es nur für `Fin 3`).

## Was davon bei Günther steht — und was nicht

* **Bei `m = 3` sind Günthers zwei Formeln von *Cognition and Volition* S. 28 Anfang und
  Schritt** — unter der Wertzuordnung `x ↦ 3 − x`: der Anfang zum Paar `(0,2)` ist
  `KKD = min(KDD, DKD)` (Günthers erste Formel, im C2-Modul `kkd_eq`), der Schritt für `DDK`
  ist `DDK = max(KDK, DKK)` (seine zweite). Die Muster der Verschiebungen sind am Dateiende
  gegen `KDD`/`DKD` geeicht; die Buchstaben-Zuordnung zu Günther ist außerhalb des Korpus
  gerechnet (siehe Kopf von `TournamentInseparability`).
* **Die Verallgemeinerung auf beliebiges `m` ist unsere.** Günther rechnet nur mit drei
  Werten; die Induktion, die Verschiebungen für `m > 3` und die Divergenz stehen nicht bei
  ihm.

## Verhältnis zur E-Reihe (N3 (a): konsumiert, ändert nicht)

Das Modul importiert `ChoiceVectors` und damit die E-Reihe (`ChoiceVectors` →
`StageAscent` → `GeneralCloneBound`). Es ändert sie nicht, es gebraucht sie in **einem**
Satz: `divergence_from_clone_basis` verbindet Z mit `preserving_is_min_or_max` (E3). Die
Erzeugbarkeit aus `{min, max, neg}` fällt ab `m = 4` auf `min` und `max` zusammen; die
Nicht-Trennbarkeit bleibt für jedes `m`. **Dass die zwei Achsen auseinandergehen, ist damit
ein Satz**, und zwar in der Form: die Basis von Z enthält Operationen, die die Invariante der
E-Reihe brechen. `LocallyClassical` ist in beiden Modulen dasselbe Prädikat (aus
`GeneralCloneBound`); `preservesR_iff` übersetzt nur die Erhaltungsform.

## Was dieses Modul NICHT sagt

* **Nichts über Günther jenseits von `m = 3`.**
* **Keine Zählung.** Transitive Operationen kommen vor und werden nicht gezählt; `m!` bleibt
  außerhalb (Q4b ist nicht gebaut).
* **Keine Minimalität der Basis** (Spec P4). Verschieden sind `2 + 2·C(m,2) − (m−1)`
  Operationen, außerhalb gerechnet; bei `m = 3` sind das alle sechs transitiven, und Z und Z'
  sagen dort dasselbe.
* **Nicht das C2-Modul als Folgerung.** `TournamentInseparability` rechnet mit `localOp`,
  nicht mit `ofChoices`; die Gleichheit ist nicht bewiesen, und eine Brücke führte das
  `[propext]` ein, das `kkd_eq` dort axiomfrei hält. Beide Module stehen nebeneinander
  (Spec P5).
* **Keine Ledger-Zeile** für Paragraph 20.

## Axiomprofil

Gemessen und am Dateiende gewacht. **Kein Satz trägt `Classical.choice`** — auch Z, Z' und
A8 nicht (`[propext, Quot.sound]`). Die Erwartung der Spec (A6: „vermutlich Choice") ist
damit widerlegt, und zwar auf zwei Wegen:

* Die Induktion zählt in `pairList m`, einer Liste aus `List.finRange`, nicht über
  `Fintype (Pairs m)` (P2).
* Die Bit-Rechnung des Anfangs (`base_bits`) trug in der ersten Fassung
  `[propext, Classical.choice, Quot.sound]` — `omega` auf einem Iff-Ziel mit Konjunktion
  (Fallstrick 7). In zwei Richtungen mit atomaren Zielen zerlegt ist sie
  `[propext, Quot.sound]`, und mit ihr Z, Z' und A8.

0 Sorries.
-/

namespace Reformulation.Proemial.LocalOpInseparability

open Reformulation.Proemial.GeneralCloneBound
open Reformulation.Proemial.ChoiceVectors

universe u

variable {m : ℕ}

/-! ## Teil 1 — Erhaltung über `Fin m` -/

/-- `R` wird von `o` erhalten: koordinatenweise angewandt, führt `o` zwei Tupel aus `R`
wieder in `R`. `R` ist eine Relation der Stelligkeit `ι` über `Fin m`. -/
def Preserves {ι : Type u} (R : Set (ι → Fin m)) (o : Fin m → Fin m → Fin m) : Prop :=
  ∀ a ∈ R, ∀ b ∈ R, (fun i => o (a i) (b i)) ∈ R

/-- Erhaltung ist unter Einsetzung abgeschlossen. -/
theorem preserves_comp {ι : Type u} {R : Set (ι → Fin m)}
    {f g h : Fin m → Fin m → Fin m}
    (hf : Preserves R f) (hg : Preserves R g) (hh : Preserves R h) :
    Preserves R (fun x y => f (g x y) (h x y)) :=
  fun a ha b hb => hf _ (hg a ha b hb) _ (hh a ha b hb)

/-- Erhaltung überträgt sich auf eine punktweise gleiche Operation. -/
theorem preserves_congr {ι : Type u} {R : Set (ι → Fin m)}
    {o o' : Fin m → Fin m → Fin m} (e : ∀ x y, o' x y = o x y)
    (h : Preserves R o) : Preserves R o' := by
  intro a ha b hb
  have hfun : (fun i => o' (a i) (b i)) = (fun i => o (a i) (b i)) :=
    funext fun i => e _ _
  rw [hfun]
  exact h a ha b hb

/-! ## Teil 2 — Das Mehrheitsgesetz -/

/-- Die Mehrheit dreier Wahlvektoren, gelesen als Komposition `f (g x y) (h x y)`:
wählen `g` und `h` auf einem Paar gleich, gilt ihre Wahl, sonst die von `f`. -/
def majC (cf cg ch : Pairs m → Bool) : Pairs m → Bool :=
  fun p => if cg p = ch p then cg p else cf p

/-- **H1, das Mehrheitsgesetz.** -/
theorem comp_eq_maj (cf cg ch : Pairs m → Bool) (a b : Fin m) :
    ofChoices m cf (ofChoices m cg a b) (ofChoices m ch a b) = ofChoices m (majC cf cg ch) a b := by
  rcases lt_trichotomy a b with h | rfl | h
  · obtain ⟨g1, -⟩ := ofChoices_pair m cg h
    obtain ⟨h1, -⟩ := ofChoices_pair m ch h
    obtain ⟨f1, f2⟩ := ofChoices_pair m cf h
    obtain ⟨r1, -⟩ := ofChoices_pair m (majC cf cg ch) h
    have fa : ofChoices m cf a a = a := ofChoices_diag m cf a
    have fb : ofChoices m cf b b = b := ofChoices_diag m cf b
    rw [g1, h1, r1]; unfold majC
    cases hg : cg ⟨(a, b), h⟩ <;> cases hh : ch ⟨(a, b), h⟩ <;> cases hf : cf ⟨(a, b), h⟩ <;>
      simp_all [min_eq_left h.le, max_eq_right h.le]
  · rw [ofChoices_diag, ofChoices_diag, ofChoices_diag, ofChoices_diag]
  · obtain ⟨-, g2⟩ := ofChoices_pair m cg h
    obtain ⟨-, h2⟩ := ofChoices_pair m ch h
    obtain ⟨f1, f2⟩ := ofChoices_pair m cf h
    obtain ⟨-, r2⟩ := ofChoices_pair m (majC cf cg ch) h
    have fa : ofChoices m cf a a = a := ofChoices_diag m cf a
    have fb : ofChoices m cf b b = b := ofChoices_diag m cf b
    rw [g2, h2, r2]; unfold majC
    cases hg : cg ⟨(b, a), h⟩ <;> cases hh : ch ⟨(b, a), h⟩ <;> cases hf : cf ⟨(b, a), h⟩ <;>
      simp_all [min_eq_left h.le, max_eq_right h.le]

/-- Punktweise gleiche Wahlvektoren geben punktweise gleiche Operationen. -/
theorem ofChoices_congr {c c' : Pairs m → Bool} (e : ∀ p, c p = c' p) (a b : Fin m) :
    ofChoices m c a b = ofChoices m c' a b := by
  have : c = c' := funext e
  rw [this]

/-! ## Teil 3 — Turnier, Transitivität, Schlüsselfunktionen -/

/-- Das Turnier einer Operation: `x` schlägt `y`, wenn `x ≠ y` und `o x y = x`. -/
def winsOver (o : Fin m → Fin m → Fin m) (x y : Fin m) : Prop := x ≠ y ∧ o x y = x

/-- Das Turnier von `o` ist transitiv. -/
def IsTransitiveOp (o : Fin m → Fin m → Fin m) : Prop :=
  ∀ x y z : Fin m, winsOver o x y → winsOver o y z → winsOver o x z

/-- Der Wahlvektor einer Schlüsselfunktion: auf dem Paar `a < b` wird `max` gewählt, wenn
`b` den kleineren Schlüssel hat. Der kleinere Schlüssel gewinnt. -/
def ofKey (k : Fin m → ℕ) : Pairs m → Bool := fun p => decide (k p.1.2 < k p.1.1)

/-- Unter einer injektiven Schlüsselfunktion gewinnt der kleinere Schlüssel. -/
theorem ofChoices_ofKey (k : Fin m → ℕ) (hk : ∀ x y, k x = k y → x = y)
    {x y : Fin m} (hxy : x ≠ y) :
    ofChoices m (ofKey k) x y = if k x < k y then x else y := by
  have hne : k x ≠ k y := fun e => hxy (hk x y e)
  rcases lt_or_gt_of_ne hxy with h | h
  · obtain ⟨e1, -⟩ := ofChoices_pair m (ofKey k) h
    rw [e1]; unfold ofKey
    by_cases hl : k y < k x
    · have hn : ¬ k x < k y := by omega
      simp only [hl, decide_true, if_true, hn, if_false, max_eq_right h.le]
    · have hn : k x < k y := by omega
      simp only [hl, decide_false, Bool.false_eq_true, if_false, hn, if_true, min_eq_left h.le]
  · obtain ⟨-, e2⟩ := ofChoices_pair m (ofKey k) h
    rw [e2]; unfold ofKey
    by_cases hl : k x < k y
    · simp only [hl, decide_true, if_true]; exact max_eq_right h.le
    · simp only [hl, decide_false, Bool.false_eq_true, if_false]; exact min_eq_left h.le

/-- **Jede injektive Schlüsselfunktion gibt eine transitive Operation.** Die
Transitivität ist die von `<` auf `ℕ`. -/
theorem ofKey_transitive (k : Fin m → ℕ) (hk : ∀ x y, k x = k y → x = y) :
    IsTransitiveOp (ofChoices m (ofKey k)) := by
  have key : ∀ x y : Fin m, winsOver (ofChoices m (ofKey k)) x y → k x < k y := by
    intro x y ⟨hxy, he⟩
    rw [ofChoices_ofKey k hk hxy] at he
    by_cases hl : k x < k y
    · exact hl
    · rw [if_neg hl] at he; exact absurd he.symm hxy
  intro x y z hxy hyz
  have h1 := key x y hxy
  have h2 := key y z hyz
  have hxz : x ≠ z := fun e => by subst e; omega
  exact ⟨hxz, by rw [ofChoices_ofKey k hk hxz, if_pos (by omega)]⟩


/-! ## Teil 4 — Die Basis: `min`, `max` und die zwei Verschiebungen -/

/-- `min` als Wahlvektor: überall `false`. -/
theorem ofChoices_false (a b : Fin m) : ofChoices m (fun _ => false) a b = min a b := by
  rcases lt_trichotomy a b with h | rfl | h
  · rw [(ofChoices_pair m _ h).1, if_neg (by decide)]
  · rw [ofChoices_diag, min_self]
  · rw [(ofChoices_pair m _ h).2, if_neg (by decide), min_comm]

/-- `max` als Wahlvektor: überall `true`. -/
theorem ofChoices_true (a b : Fin m) : ofChoices m (fun _ => true) a b = max a b := by
  rcases lt_trichotomy a b with h | rfl | h
  · rw [(ofChoices_pair m _ h).1]; exact (if_pos rfl)
  · rw [ofChoices_diag, max_self]
  · rw [(ofChoices_pair m _ h).2, if_pos rfl, max_comm]

/-- Der Schlüssel der natürlichen Ordnung. -/
def minKey (v : Fin m) : ℕ := v.val

/-- Der Schlüssel der umgekehrten Ordnung. -/
def maxKey (v : Fin m) : ℕ := m - v.val

/-- Die Verschiebung `M₁` zum Paar `(i, j)`: `j` unmittelbar vor `i`. -/
def keyBefore (p : Pairs m) (v : Fin m) : ℕ :=
  if v.val = p.1.2.val then 2 * p.1.1.val + 1 else 2 * v.val + 2

/-- Die Verschiebung `M₂` zum Paar `(i, j)`: `i` unmittelbar hinter `j`. -/
def keyAfter (p : Pairs m) (v : Fin m) : ℕ :=
  if v.val = p.1.1.val then 2 * p.1.2.val + 3 else 2 * v.val + 2

theorem minKey_inj : ∀ x y : Fin m, minKey x = minKey y → x = y :=
  fun _ _ h => Fin.ext h

theorem maxKey_inj : ∀ x y : Fin m, maxKey x = maxKey y → x = y := by
  intro x y h
  unfold maxKey at h
  have := x.isLt; have := y.isLt
  exact Fin.ext (by omega)

theorem keyBefore_inj (p : Pairs m) : ∀ x y : Fin m, keyBefore p x = keyBefore p y → x = y := by
  intro x y h
  unfold keyBefore at h
  apply Fin.ext
  by_cases hx : x.val = p.1.2.val <;> by_cases hy : y.val = p.1.2.val <;>
    simp only [hx, hy, if_true, if_false] at h <;> omega

theorem keyAfter_inj (p : Pairs m) : ∀ x y : Fin m, keyAfter p x = keyAfter p y → x = y := by
  intro x y h
  unfold keyAfter at h
  apply Fin.ext
  by_cases hx : x.val = p.1.1.val <;> by_cases hy : y.val = p.1.1.val <;>
    simp only [hx, hy, if_true, if_false] at h <;> omega

/-- Die Verschiebung `M₁`. -/
def shiftBefore (p : Pairs m) : Fin m → Fin m → Fin m := ofChoices m (ofKey (keyBefore p))

/-- Die Verschiebung `M₂`. -/
def shiftAfter (p : Pairs m) : Fin m → Fin m → Fin m := ofChoices m (ofKey (keyAfter p))

/-- **A3.** `min`, `max` und beide Verschiebungen sind transitiv — alle vier über eine
injektive Schlüsselfunktion. -/
theorem basis_transitive (p : Pairs m) :
    IsTransitiveOp (ofChoices m (ofKey minKey)) ∧ IsTransitiveOp (ofChoices m (ofKey maxKey)) ∧
      IsTransitiveOp (shiftBefore p) ∧ IsTransitiveOp (shiftAfter p) :=
  ⟨ofKey_transitive _ minKey_inj, ofKey_transitive _ maxKey_inj,
    ofKey_transitive _ (keyBefore_inj p), ofKey_transitive _ (keyAfter_inj p)⟩

theorem ofKey_minKey (q : Pairs m) : ofKey minKey q = false := by
  unfold ofKey minKey
  have := q.2
  exact decide_eq_false (by rw [Fin.lt_def] at this; omega)

theorem ofKey_maxKey (q : Pairs m) : ofKey maxKey q = true := by
  unfold ofKey maxKey
  have h := q.2
  have := q.1.2.isLt
  exact decide_eq_true (by rw [Fin.lt_def] at h; omega)

/-! ## Teil 5 — Anfang und Schritt -/

/-- Der Wahlvektor mit genau einem `max`-Paar. -/
def singleC (p : Pairs m) : Pairs m → Bool := fun q => decide (q = p)

/-- Die Paare stimmen genau dann überein, wenn ihre Werte übereinstimmen. -/
theorem pairs_eq_iff (q p : Pairs m) : q = p ↔ q.1.1.val = p.1.1.val ∧ q.1.2.val = p.1.2.val := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    exact Subtype.ext (Prod.ext (Fin.ext h1) (Fin.ext h2))

/-- Die Bit-Rechnung des Anfangs, auf `ℕ`. -/
theorem base_bits (a b i j : ℕ) (hab : a < b) (hij : i < j) :
    ((if b = j then 2 * i + 1 else 2 * b + 2) < (if a = j then 2 * i + 1 else 2 * a + 2) ∧
      (if b = i then 2 * j + 3 else 2 * b + 2) < (if a = i then 2 * j + 3 else 2 * a + 2))
      ↔ (a = i ∧ b = j) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩ <;> split_ifs at h1 h2 <;> omega
  · rintro ⟨rfl, rfl⟩
    refine ⟨?_, ?_⟩ <;> split_ifs <;> omega

/-- **H2 auf Bits.** Die Mehrheit aus `min` und den zwei Verschiebungen zum Paar `p` ist der
Wahlvektor mit genau dem `max`-Paar `p`. -/
theorem base_majC (p q : Pairs m) :
    majC (fun _ => false) (ofKey (keyBefore p)) (ofKey (keyAfter p)) q = singleC p q := by
  have hb := base_bits q.1.1.val q.1.2.val p.1.1.val p.1.2.val
    (by have := q.2; rwa [Fin.lt_def] at this) (by have := p.2; rwa [Fin.lt_def] at this)
  have hq := pairs_eq_iff q p
  unfold majC singleC ofKey keyBefore keyAfter
  by_cases hB : (if q.1.2.val = p.1.2.val then 2 * p.1.1.val + 1 else 2 * q.1.2.val + 2) <
      (if q.1.1.val = p.1.2.val then 2 * p.1.1.val + 1 else 2 * q.1.1.val + 2) <;>
    by_cases hA : (if q.1.2.val = p.1.1.val then 2 * p.1.2.val + 3 else 2 * q.1.2.val + 2) <
      (if q.1.1.val = p.1.1.val then 2 * p.1.2.val + 3 else 2 * q.1.1.val + 2)
  · have e : q = p := hq.mpr (hb.mp ⟨hB, hA⟩)
    rw [decide_eq_true hB, decide_eq_true hA, decide_eq_true e]; rfl
  · have e : q ≠ p := fun e => hA (hb.mpr (hq.mp e)).2
    rw [decide_eq_true hB, decide_eq_false hA, decide_eq_false e]; rfl
  · have e : q ≠ p := fun e => hB (hb.mpr (hq.mp e)).1
    rw [decide_eq_false hB, decide_eq_true hA, decide_eq_false e]; rfl
  · have e : q ≠ p := fun e => hB (hb.mpr (hq.mp e)).1
    rw [decide_eq_false hB, decide_eq_false hA, decide_eq_false e]; rfl

/-- **H2, der Anfang.** Die Operation mit genau einem `max`-Paar `p` ist `min` der zwei
Verschiebungen zu `p`. -/
theorem base_eq (p : Pairs m) (a b : Fin m) :
    ofChoices m (singleC p) a b = min (shiftBefore p a b) (shiftAfter p a b) := by
  rw [← ofChoices_false, shiftBefore, shiftAfter, comp_eq_maj]
  exact ofChoices_congr (fun q => (base_majC p q).symm) a b

/-- Ein `max`-Paar auf `min` zurückgesetzt. -/
def resetC (c : Pairs m → Bool) (p : Pairs m) : Pairs m → Bool :=
  fun q => if q = p then false else c q

/-- **H3 auf Bits.** -/
theorem step_majC (c : Pairs m → Bool) {p₁ p₂ : Pairs m} (hne : p₁ ≠ p₂)
    (h₁ : c p₁ = true) (h₂ : c p₂ = true) (q : Pairs m) :
    majC (fun _ => true) (resetC c p₁) (resetC c p₂) q = c q := by
  unfold majC resetC
  by_cases e1 : q = p₁
  · subst e1
    simp only [if_true, hne, if_false, h₁, Bool.false_eq_true]
  · by_cases e2 : q = p₂
    · subst e2
      simp only [e1, if_false, if_true, h₂, Bool.true_eq_false]
    · simp only [e1, e2, if_false, if_true]

/-- **H3, der Schritt.** Mit zwei verschiedenen `max`-Paaren ist die Operation `max` der zwei
Operationen, in denen je eines davon zurückgesetzt ist. -/
theorem step_eq (c : Pairs m → Bool) {p₁ p₂ : Pairs m} (hne : p₁ ≠ p₂)
    (h₁ : c p₁ = true) (h₂ : c p₂ = true) (a b : Fin m) :
    ofChoices m c a b = max (ofChoices m (resetC c p₁) a b) (ofChoices m (resetC c p₂) a b) := by
  rw [← ofChoices_true, comp_eq_maj]
  exact ofChoices_congr (fun q => (step_majC c hne h₁ h₂ q).symm) a b


/-! ## Teil 6 — Die Induktion über eine Liste der Paare

Die Induktion läuft über die Zahl der `max`-Paare, gezählt in einer **expliziten Liste**
der Paare und nicht über `Fintype (Pairs m)` — `Fin.fintype` trägt `Classical.choice` selbst
(Vorab-Bauprobe P2 der Spec). -/

/-- Alle Paare `a < b` auf `Fin m`, als Liste. -/
def pairList (m : ℕ) : List (Pairs m) :=
  (List.finRange m).flatMap fun a =>
    (List.finRange m).filterMap fun b => if h : a < b then some ⟨(a, b), h⟩ else none

theorem mem_pairList (p : Pairs m) : p ∈ pairList m := by
  unfold pairList
  rw [List.mem_flatMap]
  refine ⟨p.1.1, List.mem_finRange _, ?_⟩
  rw [List.mem_filterMap]
  exact ⟨p.1.2, List.mem_finRange _, by rw [dif_pos p.2]⟩

/-- Die Zahl der `max`-Paare eines Wahlvektors. -/
def maxCount (c : Pairs m → Bool) : ℕ := ((pairList m).filter c).length

theorem filter_length_le {α : Type*} (l : List α) (c c' : α → Bool)
    (himp : ∀ x, c' x = true → c x = true) :
    (l.filter c').length ≤ (l.filter c).length := by
  induction l with
  | nil => exact Nat.le_refl 0
  | cons y l ih =>
    rw [List.filter_cons, List.filter_cons]
    by_cases h' : c' y = true
    · rw [if_pos h', if_pos (himp y h')]
      exact Nat.succ_le_succ ih
    · rw [if_neg h']
      by_cases h : c y = true
      · rw [if_pos h]; exact Nat.le_succ_of_le ih
      · rw [if_neg h]; exact ih

theorem filter_length_lt {α : Type*} (l : List α) (c c' : α → Bool)
    (himp : ∀ x, c' x = true → c x = true) {x : α} (hx : x ∈ l)
    (hc : c x = true) (hc' : c' x = false) :
    (l.filter c').length < (l.filter c).length := by
  induction l with
  | nil => exact absurd hx List.not_mem_nil
  | cons y l ih =>
    rw [List.filter_cons, List.filter_cons]
    rcases List.mem_cons.mp hx with rfl | hl
    · rw [if_neg (by rw [hc']; exact Bool.false_ne_true), if_pos hc]
      exact Nat.lt_succ_of_le (filter_length_le l c c' himp)
    · have := ih hl
      by_cases h' : c' y = true
      · rw [if_pos h', if_pos (himp y h')]
        exact Nat.succ_lt_succ this
      · rw [if_neg h']
        by_cases h : c y = true
        · rw [if_pos h]; exact Nat.lt_succ_of_lt this
        · rw [if_neg h]; exact this

theorem maxCount_resetC_lt (c : Pairs m → Bool) {p : Pairs m} (hp : c p = true) :
    maxCount (resetC c p) < maxCount c := by
  unfold maxCount
  refine filter_length_lt _ c (resetC c p) ?_ (mem_pairList p) hp ?_
  · intro x hx
    unfold resetC at hx
    by_cases e : x = p
    · rw [if_pos e] at hx; exact absurd hx Bool.false_ne_true
    · rwa [if_neg e] at hx
  · unfold resetC; rw [if_pos rfl]

/-- **Der Zielsatz Z.** Erhält `R` die Operationen `min` und `max` und alle
Verschiebungen, so erhält `R` jede lokal-klassische Operation auf `Fin m` — jeden
Wahlvektor. `R` hat beliebige Stelligkeit `ι`. -/
theorem preserves_all_of_basis {ι : Type u} (R : Set (ι → Fin m))
    (hmin : Preserves R (fun a b => min a b)) (hmax : Preserves R (fun a b => max a b))
    (hshift : ∀ p : Pairs m, Preserves R (shiftBefore p) ∧ Preserves R (shiftAfter p)) :
    ∀ c : Pairs m → Bool, Preserves R (ofChoices m c) := by
  suffices H : ∀ n : ℕ, ∀ c : Pairs m → Bool, maxCount c = n → Preserves R (ofChoices m c) from
    fun c => H _ c rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro c hc
    cases hany : (pairList m).any c with
    | false =>
      have hall : ∀ q, c q = false := by
        intro q
        rw [List.any_eq_false] at hany
        exact Bool.eq_false_iff.mpr (hany q (mem_pairList q))
      refine preserves_congr (fun a b => ?_) hmin
      rw [ofChoices_congr hall, ofChoices_false]
    | true =>
      obtain ⟨p₁, -, h₁⟩ := List.any_eq_true.mp hany
      cases hany2 : (pairList m).any (fun q => c q && !decide (q = p₁)) with
      | false =>
        have hsingle : ∀ q, c q = singleC p₁ q := by
          intro q
          rw [List.any_eq_false] at hany2
          have hq := hany2 q (mem_pairList q)
          unfold singleC
          by_cases e : q = p₁
          · rw [e, h₁, decide_eq_true rfl]
          · rw [decide_eq_false e]
            cases hcq : c q
            · rfl
            · exact absurd (by rw [hcq, decide_eq_false e]; rfl) hq
        refine preserves_congr (fun a b => ?_)
          (preserves_comp hmin (hshift p₁).1 (hshift p₁).2)
        rw [ofChoices_congr hsingle, base_eq]
      | true =>
        obtain ⟨p₂, -, h₂⟩ := List.any_eq_true.mp hany2
        have hc₂ : c p₂ = true := (Bool.and_eq_true _ _).mp h₂ |>.1
        have hne : p₁ ≠ p₂ := by
          intro e
          have := (Bool.and_eq_true _ _).mp h₂ |>.2
          rw [e, decide_eq_true rfl] at this
          exact Bool.false_ne_true this
        refine preserves_congr (fun a b => step_eq c hne h₁ hc₂ a b)
          (preserves_comp hmax (ih _ ?_ _ rfl) (ih _ ?_ _ rfl))
        · rw [← hc]; exact maxCount_resetC_lt c h₁
        · rw [← hc]; exact maxCount_resetC_lt c hc₂

/-- **Z', das Korollar.** Erhält `R` alle transitiven lokal-klassischen Operationen, so
erhält `R` alle lokal-klassischen. Keine Relation beliebiger Stelligkeit trennt die
zyklischen von den transitiven — für jedes `m`. -/
theorem no_relation_separates_general {ι : Type u} (R : Set (ι → Fin m))
    (h : ∀ o : Fin m → Fin m → Fin m, LocallyClassical o → IsTransitiveOp o → Preserves R o) :
    ∀ o : Fin m → Fin m → Fin m, LocallyClassical o → Preserves R o := by
  have hbasis : ∀ k : Fin m → ℕ, (∀ x y, k x = k y → x = y) →
      Preserves R (ofChoices m (ofKey k)) :=
    fun k hk => h _ (ofChoices_locallyClassical m _) (ofKey_transitive k hk)
  have hmin : Preserves R (fun a b => min a b) :=
    preserves_congr (fun a b => by rw [ofChoices_congr ofKey_minKey, ofChoices_false])
      (hbasis minKey minKey_inj)
  have hmax : Preserves R (fun a b => max a b) :=
    preserves_congr (fun a b => by rw [ofChoices_congr ofKey_maxKey, ofChoices_true])
      (hbasis maxKey maxKey_inj)
  have hall := preserves_all_of_basis R hmin hmax
    (fun p => ⟨hbasis _ (keyBefore_inj p), hbasis _ (keyAfter_inj p)⟩)
  intro o ho
  have e := congrArg Subtype.val ((locallyClassicalEquiv m).left_inv ⟨o, ho⟩)
  simp only at e
  rw [← e]
  exact hall _


/-! ## Teil 7 — A8: die Divergenz zur E-Reihe als Satz -/

/-- Die Invariante `R m` der E-Reihe als Menge binärer Tupel. -/
def relSet (m : ℕ) : Set (Fin 2 → Fin m) := {v | R m (v 0) (v 1)}

/-- Das koordinatenweise Erhaltungsprädikat der E-Reihe ist `Preserves` auf `relSet`. -/
theorem preservesR_iff (f : Fin m → Fin m → Fin m) :
    PreservesR m f ↔ Preserves (relSet m) f := by
  constructor
  · intro h a ha b hb
    exact h (a 0) (a 1) (b 0) (b 1) ha hb
  · intro h x y u v hxy huv
    exact h ![x, y] hxy ![u, v] huv

/-- **A8, die Divergenz.** Für `m ≥ 4` wird die Invariante `R m` der E-Reihe von `min` und
`max` erhalten, aber **nicht** von allen Verschiebungen. Die Basis des Zielsatzes trennt
sich damit von der Erzeugungsbasis `{min, max, neg}`. Beweis ohne neue Rechnung: erhielte
`R m` alle Verschiebungen, so nach `preserves_all_of_basis` jede lokal-klassische
Operation, und nach `preserving_is_min_or_max` (E3) wäre jede davon `min` oder `max`. -/
theorem divergence_from_clone_basis (hm : 4 ≤ m) :
    PreservesR m (fun a b => min a b) ∧ PreservesR m (fun a b => max a b) ∧
      ¬ ∀ p : Pairs m, PreservesR m (shiftBefore p) ∧ PreservesR m (shiftAfter p) := by
  refine ⟨min_pres, max_pres, fun hs => ?_⟩
  have hall := preserves_all_of_basis (relSet m) ((preservesR_iff _).mp min_pres)
    ((preservesR_iff _).mp max_pres)
    (fun p => ⟨(preservesR_iff _).mp (hs p).1, (preservesR_iff _).mp (hs p).2⟩)
  let x0 : Fin m := ⟨0, by omega⟩
  let x1 : Fin m := ⟨1, by omega⟩
  let x2 : Fin m := ⟨2, by omega⟩
  have h01 : x0 < x1 := Fin.mk_lt_mk.mpr (by omega)
  have h12 : x1 < x2 := Fin.mk_lt_mk.mpr (by omega)
  let p01 : Pairs m := ⟨(x0, x1), h01⟩
  have hne : (⟨(x1, x2), h12⟩ : Pairs m) ≠ p01 := by
    intro e
    have h := congrArg (fun q : Pairs m => q.1.1.val) e
    exact absurd h (show ¬ (1 : ℕ) = 0 by omega)
  rcases preserving_is_min_or_max hm (ofChoices_locallyClassical m (singleC p01))
      ((preservesR_iff _).mpr (hall (singleC p01))) with e | e
  · have v := congrFun (congrFun e x0) x1
    rw [(ofChoices_pair m _ h01).1] at v
    have hs : singleC p01 p01 = true := decide_eq_true rfl
    rw [if_pos hs, max_eq_right h01.le, min_eq_left h01.le] at v
    exact absurd (congrArg Fin.val v) (by simp only [x0, x1]; omega)
  · have v := congrFun (congrFun e x1) x2
    rw [(ofChoices_pair m _ h12).1] at v
    have hs : singleC p01 ⟨(x1, x2), h12⟩ = false := decide_eq_false hne
    rw [hs, if_neg (by decide), max_eq_right h12.le, min_eq_left h12.le] at v
    exact absurd (congrArg Fin.val v) (by simp only [x1, x2]; omega)


/-! ## Eichung an `m = 3` (Spec §5)

Die zwei Verschiebungen zum Paar `(0,2)` sind in der Schreibweise des C2-Moduls (Reihenfolge
`{0,1}`, `{1,2}`, `{0,2}`, D = `max`) die Muster `KDD` und `DKD`; ihr `min` ist `KKD`. -/

/-- Die `max`-Paare eines Wahlvektors, als Wertpaare. -/
def maxPairs (m : ℕ) (c : Pairs m → Bool) : List (ℕ × ℕ) :=
  ((pairList m).filter c).map fun q => (q.1.1.val, q.1.2.val)

/-- Das Paar `(0,2)` auf `Fin 3`. -/
def p02 : Pairs 3 := ⟨((0 : Fin 3), (2 : Fin 3)), by decide⟩

/-- info: [(0, 2), (1, 2)] -/
#guard_msgs in #eval maxPairs 3 (ofKey (keyBefore p02))
/-- info: [(0, 1), (0, 2)] -/
#guard_msgs in #eval maxPairs 3 (ofKey (keyAfter p02))
/-- info: [(0, 2)] -/
#guard_msgs in #eval maxPairs 3 (majC (fun _ => false) (ofKey (keyBefore p02)) (ofKey (keyAfter p02)))


/-! ## Wachen -/

/-- info: 'Reformulation.Proemial.LocalOpInseparability.preserves_comp' does not depend on any axioms -/
#guard_msgs in #print axioms preserves_comp

/-- info: 'Reformulation.Proemial.LocalOpInseparability.preserves_congr' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms preserves_congr

/-- info: 'Reformulation.Proemial.LocalOpInseparability.comp_eq_maj' depends on axioms: [propext] -/
#guard_msgs in #print axioms comp_eq_maj

/-- info: 'Reformulation.Proemial.LocalOpInseparability.ofChoices_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ofChoices_congr

/-- info: 'Reformulation.Proemial.LocalOpInseparability.ofChoices_ofKey' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ofChoices_ofKey

/-- info: 'Reformulation.Proemial.LocalOpInseparability.ofKey_transitive' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ofKey_transitive

/-- info: 'Reformulation.Proemial.LocalOpInseparability.ofChoices_false' depends on axioms: [propext] -/
#guard_msgs in #print axioms ofChoices_false

/-- info: 'Reformulation.Proemial.LocalOpInseparability.ofChoices_true' depends on axioms: [propext] -/
#guard_msgs in #print axioms ofChoices_true

/-- info: 'Reformulation.Proemial.LocalOpInseparability.minKey_inj' does not depend on any axioms -/
#guard_msgs in #print axioms minKey_inj

/-- info: 'Reformulation.Proemial.LocalOpInseparability.maxKey_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms maxKey_inj

/-- info: 'Reformulation.Proemial.LocalOpInseparability.keyBefore_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms keyBefore_inj

/-- info: 'Reformulation.Proemial.LocalOpInseparability.keyAfter_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms keyAfter_inj

/-- info: 'Reformulation.Proemial.LocalOpInseparability.basis_transitive' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms basis_transitive

/-- info: 'Reformulation.Proemial.LocalOpInseparability.ofKey_minKey' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ofKey_minKey

/-- info: 'Reformulation.Proemial.LocalOpInseparability.ofKey_maxKey' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ofKey_maxKey

/-- info: 'Reformulation.Proemial.LocalOpInseparability.pairs_eq_iff' does not depend on any axioms -/
#guard_msgs in #print axioms pairs_eq_iff

/-- info: 'Reformulation.Proemial.LocalOpInseparability.base_bits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms base_bits

/-- info: 'Reformulation.Proemial.LocalOpInseparability.base_majC' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms base_majC

/-- info: 'Reformulation.Proemial.LocalOpInseparability.base_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms base_eq

/-- info: 'Reformulation.Proemial.LocalOpInseparability.step_majC' depends on axioms: [propext] -/
#guard_msgs in #print axioms step_majC

/-- info: 'Reformulation.Proemial.LocalOpInseparability.step_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms step_eq

/-- info: 'Reformulation.Proemial.LocalOpInseparability.mem_pairList' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms mem_pairList

/-- info: 'Reformulation.Proemial.LocalOpInseparability.filter_length_le' depends on axioms: [propext] -/
#guard_msgs in #print axioms filter_length_le

/-- info: 'Reformulation.Proemial.LocalOpInseparability.filter_length_lt' depends on axioms: [propext] -/
#guard_msgs in #print axioms filter_length_lt

/-- info: 'Reformulation.Proemial.LocalOpInseparability.maxCount_resetC_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms maxCount_resetC_lt

/-- info: 'Reformulation.Proemial.LocalOpInseparability.preserves_all_of_basis' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms preserves_all_of_basis

/-- info: 'Reformulation.Proemial.LocalOpInseparability.no_relation_separates_general' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms no_relation_separates_general

/-- info: 'Reformulation.Proemial.LocalOpInseparability.preservesR_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms preservesR_iff

/-- info: 'Reformulation.Proemial.LocalOpInseparability.divergence_from_clone_basis' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms divergence_from_clone_basis

end Reformulation.Proemial.LocalOpInseparability
