import Reformulation.Proemial.DeuteroCollapse
import Reformulation.Proemial.EmanationsZaehlung

/-!
# Proemial.VergroeberungMass — die Vergröberung als Maß, die Rückrechnung als Wahl

STANDALONE, NICHT im Aggregat;  Target `Probes`.  AxiomGate unberührt.  Sonde nach `KorpusRev2/Prompt_Instanz_Sonde_Vergroeberung_Mass_Wahl.md`
(Mathematiker, 30.10.2026 14:11;  Architekt 14:10).  Konsumiert `A3CoarseningProbe` (`proto`, `deutero`, `coarsening_factors`), `DeuteroCollapse`
(`deutero_of_perm`), `EmanationsZaehlung` (`sortiert`, `groessen`, `teile`, `deuteroZahl`, EM3);  ändert nichts davon.

**Namen (Regel 9):**  alle neuen Namen vor der Definition über `Reformulation/` und `Foreign/` geprüft;  0 Treffer.

## WAS

```text
V1  faser_formel        EICHUNG n ≤ 8     die Faser über jeder Partition λ hat n! / (∏ λᵢ! ∏ mⱼ!) Elemente, und die Division geht auf.
    faser_summe         EICHUNG n ≤ 8     jede Normalform liegt über einer Partition;  die Fasergrößen summieren sich zur Zahl der Normalformen.
                                          ALLGEMEIN NICHT BEWIESEN:  nicht billig (Bahn-Stabilisator über Mengenpartitionen).  Rechnung bis n = 10
                                          außerhalb des Baums (T_Vorprobe_Skripte/Vergroeberung_Mass.out)
V2  einer_fasern        SATZ, jede Länge  die Faser von deutero über r hat genau ein Element  ⟺  deutero r = {n} ∨ deutero r = (1,…,1)
    faser_konstant, faser_diskret         die zwei Einer-Fasern:  nur 0 0 … 0  bzw. nur 0 1 … (n−1)
V3  rueckrechnung_wahl  SATZ, jede Länge  es gibt genau einen Schnitt  ⟺  n ≤ 2
    injektiv_iff        SATZ, jede Länge  deutero ist auf RGS n injektiv  ⟺  n ≤ 2
    zwei_schnitte       SATZ, n ≥ 3       zwei verschiedene Schnitte, beide angegeben (schnittBlock, schnittTausch)
V4  schnitte_zahl       EICHUNG n ≤ 6     1, 1, 3, 72, 75000, 164025000000
    waehlen_length, mem_waehlen, schnitte_length   SATZ, allgemein:  Schnitte in Listenform = je Faser ein Element;  ihre Zahl = Produkt der Fasergrößen
V5  proto_faser_zahl    SATZ, jede Länge  die Faser von proto über k hat auf der Deutero-Ebene deuteroZahl n k Elemente (teilListe)
    proto_faser_bild    EICHUNG n ≤ 7     diese Partitionen sind die Bilder der Normalformen mit k Klassen (aus deutero_bild neu gefahren, mit Menge)
    proto_fasern        EICHUNG n = 4…12  Einer-Fasern genau bei k ∈ {1, n−1, n};  EM3 zitiert (deutero_eins, deutero_eins_rueck)
```

Brücken:  `deutero_coe`, `deutero_eq_groessen`, `deutero_gleich_iff`, `proto_eq_klassenZahl`, `faser_ist_faser`.

**Wie V2 und V3 gehen.**  Über jeder Klassengrößen-Liste `c :: d :: t` mit `c ≥ 2` stehen zwei Normalformen, die Blockfolge `0^c 1^d 2^… ` und die
Tauschfolge `0^(c−1) 1 0 1^(d−1) 2^…`.  Sie sind Permutationen voneinander (`tausch_perm`), darum dieselbe Vergröberung (`deutero_of_perm`),
und verschieden (`tausch_ne`).  Sortiert steht die größte Klasse vorn, darum gibt es zu jedem Zeichen außer `(n)` und `(1,…,1)` zwei
(`schnitte_trennen`).  Kein `relabel`.

**Zwei Fassungen von „Schnitt", mit Absicht.**  V3 führt die Funktion `σ : Bild n → RGS n` (`IstSchnitt`);  V4 die Liste „je Partition ein
Element der Faser" (`schnitte`), weil nur sie zählbar ist.  Die Verbindung ist `faser_ist_faser`;  ein Satz „Funktionen ≃ Listen" steht NICHT hier.

**Profile:**  kein Satz trägt `Classical.choice` (Wachen unten).  Zwei Stellen waren zu umgehen:  `deutero_not_injective_general` trägt Choice
(über `w_perm`) und wird darum nicht konsumiert, nur `deutero_of_perm`;  `mem_rgsList_iff` trägt Choice und ist hier als `mem_rgsList_frei` ohne
offenes `simp` neu bewiesen (Kenogram/Basic bleibt unberührt).  Kein `native_decide`, kein `sorry`, kein True-Feld, keine reelle Zahl.

**Gerechnet, kein Satz (außerhalb des Baums, `T_Vorprobe_Skripte/Vergroeberung_Mass.out`):**  der Verlust in Bit bei Gleichverteilung auf Trito,
n = 1…10:  0, 0, 0.951, 1.884, 3.267, 4.784, 6.504, 8.362, 10.370, 12.492.

**Was die Zahlen erzwingt (Regel 11):**  die Faserformel ist die Zahl der Mengenpartitionen vom Typ λ, Standardkombinatorik;  die Schnittzahl ist ihr
Produkt (`schnitte_length`).  Beides ist Arithmetik, kein Indiz für eine Quelle.  Die Schwelle n ≤ 2 erzwingt `einer_fasern`:  erst ab drei Stellen
gibt es ein λ außer (n) und (1,…,1).

**Ertrag:**  FOLGERUNG sind V2 und V3.  V1, V4 sind Eichungen über einer allgemeinen Zählung, V5 ZUSAMMENSTELLUNG aus EM3 und `teilListe_length`.

## QUELLE

Günther, Lille 1968 S. 17 („Kulturen … mit Entropie belastete Systeme");  BdM S. 156 f. (Entropiesatz:  „reversibel, wenn er sich auf Teilsysteme
bezieht, im Hinblick auf das Ganze … irreversibel") — TEXTSCHICHT;  am Bild:  Hermeneutes, ausstehend.

## UNSER

Das Maß (Fasergröße, Schnittzahl, Bit);  die Lesung „Rückrechnung = Schnitt der Vergröberung".

## LESART (nicht im Lean)

Dass dies Günthers Entropie trifft;  „Kulturen".

## NICHT

Kein Satz über Entropie im physikalischen Sinn;  kein Wort über Kulturen, Geschichte, Wille, Freiheit;  „Wahl" ist hier nur „mehr als ein Schnitt",
kein Subjekt;  nicht Rev11.
-/

namespace Reformulation.Proemial.VergroeberungMass

open Reformulation.Kenogram
open Reformulation.Proemial.A3CoarseningProbe (proto deutero coarsening_factors)
open Reformulation.Proemial.DeuteroCollapse (deutero_of_perm)
open Reformulation.Proemial.EmanationsZaehlung
  (einfuegen sortiert groessen klassenZahl teile deuteroZahl deutero_bild deutero_eins deutero_eins_rueck)

/-! ## Die Klassengrößen einer Folge -/

/-- Wie oft der Wert `v` in `l` steht;  dieselbe Zählung, die `deutero` führt. -/
def anzahl (l : List ℕ) (v : ℕ) : ℕ := (l.filter (· = v)).length

/-- Die Klassengrößen in der Reihenfolge der Werte. -/
def zaehlen (l : List ℕ) : List ℕ := (List.range (l.foldr max 0 + 1)).map (anzahl l)

theorem deutero_coe {n : ℕ} (r : RGS n) : deutero r = ((zaehlen r.val : List ℕ) : Multiset ℕ) := rfl

theorem anzahl_cons (a : ℕ) (l : List ℕ) (v : ℕ) :
    anzahl (a :: l) v = (if a = v then 1 else 0) + anzahl l v := by
  unfold anzahl
  rw [List.filter_cons]
  by_cases h : a = v
  · rw [if_pos (decide_eq_true h), if_pos h, List.length_cons, Nat.add_comm]
  · rw [if_neg (by rw [decide_eq_false h]; exact Bool.false_ne_true), if_neg h, Nat.zero_add]

theorem anzahl_append (l l' : List ℕ) (v : ℕ) : anzahl (l ++ l') v = anzahl l v + anzahl l' v := by
  unfold anzahl
  rw [List.filter_append, List.length_append]

theorem anzahl_rep_self (c k : ℕ) : anzahl (List.replicate c k) k = c := by
  induction c with
  | zero => rfl
  | succ c ih => rw [List.replicate_succ, anzahl_cons, if_pos rfl, ih, Nat.add_comm]

theorem anzahl_rep_ne {k v : ℕ} (c : ℕ) (h : k ≠ v) : anzahl (List.replicate c k) v = 0 := by
  induction c with
  | zero => rfl
  | succ c ih => rw [List.replicate_succ, anzahl_cons, if_neg h, ih]

theorem anzahl_pos {l : List ℕ} {v : ℕ} (h : v ∈ l) : 1 ≤ anzahl l v := by
  induction l with
  | nil => exact absurd h List.not_mem_nil
  | cons a t ih =>
    rw [anzahl_cons]
    rcases List.mem_cons.mp h with rfl | ht
    · rw [if_pos rfl]; exact Nat.le_add_right 1 _
    · exact Nat.le_trans (ih ht) (Nat.le_add_left _ _)

theorem le_foldr_max {l : List ℕ} {x : ℕ} (h : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => exact absurd h List.not_mem_nil
  | cons a t ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | ht
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih ht) (Nat.le_max_right _ _)

theorem summe_add (L : List ℕ) (f g : ℕ → ℕ) :
    (L.map (fun v => f v + g v)).sum = (L.map f).sum + (L.map g).sum := by
  induction L with
  | nil => rfl
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih]; omega

theorem summe_ite (a m : ℕ) :
    ((List.range m).map (fun v => if a = v then 1 else 0)).sum = if a < m then 1 else 0 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    split_ifs <;> omega

/-- Die Klassengrößen zerlegen die Länge. -/
theorem summe_anzahl (m : ℕ) : ∀ l : List ℕ, (∀ x ∈ l, x < m) →
    ((List.range m).map (anzahl l)).sum = l.length
  | [], _ => by
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih (fun _ h => absurd h List.not_mem_nil)]
      rfl
  | a :: t, h => by
    have hf : anzahl (a :: t) = fun v => (if a = v then 1 else 0) + anzahl t v :=
      funext (anzahl_cons a t)
    rw [hf, summe_add, summe_ite, if_pos (h a List.mem_cons_self),
      summe_anzahl m t (fun x hx => h x (List.mem_cons_of_mem _ hx)), List.length_cons, Nat.add_comm]

theorem summe_zaehlen (l : List ℕ) : (zaehlen l).sum = l.length :=
  summe_anzahl _ l (fun _ hx => Nat.lt_succ_of_le (le_foldr_max hx))

/-! ## Dichte und Einmaligkeit einer Normalform -/

theorem lauf_dicht : ∀ (l : List ℕ) (m : ℕ), isRGSAux m true l = true →
    ∀ v, m < v → v ≤ l.foldr max 0 → v ∈ l
  | [], _, _, _, h1, h2 => by
    rw [List.foldr_nil] at h2
    exact absurd (Nat.lt_of_lt_of_le h1 h2) (Nat.not_lt_zero _)
  | a :: t, m, h, v, h1, h2 => by
    rw [isRGSAux, Bool.and_eq_true] at h
    have ha : a ≤ m + 1 := of_decide_eq_true h.1
    rw [List.foldr_cons] at h2
    by_cases hv : v = a
    · rw [hv]; exact List.mem_cons_self
    · have h3 : max m a < v := by omega
      have h4 : v ≤ t.foldr max 0 := by omega
      exact List.mem_cons_of_mem _ (lauf_dicht t _ h.2 v h3 h4)

theorem rgs_dicht {l : List ℕ} (h : IsRGS l) (hne : l ≠ []) (v : ℕ) (hv : v ≤ l.foldr max 0) : v ∈ l := by
  cases l with
  | nil => exact absurd rfl hne
  | cons a t =>
    unfold IsRGS at h
    rw [isRGSAux, Bool.and_eq_true] at h
    have ha : a = 0 := of_decide_eq_true h.1
    subst ha
    cases v with
    | zero => exact List.mem_cons_self
    | succ v =>
      rw [List.foldr_cons] at hv
      have h4 : v + 1 ≤ t.foldr max 0 := by omega
      exact List.mem_cons_of_mem _ (lauf_dicht t 0 h.2 (v + 1) (Nat.succ_pos v) h4)

/-- In einer nichtleeren Normalform hat jede Klasse mindestens ein Element. -/
theorem zaehlen_pos {l : List ℕ} (h : IsRGS l) (hne : l ≠ []) : ∀ c ∈ zaehlen l, 1 ≤ c := by
  intro c hc
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hc
  exact anzahl_pos (rgs_dicht h hne v (Nat.le_of_lt_succ (List.mem_range.mp hv)))

theorem lauf_nodup : ∀ (l : List ℕ) (m : ℕ), isRGSAux m true l = true →
    (∀ x ∈ l, m < x) → l.Nodup → l = List.range' (m + 1) l.length
  | [], _, _, _, _ => rfl
  | a :: t, m, h, hx, hn => by
    rw [isRGSAux, Bool.and_eq_true] at h
    have ha : a ≤ m + 1 := of_decide_eq_true h.1
    have hb : m < a := hx a List.mem_cons_self
    have hc : a = m + 1 := by omega
    subst hc
    have hmax : max m (m + 1) = m + 1 := Nat.max_eq_right (Nat.le_succ m)
    have h2 := h.2
    rw [hmax] at h2
    obtain ⟨hna, hnt⟩ := List.nodup_cons.mp hn
    have hrec := lauf_nodup t (m + 1) h2 (fun x hxt => by
      have h5 : m < x := hx x (List.mem_cons_of_mem _ hxt)
      have h6 : x ≠ m + 1 := fun he => hna (he ▸ hxt)
      omega) hnt
    rw [List.length_cons]
    show _ = (m + 1) :: List.range' (m + 1 + 1) t.length
    rw [← hrec]

theorem nodup_of_anzahl : ∀ l : List ℕ, (∀ x ∈ l, anzahl l x ≤ 1) → l.Nodup
  | [], _ => List.nodup_nil
  | a :: t, h => by
    refine List.nodup_cons.mpr ⟨fun hat => ?_, nodup_of_anzahl t (fun x hx => ?_)⟩
    · have h1 := h a List.mem_cons_self
      rw [anzahl_cons, if_pos rfl] at h1
      have h2 := anzahl_pos hat
      omega
    · have h1 := h x (List.mem_cons_of_mem _ hx)
      rw [anzahl_cons] at h1
      omega

/-- Eine Normalform, in der jeder Wert nur einmal steht, ist `0 1 2 … (n−1)`. -/
theorem rgs_nodup {l : List ℕ} (h : IsRGS l) (hn : l.Nodup) : l = List.range' 0 l.length := by
  cases l with
  | nil => rfl
  | cons a t =>
    unfold IsRGS at h
    rw [isRGSAux, Bool.and_eq_true] at h
    have ha : a = 0 := of_decide_eq_true h.1
    subst ha
    obtain ⟨hna, hnt⟩ := List.nodup_cons.mp hn
    have hrec := lauf_nodup t 0 h.2 (fun x hxt => by
      have h6 : x ≠ 0 := fun he => hna (he ▸ hxt)
      omega) hnt
    rw [List.length_cons]
    show _ = 0 :: List.range' 1 t.length
    rw [← hrec]

/-! ## Sortieren:  die Klassengrößen als Zeichen der Vergröberung -/

theorem einfuegen_perm (a : ℕ) : ∀ l : List ℕ, (einfuegen a l).Perm (a :: l)
  | [] => List.Perm.refl _
  | b :: t => by
    unfold einfuegen
    split
    · exact List.Perm.refl _
    · exact ((einfuegen_perm a t).cons b).trans (List.Perm.swap a b t)

theorem sortiert_perm : ∀ l : List ℕ, (sortiert l).Perm l
  | [] => List.Perm.refl _
  | a :: t => (einfuegen_perm a (sortiert t)).trans ((sortiert_perm t).cons a)

theorem einfuegen_pairwise (a : ℕ) : ∀ l : List ℕ, l.Pairwise (· ≥ ·) → (einfuegen a l).Pairwise (· ≥ ·)
  | [], _ => List.pairwise_singleton _ _
  | b :: t, h => by
    unfold einfuegen
    split
    · rename_i hba
      refine List.pairwise_cons.mpr ⟨fun x hx => ?_, h⟩
      rcases List.mem_cons.mp hx with rfl | hxt
      · exact hba
      · exact Nat.le_trans ((List.pairwise_cons.mp h).1 x hxt) hba
    · rename_i hba
      obtain ⟨h1, h2⟩ := List.pairwise_cons.mp h
      refine List.pairwise_cons.mpr ⟨fun x hx => ?_, einfuegen_pairwise a t h2⟩
      rcases List.mem_cons.mp ((einfuegen_perm a t).mem_iff.mp hx) with rfl | hxt
      · exact Nat.le_of_lt (Nat.lt_of_not_le hba)
      · exact h1 x hxt

theorem sortiert_pairwise : ∀ l : List ℕ, (sortiert l).Pairwise (· ≥ ·)
  | [] => List.Pairwise.nil
  | a :: t => einfuegen_pairwise a _ (sortiert_pairwise t)

theorem sortiert_eq_of_perm {l l' : List ℕ} (h : l.Perm l') : sortiert l = sortiert l' :=
  List.Perm.eq_of_pairwise (le := (· ≥ ·)) (fun {_ _} _ _ h3 h4 => Nat.le_antisymm h4 h3)
    (sortiert_pairwise l) (sortiert_pairwise l')
    (((sortiert_perm l).trans h).trans (sortiert_perm l').symm)

/-- Die sortierte Liste einer Multimenge;  über `sortiert` aus EmanationsZaehlung, ohne `Multiset.sort`. -/
def sortM (m : Multiset ℕ) : List ℕ := Quot.liftOn m sortiert (fun _ _ h => sortiert_eq_of_perm h)

theorem sortM_coe (l : List ℕ) : sortM (l : Multiset ℕ) = sortiert l := rfl

theorem coe_sortM (m : Multiset ℕ) : ((sortM m : List ℕ) : Multiset ℕ) = m :=
  Quot.inductionOn m (fun l => Multiset.coe_eq_coe.mpr (sortiert_perm l))

/-! ## Zwei Folgen über jeder Klassengrößen-Liste -/

/-- Die Blockfolge:  `c₀`-mal `k`, dann `c₁`-mal `k+1`, … -/
def bloecke : ℕ → List ℕ → List ℕ
  | _, [] => []
  | k, c :: t => List.replicate c k ++ bloecke (k + 1) t

/-- Die Tauschfolge:  in der Blockfolge die letzte `0` mit der ersten `1` vertauscht — wo das eine andere Normalform gibt. -/
def tausch : List ℕ → List ℕ
  | c :: d :: t =>
    if 2 ≤ c then List.replicate (c - 1) 0 ++ 1 :: 0 :: (List.replicate (d - 1) 1 ++ bloecke 2 t)
    else bloecke 0 (c :: d :: t)
  | a => bloecke 0 a

theorem tausch_cons (c d : ℕ) (t : List ℕ) : tausch (c :: d :: t) =
    if 2 ≤ c then List.replicate (c - 1) 0 ++ 1 :: 0 :: (List.replicate (d - 1) 1 ++ bloecke 2 t)
    else bloecke 0 (c :: d :: t) := rfl

theorem lauf_rep (j m : ℕ) (l : List ℕ) :
    isRGSAux m true (List.replicate j m ++ l) = isRGSAux m true l := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [List.replicate_succ, List.cons_append, isRGSAux, Nat.max_self, ih,
      decide_eq_true (Nat.le_succ m), Bool.true_and]

theorem lauf_bloecke : ∀ (a : List ℕ) (k : ℕ), (∀ c ∈ a, 1 ≤ c) → isRGSAux k true (bloecke (k + 1) a) = true
  | [], _, _ => rfl
  | 0 :: _, _, h => absurd (h 0 List.mem_cons_self) (by decide)
  | (c + 1) :: t, k, h => by
    rw [bloecke, List.replicate_succ, List.cons_append, isRGSAux, Nat.max_eq_right (Nat.le_succ k),
      decide_eq_true (Nat.le_refl (k + 1)), Bool.true_and, lauf_rep]
    exact lauf_bloecke t (k + 1) (fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem isRGS_bloecke (a : List ℕ) (h : ∀ c ∈ a, 1 ≤ c) : IsRGS (bloecke 0 a) := by
  cases a with
  | nil => exact rfl
  | cons c t =>
    cases c with
    | zero => exact absurd (h 0 List.mem_cons_self) (by decide)
    | succ c =>
      unfold IsRGS
      rw [bloecke, List.replicate_succ, List.cons_append, isRGSAux, decide_eq_true rfl, Bool.true_and,
        lauf_rep]
      exact lauf_bloecke t 0 (fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem isRGS_tausch (a : List ℕ) (h : ∀ c ∈ a, 1 ≤ c) : IsRGS (tausch a) := by
  match a, h with
  | [], _ => exact rfl
  | [c], h => exact isRGS_bloecke [c] h
  | c :: d :: t, h =>
    rw [tausch_cons]
    by_cases hc : 2 ≤ c
    · rw [if_pos hc]
      obtain ⟨c', rfl⟩ : ∃ c', c = c' + 2 := ⟨c - 2, by omega⟩
      unfold IsRGS
      rw [show c' + 2 - 1 = c' + 1 from rfl, List.replicate_succ, List.cons_append, isRGSAux,
        decide_eq_true rfl, Bool.true_and, lauf_rep, isRGSAux, Nat.max_eq_right (Nat.zero_le 1),
        decide_eq_true (Nat.le_refl 1), Bool.true_and, isRGSAux, Nat.max_eq_left (Nat.zero_le 1),
        decide_eq_true (Nat.zero_le 2), Bool.true_and, lauf_rep]
      exact lauf_bloecke t 1 (fun x hx => h x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)))
    · rw [if_neg hc]
      exact isRGS_bloecke _ h

theorem length_bloecke : ∀ (a : List ℕ) (k : ℕ), (bloecke k a).length = a.sum
  | [], _ => rfl
  | c :: t, k => by
    rw [bloecke, List.length_append, List.length_replicate, length_bloecke t, List.sum_cons]

theorem tausch_perm : ∀ a : List ℕ, (∀ c ∈ a, 1 ≤ c) → (tausch a).Perm (bloecke 0 a)
  | [], _ => List.Perm.refl _
  | [_], _ => List.Perm.refl _
  | c :: d :: t, h => by
    rw [tausch_cons]
    by_cases hc : 2 ≤ c
    · rw [if_pos hc]
      obtain ⟨c', rfl⟩ : ∃ c', c = c' + 2 := ⟨c - 2, by omega⟩
      have hd : 1 ≤ d := h d (List.mem_cons_of_mem _ List.mem_cons_self)
      obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
      rw [show c' + 2 - 1 = c' + 1 from rfl, show d' + 1 - 1 = d' from rfl]
      show List.Perm _ (List.replicate (c' + 2) 0 ++ (List.replicate (d' + 1) 1 ++ bloecke 2 t))
      rw [List.replicate_succ' (n := c' + 1), List.append_assoc, List.replicate_succ (n := d')]
      exact List.Perm.append_left _ (List.Perm.swap _ _ _)
    · rw [if_neg hc]

theorem tausch_ne {c d : ℕ} (t : List ℕ) (hc : 2 ≤ c) (hd : 1 ≤ d) :
    tausch (c :: d :: t) ≠ bloecke 0 (c :: d :: t) := by
  obtain ⟨c', rfl⟩ : ∃ c', c = c' + 2 := ⟨c - 2, by omega⟩
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  rw [tausch_cons, if_pos hc, show c' + 2 - 1 = c' + 1 from rfl]
  show _ ≠ List.replicate (c' + 2) 0 ++ (List.replicate (d' + 1) 1 ++ bloecke 2 t)
  rw [List.replicate_succ' (n := c' + 1), List.append_assoc]
  intro h
  have h2 := List.append_cancel_left h
  exact absurd (List.head_eq_of_cons_eq h2) (by decide)

theorem foldr_rep (c k y : ℕ) : (List.replicate (c + 1) k).foldr max y = max k y := by
  induction c with
  | zero => rfl
  | succ c ih =>
    rw [List.replicate_succ, List.foldr_cons, ih, ← Nat.max_assoc, Nat.max_self]

theorem foldr_bloecke : ∀ (a : List ℕ) (k : ℕ), (∀ c ∈ a, 1 ≤ c) → a ≠ [] →
    (bloecke k a).foldr max 0 = k + a.length - 1
  | [], _, _, hne => absurd rfl hne
  | 0 :: _, _, h, _ => absurd (h 0 List.mem_cons_self) (by decide)
  | (c + 1) :: t, k, h, _ => by
    rw [bloecke, List.foldr_append, foldr_rep, List.length_cons]
    cases t with
    | nil =>
      show max k 0 = _
      rw [Nat.max_eq_left (Nat.zero_le k)]; rfl
    | cons x u =>
      rw [foldr_bloecke (x :: u) (k + 1) (fun y hy => h y (List.mem_cons_of_mem _ hy)) (List.cons_ne_nil _ _),
        List.length_cons]
      omega

theorem anzahl_bloecke_unter : ∀ (a : List ℕ) (k v : ℕ), v < k → anzahl (bloecke k a) v = 0
  | [], _, _, _ => rfl
  | c :: t, k, v, h => by
    rw [bloecke, anzahl_append, anzahl_rep_ne c (Nat.ne_of_gt h),
      anzahl_bloecke_unter t (k + 1) v (Nat.lt_succ_of_lt h)]

theorem map_anzahl_bloecke : ∀ (a : List ℕ) (k : ℕ),
    (List.range a.length).map (fun i => anzahl (bloecke k a) (k + i)) = a
  | [], _ => rfl
  | c :: t, k => by
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    congr 1
    · rw [bloecke, anzahl_append, Nat.add_zero, anzahl_rep_self,
        anzahl_bloecke_unter t (k + 1) k (Nat.lt_succ_self k), Nat.add_zero]
    · conv_rhs => rw [← map_anzahl_bloecke t (k + 1)]
      refine List.map_congr_left (fun i _ => ?_)
      show anzahl (bloecke k (c :: t)) (k + (i + 1)) = _
      rw [bloecke, anzahl_append, anzahl_rep_ne c (by omega),
        show k + (i + 1) = k + 1 + i by omega, Nat.zero_add]

theorem zaehlen_bloecke (a : List ℕ) (h : ∀ c ∈ a, 1 ≤ c) (hne : a ≠ []) : zaehlen (bloecke 0 a) = a := by
  have hl : 0 < a.length := List.length_pos_iff.mpr hne
  unfold zaehlen
  rw [foldr_bloecke a 0 h hne, show 0 + a.length - 1 + 1 = a.length by omega]
  conv_rhs => rw [← map_anzahl_bloecke a 0]
  refine List.map_congr_left (fun i _ => ?_)
  rw [Nat.zero_add]

/-! ## Die Fasern von `deutero` -/

/-- **Das Bild der Vergröberung auf Stufe `n`:**  die Multimengen, die als Klassengrößen vorkommen. -/
abbrev Bild (n : ℕ) := { m : Multiset ℕ // ∃ r : RGS n, deutero r = m }

/-- **Ein Schnitt** (die Lesung „Rückrechnung"):  zu jedem Zeichen eine Folge, die es trägt. -/
def IstSchnitt {n : ℕ} (σ : Bild n → RGS n) : Prop := ∀ m : Bild n, deutero (σ m) = m.val

theorem rgs_ne_nil {n : ℕ} (hn : 1 ≤ n) (r : RGS n) : r.val ≠ [] := by
  intro h
  have h1 := r.property.1
  rw [h] at h1
  exact absurd (h1 ▸ hn) (by decide)

theorem bild_pos {n : ℕ} (hn : 1 ≤ n) (m : Bild n) : ∀ c ∈ sortM m.val, 1 ≤ c := by
  obtain ⟨_, r, rfl⟩ := m
  intro c hc
  have hc' : c ∈ sortM (deutero r) := hc
  rw [deutero_coe, sortM_coe] at hc'
  exact zaehlen_pos r.property.2 (rgs_ne_nil hn r) c ((sortiert_perm _).mem_iff.mp hc')

theorem bild_summe {n : ℕ} (m : Bild n) : (sortM m.val).sum = n := by
  obtain ⟨_, r, rfl⟩ := m
  show (sortM (deutero r)).sum = n
  rw [deutero_coe, sortM_coe, (sortiert_perm _).sum_eq, summe_zaehlen]
  exact r.property.1

/-- Der Blockschnitt. -/
def schnittBlock {n : ℕ} (hn : 1 ≤ n) (m : Bild n) : RGS n :=
  ⟨bloecke 0 (sortM m.val), by rw [length_bloecke]; exact bild_summe m, isRGS_bloecke _ (bild_pos hn m)⟩

/-- Der Tauschschnitt. -/
def schnittTausch {n : ℕ} (hn : 1 ≤ n) (m : Bild n) : RGS n :=
  ⟨tausch (sortM m.val),
    (tausch_perm _ (bild_pos hn m)).length_eq.trans (by rw [length_bloecke]; exact bild_summe m),
    isRGS_tausch _ (bild_pos hn m)⟩

theorem bild_ne_nil {n : ℕ} (hn : 1 ≤ n) (m : Bild n) : sortM m.val ≠ [] := by
  intro h
  have h1 := bild_summe m
  rw [h] at h1
  exact absurd (h1 ▸ hn) (by decide)

theorem istSchnitt_block {n : ℕ} (hn : 1 ≤ n) : IstSchnitt (schnittBlock hn) := by
  intro m
  show deutero (schnittBlock hn m) = m.val
  rw [deutero_coe]
  show ((zaehlen (bloecke 0 (sortM m.val)) : List ℕ) : Multiset ℕ) = _
  rw [zaehlen_bloecke _ (bild_pos hn m) (bild_ne_nil hn m), coe_sortM]

theorem istSchnitt_tausch {n : ℕ} (hn : 1 ≤ n) : IstSchnitt (schnittTausch hn) := by
  intro m
  rw [← istSchnitt_block hn m]
  exact deutero_of_perm (tausch_perm _ (bild_pos hn m))

/-- Über einem Zeichen, dessen größte Klasse mindestens zwei Elemente hat und das mindestens zwei Klassen kennt, trennen sich die zwei Schnitte. -/
theorem schnitte_trennen {n : ℕ} (hn : 1 ≤ n) (m : Bild n) {c d : ℕ} {t : List ℕ}
    (ha : sortM m.val = c :: d :: t) (hc : 2 ≤ c) : schnittTausch hn m ≠ schnittBlock hn m := by
  intro h
  have h1 : tausch (sortM m.val) = bloecke 0 (sortM m.val) := congrArg Subtype.val h
  rw [ha] at h1
  have hd : 1 ≤ d := bild_pos hn m d (by rw [ha]; exact List.mem_cons_of_mem _ List.mem_cons_self)
  exact tausch_ne t hc hd h1

theorem sortM_pairwise (m : Multiset ℕ) : (sortM m).Pairwise (· ≥ ·) :=
  Quot.inductionOn m sortiert_pairwise

/-- Die Klasse mit `n` Elementen:  nur `0 0 … 0`. -/
theorem faser_konstant {n : ℕ} (s : RGS n) (h : deutero s = {n}) : s.val = List.replicate n 0 := by
  have h1 := coarsening_factors s
  rw [h] at h1
  have h2 : s.val.foldr max 0 = 0 := by
    have h3 : s.val.foldr max 0 + 1 = 1 := h1
    omega
  refine List.eq_replicate_iff.mpr ⟨s.property.1, fun x hx => ?_⟩
  have h3 := le_foldr_max hx
  omega

/-- Alle Klassen einelementig:  nur `0 1 … (n−1)`. -/
theorem faser_diskret {n : ℕ} (s : RGS n) (h : deutero s = Multiset.replicate n 1) :
    s.val = List.range' 0 n := by
  rw [deutero_coe, show Multiset.replicate n 1 = ((List.replicate n 1 : List ℕ) : Multiset ℕ) from rfl,
    Multiset.coe_eq_coe] at h
  have hn : s.val.Nodup := nodup_of_anzahl _ (fun x hx => by
    have hmem : anzahl s.val x ∈ zaehlen s.val :=
      List.mem_map.mpr ⟨x, List.mem_range.mpr (Nat.lt_succ_of_le (le_foldr_max hx)), rfl⟩
    exact Nat.le_of_eq (List.eq_of_mem_replicate (h.mem_iff.mp hmem)))
  have h1 := rgs_nodup s.property.2 hn
  rw [s.property.1] at h1
  exact h1

theorem alle_eins_summe : ∀ l : List ℕ, (∀ x ∈ l, x = 1) → l.sum = l.length
  | [], _ => rfl
  | a :: t, h => by
    rw [List.sum_cons, h a List.mem_cons_self, alle_eins_summe t (fun x hx => h x (List.mem_cons_of_mem _ hx)),
      List.length_cons, Nat.add_comm]

theorem rgs_null_val (r : RGS 0) : r.val = [] := List.length_eq_zero_iff.mp r.property.1

/-- (V2) **Die Einer-Fasern, für jede Länge.**  Genau über `(n)` und `(1,…,1)` ist die Rückrechnung eindeutig. -/
theorem einer_fasern {n : ℕ} (r : RGS n) :
    (∀ s : RGS n, deutero s = deutero r → s = r) ↔
      (deutero r = {n} ∨ deutero r = Multiset.replicate n 1) := by
  constructor
  · intro hs
    cases n with
    | zero =>
      left
      obtain ⟨l, hl⟩ := r
      have h0 := List.length_eq_zero_iff.mp hl.1
      subst h0
      rfl
    | succ k =>
      have hn : 1 ≤ k + 1 := Nat.succ_pos k
      let m : Bild (k + 1) := ⟨deutero r, r, rfl⟩
      have hb : schnittBlock hn m = r := hs _ (istSchnitt_block hn m)
      have ht : schnittTausch hn m = r := hs _ (istSchnitt_tausch hn m)
      have hco : ((sortM m.val : List ℕ) : Multiset ℕ) = deutero r := coe_sortM _
      have hsum := bild_summe m
      have hpw := sortM_pairwise m.val
      have hpos := bild_pos hn m
      cases ha : sortM m.val with
      | nil => exact absurd ha (bild_ne_nil hn m)
      | cons c u =>
        cases u with
        | nil =>
          left
          rw [ha, List.sum_cons, List.sum_nil, Nat.add_zero] at hsum
          rw [ha, hsum] at hco
          exact hco.symm
        | cons d t =>
          by_cases hc : 2 ≤ c
          · exact absurd (ht.trans hb.symm) (schnitte_trennen hn m ha hc)
          · right
            rw [ha] at hpw hpos
            have hall : ∀ x ∈ c :: d :: t, x = 1 := by
              intro x hx
              have h1 := hpos x hx
              have h2 : x ≤ c := by
                rcases List.mem_cons.mp hx with rfl | hxt
                · exact Nat.le_refl _
                · exact (List.pairwise_cons.mp hpw).1 x hxt
              omega
            have hrep : c :: d :: t = List.replicate (k + 1) 1 := by
              refine List.eq_replicate_iff.mpr ⟨?_, hall⟩
              rw [ha, alle_eins_summe _ hall] at hsum
              exact hsum
            rw [ha, hrep] at hco
            exact hco.symm
  · rintro (h | h) s hs
    · exact Subtype.ext ((faser_konstant s (hs.trans h)).trans (faser_konstant r h).symm)
    · exact Subtype.ext ((faser_diskret s (hs.trans h)).trans (faser_diskret r h).symm)

theorem rgs_zwei (r : RGS 2) : r.val = [0, 0] ∨ r.val = [0, 1] := by
  obtain ⟨l, hl, hr⟩ := r
  match l, hl, hr with
  | [x, y], _, hr =>
    unfold IsRGS at hr
    rw [isRGSAux, Bool.and_eq_true, isRGSAux, Bool.and_eq_true] at hr
    have hx : x = 0 := of_decide_eq_true hr.1
    have hy : y ≤ x + 1 := of_decide_eq_true hr.2.1
    subst hx
    cases y with
    | zero => exact Or.inl rfl
    | succ y =>
      have hy0 : y = 0 := by omega
      subst hy0
      exact Or.inr rfl

theorem rgs_eins (r : RGS 1) : r.val = [0] := by
  obtain ⟨l, hl, hr⟩ := r
  match l, hl, hr with
  | [x], _, hr =>
    unfold IsRGS at hr
    rw [isRGSAux, Bool.and_eq_true] at hr
    have hx : x = 0 := of_decide_eq_true hr.1
    subst hx
    rfl

/-- Unterhalb von drei Stellen trennt `deutero` alle Folgen. -/
theorem injektiv_klein {n : ℕ} (hn : n ≤ 2) (a b : RGS n) (h : deutero a = deutero b) : a = b := by
  match n, hn, a, b, h with
  | 0, _, a, b, _ => exact Subtype.ext ((rgs_null_val a).trans (rgs_null_val b).symm)
  | 1, _, a, b, _ => exact Subtype.ext ((rgs_eins a).trans (rgs_eins b).symm)
  | 2, _, a, b, h =>
    have hp : a.val.foldr max 0 + 1 = b.val.foldr max 0 + 1 := by
      have h1 := coarsening_factors a
      have h2 := coarsening_factors b
      rw [h] at h1
      exact h1.trans h2.symm
    rcases rgs_zwei a with ha | ha <;> rcases rgs_zwei b with hb | hb
    · exact Subtype.ext (ha.trans hb.symm)
    · rw [ha, hb] at hp; exact absurd hp (by decide)
    · rw [ha, hb] at hp; exact absurd hp (by decide)
    · exact Subtype.ext (ha.trans hb.symm)

/-- Der Zeuge ab drei Stellen:  die Klassengrößen `(2, 1, …, 1)`. -/
def zeugenListe (n : ℕ) : List ℕ := 2 :: 1 :: List.replicate (n - 3) 1

theorem zeuge_pos (n : ℕ) : ∀ c ∈ zeugenListe n, 1 ≤ c := by
  intro c hc
  rcases List.mem_cons.mp hc with rfl | hc
  · decide
  rcases List.mem_cons.mp hc with rfl | hc
  · decide
  · exact Nat.le_of_eq (List.eq_of_mem_replicate hc).symm

theorem zeuge_summe : ∀ j : ℕ, (List.replicate j 1).sum = j
  | 0 => rfl
  | j + 1 => by rw [List.replicate_succ, List.sum_cons, zeuge_summe j, Nat.add_comm]

/-- Der Zeuge als Folge der Länge `n`. -/
def zeuge {n : ℕ} (hn : 3 ≤ n) : RGS n :=
  ⟨bloecke 0 (zeugenListe n), by
    rw [length_bloecke, zeugenListe, List.sum_cons, List.sum_cons, zeuge_summe]; omega,
    isRGS_bloecke _ (zeuge_pos n)⟩

/-- Das Zeichen des Zeugen. -/
def zeugenBild {n : ℕ} (hn : 3 ≤ n) : Bild n := ⟨deutero (zeuge hn), zeuge hn, rfl⟩

theorem zeuge_trennt {n : ℕ} (hn : 3 ≤ n) :
    schnittTausch (Nat.le_trans (by decide) hn) (zeugenBild hn) ≠
      schnittBlock (Nat.le_trans (by decide) hn) (zeugenBild hn) := by
  have hco : sortM (zeugenBild hn).val = sortiert (zeugenListe n) := by
    show sortM (deutero (zeuge hn)) = _
    rw [deutero_coe]
    show sortM ((zaehlen (bloecke 0 (zeugenListe n)) : List ℕ) : Multiset ℕ) = _
    rw [zaehlen_bloecke _ (zeuge_pos n) (List.cons_ne_nil _ _), sortM_coe]
  have hperm : (sortM (zeugenBild hn).val).Perm (zeugenListe n) := by
    rw [hco]; exact sortiert_perm _
  have hpw := sortM_pairwise (zeugenBild hn).val
  have hlen : 2 ≤ (sortM (zeugenBild hn).val).length := by
    rw [hperm.length_eq, zeugenListe, List.length_cons, List.length_cons]; omega
  have h2 : 2 ∈ sortM (zeugenBild hn).val := hperm.mem_iff.mpr List.mem_cons_self
  cases ha : sortM (zeugenBild hn).val with
  | nil => rw [ha] at hlen; exact absurd hlen (by decide)
  | cons c u =>
    cases u with
    | nil => rw [ha] at hlen; exact absurd (show 2 ≤ 1 from hlen) (by decide)
    | cons d t =>
      rw [ha] at hpw h2
      have hc : 2 ≤ c := by
        rcases List.mem_cons.mp h2 with h | h
        · exact Nat.le_of_eq h
        · exact (List.pairwise_cons.mp hpw).1 2 h
      exact schnitte_trennen _ _ ha hc

/-- `deutero` trennt die Folgen der Länge `n` genau bis zwei Stellen. -/
theorem injektiv_iff (n : ℕ) : (∀ a b : RGS n, deutero a = deutero b → a = b) ↔ n ≤ 2 := by
  constructor
  · intro h
    by_cases hn : n ≤ 2
    · exact hn
    · have h3 : 3 ≤ n := by omega
      have hle : 1 ≤ n := Nat.le_trans (by decide) h3
      exact absurd
        (h _ _ ((istSchnitt_tausch hle _).trans (istSchnitt_block hle _).symm))
        (zeuge_trennt h3)
  · exact fun hn a b => injektiv_klein hn a b

/-- (V3) **Die Rückrechnung ist eine Wahl — ab drei Stellen.**  Es gibt genau dann genau einen Schnitt, wenn `n ≤ 2`. -/
theorem rueckrechnung_wahl (n : ℕ) : (∃! σ : Bild n → RGS n, IstSchnitt σ) ↔ n ≤ 2 := by
  constructor
  · rintro ⟨σ, _, hu⟩
    by_cases hn : n ≤ 2
    · exact hn
    · have h3 : 3 ≤ n := by omega
      have hle : 1 ≤ n := Nat.le_trans (by decide) h3
      have h1 := hu _ (istSchnitt_tausch hle)
      have h2 := hu _ (istSchnitt_block hle)
      exact absurd (congrFun (h1.trans h2.symm) (zeugenBild h3)) (zeuge_trennt h3)
  · intro hn
    have hex : ∃ σ : Bild n → RGS n, IstSchnitt σ := by
      cases n with
      | zero =>
        refine ⟨fun _ => ⟨[], rfl, rfl⟩, ?_⟩
        rintro ⟨_, r, rfl⟩
        exact congrArg deutero (Subtype.ext (rgs_null_val r).symm)
      | succ k => exact ⟨_, istSchnitt_block (Nat.succ_pos k)⟩
    obtain ⟨σ, hσ⟩ := hex
    refine ⟨σ, hσ, fun τ hτ => funext fun m => ?_⟩
    exact injektiv_klein hn _ _ ((hτ m).trans (hσ m).symm)

/-- (V3, zweite Hälfte) **Zwei verschiedene Schnitte ab drei Stellen**, beide angegeben. -/
theorem zwei_schnitte {n : ℕ} (hn : 3 ≤ n) :
    ∃ σ τ : Bild n → RGS n, IstSchnitt σ ∧ IstSchnitt τ ∧ σ ≠ τ := by
  have hle : 1 ≤ n := Nat.le_trans (by decide) hn
  exact ⟨_, _, istSchnitt_tausch hle, istSchnitt_block hle,
    fun h => zeuge_trennt hn (congrFun h (zeugenBild hn))⟩

/-! ## Brücke:  `deutero` und `groessen` -/

theorem count_eq_anzahl (l : List ℕ) (v : ℕ) : l.count v = anzahl l v := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [anzahl_cons, List.count_cons, ih, Nat.add_comm]
    by_cases h : a = v
    · rw [if_pos h, if_pos (beq_iff_eq.mpr h)]
    · rw [if_neg h, if_neg (fun hb => h (beq_iff_eq.mp hb))]

theorem groessen_eq {l : List ℕ} (hne : l ≠ []) : groessen l = sortiert (zaehlen l) := by
  cases l with
  | nil => exact absurd rfl hne
  | cons a t =>
    unfold groessen zaehlen
    rw [show klassenZahl (a :: t) = (a :: t).foldr max 0 + 1 from rfl,
      show (fun v => (a :: t).count v) = anzahl (a :: t) from funext (count_eq_anzahl _)]

/-- **Brücke:**  auf Stufe `n ≥ 1` ist `deutero` die Multimenge von `groessen`. -/
theorem deutero_eq_groessen {n : ℕ} (hn : 1 ≤ n) (r : RGS n) :
    deutero r = ((groessen r.val : List ℕ) : Multiset ℕ) := by
  rw [deutero_coe, groessen_eq (rgs_ne_nil hn r)]
  exact Multiset.coe_eq_coe.mpr (sortiert_perm _).symm

/-- **Brücke:**  dieselbe Faser von `deutero` heißt dasselbe `groessen`. -/
theorem deutero_gleich_iff {n : ℕ} (hn : 1 ≤ n) (a b : RGS n) :
    deutero a = deutero b ↔ groessen a.val = groessen b.val := by
  constructor
  · intro h
    rw [groessen_eq (rgs_ne_nil hn a), groessen_eq (rgs_ne_nil hn b)]
    rw [deutero_coe, deutero_coe, Multiset.coe_eq_coe] at h
    exact sortiert_eq_of_perm h
  · intro h
    rw [deutero_eq_groessen hn a, deutero_eq_groessen hn b, h]

/-- **Proto ist `klassenZahl`** auf Stufe `n ≥ 1`. -/
theorem proto_eq_klassenZahl {n : ℕ} (hn : 1 ≤ n) (r : RGS n) : proto r = klassenZahl r.val := by
  have hne := rgs_ne_nil hn r
  unfold proto
  cases h : r.val with
  | nil => exact absurd h hne
  | cons a t => rfl

/-! ## Die Fasern als Listen, die Partitionen -/

/-- Die Klassengrößen-Listen selbst:  dieselbe Rekursion wie `teile`, nicht steigend, jeder Teil höchstens `b`. -/
def teilListe : ℕ → ℕ → ℕ → List (List ℕ)
  | 0, n, _ => if n = 0 then [[]] else []
  | k + 1, n, b => (List.range (min b n)).flatMap
      (fun i => (teilListe k (n - (i + 1)) (i + 1)).map (fun t => (i + 1) :: t))

/-- Alle Partitionen von `n`, nach Teilezahl. -/
def partitionen (n : ℕ) : List (List ℕ) := (List.range (n + 1)).flatMap (fun k => teilListe k n n)

/-- Die Faser über `lam`:  die Normalformen der Länge `n` mit diesen Klassengrößen. -/
def faser (n : ℕ) (lam : List ℕ) : List (List ℕ) := (rgsList n).filter (fun l => groessen l == lam)

/-- `mem_rgsList_iff` trägt `Classical.choice` (Kenogram/Basic);  dieselbe Aussage ohne offenes `simp`. -/
theorem mem_rgsList_frei {n : ℕ} {l : List ℕ} : l ∈ rgsList n ↔ l.length = n ∧ IsRGS l := by
  induction n generalizing l with
  | zero =>
    show l ∈ [[]] ↔ _
    rw [List.mem_singleton, List.length_eq_zero_iff]
    constructor
    · rintro rfl; exact ⟨rfl, rfl⟩
    · rintro ⟨h, _⟩; exact h
  | succ n ih =>
    rw [rgsList, List.mem_flatMap]
    constructor
    · rintro ⟨l', hl', hl⟩
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hl
      have hv' := List.mem_range.mp hv
      obtain ⟨hlen, hrgs⟩ := ih.mp hl'
      refine ⟨by rw [List.length_append, hlen]; rfl, ?_⟩
      cases l' with
      | nil =>
        have hv0 : v = 0 := Nat.lt_one_iff.mp hv'
        subst hv0
        exact rfl
      | cons a t =>
        exact (isRGS_cons_concat a t v).mpr ⟨hrgs, Nat.le_of_lt_succ hv'⟩
    · rintro ⟨hlen, hrgs⟩
      rcases List.eq_nil_or_concat l with rfl | ⟨l', v, rfl⟩
      · exact absurd hlen (Nat.succ_ne_zero n).symm
      · rw [List.concat_eq_append] at hlen hrgs ⊢
        rw [List.length_append, List.length_singleton] at hlen
        have hlen' : l'.length = n := Nat.succ.inj hlen
        cases l' with
        | nil =>
          have hv0 : v = 0 := by
            unfold IsRGS at hrgs
            rw [List.nil_append, isRGSAux, Bool.and_eq_true] at hrgs
            exact of_decide_eq_true hrgs.1
          subst hv0
          exact ⟨[], ih.mpr ⟨hlen', rfl⟩, List.mem_map.mpr ⟨0, List.mem_range.mpr (Nat.succ_pos 0), rfl⟩⟩
        | cons a t =>
          obtain ⟨h1, h2⟩ := (isRGS_cons_concat a t v).mp hrgs
          exact ⟨a :: t, ih.mpr ⟨hlen', h1⟩,
            List.mem_map.mpr ⟨v, List.mem_range.mpr (Nat.lt_succ_of_le h2), rfl⟩⟩

/-- **Brücke:**  die Liste `faser` ist die Faser von `deutero`, auf Stufe `n ≥ 1`. -/
theorem faser_ist_faser {n : ℕ} (hn : 1 ≤ n) (r s : RGS n) :
    s.val ∈ faser n (groessen r.val) ↔ deutero s = deutero r := by
  rw [deutero_gleich_iff hn, faser, List.mem_filter]
  constructor
  · exact fun h => beq_iff_eq.mp h.2
  · exact fun h => ⟨mem_rgsList_frei.mpr s.property, beq_iff_eq.mpr h⟩

/-- Der Nenner der Faserformel:  `∏ λᵢ! · ∏ mⱼ!`. -/
def nenner (lam : List ℕ) : ℕ :=
  (lam.map Nat.factorial).prod * (lam.eraseDups.map (fun x => Nat.factorial (lam.count x))).prod

/-- (V1) **Die Faserformel, EICHUNG n ≤ 8:**  die Faser über jeder Partition hat `n! / (∏ λᵢ! ∏ mⱼ!)` Elemente, und die Division geht auf. -/
theorem faser_formel : ∀ n < 9, ∀ lam ∈ partitionen n,
    (faser n lam).length = Nat.factorial n / nenner lam ∧
      (faser n lam).length * nenner lam = Nat.factorial n := by
  decide +kernel

/-- (V1, Abschluss) **Die Fasern erschöpfen die Stufe, EICHUNG n ≤ 8:**  jede Normalform liegt über einer Partition, und die Fasergrößen summieren sich zur Zahl der Normalformen. -/
theorem faser_summe : ∀ n < 9,
    (∀ l ∈ rgsList n, groessen l ∈ partitionen n) ∧
      ((partitionen n).map (fun lam => (faser n lam).length)).sum = (rgsList n).length := by
  decide +kernel

/-! ## Die Zahl der Schnitte -/

/-- Je Liste ein Element:  alle Auswahlen. -/
def waehlen : List (List (List ℕ)) → List (List (List ℕ))
  | [] => [[]]
  | L :: Ls => L.flatMap (fun x => (waehlen Ls).map (fun w => x :: w))

theorem length_flatMap_map (L : List (List ℕ)) (W : List (List (List ℕ))) :
    (L.flatMap (fun x => W.map (fun w => x :: w))).length = L.length * W.length := by
  induction L with
  | nil => exact (Nat.zero_mul _).symm
  | cons a t ih =>
    rw [List.flatMap_cons, List.length_append, List.length_map, ih, List.length_cons, Nat.succ_mul,
      Nat.add_comm]

/-- **Die Zahl der Auswahlen ist das Produkt der Längen**, allgemein. -/
theorem waehlen_length : ∀ Ls : List (List (List ℕ)), (waehlen Ls).length = (Ls.map List.length).prod
  | [] => rfl
  | L :: Ls => by
    rw [waehlen, length_flatMap_map, waehlen_length Ls, List.map_cons, List.prod_cons]

/-- **Eine Auswahl nimmt aus jeder Liste genau ein Element**, allgemein. -/
theorem mem_waehlen : ∀ (Ls : List (List (List ℕ))) (w : List (List ℕ)),
    w ∈ waehlen Ls ↔ List.Forall₂ (· ∈ ·) w Ls
  | [], w => by
    rw [waehlen, List.mem_singleton]
    constructor
    · rintro rfl; exact List.Forall₂.nil
    · intro h; cases h; rfl
  | L :: Ls, w => by
    rw [waehlen, List.mem_flatMap]
    constructor
    · rintro ⟨x, hx, hw⟩
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
      exact List.Forall₂.cons hx ((mem_waehlen Ls u).mp hu)
    · intro h
      cases h with
      | cons hx hu => exact ⟨_, hx, List.mem_map.mpr ⟨_, (mem_waehlen Ls _).mpr hu, rfl⟩⟩

/-- Die Schnitte in Listenform:  je Partition ein Element ihrer Faser. -/
def schnitte (n : ℕ) : List (List (List ℕ)) := waehlen ((partitionen n).map (faser n))

/-- Die Zahl der Schnitte ist das Produkt der Fasergrößen, allgemein. -/
theorem schnitte_length (n : ℕ) :
    (schnitte n).length = ((partitionen n).map (fun lam => (faser n lam).length)).prod := by
  rw [schnitte, waehlen_length, List.map_map]
  rfl

/-- (V4) **Die Zahl der Schnitte, EICHUNG n ≤ 6:**  1, 1, 3, 72, 75000, 164025000000. -/
theorem schnitte_zahl :
    (schnitte 1).length = 1 ∧ (schnitte 2).length = 1 ∧ (schnitte 3).length = 3 ∧
      (schnitte 4).length = 72 ∧ (schnitte 5).length = 75000 ∧ (schnitte 6).length = 164025000000 := by
  simp only [schnitte_length]
  decide +kernel

/-! ## Deutero → Proto -/

theorem length_flatMap_map_cons (L : List ℕ) (f : ℕ → List (List ℕ)) (g : ℕ → List ℕ → List ℕ) :
    (L.flatMap (fun i => (f i).map (g i))).length = (L.map (fun i => (f i).length)).sum := by
  induction L with
  | nil => rfl
  | cons a t ih =>
    rw [List.flatMap_cons, List.length_append, List.length_map, ih, List.map_cons, List.sum_cons]

theorem teilListe_length : ∀ k n b : ℕ, (teilListe k n b).length = teile k n b
  | 0, n, _ => by
    show (if n = 0 then [[]] else []).length = if n = 0 then 1 else 0
    by_cases h : n = 0
    · rw [if_pos h, if_pos h]; rfl
    · rw [if_neg h, if_neg h]; rfl
  | k + 1, n, b => by
    show ((List.range (min b n)).flatMap _).length = ((List.range (min b n)).map _).sum
    rw [length_flatMap_map_cons]
    congr 1
    refine List.map_congr_left (fun i _ => ?_)
    exact teilListe_length k _ _

/-- (V5) **Die Faser von proto über `k`, auf der Deutero-Ebene:**  `deuteroZahl n k` Partitionen, allgemein. -/
theorem proto_faser_zahl (n k : ℕ) : (teilListe k n n).length = deuteroZahl n k :=
  teilListe_length k n n

/-- (V5, Abgleich) **EICHUNG n ≤ 7:**  die Partitionen mit `k` Teilen sind die Bilder der Normalformen mit `k` Klassen;  Menge und Zahl. -/
theorem proto_faser_bild : ∀ n < 8, ∀ k < n + 1,
    ((((rgsList n).filter (fun l => klassenZahl l == k)).map groessen).eraseDups.length =
        (teilListe k n n).length) ∧
      ∀ l ∈ rgsList n, klassenZahl l = k → groessen l ∈ teilListe k n n := by
  decide +kernel

/-- (V5, zitiert aus EM3) **Einer-Fasern von proto, EICHUNG n = 4 … 12:**  genau bei `k ∈ {1, n−1, n}`. -/
theorem proto_fasern (n : ℕ) (hn : n < 13) (k : ℕ) (hk : k < n + 1) (h4 : 4 ≤ n) (h1 : 1 ≤ k) :
    (teilListe k n n).length = 1 ↔ (k = 1 ∨ k = n - 1 ∨ k = n) := by
  rw [proto_faser_zahl]
  exact ⟨deutero_eins n hn k hk h4 h1, deutero_eins_rueck n hn k hk h4 h1⟩

end Reformulation.Proemial.VergroeberungMass

/-! ## Axiom-Wachen (gemessen, verbatim) -/

/-- info: 'Reformulation.Proemial.VergroeberungMass.deutero_coe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.deutero_coe

/-- info: 'Reformulation.Proemial.VergroeberungMass.anzahl_cons' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.anzahl_cons

/-- info: 'Reformulation.Proemial.VergroeberungMass.anzahl_append' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.anzahl_append

/-- info: 'Reformulation.Proemial.VergroeberungMass.anzahl_rep_self' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.anzahl_rep_self

/-- info: 'Reformulation.Proemial.VergroeberungMass.anzahl_rep_ne' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.anzahl_rep_ne

/-- info: 'Reformulation.Proemial.VergroeberungMass.anzahl_pos' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.anzahl_pos

/-- info: 'Reformulation.Proemial.VergroeberungMass.le_foldr_max' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.le_foldr_max

/-- info: 'Reformulation.Proemial.VergroeberungMass.summe_add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.summe_add

/-- info: 'Reformulation.Proemial.VergroeberungMass.summe_ite' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.summe_ite

/-- info: 'Reformulation.Proemial.VergroeberungMass.summe_anzahl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.summe_anzahl

/-- info: 'Reformulation.Proemial.VergroeberungMass.summe_zaehlen' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.summe_zaehlen

/-- info: 'Reformulation.Proemial.VergroeberungMass.lauf_dicht' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.lauf_dicht

/-- info: 'Reformulation.Proemial.VergroeberungMass.rgs_dicht' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.rgs_dicht

/-- info: 'Reformulation.Proemial.VergroeberungMass.zaehlen_pos' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.zaehlen_pos

/-- info: 'Reformulation.Proemial.VergroeberungMass.lauf_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.lauf_nodup

/-- info: 'Reformulation.Proemial.VergroeberungMass.nodup_of_anzahl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.nodup_of_anzahl

/-- info: 'Reformulation.Proemial.VergroeberungMass.rgs_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.rgs_nodup

/-- info: 'Reformulation.Proemial.VergroeberungMass.einfuegen_perm' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.einfuegen_perm

/-- info: 'Reformulation.Proemial.VergroeberungMass.sortiert_perm' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.sortiert_perm

/-- info: 'Reformulation.Proemial.VergroeberungMass.einfuegen_pairwise' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.einfuegen_pairwise

/-- info: 'Reformulation.Proemial.VergroeberungMass.sortiert_pairwise' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.sortiert_pairwise

/-- info: 'Reformulation.Proemial.VergroeberungMass.sortiert_eq_of_perm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.sortiert_eq_of_perm

/-- info: 'Reformulation.Proemial.VergroeberungMass.sortM_coe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.sortM_coe

/-- info: 'Reformulation.Proemial.VergroeberungMass.coe_sortM' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.coe_sortM

/-- info: 'Reformulation.Proemial.VergroeberungMass.tausch_cons' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.tausch_cons

/-- info: 'Reformulation.Proemial.VergroeberungMass.lauf_rep' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.lauf_rep

/-- info: 'Reformulation.Proemial.VergroeberungMass.lauf_bloecke' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.lauf_bloecke

/-- info: 'Reformulation.Proemial.VergroeberungMass.isRGS_bloecke' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.isRGS_bloecke

/-- info: 'Reformulation.Proemial.VergroeberungMass.isRGS_tausch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.isRGS_tausch

/-- info: 'Reformulation.Proemial.VergroeberungMass.length_bloecke' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.length_bloecke

/-- info: 'Reformulation.Proemial.VergroeberungMass.tausch_perm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.tausch_perm

/-- info: 'Reformulation.Proemial.VergroeberungMass.tausch_ne' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.tausch_ne

/-- info: 'Reformulation.Proemial.VergroeberungMass.foldr_rep' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.foldr_rep

/-- info: 'Reformulation.Proemial.VergroeberungMass.foldr_bloecke' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.foldr_bloecke

/-- info: 'Reformulation.Proemial.VergroeberungMass.anzahl_bloecke_unter' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.anzahl_bloecke_unter

/-- info: 'Reformulation.Proemial.VergroeberungMass.map_anzahl_bloecke' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.map_anzahl_bloecke

/-- info: 'Reformulation.Proemial.VergroeberungMass.zaehlen_bloecke' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.zaehlen_bloecke

/-- info: 'Reformulation.Proemial.VergroeberungMass.rgs_ne_nil' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.rgs_ne_nil

/-- info: 'Reformulation.Proemial.VergroeberungMass.bild_pos' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.bild_pos

/-- info: 'Reformulation.Proemial.VergroeberungMass.bild_summe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.bild_summe

/-- info: 'Reformulation.Proemial.VergroeberungMass.bild_ne_nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.bild_ne_nil

/-- info: 'Reformulation.Proemial.VergroeberungMass.istSchnitt_block' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.istSchnitt_block

/-- info: 'Reformulation.Proemial.VergroeberungMass.istSchnitt_tausch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.istSchnitt_tausch

/-- info: 'Reformulation.Proemial.VergroeberungMass.schnitte_trennen' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.schnitte_trennen

/-- info: 'Reformulation.Proemial.VergroeberungMass.sortM_pairwise' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.sortM_pairwise

/-- info: 'Reformulation.Proemial.VergroeberungMass.faser_konstant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.faser_konstant

/-- info: 'Reformulation.Proemial.VergroeberungMass.faser_diskret' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.faser_diskret

/-- info: 'Reformulation.Proemial.VergroeberungMass.alle_eins_summe' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.alle_eins_summe

/-- info: 'Reformulation.Proemial.VergroeberungMass.rgs_null_val' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.rgs_null_val

/-- info: 'Reformulation.Proemial.VergroeberungMass.einer_fasern' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.einer_fasern

/-- info: 'Reformulation.Proemial.VergroeberungMass.rgs_zwei' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.rgs_zwei

/-- info: 'Reformulation.Proemial.VergroeberungMass.rgs_eins' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.rgs_eins

/-- info: 'Reformulation.Proemial.VergroeberungMass.injektiv_klein' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.injektiv_klein

/-- info: 'Reformulation.Proemial.VergroeberungMass.zeuge_pos' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.zeuge_pos

/-- info: 'Reformulation.Proemial.VergroeberungMass.zeuge_summe' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.zeuge_summe

/-- info: 'Reformulation.Proemial.VergroeberungMass.zeuge_trennt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.zeuge_trennt

/-- info: 'Reformulation.Proemial.VergroeberungMass.injektiv_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.injektiv_iff

/-- info: 'Reformulation.Proemial.VergroeberungMass.rueckrechnung_wahl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.rueckrechnung_wahl

/-- info: 'Reformulation.Proemial.VergroeberungMass.zwei_schnitte' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.zwei_schnitte

/-- info: 'Reformulation.Proemial.VergroeberungMass.count_eq_anzahl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.count_eq_anzahl

/-- info: 'Reformulation.Proemial.VergroeberungMass.groessen_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.groessen_eq

/-- info: 'Reformulation.Proemial.VergroeberungMass.deutero_eq_groessen' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.deutero_eq_groessen

/-- info: 'Reformulation.Proemial.VergroeberungMass.deutero_gleich_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.deutero_gleich_iff

/-- info: 'Reformulation.Proemial.VergroeberungMass.proto_eq_klassenZahl' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.proto_eq_klassenZahl

/-- info: 'Reformulation.Proemial.VergroeberungMass.mem_rgsList_frei' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.mem_rgsList_frei

/-- info: 'Reformulation.Proemial.VergroeberungMass.faser_ist_faser' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.faser_ist_faser

/-- info: 'Reformulation.Proemial.VergroeberungMass.faser_formel' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.faser_formel

/-- info: 'Reformulation.Proemial.VergroeberungMass.faser_summe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.faser_summe

/-- info: 'Reformulation.Proemial.VergroeberungMass.length_flatMap_map' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.length_flatMap_map

/-- info: 'Reformulation.Proemial.VergroeberungMass.waehlen_length' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.waehlen_length

/-- info: 'Reformulation.Proemial.VergroeberungMass.mem_waehlen' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.mem_waehlen

/-- info: 'Reformulation.Proemial.VergroeberungMass.schnitte_length' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.schnitte_length

/-- info: 'Reformulation.Proemial.VergroeberungMass.schnitte_zahl' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.schnitte_zahl

/-- info: 'Reformulation.Proemial.VergroeberungMass.length_flatMap_map_cons' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.length_flatMap_map_cons

/-- info: 'Reformulation.Proemial.VergroeberungMass.teilListe_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.teilListe_length

/-- info: 'Reformulation.Proemial.VergroeberungMass.proto_faser_zahl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.proto_faser_zahl

/-- info: 'Reformulation.Proemial.VergroeberungMass.proto_faser_bild' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.proto_faser_bild

/-- info: 'Reformulation.Proemial.VergroeberungMass.proto_fasern' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMass.proto_fasern
