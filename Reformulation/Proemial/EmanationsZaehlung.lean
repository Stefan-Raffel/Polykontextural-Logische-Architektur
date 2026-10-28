import Reformulation.Kenogram.Basic                          -- rgsList
import Mathlib.Combinatorics.Enumerative.Stirling           -- Nat.stirlingSecond

/-!
# Proemial.EmanationsZaehlung — die Zählung der Kenogrammfolgen nach Klassen (LZEE S. 18):  „erst eine Ausbreitung, dann aber eine Reduktion"

STANDALONE, NICHT im Aggregat;  Target `Probes`.  AxiomGate unberührt.  Sonde nach `KorpusRev2/Prompt_Instanz_Sonde_Emanation_LZEE.md`
(Mathematiker, 28.10.2026 17:58;  Architekt 17:58).  Konsumiert `Kenogram.Basic` (`rgsList`) und Mathlib
(`Mathlib.Combinatorics.Enumerative.Stirling`:  `Nat.stirlingSecond`, `stirlingSecond_succ_succ`, `stirlingSecond_eq_zero_of_lt`);  ändert
nichts davon.  Der Import von Mathlibs Stirling-Modul bringt etwa vierzig Bau-Jobs mit (Probes 1246 → 1284).

**Namen (Regel 9):**  `blocks` (NegationCycleSJT) und `deutero` (A3CoarseningProbe) sind besetzt — darum `klassenZahl`, `tritoZahl`,
`deuteroZahl`, `teile`.

## WAS

```text
klassenZahl l   = Zahl der Klassen (verschiedenen Kenogramme) einer Normalform;  tritoZahl n k = #{l ∈ rgsList n | klassenZahl l = k}
deuteroZahl n k = teile k n n = Partitionen von n in genau k Teile (die Deutero-Klassen mit k Teilen)

EM1  trito_eq_stirling       SATZ, jede Länge    tritoZahl n k = Nat.stirlingSecond n k — über die Rekursion von rgsList
                                                 (anz_flatMap, anz_erw_cons, summe).  Die Brücke Bestand ↔ Mathlib, die Kenogram/Basic
                                                 als „Kandidat" führte.  CHOICE-FREI
EM2  trito_guenther          SATZ, jede Länge    S. 18, Trito:  tritoZahl n 1 = 1, tritoZahl n n = 1, und 2 ≤ tritoZahl n k für 1 < k < n
EM3  deutero_eins,           EICHUNG n = 4…12    S. 18, Deutero:  deuteroZahl n k = 1 genau für k ∈ {1, n−1, n};  sonst ≥ 2
     deutero_eins_rueck,                         (gerechnet bis n = 60:  ausserhalb des Baums, T_Vorprobe_Skripte/Emanation_Rechnung.py)
     deutero_mehrere
     deutero_bild            EICHUNG n ≤ 7       Abgleich:  deuteroZahl ist das Bild der Kenogrammfolgen (Zahl der verschiedenen
                                                 Klassengrößen-Muster unter den Folgen mit k Klassen)
EM4  proto_klasse            SATZ (trivial)      zu jedem 1 ≤ k ≤ n eine Folge mit k Klassen;  ihr Proto-Zeichen ist k — je ein Exemplar
EM5  trito_unimodal          EICHUNG n ≤ 12      die Trito-Zählung steigt erst und fällt dann (k = 1…n);  gerechnet bis n = 60.  ALLGEMEIN
                                                 NICHT BEWIESEN:  der bekannte Weg (Log-Konkavität) ist kein kurzer Induktionsschritt —
                                                 Befund, kein Ausweichen
EM6  deutero_unimodal        EICHUNG n ≤ 12      ebenso die Deutero-Zählung (schwach:  mit Plateaus, z. B. n = 3:  1, 1, 1);  gerechnet bis
                                                 n = 60:  KEIN Gegenbeispiel.  Ein allgemeiner Satz liegt nicht vor
EM7  nicht_symmetrisch       EICHUNG n = 4…12    Trito und Deutero sind nicht symmetrisch:  Ausbreitung und Reduktion verlaufen verschieden
                                                 (n = 4:  1, 7, 6, 1 und 1, 2, 1, 1)
```

Hilfssätze:  `rgsList_succ`, `anz_cons`, `anz_append`, `anz_flatMap`, `foldr_max_append`, `klassenZahl_append`, `klassenZahl_cons`,
`anz_erw_cons`, `rgsList_ne_nil`, `summe`, `st_eins`, `st_selbst`, `st_pos`, `st_zwei`.  Definitionen:  `klassenZahl`, `tritoZahl`, `erw`,
`anz`, `teile`, `deuteroZahl`, `einfuegen`, `sortiert`, `groessen`, `Unimodal`.

**Profile:**  alle 24 Sätze ohne `Classical.choice` (Wachen unten).  Eine Stelle war zu umgehen:  `anz_cons` zog Choice über die
Fallunterscheidung mit `beq_iff_eq`;  jetzt über den Bool-Wert (`of_decide_eq_true`).  Technisch:  zwei Eichungen von EM3 brauchen
`synthInstance.maxSize 1024` (die Entscheidbarkeitsinstanz der verschachtelten Aussage überschreitet mit Mathlib im Import die Standardgröße);
das berührt kein Profil.  Kein `native_decide`, kein `sorry`, kein True-Feld.

**EM8 (Rechnung, kein Satz):**  Der Gipfel der Trito-Zählung wandert mit n (k = 4 bei n = 7…9, k = 10 bei n = 25…28, k = 11 bei
n = 29, 30);  der Gipfel der Deutero-Zählung ebenfalls, mit Gleichständen (n = 13, 14:  k = 4, 5).  T_Vorprobe_Skripte/Emanation_Rechnung.out.

## QUELLE

LZEE S. 18, 19, 26 — TEXTSCHICHT (gg_logik-zeit-emanat-evol.pdf, vordenker-Edition;  Erstdruck Arbeitsgemeinschaft für Forschung NRW, Heft
136, 1967);  am Bild:  Hermeneutes.  S. 18:  in Proto jede Klasse ein Exemplar;  in Deutero alle außer der ersten, der vorletzten und der
letzten mehrere;  in Trito alle außer der ersten und der letzten mehrere;  der Prozess gehe „von einer Einheit aus" und finde „in einer
anderen Einheit sein Ende — zwischen diesen beiden Enden erst eine Ausbreitung, dann aber eine Reduktion".  Die Zählung durch
Stirlingzahlen:  Günther 1962 (Cybernetic Ontology, nach H. von Foerster), Mahler 1993.

## ZUORDNUNG

Dass Günthers Klassen „fester Länge" die Klassen nach der Zahl der Kenogramme sind und dass „Ausbreitung, dann Reduktion" die
Unimodalität meint:  ZUORDNUNG, nah am Wortlaut von S. 18.  Dass `rgsList` die Tritostruktur und `deuteroZahl` die Deuterostruktur im Sinn
von LZEE zählt:  Definitionswahl des Bestands (Kenogram/Basic) bzw. dieser Sonde.

## NICHT

„die angekündigte Analyse" — die Sonde liefert EIN Stück davon:  die Struktureigenschaften der Zählung (S. 26).  Die „sehr intrikaten
Eigenschaften dieser Reversibilität" (S. 19) bestimmt Günther nicht;  die Sonde sagt nur, was sie NICHT ist:  nicht die Symmetrie der
Klassengrößen (EM7).  Nicht:  „Günther meinte Unimodalität";  nicht:  „Reversibilität = …".  Kein Bezug zu den Negationskreisen
(InvestigationPost#19:  andere Ebene).  Harper, Lieb nur als Literaturhinweis (nicht gelesen).
-/

namespace Reformulation.Proemial.EmanationsZaehlung

open Reformulation.Kenogram (rgsList)

/-! ## Die Klassenzahl einer Kenogrammfolge und die Trito-Zählung -/

/-- **Die Zahl der Klassen** (verschiedenen Kenogramme) einer Normalform:  größtes Symbol + 1;  die leere Folge hat keine. -/
def klassenZahl : List ℕ → ℕ
  | [] => 0
  | a :: l => (a :: l).foldr max 0 + 1

/-- **Trito-Zählung:**  wie viele Kenogrammfolgen der Länge n haben genau k Klassen. -/
def tritoZahl (n k : ℕ) : ℕ := ((rgsList n).filter (fun l => klassenZahl l == k)).length

/-- Die Erweiterungen einer Folge, wie `rgsList` sie bildet. -/
def erw (l : List ℕ) : List (List ℕ) := (List.range (l.foldr max 0 + (if l.isEmpty then 1 else 2))).map (fun v => l ++ [v])

theorem rgsList_succ (n : ℕ) : rgsList (n + 1) = (rgsList n).flatMap erw := rfl

/-- Anzahl der Folgen in `L` mit k Klassen. -/
def anz (L : List (List ℕ)) (k : ℕ) : ℕ := (L.filter (fun l => klassenZahl l == k)).length

theorem anz_cons (l : List ℕ) (L : List (List ℕ)) (k : ℕ) :
    anz (l :: L) k = (if klassenZahl l = k then 1 else 0) + anz L k := by
  unfold anz
  rw [List.filter_cons]
  cases hc : (klassenZahl l == k) with
  | true =>
    rw [if_pos rfl, if_pos (of_decide_eq_true hc), List.length_cons, Nat.add_comm]
  | false =>
    rw [if_neg Bool.false_ne_true, if_neg (of_decide_eq_false hc), Nat.zero_add]

theorem anz_append (A B : List (List ℕ)) (k : ℕ) : anz (A ++ B) k = anz A k + anz B k := by
  unfold anz
  rw [List.filter_append, List.length_append]

theorem anz_flatMap (f : List ℕ → List (List ℕ)) (k : ℕ) :
    ∀ L : List (List ℕ), anz (L.flatMap f) k = (L.map (fun l => anz (f l) k)).sum
  | [] => rfl
  | l :: L => by rw [List.flatMap_cons, anz_append, anz_flatMap f k L, List.map_cons, List.sum_cons]

theorem foldr_max_append (l : List ℕ) (v : ℕ) : (l ++ [v]).foldr max 0 = max (l.foldr max 0) v := by
  induction l with
  | nil => show max v 0 = max 0 v; exact Nat.max_comm v 0
  | cons a l ih => rw [List.cons_append, List.foldr_cons, List.foldr_cons, ih, Nat.max_assoc]

theorem klassenZahl_append (l : List ℕ) (v : ℕ) : klassenZahl (l ++ [v]) = max (l.foldr max 0) v + 1 := by
  cases l with
  | nil => show max v 0 + 1 = max 0 v + 1; rw [Nat.max_comm]
  | cons a l =>
    show (a :: (l ++ [v])).foldr max 0 + 1 = _
    rw [← List.cons_append, foldr_max_append]

theorem klassenZahl_cons (a : ℕ) (l : List ℕ) : klassenZahl (a :: l) = (a :: l).foldr max 0 + 1 := rfl

/-- Zählung über eine Zahlenspanne:  wie viele v < M erfüllen p. -/
theorem anz_erw_cons (a : ℕ) (l : List ℕ) (k : ℕ) :
    anz (erw (a :: l)) k =
      (if klassenZahl (a :: l) = k then klassenZahl (a :: l) else 0) +
      (if klassenZahl (a :: l) + 1 = k then 1 else 0) := by
  rw [klassenZahl_cons]
  generalize hb : (a :: l).foldr max 0 = b
  have hrange : erw (a :: l) = (List.range (b + 2)).map (fun v => (a :: l) ++ [v]) := by
    unfold erw; rw [hb]; rfl
  rw [hrange]
  have key : ∀ v, klassenZahl ((a :: l) ++ [v]) = max b v + 1 := fun v => by rw [klassenZahl_append, hb]
  -- Zählen über range (b + 2) = range (b + 1) ++ [b + 1]
  have hsplit : ∀ j, j ≤ b + 1 → anz ((List.range j).map (fun v => (a :: l) ++ [v])) k =
      (if b + 1 = k then j else 0) := by
    intro j
    induction j with
    | zero => intro _; rw [List.range_zero, List.map_nil]; split <;> rfl
    | succ j ih =>
      intro hj
      rw [List.range_succ, List.map_append, anz_append, ih (by omega), List.map_cons, List.map_nil, anz_cons, key]
      have hm : max b j = b := Nat.max_eq_left (by omega)
      rw [hm]
      unfold anz
      rw [List.filter_nil, List.length_nil]
      by_cases h : b + 1 = k
      · rw [if_pos h, if_pos h, if_pos h]
      · rw [if_neg h, if_neg h, if_neg h]
  rw [show b + 2 = (b + 1) + 1 from rfl, List.range_succ, List.map_append, anz_append, hsplit (b + 1) (Nat.le_refl _),
    List.map_cons, List.map_nil, anz_cons, key, Nat.max_eq_right (Nat.le_succ b)]
  unfold anz
  rw [List.filter_nil, List.length_nil]
  split_ifs <;> omega

theorem rgsList_ne_nil : ∀ {n : ℕ}, ∀ l ∈ rgsList (n + 1), l ≠ []
  | n, l, hl => by
    rw [rgsList_succ] at hl
    obtain ⟨l', _, hl'⟩ := List.mem_flatMap.mp hl
    unfold erw at hl'
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hl'
    exact List.append_ne_nil_of_right_ne_nil l' (List.cons_ne_nil v [])

/-- Summenumformung für die Rekursion. -/
theorem summe (k : ℕ) : ∀ L : List (List ℕ), (∀ l ∈ L, l ≠ []) →
    (L.map (fun l => anz (erw l) (k + 1))).sum = (k + 1) * anz L (k + 1) + anz L k
  | [], _ => rfl
  | l :: L, hne => by
    have hl : l ≠ [] := hne l List.mem_cons_self
    obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hl
    rw [List.map_cons, List.sum_cons, summe k L (fun x hx => hne x (List.mem_cons_of_mem _ hx)), anz_erw_cons,
      anz_cons, anz_cons]
    generalize klassenZahl (a :: t) = c
    rw [Nat.mul_add]
    split_ifs <;> simp only [Nat.mul_one, Nat.mul_zero] <;> omega

/-- (EM1) **Die Trito-Zählung ist die Stirlingzahl zweiter Art** — für jede Länge und jede Klassenzahl. -/
theorem trito_eq_stirling : ∀ n k : ℕ, tritoZahl n k = Nat.stirlingSecond n k
  | 0, 0 => rfl
  | 0, _ + 1 => rfl
  | n + 1, 0 => by
    show anz (rgsList (n + 1)) 0 = 0
    have : ∀ L : List (List ℕ), (∀ l ∈ L, l ≠ []) → anz L 0 = 0 := by
      intro L
      induction L with
      | nil => intro _; rfl
      | cons l L ih =>
        intro hne
        obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil (hne l List.mem_cons_self)
        rw [anz_cons, if_neg (by rw [klassenZahl_cons]; omega), ih (fun x hx => hne x (List.mem_cons_of_mem _ hx))]
    exact this _ rgsList_ne_nil
  | n + 1, k + 1 => by
    show anz (rgsList (n + 1)) (k + 1) = _
    cases n with
    | zero =>
      cases k with
      | zero => rfl
      | succ k => show anz [[0]] (k + 2) = 0; rfl
    | succ n =>
      rw [rgsList_succ, anz_flatMap, summe k _ rgsList_ne_nil, Nat.stirlingSecond_succ_succ]
      show (k + 1) * tritoZahl (n + 1) (k + 1) + tritoZahl (n + 1) k = _
      rw [trito_eq_stirling (n + 1) (k + 1), trito_eq_stirling (n + 1) k]

/-! ## EM2 — Günther S. 18, Trito:  die erste und die letzte Klasse je ein Exemplar, alle anderen mehrere -/

theorem st_eins : ∀ n : ℕ, Nat.stirlingSecond (n + 1) 1 = 1
  | 0 => rfl
  | n + 1 => by rw [Nat.stirlingSecond_succ_succ, st_eins n, Nat.stirlingSecond_succ_zero]

theorem st_selbst : ∀ n : ℕ, Nat.stirlingSecond n n = 1
  | 0 => rfl
  | n + 1 => by
    rw [Nat.stirlingSecond_succ_succ, st_selbst n, Nat.stirlingSecond_eq_zero_of_lt (Nat.lt_succ_self n), Nat.mul_zero]

theorem st_pos : ∀ n k : ℕ, 1 ≤ k → k ≤ n → 1 ≤ Nat.stirlingSecond n k
  | 0, k, h1, h2 => absurd (Nat.le_trans h1 h2) (by decide)
  | n + 1, 0, h1, _ => absurd h1 (by decide)
  | n + 1, k + 1, _, h2 => by
    rw [Nat.stirlingSecond_succ_succ]
    cases k with
    | zero =>
      cases n with
      | zero => decide
      | succ n => rw [Nat.zero_add, Nat.one_mul, st_eins n]; exact Nat.le_add_right 1 _
    | succ k =>
      have h := st_pos n (k + 1) (by omega) (by omega)
      exact Nat.le_trans h (Nat.le_add_left _ _)

theorem st_zwei : ∀ n k : ℕ, 1 < k → k < n → 2 ≤ Nat.stirlingSecond n k
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | _ + 1, 0, h, _ => absurd h (by decide)
  | n + 1, k + 1, h1, h2 => by
    rw [Nat.stirlingSecond_succ_succ]
    have hp : 1 ≤ Nat.stirlingSecond n (k + 1) := st_pos n (k + 1) (by omega) (by omega)
    have hq : 1 ≤ Nat.stirlingSecond n k := st_pos n k (by omega) (by omega)
    have hm : 2 * 1 ≤ (k + 1) * Nat.stirlingSecond n (k + 1) := Nat.mul_le_mul (by omega) hp
    omega

/-- (EM2) **Günther S. 18, Trito:**  die Klasse mit einer Klasse und die mit n Klassen haben je ein Exemplar, alle dazwischen mehrere. -/
theorem trito_guenther (n : ℕ) (hn : 1 ≤ n) :
    tritoZahl n 1 = 1 ∧ tritoZahl n n = 1 ∧ ∀ k, 1 < k → k < n → 2 ≤ tritoZahl n k := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine ⟨by rw [trito_eq_stirling, st_eins], by rw [trito_eq_stirling, st_selbst], fun k h1 h2 => ?_⟩
  rw [trito_eq_stirling]
  exact st_zwei (m + 1) k h1 h2

/-! ## EM4 — Proto:  jede Klasse ein Exemplar -/

/-- (EM4) **Proto:**  zu jeder Klassenzahl 1 ≤ k ≤ n gibt es eine Kenogrammfolge der Länge n mit k Klassen;  ihr Proto-Zeichen ist die
    Zahl k selbst — jede Proto-Klasse hat genau ein Exemplar (trivial, der Vollständigkeit). -/
theorem proto_klasse (n k : ℕ) (h1 : 1 ≤ k) (h2 : k ≤ n) : ∃ l ∈ rgsList n, klassenZahl l = k := by
  have hpos : 0 < tritoZahl n k := by rw [trito_eq_stirling]; exact st_pos n k h1 h2
  obtain ⟨l, hl⟩ := List.exists_mem_of_length_pos hpos
  exact ⟨l, (List.mem_filter.mp hl).1, of_decide_eq_true (List.mem_filter.mp hl).2⟩

/-! ## EM3 — Deutero:  die Partitionen von n in genau k Teile -/

/-- Anzahl der nicht steigenden Folgen aus k positiven Teilen, jeder höchstens b, mit Summe n. -/
def teile : ℕ → ℕ → ℕ → ℕ
  | 0, n, _ => if n = 0 then 1 else 0
  | k + 1, n, b => ((List.range (min b n)).map (fun i => teile k (n - (i + 1)) (i + 1))).sum

/-- **Deutero-Zählung:**  wie viele Deutero-Klassen (Multisets der Klassengrößen) mit k Teilen die Länge n hat — die Partitionen von n in
    genau k Teile. -/
def deuteroZahl (n k : ℕ) : ℕ := teile k n n

set_option synthInstance.maxSize 1024 in
/-- (EM3a) **Günther S. 18, Deutero, EICHUNG n = 4 … 12:**  ein Exemplar haben nur die Klassen mit 1, n−1 und n Teilen … -/
theorem deutero_eins : ∀ n < 13, ∀ k < n + 1, 4 ≤ n → 1 ≤ k →
    deuteroZahl n k = 1 → (k = 1 ∨ k = n - 1 ∨ k = n) := by
  decide +kernel

set_option synthInstance.maxSize 1024 in
/-- (EM3b) … und diese drei haben je eines … -/
theorem deutero_eins_rueck : ∀ n < 13, ∀ k < n + 1, 4 ≤ n → 1 ≤ k →
    (k = 1 ∨ k = n - 1 ∨ k = n) → deuteroZahl n k = 1 := by
  decide +kernel

/-- (EM3c) … alle anderen haben mehrere. -/
theorem deutero_mehrere : ∀ n < 13, ∀ k < n + 1, 4 ≤ n → 1 ≤ k →
    deuteroZahl n k ≠ 1 → 2 ≤ deuteroZahl n k := by
  decide +kernel

/-- Die Deutero-Klasse einer Folge:  ihre Klassengrößen, absteigend sortiert. -/
def einfuegen (a : ℕ) : List ℕ → List ℕ
  | [] => [a]
  | b :: t => if b ≤ a then a :: b :: t else b :: einfuegen a t

def sortiert : List ℕ → List ℕ
  | [] => []
  | a :: t => einfuegen a (sortiert t)

def groessen (l : List ℕ) : List ℕ := sortiert ((List.range (klassenZahl l)).map (fun v => l.count v))

/-- (EM3, Abgleich) **Die Deutero-Zählung ist das Bild der Kenogrammfolgen**, EICHUNG n ≤ 7:  die Zahl der verschiedenen Klassengrößen-
    Muster unter den Folgen der Länge n mit k Klassen ist `deuteroZahl n k`. -/
theorem deutero_bild : ∀ n < 8, ∀ k < n + 1,
    (((rgsList n).filter (fun l => klassenZahl l == k)).map groessen).eraseDups.length = deuteroZahl n k := by
  decide +kernel

/-! ## EM5, EM6 — „erst eine Ausbreitung, dann aber eine Reduktion":  Unimodalität -/

/-- **Unimodal** (erst nicht fallend, dann nicht steigend) für die ersten n Werte von f:  kein Wert liegt unter beiden Nachbarn
    irgendeines Paares, das ihn einschließt. -/
def Unimodal (f : ℕ → ℕ) (n : ℕ) : Prop := ∀ i < n, ∀ j < n, ∀ l < n, i < j → j < l → min (f i) (f l) ≤ f j

instance (f : ℕ → ℕ) (n : ℕ) : Decidable (Unimodal f n) := by unfold Unimodal; infer_instance

/-- (EM5) **Trito, EICHUNG n ≤ 12:**  die Zahl der Folgen mit k Klassen steigt erst und fällt dann (k = 1 … n). -/
theorem trito_unimodal : ∀ n < 13, Unimodal (fun k => Nat.stirlingSecond n (k + 1)) n := by
  decide +kernel

/-- (EM6) **Deutero, EICHUNG n ≤ 12:**  ebenso die Zahl der Deutero-Klassen mit k Teilen.  (Gerechnet bis n = 60, ausserhalb des Baums. -/
theorem deutero_unimodal : ∀ n < 13, Unimodal (fun k => deuteroZahl n (k + 1)) n := by
  decide +kernel

/-! ## EM7 — die Folge ist nicht symmetrisch -/

/-- (EM7) **Die Zählung ist nicht symmetrisch, EICHUNG n = 4 … 12:**  Ausbreitung und Reduktion verlaufen verschieden — für Trito und für
    Deutero gibt es ein k mit verschiedener Zahl an k und an n + 1 − k. -/
theorem nicht_symmetrisch : ∀ n < 13, 4 ≤ n →
    (∃ k < n + 1, Nat.stirlingSecond n k ≠ Nat.stirlingSecond n (n + 1 - k)) ∧
    (∃ k < n + 1, deuteroZahl n k ≠ deuteroZahl n (n + 1 - k)) := by
  decide +kernel

end Reformulation.Proemial.EmanationsZaehlung

/-! ## Axiom-Wachen (gemessen, verbatim) -/

/-- info: 'Reformulation.Proemial.EmanationsZaehlung.rgsList_succ' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Proemial.EmanationsZaehlung.rgsList_succ

/-- info: 'Reformulation.Proemial.EmanationsZaehlung.anz_cons' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.EmanationsZaehlung.anz_cons

/-- info: 'Reformulation.Proemial.EmanationsZaehlung.anz_append' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.EmanationsZaehlung.anz_append

/-- info: 'Reformulation.Proemial.EmanationsZaehlung.anz_flatMap' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.EmanationsZaehlung.anz_flatMap

/-- info: 'Reformulation.Proemial.EmanationsZaehlung.foldr_max_append' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.EmanationsZaehlung.foldr_max_append

/-- info: 'Reformulation.Proemial.EmanationsZaehlung.klassenZahl_append' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.EmanationsZaehlung.klassenZahl_append

/-- info: 'Reformulation.Proemial.EmanationsZaehlung.klassenZahl_cons' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Proemial.EmanationsZaehlung.klassenZahl_cons

/-- info: 'Reformulation.Proemial.EmanationsZaehlung.anz_erw_cons' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.EmanationsZaehlung.anz_erw_cons

/-- info: 'Reformulation.Proemial.EmanationsZaehlung.rgsList_ne_nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.EmanationsZaehlung.rgsList_ne_nil

/-- info: 'Reformulation.Proemial.EmanationsZaehlung.summe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.EmanationsZaehlung.summe

/-- info: 'Reformulation.Proemial.EmanationsZaehlung.trito_eq_stirling' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.EmanationsZaehlung.trito_eq_stirling

/-- info: 'Reformulation.Proemial.EmanationsZaehlung.st_eins' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Proemial.EmanationsZaehlung.st_eins

/-- info: 'Reformulation.Proemial.EmanationsZaehlung.st_selbst' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.EmanationsZaehlung.st_selbst

/-- info: 'Reformulation.Proemial.EmanationsZaehlung.st_pos' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.EmanationsZaehlung.st_pos

/-- info: 'Reformulation.Proemial.EmanationsZaehlung.st_zwei' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.EmanationsZaehlung.st_zwei

/-- info: 'Reformulation.Proemial.EmanationsZaehlung.trito_guenther' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.EmanationsZaehlung.trito_guenther

/-- info: 'Reformulation.Proemial.EmanationsZaehlung.proto_klasse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.EmanationsZaehlung.proto_klasse

/-- info: 'Reformulation.Proemial.EmanationsZaehlung.deutero_eins' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.EmanationsZaehlung.deutero_eins

/-- info: 'Reformulation.Proemial.EmanationsZaehlung.deutero_eins_rueck' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.EmanationsZaehlung.deutero_eins_rueck

/-- info: 'Reformulation.Proemial.EmanationsZaehlung.deutero_mehrere' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.EmanationsZaehlung.deutero_mehrere

/-- info: 'Reformulation.Proemial.EmanationsZaehlung.deutero_bild' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.EmanationsZaehlung.deutero_bild

/-- info: 'Reformulation.Proemial.EmanationsZaehlung.trito_unimodal' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Proemial.EmanationsZaehlung.trito_unimodal

/-- info: 'Reformulation.Proemial.EmanationsZaehlung.deutero_unimodal' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.EmanationsZaehlung.deutero_unimodal

/-- info: 'Reformulation.Proemial.EmanationsZaehlung.nicht_symmetrisch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.EmanationsZaehlung.nicht_symmetrisch
