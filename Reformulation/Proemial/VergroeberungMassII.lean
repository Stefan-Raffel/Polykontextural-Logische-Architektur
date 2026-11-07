import Reformulation.Proemial.VergroeberungMass

/-!
# Proemial.VergroeberungMassII — die größte Faser, der Stirling-Schluss

STANDALONE, NICHT im Aggregat;  Target `Probes`.  AxiomGate unberührt.  Sonde nach
`KorpusRev2/Prompt_Instanz_Sonde_Vergroeberung_Mass_II_Mathematiker.md` (Mathematiker, 7.11.2026 09:27;  Architekt 09:26).
Nachfolge zu `VergroeberungMass` (30.10.2026);  konsumiert von dort `partitionen`, `faser`, `teilListe`, `mem_rgsList_frei`,
`groessen_eq`, `sortiert_perm`, `sortiert_pairwise`, `zaehlen_pos`, `summe_zaehlen`, von `EmanationsZaehlung` `klassenZahl`,
`tritoZahl`, `groessen`, `teilListe`-Zählung `teile`, EM1 `trito_eq_stirling`;  ändert nichts davon.

**Namen (Regel 9):**  alle neuen Namen vor der Definition über `Reformulation/` und `Foreign/` geprüft;  0 Treffer
(„drin" steht zweimal in Prosa, nie als Bezeichner).

## WAS

```text
W1  groesste_faser      EICHUNG n ≤ 7     Klasse und Größe der größten Faser:  3 [2,1] 3;  4 [2,1,1] 6;  5 [2,2,1] 15;  6 [3,2,1] 60;
                                          7 [3,2,1,1] 210  (n = 1:  (1) 1;  n = 2:  (2) 1).
    groesste_ist_max    EICHUNG n ≤ 7     `groesste n` ist eine der Fasern, und keine Faser ist größer.
    groesste_eindeutig  MESSUNG n ≤ 7     die größte Faser ist ab n = 3 eindeutig;  bei n = 2 erreichen ZWEI Partitionen das Maximum 1
                                          ((2) und (1,1)).  n = 8 … 10 nur gerechnet (unten).
W2  stirling_schluss    SATZ, jede Länge  Σ_{λ ⊢ n, k Teile} |faser n λ| = tritoZahl n k.
    stirling_schluss_stirling  SATZ       dasselbe = Nat.stirlingSecond n k (über EM1).
                                          Der Turm schließt sich in Zahlen:  Trito → Deutero → Proto, und die Faser von proto über k ist
                                          die Summe der Fasern von deutero über den Partitionen mit k Teilen.
    Bausteine, allgemein:  length_groessen (klassenZahl = Länge der Größenliste), teilListe_laenge, mem_teilListe_of (die Teilelisten
    erschöpfen die nicht steigenden positiven Listen), teilListe_nodup, summe_fasern (die Zählbrücke), groessen_mem_teilListe (jede
    Normalform liegt über einer Partition — die allgemeine Fassung der ersten Hälfte von `faser_summe`).
W3  nur Rechnung, kein Lean:  T_Vorprobe_Skripte/Vergroeberungsmass_II_Kette.py (unten).
```

**Wie W2 geht.**  `faser n λ` ist ein Filter über `rgsList n`;  über einer duplikatfreien Liste von Partitionen ist die Summe der
Filterlängen die Länge EINES Filters, „Größenliste liegt in der Liste" (`summe_fasern`, mit `drin` als `Bool`-Mitgliedschaft ohne
`decide`).  Für die Teilelisten mit k Teilen ist dieser Filter genau „klassenZahl = k":  hin über die Länge (`teilListe_laenge`,
`length_groessen`), zurück über `mem_teilListe_of` mit Länge, Summe (`summe_zaehlen`), Positivität (`zaehlen_pos`), Ordnung
(`sortiert_pairwise`) und Schranke (`mem_le_sum`).  `List.pairwise_lt_range` trägt `Classical.choice`;  darum `range_pairwise_lt`
über `List.range_succ`.  Die `==`-Instanz der Zählbrücke ist `[BEq β] [LawfulBEq β]`, weil `faser` Listen mit `instBEqList`
vergleicht;  mit `[DecidableEq β]` passt der Satz nicht auf `faser` (gemessen:  `rw` findet das Muster nicht).

**Profile:**  kein Satz trägt `Classical.choice` (Wachen unten);  `groesste_faser` und `groesste_eindeutig` sind axiomfrei.
Kein `native_decide`, kein `sorry`, kein True-Feld, keine reelle Zahl.

**Kosten (lokal, M2 Max, `/usr/bin/time -l`):**  Importgrundlinie 2,0 s / 1,68 GB;  ganze Datei 11,9 s / 2,74 GB.  Die drei
Kernelprüfungen rechnen je `faser` für alle Partitionen bis n = 7 (wie `faser_formel`);  n = 8 bleibt aus demselben Grund wie dort
draußen (30.10.:  n ≤ 8 brach den CI-Läufer).

**Gerechnet, kein Satz** (`T_Vorprobe_Skripte/Vergroeberungsmass_II_Kette.py`, Fasergrößen nach der Formel, für n ≤ 8 gegen die
Aufzählung geprüft;  deckt sich mit `Vergroeberungsmass_Vorrechnung.py` des Mathematikers):

```text
n          8            9              10
größte     840 [3,2,2,1] 3780 [3,2,2,1,1] 12600 [4,3,2,1]   (eindeutig)
Anteil an Bell:  n = 3 … 12:  0,600  0,400  0,288  0,296  0,240  0,203  0,179  0,109  0,102  0,099   — fällt, nicht streng (5 → 6 steigt)
```

Beobachtung, kein Satz:  die größte Faser nähert sich Treppen ([4,3,2,1] bei n = 10);  welche Gestalt sie allgemein hat, behauptet
diese Datei nicht.

**Kettenregel (W3, Gleichverteilung auf Trito, Bit):**  Verlust(T→P) = Verlust(T→D) + Verlust(D→P) hält für n = 1 … 12 bis auf
Rundung (isclose 1e-12);  sie ist die Identität H(T) − H(P) = (H(T) − H(D)) + (H(D) − H(P)).  Verlust(T→D) wie im Kopf von
`VergroeberungMass` (0, 0, 0,951, 1,884, 3,267, …);  Verlust(D→P):  0, 0, 0, 0,460, 0,732, 1,068, 1,367, 1,671, 1,949, 2,223, 2,483,
2,735;  H(P):  0, 1, 1,371, 1,563, 1,702, 1,814, 1,905, 1,982, 2,049, 2,108, 2,161, 2,209.  Die Formel des Prompts für Verlust(D→P)
liest sich als Σ_k p_k log₂(Σ_{λ mit k Teilen} p_λ / p_k) = 0;  gerechnet ist H(D) − H(P), wie der Prompt es ausschreibt.

**Was die Zahlen erzwingt (Regel 11):**  W2 ist die Zerlegung der Mengenpartitionen nach ihrem Blocktyp, Standardkombinatorik;
die Kettenregel ist eine Identität der Logarithmen.  Beides ist Arithmetik, kein Indiz für eine Quelle.

**Ertrag:**  W2 ist FOLGERUNG (ein Satz für jede Länge, der im Bestand nicht stand;  `faser_summe` war Eichung).  W1 ist Eichung
und Messung.

## ZUSAMMENSCHAU (unsere;  nicht im Lean)

Unter Gleichverteilung auf den Normalformen hat die Wahrscheinlichkeit einer Deutero-Klasse die Gestalt p_λ = |faser λ| / Bell n
= e^{S_λ} / Z mit S_λ = ln |faser λ|:  die Form von Thorne/Blandford, *Modern Classical Physics*, 5.6, Gl. (5.69a), S. 261
(Textschicht von `KorpusRev1/Thorne-Physics-Chapter5_6.pdf`:  „p(E,V,N;y) = N_states(E,V,N;y) / Σ_y N_states … = const × exp[S/k_B]",
„probabilities for fluctuations in closed systems").  Dort Phasenraumvolumen, hier Zahl der Normalformen;  dort Physik, hier
Kombinatorik.  Der wahrscheinlichste grobe Zustand ist der mit der größten Faser (W1).  Mehr nicht.

## QUELLE

Keine Stelle Günthers wird hier gelesen oder gedeutet (Prompt §2).  Die Zusammenschau oben ist die einzige Quellenangabe.

## UNSER

Die Größenfunktion `groesste`, die Zählbrücke `summe_fasern`, der Stirling-Schluss, die Kettenregel-Rechnung.

## NICHT

Keine reelle Zahl, kein Logarithmus im Lean;  keines der vier Wörter aus Prompt §2 in Namen oder Docstrings;  keine
Behauptung über die Gestalt der größten Faser;  keine Lesart zu Lille S. 17, Assmann, Günther;  nicht Rev11.
-/

namespace Reformulation.Proemial.VergroeberungMassII

open Reformulation.Kenogram
open Reformulation.Proemial.EmanationsZaehlung (klassenZahl tritoZahl teile deuteroZahl sortiert groessen
  trito_eq_stirling)
open Reformulation.Proemial.VergroeberungMass

/-! ## W1 — die größte Faser -/

/-- Je Partition ihre Fasergröße, in der Reihenfolge von `partitionen`. -/
def fasergroessen (n : ℕ) : List (List ℕ × ℕ) :=
  (partitionen n).map (fun lam => (lam, (faser n lam).length))

/-- Die größte Faser:  die erste Partition mit maximaler Fasergröße, und diese Größe. -/
def groesste (n : ℕ) : List ℕ × ℕ :=
  (fasergroessen n).foldl (fun b x => if b.2 < x.2 then x else b) ([], 0)

/-- Wie viele Partitionen die maximale Fasergröße erreichen. -/
def maxZahl (n : ℕ) : ℕ := ((fasergroessen n).filter (fun x => x.2 == (groesste n).2)).length

/-- (W1a) **EICHUNG n ≤ 7:**  Klasse und Größe der größten Faser. -/
theorem groesste_faser :
    groesste 1 = ([1], 1) ∧ groesste 2 = ([2], 1) ∧ groesste 3 = ([2, 1], 3) ∧
      groesste 4 = ([2, 1, 1], 6) ∧ groesste 5 = ([2, 2, 1], 15) ∧ groesste 6 = ([3, 2, 1], 60) ∧
      groesste 7 = ([3, 2, 1, 1], 210) := by
  decide +kernel

/-- (W1a, Abschluss) **EICHUNG n ≤ 7:**  `groesste` ist eine Faser, und keine ist größer. -/
theorem groesste_ist_max : ∀ n < 8,
    groesste n ∈ fasergroessen n ∧ ∀ x ∈ fasergroessen n, x.2 ≤ (groesste n).2 := by
  decide +kernel

/-- (W1b) **MESSUNG n ≤ 7:**  wie viele Partitionen das Maximum erreichen — ab `n = 3` genau eine, bei `n = 2` zwei. -/
theorem groesste_eindeutig :
    maxZahl 1 = 1 ∧ maxZahl 2 = 2 ∧ maxZahl 3 = 1 ∧ maxZahl 4 = 1 ∧ maxZahl 5 = 1 ∧
      maxZahl 6 = 1 ∧ maxZahl 7 = 1 := by
  decide +kernel

/-! ## W2 — der Stirling-Schluss -/

/-- Die Zahl der Klassen ist die Länge der Größenliste. -/
theorem length_groessen (l : List ℕ) : (groessen l).length = klassenZahl l := by
  unfold groessen
  rw [(sortiert_perm _).length_eq, List.length_map, List.length_range]

/-- Jede Teileliste mit `k` Teilen hat Länge `k`. -/
theorem teilListe_laenge : ∀ (k n b : ℕ), ∀ t ∈ teilListe k n b, t.length = k
  | 0, n, b, t, ht => by
    by_cases h : n = 0
    · rw [teilListe, if_pos h, List.mem_singleton] at ht
      rw [ht]
      rfl
    · rw [teilListe, if_neg h] at ht
      exact absurd ht List.not_mem_nil
  | k + 1, n, b, t, ht => by
    rw [teilListe, List.mem_flatMap] at ht
    obtain ⟨i, _, ht⟩ := ht
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
    rw [List.length_cons, teilListe_laenge k _ _ u hu]

theorem mem_le_sum : ∀ (t : List ℕ) (x : ℕ), x ∈ t → x ≤ t.sum
  | [], x, h => absurd h List.not_mem_nil
  | a :: u, x, h => by
    rw [List.sum_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_add_right _ _
    · exact Nat.le_trans (mem_le_sum u x h) (Nat.le_add_left _ _)

/-- Eine nicht steigende Liste positiver Zahlen mit Summe `n`, Länge `k` und Teilen `≤ b` steht in `teilListe k n b`. -/
theorem mem_teilListe_of : ∀ (k : ℕ) (t : List ℕ) (n b : ℕ), t.length = k → t.sum = n → (∀ x ∈ t, 1 ≤ x) →
    t.Pairwise (· ≥ ·) → (∀ x ∈ t, x ≤ b) → t ∈ teilListe k n b
  | 0, t, n, b, hl, hs, _, _, _ => by
    have ht : t = [] := List.length_eq_zero_iff.mp hl
    subst ht
    have hn : n = 0 := hs.symm.trans List.sum_nil
    rw [teilListe, if_pos hn]
    exact List.mem_singleton.mpr rfl
  | k + 1, t, n, b, hl, hs, hp, hw, hb => by
    cases t with
    | nil => exact absurd hl (Nat.succ_ne_zero k).symm
    | cons a u =>
      have ha1 : 1 ≤ a := hp a List.mem_cons_self
      have hab : a ≤ b := hb a List.mem_cons_self
      rw [List.sum_cons] at hs
      have han : a ≤ n := hs ▸ Nat.le_add_right a u.sum
      have hlu : u.length = k := by
        rw [List.length_cons] at hl
        exact Nat.succ.inj hl
      rw [teilListe, List.mem_flatMap]
      refine ⟨a - 1, List.mem_range.mpr (by omega), List.mem_map.mpr ⟨u, ?_, ?_⟩⟩
      · rw [Nat.sub_add_cancel ha1]
        apply mem_teilListe_of k u (n - a) a hlu (by omega)
        · exact fun x hx => hp x (List.mem_cons_of_mem a hx)
        · exact (List.pairwise_cons.mp hw).2
        · exact fun x hx => (List.pairwise_cons.mp hw).1 x hx
      · rw [Nat.sub_add_cancel ha1]

/-- `List.pairwise_lt_range` trägt `Classical.choice` (Mathlib);  dieselbe Aussage ohne. -/
theorem range_pairwise_lt : ∀ m : ℕ, (List.range m).Pairwise (· < ·)
  | 0 => List.Pairwise.nil
  | m + 1 => by
    rw [List.range_succ, List.pairwise_append]
    refine ⟨range_pairwise_lt m, List.pairwise_cons.mpr ⟨fun _ h => absurd h List.not_mem_nil, List.Pairwise.nil⟩,
      fun a ha b hb => ?_⟩
    rw [List.mem_singleton.mp hb]
    exact List.mem_range.mp ha

/-- `teilListe k n b` ist duplikatfrei:  die Teillisten verschiedener Köpfe sind disjunkt. -/
theorem teilListe_nodup : ∀ k n b : ℕ, (teilListe k n b).Nodup
  | 0, n, b => by
    by_cases h : n = 0
    · rw [teilListe, if_pos h]
      exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
    · rw [teilListe, if_neg h]
      exact List.nodup_nil
  | k + 1, n, b => by
    rw [teilListe, List.nodup_flatMap]
    refine ⟨fun i _ => (teilListe_nodup k _ _).map List.cons_injective, (range_pairwise_lt _).imp ?_⟩
    intro i j hij
    show List.Disjoint _ _
    intro t hti htj
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp hti
    obtain ⟨v, _, hv⟩ := List.mem_map.mp htj
    have := (List.cons.inj hv).1
    omega

/-- Mitgliedschaft als `Bool`, ohne `decide`. -/
def drin {β : Type} [BEq β] (y : β) : List β → Bool
  | [] => false
  | x :: L => (y == x) || drin y L

theorem drin_iff {β : Type} [BEq β] [LawfulBEq β] (y : β) : ∀ L : List β, drin y L = true ↔ y ∈ L
  | [] => ⟨fun h => absurd h Bool.false_ne_true, fun h => absurd h List.not_mem_nil⟩
  | x :: L => by
    show ((y == x) || drin y L) = true ↔ _
    rw [Bool.or_eq_true, beq_iff_eq, drin_iff y L, List.mem_cons]

/-- Zwei unverträgliche Prädikate:  die Länge des Oder-Filters ist die Summe. -/
theorem filter_or_length {α : Type} (R : List α) (p q : α → Bool) (h : ∀ l ∈ R, ¬ (p l = true ∧ q l = true)) :
    (R.filter (fun l => p l || q l)).length = (R.filter p).length + (R.filter q).length := by
  induction R with
  | nil => rfl
  | cons a t ih =>
    have ih' := ih (fun l hl => h l (List.mem_cons_of_mem a hl))
    rw [List.filter_cons, List.filter_cons, List.filter_cons]
    cases hp : p a <;> cases hq : q a
    · rw [if_neg (by decide), if_neg (by decide), if_neg (by decide)]
      exact ih'
    · rw [if_pos (by decide), if_neg (by decide), if_pos (by decide), List.length_cons, List.length_cons, ih']
      omega
    · rw [if_pos (by decide), if_pos (by decide), if_neg (by decide), List.length_cons, List.length_cons, ih']
      omega
    · exact absurd ⟨hp, hq⟩ (h a List.mem_cons_self)

/-- **Die Zählbrücke:**  über einer duplikatfreien Liste `L` ist die Summe der Faserlängen die Länge des Filters „Bild in `L`". -/
theorem summe_fasern {α β : Type} [BEq β] [LawfulBEq β] (R : List α) (f : α → β) :
    ∀ L : List β, L.Nodup →
      (L.map (fun x => (R.filter (fun l => f l == x)).length)).sum = (R.filter (fun l => drin (f l) L)).length
  | [], _ => by
    show (0 : ℕ) = (R.filter (fun _ => false)).length
    rw [List.filter_false]
    rfl
  | x :: L, hL => by
    obtain ⟨hx, hL'⟩ := List.nodup_cons.mp hL
    rw [List.map_cons, List.sum_cons, summe_fasern R f L hL']
    show _ = (R.filter (fun l => (f l == x) || drin (f l) L)).length
    rw [filter_or_length R (fun l => f l == x) (fun l => drin (f l) L)]
    intro l _ hpq
    have hm := (drin_iff _ _).mp hpq.2
    rw [beq_iff_eq.mp hpq.1] at hm
    exact hx hm

/-- Jede Normalform liegt über der Teileliste ihrer Klassenzahl — allgemein. -/
theorem groessen_mem_teilListe {n : ℕ} {l : List ℕ} (hl : l ∈ rgsList n) :
    groessen l ∈ teilListe (klassenZahl l) n n := by
  obtain ⟨hlen, hrgs⟩ := mem_rgsList_frei.mp hl
  by_cases hnil : l = []
  · subst hnil
    have hn : n = 0 := hlen.symm
    subst hn
    show ([] : List ℕ) ∈ [[]]
    exact List.mem_cons_self
  · have hsum : (sortiert (zaehlen l)).sum = n := (sortiert_perm _).sum_eq.trans ((summe_zaehlen l).trans hlen)
    rw [groessen_eq hnil]
    apply mem_teilListe_of (klassenZahl l) (sortiert (zaehlen l)) n n
    · rw [← groessen_eq hnil]
      exact length_groessen l
    · exact hsum
    · exact fun x hx => zaehlen_pos hrgs hnil x ((sortiert_perm _).mem_iff.mp hx)
    · exact sortiert_pairwise _
    · exact fun x hx => Nat.le_trans (mem_le_sum _ x hx) (Nat.le_of_eq hsum)

/-- (W2) **Der Stirling-Schluss, SATZ:**  die Fasern über den Partitionen mit `k` Teilen summieren sich zur Trito-Zahl. -/
theorem stirling_schluss (n k : ℕ) :
    ((teilListe k n n).map (fun lam => (faser n lam).length)).sum = tritoZahl n k := by
  show ((teilListe k n n).map (fun lam => ((rgsList n).filter (fun l => groessen l == lam)).length)).sum = _
  rw [summe_fasern (rgsList n) groessen (teilListe k n n) (teilListe_nodup k n n)]
  unfold tritoZahl
  congr 1
  refine List.filter_congr (fun l hl => ?_)
  rw [Bool.eq_iff_iff, drin_iff, beq_iff_eq]
  constructor
  · intro h
    rw [← length_groessen]
    exact teilListe_laenge k n n _ h
  · intro h
    rw [← h]
    exact groessen_mem_teilListe hl

/-- (W2, mit EM1) **Die Fasern über den Partitionen mit `k` Teilen summieren sich zur Stirlingzahl zweiter Art.** -/
theorem stirling_schluss_stirling (n k : ℕ) :
    ((teilListe k n n).map (fun lam => (faser n lam).length)).sum = Nat.stirlingSecond n k :=
  (stirling_schluss n k).trans (trito_eq_stirling n k)

end Reformulation.Proemial.VergroeberungMassII

/-! ## Axiom-Wachen (gemessen, verbatim) -/

/-- info: 'Reformulation.Proemial.VergroeberungMassII.groesste_faser' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMassII.groesste_faser

/-- info: 'Reformulation.Proemial.VergroeberungMassII.groesste_ist_max' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMassII.groesste_ist_max

/-- info: 'Reformulation.Proemial.VergroeberungMassII.groesste_eindeutig' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMassII.groesste_eindeutig

/-- info: 'Reformulation.Proemial.VergroeberungMassII.length_groessen' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMassII.length_groessen

/-- info: 'Reformulation.Proemial.VergroeberungMassII.teilListe_laenge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMassII.teilListe_laenge

/-- info: 'Reformulation.Proemial.VergroeberungMassII.mem_le_sum' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMassII.mem_le_sum

/-- info: 'Reformulation.Proemial.VergroeberungMassII.mem_teilListe_of' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMassII.mem_teilListe_of

/-- info: 'Reformulation.Proemial.VergroeberungMassII.range_pairwise_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMassII.range_pairwise_lt

/-- info: 'Reformulation.Proemial.VergroeberungMassII.teilListe_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMassII.teilListe_nodup

/-- info: 'Reformulation.Proemial.VergroeberungMassII.drin_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMassII.drin_iff

/-- info: 'Reformulation.Proemial.VergroeberungMassII.filter_or_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMassII.filter_or_length

/-- info: 'Reformulation.Proemial.VergroeberungMassII.summe_fasern' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMassII.summe_fasern

/-- info: 'Reformulation.Proemial.VergroeberungMassII.groessen_mem_teilListe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMassII.groessen_mem_teilListe

/-- info: 'Reformulation.Proemial.VergroeberungMassII.stirling_schluss' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMassII.stirling_schluss

/-- info: 'Reformulation.Proemial.VergroeberungMassII.stirling_schluss_stirling' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VergroeberungMassII.stirling_schluss_stirling
