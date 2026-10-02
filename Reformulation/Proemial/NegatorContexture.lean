import Reformulation.Proemial.NegationCycleThreeCycle
import Reformulation.Proemial.ContextureOverlap

/-!
# Proemial.NegatorContexture — die Negatoren und ihre Elementarkontexturen

Gebaut auf Anordnung des Architekten vom 26. September 2026 nach
`KorpusRev2/Antwort_Verbund_und_Kreise_Mathematiker.md` (Fassung 2, als Spec; §2, §3, §6),
hervorgegangen aus `KorpusRev2/Verbund_und_Kreise_an_Mathematiker_Impl.md`. Das Modul verbindet
zwei Stränge, die einander nicht importierten: die Negatoren (`NegationCycle`,
`NegationCycleThreeCycle`) und die Elementarkontexturen (`ContextureOverlap`).

* **K1 — Umtauschbereich und Elementarkontextur.** Der Negator `N_{i+1}` (`sw i`) tauscht die
  Werte `i` und `i + 1`; sein Umtauschbereich ist das Wertpaar `{i, i + 1}` (`InE`, als Menge
  `E`), eine Elementarkontextur (`isElemContexture_E`). Zwei verschiedene Negatoren ergeben
  genau dann die Kreisrelation (einen Dreierzyklus), wenn ihre Paare sich **überlappen**
  (`overlap_iff_three`), und sie vertauschen genau dann, wenn die Paare **disjunkt** sind
  (`disjoint_iff_comm`); disjunkte Paare gibt es erst ab vier Werten
  (`CompoundContexture.disjoint_elem_contextures_iff`). Für jede Wertzahl.
* **K2 — der vermittelte Umtausch.** `N_{i+1} N_{i+2} N_{i+1}` tauscht `i` und `i + 2` und lässt
  alle anderen Werte, für jede Wertzahl (`mediated_swap`). Die nicht benachbarte Zweiermenge
  `{i, i + 2}` hat keinen eigenen Negator; ihr Umtausch geht über den gemeinsamen Wert
  `i + 1`. Bei drei Werten ist er Günthers Relationsart O des Katalogs (`mediated_swap_is_O`,
  IGN S. 26 f.; EICHUNG).
  - *Grund der Bauform — QUELLENFEST* (IGN S. 17 f., am Seitenbild, Hermeneutes U1): „…das
    zwischen P und N 2 ist durch die andern beiden vermittelt, weil wir P und N als
    richtungsorientierte Ordinalzahlen behandeln. P ist weder unmittelbarer Vorgänger noch
    unmittelbarer Nachfolger von N 2." Unmittelbar tauschen nur Nachbarn der Ordnung; dass
    `N_{i+1}` genau `i` und `i + 1` tauscht, ist Günthers Grund, nicht unsere Setzung. Die
    Stelle markiert er im dritten Kreis der Tafel VI mit drei Querstrichen (S. 18).
  - *„vermittelt" — QUELLENFEST für den Umtausch 1 ↔ 3 bei drei Werten* (IGN S. 17; S. 19:
    „eine erste Vorstellung der Vermittlung. Dass das Umtauschverhältnis zwischen P und N 2,
    also zwischen den Werten 1 und 3 kein unmittelbares, sondern ein vermitteltes ist…").
    Für jede Wertzahl ist es Günthers Gestalt, von uns verallgemeinert, nicht Günthers Satz
    über `m` Werte; die Stufe bleibt FOLGERUNG (dünn).
  - *Die zweite Negation — QUELLENFEST in IGN* (S. 19, Hermeneutes U2): „Es ist also zu der
    klassischen Logik erst ein neuer Wert (N 2) hinzugetreten. Immerhin liefert uns schon
    diese elementare Erweiterung eine erste Vorstellung der Vermittlung." Ohne Hegel. Im
    Bestand ist `N1·N2·N1` bei drei Werten der Rücklauf (`NegationCycleLength.genesen_kuerzeste`)
    und eines der vier Elemente von `NegationCycle.transklassisch3`.
  - *Dieselben drei Wertpaare in verschiedenen Rollen, nicht ein Gegenstand* (Hermeneutes,
    30.9.; Rev10-Register ZH6, ZB): `NegationCycle.track_mediates` trägt den **Vermittler**,
    den Wert, den die zwei unmittelbaren Paare teilen (die 2, der durchlaufen wird; HKN S. 25),
    `mediated_swap` das **Vermittelte**, das Paar {1, 3} (IGN S. 17–19); in BdM 1963 (Tafel VII)
    vermittelt ein **System**. *Nachgeführt am 2.10.2026, zweimal: zuerst (Ledger Rev. 32) aus
    „Ein Begriff von zwei Seiten (Hermeneutes U4)", dann (Ledger Rev. 33) aus „Dieselben Werte
    in verschiedenen Rollen".*
  - *Die Verbundkontextur* (Stand 27.9.): dasselbe Wort („Verbundkontextur bedeutet
    Vermittlung", HKN S. 25/26) und dieselbe Schwelle, das dreiwertige System als erster Fall.
    In IGN kommt „Verbundkontextur" nicht vor, und in IGN und HKN steht die Gleichsetzung
    nicht. **tml 1971 S. 11 setzt die zwei gleich:** „Zu den Umtauschverhältnissen von 1⟷2
    und 2⟷3 tritt jetzt noch ein ‚vermitteltes' Umtauschverhältnis der Werte 1⟷3. …
    dann besteht die einfachste Form einer Verbund-Kontextur also aus drei
    Elementarkontexturen." QUELLENFEST nach Hermeneutes (R2, 26.9.), an der Textschicht
    gelesen, nicht am Seitenbild; gebucht von Custos (C-2). Der Kopf gibt diese Buchung
    wieder und setzt nicht selbst gleich. *Bis 27.9. stand hier „ZUORDNUNG, NAHE" (U3) mit
    „nirgends gleich" — überholt durch R2.*
* **K3 — die Stufen, je Satz am Beweis bestimmt** (CLAUDE.md §4):
  - `overlap_iff` — FOLGERUNG (dünn) — die Arithmetik des Schnitts zweier Paare.
  - `overlap_iff_three` — ZUSAMMENSTELLUNG — `overlap_iff` und `three_iff_adj`.
  - `adj_not_comm` — FOLGERUNG (dünn) — Nachbarn vertauschen nicht, am Wert `i`.
  - `disjoint_iff_comm` — ZUSAMMENSTELLUNG — `overlap_iff`, `comm_far`, `adj_not_comm`.
  - `mediated_swap` — FOLGERUNG (dünn) — die Konjugation einer Transposition, für jedes `m`.
  - `mediated_swap_is_O` — EICHUNG — an Günthers Katalog.
  - `isElemContexture_E` — INSTANZIIERUNG — am Paar; seit 27.9. per `rfl` über die Liste.
  - `E_inter_nonempty_iff_three`, `E_inter_empty_iff_comm` — ZUSAMMENSTELLUNG — die Hauptsätze
    über `mem_E` in die `Finset`-Sprache übersetzt. `mem_E` ist der Hilfssatz dazu.
  Keine Entdeckung: der Wert der Sätze ist, dass sie die zwei Stränge verbinden.
* **K4 — das Profil, gemessen.** **Seit dem 27.9. trägt kein Satz des Moduls
  `Classical.choice`.** `E` und `Em` werden direkt aus der duplikatfreien Liste gebaut
  (`⟨↑[a, b], nodup⟩`, nicht über `toFinset`, Fallstrick 24); ihre Kardinalität ist dann
  definitional die Listenlänge, und `isElemContexture_E`, `isElemContexture_Em` gelten per
  `rfl`. *Geschichte, als Messung stehen gelassen (Fundort für CLAUDE.md, Fallstrick 10):*
  bis zum 27.9. war `E` das `Finset`-Literal `{i.castSucc, i.succ}`, und `isElemContexture_E`
  trug `Classical.choice`, aus `Finset.card_pair` (gemessen, Mathlib 83a5988); alle übrigen
  Sätze waren frei. Die erste Fassung des B3-Korollars über
  `Disjoint (E i) (E j)` trug es ebenfalls, aus `Finset.disjoint_left`; die Fassung mit
  `E i ∩ E j = ∅` (die Form von `CompoundContexture`, und CLAUDE.md §5 verbietet `Disjoint` auf
  Kontextur-Trägermengen) ist frei. Das Choice gehört also nicht der Sache, sondern einzelnen
  Mengensätzen der Sprache, in der die Kontextur-Seite gebaut ist.
* **K5 — nicht:** kein Verbund-Objekt (der Verbund wäre die Familie der Paare mit ihrem
  Überlappungsgraphen, eine Benennung); keine Aussage über Vollkreise als „Durchlauf des
  Verbunds"; Werte und Wertabbildungen, nicht Kenogramme (A20-1 unberührt). Eine eigene
  Ledger-Zeile hat das Modul nicht angelegt; seit Ledger Rev. 30 trägt `mediated_swap` L11-7.
* **K6 — die vermittelte Elementarkontextur (27.9.).** Gebaut auf Anordnung des Architekten
  vom 27. September 2026 nach `KorpusRev2/Spec_Ein_Zug_O3_E_Koepfe.md` (Mathematiker,
  Fassung 2), Teil 1 und 2.
  - *Die Quelle* (tml 1971, Hermeneutes H-2, am Seitenbild): „Tafel II stellt die
    Negationsstruktur dar, die dem einfachsten Fall einer Verbund-Kontextur zugrunde liegt."
    S. 11 im Wortlaut (Custos C-2): „Stipulieren wir jetzt, dass eine Elementarkontextur durch
    ein symmetrisches Umtauschverhältnis zweier beliebiger Werte konstituiert wird, dann
    besteht die einfachste Form einer Verbund-Kontextur also aus drei Elementarkontexturen."
    Zitiert, nicht gedeutet.
  - *Was die Sätze sagen:* das Wertpaar `{i, i + 2}` (`Em`), das keinen eigenen Negator hat,
    ist eine Elementarkontextur im Sinn des Bestands (`isElemContexture_Em`, INSTANZIIERUNG;
    `mem_Em` ist der Hilfssatz), und der vermittelte Umtausch `mediated_swap` tauscht genau
    seine zwei Werte und hält alle anderen fest (`mediated_elem`, ZUSAMMENSTELLUNG aus
    `mediated_swap` und `mem_Em`).
  - *Der Nächste in der Sache, nicht verbraucht:* `ElementaryCycle.isElemContexture_orb_iff`
    — `{i, i + 2}` ist die Zweierbahn von `i` unter der Involution `mediated_swap`.
  - *Nicht:* „Elementarkontextur" ohne Umfang. Im Bestand ist es der Zweierzyklus
    (`card = 2`); der Selbstzyklus der Definitionen (§2) ist hier nicht gemeint. Der Kopf
    setzt die zwei Vermittlungen nicht selbst gleich (K2).
-/

namespace Reformulation.Proemial.NegatorContexture

open Reformulation.Proemial.NegationCycle Reformulation.Proemial.NegationCycleThreeCycle
  Reformulation.Proemial.NegationCycleCatalog Reformulation.Proemial.ContextureOverlap

variable {m : ℕ}

-- ============================================================
-- Teil 1 — die Hauptsätze, über das Prädikat (choice-frei)
-- ============================================================

/-- Der Wert `v` liegt im Umtauschbereich des Negators `N_{i+1}`: er ist `i` oder `i + 1`. -/
def InE (i : Fin m) (v : Fin (m + 1)) : Prop := v.val = i.val ∨ v.val = i.val + 1

/-- **Die Arithmetik des Schnitts:** zwei verschiedene Umtauschbereiche haben genau dann einen
gemeinsamen Wert, wenn ihre Negatoren Nachbarn sind. -/
theorem overlap_iff (i j : Fin m) (hij : i ≠ j) :
    (∃ v, InE i v ∧ InE j v) ↔ (j.val = i.val + 1 ∨ i.val = j.val + 1) := by
  constructor
  · rintro ⟨x, h1 | h1, h2 | h2⟩
    · exact absurd (Fin.ext (h1.symm.trans h2)) hij
    · right; omega
    · left; omega
    · have : i.val = j.val := by omega
      exact absurd (Fin.ext this) hij
  · rintro (h | h)
    · exact ⟨j.castSucc, Or.inr (by simp only [Fin.val_castSucc]; omega),
        Or.inl (by simp only [Fin.val_castSucc])⟩
    · exact ⟨i.castSucc, Or.inl (by simp only [Fin.val_castSucc]),
        Or.inr (by simp only [Fin.val_castSucc]; omega)⟩

/-- **B2 — Überlappung ist Kreisrelation:** zwei verschiedene Negatoren ergeben genau dann einen
Dreierzyklus, wenn ihre Umtauschbereiche einen Wert teilen. -/
theorem overlap_iff_three (i j : Fin m) (hij : i ≠ j) :
    (∃ v, InE i v ∧ InE j v) ↔ IsThree (fun v => sw j (sw i v)) := by
  rw [overlap_iff i j hij, three_iff_adj i j hij]

/-- **Nachbarn vertauschen nicht:** am Wert `i` unterscheiden sich `N_{i+1} N_{i+2}` und
`N_{i+2} N_{i+1}`. -/
theorem adj_not_comm (i j : Fin m) (h : j.val = i.val + 1) :
    sw i (sw j i.castSucc) ≠ sw j (sw i i.castSucc) := by
  intro heq
  have := congrArg Fin.val heq
  rw [sw_val, sw_val, sw_val, sw_val] at this
  simp only [Fin.val_castSucc] at this
  split_ifs at this <;> omega

/-- **B3 — Disjunktheit ist Vertauschung:** zwei verschiedene Negatoren vertauschen genau dann,
wenn ihre Umtauschbereiche keinen Wert teilen. -/
theorem disjoint_iff_comm (i j : Fin m) (hij : i ≠ j) :
    (¬ ∃ v, InE i v ∧ InE j v) ↔ ∀ v, sw i (sw j v) = sw j (sw i v) := by
  rw [overlap_iff i j hij]
  constructor
  · intro hn v
    have hv : i.val ≠ j.val := fun e => hij (Fin.ext e)
    rcases Nat.lt_or_gt_of_ne hv with hl | hl
    · exact comm_far i j (by omega) v
    · exact (comm_far j i (by omega) v).symm
  · rintro hc (h | h)
    · exact adj_not_comm i j h (hc _)
    · exact adj_not_comm j i h (hc _).symm

/-- **B4 — der vermittelte Umtausch:** `N_{i+1} N_{i+2} N_{i+1}` tauscht die Werte `i` und
`i + 2` und lässt alle anderen, für jede Wertzahl. Die nicht benachbarte Zweiermenge
`{i, i + 2}` hat keinen eigenen Negator; ihr Umtausch geht über den gemeinsamen Wert `i + 1`.
Günthers Grund dafür, dass nur Nachbarn unmittelbar tauschen, steht IGN S. 17 f. (QUELLENFEST,
siehe K2); „vermittelt" für 1 ↔ 3 bei drei Werten ebenda und S. 19. -/
theorem mediated_swap (i j : Fin m) (hj : j.val = i.val + 1) (v : Fin (m + 1)) :
    (sw i (sw j (sw i v))).val =
      if v.val = i.val then i.val + 2 else if v.val = i.val + 2 then i.val else v.val := by
  simp only [sw_val]
  split_ifs <;> omega

/-- **Eichung an Günthers O:** bei drei Werten ist der vermittelte Umtausch `N1·2·1` genau die
Relationsart O des Katalogs (IGN S. 26 f.; `NegationCycleCatalog.kat`). -/
theorem mediated_swap_is_O :
    kat (fun v => sw (0 : Fin 2) (sw 1 (sw 0 v))) = some .O := by
  decide

-- ============================================================
-- Teil 2 — die Korollare, in der Sprache der Kontextur-Seite (Finset)
-- ============================================================

/-- Der Umtauschbereich des Negators `N_{i+1}` als Wertmenge — direkt aus der duplikatfreien
Liste gebaut, nicht über `toFinset` (Fallstrick 24; K4). -/
def E (i : Fin m) : Finset (Fin (m + 1)) :=
  ⟨([i.castSucc, i.succ] : Multiset (Fin (m + 1))),
    List.nodup_cons.mpr ⟨fun h => Fin.ne_of_lt Fin.castSucc_lt_succ (List.mem_singleton.mp h),
      List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩⟩⟩

theorem mem_E (i : Fin m) (v : Fin (m + 1)) : v ∈ E i ↔ InE i v := by
  show v ∈ ([i.castSucc, i.succ] : Multiset (Fin (m + 1))) ↔ _
  rw [Multiset.mem_coe, List.mem_cons, List.mem_singleton]
  unfold InE
  constructor
  · rintro (h | h)
    · exact Or.inl (by rw [h, Fin.val_castSucc])
    · exact Or.inr (by rw [h, Fin.val_succ])
  · rintro (h | h)
    · exact Or.inl (Fin.ext (by rw [Fin.val_castSucc]; exact h))
    · exact Or.inr (Fin.ext (by rw [Fin.val_succ]; exact h))

/-- **B1:** der Umtauschbereich eines Negators ist eine Elementarkontextur — die Kardinalität
ist definitional die Listenlänge. -/
theorem isElemContexture_E (i : Fin m) : IsElemContexture (E i) := rfl

/-- B2 in der Sprache der Kontextur-Seite. -/
theorem E_inter_nonempty_iff_three (i j : Fin m) (hij : i ≠ j) :
    (E i ∩ E j).Nonempty ↔ IsThree (fun v => sw j (sw i v)) := by
  rw [← overlap_iff_three i j hij]
  constructor
  · rintro ⟨v, hv⟩
    rw [Finset.mem_inter, mem_E, mem_E] at hv
    exact ⟨v, hv⟩
  · rintro ⟨v, hv⟩
    exact ⟨v, by rw [Finset.mem_inter, mem_E, mem_E]; exact hv⟩

/-- B3 in der Sprache der Kontextur-Seite, in der Form von
`CompoundContexture.disjoint_elem_contextures_iff` (`A ∩ B = ∅`, nicht `Disjoint`; CLAUDE.md §5). -/
theorem E_inter_empty_iff_comm (i j : Fin m) (hij : i ≠ j) :
    E i ∩ E j = ∅ ↔ ∀ v, sw i (sw j v) = sw j (sw i v) := by
  rw [← disjoint_iff_comm i j hij]
  constructor
  · rintro h ⟨v, hi, hj⟩
    have hv : v ∈ E i ∩ E j := by
      rw [Finset.mem_inter, mem_E, mem_E]; exact ⟨hi, hj⟩
    rw [h] at hv
    exact Finset.notMem_empty v hv
  · intro h
    ext v
    rw [Finset.mem_inter, mem_E, mem_E]
    exact ⟨fun hv => absurd ⟨v, hv⟩ h, fun hv => absurd hv (Finset.notMem_empty v)⟩

-- ============================================================
-- Teil 3 — die vermittelte Elementarkontextur (K6)
-- ============================================================

/-- Das nicht benachbarte Wertpaar `{i, i + 2}` (für `j = i + 1`), direkt aus der
duplikatfreien Liste gebaut. -/
def Em (i j : Fin m) (hj : j.val = i.val + 1) : Finset (Fin (m + 1)) :=
  ⟨([i.castSucc, j.succ] : Multiset (Fin (m + 1))),
    List.nodup_cons.mpr ⟨fun h => by
        have := congrArg Fin.val (List.mem_singleton.mp h)
        rw [Fin.val_castSucc, Fin.val_succ] at this
        omega,
      List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩⟩⟩

/-- **Die vermittelte Elementarkontextur:** `{i, i + 2}` ist eine Elementarkontextur im Sinn
des Bestands (`card = 2`), obwohl kein Negator dieses Paar tauscht. -/
theorem isElemContexture_Em (i j : Fin m) (hj : j.val = i.val + 1) :
    IsElemContexture (Em i j hj) := rfl

/-- Mitgliedschaft in `Em`, ohne offenes `simp`. -/
theorem mem_Em (i j : Fin m) (hj : j.val = i.val + 1) (v : Fin (m + 1)) :
    v ∈ Em i j hj ↔ v = i.castSucc ∨ v = j.succ := by
  show v ∈ ([i.castSucc, j.succ] : Multiset (Fin (m + 1))) ↔ _
  rw [Multiset.mem_coe, List.mem_cons, List.mem_singleton]

/-- **Der vermittelte Umtausch tauscht genau dieses Paar:** auf `Em` bildet `mediated_swap`
jeden Wert auf den anderen des Paares ab, ausserhalb hält er jeden Wert fest. -/
theorem mediated_elem (i j : Fin m) (hj : j.val = i.val + 1) (v : Fin (m + 1)) :
    (v ∈ Em i j hj → sw i (sw j (sw i v)) ∈ Em i j hj ∧ sw i (sw j (sw i v)) ≠ v) ∧
    (v ∉ Em i j hj → sw i (sw j (sw i v)) = v) := by
  have hs := mediated_swap i j hj v
  have hv1 : v = i.castSucc ↔ v.val = i.val := ⟨fun h => by rw [h, Fin.val_castSucc],
    fun h => Fin.ext (by rw [Fin.val_castSucc]; exact h)⟩
  have hv2 : ∀ w : Fin (m + 1), w = j.succ ↔ w.val = i.val + 2 := fun w =>
    ⟨fun h => by rw [h, Fin.val_succ, hj], fun h => Fin.ext (by rw [Fin.val_succ]; omega)⟩
  rw [mem_Em, mem_Em, hv1, hv2, hv2]
  have hw1 : sw i (sw j (sw i v)) = i.castSucc ↔ (sw i (sw j (sw i v))).val = i.val :=
    ⟨fun h => by rw [h, Fin.val_castSucc], fun h => Fin.ext (by rw [Fin.val_castSucc]; exact h)⟩
  rw [hw1]
  refine ⟨fun hv => ⟨?_, ?_⟩, fun hv => Fin.ext ?_⟩
  · rcases hv with h | h
    · rw [if_pos h] at hs; exact Or.inr hs
    · rw [if_neg (by omega), if_pos h] at hs; exact Or.inl hs
  · intro he; rw [he] at hs
    rcases hv with h | h
    · rw [if_pos h] at hs; omega
    · rw [if_neg (by omega), if_pos h] at hs; omega
  · rw [if_neg (fun h => hv (Or.inl h)), if_neg (fun h => hv (Or.inr h))] at hs; exact hs

-- ============================================================
-- Wachen
-- ============================================================

/-- info: 'Reformulation.Proemial.NegatorContexture.overlap_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms overlap_iff

/-- info: 'Reformulation.Proemial.NegatorContexture.overlap_iff_three' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms overlap_iff_three

/-- info: 'Reformulation.Proemial.NegatorContexture.adj_not_comm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms adj_not_comm

/-- info: 'Reformulation.Proemial.NegatorContexture.disjoint_iff_comm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms disjoint_iff_comm

/-- info: 'Reformulation.Proemial.NegatorContexture.mediated_swap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms mediated_swap

/-- info: 'Reformulation.Proemial.NegatorContexture.mediated_swap_is_O' depends on axioms: [propext] -/
#guard_msgs in #print axioms mediated_swap_is_O

/-- info: 'Reformulation.Proemial.NegatorContexture.mem_E' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms mem_E

/-- info: 'Reformulation.Proemial.NegatorContexture.isElemContexture_E' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms isElemContexture_E

/-- info: 'Reformulation.Proemial.NegatorContexture.E_inter_nonempty_iff_three' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms E_inter_nonempty_iff_three

/-- info: 'Reformulation.Proemial.NegatorContexture.E_inter_empty_iff_comm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms E_inter_empty_iff_comm

/-- info: 'Reformulation.Proemial.NegatorContexture.isElemContexture_Em' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms isElemContexture_Em

/-- info: 'Reformulation.Proemial.NegatorContexture.mem_Em' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms mem_Em

/-- info: 'Reformulation.Proemial.NegatorContexture.mediated_elem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms mediated_elem

end Reformulation.Proemial.NegatorContexture
