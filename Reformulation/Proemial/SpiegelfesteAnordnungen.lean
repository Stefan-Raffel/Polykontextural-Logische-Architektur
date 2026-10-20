import Reformulation.Proemial.GegenidentitaetProbe   -- umkehr, dreh, stationUmkehr, stations_umkehr
import Reformulation.Proemial.NegationCycleSJT       -- origin_nodup, sjt, sjt_full

/-!
# Proemial.SpiegelfesteAnordnungen — Umkehr und Drehsinn für jede Wertzahl

*Name:* spiegelfest = umkehrfest; der Modulname ist älter als die Umbenennung `spiegel` →
`umkehr` (20. Oktober 2026; Grund im Kopf von `GegenidentitaetProbe`, Abschnitt „Der Name").

STANDALONE, NICHT im Aggregat; Target `Probes`. AxiomGate unberührt. Sonde nach
`KorpusRev2/Sondierung_Spiegelfeste_Anordnungen_Prompt.md` (Mathematiker, 20. Oktober 2026).
Konsumiert `GegenidentitaetProbe` (`umkehr`, `dreh`, `stationUmkehr`, `stations_umkehr`) und
den `NegationCycle`-Strang; ändert nichts davon. Quellen und Zuordnungen (Umkehr =
Gegenidentität, Drehsinn S. 19 f., Bahn und IuG S. 51) stehen im Kopf von `GegenidentitaetProbe`;
hier wird nicht neu gelesen.

**Der Ertrag in einem Satz.** Ab vier Werten fällt die Umkehr eines Vollkreises nie mit seinem
Drehsinn zusammen, und keiner von beiden ist je der Kreis selbst; bei drei Werten fallen Umkehr
und Drehsinn zusammen — darum braucht Tafel VI nur die Umkehr. Was `GegenidentitaetProbe` für
vier Werte über die Tafel der 88 zeigte, gilt jetzt für jede Wertzahl, ohne Tafel.

## Der Beweisweg

Für einen Vollkreis `w` sind die Stationen `origin :: T` und die seines Drehsinns
`origin :: T.reverse` (`stations_gestalt`, die Rechnung aus `reverse_full`); die der Umkehr
sind `origin :: T.map φ` mit `φ = stationUmkehr` (`stations_umkehr`). Daraus:

* (S3) `umkehr w = dreh w` ⇒ `T.map φ = T.reverse`. In einer duplikatfreien Liste mit dieser
  Eigenschaft gibt es höchstens ein `φ`-festes Element, nämlich in der Mitte (`fest_eindeutig`).
  Ab vier Werten liegen aber zwei verschiedene `φ`-feste Anordnungen in `T`: der Rücklauf und
  `drittes` = `[1, 0, 2, …, n−3, n−1, n−2]` (`N1` und `N_m` auf dem Ausgang, zwei disjunkte
  Nachbartausche). Widerspruch: `umkehr_ne_dreh_all`.
* (S4) `dreh w = w` ⇒ `T = T.reverse`, dasselbe Lemma mit `φ = id`: höchstens ein Element in `T`.
  Ab drei Werten liegen `N1 p` und `N2 p` darin. `dreh_ne_self_all`.
* (S5) `umkehr w = w` ⇒ jede Station ist `φ`-fest, also jede Anordnung; aber
  `φ (N1 p) = N_m p ≠ N1 p` ab drei Werten. `umkehr_ne_self_all`.

Bei zwei Werten (`m = 1`) gelten S4 und S5 nicht: `[0, 0]` ist ein drehfester Vollkreis, und
`Fin.rev` ist auf `Fin 1` die Identität. Bei drei Werten gibt es genau zwei umkehrfeste
Anordnungen (`umkehrfest_drei`), zu wenig für S3 — das ist `umkehr_eq_dreh_three` von der
anderen Seite.

## Stufen (CLAUDE.md §4)

| Satz | Stufe |
|---|---|
| `umkehr_ne_dreh_all`, `dreh_ne_self_all`, `umkehr_ne_self_all` | FOLGERUNG |
| `fest_eindeutig` | FOLGERUNG (allgemein, über jedem Typ) |
| `stations_gestalt` | HEBUNG (die Rechnung im Beweis von `reverse_full` als Satz) |
| `bahn_all` | ZUSAMMENSTELLUNG (S3–S5, `reverse_full`) |
| `umkehr_ne_dreh_four_aus_all`, `bahn_vier_aus_all`, `sjt_umkehr_ne_dreh` | INSTANZIIERUNG (m = 3 bzw. `sjt_full`) |
| `sjt_*_werte`, `umkehrfest_*` | EICHUNG |

Hilfssätze, gewacht wie alle Deklarationen: `fest_of_map_eq`, `stationUmkehr_map`,
`stationUmkehr_origin`, `stationUmkehr_reverse`, `mem_T`, `drittes` (def), `drittes_eq`,
`drittes_perm`, `drittes_fest`, `drittes_ne`, `reverse_ne_origin`, `negate_zero_val`,
`negate_ne_origin`.

**Kein `full_length`.** Der Weg des Prompts für S4 und S5 lief über die Länge `(m+1)!`;
`NegationCycle.full_length` trägt `Classical.choice` (gewacht). Die Beweise hier brauchen keine
Länge, nur Zeugen in `T`.

**Offen, nicht angefangen:** die Akkretivitäts-Brücke (IGN S. 9), ob die SJT-Rekursion
`n → n + 1` mit Umkehr und Drehsinn verträglich ist.

Kein `sorry`, kein `native_decide`, kein `: True`-Feld, kein `axiom`.
-/

namespace Reformulation.Proemial.SpiegelfesteAnordnungen

open Reformulation.Proemial.NegationCycle
open Reformulation.Proemial.GegenidentitaetProbe
open Reformulation.Proemial.NegationCycleCatalog (map_eq_iff origin_perm mem_of_perm)
open Reformulation.Proemial.NegationCycleThreeCycle (negate_mem_perm)
open Reformulation.Proemial.NegationCycleLength (negate_nodup)
open Reformulation.Proemial.NegationCycleSJT (origin_nodup sjt sjt_full)

-- ============================================================
-- §I — Höchstens ein festes Element (allgemein)
-- ============================================================

/-- **In einer duplikatfreien Liste `T` mit `T.map φ = T.reverse` gibt es höchstens ein
`φ`-festes Element:** ein festes Element an der Stelle `k` steht nach der Gleichung auch an der
Stelle `|T| − 1 − k`, also ist `k` die Mitte. -/
theorem fest_eindeutig {α : Type*} (φ : α → α) (T : List α) (hnd : T.Nodup)
    (hT : T.map φ = T.reverse) {a b : α} (ha : a ∈ T) (hb : b ∈ T)
    (hfa : φ a = a) (hfb : φ b = b) : a = b := by
  have mitte : ∀ k (hk : k < T.length), φ T[k] = T[k] → T.length - 1 - k = k := by
    intro k hk hf
    have hk1 : k < (T.map φ).length := by rw [List.length_map]; exact hk
    have h1 := List.getElem_of_eq hT hk1
    rw [List.getElem_map, List.getElem_reverse, hf] at h1
    exact ((hnd.getElem_inj_iff).mp h1.symm)
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hb
  have e1 := mitte i hi hfa
  have e2 := mitte j hj hfb
  have hij : i = j := by omega
  subst hij
  rfl

/-- Eine Liste, die eine Abbildung festlässt, besteht aus Fixpunkten. -/
theorem fest_of_map_eq {α : Type*} (f : α → α) :
    ∀ (l : List α), l.map f = l → ∀ x ∈ l, f x = x
  | [], _, x, hx => absurd hx List.not_mem_nil
  | a :: l, h, x, hx => by
    rw [List.map_cons] at h
    have h' := List.cons.inj h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h'.1
    · exact fest_of_map_eq f l h'.2 x hx

-- ============================================================
-- §II — Die Gestalt der Stationen unter Drehsinn und Umkehr
-- ============================================================

/-- **Stationen eines Vollkreises und seines Drehsinns:** `origin :: T` und `origin :: T.reverse`
(die Rechnung aus dem Beweis von `reverse_full`, als eigener Satz). -/
theorem stations_gestalt {m : ℕ} {w : List (Fin m)} (h : IsFullCycle w) :
    ∃ T, stations w (origin m) = origin m :: T ∧
      stations (dreh w) (origin m) = origin m :: T.reverse := by
  cases w with
  | nil => exact absurd (h.all_arrangements _ origin_perm) List.not_mem_nil
  | cons j js =>
    refine ⟨stations js (negate j (origin m)), rfl, ?_⟩
    have hc : endpoint (j :: js) (origin m) = origin m := h.closes
    have hcl : endpoint (j :: js).reverse (origin m) = origin m := by
      have := endpoint_reverse (j :: js) (origin m); rwa [hc] at this
    have hfs := fullStations_reverse (j :: js) (origin m)
    rw [hc] at hfs
    have e1 : fullStations (j :: js).reverse (origin m)
        = stations (j :: js).reverse (origin m) ++ [origin m] := by rw [fullStations, hcl]
    have e2 : (fullStations (j :: js) (origin m)).reverse
        = (origin m :: (stations js (negate j (origin m))).reverse) ++ [origin m] := by
      rw [fullStations, hc]
      show (origin m :: stations js (negate j (origin m)) ++ [origin m]).reverse = _
      rw [List.reverse_append, List.reverse_singleton, List.reverse_cons]
      rfl
    rw [e1, e2] at hfs
    exact List.append_cancel_right hfs

/-- Die Umkehr auf den Stationen, an einer Anordnung `origin.map g`: die Wertabbildung wird mit
der Umkehr der Werte konjugiert. -/
theorem stationUmkehr_map {m : ℕ} (g : Fin (m + 1) → Fin (m + 1)) :
    stationUmkehr ((origin m).map g) = (origin m).map (fun v => Fin.rev (g (Fin.rev v))) := by
  unfold stationUmkehr
  rw [← List.map_reverse, ← origin_map_rev, List.map_map, List.map_map]
  rfl

/-- Der Ausgang ist umkehrfest. -/
theorem stationUmkehr_origin {m : ℕ} : stationUmkehr (origin m) = origin m := by
  unfold stationUmkehr
  rw [← origin_map_rev, map_rev_map_rev]

/-- Der Rücklauf ist umkehrfest. -/
theorem stationUmkehr_reverse {m : ℕ} : stationUmkehr (origin m).reverse = (origin m).reverse := by
  unfold stationUmkehr
  rw [List.reverse_reverse, origin_map_rev]

/-- Eine Anordnung, die nicht der Ausgang ist, steht in `T`. -/
theorem mem_T {m : ℕ} {w : List (Fin m)} (h : IsFullCycle w) {T : List (List (Fin (m + 1)))}
    (hS : stations w (origin m) = origin m :: T) {x : List (Fin (m + 1))}
    (hx : x ∈ (origin m).permutations') (hne : x ≠ origin m) : x ∈ T := by
  have hm := h.all_arrangements x hx
  rw [hS] at hm
  rcases List.mem_cons.mp hm with he | hT
  · exact absurd he hne
  · exact hT

-- ============================================================
-- §III — Drei umkehrfeste Anordnungen ab vier Werten
-- ============================================================

/-- Die dritte umkehrfeste Anordnung: `N1` und `N_{m}` auf dem Ausgang, die zwei äußeren
Nachbarpaare vertauscht — `[1, 0, 2, …, n−3, n−1, n−2]`. -/
def drittes (k : ℕ) : List (Fin (k + 4)) :=
  negate (0 : Fin (k + 3)) (negate (Fin.rev (0 : Fin (k + 3))) (origin (k + 3)))

theorem drittes_eq (k : ℕ) : drittes k =
    (origin (k + 3)).map (fun v => sw (0 : Fin (k + 3)) (sw (Fin.rev (0 : Fin (k + 3))) v)) := by
  unfold drittes negate
  rw [List.map_map]
  rfl

theorem drittes_perm (k : ℕ) : drittes k ∈ (origin (k + 3)).permutations' := by
  have h1 := negate_mem_perm (Fin.rev (0 : Fin (k + 3)))
  have h2 := negate_perm (0 : Fin (k + 3)) _ (negate_nodup _ (origin_nodup (k + 3)))
    (fun v => mem_of_perm h1 v)
  exact List.mem_permutations'.mpr (h2.trans (List.mem_permutations'.mp h1))

theorem drittes_fest (k : ℕ) : stationUmkehr (drittes k) = drittes k := by
  rw [drittes_eq, stationUmkehr_map]
  apply (map_eq_iff origin_perm _ _).mpr
  intro v
  apply Fin.ext
  have hv := v.isLt
  simp only [Fin.val_rev, sw_val, Fin.val_zero]
  repeat' split_ifs at *
  all_goals omega

/-- Wert am Ausgang 0: das dritte setzt dort `1`, der Ausgang `0`, der Rücklauf `n − 1`. -/
theorem drittes_ne (k : ℕ) : drittes k ≠ origin (k + 3) ∧ drittes k ≠ (origin (k + 3)).reverse := by
  have h0 : (sw (0 : Fin (k + 3)) (sw (Fin.rev (0 : Fin (k + 3))) 0)).val = 1 := by
    simp only [Fin.val_rev, sw_val, Fin.val_zero]
    repeat' split_ifs at *
    all_goals omega
  refine ⟨fun e => ?_, fun e => ?_⟩
  · rw [drittes_eq] at e
    have e' : (origin (k + 3)).map (fun v => sw (0 : Fin (k + 3)) (sw (Fin.rev (0 : Fin (k + 3))) v))
        = (origin (k + 3)).map id := by rw [List.map_id]; exact e
    have := congrArg Fin.val ((map_eq_iff origin_perm _ _).mp e' 0)
    rw [h0] at this
    exact absurd this (by show (1 : ℕ) ≠ 0; decide)
  · rw [drittes_eq, ← origin_map_rev] at e
    have := congrArg Fin.val ((map_eq_iff origin_perm _ _).mp e 0)
    rw [h0, Fin.val_rev, Fin.val_zero] at this
    exact absurd this (by omega)

theorem reverse_ne_origin (k : ℕ) : (origin (k + 1)).reverse ≠ origin (k + 1) := by
  intro e
  rw [← origin_map_rev] at e
  have e' : (origin (k + 1)).map Fin.rev = (origin (k + 1)).map id := by rw [List.map_id]; exact e
  have := congrArg Fin.val ((map_eq_iff origin_perm _ _).mp e' 0)
  rw [Fin.val_rev, Fin.val_zero] at this
  exact absurd this (by show k + 1 + 1 - (0 + 1) ≠ 0; omega)

/-- (S3) **Ab vier Werten ist für keinen Vollkreis die Umkehr der Drehsinn.** -/
theorem umkehr_ne_dreh_all {m : ℕ} (hm : 3 ≤ m) (w : List (Fin m)) (h : IsFullCycle w) :
    umkehr w ≠ dreh w := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
  intro e
  obtain ⟨T, hS, hD⟩ := stations_gestalt h
  have hT : T.map stationUmkehr = T.reverse := by
    have h1 := stations_umkehr w
    rw [e, hD, hS, List.map_cons, stationUmkehr_origin] at h1
    exact (List.cons.inj h1).2.symm
  have hnd : T.Nodup := by
    have := h.nodup
    rw [hS] at this
    exact (List.nodup_cons.mp this).2
  have hd := drittes_ne k
  have h3 := mem_T h hS (drittes_perm k) hd.1
  have hr := mem_T h hS (List.mem_permutations'.mpr (List.reverse_perm _)) (reverse_ne_origin (k + 2))
  exact hd.2 (fest_eindeutig stationUmkehr T hnd hT h3 hr (drittes_fest k) stationUmkehr_reverse)

-- ============================================================
-- §IV — Drehsinn und Umkehr sind nie die Identität (ab drei Werten)
-- ============================================================

theorem negate_zero_val (k : ℕ) : (sw (0 : Fin (k + 2)) 0).val = 1 := by
  simp only [sw_val, Fin.val_zero]
  repeat' split_ifs at *
  all_goals omega

theorem negate_ne_origin (k : ℕ) : negate (0 : Fin (k + 2)) (origin (k + 2)) ≠ origin (k + 2) := by
  intro e
  unfold negate at e
  have e' : (origin (k + 2)).map (sw 0) = (origin (k + 2)).map id := by rw [List.map_id]; exact e
  have := congrArg Fin.val ((map_eq_iff origin_perm _ _).mp e' 0)
  rw [negate_zero_val] at this
  exact absurd this (by show (1 : ℕ) ≠ 0; decide)

/-- (S4) **Ab drei Werten ist kein Vollkreis drehfest.** -/
theorem dreh_ne_self_all {m : ℕ} (hm : 2 ≤ m) (w : List (Fin m)) (h : IsFullCycle w) :
    dreh w ≠ w := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  intro e
  obtain ⟨T, hS, hD⟩ := stations_gestalt h
  have hT : T.map id = T.reverse := by
    rw [e, hS] at hD
    rw [List.map_id]
    exact (List.cons.inj hD).2
  have hnd : T.Nodup := by
    have := h.nodup
    rw [hS] at this
    exact (List.nodup_cons.mp this).2
  have ha := mem_T h hS (negate_mem_perm (0 : Fin (k + 2))) (negate_ne_origin k)
  have hb := mem_T h hS (negate_mem_perm (1 : Fin (k + 2))) (by
    intro e1
    unfold negate at e1
    have e1' : (origin (k + 2)).map (sw 1) = (origin (k + 2)).map id := by rw [List.map_id]; exact e1
    have := congrArg Fin.val ((map_eq_iff origin_perm _ _).mp e1' 1)
    simp only [sw_val, Fin.val_one, id] at this
    repeat' split_ifs at *
    all_goals omega)
  have hab := fest_eindeutig id T hnd hT ha hb rfl rfl
  unfold negate at hab
  have := congrArg Fin.val ((map_eq_iff origin_perm _ _).mp hab 0)
  simp only [sw_val, Fin.val_zero, Fin.val_one] at this
  repeat' split_ifs at *

/-- (S5) **Ab drei Werten ist kein Vollkreis umkehrfest.** Ein umkehrfestes Wort hätte nur
umkehrfeste Stationen; `N1` auf dem Ausgang ist es nicht. -/
theorem umkehr_ne_self_all {m : ℕ} (hm : 2 ≤ m) (w : List (Fin m)) (h : IsFullCycle w) :
    umkehr w ≠ w := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  intro e
  have hs := stations_umkehr w
  rw [e] at hs
  have hx := h.all_arrangements _ (negate_mem_perm (0 : Fin (k + 2)))
  have hf := fest_of_map_eq stationUmkehr _ hs.symm _ hx
  unfold negate at hf
  rw [stationUmkehr_map] at hf
  have := congrArg Fin.val ((map_eq_iff origin_perm _ _).mp hf 0)
  simp only [Fin.val_rev, sw_val, Fin.val_zero] at this
  repeat' split_ifs at *
  all_goals omega

-- ============================================================
-- §V — Die Bahn und die Instanzen
-- ============================================================

/-- **Ab vier Werten hat jeder Vollkreis drei verschiedene Partner** — für jede Wertzahl. -/
theorem bahn_all {m : ℕ} (hm : 3 ≤ m) (w : List (Fin m)) (h : IsFullCycle w) :
    [w, umkehr w, dreh w, umkehr (dreh w)].Nodup := by
  have hm2 : 2 ≤ m := by omega
  have e1 : w ≠ umkehr w := (umkehr_ne_self_all hm2 w h).symm
  have e2 : w ≠ dreh w := (dreh_ne_self_all hm2 w h).symm
  have e3 : w ≠ umkehr (dreh w) := fun e =>
    umkehr_ne_dreh_all hm w h ((congrArg umkehr e).trans (umkehr_umkehr _))
  have e4 : umkehr w ≠ dreh w := umkehr_ne_dreh_all hm w h
  have e5 : umkehr w ≠ umkehr (dreh w) := fun e =>
    dreh_ne_self_all hm2 w h (by rw [← umkehr_umkehr (dreh w), ← e, umkehr_umkehr])
  have e6 : dreh w ≠ umkehr (dreh w) :=
    (umkehr_ne_self_all hm2 (dreh w) (reverse_full h)).symm
  refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_,
    List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩⟩⟩⟩
  · intro hm'
    rcases List.mem_cons.mp hm' with hm' | hm'
    · exact e1 hm'
    rcases List.mem_cons.mp hm' with hm' | hm'
    · exact e2 hm'
    exact e3 (List.mem_singleton.mp hm')
  · intro hm'
    rcases List.mem_cons.mp hm' with hm' | hm'
    · exact e4 hm'
    exact e5 (List.mem_singleton.mp hm')
  · intro hm'
    exact e6 (List.mem_singleton.mp hm')

/-- `GegenidentitaetProbe.umkehr_ne_dreh_four` als Instanz des allgemeinen Satzes. -/
theorem umkehr_ne_dreh_four_aus_all (w : List (Fin 3)) (h : IsFullCycle w) :
    umkehr w ≠ dreh w :=
  umkehr_ne_dreh_all (le_refl 3) w h

/-- `GegenidentitaetProbe.bahn_vier` als Instanz des allgemeinen Satzes. -/
theorem bahn_vier_aus_all (w : List (Fin 3)) (h : IsFullCycle w) :
    [w, umkehr w, dreh w, umkehr (dreh w)].Nodup :=
  bahn_all (le_refl 3) w h

/-- Zeugen außerhalb der Tafel: die SJT-Kreise ab vier Werten. -/
theorem sjt_umkehr_ne_dreh (k : ℕ) : umkehr (sjt (k + 3)) ≠ dreh (sjt (k + 3)) :=
  umkehr_ne_dreh_all (by omega) _ (sjt_full (k + 2))


-- ============================================================
-- §VI — Eichungen außerhalb der Tafel
-- ============================================================

/-- Eichung: der SJT-Kreis bei drei Werten (`sjt 2`, sechs Buchstaben) — Umkehr = Drehsinn. -/
theorem sjt_drei_werte : umkehr (sjt 2) = dreh (sjt 2) := by decide

/-- Eichung: vier Werte (`sjt 3`, 24 Buchstaben). -/
theorem sjt_vier_werte : umkehr (sjt 3) ≠ dreh (sjt 3) := by decide +kernel

/-- Eichung: fünf Werte (`sjt 4`, 120 Buchstaben). -/
theorem sjt_fuenf_werte : umkehr (sjt 4) ≠ dreh (sjt 4) := by decide +kernel

/-- Eichung: sechs Werte (`sjt 5`, 720 Buchstaben). -/
theorem sjt_sechs_werte : umkehr (sjt 5) ≠ dreh (sjt 5) := by decide +kernel

/-- Eichung: drei Werte haben genau zwei umkehrfeste Anordnungen (Ausgang und Rücklauf) — zu
wenig für den Widerspruch in `umkehr_ne_dreh_all`; darum fallen dort Umkehr und Drehsinn
zusammen. -/
theorem umkehrfest_drei :
    ((origin 2).permutations'.filter (fun l => stationUmkehr l == l)).length = 2 := by
  decide +kernel

/-- Eichung: vier Werte, acht umkehrfeste Anordnungen. -/
theorem umkehrfest_vier :
    ((origin 3).permutations'.filter (fun l => stationUmkehr l == l)).length = 8 := by
  decide +kernel

/-- Eichung: fünf Werte, acht umkehrfeste Anordnungen. -/
theorem umkehrfest_fuenf :
    ((origin 4).permutations'.filter (fun l => stationUmkehr l == l)).length = 8 := by
  decide +kernel

-- ============================================================
-- Wachen — Axiom-Profile
-- ============================================================

/-! **Wachen.** Ist-Ausgabe des grünen Builds (v4.30.0-rc2), alle 29 Deklarationen. Kein
`Classical.choice`: kein `full_length`, `omega` nur auf atomaren Zielen nach `split_ifs`;
die Eichungen per `decide` sind axiomfrei. -/

/-- info: 'Reformulation.Proemial.SpiegelfesteAnordnungen.fest_eindeutig' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms fest_eindeutig

/-- info: 'Reformulation.Proemial.SpiegelfesteAnordnungen.fest_of_map_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms fest_of_map_eq

/-- info: 'Reformulation.Proemial.SpiegelfesteAnordnungen.stations_gestalt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms stations_gestalt

/-- info: 'Reformulation.Proemial.SpiegelfesteAnordnungen.stationUmkehr_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms stationUmkehr_map

/-- info: 'Reformulation.Proemial.SpiegelfesteAnordnungen.stationUmkehr_origin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms stationUmkehr_origin

/-- info: 'Reformulation.Proemial.SpiegelfesteAnordnungen.stationUmkehr_reverse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms stationUmkehr_reverse

/-- info: 'Reformulation.Proemial.SpiegelfesteAnordnungen.mem_T' depends on axioms: [propext] -/
#guard_msgs in #print axioms mem_T

/-- info: 'Reformulation.Proemial.SpiegelfesteAnordnungen.drittes' depends on axioms: [propext] -/
#guard_msgs in #print axioms drittes

/-- info: 'Reformulation.Proemial.SpiegelfesteAnordnungen.drittes_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms drittes_eq

/-- info: 'Reformulation.Proemial.SpiegelfesteAnordnungen.drittes_perm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms drittes_perm

/-- info: 'Reformulation.Proemial.SpiegelfesteAnordnungen.drittes_fest' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms drittes_fest

/-- info: 'Reformulation.Proemial.SpiegelfesteAnordnungen.drittes_ne' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms drittes_ne

/-- info: 'Reformulation.Proemial.SpiegelfesteAnordnungen.reverse_ne_origin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms reverse_ne_origin

/-- info: 'Reformulation.Proemial.SpiegelfesteAnordnungen.umkehr_ne_dreh_all' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms umkehr_ne_dreh_all

/-- info: 'Reformulation.Proemial.SpiegelfesteAnordnungen.negate_zero_val' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms negate_zero_val

/-- info: 'Reformulation.Proemial.SpiegelfesteAnordnungen.negate_ne_origin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms negate_ne_origin

/-- info: 'Reformulation.Proemial.SpiegelfesteAnordnungen.dreh_ne_self_all' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms dreh_ne_self_all

/-- info: 'Reformulation.Proemial.SpiegelfesteAnordnungen.umkehr_ne_self_all' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms umkehr_ne_self_all

/-- info: 'Reformulation.Proemial.SpiegelfesteAnordnungen.bahn_all' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms bahn_all

/-- info: 'Reformulation.Proemial.SpiegelfesteAnordnungen.umkehr_ne_dreh_four_aus_all' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms umkehr_ne_dreh_four_aus_all

/-- info: 'Reformulation.Proemial.SpiegelfesteAnordnungen.bahn_vier_aus_all' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms bahn_vier_aus_all

/-- info: 'Reformulation.Proemial.SpiegelfesteAnordnungen.sjt_umkehr_ne_dreh' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sjt_umkehr_ne_dreh

/-- info: 'Reformulation.Proemial.SpiegelfesteAnordnungen.sjt_drei_werte' does not depend on any axioms -/
#guard_msgs in #print axioms sjt_drei_werte

/-- info: 'Reformulation.Proemial.SpiegelfesteAnordnungen.sjt_vier_werte' does not depend on any axioms -/
#guard_msgs in #print axioms sjt_vier_werte

/-- info: 'Reformulation.Proemial.SpiegelfesteAnordnungen.sjt_fuenf_werte' does not depend on any axioms -/
#guard_msgs in #print axioms sjt_fuenf_werte

/-- info: 'Reformulation.Proemial.SpiegelfesteAnordnungen.sjt_sechs_werte' does not depend on any axioms -/
#guard_msgs in #print axioms sjt_sechs_werte

/-- info: 'Reformulation.Proemial.SpiegelfesteAnordnungen.umkehrfest_drei' does not depend on any axioms -/
#guard_msgs in #print axioms umkehrfest_drei

/-- info: 'Reformulation.Proemial.SpiegelfesteAnordnungen.umkehrfest_vier' does not depend on any axioms -/
#guard_msgs in #print axioms umkehrfest_vier

/-- info: 'Reformulation.Proemial.SpiegelfesteAnordnungen.umkehrfest_fuenf' does not depend on any axioms -/
#guard_msgs in #print axioms umkehrfest_fuenf
end Reformulation.Proemial.SpiegelfesteAnordnungen
