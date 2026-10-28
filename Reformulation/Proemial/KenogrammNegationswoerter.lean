import Reformulation.Proemial.GegenidentitaetProbe   -- umkehr, dreh, umkehr_umkehr, dreh_dreh, count_map_rev, guentherFamilie1
import Reformulation.Proemial.NegationCycleSJT       -- origin_nodup
import Reformulation.Proemial.ReversibleExchange     -- Reversible
import Reformulation.Kenogram.Basic                  -- relabel, relabelStep

/-!
# Proemial.KenogrammNegationswoerter — was die Kenogramme von den zwei Inversionen eines Negationskreises sehen

STANDALONE, NICHT im Aggregat;  Target `Probes`.  AxiomGate unberührt.  Sonde nach
`KorpusRev2/Prompt_Instanz_Sonde_Kenogramm_Negationswoerter.md` (Mathematiker, 28.10.2026 17:38;  Architekt 17:35).  Herkunft:
`KorpusRev2/InvestigationPost#19.md` §2.1 (Reversibilität in LZEE und die Negationskreise liegen auf verschiedenen Ebenen;  kein Satz bindet
`ReversibleExchange` und die Kreise).  Konsumiert `GegenidentitaetProbe` (`umkehr`, `dreh`, `umkehr_umkehr`, `dreh_dreh`, `count_map_rev`,
`guentherFamilie1`, `umkehr_eq_dreh_three`), `NegationCycle` (`IsFullCycle`, `stations`, `origin`), `NegationCycleSJT` (`origin_nodup`),
`NegationCycleTable` (`gerichtet`), `NegationCycleThreeCycle` (`vert`), `ReversibleExchange` (`Reversible`), `Kenogram.Basic` (`relabel`,
`relabelStep`);  ändert nichts davon.

## WAS

```text
KN0  inversionen_reversibel   BRÜCKE (trivial)  Reversible umkehr ∧ Reversible dreh — bindet ReversibleExchange an die Kreise
KN1  relabel_umkehr           SATZ, jede Wertzahl  das Trito-Kenogramm (relabel) des Worts übersteht die Umkehr
     relabel_map_inj          SATZ               dieselbe Aussage wie RelabelInvariance.relabel_map_of_injective, hier über die Faltung
                                                 geführt:  CHOICE-FREI (jenes trägt Classical.choice über relabel_isRGS und
                                                 relabel_getElem?_eq_iff, gemessen 28.10.)
KN2  deuteroW_inversionen     SATZ, jede Wertzahl  das Deutero-Kenogramm (Häufigkeiten der vorkommenden Negatoren, Multiset) übersteht
                                                 Umkehr UND Drehsinn
KN3  familien_deutero         EICHUNG (m = 3)    auf den 88:  Günthers Familie 10-9-5/5-9-10 ⟺ deuteroW = {10, 9, 5};  9-6-9 ⟺ {9, 9, 6};
                                                 6-12-6 ⟺ {6, 6, 12}.  Günthers Familien SIND auf den Wörtern die Deutero-Klassen
KN4  stationen_kenogramm      SATZ, jede Wertzahl  jede Station eines Vollkreises hat das Kenogramm 0, 1, …, m:  die STATIONEN sind dem
                                                 Kenogramm unsichtbar (NegationCycle Kopf Teil 6 (d), jetzt als Satz)
KN5  dreh_sichtbar            EICHUNG (m = 3)    es gibt einen der 88, dessen rückwärts gelesenes Wort ein anderes Trito-Kenogramm hat
     dreh_immer_sichtbar      EICHUNG (m = 3)    das gilt für JEDEN der 88 (gerechnet vorab:  0 von 88 Ausnahmen)
KN5′ dreh_unsichtbar_drei     FOLGERUNG (m = 2)  bei drei Werten ist der Drehsinn unsichtbar:  dort ist er die Umkehr (KN1)
```

**Ergebnis in einem Satz:**  Das Kenogramm sieht die Stationen nicht (KN4) und die Umkehr nicht (KN1);  den Drehsinn sieht es ab vier Werten
immer (KN5), bei drei Werten nicht (KN5′);  und auf der Deutero-Ebene fallen Günthers Familien mit den Klassen zusammen (KN3), die beide
Inversionen überstehen (KN2).

Hilfssätze:  `idxOf?_map_inj`, `fold_map_inj`, `rev_injective`, `fold_nodup`, `relabel_nodup` (Kenogramm einer duplikatfreien Liste),
`perm_cons_erase'`, `isPerm_sound`, `klasse_iff`, `familien_listen` (die Eichung auf Listenebene).  Definitionen:  `deuteroL`, `deuteroW`.

**Bauweise und Profile.**  Alle 20 Sätze ohne `Classical.choice`:  `[propext]` oder `[propext, Quot.sound]` (Wachen unten).  Zwei Stellen
waren zu umgehen:  (1) KN1 über die Faltung von `relabel` statt über `relabel_map_of_injective` (s. o.);  (2) die Gleichheit von Multisets
entscheidet Mathlib über `List.isPerm_iff` und `List.perm_cons_erase`, beide mit `Classical.choice` (gemessen 28.10., Mathlib 83a5988);  darum
`isPerm_sound` und `perm_cons_erase'` selbst, und die Klassen werden über ein Element getrennt, das der anderen Liste fehlt (`klasse_iff`).
Eichungen per `decide +kernel` (Modul unter 2 s).  Kein `native_decide`, kein `sorry`, kein True-Feld.

## ZUORDNUNG

- dass `relabel` das Trito-, `deuteroW` das Deutero-Kenogramm im Sinn von LZEE ist:  Definitionswahl des Baus (`Kenogram/Basic`,
  `A3CoarseningProbe.deutero` — deren Marken gelten;  `deuteroW` ist das Deutero des WORTS, `A3CoarseningProbe.deutero` das eines RGS;
  ein Abgleich beider ist nicht gebaut).
- Günther 1962:  der Reflektor arbeitet auf Morphogrammen, die Negation auf Werten — `PatternInvariance`-Kopf, ZUORDNUNG nah.

## QUELLE

Günthers Familien:  IGN S. 43, Tafel (18), am Bild (Hermeneutes).  LZEE S. 18–23 (Evolution irreversibel, Emanation reversibel):  TEXTSCHICHT.

## NICHT

„LZEE-Reversibilität = Umkehr/Drehsinn" als Satz (LZEE spricht von emanativen Abbildungen kenogrammatischer Folgen — andere Ebene);
„Günther hat seine Familien kenogrammatisch gemeint";  irgendein kenogrammatischer Anspruch für E5–E7 oder J (Anspruchsliste H bleibt).
Was die Sonde sagt:  AUF DEN WÖRTERN fallen Günthers Familien mit den Deutero-Klassen zusammen, die Umkehr ist dem Kenogramm unsichtbar, der
Drehsinn ab vier Werten nicht.
-/

namespace Reformulation.Proemial.KenogrammNegationswoerter

open Reformulation.Kenogram (relabel relabelStep relabel_eq_foldl)
open Reformulation.Proemial.NegationCycle
open Reformulation.Proemial.GegenidentitaetProbe
open Reformulation.Proemial.NegationCycleTable (gerichtet)
open Reformulation.Proemial.NegationCycleThreeCycle (vert)
open Reformulation.Proemial.NegationCycleSJT (origin_nodup)
open Reformulation.Proemial.ReversibleExchange (Reversible)

/-! ## KN0 — die Brücke:  Umkehr und Drehsinn sind reversibel im Sinn von `ReversibleExchange` -/

theorem inversionen_reversibel {m : ℕ} : Reversible (umkehr (m := m)) ∧ Reversible (dreh (m := m)) :=
  ⟨umkehr_umkehr, dreh_dreh⟩

/-! ## KN1 — das Trito-Kenogramm übersteht jede injektive Umbenennung, also die Umkehr -/

theorem idxOf?_map_inj {α β : Type*} [DecidableEq α] [DecidableEq β] {f : α → β}
    (hf : Function.Injective f) (x : α) : ∀ s : List α, (s.map f).idxOf? (f x) = s.idxOf? x
  | [] => rfl
  | y :: ys => by
    rw [List.map_cons, List.idxOf?_cons, List.idxOf?_cons, idxOf?_map_inj hf x ys]
    have h : (f y == f x) = (y == x) := by
      show decide (f y = f x) = decide (y = x)
      exact decide_eq_decide.mpr ⟨fun e => hf e, fun e => e ▸ rfl⟩
    rw [h]

theorem fold_map_inj {α β : Type*} [DecidableEq α] [DecidableEq β] {f : α → β}
    (hf : Function.Injective f) : ∀ (l : List α) (labels : List ℕ) (seen : List α),
      (l.map f).foldl relabelStep (labels, seen.map f) =
        ((l.foldl relabelStep (labels, seen)).1, (l.foldl relabelStep (labels, seen)).2.map f)
  | [], _, _ => rfl
  | x :: xs, labels, seen => by
    rw [List.map_cons, List.foldl_cons, List.foldl_cons]
    have hstep : relabelStep (labels, seen.map f) (f x) =
        ((relabelStep (labels, seen) x).1, (relabelStep (labels, seen) x).2.map f) := by
      unfold relabelStep
      rw [idxOf?_map_inj hf x seen]
      cases seen.idxOf? x with
      | some k => rfl
      | none => rw [List.length_map, List.map_append, List.map_cons, List.map_nil]
    rw [hstep]
    exact fold_map_inj hf xs _ _

/-- **`relabel` übersteht jede injektive Umbenennung** (dieselbe Aussage wie `RelabelInvariance.relabel_map_of_injective`,
    hier über die Faltung geführt). -/
theorem relabel_map_inj {α β : Type*} [DecidableEq α] [DecidableEq β] {f : α → β}
    (hf : Function.Injective f) (l : List α) : relabel (l.map f) = relabel l := by
  rw [relabel_eq_foldl, relabel_eq_foldl]
  exact congrArg Prod.fst (fold_map_inj hf l [] [])

theorem rev_injective {m : ℕ} : Function.Injective (Fin.rev (n := m)) := fun a b h => by
  rw [← Fin.rev_rev a, h, Fin.rev_rev]

/-- (KN1) **Die Umkehr ist dem Trito-Kenogramm des Worts unsichtbar.** -/
theorem relabel_umkehr {m : ℕ} (w : List (Fin m)) : relabel (umkehr w) = relabel w :=
  relabel_map_inj rev_injective w

/-! ## KN2 — das Deutero-Kenogramm:  die Häufigkeiten der vorkommenden Negatoren -/

/-- Die Häufigkeiten der vorkommenden Symbole, als Liste in der Ordnung der Symbole. -/
def deuteroL {m : ℕ} (w : List (Fin m)) : List ℕ :=
  ((List.finRange m).map (fun a => w.count a)).filter (fun k => k != 0)

/-- **Deutero-Kenogramm eines Worts:**  die Häufigkeiten der vorkommenden Symbole, als Multiset. -/
def deuteroW {m : ℕ} (w : List (Fin m)) : Multiset ℕ := (deuteroL w : Multiset ℕ)

theorem deuteroW_dreh {m : ℕ} (w : List (Fin m)) : deuteroW (dreh w) = deuteroW w := by
  unfold deuteroW deuteroL dreh
  rw [List.map_congr_left (fun a _ => List.count_reverse (a := a) (l := w))]

theorem deuteroW_umkehr {m : ℕ} (w : List (Fin m)) : deuteroW (umkehr w) = deuteroW w := by
  unfold deuteroW deuteroL umkehr
  rw [List.map_congr_left (fun a _ => count_map_rev a w)]
  have e : (List.finRange m).map (fun a => w.count (Fin.rev a)) =
      ((List.finRange m).map (fun a => w.count a)).reverse := by
    rw [← List.map_reverse, List.finRange_reverse, List.map_map]
    rfl
  rw [e, List.filter_reverse, Multiset.coe_reverse]

/-- (KN2) **Das Deutero-Kenogramm übersteht Umkehr und Drehsinn.** -/
theorem deuteroW_inversionen {m : ℕ} (w : List (Fin m)) :
    deuteroW (dreh w) = deuteroW w ∧ deuteroW (umkehr w) = deuteroW w :=
  ⟨deuteroW_dreh w, deuteroW_umkehr w⟩

/-! ## KN3 — Günthers Familien sind auf den 88 die Deutero-Klassen

Die Gleichheit von Multisets entscheidet Mathlib über `List.isPerm_iff`, das `Classical.choice` trägt (gemessen 28.10., Mathlib 83a5988);
darum hier die Richtung `isPerm → Perm` selbst (`isPerm_sound`, über `perm_cons_erase'`) und die Trennung der Klassen über ein
Element, das der einen Liste fehlt. -/

theorem perm_cons_erase' {a : ℕ} : ∀ {l : List ℕ}, a ∈ l → l.Perm (a :: l.erase a)
  | b :: l, h => by
    by_cases hb : b = a
    · subst hb; rw [List.erase_cons_head]
    · have hb' : (b == a) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; exact hb
      rw [List.erase_cons_tail (by rw [hb']; exact Bool.false_ne_true)]
      have ha : a ∈ l := (List.mem_cons.mp h).resolve_left (fun e => hb e.symm)
      exact ((perm_cons_erase' ha).cons b).trans (List.Perm.swap a b _)

theorem isPerm_sound : ∀ {l₁ l₂ : List ℕ}, l₁.isPerm l₂ = true → l₁.Perm l₂
  | [], l₂, h => by
    cases l₂ with
    | nil => exact List.Perm.refl _
    | cons _ _ => exact absurd h Bool.false_ne_true
  | a :: l₁, l₂, h => by
    rw [List.isPerm, Bool.and_eq_true] at h
    have ha : a ∈ l₂ := List.contains_iff_mem.mp h.1
    exact ((isPerm_sound h.2).cons a).trans (perm_cons_erase' ha).symm

/-- Eine Klasse von Wörtern ist genau dann die Deutero-Klasse zu `l`, wenn ihre Wörter `l` als Häufigkeiten tragen und jedem anderen
    Wort ein Element von `l` fehlt. -/
theorem klasse_iff {m : ℕ} {P : List (Fin m) → Prop} [DecidablePred P] {w : List (Fin m)} {l : List ℕ}
    (h1 : P w → (deuteroL w).isPerm l = true) (h2 : ¬ P w → ∃ a ∈ l, a ∉ deuteroL w) :
    P w ↔ deuteroW w = (l : Multiset ℕ) := by
  constructor
  · intro hp
    exact Multiset.coe_eq_coe.mpr (isPerm_sound (h1 hp))
  · intro e
    exact Decidable.byContradiction fun hp => by
      obtain ⟨a, ha, hn⟩ := h2 hp
      have h' : a ∈ deuteroW w := by rw [e]; exact Multiset.mem_coe.mpr ha
      exact hn (Multiset.mem_coe.mp (h' : a ∈ ((deuteroL w : List ℕ) : Multiset ℕ)))

theorem familien_listen :
    (∀ w ∈ gerichtet, (guentherFamilie1 w = true → (deuteroL w).isPerm [10, 9, 5] = true) ∧
      (¬ guentherFamilie1 w = true → ∃ a ∈ [10, 9, 5], a ∉ deuteroL w)) ∧
    (∀ w ∈ gerichtet, (vert w = (9, 6, 9) → (deuteroL w).isPerm [9, 9, 6] = true) ∧
      (¬ vert w = (9, 6, 9) → ∃ a ∈ [9, 9, 6], a ∉ deuteroL w)) ∧
    (∀ w ∈ gerichtet, (vert w = (6, 12, 6) → (deuteroL w).isPerm [6, 6, 12] = true) ∧
      (¬ vert w = (6, 12, 6) → ∃ a ∈ [6, 6, 12], a ∉ deuteroL w)) := by
  decide +kernel

/-- (KN3) **Günthers Familien (IGN S. 43) sind auf den 88 gerichteten Vollkreisen genau die Deutero-Klassen.** -/
theorem familien_deutero :
    (∀ w ∈ gerichtet, guentherFamilie1 w = true ↔ deuteroW w = ↑[10, 9, 5]) ∧
    (∀ w ∈ gerichtet, vert w = (9, 6, 9) ↔ deuteroW w = ↑[9, 9, 6]) ∧
    (∀ w ∈ gerichtet, vert w = (6, 12, 6) ↔ deuteroW w = ↑[6, 6, 12]) :=
  ⟨fun w hw => klasse_iff (P := fun w => guentherFamilie1 w = true) (familien_listen.1 w hw).1 (familien_listen.1 w hw).2,
   fun w hw => klasse_iff (P := fun w => vert w = (9, 6, 9)) (familien_listen.2.1 w hw).1 (familien_listen.2.1 w hw).2,
   fun w hw => klasse_iff (P := fun w => vert w = (6, 12, 6)) (familien_listen.2.2 w hw).1 (familien_listen.2.2 w hw).2⟩

/-! ## KN4 — die Stationen eines Vollkreises sind dem Kenogramm unsichtbar -/

theorem fold_nodup {α : Type*} [DecidableEq α] : ∀ (l : List α) (labels : List ℕ) (seen : List α),
    l.Nodup → (∀ x ∈ l, x ∉ seen) →
      l.foldl relabelStep (labels, seen) = (labels ++ List.range' seen.length l.length, seen ++ l)
  | [], labels, seen, _, _ => by rw [List.foldl_nil, List.length_nil, List.range'_zero, List.append_nil, List.append_nil]
  | x :: xs, labels, seen, hnd, hnot => by
    rw [List.foldl_cons]
    have hx : x ∉ seen := hnot x List.mem_cons_self
    have hstep : relabelStep (labels, seen) x = (labels ++ [seen.length], seen ++ [x]) := by
      unfold relabelStep
      rw [List.idxOf?_eq_none_iff.mpr hx]
    rw [hstep]
    have hnd' := List.nodup_cons.mp hnd
    have hnot' : ∀ y ∈ xs, y ∉ seen ++ [x] := fun y hy h => by
      rcases List.mem_append.mp h with h | h
      · exact hnot y (List.mem_cons_of_mem x hy) h
      · rw [List.mem_singleton.mp h] at hy; exact hnd'.1 hy
    rw [fold_nodup xs _ _ hnd'.2 hnot', List.length_append, List.length_singleton, List.length_cons,
      List.range'_succ, List.append_assoc, List.append_assoc, List.singleton_append, List.singleton_append]

/-- Eine duplikatfreie Liste hat das Kenogramm `0, 1, …, n−1`. -/
theorem relabel_nodup {α : Type*} [DecidableEq α] (l : List α) (h : l.Nodup) :
    relabel l = List.range l.length := by
  rw [relabel_eq_foldl, fold_nodup l [] [] h (fun _ _ h => absurd h List.not_mem_nil), List.length_nil,
    List.nil_append, List.range_eq_range']

/-- (KN4) **Jede Station eines Vollkreises hat dasselbe Kenogramm** `0, 1, …, m`:  auf der Kenogramm-Ebene sind die Stationen
    unsichtbar (NegationCycle, Kopf Teil 6 (d), als Satz). -/
theorem stationen_kenogramm {m : ℕ} {seq : List (Fin m)} (h : IsFullCycle seq) :
    ∀ l ∈ stations seq (origin m), relabel l = List.range (m + 1) := by
  intro l hl
  have hp : l.Perm (origin m) := List.mem_permutations'.mp (h.only_arrangements l hl)
  rw [relabel_nodup l (hp.nodup_iff.mpr (origin_nodup m)), hp.length_eq]
  unfold origin
  rw [List.length_finRange]

/-! ## KN5 — der Drehsinn ist dem Kenogramm sichtbar -/

/-- (KN5) **Der Drehsinn ist auf der Kenogramm-Ebene sichtbar:**  es gibt einen gerichteten Vollkreis, dessen rückwärts gelesenes Wort
    ein anderes Trito-Kenogramm hat. -/
theorem dreh_sichtbar : ∃ w ∈ gerichtet, relabel (dreh w) ≠ relabel w := by
  decide +kernel

/-- (KN5, scharf) **Für jeden der 88 gerichteten Vollkreise** hat das rückwärts gelesene Wort ein anderes Trito-Kenogramm. -/
theorem dreh_immer_sichtbar : ∀ w ∈ gerichtet, relabel (dreh w) ≠ relabel w := by
  decide +kernel

/-- (KN5′) **Bei drei Werten ist der Drehsinn dem Kenogramm unsichtbar** — dort ist er die Umkehr (`umkehr_eq_dreh_three`), und
    die sieht das Kenogramm nicht (KN1).  Die Sichtbarkeit beginnt bei vier Werten (KN5). -/
theorem dreh_unsichtbar_drei (w : List (Fin 2)) (h : IsFullCycle w) : relabel (dreh w) = relabel w := by
  rw [← umkehr_eq_dreh_three w h]
  exact relabel_umkehr w

end Reformulation.Proemial.KenogrammNegationswoerter

/-! ## Axiom-Wachen (gemessen, verbatim) -/

/-- info: 'Reformulation.Proemial.KenogrammNegationswoerter.inversionen_reversibel' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.KenogrammNegationswoerter.inversionen_reversibel

/-- info: 'Reformulation.Proemial.KenogrammNegationswoerter.idxOf?_map_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.KenogrammNegationswoerter.idxOf?_map_inj

/-- info: 'Reformulation.Proemial.KenogrammNegationswoerter.fold_map_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.KenogrammNegationswoerter.fold_map_inj

/-- info: 'Reformulation.Proemial.KenogrammNegationswoerter.relabel_map_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.KenogrammNegationswoerter.relabel_map_inj

/-- info: 'Reformulation.Proemial.KenogrammNegationswoerter.rev_injective' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.KenogrammNegationswoerter.rev_injective

/-- info: 'Reformulation.Proemial.KenogrammNegationswoerter.relabel_umkehr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.KenogrammNegationswoerter.relabel_umkehr

/-- info: 'Reformulation.Proemial.KenogrammNegationswoerter.deuteroW_dreh' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.KenogrammNegationswoerter.deuteroW_dreh

/-- info: 'Reformulation.Proemial.KenogrammNegationswoerter.deuteroW_umkehr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.KenogrammNegationswoerter.deuteroW_umkehr

/-- info: 'Reformulation.Proemial.KenogrammNegationswoerter.deuteroW_inversionen' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.KenogrammNegationswoerter.deuteroW_inversionen

/-- info: 'Reformulation.Proemial.KenogrammNegationswoerter.perm_cons_erase'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.KenogrammNegationswoerter.perm_cons_erase'

/-- info: 'Reformulation.Proemial.KenogrammNegationswoerter.isPerm_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.KenogrammNegationswoerter.isPerm_sound

/-- info: 'Reformulation.Proemial.KenogrammNegationswoerter.klasse_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.KenogrammNegationswoerter.klasse_iff

/-- info: 'Reformulation.Proemial.KenogrammNegationswoerter.familien_listen' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.KenogrammNegationswoerter.familien_listen

/-- info: 'Reformulation.Proemial.KenogrammNegationswoerter.familien_deutero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.KenogrammNegationswoerter.familien_deutero

/-- info: 'Reformulation.Proemial.KenogrammNegationswoerter.fold_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.KenogrammNegationswoerter.fold_nodup

/-- info: 'Reformulation.Proemial.KenogrammNegationswoerter.relabel_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.KenogrammNegationswoerter.relabel_nodup

/-- info: 'Reformulation.Proemial.KenogrammNegationswoerter.stationen_kenogramm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.KenogrammNegationswoerter.stationen_kenogramm

/-- info: 'Reformulation.Proemial.KenogrammNegationswoerter.dreh_sichtbar' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.KenogrammNegationswoerter.dreh_sichtbar

/-- info: 'Reformulation.Proemial.KenogrammNegationswoerter.dreh_immer_sichtbar' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.KenogrammNegationswoerter.dreh_immer_sichtbar

/-- info: 'Reformulation.Proemial.KenogrammNegationswoerter.dreh_unsichtbar_drei' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.KenogrammNegationswoerter.dreh_unsichtbar_drei
