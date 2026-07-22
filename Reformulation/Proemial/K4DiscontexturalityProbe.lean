import Reformulation.Kenogram.Basic
import Reformulation.Proemial.A1DescentProbe    -- descent
import Reformulation.Proemial.A3CoarseningProbe -- proto, deutero

/-!
# K4DiscontexturalityProbe — die kenogrammatische Nicht-Reduzierbarkeit, lokalisiert

STANDALONE, NICHT im Aggregat (wie `CartesianProbe`/`A1DescentProbe`/`K3CouplingProbe`/
`A3CoarseningProbe`/`GegenlaeufigkeitProbe`). AxiomGate unberührt. Diese Sonde wehrt die
**Trivialität** ab: die bloße Nicht-Faktorisierbarkeit `¬∃f` am Zeugen (K4-2) wäre fast
geschenkt — die Sonde **lokalisiert** die Nicht-Reduzierbarkeit an der Trito-Information
`lastBlock` (Klassen-Größe der gestrichenen letzten Stelle).

`descent` (A1DescentProbe, `= dropLast`), `proto`/`deutero` (A3CoarseningProbe) werden
**unverändert** importiert.

## Geprüfte Sätze

- **K4-1 (die Substanz, generisch — der Hauptaufwand).** `deutero_descent_eq`:
  `descent`s Wirkung auf `deutero` ist durch `deutero` *plus* `lastBlock` bestimmt,
  per expliziter `erase/+`-Formel. Beweis über die Zerlegung `r.val = dropLast ++ [lastVal]`,
  die Additivität der Häufigkeits-Zählung und die **Lückenlosigkeit** des RGS
  (`rgs_lueckenlos`, hier term-bewiesen via `reverseRecOn`): bei `lastBlock = 1`
  verschwindet die letzte Klasse (proto sinkt um 1), sonst schrumpft sie um 1
  (proto bleibt).
- **K4-2 (die Diskontexturalität, Korollar/Zeuge).** `descent_not_factoring`:
  `descent` faktorisiert nicht durch `deutero` (Zeugenpaar `[0,0,1]`/`[0,1,0]`).
- **K4-3 (die Lokalisierung, Zeuge).** `lastBlock_not_deutero_determined`:
  `lastBlock` ist nicht aus `deutero` bestimmbar.

Zusammenspiel: K4-1 ⟹ `deutero(descent)` ist Funktion von `(deutero, lastBlock)`;
K4-3 ⟹ `lastBlock` ist *nicht* Funktion von `deutero`; K4-2 ⟹ `deutero(descent)` ist
nicht durch `deutero` allein bestimmt — **exakt an `lastBlock` lokalisiert**.

## Reichweite / Abweichung vom Spec-Wortlaut (zwingend mitgeführt)

Die explizite Formel K4-1 steht hier für `r : RGS (n+2)` (Länge ≥ 2), NICHT für die
Spec-Signatur `r : RGS (n+1)`. Grund — ein term-verifizierter Negativ-Befund, KEIN
Engpass-Umgehen: die `RGS (n+1)`-Form ist im Lean-Kodierung **falsch** am einzigen
degenerierten Punkt `r = [0]` (n=0). Dort ist `descent r = []`, und
`deutero [] = {0}` (Artefakt von `proto [] = 0+1 = 1`, das die leere Liste als „eine
Klasse der Größe 0" liest), während die Formel-RHS `{}` liefert. Die externe
Vor-Verifikation (1155 = B₁+…+B₇, Längen 1–7) benutzte die mathematische Konvention
`deutero [] = {}` und sah daher kein Gegenbeispiel; die Diskrepanz ist rein der
`proto [] = 1`-Konvention geschuldet. Für `RGS (n+2)` ist `descent r` nichtleer, das
Artefakt entfällt, und die Formel trägt die volle Lokalisierungs-Substanz (generisch,
nicht `decide`). — Die kenogrammatische DiskontexturalitätK4′ ist damit eingelöst als
**lokalisierte** Nicht-Reduzierbarkeit; NICHT berührt bleiben die wert-schichtige
Rejektions-Manifestation, die architektur-schichtige Diskontexturalitäts-Setzung
(Form-β, eigene Naht) und ρ selbst.

Kein `sorry`, kein `: True`-Feld, kein `axiom`, kein `native_decide`.
-/

namespace Reformulation.Proemial.K4DiscontexturalityProbe

open Reformulation.Kenogram
open Reformulation.Proemial.A1DescentProbe
open Reformulation.Proemial.A3CoarseningProbe

-- ============================================================
-- §I — Hilfs-Begriff und Zähl-/Maximums-Lemmas
-- ============================================================

/-- Häufigkeit eines Wertes (Klassen-Größe via Filter-Länge, deckungsgleich mit dem
`deutero`-Integranden). -/
def cnt (v : ℕ) (l : List ℕ) : ℕ := (l.filter (· = v)).length

/-- Anfügen eines Zeichens erhöht die Häufigkeit genau dann, wenn es der gezählte
Wert ist. Trägt die Additivität der Klassen-Größen unter `dropLast`. -/
theorem cnt_append_singleton (l : List ℕ) (a v : ℕ) :
    cnt v (l ++ [a]) = cnt v l + (if a = v then 1 else 0) := by
  simp only [cnt, List.filter_append, List.length_append]
  by_cases h : a = v <;> simp [h]

/-- Eine vorkommende Stelle hat positive Häufigkeit. -/
theorem cnt_pos_of_mem {v : ℕ} {l : List ℕ} (h : v ∈ l) : 0 < cnt v l :=
  List.length_pos_of_mem (List.mem_filter.mpr ⟨h, by simp⟩)

/-- Positive Häufigkeit bezeugt ein Vorkommen. -/
theorem mem_of_cnt_pos {v : ℕ} {l : List ℕ} (h : 0 < cnt v l) : v ∈ l := by
  rw [cnt, List.length_pos_iff_ne_nil] at h
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ h
  rw [List.mem_filter] at hx
  have hxv : x = v := by simpa using hx.2
  rw [← hxv]; exact hx.1

/-- Das `foldr`-Maximum dominiert jede vorkommende Stelle. -/
theorem le_foldr_max_of_mem {v : ℕ} {l : List ℕ} (h : v ∈ l) : v ≤ l.foldr max 0 := by
  induction l with
  | nil => exact absurd h (by simp)
  | cons a t ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h'
    · exact le_max_left _ _
    · exact le_trans (ih h') (le_max_right _ _)

/-- Das `foldr`-Maximum eines nichtleeren RGS wird angenommen. -/
theorem foldr_max_mem (l : List ℕ) (h : l ≠ []) : l.foldr max 0 ∈ l := by
  induction l with
  | nil => exact absurd rfl h
  | cons a t ih =>
    rcases eq_or_ne t [] with rfl | ht
    · simp
    · simp only [List.foldr_cons]
      rcases le_total a (t.foldr max 0) with hle | hle
      · rw [max_eq_right hle]; exact List.mem_cons_of_mem a (ih ht)
      · rw [max_eq_left hle]; exact List.mem_cons_self

/-- **Lückenlosigkeit.** In einem nichtleeren RGS kommt jeder Wert `≤` Maximum vor —
die Werte sind exakt `{0, …, proto-1}`. Beweis per `reverseRecOn` über die
Anfüge-Form der RGS-Invariante (`isRGS_cons_concat`). Trägt den `proto`-Sprung
in K4-1: eine letzte Klasse der Größe 1 ist notwendig der größte Wert. -/
theorem rgs_lueckenlos : ∀ {l : List ℕ}, IsRGS l → l ≠ [] → ∀ v, v ≤ l.foldr max 0 → v ∈ l := by
  intro l
  induction l using List.reverseRecOn with
  | nil => intro _ hne; exact absurd rfl hne
  | append_singleton xs x ih =>
    intro hrgs _ v hv
    rcases eq_or_ne xs [] with rfl | hxs
    · simp only [List.nil_append] at hrgs ⊢
      have hx : x = 0 := by simpa [IsRGS, isRGSAux] using hrgs
      subst hx
      have : v = 0 := by simpa using hv
      subst this
      exact List.mem_singleton.mpr rfl
    · obtain ⟨a, t, rfl⟩ : ∃ a t, xs = a :: t := by
        cases xs with
        | nil => exact absurd rfl hxs
        | cons a t => exact ⟨a, t, rfl⟩
      rw [isRGS_cons_concat] at hrgs
      obtain ⟨hrgsxs, hbound⟩ := hrgs
      rw [foldr_max_append_singleton] at hv
      rcases Nat.lt_or_ge ((a :: t).foldr max 0) v with hlt | hge
      · have hvx : v = x := by omega
        subst hvx
        exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
      · exact List.mem_append_left _ (ih hrgsxs (by simp) v hge)

-- ============================================================
-- §II — Definitionen (Trito-Information der letzten Stelle)
-- ============================================================

/-- Wert der letzten Stelle (`r.val` hat Länge `n+1`, ist also nichtleer). -/
def lastVal {n : ℕ} (r : RGS (n+1)) : ℕ :=
  r.val.getLast (List.ne_nil_of_length_pos (by have h := r.property.1; omega))

/-- Größe der Klasse, zu der die letzte Stelle gehört (Trito-Information:
*welche* Klasse, nicht nur *wie groß* die Klassen sind). -/
def lastBlock {n : ℕ} (r : RGS (n+1)) : ℕ := (r.val.filter (· = lastVal r)).length

-- ============================================================
-- §III.1 — K4-1: die Substanz (generisch, der Hauptaufwand)
-- ============================================================

/-- **K4-1 (die Substanz, generisch).** `descent`s `deutero`-Wirkung ist durch
`deutero` *plus* `lastBlock` bestimmt: die Klasse der gestrichenen letzten Stelle
(Größe `lastBlock r`) schrumpft um eins, bei Größe 1 verschwindet sie (und `proto`
sinkt um 1); alle anderen Klassen bleiben.

Bewusst für `RGS (n+2)` (Länge ≥ 2, `descent` nichtleer) — die Spec-Signatur
`RGS (n+1)` ist im Lean-Kodierung am degenerierten Punkt `r = [0]` falsch
(`deutero [] = {0}`-Artefakt, `proto [] = 1`); siehe Modul-Doku. Das ist die
echte, generische Form der Lokalisierung (kein `decide`). -/
theorem deutero_descent_eq {n : ℕ} (r : RGS (n+2)) :
    deutero (descent r) =
      (deutero r).erase (lastBlock r) +
      (if lastBlock r = 1 then (0 : Multiset ℕ) else {lastBlock r - 1}) := by
  -- Strukturelle Vorbereitung
  have hne : r.val ≠ [] := List.ne_nil_of_length_pos (by have h := r.property.1; omega)
  set L := r.val with hL
  set lv := lastVal r with hlv
  have hdecomp : L = L.dropLast ++ [lv] := by
    rw [hlv, lastVal]; exact (List.dropLast_append_getLast _).symm
  set D := L.dropLast with hD
  have hDval : (descent r).val = D := rfl
  have hDne : D ≠ [] := by
    have hl2 : L.length = n + 2 := r.property.1
    have : D.length = n + 1 := by rw [hD, List.length_dropLast]; omega
    exact List.ne_nil_of_length_pos (by omega)
  have hDrgs : IsRGS D := isRGS_dropLast r.property.2
  -- Maxima
  set M := L.foldr max 0 with hM
  set Md := D.foldr max 0 with hMd
  have hMmax : M = max Md lv := by
    rw [hM]; conv_lhs => rw [hdecomp]
    rw [foldr_max_append_singleton]
  -- proto-Werte
  have hpr : proto r = M + 1 := rfl
  have hpd : proto (descent r) = Md + 1 := rfl
  -- Zähl-Relation
  have hcnt : ∀ v, cnt v L = cnt v D + (if lv = v then 1 else 0) := by
    intro v; conv_lhs => rw [hdecomp]; rw [cnt_append_singleton]
  have hlb : lastBlock r = cnt lv L := rfl
  have hdr : deutero r = (Multiset.range (proto r)).map (fun v => cnt v L) := rfl
  have hdd : deutero (descent r) = (Multiset.range (proto (descent r))).map (fun v => cnt v D) := rfl
  have hlvM : lv ≤ M := by rw [hMmax]; exact le_max_right _ _
  by_cases hcase : lastBlock r = 1
  · -- Fall lastBlock r = 1: die letzte Klasse verschwindet, proto sinkt um 1
    have hcntL1 : cnt lv L = 1 := by rw [← hlb]; exact hcase
    have hcntlvD0 : cnt lv D = 0 := by have h := hcnt lv; rw [if_pos rfl] at h; omega
    have hlvD : lv ∉ D := fun hmem => by have := cnt_pos_of_mem hmem; omega
    obtain ⟨a, t, hat⟩ := List.exists_cons_of_ne_nil hDne
    have hLrgs : IsRGS L := r.property.2
    have hbound : lv ≤ Md + 1 := by
      have hh : IsRGS ((a :: t) ++ [lv]) := by rw [← hat, ← hdecomp]; exact hLrgs
      rw [isRGS_cons_concat] at hh
      have h2 := hh.2; rw [← hat, ← hMd] at h2; exact h2
    have hlvgt : Md < lv := by
      by_contra h
      exact hlvD (rgs_lueckenlos hDrgs hDne lv (by rw [← hMd]; exact Nat.not_lt.mp h))
    have hlveq : lv = Md + 1 := by omega
    have hMeq : M = Md + 1 := by rw [hMmax, hlveq]; omega
    have hkey : deutero r = (1 : ℕ) ::ₘ deutero (descent r) := by
      rw [hdr, hpr, hMeq, hdd, hpd, Multiset.range_succ, Multiset.map_cons]
      congr 1
      · rw [← hlveq]; exact hcntL1
      · apply Multiset.map_congr rfl
        intro v hv
        rw [Multiset.mem_range] at hv
        have hc := hcnt v; rw [if_neg (by omega)] at hc
        omega
    rw [hcase, hkey]
    simp [Multiset.erase_cons_head]
  · -- Fall lastBlock r ≠ 1: die letzte Klasse schrumpft um 1, proto bleibt
    have hlvL : lv ∈ L := by
      rw [hdecomp]; exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
    have hcge1 : 1 ≤ cnt lv L := cnt_pos_of_mem hlvL
    have hcL : cnt lv L = cnt lv D + 1 := by have h := hcnt lv; rwa [if_pos rfl] at h
    have hcge2 : 2 ≤ cnt lv L := by
      rcases Nat.lt_or_ge (cnt lv L) 2 with h | h
      · exact absurd (by rw [hlb]; omega) hcase
      · exact h
    have hlvD : lv ∈ D := mem_of_cnt_pos (by omega)
    have hlvMd : lv ≤ Md := by rw [hMd]; exact le_foldr_max_of_mem hlvD
    have hMdeq : Md = M := by rw [hMmax]; omega
    have hlvrange : lv ∈ Multiset.range (M + 1) := Multiset.mem_range.mpr (by omega)
    have hsplit : ∀ (f : ℕ → ℕ),
        (Multiset.range (M+1)).map f
          = f lv ::ₘ ((Multiset.range (M+1)).erase lv).map f := by
      intro f
      conv_lhs => rw [← Multiset.cons_erase hlvrange]
      rw [Multiset.map_cons]
    have hmapeq : ((Multiset.range (M+1)).erase lv).map (fun v => cnt v L)
        = ((Multiset.range (M+1)).erase lv).map (fun v => cnt v D) := by
      apply Multiset.map_congr rfl
      intro v hv
      have hvne : v ≠ lv := by
        intro h
        have hlvmem : lv ∈ (Multiset.range (M+1)).erase lv := h ▸ hv
        have h1 : Multiset.count lv (Multiset.range (M+1)) = 1 :=
          Multiset.count_eq_one_of_mem (Multiset.nodup_range _) hlvrange
        have h2 : Multiset.count lv ((Multiset.range (M+1)).erase lv) = 0 := by
          rw [Multiset.count_erase_self, h1]
        rw [← Multiset.count_pos] at hlvmem
        omega
      have hc := hcnt v; rw [if_neg (fun h => hvne h.symm)] at hc
      show cnt v L = cnt v D
      omega
    rw [hdd, hpd, hMdeq, hdr, hpr, hlb,
        hsplit (fun v => cnt v D), hsplit (fun v => cnt v L), hmapeq]
    rw [Multiset.erase_cons_head, if_neg (by omega), hcL]
    simp only [Nat.add_sub_cancel]
    rw [show ({cnt lv D} : Multiset ℕ) = cnt lv D ::ₘ 0 from rfl,
        Multiset.add_cons, Multiset.add_zero]

-- ============================================================
-- §III.2 — K4-2: die Diskontexturalität (Korollar, Zeuge)
-- ============================================================

/-- **K4-2 (die Diskontexturalität).** `descent` faktorisiert nicht durch `deutero`:
ein `f` müsste `f {1,2}` zugleich `{2}` (= `deutero (descent [0,0,1])`) und
`{1,1}` (= `deutero (descent [0,1,0])`) setzen. -/
theorem descent_not_factoring :
    ¬ ∃ f : Multiset ℕ → Multiset ℕ, ∀ (r : RGS 3), deutero (descent r) = f (deutero r) := by
  rintro ⟨f, hf⟩
  have h1 : deutero (descent (⟨[0,0,1], by decide⟩ : RGS 3))
      = f (deutero (⟨[0,0,1], by decide⟩ : RGS 3)) := hf _
  have h2 : deutero (descent (⟨[0,1,0], by decide⟩ : RGS 3))
      = f (deutero (⟨[0,1,0], by decide⟩ : RGS 3)) := hf _
  have hdeu : deutero (⟨[0,0,1], by decide⟩ : RGS 3) = deutero (⟨[0,1,0], by decide⟩ : RGS 3) := by
    decide
  rw [hdeu] at h1
  rw [← h2] at h1
  revert h1; decide

-- ============================================================
-- §III.3 — K4-3: die Lokalisierung (Zeuge)
-- ============================================================

/-- **K4-3 (die Lokalisierung).** `lastBlock` ist nicht aus `deutero` bestimmbar:
`[0,0,1]` und `[0,1,0]` haben gleiches `deutero = {1,2}`, aber `lastBlock` `1` vs. `2`.
`lastBlock` ist genau die Trito-Information, die `deutero` vergisst. -/
theorem lastBlock_not_deutero_determined :
    ∃ (a b : RGS 3), deutero a = deutero b ∧ lastBlock a ≠ lastBlock b := by
  refine ⟨⟨[0,0,1], by decide⟩, ⟨[0,1,0], by decide⟩, ?_, ?_⟩
  · decide
  · decide

-- ============================================================
-- §IV — Verifikation (kein `sorryAx`)
-- ============================================================

#print axioms deutero_descent_eq
#print axioms descent_not_factoring
#print axioms lastBlock_not_deutero_determined

end Reformulation.Proemial.K4DiscontexturalityProbe
