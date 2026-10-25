import Reformulation.Proemial.NegationCycle     -- sw, sw_val, sw_rev_conj
import Mathlib.Data.Fin.Rev                      -- Fin.revPerm
import Mathlib.Order.Fin.Basic                   -- Fin.rev_strictAnti
import Mathlib.Algebra.Group.End                 -- die Gruppe Equiv.Perm (1)

/-!
# Proemial.OrdnungAusUmtauschProbe — die Nachbartausche bestimmen die Ordnung bis auf eine Umkehr

STANDALONE, NICHT im Aggregat;  Target `Probes`.  AxiomGate unberührt.  Bau nach
`KorpusRev2/Prompt_Instanz_Ordnung_aus_Umtausch_Bau.md` (Mathematiker, 25.10.2026 11:01;  Architekt 11:00 „(a) Bau"), Grundlage
`KorpusRev2/Notiz_Ordnung_aus_Umtausch_Instanz_Impl.md` (10:56) und die Kratzdatei `KorpusRev2/T_Vorprobe_Skripte/Ordnung_aus_Umtausch.lean`.
Konsumiert `NegationCycle` (`sw`, `sw_val`, `sw_rev_conj`);  ändert nichts davon.

## WAS

Eine Wertpermutation σ **erhält die Negatoren** (`erhaeltNegatoren`), wenn sie durch Konjugation jeden Negator `N_{i+1} = sw i` in einen
Negator überführt.  Die Sätze:

```text
nachbar_iff                FOLGERUNG (dünn)   erhaeltNegatoren σ ↔ σ schickt benachbarte Werte auf benachbarte Werte
fest_oder_umkehr           FOLGERUNG          erhaeltNegatoren σ → (∀ v, σ v = v) ∨ (∀ v, σ v = Fin.rev v)
ordnung_aus_umtausch_zwei  ZUSAMMENSTELLUNG   erhaeltNegatoren σ ↔ σ = 1 ∨ σ = Fin.revPerm                    (jede Wertzahl)
ordnung_aus_umtausch       ZUSAMMENSTELLUNG   erhaeltNegatoren σ ↔ StrictMono σ ∨ StrictAnti σ                 (jede Wertzahl)
genau_zwei                 FOLGERUNG (dünn)   1 = Fin.revPerm ↔ m = 0 — ab zwei Werten genau zwei Lösungen;  bei EINEM Wert (m = 0)
                                              fallen sie zusammen
eich_drei/vier/fuenf       EICHUNG (decide)   über allen 6, 24, 120 Permutationen (Tupelform):  (A) ↔ (B), je genau zwei
gegen_*                    EICHUNG (decide)   die Gegenproben:  „hält 0 fest" ist mit (A) nicht äquivalent (drei, fünf Werte);  die
                                              Drehung v ↦ v + 1, (1 2)(4 5), und bei vier Werten der Tausch von 1 und 3 erfüllen (A) nicht
```

Die Richtung „Ordnung ⇒ Tausche" steht im Bestand:  `NegationCycle.sw_rev_conj` (die Umkehr führt `N_{i+1}` in `N_{m−i}` über) und
`NegatorContexture` K2 („Unmittelbar tauschen nur Nachbarn der Ordnung", QUELLENFEST).  **Diese Sonde baut die Umkehrung:  Tausche ⇒ Ordnung,
bis auf die Richtung.**  Nicht zu verwechseln mit `ErzeugteKetteProbe.ordnung_aus_fasern` (eine Ordnung aus den Fasern des Wechsels am Turm,
mit einem Rest an der Wurzel);  die Namensnähe ist gewollt (dieselbe Gestalt:  Ordnung aus einer anderen Struktur, mit genau einem Rest),
die Gegenstände sind verschieden.

## QUELLE, am Bild (Hermeneutes)

- IGN S. 17/18:  *„nur die Umtauschverhältnisse zwischen P und N₁ und das zwischen N₁ und N₂ sind … unmittelbar; das zwischen P und N₂ ist
  durch die andern beiden vermittelt, weil wir P und N als richtungsorientierte Ordinalzahlen behandeln. P ist weder unmittelbarer Vorgänger
  noch unmittelbarer Nachfolger von N₂."*  (Hermeneutes U1, 26.9.;  erneut 25.10. H-3)
- IGN S. 19/20:  *„… dass diese Vertauschbarkeit von N₁ und N₂ nur innerhalb der heterarchischen Ordnung zulässig ist. Im Hierarchischen ist
  das Verhältnis der beiden Negationen irreversibel."*  (Hermeneutes 25.10. H-4;  Seitenwechsel nach „von N₁ und")
- IGN S. 25/26:  *„… dass die Zählweise der Negationen als erste, zweite, dritte usw. als Rangordnung nur in einer hierarchischen Struktur der
  Logik Sinn und Gültigkeit hat. Im heterarchischen Bereich ist es anders, weshalb wir auch berechtigt waren, die Permutationen unseres
  Hamiltonkreises einmal mit der einen und dann mit der anderen Negation anzufangen."*  (Hermeneutes 25.10. F5)

## ZUORDNUNG

„Unmittelbares Umtauschverhältnis" = Nachbarschaft = (A) (`nachbar_iff`);  „richtungsorientiert" = die Richtung, die (A) offen lässt
(`ordnung_aus_umtausch`).  Quellenlesung S. 17/18 wie oben (Hermeneutes am Bild).

## LESART / ZUSAMMENSCHAU (S. 17/18 + S. 19 f. + S. 25/26, ein Text)

Die Tausche legen die Ordnung bis auf genau eine Umkehr fest.  Wer die Richtung wählt (Rangordnung erste/zweite, hierarchisch), hat N1 und N2
festgelegt;  ohne Richtung bleibt die Umkehr frei — sie vertauscht `N_i ↔ N_{m−i}`, bei drei Werten N1 ↔ N2:  Günthers „Vertauschbarkeit".
Das ist unsere Verbindung der drei Stellen, nicht Günthers Satz.

## LITERATUR

Aut(Weg 1 — … — m) = {id, Umkehr}:  **hier bewiesen** (`ordnung_aus_umtausch_zwei` mit `nachbar_iff`);  elementar, braucht keine
Literatur.  Die Gleichsetzung mit dem Diagrammautomorphismus von A_{m−1}, realisiert durch das längste Element w₀ = `Fin.rev`
(w₀ s_i w₀ = s_{m−i}), ist die eigentliche ZUORDNUNG zur Literatur — **ungeprüft (keine Stelle nachgesehen)**.
Vermerk:  bis 25.10. mittags stand hier „Lehrbuchstand. ZUORDNUNG zur Literatur." ohne Angabe (Custos PL33, Liste PL27 Z1).

## MARKE

EICHUNG von IGN S. 17/18, S. 19 f., S. 25/26 — der Bau rechnet nach, was Günther sagt;  nicht unerwartet.

## GESCHICHTE

Aus der Runde vom 25.10.:  Horistes' Einwand „Bindung durch Kleinheit" gegen die Stabilisator-Fassung ({id, Fin.rev} als Stabilisator von
{N1, N2}).  Diese Fassung quantifiziert über ALLE Permutationen und lebt nicht von der Grösse.

## NICHT

- Kein Träger für §20, nicht A20-4:  Werte und Negatoren wechseln die Sorte nicht;  kein Relator wird Relatum (Speculum SZ2).
- Keine Verbindung zum Turm.
- Negationskreise als Wörter über Negatoren sind nicht der Wechsel von Relator und Relatum, sondern die Figur [T8] (Instanz, Notiz §5).
- Kein Text in Rev11.

**Verbotene Kurzformen** (Horistes §2, Speculum SZ4):  „A20-4 an den Negatoren";  „der Umtausch löst die Umkehr aus" / „impliziert";
„Fin.rev ist Günthers symmetrischer Umtausch" (statt:  „die Wertumkehr, ein Umtausch der Werte 1 und m+1 im Sinn von IGN S. 19");
„Günthers Vertauschbarkeit bewiesen" (statt:  nachgerechnet).

## Bauweise

Kein `Equiv.swap`, kein `negPerm`, keine Aussage über einen Abschluss (`NegationCycleGenerators` K2:  `Equiv.swap` trägt Choice).  Der Beweis
von „⇒" folgt dem Hinweis des Mathematikers:  aus der Nachbarschaft |σ(i+1) − σ(i)| = 1 an jeder Stelle;  ein Vorzeichenwechsel gäbe
σ(i+2) = σ(i), gegen die Injektivität;  also σ(i) = σ(0) ± i, und die Werte liegen in [0, m].  Die Eichungen rechnen in der Tupelform der
Kratzdatei (σ als Wertetupel, (A) und (B) als Bool), nicht über `Equiv.Perm`.

Kein `sorry`, kein `Classical.choice`, kein `native_decide`, kein True-Feld.
-/

namespace Reformulation.Proemial.OrdnungAusUmtauschProbe

open Reformulation.Proemial.NegationCycle

variable {m : ℕ}

/-- **(A):**  σ führt das Negatorensystem durch Konjugation in sich über -/
def erhaeltNegatoren (σ : Equiv.Perm (Fin (m + 1))) : Prop :=
  ∀ i : Fin m, ∃ j : Fin m, ∀ v, σ (sw i v) = sw j (σ v)

/-- zwei Werte sind benachbart:  sie unterscheiden sich um eins -/
def benachbart (a b : Fin (m + 1)) : Prop := a.val + 1 = b.val ∨ b.val + 1 = a.val

/-! ## Die Negatoren an ihrem Paar -/

theorem sw_castSucc (i : Fin m) : sw i i.castSucc = i.succ := by
  apply Fin.ext
  rw [sw_val, Fin.val_castSucc, if_pos rfl, Fin.val_succ]

theorem sw_succ (i : Fin m) : sw i i.succ = i.castSucc := by
  apply Fin.ext
  rw [sw_val, Fin.val_succ, if_neg (Nat.succ_ne_self _), if_pos rfl, Fin.val_castSucc]

/-- ein Negator bewegt einen Wert nur auf einen Nachbarn -/
theorem sw_bewegt (j : Fin m) (x : Fin (m + 1)) (h : sw j x ≠ x) : benachbart x (sw j x) := by
  have hv := sw_val j x
  split at hv
  · left; omega
  · split at hv
    · right; omega
    · exact absurd (Fin.ext hv) h

/-- ein Negator am Paar (a, b) mit a = j, b = j + 1:  er tauscht a und b und lässt alles andere -/
theorem sw_paar (j : Fin m) (a b : Fin (m + 1)) (ha : a.val = j.val) (hb : b.val = j.val + 1) :
    sw j a = b ∧ sw j b = a ∧ ∀ y, y ≠ a → y ≠ b → sw j y = y := by
  refine ⟨Fin.ext ?_, Fin.ext ?_, fun y hya hyb => Fin.ext ?_⟩
  · rw [sw_val, if_pos ha]; omega
  · rw [sw_val, if_neg (by omega), if_pos hb]; omega
  · rw [sw_val, if_neg (fun e => hya (Fin.ext (e.trans ha.symm))), if_neg (fun e => hyb (Fin.ext (e.trans hb.symm)))]

/-! ## T1 · (A) heisst:  σ erhält die Nachbarschaft -/

/-- **(A) ist die Erhaltung der Nachbarschaft.** -/
theorem nachbar_iff (σ : Equiv.Perm (Fin (m + 1))) :
    erhaeltNegatoren σ ↔ ∀ i : Fin m, benachbart (σ i.castSucc) (σ i.succ) := by
  constructor
  · intro h i
    obtain ⟨j, hj⟩ := h i
    have e : σ i.succ = sw j (σ i.castSucc) := by rw [← hj, sw_castSucc]
    have hne : sw j (σ i.castSucc) ≠ σ i.castSucc := fun h' => by
      rw [← e] at h'
      exact (Fin.castSucc_lt_succ (i := i)).ne' (σ.injective h')
    rw [e]; exact sw_bewegt j _ hne
  · intro h i
    have hab := h i
    -- der Negator am Bildpaar, mit den Paar-Eigenschaften (symmetrisch in den beiden Bildern)
    have key : ∃ j : Fin m, sw j (σ i.castSucc) = σ i.succ ∧ sw j (σ i.succ) = σ i.castSucc ∧
        ∀ y, y ≠ σ i.castSucc → y ≠ σ i.succ → sw j y = y := by
      rcases hab with e | e
      · refine ⟨⟨(σ i.castSucc).val, by have := (σ i.succ).isLt; omega⟩, ?_⟩
        exact sw_paar _ _ _ rfl e.symm
      · refine ⟨⟨(σ i.succ).val, by have := (σ i.castSucc).isLt; omega⟩, ?_⟩
        obtain ⟨p1, p2, p3⟩ := sw_paar ⟨(σ i.succ).val, by have := (σ i.castSucc).isLt; omega⟩ (σ i.succ) (σ i.castSucc)
          rfl e.symm
        exact ⟨p2, p1, fun y h1 h2 => p3 y h2 h1⟩
    obtain ⟨j, hj1, hj2, hj3⟩ := key
    refine ⟨j, fun v => ?_⟩
    by_cases hv1 : v = i.castSucc
    · rw [hv1, sw_castSucc, hj1]
    · by_cases hv2 : v = i.succ
      · rw [hv2, sw_succ, hj2]
      · have hfix : sw i v = v := by
          obtain ⟨-, -, q⟩ := sw_paar i i.castSucc i.succ (Fin.val_castSucc i) (Fin.val_succ i)
          exact q v hv1 hv2
        rw [hfix]
        exact (hj3 (σ v) (fun e => hv1 (σ.injective e)) (fun e => hv2 (σ.injective e))).symm

/-! ## Die Richtung -/

/-- die Werte von σ als Zahlenfolge -/
def gv (σ : Equiv.Perm (Fin (m + 1))) (k : ℕ) : ℕ := if h : k < m + 1 then (σ ⟨k, h⟩).val else 0

theorem gv_eq (σ : Equiv.Perm (Fin (m + 1))) (v : Fin (m + 1)) : gv σ v.val = (σ v).val := by
  unfold gv; rw [dif_pos v.isLt]

theorem gv_lt (σ : Equiv.Perm (Fin (m + 1))) {k : ℕ} (hk : k < m + 1) : gv σ k < m + 1 := by
  unfold gv; rw [dif_pos hk]; exact (σ _).isLt

theorem gv_inj (σ : Equiv.Perm (Fin (m + 1))) {k l : ℕ} (hk : k < m + 1) (hl : l < m + 1) (h : gv σ k = gv σ l) : k = l := by
  unfold gv at h; rw [dif_pos hk, dif_pos hl] at h
  exact Fin.mk.inj (σ.injective (Fin.ext h))

theorem gv_nachbar (σ : Equiv.Perm (Fin (m + 1))) (h : erhaeltNegatoren σ) :
    ∀ k, k < m → gv σ (k + 1) = gv σ k + 1 ∨ gv σ k = gv σ (k + 1) + 1 := by
  intro k hk
  have e1 : gv σ k = (σ (⟨k, hk⟩ : Fin m).castSucc).val := gv_eq σ (⟨k, hk⟩ : Fin m).castSucc
  have e2 : gv σ (k + 1) = (σ (⟨k, hk⟩ : Fin m).succ).val := gv_eq σ (⟨k, hk⟩ : Fin m).succ
  rcases (nachbar_iff σ).mp h ⟨k, hk⟩ with e | e
  · left; rw [e1, e2]; exact e.symm
  · right; rw [e1, e2]; exact e.symm

/-- **Kein Vorzeichenwechsel:**  bis zu jeder Stelle steigt σ um je eins oder fällt um je eins -/
theorem richtung (σ : Equiv.Perm (Fin (m + 1)))
    (hn : ∀ k, k < m → gv σ (k + 1) = gv σ k + 1 ∨ gv σ k = gv σ (k + 1) + 1) :
    ∀ k, k ≤ m → (∀ t, t ≤ k → gv σ t = gv σ 0 + t) ∨ (∀ t, t ≤ k → gv σ t + t = gv σ 0) := by
  intro k
  induction k with
  | zero =>
    intro _
    left; intro t ht
    have : t = 0 := by omega
    subst this; rfl
  | succ k ih =>
    intro hk
    rcases ih (by omega) with H | H
    · rcases hn k (by omega) with e | e
      · left; intro t ht
        rcases Nat.lt_or_ge t (k + 1) with h | h
        · exact H t (by omega)
        · have ht' : t = k + 1 := by omega
          subst ht'
          have hk' := H k (le_refl k)
          omega
      · cases k with
        | zero =>
          right; intro t ht
          rcases Nat.lt_or_ge t 1 with h | h
          · have : t = 0 := by omega
            subst this; rfl
          · have : t = 1 := by omega
            subst this
            show gv σ (0 + 1) + 1 = gv σ 0
            omega
        | succ k' =>
          exfalso
          have h1 := H (k' + 1) (le_refl _)
          have h0 := H k' (by omega)
          have heq : gv σ (k' + 1 + 1) = gv σ k' := by omega
          have := gv_inj σ (by omega) (by omega) heq
          omega
    · rcases hn k (by omega) with e | e
      · cases k with
        | zero =>
          left; intro t ht
          rcases Nat.lt_or_ge t 1 with h | h
          · have : t = 0 := by omega
            subst this; rfl
          · have : t = 1 := by omega
            subst this
            show gv σ (0 + 1) = gv σ 0 + 1
            omega
        | succ k' =>
          exfalso
          have h1 := H (k' + 1) (le_refl _)
          have h0 := H k' (by omega)
          have heq : gv σ (k' + 1 + 1) = gv σ k' := by omega
          have := gv_inj σ (by omega) (by omega) heq
          omega
      · right; intro t ht
        rcases Nat.lt_or_ge t (k + 1) with h | h
        · exact H t (by omega)
        · have ht' : t = k + 1 := by omega
          subst ht'
          have hk' := H k (le_refl k)
          omega

/-- **Fest oder Umkehr:**  wer die Negatoren erhält, ist die Identität oder die Wertumkehr -/
theorem fest_oder_umkehr (σ : Equiv.Perm (Fin (m + 1))) (h : erhaeltNegatoren σ) :
    (∀ v, σ v = v) ∨ (∀ v, σ v = Fin.rev v) := by
  have hm := gv_lt σ (k := m) (Nat.lt_succ_self m)
  have h0 := gv_lt σ (k := 0) (Nat.succ_pos m)
  rcases richtung σ (gv_nachbar σ h) m (le_refl m) with H | H
  · left; intro v
    have hmv := H m (le_refl m)
    have hv := H v.val (Nat.lt_succ_iff.mp v.isLt)
    rw [gv_eq] at hv
    apply Fin.ext
    omega
  · right; intro v
    have hmv := H m (le_refl m)
    have hv := H v.val (Nat.lt_succ_iff.mp v.isLt)
    rw [gv_eq] at hv
    apply Fin.ext
    rw [Fin.val_rev]
    omega

/-! ## T3 · genau die Identität und die Wertumkehr -/

theorem erhaelt_eins : erhaeltNegatoren (1 : Equiv.Perm (Fin (m + 1))) := fun i => ⟨i, fun _ => rfl⟩

theorem erhaelt_umkehr : erhaeltNegatoren (Fin.revPerm : Equiv.Perm (Fin (m + 1))) := fun i =>
  ⟨Fin.rev i, fun v => by
    have h := sw_rev_conj i (Fin.rev v)
    rw [Fin.rev_rev] at h
    exact h⟩

/-- **Die Nachbartausche bestimmen die Ordnung bis auf eine Umkehr:**  genau die Identität und die Wertumkehr erhalten die Negatoren. -/
theorem ordnung_aus_umtausch_zwei (σ : Equiv.Perm (Fin (m + 1))) :
    erhaeltNegatoren σ ↔ σ = 1 ∨ σ = Fin.revPerm := by
  constructor
  · intro h
    rcases fest_oder_umkehr σ h with H | H
    · exact Or.inl (Equiv.ext H)
    · exact Or.inr (Equiv.ext H)
  · rintro (rfl | rfl)
    · exact erhaelt_eins
    · exact erhaelt_umkehr

/-! ## T2 · ordnungstreu oder ordnungsumkehrend -/

theorem mono_ge (f : Fin (m + 1) → Fin (m + 1)) (hf : StrictMono f) : ∀ k (hk : k < m + 1), k ≤ (f ⟨k, hk⟩).val
  | 0, _ => Nat.zero_le _
  | k + 1, hk => by
    have ih := mono_ge f hf k (by omega)
    have hlt : f ⟨k, by omega⟩ < f ⟨k + 1, hk⟩ := hf (show (⟨k, by omega⟩ : Fin (m + 1)) < ⟨k + 1, hk⟩ from Nat.lt_succ_self k)
    exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt ih hlt)

theorem mono_fest (σ : Equiv.Perm (Fin (m + 1))) (hσ : StrictMono σ) : ∀ v, σ v = v := by
  have hs : StrictMono σ.symm := fun a b hab => by
    rcases Nat.lt_or_ge (σ.symm a).val (σ.symm b).val with h | h
    · exact h
    · exfalso
      rcases Nat.eq_or_lt_of_le h with e | e
      · have : a = b := by
          have := congrArg σ (Fin.ext e.symm : σ.symm a = σ.symm b)
          rwa [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
        exact absurd hab (this ▸ lt_irrefl a)
      · have := hσ (show σ.symm b < σ.symm a from e)
        rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
        exact absurd (lt_trans hab this) (lt_irrefl a)
  intro v
  have h1 := mono_ge σ hσ v.val v.isLt
  have h2 := mono_ge σ.symm hs (σ v).val (σ v).isLt
  have e1 : (⟨v.val, v.isLt⟩ : Fin (m + 1)) = v := rfl
  have e2 : (⟨(σ v).val, (σ v).isLt⟩ : Fin (m + 1)) = σ v := rfl
  rw [e1] at h1; rw [e2, Equiv.symm_apply_apply] at h2
  exact Fin.ext (by omega)

/-- **(A) ⟺ (B):**  σ erhält die Negatoren genau dann, wenn σ die Ordnung der Werte erhält oder umkehrt. -/
theorem ordnung_aus_umtausch (σ : Equiv.Perm (Fin (m + 1))) :
    erhaeltNegatoren σ ↔ StrictMono σ ∨ StrictAnti σ := by
  rw [ordnung_aus_umtausch_zwei]
  constructor
  · rintro (rfl | rfl)
    · exact Or.inl fun _ _ h => h
    · exact Or.inr Fin.rev_strictAnti
  · rintro (h | h)
    · exact Or.inl (Equiv.ext (mono_fest σ h))
    · right
      have hm : StrictMono (Fin.revPerm.trans σ) := fun a b hab => h (Fin.rev_strictAnti hab)
      have hfest := mono_fest _ hm
      exact Equiv.ext fun v => by
        have := hfest (Fin.rev v)
        simp only [Equiv.trans_apply] at this
        rw [show (Fin.revPerm : Equiv.Perm (Fin (m + 1))) (Fin.rev v) = v from Fin.rev_rev v] at this
        rw [this]; rfl

/-- **Genau zwei, ab zwei Werten:**  Identität und Wertumkehr fallen genau bei einem Wert (m = 0) zusammen. -/
theorem genau_zwei : (1 : Equiv.Perm (Fin (m + 1))) = Fin.revPerm ↔ m = 0 := by
  constructor
  · intro h
    have := congrArg (fun σ : Equiv.Perm (Fin (m + 1)) => (σ 0).val) h
    simp only [Equiv.Perm.one_apply] at this
    rw [show (Fin.revPerm : Equiv.Perm (Fin (m + 1))) 0 = Fin.rev 0 from rfl, Fin.val_rev, Fin.val_zero] at this
    omega
  · rintro rfl
    exact Equiv.ext fun v => Fin.ext (by
      show v.val = (Fin.rev v).val
      rw [Fin.val_rev]; have := v.isLt; omega)

/-! ## Eichungen und Gegenproben (Tupelform der Kratzdatei) -/

def sig3 (a b c : Fin 3) : Fin 3 → Fin 3 | ⟨0, _⟩ => a | ⟨1, _⟩ => b | ⟨2, _⟩ => c
def sig4 (a b c d : Fin 4) : Fin 4 → Fin 4 | ⟨0, _⟩ => a | ⟨1, _⟩ => b | ⟨2, _⟩ => c | ⟨3, _⟩ => d
def sig5 (a b c d e : Fin 5) : Fin 5 → Fin 5 | ⟨0, _⟩ => a | ⟨1, _⟩ => b | ⟨2, _⟩ => c | ⟨3, _⟩ => d | ⟨4, _⟩ => e

def inj3 (a b c : Fin 3) : Bool := a != b && a != c && b != c
def inj4 (a b c d : Fin 4) : Bool := a != b && a != c && a != d && b != c && b != d && c != d
def inj5 (a b c d e : Fin 5) : Bool :=
  a != b && a != c && a != d && a != e && b != c && b != d && b != e && c != d && c != e && d != e

/-- (A) in Tupelform -/
def negSys3 (σ : Fin 3 → Fin 3) : Bool := [0, 1].all fun (i : Fin 2) => [0, 1].any fun (j : Fin 2) =>
  [0, 1, 2].all fun (v : Fin 3) => σ (sw i v) == sw j (σ v)
def negSys4 (σ : Fin 4 → Fin 4) : Bool := [0, 1, 2].all fun (i : Fin 3) => [0, 1, 2].any fun (j : Fin 3) =>
  [0, 1, 2, 3].all fun (v : Fin 4) => σ (sw i v) == sw j (σ v)
def negSys5 (σ : Fin 5 → Fin 5) : Bool := [0, 1, 2, 3].all fun (i : Fin 4) => [0, 1, 2, 3].any fun (j : Fin 4) =>
  [0, 1, 2, 3, 4].all fun (v : Fin 5) => σ (sw i v) == sw j (σ v)

/-- (B) in Tupelform:  steigend oder fallend -/
def mono3 (a b c : Fin 3) : Bool := (a < b && b < c) || (a > b && b > c)
def mono4 (a b c d : Fin 4) : Bool := (a < b && b < c && c < d) || (a > b && b > c && c > d)
def mono5 (a b c d e : Fin 5) : Bool := (a < b && b < c && c < d && d < e) || (a > b && b > c && c > d && d > e)

/-- **Eichung, drei Werte:**  über allen sechs Permutationen (A) ↔ (B);  genau zwei erfüllen sie. -/
theorem eich_drei :
    (∀ a b c : Fin 3, inj3 a b c = true → negSys3 (sig3 a b c) = mono3 a b c) ∧
    (∀ a b c : Fin 3, (inj3 a b c && negSys3 (sig3 a b c)) = true ↔ ((a = 0 ∧ b = 1 ∧ c = 2) ∨ (a = 2 ∧ b = 1 ∧ c = 0))) := by
  decide

/-- **Eichung, vier Werte:**  über allen 24 Permutationen;  genau zwei. -/
theorem eich_vier :
    (∀ a b c d : Fin 4, inj4 a b c d = true → negSys4 (sig4 a b c d) = mono4 a b c d) ∧
    (∀ a b c d : Fin 4, (inj4 a b c d && negSys4 (sig4 a b c d)) = true ↔
      ((a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 3) ∨ (a = 3 ∧ b = 2 ∧ c = 1 ∧ d = 0))) := by
  decide +kernel

/-- **Eichung, fünf Werte:**  über allen 120 Permutationen (A) ↔ (B). -/
theorem eich_fuenf : ∀ a b c d e : Fin 5, inj5 a b c d e = true → negSys5 (sig5 a b c d e) = mono5 a b c d e := by
  decide +kernel

/-- **Gegenprobe:**  „σ hält den Wert 1 (Lean 0) fest" ist mit (A) NICHT äquivalent — drei und fünf Werte. -/
theorem gegen_fest_null :
    (∃ a b c : Fin 3, inj3 a b c = true ∧ negSys3 (sig3 a b c) ≠ (a == 0)) ∧
    (∃ a b c d e : Fin 5, inj5 a b c d e = true ∧ negSys5 (sig5 a b c d e) ≠ (a == 0)) :=
  ⟨⟨0, 2, 1, by decide, by decide⟩, ⟨0, 2, 1, 3, 4, by decide, by decide⟩⟩

/-- **Gegenproben:**  die Drehung v ↦ v + 1 (drei Werte), (1 2)(4 5) (fünf Werte) und der Tausch von 1 und 3 (vier Werte, er vertauscht
    N1 und N2) erfüllen (A) nicht. -/
theorem gegen_beispiele :
    negSys3 (sig3 1 2 0) = false ∧ negSys5 (sig5 1 0 2 4 3) = false ∧ negSys4 (sig4 2 1 0 3) = false := by
  decide

end Reformulation.Proemial.OrdnungAusUmtauschProbe

/-! ## Axiom-Wachen (gemessen, verbatim) -/

/-- info: 'Reformulation.Proemial.OrdnungAusUmtauschProbe.sw_castSucc' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Proemial.OrdnungAusUmtauschProbe.sw_castSucc

/-- info: 'Reformulation.Proemial.OrdnungAusUmtauschProbe.sw_succ' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Proemial.OrdnungAusUmtauschProbe.sw_succ

/-- info: 'Reformulation.Proemial.OrdnungAusUmtauschProbe.sw_bewegt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.OrdnungAusUmtauschProbe.sw_bewegt

/-- info: 'Reformulation.Proemial.OrdnungAusUmtauschProbe.sw_paar' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.OrdnungAusUmtauschProbe.sw_paar

/-- info: 'Reformulation.Proemial.OrdnungAusUmtauschProbe.nachbar_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.OrdnungAusUmtauschProbe.nachbar_iff

/-- info: 'Reformulation.Proemial.OrdnungAusUmtauschProbe.gv_eq' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.OrdnungAusUmtauschProbe.gv_eq

/-- info: 'Reformulation.Proemial.OrdnungAusUmtauschProbe.gv_lt' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.OrdnungAusUmtauschProbe.gv_lt

/-- info: 'Reformulation.Proemial.OrdnungAusUmtauschProbe.gv_inj' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.OrdnungAusUmtauschProbe.gv_inj

/-- info: 'Reformulation.Proemial.OrdnungAusUmtauschProbe.gv_nachbar' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.OrdnungAusUmtauschProbe.gv_nachbar

/-- info: 'Reformulation.Proemial.OrdnungAusUmtauschProbe.richtung' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.OrdnungAusUmtauschProbe.richtung

/-- info: 'Reformulation.Proemial.OrdnungAusUmtauschProbe.fest_oder_umkehr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.OrdnungAusUmtauschProbe.fest_oder_umkehr

/-- info: 'Reformulation.Proemial.OrdnungAusUmtauschProbe.erhaelt_eins' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.OrdnungAusUmtauschProbe.erhaelt_eins

/-- info: 'Reformulation.Proemial.OrdnungAusUmtauschProbe.erhaelt_umkehr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.OrdnungAusUmtauschProbe.erhaelt_umkehr

/-- info: 'Reformulation.Proemial.OrdnungAusUmtauschProbe.ordnung_aus_umtausch_zwei' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.OrdnungAusUmtauschProbe.ordnung_aus_umtausch_zwei

/-- info: 'Reformulation.Proemial.OrdnungAusUmtauschProbe.mono_ge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.OrdnungAusUmtauschProbe.mono_ge

/-- info: 'Reformulation.Proemial.OrdnungAusUmtauschProbe.mono_fest' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.OrdnungAusUmtauschProbe.mono_fest

/-- info: 'Reformulation.Proemial.OrdnungAusUmtauschProbe.ordnung_aus_umtausch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.OrdnungAusUmtauschProbe.ordnung_aus_umtausch

/-- info: 'Reformulation.Proemial.OrdnungAusUmtauschProbe.genau_zwei' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.OrdnungAusUmtauschProbe.genau_zwei

/-- info: 'Reformulation.Proemial.OrdnungAusUmtauschProbe.eich_drei' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.OrdnungAusUmtauschProbe.eich_drei

/-- info: 'Reformulation.Proemial.OrdnungAusUmtauschProbe.eich_vier' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.OrdnungAusUmtauschProbe.eich_vier

/-- info: 'Reformulation.Proemial.OrdnungAusUmtauschProbe.eich_fuenf' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.OrdnungAusUmtauschProbe.eich_fuenf

/-- info: 'Reformulation.Proemial.OrdnungAusUmtauschProbe.gegen_fest_null' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.OrdnungAusUmtauschProbe.gegen_fest_null

/-- info: 'Reformulation.Proemial.OrdnungAusUmtauschProbe.gegen_beispiele' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.OrdnungAusUmtauschProbe.gegen_beispiele
