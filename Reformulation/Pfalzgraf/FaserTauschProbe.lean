import Reformulation.Pfalzgraf.Faserung   -- Faser, Wert, global, fneg₁, fneg₂, qneg₁, qneg₂, designiert, vec

/-!
# Pfalzgraf.FaserTauschProbe — die Fasertausche der Faserung:  an die Negation gekoppelt, die Ordnung in der Designation

STANDALONE, NICHT im Aggregat;  Target `Probes`.  AxiomGate unberührt.  Sonde nach `KorpusRev2/Prompt_Instanz_FaserTausch_Sonde.md`
(Mathematiker, 26.10.2026 15:20;  Architekt 15:19 „Ja, ich will den Bau der Fasertausche").  Herkunft:  die Landkarte
(`KorpusRev2/Meldung_Rev11_C1_Landkarte_Impl.md` §8, Lesefassung `Landkarte_Rev11_C1_Instanz.md` Anhang B — dort als `#eval`), die Abnahme
C1 (B1, B2;  Python-Nachrechnung des Mathematikers), Anspruchsliste Rev11 E5/E6.  Diese Sonde macht die Messung zum Satz.  Konsumiert
`Pfalzgraf/Faserung` (`Faser`, `Wert`, `global`, `fneg₁`, `fneg₂`, `qneg₁`, `qneg₂`, `designiert`, `vec`);  ändert nichts davon.  Keine Deutung.

## Zählung

Faser 0, 1, 2 = Günthers Teilsysteme 1-2, 2-3, 1-3;  Wert 0, 1, 2 = Günthers 1, 2, 3 (wie im Kopf von `Faserung`).

## WAS

```text
tauschKohaerent π σ fl   :⟺  ∀ i b,  global (π i) (xor b (fl i)) = σ (global i b)  — π, σ, fl BELIEBIGE Funktionen
ft1          FOLGERUNG (m = 3)   ein kohärenter Fasertausch (über allen σ, fl) existiert genau für bijektives π (inj3 π)
ft2          FOLGERUNG (m = 3)   für bijektives π ist (σ, fl) eindeutig — über ALLEN σ : Wert → Wert —, und σ ist von selbst bijektiv
ft3          EICHUNG (decide)    die Tafel:  (1 2) ↔ qneg₁ (Günthers 1↔2), Negation nur in Faser 0;  (0 2) ↔ qneg₂ (2↔3), nur in Faser 1;
                                 (0 1) ↔ w13 (1↔3), in allen drei Fasern;  dazu die zwei Dreierzyklen und die Identität
ft4          FOLGERUNG (m = 3)   ohne Negation (fl ≡ false) scheitert jeder Fasertausch ausser der Identität, für jedes σ
ft5          FOLGERUNG (dünn)    die Bestandsnegatoren SIND zwei der Fasertausche:  fneg₁ = vekTausch (1 2) [Negation in Faser 0],
                                 fneg₂ = vekTausch (0 2) [Negation in Faser 1]
ft6          FOLGERUNG           der vermittelte Tausch (0 1) ist durch die beiden unmittelbaren vermittelt:  vekTausch (0 1) [alle drei]
                                 = fneg₁ ∘ fneg₂ ∘ fneg₁ = fneg₂ ∘ fneg₁ ∘ fneg₂;  im Quotienten qneg₁ ∘ qneg₂ ∘ qneg₁ = w13 = qneg₂ ∘ qneg₁ ∘ qneg₂
ft7          FOLGERUNG (m = 3)   jede echte, nichtleere Designation D ⊂ Wert wird von GENAU EINER der drei Werttranspositionen erhalten
ft7_tafel    EICHUNG (decide)    {1} → qneg₂, {2} → w13, {3} → qneg₁, {1,2} → qneg₁, {1,3} → w13, {2,3} → qneg₂ (Günthers Zählung);
                                 E6:  `designiert` (= {1,2}) wird von qneg₁ erhalten, von qneg₂ nicht
gegen_*      EICHUNG             Muss-Fälle:  „genau zwei Lösungen" (an (1 2)), vertauschter Flip (Faser 1 statt 0), zwei Faktoren statt
                                 drei, „qneg₂ erhält {1,2}" — alle fallen
```

Hilfssätze:  `f3_eta`, `tk_punkt` (die Kohärenz hängt nur an den Werten von π, σ, fl — der Übergang von den konkreten Aussagen über
`f3 a b c` zu beliebigen Funktionen), `vec_eta` (jeder Faservektor ist `vec` seiner drei Werte).  Definitionen:  `tauschKohaerent`, `f3`,
`inj3`, `pi12`, `pi02`, `pi01`, `w13`, `vekTausch`, `erhaelt`, `transp`.

**Bauweise.**  Keine `Equiv`, kein `Fintype` über Funktionen (Fallstrick 10):  die Quantoren laufen über die Werte `f3 a b c` (nackte
Quantoren über `Fin 3` und `Bool`), `decide` bzw. `decide +kernel`;  `tk_punkt` hebt auf beliebige Funktionen.  `vekTausch π fl x j :=
xor (x (π j)) (fl (π j))` ist der Transport eines Faservektors für INVOLUTIVES π (π⁻¹ = π);  so kommt die Fassung ohne Inverse aus — für
die drei Transpositionen genügt das.  Profile:  `[propext]` oder `[propext, Quot.sound]`;  kein `Classical.choice`, kein `native_decide`,
kein `sorry`, kein True-Feld.

## Kleinheit — ausdrücklich

Die Eindeutigkeit (ft2) ist durch die Gestalt ERZWUNGEN (Regel 11):  die Fasern SIND die zweielementigen Wertmengen, und bei drei Werten
ist C(3, 2) = 3 — jede Wertpermutation induziert genau eine Permutation der drei Paare und umgekehrt.  Bei vier Werten (6 Fasern,
720 Fasertausche) ist das UNGEMESSEN.  Die Faserung des Bestands ist konkret m = 3.

## ZUORDNUNG

- **ft6 als Satzgestalt von IGN S. 17 f.:**  *„das zwischen P und N₂ ist durch die andern beiden vermittelt"* — am Bild,
  `KorpusRev2/Hermeneutes_IGN_S17_20_Vertauschbarkeit.md`.  Das ist **V2**, Günthers „vermittelt" (unmittelbar / mittelbar), **nicht V3**
  (Fasern/Quotient).  ZUORDNUNG mit Quelle.
- **ungeprüft, nur hier:**  Fasertausch ↔ Tausch zweier Zentren (C&V S. 20);  Pfalzgrafs freie Negatoren nach S. 176/177 (Herkunft im
  Kopf von `Faserung`).

## Generizität und Designation

Der Befund ist **Bool-generisch** — die Fasern sind klassisch zweiwertig;  nichts darin ist kenogrammatisch.  `designiert` ist UNSER
(`Faserung` Z. 268);  ft7 zeigt:  JEDE echte, nichtleere Designation zeichnet genau einen Tausch aus.  Die Ordnung kommt mit der Setzung,
nicht aus dem Tausch;  der Tausch selbst ist symmetrisch (Involution, ft5/ft6).

## NICHT

Kein Träger für §20;  kein „A20-4";  kein Papiertext.  **Verboten:**  „die Faserung trägt S. 20";  „Fasertausch = Tausch zweier
Zentren" (ZUORDNUNG, ungeprüft);  „die Negation erzwingt die Ordnung" (die Ordnung sitzt in der Designation, ft7);  „bei m Werten"
(gebaut ist m = 3).
-/

namespace Reformulation.Pfalzgraf.FaserTauschProbe

open Reformulation.Pfalzgraf

/-- **die Kohärenz eines Fasertauschs:**  π schickt Faser i auf π i, fl verneint dabei in Faser i, σ ist die Wirkung auf die Werte —
    der lokale Wert b der Faser i und sein Bild in Faser π i bezeichnen zueinander passende globale Werte -/
abbrev tauschKohaerent (π σ : Fin 3 → Fin 3) (fl : Fin 3 → Bool) : Prop :=
  ∀ i : Faser, ∀ b : Bool, global (π i) (xor b (fl i)) = σ (global i b)

/-- die Funktion aus drei Werten -/
abbrev f3 {α : Type} (a b c : α) : Fin 3 → α := ![a, b, c]

theorem f3_eta {α : Type} (f : Fin 3 → α) : ∀ v, f3 (f 0) (f 1) (f 2) v = f v
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl

/-- die Kohärenz hängt nur an den Werten von π, σ, fl -/
theorem tk_punkt (π σ : Fin 3 → Fin 3) (fl : Fin 3 → Bool) :
    tauschKohaerent π σ fl ↔ tauschKohaerent (f3 (π 0) (π 1) (π 2)) (f3 (σ 0) (σ 1) (σ 2)) (f3 (fl 0) (fl 1) (fl 2)) := by
  unfold tauschKohaerent
  simp only [f3_eta]

/-- π paarweise verschieden (auf Fin 3:  bijektiv) -/
abbrev inj3 (π : Fin 3 → Fin 3) : Prop := π 0 ≠ π 1 ∧ π 0 ≠ π 2 ∧ π 1 ≠ π 2

/-- **FT1:**  ein kohärenter Fasertausch existiert genau für die bijektiven π (über allen σ und fl) -/
theorem ft1_konkret : ∀ a b c : Fin 3,
    (∃ s0 s1 s2 : Fin 3, ∃ x y z : Bool, tauschKohaerent (f3 a b c) (f3 s0 s1 s2) (f3 x y z)) ↔ inj3 (f3 a b c) := by
  decide +kernel

theorem ft1 (π : Fin 3 → Fin 3) : (∃ σ fl, tauschKohaerent π σ fl) ↔ inj3 π := by
  constructor
  · rintro ⟨σ, fl, h⟩
    exact (ft1_konkret (π 0) (π 1) (π 2)).mp ⟨σ 0, σ 1, σ 2, fl 0, fl 1, fl 2, (tk_punkt π σ fl).mp h⟩
  · intro h
    obtain ⟨s0, s1, s2, x, y, z, hk⟩ := (ft1_konkret (π 0) (π 1) (π 2)).mpr h
    exact ⟨f3 s0 s1 s2, f3 x y z, (tk_punkt π _ _).mpr hk⟩

/-- **FT2, konkret:**  für jedes bijektive π genau ein (σ, fl) — und σ ist von selbst bijektiv -/
theorem ft2_konkret : ∀ a b c : Fin 3, inj3 (f3 a b c) →
    ∃ s0 s1 s2 : Fin 3, ∃ x y z : Bool, tauschKohaerent (f3 a b c) (f3 s0 s1 s2) (f3 x y z) ∧ inj3 (f3 s0 s1 s2) ∧
      ∀ s0' s1' s2' : Fin 3, ∀ x' y' z' : Bool, tauschKohaerent (f3 a b c) (f3 s0' s1' s2') (f3 x' y' z') →
        s0' = s0 ∧ s1' = s1 ∧ s2' = s2 ∧ x' = x ∧ y' = y ∧ z' = z := by
  decide +kernel

/-- **FT2:**  für bijektives π ist (σ, fl) eindeutig — über ALLEN σ : Wert → Wert und fl -/
theorem ft2 (π σ σ' : Fin 3 → Fin 3) (fl fl' : Fin 3 → Bool) (hπ : inj3 π)
    (h : tauschKohaerent π σ fl) (h' : tauschKohaerent π σ' fl') : (∀ v, σ v = σ' v) ∧ (∀ i, fl i = fl' i) ∧ inj3 σ := by
  obtain ⟨s0, s1, s2, x, y, z, -, hinj, huniq⟩ := ft2_konkret (π 0) (π 1) (π 2) hπ
  have e := huniq _ _ _ _ _ _ ((tk_punkt π σ fl).mp h)
  have e' := huniq _ _ _ _ _ _ ((tk_punkt π σ' fl').mp h')
  refine ⟨fun v => ?_, fun i => ?_, ?_⟩
  · rw [← f3_eta σ v, ← f3_eta σ' v, e.1, e.2.1, e.2.2.1, e'.1, e'.2.1, e'.2.2.1]
  · rw [← f3_eta fl i, ← f3_eta fl' i, e.2.2.2.1, e.2.2.2.2.1, e.2.2.2.2.2, e'.2.2.2.1, e'.2.2.2.2.1, e'.2.2.2.2.2]
  · show σ 0 ≠ σ 1 ∧ σ 0 ≠ σ 2 ∧ σ 1 ≠ σ 2
    rw [e.1, e.2.1, e.2.2.1]; exact hinj

/-- die drei Transpositionen der Fasern -/
abbrev pi12 : Fin 3 → Fin 3 := f3 0 2 1
abbrev pi02 : Fin 3 → Fin 3 := f3 2 1 0
abbrev pi01 : Fin 3 → Fin 3 := f3 1 0 2
/-- Günthers 1 ↔ 3 auf den Werten -/
def w13 (v : Wert) : Wert := if v = 0 then 2 else if v = 2 then 0 else 1

/-- **FT3, die Tafel:**  die drei Transpositionen und die zwei Dreierzyklen der Fasern, je mit ihrer Wertpermutation und ihrem Flip -/
theorem ft3 :
    tauschKohaerent pi12 qneg₁ (f3 true false false) ∧ tauschKohaerent pi02 qneg₂ (f3 false true false) ∧
    tauschKohaerent pi01 w13 (f3 true true true) ∧
    tauschKohaerent (f3 1 2 0) (f3 1 2 0) (f3 false true true) ∧ tauschKohaerent (f3 2 0 1) (f3 2 0 1) (f3 true false true) ∧
    tauschKohaerent (f3 0 1 2) (f3 0 1 2) (f3 false false false) := by
  decide

/-- **FT4, konkret:**  ohne Negation scheitert jeder Fasertausch ausser der Identität -/
theorem ft4_konkret : ∀ a b c : Fin 3, ¬ (a = 0 ∧ b = 1 ∧ c = 2) →
    ∀ s0 s1 s2 : Fin 3, ¬ tauschKohaerent (f3 a b c) (f3 s0 s1 s2) (f3 false false false) := by
  decide +kernel

theorem ft4 (π σ : Fin 3 → Fin 3) (hπ : ¬ (π 0 = 0 ∧ π 1 = 1 ∧ π 2 = 2)) : ¬ tauschKohaerent π σ (fun _ => false) := by
  intro h
  exact ft4_konkret (π 0) (π 1) (π 2) hπ (σ 0) (σ 1) (σ 2) ((tk_punkt π σ _).mp h)

/-- **der Tausch eines Faservektors** für eine involutive Faserpermutation π (π⁻¹ = π):  der Wert in Faser j kommt aus Faser π j,
    dort um fl verneint -/
def vekTausch (π : Fin 3 → Fin 3) (fl : Fin 3 → Bool) (x : Faser → Bool) : Faser → Bool := fun j => xor (x (π j)) (fl (π j))

theorem vec_eta (x : Faser → Bool) : vec (x 0) (x 1) (x 2) = x :=
  funext fun j => match j with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨2, _⟩ => rfl

theorem ft5_vec : ∀ b0 b1 b2 : Bool, ∀ j : Faser,
    fneg₁ (vec b0 b1 b2) j = vekTausch pi12 (f3 true false false) (vec b0 b1 b2) j ∧
    fneg₂ (vec b0 b1 b2) j = vekTausch pi02 (f3 false true false) (vec b0 b1 b2) j := by
  decide

/-- **FT5:**  die Bestandsnegatoren SIND zwei der Fasertausche -/
theorem ft5 (x : Faser → Bool) :
    fneg₁ x = vekTausch pi12 (f3 true false false) x ∧ fneg₂ x = vekTausch pi02 (f3 false true false) x := by
  rw [← vec_eta x]
  exact ⟨funext fun j => (ft5_vec _ _ _ j).1, funext fun j => (ft5_vec _ _ _ j).2⟩

theorem ft6_vec : ∀ b0 b1 b2 : Bool, ∀ j : Faser,
    vekTausch pi01 (f3 true true true) (vec b0 b1 b2) j = fneg₁ (fneg₂ (fneg₁ (vec b0 b1 b2))) j ∧
    vekTausch pi01 (f3 true true true) (vec b0 b1 b2) j = fneg₂ (fneg₁ (fneg₂ (vec b0 b1 b2))) j := by
  decide

/-- **FT6:**  der vermittelte Tausch (0 1) ist durch die beiden unmittelbaren vermittelt — frei und im Quotienten -/
theorem ft6 (x : Faser → Bool) :
    vekTausch pi01 (f3 true true true) x = fneg₁ (fneg₂ (fneg₁ x)) ∧
    vekTausch pi01 (f3 true true true) x = fneg₂ (fneg₁ (fneg₂ x)) ∧
    (∀ v, qneg₁ (qneg₂ (qneg₁ v)) = w13 v) ∧ (∀ v, qneg₂ (qneg₁ (qneg₂ v)) = w13 v) := by
  refine ⟨?_, ?_, by decide, by decide⟩
  · rw [← vec_eta x]; exact funext fun j => (ft6_vec _ _ _ j).1
  · rw [← vec_eta x]; exact funext fun j => (ft6_vec _ _ _ j).2

/-- t erhält die Designation D -/
abbrev erhaelt (t : Wert → Wert) (D : Wert → Bool) : Prop := ∀ v, D (t v) = D v

/-- die drei Werttranspositionen -/
def transp : List (Wert → Wert) := [qneg₁, qneg₂, w13]

/-- **FT7:**  jede echte, nichtleere Designation wird von GENAU EINER der drei Werttranspositionen erhalten -/
theorem ft7 : ∀ d0 d1 d2 : Bool, (d0 || d1 || d2) = true → (d0 && d1 && d2) = false →
    (transp.filter fun t => decide (erhaelt t (f3 d0 d1 d2))).length = 1 := by
  decide

/-- **FT7, die Tafel** (Günthers Zählung:  Wert 0, 1, 2 = Günthers 1, 2, 3) — und E6 für die Designation des Hauses -/
theorem ft7_tafel :
    erhaelt qneg₂ (f3 true false false) ∧ erhaelt w13 (f3 false true false) ∧ erhaelt qneg₁ (f3 false false true) ∧
    erhaelt qneg₁ (f3 true true false) ∧ erhaelt w13 (f3 true false true) ∧ erhaelt qneg₂ (f3 false true true) ∧
    erhaelt qneg₁ designiert ∧ ¬ erhaelt qneg₂ designiert := by
  decide

/-! ## Muss-Fälle -/

/-- FT2 mit „genau zwei" fällt:  am Tausch (1 2) gibt es nicht zwei verschiedene Lösungen -/
theorem gegen_zwei_loesungen : ¬ ∃ s0 s1 s2 x y z s0' s1' s2' x' y' z',
    tauschKohaerent pi12 (f3 s0 s1 s2) (f3 x y z) ∧ tauschKohaerent pi12 (f3 s0' s1' s2') (f3 x' y' z') ∧
    ¬ (s0 = s0' ∧ s1 = s1' ∧ s2 = s2' ∧ x = x' ∧ y = y' ∧ z = z') := by
  decide +kernel

/-- FT3 mit vertauschtem Flip fällt:  (1 2) mit Negation in Faser 1 ist für keine Wertpermutation kohärent -/
theorem gegen_flip : ∀ s0 s1 s2 : Fin 3, ¬ tauschKohaerent pi12 (f3 s0 s1 s2) (f3 false true false) := by decide

/-- FT6 mit zwei Faktoren fällt -/
theorem gegen_zwei_faktoren :
    vekTausch pi01 (f3 true true true) (vec false false false) 1 ≠ fneg₁ (fneg₂ (vec false false false)) 1 := by decide

/-- FT7:  qneg₂ erhält {Günthers 1, 2} nicht -/
theorem gegen_qneg2_erhaelt : ¬ erhaelt qneg₂ (f3 true true false) := by decide

end Reformulation.Pfalzgraf.FaserTauschProbe

/-! ## Axiom-Wachen (gemessen, verbatim) -/

/-- info: 'Reformulation.Pfalzgraf.FaserTauschProbe.f3_eta' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.FaserTauschProbe.f3_eta

/-- info: 'Reformulation.Pfalzgraf.FaserTauschProbe.tk_punkt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.FaserTauschProbe.tk_punkt

/-- info: 'Reformulation.Pfalzgraf.FaserTauschProbe.ft1_konkret' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.FaserTauschProbe.ft1_konkret

/-- info: 'Reformulation.Pfalzgraf.FaserTauschProbe.ft1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.FaserTauschProbe.ft1

/-- info: 'Reformulation.Pfalzgraf.FaserTauschProbe.ft2_konkret' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.FaserTauschProbe.ft2_konkret

/-- info: 'Reformulation.Pfalzgraf.FaserTauschProbe.ft2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.FaserTauschProbe.ft2

/-- info: 'Reformulation.Pfalzgraf.FaserTauschProbe.ft3' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.FaserTauschProbe.ft3

/-- info: 'Reformulation.Pfalzgraf.FaserTauschProbe.ft4_konkret' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.FaserTauschProbe.ft4_konkret

/-- info: 'Reformulation.Pfalzgraf.FaserTauschProbe.ft4' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.FaserTauschProbe.ft4

/-- info: 'Reformulation.Pfalzgraf.FaserTauschProbe.vec_eta' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.FaserTauschProbe.vec_eta

/-- info: 'Reformulation.Pfalzgraf.FaserTauschProbe.ft5_vec' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.FaserTauschProbe.ft5_vec

/-- info: 'Reformulation.Pfalzgraf.FaserTauschProbe.ft5' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.FaserTauschProbe.ft5

/-- info: 'Reformulation.Pfalzgraf.FaserTauschProbe.ft6_vec' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.FaserTauschProbe.ft6_vec

/-- info: 'Reformulation.Pfalzgraf.FaserTauschProbe.ft6' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.FaserTauschProbe.ft6

/-- info: 'Reformulation.Pfalzgraf.FaserTauschProbe.ft7' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.FaserTauschProbe.ft7

/-- info: 'Reformulation.Pfalzgraf.FaserTauschProbe.ft7_tafel' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.FaserTauschProbe.ft7_tafel

/-- info: 'Reformulation.Pfalzgraf.FaserTauschProbe.gegen_zwei_loesungen' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.FaserTauschProbe.gegen_zwei_loesungen

/-- info: 'Reformulation.Pfalzgraf.FaserTauschProbe.gegen_flip' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.FaserTauschProbe.gegen_flip

/-- info: 'Reformulation.Pfalzgraf.FaserTauschProbe.gegen_zwei_faktoren' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.FaserTauschProbe.gegen_zwei_faktoren

/-- info: 'Reformulation.Pfalzgraf.FaserTauschProbe.gegen_qneg2_erhaelt' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.FaserTauschProbe.gegen_qneg2_erhaelt
