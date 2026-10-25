import Reformulation.Proemial.ErzeugteKetteProbe   -- aufPfad, ueberschreibe, regelNach, einsAn, inFaser, fasersatz_a/b, pfadPunkt

/-!
# Proemial.VerlustDanebenKuenftigProbe — was in der Faser verloren geht:  „daneben" oder „künftig"

STANDALONE, NICHT im Aggregat;  Target `Probes`.  AxiomGate unberührt.  Sonde nach
`KorpusRev2/Prompt_Instanz_Verlust_Daneben_Zukunft_Sonde.md` (Mathematiker, 25.10.2026 18:54;  Architekt 18:53 „ja, bau die Sonde.").
Konsumiert `ErzeugteKetteProbe` (`aufPfad`, `pfadPunkt`, `ueberschreibe`, `regelNach`, `einsAn`, `inFaser`, `fasersatz_a`, `fasersatz_b`,
`erzeugt_lokal_pfad`, `isRGS_take_frei`) und `Kenogram` (`isRGS_head`, `isRGS_concat`);  ändert nichts davon, auch nicht dessen Kopf.

## SETZUNG

SA1 (Architekt 25.10. 09:36):  *„Wird der Relator zum Relatum, so tauschen die Rollen — in beide Richtungen. Was der Relator als Relatum
zeigt, lässt ihn nicht zurückgewinnen: der Verlust trifft den Inhalt, nicht die Richtung."*  OFFEN dort (Register SA1):  an der ersten
Stufe ist der Wortlaut stärker als der Bau (`einsortig_moeglich_eins`).  **Die Sonde entscheidet das nicht.**

## WAS

Zählung:  Kettenlänge n = Relatum der Relator-Stufe n − 1 (W (n−1) → RGS n, wie `einsortig_*`);  „Stufe 1" = Kettenlänge 2.  Zu einer
Kette r zerfallen die Turmpunkte in drei Teile:  **auf dem Pfad** (`aufPfad`, die echten Präfixe), **daneben** (`daneben`:  unterhalb der
Länge, nicht auf dem Pfad) und **künftig** (`kuenftig`:  auf oder über der Länge).  **„abseits" im Bestand (`ueberschreibe_abseits`,
Kopf von `ErzeugteKetteProbe`) = daneben ∪ künftig;**  darum hier neue Wörter.

```text
zerlegung                FOLGERUNG (dünn)   jeder Punkt liegt genau in einem der drei Teile                          (jedes r)
daneben_iff              FOLGERUNG          IsRGS r → (es gibt einen Punkt daneben ↔ 3 ≤ |r|)                       (jede Länge)
faser_gleich             HEBUNG             c in der Faser über r:  c' in der Faser ↔ c' stimmt mit c auf dem Pfad überein
                                            (`faser_iff`, vom Glied c aus)
stufe_eins_nur_kuenftig  FOLGERUNG          |r| = 2:  zwei Regeln derselben Faser unterscheiden sich nur künftig
ab_stufe_zwei_daneben    FOLGERUNG          |r| ≥ 3:  zwei Regeln derselben Faser, gleich auf allem Künftigen, verschieden daneben
immer_kuenftig           FOLGERUNG          jede Länge:  zwei Regeln derselben Faser, gleich auf allem Nicht-Künftigen, verschieden
                                            künftig
eich_zwei, eich_drei     EICHUNG (decide)   Länge 2 an [0,1] (zu `stufe_zwei_injektiv`), Länge 3 an [0,1,2] (zu `stufe_drei_faser`)
gegen_daneben_zwei       EICHUNG            Gegenprobe:  `daneben_iff` mit „2 ≤" fällt (an [0,1])
gegen_stufe_eins_drei    EICHUNG            Gegenprobe:  `stufe_eins_nur_kuenftig` für Länge 3 fällt (an [0,1,2], Punkt [0,0])
```

Die Zeugen in `ab_stufe_zwei_daneben`:  `regelNach r` und `ueberschreibe r (einsAn s)`, s die Kette der Länge 2, die nicht `r.take 2`
ist;  `einsAn s` ist 0 auf allen künftigen Punkten, weil deren Kette länger ist als 2.  In `immer_kuenftig`:  dieselbe Bauart mit
`s = r ++ [0]`, die Kette des Punktes `ueber r` eine Stelle über der Länge — an der Länge selbst nicht, weil für r = [] dort nur 0
zulässig ist.  Hilfssätze:  `kurz` (eine RGS der Länge ≤ 1 ist `[]` oder `[0]`), `unten_aufPfad` (unterhalb Stelle 2 liegt alles unter der
Länge auf dem Pfad — der Grund für `daneben_iff` und `stufe_eins_nur_kuenftig`), `einsAn_sonst`, `paar_pfad`, `paar_abseits_null`,
`paar_abseits_eins`.  Randfälle:  für |r| ≤ 1 ist `stufe_eins_nur_kuenftig` nicht formuliert (Vorgabe |r| = 2);  `daneben_iff` und
`immer_kuenftig` gelten auch für r = [] und |r| = 1.

## ZWEI LESARTEN von „Inhalt" (LESART — die Sonde entscheidet nicht)

- **A künftig** — Verlust des Noch-nicht-Vollzogenen, auf jeder Stufe (`immer_kuenftig`).  Nähe zu IGN S. 31 „das noch nicht in einer
  Entscheidung vollzogene Umtauschverhältnis" (am Bild, Hermeneutes) — ZUORDNUNG, ungeprüft.
- **B daneben** — Verlust des Nicht-Gewählten, erst ab Stufe 2 (`daneben_iff`, `stufe_eins_nur_kuenftig`, `ab_stufe_zwei_daneben`).
  Nähe zu [T28] C&V S. 16 „the mere potential which might have been chosen but was not" (am Bild, Hermeneutes CVB-3) — ZUORDNUNG,
  ungeprüft.
- **Was B mit sich führt** (LESART):  auf Stufe 1 ist der Wechsel Regel ↔ Kette verlustfrei umkehrbar (`einsortig_moeglich_eins`,
  `stufe_zwei_injektiv`) — „mutual";  Günther nennt den proemialen Wechsel „not mutual" ([T49], [T10], Definitionen §20).  Unter
  Lesart B wäre Stufe 1 noch nicht proemial.

## ZUSAMMENSCHAU (nur Hinweis)

„Als Wille" PDF 4:  „Solange uns nur zwei Werte zur Verfügung stehen, haben wir … keine echte Wahl" (am Bild);  gemessen 25.10.:  bei
zwei Werten gibt es genau einen Negator, `Fin.rev`.  Auf Stufe 1 hat die Gabelung zwei Glieder.

## NICHT

Kein Träger für §20;  keine Entscheidung zwischen A und B;  kein Text in Rev11.

**Verbotene Kurzformen:**  „die Setzung bewiesen";  „Stufe 1 ist klassisch" (statt:  unter Lesart B);  „der Verlust ist zeitlich"
(statt:  unter Lesart A).

## Bauweise

Fallunterscheidungen über `Decidable.byCases` (`aufPfad` ist entscheidbar) und `decEq` auf `List ℕ`;  `omega` nur an Zahlzielen.
Kein `sorry`, kein `Classical.choice`, kein `native_decide`, kein True-Feld.
-/

namespace Reformulation.Proemial.VerlustDanebenKuenftigProbe

open Reformulation.Kenogram
open Reformulation.Proemial.TowerAsymmetryProbe (Tower)
open Reformulation.Proemial.KenogramForkProbe (Choice)
open Reformulation.Proemial.ErzeugteKetteProbe

/-- x liegt **daneben**:  unterhalb der Länge von r, aber nicht auf dem Pfad -/
def daneben (r : List ℕ) (x : Tower) : Prop := x.1 < r.length ∧ ¬ aufPfad r x

/-- x liegt **künftig**:  auf oder über der Länge von r -/
def kuenftig (r : List ℕ) (x : Tower) : Prop := r.length ≤ x.1

instance (r : List ℕ) (x : Tower) : Decidable (daneben r x) := inferInstanceAs (Decidable (_ ∧ ¬ _))
instance (r : List ℕ) (x : Tower) : Decidable (kuenftig r x) := inferInstanceAs (Decidable (_ ≤ _))

/-! ## Werkzeug -/

/-- eine RGS der Länge höchstens 1 ist `[]` oder `[0]` -/
theorem kurz {l : List ℕ} (hl : IsRGS l) (h : l.length ≤ 1) : l = List.replicate l.length 0 := by
  match l, hl, h with
  | [], _, _ => rfl
  | [a], hl, _ =>
    have h0 : [a][0] = 0 := isRGS_head hl (Nat.zero_lt_succ 0)
    show [a] = [0]
    rw [show a = 0 from h0]

/-- unterhalb der Stelle 2 liegt jeder Punkt unter der Länge auf dem Pfad -/
theorem unten_aufPfad (r : List ℕ) (hr : IsRGS r) (x : Tower) (h1 : x.1 < r.length) (h2 : x.1 ≤ 1) : aufPfad r x := by
  refine ⟨h1, ?_⟩
  have hx : x.2.val.length = x.1 := x.2.property.1
  have ht : (r.take x.1).length = x.1 := by rw [List.length_take]; omega
  rw [kurz x.2.property.2 (by omega), kurz (isRGS_take_frei hr x.1) (by omega), hx, ht]

theorem einsAn_sonst (s : List ℕ) (x : Tower) (h : x.2.val ≠ s) : (einsAn s x).1 = 0 := by
  simp only [einsAn, dif_neg (fun hh : x.2.val = s ∧ s ≠ [] => h hh.1)]

/-- das Paar:  `regelNach r` und `ueberschreibe r (einsAn s)` — gleich auf dem Pfad, abseits 0 gegen `einsAn s` -/
theorem paar_pfad (r : List ℕ) (hr : IsRGS r) (s : List ℕ) (x : Tower) (h : aufPfad r x) :
    (regelNach r hr x).1 = (ueberschreibe r hr (einsAn s) x).1 := by
  rw [regelNach, ueberschreibe_pfad r hr _ x h, ueberschreibe_pfad r hr _ x h]

theorem paar_abseits_null (r : List ℕ) (hr : IsRGS r) (s : List ℕ) (x : Tower) (h : ¬ aufPfad r x)
    (hs : x.2.val.length ≠ s.length) : (regelNach r hr x).1 = (ueberschreibe r hr (einsAn s) x).1 := by
  rw [regelNach, ueberschreibe_abseits r hr _ x h, ueberschreibe_abseits r hr _ x h,
    einsAn_sonst s x (fun e => hs (congrArg List.length e))]
  rfl

theorem paar_abseits_eins (r : List ℕ) (hr : IsRGS r) (s : List ℕ) (hne : s ≠ []) (x : Tower) (h : ¬ aufPfad r x)
    (hs : x.2.val = s) : (regelNach r hr x).1 ≠ (ueberschreibe r hr (einsAn s) x).1 := by
  rw [regelNach, ueberschreibe_abseits r hr _ x h, ueberschreibe_abseits r hr _ x h, einsAn_an s hne x hs]
  exact Nat.zero_ne_one

/-! ## D1 · die Zerlegung -/

/-- **D1:**  jeder Punkt liegt auf dem Pfad, daneben oder künftig — genau eines davon -/
theorem zerlegung (r : List ℕ) (x : Tower) :
    (aufPfad r x ∨ daneben r x ∨ kuenftig r x) ∧ ¬ (aufPfad r x ∧ daneben r x) ∧
      ¬ (aufPfad r x ∧ kuenftig r x) ∧ ¬ (daneben r x ∧ kuenftig r x) := by
  refine ⟨?_, fun h => h.2.2 h.1, fun h => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h.1.1 h.2),
    fun h => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h.1.1 h.2)⟩
  rcases Nat.lt_or_ge x.1 r.length with hl | hg
  · exact Decidable.byCases (p := aufPfad r x) Or.inl (fun hn => Or.inr (Or.inl ⟨hl, hn⟩))
  · exact Or.inr (Or.inr hg)

/-! ## D2 · daneben gibt es erst ab Länge 3 -/

/-- **D2** -/
theorem daneben_iff (r : List ℕ) (hr : IsRGS r) : (∃ x, daneben r x) ↔ 3 ≤ r.length := by
  constructor
  · rintro ⟨x, hl, hn⟩
    rcases Nat.lt_or_ge x.1 2 with h2 | h2
    · exact absurd (unten_aufPfad r hr x hl (by omega)) hn
    · omega
  · intro h3
    rcases decEq (r.take 2) [0, 0] with he | he
    · refine ⟨p00, by show 2 < r.length; omega, fun hp => he ?_⟩
      exact hp.2.symm
    · refine ⟨p01, by show 2 < r.length; omega, fun hp => ?_⟩
      have : r.take 2 = [0, 1] := hp.2.symm
      exact absurd (this ▸ he) (by decide)

/-! ## D3 · die Faser, von einem ihrer Glieder aus -/

/-- **D3** -/
theorem faser_gleich (c c' : Choice) (r : List ℕ) (hr : IsRGS r) (hc : inFaser c r) :
    inFaser c' r ↔ ∀ x, aufPfad r x → (c x).1 = (c' x).1 := by
  constructor
  · intro hc' x h
    have heq : x = pfadPunkt r hr x.1 (Nat.le_of_lt h.1) := tower_ext rfl h.2
    rw [heq, (fasersatz_a c r hr).mp hc x.1 h.1, (fasersatz_a c' r hr).mp hc' x.1 h.1]
  · intro H
    exact erzeugt_lokal_pfad c c' r hr hc fun i hi => H _ (pfadPunkt_aufPfad r hr i hi)

/-! ## D4 · Stufe 1:  nur künftig -/

/-- **D4** -/
theorem stufe_eins_nur_kuenftig (c c' : Choice) (r : List ℕ) (hr : IsRGS r) (h2 : r.length = 2)
    (hc : inFaser c r) (hc' : inFaser c' r) : ∀ x, ¬ kuenftig r x → (c x).1 = (c' x).1 := by
  intro x hk
  have hl : x.1 < r.length := Nat.lt_of_not_le hk
  exact (faser_gleich c c' r hr hc).mp hc' x (unten_aufPfad r hr x hl (by omega))

/-! ## D5 · ab Stufe 2:  auch daneben -/

/-- **D5** -/
theorem ab_stufe_zwei_daneben (r : List ℕ) (hr : IsRGS r) (h3 : 3 ≤ r.length) :
    ∃ c c', inFaser c r ∧ inFaser c' r ∧ (∀ x, kuenftig r x → (c x).1 = (c' x).1) ∧
      ∃ x, daneben r x ∧ (c x).1 ≠ (c' x).1 := by
  obtain ⟨x, hd⟩ := (daneben_iff r hr).mpr h3
  have hx2 : x.2.val.length = x.1 := x.2.property.1
  have hne : x.2.val ≠ [] := by
    intro e
    have := x.2.property.1; rw [e] at this
    exact hd.2 (unten_aufPfad r hr x hd.1 (by simp at this; omega))
  refine ⟨regelNach r hr, ueberschreibe r hr (einsAn x.2.val), erzeugt_regelNach r hr,
    (fasersatz_b r hr _).1, fun y hy => ?_, x, hd, paar_abseits_eins r hr _ hne x hd.2 rfl⟩
  have hy2 : y.2.val.length = y.1 := y.2.property.1
  exact paar_abseits_null r hr _ y (fun hp => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hp.1 hy))
    (by have h1 : x.1 < r.length := hd.1; have h2 : r.length ≤ y.1 := hy; rw [hy2, hx2]; omega)

/-! ## D6 · auf jeder Stufe:  künftig -/

/-- der Punkt über `r ++ [0]` -/
def ueber (r : List ℕ) (hr : IsRGS r) : Tower :=
  ⟨r.length + 1, ⟨r ++ [0], by rw [List.length_append]; rfl, isRGS_concat r 0 hr (Nat.zero_le _) (fun _ => rfl)⟩⟩

/-- **D6** -/
theorem immer_kuenftig (r : List ℕ) (hr : IsRGS r) :
    ∃ c c', inFaser c r ∧ inFaser c' r ∧ (∀ x, ¬ kuenftig r x → (c x).1 = (c' x).1) ∧
      ∃ x, kuenftig r x ∧ (c x).1 ≠ (c' x).1 := by
  refine ⟨regelNach r hr, ueberschreibe r hr (einsAn (r ++ [0])), erzeugt_regelNach r hr,
    (fasersatz_b r hr _).1, fun y hy => ?_, ueber r hr, Nat.le_succ _, ?_⟩
  · have hy2 : y.2.val.length = y.1 := y.2.property.1
    have hl : y.1 < r.length := Nat.lt_of_not_le hy
    exact Decidable.byCases (p := aufPfad r y) (paar_pfad r hr _ y)
      (fun hn => paar_abseits_null r hr _ y hn (by rw [hy2, List.length_append]; simp only [List.length_singleton]; omega))
  · exact paar_abseits_eins r hr _ (List.append_ne_nil_of_right_ne_nil r (List.cons_ne_nil 0 []))
      (ueber r hr) (fun hp => Nat.lt_irrefl _ (Nat.lt_trans (Nat.lt_succ_self _) hp.1)) rfl

/-! ## Eichungen -/

theorem isRGS_01 : IsRGS [0, 1] := by decide

/-- der Punkt [0,1,0] -/
def p010 : Tower := ⟨3, ⟨[0, 1, 0], by decide⟩⟩

/-- **Länge 2** (`stufe_zwei_injektiv`):  über `[0,1]` liegen `[]` und `[0]` auf dem Pfad, `[0,0]` und `[0,1]` künftig, nichts daneben;  die
    zwei Regeln erzeugen beide [0,1] und unterscheiden sich am künftigen Punkt [0,1,0] -/
theorem eich_zwei :
    aufPfad [0, 1] wurzel ∧ aufPfad [0, 1] p0 ∧ kuenftig [0, 1] p00 ∧ kuenftig [0, 1] p01 ∧
    ¬ daneben [0, 1] p00 ∧ ¬ daneben [0, 1] p01 ∧
    erzeugt (regelNach [0, 1] isRGS_01) 2 = [0, 1] ∧ erzeugt (ueberschreibe [0, 1] isRGS_01 (einsAn [0, 1, 0])) 2 = [0, 1] ∧
    (regelNach [0, 1] isRGS_01 p010).1 = 0 ∧ (ueberschreibe [0, 1] isRGS_01 (einsAn [0, 1, 0]) p010).1 = 1 := by
  decide

/-- **Länge 3** (`stufe_drei_faser`):  über [0,1,2] liegt [0,0] daneben, [0,1] auf dem Pfad;  die zwei Regeln erzeugen beide
    [0,1,2] und unterscheiden sich am daneben liegenden Punkt [0,0] -/
theorem eich_drei :
    daneben [0, 1, 2] p00 ∧ aufPfad [0, 1, 2] p01 ∧ ¬ daneben [0, 1, 2] p01 ∧ kuenftig [0, 1, 2] p010 ∧
    erzeugt (regelNach [0, 1, 2] isRGS_012) 3 = [0, 1, 2] ∧
    erzeugt (ueberschreibe [0, 1, 2] isRGS_012 (einsAn [0, 0])) 3 = [0, 1, 2] ∧
    (regelNach [0, 1, 2] isRGS_012 p00).1 = 0 ∧ (ueberschreibe [0, 1, 2] isRGS_012 (einsAn [0, 0]) p00).1 = 1 := by
  decide

/-! ## Gegenproben -/

/-- **D2 mit „2 ≤" fällt** (an [0,1]) -/
theorem gegen_daneben_zwei : ¬ ∀ r, IsRGS r → ((∃ x, daneben r x) ↔ 2 ≤ r.length) := by
  intro H
  have h := (daneben_iff [0, 1] isRGS_01).mp ((H [0, 1] isRGS_01).mpr (le_refl _))
  exact absurd h (by decide)

/-- **D4 für Länge 3 fällt** (an [0,1,2], am Punkt [0,0]) -/
theorem gegen_stufe_eins_drei :
    ¬ ∀ c c' : Choice, ∀ r, IsRGS r → r.length = 3 → inFaser c r → inFaser c' r →
      ∀ x, ¬ kuenftig r x → (c x).1 = (c' x).1 := by
  intro H
  have e := eich_drei
  exact absurd (H _ _ [0, 1, 2] isRGS_012 rfl e.2.2.2.2.1 e.2.2.2.2.2.1 p00 (fun hk => absurd hk (by decide)))
    (by rw [e.2.2.2.2.2.2.1, e.2.2.2.2.2.2.2]; decide)

end Reformulation.Proemial.VerlustDanebenKuenftigProbe

/-! ## Axiom-Wachen (gemessen, verbatim) -/

/-- info: 'Reformulation.Proemial.VerlustDanebenKuenftigProbe.kurz' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VerlustDanebenKuenftigProbe.kurz

/-- info: 'Reformulation.Proemial.VerlustDanebenKuenftigProbe.unten_aufPfad' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VerlustDanebenKuenftigProbe.unten_aufPfad

/-- info: 'Reformulation.Proemial.VerlustDanebenKuenftigProbe.einsAn_sonst' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.VerlustDanebenKuenftigProbe.einsAn_sonst

/-- info: 'Reformulation.Proemial.VerlustDanebenKuenftigProbe.paar_pfad' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VerlustDanebenKuenftigProbe.paar_pfad

/-- info: 'Reformulation.Proemial.VerlustDanebenKuenftigProbe.paar_abseits_null' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VerlustDanebenKuenftigProbe.paar_abseits_null

/-- info: 'Reformulation.Proemial.VerlustDanebenKuenftigProbe.paar_abseits_eins' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VerlustDanebenKuenftigProbe.paar_abseits_eins

/-- info: 'Reformulation.Proemial.VerlustDanebenKuenftigProbe.zerlegung' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Proemial.VerlustDanebenKuenftigProbe.zerlegung

/-- info: 'Reformulation.Proemial.VerlustDanebenKuenftigProbe.daneben_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VerlustDanebenKuenftigProbe.daneben_iff

/-- info: 'Reformulation.Proemial.VerlustDanebenKuenftigProbe.faser_gleich' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VerlustDanebenKuenftigProbe.faser_gleich

/-- info: 'Reformulation.Proemial.VerlustDanebenKuenftigProbe.stufe_eins_nur_kuenftig' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VerlustDanebenKuenftigProbe.stufe_eins_nur_kuenftig

/-- info: 'Reformulation.Proemial.VerlustDanebenKuenftigProbe.ab_stufe_zwei_daneben' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VerlustDanebenKuenftigProbe.ab_stufe_zwei_daneben

/-- info: 'Reformulation.Proemial.VerlustDanebenKuenftigProbe.immer_kuenftig' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VerlustDanebenKuenftigProbe.immer_kuenftig

/-- info: 'Reformulation.Proemial.VerlustDanebenKuenftigProbe.isRGS_01' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Proemial.VerlustDanebenKuenftigProbe.isRGS_01

/-- info: 'Reformulation.Proemial.VerlustDanebenKuenftigProbe.eich_zwei' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VerlustDanebenKuenftigProbe.eich_zwei

/-- info: 'Reformulation.Proemial.VerlustDanebenKuenftigProbe.eich_drei' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VerlustDanebenKuenftigProbe.eich_drei

/-- info: 'Reformulation.Proemial.VerlustDanebenKuenftigProbe.gegen_daneben_zwei' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VerlustDanebenKuenftigProbe.gegen_daneben_zwei

/-- info: 'Reformulation.Proemial.VerlustDanebenKuenftigProbe.gegen_stufe_eins_drei' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.VerlustDanebenKuenftigProbe.gegen_stufe_eins_drei
