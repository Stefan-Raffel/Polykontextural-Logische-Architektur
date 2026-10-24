import Reformulation.Pfalzgraf.Faserung
import Reformulation.Proemial.ImplicationTransjunction

/-!
# Reformulation.Pfalzgraf.FaserungT — Formeln mit Transjunktion, die freie Mengen-Semantik Σ1, die Erhaltung

**Was das Modul ist (CLAUDE.md §4):** ERTRAG, Teil T von Rev11 (Modul A von zwei).  Gebaut nach
`KorpusRev2/Prompt_Instanz_T_Bau.md` (Mathematiker 24.10.2026, mit Custos' Prüfung §4).  Die Träger von Rev10
(`Faserung`, `Kaehr/Tableau`, `VKaehrProbe`, `ImplicationTransjunction`) sind unberührt.

## T1 · Die Herkünfte

```text
NACH PFALZGRAF 1991   eine Transjunktion = ein klassisches 2×2-Muster je Faser und eine Verteilung D_αβγδ der vier Zellen
                      (TT, TF, FT, FF, in dieser Reihenfolge) auf Fasern (S. 181 f., "8 Classifying Transjunctions");  die Verteilung
                      setzt den INDEX, nicht T/F ("D_αβγδ(F_i) = F_α", S. 181);  well-definedness (S. 179, 182);  Beispiel 7.3
                      (S. 180 f.).  Nach Hermeneutes, am Bild (T_Quellen_am_Bild_Antwort_Hermeneutes.md H1).
NACH MEIXL / PFALZGRAF-SOFRONIE   die zwei Verteilungen T₂ ↦ T₁ und T₂ ↦ T₃ "have the same result" (Meixl S. 26;  1995 S. 8).
UNSER                 die MENGEN-Semantik Σ1 für das freie System (`wertT`):  ein Wert, der aus Faser i in Faser k wandert, ist dort
                      Element der Wertmenge — die Menge kann LEER sein (die Quelle schickt fort, nichts kommt an) oder DOPPELT (die Faser
                      rechnet selbst und bekommt zugleich).  Pfalzgrafs Formel ist eine Auswertung für den wohldefinierten Fall;  die
                      Mengen-Fassung für den freien Fall ist LESART DES HAUSES (Custos A2).  Die Designationen D1, D2 (UNSER, Antwort
                      des Mathematikers F3);  die Quotientenauswertung mit Verteilung (`qtrans`, `zulaessigT`) nach Pfalzgrafs Wort.
```

## T2 · Die Semantik

`wertT f φ k b` heisst:  b liegt in der Wertmenge S(f, φ) k.  Eine Belegung f für die ganze Formel.

```text
var n      S k = { f n k }
neg₁/neg₂  elementweise wie fneg₁ / fneg₂ (Faser 0 bzw. 1 negiert, die anderen getauscht)
junk o     S k = { o_k(x, y) | x ∈ S(a) k, y ∈ S(c) k }
trans ϑ D  S k = { ϑ_i(x, y) | i Faser, x ∈ S(a) i, y ∈ S(c) i, D_i(x, y) = k }
D1         gueltigT1 φ :⟺ ∀ f k, false ∉ S(f, φ) k  — "in keiner Faser falsch";  das schliesst eine LEERE Faser ein
D2         gueltigT2 φ :⟺ ∀ f k, true ∈ S(f, φ) k   — "in jeder Faser auch wahr"
```

Für Formeln ohne Transjunktion ist jede Wertmenge einelementig, und D1, D2 fallen mit `gueltigFrei` zusammen
(`einbett_frei`, `einbett_gueltig1`, `einbett_gueltig2`).

## Die Sätze

```text
einbett_frei, einbett_quot     FOLGERUNG:  die Erhaltung, frei und im Quotienten
einbett_gueltig1/2             FOLGERUNG:  für Fm fallen D1, D2 und gueltigFrei zusammen
junk_als_trans                 FOLGERUNG:  ein Junktor ist die Transjunktion mit D_i ≡ i (frei und im Quotienten)
wertT_lokal                    Hilfssatz:  die Auswertung hängt nur von den Variablen ab
eich_E1, eich_E2, eich_E4      EICHUNG an Pfalzgraf 7.3 (E1), Meixl S. 26 / Pfalzgraf-Sofronie S. 8 (E2);  E4 gerechnet, Gegenprobe,
                               keine Quelle (Speculum)
```

Kein `sorry`, kein `Classical.choice`, kein `native_decide`.
-/

namespace Reformulation.Pfalzgraf.FaserungT

open Reformulation.Pfalzgraf

/-! ## Der Typ -/

/-- eine Verteilung:  die Zielfaser je Zelle (TT, TF, FT, FF) — Pfalzgrafs D_αβγδ -/
abbrev Vert := Faser × Faser × Faser × Faser
/-- die Zielfaser einer Zelle -/
def apV (d : Vert) : Bool → Bool → Faser
  | true, true => d.1 | true, false => d.2.1 | false, true => d.2.2.1 | false, false => d.2.2.2
/-- die Verteilung der Faser i aus einem Tripel -/
def vAt (d0 d1 d2 : Vert) : Faser → Vert
  | ⟨0, _⟩ => d0 | ⟨1, _⟩ => d1 | ⟨2, _⟩ => d2
/-- die lokale Verteilung der Faser i:  jede Zelle bleibt -/
def lok (i : Faser) : Vert := (i, i, i, i)

/-- Formeln mit Transjunktion:  `junk` wie in Faserung, `trans` mit Muster und Verteilung je Faser -/
inductive FmT
  | var (n : ℕ)
  | neg₁ (a : FmT)
  | neg₂ (a : FmT)
  | junk (o0 o1 o2 : Op) (a b : FmT)
  | trans (t0 t1 t2 : Op) (d0 d1 d2 : Vert) (a b : FmT)

/-- die Einbettung der Formeln von Faserung -/
def einbett : Fm → FmT
  | .var n => .var n
  | .neg₁ a => .neg₁ (einbett a)
  | .neg₂ a => .neg₂ (einbett a)
  | .junk o0 o1 o2 a b => .junk o0 o1 o2 (einbett a) (einbett b)

/-! ## Σ1 — die freie Mengen-Semantik -/

/-- Fasern vergleichen, über `.val` (Mathlibs Fin-Ordnung trägt Choice, Kaehr/Tableau K8) -/
def fbeq (i j : Faser) : Bool := Nat.beq i.val j.val
/-- es gibt ein Paar (x, y) -/
def ex2 (P : Bool → Bool → Bool) : Bool := P true true || P true false || P false true || P false false
/-- es gibt eine Faser -/
def ex3 (P : Faser → Bool) : Bool := P 0 || P 1 || P 2

/-- **Σ1.**  `wertT f φ k b`:  b liegt in der Wertmenge von φ in Faser k unter f -/
def wertT (f : FreieBelegung) : FmT → Faser → Bool → Bool
  | .var n, k, b => f n k == b
  | .neg₁ a, ⟨0, _⟩, b => wertT f a 0 (!b)
  | .neg₁ a, ⟨1, _⟩, b => wertT f a 2 b
  | .neg₁ a, ⟨2, _⟩, b => wertT f a 1 b
  | .neg₂ a, ⟨0, _⟩, b => wertT f a 2 b
  | .neg₂ a, ⟨1, _⟩, b => wertT f a 1 (!b)
  | .neg₂ a, ⟨2, _⟩, b => wertT f a 0 b
  | .junk o0 o1 o2 a c, k, b => ex2 fun x y => wertT f a k x && wertT f c k y && (ap (oAt o0 o1 o2 k) x y == b)
  | .trans t0 t1 t2 d0 d1 d2 a c, k, b => ex3 fun i => ex2 fun x y =>
      wertT f a i x && wertT f c i y && fbeq (apV (vAt d0 d1 d2 i) x y) k && (ap (oAt t0 t1 t2 i) x y == b)

/-- **D1.**  in keiner Faser falsch — auch, wo eine Faser keinen Wert hat -/
def gueltigT1 (φ : FmT) : Prop := ∀ (f : FreieBelegung) (k : Faser), wertT f φ k false = false
/-- **D2.**  in jeder Faser auch wahr -/
def gueltigT2 (φ : FmT) : Prop := ∀ (f : FreieBelegung) (k : Faser), wertT f φ k true = true
/-- die Wertmenge ist leer -/
def leer (f : FreieBelegung) (φ : FmT) (k : Faser) : Prop := wertT f φ k true = false ∧ wertT f φ k false = false

/-! ## Der Quotient mit Verteilung -/

/-- die Lesung der Faser i für das Paar (a, b):  der Wert wandert in die Zielfaser seiner Zelle -/
def faserWertT (t0 t1 t2 : Op) (d0 d1 d2 : Vert) (i : Faser) (a b : Wert) : Wert :=
  global (apV (vAt d0 d1 d2 i) (lokal i a) (lokal i b)) (ap (oAt t0 t1 t2 i) (lokal i a) (lokal i b))
/-- **well-definedness** (Pfalzgraf S. 179, 182):  je zwei Fasern, die beide Argumente lesen, liefern denselben globalen Wert -/
def zulaessigT (t0 t1 t2 : Op) (d0 d1 d2 : Vert) : Bool :=
  [0, 1, 2].all fun (a : Wert) => [0, 1, 2].all fun (b : Wert) =>
    [0, 1, 2].all fun (i : Faser) => [0, 1, 2].all fun (j : Faser) =>
      !(liest i a && liest i b && liest j a && liest j b) ||
        Nat.beq (faserWertT t0 t1 t2 d0 d1 d2 i a b).val (faserWertT t0 t1 t2 d0 d1 d2 j a b).val
/-- die Quotientenoperation:  die erste Faser, die beide Argumente liest -/
def qtrans (t0 t1 t2 : Op) (d0 d1 d2 : Vert) (a b : Wert) : Wert :=
  if liest 0 a && liest 0 b then faserWertT t0 t1 t2 d0 d1 d2 0 a b
  else if liest 1 a && liest 1 b then faserWertT t0 t1 t2 d0 d1 d2 1 a b
  else faserWertT t0 t1 t2 d0 d1 d2 2 a b
/-- die Auswertung im Quotienten -/
def auswQuotT (v : Belegung) : FmT → Wert
  | .var n => v n
  | .neg₁ a => qneg₁ (auswQuotT v a)
  | .neg₂ a => qneg₂ (auswQuotT v a)
  | .junk o0 o1 o2 a b => qop o0 o1 o2 (auswQuotT v a) (auswQuotT v b)
  | .trans t0 t1 t2 d0 d1 d2 a b => qtrans t0 t1 t2 d0 d1 d2 (auswQuotT v a) (auswQuotT v b)

/-! ## Die Erhaltung -/

theorem ex2_punkt : ∀ o1 o2 o3 o4 u v b : Bool,
    ex2 (fun x y => (u == x) && (v == y) && (ap (o1, o2, o3, o4) x y == b)) = (ap (o1, o2, o3, o4) u v == b) := by
  decide

theorem bneg_beq : ∀ x b : Bool, (x == !b) = ((!x) == b) := by decide

/-- **Erhaltung, frei.**  Für eine Formel ohne Transjunktion ist die Wertmenge einelementig:  sie enthält genau `auswFrei` -/
theorem einbett_frei (f : FreieBelegung) : ∀ (φ : Fm) (k : Faser) (b : Bool),
    wertT f (einbett φ) k b = (auswFrei f φ k == b)
  | .var _, _, _ => rfl
  | .neg₁ a, ⟨0, _⟩, b => by
    simp only [einbett, wertT, auswFrei, fneg₁]
    rw [einbett_frei f a 0 (!b), bneg_beq]
  | .neg₁ a, ⟨1, _⟩, b => einbett_frei f a 2 b
  | .neg₁ a, ⟨2, _⟩, b => einbett_frei f a 1 b
  | .neg₂ a, ⟨0, _⟩, b => einbett_frei f a 2 b
  | .neg₂ a, ⟨1, _⟩, b => by
    simp only [einbett, wertT, auswFrei, fneg₂]
    rw [einbett_frei f a 1 (!b), bneg_beq]
  | .neg₂ a, ⟨2, _⟩, b => einbett_frei f a 0 b
  | .junk o0 o1 o2 a c, k, b => by
    show ex2 (fun x y => wertT f (einbett a) k x && wertT f (einbett c) k y && (ap (oAt o0 o1 o2 k) x y == b)) =
      (ap (oAt o0 o1 o2 k) (auswFrei f a k) (auswFrei f c k) == b)
    simp only [ex2, einbett_frei f a k, einbett_frei f c k]
    obtain ⟨o1, o2, o3, o4⟩ := oAt o0 o1 o2 k
    have h := ex2_punkt o1 o2 o3 o4 (auswFrei f a k) (auswFrei f c k) b
    simp only [ex2] at h
    exact h

/-- **Erhaltung, Quotient** -/
theorem einbett_quot (v : Belegung) : ∀ φ : Fm, auswQuotT v (einbett φ) = auswQuot v φ
  | .var _ => rfl
  | .neg₁ a => congrArg qneg₁ (einbett_quot v a)
  | .neg₂ a => congrArg qneg₂ (einbett_quot v a)
  | .junk o0 o1 o2 a c => by
    show qop o0 o1 o2 (auswQuotT v (einbett a)) (auswQuotT v (einbett c)) = qop o0 o1 o2 (auswQuot v a) (auswQuot v c)
    rw [einbett_quot v a, einbett_quot v c]

theorem beq_false_false : ∀ x : Bool, (x == false) = false ↔ x = true := by decide
theorem beq_true_true : ∀ x : Bool, (x == true) = true ↔ x = true := by decide

/-- **Für Fm fallen D1 und `gueltigFrei` zusammen** -/
theorem einbett_gueltig1 (φ : Fm) : gueltigT1 (einbett φ) ↔ gueltigFrei φ := by
  unfold gueltigT1 gueltigFrei
  constructor
  · intro h f k; exact (beq_false_false _).mp ((einbett_frei f φ k false).symm.trans (h f k))
  · intro h f k; rw [einbett_frei]; exact (beq_false_false _).mpr (h f k)

/-- **… und D2** -/
theorem einbett_gueltig2 (φ : Fm) : gueltigT2 (einbett φ) ↔ gueltigFrei φ := by
  unfold gueltigT2 gueltigFrei
  constructor
  · intro h f k; exact (beq_true_true _).mp ((einbett_frei f φ k true).symm.trans (h f k))
  · intro h f k; rw [einbett_frei]; exact (beq_true_true _).mpr (h f k)

theorem lok_apV (i : Faser) : ∀ x y : Bool, apV (lok i) x y = i := by
  intro x y; cases x <;> cases y <;> rfl

/-- die Auswahl einer Faser:  `ex3` mit dem Faktor `fbeq i k` ist die Faser k -/
theorem ex3_sel (Q R : Faser → Bool → Bool → Bool) (k : Faser) :
    ex3 (fun i => ex2 fun x y => Q i x y && fbeq i k && R i x y) = ex2 (fun x y => Q k x y && R k x y) := by
  match k with
  | ⟨0, h⟩ =>
    have e0 : fbeq 0 ⟨0, h⟩ = true := rfl
    have e1 : fbeq 1 ⟨0, h⟩ = false := rfl
    have e2 : fbeq 2 ⟨0, h⟩ = false := rfl
    simp only [ex3, ex2, e0, e1, e2, Bool.and_true, Bool.and_false, Bool.false_and, Bool.or_false]
    rfl
  | ⟨1, h⟩ =>
    have e0 : fbeq 0 ⟨1, h⟩ = false := rfl
    have e1 : fbeq 1 ⟨1, h⟩ = true := rfl
    have e2 : fbeq 2 ⟨1, h⟩ = false := rfl
    simp only [ex3, ex2, e0, e1, e2, Bool.and_true, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or]
    rfl
  | ⟨2, h⟩ =>
    have e0 : fbeq 0 ⟨2, h⟩ = false := rfl
    have e1 : fbeq 1 ⟨2, h⟩ = false := rfl
    have e2 : fbeq 2 ⟨2, h⟩ = true := rfl
    simp only [ex3, ex2, e0, e1, e2, Bool.and_true, Bool.and_false, Bool.false_and, Bool.false_or]
    rfl

theorem lok_vAt : ∀ (i : Faser) (x y : Bool), apV (vAt (lok 0) (lok 1) (lok 2) i) x y = i
  | ⟨0, _⟩, x, y => lok_apV 0 x y
  | ⟨1, _⟩, x, y => lok_apV 1 x y
  | ⟨2, _⟩, x, y => lok_apV 2 x y

/-- **Ein Junktor ist die Transjunktion mit lokaler Verteilung**, frei -/
theorem junk_als_trans (f : FreieBelegung) (o0 o1 o2 : Op) (a c : FmT) (k : Faser) (b : Bool) :
    wertT f (.junk o0 o1 o2 a c) k b = wertT f (.trans o0 o1 o2 (lok 0) (lok 1) (lok 2) a c) k b := by
  simp only [wertT, lok_vAt]
  exact (ex3_sel (fun i x y => wertT f a i x && wertT f c i y) (fun i x y => ap (oAt o0 o1 o2 i) x y == b) k).symm

/-- **… und im Quotienten** -/
theorem junk_als_trans_quot (o0 o1 o2 : Op) (a b : Wert) :
    qop o0 o1 o2 a b = qtrans o0 o1 o2 (lok 0) (lok 1) (lok 2) a b := by
  simp only [qop, qtrans, faserWert, faserWertT, vAt, lok_apV]

/-! ## Lokalität -/

/-- die Variablen einer Formel -/
def varsT : FmT → List ℕ
  | .var n => [n]
  | .neg₁ a => varsT a
  | .neg₂ a => varsT a
  | .junk _ _ _ a b => varsT a ++ varsT b
  | .trans _ _ _ _ _ _ a b => varsT a ++ varsT b

/-- die Auswertung hängt nur von den Variablen der Formel ab (punktweise je Faser) -/
theorem wertT_lokal : ∀ (φ : FmT) (f g : FreieBelegung), (∀ n ∈ varsT φ, ∀ i, f n i = g n i) →
    ∀ k b, wertT f φ k b = wertT g φ k b
  | .var n, f, g, h, k, b => by show (f n k == b) = (g n k == b); rw [h n List.mem_cons_self k]
  | .neg₁ a, f, g, h, k, b => by
    have ih := wertT_lokal a f g h
    match k with
    | ⟨0, _⟩ => exact ih 0 (!b)
    | ⟨1, _⟩ => exact ih 2 b
    | ⟨2, _⟩ => exact ih 1 b
  | .neg₂ a, f, g, h, k, b => by
    have ih := wertT_lokal a f g h
    match k with
    | ⟨0, _⟩ => exact ih 2 b
    | ⟨1, _⟩ => exact ih 1 (!b)
    | ⟨2, _⟩ => exact ih 0 b
  | .junk o0 o1 o2 a c, f, g, h, k, b => by
    have iha := wertT_lokal a f g (fun n hn => h n (List.mem_append_left _ hn))
    have ihc := wertT_lokal c f g (fun n hn => h n (List.mem_append_right _ hn))
    simp only [wertT, ex2, iha, ihc]
  | .trans t0 t1 t2 d0 d1 d2 a c, f, g, h, k, b => by
    have iha := wertT_lokal a f g (fun n hn => h n (List.mem_append_left _ hn))
    have ihc := wertT_lokal c f g (fun n hn => h n (List.mem_append_right _ hn))
    simp only [wertT, ex3, ex2, iha, ihc]

/-- für eine Formel in der einen Variablen 0 genügen die acht konstanten Belegungen -/
theorem wertT_eins (φ : FmT) (h : (varsT φ).all (fun n => Nat.beq n 0) = true) (f : FreieBelegung) (k : Faser) (b : Bool) :
    wertT f φ k b = wertT (fun _ => vec (f 0 0) (f 0 1) (f 0 2)) φ k b := by
  apply wertT_lokal
  intro n hn i
  have h0 : n = 0 := Nat.eq_of_beq_eq_true (all_mp h n hn)
  subst h0
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl

theorem gueltigT1_eins (φ : FmT) (h : (varsT φ).all (fun n => Nat.beq n 0) = true)
    (hd : ∀ b0 b1 b2 : Bool, ∀ k : Faser, wertT (fun _ => vec b0 b1 b2) φ k false = false) : gueltigT1 φ :=
  fun f k => (wertT_eins φ h f k false).trans (hd _ _ _ k)

theorem gueltigT2_eins (φ : FmT) (h : (varsT φ).all (fun n => Nat.beq n 0) = true)
    (hd : ∀ b0 b1 b2 : Bool, ∀ k : Faser, wertT (fun _ => vec b0 b1 b2) φ k true = true) : gueltigT2 φ :=
  fun f k => (wertT_eins φ h f k true).trans (hd _ _ _ k)

/-! ## Eichungen -/

/-- **E1** (Pfalzgraf 7.3, S. 180 f.):  ∧∨→ ist nicht wohldefiniert, ∧∨∧ ist es — mit lokaler Verteilung, wie `unzulaessig_faelle` -/
theorem eich_E1 :
    zulaessigT opK opD opI (lok 0) (lok 1) (lok 2) = false ∧ zulaessigT opK opD opK (lok 0) (lok 1) (lok 2) = true := by
  decide

/-- die Verteilung der Faser 1 aus E2:  wahre Ergebnisse nach Faser z, falsche bleiben -/
def dE2 (z : Faser) : Vert := (z, 1, z, z)

/-- **E2** (Meixl S. 26;  Pfalzgraf/Sofronie 1995 S. 8):  Faser 1 Implikationsmuster mit T₂ ↦ T₁ (z = 0) oder T₂ ↦ T₃ (z = 2),
    Fasern 0 und 2 Implikation lokal:  beide wohldefiniert, beide gleich `meixlIMPLY` — und ohne Verteilung nicht wohldefiniert -/
theorem eich_E2 :
    zulaessigT opI opI opI (lok 0) (dE2 0) (lok 2) = true ∧ zulaessigT opI opI opI (lok 0) (dE2 2) (lok 2) = true ∧
    (∀ a b : Wert, qtrans opI opI opI (lok 0) (dE2 0) (lok 2) a b =
      Reformulation.Proemial.ImplicationTransjunction.meixlIMPLY a b) ∧
    (∀ a b : Wert, qtrans opI opI opI (lok 0) (dE2 2) (lok 2) a b =
      Reformulation.Proemial.ImplicationTransjunction.meixlIMPLY a b) ∧
    zulaessigT opI opI opI (lok 0) (lok 1) (lok 2) = false := by
  decide

/-- **E4** (gerechnet, Speculum;  keine Quelle):  an Günthers Diagonale (2, 2) liest Faser 0 ein F, Faser 1 ein T;  bei
    idempotentem Muster ist von den neun Ablagen (Zielfaser für Faser 0, Zielfaser für Faser 1) genau die lokale wohldefiniert -/
theorem eich_E4 : ∀ z0 z1 : Faser,
    Nat.beq (global z0 false).val (global z1 true).val = (fbeq z0 0 && fbeq z1 1) := by
  decide

end Reformulation.Pfalzgraf.FaserungT

/-! ## Axiom-Wachen (gemessen, verbatim) -/

/-- info: 'Reformulation.Pfalzgraf.FaserungT.ex2_punkt' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.FaserungT.ex2_punkt

/-- info: 'Reformulation.Pfalzgraf.FaserungT.bneg_beq' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.FaserungT.bneg_beq

/-- info: 'Reformulation.Pfalzgraf.FaserungT.einbett_frei' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.FaserungT.einbett_frei

/-- info: 'Reformulation.Pfalzgraf.FaserungT.einbett_quot' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.FaserungT.einbett_quot

/-- info: 'Reformulation.Pfalzgraf.FaserungT.beq_false_false' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.FaserungT.beq_false_false

/-- info: 'Reformulation.Pfalzgraf.FaserungT.beq_true_true' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.FaserungT.beq_true_true

/-- info: 'Reformulation.Pfalzgraf.FaserungT.einbett_gueltig1' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.FaserungT.einbett_gueltig1

/-- info: 'Reformulation.Pfalzgraf.FaserungT.einbett_gueltig2' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.FaserungT.einbett_gueltig2

/-- info: 'Reformulation.Pfalzgraf.FaserungT.lok_apV' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.FaserungT.lok_apV

/-- info: 'Reformulation.Pfalzgraf.FaserungT.ex3_sel' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.FaserungT.ex3_sel

/-- info: 'Reformulation.Pfalzgraf.FaserungT.lok_vAt' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.FaserungT.lok_vAt

/-- info: 'Reformulation.Pfalzgraf.FaserungT.junk_als_trans' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.FaserungT.junk_als_trans

/-- info: 'Reformulation.Pfalzgraf.FaserungT.junk_als_trans_quot' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.FaserungT.junk_als_trans_quot

/-- info: 'Reformulation.Pfalzgraf.FaserungT.wertT_lokal' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.FaserungT.wertT_lokal

/-- info: 'Reformulation.Pfalzgraf.FaserungT.wertT_eins' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.FaserungT.wertT_eins

/-- info: 'Reformulation.Pfalzgraf.FaserungT.gueltigT1_eins' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.FaserungT.gueltigT1_eins

/-- info: 'Reformulation.Pfalzgraf.FaserungT.gueltigT2_eins' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.FaserungT.gueltigT2_eins

/-- info: 'Reformulation.Pfalzgraf.FaserungT.eich_E1' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.FaserungT.eich_E1

/-- info: 'Reformulation.Pfalzgraf.FaserungT.eich_E2' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.FaserungT.eich_E2

/-- info: 'Reformulation.Pfalzgraf.FaserungT.eich_E4' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.FaserungT.eich_E4
