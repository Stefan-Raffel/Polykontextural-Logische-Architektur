import Reformulation.Pfalzgraf.FaserungT
import Reformulation.Kaehr.Tableau

/-!
# Reformulation.Kaehr.TableauT — laa als Tableauregeln, das Tableau in zwei Schlussarten, Korrektheit und Unvollständigkeit

**Was das Modul ist (CLAUDE.md §4):** ERTRAG, Teil T von Rev11 (Modul B von zwei).  Gebaut nach
`KorpusRev2/Prompt_Instanz_T_Bau.md` (Mathematiker 24.10.2026, mit Custos' Prüfung §4, Auflagen A1–A3).  Rev10-Träger unberührt.

## TT1 · Die Herkünfte

```text
NACH BASHFORD/JOEMANN/KAEHR 1993   die Tableauregeln laa, aaa, n1, n2 (S. 64, PDF 68;  laa wörtlich nach Hermeneutes H2 b, am Bild;
                                   aaa, n1, n2 an der Textschicht von PDF 68, von der Instanz gelesen);  der Schluss-Begriff
                                   (§1.5, S. 23:  "{} /// <t1 .. tn> => der Beweis schliesst wenn auch alle t1 .. tn schliessen");
                                   "keine richtigen Betas" (S. 9).  laa ist DURCH SEINE REGELN definiert (H2 c).
NACH PFALZGRAF 1991                Muster + Verteilung, D_αβγδ (S. 181 f.) — über FaserungT (Modul A).
NACH KAEHR 1981                    die junktionalen Regeln und die Negator-Regeln, gebaut in Kaehr/Tableau (aesteA, negN₁, negN₂) und
                                   hier wiederverwendet.
                                   ddd:  NACH KAEHR 1981 (Kaehr/Tableau, aesteA opD) — nicht in 1993 S. 64;  vom Haus zum Fragment genommen.
                                   Eichung (A1 a):  aaa, n1, n2 von 1993 haben je Zeichen dieselben Alternativen wie die Regeln aus
                                   Kaehr/Tableau (`eich_aaa_1993`, `eich_n1_1993`, `eich_n2_1993`).
UNSER                              die Mengen-Semantik Σ1 (FaserungT), die Vertreter Va, Vb von laa, die Regelsemantik `haeltR`,
                                   der 1993-Schluss als Tableau-Lesart, alle Sätze.
```

Die „[]"-Plätze der laa-Regeln (S. 64) fallen fort:  für eine ALTERNATIVE ist es gleichgültig, ob „[]" neutral (Empty) oder
geschlossen ([]) gelesen wird — beide Lesarten der Quelle lassen die Alternative wegfallen (Horistes T_Drei_Saetze §4;  Mathematiker N2).
Erst wo T-Anteile konjunktiv verbunden werden — in den Termregeln — fallen die Lesarten auseinander;  die Termregeln baut dieses
Modul NICHT.

## TT2 · Die zwei Schlussarten (LESART DES HAUSES)

```text
gemeinsamer Ast   eine T-Alternative ist eine Verzweigung wie jede andere:  ihre Einträge kommen auf DENSELBEN Ast und schliessen
                  mit seinen Literalen.  (widerlegeT false)
1993-Schluss      eine T-Alternative wird als EIGENES Tableau ab leerem Ast geprüft ("keine richtigen Betas", S. 9;  S. 23 II):  sie
                  schliesst, wenn sie in sich schliesst oder der übrige Ast schliesst.  (widerlegeT true)
```

## TT3 · Was T beweist (Horistes T_Drei_Saetze §5, mit Custos A1 c)

*Gegen eine freie Semantik nach Pfalzgraf (S. 181 f.), in der ein verteilter Wert mit der Belegung seiner Zielfaser zusammentrifft,
sind die Tableauregeln laa, aaa, n1, n2 (Bashford, Joemann und Kaehr 1993, S. 64) und die Disjunktion ddd nach Kaehr 1981
**korrekt** unter D1 — gültig heißt: in keiner Faser falsch, was eine Faser ohne Wert einschließt —, für die zwei gerechneten
Vertreter von laa (`tableauT_korrekt`).  Sie sind dort **nicht vollständig**: eine gültige Formel der Größe 11, in keiner Faser
leer, ist nicht beweisbar (`tableauT_unvollstaendig`).  Beides hat einen Grund: die Regeln lesen die Vermittlung mit (in der
Quotientenlesung definieren sie genau eine Günther-Tafel, `eich_laa_quotient`), und dieser Überschuss macht sie gegen die freie
Lesung korrekt und unvollständig zugleich.  Die Semantik stammt vom Haus;  die Regeln hatten keine von ihnen unabhängige.*

Der Leer-Vorbehalt ist ein Satz:  `korrekt_leer` — eine beweisbare Formel der Größe 10 hat eine leere Faser und ist nicht D2-gültig;
„korrekt" lässt sich nicht zu D2 stärken.

**S-62** (`zwei_schlussarten`):  an einer Formel der Größe 13 schließt das Tableau mit gemeinsamem Ast und nicht mit dem
1993-Schluss — ein Fall der Wechselwirkung, die die Autoren 1993 S. 62 festhalten (beide Schlussarten in der Lesart des Hauses).
Und allgemein:  schließt der 1993-Schluss, so schließt der gemeinsame Ast (`schluss1993_gemeinsam`).

## TT4 · Was T nicht beweist

*Nichts über Günthers Werte: dort ist schon der junktionale Kalkül nicht korrekt (`nicht_V`).  Nichts über die Termregeln, die
Kaehr 2005 als unbewiesen nennt — sie haben die Gestalt der Unabhängigkeit, die die Autoren 1993 selbst zurücknahmen, und sind nicht
gebaut.  Nichts darüber, welche der zwei Fassungen der Schachtelungsregel im Bericht gilt (Regel 5 / Regel III).*  Nichts für
m > 3;  nichts über ttt (nur das Zeichen T1 ist belegt, S. 9).

**Verboten** (Horistes §5, ergänzt):  „Kaehrs Tableau ist korrekt";  „laa ist korrekt";  „die Regeln sind falsch / unvollständig"
ohne Bezugssystem;  „1993 hatte Unrecht";  „S. 62 bewiesen";  „Kaehrs ‚still waiting' beantwortet";  „Regel III ist ein Druckfehler";
„korrekt" ohne D1 und den Leer-Vorbehalt;  „erstmals".

## TT5 · Die Erhaltung

`beweisbarT_einK`:  auf einer Formel ohne laa liefert das Tableau in BEIDEN Schlussarten genau das Ergebnis von `widerlege`
(Kaehr/Tableau) — die Beweisbarkeit von Fm ist erhalten (`beweisbarT m (einK φ) = beweisbar φ`).  Ein Satz, keine Eichung.

## Die Sätze

```text
widerlegeT_none            FOLGERUNG:  geschlossen ⇒ keine Belegung erfüllt die Einträge unter Σ_R — beide Schlussarten
widerlegeT_some            FOLGERUNG:  offen (gemeinsamer Ast) ⇒ die Belegung erfüllt sie
schluss1993_gemeinsam      FOLGERUNG:  1993-Schluss geschlossen ⇒ gemeinsamer Ast geschlossen
laa_inklusion              Hilfssatz (decide):  jeder Σ1-Wert von laa ist eine Regelalternative, je Vertreter
sigma1_teil_R              Hilfssatz:  Σ1 ⊆ Σ_R
tableauT_korrekt   (S-K)   FOLGERUNG;  Semantik HAUS;  D1, Va/Vb, beide Schlussarten
korrekt_leer       (S-K-leer)  EICHUNG/FOLGERUNG:  der Leer-Vorbehalt als Satz
tableauT_unvollstaendig (S-U)  FOLGERUNG (Satz durch einen Zeugen)
zwei_schlussarten  (S-62)  SATZ über zwei Schlussarten;  Deutung LESART
beweisbarT_einK            FOLGERUNG:  Erhaltung der Beweisbarkeit
eich_laa_quotient          EICHUNG (r1 des Mathematikers):  Quotientenlesung der laa-Regeln = eine Günther-Tafel, einwertig
eich_aaa_1993, eich_n1_1993, eich_n2_1993   EICHUNG (Custos A1 a)
```

## TT6 · Bauweise, wo sie vom Prompt abweicht

```text
laa_inklusion   PUNKTWEISE statt an Wertmengen:  je Faser i, Zielfaser k, Werte x, y und Zeichen b (decide über nackte Quantoren,
                3·3·2·2·2 Fälle).  Trägt dasselbe, weil jede laa-Alternative nur EINE Faser liest (`passt`):  ein Σ1-Wert entsteht aus
                einem Paar (x, y) in einer Faser i, und dafür genügt die Alternative, die genau dieses Paar liest.
opP1            hier noch einmal definiert (dieselbe Tafel wie VKaehrProbe.opP1):  VKaehrProbe liegt im Target Probes, dieses Modul im
                Aggregat, und das Aggregat importiert keine Sonde.
haeltR          positiv und existenziell, eine Belegung für die ganze Formel;  im 1993-Schluss prüft das TABLEAU die T-Alternative ab
                leerem Ast — die Semantik dazu ist Σ_R selbst (Korrektheit genügt:  was ab leerem Ast schliesst, ist für JEDE Belegung
                unerfüllbar, `widerlegeT_none`).  Vollständigkeit nur für den gemeinsamen Ast (`widerlegeT_some`).
groesseK_pos    `cases φ <;> exact Nat.succ_pos _` statt `simp [groesseK]` — Fallstrick 21, als Differential gemessen (24.10.):  der
                Beweistext von Kaehr/Tableau `groesse_pos` (`cases φ <;> simp [groesse]`) ist dort [propext] und, wörtlich wiederholt unter
                `import Reformulation.Kaehr.TableauT`, [propext, Classical.choice, Quot.sound].
```

Gegenproben G1–G3 ausserhalb des Baums:  `KorpusRev2/T_Vorprobe_Skripte/Gegenproben_T_Bau.lean`.

Kein `sorry`, kein `Classical.choice`, kein `native_decide`, kein True-Feld.
-/

namespace Reformulation.Kaehr.TableauT

open Reformulation.Pfalzgraf Reformulation.Pfalzgraf.FaserungT
open Reformulation.Kaehr.Tableau (Lit liegt liegt_iff ausLits orElse orElse_none orElse_some aesteA aesteA_vollst aesteA_korr
  aesteA_gestalt erfuellt gestaltOK negN₁ negN₂ stimmt konsistent ausLits_stimmt bool_beq widerlege probiere eintraege
  groesse beweisbar schliesst Eintrag)

/-! ## Syntax, Regeln, Vertreter -/

/-- Formeln mit laa — laa hat keine Semantik ausser seinen Regeln -/
inductive FmK
  | var (n : ℕ)
  | neg₁ (a : FmK)
  | neg₂ (a : FmK)
  | junk (o0 o1 o2 : Op) (a b : FmK)
  | laa (a b : FmK)

/-- ein Literal einer Regel:  (Wert, System, linker Operand?) -/
abbrev RLit := Bool × Faser × Bool

/-- die LOKALEN Alternativen von laa, je Zeichen (Wert, System) — 1993 S. 64 wörtlich (H2 b) -/
def laaLokal : Bool → Faser → List (List RLit)
  | true, ⟨0, _⟩ => [[(true, 0, true), (true, 0, false)], [(true, 0, true), (false, 0, false)]]
  | false, ⟨0, _⟩ => [[(false, 0, true), (false, 0, false)]]
  | true, ⟨1, _⟩ => [[(true, 1, true), (true, 1, false)]]
  | false, ⟨1, _⟩ => [[(false, 1, true)], [(false, 1, false)]]
  | true, ⟨2, _⟩ => [[(true, 2, true), (true, 2, false)]]
  | false, ⟨2, _⟩ => [[(false, 2, true)], [(false, 2, false)]]

/-- die T-ANTEILE von laa, je Zeichen — 1993 S. 64 wörtlich (H2 b);  die "[]"-Plätze fallen fort -/
def laaT : Bool → Faser → List (List RLit)
  | _, ⟨0, _⟩ => []
  | true, ⟨1, _⟩ => [[(false, 0, true), (false, 0, false)]]
  | false, ⟨1, _⟩ => [[(false, 0, true), (true, 0, false)]]
  | true, ⟨2, _⟩ => [[(true, 0, true), (true, 0, false)]]
  | false, ⟨2, _⟩ => [[(false, 0, true), (true, 0, false)]]

/-- die zwei gerechneten Vertreter von laa in Σ1 -/
inductive LaaVertreter
  | Va
  | Vb

/-- die Projektion auf das erste Argument (dieselbe Tafel wie `VKaehrProbe.opP1`;  VKaehrProbe liegt im Target Probes und wird
    vom Aggregat nicht importiert) -/
def opP1 : Op := (true, true, false, false)
/-- die Verteilung der Faser 0:  die Zelle FT wandert nach Faser 1 (Va) bzw. 2 (Vb) -/
def dLaa : LaaVertreter → Vert
  | .Va => (0, 0, 1, 0)
  | .Vb => (0, 0, 2, 0)

/-- laa als Transjunktion, je Vertreter:  Faser 0 Projektion mit Verteilung, Fasern 1, 2 Konjunktion lokal -/
def zuT (V : LaaVertreter) : FmK → FmT
  | .var n => .var n
  | .neg₁ a => .neg₁ (zuT V a)
  | .neg₂ a => .neg₂ (zuT V a)
  | .junk o0 o1 o2 a b => .junk o0 o1 o2 (zuT V a) (zuT V b)
  | .laa a b => .trans opP1 opK opK (dLaa V) (lok 1) (lok 2) (zuT V a) (zuT V b)

/-! ## Σ_R — die Regelsemantik -/

/-- **Σ_R.**  "φ hat in Faser k den Wert b" nach den Regeln:  rekursiv durch die Alternativen (positiv) -/
def haeltR (f : FreieBelegung) : FmK → Faser → Bool → Bool
  | .var n, k, b => f n k == b
  | .neg₁ a, k, b => haeltR f a (negN₁ b k).1 (negN₁ b k).2
  | .neg₂ a, k, b => haeltR f a (negN₂ b k).1 (negN₂ b k).2
  | .junk o0 o1 o2 a c, k, b => (aesteA (oAt o0 o1 o2 k) b).any fun br =>
      br.all fun e => if e.2 then haeltR f a k e.1 else haeltR f c k e.1
  | .laa a c, k, b => (laaLokal b k ++ laaT b k).any fun alt =>
      alt.all fun l => if l.2.2 then haeltR f a l.2.1 l.1 else haeltR f c l.2.1 l.1

/-! ## Das Tableau -/

/-- ein Eintrag:  (Wert, Faser, Formel) -/
abbrev EintragK := Bool × Faser × FmK

def groesseK : FmK → ℕ
  | .var _ => 1
  | .neg₁ a => groesseK a + 1
  | .neg₂ a => groesseK a + 1
  | .junk _ _ _ a b => groesseK a + groesseK b + 1
  | .laa a b => groesseK a + groesseK b + 1

def massK : List EintragK → ℕ
  | [] => 0
  | (_, _, φ) :: r => groesseK φ + massK r

/-- die Einträge eines junktionalen Astes -/
def eintraegeA (i : Faser) (a c : FmK) (br : List (Bool × Bool)) : List EintragK :=
  br.map fun e => (e.1, i, if e.2 then a else c)
/-- die Einträge einer laa-Alternative -/
def eintraegeR (a c : FmK) (alt : List RLit) : List EintragK :=
  alt.map fun l => (l.1, l.2.1, if l.2.2 then a else c)

/-- die Äste nacheinander versuchen -/
def probiereL {β : Type} (w : List EintragK → Option FreieBelegung) (mk : β → List EintragK) :
    List β → Option FreieBelegung
  | [] => none
  | br :: bs => orElse (w (mk br)) (probiereL w mk bs)

/-- **das Tableau**, Schlussart `m` (false:  gemeinsamer Ast;  true:  1993-Schluss);  none = geschlossen -/
def widerlegeT (m : Bool) : ℕ → List Lit → List EintragK → Option FreieBelegung
  | _, ls, [] => some (ausLits ls)
  | 0, ls, _ :: _ => some (ausLits ls)
  | k + 1, ls, (s, i, .var n) :: r =>
      if liegt ls (n, i, !s) then none else widerlegeT m k ((n, i, s) :: ls) r
  | k + 1, ls, (s, i, .neg₁ a) :: r => widerlegeT m k ls (((negN₁ s i).2, (negN₁ s i).1, a) :: r)
  | k + 1, ls, (s, i, .neg₂ a) :: r => widerlegeT m k ls (((negN₂ s i).2, (negN₂ s i).1, a) :: r)
  | k + 1, ls, (s, i, .junk o0 o1 o2 a c) :: r =>
      probiereL (fun e => widerlegeT m k ls (e ++ r)) (eintraegeA i a c) (aesteA (oAt o0 o1 o2 i) s)
  | k + 1, ls, (s, i, .laa a c) :: r =>
      orElse (probiereL (fun e => widerlegeT m k ls (e ++ r)) (eintraegeR a c) (laaLokal s i))
        (probiereL (fun e => bif m then (bif (widerlegeT m k [] e).isNone then none else widerlegeT m k ls r)
                             else widerlegeT m k ls (e ++ r)) (eintraegeR a c) (laaT s i))

/-- je Faser:  das Tableau für (F, k, φ) schliesst -/
def schliesstT (m : Bool) (φ : FmK) (k : Faser) : Bool := (widerlegeT m (groesseK φ) [] [(false, k, φ)]).isNone
/-- beweisbar (H1-Fassung wie Kaehr/Tableau):  alle drei Fasern -/
def beweisbarT (m : Bool) (φ : FmK) : Bool := schliesstT m φ 0 && schliesstT m φ 1 && schliesstT m φ 2

/-! ## Hilfssätze -/

def haeltE (g : FreieBelegung) (e : EintragK) : Prop := haeltR g e.2.2 e.2.1 e.1 = true

theorem probiereL_none {β : Type} {w : List EintragK → Option FreieBelegung} {mk : β → List EintragK} :
    ∀ bs : List β, probiereL w mk bs = none → ∀ br ∈ bs, w (mk br) = none
  | [], _, br, hb => absurd hb List.not_mem_nil
  | b :: bs, h, br, hb => by
    rw [probiereL, orElse_none] at h
    rcases List.mem_cons.mp hb with rfl | hb
    · exact h.1
    · exact probiereL_none bs h.2 br hb

theorem probiereL_some {β : Type} {w : List EintragK → Option FreieBelegung} {mk : β → List EintragK} {g : FreieBelegung} :
    ∀ bs : List β, probiereL w mk bs = some g → ∃ br ∈ bs, w (mk br) = some g
  | [], h => by simp [probiereL] at h
  | b :: bs, h => by
    rcases orElse_some h with h | h
    · exact ⟨b, List.mem_cons_self, h⟩
    · obtain ⟨c, hc, hw⟩ := probiereL_some bs h; exact ⟨c, List.mem_cons_of_mem _ hc, hw⟩

theorem haeltE_eintraegeA (g : FreieBelegung) (i : Faser) (a c : FmK) : ∀ br : List (Bool × Bool),
    (∀ e ∈ eintraegeA i a c br, haeltE g e) ↔ br.all (fun e => if e.2 then haeltR g a i e.1 else haeltR g c i e.1) = true
  | [] => by simp [eintraegeA]
  | (v, l) :: br => by
    have ih := haeltE_eintraegeA g i a c br
    have hc : eintraegeA i a c ((v, l) :: br) = (v, i, if l then a else c) :: eintraegeA i a c br := rfl
    rw [hc, List.all_cons, Bool.and_eq_true, ← ih]
    constructor
    · intro h
      refine ⟨?_, fun e he => h e (List.mem_cons_of_mem _ he)⟩
      have := h _ List.mem_cons_self
      cases l <;> exact this
    · rintro ⟨h1, h2⟩ e he
      rcases List.mem_cons.mp he with rfl | he
      · cases l <;> exact h1
      · exact h2 e he

theorem haeltE_eintraegeR (g : FreieBelegung) (a c : FmK) : ∀ alt : List RLit,
    (∀ e ∈ eintraegeR a c alt, haeltE g e) ↔
      alt.all (fun l => if l.2.2 then haeltR g a l.2.1 l.1 else haeltR g c l.2.1 l.1) = true
  | [] => by simp [eintraegeR]
  | (v, j, l) :: alt => by
    have ih := haeltE_eintraegeR g a c alt
    have hc : eintraegeR a c ((v, j, l) :: alt) = (v, j, if l then a else c) :: eintraegeR a c alt := rfl
    rw [hc, List.all_cons, Bool.and_eq_true, ← ih]
    constructor
    · intro h
      refine ⟨?_, fun e he => h e (List.mem_cons_of_mem _ he)⟩
      have := h _ List.mem_cons_self
      cases l <;> exact this
    · rintro ⟨h1, h2⟩ e he
      rcases List.mem_cons.mp he with rfl | he
      · cases l <;> exact h1
      · exact h2 e he

/-! ## Korrektheit des Tableaus gegen Σ_R — beide Schlussarten -/

/-- **geschlossen ⇒ unerfüllbar unter Σ_R**, in beiden Schlussarten -/
theorem widerlegeT_none (m : Bool) :
    ∀ k ls todo, widerlegeT m k ls todo = none →
      ∀ g, (∀ l ∈ ls, stimmt g l) → (∀ e ∈ todo, haeltE g e) → False := by
  intro k
  induction k with
  | zero =>
    intro ls todo h; cases todo with
    | nil => simp [widerlegeT] at h
    | cons e r => simp [widerlegeT] at h
  | succ k ih =>
    intro ls todo h g hl he
    match todo with
    | [] => simp [widerlegeT] at h
    | (s, i, .var n) :: r =>
      simp only [widerlegeT] at h
      split at h
      · rename_i hc
        have h1 := hl _ ((liegt_iff _ _).mp hc)
        have h2 := he _ List.mem_cons_self
        simp only [stimmt, haeltE, haeltR] at h1 h2
        rw [h1] at h2; cases s <;> simp at h2
      · refine ih _ _ h g ?_ (fun e he' => he e (List.mem_cons_of_mem _ he'))
        intro l hl'
        rcases List.mem_cons.mp hl' with rfl | hl'
        · have := he _ List.mem_cons_self
          simp only [haeltE, haeltR] at this
          exact (bool_beq _ _).mp this
        · exact hl l hl'
    | (s, i, .neg₁ a) :: r =>
      simp only [widerlegeT] at h
      refine ih _ _ h g hl ?_
      intro e he'
      rcases List.mem_cons.mp he' with rfl | he'
      · have h0 := he (s, i, .neg₁ a) List.mem_cons_self; simp only [haeltE, haeltR] at h0 ⊢; exact h0
      · exact he e (List.mem_cons_of_mem _ he')
    | (s, i, .neg₂ a) :: r =>
      simp only [widerlegeT] at h
      refine ih _ _ h g hl ?_
      intro e he'
      rcases List.mem_cons.mp he' with rfl | he'
      · have h0 := he (s, i, .neg₂ a) List.mem_cons_self; simp only [haeltE, haeltR] at h0 ⊢; exact h0
      · exact he e (List.mem_cons_of_mem _ he')
    | (s, i, .junk o0 o1 o2 a c) :: r =>
      simp only [widerlegeT] at h
      have h0 : haeltR g (.junk o0 o1 o2 a c) i s = true := he _ List.mem_cons_self
      simp only [haeltR] at h0
      obtain ⟨br, hbr, hall⟩ := List.any_eq_true.mp h0
      have hw := probiereL_none _ h br hbr
      refine ih _ _ hw g hl ?_
      intro e he'
      rcases List.mem_append.mp he' with he' | he'
      · exact ((haeltE_eintraegeA g i a c br).mpr hall) e he'
      · exact he e (List.mem_cons_of_mem _ he')
    | (s, i, .laa a c) :: r =>
      simp only [widerlegeT] at h
      have h0 : haeltR g (.laa a c) i s = true := he _ List.mem_cons_self
      simp only [haeltR] at h0
      obtain ⟨alt, halt, hall⟩ := List.any_eq_true.mp h0
      have hents := (haeltE_eintraegeR g a c alt).mpr hall
      have hrest : ∀ e ∈ r, haeltE g e := fun e he' => he e (List.mem_cons_of_mem _ he')
      rw [orElse_none] at h
      rcases List.mem_append.mp halt with halt | halt
      · have hw := probiereL_none _ h.1 alt halt
        refine ih _ _ hw g hl ?_
        intro e he'
        rcases List.mem_append.mp he' with he' | he'
        · exact hents e he'
        · exact hrest e he'
      · have hw := probiereL_none _ h.2 alt halt
        cases m with
        | false =>
          refine ih _ _ hw g hl ?_
          intro e he'
          rcases List.mem_append.mp he' with he' | he'
          · exact hents e he'
          · exact hrest e he'
        | true =>
          cases hf : (widerlegeT true k [] (eintraegeR a c alt)).isNone with
          | true =>
            exact ih [] _ (Option.isNone_iff_eq_none.mp hf) g (fun l hl' => absurd hl' List.not_mem_nil) hents
          | false =>
            simp only [hf, cond_true, cond_false] at hw
            exact ih _ _ hw g hl hrest

/-! ## Vollständigkeit des Tableaus gegen Σ_R — gemeinsamer Ast -/

theorem groesseK_pos (φ : FmK) : 0 < groesseK φ := by cases φ <;> exact Nat.succ_pos _

theorem massK_append : ∀ l1 l2 : List EintragK, massK (l1 ++ l2) = massK l1 + massK l2
  | [], l2 => by show massK l2 = 0 + massK l2; omega
  | (s, i, φ) :: l, l2 => by
    show groesseK φ + massK (l ++ l2) = groesseK φ + massK l + massK l2
    rw [massK_append l l2]; omega

theorem massK_eintraegeA (i : Faser) (a c : FmK) :
    ∀ br, gestaltOK br = true → massK (eintraegeA i a c br) ≤ groesseK a + groesseK c
  | [(_, true)], _ => by show groesseK a + 0 ≤ _; omega
  | [(_, false)], _ => by show groesseK c + 0 ≤ _; omega
  | [(_, true), (_, false)], _ => by show groesseK a + (groesseK c + 0) ≤ _; omega
  | [], h => absurd h (by decide)
  | [(_, false), (_, _)], h => by simp only [gestaltOK] at h; exact absurd h (by decide)
  | [(_, true), (_, true)], h => by simp only [gestaltOK] at h; exact absurd h (by decide)
  | _ :: _ :: _ :: _, h => by simp only [gestaltOK] at h; exact absurd h (by decide)

/-- die Gestalt einer laa-Alternative:  höchstens ein linker und ein rechter Eintrag, in dieser Reihenfolge -/
def gestaltR : List RLit → Bool
  | [(_, _, true)] => true | [(_, _, false)] => true | [(_, _, true), (_, _, false)] => true | _ => false

theorem laa_gestalt : ∀ (s : Bool) (i : Faser), (laaLokal s i ++ laaT s i).all gestaltR = true := by decide

theorem massK_eintraegeR (a c : FmK) :
    ∀ alt, gestaltR alt = true → massK (eintraegeR a c alt) ≤ groesseK a + groesseK c
  | [(_, _, true)], _ => by show groesseK a + 0 ≤ _; omega
  | [(_, _, false)], _ => by show groesseK c + 0 ≤ _; omega
  | [(_, _, true), (_, _, false)], _ => by show groesseK a + (groesseK c + 0) ≤ _; omega
  | [], h => absurd h (by decide)
  | [(_, _, false), (_, _, _)], h => by simp only [gestaltR] at h; exact absurd h (by decide)
  | [(_, _, true), (_, _, true)], h => by simp only [gestaltR] at h; exact absurd h (by decide)
  | _ :: _ :: _ :: _, h => by simp only [gestaltR] at h; exact absurd h (by decide)

/-- **offen ⇒ erfüllt**, gemeinsamer Ast -/
theorem widerlegeT_some :
    ∀ k ls todo g, massK todo ≤ k → konsistent ls → widerlegeT false k ls todo = some g →
      (∀ l ∈ ls, stimmt g l) ∧ (∀ e ∈ todo, haeltE g e) := by
  intro k
  induction k with
  | zero =>
    intro ls todo g hm hk h
    match todo with
    | [] => simp only [widerlegeT, Option.some.injEq] at h; subst h; exact ⟨ausLits_stimmt ls hk, by simp⟩
    | (_, _, φ) :: _ => exfalso; have := groesseK_pos φ; simp only [massK] at hm; omega
  | succ k ih =>
    intro ls todo g hm hk h
    match todo with
    | [] => simp only [widerlegeT, Option.some.injEq] at h; subst h; exact ⟨ausLits_stimmt ls hk, by simp⟩
    | (s, i, .var n) :: r =>
      simp only [widerlegeT] at h
      split at h
      · simp at h
      · rename_i hc
        have hk' : konsistent ((n, i, s) :: ls) := by
          intro a b c m1 m2
          rcases List.mem_cons.mp m1 with e1 | e1 <;> rcases List.mem_cons.mp m2 with e2 | e2
          · simp only [Prod.mk.injEq] at e1 e2
            obtain ⟨rfl, rfl, rfl⟩ := e1
            cases c <;> simp at e2
          · simp only [Prod.mk.injEq] at e1
            obtain ⟨rfl, rfl, rfl⟩ := e1
            apply hc; rw [liegt_iff]; exact e2
          · simp only [Prod.mk.injEq] at e2
            obtain ⟨rfl, rfl, hc'⟩ := e2
            have : c = !s := by rw [← hc']; simp
            subst this
            apply hc; rw [liegt_iff]; exact e1
          · exact hk a b c e1 e2
        have hm' : massK r ≤ k := by simp [massK, groesseK] at hm; omega
        obtain ⟨hl, he⟩ := ih _ _ g hm' hk' h
        refine ⟨fun l h' => hl l (List.mem_cons_of_mem _ h'), ?_⟩
        intro e he'
        rcases List.mem_cons.mp he' with rfl | he'
        · have := hl _ List.mem_cons_self
          simp only [stimmt] at this
          show haeltR g (.var n) i s = true
          simp only [haeltR, this]; exact (bool_beq s s).mpr rfl
        · exact he e he'
    | (s, i, .neg₁ a) :: r =>
      simp only [widerlegeT] at h
      have hm' : massK (((negN₁ s i).2, (negN₁ s i).1, a) :: r) ≤ k := by simp [massK, groesseK] at hm ⊢; omega
      obtain ⟨hl, he⟩ := ih _ _ g hm' hk h
      refine ⟨hl, ?_⟩
      intro e he'
      rcases List.mem_cons.mp he' with rfl | he'
      · have h0 := he ((negN₁ s i).2, (negN₁ s i).1, a) List.mem_cons_self; simp only [haeltE, haeltR] at h0 ⊢; exact h0
      · exact he e (List.mem_cons_of_mem _ he')
    | (s, i, .neg₂ a) :: r =>
      simp only [widerlegeT] at h
      have hm' : massK (((negN₂ s i).2, (negN₂ s i).1, a) :: r) ≤ k := by simp [massK, groesseK] at hm ⊢; omega
      obtain ⟨hl, he⟩ := ih _ _ g hm' hk h
      refine ⟨hl, ?_⟩
      intro e he'
      rcases List.mem_cons.mp he' with rfl | he'
      · have h0 := he ((negN₂ s i).2, (negN₂ s i).1, a) List.mem_cons_self; simp only [haeltE, haeltR] at h0 ⊢; exact h0
      · exact he e (List.mem_cons_of_mem _ he')
    | (s, i, .junk o0 o1 o2 a c) :: r =>
      simp only [widerlegeT] at h
      obtain ⟨br, hbr, hw⟩ := probiereL_some _ h
      have hm' : massK (eintraegeA i a c br ++ r) ≤ k := by
        rw [massK_append]
        have := massK_eintraegeA i a c br (aesteA_gestalt _ _ br hbr)
        simp only [massK, groesseK] at hm; omega
      obtain ⟨hl, he⟩ := ih _ _ g hm' hk hw
      refine ⟨hl, ?_⟩
      have hall := (haeltE_eintraegeA g i a c br).mp (fun e h' => he e (List.mem_append_left _ h'))
      intro e he'
      rcases List.mem_cons.mp he' with rfl | he'
      · show haeltR g (.junk o0 o1 o2 a c) i s = true
        simp only [haeltR]
        exact List.any_eq_true.mpr ⟨br, hbr, hall⟩
      · exact he e (List.mem_append_right _ he')
    | (s, i, .laa a c) :: r =>
      simp only [widerlegeT] at h
      have key : ∃ alt ∈ laaLokal s i ++ laaT s i, widerlegeT false k ls (eintraegeR a c alt ++ r) = some g := by
        rcases orElse_some h with h | h
        · obtain ⟨alt, ha, hw⟩ := probiereL_some _ h
          exact ⟨alt, List.mem_append_left _ ha, hw⟩
        · obtain ⟨alt, ha, hw⟩ := probiereL_some _ h
          exact ⟨alt, List.mem_append_right _ ha, by simpa only [cond_false] using hw⟩
      obtain ⟨alt, halt, hw⟩ := key
      have hm' : massK (eintraegeR a c alt ++ r) ≤ k := by
        rw [massK_append]
        have := massK_eintraegeR a c alt (all_mp (laa_gestalt s i) alt halt)
        simp only [massK, groesseK] at hm; omega
      obtain ⟨hl, he⟩ := ih _ _ g hm' hk hw
      refine ⟨hl, ?_⟩
      have hall := (haeltE_eintraegeR g a c alt).mp (fun e h' => he e (List.mem_append_left _ h'))
      intro e he'
      rcases List.mem_cons.mp he' with rfl | he'
      · show haeltR g (.laa a c) i s = true
        simp only [haeltR]
        exact List.any_eq_true.mpr ⟨alt, halt, hall⟩
      · exact he e (List.mem_append_right _ he')

/-- schliesst das Tableau (Schlussart m), so ist F_k φ unter Σ_R unerfüllbar -/
theorem schliesstT_korrekt (m : Bool) (φ : FmK) (k : Faser) (h : schliesstT m φ k = true) :
    ∀ g, haeltR g φ k false = false := by
  intro g
  cases hg : haeltR g φ k false
  · rfl
  · exact (widerlegeT_none m _ _ _ (Option.isNone_iff_eq_none.mp h) g (fun l hl => absurd hl List.not_mem_nil)
      (fun e he => by rcases List.mem_singleton.mp he with rfl; exact hg)).elim

/-- ist F_k φ unter Σ_R unerfüllbar, so schliesst das Tableau mit gemeinsamem Ast -/
theorem schliesstT_vollst (φ : FmK) (k : Faser) (h : ∀ g, haeltR g φ k false = false) : schliesstT false φ k = true := by
  unfold schliesstT
  cases hw : widerlegeT false (groesseK φ) [] [(false, k, φ)] with
  | none => rfl
  | some g =>
    have := (widerlegeT_some _ _ _ g (by simp [massK]) (by simp [konsistent]) hw).2 _ List.mem_cons_self
    have h' := h g
    simp only [haeltE] at this
    rw [h'] at this; exact absurd this (by decide)

/-- **schliesst der 1993-Schluss, so schliesst der gemeinsame Ast** -/
theorem schluss1993_gemeinsam (φ : FmK) (k : Faser) (h : schliesstT true φ k = true) : schliesstT false φ k = true :=
  schliesstT_vollst φ k (schliesstT_korrekt true φ k h)

/-! ## Σ1 ⊆ Σ_R -/

theorem ex2_true {P : Bool → Bool → Bool} (h : ex2 P = true) : ∃ x y, P x y = true := by
  unfold ex2 at h
  cases h1 : P true true
  · cases h2 : P true false
    · cases h3 : P false true
      · cases h4 : P false false
        · simp [h1, h2, h3, h4] at h
        · exact ⟨false, false, h4⟩
      · exact ⟨false, true, h3⟩
    · exact ⟨true, false, h2⟩
  · exact ⟨true, true, h1⟩

theorem ex3_true {P : Faser → Bool} (h : ex3 P = true) : ∃ i, P i = true := by
  unfold ex3 at h
  cases h1 : P 0
  · cases h2 : P 1
    · cases h3 : P 2
      · simp [h1, h2, h3] at h
      · exact ⟨2, h3⟩
    · exact ⟨1, h2⟩
  · exact ⟨0, h1⟩

/-- die Einschlussbedingung als Bool, je Zelle:  eine Alternative der Regel liest genau Faser i mit den Werten x, y -/
def passt (i : Faser) (x y : Bool) (alt : List RLit) : Bool :=
  alt.all fun l => fbeq l.2.1 i && (l.1 == if l.2.2 then x else y)

/-- **lokale Inklusion** (decide):  jeder Σ1-Wert von laa ist eine Regelalternative — Va -/
theorem laa_inklusion_Va : ∀ (i k : Faser) (x y b : Bool),
    (fbeq (apV (vAt (dLaa .Va) (lok 1) (lok 2) i) x y) k && (ap (oAt opP1 opK opK i) x y == b)) = true →
      (laaLokal b k ++ laaT b k).any (passt i x y) = true := by
  decide

/-- **lokale Inklusion** (decide) — Vb -/
theorem laa_inklusion_Vb : ∀ (i k : Faser) (x y b : Bool),
    (fbeq (apV (vAt (dLaa .Vb) (lok 1) (lok 2) i) x y) k && (ap (oAt opP1 opK opK i) x y == b)) = true →
      (laaLokal b k ++ laaT b k).any (passt i x y) = true := by
  decide

theorem laa_inklusion (V : LaaVertreter) : ∀ (i k : Faser) (x y b : Bool),
    (fbeq (apV (vAt (dLaa V) (lok 1) (lok 2) i) x y) k && (ap (oAt opP1 opK opK i) x y == b)) = true →
      (laaLokal b k ++ laaT b k).any (passt i x y) = true := by
  cases V
  · exact laa_inklusion_Va
  · exact laa_inklusion_Vb

theorem fbeq_eq {i j : Faser} (h : fbeq i j = true) : i = j := Fin.ext (Nat.eq_of_beq_eq_true h)

theorem passt_haelt (f : FreieBelegung) (a c : FmK) (i : Faser) (x y : Bool)
    (ha : haeltR f a i x = true) (hc : haeltR f c i y = true) :
    ∀ alt : List RLit, passt i x y alt = true →
      alt.all (fun l => if l.2.2 then haeltR f a l.2.1 l.1 else haeltR f c l.2.1 l.1) = true
  | [], _ => rfl
  | (v, j, l) :: alt, h => by
    simp only [passt, List.all_cons, Bool.and_eq_true] at h ⊢
    obtain ⟨⟨hj, hv⟩, hr⟩ := h
    refine ⟨?_, passt_haelt f a c i x y ha hc alt hr⟩
    rw [fbeq_eq hj]
    cases l
    · have : v = y := ((bool_beq v y).mp hv); subst this; exact hc
    · have : v = x := ((bool_beq v x).mp hv); subst this; exact ha

theorem erfuellt_haelt (f : FreieBelegung) (a c : FmK) (k : Faser) (x y : Bool)
    (ha : haeltR f a k x = true) (hc : haeltR f c k y = true) :
    ∀ br : List (Bool × Bool), erfuellt x y br = true →
      br.all (fun e => if e.2 then haeltR f a k e.1 else haeltR f c k e.1) = true
  | [], _ => rfl
  | (v, l) :: br, h => by
    simp only [erfuellt, List.all_cons, Bool.and_eq_true] at h ⊢
    refine ⟨?_, erfuellt_haelt f a c k x y ha hc br h.2⟩
    cases l
    · have : v = y := ((bool_beq y v).mp h.1).symm; subst this; exact hc
    · have : v = x := ((bool_beq x v).mp h.1).symm; subst this; exact ha

/-- **Σ1 ⊆ Σ_R:**  jeder Wert der freien Semantik ist ein Wert der Regelsemantik, je Vertreter -/
theorem sigma1_teil_R (V : LaaVertreter) (f : FreieBelegung) :
    ∀ (φ : FmK) (k : Faser) (b : Bool), wertT f (zuT V φ) k b = true → haeltR f φ k b = true
  | .var _, _, _, h => h
  | .neg₁ a, ⟨0, _⟩, b, h => sigma1_teil_R V f a 0 (!b) h
  | .neg₁ a, ⟨1, _⟩, b, h => sigma1_teil_R V f a 2 b h
  | .neg₁ a, ⟨2, _⟩, b, h => sigma1_teil_R V f a 1 b h
  | .neg₂ a, ⟨0, _⟩, b, h => sigma1_teil_R V f a 2 b h
  | .neg₂ a, ⟨1, _⟩, b, h => sigma1_teil_R V f a 1 (!b) h
  | .neg₂ a, ⟨2, _⟩, b, h => sigma1_teil_R V f a 0 b h
  | .junk o0 o1 o2 a c, k, b, h => by
    simp only [zuT, wertT] at h
    obtain ⟨x, y, hxy⟩ := ex2_true h
    simp only [Bool.and_eq_true] at hxy
    obtain ⟨⟨hx, hy⟩, hap⟩ := hxy
    have ha := sigma1_teil_R V f a k x hx
    have hc := sigma1_teil_R V f c k y hy
    obtain ⟨br, hbr, herf⟩ := aesteA_vollst (oAt o0 o1 o2 k) b x y ((bool_beq _ _).mp hap)
    simp only [haeltR]
    exact List.any_eq_true.mpr ⟨br, hbr, erfuellt_haelt f a c k x y ha hc br herf⟩
  | .laa a c, k, b, h => by
    simp only [zuT, wertT] at h
    obtain ⟨i, hi⟩ := ex3_true h
    obtain ⟨x, y, hxy⟩ := ex2_true hi
    simp only [Bool.and_eq_true] at hxy
    obtain ⟨⟨⟨hx, hy⟩, hk⟩, hap⟩ := hxy
    have ha := sigma1_teil_R V f a i x hx
    have hc := sigma1_teil_R V f c i y hy
    have hin := laa_inklusion V i k x y b (by rw [hk, hap]; rfl)
    obtain ⟨alt, halt, hp⟩ := List.any_eq_true.mp hin
    simp only [haeltR]
    exact List.any_eq_true.mpr ⟨alt, halt, passt_haelt f a c i x y ha hc alt hp⟩

/-! ## S-K — Korrektheit -/

/-- **S-K.**  Die Tableauregeln laa, aaa, n1, n2 (1993, S. 64) und die Disjunktion ddd nach Kaehr 1981 sind gegen Σ1 unter D1
    korrekt — gültig heißt:  in keiner Faser falsch, was eine Faser ohne Wert einschließt —, für die Vertreter Va und Vb von laa,
    in beiden Schlussarten.  Semantik HAUS. -/
theorem tableauT_korrekt (m : Bool) (V : LaaVertreter) (φ : FmK) (h : beweisbarT m φ = true) : gueltigT1 (zuT V φ) := by
  intro f k
  have hk : schliesstT m φ k = true := by
    simp only [beweisbarT, Bool.and_eq_true] at h
    match k with
    | ⟨0, _⟩ => exact h.1.1
    | ⟨1, _⟩ => exact h.1.2
    | ⟨2, _⟩ => exact h.2
  cases hw : wertT f (zuT V φ) k false
  · rfl
  · have := sigma1_teil_R V f φ k false hw
    rw [schliesstT_korrekt m φ k hk f] at this
    exact absurd this (by decide)

/-! ## Die Zeugen -/

/-- p -/
abbrev pK : FmK := .var 0
/-- Konjunktion je Faser (1993 aaa) -/
abbrev aaa (a b : FmK) : FmK := .junk opK opK opK a b
/-- Disjunktion je Faser (Kaehr 1981, nicht 1993 S. 64) -/
abbrev ddd (a b : FmK) : FmK := .junk opD opD opD a b

/-- (p ddd (n1(p) ddd n2((p laa n1(p))))) — Grösse 10 -/
def phiLeer : FmK := ddd pK (ddd (.neg₁ pK) (.neg₂ (.laa pK (.neg₁ pK))))
/-- (p ddd n1(n2(((p ddd n1(p)) laa n2(p))))) — Grösse 11 -/
def phiU : FmK := ddd pK (.neg₁ (.neg₂ (.laa (ddd pK (.neg₁ pK)) (.neg₂ pK))))
/-- (p ddd n1(n2(((p ddd n1(p)) laa (p aaa n2(p)))))) — Grösse 13 -/
def phi62 : FmK := ddd pK (.neg₁ (.neg₂ (.laa (ddd pK (.neg₁ pK)) (aaa pK (.neg₂ pK)))))

theorem groessen : groesseK phiLeer = 10 ∧ groesseK phiU = 11 ∧ groesseK phi62 = 13 := by decide

theorem eins_Leer (V : LaaVertreter) : (varsT (zuT V phiLeer)).all (fun n => Nat.beq n 0) = true := by cases V <;> decide
theorem eins_U (V : LaaVertreter) : (varsT (zuT V phiU)).all (fun n => Nat.beq n 0) = true := by cases V <;> decide
theorem eins_62 (V : LaaVertreter) : (varsT (zuT V phi62)).all (fun n => Nat.beq n 0) = true := by cases V <;> decide

/-- **S-K-leer.**  Der Vorbehalt als Satz:  `phiLeer` ist beweisbar (gemeinsamer Ast), also D1-gültig (S-K), hat eine leere Faser
    und ist NICHT D2-gültig — für Va und Vb.  "korrekt" lässt sich nicht zu D2 stärken. -/
theorem korrekt_leer (V : LaaVertreter) :
    beweisbarT false phiLeer = true ∧ gueltigT1 (zuT V phiLeer) ∧
    (∃ f k, leer f (zuT V phiLeer) k) ∧ ¬ gueltigT2 (zuT V phiLeer) := by
  have hb : beweisbarT false phiLeer = true := by decide
  have hw : ∃ b0 b1 b2 : Bool, ∃ k : Faser,
      wertT (fun _ => vec b0 b1 b2) (zuT V phiLeer) k true = false ∧
      wertT (fun _ => vec b0 b1 b2) (zuT V phiLeer) k false = false := by cases V <;> decide
  obtain ⟨b0, b1, b2, k, h1, h2⟩ := hw
  exact ⟨hb, tableauT_korrekt false V phiLeer hb, ⟨_, k, h1, h2⟩, fun h => by rw [h _ k] at h1; exact absurd h1 (by decide)⟩

/-- **S-U.**  Unvollständigkeit:  `phiU` ist gegen Σ1 unter D1 UND D2 gültig, in keiner Faser leer, und nicht beweisbar —
    für Va und Vb, in beiden Schlussarten. -/
theorem tableauT_unvollstaendig (m : Bool) (V : LaaVertreter) :
    gueltigT1 (zuT V phiU) ∧ gueltigT2 (zuT V phiU) ∧ (∀ f k, ¬ leer f (zuT V phiU) k) ∧ beweisbarT m phiU = false := by
  have h2 : gueltigT2 (zuT V phiU) := gueltigT2_eins _ (eins_U V) (by cases V <;> decide)
  refine ⟨gueltigT1_eins _ (eins_U V) (by cases V <;> decide), h2, fun f k hl => ?_, by cases m <;> decide⟩
  have := hl.1; rw [h2 f k] at this; exact absurd this (by decide)

/-- **S-U**, als Existenzsatz -/
theorem tableauT_unvollstaendig_ex (m : Bool) (V : LaaVertreter) :
    ∃ φ : FmK, gueltigT1 (zuT V φ) ∧ gueltigT2 (zuT V φ) ∧ (∀ f k, ¬ leer f (zuT V φ) k) ∧ beweisbarT m φ = false :=
  ⟨phiU, tableauT_unvollstaendig m V⟩

/-- **S-62.**  An einer Formel der Grösse 13 schliesst das Tableau mit gemeinsamem Ast und NICHT mit dem 1993-Schluss;  sie ist
    D1- und D2-gültig, für Va und Vb.  Deutung (LESART):  ein Fall der Wechselwirkung, die die Autoren 1993 S. 62 festhalten. -/
theorem zwei_schlussarten (V : LaaVertreter) :
    beweisbarT false phi62 = true ∧ beweisbarT true phi62 = false ∧ gueltigT1 (zuT V phi62) ∧ gueltigT2 (zuT V phi62) := by
  have hb : beweisbarT false phi62 = true := by decide
  exact ⟨hb, by decide, tableauT_korrekt false V phi62 hb, gueltigT2_eins _ (eins_62 V) (by cases V <;> decide)⟩

/-! ## Erhaltung der Beweisbarkeit -/

/-- die Einbettung der Formeln von Faserung -/
def einK : Fm → FmK
  | .var n => .var n
  | .neg₁ a => .neg₁ (einK a)
  | .neg₂ a => .neg₂ (einK a)
  | .junk o0 o1 o2 a b => .junk o0 o1 o2 (einK a) (einK b)

def einE (e : Eintrag) : EintragK := (e.1, e.2.1, einK e.2.2)

theorem groesse_einK : ∀ φ : Fm, groesseK (einK φ) = groesse φ
  | .var _ => rfl
  | .neg₁ a => by simp only [einK, groesseK, groesse, groesse_einK a]
  | .neg₂ a => by simp only [einK, groesseK, groesse, groesse_einK a]
  | .junk _ _ _ a b => by simp only [einK, groesseK, groesse, groesse_einK a, groesse_einK b]

theorem eintraege_einK (i : Faser) (a c : Fm) :
    ∀ br, eintraegeA i (einK a) (einK c) br = (eintraege i a c br).map einE
  | [] => rfl
  | (v, l) :: br => by
    show (v, i, if l then einK a else einK c) :: eintraegeA i (einK a) (einK c) br =
      einE (v, i, if l then a else c) :: (eintraege i a c br).map einE
    rw [eintraege_einK i a c br]; cases l <;> rfl

theorem probiere_einK (w : List Eintrag → Option FreieBelegung) (w' : List EintragK → Option FreieBelegung)
    (i : Faser) (a c : Fm) (hw : ∀ br, w' ((eintraege i a c br).map einE) = w (eintraege i a c br)) :
    ∀ bs, probiereL w' (eintraegeA i (einK a) (einK c)) bs = probiere w i a c bs
  | [] => rfl
  | br :: bs => by
    simp only [probiereL, probiere]
    rw [eintraege_einK, hw br, probiere_einK w w' i a c hw bs]

/-- auf Formeln ohne laa ist das Tableau — in beiden Schlussarten — das Tableau von Kaehr/Tableau -/
theorem widerlegeT_einK (m : Bool) :
    ∀ k ls todo, widerlegeT m k ls (todo.map einE) = widerlege k ls todo := by
  intro k
  induction k with
  | zero => intro ls todo; cases todo <;> rfl
  | succ k ih =>
    intro ls todo
    match todo with
    | [] => rfl
    | (s, i, .var n) :: r =>
      show (if liegt ls (n, i, !s) then none else widerlegeT m k ((n, i, s) :: ls) (r.map einE)) =
        (if liegt ls (n, i, !s) then none else widerlege k ((n, i, s) :: ls) r)
      rw [ih]
    | (s, i, .neg₁ a) :: r =>
      show widerlegeT m k ls (einE ((negN₁ s i).2, (negN₁ s i).1, a) :: r.map einE) = _
      rw [← List.map_cons, ih]; rfl
    | (s, i, .neg₂ a) :: r =>
      show widerlegeT m k ls (einE ((negN₂ s i).2, (negN₂ s i).1, a) :: r.map einE) = _
      rw [← List.map_cons, ih]; rfl
    | (s, i, .junk o0 o1 o2 a c) :: r =>
      show probiereL (fun e => widerlegeT m k ls (e ++ r.map einE)) (eintraegeA i (einK a) (einK c))
          (aesteA (oAt o0 o1 o2 i) s) = probiere (fun e => widerlege k ls (e ++ r)) i a c (aesteA (oAt o0 o1 o2 i) s)
      apply probiere_einK
      intro br
      rw [← List.map_append, ih]

/-- **Erhaltung der Beweisbarkeit:**  für eine Formel ohne laa ist `beweisbarT` (beide Schlussarten) Kaehrs `beweisbar` -/
theorem beweisbarT_einK (m : Bool) (φ : Fm) : beweisbarT m (einK φ) = beweisbar φ := by
  have h : ∀ k : Faser, schliesstT m (einK φ) k = schliesst φ k := by
    intro k
    unfold schliesstT schliesst
    rw [groesse_einK]
    exact congrArg Option.isNone (widerlegeT_einK m (groesse φ) [] [(false, k, φ)])
  simp only [beweisbarT, beweisbar, h]

/-! ## Eichungen -/

/-- die Quotientenlesung eines Regel-Literals:  "der globale Wert des Operanden liegt in L_s und ist dort b" -/
def gilt_quot (a b : Wert) (l : RLit) : Bool :=
  let v := if l.2.2 then a else b
  liest l.2.1 v && Nat.beq (global l.2.1 l.1).val v.val
/-- das Zeichen (s, k) von laa gilt in der Quotientenlesung an der Zelle (a, b) -/
def laaQ (s : Bool) (k : Faser) (a b : Wert) : Bool := (laaLokal s k ++ laaT s k).any fun alt => alt.all (gilt_quot a b)
/-- Günthers Tafel [[1, 1, 3], [3, 2, 3], [3, 3, 3]], in Lean-Zählung -/
def laaTafel : Wert → Wert → Wert
  | ⟨0, _⟩, ⟨0, _⟩ => 0 | ⟨0, _⟩, ⟨1, _⟩ => 0 | ⟨1, _⟩, ⟨1, _⟩ => 1 | _, _ => 2

/-- **Eichung r1** (Mathematiker, Antwort F1–F4 §5 b):  in der Quotientenlesung gilt an jeder Zelle mindestens ein Zeichen, und jedes
    geltende Zeichen hat denselben globalen Wert — den der Tafel [[1,1,3],[3,2,3],[3,3,3]].  Die Regeln definieren EINE Tafel. -/
theorem eich_laa_quotient : ∀ a b : Wert,
    ([true, false].any fun s => [0, 1, 2].any fun (k : Faser) => laaQ s k a b) = true ∧
    ∀ (s : Bool) (k : Faser), laaQ s k a b = true → Nat.beq (global k s).val (laaTafel a b).val = true := by
  decide

/-- aaa nach 1993 S. 64 (Textschicht PDF 68):  [Tk: Tk X && Tk Y]  [Fk: Fk X || Fk Y] -/
def aaa1993 : Bool → Faser → List (List RLit)
  | true, k => [[(true, k, true), (true, k, false)]]
  | false, k => [[(false, k, true)], [(false, k, false)]]
/-- n1 nach 1993 S. 64:  das Folgezeichen (Faser, Wert) -/
def n1_1993 : Bool → Faser → Faser × Bool
  | true, ⟨0, _⟩ => (0, false) | false, ⟨0, _⟩ => (0, true)
  | true, ⟨1, _⟩ => (2, true) | false, ⟨1, _⟩ => (2, false)
  | true, ⟨2, _⟩ => (1, true) | false, ⟨2, _⟩ => (1, false)
/-- n2 nach 1993 S. 64 -/
def n2_1993 : Bool → Faser → Faser × Bool
  | true, ⟨0, _⟩ => (2, true) | false, ⟨0, _⟩ => (2, false)
  | true, ⟨1, _⟩ => (1, false) | false, ⟨1, _⟩ => (1, true)
  | true, ⟨2, _⟩ => (0, true) | false, ⟨2, _⟩ => (0, false)

/-- **Eichung A1 (a):**  aaa von 1993 hat je Zeichen dieselben Alternativen wie die Regel aus Kaehr/Tableau (`aesteA opK`) -/
theorem eich_aaa_1993 : ∀ (s : Bool) (k : Faser), aaa1993 s k = (aesteA opK s).map (fun br => br.map fun e => (e.1, k, e.2)) := by
  decide
/-- **Eichung A1 (a):**  n1 von 1993 = `negN₁` -/
theorem eich_n1_1993 : ∀ (s : Bool) (k : Faser), n1_1993 s k = negN₁ s k := by decide
/-- **Eichung A1 (a):**  n2 von 1993 = `negN₂` -/
theorem eich_n2_1993 : ∀ (s : Bool) (k : Faser), n2_1993 s k = negN₂ s k := by decide

end Reformulation.Kaehr.TableauT

/-! ## Axiom-Wachen (gemessen, verbatim) -/

/-- info: 'Reformulation.Kaehr.TableauT.probiereL_none' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Kaehr.TableauT.probiereL_none

/-- info: 'Reformulation.Kaehr.TableauT.probiereL_some' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Kaehr.TableauT.probiereL_some

/-- info: 'Reformulation.Kaehr.TableauT.haeltE_eintraegeA' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Kaehr.TableauT.haeltE_eintraegeA

/-- info: 'Reformulation.Kaehr.TableauT.haeltE_eintraegeR' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Kaehr.TableauT.haeltE_eintraegeR

/-- info: 'Reformulation.Kaehr.TableauT.widerlegeT_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Kaehr.TableauT.widerlegeT_none

/-- info: 'Reformulation.Kaehr.TableauT.groesseK_pos' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Kaehr.TableauT.groesseK_pos

/-- info: 'Reformulation.Kaehr.TableauT.massK_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Kaehr.TableauT.massK_append

/-- info: 'Reformulation.Kaehr.TableauT.massK_eintraegeA' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Kaehr.TableauT.massK_eintraegeA

/-- info: 'Reformulation.Kaehr.TableauT.laa_gestalt' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Kaehr.TableauT.laa_gestalt

/-- info: 'Reformulation.Kaehr.TableauT.massK_eintraegeR' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Kaehr.TableauT.massK_eintraegeR

/-- info: 'Reformulation.Kaehr.TableauT.widerlegeT_some' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Kaehr.TableauT.widerlegeT_some

/-- info: 'Reformulation.Kaehr.TableauT.schliesstT_korrekt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Kaehr.TableauT.schliesstT_korrekt

/-- info: 'Reformulation.Kaehr.TableauT.schliesstT_vollst' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Kaehr.TableauT.schliesstT_vollst

/-- info: 'Reformulation.Kaehr.TableauT.schluss1993_gemeinsam' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Kaehr.TableauT.schluss1993_gemeinsam

/-- info: 'Reformulation.Kaehr.TableauT.ex2_true' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Kaehr.TableauT.ex2_true

/-- info: 'Reformulation.Kaehr.TableauT.ex3_true' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Kaehr.TableauT.ex3_true

/-- info: 'Reformulation.Kaehr.TableauT.laa_inklusion_Va' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Kaehr.TableauT.laa_inklusion_Va

/-- info: 'Reformulation.Kaehr.TableauT.laa_inklusion_Vb' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Kaehr.TableauT.laa_inklusion_Vb

/-- info: 'Reformulation.Kaehr.TableauT.laa_inklusion' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Kaehr.TableauT.laa_inklusion

/-- info: 'Reformulation.Kaehr.TableauT.fbeq_eq' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Kaehr.TableauT.fbeq_eq

/-- info: 'Reformulation.Kaehr.TableauT.passt_haelt' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Kaehr.TableauT.passt_haelt

/-- info: 'Reformulation.Kaehr.TableauT.erfuellt_haelt' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Kaehr.TableauT.erfuellt_haelt

/-- info: 'Reformulation.Kaehr.TableauT.sigma1_teil_R' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Kaehr.TableauT.sigma1_teil_R

/-- info: 'Reformulation.Kaehr.TableauT.tableauT_korrekt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Kaehr.TableauT.tableauT_korrekt

/-- info: 'Reformulation.Kaehr.TableauT.groessen' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Kaehr.TableauT.groessen

/-- info: 'Reformulation.Kaehr.TableauT.eins_Leer' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Kaehr.TableauT.eins_Leer

/-- info: 'Reformulation.Kaehr.TableauT.eins_U' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Kaehr.TableauT.eins_U

/-- info: 'Reformulation.Kaehr.TableauT.eins_62' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Kaehr.TableauT.eins_62

/-- info: 'Reformulation.Kaehr.TableauT.korrekt_leer' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Kaehr.TableauT.korrekt_leer

/-- info: 'Reformulation.Kaehr.TableauT.tableauT_unvollstaendig' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Kaehr.TableauT.tableauT_unvollstaendig

/-- info: 'Reformulation.Kaehr.TableauT.tableauT_unvollstaendig_ex' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Kaehr.TableauT.tableauT_unvollstaendig_ex

/-- info: 'Reformulation.Kaehr.TableauT.zwei_schlussarten' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Kaehr.TableauT.zwei_schlussarten

/-- info: 'Reformulation.Kaehr.TableauT.groesse_einK' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Kaehr.TableauT.groesse_einK

/-- info: 'Reformulation.Kaehr.TableauT.eintraege_einK' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Kaehr.TableauT.eintraege_einK

/-- info: 'Reformulation.Kaehr.TableauT.probiere_einK' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Kaehr.TableauT.probiere_einK

/-- info: 'Reformulation.Kaehr.TableauT.widerlegeT_einK' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Kaehr.TableauT.widerlegeT_einK

/-- info: 'Reformulation.Kaehr.TableauT.beweisbarT_einK' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Kaehr.TableauT.beweisbarT_einK

/-- info: 'Reformulation.Kaehr.TableauT.eich_laa_quotient' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Kaehr.TableauT.eich_laa_quotient

/-- info: 'Reformulation.Kaehr.TableauT.eich_aaa_1993' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Kaehr.TableauT.eich_aaa_1993

/-- info: 'Reformulation.Kaehr.TableauT.eich_n1_1993' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Kaehr.TableauT.eich_n1_1993

/-- info: 'Reformulation.Kaehr.TableauT.eich_n2_1993' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Kaehr.TableauT.eich_n2_1993
