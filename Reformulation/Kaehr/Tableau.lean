import Reformulation.Pfalzgraf.Faserung

/-!
# Reformulation.Kaehr.Tableau — Kaehrs Tableau für das freie System, korrekt und vollständig

**Was das Modul ist (CLAUDE.md §4):** ERTRAG. Gebaut nach `KorpusRev2/Spec_B_Teil_II_Kaehr_Tableau.md`
(Fassung 2, Mathematiker; Ort nach Custos TB1). Kaehrs junktionale Tableau-Regeln von 1981, mit dem
Druckfehler L1 berichtigt, sind ein signiertes Tableau für Pfalzgrafs freies Parallelsystem. Das Modul
baut sie als ausführbaren Beweiser `widerlege` und beweist sie korrekt und vollständig gegen die
Gültigkeit im freien System: `beweisbar_iff`.

## K1 · Die Herkünfte, Zeile für Zeile

```text
NACH KAEHR       die Regeln für N₁, N₂ und für Konjunktion, Disjunktion, Implikation — Kaehr 1981, "Das
                 graphematische Problem einer Formalisierung", Appendix I, PDF-S. 16 (am Bild);  die Beispiele
                 H1 (PDF-S. 16) und H2 (PDF-S. 17);  der Abschluss innerhalb EINES Systems
UNSER            die Berichtigung von L1;  die Beweisbarkeit in der H1-Fassung (alle drei Fasern unmittelbar,
                 E3′c);  die Tafelregel für die übrigen dreizehn Operationen;  die Verallgemeinerung über Kaehrs
                 Beschränkung auf zwei Variablen hinaus (K6);  die Lean-Gestalt (K8)
NACH PFALZGRAF   das freie System, die Fasern, die Negatoren als Semantik (Pfalzgraf/Faserung)
```

Kaehrs Systeme 1, 2, 3 sind Pfalzgrafs L₁, L₂, L₃ ohne Umrechnung (Kaehrs Vermittlung t¹ = t³, f¹ ≡ t²,
f² = f³, PDF-S. 16); in Lean die Fasern 0, 1, 2 = Günthers Teilsysteme 1-2, 2-3, 1-3.

## K2 · Kaehrs Druckfehler, benannt

* **L1:** Die Tafel (PDF-S. 16) druckt t³N₁X → f²X. Nach den übrigen Zeilen und nach Kaehrs eigenem
  Beispiel H1 (Spalte f³: „t³ N₁(N₂(N₁p)) → t² N₂(N₁p)“) ist es t³N₁X → t²X. Am Bild geprüft: L1 ist der
  **einzige** Druckfehler in den Regeln.
* **H2, Spalte 1:** gedruckt „f¹ p∧N₃p∧N₄p“, nach den Regeln „t² p∧N₃p∧N₄p“.
* **L3b, H2, Spalte 2, letzte Zeile:** gedruckt „f³p“, nach den Regeln f²p. Mit f³p schlösse der Ast,
  gegen Kaehrs eigenes „∅“.
* **L4, die Beweisbarkeit:** gedruckt die simultane T-Inkonsistenz von {ρ¹X¹}, {ρ²N₁X²}, {ρ³X³}. Die
  zweite Menge prüft über N₁ Faser 3, Faser 2 prüft keine. Gebaut ist die Fassung aus Kaehrs Beispiel H1
  (f¹H, f²H, f³H). `kaehr_gedruckt_nicht_korrekt` zeigt, dass die gedruckte nicht korrekt ist.

## K3 · Die Falle

Gültigkeit im freien System ist durch Durchrechnen entscheidbar, über 2^(3·Variablen) Belegungen. Das
Ergebnis dieses Moduls ist nicht, dass sie entscheidbar ist, sondern dass **Kaehrs Regeln** ein
Entscheidungsverfahren sind und jede Antwort ein Zertifikat trägt: `none` heisst geschlossen (Korrektheit,
`widerlege_none`), `some g` liefert eine Belegung, die nachrechenbar falsifiziert (`widerlege_some`).

## K4 · Warum vollständig hier geht und V nicht

Das freie System hat keine Kopplung zwischen den Fasern. Ein offener, abgebauter Ast trägt nur signierte
Variablen ohne Widerspruch innerhalb einer Faser, und das ist eine freie Belegung. Im Quotienten ist die
Kopplung partiell, und genau daran scheiterte die Invariante für V (Kopf von Pfalzgraf/Faserung, K4).

## K5 · Was Kaehr selbst dazu sagt

Der Tableau-Bericht von 1993 (Bashford, Joemann, Kaehr) nannte die Regeln *„noch nicht vollständig und
korrekt“* (PDF-S. 5). Für das junktionale Fragment ist das mit diesem Modul entschieden: Die Regeln von 1981
sind, mit L1 berichtigt und mit der Beweisbarkeit nach H1, korrekt und vollständig. Für Transjunktionen ist
nichts entschieden (B5).

## K6 · Kaehrs Zwei-Variablen-Beschränkung

*„E⁽³⁾ sei eine Menge signierter Formeln mit höchstens zwei Variablen“* (PDF-S. 15, S. 14 gedruckt). Das
Tableau hier gilt für beliebig viele Variablen; das ist UNSERE Verallgemeinerung.

## K7 · Die Implikation steht in der Tafel, nicht im Namen

Kaehr nennt die Logik G^(3,2)_(∧,∨,N₁,N₂) (PDF-S. 15); seine Regeltafel (PDF-S. 16) führt aber auch ⊃, und H1
rechnet damit. Gebaut sind Kaehrs Regeln für alle drei.

## K8 · Die beweistechnische Gestalt

Brennstoff statt Wohlfundiertheit: `widerlege` rekursiert über einen Brennstoff in Höhe der Formelgrösse,
darum rechnet es unter `decide` und `#guard`. Zwei Invarianten statt eines Hintikka-Lemmas: die
Gegenbelegung entsteht direkt aus den Literalen des offenen Astes (`ausLits`). Kaehrs Regeln für ∧, ∨, ⊃
werden **wörtlich** gefahren (`aesteA`, Fassung (b2)); für die übrigen dreizehn Operationen verzweigt die
Tafelregel über alle passenden Eingaben.

*Choice umgangen, gemessen (Mathlib 83a5988):* `List.contains` und `==` auf `Fin` ziehen Mathlibs
Ordnungsinstanzen (`instLawfulBCmpCompare_mathlib`, `Fin.instLawfulEqOrd`), darum vergleicht `stelle` über
`Nat.beq` auf `.val`. `by_cases` und `tauto` sind durch Bool-Fallunterscheidungen ersetzt, `==` auf `Bool`
durch eine entscheidbare `Prop`-Bedingung, und `omega` steht nur nach `exfalso`.

## Stufen (Ertrags-Skala, CLAUDE.md §4)

```text
negregeln_frei, negN₁_frei, negN₂_frei   FOLGERUNG:  Kaehrs Negator-Regeln SIND die freien Negatoren (korrekt und umkehrbar)
widerlege_none, widerlege_some           FOLGERUNG:  die zwei Invarianten (Korrektheit, Vollständigkeit)
tableau_korrekt, tableau_vollstaendig,   FOLGERUNG:  Kaehrs Kalkül, berichtigt, ist für das freie System korrekt und vollständig
  beweisbar_iff, schliesst_iff
kaehr_H1, kaehr_H2                        EICHUNG an Kaehr 1981, PDF-S. 16 f.
kaehr_gedruckt_nicht_korrekt              FOLGERUNG gegen die gedruckte Definition (L4)
die übrigen Sätze                         Hilfssätze der zwei Invarianten
```

0 Sorries. Gemessene Profile verbatim in den Wachen am Dateiende.
-/

namespace Reformulation.Kaehr.Tableau

open Reformulation.Pfalzgraf

/-- ein signierter Eintrag:  (Wert, Faser, Formel) — "φ hat in Faser i den Wert s" -/
abbrev Eintrag := Bool × Faser × Fm
/-- ein Literal auf dem Ast:  (Variable, Faser, Wert) -/
abbrev Lit := ℕ × Faser × Bool

def groesse : Fm → ℕ
  | .var _ => 1
  | .neg₁ a => groesse a + 1
  | .neg₂ a => groesse a + 1
  | .junk _ _ _ a b => groesse a + groesse b + 1

def mass : List Eintrag → ℕ
  | [] => 0
  | (_, _, φ) :: r => groesse φ + mass r

/-- dieselbe Stelle (Variable, Faser), über `.val` verglichen (Mathlibs Fin-Ordnung trägt Choice) -/
def stelle (m : ℕ) (j : Faser) (n : ℕ) (i : Faser) : Bool := Nat.beq m n && Nat.beq j.val i.val
theorem stelle_iff {m n : ℕ} {j i : Faser} : stelle m j n i = true ↔ m = n ∧ j = i := by
  unfold stelle
  rw [Bool.and_eq_true]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨Nat.eq_of_beq_eq_true h1, Fin.ext (Nat.eq_of_beq_eq_true h2)⟩
  · rintro ⟨rfl, rfl⟩; exact ⟨Nat.beq_refl _, Nat.beq_refl _⟩
/-- ein Literal liegt auf dem Ast -/
def liegt : List Lit → Lit → Bool
  | [], _ => false
  | (m, j, t) :: ls, (n, i, s) => (stelle m j n i && (t == s)) || liegt ls (n, i, s)
theorem liegt_iff : ∀ (ls : List Lit) (l : Lit), liegt ls l = true ↔ l ∈ ls := by
  intro ls
  induction ls with
  | nil => intro l; simp [liegt]
  | cons m ls ih =>
    intro l
    obtain ⟨n, i, s⟩ := l
    obtain ⟨m', j, t⟩ := m
    simp only [liegt, Bool.or_eq_true, Bool.and_eq_true, stelle_iff, ih, List.mem_cons]
    constructor
    · rintro (⟨⟨rfl, rfl⟩, h⟩ | h)
      · left; cases t <;> cases s <;> simp_all
      · exact Or.inr h
    · rintro (h | h)
      · left; simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨⟨rfl, rfl⟩, by cases s <;> rfl⟩
      · exact Or.inr h
/-- die Belegung eines offenen Astes:  das erste passende Literal, sonst wahr -/
def ausLits : List Lit → FreieBelegung
  | [], _, _ => true
  | (m, j, t) :: ls, n, i => if stelle m j n i then t else ausLits ls n i

def orElse : Option FreieBelegung → Option FreieBelegung → Option FreieBelegung
  | some g, _ => some g
  | none, b => b

/-- die Äste eines Junktor-Eintrags, abstrakt:  je Ast eine Liste (Wert, links?).  Kaehrs α/β-Regeln WÖRTLICH für ∧, ∨, ⊃
    (Kaehr 1981, PDF-S. 16);  für die übrigen dreizehn Operationen die Tafelregel (UNSER) -/
def aesteA (o : Op) (s : Bool) : List (List (Bool × Bool)) :=
  if o = opK then (if s then [[(true, true), (true, false)]] else [[(false, true)], [(false, false)]])
  else if o = opD then (if s then [[(true, true)], [(true, false)]] else [[(false, true), (false, false)]])
  else if o = opI then (if s then [[(false, true)], [(true, false)]] else [[(true, true), (false, false)]])
  else (if ap o true true = s then [[(true, true), (true, false)]] else []) ++
    (if ap o true false = s then [[(true, true), (false, false)]] else []) ++
    (if ap o false true = s then [[(false, true), (true, false)]] else []) ++
    (if ap o false false = s then [[(false, true), (false, false)]] else [])

/-- ein abstrakter Ast ist unter den Eingaben x (links), y (rechts) erfüllt -/
def erfuellt (x y : Bool) (br : List (Bool × Bool)) : Bool := br.all fun e => (if e.2 then x else y) == e.1
/-- die Gestalt eines Astes:  höchstens ein linker und ein rechter Eintrag -/
def gestaltOK : List (Bool × Bool) → Bool
  | [(_, true)] => true | [(_, false)] => true | [(_, true), (_, false)] => true | _ => false
/-- die Einträge eines Astes -/
def eintraege (i : Faser) (a b : Fm) (br : List (Bool × Bool)) : List Eintrag :=
  br.map fun e => (e.1, i, if e.2 then a else b)
/-- die Äste nacheinander versuchen -/
def probiere (w : List Eintrag → Option FreieBelegung) (i : Faser) (a b : Fm) :
    List (List (Bool × Bool)) → Option FreieBelegung
  | [] => none
  | br :: bs => orElse (w (eintraege i a b br)) (probiere w i a b bs)

/-- Kaehrs Negator-Regeln (L1 berichtigt):  der Folgeeintrag -/
def negN₁ (s : Bool) : Faser → Faser × Bool
  | ⟨0, _⟩ => (0, !s) | ⟨1, _⟩ => (2, s) | ⟨2, _⟩ => (1, s)
def negN₂ (s : Bool) : Faser → Faser × Bool
  | ⟨0, _⟩ => (2, s) | ⟨1, _⟩ => (1, !s) | ⟨2, _⟩ => (0, s)

/-- das Tableau:  none = alle Äste geschlossen;  some g = ein offener, gesättigter Ast mit seiner Belegung -/
def widerlege : ℕ → List Lit → List Eintrag → Option FreieBelegung
  | _, ls, [] => some (ausLits ls)
  | 0, ls, _ :: _ => some (ausLits ls)
  | k + 1, ls, (s, i, .var n) :: r =>
      if liegt ls (n, i, !s) then none else widerlege k ((n, i, s) :: ls) r
  | k + 1, ls, (s, i, .neg₁ a) :: r => widerlege k ls (((negN₁ s i).2, (negN₁ s i).1, a) :: r)
  | k + 1, ls, (s, i, .neg₂ a) :: r => widerlege k ls (((negN₂ s i).2, (negN₂ s i).1, a) :: r)
  | k + 1, ls, (s, i, .junk o0 o1 o2 a b) :: r =>
      probiere (fun e => widerlege k ls (e ++ r)) i a b (aesteA (oAt o0 o1 o2 i) s)

def gilt (g : FreieBelegung) (e : Eintrag) : Prop := auswFrei g e.2.2 e.2.1 = e.1
def stimmt (g : FreieBelegung) (l : Lit) : Prop := g l.1 l.2.1 = l.2.2
def konsistent (ls : List Lit) : Prop := ∀ n i s, (n, i, s) ∈ ls → (n, i, !s) ∉ ls

-- die Negator-Regeln sind die freien Negatoren (N)
theorem negN₁_frei (g : FreieBelegung) (s : Bool) (i : Faser) (a : Fm) :
    gilt g (s, i, .neg₁ a) ↔ gilt g ((negN₁ s i).2, (negN₁ s i).1, a) := by
  unfold gilt
  match i with
  | ⟨0, _⟩ => cases s <;> cases h : auswFrei g a 0 <;> simp [auswFrei, fneg₁, negN₁, h]
  | ⟨1, _⟩ => simp [auswFrei, fneg₁, negN₁]
  | ⟨2, _⟩ => simp [auswFrei, fneg₁, negN₁]
theorem negN₂_frei (g : FreieBelegung) (s : Bool) (i : Faser) (a : Fm) :
    gilt g (s, i, .neg₂ a) ↔ gilt g ((negN₂ s i).2, (negN₂ s i).1, a) := by
  unfold gilt
  match i with
  | ⟨0, _⟩ => simp [auswFrei, fneg₂, negN₂]
  | ⟨1, _⟩ => cases s <;> cases h : auswFrei g a 1 <;> simp [auswFrei, fneg₂, negN₂, h]
  | ⟨2, _⟩ => simp [auswFrei, fneg₂, negN₂]

theorem orElse_some {a b : Option FreieBelegung} {g : FreieBelegung} (h : orElse a b = some g) :
    a = some g ∨ b = some g := by
  cases a with
  | none => right; simpa [orElse] using h
  | some x => left; simpa [orElse] using h

theorem orElse_none {a b : Option FreieBelegung} : orElse a b = none ↔ a = none ∧ b = none := by
  cases a <;> simp [orElse]


theorem bool_beq (x v : Bool) : (x == v) = true ↔ x = v := by cases x <;> cases v <;> decide

theorem aesteA_vollst4 : ∀ a b c d s x y : Bool, ap (a, b, c, d) x y = s →
    (aesteA (a, b, c, d) s).any (erfuellt x y) = true := by decide
theorem aesteA_korr4 : ∀ a b c d s x y : Bool,
    (aesteA (a, b, c, d) s).all (fun br => !erfuellt x y br || ap (a, b, c, d) x y == s) = true := by decide
theorem aesteA_gestalt4 : ∀ a b c d s : Bool, (aesteA (a, b, c, d) s).all gestaltOK = true := by decide

theorem aesteA_vollst (o : Op) (s x y : Bool) (h : ap o x y = s) : ∃ br ∈ aesteA o s, erfuellt x y br = true := by
  obtain ⟨a, b, c, d⟩ := o
  exact List.any_eq_true.mp (aesteA_vollst4 a b c d s x y h)
theorem aesteA_korr (o : Op) (s x y : Bool) (br : List (Bool × Bool)) (hb : br ∈ aesteA o s)
    (he : erfuellt x y br = true) : ap o x y = s := by
  obtain ⟨a, b, c, d⟩ := o
  have h := List.all_eq_true.mp (aesteA_korr4 a b c d s x y) br hb
  rw [he] at h
  revert h
  cases ap (a, b, c, d) x y <;> cases s <;> intro h <;> first | rfl | exact absurd h (by decide)
theorem aesteA_gestalt (o : Op) (s : Bool) (br : List (Bool × Bool)) (hb : br ∈ aesteA o s) :
    gestaltOK br = true := by
  obtain ⟨a, b, c, d⟩ := o
  exact List.all_eq_true.mp (aesteA_gestalt4 a b c d s) br hb

theorem gilt_eintraege (g : FreieBelegung) (i : Faser) (a b : Fm) :
    ∀ br, (∀ e ∈ eintraege i a b br, gilt g e) ↔ erfuellt (auswFrei g a i) (auswFrei g b i) br = true := by
  intro br
  induction br with
  | nil => simp [eintraege, erfuellt]
  | cons e br ih =>
    obtain ⟨v, l⟩ := e
    have hcons : eintraege i a b ((v, l) :: br) = (v, i, if l then a else b) :: eintraege i a b br := rfl
    have hall : erfuellt (auswFrei g a i) (auswFrei g b i) ((v, l) :: br) =
        (((if l then auswFrei g a i else auswFrei g b i) == v) && erfuellt (auswFrei g a i) (auswFrei g b i) br) := rfl
    rw [hcons, hall, Bool.and_eq_true, bool_beq, ← ih]
    constructor
    · intro h
      refine ⟨?_, fun e he => h e (List.mem_cons_of_mem _ he)⟩
      have := h _ List.mem_cons_self
      cases l <;> exact this
    · rintro ⟨h1, h2⟩ e he
      rcases List.mem_cons.mp he with rfl | he
      · cases l <;> exact h1
      · exact h2 e he

theorem mass_append : ∀ l1 l2 : List Eintrag, mass (l1 ++ l2) = mass l1 + mass l2 := by
  intro l1 l2
  induction l1 with
  | nil => show mass l2 = 0 + mass l2; omega
  | cons e l ih =>
    obtain ⟨_, _, φ⟩ := e
    show groesse φ + mass (l ++ l2) = groesse φ + mass l + mass l2
    rw [ih]; omega

theorem mass_eintraege (i : Faser) (a b : Fm) :
    ∀ br, gestaltOK br = true → mass (eintraege i a b br) ≤ groesse a + groesse b
  | [(_, true)], _ => by show groesse a + 0 ≤ _; omega
  | [(_, false)], _ => by show groesse b + 0 ≤ _; omega
  | [(_, true), (_, false)], _ => by show groesse a + (groesse b + 0) ≤ _; omega
  | [], h => absurd h (by decide)
  | [(_, false), (_, _)], h => by simp only [gestaltOK] at h; exact absurd h (by decide)
  | [(_, true), (_, true)], h => by simp only [gestaltOK] at h; exact absurd h (by decide)
  | _ :: _ :: _ :: _, h => by simp only [gestaltOK] at h; exact absurd h (by decide)

theorem probiere_none {w : List Eintrag → Option FreieBelegung} {i : Faser} {a b : Fm} :
    ∀ bs, probiere w i a b bs = none ↔ ∀ br ∈ bs, w (eintraege i a b br) = none := by
  intro bs
  induction bs with
  | nil => simp [probiere]
  | cons br bs ih =>
    rw [probiere, orElse_none, ih]
    constructor
    · rintro ⟨h1, h2⟩ c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact h1
      · exact h2 c hc
    · intro h; exact ⟨h _ List.mem_cons_self, fun c hc => h c (List.mem_cons_of_mem _ hc)⟩

theorem probiere_some {w : List Eintrag → Option FreieBelegung} {i : Faser} {a b : Fm} {g : FreieBelegung} :
    ∀ bs, probiere w i a b bs = some g → ∃ br ∈ bs, w (eintraege i a b br) = some g := by
  intro bs
  induction bs with
  | nil => intro h; simp [probiere] at h
  | cons br bs ih =>
    intro h
    rcases orElse_some h with h | h
    · exact ⟨br, List.mem_cons_self, h⟩
    · obtain ⟨c, hc, hw⟩ := ih h; exact ⟨c, List.mem_cons_of_mem _ hc, hw⟩

/-- K1′ (Korrektheit):  schliesst das Tableau, so erfüllt keine Belegung Literale und Einträge zugleich -/
theorem widerlege_none :
    ∀ k ls todo, widerlege k ls todo = none →
      ∀ g, (∀ l ∈ ls, stimmt g l) → (∀ e ∈ todo, gilt g e) → False := by
  intro k
  induction k with
  | zero =>
    intro ls todo h; cases todo with
    | nil => simp [widerlege] at h
    | cons e r => simp [widerlege] at h
  | succ k ih =>
    intro ls todo h g hl he
    match todo with
    | [] => simp [widerlege] at h
    | (s, i, .var n) :: r =>
      simp only [widerlege] at h
      split at h
      · rename_i hc
        have hm : (n, i, !s) ∈ ls := (liegt_iff _ _).mp hc
        have h1 := hl _ hm
        have h2 := he _ List.mem_cons_self
        simp only [stimmt, gilt, auswFrei] at h1 h2
        rw [h1] at h2; cases s <;> simp at h2
      · refine ih _ _ h g ?_ (fun e he' => he e (List.mem_cons_of_mem _ he'))
        intro l hl'
        rcases List.mem_cons.mp hl' with rfl | hl'
        · have := he _ List.mem_cons_self; simpa [stimmt, gilt, auswFrei] using this
        · exact hl l hl'
    | (s, i, .neg₁ a) :: r =>
      simp only [widerlege] at h
      refine ih _ _ h g hl ?_
      intro e he'
      rcases List.mem_cons.mp he' with rfl | he'
      · exact (negN₁_frei g s i a).mp (he _ List.mem_cons_self)
      · exact he e (List.mem_cons_of_mem _ he')
    | (s, i, .neg₂ a) :: r =>
      simp only [widerlege] at h
      refine ih _ _ h g hl ?_
      intro e he'
      rcases List.mem_cons.mp he' with rfl | he'
      · exact (negN₂_frei g s i a).mp (he _ List.mem_cons_self)
      · exact he e (List.mem_cons_of_mem _ he')
    | (s, i, .junk o0 o1 o2 a b) :: r =>
      simp only [widerlege] at h
      have h0 := he _ List.mem_cons_self
      simp only [gilt, auswFrei] at h0
      obtain ⟨br, hbr, herf⟩ := aesteA_vollst _ _ _ _ h0
      have hw := (probiere_none _).mp h br hbr
      refine ih _ _ hw g hl ?_
      intro e he'
      rcases List.mem_append.mp he' with he' | he'
      · exact ((gilt_eintraege g i a b br).mpr herf) e he'
      · exact he e (List.mem_cons_of_mem _ he')

/-- die Belegung eines konsistenten Astes stimmt mit jedem seiner Literale -/
theorem ausLits_stimmt : ∀ ls : List Lit, konsistent ls → ∀ l ∈ ls, stimmt (ausLits ls) l := by
  intro ls
  induction ls with
  | nil => intro _ l hl; simp at hl
  | cons m ls ih =>
    intro hk l hl
    obtain ⟨n, i, s⟩ := l
    obtain ⟨n', i', s'⟩ := m
    have hk' : konsistent ls := fun a b c h1 h2 => hk a b c (List.mem_cons_of_mem _ h1) (List.mem_cons_of_mem _ h2)
    simp only [stimmt, ausLits]
    cases hs : stelle n' i' n i
    · simp only [Bool.false_eq_true, if_false]
      rcases List.mem_cons.mp hl with h | h
      · simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        rw [stelle_iff.mpr ⟨rfl, rfl⟩] at hs; exact absurd hs (by decide)
      · exact ih hk' _ h
    · simp only [if_true]
      obtain ⟨rfl, rfl⟩ := stelle_iff.mp hs
      rcases List.mem_cons.mp hl with h | h
      · simp only [Prod.mk.injEq] at h; exact h.2.2.symm
      · cases s <;> cases s'
        · rfl
        · exact (hk n' i' true List.mem_cons_self (List.mem_cons_of_mem _ h)).elim
        · exact (hk n' i' false List.mem_cons_self (List.mem_cons_of_mem _ h)).elim
        · rfl

theorem groesse_pos (φ : Fm) : 0 < groesse φ := by cases φ <;> simp [groesse]

/-- K2′ (Vollständigkeit):  liefert das Tableau eine Belegung, so erfüllt sie Literale und Einträge -/
theorem widerlege_some :
    ∀ k ls todo g, mass todo ≤ k → konsistent ls → widerlege k ls todo = some g →
      (∀ l ∈ ls, stimmt g l) ∧ (∀ e ∈ todo, gilt g e) := by
  intro k
  induction k with
  | zero =>
    intro ls todo g hm hk h
    match todo with
    | [] => simp only [widerlege, Option.some.injEq] at h; subst h; exact ⟨ausLits_stimmt ls hk, by simp⟩
    | (_, _, φ) :: _ => exfalso; have := groesse_pos φ; simp only [mass] at hm; omega
  | succ k ih =>
    intro ls todo g hm hk h
    match todo with
    | [] => simp only [widerlege, Option.some.injEq] at h; subst h; exact ⟨ausLits_stimmt ls hk, by simp⟩
    | (s, i, .var n) :: r =>
      simp only [widerlege] at h
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
        have hm' : mass r ≤ k := by simp [mass, groesse] at hm; omega
        obtain ⟨hl, he⟩ := ih _ _ g hm' hk' h
        refine ⟨fun l h' => hl l (List.mem_cons_of_mem _ h'), ?_⟩
        intro e he'
        rcases List.mem_cons.mp he' with rfl | he'
        · have := hl _ List.mem_cons_self; simpa [stimmt, gilt, auswFrei] using this
        · exact he e he'
    | (s, i, .neg₁ a) :: r =>
      simp only [widerlege] at h
      have hm' : mass (((negN₁ s i).2, (negN₁ s i).1, a) :: r) ≤ k := by simp [mass, groesse] at hm ⊢; omega
      obtain ⟨hl, he⟩ := ih _ _ g hm' hk h
      refine ⟨hl, ?_⟩
      intro e he'
      rcases List.mem_cons.mp he' with rfl | he'
      · exact (negN₁_frei g s i a).mpr (he _ List.mem_cons_self)
      · exact he e (List.mem_cons_of_mem _ he')
    | (s, i, .neg₂ a) :: r =>
      simp only [widerlege] at h
      have hm' : mass (((negN₂ s i).2, (negN₂ s i).1, a) :: r) ≤ k := by simp [mass, groesse] at hm ⊢; omega
      obtain ⟨hl, he⟩ := ih _ _ g hm' hk h
      refine ⟨hl, ?_⟩
      intro e he'
      rcases List.mem_cons.mp he' with rfl | he'
      · exact (negN₂_frei g s i a).mpr (he _ List.mem_cons_self)
      · exact he e (List.mem_cons_of_mem _ he')
    | (s, i, .junk o0 o1 o2 a b) :: r =>
      simp only [widerlege] at h
      obtain ⟨br, hbr, hw⟩ := probiere_some _ h
      have hm' : mass (eintraege i a b br ++ r) ≤ k := by
        rw [mass_append]
        have := mass_eintraege i a b br (aesteA_gestalt _ _ br hbr)
        simp only [mass, groesse] at hm; omega
      obtain ⟨hl, he⟩ := ih _ _ g hm' hk hw
      refine ⟨hl, ?_⟩
      have herf := (gilt_eintraege g i a b br).mp (fun e h' => he e (List.mem_append_left _ h'))
      have hs := aesteA_korr _ _ _ _ br hbr herf
      intro e he'
      rcases List.mem_cons.mp he' with rfl | he'
      · show auswFrei g (Fm.junk o0 o1 o2 a b) i = s
        exact hs
      · exact he e (List.mem_append_right _ he')

/-- je Faser:  das Tableau für (f, i, φ) schliesst -/
def schliesst (φ : Fm) (i : Faser) : Bool := (widerlege (groesse φ) [] [(false, i, φ)]).isNone
/-- beweisbar (Kaehrs H1-Fassung):  alle drei Fasern -/
def beweisbar (φ : Fm) : Bool := schliesst φ 0 && schliesst φ 1 && schliesst φ 2
/-- Kaehrs gedruckte Beweisbarkeit:  Faser 1, die zweite Menge mit N₁ vorgeschaltet, Faser 3 -/
def beweisbarGedruckt (φ : Fm) : Bool := schliesst φ 0 && schliesst (.neg₁ φ) 1 && schliesst φ 2

theorem schliesst_iff (φ : Fm) (i : Faser) : schliesst φ i = true ↔ ∀ f, auswFrei f φ i = true := by
  unfold schliesst
  constructor
  · intro h f
    cases hf : auswFrei f φ i
    · exact (widerlege_none _ _ _ (Option.isNone_iff_eq_none.mp h) f (by simp) (by simp [gilt, hf])).elim
    · rfl
  · intro hv
    cases hw : widerlege (groesse φ) [] [(false, i, φ)] with
    | none => rfl
    | some g =>
      have := (widerlege_some _ _ _ g (by simp [mass]) (by simp [konsistent]) hw).2 _ List.mem_cons_self
      simp [gilt, hv g] at this

/-- K1 + K2:  beweisbar ⟺ gültig im freien System -/
theorem beweisbar_iff (φ : Fm) : beweisbar φ = true ↔ gueltigFrei φ := by
  unfold beweisbar gueltigFrei
  simp only [Bool.and_eq_true, schliesst_iff]
  constructor
  · rintro ⟨⟨h0, h1⟩, h2⟩ f i
    match i with
    | ⟨0, _⟩ => exact h0 f
    | ⟨1, _⟩ => exact h1 f
    | ⟨2, _⟩ => exact h2 f
  · intro h; exact ⟨⟨fun f => h f 0, fun f => h f 1⟩, fun f => h f 2⟩

/-- Kaehrs Negator-Regeln sind die freien Negatoren:  korrekt und umkehrbar -/
theorem negregeln_frei (g : FreieBelegung) (s : Bool) (i : Faser) (a : Fm) :
    (gilt g (s, i, .neg₁ a) ↔ gilt g ((negN₁ s i).2, (negN₁ s i).1, a)) ∧
    (gilt g (s, i, .neg₂ a) ↔ gilt g ((negN₂ s i).2, (negN₂ s i).1, a)) :=
  ⟨negN₁_frei g s i a, negN₂_frei g s i a⟩

/-- **K1.** Korrektheit -/
theorem tableau_korrekt (φ : Fm) (h : beweisbar φ = true) : gueltigFrei φ := (beweisbar_iff φ).mp h
/-- **K2.** Vollständigkeit -/
theorem tableau_vollstaendig (φ : Fm) (h : gueltigFrei φ) : beweisbar φ = true := (beweisbar_iff φ).mpr h

/-- Kaehrs H1 (Negationszyklus):  N₁N₂N₁p ⊃⊃⊃ N₂N₁N₂p -/
def H1 : Fm := .junk opI opI opI (.neg₁ (.neg₂ (.neg₁ p))) (.neg₂ (.neg₁ (.neg₂ p)))
/-- K = p ∨∨∨ N₁N₂(p ∧∧∧ N₂p) -/
def K : Fm := dis p (.neg₁ (.neg₂ (kon p (.neg₂ p))))
/-- die Gegenbelegung des Tableaus für (f, i, φ), an der Variablen p -/
def gegenbelegung (φ : Fm) (i : Faser) : Option (List Bool) :=
  (widerlege (groesse φ) [] [(false, i, φ)]).map fun g => [g 0 0, g 0 1, g 0 2]

/-- **E1.** Kaehrs H1 ist beweisbar (Kaehr 1981, PDF-S. 16:  "x", geschlossen) -/
theorem kaehr_H1 : beweisbar H1 = true := by decide

/-- **E2.** Der Trennfall ist nicht beweisbar;  die Gegenbelegungen sind Kaehrs zwei offene Äste (T, T, F) und
    (F, F, T), je in der Faser, die sie falsch machen (Kaehr 1981, PDF-S. 17:  "∅") -/
theorem kaehr_H2 :
    beweisbar trenn = false ∧ gegenbelegung trenn 0 = some [true, true, false] ∧
    gegenbelegung trenn 1 = some [true, true, false] ∧ gegenbelegung trenn 2 = some [false, false, true] := by
  decide

/-- **KG.** Nach Kaehrs gedruckter Beweisbarkeit ist K beweisbar, nach der H1-Fassung nicht, und K ist im
    freien System nicht gültig — die gedruckte Fassung ist nicht korrekt -/
theorem kaehr_gedruckt_nicht_korrekt :
    beweisbarGedruckt K = true ∧ beweisbar K = false ∧ ¬ gueltigFrei K := by
  refine ⟨by decide, by decide, fun h => ?_⟩
  have := (beweisbar_iff K).mpr h
  exact absurd this (by decide)

/-! ## Der Beweiser läuft (A4) -/

#guard beweisbar H1
#guard !beweisbar trenn
#guard gegenbelegung trenn 0 == some [true, true, false]
#guard gegenbelegung trenn 2 == some [false, false, true]
#guard beweisbar gegen
#guard beweisbarGedruckt K && !beweisbar K

end Reformulation.Kaehr.Tableau

/-! ## Axiom-Stand — als Regressions-Wachen gesetzt (alle Sätze des Moduls) -/

/-- info: 'Reformulation.Kaehr.Tableau.stelle_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Kaehr.Tableau.stelle_iff

/-- info: 'Reformulation.Kaehr.Tableau.liegt_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Kaehr.Tableau.liegt_iff

/-- info: 'Reformulation.Kaehr.Tableau.negN₁_frei' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Kaehr.Tableau.negN₁_frei

/-- info: 'Reformulation.Kaehr.Tableau.negN₂_frei' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Kaehr.Tableau.negN₂_frei

/-- info: 'Reformulation.Kaehr.Tableau.orElse_some' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Kaehr.Tableau.orElse_some

/-- info: 'Reformulation.Kaehr.Tableau.orElse_none' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Kaehr.Tableau.orElse_none

/-- info: 'Reformulation.Kaehr.Tableau.bool_beq' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Kaehr.Tableau.bool_beq

/-- info: 'Reformulation.Kaehr.Tableau.aesteA_vollst4' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Kaehr.Tableau.aesteA_vollst4

/-- info: 'Reformulation.Kaehr.Tableau.aesteA_korr4' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Kaehr.Tableau.aesteA_korr4

/-- info: 'Reformulation.Kaehr.Tableau.aesteA_gestalt4' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Kaehr.Tableau.aesteA_gestalt4

/-- info: 'Reformulation.Kaehr.Tableau.aesteA_vollst' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Kaehr.Tableau.aesteA_vollst

/-- info: 'Reformulation.Kaehr.Tableau.aesteA_korr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Kaehr.Tableau.aesteA_korr

/-- info: 'Reformulation.Kaehr.Tableau.aesteA_gestalt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Kaehr.Tableau.aesteA_gestalt

/-- info: 'Reformulation.Kaehr.Tableau.gilt_eintraege' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Kaehr.Tableau.gilt_eintraege

/-- info: 'Reformulation.Kaehr.Tableau.mass_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Kaehr.Tableau.mass_append

/-- info: 'Reformulation.Kaehr.Tableau.mass_eintraege' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Kaehr.Tableau.mass_eintraege

/-- info: 'Reformulation.Kaehr.Tableau.probiere_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Kaehr.Tableau.probiere_none

/-- info: 'Reformulation.Kaehr.Tableau.probiere_some' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Kaehr.Tableau.probiere_some

/-- info: 'Reformulation.Kaehr.Tableau.widerlege_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Kaehr.Tableau.widerlege_none

/-- info: 'Reformulation.Kaehr.Tableau.ausLits_stimmt' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Kaehr.Tableau.ausLits_stimmt

/-- info: 'Reformulation.Kaehr.Tableau.groesse_pos' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Kaehr.Tableau.groesse_pos

/-- info: 'Reformulation.Kaehr.Tableau.widerlege_some' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Kaehr.Tableau.widerlege_some

/-- info: 'Reformulation.Kaehr.Tableau.schliesst_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Kaehr.Tableau.schliesst_iff

/-- info: 'Reformulation.Kaehr.Tableau.beweisbar_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Kaehr.Tableau.beweisbar_iff

/-- info: 'Reformulation.Kaehr.Tableau.negregeln_frei' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Kaehr.Tableau.negregeln_frei

/-- info: 'Reformulation.Kaehr.Tableau.tableau_korrekt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Kaehr.Tableau.tableau_korrekt

/-- info: 'Reformulation.Kaehr.Tableau.tableau_vollstaendig' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Kaehr.Tableau.tableau_vollstaendig

/-- info: 'Reformulation.Kaehr.Tableau.kaehr_H1' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Kaehr.Tableau.kaehr_H1

/-- info: 'Reformulation.Kaehr.Tableau.kaehr_H2' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Kaehr.Tableau.kaehr_H2

/-- info: 'Reformulation.Kaehr.Tableau.kaehr_gedruckt_nicht_korrekt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Kaehr.Tableau.kaehr_gedruckt_nicht_korrekt
