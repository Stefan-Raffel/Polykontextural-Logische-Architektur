import Reformulation.Proemial.CoalgebraMorphism

/-!
# Reformulation.Proemial.ContexturalFibration — die Kontextur-Faserung (einunddreißigste Schicht, der AP6-Schluss)

**AP6-Zug-4, der Schluss-Zug.** Der Träger wird gefasert (`ι × α` — jeder Zustand
trägt seinen Kontextur-Index; **die Benennung ist Deutung**, term-fest wird die
Struktur), und die **Faser-Treue** `FiberPreserving` sagt, dass die Möglichkeiten
in der Kontextur bleiben — die strukturelle Schwester der Diskontexturalität
(Deutung, markiert; **die Setzung des F-Strangs wird nicht konsumiert**). Der
Haupt-Satz macht die Faser-Einbettung zum Koalgebra-Morphismus (Konsum der 30.),
kein Kollaps kreuzt die Grenze (Kollaps-Sprache der 28.), die Kür hält die Bahn in
der Kontextur (`reachSet` der 29.) — **der Schluss-Zug konsumiert die drei
Vorgänger-Begriffe (`Collapses`, `reachSet`, `IsMorphism`) in je einem eigenen
Satz: Begriffs-Konsum, kein Satz-Konsum; mit dieser Schicht ist AP6 geschlossen.**
Der Springer belegt die Echtheit der Bedingung; der Familien-Bogen
`fiber (detFam F) i = det (F i)` schließt zur 28.

**Ein Import** (`CoalgebraMorphism`, transitiv die gesamte Kette und das Substrat);
die Kette wird 16→…→30→31. Term-identisch konsumiert werden `Branching`, `det`,
`Collapses` (28.), `reachSet` (29.), `IsMorphism` (30.),
`Function.iterate_succ_apply'` (Referenz-Liste, `[propext, Quot.sound]`). Nichts
wird dupliziert; **kein Mathlib-Import über die transitive Hülle hinaus**.

## (1) Bestands-Lage

Reiner Term-Zug, keine Quellen-Berührung; kein Stellen-Bau; **AP6-Zug-4, der
Schluss-Zug** — term-fest wird die Struktur, nicht die Benennung.

## (2) REICHWEITEN-MARKE (Pflicht)

Die Kontextur-Benennung der Fasern ist **Deutung** (A5-Anbindung mit Term darunter,
kein Zitat); **Diskontexturalität als Faser-Treue ist Deutung, markiert** — die
Diskontexturalitäts-Setzung des F-Strangs wird **nicht konsumiert und nicht
behauptet**; der **Transjunktions-Anschluss** (Kontextur-Wechsel als Bruch der
Faser-Treue) ist **benannt, kein Satz über Transjunktionen**.

## (3) Deutungs-Marken

**Produkt-Träger Modellwahl** — die abhängige Faserung (`α : ι → Type`) ist die
reichere Fassung, **benannter Folge-Posten**. „Kein Kollaps kreuzt" und „die Bahn
verlässt die Kontextur nie" sind **markierte Struktur-Aussagen** (Projekt-Rede);
die Springer-Miniatur ist ehrlich als Miniatur; kein Physik-Anspruch; Designation
ist nicht Denotation.

## (4) Term-fest werden hiermit

Die sechs Sätze `fiber_emb_morphism`, `fiber_preserving_no_crossing`,
`crossing_not_fiber_preserving`, `detFam_fiber_preserving`, `fiber_detFam`, Kür
`reach_stays_in_fiber`.

**KONSUM-EHRLICHKEIT:** `fiber_preserving_no_crossing` (M3) ist reine Anwendung,
`detFam_fiber_preserving` (M5a) reine Extraktion — beides Sach-Befund der
Konstruktion; eigener Beweis-Gehalt liegt in `fiber_emb_morphism` (M2),
`fiber_detFam` (M5b) und der Kür-Induktion. **Der Schluss konsumiert die drei
Vorgänger-Begriffe in je einem eigenen Satz — Begriffs-Konsum, kein Satz-Konsum**
(kein Theorem eines Vorgängers läuft in einen Beweis dieser Schicht ein; Trag-Befund
Prüfzug 4): 28. `Collapses` (M3 — am ∈-Synonym überdies **nominell**; der
substanzielle 28.-Rückgriff ist der Familien-Bogen `fiber_detFam`, dessen Statement
`det` irreduzibel führt), 29. `reachSet` (Kür), 30. `IsMorphism` (M2).

## (5) Abgrenzung

Abhängige Faserung, Ketten-Satz und die weitergehende Faser-Fluss-Kommutation über
`fiber` hinaus sind benannte Folge-Posten; **keine Transjunktions-Sätze**. **Mit
dieser Schicht ist AP6 geschlossen.** Konditional ist nichts, gesetzt ist nichts.

## (6) Sorry-Bilanz und Axiom-Ist — mit Prod-Vormessung und Rechnungs-Abgleich

**0 Sorries.** Axiom-Ist (erster grüner Build, v4.30.0-rc2), je Satz
`#guard_msgs`-verwacht am Datei-Ende (sechs Wachen):

* **axiom-frei:** `fiber_preserving_no_crossing` (reine Anwendung),
  `detFam_fiber_preserving` (`congrArg`-Extraktion).
* **`[propext]`:** `crossing_not_fiber_preserving` (Springer-Singleton plus
  `decide` über `Fin 2`).
* **`[propext, Quot.sound]`:** `fiber_emb_morphism`, `fiber_detFam` (Set-ext),
  `reach_stays_in_fiber` (Set-ext plus `iterate_succ_apply'`).

**Prod-Familien-Vormessung (Teil 0 (1), neue Familie):** **eta-Defeq trägt** —
`p = (p.1, p.2)` ist `rfl` (**axiom-frei** gemessen, strukturelle Eta ist
definitional in Lean 4); darum laufen alle `(p.1, p.2)`-Umschriebe (M2-Rückrichtung,
Kür-Zwischenzustand) **ohne Lemma** über `rw [← h1]` plus Eta. `congrArg Prod.fst`
auf der definitionalen Paar-Gleichung ist **axiom-frei** (trägt M5a, Kür-Basis);
`Prod.ext`/`ext_iff`/`mk.injEq` wurden **nicht benötigt**. Die Springer-Mitgliedschaft
`(1, 0) ∈ {(1, 0)}` ist `rfl` (`[propext]`-Bereich am `decide`).

**Abgleich gegen die Profil-Rechnung (M6(6), R2 = Erwartung):** getroffen an allen
sechs — M2/M5b Set-ext, M3/M5a axiom-frei, M4 `[propext]`, Kür `[propext,
Quot.sound]`; **kein `Classical`** an keiner Stelle (die Prod-Familie trägt keins,
gemessen — kein Hüllen-Schicksal).
-/

namespace Reformulation.Proemial.ContexturalFibration

open Reformulation.Proemial.BranchingCoalgebra
open Reformulation.Proemial.FlowIteration
open Reformulation.Proemial.CoalgebraMorphism

-- ============================================================
-- Teil 1 — Die Definitionen (M1)
-- ============================================================

/-- Die Faser-Einbettung: der Zustand in seine Kontextur gesetzt
    (Kontextur-Benennung: Deutung — A5-Anbindung mit Term). -/
def emb {ι α : Type*} (i : ι) : α → ι × α := fun a => (i, a)

/-- FASER-TREUE: die Möglichkeiten bleiben in der Kontextur — die
    strukturelle Schwester der Diskontexturalität (Deutung, markiert; die
    Setzung des F-Strangs wird nicht konsumiert). -/
def FiberPreserving {ι α : Type*} (c : Branching (ι × α)) : Prop :=
  ∀ (i : ι) (a : α), ∀ p ∈ c (i, a), p.1 = i

/-- Die Faser-Restriktion: die Verzweigung, in der Kontextur i gelesen. -/
def fiber {ι α : Type*} (c : Branching (ι × α)) (i : ι) : Branching α :=
  fun a => {b | (i, b) ∈ c (i, a)}

/-- Die deterministische Familie: je Kontextur ihre Funktion. -/
def detFam {ι α : Type*} (F : ι → α → α) : Branching (ι × α) :=
  fun p => {(p.1, F p.1 p.2)}

-- ============================================================
-- Teil 2 — Der Haupt-Satz (M2)
-- ============================================================

/-- „DIE EINBETTUNG IST MORPHISMUS": bei Faser-Treue ist die
    Faser-Einbettung ein Koalgebra-Morphismus (Konsum der 30. — die in
    Zug 3 angekündigte Verwendung). -/
theorem fiber_emb_morphism {ι α : Type*} {c : Branching (ι × α)}
    (hc : FiberPreserving c) (i : ι) :
    IsMorphism (emb i) (fiber c i) c := by
  intro a
  apply Set.ext
  intro p
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact hb
  · intro hp
    have h1 : p.1 = i := hc i a p hp
    have hpe : (i, p.2) = p := by rw [← h1]
    refine ⟨p.2, ?_, hpe⟩
    show (i, p.2) ∈ c (i, a)
    rw [hpe]
    exact hp

-- ============================================================
-- Teil 3 — Kein Kollaps kreuzt, und der Springer (M3/M4)
-- ============================================================

/-- „KEIN KOLLAPS ÜBERSCHREITET DIE KONTEXTUR-GRENZE": die Faser-Treue in
    der Kollaps-Sprache der 28. — reine Anwendung. -/
theorem fiber_preserving_no_crossing {ι α : Type*} {c : Branching (ι × α)}
    (hc : FiberPreserving c) {i j : ι} {a b : α}
    (h : Collapses c (i, a) (j, b)) : j = i :=
  hc i a (j, b) h

/-- Der Springer: alle Möglichkeiten in der fremden Kontextur — die
    einfachste Form, die die Echtheit der Bedingung belegt (Miniatur). -/
def hopper : Branching (Fin 2 × Fin 2) := fun _ => {(1, 0)}

/-- Die Faser-Treue ist echte Bedingung, keine Tautologie. -/
theorem crossing_not_fiber_preserving : ¬ FiberPreserving hopper := by
  intro h
  exact absurd (h 0 0 (1, 0) rfl) (by decide)

-- ============================================================
-- Teil 4 — Der det-Anschluss (M5)
-- ============================================================

/-- Die deterministische Familie ist faser-treu per Konstruktion
    (definitionale Extraktion plus `congrArg`-Projektion). -/
theorem detFam_fiber_preserving {ι α : Type*} (F : ι → α → α) :
    FiberPreserving (detFam F) :=
  fun _ _ _ hp => congrArg Prod.fst hp

/-- DER BOGEN ZURÜCK ZUR 28.: die Faser der deterministischen Familie ist
    die deterministische Einbettung des Familien-Glieds. -/
theorem fiber_detFam {ι α : Type*} (F : ι → α → α) (i : ι) :
    fiber (detFam F) i = det (F i) := by
  funext a
  apply Set.ext
  intro b
  constructor
  · intro hb
    exact congrArg Prod.snd (hb : (i, b) = (i, F i a))
  · intro hb
    exact congrArg (fun x => (i, x)) (hb : b = F i a)

-- ============================================================
-- Teil 5 — Kür (K1)
-- ============================================================

/-- KÜR — „DIE BAHN VERLÄSST DIE KONTEXTUR NIE" (markierte
    Struktur-Aussage): jede erreichbare Möglichkeit liegt in der
    Start-Kontextur. Basis `congrArg Prod.fst`; Schritt `iterate_succ_apply'`
    plus Faser-Treue am eta-gedrehten Zwischen-Zustand. -/
theorem reach_stays_in_fiber {ι α : Type*} {c : Branching (ι × α)}
    (hc : FiberPreserving c) (n : ℕ) (i : ι) (a : α) :
    ∀ p ∈ reachSet c n (i, a), p.1 = i := by
  induction n with
  | zero =>
      intro p hp
      exact congrArg Prod.fst hp
  | succ n ih =>
      intro p hp
      have hp' : p ∈ flow c (reachSet c n (i, a)) := by
        have hpp : p ∈ (flow c)^[n + 1] {(i, a)} := hp
        rwa [Function.iterate_succ_apply'] at hpp
      obtain ⟨q, hq, hpq⟩ := hp'
      have hq1 : q.1 = i := ih q hq
      have hpq' : p ∈ c (i, q.2) := by rw [← hq1]; exact hpq
      exact hc i q.2 p hpq'

end Reformulation.Proemial.ContexturalFibration

-- ============================================================
-- Teil 6 — Die `#guard_msgs`-Wachen (M7; Ist-gebunden)
-- ============================================================

-- Ist-Ausgabe des ersten grünen Builds (v4.30.0-rc2), pro Satz als Wache.
open Reformulation.Proemial.ContexturalFibration in
section

/-- info: 'Reformulation.Proemial.ContexturalFibration.fiber_emb_morphism' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms fiber_emb_morphism

/-- info: 'Reformulation.Proemial.ContexturalFibration.fiber_preserving_no_crossing' does not depend on any axioms -/
#guard_msgs in #print axioms fiber_preserving_no_crossing

/-- info: 'Reformulation.Proemial.ContexturalFibration.crossing_not_fiber_preserving' depends on axioms: [propext] -/
#guard_msgs in #print axioms crossing_not_fiber_preserving

/-- info: 'Reformulation.Proemial.ContexturalFibration.detFam_fiber_preserving' does not depend on any axioms -/
#guard_msgs in #print axioms detFam_fiber_preserving

/-- info: 'Reformulation.Proemial.ContexturalFibration.fiber_detFam' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms fiber_detFam

/-- info: 'Reformulation.Proemial.ContexturalFibration.reach_stays_in_fiber' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms reach_stays_in_fiber

end
