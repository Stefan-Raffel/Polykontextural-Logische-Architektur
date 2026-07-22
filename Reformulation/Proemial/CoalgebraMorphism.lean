import Reformulation.Proemial.FlowIteration

/-!
# Reformulation.Proemial.CoalgebraMorphism — die Koalgebra-Morphismen (dreißigste Schicht)

**AP6-Zug-3, reiner Term-Zug.** Der Morphismus zwischen Verzweigungen ist die
**Bild-Vertauschung** `IsMorphism h c d := ∀ a, h '' c a = d (h a)` (strikte
Fassung; die laxe `⊆`-Variante ist benannt, nicht gebaut). Der Haupt-Satz sagt,
dass **der Fluss morphismus-treu ist** (`h '' flow c S = flow d (h '' S)`) — die
punktweise Bedingung hebt sich auf die Inhalte; die Kür verpflanzt die Bahnen
(`h '' reachSet c n a = reachSet d n (h a)`). Der Zeuge ist die
**Selbst-Äquivarianz**: jede Funktion ist Morphismus ihrer eigenen
deterministischen Verzweigung — eine Konsum-Zeile am Defeq (der Zeuge *ist* das
Bahn-Gesetz der 26. am Punkt).

**Ein Import** (`FlowIteration`, transitiv die gesamte Kette und das Substrat);
die Kette wird 16→…→29→30. Term-identisch konsumiert werden `Branching`, `det`,
`flow` (28.), `reachSet` (29.), `reflect_singleton` (26., am endo-Zeugen),
`Function.iterate_succ_apply'` (Referenz-Liste, `[propext, Quot.sound]`). Nichts
wird dupliziert; **kein Mathlib-Import über die transitive Hülle hinaus**.

## (1) Bestands-Lage

Reiner Term-Zug, keine Quellen-Berührung; kein Stellen-Bau (kein Intervall, keine
Marken-Trias); AP6-Zug-3 auf dem Fundament der 28./29.

## (2) ABGRENZUNGS-MARKE (Pflicht)

„Morphismus" ist **elementare kategoriale Rede, kein Apparat** — **kein
Kategorien-Framework** importiert, das `Classical`-lastige F1-Coalgebraic-Massiv
**nicht konsumiert**; strikte Gleichheits-Fassung, die laxe `⊆`-Variante
**benannt, nicht gebaut**. Keine Kategorie als Objekt, keine Funktoren.

## (3) Deutungs-Marken

`reflect`-Verwandtschaft: das `reflect` der 25. ist endo (`α → α`); für heterogenes
`h : α → β` tritt `Set.image h` direkt an — **dieselbe Konstruktion, allgemeiner
Typ**. „Der Fluss ist morphismus-treu" und „Bahnen-Verpflanzung" sind **markierte
Struktur-Aussagen** (Projekt-Rede); kein Physik-Anspruch; Designation ist nicht
Denotation.

## (4) Term-fest werden hiermit

Die fünf Sätze `morphism_id`, `morphism_comp`, `morphism_flow`,
`det_selfmorphism`, Kür `morphism_reach` (nebst dem **privaten** Helfer
`image_singleton_het` — heterogenes Einer-Bild, kein absehbarer Fremd-Konsum;
Wort und Schlüsselwort deckungsgleich, Lehre des 28.-Sammelpostens).

**KONSUM-EHRLICHKEIT:** `det_selfmorphism` (M5) ist **reine Konsum-Zeile** — der
Zeuge ist das Bahn-Gesetz der 26. (`reflect_singleton`) am Punkt, beide Seiten per
Defeq; eigener Beweis-Gehalt liegt in `morphism_flow` (M4) und der Kür-Induktion.
`morphism_id`/`morphism_comp` (M2/M3) sind **Konsum** der classical-freien
Bild-Lemmata `Set.image_id`/`Set.image_comp` (Vormessungs-Ausgang, Rubrik (6)).

## (5) Abgrenzung

Der **Ketten-Satz** ist **benannt, nicht gebaut** — nach den Morphismen würde er
schöner (Ketten unter Morphismen-Bildern erhalten: ein Satz statt zweier). Die
**Kontextur-Faserung ist Zug 4, der AP6-Schluss**. Keine Kategorie als Objekt;
konditional ist nichts, gesetzt ist nichts.

## (6) Sorry-Bilanz und Axiom-Ist — mit Vormessung und Rechnungs-Abgleich

**0 Sorries.** Axiom-Ist (erster grüner Build, v4.30.0-rc2), je Satz
`#guard_msgs`-verwacht am Datei-Ende (fünf Wachen): **alle fünf**
`[propext, Quot.sound]`.

**Quell-Satz-Vormessung (Teil 0 (1), vor Routen-Wahl):**

* `Set.image_id` — `[propext, Quot.sound]` (**classical-frei**, benutzt in
  `morphism_id`).
* `Set.image_comp` — `[propext, Quot.sound]` (**classical-frei**, benutzt in
  `morphism_comp`).
* Kontrast (Referenz-Liste): `Set.image_singleton`/`image_empty`/`image_mono`
  tragen in diesem Mathlib `Classical.choice` — darum das heterogene Einer-Bild
  `image_singleton_het` als **Eigenbeweis** (ext + `rintro`), `[propext,
  Quot.sound]`, kein `Classical`.
* `reflect_singleton f 1 (f a)` trägt `det_selfmorphism` per Defeq
  (`[propext, Quot.sound]`); `Function.iterate_succ_apply'` `[propext, Quot.sound]`
  (Referenz).

**Abgleich gegen die Profil-Rechnung (M6(6), R2 = Erwartung):** getroffen an allen
fünf — die vier Muss-Sätze im Set-ext-Bereich `[propext, Quot.sound]`, die Kür
erbt zusätzlich `iterate_succ_apply'` auf gleichem Niveau; **kein `Classical`** an
keiner Stelle (die Bild-Lemmata `image_id`/`image_comp` sind classical-frei —
gemessen, kein Hüllen-Schicksal).
-/

namespace Reformulation.Proemial.CoalgebraMorphism

open Reformulation.Proemial.BranchingCoalgebra
open Reformulation.Proemial.FlowIteration
open Reformulation.Proemial.ContentReflexivity
open Reformulation.Proemial.MediationProcess

-- ============================================================
-- Teil 1 — Die Definition (M1)
-- ============================================================

/-- Der Koalgebra-Morphismus als Bild-Vertauschung: die Abbildung, unter der
    die Möglichkeiten des Urbilds genau die Möglichkeiten des Bildes sind
    (Standard-Bedingung der Set-Koalgebren, elementar; strikte Fassung — die
    laxe `⊆`-Variante ist benannt, nicht gebaut). Elementare kategoriale Rede,
    kein Apparat. -/
def IsMorphism {α β : Type*} (h : α → β) (c : Branching α) (d : Branching β) :
    Prop :=
  ∀ a, h '' c a = d (h a)

-- ============================================================
-- Teil 2 — Identität und Komposition (M2/M3)
-- ============================================================

/-- Die Identität ist Morphismus jeder Verzweigung (Konsum von `Set.image_id`,
    classical-frei per Vormessung). -/
theorem morphism_id {α : Type*} (c : Branching α) : IsMorphism id c c :=
  fun a => Set.image_id (c a)

/-- Morphismen komponieren (Konsum von `Set.image_comp`, dann die zwei
    Voraussetzungen der Reihe nach; der letzte Schritt am Defeq von `∘`). -/
theorem morphism_comp {α β γ : Type*} {h : α → β} {k : β → γ}
    {c : Branching α} {d : Branching β} {e : Branching γ}
    (hh : IsMorphism h c d) (hk : IsMorphism k d e) :
    IsMorphism (k ∘ h) c e := by
  intro a
  show (k ∘ h) '' c a = e (k (h a))
  rw [Set.image_comp, hh a, hk (h a)]

-- ============================================================
-- Teil 3 — Der Haupt-Satz (M4)
-- ============================================================

/-- „DER FLUSS IST MORPHISMUS-TREU": der Fluss vertauscht mit dem Bild
    entlang jedes Morphismus — die punktweise Bedingung hebt sich auf die
    Inhalte (Hebungs-Motiv der Geist-Reihe, zwischen zwei Koalgebren).
    Eigenbeweis auf den setOf-Routen der 28. -/
theorem morphism_flow {α β : Type*} {h : α → β}
    {c : Branching α} {d : Branching β}
    (hm : IsMorphism h c d) (S : Set α) :
    h '' flow c S = flow d (h '' S) := by
  apply Set.ext
  intro y
  constructor
  · rintro ⟨b, ⟨a, haS, hb⟩, rfl⟩
    exact ⟨h a, ⟨a, haS, rfl⟩, hm a ▸ ⟨b, hb, rfl⟩⟩
  · rintro ⟨x, ⟨a, haS, rfl⟩, hy⟩
    rw [← hm a] at hy
    obtain ⟨b, hb, rfl⟩ := hy
    exact ⟨b, ⟨a, haS, hb⟩, rfl⟩

-- ============================================================
-- Teil 4 — Der Zeuge (M5)
-- ============================================================

/-- SELBST-ÄQUIVARIANZ: jede Funktion ist Morphismus ihrer eigenen
    deterministischen Verzweigung — Konsum-Zeile am Defeq (`reflect_singleton`
    der 26. am Punkt, Muster der 27.). -/
theorem det_selfmorphism {α : Type*} (f : α → α) :
    IsMorphism f (det f) (det f) :=
  fun a => reflect_singleton f 1 (f a)

-- ============================================================
-- Teil 5 — Kür (K1)
-- ============================================================

/-- Heterogenes Einer-Bild: `h '' {a} = {h a}` (privater Helfer, Eigenbeweis —
    nicht `Set.image_singleton`, das in diesem Mathlib `Classical` trägt). -/
private theorem image_singleton_het {α β : Type*} (h : α → β) (a : α) :
    h '' ({a} : Set α) = {h a} := by
  apply Set.ext
  intro y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    rfl
  · intro hy
    rw [Set.mem_singleton_iff] at hy
    exact ⟨a, rfl, hy.symm⟩

/-- KÜR — „DIE BAHNEN-VERPFLANZUNG" (markierte Struktur-Aussage): die
    Erreichbarkeit ist morphismus-treu. Basis: heterogenes Einer-Bild
    (`image_singleton_het`); Schritt: `iterate_succ_apply'` + Haupt-Satz + IH. -/
theorem morphism_reach {α β : Type*} {h : α → β}
    {c : Branching α} {d : Branching β}
    (hm : IsMorphism h c d) (n : ℕ) (a : α) :
    h '' reachSet c n a = reachSet d n (h a) := by
  induction n with
  | zero =>
      show h '' ({a} : Set α) = {h a}
      exact image_singleton_het h a
  | succ n ih =>
      have ih' : h '' (flow c)^[n] {a} = (flow d)^[n] {h a} := ih
      show h '' (flow c)^[n + 1] {a} = (flow d)^[n + 1] {h a}
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        morphism_flow hm, ih']

end Reformulation.Proemial.CoalgebraMorphism

-- ============================================================
-- Teil 6 — Die `#guard_msgs`-Wachen (M7; Ist-gebunden)
-- ============================================================

-- Ist-Ausgabe des ersten grünen Builds (v4.30.0-rc2), pro Satz als Wache.
open Reformulation.Proemial.CoalgebraMorphism in
section

/-- info: 'Reformulation.Proemial.CoalgebraMorphism.morphism_id' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms morphism_id

/-- info: 'Reformulation.Proemial.CoalgebraMorphism.morphism_comp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms morphism_comp

/-- info: 'Reformulation.Proemial.CoalgebraMorphism.morphism_flow' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms morphism_flow

/-- info: 'Reformulation.Proemial.CoalgebraMorphism.det_selfmorphism' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms det_selfmorphism

/-- info: 'Reformulation.Proemial.CoalgebraMorphism.morphism_reach' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms morphism_reach

end
