import Reformulation.Proemial.SelfDetermination

/-!
# Reformulation.Proemial.BranchingCoalgebra — die Verzweigungs-Koalgebra (achtundzwanzigste Schicht)

**AP6-Fundament, kein Stellen-Bau.** Neben der geschlossenen Stellen-Reihe der
achtfachen Thematik (bis 27.) tritt die Verzweigung als **Set-Koalgebra**:
`Branching α := α → Set α` gibt jedem Zustand seine Möglichkeiten. Ihr **Fluss**
ist die auf Inhalte gehobene Koalgebra, und der **Anschluss-Satz** sagt wörtlich,
dass die Geist-Reihe der gabellose Spezialfall war: `flow (det f) = reflect f` —
`reflect` (25.) war die deterministische Verzweigung. Die **Miniatur** (ehrlich
als solche, kein Rang neben den großen Differentialen): die Gabel `fork` ist von
keiner Funktions-Hebung erzeugt — die Verzweigung übersteigt die Reflexion. Die
**Kollaps-Figur** setzt Möglichkeit → Kollaps → Aktualität als Lage-Sätze
(Eindeutigkeit ohne Gabel, ihr Fall an der Gabel); die Irreversibilität des
Kollapses bleibt Deutungs-Anschluss, kein Satz.

**Ein Import** (`SelfDetermination`, transitiv die gesamte Kette und das
Substrat); die Kette wird 16→19→20→22→23→24→25→26→27→28. Term-identisch
konsumiert werden `reflect` (25.), `reflect_singleton` (26.),
`Set.singleton_injective` (rein, Referenz-Liste). Nichts wird dupliziert; **kein
Mathlib-Import über die transitive Hülle hinaus**.

## (1) Quellen-Lage in drei Härten

Die **Chaos-Negation** ist quellen-fest (A2-Bestand) — **ihre Anwendung auf diesen
Bau ist Lesart**. Möglichkeit → Kollaps → Aktualität ist **Projekt-Rede**
(Gestalt §5, kein Zitat). Die „eingefrorenen Zufälle" sind **extern und werden nur
benannt** (Cramer-Umfeld; keine Zitation ohne Autopsie).

## (2) Kein Stellen-Bau

Kein Intervall-Anspruch, keine Orts-Sätze, keine Marken-Trias — AP6-Fundament
neben der geschlossenen Stellen-Reihe.

## (3) Deutungs-Marken

Set-Werte als Möglichkeiten sind **Deutung**; „über den Kontexturen" ist
**A5-Anbindung** (Muster: Kontextur-Lesart der 16.), nicht Träger-Struktur; die
Kollaps-Irreversibilität ist **Deutungs-Anschluss** an die Zeit-Achse; **kein
Physik-Anspruch** (Determinismus und Indeterminismus sind hier Struktur-Begriffe,
keine Natur-Begriffe); Designation ist nicht Denotation.

## (4) Term-fest werden hiermit

Die sechs Sätze `flow_det`, `fork_not_lifted`, `deterministic_flow_lifted`,
`det_collapse_unique`, `fork_collapse_not_unique`, Kür `flow_monotone` (nebst dem
öffentlichen Helfer `flow_singleton` — vom Iterations-Fluss konsumiert).

**KONSUM-EHRLICHKEIT:** eigener Beweis-Gehalt liegt im Anschluss-Satz, in der
Miniatur und in den Kollaps-Sätzen; die leichte Hälfte (`deterministic_flow_lifted`)
reicht den gegebenen Funktions-Zeugen durch. **MINIATUR-EHRLICHKEIT:** das
Differential ist eine Miniatur — arme Klasse „gehobene Flüsse", ein
`Fin 2`-Zeuge; **kein Rang** neben den großen Differentialen (R1: keine Ansprüche
ohne Ist-Prüfung; hier: keiner erhoben).

## (5) Konstruktions-Entscheide

`Deterministic` in **Funktions-Fassung** (`∃ f, ∀ a, c a = {f a}`): die
punktweise Fassung (`∀ a, ∃ b, …`) wäre beim Heben choice-pflichtig; die
Funktions-Fassung hält die Schicht classical-frei.

**Definitions-Form des Flusses — Teil-0-Routen-Entscheid (Vormessung):** die
`⋃ a ∈ S, c a`-Form war bevorzugt, ist aber **nicht wählbar ohne Import über die
Hülle hinaus** — die `⋃`-Notation liegt in `Mathlib.Data.Set.Lattice`, außerhalb
der transitiven Hülle von `SelfDetermination` (gemessen: Parse-Fehler „expected
token" ohne den Zusatz-Import). Gewählt ist darum die extensional gleiche
**setOf-Form** `fun S => {b | ∃ a ∈ S, b ∈ c a}` — Mitgliedschaft definitional
(kein `Set.mem_iUnion₂`), **classical-frei** und **hüllen-treu** (kein Zusatz-
Import), und sie macht die Kür `flow_monotone` **axiom-frei**. Beide Formen sind
extensional gleich; die ärmere, hüllen-treue Form gewinnt (Routen-Bau-Regel).
Vormessung beider Formen: siehe Rubrik (7).

## (6) Abgrenzung

Iterations-Fluss, Koalgebra-Morphismen, Kontextur-Faserung sind benannte
Folge-Pakete mit eigener KS. Der modale Rahmen (Pfad C) und das kategoriale
Coalgebraic-Massiv bleiben unberührt und **nicht konsumiert**. Konditional ist
nichts; gesetzt ist nichts.

## (7) Sorry-Bilanz und Axiom-Ist — mit Vormessungs-Tabelle und Rechnungs-Abgleich

**0 Sorries.** Axiom-Ist (erster grüner Build, v4.30.0-rc2), je Satz
`#guard_msgs`-verwacht am Datei-Ende (sechs Wachen):

* **`[propext, Quot.sound]`:** `flow_det`, `fork_not_lifted`,
  `deterministic_flow_lifted` (Set-Extensionalität; die Singleton-Hüllen reisen
  mit).
* **`[propext]`:** `fork_collapse_not_unique` (`Fin 2`-Insert-Terme plus `decide`).
* **axiom-frei:** `det_collapse_unique` (Singleton-Bereich, definitional — die
  Erwartung „bis `[propext]`" ist zur Axiom-Freiheit eingelöst) und `flow_monotone`
  (setOf-Eigenbeweis).

**Quell-Satz-Vormessung (Teil 0, vor Routen-Wahl):**

* `⋃`-Notation / `Set.mem_iUnion₂`: **außerhalb der Hülle** (`Mathlib.Data.Set.
  Lattice`); zöge einen Zusatz-Import herein. Die `mem_iUnion₂`-Route selbst ist
  classical-frei gemessen (`[propext, Quot.sound]`) — der Ausschluss ist der
  Import-Hülle geschuldet, nicht `Classical`.
* setOf-Form (gewählt): `flow_det`/`flow_singleton` `[propext, Quot.sound]`,
  `flow_monotone` **axiom-frei** — alles in der Hülle.
* `Set.singleton_injective` `[propext, Quot.sound]` (rein; nicht benötigt, da die
  Singleton-Extraktion definitional läuft); Insert- und Singleton-Mitgliedschaft per
  `Or.inl rfl`/`Or.inr rfl` und `Set.mem_singleton_iff` (`[propext]`-Bereich).

**Abgleich gegen die Profil-Rechnung (M6(7), R2 = Erwartung):** getroffen —
`flow_det`/`fork_not_lifted`/`deterministic_flow_lifted` im Set-ext-Bereich,
`fork_collapse_not_unique` im `[propext]`-Bereich, `det_collapse_unique` und die
Kür `flow_monotone` **axiom-frei** (die von der Rechnung als „potenziell
axiom-frei" markierte setOf-Route ist eingelöst, `det_collapse_unique`
unterbietet die Rechnung); **kein `Classical`** an keiner der sechs Stellen.
-/

namespace Reformulation.Proemial.BranchingCoalgebra

open Reformulation.Proemial.ContentReflexivity
open Reformulation.Proemial.MediationProcess

-- ============================================================
-- Teil 1 — Die Definitionen (M1)
-- ============================================================

/-- Die Verzweigung: jedem Zustand seine Möglichkeiten (Set-Werte als
    Möglichkeits-Lesart — Deutung; „über den Kontexturen" ist A5-Anbindung,
    nicht Träger-Struktur; kein Physik-Anspruch). -/
def Branching (α : Type*) := α → Set α

/-- Die deterministische Einbettung: jede Funktion ist eine Verzweigung
    ohne Gabel. -/
def det {α : Type*} (f : α → α) : Branching α := fun a => {f a}

/-- Determinismus in Funktions-Fassung — Konstruktions-Entscheid: die
    punktweise Fassung (`∀ a, ∃ b, …`) wäre beim Heben choice-pflichtig;
    diese Fassung hält die Schicht classical-frei. -/
def Deterministic {α : Type*} (c : Branching α) : Prop :=
  ∃ f : α → α, ∀ a, c a = {f a}

/-- Der Fluss: die Koalgebra, auf Inhalte gehoben. setOf-Form per Teil-0-
    Routen-Entscheid (Modul-Doc (5)): Mitgliedschaft definitional, classical-frei
    und hüllen-treu (die `⋃`-Form läge außerhalb der Import-Hülle). -/
def flow {α : Type*} (c : Branching α) : Set α → Set α :=
  fun S => {b | ∃ a ∈ S, b ∈ c a}

-- ============================================================
-- Teil 2 — Der Anschluss-Satz (M2)
-- ============================================================

/-- DER ANSCHLUSS AN DIE GEIST-REIHE: der Fluss der deterministischen
    Verzweigung ist genau die Hebung der 25. — `reflect` war der gabellose
    Spezialfall der Verzweigung. -/
theorem flow_det {α : Type*} (f : α → α) : flow (det f) = reflect f := by
  funext S
  apply Set.ext
  intro y
  constructor
  · rintro ⟨a, ha, hy⟩
    exact ⟨a, ha, (hy : y = f a).symm⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩

/-- Der Fluss am Einer-Inhalt: Auswertungs-Helfer, öffentlich — der
    Iterations-Fluss (29.) konsumiert ihn (setOf-Route). -/
theorem flow_singleton {α : Type*} (c : Branching α) (a : α) :
    flow c {a} = c a := by
  apply Set.ext
  intro y
  constructor
  · rintro ⟨a', ha', hy⟩
    rw [Set.mem_singleton_iff] at ha'
    subst ha'
    exact hy
  · intro hy
    exact ⟨a, rfl, hy⟩

-- ============================================================
-- Teil 3 — Die Differential-Miniatur (M3)
-- ============================================================

/-- Die Gabel: eine echte Zwei-Möglichkeits-Stelle. -/
def fork : Branching (Fin 2) := fun _ => {0, 1}

/-- DIE VERZWEIGUNG ÜBERSTEIGT DIE REFLEXION (Miniatur, ehrlich als solche;
    kein Rang neben den großen Differentialen): die echte Verzweigung ist
    von keiner Funktions-Hebung erzeugt. Kern: am Einer-Inhalt liefert die
    Hebung Einer (Bahn-Gesetz), die Gabel Zweier; `0 ≠ 1` per `decide`. -/
theorem fork_not_lifted : ∀ f : Fin 2 → Fin 2, flow fork ≠ reflect f := by
  intro f hEq
  have h0 : flow fork ({0} : Set (Fin 2)) = reflect f {0} := by rw [hEq]
  rw [flow_singleton] at h0
  have hr : reflect f ({0} : Set (Fin 2)) = {f 0} := reflect_singleton f 1 0
  rw [hr] at h0
  -- h0 : fork 0 = {f 0}; fork 0 = {0, 1} definitional
  have e0 : (0 : Fin 2) ∈ ({f 0} : Set (Fin 2)) := by rw [← h0]; exact Or.inl rfl
  have e1 : (1 : Fin 2) ∈ ({f 0} : Set (Fin 2)) := by rw [← h0]; exact Or.inr rfl
  rw [Set.mem_singleton_iff] at e0 e1
  exact absurd (e0.trans e1.symm) (by decide)

-- ============================================================
-- Teil 4 — Leichte Hälfte und Kollaps-Figur (M4/M5)
-- ============================================================

/-- Deterministisch → der Fluss ist eine Hebung (der Funktions-Zeuge wird
    durchgereicht — kein Choice). -/
theorem deterministic_flow_lifted {α : Type*} {c : Branching α}
    (h : Deterministic c) : ∃ f : α → α, flow c = reflect f := by
  obtain ⟨f, hf⟩ := h
  exact ⟨f, by rw [show c = det f from funext hf, flow_det]⟩

/-- Der Kollaps: die Aktualisierung wählt aus den Möglichkeiten
    (Möglichkeit → Kollaps → Aktualität: Projekt-Rede, Gestalt §5; die
    Irreversibilität des Kollapses bleibt Deutungs-Anschluss — kein Satz;
    der Kollaps-AKT ist die Spontaneitäts-Grenze). -/
def Collapses {α : Type*} (c : Branching α) (a b : α) : Prop := b ∈ c a

/-- Ohne Gabel genau ein Ausgang. -/
theorem det_collapse_unique {α : Type*} (f : α → α) (a b b' : α)
    (h : Collapses (det f) a b) (h' : Collapses (det f) a b') : b = b' := by
  have hb : b = f a := h
  have hb' : b' = f a := h'
  rw [hb, hb']

/-- An der Gabel nicht (Zeuge a = 0, b = 0, b' = 1). -/
theorem fork_collapse_not_unique :
    ¬ (∀ a b b' : Fin 2, Collapses fork a b → Collapses fork a b' → b = b') := by
  intro h
  exact absurd (h 0 0 1 (Or.inl rfl) (Or.inr rfl)) (by decide)

-- ============================================================
-- Teil 5 — Kür (K1)
-- ============================================================

/-- KÜR: der Möglichkeits-Fluss achtet die Inhalts-Ordnung — das Geschwister
    der 25.-Kür. setOf-Eigenbeweis (axiom-frei, Profil-Messung Modul-Doc (7)). -/
theorem flow_monotone {α : Type*} (c : Branching α) {S T : Set α}
    (h : S ⊆ T) : flow c S ⊆ flow c T := by
  rintro y ⟨a, ha, hy⟩
  exact ⟨a, h ha, hy⟩

end Reformulation.Proemial.BranchingCoalgebra

-- ============================================================
-- Teil 6 — Die `#guard_msgs`-Wachen (M7; Ist-gebunden)
-- ============================================================

-- Ist-Ausgabe des ersten grünen Builds (v4.30.0-rc2), pro Satz als Wache.
open Reformulation.Proemial.BranchingCoalgebra in
section

/-- info: 'Reformulation.Proemial.BranchingCoalgebra.flow_det' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms flow_det

/-- info: 'Reformulation.Proemial.BranchingCoalgebra.fork_not_lifted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms fork_not_lifted

/-- info: 'Reformulation.Proemial.BranchingCoalgebra.deterministic_flow_lifted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms deterministic_flow_lifted

/-- info: 'Reformulation.Proemial.BranchingCoalgebra.det_collapse_unique' does not depend on any axioms -/
#guard_msgs in #print axioms det_collapse_unique

/-- info: 'Reformulation.Proemial.BranchingCoalgebra.fork_collapse_not_unique' depends on axioms: [propext] -/
#guard_msgs in #print axioms fork_collapse_not_unique

/-- info: 'Reformulation.Proemial.BranchingCoalgebra.flow_monotone' does not depend on any axioms -/
#guard_msgs in #print axioms flow_monotone

end
