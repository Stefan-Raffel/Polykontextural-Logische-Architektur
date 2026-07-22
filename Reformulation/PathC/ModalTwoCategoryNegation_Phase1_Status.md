# ModalTwoCategoryNegation — Phase 1 Status

*Reformulation.PathC.ModalTwoCategoryNegation*
*Datum: 2026-05-17*

---

## (i) Kompilierungs-Status

Alle Sub-Aufgaben kompilieren ohne Fehler. Build-Ergebnis:

```
✔ [1265/1265] Built Reformulation.PathC.ModalTwoCategoryNegation (1.6s)
Build completed successfully (1265 jobs)
```

Keine sorry-Stellen. Alle Definitionen, Strukturen, induktiven Typen und
Theoreme kompilieren durch.

**Sub-Aufgaben im Einzelnen:**

| Sub-Aufgabe | Status |
|-------------|--------|
| Datei-Anlage und Modul-Struktur | ✓ kompiliert |
| `NegationEndofunctor` mit Kompositions-Defs | ✓ kompiliert |
| `NegationCompositionClass` (5-Klassen, `classify`, `isSmooth`) | ✓ kompiliert |
| `MixedCompositionClass` (3-Klassen) | ✓ kompiliert |
| `NegTauInvolution` / `NegDeltaRoughness` / `NegOmegaRoughness` | ✓ kompiliert |
| `ModalTwoCategoryWithNegations extends ModalTwoCategory E` | ✓ kompiliert |
| Existenz-Theoreme (5 Klassen, Involutions-Zeugen) | ✓ alle `rfl` |
| Klassifikations-Theoreme | ✓ alle `rfl` |
| `isSmooth`-Theoreme | ✓ alle `simp` |

---

## (ii) Mathlib API-Lücken

Keine Mathlib-API-Lücken aufgetreten. Alle verwendeten Konstrukte sind
in Mathlib vorhanden:

- `F ≅ G` für Funktoren (Iso im Funktor-Kategorie-Sinne) — verfügbar via
  Standard-CategoryTheory-Imports.
- `Nonempty` für propositionale Existenz-Markierungen — Standard.
- `¬ Nonempty` für Rauheits-Assertions — kein `TODO Mathlib API` erforderlich.
- `deriving DecidableEq, Repr` für beide induktive Typen — kompiliert ohne
  Hilfs-Instanzen.

---

## (iii) Aufwands-Empirie

**Antizipierter Aufwand:** eine halbe Sitzung (§III.21 Aufwand-Antizipation).

**Tatsächlicher Aufwand:** eine halbe Sitzung — methodologisch im
antizipierten Rahmen. Keine 20×-Disparität (im Gegensatz zur cone_objs-Folge).

Begründung: Phase 1 tragt ausschließlich Grund-Strukturen ohne Beweise über
kategorielle Konstruktionen hinaus. Die Existenz- und Klassifikations-Theoreme
schließen alle per `rfl` (Definitional-Gleichheit durch `abbrev negEndo`), die
`isSmooth`-Theoreme per `simp`. Keine Lean-API-Komplexität.

Antizipation für Phase 2 (Theorem 1: Klassifikations-Erschöpfung): höhere
Disparität wahrscheinlich, wenn die Klassifikations-Funktion komplexe
Induktions-Struktur über `List ModalSymbol` verlangt.

---

## (iv) Konsistenz-Prüfung gegenüber ModalTwoCategory

**Konsistent in allen Kern-Aspekten:**

| Aspekt | ModalTwoCategory | ModalTwoCategoryWithNegations |
|--------|------------------|-------------------------------|
| Haupt-Struktur-Form | `structure ... extends ModalEndofunctor E` | `structure ... extends ModalTwoCategory E` |
| Kompositions-Klasse | `inductive CompositionClass` (4 Konstruktoren) | `inductive NegationCompositionClass` (5 Konstruktoren) |
| `deriving` | `DecidableEq, Repr` | `DecidableEq, Repr` |
| `classify`-Funktion | String → CompositionClass | String → NegationCompositionClass |
| `isSmooth`-Funktion | Pattern-match → Prop | Pattern-match → Prop |
| Compat-2-Morphismen | `𝟭 E ⟶ (delta ⋙ tau ⋙ omega)` | `𝟭 E ⟶ (negDelta ⋙ negTau ⋙ negOmega)` |
| Existenz-Theoreme | `∃ η, η = M.compatTriple1` via `rfl` | `∃ η, η = M.negCompatTriple1` via `rfl` |
| isSmooth-Theoreme | `by simp [CompositionClass.isSmooth]` | `by simp [NegationCompositionClass.isSmooth]` |
| Universe-Parameter | `universe u v` / `[Category.{v} E]` | identisch |
| Namensraum | `Reformulation.PathC` | identisch |

**Einzige substantielle Erweiterung gegenüber ModalTwoCategory:**

Die Involutions-Daten (`negTauInvolLeft`, `negTauInvolRight` als `≅`-Felder)
sind in ModalTwoCategory ohne Parallele — dort ist Rauheit *implizit*
(Abwesenheit von Feldern). Für die Negations-Form ist die explizite
Involutions-Iso-Form methodologisch notwendig (die Unterscheidung
trivial_bis2Iso vs. trivial_rough ist substantiell). Die Rauheits-Prop-Strukturen
(`NegDeltaRoughness`, `NegOmegaRoughness`) ergänzen die implizite Rauheit mit
expliziten Zeugen, ohne die PathC-Konvention zu verletzen.

**Zirkuläre Import-Prüfung:**

Korrekte Import-Richtung: `ModalTwoCategoryNegation` importiert
`ModalTwoCategory`, nicht umgekehrt. `ModalTwoCategory.lean` bleibt
unberührt. Keine zirkuläre Abhängigkeit.

---

## Eingangsmarkierung für Phase 2

Phase 1 ist methodologisch abgeschlossen. Für Phase 2 (Theoreme 1 und 2):

**Theorem 1 (Klassifikations-Erschöpfung):** verlangt eine
`negationCompositionClassification`-Funktion über `List ModalSymbol`
(oder `List (E ⥤ E)`), die zeigt, dass die 5 Klassen erschöpfend und
disjunkt sind. Die `classify`-Funktion in Phase 1 ist String-basiert;
Phase 2 muss eine struktur-basierte Klassifikation über die
Funktor-Listen tragen.

**Theorem 2 (Subjektstellen-Differenzierung):** verlangt einen
Widerspruchs-Beweis zwischen `NegTauInvolution` (2-Iso existiert) und
`NegDeltaRoughness` / `NegOmegaRoughness` (kein 2-Iso). Der
konstruktive Kern: Annahme von `negUnified` mit allen drei Involutionen
führt zu Widerspruch mit `noResolutionLeft`/`noResolutionRight`.

Phase 2 verlangt eine eigene Aufgabe mit Voraussetzungs-Klärung, ob
Theorem 1 über `decide` (für endliche Mengen von Kompositions-Namen)
oder über strukturelle Induktion geführt wird.
