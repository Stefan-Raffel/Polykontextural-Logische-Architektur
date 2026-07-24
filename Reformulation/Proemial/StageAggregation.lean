import Reformulation.Proemial.GeneralCloneBound

/-!
# Proemial.StageAggregation — die Anwendungsbrücke: Stufenaggregation (E4)

**Benennung.** Diese Datei liefert **keinen neuen Satz**. Der Anwendungssatz
`agg_nicht_erzeugbar` ist eine **Instanz von E3**
(`GeneralCloneBound.locally_classical_in_clone_iff`, spezialisiert auf m = 4);
neu sind allein die Daten — ein konkreter Zeuge `agg` und zwei Widerlegungspunkte.
Was hinzukommt, ist die **Lesart**, und die ist Deutung, kein Satzgehalt
(CLAUDE.md §4). Der Dateiname sagt, was gebaut ist — `StageAggregation`, nicht
`Mediation` und nicht `PolicyBridge` (Marke 3).

## Die Lesart

`Fin 4` als vier linear geordnete **Autorisierungsstufen**, `agg` als
**Aggregationspolitik**, ein Term über `L` als **Verschaltung lokaler, kontextur-
blinder Prüfer**. Kontextur-blinde Prüfer sind intra-kontexturelle Operationen
(`Definitionen.md` §9); ein Term über `L` ist ihre Verschaltung, gleich in welcher
Tiefe. Unter dieser Lesart sagt E3:

> Eine Politik, die in verschiedenen Stufenbereichen verschieden aggregiert, lässt
> sich aus lokalen, kontextur-blinden Prüfern **nicht zusammensetzen** — gleich in
> welcher Verschaltung und gleich wie viele.

Mit `agg_nicht_erzeugbar_konstanten` gilt das auch dann, wenn man beliebige
**konstante Prüfer** („liefere immer Stufe k") als Bausteine hinzunimmt.

## Die Anwendungsschwelle: vier Stufen

**Bei drei Stufen wäre der Satz falsch.** E1 (`NonUniformCloneBound`) zeigt, dass
bei m = 3 vier der acht Wahlmuster erzeugbar sind — mit nur drei
Autorisierungsstufen sind manche gemischten Politiken sehr wohl aus lokalen
Prüfern komponierbar. **Vier Stufen sind die erste Wertzahl, ab der jede echt
gemischte, lokal-klassische Politik unkomponierbar ist** (E3, für alle m ≥ 4). Die
Schranke hat eine Anwendungsschwelle, und sie ist im Bestand bewiesen, nicht
behauptet.

## Die Grenze — und warum sie begrifflich ist

Die Schranke greift auf **linear gestuften** Trägern. Der Grund ist nicht die
Beweistechnik: eine Zweiermenge `{x, y}` ist unter `min`/`max` **genau dann
abgeschlossen, wenn `x` und `y` vergleichbar sind**. Auf unvergleichbaren Paaren
liegt das Infimum außerhalb von `{x, y}` — die lokale Operation verlässt die
Menge, und diese ist dann keine Elementarkontextur im Sinne von `Definitionen.md`
§2 (ein in sich geschlossener zweiwertiger Zusammenhang). **Die Grenze liegt im
Begriff, nicht im Beweis.**

Auf nicht-linearen Verbänden fällt die Charakterisierung tatsächlich: bereits am
kleinsten flachen Verband `M3` ist ein lokal-klassischer Term konstruierbar, der
weder Infimum noch Supremum ist (Sonden-Befund der E4-Begutachtung,
**außerhalb des Korpus gerechnet**, Gegenbeispiel von Hand nachgerechnet; die
Zahlen bleiben außerhalb, CLAUDE.md §6). Ein Übergangsgraph benannter Rollen ohne
Stufenordnung wird von dieser Schranke **nicht** getragen; was dort beweisbar
bleibt, ist Erreichbarkeit in einem endlichen Graphen und leistet nichts, was ein
Typsystem nicht auch leistet.

## Robustheit (CLAUDE.md §9)

Die Invariante `R 4` ist **reflexiv** (`GeneralCloneBound.R_diag`); darum überlebt
die Schranke die Erweiterung der Signatur um **alle vier Konstanten** — Kontrast zu
`TransjunctionCloneBound`, dessen `{0,2}`-Schranke an der `1`-Konstante fiel. In
der Anwendungslesart ist das die tragende Hälfte: ein konstanter Prüfer ist der
natürlichste Baustein überhaupt, den ein Autorisierungssystem hat.

## Wortlaut-Grenzen

1. **Keine Behauptung über AI-Systeme.** Der Satz handelt von
   Aggregationsfunktionen auf endlichen Stufenmengen. Dass Autorisierungsmodelle
   so gebaut sind, ist eine Anwendungsannahme, keine Folgerung.
2. **Keine Sicherheitsgarantie.** Die Schranke sagt, was aus lokalen Bausteinen
   nicht zusammensetzbar ist. Sie sagt nicht, dass ein System mit Vermittler
   sicher ist.
3. Die Grenzziehung **widerlegt** die Anwendungsnotiz nicht — sie beschneidet sie
   auf ihren eigenen stärksten Punkt (Nicht-Internalität), verlegt auf gestufte
   Träger.

Fallstrick 2 (CLAUDE.md §8): `LocallyClassical` ist ein `def`, `decide` sieht nicht
hindurch — `unfold LocallyClassical ActsAsMin ActsAsMax` davor.

0 Sorries; kein Satz zieht `Classical.choice`.
-/

open FirstOrder Language
open Reformulation.Proemial.TransjunctionCloneBound (L)
open Reformulation.Proemial.GeneralCloneBound

namespace Reformulation.Proemial.StageAggregation

/-! ## Teil 1 — Stufenmodell und Politik -/

/-- Vier Autorisierungsstufen, linear geordnet (Lesart; term-fest ist `Fin 4`). -/
abbrev Stufe := Fin 4

/-- Die Aggregationspolitik: konservativ (Minimum) überall — außer zwischen den
beiden höchsten Stufen, wo permissiv (Maximum) aggregiert wird. Genau diese
Mischung macht sie zum Zeugen: auf jeder Elementarkontextur klassisch, im ganzen
weder `min` noch `max`. -/
def agg (a b : Stufe) : Stufe :=
  if (a = 2 && b = 3) || (a = 3 && b = 2) then max a b else min a b

/-! ## Teil 2 — die beiden Voraussetzungen und der Anwendungssatz -/

/-- **`agg` ist lokal klassisch:** auf jeder Elementarkontextur `{x, y}` wirkt sie
wie `min` oder wie `max`. Fallstrick 2: `unfold` vor `decide`. -/
theorem agg_lokal : LocallyClassical agg := by
  unfold LocallyClassical ActsAsMin ActsAsMax; decide

/-- **Der Anwendungssatz (E4): `agg` ist nicht erzeugbar.** Keine Verschaltung
lokaler, kontextur-blinder Prüfer liefert die Politik — gleich in welcher Tiefe.
Eine **Instanz von E3**, kein neuer Satz: die `mp`-Richtung von
`locally_classical_in_clone_iff` plus zwei Widerlegungspunkte, `(2,3)` gegen `min`
und `(0,1)` gegen `max`. -/
theorem agg_nicht_erzeugbar :
    ¬ ∃ t : L.Term (Fin 2), ∀ v, t.realize v = agg (v 0) (v 1) := by
  intro h
  rcases (locally_classical_in_clone_iff (m := 4) (by omega) agg agg_lokal).mp h with h1 | h1
  · have hp := congrFun (congrFun h1 2) 3; revert hp; decide
  · have hp := congrFun (congrFun h1 0) 1; revert hp; decide

/-- **Robustheit nach CLAUDE.md §9:** auch mit beliebigen konstanten Prüfern als
Bausteinen bleibt `agg` unkomponierbar. Träger ist die Reflexivität von `R 4`
(`R_diag`), über die E3 die Konstanten-Fassung `constant_clone_min_or_max`
bereitstellt. -/
theorem agg_nicht_erzeugbar_konstanten :
    ¬ ∃ t : (Lc 4).Term (Fin 2), ∀ v, t.realize v = agg (v 0) (v 1) := by
  intro h
  rcases constant_clone_min_or_max (m := 4) (by omega) agg agg_lokal h with h1 | h1
  · have hp := congrFun (congrFun h1 2) 3; revert hp; decide
  · have hp := congrFun (congrFun h1 0) 1; revert hp; decide

/-! ## Teil 3 — Statement-Pins

Voller Wortlaut links, Satz rechts — jede Drift des *Statements* bricht den Build.
Namenlose `example`s, keine Axiom-Wache. -/

-- STATEMENT-PIN
example : ∀ x y : Fin 4, x ≠ y →
    (∀ a b : Fin 4, (a = x ∨ a = y) → (b = x ∨ b = y) → agg a b = min a b) ∨
    (∀ a b : Fin 4, (a = x ∨ a = y) → (b = x ∨ b = y) → agg a b = max a b) :=
  agg_lokal

-- STATEMENT-PIN
example : ¬ ∃ t : L.Term (Fin 2), ∀ v : Fin 2 → Fin 4,
    t.realize v = agg (v 0) (v 1) :=
  agg_nicht_erzeugbar

-- STATEMENT-PIN
example : ¬ ∃ t : (Lc 4).Term (Fin 2), ∀ v : Fin 2 → Fin 4,
    t.realize v = agg (v 0) (v 1) :=
  agg_nicht_erzeugbar_konstanten

/-! ## Teil 4 — die Axiom-Wachen (Ist-gebunden)

Ist-Ausgabe des grünen Builds (v4.30.0-rc2), pro Satz als Regressions-Wache
eingefroren (Datei-Vollständigkeits-Regel: alle drei Sätze der Datei). **Kein Satz
zieht `Classical.choice` oder `sorryAx`.** -/

/-- info: 'Reformulation.Proemial.StageAggregation.agg_lokal' depends on axioms: [propext] -/
#guard_msgs in #print axioms agg_lokal

/-- info: 'Reformulation.Proemial.StageAggregation.agg_nicht_erzeugbar' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms agg_nicht_erzeugbar

/-- info: 'Reformulation.Proemial.StageAggregation.agg_nicht_erzeugbar_konstanten' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms agg_nicht_erzeugbar_konstanten

end Reformulation.Proemial.StageAggregation
