import Reformulation.Proemial.TowerAsymmetryProbe

/-!
# Proemial.AsymmetricDiscontexturalTransition — die gebündelte KA.4-Struktur, am Turm instanziiert

STANDALONE, NICHT im Aggregat (konsumiert `TowerAsymmetryProbe` und darüber die
Standalone-Sonden `A1DescentProbe`/`ProemialInversionProbe`). Aggregatfähig erst
nach deren Graduierung.

**Ertrag-tragend, aber Struktur = Benennung.** Diese Datei bündelt den in
`TowerAsymmetryProbe` bewiesenen Verbindungssatz zur **Struktur** aus der
KA.4-Skizze: die drei Merkmale von Günthers asymmetrischer Diskontexturalität
als drei **Beweisfelder**, die Kontextur-Identifikation als **ein** markiertes
Setzungsfeld. Die Struktur selbst fügt keinen Satzgehalt hinzu (der steht im
Turm); sie gibt ihm die Form, in der Kern (bewiesen) und Rand (gesetzt) an den
Feldern ablesbar getrennt sind.

## Die Felder

Kern — drei Beweisfelder, je eine Spalte der Matrix:

- `not_reversible : NoReturn ascent` — **Richtung**. Die gerichtete Bewegung ist
  nicht umkehrbar.
- `substructure_preserved : ∀ x, sub x (ascent x)` — **Substruktur-Erhaltung**.
  Das Alte bleibt als Teilstruktur im Neuen (erste Hälfte des Rangverlusts).
- `not_determined : ∃ y a b, a ≠ b ∧ descent a = y ∧ descent b = y` —
  **Determinationsverlust**. Der Abstieg hat nichttriviale Fasern; die
  Aufwärtsbewegung ist nicht determiniert (zweite Hälfte des Rangverlusts).

Rand — ein markiertes Setzungsfeld (B5-Disziplin, `True`, KEIN Beweis):

- `contextureCrossing : True` — die Identifikation „Stufenwechsel =
  Kontexturwechsel". Sie ist Definitionswahl, nicht Satz. Genau **ein**
  Deutungsfeld, keine `True`-Feld-Inflation.

## Warum genau diese Trennung

Der Verbindungssatz (`TowerAsymmetryProbe.tower_asymmetric`) beweist die drei
Kern-Felder an einem konkreten Träger. Was er **nicht** beweist — dass der
Stufenwechsel ein Kontexturwechsel im Günther-Sinn ist —, sitzt im einen
`True`-Feld, sichtbar als Setzung markiert. Damit entscheidet die Instanz KA
**modulo** dieser Setzung: der strukturelle Bruch ist gebaut und geprüft, seine
Identifikation mit Günthers Begriff bleibt beglaubigungspflichtige Lesart. Die
Kontexturgrenze-Spalte schließt prinzipiell nur Definition plus Satz — das
`True`-Feld ist die Definitionshälfte, ehrlich als solche geführt.

Kein `sorry`, kein `axiom`. Das eine `True`-Feld ist die bewusste Setzung, kein
Platzhalter für Fehlendes.
-/

namespace Reformulation.Proemial.AsymmetricTransition

open Reformulation.Kenogram
open Reformulation.Proemial.A1DescentProbe (descent)
open Reformulation.Proemial.IrreversibleAdvance (NoReturn)
open Reformulation.Proemial.TowerAsymmetryProbe
  (Tower step step_noreturn step_preserves_substructure ascent_not_determined)

-- ============================================================
-- §I — Die gebündelte Struktur
-- ============================================================

/-- **Die KA.4-Struktur.** Ein gerichteter Übergang mit den drei bewiesenen
Kern-Merkmalen und der einen markierten Kontextur-Setzung. Träger, Auf- und
Abstieg sowie die Substruktur-Relation sind Daten; die vier letzten Felder
tragen Kern (drei Beweise) und Rand (ein `True`). -/
structure AsymmetricDiscontexturalTransition where
  /-- Der Träger des Übergangs. -/
  Carrier : Type
  /-- Der gerichtete Aufstiegs-Schritt (Relatum → Relator). -/
  ascent : Carrier → Carrier
  /-- Der Abstieg / die Vergröberung. -/
  descent : Carrier → Carrier
  /-- Die Substruktur-Relation („ist Teilstruktur von"). -/
  sub : Carrier → Carrier → Prop
  /-- **Beweisfeld — Richtung.** Der Aufstieg ist rückkehrfrei. -/
  not_reversible : NoReturn ascent
  /-- **Beweisfeld — Substruktur.** Das Alte bleibt Teilstruktur im Neuen. -/
  substructure_preserved : ∀ x, sub x (ascent x)
  /-- **Beweisfeld — Determinationsverlust.** Der Abstieg hat nichttriviale
      Fasern. -/
  not_determined : ∃ y a b, a ≠ b ∧ descent a = y ∧ descent b = y
  /-- **Setzungsfeld (Rand, KEIN Beweis).** Die Identifikation „Stufenwechsel =
      Kontexturwechsel" — B5-Disziplin, als Setzung markiert. -/
  contextureCrossing : True

-- ============================================================
-- §II — Der totale Turm-Abstieg
-- ============================================================

/-- Der Turm-Abstieg als **totale** Funktion `Tower → Tower`: auf Stufe `n+1`
der A1-Abstieg `RGS (n+1) → RGS n`, auf Stufe `0` die Identität (nichts
abzusteigen). Die Totalisierung berührt die Zeugen nicht — der Verlust-Zeuge
lebt auf Stufe `3 → 2`. -/
def towerDescent : Tower → Tower
  | ⟨0, r⟩ => ⟨0, r⟩
  | ⟨n + 1, r⟩ => ⟨n, descent r⟩

/-- Die Substruktur-Relation auf dem Turm: Präfix-Beziehung der Ketten. -/
def towerSub (x y : Tower) : Prop := x.2.val <+: y.2.val

-- ============================================================
-- §III — Die Turm-Instanz
-- ============================================================

/-- **Die Instanz (Ertrag am Zeugen).** Der Turm erfüllt die KA.4-Struktur: die
drei Kern-Felder aus `TowerAsymmetryProbe` (Richtung, Substruktur,
Determinationsverlust), das eine `True`-Feld als markierte Kontextur-Setzung.

Der Determinationsverlust-Zeuge ist konkret die nichttriviale Faser über
`[0,1] : RGS 2`: `[0,1,0]` und `[0,1,2]` (beide `RGS 3`) steigen beide zu
`[0,1]` ab. Er instanziiert das generische `ascent_not_determined` an Stufe 2. -/
def towerTransition : AsymmetricDiscontexturalTransition where
  Carrier := Tower
  ascent := step
  descent := towerDescent
  sub := towerSub
  not_reversible := step_noreturn
  substructure_preserved := step_preserves_substructure
  not_determined := by
    refine ⟨⟨2, ⟨[0, 1], by decide⟩⟩,
            ⟨3, ⟨[0, 1, 0], by decide⟩⟩,
            ⟨3, ⟨[0, 1, 2], by decide⟩⟩, ?_, ?_, ?_⟩
    · intro h; injection h with h1 h2; exact absurd h2 (by decide)
    · apply Sigma.ext rfl; apply heq_of_eq; apply Subtype.ext; decide
    · apply Sigma.ext rfl; apply heq_of_eq; apply Subtype.ext; decide
  contextureCrossing := trivial

/-- Der Determinationsverlust der Instanz ist **nicht** leer gesetzt: das Feld
`not_determined` trägt einen echten Zeugen — hier als eigener Satz vorgezeigt,
damit die Nicht-Trivialität des Kern-Felds aktenkundig ist. Zugleich der
Anschluss an das generische `ascent_not_determined` (alle Stufen ab 1). -/
theorem towerTransition_not_determined :
    ∃ y a b, a ≠ b ∧ towerDescent a = y ∧ towerDescent b = y :=
  towerTransition.not_determined

-- ============================================================
-- Wachen — Axiom-Profile
-- ============================================================

/-! **Wachen.** Ist-Ausgabe des grünen Builds (v4.30.0-rc2). Die Instanz
`towerTransition` erbt über ihre Kern-Felder die Turm-Profile; die
`not_determined`-Konstruktion (Sigma- und Subtype-Gleichheiten per `decide`) und
das `True`-Feld fügen kein Axiom hinzu. `towerTransition_not_determined` sichert
das Nicht-Leersein des Verlust-Felds als eigener gewachter Satz. -/

/-- info: 'Reformulation.Proemial.AsymmetricTransition.towerTransition' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms towerTransition

/-- info: 'Reformulation.Proemial.AsymmetricTransition.towerTransition_not_determined' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms towerTransition_not_determined

end Reformulation.Proemial.AsymmetricTransition
