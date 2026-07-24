import Reformulation.Kenogram.Basic
import Reformulation.Proemial.A1DescentProbe        -- descent
import Reformulation.Proemial.ProemialInversionProbe -- extend, descent_extend
import Reformulation.Proemial.IrreversibleAdvance    -- NoReturn, noreturn_of_strict_rank

/-!
# Proemial.TowerAsymmetryProbe — der Verbindungssatz der asymmetrischen Diskontexturalität

STANDALONE, NICHT im Aggregat (konsumiert `A1DescentProbe` und
`ProemialInversionProbe`, beide standalone). Erst wenn diese Sonden den
Sonden-Status verlassen, kann diese Datei aggregatfähig werden.

**Ertrag** (nicht bloß Benennung). Diese Sonde baut den in der KA-Notiz und der
Fortgangs-Empfehlung angegebenen **Entscheidungssatz**: den ersten Zeugen, der
die drei Merkmale, die Günthers asymmetrische Diskontexturalität *zugleich*
verlangt, in **einem** Satz bindet — bisher lagen sie auf getrennte Zeugen
verteilt (Dreispalten-Matrix Richtung / Kontexturgrenze / Rangverlust; keine
Zeile besetzte mehr als zwei Spalten).

## Der Träger und der Schritt

`Tower := Σ n : ℕ, RGS n` — die kumulierte Stufenskala der RGS. Der kanonische
Aufstiegs-Schritt hängt an jede Kette das Zeichen `0` an:

```text
step ⟨n, r⟩ := ⟨n + 1, extend r 0 …⟩
```

`extend r 0` ist für **jedes** `r` zulässig: `hk : 0 ≤ foldr max 0 + 1` ist
`Nat.zero_le`, `h0 : r.val = [] → 0 = 0` ist trivial. Der Schritt ist damit
total, ohne Fallunterscheidung.

## Die drei gebundenen Merkmale

1. **Richtung (Nicht-Umkehrbarkeit).** `NoReturn step`: keine positive
   Iterationszahl führt zurück. Reiner Konsum von `noreturn_of_strict_rank`
   (23., via 16.) mit `rank := Sigma.fst`; die hinreichende Bedingung
   `hrank x : x.1 < (step x).1` ist `Nat.lt_succ_self`. Die gerichtete Zeit der
   Stufenskala, ohne neue Beweisarbeit.

2. **Substruktur-Erhaltung.** `x.2.val <+: (step x).2.val`: die alte Kette
   bleibt als **Präfix** im Neuen erhalten (`extend` hängt nur an). Das ist die
   eine Hälfte von Günthers Rangverlust — „die alte Kontextur bleibt als
   Sub-Struktur" — und sie ist definitional, `List.prefix_append`.

3. **Determinationsverlust (Faser-Mehrdeutigkeit), generisch.** Für **jede**
   Stufe `n ≥ 1` und jedes `r : RGS n` liegen über `r` mindestens zwei
   verschiedene Urbilder unter `descent` (`extend r 0 ≠ extend r 1`, beide
   descendieren auf `r`). Das Untere determiniert das Obere nicht mehr — die
   andere Hälfte des Rangverlusts, „hat aber seinen universalen Charakter
   verloren", als Unterbestimmtheit der Aufwärtsbewegung. Verallgemeinert den
   konkreten `RGS 3`-Zeugen `fiber_nontrivial` auf alle Stufen ab 1.

`tower_asymmetric` bindet die drei in einem Satz — der Ertrag dieser Datei und
das Erfüllungsstück des Ertrags-Kriteriums des Zeugenregisters (zwei getrennte
Beweisarten — Faser-Asymmetrie und Irreversibilität — durch ein gemeinsames,
nicht-triviales Lemma verbunden).

## Die verbleibende Grenze (ausdrücklich)

Was hier **nicht** bewiesen wird: dass der Stufenwechsel `n → n+1` ein
*Kontexturwechsel* im Günther-Sinn ist. Diese Identifikation
(„RGS-Stufe = Kontextur") ist eine Definitionswahl und bleibt Setzung, nicht
Satz. Der Verbindungssatz entscheidet KA darum **modulo einer markierten
Kontextur-Setzung**; die Kontexturgrenze-Spalte schließt prinzipiell nur
Definition plus Satz, nie ein Satz allein. Ebenso bleibt „universaler Charakter"
als Faser-Unterbestimmtheit formalisiert und wird als solche benannt — kein
Universalitäts-Metatheorem (Marken-Regel CLAUDE.md §6).

Kein `sorry`, kein `: True`-Feld, kein `axiom`.
-/

namespace Reformulation.Proemial.TowerAsymmetryProbe

open Reformulation.Kenogram
open Reformulation.Proemial.A1DescentProbe (descent)
open Reformulation.Proemial.ProemialInversionProbe (extend descent_extend)
open Reformulation.Proemial.IrreversibleAdvance (NoReturn noreturn_of_strict_rank)

-- ============================================================
-- §I — Träger und kanonischer Schritt
-- ============================================================

/-- Die kumulierte Stufenskala: ein RGS beliebiger Länge, mit seiner Länge als
erster Komponente. -/
abbrev Tower : Type := Σ n : ℕ, RGS n

/-- Der kanonische Aufstiegs-Schritt: hänge `0` an. Total (keine
Fallunterscheidung), weil `extend _ 0` für jedes `r` zulässig ist. -/
def step : Tower → Tower :=
  fun x => ⟨x.1 + 1, extend x.2 0 (Nat.zero_le _) (fun _ => rfl)⟩

-- ============================================================
-- §II — Merkmal 1: Richtung (Nicht-Umkehrbarkeit)
-- ============================================================

/-- **Merkmal 1.** `step` ist rückkehrfrei: der Rang (die Stufe) steigt strikt,
also führt keine positive Iteration zurück. Konsum von `noreturn_of_strict_rank`
(23.), `rank := Sigma.fst`, `hrank` = `Nat.lt_succ_self`. -/
theorem step_noreturn : NoReturn step :=
  noreturn_of_strict_rank (fun x => x.1) (fun x => Nat.lt_succ_self x.1)

-- ============================================================
-- §III — Merkmal 2: Substruktur-Erhaltung (Präfix)
-- ============================================================

/-- **Merkmal 2.** Die alte Kette bleibt als Präfix im aufgestiegenen erhalten
(`extend` hängt nur an). Die eine Hälfte des Rangverlusts, definitional. -/
theorem step_preserves_substructure (x : Tower) :
    x.2.val <+: (step x).2.val :=
  List.prefix_append x.2.val [0]

-- ============================================================
-- §IV — Merkmal 3: Determinationsverlust (Faser-Mehrdeutigkeit), generisch
-- ============================================================

/-- **Merkmal 3.** Für jede Stufe `n ≥ 1` liegen über jedem `r : RGS n` zwei
verschiedene Urbilder unter `descent`: `extend r 0` und `extend r 1` sind beide
zulässig (bei nichtleerer Kette), verschieden (letztes Zeichen `0 ≠ 1`) und
descendieren beide auf `r` (`descent_extend`). Die Aufwärtsbewegung ist nicht
determiniert — die andere Hälfte des Rangverlusts, für ALLE Stufen ab 1 (nicht
nur der `RGS 3`-Zeuge `fiber_nontrivial`). -/
theorem ascent_not_determined {n : ℕ} (hn : 1 ≤ n) (r : RGS n) :
    ∃ a b : RGS (n + 1), a ≠ b ∧ descent a = r ∧ descent b = r := by
  have hne_nil : r.val ≠ [] := by
    intro hnil
    have hlen : r.val.length = 0 := by rw [hnil]; rfl
    rw [r.property.1] at hlen
    omega
  have hk0 : (0 : ℕ) ≤ r.val.foldr max 0 + 1 := Nat.zero_le _
  have h00 : r.val = [] → (0 : ℕ) = 0 := fun _ => rfl
  have hk1 : (1 : ℕ) ≤ r.val.foldr max 0 + 1 := Nat.succ_le_succ (Nat.zero_le _)
  have h01 : r.val = [] → (1 : ℕ) = 0 := fun hnil => absurd hnil hne_nil
  refine ⟨extend r 0 hk0 h00, extend r 1 hk1 h01, ?_,
    descent_extend r 0 hk0 h00, descent_extend r 1 hk1 h01⟩
  intro heq
  have hval : r.val ++ [0] = r.val ++ [1] := congrArg Subtype.val heq
  simp at hval

-- ============================================================
-- §V — Der Verbindungssatz: die drei Merkmale in einem Satz
-- ============================================================

/-- **Der Verbindungssatz (Ertrag).** Richtung, Substruktur-Erhaltung und
Determinationsverlust — die drei Merkmale von Günthers asymmetrischer
Diskontexturalität — an EINEM Träger gebunden. Der erste Zeuge im Korpus, der
alle drei Spalten der Matrix zugleich besetzt; bisher trug jede Zeile höchstens
zwei. Beweis: Verschaltung der drei vorstehenden Sätze, kein neuer Gehalt über
sie hinaus. -/
theorem tower_asymmetric :
    NoReturn step
    ∧ (∀ x : Tower, x.2.val <+: (step x).2.val)
    ∧ (∀ n : ℕ, 1 ≤ n → ∀ r : RGS n,
        ∃ a b : RGS (n + 1), a ≠ b ∧ descent a = r ∧ descent b = r) :=
  ⟨step_noreturn, step_preserves_substructure, fun _ hn r => ascent_not_determined hn r⟩

-- ============================================================
-- Wachen — Axiom-Profile
-- ============================================================

/-! **Wachen.** Ist-Ausgabe des grünen Builds (v4.30.0-rc2), pro tragendem Satz
eingefroren. Der Verbindungssatz `tower_asymmetric` sichert als konsumierender
Satz die drei Teil-Profile über seine Hülle mit. -/

/-- info: 'Reformulation.Proemial.TowerAsymmetryProbe.step_noreturn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms step_noreturn

/-- info: 'Reformulation.Proemial.TowerAsymmetryProbe.step_preserves_substructure' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms step_preserves_substructure

/-- info: 'Reformulation.Proemial.TowerAsymmetryProbe.ascent_not_determined' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ascent_not_determined

/-- info: 'Reformulation.Proemial.TowerAsymmetryProbe.tower_asymmetric' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms tower_asymmetric

end Reformulation.Proemial.TowerAsymmetryProbe
