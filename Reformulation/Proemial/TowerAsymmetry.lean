import Reformulation.Kenogram.Descent
import Reformulation.Proemial.IrreversibleAdvance

/-!
# Reformulation.Proemial.TowerAsymmetry — der Verbindungssatz, aggregatfähig

**Ertrag, unverändert seit der Sonde.** Die drei Merkmale, die Günthers
asymmetrische Diskontexturalität *zugleich* verlangt, an **einem** Träger
gebunden: Richtung, Substruktur-Erhaltung, Determinationsverlust. Bisher lagen
sie auf getrennte Zeugen verteilt; keine Zeile der Dreispalten-Matrix besetzte
mehr als zwei Spalten.

**Diese Datei ist eine Hebung, kein neuer Gehalt.** Der Ertrag steht seit
`Proemial.TowerAsymmetryProbe`; hier wird er **erreichbar** — die Sonde
konsumierte `A1DescentProbe` und `ProemialInversionProbe`, beide standalone, und
war darum selbst nicht aggregatfähig. Diese Sperre ist gefallen: `descent`,
`extend` und `descent_extend` liegen seit dem Descent-Zug in
`Kenogram.Descent` in Aggregat-Form vor. Konsumiert wird von dort, nicht
nachgebaut.

**Die Sonde bleibt byte-unverändert als historischer Beleg.** Der Verweis steht
hier und nicht dort; Präzedenz `Proemial.RetractionBracket` und
`Proemial.ExtensionalCollapse`.

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
   Iterationszahl führt zurück. Reiner Konsum von `noreturn_of_strict_rank` mit
   `rank := Sigma.fst`; die hinreichende Bedingung `hrank x : x.1 < (step x).1`
   ist `Nat.lt_succ_self`.

2. **Substruktur-Erhaltung.** `x.2.val <+: (step x).2.val`: die alte Kette bleibt
   als **Präfix** im Neuen erhalten. Die eine Hälfte von Günthers Rangverlust —
   „die alte Kontextur bleibt als Sub-Struktur" — und sie ist definitional,
   `List.prefix_append`.

3. **Determinationsverlust (Faser-Mehrdeutigkeit), generisch.** Für **jede**
   Stufe `n ≥ 1` und jedes `r : RGS n` liegen über `r` mindestens zwei
   verschiedene Urbilder unter `descent`. Das Untere determiniert das Obere nicht
   mehr — die andere Hälfte des Rangverlusts, als Unterbestimmtheit der
   Aufwärtsbewegung. Verallgemeinert den konkreten `RGS 3`-Zeugen
   `Kenogram.fiber_nontrivial` auf alle Stufen ab 1.

`tower_asymmetric` bindet die drei in **einem** Satz.

## Vier Grenzen, aus dem Sondenkopf übernommen und nicht verdünnt

1. **„RGS-Stufe = Kontextur" ist Setzung**, nicht Satz. Der Verbindungssatz
   entscheidet die Frage der asymmetrischen Diskontexturalität **modulo dieser
   markierten Kontextur-Setzung**; die Kontexturgrenze-Spalte schliesst
   prinzipiell nur Definition plus Satz, nie ein Satz allein.

2. **Die drei Merkmale sind verschieden hart**, und das gehört gelesen, bevor die
   Konjunktion für drei gleichwertige Befunde genommen wird. Merkmal 1 ist
   **geerbt** (Rangfunktion `Sigma.fst`, Beweis `Nat.lt_succ_self`; die
   Asymmetrie sitzt in der Zählung der Stufen, nicht in ihrer kenogrammatischen
   Struktur). Merkmal 2 ist **definitional** (es betrifft die gewählte
   Schrittdefinition, nicht den Träger). Nur Merkmal 3 trägt **eigenen Gehalt**.
   Die Konjunktion selbst ist trivial, sobald die Teile stehen; ihr Wert liegt
   darin, dass die drei an **einem** Träger zusammenkommen. Das ist eine
   **Verortung, kein Beweisfortschritt.**

3. **Die Stufenachse ist die Stellenzahl, nicht Günthers Relationsordnung.**
   **Kein Satz dieser Datei trägt einen `Definitionen.md`-§20-Anspruch**; der
   Träger der Relationen-als-Gegenstände-Lesart ist die Leiter nachweislich
   nicht — die Abzählung steht in der Zerlegungs-Sondierung §3.2 (S1) und in
   `Proemial_V1_Stelligkeit2_Befund.md`. „Universaler Charakter" bleibt als
   Faser-Unterbestimmtheit formalisiert und ist kein Universalitäts-Metatheorem.

4. Kein `sorry`, kein `axiom`, kein `: True`-Feld, kein `native_decide`; kein
   Ledger-Zug.

## Die Naht zwischen den Strängen — Entscheidung, nicht Notwendigkeit

Diese Datei liegt in `Proemial/` und importiert `Kenogram.Descent`, **nicht
umgekehrt**. Der Grund ist Hygiene und keine Sachnotwendigkeit: die γ-Freiheit
des Kenogram-Zweigs ist als **Datei-Eigenschaft** gemessen und soll so messbar
bleiben, also erhält der Zweig keinen Proemial-Import. **Das ist eine
Architektur-Entscheidung des Betreibers.**

**Sie ist nicht die erste ihrer Art**, und das ist gemessen: `RelabelInvariance`
(`Kenogram.Basic` + `Proemial.GeneralCloneBound`) und `RetractionBracket`
(`Kenogram.Descent` + `Proemial.ArrowAscent`) tragen dieselbe Naht bereits im
Aggregat. Diese Datei ist die **dritte**, und `RetractionBracket` ist ihre
unmittelbare Präzedenz — dieselben beiden Stränge, dieselbe Richtung des Imports.

## Aggregat-Reife

Zwei Importe: `Kenogram.Descent`, `Proemial.IrreversibleAdvance`. Kein Import
einer Sonde. Keine Setzung, keine Definition mit Ledger-Anspruch.
-/

namespace Reformulation.Proemial.TowerAsymmetry

open Reformulation.Kenogram (RGS descent extend descent_extend)
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
also führt keine positive Iteration zurück. Konsum von `noreturn_of_strict_rank`,
`rank := Sigma.fst`, `hrank` = `Nat.lt_succ_self`. **Geerbt**, siehe Grenze 2 im
Dateikopf. -/
theorem step_noreturn : NoReturn step :=
  noreturn_of_strict_rank (fun x => x.1) (fun x => Nat.lt_succ_self x.1)

-- ============================================================
-- §III — Merkmal 2: Substruktur-Erhaltung (Präfix)
-- ============================================================

/-- **Merkmal 2.** Die alte Kette bleibt als Präfix im aufgestiegenen erhalten
(`extend` hängt nur an). Die eine Hälfte des Rangverlusts, **definitional**. -/
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
nur der `RGS 3`-Zeuge `Kenogram.fiber_nontrivial`). **Merkmal 1 ist geerbt,
Merkmal 2 definitional; dieser Satz trägt eigenen Gehalt** (Grenze 2 im
Dateikopf). -/
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

/-- **Der Verbindungssatz.** Richtung, Substruktur-Erhaltung und
Determinationsverlust — die drei Merkmale von Günthers asymmetrischer
Diskontexturalität — an EINEM Träger gebunden. Der erste Zeuge im Korpus, der
alle drei Spalten der Matrix zugleich besetzt; bisher trug jede Zeile höchstens
zwei. Beweis: Verschaltung der drei vorstehenden Sätze, **kein neuer Gehalt über
sie hinaus**; zur verschiedenen Härte der drei siehe Grenze 2 im Dateikopf. -/
theorem tower_asymmetric :
    NoReturn step
    ∧ (∀ x : Tower, x.2.val <+: (step x).2.val)
    ∧ (∀ n : ℕ, 1 ≤ n → ∀ r : RGS n,
        ∃ a b : RGS (n + 1), a ≠ b ∧ descent a = r ∧ descent b = r) :=
  ⟨step_noreturn, step_preserves_substructure, fun _ hn r => ascent_not_determined hn r⟩

-- ============================================================
-- §VI — Wachen: Axiom-Profile
-- ============================================================

/-! **Wachen.** Ist-Ausgabe des grünen Builds, pro tragendem Satz eingefroren.
Der Verbindungssatz `tower_asymmetric` sichert als konsumierender Satz die drei
Teil-Profile über seine Hülle mit. -/

/-- info: 'Reformulation.Proemial.TowerAsymmetry.step_noreturn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms step_noreturn

/-- info: 'Reformulation.Proemial.TowerAsymmetry.step_preserves_substructure' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms step_preserves_substructure

/-- info: 'Reformulation.Proemial.TowerAsymmetry.ascent_not_determined' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ascent_not_determined

/-- info: 'Reformulation.Proemial.TowerAsymmetry.tower_asymmetric' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms tower_asymmetric

end Reformulation.Proemial.TowerAsymmetry
