import Reformulation.Kenogram.Basic

/-!
# A3CoarseningProbe — Anti-Deklarations-Sonde für den Vergröberungs-Turm

STANDALONE, NICHT im Aggregat (wie `CartesianProbe`/`A1DescentProbe`/`K3CouplingProbe`).
Diese Sonde steht *vor* dem proemialen Entwurf ρ und liefert kein ρ und keinen Teil
von ρ. Sie prüft maschinell genau eine Frage — Horistês' untere Naht: ist die
A3-Stufung (proto/deutero/trito) aus dem RGS-Material **ableitbar** (nicht zu
deklarieren), und ist der Turm an beiden Sprossen **echt vergröbernd**?

- **Faktorisierung:** der Turm schließt sich, `proto = card ∘ deutero`.
- **Sonde-P(a):** `trito ↠ deutero` ist nicht injektiv — Stellungs-Information geht
  verloren (`[0,0,1] ≠ [0,1,0]`, aber gleiche Klassen-Größen-Multiset `{1,2}`).
- **Sonde-P(b):** `deutero ↠ proto` ist nicht injektiv — Häufigkeits-Information
  geht verloren (`{2,2} ≠ {1,3}`, aber beide `proto = 2`).
- **Sonde-N (Kontrast):** `relabel` ist auf RGS Identität (K1′-Material), leistet
  also keine Vergröberung; der Informationsverlust kommt allein von der A3-Stufung.

Reichweite: eingelöst ist Stufe 1 — die A3-Stufung ist ableitbar und beide
Vergröberungen sind echte, nicht-injektive Informationsverluste. NICHT berührt:
Stufe 2 (die proemielle Inversion / Faser-Asymmetrie).

Kein `sorry`, kein `: True`-Feld, kein `axiom`, kein `native_decide`.
-/

namespace Reformulation.Proemial.A3CoarseningProbe

open Reformulation.Kenogram

-- ============================================================
-- §I — Definitionen (RGS-Seite, computable)
-- ============================================================

/-- **proto** — Anzahl der Klassen. Für nichtleere, ab 0 lückenlose RGS ist das
das Maximum der Werte plus eins. -/
def proto {n : ℕ} (r : RGS n) : ℕ := (r.val.foldr max 0) + 1

/-- **deutero** — die Multiset der Klassen-Größen (permutationsinvariant, weil
Multiset; hängt nur von den Häufigkeiten ab, nicht von der Werte-Reihenfolge). -/
def deutero {n : ℕ} (r : RGS n) : Multiset ℕ :=
  (Multiset.range (proto r)).map (fun v => (r.val.filter (· = v)).length)

-- ============================================================
-- §II.1 — Faktorisierung (der Turm schließt sich)
-- ============================================================

/-- **Faktorisierung.** `proto r = card (deutero r)`: die unterste Stufe ist die
Klassenzahl, die mittlere Stufe trägt genau so viele Klassen-Größen. -/
theorem coarsening_factors {n : ℕ} (r : RGS n) : proto r = (deutero r).card := by
  simp only [deutero, Multiset.card_map, Multiset.card_range]

-- ============================================================
-- §II.2 — Sonde-P(a): trito ↠ deutero nicht-injektiv
-- ============================================================

/-- **Sonde-P(a).** `trito ↠ deutero` ist nicht injektiv: `[0,0,1]` und `[0,1,0]`
(beide RGS der Länge 3) sind verschieden, haben aber dieselbe Klassen-Größen-
Multiset `{1,2}`. Die Stellungs-Information geht beim Übergang verloren. -/
theorem deutero_not_injective : ∃ (a b : RGS 3), a ≠ b ∧ deutero a = deutero b := by
  refine ⟨⟨[0, 0, 1], by decide⟩, ⟨[0, 1, 0], by decide⟩, ?_, ?_⟩
  · decide
  · decide

-- ============================================================
-- §II.3 — Sonde-P(b): deutero ↠ proto nicht-injektiv
-- ============================================================

/-- **Sonde-P(b).** `deutero ↠ proto` ist nicht injektiv: `[0,0,1,1]`
(`deutero = {2,2}`) und `[0,0,0,1]` (`deutero = {1,3}`) haben verschiedene
Größen-Verteilung, aber beide `proto = 2`. Die Häufigkeits-Information geht
beim Übergang zur Klassenzahl verloren. -/
theorem proto_coarser_than_deutero :
    ∃ (a b : RGS 4), deutero a ≠ deutero b ∧ proto a = proto b := by
  refine ⟨⟨[0, 0, 1, 1], by decide⟩, ⟨[0, 0, 0, 1], by decide⟩, ?_, ?_⟩
  · decide
  · decide

-- ============================================================
-- §II.4 — Sonde-N (Kontrast): die Vergröberung ist nicht `relabel`
-- ============================================================

/-- **Sonde-N.** `relabel` ist auf RGS die Identität — leistet keine Vergröberung.
Der Informationsverlust von §II.2/§II.3 kommt allein von der A3-Stufung. -/
example : relabel [0, 0, 1] = [0, 0, 1] := relabel_eq_self_of_isRGS (by decide)

-- ============================================================
-- §III — Verifikation (kein `sorryAx`)
-- ============================================================

#print axioms coarsening_factors
#print axioms deutero_not_injective
#print axioms proto_coarser_than_deutero

end Reformulation.Proemial.A3CoarseningProbe
