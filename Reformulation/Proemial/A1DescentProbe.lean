import Reformulation.Kenogram.Basic

/-!
# A1DescentProbe — Anti-Kollaps-Sonde für die A1-Verankerung des proemialen Aufsatzes

STANDALONE, NICHT im Aggregat (wie `CartesianProbe`/`AxiomProbe`). Diese Sonde
steht *vor* dem proemialen Entwurf ρ und liefert kein ρ und keinen Teil von ρ.
Sie prüft maschinell genau eine Frage (K1′, Anti-Kanonisierung):

- **Sonde-P (positiv):** der A1-Abstieg `descent : RGS (n+1) → RGS n` ist NICHT
  injektiv — mehrere RGS der Länge `n+1` fallen auf dasselbe RGS der Länge `n`.
  Echter Informationsverlust in der *Stufen-Bewegung*, unabhängig von `relabel`.
- **Sonde-N (negativ):** `relabel` leistet keinen Stufenwechsel (längenerhaltend)
  und auf RGS keinen Informationsverlust (Identität). Die A2-Achse trägt die
  proemiale Stufen-Asymmetrie also nicht; sie kann nur von A1 kommen.

Reichweite: eingelöst ist die NOTWENDIGE Bedingung K1′. NICHT berührt: K3′
(die Kopplung Umtausch⇄Ordnung) — die entscheidet erst der ρ-Vollbau.

Kein `sorry`, kein `: True`-Feld, kein `axiom`.
-/

namespace Reformulation.Proemial.A1DescentProbe

open Reformulation.Kenogram

-- ============================================================
-- §I.1 — Hilfslemma: Präfix-Abgeschlossenheit (Wohldefiniertheit von `descent`)
-- ============================================================

/-- Präfix-Abgeschlossenheit von `IsRGS` unter `dropLast`: streicht man das letzte
Zeichen eines RGS, bleibt ein RGS. Trägt die Wohldefiniertheit von `descent`. -/
theorem isRGS_dropLast {l : List ℕ} (h : IsRGS l) : IsRGS l.dropLast := by
  rcases List.eq_nil_or_concat l with rfl | ⟨l', v, rfl⟩
  · -- l = []: dropLast [] = [], IsRGS [] trivial.
    decide
  · -- l = l' ++ [v]: (l' ++ [v]).dropLast = l'.
    simp only [List.concat_eq_append] at h ⊢
    rw [List.dropLast_concat]
    rcases l' with _ | ⟨a, t⟩
    · -- l' = []: IsRGS [] trivial.
      decide
    · -- l' = a :: t: isRGS_cons_concat zerlegt h in den Präfix-Faktor.
      rw [isRGS_cons_concat] at h
      exact h.1

-- ============================================================
-- §I.2 — Die A1-Abstiegs-Funktion
-- ============================================================

/-- A1-Abstieg: Streichen des letzten Zeichens senkt die Länge um eins. Bewegt
sich entlang der evolutiven Achse `n+1 → n` (Stufen-Bewegung). -/
def descent {n : ℕ} (r : RGS (n + 1)) : RGS n :=
  ⟨r.val.dropLast, by
    refine ⟨?_, isRGS_dropLast r.property.2⟩
    rw [List.length_dropLast, r.property.1]
    omega⟩

-- ============================================================
-- §I.3 — Sonde-P: Nicht-Injektivität von `descent` (K1′-tragende Asymmetrie)
-- ============================================================

/-- **Sonde-P.** Der A1-Abstieg ist nicht injektiv: `[0,1,1]` und `[0,1,2]`
(beide RGS der Länge 3) fallen auf dasselbe `[0,1] : RGS 2`. Die gestrichene
letzte Position (`1` vs. `2`) ist die beim Abstieg verlorene Stufen-Information —
genau der von K1′ geforderte Informationsverlust der Stufen-Bewegung. -/
theorem descent_not_injective :
    ∃ (a b : RGS 3), a ≠ b ∧ descent a = descent b := by
  refine ⟨⟨[0, 1, 1], by decide⟩, ⟨[0, 1, 2], by decide⟩, ?_, ?_⟩
  · decide
  · apply Subtype.ext
    decide

-- ============================================================
-- §I.4 — Sonde-N: `relabel` trägt keine Stufen-Asymmetrie (A2-Ausschluss)
-- ============================================================

/-- **Sonde-N (a).** `relabel` leistet keinen Stufenwechsel: längenerhaltend. -/
theorem relabel_no_stage_change (vals : List ℕ) :
    (relabel vals).length = vals.length :=
  relabel_length vals

/-- **Sonde-N (b).** `relabel` ist auf RGS die Identität — kein Informationsverlust
auf der gleichlangen Achse. -/
theorem relabel_id_on_rgs {l : List ℕ} (h : IsRGS l) : relabel l = l :=
  relabel_eq_self_of_isRGS h

/-- **Sonde-N (c), Kontrast-Pointe.** `relabel` kann `descent` nicht nachbilden:
die Länge bleibt 3, kein Abstieg auf Länge 2. -/
example : (relabel [0, 1, 1]).length = 3 := by decide

-- ============================================================
-- §III — Wachen: Axiom-Profile
-- ============================================================

/-! **Wachen.** Ist-Ausgabe des grünen Builds (v4.30.0-rc2), pro Satz eingefroren.
Alle vier Sätze der Datei tragen eine Wache; das Hilfslemma `isRGS_dropLast` ist
mit aufgenommen, weil an ihm die Wohldefiniertheit von `descent` und damit eine
Eigenschaft der ganzen Datei hängt (CLAUDE.md §3, „Ausnahme, die keine ist").

`Classical.choice` in `relabel_id_on_rgs` ist geerbt und nicht hier erzeugt: der
Beweis ist der Aufruf von `Kenogram.relabel_eq_self_of_isRGS`, und dessen Profil
ist am selben Stand gemessen `[propext, Classical.choice, Quot.sound]`. Die drei
übrigen Profile der Datei sind choice-frei; insbesondere trägt
`relabel_no_stage_change` über `Kenogram.relabel_length` nur `[propext,
Quot.sound]`. -/

/-- info: 'Reformulation.Proemial.A1DescentProbe.isRGS_dropLast' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms isRGS_dropLast

/-- info: 'Reformulation.Proemial.A1DescentProbe.descent_not_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms descent_not_injective

/-- info: 'Reformulation.Proemial.A1DescentProbe.relabel_no_stage_change' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms relabel_no_stage_change

/-- info: 'Reformulation.Proemial.A1DescentProbe.relabel_id_on_rgs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms relabel_id_on_rgs

end Reformulation.Proemial.A1DescentProbe
