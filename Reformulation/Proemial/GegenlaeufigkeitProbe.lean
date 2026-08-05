import Reformulation.Proemial.A1DescentProbe
import Reformulation.Proemial.A3CoarseningProbe

/-!
# GegenlaeufigkeitProbe — Beleg-Modul zum Gutachten der Gegenläufigkeits-Schranke

STANDALONE, NICHT im Aggregat (wie `A1DescentProbe`/`A3CoarseningProbe`/`K3CouplingProbe`).
Begleit-Modul zu `Gutachten_Gegenlaeufigkeit_Final.md`: hebt den dort geführten
Befund von der rechnerischen Stichprobe (n≤5) auf den Term. Importiert `descent`
(A1DescentProbe) und `proto`/`deutero` (A3CoarseningProbe) unverändert.

Geprüfte Fragen:
- **Q1 (Kopplung).** Das Zeugenpaar `[0,0,1]`/`[0,1,0]` trägt: gleiches `deutero`
  auf A3, aber `descent` spaltet die A3-Bilder (`{2}` vs. `{1,1}`). Die
  trito-Feinstruktur schlägt auf die A1-Bewegung durch.
- **Q2 (Monotonie generisch).** `proto_descent_le`: `descent` senkt `proto` nie —
  für ALLE n, nicht nur die Stichprobe. Spiegel-Lemma: Anhängen hebt `proto` nie.
  Beide gradierten Achsen (A1 Länge, A3 proto) bewegen sich unter jeder
  Rand-Schritt-Operation GLEICHSINNIG, nie gegenläufig.
- **Q2/Q3 (kanonisch ≠ numerisch).** Ein RGS 4 mit `proto 1` und ein RGS 3 mit
  `proto 3` koexistieren — die Schranke liegt allein in der Kanonizität von
  `descent`/`extend`, nicht in der Arithmetik.

Reichweite: term-bewiesen ist das Fehlen der Gegenläufigkeit für die KANONISCHEN
Schritt-Operationen. NICHT berührt: eine positive K4′-Fassung der Ebenen-
Verschränkung (Gutachten Q4) — eigener Bauplatz.

Kein `sorry`, kein `axiom`, kein `native_decide`.
-/

namespace Reformulation.Proemial.GegenlaeufigkeitProbe

open Reformulation.Kenogram
open Reformulation.Proemial.A1DescentProbe (descent)
open Reformulation.Proemial.A3CoarseningProbe (proto deutero)

-- ============================================================
-- §I — Q1: Kopplungs-Zeugenpaar [0,0,1] / [0,1,0]
-- ============================================================

/-- Gleiches `deutero` auf der A3-Achse. -/
example : deutero (⟨[0,0,1], by decide⟩ : RGS 3) = deutero (⟨[0,1,0], by decide⟩ : RGS 3) := by
  decide

/-- `descent` spaltet die A3-Bilder: `deutero (descent [0,0,1]) = {2}`. -/
example : deutero (descent (⟨[0,0,1], by decide⟩ : RGS 3)) = ({2} : Multiset ℕ) := by decide

/-- `deutero (descent [0,1,0]) = {1,1}`. -/
example : deutero (descent (⟨[0,1,0], by decide⟩ : RGS 3)) = ({1,1} : Multiset ℕ) := by decide

/-- Die descent-Bilder sind verschieden — die Kopplung A1×A3 ist nicht-trivial. -/
example : deutero (descent (⟨[0,0,1], by decide⟩ : RGS 3))
        ≠ deutero (descent (⟨[0,1,0], by decide⟩ : RGS 3)) := by decide

/-- `proto` der descent-Bilder (gespaltenes A3-Bild der A1-Bewegung). -/
example : proto (descent (⟨[0,0,1], by decide⟩ : RGS 3)) = 1 := by decide
example : proto (descent (⟨[0,1,0], by decide⟩ : RGS 3)) = 2 := by decide

-- ============================================================
-- §II — Q2: Monotonie-Schranke generisch (term, kein decide)
-- ============================================================

/-- `foldr max` ist monoton unter `List.Sublist` (Induktion über die Sublist-Relation). -/
theorem foldr_max_sublist_le {l₁ l₂ : List ℕ} (h : List.Sublist l₁ l₂) :
    l₁.foldr max 0 ≤ l₂.foldr max 0 := by
  induction h with
  | slnil => simp
  | cons a _ ih =>
      simp only [List.foldr_cons]
      exact le_trans ih (le_max_right a _)
  | cons_cons a _ ih =>
      simp only [List.foldr_cons]
      exact max_le_max (le_refl a) ih

/-- **Q2-Hauptlemma.** `descent` senkt `proto` nie — generisch, alle `n`.
Hebt (B3) von der Stichprobe (n≤5) auf den Term. -/
theorem proto_descent_le {n : ℕ} (r : RGS (n+1)) :
    proto (descent r) ≤ proto r := by
  have hsub : List.Sublist (descent r).val r.val := List.dropLast_sublist r.val
  simp only [proto]
  exact Nat.add_le_add_right (foldr_max_sublist_le hsub) 1

/-- **Spiegel-Lemma.** Anhängen (extend-Richtung, Länge rauf) senkt `proto` nie.
Damit ist die Gegenläufigkeit für BEIDE Präfix/Suffix-Schritt-Formen ausgeschlossen:
Länge runter ⇒ proto runter-oder-gleich (descent), Länge rauf ⇒ proto rauf-oder-gleich. -/
theorem foldr_max_append_ge (l : List ℕ) (v : ℕ) :
    l.foldr max 0 ≤ (l ++ [v]).foldr max 0 :=
  foldr_max_sublist_le (List.sublist_append_left l [v])

-- ============================================================
-- §III — Q2/Q3: die Schranke ist kanonisch, nicht numerisch
-- ============================================================

/-- proto-rauf & Länge-runter ist *als Objektpaar* unproblematisch:
RGS 4 mit `proto 1`, RGS 3 mit `proto 3`. Die Schranke liegt also nicht in der
Arithmetik, sondern allein in der Kanonizität von `descent`/`extend`. -/
example : ∃ (a : RGS 4) (b : RGS 3), proto a < proto b :=
  ⟨⟨[0,0,0,0], by decide⟩, ⟨[0,1,2], by decide⟩, by decide⟩

-- ============================================================
-- §IV — Wachen: Axiom-Profile
-- ============================================================

/-! **Wachen (Zug B).** Ist-Ausgabe des grünen Builds (v4.30.0-rc2), pro Satz
eingefroren; sie ersetzen die drei vormals nackten Aufrufe. Alle drei Sätze der Datei
tragen eine Wache. -/

/-- info: 'Reformulation.Proemial.GegenlaeufigkeitProbe.proto_descent_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms proto_descent_le

/-- info: 'Reformulation.Proemial.GegenlaeufigkeitProbe.foldr_max_sublist_le' depends on axioms: [propext] -/
#guard_msgs in #print axioms foldr_max_sublist_le

/-- info: 'Reformulation.Proemial.GegenlaeufigkeitProbe.foldr_max_append_ge' depends on axioms: [propext] -/
#guard_msgs in #print axioms foldr_max_append_ge

end Reformulation.Proemial.GegenlaeufigkeitProbe
