import Reformulation.Kenogram.Basic
import Reformulation.Proemial.A1DescentProbe
import Reformulation.Proemial.A3CoarseningProbe

/-!
# ProemialInversionProbe — Anti-Kollaps-Sonde für die proemielle Inversion (Stufe 2)

STANDALONE, NICHT im Aggregat (wie `A1DescentProbe`/`A3CoarseningProbe`/`CartesianProbe`).
Diese Sonde steht *vor* dem proemialen Entwurf ρ und liefert kein ρ und keinen Teil
von ρ. Sie löst die in `A3CoarseningProbe` ausdrücklich offen markierte **Stufe 2 —
die proemielle Inversion / Faser-Asymmetrie** ein.

**Die scharfe Frage:** Trägt die kenogrammatische C-Schicht die proemielle Inversion
als echte *Faser-Asymmetrie* — eine Split-Epi-Struktur der Stufen-Bewegung `descent`,
die im Unterschied zum γ-Lift des B-Kollaps *nicht* zum Iso kollabiert und darum
Substanz trägt?

- **Sonde-P1 (Schnitt-Eigenschaft, descent split epi):** `descent ∘ extend = id`,
  generisch für alle `n`. Hängt man eine zulässige Stelle an und streicht sie wieder,
  kehrt man zum Ausgang zurück — die Stufen-Bewegung ist in *einer* Richtung
  umkehrbar (`extend` ist ein Schnitt).
- **Sonde-P2 (Faser-Asymmetrie, descent kein Iso):** über `[0,1] : RGS 2` liegen
  mindestens zwei verschiedene Urbilder (`[0,1,0]`, `[0,1,2]`) mit gleichem `descent`.
  Aufwärts (Relatum zum Relator erheben) ist die Bewegung eine *Wahl* unter den
  Fasern — mehrdeutig, im Gegensatz zur eindeutigen Abwärts-Bewegung.
- **Sonde-N (Iso-Kollaps-Abgrenzung):** split-epi UND nicht-iso, als ein Satz
  zusammengeführt. Wäre `descent` ein Iso (wie γ in `CartesianProbe`), zwänge der
  Kollaps; hier nicht-iso, daher trägt die proemielle Inversion genau die Substanz,
  die der α+γ-Lift nicht trug.
- **Sonde-Z (Achsen-Trennung A1/A3):** `descent` ist *stufen-wechselnd*
  (längen-ändernd), die A3-Partitionshierarchie *schicht-intern* (längen-erhaltend).
  Typus-Sprung zwischen Stufen (Kern) gegen Informationsverlust innerhalb einer
  Schicht (A3) — die Partitionshierarchie realisiert den Kern nicht.

Reichweite: term-belegt ist die Split-Epi-Struktur (P1), die Faser-Asymmetrie /
Nicht-Iso (P2), ihre Konjunktion als Iso-Kontrast (N) und die Achsen-Trennung (Z).
GESTÜTZT, nicht bewiesen (Doc-Deutung): dass diese Faser-Asymmetrie Günthers
*proemielle Typinversion* (Relator⇄Relatum-Stufentausch) IST — das entscheidet die
Quelle (Hermeneutes), nicht die Sonde. NICHT berührt: die proemielle Verschränkung
(`K3CouplingProbe`), die S_n-Allgemeinheit, das volle ρ.

Kein `sorry`, kein `axiom`, kein `: True`-Feld, kein `native_decide` (nur `decide`).
-/

namespace Reformulation.Proemial.ProemialInversionProbe

open Reformulation.Kenogram
open Reformulation.Proemial.A1DescentProbe (descent)

-- ============================================================
-- §I — Die eine neue Definition: der A1-Aufstieg `extend`
-- ============================================================

/-- A1-Aufstieg: Anhängen einer zulässigen Stelle `k` an ein RGS. Schnitt von
`descent`. Wohldefiniert, sofern `k` das Präfix-Maximum um höchstens eins
überschreitet (RGS-Bedingung), via `isRGS_concat`. Die Hypothesen-Form ist die
volle generische Fassung aus der Spec (`hk`, `h0`); `h0` ist nur für `n = 0`
nicht-trivial und bei den Zeugen in §III (Länge ≥ 2) vacuously erfüllt — sie wurde
beibehalten, weil die Schnitt-Eigenschaft §II so für ALLE `n` durchgeht. -/
def extend {n : ℕ} (r : RGS n) (k : ℕ)
    (hk : k ≤ r.val.foldr max 0 + 1) (h0 : r.val = [] → k = 0) : RGS (n + 1) :=
  ⟨r.val ++ [k], by
    refine ⟨?_, isRGS_concat r.val k r.property.2 hk h0⟩
    rw [List.length_append, r.property.1]; rfl⟩

-- ============================================================
-- §II — Sonde-P1: Schnitt-Eigenschaft (descent ist split epi), generisch
-- ============================================================

/-- **Sonde-P1.** `descent` ist split epi: `extend` ist ein Schnitt, generisch für
ALLE `n`. `descent (extend r k …) = (r.val ++ [k]).dropLast = r.val` über
`List.dropLast_concat`; abgeschlossen mit `Subtype.ext`. Die Stufen-Bewegung ist
abwärts-rückholbar — die Inversion ist eine echte Retraktion, keine bloße
Nicht-Injektion. -/
theorem descent_extend {n : ℕ} (r : RGS n) (k : ℕ)
    (hk : k ≤ r.val.foldr max 0 + 1) (h0 : r.val = [] → k = 0) :
    descent (extend r k hk h0) = r := by
  apply Subtype.ext
  show (r.val ++ [k]).dropLast = r.val
  rw [List.dropLast_concat]

-- ============================================================
-- §III — Sonde-P2: Faser-Asymmetrie (descent ist kein Iso), konkreter Zeuge
-- ============================================================

/-- **Sonde-P2.** `descent` ist kein Iso: über dem benannten Basis-Punkt
`[0,1] : RGS 2` liegen mindestens zwei verschiedene Urbilder `[0,1,0] ≠ [0,1,2]`
(beide `RGS 3`) mit gleichem `descent`. Die Aufwärts-Bewegung (Relatum → Relator)
ist mehrdeutig — eine Wahl unter den Fasern, nicht umkehrbar. (Faser-Form der
nicht-Injektivität von `A1DescentProbe.descent_not_injective`, hier über benanntem
Basis-Punkt.) -/
theorem fiber_nontrivial :
    ∃ (a b : RGS 3), a ≠ b ∧ descent a = descent b ∧
      (∃ r : RGS 2, descent a = r ∧ descent b = r) := by
  refine ⟨⟨[0, 1, 0], by decide⟩, ⟨[0, 1, 2], by decide⟩, ?_, ?_, ⟨[0, 1], by decide⟩, ?_, ?_⟩
  · decide
  · apply Subtype.ext; decide
  · apply Subtype.ext; decide
  · apply Subtype.ext; decide

-- ============================================================
-- §IV — Sonde-N: Iso-Kollaps-Abgrenzung (der Substanz-Befund)
-- ============================================================

/-- **Sonde-N.** Split-epi UND nicht-iso, in einem Satz zusammengeführt: die erste
Konjunkte sichert die Retraktion (`descent_extend`), die zweite widerlegt den Iso
(`descent` nicht injektiv, aus `fiber_nontrivial`).

Doc-Deutung (NICHT als Lean-Satz): wäre `descent` ein Iso — wie γ in
`CartesianProbe`, wo jeder Iso-Lift cartesian kollabiert (kein Datum über „γ ist
Iso" hinaus, der B-Kollaps) —, zwänge der Kollaps. Hier ist `descent` split epi
*aber kein Iso*; damit trägt die proemielle Inversion auf der C-Schicht genau die
Substanz, die der α+γ-Lift nicht trug. Das ist die positive Antwort auf die
B-Position-Frage, auf die kenogrammatische Schicht verlegt. -/
theorem split_epi_not_iso :
    (∀ {n : ℕ} (r : RGS n) (k : ℕ) (hk : k ≤ r.val.foldr max 0 + 1)
        (h0 : r.val = [] → k = 0), descent (extend r k hk h0) = r)
    ∧ (∃ (a b : RGS 3), a ≠ b ∧ descent a = descent b) := by
  refine ⟨fun r k hk h0 => descent_extend r k hk h0, ?_⟩
  obtain ⟨a, b, hne, heq, _⟩ := fiber_nontrivial
  exact ⟨a, b, hne, heq⟩

-- ============================================================
-- §V — Sonde-Z: Achsen-Trennung (A3 realisiert den Kern nicht)
-- ============================================================

/-- **Sonde-Z.** Die proemielle Inversion ist *stufen-wechselnd*: `descent` senkt
die Länge (`n+1 → n`). `(descent r).val.length = n` über die `dropLast`-Länge,
`r.val.length = n+1` aus der RGS-Invariante.

Doc-Deutung (NICHT als Lean-Satz): `descent` ändert die Stufe (Längen-Differenz),
während `A3` (`proto`/`deutero`) die zugrundeliegende Länge nie ändert — die
A3-Stufung lebt schicht-intern auf fester Länge. Damit ist die Achsen-Trennung
term-belegt: *Typus-Sprung zwischen Stufen* (Kern, längen-ändernd) gegen
*Informationsverlust innerhalb einer Schicht* (A3, längen-erhaltend). Die
Partitionshierarchie realisiert den Kern der Inversion nicht; sie sitzt auf einer
anderen Achse. -/
theorem inversion_changes_stage {n : ℕ} (r : RGS (n + 1)) :
    (descent r).val.length = n ∧ r.val.length = n + 1 := by
  refine ⟨?_, r.property.1⟩
  show r.val.dropLast.length = n
  rw [List.length_dropLast, r.property.1]; omega

-- ============================================================
-- §VI — Verifikation (kein `sorryAx`)
-- ============================================================

#print axioms descent_extend
#print axioms fiber_nontrivial
#print axioms inversion_changes_stage

end Reformulation.Proemial.ProemialInversionProbe
