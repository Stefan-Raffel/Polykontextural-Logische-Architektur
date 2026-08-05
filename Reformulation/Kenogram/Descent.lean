import Reformulation.Kenogram.PlaceSwap

/-!
# Reformulation.Kenogram.Descent — Stufenabstieg und Aufstieg, in Aggregat-Form

**Hebung, kein neuer Gehalt.** Dieses Modul bringt den kenogrammatischen Stufenabstieg
und seinen partiellen Aufstieg in benannte, dokumentierte Aggregat-Form. Die Sätze
stammen aus den Standalone-Sonden `Proemial.A1DescentProbe` und
`Proemial.ProemialInversionProbe`; **beide bleiben byte-unverändert als historische
Belege stehen**, nach dem Muster von `Proemial.ExtensionalCollapse` und der Hebung des
Ordnungswechsel-Zuges.

**Warum die Hebung:** ein Aggregat-Satz konsumiert `descent_split_epi_not_iso` (die
Klammer). Ein Zeuge, den nur eine Standalone-Sonde trägt, ist für einen Aggregat-Satz
nicht erreichbar.

## Was gehoben ist, und was nicht

Gemessen an der Konstantenhülle des Zielsatzes, **vor** der Hebung: aus
`ProemialInversionProbe` fünf Konstanten (`extend`, `descent_extend`,
`fiber_nontrivial`, `split_epi_not_iso` samt Beweisterm), aus `A1DescentProbe` vier
(`descent`, `isRGS_dropLast` samt Beweistermen), aus `A3CoarseningProbe` **keine**.

**Eine Ersparnis, die sich als teuer erwies — und darum unterblieb.** `isRGS_dropLast`
liegt seit dem Stellen-Tausch-Zug als `Kenogram.isRGS_dropLast'` im Aggregat, aus dem
Präfix-Lemma hergeleitet; sie zu konsumieren hätte eine Deklaration gespart. **Gemessen an
beiden Fassungen: jene erbt `Classical.choice`** (über `relabel_eq_self_of_isRGS`) und
vererbt es an den Abstieg und alles, was ihn konsumiert. Die Sonde beweist dieselbe
Aussage **choice-frei** per Induktion. Gehoben ist darum die Induktion, nicht die
Herleitung — die vier Deklarationen der Hüllenmessung sind vollständig gehoben.

## Die Asymmetrie der beiden Bewegungen

`descent` ist **total**: das Streichen der letzten Stelle ist überall definiert und
kanonisch. `extend` ist **partiell**: es nimmt eine Stelle `k` und zwei Beweisargumente,
denn nicht jede Stelle ist zulässig.

**Das ist keine Bauform, sondern die Sache.** Der Aufstieg **wählt** — welche Stelle
angehängt wird, sagt die Struktur nicht —, und eine Wahl hat Argumente. Ein totaler
Schnitt entsteht erst, wenn man die Wahl fest trifft; siehe die Klammer.

Kein `sorry`, kein `axiom`, kein `: True`-Feld.
-/

namespace Reformulation.Kenogram

-- ============================================================
-- §I — Der Abstieg
-- ============================================================

/-- Präfix-Abgeschlossenheit unter `dropLast`, per Induktion über die Zerlegung.

**Warum nicht `isRGS_dropLast'`?** Jene Fassung (Stellen-Tausch-Zug) leitet dieselbe
Aussage aus dem Präfix-Lemma her und erbt dabei `Classical.choice` über
`relabel_eq_self_of_isRGS`. Diese hier ist **choice-frei** und hält damit die ganze
Abstiegs-Kette choice-frei — gemessen an beiden Fassungen, nicht vermutet. Gehoben aus
`Proemial.A1DescentProbe.isRGS_dropLast`. -/
theorem isRGS_dropLast {l : List ℕ} (h : IsRGS l) : IsRGS l.dropLast := by
  rcases List.eq_nil_or_concat l with rfl | ⟨l', v, rfl⟩
  · decide
  · simp only [List.concat_eq_append] at h ⊢
    rw [List.dropLast_concat]
    rcases l' with _ | ⟨a, t⟩
    · decide
    · rw [isRGS_cons_concat] at h
      exact h.1

/-- **Der Stufenabstieg.** Streichen der letzten Stelle senkt die Länge um eins.
Gehoben aus `Proemial.A1DescentProbe.descent`. -/
def descent {n : ℕ} (r : RGS (n + 1)) : RGS n :=
  ⟨r.val.dropLast, by
    refine ⟨?_, isRGS_dropLast r.property.2⟩
    rw [List.length_dropLast, r.property.1]; omega⟩

/-- Der Abstieg ist nicht injektiv: `[0,1,1]` und `[0,1,2]` fallen auf `[0,1]`.
Gehoben aus `Proemial.A1DescentProbe.descent_not_injective`. -/
theorem descent_not_injective :
    ∃ (a b : RGS 3), a ≠ b ∧ descent a = descent b := by
  refine ⟨⟨[0, 1, 1], by decide⟩, ⟨[0, 1, 2], by decide⟩, ?_, ?_⟩
  · decide
  · apply Subtype.ext; decide

-- ============================================================
-- §II — Der partielle Aufstieg
-- ============================================================

/-- **Der Aufstieg, partiell.** Anhängen einer **zulässigen** Stelle `k`. Die zwei
Hypothesen sind die Zulässigkeit: `k` überschreitet das Präfix-Maximum um höchstens eins,
und über der leeren Folge ist nur `0` erlaubt.

**`extend` ist keine Funktion `RGS n → RGS (n+1)`** — sie nimmt `k` und zwei
Beweisargumente. Wer einen totalen Schnitt will, muss die Stelle fest wählen; siehe den
Dateikopf. Gehoben aus `Proemial.ProemialInversionProbe.extend`. -/
def extend {n : ℕ} (r : RGS n) (k : ℕ)
    (hk : k ≤ r.val.foldr max 0 + 1) (h0 : r.val = [] → k = 0) : RGS (n + 1) :=
  ⟨r.val ++ [k], by
    refine ⟨?_, isRGS_concat r.val k r.property.2 hk h0⟩
    rw [List.length_append, r.property.1]; rfl⟩

/-- **Die Retraktionsgleichung, generisch.** Für **jeden zulässigen** Aufstieg gilt
`descent ∘ extend = id`. Gehoben aus `Proemial.ProemialInversionProbe.descent_extend`.

Sie sagt **nicht**, dass `descent` einen Schnitt hat — dazu müsste `k` fest gewählt
sein. -/
theorem descent_extend {n : ℕ} (r : RGS n) (k : ℕ)
    (hk : k ≤ r.val.foldr max 0 + 1) (h0 : r.val = [] → k = 0) :
    descent (extend r k hk h0) = r := by
  apply Subtype.ext
  show (r.val ++ [k]).dropLast = r.val
  rw [List.dropLast_concat]

/-- **Die Faser-Asymmetrie.** Über `[0,1] : RGS 2` liegen mindestens zwei verschiedene
Urbilder. Der Aufstieg ist eine Wahl unter Fasern, der Abstieg kanonisch. Gehoben aus
`Proemial.ProemialInversionProbe.fiber_nontrivial`. -/
theorem fiber_nontrivial :
    ∃ (a b : RGS 3), a ≠ b ∧ descent a = descent b ∧
      (∃ r : RGS 2, descent a = r ∧ descent b = r) := by
  refine ⟨⟨[0, 1, 0], by decide⟩, ⟨[0, 1, 2], by decide⟩, ?_, ?_, ⟨[0, 1], by decide⟩, ?_, ?_⟩
  · decide
  · apply Subtype.ext; decide
  · apply Subtype.ext; decide
  · apply Subtype.ext; decide

/-- **Split epi und kein Iso, in einem Satz.** Die Retraktionsgleichung für jeden
zulässigen Aufstieg, und die Nicht-Injektivität des Abstiegs. Gehoben aus
`Proemial.ProemialInversionProbe.split_epi_not_iso`.

**Der Name sagt, was der Satz tut, und nicht, was er bedeutet.** Die Deutung als
proemielle Typinversion steht im Kopf der Sonde und wird hier nicht wiederholt. -/
theorem descent_split_epi_not_iso :
    (∀ {n : ℕ} (r : RGS n) (k : ℕ) (hk : k ≤ r.val.foldr max 0 + 1)
        (h0 : r.val = [] → k = 0), descent (extend r k hk h0) = r)
    ∧ (∃ (a b : RGS 3), a ≠ b ∧ descent a = descent b) := by
  refine ⟨fun r k hk h0 => descent_extend r k hk h0, ?_⟩
  obtain ⟨a, b, hne, heq, _⟩ := fiber_nontrivial
  exact ⟨a, b, hne, heq⟩

-- ============================================================
-- §III — Wachen: Axiom-Profile
-- ============================================================

/-! **Wachen.** Ist-Ausgabe des grünen Builds (v4.30.0-rc2), pro Deklaration eingefroren.

**Die ganze Kette ist choice-frei** — und das ist das Ergebnis der Entscheidung im
Dateikopf: die Herleitung aus dem Präfix-Lemma hätte `Classical.choice` eingetragen und an
jeden Konsumenten weitergegeben. Gemessen an beiden Fassungen, nicht vermutet. -/

/-- info: 'Reformulation.Kenogram.isRGS_dropLast' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms isRGS_dropLast

/-- info: 'Reformulation.Kenogram.descent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms descent

/-- info: 'Reformulation.Kenogram.descent_not_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms descent_not_injective

/-- info: 'Reformulation.Kenogram.extend' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms extend

/-- info: 'Reformulation.Kenogram.descent_extend' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms descent_extend

/-- info: 'Reformulation.Kenogram.fiber_nontrivial' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms fiber_nontrivial

/-- info: 'Reformulation.Kenogram.descent_split_epi_not_iso' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms descent_split_epi_not_iso

end Reformulation.Kenogram
