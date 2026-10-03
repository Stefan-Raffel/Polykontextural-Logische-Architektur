import Mathlib.Order.RelClasses
import Mathlib.Logic.Relation
import Mathlib.Data.Fintype.Card

/-!
# Reformulation.Proemial.IntransitivityDifferential — das Intransitivitäts-Differential (vierzehnte Schicht)

## (1) Quellen-fest

Günther 1937 (*Wahrheit, Wirklichkeit und Zeit*), Druck-Zählung am Roh-PDF
verifiziert:

1. Die Zeit ist von höherer Mächtigkeit als der Wille.
2. Das Denken besitzt höhere Mächtigkeit als die Zeit.
3. Der Wille entwickelt eine höhere Mächtigkeit als das Denken.

Daraus können „niemals drei Aussagegruppen von transitivem Charakter gebildet
werden" — die „mangelnde Transitivität der drei Prinzipien" wörtlich. Die
Reduktion verkettet (2) und (1) gegen (3). Zyklus-Lesefolge
(Denken ≻ Zeit ≻ Wille ≻ Denken) und `cyc3`-Kodierung (0 ≙ Denken, 1 ≙ Zeit,
2 ≙ Wille, erste Stelle dominiert) sind Darstellungs-Wahl dieses Moduls, keine
Quellen-Zählung.

## (2) Term-fest werden hiermit

Beide Hälften des Differentials, in EINER Sprache (Ordnungssprache):

* **arme Klasse** — die strikte Ordnung: Relationen mit `IsTrans` + `Std.Irrefl`
  (= Mathlibs `IsStrictOrder`-Zerlegung in v4.30; `IsIrrefl` ist dort zugunsten
  `Std.Irrefl` deprecated, Asymmetrie folgt). Instanz-quantifiziert über *alle* Träger und *alle*
  Instanzen (`no_cycle_in_strict_order`, `cyc3_not_representable`, `no_return`).
* **reiche Seite** — der Zeuge `cyc3` auf `Fin 3` mit den Ehrlichkeits-Sätzen
  (`cyc3_holds`, `cyc3_irrefl`, `cyc3_not_transitive`): er existiert, ist
  irreflexiv und verlässt die arme Klasse EXAKT an der Transitivität, nirgends
  sonst.

## (3) Marke 3 — Deutung, nicht Behauptung

Die Benennung 0 ≙ Denken, 1 ≙ Zeit, 2 ≙ Wille ist Lesart und lebt nur im
Doc-String. Der Träger `Fin 3` ist neutral; kein Satz dieser Datei kennt sie.

## (4) Abgrenzung

Die reiche Seite ist der *minimale relationale Zeuge*. Ob die modale Triade
selbst den Zyklus trägt, bleibt hier unbehauptet — deren Asymmetrie-Klassifikation
ist Design-Datum (A3 der Gestalt), der zugehörige Swap-Satz ein eigenes Paket
(AP7). Ebenso nicht Teil dieser Schicht: die `ModelTheory`-starke Marke-1-Fassung
(Pfad B, Folge-Paket). Konditional ist hier *nichts*.

## (5) Sorry-Bilanz und Axiom-Stand

0 Sorries. Beide Differential-Hälften sind reine Logik bzw. Kernel-Berechnung
(`decide`), ohne projekteigene Setzungen. *Nachgeführt am 3. Oktober 2026 (Custos KC2 (b)):*
hier stand „nur die von `decide`/`propext` gezogenen Kern-Axiome". Das war schon vor
diesem Zug ungenau, denn `no_return` trägt `[propext, Quot.sound]`. Mit Teil 5 tragen auch
die Sätze des Rangsatzes `[propext, Quot.sound]`, und `rang_azyklisch` ist axiomfrei.
**Kein `Classical.choice` im Modul.** Die gemessenen Profile stehen verbatim in den Wachen am
Dateiende.

## (6) Der allgemeine Rangsatz (Teil 5) — UNSER, Mathematik, keine Günther-Lesung

`rang_zyklenfrei`: Eine Relation auf einem endlichen Träger hat genau dann eine
Rangfunktion nach `ℕ` (jeder Schritt senkt den Rang), wenn ihre transitive Hülle keine
Rückkehr kennt. Das ist ein Satz der Mathematik und keine Lesung Günthers. **Die Marke 3
gilt für ihn NICHT**; die Lesart 0 ≙ Denken, 1 ≙ Zeit, 2 ≙ Wille betrifft allein `cyc3`.

*Verhältnis zu den Teilen 3 und 4.* `no_return` setzt Transitivität voraus und fällt
über `Relation.transGen_eq_self` auf `r` zurück. `cyc3_not_representable` ist der Fall
eines einzelnen Dreierzyklus. Beide sind Fälle von `rang_zyklenfrei`: Eine strikte Ordnung
auf einem endlichen Träger hat einen Rang, ein Dreierzyklus keinen. Das wird hier GESAGT
und nicht umgebaut (KC2 (d)).

*Verbraucher.* `Reformulation/Kaehr/Kopplung.lean` importiert dieses Modul; dort sind
`gestuft` (es gibt eine Rangfunktion) und `geschlossen_ungestuft` zuhause. **Im Term
verbraucht `geschlossen_ungestuft` diesen Satz nicht.** Es beweist seine Instanz direkt
mit zwei Ungleichungen. Der Weg über `rang_zyklenfrei` bei `V = Fin k` zöge über die
Instanz `Fin.fintype` `Classical.choice` (gemessen 3.10.2026, Mathlib 83a5988: eine
Wegwerf-Fassung `gestuft G ↔ ∀ a, ¬ TransGen (ueber G) a a` trug
`[propext, Classical.choice, Quot.sound]`). Fallstrick 10, zweite Verschärfung.

*Choice-frei, und was das kostet.* Die Existenzrichtung `azyklisch_rang` setzt
ρ(a) := Zahl der von `a` aus erreichbaren Knoten. Die Erreichbarkeit ist dabei als
iterierte Menge `erreichtIn` berechnet, nicht klassisch entschieden. Darum stehen
`[DecidableEq V] [DecidableRel r]` in der Signatur. Der Stillstand nach `Fintype.card V`
Schritten folgt aus „Wachstum oder Stillstand" (`erreichtIn_waechst`), ohne
Schubfachschluss über Pfade. Umgangen sind dabei vier Choice-Quellen aus Mathlib (83a5988),
jede einzeln gemessen:
* `Finset.mem_union` und `Finset.mem_biUnion` → der Hüllenschritt nur über `Finset.filter`;
* `Finset.eq_empty_of_forall_notMem` → `Finset.ext` mit `Finset.notMem_empty`;
* `Finset.decidableEq` in einer Fallunterscheidung über Mengengleichheit → die
  Fallunterscheidung über die Kardinalitäten (`Nat.decEq`), die Gleichheit dann aus
  `Finset.eq_of_subset_of_card_le`.

Der kürzere Weg über Wohlfundiertheit fällt aus, weil `Finite.wellFounded_of_trans_of_irrefl`
selbst `Classical.choice` trägt.
-/

namespace Reformulation.Proemial.IntransitivityDifferential

/-! ## Teil 1 — Der Zeuge (M1/M4) -/

/-- Der orientierte 3-Zyklus auf `Fin 3`: `cyc3 a b` ↔ `b = a + 1` — die
    Fin-3-Addition zykliert, Paare (0,1), (1,2), (2,0).
    Lesart (Marke 3, NUR Doc-String): erste Stelle dominiert („a ist von
    höherer Mächtigkeit als b"); 0 ≙ Denken, 1 ≙ Zeit, 2 ≙ Wille
    (Günther 1937). Der Träger selbst ist neutral. -/
def cyc3 : Fin 3 → Fin 3 → Prop := fun a b => b = a + 1

instance : DecidableRel cyc3 := fun a b => decEq b (a + 1)

/-- POSITIVE HÄLFTE: der Zyklus-Zeuge existiert als Term. -/
theorem cyc3_holds : cyc3 0 1 ∧ cyc3 1 2 ∧ cyc3 2 0 := by decide

/-- EHRLICHKEIT (1): der Zeuge ist irreflexiv — er verlässt die arme
    Klasse NICHT an der Irreflexivität. (Irreflexivität ausbuchstabiert;
    die benannten Prädikate `Irreflexive`/`Std.Irrefl` sind hier bewusst
    vermieden, siehe Abweichungs-Notiz.) -/
theorem cyc3_irrefl : ∀ a, ¬ cyc3 a a := by decide

/-- EHRLICHKEIT (2): der Zeuge ist nicht transitiv — er verlässt die arme
    Klasse EXAKT an der Transitivität (cyc3 0 1, cyc3 1 2, ¬ cyc3 0 2).
    (Transitivität ausbuchstabiert als `∀ a b c, r a b → r b c → r a c`.) -/
theorem cyc3_not_transitive : ¬ ∀ a b c, cyc3 a b → cyc3 b c → cyc3 a c := by decide

/-! ## Teil 2 — Negative Hälfte, nackte Fassung (M2) -/

/-- NEGATIVE HÄLFTE (nackt), Günthers Reduktion von 1937 gespiegelt:
    in KEINER transitiv-irreflexiven Struktur (strikte Ordnung) existiert
    ein 3-Zyklus. Quantifiziert über alle Träger und alle Instanzen der
    armen Klasse. -/
theorem no_cycle_in_strict_order {α : Type*} (r : α → α → Prop)
    [IsTrans α r] [Std.Irrefl r] :
    ∀ a b c, ¬ (r a b ∧ r b c ∧ r c a) := by
  rintro a b c ⟨hab, hbc, hca⟩
  -- (i) Verkettung — in Günthers Zählung (2) und (1): a ≻ c
  have hac : r a c := trans_of r hab hbc
  -- (ii) Gegenprinzip (3): c ≻ a — steht als hca bereit.
  -- (iii) Asymmetrie-Kollaps: a ≻ c und c ≻ a ergeben a ≻ a,
  --       gegen die Irreflexivität.
  exact irrefl_of r a (trans_of r hac hca)

/-! ## Teil 3 — Negative Hälfte, Darstellbarkeits-Fassung (M3) -/

/-- NEGATIVE HÄLFTE (Darstellbarkeit): es gibt KEIN relations-erhaltendes
    f vom Zyklus in irgendeine strikte Ordnung — auch kollabierende
    Abbildungen scheitern (Kollaps zweier Zyklus-Punkte erzeugt r x x). -/
theorem cyc3_not_representable {α : Type*} (r : α → α → Prop)
    [IsTrans α r] [Std.Irrefl r] :
    ¬ ∃ f : Fin 3 → α, ∀ a b, cyc3 a b → r (f a) (f b) := by
  rintro ⟨f, hf⟩
  exact no_cycle_in_strict_order r (f 0) (f 1) (f 2)
    ⟨hf 0 1 (by decide), hf 1 2 (by decide), hf 2 0 (by decide)⟩

/-! ## Teil 4 — Kür: Zyklen jeder Länge (K1) -/

/-- KÜR: keine Rückkehr in beliebig vielen Schritten — die transitive
    Hülle einer transitiven Relation fällt auf sie zurück. -/
theorem no_return {α : Type*} (r : α → α → Prop)
    [IsTrans α r] [Std.Irrefl r] :
    ∀ a, ¬ Relation.TransGen r a a := by
  intro a h
  have hr : r a a := by rwa [Relation.transGen_eq_self] at h
  exact irrefl_of r a hr

/-! ## Teil 5 — der allgemeine Rangsatz (Kopf §(6)) -/

/-- RICHTUNG →: eine Rangfunktion schliesst jede Rückkehr aus — für jeden Träger. -/
theorem rang_azyklisch {V : Type*} (r : V → V → Prop) (ρ : V → ℕ)
    (hρ : ∀ a b, r a b → ρ b < ρ a) : ∀ a, ¬ Relation.TransGen r a a := by
  have key : ∀ a b, Relation.TransGen r a b → ρ b < ρ a := by
    intro a b h
    induction h with
    | single hab => exact hρ _ _ hab
    | tail _ hbc ih => exact lt_trans (hρ _ _ hbc) ih
  intro a h; exact lt_irrefl _ (key a a h)

section Rang
variable {V : Type*} [Fintype V] (r : V → V → Prop) [DecidableRel r]

/-- die direkten Nachfolger von `a` -/
def nachfolger (a : V) : Finset V := Finset.univ.filter (r a)

theorem mem_nachfolger {a c : V} : c ∈ nachfolger r a ↔ r a c := by
  simp only [nachfolger, Finset.mem_filter, Finset.mem_univ, true_and]

variable [DecidableEq V]

/-- ein Schritt der Hülle, nur über `filter` (Kopf §(6)) -/
def huellenSchritt (T : Finset V) : Finset V :=
  Finset.univ.filter (fun c => c ∈ T ∨ ∃ d ∈ T, r d c)

theorem mem_huellenSchritt {T : Finset V} {c : V} :
    c ∈ huellenSchritt r T ↔ c ∈ T ∨ ∃ d ∈ T, r d c := by
  simp only [huellenSchritt, Finset.mem_filter, Finset.mem_univ, true_and]

/-- die von `a` aus in höchstens `n + 1` Schritten erreichbaren Knoten -/
def erreichtIn (a : V) : ℕ → Finset V
  | 0 => nachfolger r a
  | n + 1 => huellenSchritt r (erreichtIn a n)

theorem erreichtIn_transGen {a c : V} : ∀ {n}, c ∈ erreichtIn r a n → Relation.TransGen r a c
  | 0, h => .single ((mem_nachfolger r).mp h)
  | n + 1, h => by
    rcases (mem_huellenSchritt r).mp h with h | ⟨d, hd, hdc⟩
    · exact erreichtIn_transGen h
    · exact .tail (erreichtIn_transGen hd) hdc

theorem erreichtIn_mono (a : V) (n : ℕ) : erreichtIn r a n ⊆ erreichtIn r a (n + 1) :=
  fun _ h => (mem_huellenSchritt r).mpr (Or.inl h)

theorem erreichtIn_nach {a b : V} (hab : r a b) :
    ∀ {n c}, c ∈ erreichtIn r b n → c ∈ erreichtIn r a (n + 1)
  | 0, c, h =>
    (mem_huellenSchritt r).mpr (Or.inr ⟨b, (mem_nachfolger r).mpr hab, (mem_nachfolger r).mp h⟩)
  | n + 1, c, h => by
    rcases (mem_huellenSchritt r).mp h with h | ⟨d, hd, hdc⟩
    · exact (mem_huellenSchritt r).mpr (Or.inl (erreichtIn_nach hab h))
    · exact (mem_huellenSchritt r).mpr (Or.inr ⟨d, erreichtIn_nach hab hd, hdc⟩)

/-- gleiche Kardinalität bei Inklusion: der Schritt steht still -/
theorem erreichtIn_gleich (a : V) (n : ℕ)
    (h : (erreichtIn r a (n + 1)).card = (erreichtIn r a n).card) :
    erreichtIn r a (n + 1) = erreichtIn r a n :=
  (Finset.eq_of_subset_of_card_le (erreichtIn_mono r a n) (Nat.le_of_eq h)).symm

/-- Wachstum oder Stillstand. Die Fallunterscheidung läuft über Kardinalitäten, nicht über
    Mengengleichheit (`Finset.decidableEq` trägt Choice, Kopf §(6)). -/
theorem erreichtIn_waechst (a : V) :
    ∀ n, erreichtIn r a (n + 1) = erreichtIn r a n ∨ n + 1 ≤ (erreichtIn r a n).card
  | 0 => by
    rcases Nat.decEq (erreichtIn r a 0).card 0 with h0 | h0
    · right; omega
    · left
      have he : erreichtIn r a 0 = ∅ := Finset.card_eq_zero.mp h0
      show huellenSchritt r (erreichtIn r a 0) = erreichtIn r a 0
      rw [he]
      refine Finset.ext fun c => ⟨fun hc => ?_, fun hc => absurd hc (Finset.notMem_empty c)⟩
      rcases (mem_huellenSchritt r).mp hc with h | ⟨d, hd, _⟩
      · exact absurd h (Finset.notMem_empty c)
      · exact absurd hd (Finset.notMem_empty d)
  | n + 1 => by
    rcases erreichtIn_waechst a n with h | h
    · left
      show huellenSchritt r (erreichtIn r a (n + 1)) = erreichtIn r a (n + 1)
      rw [h]; exact h
    · rcases Nat.decEq (erreichtIn r a (n + 1)).card (erreichtIn r a n).card with hc | hc
      · have hlt : (erreichtIn r a n).card < (erreichtIn r a (n + 1)).card :=
          Nat.lt_of_le_of_ne (Finset.card_le_card (erreichtIn_mono r a n)) (fun he => hc he.symm)
        right; omega
      · left
        have he := erreichtIn_gleich r a n hc
        show huellenSchritt r (erreichtIn r a (n + 1)) = erreichtIn r a (n + 1)
        rw [he]; exact he

/-- nach `Fintype.card V` Schritten steht die Hülle still -/
theorem erreichtIn_stabil (a : V) :
    erreichtIn r a (Fintype.card V + 1) = erreichtIn r a (Fintype.card V) := by
  rcases erreichtIn_waechst r a (Fintype.card V) with h | h
  · exact h
  · exact absurd (Nat.le_trans h (Finset.card_le_univ _)) (Nat.not_succ_le_self _)

/-- RICHTUNG ←: ohne Rückkehr gibt es eine Rangfunktion, ρ(a) = Zahl der von `a` aus
    erreichbaren Knoten. -/
theorem azyklisch_rang (hac : ∀ a, ¬ Relation.TransGen r a a) :
    ∃ ρ : V → ℕ, ∀ a b, r a b → ρ b < ρ a := by
  refine ⟨fun a => (erreichtIn r a (Fintype.card V)).card, ?_⟩
  intro a b hab
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro c hc
    have := erreichtIn_nach r hab hc
    rwa [erreichtIn_stabil] at this
  · intro he
    have hb : b ∈ erreichtIn r a (Fintype.card V) := by
      apply Finset.mem_of_subset (s₁ := erreichtIn r a 0)
      · clear he; induction Fintype.card V with
        | zero => exact Finset.Subset.refl _
        | succ n ih => exact Finset.Subset.trans ih (erreichtIn_mono r a n)
      · exact (mem_nachfolger r).mpr hab
    rw [← he] at hb
    exact hac b (erreichtIn_transGen r hb)

/-- DER RANGSATZ: eine Relation auf einem endlichen Träger hat genau dann eine
    Rangfunktion nach `ℕ`, wenn sie zyklenfrei ist. UNSER, keine Günther-Lesung (Kopf §(6)). -/
theorem rang_zyklenfrei :
    (∃ ρ : V → ℕ, ∀ a b, r a b → ρ b < ρ a) ↔ ∀ a, ¬ Relation.TransGen r a a :=
  ⟨fun ⟨ρ, hρ⟩ => rang_azyklisch r ρ hρ, azyklisch_rang r⟩

end Rang

end Reformulation.Proemial.IntransitivityDifferential

/-! ## Axiom-Stand (Nebenbefund) — als Regressions-Wachen gesetzt

Ist-Ausgabe des grünen Builds (v4.30.0-rc2), pro Satz eingefroren. Ab hier bricht jede
Axiom-Drift den Build. `no_cycle_in_strict_order` trägt die Nicht-Abhängigkeits-Form
(axiom-frei), gemessen und nicht nachgebaut. -/

/-- info: 'Reformulation.Proemial.IntransitivityDifferential.cyc3_holds' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.IntransitivityDifferential.cyc3_holds

/-- info: 'Reformulation.Proemial.IntransitivityDifferential.cyc3_irrefl' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.IntransitivityDifferential.cyc3_irrefl

/-- info: 'Reformulation.Proemial.IntransitivityDifferential.cyc3_not_transitive' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.IntransitivityDifferential.cyc3_not_transitive

/-- info: 'Reformulation.Proemial.IntransitivityDifferential.no_cycle_in_strict_order' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Proemial.IntransitivityDifferential.no_cycle_in_strict_order

/-- info: 'Reformulation.Proemial.IntransitivityDifferential.cyc3_not_representable' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.IntransitivityDifferential.cyc3_not_representable

/-- info: 'Reformulation.Proemial.IntransitivityDifferential.no_return' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.IntransitivityDifferential.no_return

/-! ### Teil 5 — der Rangsatz (3. Oktober 2026, Custos KC2 (c): alle Sätze des Moduls gewacht) -/

/-- info: 'Reformulation.Proemial.IntransitivityDifferential.rang_azyklisch' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Proemial.IntransitivityDifferential.rang_azyklisch

/-- info: 'Reformulation.Proemial.IntransitivityDifferential.mem_nachfolger' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.IntransitivityDifferential.mem_nachfolger

/-- info: 'Reformulation.Proemial.IntransitivityDifferential.mem_huellenSchritt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.IntransitivityDifferential.mem_huellenSchritt

/-- info: 'Reformulation.Proemial.IntransitivityDifferential.erreichtIn_transGen' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.IntransitivityDifferential.erreichtIn_transGen

/-- info: 'Reformulation.Proemial.IntransitivityDifferential.erreichtIn_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.IntransitivityDifferential.erreichtIn_mono

/-- info: 'Reformulation.Proemial.IntransitivityDifferential.erreichtIn_nach' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.IntransitivityDifferential.erreichtIn_nach

/-- info: 'Reformulation.Proemial.IntransitivityDifferential.erreichtIn_gleich' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.IntransitivityDifferential.erreichtIn_gleich

/-- info: 'Reformulation.Proemial.IntransitivityDifferential.erreichtIn_waechst' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.IntransitivityDifferential.erreichtIn_waechst

/-- info: 'Reformulation.Proemial.IntransitivityDifferential.erreichtIn_stabil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.IntransitivityDifferential.erreichtIn_stabil

/-- info: 'Reformulation.Proemial.IntransitivityDifferential.azyklisch_rang' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.IntransitivityDifferential.azyklisch_rang

/-- info: 'Reformulation.Proemial.IntransitivityDifferential.rang_zyklenfrei' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.IntransitivityDifferential.rang_zyklenfrei
