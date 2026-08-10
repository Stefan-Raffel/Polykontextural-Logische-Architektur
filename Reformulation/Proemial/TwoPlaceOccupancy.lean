import Reformulation.Kenogram.Unbounded
import Reformulation.Proemial.RecurringGround
import Reformulation.Proemial.ReversibleExchange

/-!
# Reformulation.Proemial.TwoPlaceOccupancy — die Faser über der zweistelligen Figur

**Ertrag.** Über den zwei Kenogrammen der Länge zwei wird die Wertbelegung
vermessen, und zwar in vier Schritten: der Stellentausch **trennt** die beiden
Figuren; auf der zweiten ist er **involutiv und fixpunktfrei**; beide Fasern
haben eine angebbare **Äquivalenz**; und die Wertvertauschungen wirken auf der
zweiten Faser so, dass **keine invariante Funktion sie aufteilt**.

Der vierte Satz ist die eigentliche Auskunft, und sie ist **negativ**: aus der
Belegung allein lässt sich kein Ordnungsdatum gewinnen. Wer „aufsteigend" von
„absteigend" unterscheiden will, muss die Ordnung des Wertevorrats hinzunehmen —
sie kommt nicht aus dem Muster.

## Quellenanker

Günther, *Erkennen und Wollen*, S. 27: die zwei leeren Quadrate stellen
**Kenogramme** dar; ihre Wertbelegungen ergeben entweder ein symmetrisches
Umtauschverhältnis oder den Charakter einer Ordnung. Der Träger dieses Moduls ist
darum `RGS 2` mit seinen zwei Elementen — **nicht** eine binäre Relation über der
Menge aller Kenogramme.

## Was hier nicht steht

* **Kein `Definitionen.md`-§20-Anspruch.** Kein Satz dieser Datei trägt einen.
  Gebaut ist die Belegungsseite einer zweistelligen Figur, mehr nicht.
* **Keine Ledger-Zeile, keine Marke.** Die zwei Definitionen `figEq` und `figNe`
  sind Benennungen zweier Elemente von `RGS 2` und keine neuen Begriffe.
* **Keine Deutung in einem Satznamen.** Die Namen sagen, was der Satz sagt.

## Die Reichweite von §IV, ausdrücklich

Die beiden Äquivalenzen stehen für `n = 2` und sind **allgemein in `k`**. Die
weitergehende Fassung — über einem RGS mit `m` Marken ist die Faser äquivalent
zur Menge der injektiven Zuordnungen `Fin m ↪ Fin k` — ist **nicht gebaut** und
wird nicht behauptet. Bauform wie `Kenogram.Fiber.fiberEquiv`: als Äquivalenz und
nicht als Kardinalzahl, weil `canonicalize` `noncomputable` ist und eine
Kartenfassung eine `Fintype`-Instanz über einem unentscheidbaren Prädikat
verlangte.

## Die Ablage, als Entscheidung geführt und mit ihrer Messung

Die Datei liegt in `Proemial/` und importiert Richtung Kenogramm; Präzedenz sind
`Proemial.TowerAsymmetry` und `Proemial.RetractionBracket`. Der Grund ist
`swapOnFiber_reversible` und `swapOnFiber_fixpointfree`: sie konsumieren
`Reversible` aus `Proemial.ReversibleExchange` und `FixpointFree` aus
`Proemial.RecurringGround` — **dieselben zwei Prädikate, die
`Proemial.ArrowAscent` in seiner armen Hälfte als Hypothese verlangt.** Eine
Eigenformulierung derselben zwei Bedingungen käme ohne die Importe aus und wäre
messbar billiger: gemessen **19 Module in der Importhülle gegen 11**, im Baum
**10 gegen 5**. Die billigere Lage ist **nicht** gewählt, und der Grund steht
hier statt in einer Fussnote: ohne die Bestands-Prädikate wären die zwei Sätze
eine Analogie zum Umtausch des Bestandes statt derselbe Begriff, und der
Anschluss an `ArrowAscent` ginge verloren. **Der Preis ist gemessen und
gemeldet.** Weder Hülle enthält ein `AlphaGamma*`-Modul; der Kenogram-Zweig
bleibt unberührt.

## Axiomprofile

Alles, was `canonicalize` berührt, erbt `Classical.choice` über den
Kenogram-Zweig. **Zwei Sätze liegen darunter** — `placeSwap_involutive` mit
`[propext]` und `comp_placeSwap_eq_iff` mit `[propext, Quot.sound]`. Das ist
nicht selbstverständlich: die naheliegende Fassung über `fin_cases` zieht
`Classical.choice` auch dort, die Handzerlegung über `Fin`-Konstruktoren nicht.
Gemessen, nicht vermutet.

Kein `sorry`, kein `axiom`, kein `: True`-Feld, kein `native_decide`.
-/

namespace Reformulation.Proemial.TwoPlaceOccupancy

open Reformulation.Kenogram Reformulation.Kenogram.Fillability
open Reformulation.Proemial.RecurringGround (FixpointFree)
open Reformulation.Proemial.ReversibleExchange (Reversible)

-- ============================================================
-- §I — Die zwei Figuren und der Stellentausch
-- ============================================================

/-- Die Figur mit **einer** Marke: beide Stellen tragen dieselbe. -/
def figEq : RGS 2 := ⟨[0, 0], by decide⟩

/-- Die Figur mit **zwei** Marken: die Stellen tragen verschiedene. -/
def figNe : RGS 2 := ⟨[0, 1], by decide⟩

/-- Der Tausch der beiden Stellen. -/
def placeSwap : Fin 2 → Fin 2 := ![1, 0]

/-- Der Stellentausch ist selbstinvers. Handzerlegung über die
`Fin`-Konstruktoren; `fin_cases` an derselben Stelle zöge `Classical.choice`. -/
theorem placeSwap_involutive : ∀ i, placeSwap (placeSwap i) = i := by
  intro i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

/-- Eine Belegung ist unter dem Stellentausch genau dann fest, wenn ihre beiden
Stellen denselben Wert tragen. -/
theorem comp_placeSwap_eq_iff {k : ℕ} (f : Fin 2 → Fin k) :
    f ∘ placeSwap = f ↔ f 0 = f 1 := by
  constructor
  · intro h
    exact (congrFun h 0).symm
  · intro h
    funext i
    match i with
    | ⟨0, _⟩ => exact h.symm
    | ⟨1, _⟩ => exact h

-- ============================================================
-- §II — Z1: der Stellentausch trennt die zwei Figuren
-- ============================================================

private theorem rgsFun_figEq (i : Fin 2) : rgsFun figEq i = 0 := by fin_cases i <;> rfl

private theorem rgsFun_figNe_eq_iff (i j : Fin 2) :
    rgsFun figNe i = rgsFun figNe j ↔ i = j := by
  fin_cases i <;> fin_cases j <;> simp [rgsFun, figNe]

/-- Punktweises Kriterium für die Figur mit einer Marke. -/
theorem canonicalize_eq_figEq_iff_pointwise {k : ℕ} (f : Fin 2 → Fin k) :
    canonicalize f = figEq ↔ f 0 = f 1 := by
  have hr : canonicalize (rgsFun figEq) = figEq := canonicalize_rgsFun figEq
  constructor
  · intro h
    have h2 : canonicalize f = canonicalize (rgsFun figEq) := by rw [hr, h]
    exact ((canonicalize_eq_iff f (rgsFun figEq)).mp h2 0 1).mpr
      (by rw [rgsFun_figEq, rgsFun_figEq])
  · intro h
    have h2 : ∀ i j, f i = f j ↔ rgsFun figEq i = rgsFun figEq j := by
      intro i j
      constructor
      · intro _; rw [rgsFun_figEq, rgsFun_figEq]
      · intro _; fin_cases i <;> fin_cases j <;> first | rfl | exact h | exact h.symm
    rw [← hr]
    exact (canonicalize_eq_iff f (rgsFun figEq)).mpr h2

/-- Punktweises Kriterium für die Figur mit zwei Marken. -/
theorem canonicalize_eq_figNe_iff_pointwise {k : ℕ} (f : Fin 2 → Fin k) :
    canonicalize f = figNe ↔ f 0 ≠ f 1 := by
  simp only [ne_eq]
  have hr : canonicalize (rgsFun figNe) = figNe := canonicalize_rgsFun figNe
  constructor
  · intro h hc
    have h2 : canonicalize f = canonicalize (rgsFun figNe) := by rw [hr, h]
    have := (canonicalize_eq_iff f (rgsFun figNe)).mp h2 0 1
    have h01 : (0 : Fin 2) = 1 := (rgsFun_figNe_eq_iff 0 1).mp (this.mp hc)
    exact absurd h01 (by decide)
  · intro h
    have h2 : ∀ i j, f i = f j ↔ rgsFun figNe i = rgsFun figNe j := by
      intro i j
      rw [rgsFun_figNe_eq_iff]
      constructor
      · intro hij
        fin_cases i <;> fin_cases j <;>
          first | rfl | exact absurd hij h | exact absurd hij.symm h
      · intro hij; rw [hij]
    rw [← hr]
    exact (canonicalize_eq_iff f (rgsFun figNe)).mpr h2

/-- **Z1, erste Hälfte.** Eine Belegung liegt genau dann über der Figur mit einer
Marke, wenn der Stellentausch sie festlässt. -/
theorem canonicalize_eq_figEq_iff {k : ℕ} (f : Fin 2 → Fin k) :
    canonicalize f = figEq ↔ f ∘ placeSwap = f := by
  rw [canonicalize_eq_figEq_iff_pointwise, comp_placeSwap_eq_iff]

/-- **Z1, zweite Hälfte.** Eine Belegung liegt genau dann über der Figur mit zwei
Marken, wenn der Stellentausch sie bewegt.

Zusammen mit der ersten Hälfte: **der Stellentausch trennt die zwei Figuren**,
und der Unterschied hängt allein am Muster, nicht an den Werten. -/
theorem canonicalize_eq_figNe_iff {k : ℕ} (f : Fin 2 → Fin k) :
    canonicalize f = figNe ↔ f ∘ placeSwap ≠ f := by
  rw [canonicalize_eq_figNe_iff_pointwise, ne_eq, ne_eq, comp_placeSwap_eq_iff]

-- ============================================================
-- §III — Z2: der Tausch auf der Faser der zweiten Figur
-- ============================================================

/-- Die Faser der zweistelligen Belegungen über der Figur mit zwei Marken. -/
def DistinctFiber (k : ℕ) : Type := {f : Fin 2 → Fin k // canonicalize f = figNe}

/-- Der Stellentausch, auf diese Faser eingeschränkt. Er verlässt sie nicht. -/
def swapOnFiber {k : ℕ} (f : DistinctFiber k) : DistinctFiber k :=
  ⟨f.1 ∘ placeSwap, by
    rw [canonicalize_eq_figNe_iff_pointwise]
    have h := (canonicalize_eq_figNe_iff_pointwise f.1).mp f.2
    show f.1 (placeSwap 0) ≠ f.1 (placeSwap 1)
    exact fun hc => h (by simpa [placeSwap] using hc.symm)⟩

/-- **Z2, erste Hälfte.** Der Tausch auf der Faser ist selbstinvers — `Reversible`
im Sinn von `Proemial.ReversibleExchange`. -/
theorem swapOnFiber_reversible {k : ℕ} : Reversible (swapOnFiber (k := k)) := by
  intro f
  apply Subtype.ext
  funext i
  show f.1 (placeSwap (placeSwap i)) = f.1 i
  rw [placeSwap_involutive]

/-- **Z2, zweite Hälfte.** Der Tausch auf der Faser hat keinen Fixpunkt —
`FixpointFree` im Sinn von `Proemial.RecurringGround`.

Damit trägt die Faser über der zweiten Figur genau die zwei Eigenschaften, die
`Proemial.ArrowAscent` in seiner armen Hälfte als Hypothese verlangt. -/
theorem swapOnFiber_fixpointfree {k : ℕ} : FixpointFree (swapOnFiber (k := k)) := by
  intro f hc
  have h := (canonicalize_eq_figNe_iff_pointwise f.1).mp f.2
  have := congrFun (congrArg Subtype.val hc) 0
  exact h (by simpa [placeSwap] using this.symm)

-- ============================================================
-- §IV — Z3: die zwei Fasern, als Äquivalenz
-- ============================================================

/-- **Z3, erste Hälfte.** Über der Figur mit einer Marke liegen genau die
konstanten Belegungen: die Faser ist äquivalent zum Wertevorrat. -/
def fiberEqualEquiv {k : ℕ} : {f : Fin 2 → Fin k // canonicalize f = figEq} ≃ Fin k where
  toFun f := f.1 0
  invFun c := ⟨fun _ => c, by rw [canonicalize_eq_figEq_iff_pointwise]⟩
  left_inv := by
    rintro ⟨f, hf⟩
    apply Subtype.ext
    have h01 : f 0 = f 1 := (canonicalize_eq_figEq_iff_pointwise f).mp hf
    funext i
    fin_cases i
    · rfl
    · exact h01
  right_inv := by intro c; rfl

/-- **Z3, zweite Hälfte.** Über der Figur mit zwei Marken liegen genau die
geordneten Paare verschiedener Werte. -/
def fiberDistinctEquiv {k : ℕ} :
    DistinctFiber k ≃ {p : Fin k × Fin k // p.1 ≠ p.2} where
  toFun f := ⟨(f.1 0, f.1 1), (canonicalize_eq_figNe_iff_pointwise f.1).mp f.2⟩
  invFun p := ⟨![p.1.1, p.1.2], by
    rw [canonicalize_eq_figNe_iff_pointwise]; exact p.2⟩
  left_inv := by
    rintro ⟨f, hf⟩
    apply Subtype.ext
    funext i
    fin_cases i <;> rfl
  right_inv := by rintro ⟨⟨a, b⟩, h⟩; rfl

-- ============================================================
-- §V — Z4: die Wertvertauschungen und ihre Folge
-- ============================================================

/-- Die Wertvertauschungen wirken auf der Faser: eine Bijektion des Wertevorrats
erhält die Verschiedenheit der beiden Stellen. -/
def permAct {k : ℕ} (π : Equiv.Perm (Fin k)) (f : DistinctFiber k) : DistinctFiber k :=
  ⟨π ∘ f.1, by
    rw [canonicalize_eq_figNe_iff_pointwise]
    have h := (canonicalize_eq_figNe_iff_pointwise f.1).mp f.2
    exact fun hc => h (π.injective hc)⟩

private theorem swap_two_of_ne (a b c d : Fin 2) (hab : a ≠ b) (hcd : c ≠ d) :
    Equiv.swap a c b = d := by
  revert hab hcd
  revert a b c d
  decide

/-- Bei zwei Werten wirken die Wertvertauschungen auf der Faser **transitiv**. -/
theorem permAct_surjective_two (f g : DistinctFiber 2) :
    ∃ π : Equiv.Perm (Fin 2), permAct π f = g := by
  refine ⟨Equiv.swap (f.1 0) (g.1 0), ?_⟩
  apply Subtype.ext
  funext i
  have hf := (canonicalize_eq_figNe_iff_pointwise f.1).mp f.2
  have hg := (canonicalize_eq_figNe_iff_pointwise g.1).mp g.2
  fin_cases i
  · show Equiv.swap (f.1 0) (g.1 0) (f.1 0) = g.1 0
    exact Equiv.swap_apply_left _ _
  · show Equiv.swap (f.1 0) (g.1 0) (f.1 1) = g.1 1
    exact swap_two_of_ne _ _ _ _ hf hg

/-- **Z4.** Jede unter den Wertvertauschungen invariante Funktion auf der Faser
ist konstant.

**Die Auskunft ist negativ, und sie ist der Ertrag dieses Moduls:** aus der
Belegung allein ist kein Ordnungsdatum zu gewinnen. Die Figur gibt den Tausch
(§II, §III) und gibt die Ordnung nicht. Wer zwei Belegungen derselben Figur
unterscheiden will, muss die Ordnung des Wertevorrats hinzunehmen — ein Datum,
das im Muster nicht vorkommt.

Die Aussage steht hier für den zweielementigen Wertevorrat; für grössere `k` ist
sie **nicht gebaut** und wird nicht behauptet. -/
theorem invariant_const_two {β : Type*} (F : DistinctFiber 2 → β)
    (hF : ∀ (π : Equiv.Perm (Fin 2)) (f : DistinctFiber 2), F (permAct π f) = F f) :
    ∀ f g : DistinctFiber 2, F f = F g := by
  intro f g
  obtain ⟨π, hπ⟩ := permAct_surjective_two f g
  calc F f = F (permAct π f) := (hF π f).symm
    _ = F g := by rw [hπ]

-- ============================================================
-- §VI — Wachen: Axiom-Profile
-- ============================================================

/-! **Wachen.** Ist-Ausgabe des grünen Builds, pro Deklaration eingefroren.
Die Erwartung der Spezifikation — alles, was `canonicalize` berührt, erbt
`Classical.choice` — trifft; die zwei Sätze, die es nicht berühren, liegen
darunter. -/

/-- info: 'Reformulation.Proemial.TwoPlaceOccupancy.placeSwap_involutive' depends on axioms: [propext] -/
#guard_msgs in #print axioms placeSwap_involutive

/-- info: 'Reformulation.Proemial.TwoPlaceOccupancy.comp_placeSwap_eq_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms comp_placeSwap_eq_iff

/--
info: 'Reformulation.Proemial.TwoPlaceOccupancy.canonicalize_eq_figEq_iff_pointwise' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms canonicalize_eq_figEq_iff_pointwise

/--
info: 'Reformulation.Proemial.TwoPlaceOccupancy.canonicalize_eq_figNe_iff_pointwise' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms canonicalize_eq_figNe_iff_pointwise

/--
info: 'Reformulation.Proemial.TwoPlaceOccupancy.canonicalize_eq_figEq_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms canonicalize_eq_figEq_iff

/--
info: 'Reformulation.Proemial.TwoPlaceOccupancy.canonicalize_eq_figNe_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms canonicalize_eq_figNe_iff

/-- info: 'Reformulation.Proemial.TwoPlaceOccupancy.swapOnFiber' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms swapOnFiber

/--
info: 'Reformulation.Proemial.TwoPlaceOccupancy.swapOnFiber_reversible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms swapOnFiber_reversible

/--
info: 'Reformulation.Proemial.TwoPlaceOccupancy.swapOnFiber_fixpointfree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms swapOnFiber_fixpointfree

/-- info: 'Reformulation.Proemial.TwoPlaceOccupancy.fiberEqualEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fiberEqualEquiv

/-- info: 'Reformulation.Proemial.TwoPlaceOccupancy.fiberDistinctEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fiberDistinctEquiv

/-- info: 'Reformulation.Proemial.TwoPlaceOccupancy.permAct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms permAct

/--
info: 'Reformulation.Proemial.TwoPlaceOccupancy.permAct_surjective_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms permAct_surjective_two

/--
info: 'Reformulation.Proemial.TwoPlaceOccupancy.invariant_const_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms invariant_const_two

end Reformulation.Proemial.TwoPlaceOccupancy
