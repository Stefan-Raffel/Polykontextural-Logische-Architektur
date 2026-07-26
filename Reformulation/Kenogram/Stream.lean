import Reformulation.Kenogram.Basic
import Mathlib.Data.Stream.Init
import Mathlib.Data.Stream.Defs

/-!
# Reformulation.Kenogram.Stream — F-2 / S2, die Strom-Schicht (finale Koalgebra)

Zweite Schicht (S2, ko-induktiv) der Modul-Familie `Kenogram`. S1
(`Kenogram.Basic`) hat den endlichen Anschnitt verifiziert; S2 legt die
kenogrammatische **Möglichkeits-Schicht in voller Form** nieder — die
unbeschränkte Verlängerung als Subtyp von `Stream' ℕ`. Vier Phasen:

1. **Trägerstruktur** `RGSStream` (Subtyp von `Stream' ℕ` mit Wachstums-Bedingung).
2. **Bisimulations-Kern** `relabelStream_eq_iff` (die ko-induktive
   Verallgemeinerung von `canonicalize_eq_iff` aus S1 — die Beweis-Last).
3. **K-7-Einlösung** `kenogram_no_reduction_basis` (Finalität als Abwesenheit
   initialer Basis, ruht auf dem Kern).
4. **A3-Strom-Feinheit** (Sub-Substanz-J-Sondierung — Bewohnbarkeits-Frage,
   ehrlich offen).

## Beweis-Architektur-Befund (zentral, B-Block aufgelöst)

`Stream' α` ist in Mathlib **definitorisch** `ℕ → α` (`Mathlib.Data.Stream.Defs`),
und `Stream'.ext` ist die Funktions-Extensionalität. Damit fällt die antizipierte
ko-induktive Bisimulations-Last auf **punktweise Funktions-Gleichheit** zusammen:
Strom-Gleichheit ⇔ `∀ n, get s₁ n = get s₂ n`. Der Bisimulations-Kern ist daher
*nicht* über `Stream'.eq_of_bisim` / eine eigene ko-induktive Relation geführt,
sondern über eine **punktweise** Beobachtungs-Normalform `label`:

* `firstOcc s n` — die Position des ersten Auftretens des Wertes `s n`
  (`Nat.find`, die `firstOcc`-Präzisierung der Spec, injektiv im Limit statt
  `List.Nodup`).
* `numDistinct s m` — die Zahl distinkter Werte im Präfix `s 0 … s (m-1)`.
* `label s n := numDistinct s (firstOcc s n)` — der Klassen-Index (Rang) nach
  erstem Auftreten, die Strom-Normalform.

`relabelStream s` ist `⟨fun n => label s n, _⟩`. Die zwei Spec-Sondierungs-Stellen
sind damit aufgelöst: (i) die `firstOcc`-Injektivität trägt `label_eq_iff`
(Rang = Wert-Klasse); (ii) die Mathlib-Stream-Bisimulations-API ist `Stream'.ext`
= Funktions-Extensionalität (kein eigenes Bisimulations-Prinzip nötig).

## K-Anker (zeichengetreu, aus S1 fortgeführt)

* **K-1** — der Strom ist die reine Leerstellen-Folge (`Stream' ℕ`, *kein* `None`;
  die Belegung K-6 ist separat). Die Möglichkeits/Aktualitäts-Grenze am reinsten.
* **K-3** — die Erzeugungs-Regel „wiederholen oder neu setzen" ist `IsRGSStream`
  im Unendlichen: jeder Wert überschreitet das bisherige Maximum um höchstens eins.
* **K-7** — Finalität als Abwesenheit initialer Basis (`kenogram_no_reduction_basis`,
  Phase 3): die finale Koalgebra ist Grenzpunkt (Senke), nicht Quelle.

Spec: F2_S2_Sub_Spec.md. Prompt: F2_S2_Sub_Prompt.md. Frühjahr 2026.
-/

namespace Reformulation.Kenogram.Stream

variable {α : Type*} [DecidableEq α]

/-! ## Phase 1 — Trägerstruktur (Subtyp von `Stream' ℕ`)

**Erste Doc-string-Pflicht (Subtyp-Trägerwahl, M-Typ als [Kandidat]).**
Die Trägerwahl ist der **Subtyp** von `Stream' ℕ`, nicht der M-Typ (die
finale Koalgebra als Objekt). Begründung (dreifach beglaubigte VK-Entscheidung):
K-7 verlangt die finale Koalgebra *nicht* als Objekt — K-7 ist Abwesenheits-Befund
über die initiale Basis, und die Finalität bezeugt ihn über die
**Bisimulations-Charakterisierung** (`relabelStream_eq_iff`), nicht über die
Objekt-Universalität. Die struktur-reine Universalität-als-Objekt-Form (M-Typ)
bleibt **[Kandidat]** für eine spätere, eigens motivierte Vermittlungs-Verschärfung
(Vermittlungs-Substanz, nicht F-2-Substanz). -/

/-- Wohlgeformtheit eines kenogrammatischen Stroms: `a₀ = 0` und an jeder
Position wächst der Wert höchstens um eins über das bisherige Maximum
(K-3 Erzeugungs-Regel im Unendlichen). -/
def IsRGSStream (s : Stream' ℕ) : Prop :=
  s.get 0 = 0 ∧ ∀ n, s.get (n + 1) ≤ (Finset.range (n + 1)).sup (fun i => s.get i) + 1

/-- `RGSStream`: die unendlichen *restricted growth strings* als Subtyp von
`Stream' ℕ`. Trägerstruktur der Möglichkeits-Schicht in voller Form. -/
def RGSStream := { s : Stream' ℕ // IsRGSStream s }

/-! ## Phase 2 — Bisimulations-Kern (die Last), über punktweise Normalform

**Zweite Doc-string-Pflicht (Bisimulations-Invariante, offener Ausgang —
aufgelöst).** Die antizipierte Bisimulations-Invariante ist hier punktweise
realisiert (siehe Modul-Doc). Die zwei Sondierungs-Stellen:

* (i) **`firstOcc`-Injektivität im Limit** (statt `List.Nodup`): getragen von
  `label_eq_iff` — zwei Positionen tragen genau dann denselben Rang, wenn sie
  denselben Wert tragen. Die Rang-Funktion ist auf den Wert-Klassen injektiv
  (strenge Monotonie in `firstOcc`).
* (ii) **Mathlib-Stream-Bisimulations-API**: `Stream' α = ℕ → α` und
  `Stream'.ext` = Funktions-Extensionalität. Der Ausgang der Antizipation ist
  damit *positiv* — die ko-induktive Last reduziert sich auf punktweise
  Funktions-Gleichheit, kein eigenes Bisimulations-Prinzip nötig. -/

/-- Die Position des ersten Auftretens des Wertes `s n` — die ko-induktive
`firstOcc`-Präzisierung (injektive Funktion statt `List.Nodup` im Limit). -/
def firstOcc (s : Stream' α) (n : ℕ) : ℕ :=
  Nat.find (p := fun k => s k = s n) ⟨n, rfl⟩

/-- Der Wert an der ersten Auftretens-Position ist der Wert an `n`. -/
theorem firstOcc_spec (s : Stream' α) (n : ℕ) : s (firstOcc s n) = s n :=
  Nat.find_spec (p := fun k => s k = s n) ⟨n, rfl⟩

/-- Die erste Auftretens-Position ist minimal: jede Position `k` mit `s k = s n`
beschränkt `firstOcc s n` nach oben. -/
theorem firstOcc_le_of_eq (s : Stream' α) {k n : ℕ} (h : s k = s n) :
    firstOcc s n ≤ k :=
  Nat.find_min' (p := fun m => s m = s n) ⟨n, rfl⟩ h

/-- `firstOcc s n ≤ n` (die Stelle `n` selbst ist ein Zeuge). -/
theorem firstOcc_le (s : Stream' α) (n : ℕ) : firstOcc s n ≤ n :=
  firstOcc_le_of_eq s rfl

/-- Vor der ersten Auftretens-Position tritt der Wert `s n` nicht auf. -/
theorem firstOcc_min (s : Stream' α) {k n : ℕ} (h : k < firstOcc s n) :
    s k ≠ s n :=
  Nat.find_min (p := fun m => s m = s n) ⟨n, rfl⟩ h

/-- `firstOcc` hängt nur vom Wert ab: gleiche Werte haben dieselbe erste
Auftretens-Position. -/
theorem firstOcc_eq_of_value (s : Stream' α) {i j : ℕ} (h : s i = s j) :
    firstOcc s i = firstOcc s j := by
  apply le_antisymm
  · exact firstOcc_le_of_eq s (by rw [firstOcc_spec s j]; exact h.symm)
  · exact firstOcc_le_of_eq s (by rw [firstOcc_spec s i]; exact h)

/-- `firstOcc` ist idempotent: die erste Auftretens-Position ist selbst eine
erste Auftretens-Position. -/
theorem firstOcc_firstOcc (s : Stream' α) (n : ℕ) :
    firstOcc s (firstOcc s n) = firstOcc s n :=
  firstOcc_eq_of_value s (firstOcc_spec s n)

/-- Die Zahl distinkter Werte im Präfix `s 0 … s (m-1)` (Bild der Wert-Funktion
über `range m`). -/
def numDistinct (s : Stream' α) (m : ℕ) : ℕ := ((Finset.range m).image s).card

/-- **Strom-Beobachtungs-Normalform** `label`: der Klassen-Index (Rang) des
Wertes `s n` nach erstem Auftreten = die Zahl distinkter Werte, die *vor* dem
ersten Auftreten von `s n` auftreten. Die punktweise Strom-Form von `relabel`
(S1). -/
def label (s : Stream' α) (n : ℕ) : ℕ := numDistinct s (firstOcc s n)

/-- `label` an einer ersten Auftretens-Position stimmt mit `label` an der
Original-Position überein. -/
theorem label_firstOcc (s : Stream' α) (n : ℕ) :
    label s (firstOcc s n) = label s n := by
  rw [label, label, firstOcc_firstOcc]

/-- Ein Wert tritt im Präfix `range n` genau dann auf, wenn seine erste
Auftretens-Position vor `n` liegt. -/
theorem mem_image_range_iff (s : Stream' α) (n : ℕ) :
    s n ∈ (Finset.range n).image s ↔ firstOcc s n < n := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨k, hk, hkn⟩
    rw [Finset.mem_range] at hk
    exact lt_of_le_of_lt (firstOcc_le_of_eq s hkn) hk
  · intro h
    exact ⟨firstOcc s n, Finset.mem_range.mpr h, firstOcc_spec s n⟩

/-- Rekurrenz von `numDistinct`: beim Fortschreiten um eine Position wächst die
Zahl distinkter Werte um eins genau dann, wenn der neue Wert neu ist. -/
theorem numDistinct_succ (s : Stream' α) (n : ℕ) :
    numDistinct s (n + 1)
      = numDistinct s n + (if s n ∈ (Finset.range n).image s then 0 else 1) := by
  unfold numDistinct
  rw [Finset.range_add_one, Finset.image_insert]
  by_cases h : s n ∈ (Finset.range n).image s
  · rw [if_pos h, Finset.card_insert_of_mem h, Nat.add_zero]
  · rw [if_neg h, Finset.card_insert_of_notMem h]

/-- **Schlüssel-Schranke** (trägt die Wachstums-Bedingung): die Zahl distinkter
Werte im Präfix `range m` überschreitet das Rang-Maximum dieses Präfixes um
höchstens eins. Induktion über `m`; im Neu-Fall ist `label s m = numDistinct s m`. -/
theorem numDistinct_le_sup (s : Stream' α) (m : ℕ) :
    numDistinct s m ≤ (Finset.range m).sup (fun i => label s i) + 1 := by
  induction m with
  | zero => simp [numDistinct]
  | succ m ih =>
    rw [numDistinct_succ]
    by_cases h : s m ∈ (Finset.range m).image s
    · rw [if_pos h, Nat.add_zero]
      have hmono : (Finset.range m).sup (fun i => label s i)
          ≤ (Finset.range (m + 1)).sup (fun i => label s i) :=
        Finset.sup_mono (Finset.range_subset_range.mpr (Nat.le_succ m))
      omega
    · rw [if_neg h]
      have hfo : firstOcc s m = m :=
        le_antisymm (firstOcc_le s m)
          (not_lt.mp (fun hc => h ((mem_image_range_iff s m).mpr hc)))
      have hlabel : label s m = numDistinct s m := by rw [label, hfo]
      have hle : label s m ≤ (Finset.range (m + 1)).sup (fun i => label s i) :=
        Finset.le_sup (Finset.mem_range.mpr (Nat.lt_succ_self m))
      omega

/-- **Wachstums-Schritt** der Strom-Normalform (trägt `IsRGSStream`): der Rang an
`n+1` überschreitet das Rang-Maximum des Präfixes um höchstens eins — im
Wiederhol-Fall ist er ein früherer Rang, im Neu-Fall genau das Maximum plus eins. -/
theorem label_succ_le (s : Stream' α) (n : ℕ) :
    label s (n + 1) ≤ (Finset.range (n + 1)).sup (fun i => label s i) + 1 := by
  by_cases h : firstOcc s (n + 1) < n + 1
  · have hle : label s (n + 1) ≤ (Finset.range (n + 1)).sup (fun i => label s i) := by
      rw [← label_firstOcc s (n + 1)]
      exact Finset.le_sup (Finset.mem_range.mpr h)
    omega
  · have hfo : firstOcc s (n + 1) = n + 1 :=
      le_antisymm (firstOcc_le s (n + 1)) (not_lt.mp h)
    have hlabel : label s (n + 1) = numDistinct s (n + 1) := by rw [label, hfo]
    rw [hlabel]
    exact numDistinct_le_sup s (n + 1)

/-- `fun n => label s n` ist ein wohlgeformter kenogrammatischer Strom. -/
theorem isRGSStream_label (s : Stream' α) : IsRGSStream (fun n => label s n) := by
  refine ⟨?_, ?_⟩
  · show label s 0 = 0
    rw [label, show firstOcc s 0 = 0 from Nat.le_zero.mp (firstOcc_le s 0)]
    simp [numDistinct]
  · intro n
    show label s (n + 1) ≤ (Finset.range (n + 1)).sup (fun i => label s i) + 1
    exact label_succ_le s n

/-- **Die Strom-Beobachtungs-Normalform** `relabelStream`: jedem rohen Wertstrom
seinen kenogrammatischen Strom (Klassen-Index nach erstem Auftreten). Die
punktweise Strom-Verallgemeinerung von `relabel` (S1). -/
def relabelStream (s : Stream' α) : RGSStream :=
  ⟨fun n => label s n, isRGSStream_label s⟩

/-- Strenge Monotonie der Rang-Funktion in `firstOcc`: eine frühere erste
Auftretens-Position trägt einen echt kleineren Rang. Trägt die Injektivität von
`label` auf Wert-Klassen (firstOcc-Präzisierung, Sondierungs-Stelle (i)). -/
theorem label_lt_of_firstOcc_lt (s : Stream' α) {i j : ℕ}
    (h : firstOcc s i < firstOcc s j) : label s i < label s j := by
  rw [label, label]
  have hsub : (Finset.range (firstOcc s i)).image s
      ⊆ (Finset.range (firstOcc s j)).image s :=
    Finset.image_subset_image (Finset.range_subset_range.mpr (le_of_lt h))
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset hsub]
  refine ⟨s (firstOcc s i), Finset.mem_image.mpr ⟨firstOcc s i, Finset.mem_range.mpr h, rfl⟩, ?_⟩
  rw [Finset.mem_image]
  rintro ⟨k, hk, hks⟩
  rw [Finset.mem_range] at hk
  exact firstOcc_min s hk (by rw [hks]; exact firstOcc_spec s i)

/-- **Rang = Wert-Klasse (Schlüssel-Lemma).** Zwei Positionen tragen genau dann
denselben Rang, wenn sie denselben Wert tragen. Die punktweise Auflösung der
`firstOcc`-Injektivität; trägt beide Richtungen des Bisimulations-Kerns. -/
theorem label_eq_iff (s : Stream' α) (i j : ℕ) :
    label s i = label s j ↔ s i = s j := by
  constructor
  · intro h
    by_contra hne
    have hfne : firstOcc s i ≠ firstOcc s j := by
      intro he
      apply hne
      rw [← firstOcc_spec s i, ← firstOcc_spec s j, he]
    rcases lt_or_gt_of_ne hfne with hlt | hgt
    · exact absurd h (ne_of_lt (label_lt_of_firstOcc_lt s hlt))
    · exact absurd h.symm (ne_of_lt (label_lt_of_firstOcc_lt s hgt))
  · intro h
    rw [label, label, firstOcc_eq_of_value s h]

/-- Unter gleichem Gleichheits-Muster stimmen die ersten Auftretens-Positionen
überein (die `firstOcc`-Prädikate sind als Mengen gleich). -/
theorem firstOcc_eq_of_pattern {f g : Stream' α}
    (hpat : ∀ i j, f i = f j ↔ g i = g j) (n : ℕ) :
    firstOcc f n = firstOcc g n := by
  apply le_antisymm
  · exact firstOcc_le_of_eq f ((hpat (firstOcc g n) n).mpr (firstOcc_spec g n))
  · exact firstOcc_le_of_eq g ((hpat (firstOcc f n) n).mp (firstOcc_spec f n))

/-- Unter gleichem Gleichheits-Muster stimmt die Zahl distinkter Werte in jedem
Präfix überein (Induktion: der „neu/wiederholt"-Status hängt nur vom Muster ab). -/
theorem numDistinct_eq_of_pattern {f g : Stream' α}
    (hpat : ∀ i j, f i = f j ↔ g i = g j) (m : ℕ) :
    numDistinct f m = numDistinct g m := by
  induction m with
  | zero => simp [numDistinct]
  | succ m ih =>
    rw [numDistinct_succ, numDistinct_succ, ih]
    congr 1
    have hiff : (f m ∈ (Finset.range m).image f) ↔ (g m ∈ (Finset.range m).image g) := by
      simp only [Finset.mem_image, Finset.mem_range]
      constructor
      · rintro ⟨k, hk, hkm⟩; exact ⟨k, hk, (hpat k m).mp hkm⟩
      · rintro ⟨k, hk, hkm⟩; exact ⟨k, hk, (hpat k m).mpr hkm⟩
    by_cases h : f m ∈ (Finset.range m).image f
    · rw [if_pos h, if_pos (hiff.mp h)]
    · rw [if_neg h, if_neg (fun hc => h (hiff.mpr hc))]

/-- ## BISIMULATIONS-KERN (der Hauptbeweis von S2).

Zwei rohe Wertströme haben dieselbe kenogrammatische Normalform genau dann, wenn
sie an allen Positionen-Paaren dasselbe Gleichheits-Muster tragen — die
ko-induktive Verallgemeinerung der endlichen Finalitäts-These `canonicalize_eq_iff`
(S1). **Strom-Trito-Identität = ko-induktive Verhaltens-Äquivalenz.**

Die Strom-Gleichheit fällt über `Stream'.ext` (Funktions-Extensionalität) auf
`∀ n, label f n = label g n` zusammen; die `⇒`-Richtung über `label_eq_iff`
(Rang = Wert-Klasse), die `⇐`-Richtung über `firstOcc_eq_of_pattern` und
`numDistinct_eq_of_pattern` (Normalform hängt nur vom Muster ab). -/
theorem relabelStream_eq_iff (f g : Stream' α) :
    relabelStream f = relabelStream g ↔ (∀ i j, f i = f j ↔ g i = g j) := by
  constructor
  · intro h i j
    have hlab : ∀ n, label f n = label g n :=
      fun n => congrFun (congrArg Subtype.val h) n
    rw [← label_eq_iff f i j, hlab i, hlab j]
    exact label_eq_iff g i j
  · intro hpat
    apply Subtype.ext
    funext n
    show label f n = label g n
    rw [label, label, firstOcc_eq_of_pattern hpat n, numDistinct_eq_of_pattern hpat]

/-! ## Phase 3 — K-7-Einlösung (Finalität als Abwesenheit initialer Basis)

K-7 ruht auf dem Bisimulations-Kern (Phase 2). Die **strukturlogische** Einlösung
ist `kenogram_no_reduction_basis`: jeder kenogrammatische Strom ist seine eigene
Normalform (`relabelStream` ist eine **Retraktion**). Das ist der Senke- bzw.
Grenzpunkt-Befund: die finale Koalgebra wird nicht aus einer tieferen Basis
*erzeugt* —
die kenogrammatischen Ströme sind genau die Fixpunkte der Beobachtungs-Normalform,
nicht das Bild eines initialen Erzeugungs-Morphismus. Zusammen mit
`relabelStream_eq_iff` (Identität = Beobachtungs-Identität, nicht
Ableitungs-Identität) ist K-7 strukturlogisch eingelöst, nicht nur
Doc-string-verortet. -/

/-- Dichtheit der Ränge (Strom-Form der RGS-Dichtheit): die Ränge der ersten `m`
Positionen sind genau `{0, …, numDistinct s m - 1}` — ein lückenloses
Anfangssegment. (Wiederhol-Schritt absorbiert über die Induktions-Gleichheit;
Neu-Schritt verlängert das Segment um genau eins.) -/
theorem image_label_range (s : Stream' α) (m : ℕ) :
    (Finset.range m).image (fun i => label s i) = Finset.range (numDistinct s m) := by
  induction m with
  | zero => simp [numDistinct]
  | succ m ih =>
    rw [Finset.range_add_one, Finset.image_insert, ih]
    by_cases h : firstOcc s m < m
    · have hmem : label s m ∈ Finset.range (numDistinct s m) := by
        rw [← ih]
        exact Finset.mem_image.mpr ⟨firstOcc s m, Finset.mem_range.mpr h, label_firstOcc s m⟩
      have hsame : numDistinct s (m + 1) = numDistinct s m := by
        rw [numDistinct_succ, if_pos ((mem_image_range_iff s m).mpr h), Nat.add_zero]
      rw [Finset.insert_eq_self.mpr hmem, hsame]
    · have hfo : firstOcc s m = m := le_antisymm (firstOcc_le s m) (not_lt.mp h)
      have hlm : label s m = numDistinct s m := by rw [label, hfo]
      have hnd : numDistinct s (m + 1) = numDistinct s m + 1 := by
        rw [numDistinct_succ, if_neg (fun hc => h ((mem_image_range_iff s m).mp hc))]
      rw [hlm, hnd, Finset.range_add_one]

/-- Ein kenogrammatischer Strom ist seine eigene Normalform: `label s n = s n`.
Strom-Form der S1-Aussage `relabel_eq_self_of_isRGS`. Strenge Induktion über die
Position: Wiederhol-Stellen über den früheren Rang, Neu-Stellen über die Dichtheit
(`image_label_range`) und die Wachstums-Bedingung. -/
theorem label_eq_self (s : Stream' ℕ) (hs : IsRGSStream s) (n : ℕ) : label s n = s n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : firstOcc s n < n
    · -- Wiederhol-Stelle
      rw [← label_firstOcc s n, ih (firstOcc s n) h, firstOcc_spec s n]
    · -- Neu-Stelle
      have hfo : firstOcc s n = n := le_antisymm (firstOcc_le s n) (not_lt.mp h)
      have hlm : label s n = numDistinct s n := by rw [label, hfo]
      rcases Nat.eq_zero_or_pos n with hn0 | hnpos
      · subst hn0
        have h0 : s 0 = 0 := hs.1
        rw [hlm, show numDistinct s 0 = 0 from by simp [numDistinct], h0]
      · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
        rw [hlm]
        -- die Präfix-Werte sind genau die Präfix-Ränge (Induktion), also `range N`
        have himg : (Finset.range (k + 1)).image s = Finset.range (numDistinct s (k + 1)) := by
          rw [show (Finset.range (k + 1)).image s = (Finset.range (k + 1)).image (fun i => label s i)
              from Finset.image_congr (by
                intro x hx
                exact (ih x (Finset.mem_range.mp (Finset.mem_coe.mp hx))).symm)]
          exact image_label_range s (k + 1)
        have hNpos : 0 < numDistinct s (k + 1) := by
          rw [numDistinct, Finset.card_pos]
          exact ⟨s 0, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (Nat.succ_pos k), rfl⟩⟩
        have hnotin : s (k + 1) ∉ (Finset.range (k + 1)).image s := by
          rw [mem_image_range_iff, hfo]; exact lt_irrefl _
        have hge : numDistinct s (k + 1) ≤ s (k + 1) := by
          by_contra hc
          exact hnotin (himg.symm ▸ Finset.mem_range.mpr (not_le.mp hc))
        have hgrow : s (k + 1) ≤ (Finset.range (k + 1)).sup s + 1 := hs.2 k
        have hsuplt : (Finset.range (k + 1)).sup s < numDistinct s (k + 1) := by
          rw [Finset.sup_lt_iff hNpos]
          intro b hb
          exact Finset.mem_range.mp (himg ▸ Finset.mem_image.mpr ⟨b, hb, rfl⟩)
        omega

/-- ## K-7 (Negativ-Test, strukturlogische Einlösung): keine Reduktionsbasis.

Die kenogrammatische Strom-Identität ist **Beobachtungs-Identität** (Bisimulation),
nicht **Ableitungs-Identität** (Quotient einer initialen Basis): jeder
kenogrammatische Strom ist Fixpunkt der Beobachtungs-Normalform `relabelStream`,
diese ist also eine Retraktion auf die Träger der finalen Koalgebra. Die finale
Koalgebra ist **Grenzpunkt (Senke), nicht Quelle** — es gibt keine
Reduktionsbasis, aus der die Ströme deduziert werden. Eingelöst über die
Bisimulations-Charakterisierung (nicht über Objekt-Universalität — daher Subtyp,
nicht M-Typ; VK-Trägerwahl). Ruht auf `relabelStream_eq_iff` und `label_eq_self`. -/
theorem kenogram_no_reduction_basis (r : RGSStream) : relabelStream r.1 = r := by
  apply Subtype.ext
  funext n
  show label r.1 n = r.1 n
  exact label_eq_self r.1 r.2 n

/-! ## Phase 4 — A3-Strom-Feinheit (Sub-Substanz J), EHRLICH OFFEN

**Dritte Doc-string-Pflicht (A3-Strom-Feinheit, Sub-Substanz J).** Die
A3-Vergröberung (Trito → Deutero → Proto) ist im endlichen Fall das
Block-Größen-Multiset. Im Strom mit unbeschränkter Kenogramm-Zahl wird die
Deutero-Projektion subtiler — „Block-Größen-Multiset" ist nicht mehr endlich.
**Quellen-positive Substanz** (Hermeneutes, S. 24): Günthers „Bereicherung des
Relationsgewebes" bei progressiver Kenogramm-Zahl stützt, dass die Schicht-*Form*
sich verfeinert, während die Schicht-*Zahl* drei bleibt (K-5).

**Bewohnbarkeits-Frage (EHRLICH OFFEN — keine scheinbare Schließung):** Trägt ein
Strom mit unbeschränkter Kenogramm-Zahl eine A2/A3-Differenzierung, die
nicht-trivial ist? Die folgende Sondierung *stellt* die Frage, schließt sie nicht:
sie definiert die Deutero-Block-Projektion und hält zwei Strom-Verhalten
illustrativ auseinander, **ohne** daraus einen Abschluss in eine der beiden
Richtungen (Zeuge / Kollaps) zu behaupten. Der Sondierungs-Befund (Sektion in der
Final-Notiz): die Nicht-Trivialität ist *strom-abhängig* — es gibt sowohl Ströme
mit unbeschränkter Kenogramm-Zahl und ausschließlich Singleton-Blöcken als auch
(strukturell) solche mit wachsenden Blöcken; die substantielle A2/A3-Frage für den
unbeschränkten Fall ist durch diese Illustrationen **nicht** entschieden und bleibt
als eigene Einheit offen (kein Konditionalitäts-Anker). -/

/-- A3-Deutero-Block-Projektion (Sondierung): der Deutero-Block einer Position ist
die — im Strom i. A. unendliche — Menge der Positionen mit demselben Wert. Das
Vergröberungs-Datum, das A3 von A2 (der Rang-Verfeinerung) trennen *könnte*. -/
def block (s : Stream' α) (n : ℕ) : Set ℕ := {k | s k = s n}

/-- Illustration (KEIN Abschluss der J-Frage): der Identitäts-Strom ist
kenogrammatisch (`IsRGSStream`) und hat unbeschränkte Kenogramm-Zahl. -/
example : IsRGSStream (fun n => n) := by
  refine ⟨rfl, fun n => ?_⟩
  show n + 1 ≤ (Finset.range (n + 1)).sup (fun i => i) + 1
  have hle : n ≤ (Finset.range (n + 1)).sup (fun i => i) :=
    Finset.le_sup (f := fun i => i) (Finset.mem_range.mpr (Nat.lt_succ_self n))
  omega

/-- Illustration (KEIN Abschluss der J-Frage): im Identitäts-Strom ist jeder
Deutero-Block ein Singleton — die A3-Vergröberung ist hier trivial. Dass *andere*
Ströme mit unbeschränkter Kenogramm-Zahl nicht-triviale Blöcke tragen, macht die
substantielle Frage strom-abhängig (offen, kein Kollaps-Beleg). -/
example : block (fun n => n) 3 = {3} := by
  ext k; simp [block]

/-! ## Axiom-Wachen (B2)

Die gemessenen Profile der 12 tragenden Deklarationen dieser Datei, eingefroren.
`firstOcc` und seine drei Spezifikations-Lemmata sind axiomfrei; ab `numDistinct`
zieht der Strom-Zweig `Classical.choice` ueber `Finset.image`/`Finset.range` — eine
konsumierte Mathlib-Quelle, keine Taktik dieser Datei (B1 §4.2). -/

/-- info: 'Reformulation.Kenogram.Stream.IsRGSStream' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IsRGSStream

/-- info: 'Reformulation.Kenogram.Stream.RGSStream' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RGSStream

/-- info: 'Reformulation.Kenogram.Stream.firstOcc' does not depend on any axioms -/
#guard_msgs in #print axioms firstOcc

/-- info: 'Reformulation.Kenogram.Stream.firstOcc_spec' does not depend on any axioms -/
#guard_msgs in #print axioms firstOcc_spec

/-- info: 'Reformulation.Kenogram.Stream.firstOcc_le_of_eq' does not depend on any axioms -/
#guard_msgs in #print axioms firstOcc_le_of_eq

/-- info: 'Reformulation.Kenogram.Stream.firstOcc_le' does not depend on any axioms -/
#guard_msgs in #print axioms firstOcc_le

/-- info: 'Reformulation.Kenogram.Stream.numDistinct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms numDistinct

/-- info: 'Reformulation.Kenogram.Stream.label' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms label

/-- info: 'Reformulation.Kenogram.Stream.relabelStream' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms relabelStream

/-- info: 'Reformulation.Kenogram.Stream.label_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms label_eq_iff

/-- info: 'Reformulation.Kenogram.Stream.relabelStream_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms relabelStream_eq_iff

/-- info: 'Reformulation.Kenogram.Stream.kenogram_no_reduction_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms kenogram_no_reduction_basis

end Reformulation.Kenogram.Stream
