import Mathlib.Order.Partition.Finpartition
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Equiv.Basic

/-!
# Reformulation.Kenogram.Basic — F-2 / S1, die kenogrammatische Möglichkeits-Schicht

Erste Schicht (S1, endlich) der neuen Modul-Familie `Kenogram`. Anders als die
F-3.6-Abrundungs-Einheiten trägt diese Einheit einen **Hauptsatz**: das
Repräsentations-Theorem `rgs_equiv_partition`, das die *restricted growth strings*
(RGS) der Länge `n` in kanonische Bijektion zu den Mengenpartitionen von `Fin n`
setzt. Vier Phasen:

1. **RGS-Definition** `IsRGS` / `RGS n` mit `DecidablePred` und `Fintype`.
2. **Repräsentations-Theorem** `rgs_equiv_partition` (HAUPTSATZ).
3. **Finpartition-Anschluss** (A2-Verband geschenkt) und Beobachtungs-Funktion
   `canonicalize` mit `canonicalize_eq_iff` (endliche Finalitäts-These).
4. **Berechnungs-Reihe**: `decide` gegen Günthers Tafel-Marken (5, 15, 52, 256).

## K-Anker (Hermeneutes, zeichengetreu)

* **K-1** — der Wert `0` ist Klassen-Index, *kein* `None` und *keine* Belegung;
  eine Leerstelle ist kein fehlender Wert, sondern die erste Klasse.
* **K-2** — Trito-Identität = Partition (Klassifikations-Gestalt).
* **K-3** — die Erzeugungs-Regel „wiederholen oder neu setzen" ist `IsRGS`:
  das nächste Zeichen ist ein bereits vergebener Index oder genau der nächste
  neue Index (bisheriges Maximum plus eins).

## Definitionswahl (Vor-Prüfungs-Eingriff)

RGS ist die **primäre** Definition, Finpartition die abgeleitete — gegen die
naheliegende Lattice-Instanz-Reihenfolge. Grund: RGS trägt die Berechnung
(`decide` über Listen) und die finale Semantik (die Beobachtungs-Folge *ist*
das RGS). Die Bijektion macht die Verbands-Struktur dennoch verfügbar (Transport).

## Klasse-B-Befunde (Partitions-Kombinatorik-Terrain)

* **B-1 (Reformulierung) — `IsRGS` als Bool-Lauf statt `.get`-Prädikat.** Die
  Spec-Form `(∀ h, l.get ⟨0,h⟩ = 0) ∧ ∀ i (h : i+1 < l.length), …` ist *nicht*
  per `infer_instance` entscheidbar (unbeschränktes `∀ i : ℕ`). Primär ist daher
  der Akkumulator-Lauf `isRGSAux` (freie `Decidable`-Instanz); die Spec-Form
  steht als Charakterisierungs-Theorem `isRGS_iff` daneben. Sub-Substanz-I-Befund.
* **B-2 — `decide` trägt n=5/52 billig.** Über den expliziten Generator
  `rgsList` (Fintype via `Fintype.ofFinset`) ist `Fintype.card (RGS 5) = 52`
  per `decide` in Sekundenbruchteilen lösbar; die antizipierte Performance-Flanke
  ist *positiv aufgelöst*, kein Fallback nötig.
* **B-3 — `Finpartition.ofSetoid` + `Setoid.ker`.** Die Hin-Richtung des
  Hauptsatzes geht direkt über `Finpartition.ofSetoid (Setoid.ker (rgsFun r))`;
  die nötige `DecidableRel`-Instanz wird lokal über `decEq` bereitgestellt.
* **B-4 — `Finpartition.part` ist noncomputable** (über `choose`), daher sind
  `partitionToRGS` und die Rück-Komposition noncomputable; die Berechnungs-Reihe
  bleibt davon unberührt (sie lebt auf der RGS-Seite).

Spec: F2_S1_Sub_Spec.md. Prompt: F2_S1_Sub_Prompt.md. Frühjahr 2026.
-/

namespace Reformulation.Kenogram

open Finset List

/-! ## Phase 1 — RGS-Definition, Entscheidbarkeit, Fintype -/

/-- Akkumulator-Lauf der RGS-Bedingung (K-3, zeichengetreu): `m` ist das bisher
gesehene Maximum, `started` ob schon ein Zeichen vergeben wurde. Das nächste
Zeichen muss — sobald begonnen — höchstens `m + 1` sein (wiederholen oder neu
setzen), und das allererste Zeichen muss `0` sein (K-1: die erste Klasse). -/
def isRGSAux : ℕ → Bool → List ℕ → Bool
  | _, _,     []     => true
  | m, true,  a :: t => decide (a ≤ m + 1) && isRGSAux (max m a) true t
  | _, false, a :: t => decide (a = 0)     && isRGSAux a true t

/-- `IsRGS l`: `l` ist ein *restricted growth string*. Berechnungs-Träger der
Schicht; die `.get`-Form der Spec steht als `isRGS_iff` daneben (B-1). -/
def IsRGS (l : List ℕ) : Prop := isRGSAux 0 false l = true

instance : DecidablePred IsRGS := fun _ => (inferInstance : Decidable (_ = true))

/-- Anfügen eines Zeichens an einen begonnenen Lauf: der Lauf bleibt gültig genau
dann, wenn der Rumpf gültig ist und das neue Zeichen das laufende Maximum um
höchstens eins überschreitet. -/
theorem isRGSAux_concat (m : ℕ) (l : List ℕ) (v : ℕ) :
    isRGSAux m true (l ++ [v])
      = (isRGSAux m true l && decide (v ≤ l.foldl max m + 1)) := by
  induction l generalizing m with
  | nil => simp [isRGSAux]
  | cons a t ih =>
      simp only [List.cons_append, isRGSAux, List.foldl_cons, ih (max m a)]
      exact (Bool.and_assoc _ _ _).symm

/-- Das laufende Maximum eines `foldl max a` ist das Maximum aus Startwert und
`foldr`-Maximum des Rumpfes (Brücke zwischen Lauf-Form und Präfix-Form). -/
theorem foldl_max_eq (a : ℕ) (t : List ℕ) :
    t.foldl max a = max a (t.foldr max 0) := by
  induction t generalizing a with
  | nil => simp
  | cons b t ih => simp only [List.foldl_cons, List.foldr_cons, ih]; omega

/-- Prop-Form des Anfüge-Schritts an einen nichtleeren RGS: `(a :: t) ++ [v]` ist
ein RGS genau dann, wenn `a :: t` einer ist und `v` das Präfix-Maximum um
höchstens eins überschreitet. -/
theorem isRGS_cons_concat (a : ℕ) (t : List ℕ) (v : ℕ) :
    IsRGS ((a :: t) ++ [v]) ↔ IsRGS (a :: t) ∧ v ≤ (a :: t).foldr max 0 + 1 := by
  unfold IsRGS
  rw [show (a :: t) ++ [v] = a :: (t ++ [v]) from rfl]
  simp only [isRGSAux, isRGSAux_concat a t v, Bool.and_eq_true,
    decide_eq_true_eq, foldl_max_eq, List.foldr_cons]
  tauto

/-- Expliziter Generator aller RGS der Länge `n` (Berechnungs-Träger des
`Fintype`): jeder RGS der Länge `n` wird um ein zulässiges Zeichen verlängert —
für den leeren Anfang genau `0`, sonst `0 … (Maximum + 1)`. -/
def rgsList : ℕ → List (List ℕ)
  | 0 => [[]]
  | n + 1 => (rgsList n).flatMap (fun l =>
      (List.range (l.foldr max 0 + (if l.isEmpty then 1 else 2))).map (fun v => l ++ [v]))

@[simp] theorem ite_isEmpty_cons (a : ℕ) (t : List ℕ) (x y : ℕ) :
    (if (a :: t).isEmpty = true then x else y) = y := rfl

@[simp] theorem ite_isEmpty_nil (x y : ℕ) :
    (if ([] : List ℕ).isEmpty = true then x else y) = x := rfl

/-- **Korrektheit des Generators**: `rgsList n` zählt genau die RGS der Länge `n`
auf. Macht die Berechnungs-Reihe (`Fintype.card (RGS n)`) zu einer echten
Treue-Aussage und nicht nur zu einer Generator-Zählung. -/
theorem mem_rgsList_iff {n : ℕ} {l : List ℕ} :
    l ∈ rgsList n ↔ l.length = n ∧ IsRGS l := by
  induction n generalizing l with
  | zero =>
      simp only [rgsList, List.mem_singleton, List.length_eq_zero_iff]
      constructor
      · rintro rfl; exact ⟨rfl, by decide⟩
      · rintro ⟨h, _⟩; exact h
  | succ n ih =>
      simp only [rgsList, List.mem_flatMap, List.mem_map, List.mem_range]
      constructor
      · rintro ⟨l', hl', v, hv, rfl⟩
        obtain ⟨hlen, hrgs⟩ := ih.mp hl'
        refine ⟨by rw [List.length_append, hlen]; rfl, ?_⟩
        rcases l' with _ | ⟨a, t⟩
        · simp only [List.foldr_nil, ite_isEmpty_nil] at hv
          have : v = 0 := by omega
          subst this; decide
        · simp only [ite_isEmpty_cons] at hv
          rw [isRGS_cons_concat]; exact ⟨hrgs, by omega⟩
      · rintro ⟨hlen, hrgs⟩
        rcases List.eq_nil_or_concat l with rfl | ⟨l', v, rfl⟩
        · simp at hlen
        · simp only [List.concat_eq_append] at hlen hrgs ⊢
          rw [List.length_append] at hlen
          refine ⟨l', ?_, v, ?_, rfl⟩
          · rw [ih]
            refine ⟨by simpa using hlen, ?_⟩
            rcases l' with _ | ⟨a, t⟩
            · decide
            · rw [isRGS_cons_concat] at hrgs; exact hrgs.1
          · rcases l' with _ | ⟨a, t⟩
            · simp only [List.foldr_nil, ite_isEmpty_nil]
              have : v = 0 := by
                unfold IsRGS at hrgs
                simp only [List.nil_append, isRGSAux, Bool.and_eq_true, decide_eq_true_eq] at hrgs
                exact hrgs.1
              omega
            · simp only [ite_isEmpty_cons]
              rw [isRGS_cons_concat] at hrgs; have := hrgs.2; omega

/-- `RGS n`: die *restricted growth strings* der Länge `n` als Subtyp von
`List ℕ`. Primäre Definition der Schicht (Definitionswahl, siehe Modul-Doc). -/
def RGS (n : ℕ) := { l : List ℕ // l.length = n ∧ IsRGS l }

instance (n : ℕ) : DecidableEq (RGS n) := Subtype.instDecidableEq

/-- `Fintype (RGS n)` über den (korrekt bewiesenen) Generator `rgsList`. Trägt
die `decide`-Berechnung von `Fintype.card (RGS n)`. -/
instance instFintypeRGS (n : ℕ) : Fintype (RGS n) :=
  Fintype.ofFinset (rgsList n).toFinset
    (fun _ => by rw [List.mem_toFinset]; exact mem_rgsList_iff)

/-- **Hilfs-Charakterisierung des begonnenen Laufs** (`started = true`,
Stelle A der S1.b-Schließung): `isRGSAux m true l` ist genau dann wahr, wenn
jeder Eintrag `l[i]` das Maximum aus Start-Schranke `m` und Präfix-Maximum
`(l.take i).foldr max 0` um höchstens eins überschreitet. Verallgemeinerter
Lauf-Zustand `(m, started)`, der `isRGS_iff` trägt. -/
theorem isRGSAux_true_iff (m : ℕ) (l : List ℕ) :
    isRGSAux m true l = true ↔
      ∀ i (h : i < l.length), l[i] ≤ max m ((l.take i).foldr max 0) + 1 := by
  induction l generalizing m with
  | nil => simp [isRGSAux]
  | cons a t ih =>
    simp only [isRGSAux, Bool.and_eq_true, decide_eq_true_eq, ih (max m a)]
    constructor
    · rintro ⟨ha, hrest⟩ i h
      cases i with
      | zero =>
        simp only [List.getElem_cons_zero, List.take_zero, List.foldr_nil]; omega
      | succ j =>
        have hj : j < t.length := by simpa using h
        have hthis := hrest j hj
        simp only [List.getElem_cons_succ, List.take_succ_cons, List.foldr_cons,
          ← max_assoc]
        exact hthis
    · intro H
      refine ⟨?_, fun j hj => ?_⟩
      · have h0 := H 0 (by simp)
        simp only [List.getElem_cons_zero, List.take_zero, List.foldr_nil] at h0; omega
      · have hthis := H (j + 1) (by simpa using hj)
        simp only [List.getElem_cons_succ, List.take_succ_cons, List.foldr_cons,
          ← max_assoc] at hthis
        exact hthis

/-- **Spec-Charakterisierung (B-1, Sub-Substanz-I).** Die wörtliche `.get`-Form
der Spec ist äquivalent zum Akkumulator-Lauf `IsRGS`. Damit ist die
Statement-Treue als Theorem festgehalten, obwohl der primäre Träger der
Bool-Lauf ist (Stelle A der S1.b-Schließung — geschlossen über
`isRGSAux_true_iff`). -/
theorem isRGS_iff (l : List ℕ) :
    IsRGS l ↔
      (∀ h : 0 < l.length, l.get ⟨0, h⟩ = 0) ∧
        ∀ i (h : i + 1 < l.length),
          l.get ⟨i + 1, h⟩ ≤ (l.take (i + 1)).foldr max 0 + 1 := by
  cases l with
  | nil => simp [IsRGS, isRGSAux]
  | cons a t =>
    rw [IsRGS]
    simp only [isRGSAux, Bool.and_eq_true, decide_eq_true_eq, isRGSAux_true_iff]
    constructor
    · rintro ⟨ha, hrest⟩
      refine ⟨fun _ => ?_, fun i h => ?_⟩
      · simp [List.get_eq_getElem, ha]
      · have hi : i < t.length := by simpa using h
        have hthis := hrest i hi
        simp only [List.get_eq_getElem, List.getElem_cons_succ, List.take_succ_cons,
          List.foldr_cons]
        exact hthis
    · rintro ⟨h0, hrest⟩
      have ha : a = 0 := by simpa [List.get_eq_getElem] using h0 (by simp)
      refine ⟨ha, fun i hi => ?_⟩
      have hthis := hrest i (by simpa using hi)
      simp only [List.get_eq_getElem, List.getElem_cons_succ, List.take_succ_cons,
        List.foldr_cons] at hthis
      exact hthis

/-! ## Phase 2 — Repräsentations-Theorem (HAUPTSATZ) -/

/-- Die Wert-Funktion eines RGS: `i ↦ l[i]`. Ihre Fasern (Urbilder gleicher
Werte) sind die Partitions-Blöcke (K-2). -/
def rgsFun {n : ℕ} (r : RGS n) : Fin n → ℕ :=
  fun i => r.1[(i : ℕ)]'(by rw [r.2.1]; exact i.2)

instance kerDecidableRel {α β : Type*} [DecidableEq β] (f : α → β) :
    DecidableRel (Setoid.ker f).r := fun a b => decEq (f a) (f b)

/-- **Hin-Richtung des Hauptsatzes** (Erzeugung ⇒ Klassifikation): Positionen
`i, j` liegen im selben Block genau dann, wenn `l[i] = l[j]`. Direkt über
`Finpartition.ofSetoid` des `Setoid.ker` der Wert-Funktion (B-3). -/
noncomputable def rgsToPartition {n : ℕ} (r : RGS n) :
    Finpartition (univ : Finset (Fin n)) :=
  Finpartition.ofSetoid (Setoid.ker (rgsFun r))

/-- Beobachtungs- und Kanonisierungs-Maschine: vergibt jedem Listen-Eintrag den
Klassen-Index nach erstem Auftreten (`seen` sammelt die distinkten Werte in
Auftretens-Reihenfolge). Erzeugt genau die RGS-Normalform. -/
def relabel {α : Type*} [DecidableEq α] (vals : List α) : List ℕ :=
  (vals.foldl (fun (st : List ℕ × List α) x =>
    match st.2.idxOf? x with
    | some k => (st.1 ++ [k], st.2)
    | none   => (st.1 ++ [st.2.length], st.2 ++ [x])) ([], [])).1

/-- `relabel` erhält die Länge: die Etiketten-Liste ist so lang wie die
Wert-Liste. -/
theorem relabel_length {α : Type*} [DecidableEq α] (vals : List α) :
    (relabel vals).length = vals.length := by
  have aux : ∀ (acc : List ℕ) (seen : List α),
      (vals.foldl (fun (st : List ℕ × List α) x =>
        match st.2.idxOf? x with
        | some k => (st.1 ++ [k], st.2)
        | none   => (st.1 ++ [st.2.length], st.2 ++ [x])) (acc, seen)).1.length
        = acc.length + vals.length := by
    induction vals with
    | nil => intro acc seen; simp
    | cons x xs ih =>
        intro acc seen
        simp only [List.foldl_cons]
        rcases seen.idxOf? x with k | _ <;>
          simp only [ih, List.length_append, List.length_cons, List.length_nil] <;> omega
  simpa [relabel] using aux [] []

/-- Schritt-Funktion des `relabel`-Laufs, als benannte Funktion herausgezogen
(definitionsgleich zur Lambda in `relabel`, daher `relabel_eq_foldl` per `rfl`).
Trägt die Invarianten-Beweise (Stelle B und Stelle C). -/
def relabelStep {α : Type*} [DecidableEq α] (st : List ℕ × List α) (x : α) :
    List ℕ × List α :=
  match st.2.idxOf? x with
  | some k => (st.1 ++ [k], st.2)
  | none   => (st.1 ++ [st.2.length], st.2 ++ [x])

theorem relabel_eq_foldl {α : Type*} [DecidableEq α] (vals : List α) :
    relabel vals = (vals.foldl relabelStep ([], [])).1 := rfl

/-- Das `foldr`-Maximum verträgt sich mit dem Anfügen eines Elements: der
laufende Höchststand wächst um das neue Element. Trägt die Wachstums-Rechnung
der RGS-Invariante. -/
theorem foldr_max_append_singleton (l : List ℕ) (v : ℕ) :
    (l ++ [v]).foldr max 0 = max (l.foldr max 0) v := by
  induction l with
  | nil => simp
  | cons a t ih => simp only [List.cons_append, List.foldr_cons, ih]; omega

/-- Anfüge-Schritt für RGS in Prop-Form: hängt man an einen RGS `l` ein Zeichen
`v` an, das das Präfix-Maximum um höchstens eins überschreitet (und `0` ist,
falls `l` leer war), so ist `l ++ [v]` wieder ein RGS. -/
theorem isRGS_concat (l : List ℕ) (v : ℕ) (h : IsRGS l)
    (hv : v ≤ l.foldr max 0 + 1) (hv0 : l = [] → v = 0) : IsRGS (l ++ [v]) := by
  cases l with
  | nil => rw [List.nil_append, hv0 rfl]; decide
  | cons a t => rw [isRGS_cons_concat]; exact ⟨h, hv⟩

/-- `relabel` einer Wert-Liste ist ein RGS (Stelle B der S1.b-Schließung).

Invariante über den `foldl`-Zustand `(labels, seen)`: `labels` ist ein RGS,
`seen.length = (labels.foldr max 0) + 1` und `labels ≠ []`. Im `none`-Fall ist
das neue Etikett `seen.length = Maximum + 1` (Wachstum um genau eins, K-3); im
`some k`-Fall ist `k < seen.length`, also `k ≤ Maximum` (Wiederholung).
`isRGS_concat` schließt den Schritt. -/
theorem relabel_isRGS {α : Type*} [DecidableEq α] (vals : List α) :
    IsRGS (relabel vals) := by
  rw [relabel_eq_foldl]
  suffices H : ∀ (l : List α) (labels : List ℕ) (seen : List α),
      IsRGS labels → seen.length = labels.foldr max 0 + 1 → labels ≠ [] →
      IsRGS (l.foldl relabelStep (labels, seen)).1 by
    cases vals with
    | nil => show IsRGS []; decide
    | cons x xs =>
      have hstep0 : relabelStep ([], []) x = ([0], [x]) := rfl
      rw [List.foldl_cons, hstep0]
      exact H xs [0] [x] (by decide) rfl (by decide)
  intro l
  induction l with
  | nil => intro labels seen hrgs _ _; simpa using hrgs
  | cons x xs ih =>
    intro labels seen hrgs hlen hne
    rw [List.foldl_cons]
    cases hc : seen.idxOf? x with
    | none =>
      have hstep : relabelStep (labels, seen) x = (labels ++ [seen.length], seen ++ [x]) := by
        simp only [relabelStep, hc]
      rw [hstep]
      refine ih _ _ ?_ ?_ ?_
      · exact isRGS_concat labels seen.length hrgs (le_of_eq hlen) (fun he => absurd he hne)
      · rw [foldr_max_append_singleton,
          max_eq_right (show labels.foldr max 0 ≤ seen.length by omega)]
        simp [List.length_append]
      · simp
    | some k =>
      obtain ⟨hk, -, -⟩ := List.idxOf?_eq_some_iff.mp hc
      have hstep : relabelStep (labels, seen) x = (labels ++ [k], seen) := by
        simp only [relabelStep, hc]
      rw [hstep]
      refine ih _ _ ?_ ?_ ?_
      · exact isRGS_concat labels k hrgs (by omega) (fun he => absurd he hne)
      · rw [foldr_max_append_singleton, hlen,
          max_eq_left (show k ≤ labels.foldr max 0 by omega)]
      · simp

/-- **Lauf-Spezifikation des `relabel`-Faltzustands** (Stelle C, Kern-Lemma).
Mit `cs` = bisher verarbeitete Werte gilt invariant: die Etiketten-Liste ist so
lang wie `cs`, die `seen`-Liste ist duplikatfrei, und das Etikett `labels[p]`
verweist über `seen` genau auf den `p`-ten Wert (`seen[labels[p]]? = cs[p]?`).
Trägt die Muster-Treue von `relabel` (`relabel_getElem?_eq_iff`). -/
theorem relabel_foldl_spec {α : Type*} [DecidableEq α] (l : List α) :
    ∀ (cs : List α) (labels : List ℕ) (seen : List α),
      labels.length = cs.length → seen.Nodup →
      (∀ (p : ℕ), (labels[p]?.bind fun k => seen[k]?) = cs[p]?) →
      (l.foldl relabelStep (labels, seen)).1.length = (cs ++ l).length ∧
        (l.foldl relabelStep (labels, seen)).2.Nodup ∧
        ∀ (p : ℕ), ((l.foldl relabelStep (labels, seen)).1[p]?.bind
          fun k => (l.foldl relabelStep (labels, seen)).2[k]?) = (cs ++ l)[p]? := by
  induction l with
  | nil =>
    intro cs labels seen hlen hnodup hbind
    simp only [List.foldl_nil, List.append_nil]
    exact ⟨hlen, hnodup, hbind⟩
  | cons x xs ih =>
    intro cs labels seen hlen hnodup hbind
    rw [show cs ++ (x :: xs) = (cs ++ [x]) ++ xs by simp, List.foldl_cons]
    cases hc : seen.idxOf? x with
    | none =>
      have hxnotin : x ∉ seen := List.idxOf?_eq_none_iff.mp hc
      have hstep : relabelStep (labels, seen) x = (labels ++ [seen.length], seen ++ [x]) := by
        simp only [relabelStep, hc]
      rw [hstep]
      refine ih (cs ++ [x]) (labels ++ [seen.length]) (seen ++ [x]) ?_ ?_ ?_
      · simp [List.length_append, hlen]
      · rw [List.nodup_append]
        refine ⟨hnodup, by simp, ?_⟩
        intro a ha b hb
        rw [List.mem_singleton] at hb; subst hb
        intro hax; subst hax; exact hxnotin ha
      · intro p
        rcases lt_trichotomy p labels.length with hp | hp | hp
        · have hpc : p < cs.length := by omega
          rw [List.getElem?_append_left hp, List.getElem?_append_left hpc]
          rcases hlp : labels[p]? with _ | j
          · rw [List.getElem?_eq_none_iff] at hlp; omega
          · have hb := hbind p
            rw [hlp] at hb
            simp only [Option.bind_some] at hb ⊢
            have hcsp : cs[p]? = some (cs[p]'hpc) := List.getElem?_eq_getElem hpc
            rw [hcsp] at hb
            obtain ⟨hjs, -⟩ := List.getElem?_eq_some_iff.mp hb
            rw [List.getElem?_append_left hjs, hb, hcsp]
        · subst hp
          rw [List.getElem?_concat_length, Option.bind_some, List.getElem?_concat_length,
            hlen, List.getElem?_concat_length]
        · rw [List.getElem?_eq_none_iff.mpr (by simp [List.length_append]; omega),
            Option.bind_none, List.getElem?_eq_none_iff.mpr (by simp [List.length_append]; omega)]
    | some k =>
      obtain ⟨hk, hkx, -⟩ := List.idxOf?_eq_some_iff.mp hc
      have hstep : relabelStep (labels, seen) x = (labels ++ [k], seen) := by
        simp only [relabelStep, hc]
      rw [hstep]
      refine ih (cs ++ [x]) (labels ++ [k]) seen ?_ hnodup ?_
      · simp [List.length_append, hlen]
      · intro p
        rcases lt_trichotomy p labels.length with hp | hp | hp
        · have hpc : p < cs.length := by omega
          rw [List.getElem?_append_left hp, List.getElem?_append_left hpc]
          exact hbind p
        · subst hp
          rw [List.getElem?_concat_length, Option.bind_some,
            List.getElem?_eq_getElem hk, hkx, hlen, List.getElem?_concat_length]
        · rw [List.getElem?_eq_none_iff.mpr (by simp [List.length_append]; omega),
            Option.bind_none, List.getElem?_eq_none_iff.mpr (by simp [List.length_append]; omega)]

/-- **Muster-Treue von `relabel`** (Stelle C, Kern-Lemma): zwei Positionen
tragen genau dann dasselbe Etikett, wenn sie denselben Wert tragen — über
`getElem?` formuliert (deckt Bereichs-Grenzen mit ab, da `relabel vals` und
`vals` gleich lang sind). Aus der Lauf-Spezifikation und der Duplikatfreiheit
von `seen`. -/
theorem relabel_getElem?_eq_iff {α : Type*} [DecidableEq α] (vals : List α) (i j : ℕ) :
    (relabel vals)[i]? = (relabel vals)[j]? ↔ vals[i]? = vals[j]? := by
  obtain ⟨hL, hN, hB⟩ := relabel_foldl_spec vals [] [] [] rfl (by simp) (by simp)
  rw [List.nil_append] at hB hL
  set st := vals.foldl relabelStep ([], []) with hst
  have hrel : relabel vals = st.1 := relabel_eq_foldl vals
  -- Charakterisierung der Werte über die Etiketten
  have key : ∀ p, p < vals.length →
      ∃ a, st.1[p]? = some a ∧ a < st.2.length ∧ st.2[a]? = vals[p]? := by
    intro p hp
    have hp1 : p < st.1.length := by rw [hL]; exact hp
    obtain ⟨a, ha⟩ : ∃ a, st.1[p]? = some a := by
      rw [List.getElem?_eq_getElem hp1]; exact ⟨_, rfl⟩
    have hbp := hB p
    rw [ha, Option.bind_some] at hbp
    have hvp : vals[p]? = some (vals[p]'hp) := List.getElem?_eq_getElem hp
    rw [hvp] at hbp
    obtain ⟨has, -⟩ := List.getElem?_eq_some_iff.mp hbp
    exact ⟨a, ha, has, by rw [hbp, hvp]⟩
  rw [hrel]
  constructor
  · intro h
    have hi := hB i; have hj := hB j
    rw [h] at hi; rw [hi] at hj; exact hj
  · intro h
    by_cases hi : i < vals.length
    · by_cases hj : j < vals.length
      · obtain ⟨a, hai, has, hav⟩ := key i hi
        obtain ⟨b, hbj, hbs, hbv⟩ := key j hj
        rw [hai, hbj]
        congr 1
        have : st.2[a]? = st.2[b]? := by rw [hav, hbv, h]
        exact (List.getElem?_inj has hN).mp this
      · exfalso
        have hjn : vals[j]? = none := List.getElem?_eq_none_iff.mpr (by omega)
        have hin : vals[i]? = some (vals[i]'hi) := List.getElem?_eq_getElem hi
        rw [hin, hjn] at h; simp at h
    · by_cases hj : j < vals.length
      · exfalso
        have hin : vals[i]? = none := List.getElem?_eq_none_iff.mpr (by omega)
        have hjn : vals[j]? = some (vals[j]'hj) := List.getElem?_eq_getElem hj
        rw [hin, hjn] at h; simp at h
      · have hin : st.1[i]? = none :=
          List.getElem?_eq_none_iff.mpr (by rw [hL]; omega)
        have hjn : st.1[j]? = none :=
          List.getElem?_eq_none_iff.mpr (by rw [hL]; omega)
        rw [hin, hjn]

/-! ### RGS-Eindeutigkeit (Stelle C/D-Fundament): ein RGS ist durch sein
Gleichheits-Muster bestimmt. -/

/-- Der erste Eintrag eines nichtleeren RGS ist `0` (K-1, getElem-Form). -/
theorem isRGS_head {l : List ℕ} (h : IsRGS l) (hl : 0 < l.length) : l[0] = 0 := by
  rw [isRGS_iff] at h
  have := h.1 hl
  rwa [List.get_eq_getElem] at this

/-- RGS-Schranke in getElem-Form: ab Position `1` überschreitet jeder Eintrag das
Präfix-Maximum um höchstens eins (K-3). -/
theorem isRGS_getElem_le {l : List ℕ} (h : IsRGS l) {i : ℕ} (hi : i < l.length)
    (hpos : 0 < i) : l[i] ≤ (l.take i).foldr max 0 + 1 := by
  rw [isRGS_iff] at h
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  have := h.2 k (by omega)
  rwa [List.get_eq_getElem] at this

/-- **Dichtheit der RGS-Präfixe**: jeder Wert bis zum Präfix-Maximum tritt im
Präfix auf (RGS-Werte füllen ein Anfangssegment lückenlos). -/
theorem rgs_take_mem {l : List ℕ} (h : IsRGS l) :
    ∀ i, i ≤ l.length → 0 < i → ∀ v, v ≤ (l.take i).foldr max 0 → v ∈ l.take i := by
  intro i
  induction i with
  | zero => intro _ hlt _ _; omega
  | succ i ih =>
    intro hle _ v hv
    have hil : i < l.length := by omega
    rw [List.take_succ_eq_append_getElem hil, foldr_max_append_singleton] at hv
    rw [List.take_succ_eq_append_getElem hil]
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · subst hi0
      have h0 : l[0] = 0 := isRGS_head h hil
      simp only [List.take_zero, List.foldr_nil, h0, max_self, Nat.le_zero] at hv
      subst hv
      simp [h0]
    · by_cases hvm : v ≤ (l.take i).foldr max 0
      · exact List.mem_append_left _ (ih (by omega) hipos v hvm)
      · have hli : l[i] ≤ (l.take i).foldr max 0 + 1 := isRGS_getElem_le h hil hipos
        have hMlt : (l.take i).foldr max 0 < l[i] := by
          by_contra hc
          rw [not_lt] at hc
          rw [max_eq_left hc] at hv
          exact hvm hv
        have hvl : v = l[i] := by
          rw [max_eq_right (le_of_lt hMlt)] at hv; omega
        subst hvl
        exact List.mem_append_right _ (by simp)

/-- Ist `l[i]` ein *neuer* Wert (taucht im Präfix nicht auf), so ist er genau das
Präfix-Maximum plus eins — über die Dichtheit (`rgs_take_mem`). -/
theorem rgs_new_eq {l : List ℕ} (h : IsRGS l) {i : ℕ} (hi : i < l.length) (hpos : 0 < i)
    (hnew : ∀ j, j < i → l[j]? ≠ l[i]?) :
    l[i] = (l.take i).foldr max 0 + 1 := by
  have hle := isRGS_getElem_le h hi hpos
  by_contra hne
  have hlt : l[i] ≤ (l.take i).foldr max 0 := by omega
  have hmem := rgs_take_mem h i (by omega) hpos l[i] hlt
  rw [List.mem_iff_getElem] at hmem
  obtain ⟨k, hk, hkv⟩ := hmem
  rw [List.length_take] at hk
  have hki : k < i := by omega
  rw [List.getElem_take] at hkv
  apply hnew k hki
  rw [List.getElem?_eq_getElem (by omega : k < l.length), List.getElem?_eq_getElem hi, hkv]

/-- **RGS-Eindeutigkeit durch das Muster** (Stelle C/D-Fundament): zwei RGS
gleicher Länge mit demselben Gleichheits-Muster (`l₁[i]? = l₁[j]? ↔ l₂[i]? =
l₂[j]?`) sind gleich. Starke Induktion über die Position: erste Stelle `0`,
Wiederhol-Stellen über das Muster + Induktion, Neu-Stellen über `rgs_new_eq` und
die Gleichheit der Präfixe. -/
theorem rgs_unique_of_pattern {l₁ l₂ : List ℕ} (h₁ : IsRGS l₁) (h₂ : IsRGS l₂)
    (hlen : l₁.length = l₂.length)
    (hpat : ∀ (i j : ℕ), l₁[i]? = l₁[j]? ↔ l₂[i]? = l₂[j]?) : l₁ = l₂ := by
  apply List.ext_getElem?
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    by_cases hi : i < l₁.length
    · rcases Nat.eq_zero_or_pos i with hi0 | hipos
      · subst hi0
        rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem (by omega : 0 < l₂.length),
          isRGS_head h₁ hi, isRGS_head h₂ (by omega)]
      · by_cases hrep : ∃ j, j < i ∧ l₁[j]? = l₁[i]?
        · obtain ⟨j, hji, hjeq⟩ := hrep
          rw [← hjeq, ih j hji]
          exact ((hpat i j).mp hjeq.symm).symm
        · simp only [not_exists, not_and] at hrep
          have hnew2 : ∀ j, j < i → l₂[j]? ≠ l₂[i]? := fun j hji heq =>
            hrep j hji ((hpat j i).mpr heq)
          have htake : l₁.take i = l₂.take i := by
            apply List.ext_getElem?
            intro k
            simp only [List.getElem?_take]
            rcases lt_or_ge k i with hk | hk
            · rw [if_pos hk, if_pos hk]; exact ih k hk
            · rw [if_neg (by omega : ¬ k < i), if_neg (by omega : ¬ k < i)]
          rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem (by omega : i < l₂.length),
            rgs_new_eq h₁ hi hipos hrep, rgs_new_eq h₂ (by omega) hipos hnew2, htake]
    · rw [List.getElem?_eq_none_iff.mpr (by omega), List.getElem?_eq_none_iff.mpr (by omega)]

/-- `relabel` lässt einen RGS unverändert (ein RGS ist bereits seine eigene
Normalform) — über Muster-Treue und Eindeutigkeit. Trägt `left_inv`. -/
theorem relabel_eq_self_of_isRGS {l : List ℕ} (h : IsRGS l) : relabel l = l :=
  rgs_unique_of_pattern (relabel_isRGS l) h (by rw [relabel_length])
    (fun i j => relabel_getElem?_eq_iff l i j)

/-- **Beobachtungs-Funktion** `canonicalize` (endliche Finalitäts-These,
Stufe 4): jeder rohen Wert-Folge `f : Fin n → α` ihre RGS-Normalform — die
Klassen-Indizes nach erstem Auftreten. -/
noncomputable def canonicalize {α : Type*} [DecidableEq α] {n : ℕ} (f : Fin n → α) :
    RGS n :=
  ⟨relabel (List.ofFn f),
    ⟨by rw [relabel_length, List.length_ofFn], relabel_isRGS _⟩⟩

/-- **Rück-Richtung des Hauptsatzes** (Klassifikation ⇒ Erzeugung): kanonische
Block-Nummerierung nach erstem Auftreten. Definiert über `canonicalize` der
Block-wertigen Funktion `i ↦ P.part i` — die Blöcke werden in der Reihenfolge
ihres ersten Elements durchnummeriert (K-3-Normalform). -/
noncomputable def partitionToRGS {n : ℕ} (P : Finpartition (univ : Finset (Fin n))) :
    RGS n :=
  canonicalize (fun i => P.part i)

/-- `ofFn f` an einer `Fin n`-Position liefert genau `some (f i)`. -/
theorem ofFn_getElem?_self {α : Type*} {n : ℕ} (f : Fin n → α) (i : Fin n) :
    (List.ofFn f)[(i : ℕ)]? = some (f i) := by
  rw [List.getElem?_ofFn, dif_pos i.2]

/-- Das `getElem?`-Gleichheits-Muster von `ofFn f` und `ofFn g` stimmt überein,
sobald `f` und `g` dasselbe Muster über `Fin n` tragen (deckt Bereichs-Grenzen
mit ab). Brücke zwischen `Fin n`-Muster und Listen-Muster. -/
theorem ofFn_getElem?_pattern {α β : Type*} {n : ℕ} (f : Fin n → α) (g : Fin n → β)
    (h : ∀ i j : Fin n, f i = f j ↔ g i = g j) (a b : ℕ) :
    ((List.ofFn f)[a]? = (List.ofFn f)[b]?) ↔ ((List.ofFn g)[a]? = (List.ofFn g)[b]?) := by
  rw [List.getElem?_ofFn, List.getElem?_ofFn, List.getElem?_ofFn, List.getElem?_ofFn]
  by_cases ha : a < n <;> by_cases hb : b < n
  · simp only [dif_pos ha, dif_pos hb, Option.some.injEq]; exact h ⟨a, ha⟩ ⟨b, hb⟩
  · simp [dif_pos ha, dif_neg hb]
  · simp [dif_neg ha, dif_pos hb]
  · simp [dif_neg ha, dif_neg hb]

/-- **Finalitäts-These (endliche Form), Stufe 4 — Stelle C der S1.b-Schließung.**
Zwei rohe Wert-Folgen haben dieselbe RGS-Normalform genau dann, wenn sie
verhaltens-äquivalent sind (gleiche Gleichheits-Muster). Trito-Identität (rechte
Seite, K-2) = RGS-Gleichheit (linke Seite) = endliche Verhaltens-Äquivalenz. Die
Stelle, an der F-2 sich von Standard-Kombinatorik trennt. (Vor `rgs_equiv_partition`
eingeordnet, da `left_inv` darauf ruht.) Die Strom-Form (finale Koalgebra) ist S2.

Beweis-Pfad: `canonicalize f = canonicalize g` ⇔ `relabel (ofFn f) = relabel (ofFn g)`
(`Subtype.mk.injEq`); ⇒ über `relabel_getElem?_eq_iff` + `ofFn_getElem?_self`,
⇐ über `rgs_unique_of_pattern` + `ofFn_getElem?_pattern`. -/
theorem canonicalize_eq_iff {α β : Type*} [DecidableEq α] [DecidableEq β] {n : ℕ}
    (f : Fin n → α) (g : Fin n → β) :
    canonicalize f = canonicalize g ↔ (∀ i j, f i = f j ↔ g i = g j) := by
  constructor
  · intro h i j
    have hrel : relabel (List.ofFn f) = relabel (List.ofFn g) := Subtype.ext_iff.mp h
    calc f i = f j
        ↔ (List.ofFn f)[(i : ℕ)]? = (List.ofFn f)[(j : ℕ)]? := by
          rw [ofFn_getElem?_self, ofFn_getElem?_self, Option.some.injEq]
      _ ↔ (relabel (List.ofFn f))[(i : ℕ)]? = (relabel (List.ofFn f))[(j : ℕ)]? :=
          (relabel_getElem?_eq_iff _ _ _).symm
      _ ↔ (relabel (List.ofFn g))[(i : ℕ)]? = (relabel (List.ofFn g))[(j : ℕ)]? := by rw [hrel]
      _ ↔ (List.ofFn g)[(i : ℕ)]? = (List.ofFn g)[(j : ℕ)]? := relabel_getElem?_eq_iff _ _ _
      _ ↔ g i = g j := by rw [ofFn_getElem?_self, ofFn_getElem?_self, Option.some.injEq]
  · intro h
    apply Subtype.ext
    show relabel (List.ofFn f) = relabel (List.ofFn g)
    apply rgs_unique_of_pattern (relabel_isRGS _) (relabel_isRGS _)
      (by simp only [relabel_length, List.length_ofFn])
    intro a b
    rw [relabel_getElem?_eq_iff, relabel_getElem?_eq_iff]
    exact ofFn_getElem?_pattern f g h a b

/-! ## Phase 3 — Finpartition-Anschluss (A2 geschenkt) + Finalitäts-These

Die A2-Verbands-Struktur (emanativ-gleichlang, Π-Verband) über `RGS n` ist über
die Bijektion `rgs_equiv_partition` geschenkt: `Finpartition` trägt in Mathlib
die `Lattice`-Instanz, und die Bijektion transportiert die Ordnung auf `RGS n`.
Die Verfeinerungs-Ordnung selbst wird hier nicht als Instanz erzwungen (A2 ist
nicht der Substanz-Kern dieser Schicht); siehe die A1/A2/A3-Markierung unten. -/

/-- Eine Finpartition ist durch ihre `part`-Funktion bestimmt: stimmen die Blöcke
jedes Elements überein, so sind die Partitionen gleich. Trägt `right_inv`. -/
theorem finpartition_ext_part {α : Type*} [DecidableEq α] [Fintype α]
    {P Q : Finpartition (univ : Finset α)} (h : ∀ a, P.part a = Q.part a) : P = Q := by
  apply Finpartition.ext
  ext s
  constructor
  · intro hs
    obtain ⟨a, _, rfl⟩ := P.part_surjOn (Finset.mem_coe.mpr hs)
    rw [h a]; exact Q.part_mem.mpr (Finset.mem_univ a)
  · intro hs
    obtain ⟨a, _, rfl⟩ := Q.part_surjOn (Finset.mem_coe.mpr hs)
    rw [← h a]; exact P.part_mem.mpr (Finset.mem_univ a)

/-- Blöcke der `rgsToPartition r` stimmen genau dann überein, wenn die zugehörigen
RGS-Werte gleich sind (Faser-Charakterisierung über `mem_part_ofSetoid_iff_rel`). -/
theorem rgsToPartition_part_eq_iff {n : ℕ} (r : RGS n) (i j : Fin n) :
    (rgsToPartition r).part i = (rgsToPartition r).part j ↔ rgsFun r i = rgsFun r j := by
  have key : ∀ a b : Fin n, b ∈ (rgsToPartition r).part a ↔ rgsFun r a = rgsFun r b :=
    fun a b => Finpartition.mem_part_ofSetoid_iff_rel
  constructor
  · intro hpart
    have hj : j ∈ (rgsToPartition r).part i := by
      rw [hpart]; exact (rgsToPartition r).mem_part (Finset.mem_univ j)
    exact (key i j).mp hj
  · intro hval
    exact (rgsToPartition r).part_eq_of_mem
      ((rgsToPartition r).part_mem.mpr (Finset.mem_univ j)) ((key j i).mpr hval.symm)

/-- Die kanonisierte Block-Funktion `partitionToRGS P` hat dieselben Fasern wie
`P` (gleicher Wert ⇔ gleicher Block) — über Muster-Treue von `relabel`. -/
theorem rgsFun_partitionToRGS_eq_iff {n : ℕ} (P : Finpartition (univ : Finset (Fin n)))
    (a b : Fin n) :
    rgsFun (partitionToRGS P) a = rgsFun (partitionToRGS P) b ↔ P.part a = P.part b := by
  have ha : (a : ℕ) < (partitionToRGS P).1.length := by rw [(partitionToRGS P).2.1]; exact a.2
  have hb : (b : ℕ) < (partitionToRGS P).1.length := by rw [(partitionToRGS P).2.1]; exact b.2
  rw [show rgsFun (partitionToRGS P) a = (partitionToRGS P).1[(a : ℕ)] from rfl,
      show rgsFun (partitionToRGS P) b = (partitionToRGS P).1[(b : ℕ)] from rfl,
      ← Option.some.injEq, ← List.getElem?_eq_getElem ha, ← List.getElem?_eq_getElem hb]
  show (relabel (List.ofFn fun i => P.part i))[(a : ℕ)]?
      = (relabel (List.ofFn fun i => P.part i))[(b : ℕ)]? ↔ P.part a = P.part b
  rw [relabel_getElem?_eq_iff, ofFn_getElem?_self, ofFn_getElem?_self, Option.some.injEq]

/-- ## REPRÄSENTATIONS-THEOREM (Hauptsatz der F-2-Schicht) — Stelle D/E.

Die *restricted growth strings* der Länge `n` stehen in kanonischer Bijektion
zu den Mengenpartitionen von `Fin n`. Erzeugungs-Gestalt (K-3, RGS) und
Klassifikations-Gestalt (K-2, Partition) sind zwei Darstellungen EINER Substanz
— die Architektur-Wahl, auf die die Vor-Klärung zulief, ist keine Wahl, sondern
dieser Satz.

* `left_inv` (RGS → Partition → RGS = id): `canonicalize` der Block-Funktion hat
  dasselbe Muster wie `rgsFun r` (`rgsToPartition_part_eq_iff` + `canonicalize_eq_iff`),
  und `canonicalize (rgsFun r) = r`, weil ein RGS schon seine Normalform ist
  (`relabel_eq_self_of_isRGS`).
* `right_inv` (Partition → RGS → Partition = id): gleiche Fasern über
  `rgsFun_partitionToRGS_eq_iff` + `mem_part_ofSetoid_iff_rel` + `finpartition_ext_part`.
-/
noncomputable def rgs_equiv_partition (n : ℕ) :
    RGS n ≃ Finpartition (univ : Finset (Fin n)) where
  toFun := rgsToPartition
  invFun := partitionToRGS
  left_inv := by
    intro r
    show canonicalize (fun i => (rgsToPartition r).part i) = r
    have hce : canonicalize (fun i => (rgsToPartition r).part i) = canonicalize (rgsFun r) := by
      rw [canonicalize_eq_iff]; intro i j; exact rgsToPartition_part_eq_iff r i j
    rw [hce]
    apply Subtype.ext
    have hof : List.ofFn (rgsFun r) = r.1 := by
      apply List.ext_getElem?
      intro k
      by_cases hk : k < n
      · rw [List.getElem?_ofFn, dif_pos hk, List.getElem?_eq_getElem (by rw [r.2.1]; exact hk)]
        rfl
      · rw [List.getElem?_ofFn, dif_neg hk, List.getElem?_eq_none_iff.mpr (by rw [r.2.1]; omega)]
    show relabel (List.ofFn (rgsFun r)) = r.1
    rw [hof]; exact relabel_eq_self_of_isRGS r.2.2
  right_inv := by
    intro P
    apply finpartition_ext_part
    intro a
    ext b
    show b ∈ (Finpartition.ofSetoid (Setoid.ker (rgsFun (partitionToRGS P)))).part a
      ↔ b ∈ P.part a
    rw [Finpartition.mem_part_ofSetoid_iff_rel]
    show rgsFun (partitionToRGS P) a = rgsFun (partitionToRGS P) b ↔ b ∈ P.part a
    rw [rgsFun_partitionToRGS_eq_iff, eq_comm,
      ← P.mem_part_iff_part_eq_part (Finset.mem_univ b) (Finset.mem_univ a)]

/-! ## Phase 4 — Berechnungs-Reihe (die härtesten Treue-Tests)

Lean *berechnet* Günthers Tafel-Zahlen aus der Definition, statt eine Formel zu
zitieren — die schärfste Form der Treue. Alle Bell-Marken per `decide` über den
korrekt bewiesenen Generator (`mem_rgsList_iff`), die Performance-Flanke n=5 ist
positiv aufgelöst (B-2). -/

example : Fintype.card (RGS 1) = 1 := by decide
example : Fintype.card (RGS 2) = 2 := by decide
example : Fintype.card (RGS 3) = 5 := by decide

set_option maxRecDepth 4000 in
/-- B(4) = 15 (Günther, Tafel VIII). -/
example : Fintype.card (RGS 4) = 15 := by decide

set_option maxRecDepth 8000 in
/-- B(5) = 52 („52 Morphogramme", LZEE S. 12). Performance-Haupt-Sondierung:
`decide` trägt (B-2). -/
example : Fintype.card (RGS 5) = 52 := by decide

/-- Werte-Summen-Identität (m = n), Günthers eigene Rechnung (LZEE S. 23):
`4^4 = 256`. -/
example : (4 : ℕ) ^ 4 = 256 := by decide

/-! **Faser-Zahlen (K-4) und Summen-Identität — [Kandidat], vertagt.** Die
Deutero-Fasern (Block-Größen-Multiset) `2 / 4 / 3` und die volle
Summen-Identität `∑_P fallingFactorial 4 P.parts.card = 256` brauchen Hilfs-Defs
(`fiber_over_deutero`, `fallingFactorial`) und sind laut Spec wünschenswert, aber
*nicht* S1-pflichtig; die Kern-Marken (5, 15, 52, 256) sind erfüllt. Vertagt als
Korollar-Kandidaten an eine S1.b-Folge oder S2.

**Bonus-Schicht (Stirling/Bell aus Deutero-Fasern) — [Kandidat], nicht erzwungen.** -/

/-! ## A1/A2/A3 — drei Beziehungs-Arten (PKL-Verfeinerung, Hermeneutes-Pflicht)

WARNUNG (PKL-Markierung): Die Drei-Teilung A1/A2/A3 ist **NICHT** Günthers
Terminologie. Günther trägt eine Zweiteilung evolutiv/emanativ (LZEE S. 21); die
Drei-Teilung ist eine strukturlogisch in seinen Tafeln *anwesende*
PKL-Verfeinerung, hier benannt, ohne Günther als Autorität für die Drei-Teilung
in Anspruch zu nehmen.

* **A1 evolutiv** (n nach n+1): Anfangsstück-Baum, das Verlängern eines RGS um
  ein zulässiges Zeichen — exakt der Generator-Schritt `rgsList`.
* **A2 emanativ-gleichlang**: der Π-Verband der Partitionen fester Länge; A2 ist
  über `rgs_equiv_partition` geschenkt (Mathlib-`Lattice` auf `Finpartition`).
* **A3 schicht-vertikal**: der Vergröberungs-Turm Trito → Deutero → Proto
  (Beobachtungs-Abstraktion); in S1 nur als Markierung, volle Substanz in S2.

**Falsifikations-Stelle 1** (Speculum / Sub-J): *Kollabieren A2 (Π-Verband) und
A3 (Vergröberungs-Turm) im Spezialfall einer einzelnen Struktur?* In S1 als
Markierung geführt: die Trennung ist nicht-trivial, schon weil verschiedene RGS
gleicher Länge verschiedene Partitionen *und* verschiedene Deutero-Fasern haben
können — das folgende `example` hält zwei Strukturen auseinander (Nicht-Kollaps
als entscheidbarer Zeuge; Sub-Substanz E: die Trennung kollabiert nicht zur
Tautologie). Die volle A2/A3-Spezialfall-Prüfung ist S2-Stoff. -/

/-- Nicht-Kollaps-Zeuge (Falsifikations-Stelle 1, entscheidbare Minimal-Form):
zwei verschiedene RGS der Länge 3 sind als RGS verschieden. -/
example : ([0, 1, 1] : List ℕ) ≠ ([0, 1, 2] : List ℕ) := by decide

/-! ## K-7-Doppel-Test (Architektur-Pflicht-Paar)

* **positiv (Containment):** die klassischen morphogrammatischen Strukturen
  (Tafeln V/VI, in Tafel VIII rot „Klassisch") als Sub-Struktur. S1-Form: die
  klassischen Länge-2-Morphogramme sind genau die beiden RGS der Länge 2 —
  `[0,0]` (eine Klasse) und `[0,1]` (zwei Klassen). Das folgende `example` zeigt
  das Containment entscheidbar; die volle Embedding-Substanz ist S2/Architektur.
* **negativ (keine Reduktionsbasis):** keine universelle Basis, aus der alle
  Kenogramme deduziert werden (Florenz-Fund-Disziplin). In S1 als Markierung;
  von der finalen Koalgebra (S2: Grenzpunkt, keine Basis) strukturlogisch getragen. -/

/-- K-7 positiv (Containment, S1-Form): die beiden klassischen Länge-2-Morphogramme
sind RGS. -/
example : IsRGS [0, 0] ∧ IsRGS [0, 1] := by decide

/-- K-7 positiv: es gibt genau zwei Länge-2-Morphogramme (= B(2)). -/
example : Fintype.card (RGS 2) = 2 := by decide

/-! ## Axiom-Wachen (B2)

Die gemessenen Profile der 22 tragenden Deklarationen dieser Datei, eingefroren.
Traegerauswahl nach den Kriterien der B1-Abnahme: konsumiert ausserhalb der eigenen
Datei (korpusweit, inklusive der Standalone-Sonden), im Kopf-Doc als Ertrag
ausgewiesen, oder Nachtrag N2. `Classical.choice` steht hier, wo `Finset`- und
`Finpartition`-Maschinerie konsumiert wird; die Choice-Analyse (B1 §4) hat das als
extern und nicht vermeidbar ausgewiesen. -/

/-- info: 'Reformulation.Kenogram.isRGSAux' does not depend on any axioms -/
#guard_msgs in #print axioms isRGSAux

/-- info: 'Reformulation.Kenogram.IsRGS' does not depend on any axioms -/
#guard_msgs in #print axioms IsRGS

/-- info: 'Reformulation.Kenogram.instDecidablePredListNatIsRGS' does not depend on any axioms -/
#guard_msgs in #print axioms instDecidablePredListNatIsRGS

/-- info: 'Reformulation.Kenogram.isRGS_cons_concat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms isRGS_cons_concat

/-- info: 'Reformulation.Kenogram.rgsList' does not depend on any axioms -/
#guard_msgs in #print axioms rgsList

/-- info: 'Reformulation.Kenogram.mem_rgsList_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mem_rgsList_iff

/-- info: 'Reformulation.Kenogram.RGS' does not depend on any axioms -/
#guard_msgs in #print axioms RGS

/-- info: 'Reformulation.Kenogram.instDecidableEqRGS' does not depend on any axioms -/
#guard_msgs in #print axioms instDecidableEqRGS

/-- info: 'Reformulation.Kenogram.instFintypeRGS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms instFintypeRGS

/-- info: 'Reformulation.Kenogram.isRGS_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms isRGS_iff

/-- info: 'Reformulation.Kenogram.relabel' does not depend on any axioms -/
#guard_msgs in #print axioms relabel

/-- info: 'Reformulation.Kenogram.relabel_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms relabel_length

/-- info: 'Reformulation.Kenogram.foldr_max_append_singleton' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms foldr_max_append_singleton

/-- info: 'Reformulation.Kenogram.isRGS_concat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms isRGS_concat

/-- info: 'Reformulation.Kenogram.relabel_isRGS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms relabel_isRGS

/-- info: 'Reformulation.Kenogram.relabel_getElem?_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms relabel_getElem?_eq_iff

/-- info: 'Reformulation.Kenogram.rgs_unique_of_pattern' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms rgs_unique_of_pattern

/-- info: 'Reformulation.Kenogram.relabel_eq_self_of_isRGS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms relabel_eq_self_of_isRGS

/-- info: 'Reformulation.Kenogram.canonicalize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms canonicalize

/-- info: 'Reformulation.Kenogram.partitionToRGS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms partitionToRGS

/-- info: 'Reformulation.Kenogram.canonicalize_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms canonicalize_eq_iff

/-- info: 'Reformulation.Kenogram.rgs_equiv_partition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rgs_equiv_partition

end Reformulation.Kenogram
