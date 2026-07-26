import Reformulation.Kenogram.Basic
import Reformulation.Kenogram.Stream

/-!
# Reformulation.Kenogram.Bridge — F-2 / S2b, die S1↔S2-Brücke

Dritte Schicht der Modul-Familie `Kenogram` und **die erste Datei, die beide
Vorgänger importiert UND benutzt** — `Basic` (S1, endlich) und `Stream` (S2,
unbeschränkt). Sie löst die in der S2-Bewertung (II.3) am Code aufgedeckte Naht:
`Stream.lean` nutzt kein `Basic.lean`-Lemma, S1 und S2 sind parallel
re-implementiert, und dass `label` (S2) und `relabel` (S1) dieselbe Normalform
berechnen, war *Inspektions-Urteil*. S2b macht es zum **Theorem**.

## Die Brücken-Aussage — Restriktions-Verträglichkeit, nicht Gleichheit

Die naive Brücke („`label` = `relabel`") ist typ-falsch: `canonicalize` (S1)
bildet `Fin n → α` auf `RGS n` ab, `relabelStream` (S2) bildet `Stream' α` auf
`RGSStream` ab — verschiedene Definitionsbereiche. Die richtige, substantiellere
Aussage ist die **Präfix-Restriktions-Verträglichkeit:**

> *Das n-Präfix der Strom-Normalform ist die endliche Normalform des n-Präfixes.*

Formal `relabelStream_take_eq_canonicalize` (Bündel-Form, der Hauptsatz):
`(relabelStream s).val.take n = (canonicalize (fun i : Fin n => s i.val)).val`,
und punktweise `relabelStream_restrict_canonicalize`. **S2 restringiert auf S1** —
also ist S2 die Verallgemeinerung von S1, maschinell statt per Inspektion
(Anschnitt/Grenzpunkt-Lesart als Theorem).

## Beweis-Architektur

Beide Normalformen sind **präfix-determiniert** (der Rang an Position `i` hängt nur
von `{s j : j ≤ i}` ab). Die Brücke geht *nicht* über eine Induktion mit
Lokalitäts-Lemmata, sondern direkt über die gemeinsame Muster-Charakterisierung:
beide Listen sind RGS gleicher Länge mit demselben Gleichheits-Muster (auf dem
gemeinsamen Präfix `s a = s b`), also gleich via `rgs_unique_of_pattern` (S1).
Tragende S1-Bausteine (Basic-Kopplung): `relabel_getElem?_eq_iff`,
`rgs_unique_of_pattern`, `relabel_isRGS`, `relabel_length`, `isRGS_concat`,
`foldr_max_append_singleton`. Tragende S2-Bausteine: `label_eq_iff`,
`isRGSStream_label`.

Spec: F2_S2b_Sub_Spec.md. Prompt: F2_S2b_Sub_Prompt.md. Frühjahr 2026.
-/

namespace Reformulation.Kenogram.Bridge

open Reformulation.Kenogram
open Reformulation.Kenogram.Stream

variable {α : Type*} [DecidableEq α]

/-! ## Hilfs-Brücken: Präfix-Maximum als `Finset.sup`, und Reflexion von
`IsRGSStream` auf `IsRGS` des Präfixes (beide nutzen Basic-Lemmata). -/

/-- Brücke zwischen der `Finset.sup`-Form (S2 `IsRGSStream`) und der
`List.foldr max`-Form (S1 `IsRGS`): das Präfix-Maximum stimmt überein. Nutzt
`foldr_max_append_singleton` aus `Basic` (S1). -/
theorem sup_range_eq_foldr_take (t : Stream' ℕ) (n : ℕ) :
    (Finset.range n).sup (fun i => t.get i) = (t.take n).foldr max 0 := by
  induction n with
  | zero => simp [Stream'.take_zero]
  | succ n ih =>
    rw [Finset.range_add_one, Finset.sup_insert, Stream'.take_succ',
      foldr_max_append_singleton, ih]
    exact max_comm _ _

/-- **Reflexion** der Wohlgeformtheit: das n-Präfix eines kenogrammatischen Stroms
ist ein endlicher RGS. Nutzt `isRGS_concat` aus `Basic` (S1) und die
Präfix-Maximum-Brücke. -/
theorem isRGSStream_take (t : Stream' ℕ) (ht : IsRGSStream t) (n : ℕ) :
    IsRGS (t.take n) := by
  induction n with
  | zero => show IsRGS []; decide
  | succ n ih =>
    rw [Stream'.take_succ']
    refine isRGS_concat (t.take n) (t.get n) ih ?_ ?_
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [Stream'.take_zero, ht.1]
      · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        have hgrow := ht.2 m
        rwa [sup_range_eq_foldr_take] at hgrow
    · intro he
      have hlen := Stream'.length_take n t
      rw [he, List.length_nil] at hlen
      subst hlen
      exact ht.1

/-! ## Phase 1 — Präfix-Lokalität (die S2-Seite)

`label_prefix_local` ist die S2-seitige Präfix-Determiniertheit. Die S1-seitige
(`relabel`) ist für die hier gewählte Beweis-Architektur (Muster + Eindeutigkeit
statt Induktion-mit-Lokalität) **nicht load-bearing** — siehe Register-Befund in
der Final-Notiz; die Brücke kommt ohne sie aus. -/

/-- **Präfix-Lokalität von `label` (S2).** Der Rang an Position `n` hängt nur von
den Werten bis `n` ab: stimmen zwei Ströme auf `[0, n]` überein, so stimmen ihre
Ränge an `n` überein. Aus der `label`-Definition: `firstOcc s n ≤ n`, und sowohl
`firstOcc` als auch `numDistinct` des Präfixes lesen nur Werte `≤ n`. -/
theorem label_prefix_local (s t : Stream' α) (n : ℕ)
    (h : ∀ i, i ≤ n → s i = t i) : label s n = label t n := by
  have hfo : firstOcc s n = firstOcc t n := by
    apply le_antisymm
    · refine firstOcc_le_of_eq s ?_
      have hle : firstOcc t n ≤ n := firstOcc_le t n
      rw [h _ hle, firstOcc_spec t n, ← h n (le_refl n)]
    · refine firstOcc_le_of_eq t ?_
      have hle : firstOcc s n ≤ n := firstOcc_le s n
      rw [← h _ hle, firstOcc_spec s n, h n (le_refl n)]
  rw [label, label, hfo, numDistinct, numDistinct]
  congr 1
  apply Finset.image_congr
  intro i hi
  rw [Finset.mem_coe, Finset.mem_range] at hi
  exact h i (le_of_lt (lt_of_lt_of_le hi (firstOcc_le t n)))

/-! ## Phase 2 — die Brücke (HAUPTSATZ)

Die `getElem?`-Auswertung beider Präfix-Listen, dann `rgs_unique_of_pattern`. -/

/-- `getElem?` des n-Präfixes der Strom-Normalform. -/
theorem take_label_getElem? (s : Stream' α) (n a : ℕ) :
    ((relabelStream s).val.take n)[a]? = if a < n then some (label s a) else none := by
  by_cases h : a < n
  · rw [if_pos h, Stream'.getElem?_take h]; rfl
  · rw [if_neg h, List.getElem?_eq_none_iff.mpr (by rw [Stream'.length_take]; omega)]

omit [DecidableEq α] in
/-- `getElem?` des n-Präfixes eines rohen Stroms. -/
theorem take_val_getElem? (s : Stream' α) (n a : ℕ) :
    (s.take n)[a]? = if a < n then some (s a) else none := by
  by_cases h : a < n
  · rw [if_pos h, Stream'.getElem?_take h]; rfl
  · rw [if_neg h, List.getElem?_eq_none_iff.mpr (by rw [Stream'.length_take]; omega)]

omit [DecidableEq α] in
/-- Das n-Präfix eines rohen Stroms ist `List.ofFn` der `Fin n`-Restriktion —
die Identifikation `Stream'`-Präfix ↔ `Fin n`-Funktion. -/
theorem take_eq_ofFn (s : Stream' α) (n : ℕ) :
    s.take n = List.ofFn (fun i : Fin n => s i.val) := by
  apply List.ext_getElem?
  intro a
  rw [take_val_getElem? s n a, List.getElem?_ofFn]
  by_cases h : a < n
  · rw [if_pos h, dif_pos h]
  · rw [if_neg h, dif_neg h]

/-- **S1↔S2-BRÜCKE (Bündel-Form, Restriktions-Verträglichkeit).** Das n-Präfix der
Strom-Normalform `relabelStream s` ist die endliche Normalform `relabel` des
n-Präfixes `s.take n`. Bewiesen über `rgs_unique_of_pattern` (S1): beide Listen
sind RGS gleicher Länge mit demselben Gleichheits-Muster. -/
theorem relabelStream_take_eq_relabel (s : Stream' α) (n : ℕ) :
    (relabelStream s).val.take n = relabel (s.take n) := by
  apply rgs_unique_of_pattern
  · exact isRGSStream_take (relabelStream s).val (relabelStream s).property n
  · exact relabel_isRGS (s.take n)
  · rw [Stream'.length_take, relabel_length, Stream'.length_take]
  · intro a b
    rw [relabel_getElem?_eq_iff, take_label_getElem? s n a, take_label_getElem? s n b,
      take_val_getElem? s n a, take_val_getElem? s n b]
    by_cases ha : a < n <;> by_cases hb : b < n <;> simp [ha, hb, label_eq_iff]

/-- **S1↔S2-BRÜCKE (canonicalize-Form, der Hauptsatz).** Das n-Präfix der
Strom-Normalform ist die `canonicalize`-Normalform der `Fin n`-Restriktion. Die
maschinelle Einlösung der „Verallgemeinerung": die endliche kenogrammatische
Schicht ist der Anschnitt der Strom-Schicht (Anschnitt/Grenzpunkt, Horistês'
S2-VK-Rahmung), als Theorem. -/
theorem relabelStream_take_eq_canonicalize (s : Stream' α) (n : ℕ) :
    (relabelStream s).val.take n = (canonicalize (fun i : Fin n => s i.val)).val := by
  rw [relabelStream_take_eq_relabel, take_eq_ofFn]
  rfl

/-- **Punktweise Brücke** (Konditionalitäts-Anker): an jeder Präfix-Position `i < n`
liefert die endliche Normalform genau den Strom-Rang `label s i`. -/
theorem relabelStream_restrict_canonicalize (s : Stream' α) (n : ℕ) (i : Fin n) :
    (canonicalize (fun j : Fin n => s j.val)).val[i.val]? = some (label s i.val) := by
  rw [← relabelStream_take_eq_canonicalize, take_label_getElem? s n i.val, if_pos i.isLt]

/-! ## Phase 3 — Adäquatheits-Korollar (schließt die Inspektions-Naht II.3/II.5) -/

/-- **Adäquatheits-Korollar.** `label` (S2) und `relabel` (S1) berechnen dieselbe
Normalform auf jedem gemeinsamen Präfix: an Position `i < n` ist der Strom-Rang
`label s i` genau der `relabel`-Wert des n-Präfixes. Die in der S2-Bewertung
(II.3/II.5) als *Inspektions-Urteil* markierte Adäquatheits-Naht ist damit
**maschinell geschlossen** — die Familien-Einordnung wandert von der Inspektion
zurück auf die Mechanik. -/
theorem label_relabel_agree (s : Stream' α) (n a : ℕ) (h : a < n) :
    (relabel (s.take n))[a]? = some (label s a) := by
  rw [← relabelStream_take_eq_relabel, take_label_getElem? s n a, if_pos h]

/-! ## K-7-Doc-Korrektur (Anfügungs-Form, Quer-Verweis — null S2-Erosion)

**Korrektur des `kenogram_no_reduction_basis`-Doc-strings (S2) in Anfügungs-Form.**
Der S2-Doc-string von `Stream.kenogram_no_reduction_basis` benennt als
Abhängigkeit „`relabelStream_eq_iff` *und* `label_eq_self`". Der Beweis-Körper
referenziert `relabelStream_eq_iff` jedoch **null mal** (S2-Bewertung II.2, zweite
Manifestation der A→B-Drift); die tatsächliche Code-Abhängigkeit ist
`label_eq_self` + die Rang-Dichtheit `image_label_range`. Die Verbindung zum
Bisimulations-Kern ist **konzeptuell** (beide Sätze sind Facetten der
Beobachtungs-Identität), **keine Code-Abhängigkeit**.

Diese Korrektur ist **additiv** (Anfügung im Brücken-Modul, null Berührung des
S2-Bestands). **Anfügungs-Preis-Klausel:** die Heilung ist nur vorwärts sichtbar —
wer den S2-Doc-string liest, ohne dieses Modul zu kennen, sieht die Überzeichnung
weiter. (Die direkte S2-Bestands-Markierung wäre die Alternative, falls eine
Erosion gewünscht ist; hier bewusst vermieden.)

**Selbst-reflexiver „ruht auf"-Audit dieses Moduls:** die Brücke
(`relabelStream_take_eq_relabel`) ruht im Beweis-Körper nachweislich auf
`rgs_unique_of_pattern`, `isRGSStream_take`, `relabel_isRGS`, `relabel_length`,
`relabel_getElem?_eq_iff`, `label_eq_iff` — und auf nichts, was die Doc-strings
nicht benennen. Keine dritte A→B-Drift angefügt. -/

/-! ## Axiom-Wachen (B2)

Die gemessenen Profile der vier tragenden Saetze dieser Datei, eingefroren:
der Bruecken-Hauptsatz in Buendel- und punktweiser Form, die Praefix-Lokalitaet
`label_prefix_local` und das Adaequatheits-Korollar `label_relabel_agree`
(beide ueber Nachtrag N2 aufgenommen — im Kopf-Doc nur im Fliesstext genannt und
darum vom Backtick-Kriterium nicht gefasst). -/

/-- info: 'Reformulation.Kenogram.Bridge.label_prefix_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms label_prefix_local

/--
info: 'Reformulation.Kenogram.Bridge.relabelStream_take_eq_canonicalize' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms relabelStream_take_eq_canonicalize

/--
info: 'Reformulation.Kenogram.Bridge.relabelStream_restrict_canonicalize' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms relabelStream_restrict_canonicalize

/-- info: 'Reformulation.Kenogram.Bridge.label_relabel_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms label_relabel_agree

end Reformulation.Kenogram.Bridge
