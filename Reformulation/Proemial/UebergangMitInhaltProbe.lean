import Reformulation.Proemial.AsymmetricDiscontexturalTransition
import Reformulation.Proemial.KenogramForkProbe
import Reformulation.Kenogram.Operational            -- Kenogram.le_foldr_max

/-!
# Proemial.UebergangMitInhaltProbe — ein Feld an den Enden, und zwei Aufstiege, die die drei alten nicht trennen

STANDALONE, NICHT im Aggregat (konsumiert `AsymmetricDiscontexturalTransition` und
`KenogramForkProbe`, beide standalone). Target `Probes`. Sonde nach
`KorpusRev2/Prompt_Sonde_Uebergang_mit_Inhalt_Lichtfigur.md` (Mathematiker, 24.10.2026; Grundlage
`KorpusRev2/Klaerung_Lichtfigur_Uebergang_mit_Inhalt.md` §3, §4).

**Was das Modul ist (CLAUDE.md §4):** eine Sonde mit ERTRAG im Kleinen. Die KA.4-Struktur
`AsymmetricDiscontexturalTransition` wird um ein Beweisfeld an den Enden ERWEITERT, nicht
geändert: `TransitionMitInhalt` erbt die vier Felder und das Setzungsfeld `contextureCrossing : True`
(Registerzeile S33) unverändert und fügt `zeichen` und `nichtIntern` hinzu. Die Setzung ist nicht
neu angelegt, nur geerbt; ihre Klasse (konstitutiv) steht am Feld in der Elternstruktur.

## (1) Anlass

Die Lichtfigur (Vorklärung 16.10., Klärung 24.10.): Der Träger des Übergangs hat keinen Inhalt;
was ihn ausmacht, steht an seinen Enden. Vorfrage 3.1 dort: Kann ein Feld an den Enden mehr sagen
als `substructure_preserved` und `not_determined`? **Antwort der Sonde: ja.** `nichtIntern` trennt
zwei Aufstiege, die alle drei alten Beweisfelder erfüllen (`drei_felder_trennen_nicht`,
`towerTransitionNeu`, `towerTransition_nicht_nichtIntern`).

## (2) Befund

`step` (TowerAsymmetryProbe) ist ITERATIV: Es hängt `0` an, und `0` steht in jeder nichtleeren
Kette schon (`isRGS_head`). Der Bestand instanziiert die KA.4-Struktur (`towerTransition`) mit
einem Aufstieg, der kein neues Zeichen über die Grenze trägt (`step_intern`). Das ist kein Fehler:
Die Felder sagen, was sie sagen; die Sonde macht sichtbar, was sie nicht sagen.

`stepNeu` ist der akkretive Aufstieg: Er hängt `M + 1` an (M das grösste Zeichen), über der leeren
Kette `0`. **Er ist kein neuer Aufstieg im Bestand:** `KenogramForkProbe` führt seit dem
13.10.2026 `stepNew` (nur über nichtleeren Ketten) und `ascentBy` (Aufstieg nach jeder Wahlregel)
mit Richtung und Substruktur für jede Wahl. Hier ist `stepNeu := ascentBy waehleNeu`, die
Totalisierung von `stepNew`; Richtung und Substruktur sind darum Einsetzungen
(`stepNeu_noreturn`, `stepNeu_preserves_substructure`), und `stepNeu_eq_stepNew` bindet sie an den
Bestand.

## (3) ZUORDNUNG (Lesart, kein Satz)

Günther stellt beide Pole auf eine Seite, IGN S. 9 (Textschicht, PDF = Druckseite): *„neben der
sich immer gleichen Wiederholung in der originalgetreuen Abbildung des Urbilds auch noch
Akkretivität, d.h. »Wiederholung mit Verwandlung«“*. Die erste ↔ `step`, die zweite ↔ `stepNeu`.
Nach der Lesung des Mathematikers (Beiträge III, Vorwort S. IX, am Bild 23.10.; von der Instanz
nicht geprüft, der Scan hat keine Textschicht) steht dort die Wiederholung durch Spiegelung, im
Abbild nur das, was man schon im Urbild gewusst hat ↔ `step`. Die Zuordnung der drei alten Felder
zur Lichtfigur (Strahl ↔ `not_reversible`, gerader Stab ↔ `substructure_preserved`, Brechungsbild
↔ `not_determined`) ist die der Klärung vom 24.10.; die Quellen dort (gebrochene Rationalität
1958 S. 8, Textschicht; Vorlesung 7.12.1981 F5/1, Whisper) sind von der Instanz nicht geprüft.
**Keine Behauptung über Günthers Begriff des Kontexturwechsels.**

## (3a) Das Feld charakterisiert (§IV, nachgetragen 24.10.2026)

Das Feld trennt nicht nur zwei Beispiele. Für JEDE Wahlregel gilt über einer nichtleeren Kette:
`nichtIntern` genau bei der Wahl des neuen Zeichens `M + 1` (`nichtIntern_iff_akkretiv`); über der
leeren Kette ist jede Wahl `0` und neu (`nichtIntern_nil`). Die Richtung (→) braucht die Dichtheit der
RGS (`Kenogram.rgs_take_mem`: jedes Zeichen bis zum Maximum kommt vor). Iteriert ab der leeren Kette gibt
`stepNeu` die Kette `[0, 1, …, n−1]`, `step` die Kette `[0, 0, …, 0]` (`stepNeu_iter`, `step_iter`).
Die zwei Pole von IGN S. 9, „originalgetreue Abbildung des Urbilds“ und „Wiederholung mit Verwandlung“,
sind die zwei Werte dieser Wahl; die Akkretion ist hier der Zuwachs um EIN Zeichen, `M + 1`. ZUORDNUNG.
Gebaut nach `KorpusRev2/Prompt_3_4_nichtIntern_Charakterisierung_und_Meixl_Tafeln_Guenthers.md`.

*Dublette entfernt (24.10.):* Der Zug vom selben Morgen führte ein eigenes `le_foldr_max`; der Bestand hat
es dreimal (`Kenogram.le_foldr_max` in Operational, `Kenogram.Unbounded.le_foldr_max`,
`K4DiscontexturalityProbe.le_foldr_max_of_mem`). Es ist gestrichen; die Sonde nimmt `Kenogram.le_foldr_max`.

## (4) S33 unberührt

`contextureCrossing : True` steht in BEIDEN Instanzen, `towerTransition` und `towerTransitionNeu`.
Ob „Kontexturwechsel" bei Günther Akkretion voraussetzt, ist OFFEN und eine Quellenfrage
(Hermeneutes: NN 1971 Iteration/Akkretion, IGN S. 9, Cybernetic Ontology). Die Sonde entscheidet es
nicht.

## Die Sätze

```text
stepNeu_noreturn                INSTANZIIERUNG (ascentBy_noreturn)
stepNeu_preserves_substructure  INSTANZIIERUNG (ascentBy_preserves_substructure)
stepNeu_eq_stepNew              FOLGERUNG:  stepNeu ist über nichtleeren Ketten stepNew
stepNeu_nichtIntern             FOLGERUNG, UNSER:  der akkretive Aufstieg trägt ein neues Zeichen
step_intern                     FOLGERUNG, UNSER:  der iterative Aufstieg trägt keins (nichtleere Kette)
towerTransition_nicht_nichtIntern  FOLGERUNG, UNSER:  die Bestands-Instanz erfüllt das Feld nicht
drei_felder_trennen_nicht       FOLGERUNG, UNSER:  beide Aufstiege erfüllen Richtung und Substruktur
stepNeu_fork, step_fork         FOLGERUNG aus forkWidth_extend:  +1 gegen +0
stufe_zwei                      EICHUNG:  [0,1] ↦ [0,1,2] bzw. [0,1,0]
nichtIntern_iff_akkretiv        FOLGERUNG, UNSER:  das Feld charakterisiert (§IV, 24.10.)
nichtIntern_nil                 FOLGERUNG:  über der leeren Kette trägt jede Wahl ein neues Zeichen
stepNeu_iter, step_iter         FOLGERUNG:  [0, 1, …, n−1] gegen [0, 0, …, 0]
stufe_drei                      EICHUNG:  [0,1,2] gegen [0,0,0]
foldr_max_range, stepNeu_val    Hilfssätze
```

`towerTransitionNeu` ist die Instanz (def). `not_determined` hängt nur am Abstieg und ist in beiden
Instanzen derselbe Zeuge.

**Nicht hier:** Physik (Eigenzeit, affiner Parameter, Lichtbahn). Kein Wort davon im Modul ausser
diesem.

Kein `sorry`, kein `Classical.choice`, kein `native_decide`.
-/

namespace Reformulation.Proemial.UebergangMitInhaltProbe

open Reformulation.Kenogram
open Reformulation.Proemial.IrreversibleAdvance (NoReturn)
open Reformulation.Proemial.TowerAsymmetryProbe (Tower step)
open Reformulation.Proemial.KenogramForkProbe (Choice ascentBy ascentBy_noreturn
  ascentBy_preserves_substructure stepNew forkWidth forkWidth_extend)
open Reformulation.Proemial.AsymmetricTransition

-- ============================================================
-- §I — Der akkretive Aufstieg
-- ============================================================

/-- die akkretive Wahlregel:  ein NEUES Zeichen `M + 1`, über der leeren Kette `0` -/
def waehleNeu : Choice := fun x =>
  if h : x.2.val = [] then ⟨0, Nat.zero_le _, fun _ => rfl⟩
  else ⟨x.2.val.foldr max 0 + 1, Nat.le_refl _, fun h' => absurd h' h⟩

/-- der akkretive Aufstieg -/
def stepNeu : Tower → Tower := ascentBy waehleNeu

theorem stepNeu_noreturn : NoReturn stepNeu := ascentBy_noreturn waehleNeu

theorem stepNeu_preserves_substructure (x : Tower) : x.2.val <+: (stepNeu x).2.val :=
  ascentBy_preserves_substructure waehleNeu x

/-- über nichtleeren Ketten ist `stepNeu` der Bestandsschritt `stepNew` (KenogramForkProbe) -/
theorem stepNeu_eq_stepNew (x : Tower) (h : x.2.val ≠ []) : stepNeu x = stepNew x h := by
  unfold stepNeu ascentBy waehleNeu stepNew
  simp only [dif_neg h]

-- ============================================================
-- §II — Das Feld an den Enden und die erweiterte Struktur
-- ============================================================

/-- **Nicht-Internalität des Übergangs:**  das Ziel trägt ein Zeichen, das die Quelle nicht hat -/
def NichtIntern (T : AsymmetricDiscontexturalTransition) (z : T.Carrier → List ℕ) : Prop :=
  ∀ x, ∃ s, s ∈ z (T.ascent x) ∧ s ∉ z x

/-- die KA.4-Struktur MIT Inhalt an den Enden:  die Felder der Elternstruktur unverändert (auch
    das Setzungsfeld `contextureCrossing : True`, S33, konstitutiv, geerbt), dazu ein Beweisfeld -/
structure TransitionMitInhalt extends AsymmetricDiscontexturalTransition where
  /-- die Zeichen eines Punktes -/
  zeichen : Carrier → List ℕ
  /-- **Beweisfeld — Nicht-Internalität.** Der Aufstieg trägt ein Zeichen, das die Quelle nicht hat. -/
  nichtIntern : ∀ x, ∃ s, s ∈ zeichen (ascent x) ∧ s ∉ zeichen x

-- ============================================================
-- §III — Die Sätze
-- ============================================================

/-- **Der akkretive Aufstieg trägt ein neues Zeichen:**  `0` über der leeren Kette, sonst `M + 1` -/
theorem stepNeu_nichtIntern (x : Tower) :
    ∃ s, s ∈ (stepNeu x).2.val ∧ s ∉ x.2.val := by
  by_cases h : x.2.val = []
  · refine ⟨0, ?_, ?_⟩
    · show 0 ∈ x.2.val ++ [(waehleNeu x).1]
      unfold waehleNeu
      rw [dif_pos h]
      exact List.mem_append_right _ List.mem_cons_self
    · rw [h]; exact List.not_mem_nil
  · refine ⟨x.2.val.foldr max 0 + 1, ?_, fun hm => Nat.not_succ_le_self _ (le_foldr_max hm)⟩
    show _ ∈ x.2.val ++ [(waehleNeu x).1]
    unfold waehleNeu
    rw [dif_neg h]
    exact List.mem_append_right _ List.mem_cons_self

/-- **Instanz NEU.**  Der akkretive Turm erfüllt die erweiterte Struktur.  Abstieg, Substruktur-
    Relation, Determinationsverlust und Setzungsfeld wie `towerTransition`. -/
def towerTransitionNeu : TransitionMitInhalt where
  Carrier := Tower
  ascent := stepNeu
  descent := towerDescent
  sub := towerSub
  not_reversible := stepNeu_noreturn
  substructure_preserved := stepNeu_preserves_substructure
  not_determined := towerTransition.not_determined
  contextureCrossing := trivial
  zeichen := fun x => x.2.val
  nichtIntern := stepNeu_nichtIntern

/-- **Der iterative Aufstieg trägt kein neues Zeichen:**  das angehängte `0` steht in jeder
    nichtleeren Kette schon (`isRGS_head`, die Kette beginnt mit `0`) -/
theorem step_intern : ∀ x : Tower, x.2.val ≠ [] → ¬ (∃ s, s ∈ (step x).2.val ∧ s ∉ x.2.val) := by
  intro x hne ⟨s, hs, hn⟩
  have hs' : s ∈ x.2.val ++ [0] := hs
  rcases List.mem_append.mp hs' with h | h
  · exact hn h
  · have hs0 : s = 0 := List.mem_singleton.mp h
    have hlen : 0 < x.2.val.length := List.length_pos_iff.mpr hne
    have h0 : x.2.val[0] = 0 := isRGS_head x.2.property.2 hlen
    exact hn (hs0 ▸ h0 ▸ List.getElem_mem hlen)

/-- **Die Bestands-Instanz erfüllt das Feld nicht:**  Zeuge `[0]` -/
theorem towerTransition_nicht_nichtIntern :
    ¬ NichtIntern towerTransition (fun x => x.2.val) := fun h =>
  step_intern ⟨1, ⟨[0], by decide⟩⟩ (by decide) (h ⟨1, ⟨[0], by decide⟩⟩)

/-- **Die drei alten Felder trennen nicht:**  beide Aufstiege sind rückkehrfrei und erhalten die
    Substruktur;  der Determinationsverlust hängt nur am gemeinsamen Abstieg `towerDescent` -/
theorem drei_felder_trennen_nicht :
    (NoReturn step ∧ (∀ x, towerSub x (step x))) ∧ (NoReturn stepNeu ∧ (∀ x, towerSub x (stepNeu x))) :=
  ⟨⟨towerTransition.not_reversible, towerTransition.substructure_preserved⟩,
    ⟨stepNeu_noreturn, stepNeu_preserves_substructure⟩⟩

/-- **Eichung an der Gabelung:**  der akkretive Schritt erweitert die Gabelung um eins -/
theorem stepNeu_fork (x : Tower) (h : x.2.val ≠ []) :
    forkWidth (stepNeu x).2 = forkWidth x.2 + 1 := by
  rw [stepNeu_eq_stepNew x h]
  show forkWidth (extend x.2 (x.2.val.foldr max 0 + 1) (Nat.le_refl _) (fun e => absurd e h)) = _
  rw [forkWidth_extend, if_pos rfl, if_neg h]

/-- **und der iterative nicht** -/
theorem step_fork (x : Tower) (h : x.2.val ≠ []) : forkWidth (step x).2 = forkWidth x.2 := by
  show forkWidth (extend x.2 0 (Nat.zero_le _) (fun _ => rfl)) = _
  rw [forkWidth_extend, if_neg (fun e => Nat.succ_ne_zero _ e.symm), if_neg h]
  rfl

/-- **Eichung an Stufe 2:**  `[0,1]` ↦ `[0,1,2]` (akkretiv) und `[0,1,0]` (iterativ) -/
theorem stufe_zwei :
    (stepNeu ⟨2, ⟨[0, 1], by decide⟩⟩).2.val = [0, 1, 2] ∧
    (step ⟨2, ⟨[0, 1], by decide⟩⟩).2.val = [0, 1, 0] := by
  constructor <;> decide

-- ============================================================
-- §IV — Das Feld charakterisiert:  nichtIntern genau bei der Wahl des neuen Zeichens
-- ============================================================

/-- **Charakterisierung.**  Über einer nichtleeren Kette trägt der Aufstieg nach JEDER Wahlregel
    genau dann ein neues Zeichen, wenn sie `M + 1` wählt.  (→) braucht die Dichtheit der RGS
    (`rgs_take_mem`:  jedes Zeichen bis zum Maximum kommt vor), (←) die Schranke `le_foldr_max`. -/
theorem nichtIntern_iff_akkretiv (c : Choice) (x : Tower) (h : x.2.val ≠ []) :
    (∃ s, s ∈ (ascentBy c x).2.val ∧ s ∉ x.2.val) ↔ (c x).1 = x.2.val.foldr max 0 + 1 := by
  constructor
  · rintro ⟨s, hs, hn⟩
    have hs' : s ∈ x.2.val ++ [(c x).1] := hs
    rcases List.mem_append.mp hs' with hl | hk
    · exact absurd hl hn
    · have hsk : s = (c x).1 := List.mem_singleton.mp hk
      match Nat.decEq (c x).1 (x.2.val.foldr max 0 + 1) with
      | isTrue e => exact e
      | isFalse ne =>
        exfalso
        have hle : (c x).1 ≤ x.2.val.foldr max 0 :=
          Nat.lt_succ_iff.mp (Nat.lt_of_le_of_ne (c x).2.1 ne)
        have hpos : 0 < x.2.val.length := List.length_pos_iff.mpr h
        have hmem := rgs_take_mem x.2.property.2 x.2.val.length (Nat.le_refl _) hpos (c x).1
          (by rw [List.take_length]; exact hle)
        rw [List.take_length] at hmem
        exact hn (hsk ▸ hmem)
  · intro hk
    refine ⟨(c x).1, ?_, ?_⟩
    · show _ ∈ x.2.val ++ [(c x).1]
      exact List.mem_append_right _ List.mem_cons_self
    · intro hm
      have := le_foldr_max hm
      rw [hk] at this
      exact Nat.not_succ_le_self _ this

/-- **Der leere Fall:**  über der leeren Kette ist jede Wahl `0`, und `0` ist dort neu -/
theorem nichtIntern_nil (c : Choice) (x : Tower) (h : x.2.val = []) :
    ∃ s, s ∈ (ascentBy c x).2.val ∧ s ∉ x.2.val := by
  refine ⟨(c x).1, ?_, ?_⟩
  · show _ ∈ x.2.val ++ [(c x).1]
    exact List.mem_append_right _ List.mem_cons_self
  · have hl : ∀ (l : List ℕ) (k : ℕ), l = [] → k ∉ l := fun l k e hm => by subst e; exact List.not_mem_nil hm
    exact hl _ _ h

/-- das Maximum von `[0, …, n]` ist `n` -/
theorem foldr_max_range : ∀ n : ℕ, (List.range (n + 1)).foldr max 0 = n
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, foldr_max_append_singleton, foldr_max_range n]
    exact Nat.max_eq_right (Nat.le_succ n)

/-- der akkretive Schritt, ausgeschrieben -/
theorem stepNeu_val (y : Tower) :
    (stepNeu y).2.val = y.2.val ++ [if y.2.val = [] then 0 else y.2.val.foldr max 0 + 1] := by
  show y.2.val ++ [(waehleNeu y).1] = _
  unfold waehleNeu
  by_cases h : y.2.val = []
  · rw [dif_pos h, if_pos h]
  · rw [dif_neg h, if_neg h]

/-- **Iteration des akkretiven Aufstiegs:**  n-mal `stepNeu` ab der leeren Kette ist `[0, 1, …, n−1]` -/
theorem stepNeu_iter : ∀ n : ℕ, (stepNeu^[n] ⟨0, ⟨[], by decide⟩⟩).2.val = List.range n
  | 0 => rfl
  | n + 1 => by
    rw [Function.iterate_succ_apply', stepNeu_val, stepNeu_iter n]
    cases n with
    | zero => rfl
    | succ m =>
      have hne : List.range (m + 1) ≠ [] := fun e => by
        have hl := congrArg List.length e
        rw [List.length_range] at hl
        exact Nat.succ_ne_zero m hl
      rw [if_neg hne, foldr_max_range m]
      exact (List.range_succ (n := m + 1)).symm

/-- **und des iterativen:**  n-mal `step` ab der leeren Kette ist `[0, 0, …, 0]` -/
theorem step_iter : ∀ n : ℕ, (step^[n] ⟨0, ⟨[], by decide⟩⟩).2.val = List.replicate n 0
  | 0 => rfl
  | n + 1 => by
    rw [Function.iterate_succ_apply']
    show (step^[n] ⟨0, ⟨[], by decide⟩⟩).2.val ++ [0] = _
    rw [step_iter n, List.replicate_succ']

/-- **Eichung an Stufe 3:**  `[0,1,2]` gegen `[0,0,0]` -/
theorem stufe_drei :
    (stepNeu^[3] ⟨0, ⟨[], by decide⟩⟩).2.val = [0, 1, 2] ∧
    (step^[3] ⟨0, ⟨[], by decide⟩⟩).2.val = [0, 0, 0] := by
  constructor <;> decide

end Reformulation.Proemial.UebergangMitInhaltProbe

-- ============================================================
-- Wachen — Axiom-Profile
-- ============================================================


/-- info: 'Reformulation.Proemial.UebergangMitInhaltProbe.stepNeu_noreturn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.UebergangMitInhaltProbe.stepNeu_noreturn

/-- info: 'Reformulation.Proemial.UebergangMitInhaltProbe.stepNeu_preserves_substructure' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.UebergangMitInhaltProbe.stepNeu_preserves_substructure

/-- info: 'Reformulation.Proemial.UebergangMitInhaltProbe.stepNeu_eq_stepNew' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.UebergangMitInhaltProbe.stepNeu_eq_stepNew

/-- info: 'Reformulation.Proemial.UebergangMitInhaltProbe.stepNeu_nichtIntern' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.UebergangMitInhaltProbe.stepNeu_nichtIntern

/-- info: 'Reformulation.Proemial.UebergangMitInhaltProbe.step_intern' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.UebergangMitInhaltProbe.step_intern

/-- info: 'Reformulation.Proemial.UebergangMitInhaltProbe.towerTransition_nicht_nichtIntern' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.UebergangMitInhaltProbe.towerTransition_nicht_nichtIntern

/-- info: 'Reformulation.Proemial.UebergangMitInhaltProbe.drei_felder_trennen_nicht' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.UebergangMitInhaltProbe.drei_felder_trennen_nicht

/-- info: 'Reformulation.Proemial.UebergangMitInhaltProbe.stepNeu_fork' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.UebergangMitInhaltProbe.stepNeu_fork

/-- info: 'Reformulation.Proemial.UebergangMitInhaltProbe.step_fork' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.UebergangMitInhaltProbe.step_fork

/-- info: 'Reformulation.Proemial.UebergangMitInhaltProbe.stufe_zwei' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.UebergangMitInhaltProbe.stufe_zwei

/-- info: 'Reformulation.Proemial.UebergangMitInhaltProbe.nichtIntern_iff_akkretiv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.UebergangMitInhaltProbe.nichtIntern_iff_akkretiv

/-- info: 'Reformulation.Proemial.UebergangMitInhaltProbe.nichtIntern_nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.UebergangMitInhaltProbe.nichtIntern_nil

/-- info: 'Reformulation.Proemial.UebergangMitInhaltProbe.foldr_max_range' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.UebergangMitInhaltProbe.foldr_max_range

/-- info: 'Reformulation.Proemial.UebergangMitInhaltProbe.stepNeu_val' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.UebergangMitInhaltProbe.stepNeu_val

/-- info: 'Reformulation.Proemial.UebergangMitInhaltProbe.stepNeu_iter' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.UebergangMitInhaltProbe.stepNeu_iter

/-- info: 'Reformulation.Proemial.UebergangMitInhaltProbe.step_iter' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.UebergangMitInhaltProbe.step_iter

/-- info: 'Reformulation.Proemial.UebergangMitInhaltProbe.stufe_drei' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.UebergangMitInhaltProbe.stufe_drei
