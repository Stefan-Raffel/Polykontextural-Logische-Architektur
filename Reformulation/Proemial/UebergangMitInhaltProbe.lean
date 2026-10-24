import Reformulation.Proemial.AsymmetricDiscontexturalTransition
import Reformulation.Proemial.KenogramForkProbe

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

## (4) S33 unberührt

`contextureCrossing : True` steht in BEIDEN Instanzen, `towerTransition` und `towerTransitionNeu`.
Ob „Kontexturwechsel" bei Günther Akkretion voraussetzt, ist OFFEN und eine Quellenfrage
(Hermeneutes: NN 1971 Iteration/Akkretion, IGN S. 9, Cybernetic Ontology). Die Sonde entscheidet es
nicht.

## Die Sätze

```text
le_foldr_max                    Hilfssatz:  jedes Zeichen ≤ M (Induktion, choice-frei)
stepNeu_noreturn                INSTANZIIERUNG (ascentBy_noreturn)
stepNeu_preserves_substructure  INSTANZIIERUNG (ascentBy_preserves_substructure)
stepNeu_eq_stepNew              FOLGERUNG:  stepNeu ist über nichtleeren Ketten stepNew
stepNeu_nichtIntern             FOLGERUNG, UNSER:  der akkretive Aufstieg trägt ein neues Zeichen
step_intern                     FOLGERUNG, UNSER:  der iterative Aufstieg trägt keins (nichtleere Kette)
towerTransition_nicht_nichtIntern  FOLGERUNG, UNSER:  die Bestands-Instanz erfüllt das Feld nicht
drei_felder_trennen_nicht       FOLGERUNG, UNSER:  beide Aufstiege erfüllen Richtung und Substruktur
stepNeu_fork, step_fork         FOLGERUNG aus forkWidth_extend:  +1 gegen +0
stufe_zwei                      EICHUNG:  [0,1] ↦ [0,1,2] bzw. [0,1,0]
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

/-- jedes Zeichen der Kette ist höchstens ihr grösstes -/
theorem le_foldr_max : ∀ {l : List ℕ} {a : ℕ}, a ∈ l → a ≤ l.foldr max 0
  | _ :: _, _, .head _ => Nat.le_max_left _ _
  | _ :: _, _, .tail _ h => Nat.le_trans (le_foldr_max h) (Nat.le_max_right _ _)

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

end Reformulation.Proemial.UebergangMitInhaltProbe

-- ============================================================
-- Wachen — Axiom-Profile
-- ============================================================

/-- info: 'Reformulation.Proemial.UebergangMitInhaltProbe.le_foldr_max' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.UebergangMitInhaltProbe.le_foldr_max

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
