import Reformulation
import Lean.Elab.Command

/-!
# Proemial.DefinitionLedger — die Traegerspalte des Definition-Ledgers, compilergeprueft

**Benennung, keine Ertragsdatei.** Diese Datei enthaelt keinen Satz, keine Definition mit
Inhalt und keine Aussage ueber den Gegenstand. Sie haelt die Traegerspalte des
Definition-Ledgers (`docs/definition-ledger.md`) gegen die Aggregatumgebung, damit die
Tabelle nicht still veraltet.

## Was geprueft wird

- **R1 — der Traeger loest auf.** Jeder in der Tabelle genannte Name wird ueber die Umgebung
  nachgeschlagen. Ein Tippfehler oder eine gewanderte Deklaration bricht den Bau.
- **R2 — der Traegerstatus stimmt mit der Deklarationsart ueberein.** `#ledger_theorem`
  verlangt `thmInfo` mit einem Schluss, der nicht `True` ist; `#ledger_def` verlangt
  `defnInfo` — das sind `def`, `abbrev` und `instance`; `#ledger_setzung` verlangt `thmInfo`
  mit Schluss `True`. Eine `structure` (`inductInfo`) wird **nicht** akzeptiert: im Ledger
  steht keine als Traeger, und wenn eine auftraete, soll das eine Entscheidung sein und
  keine stille Erweiterung.

Dass `Setzung` und `Theorem` an der Deklarationsart nicht zu unterscheiden sind, ist
gemessen: die Projektion eines `True`-Feldes ist ein `theorem`. Unterschieden werden sie am
Schluss des Typs — dasselbe Kriterium, an dem `CLAUDE.md` §10 haengt.

## Was nicht geprueft wird

R3 (kein Zuordnungsstatus `Theorem`), R4 (Traegerstatus `Offen` erzwingt leere
Traegerspalte), R5 (alle 19 Paragraphen vertreten), R6 (Traegerstatus `Theorem` erzwingt
ausgefuellte Wachenspalte), R7 (jede Traegerzeile der Tabelle hat genau eine passende
Referenz in dieser Datei — und umgekehrt) und R8 (jede Zeilen-ID kommt in beiden Dateien
genau einmal vor) sind Textpruefungen und stehen in `doc_lint.sh`. Der
Zuordnungsstatus ist redaktionell und ueberhaupt nicht pruefbar. Zeilen mit Traegerstatus
`Offen` erscheinen hier nicht.

## Ablage und Kennzahlen

Eigenes `lean_lib`-Target `DefinitionLedger` in `defaultTargets`, **nicht** vom Aggregat
importiert. Die Gate-Konstantenzahl darf sich dadurch nicht aendern: aendert sie sich, ist
diese Datei in den Aggregat-Importbaum geraten, und das ist ein Fehler, kein Messergebnis.

## Wartungsposten

Der Metacode haengt an vier Lean-internen Namen: `realizeGlobalConstNoOverload`,
`ConstantInfo` samt Konstruktoren, `Meta.forallTelescopeReducing` und `throwErrorAt`. Wandert
einer davon bei einem Toolchain-Wechsel, bricht der Bau **hier** — laut und lokal. Betroffen
ist dann die Pruefung der Tabelle, **keine** Aussage des Korpus: diese Datei traegt keine.

Kein `sorry`, kein `axiom`, kein Feld vom Typ `True`, keine Wache — es gibt keinen Satz, an
dem ein Axiomprofil haengen koennte.
-/

open Lean Elab Command

namespace Reformulation.Proemial.DefinitionLedger

/-- Der Traegerstatus des Ledgers, soweit er eine Deklaration bezeichnet. -/
private inductive LedgerTS | thm | defn | setzung

private def tsName : LedgerTS → String
  | .thm => "Theorem" | .defn => "Definition" | .setzung => "Setzung"

/-- Die Deklarationsart, wie die Fehlermeldung sie nennt. -/
private def artName (ci : ConstantInfo) : String :=
  match ci with
  | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .inductInfo _ => "structure"
  | .axiomInfo _ => "axiom" | .opaqueInfo _ => "opaque" | .ctorInfo _ => "constructor"
  | .quotInfo _ => "quot" | .recInfo _ => "recursor"

/-- R1 und R2 fuer eine Ledger-Zeile. `zeile` ist die Zeilen-ID, damit die Meldung sagt,
welche Zeile bricht, und nicht nur, welche Datei-Zeile. -/
private def ledgerCheck (zeile : String) (i : Ident) (erwartet : LedgerTS) :
    CommandElabM Unit := do
  let n ← liftCoreM <| realizeGlobalConstNoOverload i
  let some ci := (← getEnv).find? n
    | throwErrorAt i "Ledger {zeile}: `{n}` loest nicht gegen die Aggregatumgebung auf (R1)"
  let trueSchluss ← liftTermElabM <|
    Meta.forallTelescopeReducing ci.type fun _ b => pure (b.isConstOf ``True)
  let passt : Bool := match erwartet, ci with
    | .thm, .thmInfo _ => !trueSchluss
    | .defn, .defnInfo _ => true
    | .setzung, .thmInfo _ => trueSchluss
    | _, _ => false
  unless passt do
    throwErrorAt i "Ledger {zeile}: TS ist als {tsName erwartet} gefuehrt, `{n}` ist aber \
      {artName ci}{if trueSchluss then " mit Schluss True (Setzung)" else ""} (R2)"

/-- Ledger-Zeile mit Traegerstatus `Theorem`. -/
syntax "#ledger_theorem " str ident : command

/-- Ledger-Zeile mit Traegerstatus `Definition` (`def`, `abbrev`, `instance`). -/
syntax "#ledger_def " str ident : command

/-- Ledger-Zeile mit Traegerstatus `Setzung` (Schluss `True`). -/
syntax "#ledger_setzung " str ident : command

elab_rules : command
  | `(#ledger_theorem $z:str $i:ident) => ledgerCheck z.getString i .thm
  | `(#ledger_def $z:str $i:ident) => ledgerCheck z.getString i .defn
  | `(#ledger_setzung $z:str $i:ident) => ledgerCheck z.getString i .setzung

end Reformulation.Proemial.DefinitionLedger

-- ============================================================
-- Die Traegerspalte, Zeile fuer Zeile (Ledger Rev. 5)
-- Zeilen mit Traegerstatus `Offen` erscheinen nicht.
-- ============================================================

#ledger_def "L01-1" Reformulation.Proemial.TransjunctionCloneBound.S
#ledger_def "L01-2" Reformulation.Proemial.NonUniformCloneBound.PreservesPair
#ledger_def "L01-3" Reformulation.Proemial.NonUniformCloneBound.ContextureFaithful
#ledger_theorem "L01-4" Reformulation.Proemial.ContexturalFibration.fiber_emb_morphism

#ledger_def "L02-1" Reformulation.Proemial.ContextureOverlap.IsElemContexture
#ledger_theorem "L02-2" Reformulation.Proemial.ContextureOverlap.three_contextures_overlap
#ledger_theorem "L02-3" Reformulation.Proemial.ContextureOverlap.elem_contexture_overlap_le_one
#ledger_def "L02-4" Reformulation.Proemial.GeneralCloneBound.ActsAsMin
#ledger_def "L02-5" Reformulation.Proemial.GeneralCloneBound.ActsAsMax
#ledger_theorem "L02-6" Reformulation.Proemial.ElementaryCycle.card_orb_le_two
#ledger_theorem "L02-7" Reformulation.Proemial.ElementaryCycle.isElemContexture_orb_iff
#ledger_theorem "L02-8" Reformulation.Proemial.ElementaryCycle.exists_involutive_orb_eq

#ledger_theorem "L03-1" Reformulation.Proemial.GeneralCloneBound.locally_classical_in_clone_iff

#ledger_theorem "L04-1" Reformulation.Proemial.TransjunctionCloneBound.T_not_in_clone
#ledger_theorem "L04-2" Reformulation.Proemial.NonUniformCloneBound.W_not_in_clone
#ledger_theorem "L04-3" Reformulation.Proemial.GeneralCloneBound.locally_classical_in_clone_iff
#ledger_setzung "L04-4" Reformulation.Proemial.Discontextural.DiscontexturalStratification.discontextural_posited
#ledger_theorem "L04-5" Reformulation.Proemial.QuaternaryCloneBound.locally_classical_in_clone_iff4
#ledger_theorem "L04-6" Reformulation.Proemial.QuaternaryCloneBound.mixed_not_in_constant_clone

#ledger_theorem "L05-1" Reformulation.Proemial.TransjunctionCloneBound.T_leaves_contextur
#ledger_theorem "L05-2" Reformulation.Proemial.NonUniformCloneBound.W_contexture_faithful
#ledger_theorem "L05-3" Reformulation.Proemial.StageAggregation.agg_nicht_erzeugbar
#ledger_theorem "L05-5" Reformulation.Proemial.PolicyCheck.freigabe_nicht_erzeugbar
#ledger_theorem "L05-6" Reformulation.Proemial.RAGAuthority.autoritaet_nicht_erzeugbar

#ledger_theorem "L06-2" Reformulation.Proemial.NonUniformCloneBound.W_locally_classical
#ledger_theorem "L06-3" Reformulation.Proemial.NonUniformCloneBound.W_not_in_clone
#ledger_theorem "L06-4" Reformulation.Proemial.ContextureOverlap.three_contextures_overlap
#ledger_theorem "L06-5" Reformulation.Proemial.StageAggregation.agg_nicht_erzeugbar_konstanten
#ledger_theorem "L06-6" Reformulation.Proemial.PolicyCheck.freigabe_nicht_erzeugbar_konstanten
#ledger_theorem "L06-7" Reformulation.Proemial.RAGAuthority.autoritaet_nicht_erzeugbar_konstanten

#ledger_def "L07-1" Reformulation.Proemial.TransjunctionCloneBound.negFin
#ledger_theorem "L07-2" Reformulation.Proemial.TransjunctionCloneBound.T_not_in_clone
#ledger_theorem "L07-3" Reformulation.Proemial.GeneralCloneBound.locally_classical_in_clone_iff

#ledger_def "L08-1" Reformulation.Proemial.TransjunctionCloneBound.T
#ledger_theorem "L08-2" Reformulation.Proemial.TransjunctionCloneBound.T_rejective
#ledger_theorem "L08-3" Reformulation.Proemial.TransjunctionCloneBound.T_crosses_exactly_one

#ledger_def "L09-1" Reformulation.Proemial.TransjunctionCloneBound.L
#ledger_theorem "L09-2" Reformulation.Proemial.TransjunctionCloneBound.term_preserves_contextur
#ledger_theorem "L09-3" Reformulation.Proemial.TransjunctionCloneBound.term_clone_localization

#ledger_def "L10-1" Reformulation.Proemial.TransjunctionCloneBound.phi
#ledger_theorem "L10-2" Reformulation.Proemial.TransjunctionCloneBound.test1_injective
#ledger_theorem "L10-3" Reformulation.Proemial.TransjunctionCloneBound.test1_min_max
#ledger_def "L10-4" Reformulation.Proemial.NonUniformCloneBound.conj

#ledger_def "L11-1" Reformulation.Proemial.NonUniformCloneBound.W
#ledger_theorem "L11-2" Reformulation.Proemial.StageAggregation.agg_lokal
#ledger_theorem "L11-4" Reformulation.Proemial.PolicyCheck.freigabe_lokal
#ledger_theorem "L11-5" Reformulation.Proemial.RAGAuthority.autoritaet_lokal

#ledger_theorem "L12-1" Reformulation.Proemial.GeneralCloneBound.locally_classical_in_clone_iff
#ledger_def "L12-2" Reformulation.Proemial.StageAggregation.agg
#ledger_theorem "L12-3" Reformulation.Proemial.RegimeThreshold.regime_threshold_at_four
#ledger_def "L12-5" Reformulation.Proemial.PolicyCheck.freigabe
#ledger_def "L12-6" Reformulation.Proemial.RAGAuthority.autoritaet

#ledger_theorem "L13-1" Reformulation.Proemial.TransjunctionCloneBound.T_rejective

#ledger_def "L16-1" Reformulation.Kenogram.relabel
#ledger_theorem "L16-2" Reformulation.Kenogram.rgs_unique_of_pattern

#ledger_theorem "L17-1" Reformulation.Proemial.ContextureOverlap.three_contextures_overlap

#ledger_theorem "L18-1" Reformulation.Proemial.IntervalBackbone.two_mul_intervalStart
#ledger_theorem "L18-2" Reformulation.Proemial.IntervalBackbone.intervalEnd_sub_start

#ledger_theorem "L19-1" Reformulation.Proemial.IntervalBackbone.tafel_IV
#ledger_theorem "L19-2" Reformulation.Proemial.IntervalBackbone.intervalEnd_succ_start
