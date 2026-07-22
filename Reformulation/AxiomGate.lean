import Reformulation
import Lean

/-!
# Reformulation.AxiomGate — Aggregat-Axiom-Gate (Engineering-Gates Phase 3a)

**Scharfes, build-integriertes `sorryAx`-Gate über dem Aggregat `Reformulation`.**

Dieses Modul **importiert** das Aggregat (`import Reformulation`) und wird selbst
**nicht** vom Aggregat importiert — es sitzt topologisch *über* dem Aggregat (kein
Zirkel). Es wird über das eigene Lake-Target `AxiomGate` (in `defaultTargets`)
gebaut; der `Reformulation`-Glob (Default `Glob.one`) fasst es nicht, deshalb das
explizite Target (siehe `lakefile.toml` und die Phase-3a-Sondierung).

Zweck: bei **jedem** `lake build` mechanisch prüfen, dass der Axiom-Abschluss des
Aggregats `sorryAx` **nur** über die unten gewhitelisteten, bekannten Klasse-D-Lücken
zieht. Taucht ein **neuer, nicht-gewhitelisteter** `sorryAx`-Träger auf, failt das
`throwError` im Top-Level-`run_cmd` den Build (rot). Das ist die mechanische
Garantie, die bei der ins Aggregat gewanderten Beck-Chevalley-Lücke fehlte: eine
„0 Sorries"-Aggregat-Aussage ist ab hier *belegt* statt behauptet.
-/

open Lean Elab Command

namespace Reformulation.AxiomGate

/-- Ein Modul gehört zum Aggregat-Codebestand, wenn sein Name `Reformulation` ist
oder mit `Reformulation.` beginnt. Schließt Mathlib/Lean/Std aus. (Wie in der
Phase-1-Probe `Diagnostics.AxiomProbe`.) -/
def isReformulationModule (m : Name) : Bool :=
  m == `Reformulation || (`Reformulation).isPrefixOf m

/-- **Die Whitelist — die vier bekannten, niedergelegten Klasse-D-Lücken.**

Diese Liste ist die versionierte, Diff-sichtbare Form der Aggregat-Aussage
„das Aggregat zieht `sorryAx` über genau diese vier Konstanten und keine andere".
Jede weitere `sorryAx`-Konstante ist ein Verstoß, kein Whitelist-Kandidat.

Zwei literale Sorry-Wurzeln an der Belegungs-Naht (F3e-BC ↔ F-3-Architektur, S↔K):
* `F3e.beckChevalleyFromData` — Klasse-D, BC-Konstruktion invariante Schicht,
  F1-belegungsspezifisch.
* `Proemial.belegung_specialization_cognitive` — F-3-Folge-Aufgabe (Lesart C),
  Belegungs-Wahl ausstehend.

Zwei abgeleitete (erben `sorryAx` von `beckChevalleyFromData`):
* `F3e.beckChevalley_exists`
* `F3e.beckChevalley_unique`

Gestrichen (Sorry-Konsolidierung γ-V):
`Proemial.Substantial.beck_chevalley_verschraenkung_substantial` — veraltete,
mit dem F-3-Stub (ohne `compat`) unbeweisbare Parallelform; Substanz sorry-frei
eingelöst in `…BeckChevalley.beck_chevalley_verschraenkung_truly_substantial`.
Memorial-Block in `AlphaGammaSubstantial.lean`. -/
def whitelist : Array Name := #[
  ``Reformulation.F3e.beckChevalleyFromData,
  ``Reformulation.Proemial.belegung_specialization_cognitive,
  ``Reformulation.F3e.beckChevalley_exists,
  ``Reformulation.F3e.beckChevalley_unique ]

/-! **Das Gate.** Iteriert über alle `Reformulation.*`-Konstanten, sammelt die
`sorryAx`-Träger, und gleicht gegen die Whitelist ab:
* `violations := sorryHolders \ whitelist` — neue, nicht-gewhitelistete Lücken;
  nicht leer ⇒ `throwError` (Build-Fehler, die scharfe Hälfte).
* `stale := whitelist \ sorryHolders` — Whitelist-Einträge, die *nicht mehr*
  `sorryAx` ziehen (Lücke geschlossen) oder nicht mehr existieren; nicht leer ⇒
  `throwError` (damit die Whitelist nicht zur Müllhalde verrottet).
* sonst `logInfo` mit Bestätigung. -/
run_cmd do
  let env ← getEnv
  let modNames := env.allImportedModuleNames
  let whitelistSet : NameSet :=
    whitelist.foldl (fun s n => s.insert n) {}
  let mut considered := 0
  let mut sorryHolders : NameSet := {}
  for (c, _info) in env.constants.toList do
    let some modIdx := env.getModuleIdxFor? c | continue
    let modName := modNames[modIdx.toNat]!
    unless isReformulationModule modName do continue
    considered := considered + 1
    let axs ← collectAxioms c
    if axs.contains ``sorryAx then
      sorryHolders := sorryHolders.insert c
  -- Verstoß-Prüfung: sorryAx-Träger, die nicht gewhitelistet sind.
  let violations := sorryHolders.toArray.filter (fun n => !whitelistSet.contains n)
  -- Stale-Prüfung: gewhitelistete Namen, die keinen sorryAx (mehr) ziehen / fehlen.
  let stale := whitelist.filter (fun n => !sorryHolders.contains n)
  if !violations.isEmpty then
    throwError m!"AXIOM-GATE ROT — neue, nicht-gewhitelistete sorryAx-Träger im Aggregat \
      Reformulation ({violations.size}):\n{violations.qsort Name.lt}\n\
      Entweder die Lücke schließen oder (falls bekannte Klasse-D-Lücke) bewusst in \
      Reformulation.AxiomGate.whitelist aufnehmen."
  if !stale.isEmpty then
    throwError m!"AXIOM-GATE ROT — obsolete Whitelist-Einträge in \
      Reformulation.AxiomGate.whitelist ({stale.size}): {stale.qsort Name.lt}\n\
      Diese Konstanten ziehen kein sorryAx (mehr) oder existieren nicht. Lücke \
      geschlossen ⇒ Eintrag aus der Whitelist entfernen (Whitelist nicht verrotten lassen)."
  logInfo m!"AXIOM-GATE GRÜN — Aggregat Reformulation ({considered} geprüfte \
    Konstanten) zieht sorryAx nur über die {whitelist.size} gewhitelisteten, \
    bekannten Klasse-D-Lücken:\n{sorryHolders.toArray.qsort Name.lt}"

end Reformulation.AxiomGate
