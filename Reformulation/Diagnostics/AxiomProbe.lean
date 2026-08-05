import Reformulation
import Lean

/-!
# Reformulation.Diagnostics.AxiomProbe — Engineering-Gates Phase-1-Diagnose

**Reine Bestandsaufnahme — kein Eingriff.** Diese Datei importiert das Aggregat
`Reformulation`, wird aber selbst NICHT in `Reformulation.lean` aufgenommen. Sie ist
Werkzeug, nicht Schicht.

Zweck: den tatsächlichen Axiom-Abschluss des Aggregats am Code feststellen
(zieht `sorryAx`? über welche Konstanten? welche benannten Axiome?) und zugleich
die K-G.1-Machbarkeit von `Lean.collectAxioms` als Gate-API prüfen.

Ausführen via `lake env lean Reformulation/Diagnostics/AxiomProbe.lean`.
-/

open Lean Elab Command

namespace Reformulation.Diagnostics

/-- Ein Modul gehört zum Aggregat-Codebestand, wenn sein Name `Reformulation` ist
oder mit `Reformulation.` beginnt. Schließt Mathlib/Lean/Std aus. -/
def isReformulationModule (m : Name) : Bool :=
  m == `Reformulation || (`Reformulation).isPrefixOf m

/-- Heuristik: ist `n` eine vom Compiler erzeugte Hilfs-Deklaration
(`match_`, `proof_`, `eq_`, `_cstage`, `.def`, `.eq_def`, …)? Nur für eine
zusätzliche „Wurzel-Sicht"; die vollständige Liste wird unabhängig davon gemeldet. -/
def isInternalName (n : Name) : Bool :=
  n.isInternal ||
  n.components.any (fun c =>
    let s := c.toString
    s.startsWith "_" ||
    "match_".isPrefixOf s || "proof_".isPrefixOf s ||
    s == "eq_def" || "eq_".isPrefixOf s || "rec".isPrefixOf s)

/-! **Teil 1 — Aggregat-weite Axiom-Diagnose via `Lean.collectAxioms`.**
Iteriert über alle Konstanten, die aus `Reformulation.*`-Modulen stammen, sammelt
für jede den Axiom-Abschluss und meldet: Gesamtzahl, `sorryAx`-Träger (vollständig),
sonstige nicht-Standard-Axiome, und die Menge aller benannten Axiome. -/
run_cmd do
  let env ← getEnv
  let modNames := env.allImportedModuleNames
  let standard : NameSet :=
    (({} : NameSet).insert ``propext).insert ``Classical.choice |>.insert ``Quot.sound
  let mut considered := 0
  let mut withSorry : Array Name := #[]
  let mut withSorryRoots : Array Name := #[]
  let mut allAxioms : NameSet := {}
  let mut nonStandard : NameSet := {}
  for (c, _info) in env.constants.toList do
    let some modIdx := env.getModuleIdxFor? c | continue
    let modName := modNames[modIdx.toNat]!
    unless isReformulationModule modName do continue
    considered := considered + 1
    let axs ← collectAxioms c
    for a in axs do
      allAxioms := allAxioms.insert a
      unless standard.contains a do nonStandard := nonStandard.insert a
    if axs.contains ``sorryAx then
      withSorry := withSorry.push c
      unless isInternalName c do withSorryRoots := withSorryRoots.push c
  logInfo m!"════════ TEIL 1 — AGGREGAT-AXIOM-DIAGNOSE (collectAxioms) ════════"
  logInfo m!"Geprüfte Reformulation.*-Konstanten: {considered}"
  logInfo m!"Konstanten mit sorryAx im Abschluss (gesamt, inkl. intern): {withSorry.size}"
  logInfo m!"davon Wurzel-Deklarationen (ohne Compiler-Hilfen): {withSorryRoots.size}"
  let verdict := if withSorry.isEmpty then "NEIN" else "JA"
  logInfo m!"ZIEHT DAS AGGREGAT sorryAx? {verdict}"
  logInfo m!"──── sorryAx-Träger (Wurzel-Deklarationen) ────\n{withSorryRoots.qsort Name.lt}"
  logInfo m!"──── ALLE sorryAx-Träger (inkl. interne Hilfsdeklarationen) ────\n{withSorry.qsort Name.lt}"
  logInfo m!"──── Alle im Aggregat auftretenden Axiome ────\n{allAxioms.toArray.qsort Name.lt}"
  logInfo m!"──── davon NICHT-Standard (≠ propext/Classical.choice/Quot.sound) ────\n{nonStandard.toArray.qsort Name.lt}"

end Reformulation.Diagnostics

/-! ## Teil 1 (Fallback) — verdächtige Schlüssel-Konstanten einzeln -/

-- Bekanntes `sorry` (Klasse-D) an der invarianten Schicht:
#print axioms Reformulation.F3e.beckChevalleyFromData

-- Proemial-γ-Sätze, die BeckChevalley referenzieren:
-- Bis Zug A (5. August 2026) hiess dieser Satz `beck_chevalley_verschraenkung`.
#print axioms Reformulation.Proemial.pbv_gamma_isIso
-- (Sorry-Konsolidierung γ-V: `beck_chevalley_verschraenkung_substantial` entfernt —
--  veraltete F-3-Stub-Parallelform; Substanz sorry-frei in `…truly_substantial` unten.)

-- „Eigenständige BC-Konstruktion" (laut Doc „γ-V ohne Sorry"): prüfen, ob der
-- Axiom-Abschluss das wirklich bestätigt.
#print axioms Reformulation.Proemial.Substantial.BeckChevalley.beck_chevalley_verschraenkung_truly_substantial

-- Kontrast: bekannt sauberer Satz — sollte nur propext/Classical.choice/Quot.sound ziehen.
#print axioms Reformulation.Kenogram.soundness
