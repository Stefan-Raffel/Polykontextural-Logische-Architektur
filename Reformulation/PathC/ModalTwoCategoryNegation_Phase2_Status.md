# ModalTwoCategoryNegation — Phase 2 Status

*Reformulation.PathC.ModalTwoCategoryNegation (Phase 2 additions)*
*Datum: 2026-05-17*

---

## (i) Kompilierungs-Status

Build-Ergebnis:

```
⚠ [1265/1265] Built Reformulation.PathC.ModalTwoCategoryNegation (1.6s)
warning: declaration uses `sorry`
Build completed successfully (1265 jobs)
```

1 sorry — Theorem 2b, wie spezifiziert (§IV Empfohlene Wahl: Option C).
Keine weiteren Errors.

**Sub-Aufgaben im Einzelnen:**

| Sub-Aufgabe | Status |
|-------------|--------|
| Datei-Anschluss (Aufgabe 1) | ✓ gleiche Datei |
| `ModalSymbol` (6 Konstruktoren, deriving) | ✓ kompiliert |
| `Komposition` (3 Konstruktoren, deriving) | ✓ kompiliert |
| `ModalSymbol.interpret` | ✓ kompiliert |
| `Komposition.interpret` | ✓ kompiliert |
| `classifyKomposition` | ✓ kompiliert (alle Klauseln + catch-all) |
| Theorem 1a (total) | ✓ 0 sorries |
| Theorem 1b (unique) | ✓ 0 sorries |
| Theorem 1c (surjective) | ✓ 0 sorries |
| Theorem 2a (simplified) | ✓ 0 sorries |
| Theorem 2b (with separation) | ✓ 1 sorry (offene Folge-Substanz) |

**Theorem-Status:**

| Theorem | Lean-Beweis-Form | Sorries |
|---------|-----------------|---------|
| 1a (total) | `fun k => ⟨classifyKomposition k, rfl⟩` | 0 |
| 1b (unique) | `fun _ _ _ h₁ h₂ => h₁.symm.trans h₂` | 0 |
| 1c (surjective) | `cases c` + `exact ⟨zeuge, rfl⟩` pro Klasse | 0 |
| 2a (simplified) | `Functor.isoWhiskerRight isoDelta.symm M.delta).trans + noResolutionLeft` | 0 |
| 2b (with separation) | iso-Transport via `isoWhiskerRight isoTau M.tau` + `hSingleInvol` | 1 |

---

## (ii) Mathlib API-Lücken

**B-3/Phase2 — `Functor.isoWhiskerRight` (nicht `isoWhiskerRight`).**

`isoWhiskerRight` ist in `CategoryTheory.Functor`-Namespace definiert
(`Mathlib/CategoryTheory/Whiskering.lean:243`). Mit `open CategoryTheory` allein
nicht zugänglich — `Functor.isoWhiskerRight` muss explizit qualifiziert werden.

Zusätzlicher Import `Mathlib.CategoryTheory.Whiskering` erforderlich — nicht
transitiv über die bestehenden Imports verfügbar.

Kein `TODO Mathlib API:` — das ist ein Namens- und Import-Befund, kein
API-Lücken-Befund. Die Funktion existiert in Mathlib, sie muss nur korrekt
qualifiziert werden.

---

## (iii) Aufwands-Empirie

**Antizipierter Aufwand:** 1 Sitzung (§VI.2 Spec).

**Tatsächlicher Aufwand:** ¼ Sitzung — erheblich unter Antizipation.

Begründung: Strategie-C-Wahl (Drei-Konstruktor-Typ statt List-Induktion)
eliminiert die antizipierte Lean-Komplexität vollständig. Alle Theorem-1-Beweise
tragen `rfl`-Zeugen. Theorem 2a schließt in zwei Takt-Schritten
(`apply noResolutionLeft; exact ⟨iso-Konstruktion⟩`).

Spec-Antizipations-Treffer: die Strategie-C-Wahl hat sich als metodologisch
korrekt erwiesen — keine ζ-Charakteristik, keine Sub-Befund-Kaskade.

---

## (iv) Sorry-Markierungen

1 sorry — Theorem 2b (`subjectstellen_differentiation_with_separation`).

Position: Argument vom Typ `Nonempty ((negUnified ⋙ M.delta) ≅ 𝟭 T)` an
`hSingleInvol negUnified hTauInvol`. Dieses Sorry ist nicht durch
`NegDeltaRoughness + isoDelta` schließbar — `isoDelta : negUnified ≅ M.negDelta`
und `hNegDeltaRough.noResolutionLeft` zusammen geben nur
`¬ Nonempty ((M.negDelta ⋙ M.delta) ≅ 𝟭 T)`, nicht die positive Iso-Konstruktion.

---

## (v) TODO Mathematician-Markierungen

1 TODO Mathematician — im Docstring von Theorem 2b sowie im Proof-Body.

**Inhalt:** Full proof requires structural separation axiom for τ and δ beyond
the current ModalTwoCategory fields; `isoDelta` alone yields
`¬ Nonempty ((M.negDelta ⋙ M.delta) ≅ 𝟭 T)` from roughness, not the positive
`Nonempty` needed to close the contradiction with `hSingleInvol`.

**Folge-Konsequenz:** Theorem 2c (vollständige Subjektstellen-Differenzierung
ohne zusätzliche Hypothesen) bleibt offene Phase-3-Folge-Substanz.

---

## Eingangsmarkierung für Phase 3

**Phase 3 baut auf:**
- `NegationCompositionClass` (Phase 1)
- `MixedCompositionClass` (Phase 1)
- `ModalTwoCategoryWithNegations` (Phase 1)
- `Komposition` und `classifyKomposition` (Phase 2)

**Phase 3 tragt:**
- `MixedCompositionClass`-Klassifikations-Funktion mit Hypostasierungs-Parameter
- `DeltaHypostatization`, `TauHypostatization`, `OmegaHypostatization` als Prop-Klassen
- Theorem 3 (Hypostasierungs-Charakterisierung) als bidirektionale Implikation

**Methodologische Vorab-Beobachtung:** Theorem 2b-sorry deutet darauf hin,
dass Phase 3 für Theorem 2c eine explizite `ModalTwoCategory`-Erweiterung
um einen Operator-Separations-Axiomsatz braucht, oder dass Theorem 2c
als Domain-Studien-Substanz (D7/D8/D9) niedergelegt wird.
