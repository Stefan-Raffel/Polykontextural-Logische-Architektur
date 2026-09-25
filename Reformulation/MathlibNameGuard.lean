import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Subobject.Lattice

/-!
# MathlibNameGuard — drei vom Elaborator erzeugte Mathlib-Namen, vom Bau bewacht

**Benennung, keine Ertragsdatei.** Diese Datei enthaelt keinen Satz und keine Definition.
Kommentare im Bestand verankern drei Mathlib-Instanzen ueber ihren Namen (Ankerregel, Mathlib-
Form, Custos U3/SV7). Die drei Instanzen sind in Mathlib **anonym** deklariert; ihr Name ist
vom Elaborator aus der Signatur erzeugt und kann sich bei einem Mathlib-Wechsel still aendern.
Damit ein solcher Wechsel nicht still einen Kommentar entwertet, nennt diese Datei jeden Namen
einmal als Term. Loest ein Name nicht mehr auf, bricht der Bau.

| Name | verwiesen in |
|---|---|
| `CategoryTheory.Adjunction.instIsIsoFunctorCounitOfIsEquivalence` | `Proemial/AlphaGammaSubstantial.lean:389` |
| `CategoryTheory.instHasSheafifyType` | `MathlibExtensions/Sites/SheafAdjunction.lean:46`, `:53` |
| `CategoryTheory.Subobject.instCompleteLattice` | `MathlibExtensions/Topos/Subobject/Lattice.lean:20` |

Gemessen an Mathlib 83a5988 (2026-05-05).

**Ein Bruch hier heisst: die Verweise nachfuehren.** Den neuen Namen am Mathlib-Quelltext bzw.
mit `#check` bestimmen, ihn hier und an jeder Stelle der Tafel eintragen. Nicht die Zeile hier
loeschen, damit der Bau wieder gruen wird.

Eigenes Target `MathlibNameGuard` in `defaultTargets` (lakefile.toml); vom Aggregat nicht
importiert, vom AxiomGate nicht gefasst.
-/

-- `noncomputable section`: `Subobject.instCompleteLattice` ist in Mathlib noncomputable.
noncomputable section

example := @CategoryTheory.Adjunction.instIsIsoFunctorCounitOfIsEquivalence
example := @CategoryTheory.instHasSheafifyType
example := @CategoryTheory.Subobject.instCompleteLattice

end
