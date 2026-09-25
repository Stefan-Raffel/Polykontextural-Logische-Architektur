import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.CategoryTheory.RegularCategory.Basic
import Mathlib.CategoryTheory.FiberedCategory.Cartesian
import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
import Mathlib.Order.Partition.Finpartition
import Mathlib.CategoryTheory.Subobject.Classifier.Defs

/-!
# MathlibNameGuard — die Mathlib-Namen der Kommentar-Anker, beim Mathlib-Bump gebaut

**Benennung, keine Ertragsdatei.** Diese Datei enthaelt keinen Satz und keine Definition.
Kommentare im Bestand verankern Mathlib-Deklarationen ueber ihren Namen (Ankerregel, Mathlib-
Form, Custos U3/SV7). Die Datei nennt jeden dieser Namen einmal als Term. Loest ein Name nicht
mehr auf, bricht `lake build MathlibNameGuard`.

**Nicht im Default-Bau** (Architekt-Entscheid C, 26.9.2026): Namen aendern sich nur mit
Mathlib. Das Target wird beim Mathlib-Bump gefahren: `lake build MathlibNameGuard`.

**Ein Bruch hier heisst: die Verweise nachfuehren.** Den neuen Namen am Mathlib-Quelltext bzw.
mit `#check` bestimmen, ihn hier und an jeder Stelle der Tafeln eintragen. Nicht die Zeile hier
loeschen, damit der Bau wieder gruen wird.

## Vom Elaborator erzeugte Namen (anonyme Instanzen, aendern sich mit der Signatur)

| Name | verwiesen in |
|---|---|
| `CategoryTheory.Adjunction.instIsIsoFunctorCounitOfIsEquivalence` | `Proemial/AlphaGammaSubstantial.lean:389` |
| `CategoryTheory.instHasSheafifyType` | `MathlibExtensions/Sites/SheafAdjunction.lean:46`, `:53` |
| `CategoryTheory.Subobject.instCompleteLattice` | `MathlibExtensions/Topos/Subobject/Lattice.lean:20` |

## Vom Autor vergebene Namen

| Name | verwiesen in |
|---|---|
| `CategoryTheory.Functor.IsEquivalence` | `Proemial/AlphaGammaSubstantial.lean:30` |
| `CategoryTheory.NatIso.isIso_app_of_isIso` | `Proemial/AlphaGammaSubstantial.lean:393` |
| `Finpartition.card_mono` | `Kenogram/PartitionDescent.lean:46` |
| `Finpartition.card_parts_le_card` | `Kenogram/PartitionDescent.lean:47` |
| `CategoryTheory.Regular.hasStrongEpiMonoFactorisations` | `MathlibExtensions/Topos/Regular.lean:47` |
| `CategoryTheory.Limits.has_smallest_coproducts_of_hasCoproducts` | `MathlibExtensions/Topos/Subobject/Lattice.lean:63` |
| `CategoryTheory.Adjunction.right_triangle_components` | `Proemial/AlphaGammaSubstantialRefined.lean:27` |
| `CategoryTheory.Iso.inv_hom_id_app` | `Proemial/AlphaGammaSubstantialRefined.lean:30` |
| `CategoryTheory.Limits.pullback.isIso_diagonal_iff` | `Proemial/AlphaGammaRelPullback.lean:34` |
| `CategoryTheory.Functor.IsStronglyCartesian.of_iso` | `Proemial/CartesianProbe.lean:57` |
| `CategoryTheory.Subobject.Classifier` | `Proemial/ExtensionalCollapse.lean:58` |

Gemessen an Mathlib 83a5988 (2026-05-05). Eigenes Target `MathlibNameGuard`, nicht in
`defaultTargets` (lakefile.toml); vom Aggregat nicht importiert, vom AxiomGate nicht gefasst.
-/

-- `noncomputable section`: `Subobject.instCompleteLattice` ist in Mathlib noncomputable.
noncomputable section

example := @CategoryTheory.Adjunction.instIsIsoFunctorCounitOfIsEquivalence
example := @CategoryTheory.instHasSheafifyType
example := @CategoryTheory.Subobject.instCompleteLattice

example := @CategoryTheory.Functor.IsEquivalence
example := @CategoryTheory.NatIso.isIso_app_of_isIso
example := @Finpartition.card_mono
example := @Finpartition.card_parts_le_card
example := @CategoryTheory.Regular.hasStrongEpiMonoFactorisations
example := @CategoryTheory.Limits.has_smallest_coproducts_of_hasCoproducts
example := @CategoryTheory.Adjunction.right_triangle_components
example := @CategoryTheory.Iso.inv_hom_id_app
example := @CategoryTheory.Limits.pullback.isIso_diagonal_iff
example := @CategoryTheory.Functor.IsStronglyCartesian.of_iso
example := @CategoryTheory.Subobject.Classifier

end
