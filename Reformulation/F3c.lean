-- F3.c — Modal 2-category with smoothness predicate and canonical
-- (non-)existence statements for 2-morphisms.
--
-- Reformulation-Verweis: Klärungs-Sitzungen 1, 2, 3 (F3c_Klaerung_*.docx)
-- und F3c_Spec.docx. Strukturmerkmale:
--
-- * τ, δ, ω as endo-functors on a base category 𝒯 (ModalOperators);
-- * cyclic δ-bound entanglement, formalized as compatibility data on
--   ω∘τ∘δ and τ∘ω∘δ (ModalTwoCategory);
-- * four-class refinement of the three-class composition structure
--   (trivial, asymmetric-smooth, smooth-with-compatibility-datum, rough),
--   captured syntactically by the IsSmooth predicate on List ModalSymbol;
-- * five existence and five non-existence statements for canonical
--   2-morphisms (E1–E5, NE1–NE5).

import Reformulation.F3c.Symbols
import Reformulation.F3c.Operators
import Reformulation.F3c.TwoCategory
import Reformulation.F3c.Existence
import Reformulation.F3c.NonExistence
