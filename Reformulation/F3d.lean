-- F3.d — Triple context-negation as extension of the modal 2-category.
--
-- Reformulation-Verweis: F3d_Spec.md, F3d_Implementation_Final.md.
-- Follows from clarification sessions K1 (context-negation and modal
-- triad — relation and localization) and K2 (classification question).
--
-- Architecture:
-- * The three context-negations ¬_τ, ¬_δ, ¬_ω are *aspects* of the
--   modal triad (τ, δ, ω), not independent architecture (K2 §III.4).
-- * They are formalized as additional endo-functors in an extended
--   structure class `ModalTwoCategoryWithNegations` (F3d.Negations),
--   together with their compatibility data and the hypostatization-
--   diagnosis form (F3d.Hypostasis, F3d.Theorems).
-- * `ModalSymbol` and `IsSmooth` are extended in-place in F3.c
--   (Reformulation.F3c.Symbols) to carry the negation symbols
--   syntactically, reusing the established smoothness machinery.
--
-- Build-Reihenfolge: F3.b → F3.c (with extension) → F3.d → F1.D*

import Reformulation.F3d.Negations
import Reformulation.F3d.Hypostasis
import Reformulation.F3d.Theorems
