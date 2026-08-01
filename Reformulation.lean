-- Reformulation of Günther's polycontextural logic
--
-- This library provides the formal underpinnings for the reformulation
-- carried out in the structural and applied phases of the project:
--
-- * F3.b — combinatorial tableau of the four-class transition classification
-- * F3.c — modal 2-category with smoothness predicate and (non-)existence
--          statements for canonical 2-morphisms
-- * F3.a — endofunctor construction with stage-modulated form and four
--          constituents (Endofunctor, Valuation, SchemaMorphism,
--          DoubleValuation)
-- * F3.d — triple context-negation as extension of the modal 2-category;
--          ModalTwoCategoryWithNegations, Hypostatization, En/NEn theorems
-- * F3.e — Beck-Chevalley enforcement as constructive consequence;
--          ModalTwoCategoryWithPullbacks, BeckChevalleyAxioms,
--          beckChevalleyFromData, Existence/Uniqueness/ModalCompat theorems
-- * F3.g — finite combinatorics of the iteration stages (Path D);
--          TransitionClass, class availability, ClassIV sub-differentiation,
--          StageTransitionWithB6Trace, Quine convergence
--
-- The structural-phase architecture (modal triad τ, δ, ω; cyclic δ-bound
-- entanglement; double fibration 𝒯 → 𝒞 × 𝒪; structural conditions B1–B6;
-- Beck-Chevalley; three-class composition structure; cumulative iteration;
-- vierfachklassifikation of transitions) is reflected here in formal
-- Lean form, with Mathlib as the supporting library.
--
-- The schicht-aufteilung over the F3 modules:
-- * F3.b and F3.c carry the invariant layer.
-- * F3.a carries the stage-modulated layer.
-- * F3.d extends the invariant layer with context-negations.
-- * F3.e extends the invariant layer with pullback-compatibility and BC.
-- * F1 (partially formalized in D2, D5) carries the local layer.
-- * Proemial — α+γ-Form der Proemialrelation; ProemialAdjunction (α),
--   ProemialBeckChevalleyVerschraenkung (γ, Lesart B); F-1-Niederlegung.
--
-- See the project documents (Sitzungsprotokolle T1a–T12, F2_Schema,
-- F2_Kommentar, the F3.a / F3.b / F3.c Klärung-Spec-Implementation triples)
-- for the structural background.

import Reformulation.F3b
import Reformulation.F3c
import Reformulation.F3a
import Reformulation.F3d
import Reformulation.F3e
import Reformulation.F3f
import Reformulation.F3g
import Reformulation.F1
import Reformulation.Proemial
import Reformulation.Kenogram.Basic
import Reformulation.Kenogram.Stream
import Reformulation.Kenogram.Bridge
import Reformulation.Kenogram.Operational
import Reformulation.Kenogram.Morphogram
