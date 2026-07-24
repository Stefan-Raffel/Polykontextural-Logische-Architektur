-- F3.e — Beck-Chevalley enforcement as constructive consequence.
--
-- Reformulation reference: F3e_Spec.md, F3e_Implementation_Final.md.
-- Follows from clarification sessions K1 (sources, readings, class question)
-- and K2 (classification decisions), plus the F3.e-Spec.
--
-- Architecture:
-- * The central enforcement claim: B5 plus modal 2-category plus
--   pull-back compatibility of modal operators jointly carry the 2-categorical
--   Beck-Chevalley compatibility as a constructive consequence (K2.1: Lesart C).
-- * `ModalTwoCategoryWithPullbacks` (F3e.ModalTwoCategoryWithPullbacks):
--   extends `ModalTwoCategoryWithNegations` (F3.d) with two pullback functors
--   ψ*, φ* and their modal compatibility NatIsos; B5-anchored via K.k1.
-- * `BeckChevalleyAxioms` (F3e.BeckChevalleyAxioms): prop_field-True
--   predicate for the standard 2-categorical BC conditions.
-- * `beckChevalleyFromData` (F3e.BeckChevalleyConstruction): the canonical
--   BC-NatIso, read off the structure field `pullBackCommute` (sorry-frei;
--   die belegungsspezifische Form bleibt F1-Material).
-- * Theorems (F3e.Theorems): existence, modal compatibility, B5-anchoring.
--   (`beckChevalley_unique` gestrichen — Whitelist-Auflösung 24. Juli 2026.)
--
-- Whitelist-Auflösung (24. Juli 2026): das Aggregat zieht kein `sorryAx` mehr;
-- die vier vormaligen Klasse-D-Einträge sind geschlossen bzw. gestrichen.
--
-- Build-Reihenfolge: F3.b → F3.c (with F3.d extension) → F3.d → F3.e → F1.D*

import Reformulation.F3e.ModalTwoCategoryWithPullbacks
import Reformulation.F3e.BeckChevalleyAxioms
import Reformulation.F3e.BeckChevalleyConstruction
import Reformulation.F3e.Theorems
