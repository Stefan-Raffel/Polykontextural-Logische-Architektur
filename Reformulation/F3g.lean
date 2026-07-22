import Reformulation.F3g.TransitionClass
import Reformulation.F3g.Availability
import Reformulation.F3g.Classification
import Reformulation.F3g.Anschluss
import Reformulation.F3g.Quine
import Reformulation.F3g.Demo

/-!
# F3.g — Finite combinatorics of the iteration stages

This module carries the stage modulation of the four-class transition
classification (Path D: T1b III, T5 V–VI, T8 III).

## Four substantive aspects

* **Class availability per stage** (F3g.Availability):
  four classes in stage 1; three (II–IV) in stages n > 1.
* **ClassIV ω sub-differentiation** (F3g.Availability):
  initialising / continuing, available in stages n > 1.
* **B6 from B2** (F3g.Classification):
  `StageTransitionWithB6Trace` — additive extension of `StageTransition`
  with explicit ω-initialisation field.
* **Quine convergence** (F3g.Quine):
  protosyntactic stage 1 (class I available) ↔ syntactic stages n > 1
  (class I unavailable; ω is B6-initialised).

## Connection modules

* **F3g.Anschluss**: coherence between class availability, K-configurations
  (F3.b), stage-1 K1-anchoring (F3.f), and the B6-trace extension.
* **F3g.Demo**: trivial-domain realisability demonstration for
  `StageTransitionWithB6Trace` (non-empty; `Discrete PUnit` instantiation).

## Connection to prior F-modules

- F3.b: K-configurations (K1–K8) and class assignments.
- F3.f: `Stage`, `StageTransition` (base classes extended here).
-/
