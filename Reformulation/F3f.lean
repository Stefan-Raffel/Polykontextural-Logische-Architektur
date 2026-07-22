import Reformulation.F3f.Stage
import Reformulation.F3f.StageTransition
import Reformulation.F3f.QuineConvergence
import Reformulation.F3f.StageWithF3aAnchor

/-!
# F3.f: The coalgebraic stratum

Formal niederlegung der koalgebraischen Schicht der PKL-Architektur.
Trägt Stage, StageTransition, QuineConvergence und (Rev3) StageWithF3aAnchor.

## Architecture

* `Stage (n : ℕ)` (F3f.Stage): stage-local data — total-space category,
  stage object, stage-dependent end-functor, coalgebra structure γ,
  B5-anchoring, algebra-extension prohibition marker.
* `StageTransition (n : ℕ)` (F3f.StageTransition): inter-stage data —
  current Stage, next Stage, modally differentiated translation function.
* `quine_convergence_stage_1` (F3f.QuineConvergence): stage 1 carries
  the material-free K1 configuration (protosyntactic base).
* `StageWithF3aAnchor (n : ℕ)` (F3f.StageWithF3aAnchor): Rev3 additive
  extension — Stage extended with F3.a three-functor decomposition anchor.
  Used by F1 belegungen that want to track the F3.a structural components.

## Key architectural choices (Spec-Entscheidungen)

1. Generic endenFunktor (no F3.a dependency at invariant Stage layer).
2. noAlgebraExtension : True (prop_field-True marker).
3. Three base modules (Stage, StageTransition, QuineConvergence).
4. Rev3: StageWithF3aAnchor via `extends Stage` — purely additive.

## Build-Reihenfolge

F3.b → F3.c → F3.f.Stage → F3.f.StageTransition → F3.f.QuineConvergence →
F3.a → F3.f.StageWithF3aAnchor → F3.f → F1.D*

No sorry in F3.f modules (pre-existing sorry in F3.e not affected).
-/
