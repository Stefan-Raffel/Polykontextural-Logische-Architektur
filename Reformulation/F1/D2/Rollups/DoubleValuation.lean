import Reformulation.F1.D2.Rollups.RollupGeneral
import Reformulation.F1.D2.Rollups.Families
import Reformulation.F3a

/-!
# F1.D2.Rollups.DoubleValuation — Sub-layer 3: double-valuation-specific

Introduces RollupCompatibility and the two connection functions as
third belegungen of F3.a placeholders. Contains Central Theorem 2.

Structural content:
* `RollupCompatibility` — cross-stage compatibility for layer-1/layer-2
  double valuations. Hybrid form: beckChevalleyHolds placeholder plus
  a verifiableOnLayer1 predicate (trivially satisfiable via ℕ abstraction).
* `rollup_doubleValuation_inheritance` — Central Theorem 2: formal form
  of "Layer-1 trägt, Layer-2 baut auf" — vertical-asymmetric stage iteration.

The two connection functions into the F3.a placeholders were removed in the
Phase-2 sharpening; see the memorial block at the end of this module, which also
records what the three-fold belegung did and did not show. Central Theorem 2 is
unaffected — it states an equation over `inheritanceCompat`, not a placeholder.

See F1_D2_Rollups_Spec.md §IV, §VIII.
-/

namespace Reformulation.F1.D2.Rollups.DoubleValuation

open Reformulation.F1.D2.Rollups.RollupGeneral
open Reformulation.F1.D2.Rollups.Families
open Reformulation.F3a

/-- Rollup compatibility: cross-stage compatibility for layer-1/layer-2
double valuations. Hybrid form: a placeholder for the full pull-back form
(beckChevalleyHolds : True), plus a verifiability predicate that captures
the structural soundness of stage-iteration.

The verifiableOnLayer1 predicate abstracts over concrete transaction
representations via ℕ. The concrete form is per-family: validity proof
(zkRollup, validium), challenge mechanism (optimisticRollup), or
data-availability witness (sovereign). A concrete RollupCompatibility
instance with engineering data is follow-on work. -/
structure RollupCompatibility (rdv : RollupDoubleValuation) where
  /-- The Beck-Chevalley witness for stage-iteration compatibility (placeholder). -/
  beckChevalleyHolds : True
  /-- Verifiability: every transaction state on layer-2 has a verification
  path to layer-1. Abstracted over concrete transactions via ℕ.
  Trivially satisfiable: choose verificationPath = 0. -/
  verifiableOnLayer1 : ∀ (_ : ℕ),
    ∃ (verificationPath : ℕ), verificationPath ≥ 0

/-- Central F1.D2.Rollups Theorem 2: in any rollup double valuation, the
layer-2's parent layer-1 equals the double valuation's layer-1. Formal form
of "Layer-1 trägt, Layer-2 baut auf" — the vertical-asymmetric structure of
stage iteration.

Methodological parallel to polkadot_doubleValuation_asymmetric in
F1.D5.Polkadot, but with different asymmetry character: rollup is
vertical-iterative (stage iteration from layer-1 to layer-2), polkadot
is spatially-asymmetric (parachains depending on relay-chain in the
same reflection-space set). -/
theorem rollup_doubleValuation_inheritance (rdv : RollupDoubleValuation) :
    rdv.layer2.parentLayer1 = rdv.layer1 :=
  rdv.inheritanceCompat

/-! ## Memorial block: declarations removed because their statement was `True`

Removed in the Phase-2 sharpening (Setzungsregister, `docs/status-register.md`).
The name claimed content, the statement was `True`. No consumer in the aggregate;
the removal breaks nothing.

Signatures are quoted indented by two spaces so that the counting route `^def`
does not count the memorial quote as a declaration.

**Removed 1 — `RollupDoubleValuation.toDoubleValuationCompat`.** Register `S47`.

```
  def RollupDoubleValuation.toDoubleValuationCompat
      (_r : RollupDoubleValuation) : True :=
    trivial
```

**Removed 2 — `RollupCompatibility.toBeckChevalley`.** Register row `S48`.

```
  def RollupCompatibility.toBeckChevalley
      {rdv : RollupDoubleValuation} (_c : RollupCompatibility rdv) : True :=
    trivial
```

*What was claimed:* that rollups fill two F3.a placeholders —
`DoubleValuation.compatibility` (register row `S15`) and
`DesignativeRestriction.beckChevalley` (register row `S14`) — each for the third
time in the project, in vertically asymmetric stage-iteration form.
*What a load-bearing statement would need:* both target fields must carry
content. A function into `True` establishes no connection, since every term of
every type maps to `trivial`; that is why the same two placeholders could be
filled three times without any of the three constructions meeting resistance.

### What the three-fold belegung did and did not show

This is the one place where the observation is recorded, so that it is not
repeated across the six modules that carried the connection functions.

The doc-strings of the removed functions read as a series: each placeholder was
filled three times, and the three fillings differ in structural form —

* `compatibility`: symmetric (Ethereum, FFG-Lock within one chain), spatially
  asymmetric (Polkadot, relay-chain inclusion between chains), vertically
  asymmetric (rollups, stage iteration between layer-1 and layer-2);
* `beckChevalley`: light-client pull-back (IBC), relay-chain mediation (XCM),
  stage-verification pull-back (rollups).

The series is a real observation, and it is an observation **about the
modelling, not about the calculus**. It says that three engineering mechanisms
of visibly different shape were each expressible as a filling of the same F3.a
form. It does not say that the F3.a form is multiply satisfiable in any
load-bearing sense — with the field typed `True`, satisfiability is not at
stake, and no filling could have failed. The earlier wording "the F3.a form is
multiply multi-belegbar, not only doubly" claimed the latter from evidence for
the former. It is retained here in the weaker and correct reading, and it is
what the placeholders would have to be given content to make testable.
-/

end Reformulation.F1.D2.Rollups.DoubleValuation
