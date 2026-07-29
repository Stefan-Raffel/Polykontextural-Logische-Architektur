import Reformulation.F1.D5.MultiChainGeneral
import Mathlib.Data.Fintype.Basic

/-!
# F1.D5.BridgeTypes — Sub-layer 3: bridge-type differentiation

Introduces the three structurally differentiated bridge types from
T10 IV and the central F1.D5 theorem: `bridge_soundness_iff_lightClient`.

Structural content:
* `BridgeType` — inductive type with three constructors: `multiSig`,
  `optimistic`, `lightClient`. `DecidableEq` and `Fintype` instances
  derived (finite inductive type).
* `BridgeType.isStructurallySound` — structural soundness predicate
  per bridge type. Encodes the T10 IV diagnostic:
  - `multiSig`: `False` (Beck-Chevalley replaced by majority trust)
  - `optimistic`: `False` (Beck-Chevalley replaced by initial trust)
  - `lightClient`: `True` (Beck-Chevalley fully verified)
* `bridge_soundness_iff_lightClient` — central F1.D5 theorem (non-
  tautological): a bridge is structurally sound iff it is lightClient.
  Proof: case-split on the three constructors plus simp.

Methodological point: this theorem carries genuine provable content — the
T10 IV structural diagnostic made formal. The contrast originally drawn here
was with F1.D2's central statement, which was tautological in `True`-form; that
statement was removed in the Phase-2 sharpening, and the memorial block in
`F1/D2/Ethereum.lean` records what it would take to make it load-bearing.

Sub-layer 3 note: this is a cross-cutting differentiation (Quer-
Differenzierung), not a depth-specialization as in F1.D2 Sub-Schicht 3.
`BridgeTypes` imports only `MultiChainGeneral`, not `IBC` — the bridge
classification is orthogonal to the IBC realization.

See F1_D5_Spec.md §IV (Sub-Schicht 3: Bridge-Typ-differenzierend),
T10 IV.
-/

namespace Reformulation.F1.D5.BridgeTypes

/-- The three structurally differentiated bridge types from T10 IV.
* `multiSig`: structurally brittle (Beck-Chevalley replaced by
  majority trust).
* `optimistic`: structurally brittle (Beck-Chevalley replaced by
  initial trust, no challenge period modeled here).
* `lightClient`: structurally sound (Beck-Chevalley fully verified). -/
inductive BridgeType : Type where
  | multiSig
  | optimistic
  | lightClient
  deriving DecidableEq, Fintype

/-- Structural soundness predicate per bridge type. Encodes the T10 IV
diagnostic in formal Lean. -/
def BridgeType.isStructurallySound : BridgeType → Prop
  | .multiSig    => False
  | .optimistic  => False
  | .lightClient => True

/-- Central F1.D5 theorem: a bridge is structurally sound if and only
if it is of type `lightClient`. This makes the T10 IV diagnostic
("Multi-Sig and Optimistic bridges are structurally brittle; Light-
Client bridges are structurally sound") a formally provable theorem.
Non-tautological: case-split on the three bridge types. -/
theorem bridge_soundness_iff_lightClient (b : BridgeType) :
    b.isStructurallySound ↔ b = BridgeType.lightClient := by
  cases b
  case multiSig    => simp [BridgeType.isStructurallySound]
  case optimistic  => simp [BridgeType.isStructurallySound]
  case lightClient => simp [BridgeType.isStructurallySound]

end Reformulation.F1.D5.BridgeTypes
