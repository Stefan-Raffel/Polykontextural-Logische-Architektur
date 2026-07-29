import Reformulation.F1.D5.MultiChainGeneral

/-!
# F1.D5.IBC — Sub-layer 2: IBC-specific types and cross-chain compatibility

Introduces the IBC-specific data types and the central cross-chain
compatibility structure. Engineering anchor: Cosmos IBC.

Structural content:
* `Header` — light-client header from a source chain, carrying height
  and block hash. Structurally: the pull-back operation on the δ-axis.
* `Packet` — cross-chain packet with sequence number for replay
  protection (B5/B6 belegung in the cross-chain stratum).
* `Header.isVerifiable` — light-client verification predicate.
  Returns `True` as a placeholder; the cryptographic realization
  (signature schemes, Merkle proofs) is local-stratum-3 material.
* `CrossChainCompatibility` — 2-categorical Beck-Chevalley structure
  for a connection. Hybrid form: `beckChevalleyHolds : True` as
  placeholder plus provable `replayProtection` predicate.

The connection function to the F3.a `DesignativeRestriction.beckChevalley`
placeholder was removed in the Phase-2 sharpening; see the memorial block at the
end of this module. What this module carries is `replayProtection`, a provable
predicate, and that stays.

See F1_D5_Spec.md §III (Sub-Schicht 2: IBC-spezifisch), T10 IV.
-/

namespace Reformulation.F1.D5.IBC

open Reformulation.F1.D5.MultiChainGeneral

/-- A light-client header from a source chain, to be verified in a
target chain. Structurally: the pull-back operation on the δ-axis. -/
structure Header where
  sourceChain : Chain
  height      : ℕ
  blockHash   : ℕ
  deriving DecidableEq

/-- A cross-chain packet carrying data from one chain to another.
The sequence number provides replay-protection (B5/B6 belegung in
the cross-chain stratum). -/
structure Packet where
  connection : Connection
  sequence   : ℕ
  data       : ℕ
  deriving DecidableEq

/-- Light-client verification predicate. Abstracts the cryptographic
verification (signature schemes, Merkle proofs); the concrete
realization is local-stratum-3 material (a future
F1.D5.IBC.Tendermint sub-belegung). -/
def Header.isVerifiable (_h : Header) : Prop := True

/-- 2-categorical Beck-Chevalley compatibility for a connection.
Hybrid form: a placeholder for the full pull-back form
(`beckChevalleyHolds : True`), plus a provable replay-protection
predicate (`replayProtection`). -/
structure CrossChainCompatibility (conn : Connection) where
  /-- The Beck-Chevalley witness for cross-chain pull-back
  compatibility. Placeholder per the prop_field : True convention. -/
  beckChevalleyHolds : True
  /-- Replay-protection: each packet has a unique sequence in its
  connection. This is the B5/B6 condition in the cross-chain stratum,
  formulated as a provable predicate. -/
  replayProtection : ∀ (p₁ p₂ : Packet),
    p₁.connection = conn → p₂.connection = conn →
    p₁.sequence = p₂.sequence → p₁ = p₂

/-! ## Memorial block: declaration removed because its statement was `True`

Removed in the Phase-2 sharpening (Setzungsregister, `docs/status-register.md`).
The name claimed content, the statement was `True`. No consumer in the aggregate;
the removal breaks nothing.

Signature quoted indented by two spaces so that the counting route `^def` does
not count the memorial quote as a declaration.

**Removed — `CrossChainCompatibility.toBeckChevalley`.** Register row `S44`.

```
  def CrossChainCompatibility.toBeckChevalley
      {conn : Connection} (_c : CrossChainCompatibility conn) : True :=
    trivial
```

*What was claimed:* that IBC cross-chain compatibility fills the F3.a
`DesignativeRestriction.beckChevalley` placeholder — the first of three
belegungen of that placeholder in the project, in light-client form.
*What a load-bearing statement would need:* the target field
`F3a.DesignativeRestriction.beckChevalley` (register row `S14`) must carry an
actual 2-isomorphism instead of `True`; a function into `True` establishes no
connection, since every term of every type maps to `trivial`. Once the field has
content, filling it becomes a construction that can fail — and then the
observation that three structurally different mechanisms fill it (see the
memorial block in `F1/D2/Rollups/DoubleValuation.lean`) would say something.
Here the local material that could feed such a construction is `Header` with
`height` and `blockHash`, plus `replayProtection`, which stays.
-/

end Reformulation.F1.D5.IBC
