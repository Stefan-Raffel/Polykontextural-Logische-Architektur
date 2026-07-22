import Reformulation.PreC.SiteAnschluss
import Reformulation.PreC.GeometricMorphismMin

/-!
# Reformulation.PreC.PKLFormWahlen — Four form-choice demonstrations

Carries four form-choice demonstrations for the Pre-C tractability
demonstration. Each demonstration shows that a central architectural
form-choice of the PKL position is expressible in Lean's structure-class
and function system, using the Phase-A Mathlib connection.

The mathematical substance is minimal — trivial examples throughout —
because Pre-C is a tractability demonstration, not a full PKL formulation.
The form-choices carry ontological pointedness in their structural form,
not in their content.

## Form-choice 1: Topos-component pluralism

PKL's contexture plurality lives as a family of sheaf categories indexed
by `Fin n`. The fast-discrete structure is carried by the `ContextureSite`,
which admits only identity-covering sieves.

## Form-choice 2: Double fibration

The PKL doubling of contexture-axis (𝒯) and schema-axis (𝒪) lives as a
structure with two index counts plus a Belegungs-function. The
Belegungs-function is the sole interlocking datum between the two axes.

## Form-choice 3: translate as function between types (not functor)

The central form-choice of the coalgebraic layer: `translate` is a
function between types, NOT a functor between categories. This structural
form carries the algebra-prohibition.

## Form-choice 4: B5 as initial singularity

The conditional structure of stage 1: `initialConfig 1 = k1` is forced.
This carries B5 (asymmetry as source of the three asymmetries) structurally.
-/

namespace Reformulation.PreC.PKLFormWahlen

open CategoryTheory Reformulation.PreC

/-! ### Form-choice 1: Topos-component pluralism -/

/-- For `n = 3` (three contextures), the three components are accessible
    as parallel sheaf categories over the PKL site. -/
example : ContextureComponent 3 = Sheaf (ContextureSite 3) Type := rfl

/-! ### Form-choice 2: Double fibration -/

/-- Double fibration structure: two orthogonal index axes plus Belegungs-function.

    `𝒯` carries the ontological axis (contextures, indexed by `Fin contextureCount`).
    `𝒪` carries the operational axis (schemas, indexed by `Fin schemaCount`).
    The Belegungs-function is the only connecting datum between the two axes. -/
structure PKLDoubleFibration where
  contextureCount : Nat
  schemaCount : Nat
  /-- Belegungs-function: total-space type per contexture–schema pair. -/
  belegung : Fin contextureCount × Fin schemaCount → Type

/-- Trivial double fibration: three contextures, four schemas, Unit total-spaces. -/
def trivialDoubleFibration : PKLDoubleFibration where
  contextureCount := 3
  schemaCount := 4
  belegung := fun _ => Unit

/-! ### Form-choice 3: translate as function between types -/

/-- Modal symbol enumeration: the six values of the modal triad plus
    their negation aspects. Parallel to F3.f's ModalSymbol. -/
inductive PreCModalSymbol : Type where
  | tau     : PreCModalSymbol
  | delta   : PreCModalSymbol
  | omega   : PreCModalSymbol
  | negTau  : PreCModalSymbol
  | negDelta : PreCModalSymbol
  | negOmega : PreCModalSymbol
  deriving DecidableEq, Repr

/-- `translate` as a function between types, parametrised in a modal mode.

    This is a function between types, NOT a functor between categories.
    The structural form carries the algebra-prohibition: translate has no
    functorial obligation (no identity law, no composition law). -/
def translate {α β : Type} (_ : PreCModalSymbol) (f : α → β) : α → β := f

/-- Trivial translate: identity per mode. -/
def trivialTranslate (m : PreCModalSymbol) : Unit → Unit :=
  translate m id

/-! ### Form-choice 4: B5 as initial singularity -/

/-- Configuration enumeration: eight combinatorial configuration classes.
    Parallel to F3.b's K-enumeration. -/
inductive PreCConfiguration : Type where
  | k1 | k2 | k3 | k4 | k5 | k6 | k7 | k8
  deriving DecidableEq, Repr

/-- Initial-configuration function with B5-conditional pattern.
    At stage 1, K1 is forced; at all other stages, K2 (trivial default). -/
def initialConfig : Nat → PreCConfiguration
  | 1 => .k1
  | _ => .k2

/-- B5-theorem: at stage 1, the initial configuration is K1.
    In geometric-sequent form: `⊤ ⊢_(n=1) initialConfig n = k1`.
    Proof: direct reduction via `rfl`. -/
theorem B5_initialConfig_at_stage_1 :
    initialConfig 1 = PreCConfiguration.k1 := rfl

end Reformulation.PreC.PKLFormWahlen
