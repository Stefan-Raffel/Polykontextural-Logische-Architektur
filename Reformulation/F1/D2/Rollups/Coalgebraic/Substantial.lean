import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Discrete.Basic
import Reformulation.F3a.Endofunctor
import Reformulation.F3a.SchemaMorphism
import Reformulation.F3c.Symbols
import Reformulation.F3f.Stage
import Reformulation.F3f.StageTransition
import Reformulation.F3f.StageWithF3aAnchor
import Reformulation.F1.D2.Rollups
import Reformulation.F1.D2.Rollups.Coalgebraic

/-!
# F1.D2.Rollups.Coalgebraic.Substantial

Substantial belegung of the coalgebraic stratum over Rev2's sparse form.

## Architectural background

Rev2 carries the coalgebraic stratum's *form* in the rollup domain
(two stages with Discrete categories, identity end-functor, constant
translate). Substantial carries five substantial aspects per K1-Rev2:

- substantial category structure on Layer1Chain and Layer2Rollup
  (Pfad β: list-based morphisms with kind tracking; Klasse-B: morphisms
  lifted to Type 1 via ULift to satisfy Stage.{1}'s Category.{1,1} requirement)
- bilanz-substantiated end-functor (Pfad-β-Lite: constant on bilanz)
- modal-differentiated translate over six ModalSymbol values
- B6 uniqueness theorem with ω as the distinguished iteration mode
- F3.a anchor via StageWithF3aAnchor (F3.f-Rev3 class, Pfad θ)

## Modul scope

Substantial is *additive* alongside Rev2. The aggregator
`Reformulation.F1.D2.Rollups` is unchanged.

## Methodological note

Substantial is the first F1 belegung that triggered an F-extension
(F3.f-Rev3 via Pfad θ for C13). This trigger-relationship between F1
and F is documented in F3.f-K5 §IX.1.
-/

namespace Reformulation.F1.D2.Rollups.Coalgebraic.Substantial

open CategoryTheory
open Reformulation.F1.D2.Rollups.RollupGeneral
open Reformulation.F1.D2.Rollups.Families

-- ============================================================================
-- §III: ConsensusStep and Layer1Chain category (K2.1)
-- Klasse-B: Hom lifted to Type 1 via ULift to satisfy Category.{1,1}
--           (Stage.{1}'s [cat : Category totalSpace] requires morphisms in Type u=1)
-- ============================================================================

/-- Three kinds of L1 consensus transitions. -/
inductive ConsensusStepKind
  | block
  | epoch
  | justification
  deriving DecidableEq, Repr

/-- A morphism between Layer1Chain values: list of consensus steps.
    Wrapped in ULift.{1} so that Category Layer1Chain lives in Category.{1,1},
    as required by Stage.{1}. -/
structure ConsensusStep (X Y : Layer1Chain) where
  steps : List ConsensusStepKind

/-- Category on Layer1Chain with consensus-step morphisms (Pfad β).
    Morphisms live in Type 1 via ULift per the Stage.{1} universe requirement. -/
instance : Category Layer1Chain where
  Hom X Y := ULift.{1} (ConsensusStep X Y)
  id _ := ⟨⟨[]⟩⟩
  comp f g := ⟨⟨f.down.steps ++ g.down.steps⟩⟩
  -- [] ++ steps = steps definitionally (first case of List.append)
  id_comp _ := rfl
  -- steps ++ [] = steps is NOT definitional; prove via simp
  comp_id f := by obtain ⟨⟨s⟩⟩ := f; simp [List.append_nil]
  assoc f g h := by
    obtain ⟨⟨fs⟩⟩ := f; obtain ⟨⟨gs⟩⟩ := g; obtain ⟨⟨hs⟩⟩ := h
    simp [List.append_assoc]

-- ============================================================================
-- §IV: RollupStep and Layer2Rollup category (K2.2)
-- ============================================================================

/-- Three kinds of L2 rollup transitions. -/
inductive RollupStepKind
  | sequencer
  | proof
  | settlement
  deriving DecidableEq, Repr

structure RollupStep (X Y : Layer2Rollup) where
  steps : List RollupStepKind

instance : Category Layer2Rollup where
  Hom X Y := ULift.{1} (RollupStep X Y)
  id _ := ⟨⟨[]⟩⟩
  comp f g := ⟨⟨f.down.steps ++ g.down.steps⟩⟩
  id_comp _ := rfl
  comp_id f := by obtain ⟨⟨s⟩⟩ := f; simp [List.append_nil]
  assoc f g h := by
    obtain ⟨⟨fs⟩⟩ := f; obtain ⟨⟨gs⟩⟩ := g; obtain ⟨⟨hs⟩⟩ := h
    simp [List.append_assoc]

-- ============================================================================
-- §V: ModalAspect and Layer2RollupSubstantial (K2.5 prerequisite)
-- ============================================================================

/-- Six modal aspects parallel to F3.c's ModalSymbol, used as structural
    markers on Layer2RollupSubstantial. -/
inductive ModalAspect
  | tau
  | delta
  | omega
  | negTau
  | negDelta
  | negOmega
  deriving DecidableEq, Repr

/-- Layer2Rollup extended with a modal-aspect marker. -/
structure Layer2RollupSubstantial extends Layer2Rollup where
  modalAspect : ModalAspect

structure Layer2RollupSubstantialStep (X Y : Layer2RollupSubstantial) where
  steps : List RollupStepKind

instance : Category Layer2RollupSubstantial where
  Hom X Y := ULift.{1} (Layer2RollupSubstantialStep X Y)
  id _ := ⟨⟨[]⟩⟩
  comp f g := ⟨⟨f.down.steps ++ g.down.steps⟩⟩
  id_comp _ := rfl
  comp_id f := by obtain ⟨⟨s⟩⟩ := f; simp [List.append_nil]
  assoc f g h := by
    obtain ⟨⟨fs⟩⟩ := f; obtain ⟨⟨gs⟩⟩ := g; obtain ⟨⟨hs⟩⟩ := h
    simp [List.append_assoc]

-- ============================================================================
-- §VI: Schema and F3.a components (K2.3)
-- Klasse-B: schema.positions lifted to Type 1 via ULift to satisfy
--           StageWithF3aAnchor.{1}'s Schema.{1} requirement
-- ============================================================================

/-- Schema positions for the rollup bilanz. -/
inductive RollupSchemaPosition
  | stateRoot
  | validatorSet
  | justification
  | composite
  deriving DecidableEq, Repr

/-- L1 rollup-bilanz schema. positions lifted to Type 1 for Schema.{1}. -/
def rollupSchemaL1 : Reformulation.F3a.Schema 1 := {
  positions := ULift.{1} RollupSchemaPosition
  connections := ∅
  selfReferenceMarkers := ∅
}

/-- L2 rollup-bilanz schema. -/
def rollupSchemaL2 : Reformulation.F3a.Schema 2 := {
  positions := ULift.{1} RollupSchemaPosition
  connections := ∅
  selfReferenceMarkers := ∅
}

/-- F3.a first component for L1: identity restriction (Pfad β, Lite). -/
def rollupResDesL1 :
    Reformulation.F3a.DesignativeRestriction 1 Layer1Chain Layer1Chain := {
  resDes := 𝟭 _
  beckChevalley := trivial
}

/-- F3.a second component for L1: identity outer balance.
    J = Discrete (PUnit.{2}) : Type 1 per universe requirement. -/
def rollupOuterBalanceL1 :
    Reformulation.F3a.OuterBalance 1 (Discrete (PUnit.{2})) Layer1Chain Layer1Chain := {
  outerBalance := 𝟭 _
  isFunctorial := trivial
}

/-- F3.a third component for L1: constant skeleton (B.1 corrected). -/
def rollupSkeletonL1 :
    Reformulation.F3a.Skeleton 1 Layer1Chain rollupSchemaL1 := {
  skeletonFun := fun _ => ULift.up .composite
  isUnique := trivial
}

/-- F3.a first component for L2. -/
def rollupResDesL2 :
    Reformulation.F3a.DesignativeRestriction 2 Layer2RollupSubstantial Layer2RollupSubstantial := {
  resDes := 𝟭 _
  beckChevalley := trivial
}

/-- F3.a second component for L2. -/
def rollupOuterBalanceL2 :
    Reformulation.F3a.OuterBalance 2 (Discrete (PUnit.{2})) Layer2RollupSubstantial Layer2RollupSubstantial := {
  outerBalance := 𝟭 _
  isFunctorial := trivial
}

/-- F3.a third component for L2. -/
def rollupSkeletonL2 :
    Reformulation.F3a.Skeleton 2 Layer2RollupSubstantial rollupSchemaL2 := {
  skeletonFun := fun _ => ULift.up .composite
  isUnique := trivial
}

-- ============================================================================
-- §VII: Bilanz constructions and endenFunktor (K2.4, Pfad-β-Lite)
-- ============================================================================

/-- Default Layer2Rollup from a Layer1Chain (Optimistic family, Lite default). -/
def defaultLayer2Rollup (l1 : Layer1Chain) : Layer2Rollup := {
  family := .optimisticRollup
  parentLayer1 := l1
  inheritedGenesis := trivial
}

/-- L1 bilanz: identity (Pfad-β-Lite constancy). -/
def rollupBilanzL1Const (anchor : Layer1Chain) : Layer1Chain := anchor

/-- L2 bilanz: constant on anchor's parentLayer1 and modalAspect. -/
def rollupBilanzL2Const (anchor : Layer2RollupSubstantial) : Layer2RollupSubstantial := {
  toLayer2Rollup := defaultLayer2Rollup anchor.parentLayer1
  modalAspect := anchor.modalAspect
}

/-- L1 endenFunktor: constant on bilanz (Pfad-β-Lite).
    map_comp uses rfl because 𝟙 ≫ 𝟙 = 𝟙 definitionally with ULift morphisms. -/
def rollupEndenFunktorL1 (anchor : Layer1Chain) : Layer1Chain ⥤ Layer1Chain where
  obj _ := rollupBilanzL1Const anchor
  map _ := 𝟙 _
  map_id _ := rfl
  map_comp _ _ := rfl

/-- L2 endenFunktor: constant on bilanz. -/
def rollupEndenFunktorL2 (anchor : Layer2RollupSubstantial) :
    Layer2RollupSubstantial ⥤ Layer2RollupSubstantial where
  obj _ := rollupBilanzL2Const anchor
  map _ := 𝟙 _
  map_id _ := rfl
  map_comp _ _ := rfl

-- ============================================================================
-- §VIII: schemaLift constructions (K2.3.3)
-- ============================================================================

/-- Lift from schema positions (ULift RollupSchemaPosition) to Layer1Chain:
    constant on bilanz (Pfad-β-Lite). -/
def rollupSchemaLiftL1 (anchor : Layer1Chain) :
    rollupSchemaL1.positions → Layer1Chain := fun _ =>
  rollupBilanzL1Const anchor

/-- Lift to Layer2RollupSubstantial: constant on bilanz. -/
def rollupSchemaLiftL2 (anchor : Layer2RollupSubstantial) :
    rollupSchemaL2.positions → Layer2RollupSubstantial := fun _ =>
  rollupBilanzL2Const anchor

-- ============================================================================
-- §IX: f3aConsistent theorems
-- Both sides reduce to rollupBilanzXConst anchor by rfl.
-- ============================================================================

theorem rollupF3aConsistentL1 (anchor : Layer1Chain) :
    ∀ x : Layer1Chain,
      (rollupEndenFunktorL1 anchor).obj x =
        rollupSchemaLiftL1 anchor (rollupSkeletonL1.skeletonFun
          (rollupOuterBalanceL1.outerBalance.obj
            (rollupResDesL1.resDes.obj x))) := fun _ => rfl

theorem rollupF3aConsistentL2 (anchor : Layer2RollupSubstantial) :
    ∀ x : Layer2RollupSubstantial,
      (rollupEndenFunktorL2 anchor).obj x =
        rollupSchemaLiftL2 anchor (rollupSkeletonL2.skeletonFun
          (rollupOuterBalanceL2.outerBalance.obj
            (rollupResDesL2.resDes.obj x))) := fun _ => rfl

-- ============================================================================
-- §X: Six translate operations (K2.5)
-- ============================================================================

def translateTauOp (l1 : Layer1Chain) : Layer2RollupSubstantial :=
  { toLayer2Rollup := defaultLayer2Rollup l1, modalAspect := .tau }

def translateDeltaOp (l1 : Layer1Chain) : Layer2RollupSubstantial :=
  { toLayer2Rollup := defaultLayer2Rollup l1, modalAspect := .delta }

def translateOmegaOp (l1 : Layer1Chain) : Layer2RollupSubstantial :=
  { toLayer2Rollup := defaultLayer2Rollup l1, modalAspect := .omega }

def translateNegTauOp (l1 : Layer1Chain) : Layer2RollupSubstantial :=
  { toLayer2Rollup := defaultLayer2Rollup l1, modalAspect := .negTau }

def translateNegDeltaOp (l1 : Layer1Chain) : Layer2RollupSubstantial :=
  { toLayer2Rollup := defaultLayer2Rollup l1, modalAspect := .negDelta }

def translateNegOmegaOp (l1 : Layer1Chain) : Layer2RollupSubstantial :=
  { toLayer2Rollup := defaultLayer2Rollup l1, modalAspect := .negOmega }

/-- Dispatch over ModalSymbol to the six operation constructors. -/
def rollupTranslate (l1 : Layer1Chain) :
    Reformulation.F3c.ModalSymbol → Layer2RollupSubstantial
  | .tau      => translateTauOp l1
  | .delta    => translateDeltaOp l1
  | .omega    => translateOmegaOp l1
  | .negTau   => translateNegTauOp l1
  | .negDelta => translateNegDeltaOp l1
  | .negOmega => translateNegOmegaOp l1

/-- The six translate operations produce distinct ModalAspect values. -/
theorem translate_distinct_modal_aspects (l1 : Layer1Chain) :
    (rollupTranslate l1 .tau).modalAspect    = .tau    ∧
    (rollupTranslate l1 .delta).modalAspect  = .delta  ∧
    (rollupTranslate l1 .omega).modalAspect  = .omega  ∧
    (rollupTranslate l1 .negTau).modalAspect  = .negTau  ∧
    (rollupTranslate l1 .negDelta).modalAspect = .negDelta ∧
    (rollupTranslate l1 .negOmega).modalAspect = .negOmega :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- §XI: fromRollupDoubleValuationSubstantial
-- ============================================================================

/-- Constructs the Substantial-form Stage 1, Stage 2, and StageTransition
    from a RollupDoubleValuation. Stage 2's stageObj has modalAspect = ω
    per K1-Rev2 Wahl 4 (B6 uniqueness). -/
def fromRollupDoubleValuationSubstantial (rdv : RollupDoubleValuation) :
    Reformulation.F3f.StageWithF3aAnchor.{1} 1 ×
    Reformulation.F3f.StageWithF3aAnchor.{1} 2 ×
    Reformulation.F3f.StageTransition.{1} 1 :=
  let stage1 : Reformulation.F3f.StageWithF3aAnchor.{1} 1 := {
    totalSpace := Layer1Chain
    cat := inferInstance
    stageObj := rdv.layer1
    endenFunktor := rollupEndenFunktorL1 rdv.layer1
    γ := 𝟙 _
    initialConfig := Reformulation.F3b.K.k1
    initialConfig_at_stage_1 := fun _ => rfl
    noAlgebraExtension := trivial
    designativePart := Layer1Chain
    cat_des := inferInstance
    J := Discrete (PUnit.{2})
    cat_J := inferInstance
    tracesFamily := Layer1Chain
    cat_traces := inferInstance
    schema := rollupSchemaL1
    resDes := rollupResDesL1
    outerBalance := rollupOuterBalanceL1
    skeleton := rollupSkeletonL1
    schemaLift := rollupSchemaLiftL1 rdv.layer1
    f3aConsistent := rollupF3aConsistentL1 rdv.layer1
  }
  let s2obj : Layer2RollupSubstantial := {
    toLayer2Rollup := defaultLayer2Rollup rdv.layer1
    modalAspect := .omega
  }
  let stage2 : Reformulation.F3f.StageWithF3aAnchor.{1} 2 := {
    totalSpace := Layer2RollupSubstantial
    cat := inferInstance
    stageObj := s2obj
    endenFunktor := rollupEndenFunktorL2 s2obj
    γ := 𝟙 _
    initialConfig := Reformulation.F3b.K.k2
    initialConfig_at_stage_1 := fun h => absurd h (by decide)
    noAlgebraExtension := trivial
    designativePart := Layer2RollupSubstantial
    cat_des := inferInstance
    J := Discrete (PUnit.{2})
    cat_J := inferInstance
    tracesFamily := Layer2RollupSubstantial
    cat_traces := inferInstance
    schema := rollupSchemaL2
    resDes := rollupResDesL2
    outerBalance := rollupOuterBalanceL2
    skeleton := rollupSkeletonL2
    schemaLift := rollupSchemaLiftL2 s2obj
    f3aConsistent := rollupF3aConsistentL2 s2obj
  }
  let transition : Reformulation.F3f.StageTransition.{1} 1 := {
    current := stage1.toStage
    next := stage2.toStage
    translate := fun m _ => rollupTranslate rdv.layer1 m
  }
  ⟨stage1, stage2, transition⟩

-- ============================================================================
-- §XII: B6 uniqueness theorem (K2.6)
-- ============================================================================

/-- B6 uniqueness: ω is the unique ModalSymbol m such that rollupTranslate
    produces an ω-aspect Layer2RollupSubstantial. Architectural pointe:
    rollup iteration as stage-iteration is constitutively ω-borne.

    Klasse-D adaptation: stated directly in terms of rollupTranslate.modalAspect
    to avoid opacity of fromRollupDoubleValuationSubstantial's product projections
    in the theorem type (Category.{1,1} totalSpace synthesis issue). The theorem
    captures the full architectural content: ω is the unique mode with omega-aspect. -/
theorem b6_unique_iteration_mode (rdv : RollupDoubleValuation) :
    ∃! m : Reformulation.F3c.ModalSymbol,
      (rollupTranslate rdv.layer1 m).modalAspect = ModalAspect.omega := by
  refine ⟨Reformulation.F3c.ModalSymbol.omega, rfl, fun m hm => ?_⟩
  -- For each non-omega case: dsimp reduces hm to a closed ModalAspect equality,
  -- then decide derives the contradiction.
  cases m with
  | omega    => rfl
  | tau      => dsimp only [rollupTranslate, translateTauOp] at hm; exact absurd hm (by decide)
  | delta    => dsimp only [rollupTranslate, translateDeltaOp] at hm; exact absurd hm (by decide)
  | negTau   => dsimp only [rollupTranslate, translateNegTauOp] at hm; exact absurd hm (by decide)
  | negDelta => dsimp only [rollupTranslate, translateNegDeltaOp] at hm; exact absurd hm (by decide)
  | negOmega => dsimp only [rollupTranslate, translateNegOmegaOp] at hm; exact absurd hm (by decide)

end Reformulation.F1.D2.Rollups.Coalgebraic.Substantial
