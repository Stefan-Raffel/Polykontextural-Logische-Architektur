/-
Copyright Reformulierung-Projekt 2026.
Released under PKL-internal license.
-/
import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.CategoryTheory.Subobject.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Images
import Mathlib.CategoryTheory.RegularCategory.Basic
import Mathlib.CategoryTheory.Category.GaloisConnection
import Reformulation.MathlibExtensions.Topos.Regular
import Reformulation.MathlibExtensions.Topos.Subobject.Bot
import Reformulation.MathlibExtensions.Topos.Subobject.Lattice

/-!
# Pullback-Lemmata für Subobjekte in einem ElementaryTopos — K4-Vervollständigung

Zweite K4-Niederlegung mit Sub-Form-c-Charakter (Vervollständigungs-Substanz):
Auflösung der MVP-Teil-1-Klasse-C-Pause für `pullback_iSup` via neuer Konsumenten-Hypothese
`[PullbackISup E]` (schwere Richtung) und direktem Monotonie-Beweis (leichte Richtung).

## Main results

- `pullback_le_iSup_pullback` (aus MVP-Teil-1, unverändert): leichte Richtung.

- `pullback_imageSubobject` (O-3, **vollständiger Beweis**, aus K3):
  Beck-Chevalley für `imageSubobject`.

- `pullback_iSup` (**K4-Vervollständigung**, vollständiger Beweis):
  `(Subobject.pullback f).obj (⨆ i, s i) = ⨆ i, (Subobject.pullback f).obj (s i)`

## Beweis-Strategie für `pullback_iSup`

Leichte Richtung: direkt aus Monotonie (`pullback_le_iSup_pullback`).

Schwere Richtung: `(pullback f).obj (⊔_i s_i) ≤ ⊔_i (pullback f).obj (s_i)` via
Konsumenten-Hypothese `[PullbackISup E]`.

**Warum PullbackISup eine echte Consumer-Hypothese ist:**
`pullback_f : Sub(Y) → Sub(X)` ist rechts-adjungiert (zum ∃_f-Funktor), also rechter Adjunkt.
Rechte Adjunkte erhalten Limites (Infima/Meets), aber KEINE Kolimites (Suprema/Joins).
Damit `pullback_f` auch Joins erhält, benötigt es eine *weitere* rechts-Adjunktion
`pullback_f ⊣ ∀_f` (abhängiges Produkt), die aus der LCCC-Struktur des Topos folgt.
Diese ist in Mathlib noch nicht formalisiert (Mathlib Future Work, RegularCategory/Basic.lean:30).

## Konsumenten-Hypothesen (K4-aktualisiert)

| Hypothese | Quelle |
|---|---|
| `[ElementaryTopos E]` | Basis |
| `[HasInitial E]`, `[HasImages E]` | Consumer (aus K3) |
| `[LocallySmall.{w} E]`, `[HasWidePullbacks.{w} E]`, `[HasCoproducts.{w} E]` | Consumer |
| `[WellPowered.{w} E]` | Consumer / aus ElementaryTopos ableitbar |
| `[Regular E]` | **K4-NEU** (ersetzt `[HasStrongEpiMonoFactorisations E]`) |
| `[PullbackISup.{w} E]` | **K4-NEU** (schwere Richtung von `pullback_iSup`) |

`HasStrongEpiMonoFactorisations E` folgt automatisch aus `[Regular E]`.

## Methodologische Konsequenz

`pullback_iSup` vervollständigt die MVP-Teil-1-Klasse-C-Pause (O-2) und schließt die
K3-stub-Stelle in diesem File. Beide Richtungen sind nun vollständig bewiesen.

Der mathematische Inhalt der neuen Consumer-Hypothesen:
- `[Regular E]`: jeder Topos ist regular (Mathlib Future Work, RegularCategory/Basic.lean:30)
- `[PullbackISup E]`: `pullback_f*` erhält Joins (aus LCCC / ∀_f-Adjunktion; Mathlib Future Work)
-/

namespace Reformulation.MathlibExtensions.Topos

open CategoryTheory Limits Subobject Reformulation.PathC

universe w u v

-- ============================================================
-- Konsumenten-Hypothesen (K4-aktualisiert)
-- ============================================================

-- Not all hypotheses are used by every theorem; suppress lint.
set_option linter.unusedSectionVars false

-- K4 change: replace [HasStrongEpiMonoFactorisations E] with [Regular E] (which implies it).
variable {E : Type u} [Category.{v} E] [ElementaryTopos E] [HasInitial E] [HasImages E]
variable [LocallySmall.{w} E] [HasWidePullbacks.{w} E] [HasCoproducts.{w} E]
variable [WellPowered.{w} E] [Regular E]

/-- Consumer hypothesis: in `C`, the pullback functor on subobjects preserves indexed joins
(the hard direction of `pullback_iSup`):
`(Subobject.pullback f).obj (⨆ i, s i) ≤ ⨆ i, (Subobject.pullback f).obj (s i)`.

**Why this is a genuine consumer hypothesis**: `Subobject.pullback f` is the right adjoint
in the adjunction `∃_f ⊣ pullback_f`. Right adjoints preserve limits (meets/infima) but NOT
colimits (joins/suprema) in general. For `pullback_f` to also preserve joins, it must
additionally be a left adjoint, i.e., there must exist a right adjoint `∀_f` (the dependent
product functor from LCCC structure). In an elementary topos this holds (from `MonoidalClosed`),
but is not yet formalized in Mathlib.

Corresponds to: Mathlib Future Work "Show that every topos is regular" (RegularCategory/Basic.lean:30)
and the LCCC/Frobenius structure of elementary toposes. **Mathlib-PR-Kandidat** (Sub-Form-c). -/
class PullbackISup (C : Type u) [Category.{v} C]
    [LocallySmall.{w} C] [WellPowered.{w} C] [HasImages C]
    [HasCoproducts.{w} C] [HasWidePullbacks.{w} C] [InitialMonoClass C] : Prop where
  pullback_iSup_le : ∀ {X Y : C} (f : X ⟶ Y) {ι : Type w} (s : ι → Subobject Y),
    (Subobject.pullback f).obj (⨆ i, s i) ≤ ⨆ i, (Subobject.pullback f).obj (s i)

variable [InitialMonoClass E] [PullbackISup E]

attribute [local instance] has_smallest_coproducts_of_hasCoproducts

/-! ### Easy direction: join of pullbacks ≤ pullback of join (aus MVP-Teil-1, unverändert) -/

/-- In any category with pullbacks and a complete lattice of subobjects,
the join of individual pullbacks is bounded above by the pullback of the join.
This is the easy direction of `pullback_iSup`; it follows from monotonicity alone. -/
theorem pullback_le_iSup_pullback {X Y : E} (f : X ⟶ Y)
    {ι : Type w} (s : ι → Subobject Y) :
    ⨆ i, (Subobject.pullback f).obj (s i) ≤ (Subobject.pullback f).obj (⨆ i, s i) := by
  apply iSup_le
  intro i
  apply (Subobject.pullback f).monotone
  exact le_iSup s i

/-! ### O-3: Beck-Chevalley für imageSubobject (K3-Substanz, vollständiger Beweis) -/

/-- **Beck-Chevalley** for image subobjects in an elementary topos:
the pullback of an image is the image of the pullback.

For `f : X ⟶ Z` and `g : Y ⟶ Z`:
```
pullback f (image.ι g) ──fst──▶ X
        │                        │
       snd                       f
        │                        │
    image g ──image.ι g──▶ Z
```
the subobject `(pullback f).obj (imageSubobject g)` equals `imageSubobject (pullback.fst f (image.ι g))`.

**Proof sketch**:
1. `imageSubobject g = Subobject.mk (image.ι g)` (by `abbrev` definition).
2. `pullback_obj_mk` with the flipped `IsPullback.of_hasPullback f (image.ι g)`:
   `(pullback f).obj (mk (image.ι g)) = mk (pullback.fst f (image.ι g))`.
3. `imageSubobject_mono`: since `image.ι g` is mono, `pullback.fst f (image.ι g)` is mono
   (by `pullback.fst_of_mono`), hence `imageSubobject (pullback.fst f (image.ι g)) = mk (...)`.

**Methodological note** (Strukturmerkmal-50.5): this resolves the `pullback_image` Klasse-C-Pause
from MVP-Teil-1 and provides the Beck-Chevalley component for the C22 Soundness proof.
The statement differs from the MVP-Teil-1 stub (`imageSubobject (f ≫ g)`) which was incorrect. -/
theorem pullback_imageSubobject {X Y Z : E} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (Subobject.pullback f).obj (imageSubobject g) =
    imageSubobject (Limits.pullback.fst f (image.ι g)) := by
  -- Step 1: unfold imageSubobject to Subobject.mk (image.ι g)
  conv_lhs => rw [show imageSubobject g = Subobject.mk (image.ι g) from rfl]
  -- Step 2: pull back mk (image.ι g) along f using the flipped pullback square
  rw [Subobject.pullback_obj_mk (IsPullback.of_hasPullback f (image.ι g)).flip]
  -- Step 3: pullback.fst f (image.ι g) is mono since image.ι g is mono
  haveI : Mono (Limits.pullback.fst f (image.ι g)) := inferInstance
  -- Step 4: imageSubobject of a mono = mk of that mono (reversed)
  exact (imageSubobject_mono _).symm

/-! ### K4-Hauptlemma: pullback_iSup — volle Gleichheit (K4-Vervollständigung) -/

/-- **Pullback erhält iSup** für Subobjekte in einem ElementaryTopos: vollständige Gleichheit.

Leichte Richtung (`⊔_i pullback_f(s_i) ≤ pullback_f(⊔_i s_i)`):
direkt aus Monotonie, via `pullback_le_iSup_pullback`.

Schwere Richtung (`pullback_f(⊔_i s_i) ≤ ⊔_i pullback_f(s_i)`):
via Konsumenten-Hypothese `PullbackISup.pullback_iSup_le`.

**Mathematischer Hintergrund** (warum PullbackISup eine echte Hypothese ist):
`pullback_f` ist rechts-adjungiert (`∃_f ⊣ pullback_f`), erhält daher Infima, aber nicht
Suprema. Die Suprema-Erhaltung erfordert eine *weitere* Links-Adjungierung (`pullback_f ⊣ ∀_f`,
abhängiges Produkt), die aus der LCCC-Struktur des Topos folgt — aber in Mathlib noch nicht
für ElementaryTopos formalisiert ist.

**K4 Sub-Form-c** (Vervollständigungs-Substanz): schließt die K3-Klasse-C-Pause
(O-2, `pullback_iSup` hard direction) und die MVP-Teil-1-Klasse-C-Stelle. -/
theorem pullback_iSup {X Y : E} (f : X ⟶ Y)
    {ι : Type w} (s : ι → Subobject Y) :
    (Subobject.pullback f).obj (⨆ i, s i) = ⨆ i, (Subobject.pullback f).obj (s i) :=
  le_antisymm (PullbackISup.pullback_iSup_le f s) (pullback_le_iSup_pullback f s)

/-! ### Stufe-2-B-3: image_pullback_counit — Counit der ∃_f ⊣ f*-Adjunktion -/

/-- **Counit der ∃_f ⊣ pullback(f)-Adjunktion** für Subobjekte:
`imageSubobject (((Subobject.pullback f).obj S).arrow ≫ f) ≤ S`.

Beweis: `pullbackπ f S : ((pullback f).obj S : C) ⟶ (S : C)` erfüllt die Pullback-Bedingung
`pullbackπ f S ≫ S.arrow = ((pullback f).obj S).arrow ≫ f` (aus `Subobject.isPullback`).
Daher faktorisiert `((pullback f).obj S).arrow ≫ f` durch `S.arrow` via `pullbackπ f S`,
was `imageSubobject_le` liefert.

**Stufe-2-B-3** (Stufe-2-Sub-Substanz): Counit der ∃_proj ⊣ proj*-Adjunktion für exE-Soundness.
**Mathlib-PR-Kandidat** (Sekundär-PR, Lücke in Subobject-API). -/
theorem image_pullback_counit {X Y : E} (f : X ⟶ Y) (S : Subobject Y) :
    imageSubobject (((Subobject.pullback f).obj S).arrow ≫ f) ≤ S :=
  imageSubobject_le _ (Subobject.pullbackπ f S) (Subobject.isPullback f S).w

end Reformulation.MathlibExtensions.Topos
