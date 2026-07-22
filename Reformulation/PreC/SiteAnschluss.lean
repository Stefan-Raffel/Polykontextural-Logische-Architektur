import Mathlib.CategoryTheory.EssentiallySmall
import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.CategoryTheory.Sites.Sheaf

/-!
# Reformulation.PreC.SiteAnschluss — Phase-A connection: PKL site and sheaves

Connects the PKL contexture-plurality structure to Mathlib's site-and-sheaf
machinery (Phase A of the Pre-C tractability demonstration).

The PKL index category is the discrete category over `Fin n`: `n` objects
representing `n` contextures, only identity morphisms between them. The
Grothendieck topology is the trivial topology (only maximal sieves cover),
appropriate for the fast-discrete plurality structure of PKL.

The contexture component category is the category of type-valued sheaves
over the PKL site — the minimal sheaf-categorical form that each
PKL contexture lives in.
-/

namespace Reformulation.PreC

open CategoryTheory

/-- Index category of contexture components: the discrete category over `Fin n`.
    Carries PKL's fast-discrete plurality: `n` objects, only identity morphisms.
    The minimal site base for PKL contexture pluralism. -/
abbrev ContextureIndex (n : Nat) : Type := Discrete (Fin n)

/-- Every `ContextureIndex n` is essentially small at universe 0,
    since `Fin n : Type 0` is small. -/
instance contextureIndex_essentiallySmall (n : Nat) :
    EssentiallySmall.{0} (ContextureIndex n) :=
  Discrete.essentiallySmallOfSmall

/-- Trivial Grothendieck topology on `ContextureIndex n`.
    A sieve covers iff it is the maximal sieve. Appropriate for the
    fast-discrete plurality: no non-trivial covering families between
    distinct contexture components. -/
def ContextureSite (n : Nat) : GrothendieckTopology (ContextureIndex n) :=
  GrothendieckTopology.trivial _

/-- Contexture component: the category of type-valued sheaves over the
    PKL site. Each PKL contexture lives as such a component. -/
abbrev ContextureComponent (n : Nat) : Type _ :=
  Sheaf (ContextureSite n) (Type)

end Reformulation.PreC
