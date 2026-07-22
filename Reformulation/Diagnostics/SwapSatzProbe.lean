import Mathlib.CategoryTheory.Discrete.Basic
import Reformulation.PathC.ModalTwoCategory

/-!
# Reformulation.Diagnostics.SwapSatzProbe — Machbarkeits-Sonde AP7 (kein Satz)

**Reine Sonde — kein Eingriff, NICHT im Aggregat.** Prüft am Term die
Formulierbarkeit des Swap-Satzes (S1 Zeugen-Kern, F1/F2 Fassungen) und den
Axiom-Stand des Pfad-C-Rahmens (S2-F3(a)). Wird nur behalten, wenn sorry-frei.

Ausführen: `lake env lean Reformulation/Diagnostics/SwapSatzProbe.lean`
-/

namespace Reformulation.Diagnostics.SwapSatzProbe

open CategoryTheory

-- ── S1: der Zeugen-Kern auf `Discrete (Fin 2)` ──────────────────────────────

/-- Endofunktor aus `f = const 0`. -/
def F : Discrete (Fin 2) ⥤ Discrete (Fin 2) :=
  Discrete.functor (fun _ => Discrete.mk 0)

/-- Endofunktor aus `g = swap` (0↦1, 1↦0). -/
def G : Discrete (Fin 2) ⥤ Discrete (Fin 2) :=
  Discrete.functor (fun i => Discrete.mk (if i = 0 then 1 else 0))

/-- Die Objekt-Ungleichung: `(F⋙G)⟨0⟩ = ⟨1⟩`, `(G⋙F)⟨0⟩ = ⟨0⟩`. -/
example : ((F ⋙ G).obj (Discrete.mk 0)).as ≠ ((G ⋙ F).obj (Discrete.mk 0)).as := by
  simp only [F, G, Functor.comp_obj, Discrete.functor_obj_eq_as]
  decide

/-- **F2 (Instanz-Fassung — der Kern):** zwischen den beiden Kompositionen des
    Zeugen existiert kein 2-Iso (Natur-Iso im Funktor-Kategorie). -/
theorem no_swap_witness : ¬ Nonempty (F ⋙ G ≅ G ⋙ F) := by
  rintro ⟨e⟩
  have h := Discrete.eq_of_hom (e.hom.app (Discrete.mk 0))
  simp only [F, G, Functor.comp_obj, Discrete.functor_obj_eq_as] at h
  exact absurd h (by decide)

/-- **F1 (Uniformitäts-Fassung — die Kanonizitäts-Widerlegung):** es gibt keine
    einheitliche Swap-Zuordnung, die für JEDE Kategorie und JEDES Endofunktor-Paar
    einen 2-Iso `F⋙G ≅ G⋙F` liefert. Sauber quantifiziert als `¬ ∀ …, Nonempty …`
    (keine Σ über Universen, kein `PLift`), widerlegt durch den S1-Zeugen. -/
theorem no_uniform_swap :
    ¬ ∀ (C : Type) [Category.{0} C] (X Y : C ⥤ C), Nonempty (X ⋙ Y ≅ Y ⋙ X) := by
  intro s
  exact no_swap_witness (s (Discrete (Fin 2)) F G)

end Reformulation.Diagnostics.SwapSatzProbe

-- ── S2-F3(a): Axiom-Stand des Pfad-C-Rahmens ────────────────────────────────
-- Hängen Rahmen und Kompositions-Defs an `sorryAx`?
#print axioms Reformulation.PathC.ModalEndofunctor.tauOmega
#print axioms Reformulation.PathC.ModalEndofunctor.omegaTau
#print axioms Reformulation.PathC.ModalTwoCategory.tauOmega_asymmetric_smooth
#print axioms Reformulation.PathC.ModalTwoCategory.omegaTau_asymmetric_smooth
#print axioms Reformulation.PathC.elementaryTopos_of_components
#print axioms Reformulation.Diagnostics.SwapSatzProbe.no_swap_witness
#print axioms Reformulation.Diagnostics.SwapSatzProbe.no_uniform_swap
