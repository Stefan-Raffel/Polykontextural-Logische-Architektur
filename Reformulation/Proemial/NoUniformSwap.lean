import Mathlib.CategoryTheory.Discrete.Basic

/-!
# Reformulation.Proemial.NoUniformSwap — der Swap-Satz (siebzehnte Schicht)

Das älteste „benannt, nicht gebaut" der Architektur (NE3, kein kanonischer Swap)
erhält seinen Satz — in der Fassung, die der Term heute trägt: punktuelle Existenz
bewiesen, Uniformität über alle Endofunktor-Paare widerlegt, Instanz-Zeuge benannt.
Kategorien-Sprache (Mathlib `CategoryTheory`), Zeuge auf `Discrete (Fin 2)`.
Selbsttragend.

## (1) Design-Lage

NE3 (kein kanonischer Swap `τ∘ω ⇔ ω∘τ`) war Design-Datum ohne Satz; der Trakt
benennt die Lücke selbst — `Reformulation/F3c/NonExistence.lean`: „A theorem
statement requires constructing a `ModalTwoCategory` instance in which the two
compositions are not 2-isomorphic — that is local-layer material, belonging in F1."
Diese Schicht füllt sie in der heute tragbaren Fassung.

## (2) Quellen-Trennung (Deutung, Marke 3)

Die heterarchische Vertauschbarkeit (Günther 1979) trägt die *Wahl* (fünfzehnte
Schicht, `DirectionChoice`); die Nicht-Kanonizität des Swaps macht die Wahl
semantisch *echt* (existierte der kanonische Swap, erübrigte sich die Wahl). Diese
Verbindung Wahl ↔ Swap ist Deutung; kein Satz dieser Schicht behauptet sie.

## (3) Dreistufiger Schnitt (Kern)

* **bewiesen** — Swaps existieren punktuell: `swap_exists_self` (jedes Selbst-Paar),
  Kür `swap_exists_of_comm` (jedes kommutierende Paar);
* **bewiesen** — keine uniforme Swap-Zuordnung über alle Endofunktor-Paare:
  `no_swap_witness` (Instanz), `no_uniform_swap` (Uniformität);
* **benannt** — die klassen-quantifizierte *Triaden*-Fassung: die Paar-Uniformität
  ist die stärkere Quantifikation, ihre Widerlegung impliziert die Triaden-Widerlegung
  NICHT; der einzige heute baubare `ModalTwoCategory`-Bewohner ist degeneriert und
  kommutiert — Folge-Posten **17b: der nicht-degenerierte Bewohner**.

## (4) Naht-Prüfstelle (stehende Vormerkung, hier erstmals scharf)

Die bewiesene Nicht-Uniformität wird weder als Beweis der Wahl-Echtheit (fünfzehnte
Schicht) noch als Triaden-Asymmetrie erzählt; die Schicht heißt nach dem Bewiesenen
(`NoUniformSwap`).

## (5) Abgrenzung

Die Sonde `Reformulation/Diagnostics/SwapSatzProbe.lean` bleibt als historischer
Beleg (getrennter Namespace, unangetastet). Die Proemial-Involution (γ-2-Iso,
`AlphaGamma`, `form_inhalt_vertauschungs_operativitaet`) ist das Spiegel-Bild —
dort *ist* ein Iso Datum, hier ist eine Nicht-Existenz Satz; Vermerk, keine
Behauptung.

## (6) Sorry-Bilanz und Axiom-Ist (am `#print`, nach dem Build befüllt)

0 Sorries. Axiom-Ist (per `#print axioms` am Datei-Ende): `propext`,
`Classical.choice`, `Quot.sound` in allen fünf Sätzen. Herkunft von
`Classical.choice`: die CategoryTheory- und Iso-Maschinerie (`Nonempty`, `Iso`),
nicht eigene Beweisführung. **Abweichungs-Vermerk (am Term geprüft):** die
Spec-Erwartung „erstmals `Classical.choice` im Aggregat-Profil" ist NICHT zutreffend
— `Classical.choice` ist bereits präsent, sowohl über PathC
(`ModalEndofunctor.tauOmega`) als auch INNERHALB Proemial über
`AlphaGamma.form_inhalt_vertauschungs_operativitaet`; diese Schicht führt es also
nicht neu ein. Kein `sorryAx`, kein `decide`-Axiom (das `decide` in M1/M2 ist
Kernel-Berechnung, kein Axiom).
-/

namespace Reformulation.Proemial.NoUniformSwap

open CategoryTheory

/-- Endofunktor aus `f = const 0` auf der diskreten Zwei-Punkte-Kategorie. -/
def F : Discrete (Fin 2) ⥤ Discrete (Fin 2) :=
  Discrete.functor (fun _ => Discrete.mk 0)

/-- Endofunktor aus `g = swap` (0↦1, 1↦0). -/
def G : Discrete (Fin 2) ⥤ Discrete (Fin 2) :=
  Discrete.functor (fun i => Discrete.mk (if i = 0 then 1 else 0))

/-- Das Zeugen-Paar kommutiert nicht: die Kompositionen trennen sich am
    Objekt ⟨0⟩ — `(F⋙G)⟨0⟩ = ⟨1⟩`, `(G⋙F)⟨0⟩ = ⟨0⟩`. -/
theorem comp_obj_ne :
    ((F ⋙ G).obj (Discrete.mk 0)).as ≠ ((G ⋙ F).obj (Discrete.mk 0)).as := by
  simp only [F, G, Functor.comp_obj, Discrete.functor_obj_eq_as]
  decide

/-- INSTANZ-ZEUGE: zwischen den beiden Kompositionen des Zeugen-Paares
    existiert KEIN 2-Iso — ein Natur-Iso lieferte an ⟨0⟩ einen Morphismus
    in der diskreten Kategorie, und `Discrete.eq_of_hom` erzwänge 1 = 0. -/
theorem no_swap_witness : ¬ Nonempty (F ⋙ G ≅ G ⋙ F) := by
  rintro ⟨e⟩
  have h := Discrete.eq_of_hom (e.hom.app (Discrete.mk 0))
  simp only [F, G, Functor.comp_obj, Discrete.functor_obj_eq_as] at h
  exact absurd h (by decide)

/-- UNIFORMITÄTS-WIDERLEGUNG: es gibt keine einheitliche Swap-Zuordnung,
    die für jede (kleine) Kategorie und jedes Endofunktor-Paar einen
    2-Iso `X⋙Y ≅ Y⋙X` liefert — der Zeuge widerlegt sie. Quantifiziert
    als `¬ ∀ …, Nonempty …` (keine Σ über Universen, kein `PLift`;
    `Category.{0}` gepinnt — Sondierungs-Befund). -/
theorem no_uniform_swap :
    ¬ ∀ (C : Type) [Category.{0} C] (X Y : C ⥤ C),
        Nonempty (X ⋙ Y ≅ Y ⋙ X) := by
  intro s
  exact no_swap_witness (s (Discrete (Fin 2)) F G)

/-- EHRLICHKEIT: Swaps existieren punktuell — jedes Selbst-Paar trägt den
    2-Iso trivial. Die Nicht-Existenz oben ist die der UNIFORMITÄT, nicht
    die des Phänomens. -/
theorem swap_exists_self {C : Type*} [Category C] (X : C ⥤ C) :
    Nonempty (X ⋙ X ≅ X ⋙ X) :=
  ⟨Iso.refl _⟩

/-- KÜR — woher Swaps kommen, wenn sie existieren: jedes kommutierende
    Paar trägt den 2-Iso per Gleichheits-Transport. Zusammen mit dem
    Instanz-Zeugen: die Uniformität scheitert genau an der
    Nicht-Kommutation. -/
theorem swap_exists_of_comm {C : Type*} [Category C] {X Y : C ⥤ C}
    (h : X ⋙ Y = Y ⋙ X) : Nonempty (X ⋙ Y ≅ Y ⋙ X) :=
  ⟨eqToIso h⟩

end Reformulation.Proemial.NoUniformSwap

-- #print axioms als Regressions-Wachen (Zug „Wachen-Vollzug", Datei-Vollständigkeit).
-- Ist-Ausgabe des grünen Builds (v4.30.0-rc2), pro Satz eingefroren; ab hier bricht
-- jede Axiom-Drift den Build.
open Reformulation.Proemial.NoUniformSwap in
section

/-- info: 'Reformulation.Proemial.NoUniformSwap.comp_obj_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms comp_obj_ne

/-- info: 'Reformulation.Proemial.NoUniformSwap.no_swap_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms no_swap_witness

/-- info: 'Reformulation.Proemial.NoUniformSwap.no_uniform_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms no_uniform_swap

/-- info: 'Reformulation.Proemial.NoUniformSwap.swap_exists_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms swap_exists_self

/-- info: 'Reformulation.Proemial.NoUniformSwap.swap_exists_of_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms swap_exists_of_comm
end
