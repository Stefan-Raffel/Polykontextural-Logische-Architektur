import Reformulation.Proemial.TransjunctionCloneBound

/-!
# Proemial.ExtensionalCollapse — das Schicht-I-Differential in Zeugen-Fassung (achtzehnte Schicht)

Die erste Schicht der Architektur (Klassifizieren ≠ Klassifiziertes) bekommt hier ihr
Differential in Zeugen-Fassung: die extensionale Buchführung als instanz-quantifizierte
arme Klasse, der Kollaps als Satz („zwei Darstellungen fallen zusammen, die typentheoretisch
verschieden bleiben"), der Überschuss als benannte Funktion samt dem Satz, dass sie die arme
Klasse verlässt. Gehoben aus den Vor-Sonden (`ReflexionsrestProbe`, `LawvereVorSonde`, beide
byte-unverändert als historische Belege) in benannte, dokumentierte Aggregat-Form.

## (1) Quellen

Günthers Russell- und Typentheorie-Bezug am Reflexionsüberschuss, „der in dieser Formel nicht
aufgehen will" (*Schöpfung, Reflexion und Geschichte* 1960; quellen-fest seit der Band-III-Welle);
Tarski (1936) und Lawvere (1969) als formale Anker der Schicht I. Die Identifikation
Reflexionsüberschuss ≙ Syntax-Überschuss ist **Deutung** und so markiert — kein Lean-Satz
behauptet sie.

## (2) E&W-DREI-STUFEN-WACHE (prominent)

Bewiesen wird die *formale* Intensionalität (Term-Ebene: Konstruktor-Verschiedenheit
`func` vs. `var` — `propext`-immun im Sinn: `propext` kann die Verschiedenheit nicht
*einebnen*, anders als auf `X → Prop`, wo extensional gleiche Prädikate durch
`propext`/`funext` gleich würden; der **Beweis** von `witness_ne` selbst zieht `propext`,
dort minimal und per Wache Ist-festgeschrieben). Die *intensionale
Stufe* der dreistufigen E&W-Bindung (der Vorstellungs-Gehalt) wird **nicht** eingelöst — sie
bleibt offener V2-Posten des proemiellen Pakets. Kein Satz und kein Doc-Wort dieser Schicht
erzählt anderes.

## (3) Term-fest werden hiermit

Der Kollaps-Satz `no_extensional_separation` (instanz-quantifiziert über alle denotations-
invarianten Klassifikationen), die Diskriminator-Trennung `discriminator_separates` samt
Nicht-Invarianz `discriminator_not_invariant` (der Preis des Überschusses), die Zeugen-
Ungleichheit `witness_ne`, die Schere-N in Schicht-Form `extension_without_intension`, die
Kür `evalAt_separates_semantic`.

## (4) Bauform und Stufen-Disziplin

Faktorisierungs-Form (Erbe der fünfzehnten Schicht `DirectionChoice`): eine arme Klasse, ein
Zeugen-Paar, das sie nicht trennt, ein Überschuss, der sie verlässt. Der Kollaps-Satz ist der
dünnste der Phase — eine Zeile über dem Scharnier `witness_equiv` —, darum strengste Wort-
Kontrolle. Die arme Klasse trennt genau bis zur semantischen Differenz (Kür
`evalAt_separates_semantic`: `var 0` gegen `var 1`) und endet am Zeugen-Paar.
Reichweiten-Marke: der Kollaps ist **struktur-relativ** bewiesen — `DenotationInvariant`
quantifiziert über die Belegungen der *einen* `L`-Struktur `Fin 3`, nicht über alle
`L`-Strukturen; am Zeugen-Paar ist das folgenlos (die max-Idempotenz gilt in jedem Verband),
die modelltheoretische Fassung über alle Strukturen bleibt außerhalb (Abgrenzung 5).

## (5) Abgrenzung

**2b** (die γ-Anbindung) ist benannt und begründet vertagt — Typ-Spalt-Befund der
`LawvereVorSonde`: γ ist ein Morphismus-Iso, kein Punkt-Pfeil auf ein Funktionsobjekt;
topos-internes Lawvere fehlt in Mathlib (`CategoryTheory.Topos.Classifier` ist defs-only).
Die zwei Vor-Sonden bleiben als historische Belege (Hebungs-Muster); der Lawvere-Trakt bleibt
Sonde in eigener Sprache (Funktionen und `Set`, nicht `Term`). Keine Tarski-Undefinierbarkeits-
oder Gödel-artige Aussage wird geliefert oder behauptet.

## (6) Sorry-Bilanz und Axiom-Ist

0 Sorries. Axiom-Ist: siehe die `#guard_msgs`-Wachen am Datei-Ende (erwarteter Bereich
`propext`/`Quot.sound`, kein `Classical` erwartet, plus das Erbe von `T_not_in_clone`). Dies
ist die erste Schicht unter der `#guard_msgs`-Wache (Plan Rev4 §1): ab dem gesetzten Ist
bricht jede Axiom-Drift den Build.
-/

open FirstOrder Language

namespace Reformulation.Proemial.ExtensionalCollapse

open Reformulation.Proemial.TransjunctionCloneBound

-- ============================================================
-- Teil 1 — Zeugen-Paar und Scharnier (M1)
-- ============================================================

/-- Zeuge `s`: die syntaktische Komposition `∨(x₀, x₀)` (`func`-Konstruktor). -/
def s : L.Term (Fin 2) :=
  Term.func (l := 2) (BinaryFun.or : L.Functions 2) ![Term.var 0, Term.var 0]

/-- Zeuge `t`: die syntaktische Projektion `x₀` (`var`-Konstruktor). -/
def t : L.Term (Fin 2) := Term.var 0

/-- SCHARNIER: identische Denotation — `max (v 0) (v 0) = v 0` (Idempotenz von `max`). -/
theorem witness_equiv : ∀ v : Fin 2 → Fin 3, s.realize v = t.realize v := by
  intro v
  simp [s, t]

-- ============================================================
-- Teil 2 — Der benannte Diskriminator (M2)
-- ============================================================

/-- Der Überschuss als Funktion: trennt Kompositionen (`func`) von Projektionen (`var`) —
    die anonyme match-Funktion des Sonden-Beweises, zur benannten Funktion befördert und
    damit zitierfähig. -/
def isComposite : L.Term (Fin 2) → Bool
  | Term.var _    => false
  | Term.func _ _ => true

/-- Der Diskriminator trennt das Zeugen-Paar. -/
theorem discriminator_separates : isComposite s = true ∧ isComposite t = false :=
  ⟨rfl, rfl⟩

/-- POSITIVE HÄLFTE: die Syntax trennt das Paar. -/
theorem witness_ne : s ≠ t := by
  intro h
  have h' := congrArg isComposite h
  rw [discriminator_separates.1, discriminator_separates.2] at h'
  exact Bool.noConfusion h'

-- ============================================================
-- Teil 3 — Arme Klasse und Kollaps-Satz (M3)
-- ============================================================

/-- Die arme Klasse: denotations-invariante Klassifikationen — die extensionale Buchführung,
    instanz-quantifiziert über alle Wertebereiche und alle `F`. -/
def DenotationInvariant {β : Type*} (F : L.Term (Fin 2) → β) : Prop :=
  ∀ u w : L.Term (Fin 2), (∀ v : Fin 2 → Fin 3, u.realize v = w.realize v) → F u = F w

/-- KOLLAPS-SATZ (negative Hälfte): jede denotations-invariante Klassifikation identifiziert
    das Zeugen-Paar — „zwei Darstellungen fallen zusammen, die typentheoretisch verschieden
    bleiben" (Gestalt §4) als Theorem. Der Beweis ist eine Zeile über dem Scharnier: der
    dünnste Kollaps-Satz der Phase. Die *formale* Intensionalität ist bewiesen; die
    intensionale E&W-Stufe wird NICHT eingelöst (Rubrik 2 im Modul-Kopf). -/
theorem no_extensional_separation {β : Type*} (F : L.Term (Fin 2) → β)
    (hF : DenotationInvariant F) : F s = F t :=
  hF s t witness_equiv

-- ============================================================
-- Teil 4 — Der Preis des Überschusses und die Schere-N (M4/M5)
-- ============================================================

/-- EHRLICHKEIT: der Diskriminator ist NICHT denotations-invariant — die Trennung kostet
    exakt den Austritt aus der armen Klasse. -/
theorem discriminator_not_invariant : ¬ DenotationInvariant isComposite := by
  intro h
  have h' := no_extensional_separation isComposite h
  rw [discriminator_separates.1, discriminator_separates.2] at h'
  exact Bool.noConfusion h'

/-- SCHERE-N (gehoben aus `TransjunctionCloneBound`): Extension ohne Intension — die
    semantische Funktion `T` wird von keinem Term realisiert. Zusammen mit Teil 1–3: beide
    Richtungen der Funktion/Totalität-Schere in einer Schicht. -/
theorem extension_without_intension :
    ¬ ∃ u : L.Term (Fin 2), ∀ v : Fin 2 → Fin 3, u.realize v = T (v 0) (v 1) :=
  T_not_in_clone

-- ============================================================
-- Teil 5 — Kür: Nicht-Trivialität der armen Klasse (K1)
-- ============================================================

/-- Die Auswertungs-Klassifikation: denotations-invariant per Konstruktion. -/
def evalAt (v₀ : Fin 2 → Fin 3) : L.Term (Fin 2) → Fin 3 :=
  fun u => u.realize v₀

theorem evalAt_invariant (v₀ : Fin 2 → Fin 3) : DenotationInvariant (evalAt v₀) :=
  fun _ _ h => h v₀

/-- KÜR: die arme Klasse ist nicht trivial — sie trennt semantisch Verschiedenes (`var 0`
    gegen `var 1` an der Stelle `![0, 1]`). Die extensionale Welt trennt genau bis zur
    semantischen Differenz — und endet am Zeugen-Paar. -/
theorem evalAt_separates_semantic :
    ∃ v₀ : Fin 2 → Fin 3, evalAt v₀ (Term.var 0) ≠ evalAt v₀ (Term.var 1) := by
  refine ⟨![0, 1], ?_⟩
  simp [evalAt]

-- ============================================================
-- Teil 6 — Die `#guard_msgs`-Wache (M7; Ist-gebunden, erstmals)
-- ============================================================

-- Ist-Ausgabe des ersten grünen Builds (v4.30.0-rc2), pro Kern-Satz als Wache gesetzt.
-- Ab hier bricht jede Axiom-Drift den Build. Nie auf ein Soll gesetzt; der Ist liegt im
-- Spec-Erwartungsbereich (`propext`/`Quot.sound`, kein `Classical`).

/-- info: 'Reformulation.Proemial.ExtensionalCollapse.witness_ne' depends on axioms: [propext] -/
#guard_msgs in #print axioms witness_ne

/-- info: 'Reformulation.Proemial.ExtensionalCollapse.no_extensional_separation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms no_extensional_separation

/-- info: 'Reformulation.Proemial.ExtensionalCollapse.discriminator_not_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms discriminator_not_invariant

/-- info: 'Reformulation.Proemial.ExtensionalCollapse.extension_without_intension' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms extension_without_intension

/-- info: 'Reformulation.Proemial.ExtensionalCollapse.evalAt_separates_semantic' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms evalAt_separates_semantic

end Reformulation.Proemial.ExtensionalCollapse
