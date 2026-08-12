import Reformulation.Kenogram.ReverseCanonical

/-!
# Reformulation.Proemial.ReferenceReversal — Umkehrung und Verweisrelation

**Ertrag.** Eine Involution auf kenogrammatischen Normalformen und ihre Wirkung
auf eine Relation zwischen Stellen.

1. **Involution** (`revAt_involutive`) — auf Normalformen ist die kanonisierte
   Umkehrung selbstinvers.
2. **Spiegelung** (`refRel_revAt`) — die Verweisrelation geht unter der
   Umkehrung in ihre gespiegelte Fassung über: was an den Stellen `i < j` galt,
   gilt danach an den gespiegelten Stellen in umgekehrter Reihenfolge.
3. **Fixpunkte** (`revAt_fixpoint_iff`) — eine Normalform bleibt genau dann fest,
   wenn ihr Gleichheitsmuster spiegelsymmetrisch ist.

## Was hier nicht beansprucht wird

**Kein proemialer Umtausch.** Die Relation verbindet zwei **Relata**: die
verweisende und die verwiesene Stelle. Der Relator ist bei Günther das
**Verbindende** und keines der verbundenen Glieder (*Cognition and Volition*,
S. 19: *„The relata are the entities which are connected by a relationship, the
relator"*). Was hier steht, hat die Form, die Günther auf S. 20 von der
Proemialrelation **abhebt**: den klassischen Symmetrietausch, in dem nur die
Relata ihre Plätze wechseln.

**Das ist keine Einschränkung, die nachgereicht wird, sondern die Bestimmung des
Moduls.** Es ist kein Träger für `Definitionen.md` §20, und keiner seiner Sätze
wird dort geführt.

## Die Fixpunkte, mit Kriterium

Eine Normalform ist genau dann fest, wenn ihr Gleichheitsmuster unter der
Spiegelung der Stellen erhalten bleibt. Die Diagonale `[0,1,...,n-1]` erfüllt das
auf jeder Stufe und ist damit stets ein Fixpunkt.

**Dies ist als Kriterium notiert und nicht als Mangel.** *Fixpunktfrei* war eine
Bedingung dieses Bestandes und keine Forderung der Quelle; Günthers
Negationssystem umfasst *„all possible permutations between the values"*
(*Cognition and Volition*, S. 24), und ob es Fixpunkte ausschliesst, sagt er
nicht.

## Verwendung gegen Erweiterung

`refRel_revAt` und `revAt_involutive` **verwenden** die Kanonisierungs-Theorie des
Bestandes — Muster-Treue, Längensatz, Eindeutigkeit der Normalform.
`Kenogram.relabel_reverse_relabel`, das die Involutivität trägt, **erweitert**
sie: einen Satz über `relabel` und `reverse` führte der Bestand nicht.

## Zur Bezeichnung `refRel`

Der Name ist **beschreibend** und benennt keine Kategorie der Quelle. Gemeint ist:
zwei Stellen tragen dieselbe Marke, und die eine steht vor der anderen.

Der Bestand führt die **ungeordnete** Fassung dieser Sache — `rgsToPartition` über
`Setoid.ker (rgsFun r)`, mit der Aussage, dass zwei Stellen genau dann im selben
Block liegen, wenn sie denselben Wert tragen (`Kenogram.Basic`). `refRel` ist
diese Blockrelation **zuzüglich der Stellenordnung**; einen Begriff dafür führt
der Bestand nicht.
-/

namespace Reformulation.Proemial.ReferenceReversal

open Reformulation.Kenogram

/-- Die kanonisierte Umkehrung der Stellenordnung. -/
def revAt (l : List ℕ) : List ℕ := relabel l.reverse

/-- Die Verweisrelation: die Stelle `j` trägt dieselbe Marke wie die frühere
Stelle `i`. Die Schranke `j < l.length` gehört zur Sache — ausserhalb der Liste
gibt es keine Stellen. -/
def refRel (l : List ℕ) (i j : ℕ) : Prop :=
  i < j ∧ j < l.length ∧ l[i]? = l[j]?

/-- Die Umkehrung erhält die Länge. -/
@[simp] theorem revAt_length (l : List ℕ) : (revAt l).length = l.length := by
  rw [revAt, relabel_length, List.length_reverse]

/-- Die Umkehrung liefert eine Normalform, ohne Voraussetzung an das Argument. -/
theorem revAt_isRGS (l : List ℕ) : IsRGS (revAt l) := relabel_isRGS _

/-- **Die Umkehrung ist auf Normalformen selbstinvers.** Der Schritt, der es
trägt, ist `Kenogram.relabel_reverse_relabel`: die Kanonisierung im Inneren darf
entfallen, und danach hebt die zweifache Umkehrung der Stellen sich auf. -/
theorem revAt_involutive {l : List ℕ} (h : IsRGS l) : revAt (revAt l) = l := by
  unfold revAt
  rw [relabel_reverse_relabel, List.reverse_reverse, relabel_eq_self_of_isRGS h]

/-- **Die Verweisrelation wird gespiegelt.** Unter der Umkehrung besteht sie an
den Stellen `i < j` genau dann, wenn sie zuvor an den gespiegelten Stellen
bestand — mit vertauschter Reihenfolge, weil die Spiegelung die Stellenordnung
umkehrt. Die Aussage braucht `IsRGS` nicht. -/
theorem refRel_revAt (l : List ℕ) (i j : ℕ) (hj : j < l.length) :
    refRel (revAt l) i j ↔ refRel l (l.length - 1 - j) (l.length - 1 - i) := by
  unfold refRel revAt
  rw [relabel_length, List.length_reverse]
  constructor
  · rintro ⟨hij, hjl, hpat⟩
    have hi : i < l.length := lt_trans hij hjl
    rw [relabel_getElem?_eq_iff, List.getElem?_reverse hi,
        List.getElem?_reverse hjl] at hpat
    exact ⟨by omega, by omega, hpat.symm⟩
  · rintro ⟨hij, hjl', hpat⟩
    have hi : i < l.length := by omega
    refine ⟨by omega, hj, ?_⟩
    rw [relabel_getElem?_eq_iff, List.getElem?_reverse hi, List.getElem?_reverse hj]
    exact hpat.symm

/-- **Die Fixpunkte, gekennzeichnet.** Eine Normalform bleibt genau dann fest,
wenn ihr Gleichheitsmuster die Spiegelung übersteht — wenn also zwei Stellen der
umgekehrten Folge genau dann dieselbe Marke tragen, wenn die entsprechenden
Stellen der Folge selbst es tun. -/
theorem revAt_fixpoint_iff {l : List ℕ} (h : IsRGS l) :
    revAt l = l ↔ ∀ i j : ℕ, (l.reverse[i]? = l.reverse[j]? ↔ l[i]? = l[j]?) := by
  constructor
  · intro hfix i j
    rw [← relabel_getElem?_eq_iff l.reverse i j]
    show (revAt l)[i]? = (revAt l)[j]? ↔ _
    rw [hfix]
  · intro hpat
    apply rgs_unique_of_pattern (relabel_isRGS _) h
    · rw [relabel_length, List.length_reverse]
    · intro i j
      rw [relabel_getElem?_eq_iff]
      exact hpat i j

/-! ## Wachen -/

-- STATEMENT-PIN
example {l : List ℕ} (h : IsRGS l) : revAt (revAt l) = l := revAt_involutive h

-- STATEMENT-PIN
example (l : List ℕ) (i j : ℕ) (hj : j < l.length) :
    refRel (revAt l) i j ↔ refRel l (l.length - 1 - j) (l.length - 1 - i) :=
  refRel_revAt l i j hj

/-- info: 'Reformulation.Proemial.ReferenceReversal.revAt' does not depend on any axioms -/
#guard_msgs in #print axioms revAt

/-- info: 'Reformulation.Proemial.ReferenceReversal.refRel' depends on axioms: [propext] -/
#guard_msgs in #print axioms refRel

/-- info: 'Reformulation.Proemial.ReferenceReversal.revAt_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms revAt_length

/-- info: 'Reformulation.Proemial.ReferenceReversal.revAt_isRGS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms revAt_isRGS

/-- info: 'Reformulation.Proemial.ReferenceReversal.revAt_involutive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms revAt_involutive

/-- info: 'Reformulation.Proemial.ReferenceReversal.refRel_revAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms refRel_revAt

/-- info: 'Reformulation.Proemial.ReferenceReversal.revAt_fixpoint_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms revAt_fixpoint_iff

end Reformulation.Proemial.ReferenceReversal
