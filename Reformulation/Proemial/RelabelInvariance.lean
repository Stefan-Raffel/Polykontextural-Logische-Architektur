import Reformulation.Kenogram.Basic
import Reformulation.Proemial.GeneralCloneBound

/-!
# Proemial.RelabelInvariance — die Kanonisierung gegen Umbenennung der Werte

**Ertrag, zweifach geschnitten.**

* **S1 — der Satz.** `relabel_map_of_injective`: über beliebigen Trägern mit
  entscheidbarer Gleichheit ist die Kanonisierung gegen **jede injektive
  Umbenennung** der Werte invariant, und zwar **heterogen** — die Umbenennung darf
  den Trägertyp wechseln.
* **S2 — die Instanz.** `relabel_map_negFin`: für die ordnungsumkehrende Negation
  `negFin` eines Stufenträgers. In ihrer **Aussage** kommen die Kanonisierung des
  kenogrammatischen Grundes und die Negation der Klon-Signatur zusammen vor; das
  ist die Verbindung, die dieses Modul herstellt — siehe die Messung unten.

## Was bewiesen ist, und in welcher Richtung

**Bewiesen ist, dass die Kanonisierung die Wertumkehr nicht sieht — sie wirkt auf
Normalformen als Identität.** Der Satz zeigt die **Invarianz einer bestimmten
Abbildung**, nicht die Nichtexistenz einer Darstellung. Ob die Ordnungsumkehr der
Werte auf dem kenogrammatischen Grund überhaupt darstellbar ist, ist eine andere
Frage; dieses Modul **berührt sie und beantwortet sie nicht**, und sie bleibt
offen. Die Beschreibung darf dem Satz nicht vorauslaufen.

## Warum das Modul im Proemial-Zweig liegt

Gemessen an den Kopfzeilen: der Proemial-Zweig importiert `Kenogram`, der
Kenogram-Zweig importiert **nie** `Proemial`. `negFin` liegt in
`Proemial/GeneralCloneBound.lean`; S2 braucht beides, also ist der Ort durch die
Importrichtung bestimmt und nicht gewählt. Dass S1 für sich eine rein
kenogrammatische Aussage ist, bleibt richtig — sie steht hier als die allgemeine
Form, aus der S2 folgt, nicht als Beitrag zum Proemial-Begriff.

## Die Verortung: worauf die beiden Hälften operieren

Der Tausch der Stellen (`Kenogram/PlaceSwap.lean`, `swapPlaces`) und die
Ordnungsumkehr der Werte (`negFin`) arbeiten auf verschiedenen Gegenständen: der
eine auf **Stellen** einer Reihe, die andere auf **Werten** eines Trägers. Die
Kanonisierung numeriert nach erstem Auftreten; darum sieht sie eine Umbenennung
der Werte nicht und eine Umstellung der Stellen wohl. **S1 ist die Satzform
dieser Verschiedenheit** — mehr nicht.

## Deutungsgrenzen

**Dies ist nicht die proemiale Relation.** Der Satz sagt nichts über den Wechsel
von Erkennen und Wollen, und er berührt die Grenze *eine Kopplung ist kein Grund*
nicht: aus einer Invarianz folgt nichts über einen Grund. Kein Name dieses Moduls
trägt ein Deutungswort.

Der Bestand kennt bereits `Kenogram.relabel_swapVals` — die
**Transpositionsfassung** (`swapVals a b l = l.map (Equiv.swap a b)`, homogen über
`List ℕ`). S1 verallgemeinert sie in zwei Richtungen, von der Transposition zur
beliebigen injektiven Abbildung und von `List ℕ` auf beliebige Träger; das
bestehende Lemma wird nicht konsumiert und nicht ersetzt.

## Wo die Verbindung liegt — gemessen, nicht behauptet

Am Beweisterm und am Typ, über `getUsedConstants`, Namensraum-Präfixe
`Reformulation.Kenogram` und `Reformulation.Proemial`:

| | Term, direkt | Typ | Term, transitiv |
|---|---|---|---|
| `relabel_map_of_injective` | Keno 5 · Proe 0 | Keno 1 · Proe 0 | Keno 62 · Proe 0 |
| `relabel_map_negFin` | Keno **0** · Proe 2 | Keno 1 · Proe 1 | Keno 62 · Proe 4 |

**Die Verbindung liegt in der Aussage, nicht im Beweisterm.** S2 geht über S1;
sein Term nennt darum keine kenogrammatische Konstante unmittelbar. Wer den
Beweisterm als Ort der Verbindung nennt, sagt etwas Falsches.

**Und dies ist nicht die Kontaktzahl** (`CLAUDE.md` §12). Die misst den
kenogrammatischen gegen den **kategorialen** Strang; `negFin` ist keine
kategoriale Grösse, sondern gehört zur Signatur der Klon-Schranken. Zur Eichung
mitgemessen: der benannte Träger der Kontaktzahl,
`RetractionBracket.both_strands_retract`, hat Keno 2 · Proe 3 **direkt am Term**
— eine andere Lage als hier. **Die Kontaktzahl bewegt sich durch dieses Modul
nicht.**

## Profil

`Classical.choice` ist **geerbt** und nicht hier erzeugt: `relabel_isRGS` und
`relabel_getElem?_eq_iff` tragen ihn beide (gemessen), und beide gehen in den
Beweis von S1 ein. `relabel_length` und `rgs_unique_of_pattern` sind
choice-frei. Ein choice-freier Weg ist nicht bekannt und wurde nicht gesucht —
er brauchte einen choice-freien Ersatz für die Musterkennzeichnung.

## Aggregat-Reife

Konsumiert `Kenogram.Basic` und `Proemial.GeneralCloneBound` — beides Aggregat.
Keine Sonde, keine Setzung.

Kein `sorry`, kein `axiom`, kein `: True`-Feld.
-/

open Reformulation.Kenogram
open Reformulation.Proemial.GeneralCloneBound (negFin)

namespace Reformulation.Proemial.RelabelInvariance

/-! ## Teil 1 — das Musterkriterium unter injektiver Abbildung -/

/-- Eine injektive Abbildung erhält das Gleichheitsmuster der Stellen: zwei
Stellen des Bildes stimmen genau dann überein, wenn die Stellen der Vorlage es
tun. Privat; kein eigener Posten. -/
private theorem map_pattern {α β : Type*} [DecidableEq α] [DecidableEq β]
    {f : α → β} (hf : Function.Injective f) (l : List α) (i j : ℕ) :
    (l.map f)[i]? = (l.map f)[j]? ↔ l[i]? = l[j]? := by
  simp only [List.getElem?_map]
  constructor
  · intro h
    cases hi : l[i]? <;> cases hj : l[j]? <;> simp [hi, hj] at h ⊢
    exact hf h
  · intro h; rw [h]

/-! ## Teil 2 — S1, die allgemeine Wertblindheit -/

/-- **S1.** Die Kanonisierung ist gegen jede **injektive** Umbenennung der Werte
invariant — heterogen: `f` darf den Trägertyp wechseln. Der Weg ist der von
`relabel_swapVals`, auf das allgemeine Musterkriterium gestellt: gleiche Länge,
gleiches Muster, und die Eindeutigkeit der Normalform schliesst. -/
theorem relabel_map_of_injective {α β : Type*} [DecidableEq α] [DecidableEq β]
    {f : α → β} (hf : Function.Injective f) (l : List α) :
    relabel (l.map f) = relabel l := by
  apply rgs_unique_of_pattern (relabel_isRGS _) (relabel_isRGS _)
  · rw [relabel_length, relabel_length, List.length_map]
  · intro i j
    rw [relabel_getElem?_eq_iff, relabel_getElem?_eq_iff]
    exact map_pattern hf l i j

/-! ## Teil 3 — S2, die Instanz an der ordnungsumkehrenden Negation -/

/-- `negFin m` ist injektiv. Privat; die Aussage steht im Bestand nicht und wird
hier nur als Voraussetzung von S2 gebraucht. -/
private theorem negFin_inj (m : ℕ) : Function.Injective (negFin m) := by
  intro a b h
  have hv := congrArg Fin.val h
  simp only [negFin] at hv
  have := a.isLt; have := b.isLt
  exact Fin.ext (by omega)

/-- **S2.** Für die ordnungsumkehrende Negation eines Stufenträgers: die
Kanonisierung sieht sie nicht. Die **Aussage** nennt `relabel` und `negFin`; der
Beweisterm nennt sie nicht beide, er geht über S1 (Messung im Kopf). -/
theorem relabel_map_negFin {m : ℕ} (l : List (Fin m)) :
    relabel (l.map (negFin m)) = relabel l :=
  relabel_map_of_injective (negFin_inj m) l

/-! ## Teil 4 — Statement-Pins

Voller Wortlaut links, Satz rechts — jede Drift des *Statements* bricht den Bau. -/

-- STATEMENT-PIN
example {α β : Type} [DecidableEq α] [DecidableEq β] (f : α → β)
    (hf : Function.Injective f) (l : List α) :
    relabel (l.map f) = relabel l :=
  relabel_map_of_injective hf l

-- STATEMENT-PIN
example (m : ℕ) (l : List (Fin m)) :
    relabel (l.map (negFin m)) = relabel l :=
  relabel_map_negFin l

/-! ## Teil 5 — die Axiom-Wachen (Ist-gebunden)

Ist-Ausgabe des grünen Builds. `Classical.choice` ist geerbt, siehe Kopf. -/

/-- info: 'Reformulation.Proemial.RelabelInvariance.relabel_map_of_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms relabel_map_of_injective

/-- info: 'Reformulation.Proemial.RelabelInvariance.relabel_map_negFin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms relabel_map_negFin

end Reformulation.Proemial.RelabelInvariance
