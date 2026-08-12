import Reformulation.Kenogram.Basic

/-!
# Reformulation.Kenogram.ReverseCanonical — Kanonisierung und Umkehrung

**Ertrag.** Ein Satz über das Zusammenspiel von `relabel` und `List.reverse`:

```text
relabel (relabel l).reverse = relabel l.reverse
```

**Die Kanonisierung vor der Umkehrung ist unschädlich.** Wer erst kanonisiert und
dann umkehrt, kommt auf dieselbe Normalform wie der, der erst umkehrt.

**Dies ist eine Erweiterung der Kanonisierungs-Theorie und kein Verbrauch.** Der
Bestand führt Sätze über `relabel` unter Abbildung der Werte
(`relabel_map_of_injective`), unter Präfixbildung (`relabel_take`) und unter dem
Abstieg (`relabel_dropLast`); über das Zusammenspiel mit der Umkehrung führt er
keinen. Der Beweis geht über die Eindeutigkeit der Normalform
(`rgs_unique_of_pattern`) und die Muster-Treue (`relabel_getElem?_eq_iff`), mit
vollständiger Fallunterscheidung über die Bereichsgrenzen.

## Reichweite

Die Aussage läuft über **beliebige** `List ℕ` und braucht `IsRGS` nicht. Sie ist
damit allgemeiner als ihre Anwendung: `Proemial.ReferenceReversal` benutzt sie,
um die Involutivität der Umkehrung **auf Normalformen** zu zeigen, und dort
kommt die Voraussetzung erst hinzu.

## Ablage

Die Datei liegt im Kenogram-Zweig, weil ihr Satz ausschliesslich über `relabel`
und `reverse` spricht. **Kein `Proemial`-Import** — die Freiheit des
Kenogram-Zweigs von der Gegenrichtung ist eine Datei-Eigenschaft und bleibt es.
-/

namespace Reformulation.Kenogram

/-- **Die Kanonisierung vor der Umkehrung ist unschädlich.** Beide Seiten sind
Normalformen gleicher Länge; ihr Gleichheitsmuster stimmt überein, weil `relabel`
das Muster erhält und die Umkehrung die Stellen nur umnummeriert. Die
Fallunterscheidung deckt die Bereichsgrenzen mit ab: ausserhalb liefern beide
`none`, und `none` ist mit `some` nicht vergleichbar. -/
theorem relabel_reverse_relabel (l : List ℕ) :
    relabel (relabel l).reverse = relabel l.reverse := by
  apply rgs_unique_of_pattern (relabel_isRGS _) (relabel_isRGS _)
  · rw [relabel_length, relabel_length, List.length_reverse, List.length_reverse,
        relabel_length]
  · intro i j
    rw [relabel_getElem?_eq_iff, relabel_getElem?_eq_iff]
    by_cases hi : i < l.length
    · by_cases hj : j < l.length
      · rw [List.getElem?_reverse (by rwa [relabel_length]),
            List.getElem?_reverse (by rwa [relabel_length]),
            List.getElem?_reverse hi, List.getElem?_reverse hj,
            relabel_length, relabel_getElem?_eq_iff]
      · have h1 : ((relabel l).reverse)[j]? = none := by
          rw [List.getElem?_eq_none_iff]; simp [relabel_length]; omega
        have h2 : (l.reverse)[j]? = none := by
          rw [List.getElem?_eq_none_iff]; simp; omega
        have h3 : ((relabel l).reverse)[i]? ≠ none := by
          rw [ne_eq, List.getElem?_eq_none_iff]; simp [relabel_length]; omega
        have h4 : (l.reverse)[i]? ≠ none := by
          rw [ne_eq, List.getElem?_eq_none_iff]; simp; omega
        rw [h1, h2]
        exact ⟨fun h => absurd h h3, fun h => absurd h h4⟩
    · by_cases hj : j < l.length
      · have h1 : ((relabel l).reverse)[i]? = none := by
          rw [List.getElem?_eq_none_iff]; simp [relabel_length]; omega
        have h2 : (l.reverse)[i]? = none := by
          rw [List.getElem?_eq_none_iff]; simp; omega
        have h3 : ((relabel l).reverse)[j]? ≠ none := by
          rw [ne_eq, List.getElem?_eq_none_iff]; simp [relabel_length]; omega
        have h4 : (l.reverse)[j]? ≠ none := by
          rw [ne_eq, List.getElem?_eq_none_iff]; simp; omega
        rw [h1, h2]
        exact ⟨fun h => absurd h.symm h3, fun h => absurd h.symm h4⟩
      · have h1 : ((relabel l).reverse)[i]? = none := by
          rw [List.getElem?_eq_none_iff]; simp [relabel_length]; omega
        have h2 : ((relabel l).reverse)[j]? = none := by
          rw [List.getElem?_eq_none_iff]; simp [relabel_length]; omega
        have h3 : (l.reverse)[i]? = none := by
          rw [List.getElem?_eq_none_iff]; simp; omega
        have h4 : (l.reverse)[j]? = none := by
          rw [List.getElem?_eq_none_iff]; simp; omega
        simp [h1, h2, h3, h4]

/-! ## Wache -/

-- STATEMENT-PIN
example (l : List ℕ) : relabel (relabel l).reverse = relabel l.reverse :=
  relabel_reverse_relabel l

/--
info: 'Reformulation.Kenogram.relabel_reverse_relabel' depends on axioms: [propext,
Classical.choice,
Quot.sound]
-/
#guard_msgs in #print axioms relabel_reverse_relabel

end Reformulation.Kenogram
