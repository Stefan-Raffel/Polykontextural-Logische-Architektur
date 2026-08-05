import Reformulation.Proemial.AsymmetricDiscontexturality
import Reformulation.Proemial.ProemialInversionProbe
import Reformulation.Proemial.K4DiscontexturalityProbe
import Reformulation.Proemial.TowerAsymmetryProbe
import Reformulation.Proemial.AsymmetricDiscontexturalTransition

/-!
# Proemial.AsymmetricDiscontexturalityProbeRegister — Sonden-Anschluss des Zeugenregisters

STANDALONE, NICHT im Aggregat (wie `ProemialInversionProbe`/
`K4DiscontexturalityProbe`, deren Zeugen hier konsumiert werden). Diese Datei
darf erst dann in `Reformulation/Proemial.lean` aufgenommen werden, wenn die
Sonden selbst den Sonden-Status verlassen.

**Benennung.** Kein neuer Satz. Die Datei schließt die beiden
Faser-Asymmetrie-Zeugen der Standalone-Sonden an das Zeugenregister
`AsymmetricDiscontexturality` an (Beweisart 4, `FiberAsymmetryWitness`):

- `ProemialInversionProbe.split_epi_not_iso` — `descent` ist split epi
  (Retraktion `descent ∘ extend = id`), aber kein Iso (nicht injektiv auf
  `RGS 3`): die Abwärtsbewegung ist kanonisch, die Aufwärtsbewegung eine Wahl
  unter Fasern.
- `K4DiscontexturalityProbe.descent_not_factoring` — `descent` faktorisiert
  nicht durch die Vergröberung `deutero`: der Stufenabstieg ist kein
  schicht-internes Datum.

Die Statements werden über lokale `abbrev`s wörtlich re-zitiert (kein
STATEMENT-PIN-Marker — konsumierende Theoreme, keine `example`-Pins; Entscheid
im Dateikopf von `AsymmetricDiscontexturality`).

## Der gebundene Zeuge (Verbindungssatz-Eintrag, kein neuer Wrapper-Typ)

Über die beiden ungebundenen Faser-Zeugen hinaus führt diese Datei einen
**Verweis-Eintrag** auf den Verbindungssatz `TowerAsymmetryProbe.tower_asymmetric`
und seine gebündelte Form `AsymmetricTransition.towerTransition`. Der
Verbindungssatz bindet Beweisart 4 (Faser-Asymmetrie) und Beweisart 5
(Irreversibilität) samt Substruktur-Erhaltung an **einem** Träger — der erste
Zeuge im Korpus, der die drei Merkmale der asymmetrischen Diskontexturalität
zugleich trägt.

**Ausdrücklich kein siebter Wrapper-Typ:** die Bindung ist keine neue
Beweisart, sondern die Verschaltung zweier vorhandener. Der Eintrag ist darum
ein reiner Re-Export (`tower_asymmetric_bound`), kein neuer `…Witness`-Typ. Die
verbleibende Grenze — der gebundene Zeuge entscheidet KA nur **modulo** der
markierten Identifikation „Stufenwechsel = Kontexturwechsel" — ist im Dateikopf
von `AsymmetricDiscontexturalTransition` benannt.

**Wachenlos mit Vermerk.** Der zitierte Zeuge `ProemialInversionProbe.split_epi_not_iso`
trägt seit dem K1-Zug (5. August 2026) eine eigene Wache, ebenso die übrigen drei Sätze
seiner Datei und die zehn der Sonden `A1DescentProbe`, `A3CoarseningProbe` und
`K3CouplingProbe`; alle vierzehn sind über das Target `Probes` erzwungen. Der zweite
zitierte Zeuge `K4DiscontexturalityProbe.descent_not_factoring` ist davon **nicht**
erfasst — jene Sonde führt den Wortlaut „vor dem proemialen Entwurf ρ" nicht und stand
darum ausserhalb der K1-Menge; ihre neun Sätze sind ungewacht.

Diese Datei selbst bleibt wachenlos. Ihre zwei Sätze sind Einpackungen
(`⟨split_epi_not_iso⟩`, `⟨descent_not_factoring⟩`) und tragen keinen Gehalt über die
eingepackten Zeugen hinaus; das Profil von `split_epi_not_iso` ist seit K1 an der Quelle
gewacht, das von `descent_not_factoring` nicht. Bei einem späteren Aggregatanschluss sind
Wachen nachzurüsten und die Eichwerte neu zu messen (CLAUDE.md §§1–3).

## Status

Benennung, 0 Sorries. Validierung per
`lake env lean Reformulation/Proemial/AsymmetricDiscontexturalityProbeRegister.lean`.
-/

namespace Reformulation.Proemial.AsymmetricDiscontexturalityProbeRegister

open Reformulation.Kenogram (RGS)
open Reformulation.Proemial.A1DescentProbe (descent)
open Reformulation.Proemial.A3CoarseningProbe (deutero)
open Reformulation.Proemial.ProemialInversionProbe (extend split_epi_not_iso)
open Reformulation.Proemial.K4DiscontexturalityProbe (descent_not_factoring)
open Reformulation.Proemial.AsymmetricDiscontexturality (FiberAsymmetryWitness)
open Reformulation.Proemial.TowerAsymmetryProbe (tower_asymmetric)

/-- Das Statement von `ProemialInversionProbe.split_epi_not_iso`, wörtlich
    re-zitiert: Retraktion für alle Stufen, Nicht-Injektivität auf `RGS 3`. -/
abbrev SplitEpiNotIsoStatement : Prop :=
  (∀ {n : ℕ} (r : RGS n) (k : ℕ) (hk : k ≤ r.val.foldr max 0 + 1)
      (h0 : r.val = [] → k = 0), descent (extend r k hk h0) = r)
  ∧ (∃ (a b : RGS 3), a ≠ b ∧ descent a = descent b)

/-- Das Statement von `K4DiscontexturalityProbe.descent_not_factoring`,
    wörtlich re-zitiert: keine Funktion auf den Vergröberungen vertauscht mit
    dem Abstieg. -/
abbrev DescentNotFactoringStatement : Prop :=
  ¬ ∃ f : Multiset ℕ → Multiset ℕ, ∀ (r : RGS 3), deutero (descent r) = f (deutero r)

/-- **Zeuge zu Beweisart 4 (Sonde-N).** Split epi ohne Iso: die proemielle
    Inversion trägt auf der kenogrammatischen Schicht genau die Substanz, die
    der Iso-Kollaps nicht trüge. -/
theorem split_epi_not_iso_witness :
    FiberAsymmetryWitness SplitEpiNotIsoStatement :=
  ⟨split_epi_not_iso⟩

/-- **Zeuge zu Beweisart 4 (K4-2).** Der Abstieg faktorisiert nicht durch die
    schicht-interne Vergröberung — die Faser-Asymmetrie sitzt quer zur
    A3-Achse. -/
theorem descent_not_factoring_witness :
    FiberAsymmetryWitness DescentNotFactoringStatement :=
  ⟨descent_not_factoring⟩

/-- **Verbindungssatz-Eintrag (Re-Export, kein Wrapper-Typ).** Der gebundene
    Zeuge: Richtung, Substruktur-Erhaltung und Determinationsverlust an einem
    Träger. Reiner `alias` auf `TowerAsymmetryProbe.tower_asymmetric` — die
    Bindung von Beweisart 4 und 5, keine neue Beweisart. Das Profil ist im Turm
    gewacht (`[propext, Quot.sound]`); der Re-Export erbt es. -/
alias tower_asymmetric_bound := tower_asymmetric

end Reformulation.Proemial.AsymmetricDiscontexturalityProbeRegister
