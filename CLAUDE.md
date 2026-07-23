# CLAUDE.md - Bau-Konventionen fuer dieses Repository

*PKL-Reformulierung Gotthard Guenthers in Lean 4 / Mathlib. Diese Datei bindet die
Implementations-Instanz. Projektgeschichte und Begruendungen stehen in den Niederlegungen
im iCloud-Korpus, nicht hier - hier steht nur, was beim Bauen zu tun und zu lassen ist.*

---

## 1 - Nach jedem geschlossenen Bau: Commit mit Eichwerten

Jeder abgeschlossene Bau endet mit einem Commit, dessen Nachricht die am **gruenen Build
gezaehlten** Kennzahlen fuehrt:

```
<Was gebaut wurde, eine Zeile>

Aggregat: <N> gepruefte Konstanten, <M> Axiom-Wachen ueber <D> Dateien,
AxiomGate <Stand>, Whitelist <W>, <J> Build-Jobs.
Neu: <Datei>, <k> Saetze, <w> Wachen, <s> Sorries.
```

Damit haengt jede Kennzahl an einem Commit-Hash statt an einer Uhrzeit. Ein Stichtag ohne
Zustand ist nicht nachpruefbar; ein Hash ist es.

**Nicht committen ohne gruenen Build.** `git status` vor dem Commit leer pruefen.

---

## 2 - Vor jeder Lieferung

- `lake build` laeuft durch, AxiomGate gruen.
- Fuer **jeden** neuen Satz `#print axioms` ausfuehren, das gemessene Profil verbatim in eine
  `#guard_msgs`-Wache einfrieren. Profile werden gemessen, nicht geschaetzt.
- **Keine** neuen Whitelist-Eintraege im AxiomGate, solange die Luecke nicht als Klasse D
  begruendet und dokumentiert ist. Die vier bestehenden sind der Stand.
- `Classical.choice` ist kein Fehler, aber ein Befund: wo er auftritt, gehoert er in die
  Rueckgabe. Wo er vermeidbar war, gehoert der Weg dokumentiert (Fintype-Maschinerie ueber
  Funktionsraeumen zieht ihn regelmaessig; punktweise Brueckenlemmata vermeiden ihn).

---

## 3 - Wachen

Jeder **tragende** Satz traegt eine Wache. Hilfslemmata sind ausgenommen, sofern ihr Profil
ueber die Huelle eines gewachten Satzes mitgesichert ist - Axiom-Profile sind
Huell-Eigenschaften, ein konsumierender Satz faengt Aenderungen in seinen Voraussetzungen mit.

**Ausnahme, die keine ist:** Ein Hilfssatz, an dem eine *Eigenschaft der ganzen Datei* haengt
(etwa die Classical-Freiheit), wird gewacht, auch wenn er formal Hilfslemma ist. Beispiel:
`realize_eq_of_pointwise` in `Proemial/NonUniformCloneBound.lean`.

Wachen stehen in eigenen Bloecken am Dateiende, nicht vor den Deklarationen.

---

## 4 - Im Dateikopf: Ertrag oder Benennung

Jedes neue Modul vermerkt im Doc-String, was es ist:

- **Ertrag** - liefert einen Satz, den Mathlib nicht schon hat und den man ohne den
  PKL-Begriff nicht formuliert haette.
- **Benennung** - uebersetzt einen Begriff in Lean-Syntax ohne neuen Satzgehalt. Legitim als
  Traeger, aber als solche zu kennzeichnen.

Beides ist zulaessig. Die Verwechslung ist es nicht.

---

## 5 - Nicht bauen

Drei Formalisierungen widersprechen dem Korpus oder der Quelle und sind zu vermeiden:

1. **`Disjoint K1 K2`** auf Kontextur-Traegermengen. Die Elementarkontexturen ueberlappen
   paarweise in genau einem Wert (`{0,1} ∩ {1,2} = {1}` usw.), und die Ueberlappung ist
   konstitutiv fuer die vorhandenen Schranken-Beweise.
2. **`¬ ∃ f : K1 → K2`** als Formalisierung von Diskontexturalitaet. Sein und Nichts sind bei
   Guenther isomorph und trotzdem diskontextural. Die tragfaehige Form ist
   `¬ ∃ t : L.Term, ...` - Nicht-Erzeugbarkeit im Termklon.
3. **Verbundkontextur-Folge beginnend bei 1.** Sie beginnt bei 3; die 1 gehoert zur
   Ontologien-Folge. `Definitionen.md` §3 fuehrt hier einen Off-by-one.

---

## 6 - Marken und Wortlaut-Grenzen

Deutungen werden als Deutungen gefuehrt, nicht als Saetze. Der **Dateiname** sagt, was bewiesen
ist, nicht was gedeutet wird - darum `NonUniformCloneBound` und nicht `Mediation`.

Zahlen, die ausserhalb des Korpus gerechnet wurden (Klon-Groessen, Aufzaehlungen ueber alle
Operationen), bleiben ausserhalb. In den Korpus gehoeren sie nur in Bijektions- oder
Iff-Form, nicht als Kardinalzahl-Behauptung.

Rang-Ansprueche ("erstmals", "die einzige Stelle") werden der Quelle zugeschrieben, die sie
erhebt, und nicht als Korpus-Aussage gefuehrt.

---

## 7 - Umgebung

- Lean `4.30.0-rc2`; `.lake/` ist 7,5 GB und per `.gitignore` ausgeschlossen.
- Der Quellbestand ist wenige hundert Dateien, zusammen unter 1 MB. Wer wesentlich mehr
  committet, hat die Ignore-Regel verletzt.
- `lake build` repliziert; ein vollstaendiger Neubau ist nicht noetig, um Profile zu pruefen -
  `lake env lean` auf einer generierten `#print axioms`-Datei genuegt.

---

## 8 - Lean-Fallstricke (gemessen, nicht vermutet)

Alle sechs sind an diesem Korpus aufgetreten und haben Zeit gekostet. Sie stehen hier, damit
sie nicht ein zweites Mal gefunden werden muessen.

**1 - `Fin n`-Subtraktion ist modular.** `|a - b| <= 1` ueber `Fin 4` ist **nicht** die
Nachbarschaftsrelation, sondern etwas anderes. Relationen dieser Art werden als explizite Tafel
ueber `.val` geschrieben oder ueber `Nat`-Ungleichungen an `.val`. (Aus der E2-Spezifikation.)

**2 - `abbrev` statt `def` fuer alles, was `decide` sehen soll.** Bei `def P ... : Prop := ...`
findet die Instanzensuche die `Decidable`-Instanz nicht und `decide` schlaegt fehl
(*failed to synthesize Decidable*). `abbrev` ist reducible und loest es. (Vorab-Probe zu E2.)

**3 - Quantifizierung ueber Funktionsraeume zieht `Classical.choice`.** Gemessen am selben Satz:
`forall c : Fin 6 -> Bool, ...` ergab `[propext, Classical.choice, Quot.sound]`, sechs explizite
`Bool`-Argumente ergaben `[propext]`. **Wo ein endlicher Funktionsraum quantifiziert wird, sind
explizite Argumente vorzuziehen** - der Unterschied ist nicht kosmetisch, er steht im Profil.

**4 - `decide` verweigert freie Variablen im Ziel** (*Expected type must not contain free
variables*). Die angebotene Option `+revert` **kaskadiert**: sie zieht ueber Hypothesen auch
Groessen ins Ziel, die es unentscheidbar machen. Heilung: die Abhaengigen vorher mit `clear`
entfernen, wenn das Ziel sie ohnehin nicht mehr braucht. (E2-Bau.)

**5 - `decide +revert` ueber grosse Fallzahlen laeuft in den `whnf`-Timeout.** Bei ~4096
Kombinationen gemessen (200 000 Heartbeats). **Die Heartbeat-Grenze nicht heraufsetzen** -
stattdessen pro Koordinate Fallzug und die Mischfaelle per `show`-defeq auf einen konkreten
Widerspruch reduzieren; die Auswertung geschieht dann in der Definitional-Pruefung. (E2-Bau.)

**6 - `rw [ht ![x, u], ...]` scheitert am Token `]]`.** Die Klammerform `ht (![x, u])`
funktioniert. (E1 und E2, beide Male.)

---

## 9 - Schranken: Robustheit gegen Signatur-Erweiterung pruefen

Eine Nicht-Erzeugbarkeits-Schranke haengt an ihrer Invariante. Wird die Signatur um Konstanten
erweitert, faellt die Schranke genau dann nicht, wenn die Invariante jedes `(c,c)` enthaelt -
also **reflexiv** ist.

| Zeuge | Invariante | ueberlebt Konstanten |
|---|---|---|
| `TransjunctionCloneBound` | Elementarkontextur `{0,2}` | **nein** (`1` liegt nicht darin) |
| `QuaternaryCloneBound` | `R_4`, reflexiv | **ja** |

**Vor dem Bau einer neuen Schranke ist zu pruefen, ob ihre Invariante reflexiv ist**, und das
Ergebnis gehoert in den Doc-String. Eine Schranke, die an einer hinzugefuegten Konstante faellt,
behauptet weniger, als sie zu behaupten scheint - das ist kein Fehler, aber es muss dastehen.