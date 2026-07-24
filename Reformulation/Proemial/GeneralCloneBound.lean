import Reformulation.Proemial.NonUniformCloneBound

/-!
# Proemial.GeneralCloneBound — die Charakterisierung für alle m ≥ 4 (Kairos, E3)

**Ertrag.** Der Zielsatz (`locally_classical_in_clone_iff`) hebt E2 von der festen
Wertzahl ab:

> Für **jedes m ≥ 4** gilt: eine lokal-klassische Operation auf `Fin m` liegt
> **genau dann** im Klon von `{min, max, neg}`, wenn sie `min` oder `max` ist.

Kein `decide`, keine Fallunterscheidung nach m; Induktion läuft allein über
Weglängen (Sonde 19). Die Einordnung „der erste Satz des Projekts, der nicht an
einer festen Wertzahl hängt" erhebt die E3-Spezifikation (§1); sie trifft die
Klon-Schranken-Reihe D → E1 → E2, deren bisherige Sätze sämtlich bei festem
m = 3 bzw. m = 4 liegen.

**Die Schranke `m ≥ 4` ist wesentlich, keine Bequemlichkeit.** Bei `m = 3` ist der
Satz **falsch**: dort sind vier der acht Wahlmuster erzeugbar (E1,
`four_of_eight_generatable`). Der Grund steht in dieser Datei am Bau: die beiden
Randkanten `Xb`/`Xt` brechen über die **Ausschlusspunkte** von `R m` (unten), und bei
`m = 3` kollidieren diese Punkte mit dem Abstiegsgerüst — `Xb` bräuchte `(2,1) ∈ R`,
das bei `m = 3` gerade der Ausschlusspunkt `(m−1, m−2)` ist; `Xt` bräuchte
`(m−3, m−2) = (0,1)` (Sonde 19 §3).

## Beweismittel: die Invariante `R m` und das Kantengerüst (Sonde 18/19)

`R m` ist die Nachbarschaftsrelation `|a−b| ≤ 1` der linearen Ordnung auf `Fin m`,
an beiden Enden um die Randpaare `(0,1)` und `(m−1, m−2)` gebrochen — die uniforme
Formel der Sonde 17, hier in **Disjunktionsform** (`≠ ∨ ≠` statt `¬(= ∧ =)`), weil
eine negierte Konjunktion als Hypothese `omega` in klassische Logik zwingt
(Vorab-Bauprobe der E3-Spezifikation §4). Die Basis erhält `R m`
(`min_pres`/`max_pres`/`neg_pres`), also erhält jeder Term `R m` (`R_is_invariant`,
dieselbe `Term.realize_mem`-Verschaltung wie in E1/E2 — keine eigene Induktion).

An die Stelle des E2-`decide` (`mixed_breaks`, 64 Fälle) tritt das **Kantengerüst**
der Sonde 19: sechs Familien von Kontexturpaaren mit geschlossen angebbarer
Bruchstelle (`break_F1` … `break_Xt`). Wirkt `f` auf der einen Kontextur als `min`
und auf der anderen als `max`, wirft die Bruchstelle das Bild aus `R m` hinaus —
reine Arithmetik über `|a−b| ≤ 1`, uniform in m.

**Die Ausschlusspunkte tragen den Abstieg.** `break_Xb` bricht mit Bild **genau**
`(0,1)`, `break_Xt` mit Bild **genau** `(m−1, m−2)` — die beiden aus der
Nachbarschaft herausgenommenen Paare, in E2 noch Randnotiz der Formel, sind hier
das Beweismittel, ohne das der Abstieg von `max`-Kontexturen zu `min`-Kontexturen
nicht schließt. Das ist der strukturelle Kern des Beweises.

## Bauform: Propagation statt Weg-Datenstruktur

Die Sonde-19-Auswahlregel (kanonischer Weg, erster min→max-Wechsel) ist hier in der
äquivalenten **Propagations-Form** gebaut: erhält `f` die Invariante, pflanzt sich
`ActsAsMin` **entlang** jeder Gerüst-Kante fort (`step_min`) und `ActsAsMax`
**entgegen** jeder Gerüst-Kante (`step_max`) — der erste min→max-Wechsel auf dem Weg
ist genau die Kante, an der die Propagation den Widerspruch fände. Damit zerfällt die
Wegkonstruktion in gewöhnliche `Nat.le_induction`-Ketten (`min_chain_*`,
`max_chain_*`) ohne Listen-Verschaltung: von `{0,1}` aus erreicht der Aufstieg
(F1/F2) jede Kontextur (`min_propagates`), und rückwärts durch Keller und Gipfel
(Xb, D′, D, Xt, F1) ebenso (`max_propagates`).

## Robustheit: die Schranke überlebt Konstanten

`R m` ist **reflexiv** (`R_diag`, für m ≥ 2): die Diagonale liegt ganz in `R m`,
jede Konstante erhält die Invariante, und die Charakterisierung besteht auch über
der um **alle m Konstanten** erweiterten Sprache `Lc m` fort
(`constant_clone_min_or_max`) — wie in E2 (CLAUDE.md §9), jetzt für alle m ≥ 4.

**Ein neuer, gemessener Fallstrick (Wegwerf-Probe dieser Datei):** `omega` mit einer
**Disjunktion im Ziel** zieht `Classical.choice` (Disjunktions-*Hypothesen* sind
harmlos — das Gegenstück zum Befund der E3-Spezifikation §4 über negierte
Konjunktionen als Hypothese). Heilung hier: `ne_or_ne_of_imp` wählt den Disjunkt
choice-frei per `dite` über `Nat.decEq`; `omega` bekommt nur atomare Ziele.

**Wortlaut-Grenzen (verbindlich):**

1. **Keine Zähl-Behauptung.** Der Zielsatz ist ein Iff über alle m ≥ 4; Kanten- und
   Belegungszahlen (14/31/57, 62/1022/32766) stehen in Sonde 18/19 und bleiben dort.
2. **m = 3 wird nicht mitbehauptet** — dort ist die Aussage falsch (E1); die Schranke
   `m ≥ 4` steht im Zielsatz und ist oben begründet, nicht stillschweigend gesetzt.
3. **Keine Vermittlungs-These (Marke 3).** Der Dateiname sagt `GeneralCloneBound`,
   nicht `Mediation`.
-/

open FirstOrder Language

namespace Reformulation.Proemial.GeneralCloneBound

open Reformulation.Proemial.TransjunctionCloneBound (L UnaryFun BinaryFun)
open Reformulation.Proemial.NonUniformCloneBound (varX varY tand tor)

variable {m : ℕ}

/-! ## Teil 0 — der choice-freie Disjunkt-Wähler

`omega` mit Disjunktions-Ziel zieht `Classical.choice` (gemessen, Wegwerf-Probe).
Dieser Helfer entscheidet die linke Gleichheit per `Nat.decEq` (dite, choice-frei)
und reduziert jedes `≠ ∨ ≠`-Ziel auf ein atomares `omega`-Ziel. -/

/-- Choice-freie Wahl in einem `≠ ∨ ≠`-Ziel: gilt rechts unter Annahme der linken
Gleichheit, so gilt die Disjunktion — per `dite` über `Nat.decEq`, ohne
`Classical.choice`. -/
theorem ne_or_ne_of_imp {a c b d : ℕ} (h : a = c → b ≠ d) : a ≠ c ∨ b ≠ d :=
  if hac : a = c then Or.inr (h hac) else Or.inl hac

/-! ## Teil 1 — die Struktur auf `Fin m`

Dieselbe Sprache `L` wie in E1/E2 (Symbole `¬`, `∧`, `∨`), Trägermenge `Fin m` für
beliebiges m: `∧ = min`, `∨ = max` über dem `LinearOrder`, `¬ = negFin m` (die
ordnungsumkehrende Negation `a ↦ m−1−a` über `.val` — nicht über die modulare
`Fin`-Subtraktion, CLAUDE.md §8.1). -/

/-- Die ordnungsumkehrende Negation auf `Fin m` (`a ↦ m−1−a`), über `.val` gebaut
(die `Fin`-Subtraktion wäre modular). -/
def negFin (m : ℕ) (a : Fin m) : Fin m :=
  ⟨m - 1 - a.val, by have := a.isLt; omega⟩

/-- Die Interpretation auf `Fin m`: `∧ = min`, `∨ = max`, `¬ = negFin m` — das
allgemeine Gegenstück zu `struc` (m = 3) und `struc4` (m = 4). -/
instance strucM : L.Structure (Fin m) where
  funMap := fun {n} =>
    match n with
    | 1 => fun _ x => negFin m (x 0)
    | 2 => fun f x => match f with
        | .and => min (x 0) (x 1)
        | .or => max (x 0) (x 1)
    | 0 => fun f _ => nomatch f
    | (_ + 3) => fun f _ => nomatch f
  RelMap := fun r _ => nomatch r

/-! ## Teil 2 — lokale Prädikate für allgemeines m

Bei festem m waren Kontexturtreue und lokale Klassizität endliche Konjunktionen
(E2, sechs Glieder); für allgemeines m quantifizieren sie über alle Paare `x ≠ y`.
Keine Funktionsraum-Quantifikation (CLAUDE.md §8.3). -/

/-- `f` wirkt auf `{x, y}` als Konjunktion: dort ist `f = min`. -/
def ActsAsMin (f : Fin m → Fin m → Fin m) (x y : Fin m) : Prop :=
  ∀ a b : Fin m, (a = x ∨ a = y) → (b = x ∨ b = y) → f a b = min a b

/-- `f` wirkt auf `{x, y}` als Disjunktion: dort ist `f = max`. -/
def ActsAsMax (f : Fin m → Fin m → Fin m) (x y : Fin m) : Prop :=
  ∀ a b : Fin m, (a = x ∨ a = y) → (b = x ∨ b = y) → f a b = max a b

/-- Lokale Klassizität: auf jeder Elementarkontextur `{x, y}` (x ≠ y) wirkt `f`
wie `min` oder wie `max`. -/
def LocallyClassical (f : Fin m → Fin m → Fin m) : Prop :=
  ∀ x y : Fin m, x ≠ y → ActsAsMin f x y ∨ ActsAsMax f x y

/-! ## Teil 3 — die Invariante `R m`

Die uniforme Formel der Sonde 17: Nachbarschaft `|a−b| ≤ 1`, gebrochen um die
Ausschlusspunkte `(0,1)` und `(m−1, m−2)`. **Disjunktionsform** statt negierter
Konjunktion (E3-Spezifikation §4: die Negationsform zöge über `omega`
`Classical.choice` in jede Konsum-Stelle). -/

/-- Die Invariante `R m`: Nachbarschaft in der linearen Ordnung, an beiden Enden
gebrochen. Über `ℕ`-Ungleichungen an `.val` (die `Fin`-Subtraktion wäre modular);
die Ausschlüsse als Disjunktionen. -/
def R (m : ℕ) (x y : Fin m) : Prop :=
  x.val ≤ y.val + 1 ∧ y.val ≤ x.val + 1 ∧ (x.val ≠ 0 ∨ y.val ≠ 1) ∧
    (x.val ≠ m - 1 ∨ y.val ≠ m - 2)

/-- `f` erhält `R m` (das binäre Erhaltungs-Prädikat). -/
def PreservesR (m : ℕ) (f : Fin m → Fin m → Fin m) : Prop :=
  ∀ x y u v : Fin m, R m x y → R m u v → R m (f x u) (f y v)

/-- **`R m` ist reflexiv** (für m ≥ 2): die Diagonale liegt ganz in `R m`. Der
Träger der Robustheit (Teil 7): Konstanten können `R m` nicht brechen
(CLAUDE.md §9). Bei m ≤ 1 fallen die beiden Ausschlusspunkte auf die Diagonale —
die Voraussetzung ist scharf. -/
theorem R_diag (hm : 2 ≤ m) (a : Fin m) : R m a a := by
  have := a.isLt
  exact ⟨by omega, by omega, ne_or_ne_of_imp (by omega), ne_or_ne_of_imp (by omega)⟩

/-- **`R m` ist echt (Nichttrivialitäts-Beleg, m ≥ 4):** das Nachbarpaar `(1,0)`
liegt darin, die beiden Ausschlusspunkte `(0,1)` und `(m−1, m−2)` nicht, ein
Fernpaar `(0,2)` auch nicht. Ohne diesen Beleg wäre jede Erhaltungs-Aussage über
`R m` wertlos. -/
theorem R_proper (hm : 4 ≤ m) :
    R m ⟨1, by omega⟩ ⟨0, by omega⟩ ∧ ¬ R m ⟨0, by omega⟩ ⟨1, by omega⟩ ∧
      ¬ R m ⟨m - 1, by omega⟩ ⟨m - 2, by omega⟩ ∧ ¬ R m ⟨0, by omega⟩ ⟨2, by omega⟩ := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · exact Nat.le_refl 1
  · exact Nat.zero_le 2
  · exact Or.inl Nat.one_ne_zero
  · exact Or.inl (show (1 : ℕ) ≠ m - 1 by omega)
  · rintro ⟨-, -, h3, -⟩
    rcases h3 with h | h <;> exact h rfl
  · rintro ⟨-, -, -, h4⟩
    rcases h4 with h | h <;> exact h rfl
  · rintro ⟨-, h2, -, -⟩
    exact absurd h2 (show ¬ (2 : ℕ) ≤ 0 + 1 by omega)

/-- **`min` (`∧`) erhält `R m`.** Über `Fin.coe_min` auf `ℕ`-`min` gebracht;
`omega` versteht `ℕ`-`min` nativ — die von der Spezifikation §4 erwartete Fallarbeit
über `Nat.le_total` entfällt (ihre Probe hatte das `Fin`-`min` nicht konvertiert). -/
theorem min_pres : PreservesR m (fun a b => min a b) := by
  intro x y u v hxy huv
  obtain ⟨h1, h2, h3, h4⟩ := hxy
  obtain ⟨h5, h6, h7, h8⟩ := huv
  have hx := x.isLt; have hy := y.isLt; have hu := u.isLt; have hv := v.isLt
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Fin.coe_min]
  · omega
  · omega
  · exact ne_or_ne_of_imp (by omega)
  · exact ne_or_ne_of_imp (by omega)

/-- **`max` (`∨`) erhält `R m`.** -/
theorem max_pres : PreservesR m (fun a b => max a b) := by
  intro x y u v hxy huv
  obtain ⟨h1, h2, h3, h4⟩ := hxy
  obtain ⟨h5, h6, h7, h8⟩ := huv
  have hx := x.isLt; have hy := y.isLt; have hu := u.isLt; have hv := v.isLt
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Fin.coe_max]
  · omega
  · omega
  · exact ne_or_ne_of_imp (by omega)
  · exact ne_or_ne_of_imp (by omega)

/-- **`negFin m` (`¬`) erhält `R m`.** Die Reflexion tauscht die beiden
Ausschlusspunkte gegeneinander aus. -/
theorem neg_pres : ∀ a c : Fin m, R m a c → R m (negFin m a) (negFin m c) := by
  intro a c h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have ha := a.isLt; have hc := c.isLt
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [negFin]
  · omega
  · omega
  · exact ne_or_ne_of_imp (by omega)
  · exact ne_or_ne_of_imp (by omega)

/-! ## Teil 4 — die sechs Familien-Lemmata (das Kantengerüst der Sonde 19)

Jedes Lemma: wirkt `f` auf der einen Kontextur als `min` und auf der anderen als
`max`, wirft die geschlossen angegebene Bruchstelle das Bild aus `R m` hinaus.
Reine Arithmetik über `.val`, uniform in m (nur die Randkanten `Xb`/`Xt` nennen m).
Die `ActsAs`-Hypothesen stehen am Ende, damit die partielle Anwendung direkt die
`hbreak`-Form der Schritt-Lemmata (Teil 5) liefert.

| Familie | Kante (min → max) | Bruchstelle | Bild |
|---|---|---|---|
| F1 | `{a,b} → {a,b+1}` | `((a,a),(b,b+1))` | `(a,b+1)` |
| F2 | `{a,b} → {a+1,b}`, `a+1<b` | `((a+1,a),(b,b))` | `(b,a)` |
| D | `{s+1,t} → {s,t}`, `t≥s+3` | `((s+1,s),(t,t))` | `(s+1,t)` |
| D′ | `{s,t+1} → {s,t}`, `t≥s+2` | `((s,s),(t,t+1))` | `(t,s)` |
| Xb | `{0,2} → {0,1}` | `((2,1),(0,0))` | **`(0,1)`** |
| Xt | `{m−2,m−1} → {m−3,m−1}` | `((m−3,m−2),(m−1,m−1))` | **`(m−1,m−2)`** |

`Xb` und `Xt` brechen über die **Ausschlusspunkte selbst** — ihr Bild ist genau das
herausgenommene Randpaar. -/

/-- **Familie F1** (`{x,u} → {x,v}` mit `v = u+1`, Aufstieg im oberen Element):
Bruchstelle `((x,x),(u,v))`, Bild `(x,v)` — verletzt die Nachbarschaft, weil
`v ≥ x+2`. -/
theorem break_F1 (f : Fin m → Fin m → Fin m) (x u v : Fin m)
    (hxu : x.val < u.val) (hv : v.val = u.val + 1)
    (hmin : ActsAsMin f x u) (hmax : ActsAsMax f x v) :
    ¬ PreservesR m f := by
  intro hpres
  have hx := x.isLt; have hu := u.isLt; have hvlt := v.isLt
  have hRxx : R m x x :=
    ⟨by omega, by omega, ne_or_ne_of_imp (by omega), ne_or_ne_of_imp (by omega)⟩
  have hRuv : R m u v :=
    ⟨by omega, by omega, ne_or_ne_of_imp (by omega), ne_or_ne_of_imp (by omega)⟩
  have h := hpres x x u v hRxx hRuv
  rw [hmin x u (Or.inl rfl) (Or.inr rfl), hmax x v (Or.inl rfl) (Or.inr rfl)] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [Fin.coe_min, Fin.coe_max] at h1 h2
  omega

/-- **Familie F2** (`{x,u} → {v,u}` mit `v = x+1 < u`, Aufstieg im unteren
Element): Bruchstelle `((v,x),(u,u))`, Bild `(u,x)` — verletzt die Nachbarschaft,
weil `u ≥ x+2`. -/
theorem break_F2 (f : Fin m → Fin m → Fin m) (x u v : Fin m)
    (hv : v.val = x.val + 1) (hvu : v.val < u.val)
    (hmin : ActsAsMin f x u) (hmax : ActsAsMax f v u) :
    ¬ PreservesR m f := by
  intro hpres
  have hx := x.isLt; have hu := u.isLt; have hvlt := v.isLt
  have hRvx : R m v x :=
    ⟨by omega, by omega, ne_or_ne_of_imp (by omega), ne_or_ne_of_imp (by omega)⟩
  have hRuu : R m u u :=
    ⟨by omega, by omega, ne_or_ne_of_imp (by omega), ne_or_ne_of_imp (by omega)⟩
  have h := hpres v x u u hRvx hRuu
  rw [hmax v u (Or.inl rfl) (Or.inr rfl), hmin x u (Or.inl rfl) (Or.inr rfl)] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [Fin.coe_min, Fin.coe_max] at h1 h2
  omega

/-- **Familie D** (`{v,u} → {x,u}` mit `v = x+1`, `u ≥ x+3`, Abstieg im unteren
Element): Bruchstelle `((v,x),(u,u))`, Bild `(v,u)` — verletzt die Nachbarschaft,
weil `u ≥ v+2`. -/
theorem break_D (f : Fin m → Fin m → Fin m) (x u v : Fin m)
    (hv : v.val = x.val + 1) (hd : x.val + 3 ≤ u.val)
    (hmin : ActsAsMin f v u) (hmax : ActsAsMax f x u) :
    ¬ PreservesR m f := by
  intro hpres
  have hx := x.isLt; have hu := u.isLt; have hvlt := v.isLt
  have hRvx : R m v x :=
    ⟨by omega, by omega, ne_or_ne_of_imp (by omega), ne_or_ne_of_imp (by omega)⟩
  have hRuu : R m u u :=
    ⟨by omega, by omega, ne_or_ne_of_imp (by omega), ne_or_ne_of_imp (by omega)⟩
  have h := hpres v x u u hRvx hRuu
  rw [hmin v u (Or.inl rfl) (Or.inr rfl), hmax x u (Or.inl rfl) (Or.inr rfl)] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [Fin.coe_min, Fin.coe_max] at h1 h2
  omega

/-- **Familie D′** (`{x,v} → {x,u}` mit `v = u+1`, `u ≥ x+2`, Abstieg im oberen
Element): Bruchstelle `((x,x),(u,v))`, Bild `(u,x)` — verletzt die Nachbarschaft,
weil `u ≥ x+2`. -/
theorem break_D' (f : Fin m → Fin m → Fin m) (x u v : Fin m)
    (hv : v.val = u.val + 1) (hd : x.val + 2 ≤ u.val)
    (hmin : ActsAsMin f x v) (hmax : ActsAsMax f x u) :
    ¬ PreservesR m f := by
  intro hpres
  have hx := x.isLt; have hu := u.isLt; have hvlt := v.isLt
  have hRxx : R m x x :=
    ⟨by omega, by omega, ne_or_ne_of_imp (by omega), ne_or_ne_of_imp (by omega)⟩
  have hRuv : R m u v :=
    ⟨by omega, by omega, ne_or_ne_of_imp (by omega), ne_or_ne_of_imp (by omega)⟩
  have h := hpres x x u v hRxx hRuv
  rw [hmax x u (Or.inl rfl) (Or.inr rfl), hmin x v (Or.inl rfl) (Or.inr rfl)] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [Fin.coe_min, Fin.coe_max] at h1 h2
  omega

/-- **Randkante Xb** (`{0,2} → {0,1}`, m ≥ 4): Bruchstelle `((2,1),(0,0))`, Bild
**genau der Ausschlusspunkt `(0,1)`** — der Keller-Abstieg, den es bei `m = 3`
nicht gibt (dort ist `(2,1)` selbst der Ausschlusspunkt `(m−1,m−2)`). -/
theorem break_Xb (f : Fin m → Fin m → Fin m) (hm : 4 ≤ m) (z o t : Fin m)
    (hz : z.val = 0) (ho : o.val = 1) (ht : t.val = 2)
    (hmin : ActsAsMin f z t) (hmax : ActsAsMax f z o) :
    ¬ PreservesR m f := by
  intro hpres
  have hRto : R m t o :=
    ⟨by omega, by omega, ne_or_ne_of_imp (by omega), ne_or_ne_of_imp (by omega)⟩
  have hRzz : R m z z :=
    ⟨by omega, by omega, ne_or_ne_of_imp (by omega), ne_or_ne_of_imp (by omega)⟩
  have h := hpres t o z z hRto hRzz
  rw [hmin t z (Or.inr rfl) (Or.inl rfl), hmax o z (Or.inr rfl) (Or.inl rfl)] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [Fin.coe_min, Fin.coe_max] at h3
  omega

/-- **Randkante Xt** (`{m−2,m−1} → {m−3,m−1}`, m ≥ 4): Bruchstelle
`((m−3,m−2),(m−1,m−1))`, Bild **genau der Ausschlusspunkt `(m−1,m−2)`** — der
Gipfel-Abstieg; bei `m = 3` wäre `(m−3,m−2) = (0,1)` selbst ausgeschlossen. -/
theorem break_Xt (f : Fin m → Fin m → Fin m) (hm : 4 ≤ m) (w p q : Fin m)
    (hw : w.val = m - 3) (hp : p.val = m - 2) (hq : q.val = m - 1)
    (hmin : ActsAsMin f p q) (hmax : ActsAsMax f w q) :
    ¬ PreservesR m f := by
  intro hpres
  have hRwp : R m w p :=
    ⟨by omega, by omega, ne_or_ne_of_imp (by omega), ne_or_ne_of_imp (by omega)⟩
  have hRqq : R m q q :=
    ⟨by omega, by omega, ne_or_ne_of_imp (by omega), ne_or_ne_of_imp (by omega)⟩
  have h := hpres w p q q hRwp hRqq
  rw [hmax w q (Or.inl rfl) (Or.inr rfl), hmin p q (Or.inl rfl) (Or.inr rfl)] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [Fin.coe_min, Fin.coe_max] at h4
  omega

/-! ## Teil 5 — Propagation und die beiden Hauptlemmata

Unter `PreservesR` pflanzt sich `min` entlang jeder Gerüst-Kante fort und `max`
entgegen (`step_min`/`step_max`) — der Kontrapositiv der Familien-Lemmata plus
lokale Klassizität. Die Ketten sind `Nat.le_induction` über die Weglänge; die
Sonde-19-Route `{0,1} → Gipfel → Keller → beliebig` wird zu `min_propagates` /
`max_propagates`. -/

section Propagation

variable {f : Fin m → Fin m → Fin m}

/-- Ein Propagations-Schritt für `min`: bricht die Kante bei min/max-Mischung und
erhält `f` die Invariante, so erzwingt `min` am Kantenfuß `min` am Kantenkopf. -/
theorem step_min (hLC : LocallyClassical f) (hpres : PreservesR m f)
    {x y u v : Fin m} (huv : u ≠ v)
    (hbreak : ActsAsMin f x y → ActsAsMax f u v → ¬ PreservesR m f)
    (hmin : ActsAsMin f x y) : ActsAsMin f u v := by
  rcases hLC u v huv with h | h
  · exact h
  · exact absurd hpres (hbreak hmin h)

/-- Ein Propagations-Schritt für `max`, entgegen der Kantenrichtung: `max` am
Kantenkopf erzwingt `max` am Kantenfuß. -/
theorem step_max (hLC : LocallyClassical f) (hpres : PreservesR m f)
    {x y u v : Fin m} (hxy : x ≠ y)
    (hbreak : ActsAsMin f x y → ActsAsMax f u v → ¬ PreservesR m f)
    (hmax : ActsAsMax f u v) : ActsAsMax f x y := by
  rcases hLC x y hxy with h | h
  · exact absurd hpres (hbreak h hmax)
  · exact h

/-- **F1-Kette aufwärts:** `min` auf `{x,d}` propagiert zu `{x,e}` für alle
`d ≤ e < m`. -/
theorem min_chain_F1 (hLC : LocallyClassical f) (hpres : PreservesR m f)
    (x : Fin m) (d : ℕ) (hd : d < m) (hxd : x.val < d)
    (hmin : ActsAsMin f x ⟨d, hd⟩) :
    ∀ e, d ≤ e → ∀ (he : e < m), ActsAsMin f x ⟨e, he⟩ := by
  intro e hde
  induction e, hde using Nat.le_induction with
  | base => intro _; exact hmin
  | succ n hdn ih =>
      intro he
      have hn : n < m := by omega
      exact step_min hLC hpres
        (Fin.ne_of_val_ne (show x.val ≠ n + 1 by omega))
        (break_F1 f x ⟨n, hn⟩ ⟨n + 1, he⟩ (show x.val < n by omega) rfl)
        (ih hn)

/-- **F2-Kette aufwärts:** `min` auf `{a,y}` propagiert zu `{c,y}` für alle
`a ≤ c < y`. -/
theorem min_chain_F2 (hLC : LocallyClassical f) (hpres : PreservesR m f)
    (y : Fin m) (a : ℕ) (ha : a < m)
    (hmin : ActsAsMin f ⟨a, ha⟩ y) :
    ∀ c, a ≤ c → c < y.val → ∀ (hc : c < m), ActsAsMin f ⟨c, hc⟩ y := by
  intro c hac
  induction c, hac using Nat.le_induction with
  | base => intro _ _; exact hmin
  | succ n han ih =>
      intro hcy hc
      have hn : n < m := by omega
      exact step_min hLC hpres
        (Fin.ne_of_val_ne (show n + 1 ≠ y.val by omega))
        (break_F2 f ⟨n, hn⟩ y ⟨n + 1, hc⟩ rfl (show n + 1 < y.val from hcy))
        (ih (by omega) hn)

/-- **F1-Kette abwärts (max, entgegen der Kante):** `max` auf `{x,e}` propagiert
zu `{x,d}` für alle `x < d ≤ e`. -/
theorem max_chain_F1 (hLC : LocallyClassical f) (hpres : PreservesR m f)
    (x : Fin m) (d : ℕ) (hxd : x.val < d) :
    ∀ e, d ≤ e → ∀ (he : e < m), ActsAsMax f x ⟨e, he⟩ →
      ∀ (hd : d < m), ActsAsMax f x ⟨d, hd⟩ := by
  intro e hde
  induction e, hde using Nat.le_induction with
  | base => intro he hmax hd; exact hmax
  | succ n hdn ih =>
      intro he hmax hd
      have hn : n < m := by omega
      exact ih hn
        (step_max hLC hpres
          (Fin.ne_of_val_ne (show x.val ≠ n by omega))
          (break_F1 f x ⟨n, hn⟩ ⟨n + 1, he⟩ (show x.val < n by omega) rfl)
          hmax) hd

/-- **D′-Kette aufwärts (max, entgegen der Kante):** `max` auf `{x,t}` propagiert
zu `{x,e}` für alle `t ≤ e < m`, sofern `t ≥ x+2`. -/
theorem max_chain_D' (hLC : LocallyClassical f) (hpres : PreservesR m f)
    (x : Fin m) (t : ℕ) (ht : t < m) (hxt : x.val + 2 ≤ t)
    (hmax : ActsAsMax f x ⟨t, ht⟩) :
    ∀ e, t ≤ e → ∀ (he : e < m), ActsAsMax f x ⟨e, he⟩ := by
  intro e hte
  induction e, hte using Nat.le_induction with
  | base => intro _; exact hmax
  | succ n htn ih =>
      intro he
      have hn : n < m := by omega
      exact step_max hLC hpres
        (Fin.ne_of_val_ne (show x.val ≠ n + 1 by omega))
        (break_D' f x ⟨n, hn⟩ ⟨n + 1, he⟩ rfl (show x.val + 2 ≤ n by omega))
        (ih hn)

/-- **D-Kette aufwärts (max, entgegen der Kante):** `max` auf `{s,y}` propagiert
zu `{c,y}` für alle `s ≤ c` mit `c + 2 ≤ y`. -/
theorem max_chain_D (hLC : LocallyClassical f) (hpres : PreservesR m f)
    (y : Fin m) (s : ℕ) (hs : s < m)
    (hmax : ActsAsMax f ⟨s, hs⟩ y) :
    ∀ c, s ≤ c → c + 2 ≤ y.val → ∀ (hc : c < m), ActsAsMax f ⟨c, hc⟩ y := by
  intro c hsc
  induction c, hsc using Nat.le_induction with
  | base => intro _ _; exact hmax
  | succ n hsn ih =>
      intro hcy hc
      have hn : n < m := by omega
      exact step_max hLC hpres
        (Fin.ne_of_val_ne (show n + 1 ≠ y.val by omega))
        (break_D f ⟨n, hn⟩ y ⟨n + 1, hc⟩ rfl (show n + 3 ≤ y.val by omega))
        (ih (by omega) hn)

/-- **`min` auf `{0,1}` propagiert überallhin** (m ≥ 4): die Sonde-19-Aufstiegsroute
`{0,1} —F1→ {0,d} —F2→ {c,d}`. -/
theorem min_propagates (hm : 4 ≤ m) (hLC : LocallyClassical f)
    (hpres : PreservesR m f)
    (h01 : ActsAsMin f ⟨0, by omega⟩ ⟨1, by omega⟩) :
    ∀ (c d : ℕ) (hc : c < m) (hd : d < m), c < d → ActsAsMin f ⟨c, hc⟩ ⟨d, hd⟩ := by
  intro c d hc hd hcd
  have h0d : ActsAsMin f ⟨0, by omega⟩ ⟨d, hd⟩ :=
    min_chain_F1 hLC hpres ⟨0, by omega⟩ 1 (by omega) (show (0 : ℕ) < 1 by omega)
      h01 d (by omega) hd
  exact min_chain_F2 hLC hpres ⟨d, hd⟩ 0 (by omega) h0d c (by omega) hcd hc

/-- **`max` auf `{0,1}` propagiert überallhin** (m ≥ 4): die Sonde-19-Abstiegsroute
rückwärts — Keller (`Xb`), D′ hinauf zu `{0,m−1}`, D hinauf zu `{c,m−1}` bzw. Gipfel
(`Xt`) zu `{m−2,m−1}`, dann F1 hinab zu `{c,d}`. Hier tragen die Ausschlusspunkte. -/
theorem max_propagates (hm : 4 ≤ m) (hLC : LocallyClassical f)
    (hpres : PreservesR m f)
    (h01 : ActsAsMax f ⟨0, by omega⟩ ⟨1, by omega⟩) :
    ∀ (c d : ℕ) (hc : c < m) (hd : d < m), c < d → ActsAsMax f ⟨c, hc⟩ ⟨d, hd⟩ := by
  -- Keller: Xb rückwärts, {0,1} → {0,2}
  have h02 : ActsAsMax f ⟨0, by omega⟩ ⟨2, by omega⟩ :=
    step_max hLC hpres (Fin.ne_of_val_ne (show (0 : ℕ) ≠ 2 by omega))
      (break_Xb f hm ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩ rfl rfl rfl) h01
  -- D′ hinauf: {0,t} für alle 2 ≤ t < m
  have h0t : ∀ t, 2 ≤ t → ∀ (ht : t < m), ActsAsMax f ⟨0, by omega⟩ ⟨t, ht⟩ := by
    intro t h2t ht
    exact max_chain_D' hLC hpres ⟨0, by omega⟩ 2 (by omega)
      (show (0 : ℕ) + 2 ≤ 2 by omega) h02 t h2t ht
  -- D hinauf: {c, m−1} für alle c + 2 ≤ m − 1
  have hcm : ∀ c, c + 2 ≤ m - 1 → ∀ (hc : c < m),
      ActsAsMax f ⟨c, hc⟩ ⟨m - 1, by omega⟩ := by
    intro c hc2 hc
    exact max_chain_D hLC hpres ⟨m - 1, by omega⟩ 0 (by omega)
      (h0t (m - 1) (by omega) (by omega)) c (by omega) hc2 hc
  -- Gipfel: Xt rückwärts, {m−3,m−1} → {m−2,m−1}
  have htop : ActsAsMax f ⟨m - 2, by omega⟩ ⟨m - 1, by omega⟩ :=
    step_max hLC hpres (Fin.ne_of_val_ne (show m - 2 ≠ m - 1 by omega))
      (break_Xt f hm ⟨m - 3, by omega⟩ ⟨m - 2, by omega⟩ ⟨m - 1, by omega⟩ rfl rfl rfl)
      (hcm (m - 3) (by omega) (by omega))
  -- beliebiges {c,d}: erst {c,m−1}, dann F1 hinab
  intro c d hc hd hcd
  have hcm1 : ActsAsMax f ⟨c, hc⟩ ⟨m - 1, by omega⟩ := by
    rcases Nat.lt_or_ge c (m - 2) with h | h
    · exact hcm c (by omega) hc
    · have hceq : c = m - 2 := by omega
      subst hceq
      exact htop
  exact max_chain_F1 hLC hpres ⟨c, hc⟩ d hcd (m - 1) (by omega) (by omega) hcm1 hd

/-- **Das Herzstück von E3:** eine lokal-klassische Operation, die `R m` erhält,
ist `min` oder `max` (m ≥ 4) — die kontraponierte Gesamtform der Sonde-19-Regel:
wäre die Wahl gemischt, fände die Propagation die brechende Kante. -/
theorem preserving_is_min_or_max (hm : 4 ≤ m) (hLC : LocallyClassical f)
    (hpres : PreservesR m f) :
    (f = fun a b => min a b) ∨ (f = fun a b => max a b) := by
  rcases hLC ⟨0, by omega⟩ ⟨1, by omega⟩
      (Fin.ne_of_val_ne (show (0 : ℕ) ≠ 1 by omega)) with h01 | h01
  · left
    funext a b
    rcases Nat.lt_trichotomy a.val b.val with hab | hab | hab
    · exact min_propagates hm hLC hpres h01 a.val b.val a.isLt b.isLt hab
        a b (Or.inl rfl) (Or.inr rfl)
    · have hba : a = b := Fin.ext hab
      subst hba
      rcases Nat.eq_zero_or_pos a.val with ha0 | ha0
      · exact h01 a a (Or.inl (Fin.ext ha0)) (Or.inl (Fin.ext ha0))
      · exact min_propagates hm hLC hpres h01 0 a.val (by omega) a.isLt ha0
          a a (Or.inr rfl) (Or.inr rfl)
    · exact min_propagates hm hLC hpres h01 b.val a.val b.isLt a.isLt hab
        a b (Or.inr rfl) (Or.inl rfl)
  · right
    funext a b
    rcases Nat.lt_trichotomy a.val b.val with hab | hab | hab
    · exact max_propagates hm hLC hpres h01 a.val b.val a.isLt b.isLt hab
        a b (Or.inl rfl) (Or.inr rfl)
    · have hba : a = b := Fin.ext hab
      subst hba
      rcases Nat.eq_zero_or_pos a.val with ha0 | ha0
      · exact h01 a a (Or.inl (Fin.ext ha0)) (Or.inl (Fin.ext ha0))
      · exact max_propagates hm hLC hpres h01 0 a.val (by omega) a.isLt ha0
          a a (Or.inr rfl) (Or.inr rfl)
    · exact max_propagates hm hLC hpres h01 b.val a.val b.isLt a.isLt hab
        a b (Or.inr rfl) (Or.inl rfl)

end Propagation

/-! ## Teil 6 — Klon-Verschaltung und der Zielsatz

Wörtlich die E2-Verschaltung über `Fin m`: `R m` als Substruktur des Produkts,
`Term.realize_mem` hält die Paar-Realisierung darin, die Projektions-Homomorphismen
zerlegen sie — keine eigene Term-Induktion. Die Erzeugbarkeit von `min`/`max` ist
für allgemeines m **definitional** (`rfl` statt des E2-`decide` über 16 Punkte). -/

/-- Die komponentenweise Produkt-Struktur auf `Fin m × Fin m`. -/
instance prodStrucM : L.Structure (Fin m × Fin m) where
  funMap := fun {_n} f x =>
    (Structure.funMap f (fun i => (x i).1), Structure.funMap f (fun i => (x i).2))
  RelMap r _ := nomatch r

/-- Die Invariante `R m` als Substruktur des Produkts (Träger `{p | R m p.1 p.2}`).
Die `fun_mem`-Verpflichtung ist wörtlich `min_pres`/`max_pres`/`neg_pres`. -/
def RSub (m : ℕ) : L.Substructure (Fin m × Fin m) where
  carrier := {p | R m p.1 p.2}
  fun_mem := by
    intro n f
    match n, f with
    | 1, .neg =>
        intro x hx
        exact neg_pres (x 0).1 (x 0).2 (hx 0)
    | 2, .and =>
        intro x hx
        exact min_pres (x 0).1 (x 0).2 (x 1).1 (x 1).2 (hx 0) (hx 1)
    | 2, .or =>
        intro x hx
        exact max_pres (x 0).1 (x 0).2 (x 1).1 (x 1).2 (hx 0) (hx 1)

/-- Die erste Projektion `Fin m × Fin m → Fin m` als `L`-Homomorphismus. -/
def fstHomM : (Fin m × Fin m) →[L] (Fin m) where
  toFun := Prod.fst
  map_fun' := fun _ _ => rfl
  map_rel' := fun r => nomatch r

/-- Die zweite Projektion `Fin m × Fin m → Fin m` als `L`-Homomorphismus. -/
def sndHomM : (Fin m × Fin m) →[L] (Fin m) where
  toFun := Prod.snd
  map_fun' := fun _ _ => rfl
  map_rel' := fun r => nomatch r

/-- **Jeder Term erhält `R m` (Klon-Ebene).** Stimmen zwei Belegungen `v`, `w`
argumentweise in `R m` überein, so auch die Realisierungen jedes Terms — dieselbe
Verschaltung wie `r4_is_invariant` (E2), uniform in m. -/
theorem R_is_invariant (t : L.Term (Fin 2)) (v w : Fin 2 → Fin m)
    (h : ∀ i, R m (v i) (w i)) : R m (t.realize v) (t.realize w) := by
  have hmem : t.realize (fun i => (v i, w i)) ∈ RSub m :=
    Term.realize_mem t (fun i => (v i, w i)) (fun i =>
      show (v i, w i) ∈ ({p | R m p.1 p.2} : Set (Fin m × Fin m)) from h i)
  have hmem' : R m (t.realize (fun i => (v i, w i))).1
      (t.realize (fun i => (v i, w i))).2 := hmem
  have hv : t.realize v = (t.realize (fun i => (v i, w i))).1 :=
    HomClass.realize_term fstHomM (t := t) (v := fun i => (v i, w i))
  have hw : t.realize w = (t.realize (fun i => (v i, w i))).2 :=
    HomClass.realize_term sndHomM (t := t) (v := fun i => (v i, w i))
  rw [hv, hw]; exact hmem'

/-- **Jede erzeugbare Operation erhält `R m`** — die Konsum-Form der Klon-Invarianz
(E2-Schablone). -/
theorem in_clone_preservesR (f : Fin m → Fin m → Fin m)
    (h : ∃ t : L.Term (Fin 2), ∀ v : Fin 2 → Fin m, t.realize v = f (v 0) (v 1)) :
    PreservesR m f := by
  obtain ⟨t, ht⟩ := h
  intro x y u v hxy huv
  have hinv : R m (t.realize ![x, u]) (t.realize ![y, v]) :=
    R_is_invariant t ![x, u] ![y, v] (fun i =>
      Fin.cases hxy (fun j => Fin.cases huv (fun k => k.elim0) j) i)
  rw [ht (![x, u]), ht (![y, v])] at hinv
  exact hinv

/-- **`min` ist erzeugbar:** der Term `x ∧ y` — für allgemeines m definitional
(`rfl`), wo E2 pro Punkt `decide` brauchte. -/
theorem min_in_clone :
    ∃ t : L.Term (Fin 2), ∀ v : Fin 2 → Fin m, t.realize v = min (v 0) (v 1) :=
  ⟨tand varX varY, fun _ => rfl⟩

/-- **`max` ist erzeugbar:** der Term `x ∨ y`. -/
theorem max_in_clone :
    ∃ t : L.Term (Fin 2), ∀ v : Fin 2 → Fin m, t.realize v = max (v 0) (v 1) :=
  ⟨tor varX varY, fun _ => rfl⟩

/-- **Der Zielsatz (E3): die Charakterisierung für alle m ≥ 4.** Eine
lokal-klassische Operation auf `Fin m` liegt **genau dann** im Klon von
`{min, max, neg}`, wenn sie `min` oder `max` ist — die Verallgemeinerung von E2
auf alle Wertzahlen ab 4 (Rang-Einordnung im Dateikopf, der E3-Spezifikation
zugeschrieben). Bei `m = 3` ist die Aussage **falsch** (E1: vier der acht
Wahlmuster erzeugbar) — die Schranke `m ≥ 4` ist wesentlich (Dateikopf). -/
theorem locally_classical_in_clone_iff (hm : 4 ≤ m) (f : Fin m → Fin m → Fin m)
    (h : LocallyClassical f) :
    (∃ t : L.Term (Fin 2), ∀ v : Fin 2 → Fin m, t.realize v = f (v 0) (v 1))
      ↔ ((f = fun a b => min a b) ∨ (f = fun a b => max a b)) := by
  constructor
  · intro hf
    exact preserving_is_min_or_max hm h (in_clone_preservesR f hf)
  · rintro (rfl | rfl)
    · exact min_in_clone
    · exact max_in_clone

/-! ## Teil 7 — Robustheit: die Schranke überlebt Konstanten

`R m` ist reflexiv (`R_diag`); darum bleibt sie auch unter der um **alle m
Konstanten** erweiterten Sprache `Lc m` eine Invariante, und die Hinrichtung der
Charakterisierung besteht fort (CLAUDE.md §9). Die Substruktur nimmt die
Voraussetzung `2 ≤ m` als Argument — bei `m ≤ 1` fielen die Ausschlusspunkte auf
die Diagonale, und die Konstanten-Verpflichtung wäre unerfüllbar. -/

/-- Die um alle m Konstanten erweiterte Sprache (`Functions 0 = Fin m`). -/
def Lc (m : ℕ) : Language where
  Functions := fun
    | 0 => Fin m
    | 1 => UnaryFun
    | 2 => BinaryFun
    | _ => Empty
  Relations := fun _ => Empty

/-- Interpretation für `Lc m`: wie `strucM`, plus jede Konstante `k ↦ k`. -/
instance strucLc : (Lc m).Structure (Fin m) where
  funMap := fun {n} =>
    match n with
    | 0 => fun k _ => k
    | 1 => fun _ x => negFin m (x 0)
    | 2 => fun f x => match f with
        | .and => min (x 0) (x 1)
        | .or => max (x 0) (x 1)
    | (_ + 3) => fun f _ => nomatch f
  RelMap := fun r _ => nomatch r

/-- Die komponentenweise Produkt-Struktur auf `Fin m × Fin m` über `Lc m`. -/
instance prodStrucLc : (Lc m).Structure (Fin m × Fin m) where
  funMap := fun {_n} f x =>
    (Structure.funMap f (fun i => (x i).1), Structure.funMap f (fun i => (x i).2))
  RelMap r _ := nomatch r

/-- `R m` als Substruktur des Produkts über `Lc m`: der Konstanten-Fall ist genau
die Reflexivität `R_diag` — jede Konstante realisiert das Diagonal-Paar
`(k, k) ∈ R m`. -/
def RSubLc (m : ℕ) (hm : 2 ≤ m) : (Lc m).Substructure (Fin m × Fin m) where
  carrier := {p | R m p.1 p.2}
  fun_mem := by
    intro n f
    match n, f with
    | 0, k =>
        intro _ _
        exact R_diag hm k
    | 1, .neg =>
        intro x hx
        exact neg_pres (x 0).1 (x 0).2 (hx 0)
    | 2, .and =>
        intro x hx
        exact min_pres (x 0).1 (x 0).2 (x 1).1 (x 1).2 (hx 0) (hx 1)
    | 2, .or =>
        intro x hx
        exact max_pres (x 0).1 (x 0).2 (x 1).1 (x 1).2 (hx 0) (hx 1)

/-- Die erste Projektion als `Lc m`-Homomorphismus. -/
def fstHomLc : (Fin m × Fin m) →[Lc m] (Fin m) where
  toFun := Prod.fst
  map_fun' := fun _ _ => rfl
  map_rel' := fun r => nomatch r

/-- Die zweite Projektion als `Lc m`-Homomorphismus. -/
def sndHomLc : (Fin m × Fin m) →[Lc m] (Fin m) where
  toFun := Prod.snd
  map_fun' := fun _ _ => rfl
  map_rel' := fun r => nomatch r

/-- **Jeder `Lc m`-Term erhält `R m`** — die Klon-Invarianz überlebt die
Konstanten (Verschaltung wie `R_is_invariant`, mit `RSubLc`). -/
theorem R_is_invariantLc (hm : 2 ≤ m) (t : (Lc m).Term (Fin 2))
    (v w : Fin 2 → Fin m) (h : ∀ i, R m (v i) (w i)) :
    R m (t.realize v) (t.realize w) := by
  have hmem : t.realize (fun i => (v i, w i)) ∈ RSubLc m hm :=
    Term.realize_mem t (fun i => (v i, w i)) (fun i =>
      show (v i, w i) ∈ ({p | R m p.1 p.2} : Set (Fin m × Fin m)) from h i)
  have hmem' : R m (t.realize (fun i => (v i, w i))).1
      (t.realize (fun i => (v i, w i))).2 := hmem
  have hv : t.realize v = (t.realize (fun i => (v i, w i))).1 :=
    HomClass.realize_term fstHomLc (t := t) (v := fun i => (v i, w i))
  have hw : t.realize w = (t.realize (fun i => (v i, w i))).2 :=
    HomClass.realize_term sndHomLc (t := t) (v := fun i => (v i, w i))
  rw [hv, hw]; exact hmem'

/-- Konsum-Form über `Lc m`: auch mit Konstanten erhält jede erzeugbare Operation
`R m`. -/
theorem in_cloneLc_preservesR (hm : 2 ≤ m) (f : Fin m → Fin m → Fin m)
    (h : ∃ t : (Lc m).Term (Fin 2), ∀ v : Fin 2 → Fin m,
      t.realize v = f (v 0) (v 1)) :
    PreservesR m f := by
  obtain ⟨t, ht⟩ := h
  intro x y u v hxy huv
  have hinv : R m (t.realize ![x, u]) (t.realize ![y, v]) :=
    R_is_invariantLc hm t ![x, u] ![y, v] (fun i =>
      Fin.cases hxy (fun j => Fin.cases huv (fun k => k.elim0) j) i)
  rw [ht (![x, u]), ht (![y, v])] at hinv
  exact hinv

/-- **Der Robustheitssatz (E3).** Auch über der um alle m Konstanten erweiterten
Basis bleibt eine erzeugbare lokal-klassische Operation `min` oder `max` — die
Schranke hängt nicht am Konstanten-Verbot, weil `R m` reflexiv ist (Kontrast zu
`TransjunctionCloneBound`, dessen `{0,2}`-Schranke an der `1`-Konstante fiel). -/
theorem constant_clone_min_or_max (hm : 4 ≤ m) (f : Fin m → Fin m → Fin m)
    (hLC : LocallyClassical f)
    (hf : ∃ t : (Lc m).Term (Fin 2), ∀ v : Fin 2 → Fin m,
      t.realize v = f (v 0) (v 1)) :
    (f = fun a b => min a b) ∨ (f = fun a b => max a b) :=
  preserving_is_min_or_max hm hLC (in_cloneLc_preservesR (by omega) f hf)

/-! **Statement-Pins.** Voller Wortlaut links, Satz rechts — jede Drift des
*Statements* bricht den Build. Namenlose `example`s, keine Axiom-Wache. -/

-- STATEMENT-PIN
example (m : ℕ) (hm : 4 ≤ m) (f : Fin m → Fin m → Fin m) (h : LocallyClassical f) :
    (∃ t : L.Term (Fin 2), ∀ v : Fin 2 → Fin m, t.realize v = f (v 0) (v 1))
      ↔ ((f = fun a b => min a b) ∨ (f = fun a b => max a b)) :=
  locally_classical_in_clone_iff hm f h

-- STATEMENT-PIN
example (m : ℕ) (hm : 4 ≤ m) (f : Fin m → Fin m → Fin m) (hLC : LocallyClassical f)
    (hpres : PreservesR m f) :
    (f = fun a b => min a b) ∨ (f = fun a b => max a b) :=
  preserving_is_min_or_max hm hLC hpres

-- STATEMENT-PIN
example (m : ℕ) (t : L.Term (Fin 2)) (v w : Fin 2 → Fin m)
    (h : ∀ i, R m (v i) (w i)) : R m (t.realize v) (t.realize w) :=
  R_is_invariant t v w h

-- STATEMENT-PIN
example (m : ℕ) (f : Fin m → Fin m → Fin m) (hm : 4 ≤ m) (z o t : Fin m)
    (hz : z.val = 0) (ho : o.val = 1) (ht : t.val = 2)
    (hmin : ActsAsMin f z t) (hmax : ActsAsMax f z o) : ¬ PreservesR m f :=
  break_Xb f hm z o t hz ho ht hmin hmax

-- STATEMENT-PIN
example (m : ℕ) (f : Fin m → Fin m → Fin m) (hm : 4 ≤ m) (w p q : Fin m)
    (hw : w.val = m - 3) (hp : p.val = m - 2) (hq : q.val = m - 1)
    (hmin : ActsAsMin f p q) (hmax : ActsAsMax f w q) : ¬ PreservesR m f :=
  break_Xt f hm w p q hw hp hq hmin hmax

-- STATEMENT-PIN
example (m : ℕ) (hm : 4 ≤ m) (f : Fin m → Fin m → Fin m)
    (hLC : LocallyClassical f)
    (hf : ∃ t : (Lc m).Term (Fin 2), ∀ v : Fin 2 → Fin m,
      t.realize v = f (v 0) (v 1)) :
    (f = fun a b => min a b) ∨ (f = fun a b => max a b) :=
  constant_clone_min_or_max hm f hLC hf

/-! ## Teil 8 — die Axiom-Wachen (Ist-gebunden)

Ist-Ausgabe des grünen Builds (v4.30.0-rc2), pro Satz als Regressions-Wache
eingefroren (Datei-Vollständigkeits-Regel: alle Sätze der Datei). Ab hier bricht
jede Axiom-Drift den Build. **Kein Satz zieht `Classical.choice` oder `sorryAx`**
— die drei gemessenen Fallen (Funktionsraum-Quantifikation, negierte Konjunktion
als Hypothese, Disjunktion im `omega`-Ziel) sind bewusst umgangen (explizite
Paar-Quantifikation, Disjunktionsform von `R`, `ne_or_ne_of_imp`).
`ne_or_ne_of_imp` ist axiom-frei, `step_min`/`step_max` liegen bei `[propext]`. -/

/-- info: 'Reformulation.Proemial.GeneralCloneBound.ne_or_ne_of_imp' does not depend on any axioms -/
#guard_msgs in #print axioms ne_or_ne_of_imp

/-- info: 'Reformulation.Proemial.GeneralCloneBound.R_diag' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms R_diag

/-- info: 'Reformulation.Proemial.GeneralCloneBound.R_proper' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms R_proper

/-- info: 'Reformulation.Proemial.GeneralCloneBound.min_pres' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms min_pres

/-- info: 'Reformulation.Proemial.GeneralCloneBound.max_pres' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms max_pres

/-- info: 'Reformulation.Proemial.GeneralCloneBound.neg_pres' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms neg_pres

/-- info: 'Reformulation.Proemial.GeneralCloneBound.break_F1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms break_F1

/-- info: 'Reformulation.Proemial.GeneralCloneBound.break_F2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms break_F2

/-- info: 'Reformulation.Proemial.GeneralCloneBound.break_D' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms break_D

/-- info: 'Reformulation.Proemial.GeneralCloneBound.break_D'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms «break_D'»

/-- info: 'Reformulation.Proemial.GeneralCloneBound.break_Xb' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms break_Xb

/-- info: 'Reformulation.Proemial.GeneralCloneBound.break_Xt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms break_Xt

/-- info: 'Reformulation.Proemial.GeneralCloneBound.step_min' depends on axioms: [propext] -/
#guard_msgs in #print axioms step_min

/-- info: 'Reformulation.Proemial.GeneralCloneBound.step_max' depends on axioms: [propext] -/
#guard_msgs in #print axioms step_max

/-- info: 'Reformulation.Proemial.GeneralCloneBound.min_chain_F1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms min_chain_F1

/-- info: 'Reformulation.Proemial.GeneralCloneBound.min_chain_F2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms min_chain_F2

/-- info: 'Reformulation.Proemial.GeneralCloneBound.max_chain_F1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms max_chain_F1

/-- info: 'Reformulation.Proemial.GeneralCloneBound.max_chain_D'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms «max_chain_D'»

/-- info: 'Reformulation.Proemial.GeneralCloneBound.max_chain_D' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms max_chain_D

/-- info: 'Reformulation.Proemial.GeneralCloneBound.min_propagates' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms min_propagates

/-- info: 'Reformulation.Proemial.GeneralCloneBound.max_propagates' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms max_propagates

/-- info: 'Reformulation.Proemial.GeneralCloneBound.preserving_is_min_or_max' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms preserving_is_min_or_max

/-- info: 'Reformulation.Proemial.GeneralCloneBound.R_is_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms R_is_invariant

/-- info: 'Reformulation.Proemial.GeneralCloneBound.in_clone_preservesR' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms in_clone_preservesR

/-- info: 'Reformulation.Proemial.GeneralCloneBound.min_in_clone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms min_in_clone

/-- info: 'Reformulation.Proemial.GeneralCloneBound.max_in_clone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms max_in_clone

/-- info: 'Reformulation.Proemial.GeneralCloneBound.locally_classical_in_clone_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms locally_classical_in_clone_iff

/-- info: 'Reformulation.Proemial.GeneralCloneBound.R_is_invariantLc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms R_is_invariantLc

/-- info: 'Reformulation.Proemial.GeneralCloneBound.in_cloneLc_preservesR' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms in_cloneLc_preservesR

/-- info: 'Reformulation.Proemial.GeneralCloneBound.constant_clone_min_or_max' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms constant_clone_min_or_max

end Reformulation.Proemial.GeneralCloneBound
