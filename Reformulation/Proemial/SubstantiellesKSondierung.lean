import Reformulation.Proemial.RealizedTransjunction

/-!
# Reformulation.Proemial.SubstantiellesKSondierung — EXPLORATIVE SONDIERUNG (keine Schicht)

Dies ist KEINE Niederlegungs-Schicht und KEIN Aggregat-Eintrag. Explorative
Datei, deren Zweck das ERPROBEN ist, ob ein *substantielles* `K` (nicht `Unit`)
die binde-relevante Bedingung (iii) trägt. Ergebnis ist ein BEFUND
(`Substantielles_K_Sondierung_Befund.md`), keine Spec.

## Hintergrund (Re-Spezifikation nach Janus' Befund)

Die elfte Schicht (`RealizedTransjunction.lean`) zeigte
`exTransject_not_internal`: die konkrete Operation sitzt außerhalb der *reinen*
`internalS`-Familie (Bild immer `inl`). Janus' Befund: das ist zu schwach —
JEDE rejizierende Operation sitzt außerhalb der reinen `internalS`, auch bei
`K = Unit`. Das Kriterium muss verschärft werden: sitzt `transject` außerhalb der
um *kanonische Überschreitungen* erweiterten Familie?

## Die Schlüssel-Frage und ihre Antwort (hier erprobt)

Gesucht ist eine Definition der erweiterten Familie, sodass
* (a) bei `K = Unit` die erweiterte Familie ALLES erfasst (kein `transject`
  außerhalb — `K = Unit` bindet nicht);
* (b) bei substantiellem `K` die erweiterte Familie eine ECHTE Teilmenge ist
  (ein konkretes `transject` kann außerhalb sitzen — (iii) erfüllbar).

**Befund dieser Datei: die UNÄRE Überschreitung trägt (a) und (b).**
`InExtendedUnary` = die `internalS`-Familie PLUS eine Rejektion, deren Ziel von
einer Abbildung `g : S → K` *des ersten Arguments allein* bestimmt ist. Das ist
die kanonische Überschreitung: ein S-internes Verfahren, das *überschreitet*,
überschreitet zu einem Ziel, das an der *Quell-Stelle* (erstes Argument) hängt,
nicht an der *Interaktion* beider Argumente.

* `unit_captures_all` — (a): bei `K = Unit` ist jedes `t` in `InExtendedUnary`
  (das einzige `g : S → Unit` ist konstant; der `inr`-Zweig ist auf `()` fixiert).
* `exTransjectA_outside` — (b)+(iii): `S = ℕ`, `K = ℕ → Bool` (überabzählbar,
  kardinal eigenständig); `exTransjectA` rejiziert zu einem Ziel, das von `b`
  abhängt — es sitzt außerhalb. Instanzgebunden bewiesen (Zwei-Zeugen-Argument
  `(0,1)`/`(0,2)`), KEIN Form α.

## Die zwei Kontrast-Befunde (warum (iii) am Unär-Schnitt hängt)

* `exTransjectB_inside` (Kandidat B, strukturerhaltend): überschreitet via `g a`
  (Quelle allein, funktor-artig — der `.obj`-Wechsel der ersten Sondierung). Es
  sitzt INNERHALB → (iii) scheitert. Strukturerhaltung macht die Überschreitung
  unär und zieht `transject` in die Familie.
* `binary_captures_all` (Kandidat C, Pfad-B-Test): lässt man BINÄRE
  Überschreitungen `g : S → S → K` zu, so erfasst die Familie ALLES — (iii) ist
  unmöglich (die verbotene „trivial-alles"-Fassung). Das belegt: der Pfad-A-Erfolg
  hängt an der gesetzten Unär-Schranke; sie ist nicht durch `no_generic_switch`
  erzwungen.

## Kriterien-Erfüllung der Pfad-A-Instanz (Kandidat A)

* (i) strukturelle Eigenständigkeit: `K = ℕ → Bool` ist kardinal von `S = ℕ`
  verschieden — keine kanonische Iso `S → K` (KEIN `Discrete-Bool`-Zweitkopie).
* (ii) Nicht-Tabellierbarkeit: `S = ℕ` unendlich; `rejection_targets_injective`
  zeigt, dass `exTransjectA` unendlich viele paarweise verschiedene Rejektions-
  Werte produziert — bei endlichem `S` unmöglich.
* (iii) Nicht-Kanonizität an der Instanz: `exTransjectA_outside` (s.o.).

## Verbots-Disziplin

Kein `sorry` (ein Sorry zum Erzwingen von (iii) wäre der Pfad-B-Befund — gemeldet).
Kein Form α (alle `not_internal`/`outside`-Sätze betreffen die EINE konkrete
Operation über endliche Zeugen). Kein `K = Unit`/kardinal-gleiches `K` als
substantiell. Die erweiterte Familie ist weder trivial-alles (das ist gerade die
BINÄRE Kontrast-Fassung) noch trivial-nichts (unär ⊋ rein-internalS).

## Sorry-Bilanz: 0.
-/

namespace Reformulation.Proemial.SubstantiellesK

-- ============================================================
-- Die erweiterte internalS-Familie — die Schlüssel-Definition
-- ============================================================

/-- UNÄRE Überschreitung (die tragende Fassung): `t` liegt in der erweiterten
    Familie, wenn es eine S-interne Operation `op`, einen Selektor `sel` und eine
    *unäre* Überschreitung `g : S → K` gibt, sodass `t a b` entweder S-intern
    (`inl (op a b)`) ist oder zu `inr (g a)` überschreitet — das Rejektions-Ziel
    hängt am ERSTEN Argument allein. -/
def InExtendedUnary {S K : Type*} (t : S → S → (S ⊕ K)) : Prop :=
  ∃ (op : S → S → S) (sel : S → S → Bool) (g : S → K),
    ∀ a b, t a b = cond (sel a b) (Sum.inl (op a b)) (Sum.inr (g a))

/-- BINÄRE Überschreitung (die verbotene trivial-alles-Fassung, nur zum
    Kontrast): das Rejektions-Ziel `g a b` darf an beiden Argumenten hängen. -/
def InExtendedBinary {S K : Type*} (t : S → S → (S ⊕ K)) : Prop :=
  ∃ (op : S → S → S) (sel : S → S → Bool) (g : S → S → K),
    ∀ a b, t a b = cond (sel a b) (Sum.inl (op a b)) (Sum.inr (g a b))

-- ============================================================
-- (a): bei K = Unit erfasst die UNÄRE Familie ALLES
-- ============================================================

/-- (a) DIE UNIT-SEITE DER SCHLÜSSEL-FRAGE: bei `K = Unit` liegt JEDES
    `t : S → S → (S ⊕ Unit)` in der unären erweiterten Familie. Grund: das
    einzige `g : S → Unit` ist konstant `()`, und der `inr`-Zweig ist damit auf
    `inr ()` fixiert — er kann jeden vorkommenden `inr`-Wert treffen (es gibt nur
    einen). Darum bindet `K = Unit` nicht. -/
theorem unit_captures_all {S : Type*} [Inhabited S]
    (t : S → S → (S ⊕ Unit)) : InExtendedUnary t := by
  refine ⟨fun a b => (t a b).elim id (fun _ => default),
          fun a b => (t a b).isLeft,
          fun _ => (), ?_⟩
  intro a b
  cases h : t a b with
  | inl s => simp [h]
  | inr u => simp [h]

-- ============================================================
-- Kandidat A — S = ℕ unendlich, K = ℕ → Bool kardinal eigenständig
-- ============================================================

/-- Kandidat A: `S = ℕ`, `K = ℕ → Bool` (überabzählbar). `exTransjectA` bleibt
    bei `a = b` S-intern (`inl`); bei `a ≠ b` rejiziert sie zu einem Ziel, das
    `b` KODIERT (die charakteristische Funktion von `{b}`) — das Rejektions-Ziel
    hängt also an `b`, nicht am ersten Argument allein. -/
def exTransjectA : ℕ → ℕ → (ℕ ⊕ (ℕ → Bool)) :=
  fun a b => if a = b then Sum.inl a else Sum.inr (fun n => decide (n = b))

/-- (ii) NICHT-TABELLIERBARKEIT (unendliches `S`): die Rejektions-Ziele von
    `exTransjectA` sind paarweise verschieden — unendlich viele verschiedene
    Werte. Bei endlichem `S` wäre `transject` durch `|S|²` Werte tabellierbar;
    hier ist es das nicht. -/
theorem rejection_targets_injective :
    Function.Injective (fun b : ℕ => (fun n => decide (n = b))) := by
  intro b1 b2 hb
  have := congrFun hb b1
  simpa using this

/-- (iii)+(b) DER PFAD-A-KERN: `exTransjectA` sitzt AUSSERHALB der unären
    erweiterten Familie. Instanzgebunden bewiesen (KEIN Form α): die zwei Zeugen
    `(0,1)` und `(0,2)` rejizieren beide (gleiches erstes Argument `0`), aber zu
    VERSCHIEDENEN Zielen. Ein unäres `g 0` müsste beide Ziele zugleich sein —
    Widerspruch. Hier beißt die Substanz von `K`: bei `K = Unit` wären die zwei
    Ziele gleich (`()`), der Widerspruch verschwände. -/
theorem exTransjectA_outside : ¬ InExtendedUnary exTransjectA := by
  rintro ⟨op, sel, g, h⟩
  have h1 := h 0 1
  have h2 := h 0 2
  have e1 : exTransjectA 0 1 = Sum.inr (fun n => decide (n = 1)) := rfl
  have e2 : exTransjectA 0 2 = Sum.inr (fun n => decide (n = 2)) := rfl
  rw [e1] at h1
  rw [e2] at h2
  have hg1 : g 0 = (fun n => decide (n = 1)) := by
    cases hs : sel 0 1 with
    | true => rw [hs, cond_true] at h1; exact absurd h1 (by simp)
    | false => rw [hs, cond_false] at h1; simpa using h1.symm
  have hg2 : g 0 = (fun n => decide (n = 2)) := by
    cases hs : sel 0 2 with
    | true => rw [hs, cond_true] at h2; exact absurd h2 (by simp)
    | false => rw [hs, cond_false] at h2; simpa using h2.symm
  rw [hg1] at hg2
  have := congrFun hg2 1
  simp at this

-- ============================================================
-- Kandidat B — strukturerhaltend: die Überschreitung ist unär ⇒ INNERHALB
-- ============================================================

/-- Kandidat B (strukturerhaltend / funktor-artig): die Überschreitung läuft über
    `g a` — das Rejektions-Ziel hängt an der QUELLE allein (dem ersten Argument),
    genau wie der `.obj`-Wechsel `S → K` der ersten Sondierung. -/
def exTransjectB (g : ℕ → (ℕ → Bool)) : ℕ → ℕ → (ℕ ⊕ (ℕ → Bool)) :=
  fun a b => if a = b then Sum.inl a else Sum.inr (g a)

/-- DER B-BEFUND (Pfad B für die strukturerhaltende Variante): eine
    strukturerhaltende Überschreitung ist unär und liegt damit INNERHALB der
    erweiterten Familie — (iii) scheitert. Strukturerhaltung bindet nicht; sie
    zieht `transject` gerade in die Familie. (Anschluss an den C-Befund der ersten
    Sondierung: die Operation ist kein Funktor, aber eine *funktor-artige*
    Überschreitung ist unär.) -/
theorem exTransjectB_inside (g : ℕ → (ℕ → Bool)) :
    InExtendedUnary (exTransjectB g) := by
  refine ⟨fun a _ => a, fun a b => decide (a = b), g, ?_⟩
  intro a b
  by_cases hab : a = b
  · simp [exTransjectB, hab]
  · simp [exTransjectB, hab]

-- ============================================================
-- Kandidat C — der Pfad-B-Test: BINÄRE Überschreitung erfasst ALLES
-- ============================================================

/-- DER C-BEFUND (der Pfad-B-Test, explizit): lässt man BINÄRE Überschreitungen
    `g : S → S → K` zu, so liegt JEDES `t` in der erweiterten Familie — (iii) ist
    dann unmöglich (jede `transject` ist drin). Das ist die vom Prompt verbotene
    „trivial-alles"-Fassung; sie ist hier bewiesen, um zu zeigen, WORAN der
    Pfad-A-Erfolg hängt: einzig an der gesetzten Unär-Schranke der Überschreitung.
    `no_generic_switch` erzwingt diese Schranke NICHT. -/
theorem binary_captures_all {S K : Type*} [Inhabited S] [Inhabited K]
    (t : S → S → (S ⊕ K)) : InExtendedBinary t := by
  refine ⟨fun a b => (t a b).elim id (fun _ => default),
          fun a b => (t a b).isLeft,
          fun a b => (t a b).elim (fun _ => default) id, ?_⟩
  intro a b
  cases h : t a b with
  | inl s => simp [h]
  | inr k => simp [h]

-- ============================================================
-- Wachen — Axiom-Profile
-- ============================================================

/-! **Wachen (Zug B).** Ist-Ausgabe des grünen Builds (v4.30.0-rc2), pro Satz
eingefroren; sie ersetzen die fünf vormals nackten Aufrufe. Alle fünf Sätze der Datei
tragen eine Wache, alle mit demselben Profil `[propext]`.

Der Namensraum heisst `Reformulation.Proemial.SubstantiellesK`, die Datei
`SubstantiellesKSondierung.lean`; die Erwartungstexte führen den Namensraum und nicht
den Dateinamen. -/

/-- info: 'Reformulation.Proemial.SubstantiellesK.unit_captures_all' depends on axioms: [propext] -/
#guard_msgs in #print axioms unit_captures_all

/-- info: 'Reformulation.Proemial.SubstantiellesK.exTransjectA_outside' depends on axioms: [propext] -/
#guard_msgs in #print axioms exTransjectA_outside

/-- info: 'Reformulation.Proemial.SubstantiellesK.rejection_targets_injective' depends on axioms: [propext] -/
#guard_msgs in #print axioms rejection_targets_injective

/-- info: 'Reformulation.Proemial.SubstantiellesK.exTransjectB_inside' depends on axioms: [propext] -/
#guard_msgs in #print axioms exTransjectB_inside

/-- info: 'Reformulation.Proemial.SubstantiellesK.binary_captures_all' depends on axioms: [propext] -/
#guard_msgs in #print axioms binary_captures_all

end Reformulation.Proemial.SubstantiellesK
