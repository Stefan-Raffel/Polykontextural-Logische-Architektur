import Reformulation.Proemial.StageParity
import Reformulation.Proemial.AkkretivitaetsBruecke

/-!
# Proemial.StufenZusammenfassung — die Doppelschritte, ihr Ganzes, und ob der Aufstieg konservativ ist

STANDALONE, NICHT im Aggregat;  Target `Probes`.  AxiomGate unberührt.  Sonde nach
`KorpusRev2/Prompt_Instanz_Sonde_Stufen_Zusammenfassung_Mathematiker.md` (Mathematiker, 10.11.2026 18:41;  Architekt 18:39).  Konsumiert
`StageParity` (`eSym`, `eSym_val`, `eSym_negFin`, `negFin_val`), `StageAscent` (`w`), `GeneralCloneBound` (`negFin`, `strucM`, die Signatur
`L`), `AkkretivitaetsBruecke` (`phi`, `phi_umkehr`), `GegenidentitaetProbe` (`umkehr`, `dreh`), `NegationCycle` (`tafelVI4`, `tafelVI5`);
ändert nichts davon.

**Namen (Regel 9):**  vor der Definition über `Reformulation/` und `Foreign/` geprüft;  `gleichL` ist in `VollzugDurchlaufProbe` besetzt, darum
hier `gleichW`.

## WAS

```text
W3a  dg, dgn                SATZ   der gerade Doppelschritt 2k → 2k+2 (Lücke:  die zwei Mittelplätze) und jede Komposition solcher Schritte
     dg_strictMono,                ist ordnungstreu und umkehrverträglich (dgn_strictMono, dgn_negFin).
     dg_negFin, dgn_*
W3b  ltG, swapG, iG         SATZ   das Ganze der geraden Kette, ω + ω* auf Bool × ℕ:  jede gerade Stufe bettet ordnungstreu und umkehrverträglich
     iG_strictMono,                ein, verträglich mit dem Doppelschritt, und die Stufen überdecken das Ganze.
     iG_negFin, iG_dg,
     iG_cover
     ganzes_universell      SATZ   jede mit den Doppelschritten verträgliche Familie von Abbildungen der Stufen faktorisiert eindeutig über das
                                   Ganze (gerichtete Vereinigung, als Menge;  Ordnung und Umkehr der faktorisierten Abbildung nicht behauptet).
W3c  ganzes_kein_glied,     SATZ   es gibt keine ordnungstreue Abbildung des Ganzen in eine Stufe Fin m, also auch keinen Ordnungsisomorphismus;
     ganzesU_kein_glied            ebenso für das ungerade Ganze.
W3d  du, iU, ltU, swapU     SATZ   für ungerades m gibt es den Doppelschritt 2k+1 → 2k+3, Fixpunkt auf Fixpunkt (du_strictMono, du_negFin), und
     iU_*                          sein Ganzes ω + 1 + ω* auf Option (Bool × ℕ) mit denselben Sätzen wie W3b (ohne die Faktorisierung).
W3e  kein_weg_zurueck       SATZ   vom ungeraden Ganzen ins gerade gibt es KEINE umkehrverträgliche Abbildung, gleich welche (Mitte = Fixpunkt).
     weg_hin                SATZ   vom geraden ins ungerade gibt es eine:  ordnungstreu, injektiv, umkehrverträglich (`some`).
     weg_hin_eSym           SATZ   und sie ist auf jeder Stufe der symmetrische Stufenschritt eSym (`SPar.eSym_strictMono`, `SPar.eSym_negFin`):  some ∘ iG k = iU k ∘ eSym (2k).
W3f  wG, w_iG               SATZ   die Regel des Zeugen hat auf dem Ganzen einen Sinn (das unterste Paar ist (false,0), (false,1)) und stimmt ab
                                   vier Werten auf jeder eingebetteten Stufe mit dem Zeugen überein (Gegenstück zu `SAsc.w_castSucc`, `SPar.w_eSym`).
     w_iG_eins              EICHUNG bei zwei Werten nicht:  dort liegt das unterste Paar der Stufe auf zwei Hälften des Ganzen.
W1   homVon, realize_komm   SATZ   eine Abbildung, die mit min, max und der Umkehr vertauscht, ist ein Homomorphismus der Signatur von Kap. 5;
                                   jeder Term vertauscht mit ihr, in jeder Stelligkeit.
     res_gleich             SATZ   längs eSym ist der Aufstieg m → m+1 bei geradem m KONSERVATIV:  die Einschränkung des höheren Klons ist genau
                                   der niedere, in jeder Stelligkeit (dieselbe Gleichung trägt beide Inklusionen).
     res_gleich_dg          SATZ   dasselbe für den geraden Doppelschritt.
W2   drei_eine_bahn,        EICHUNG 3 → 4:  die zwei dreiwertigen Vollkreise sind eine Bahn;  ihre Bilder unter Φ sind es in keiner festen
     drei_getrennt,                Schubrichtung, auch nicht bis auf Drehung;  über beide Schubrichtungen zusammen wieder (phi_umkehr).
     drei_beide
```

**Gemessen, kein Satz** (`KorpusRev2/T_Vorprobe_Skripte/Sonde_Stufen_Zusammenfassung_Vorrechnung.lean`, `#eval`, Ausgabe `.out`):

```text
W1   binäre Termfunktionen von {∧, ∨, ¬} auf Fin m (eigene Abschlussrechnung, NICHT an den Klonbegriff von Kap. 5 angeschlossen):
     |K_2| = 16, |K_3| = |K_4| = |K_5| = 82.
     längs eSym:     2 → 3  Res = K_2 (16);   4 → 5  Res = K_4 (82)          — wie res_gleich sagt
                     3 → 4  Res ⊊ K_3 (25 von 82)                            — eSym ist bei ungeradem m nicht umkehrverträglich (`SPar.odd_no_neg_compatible`)
     längs castSucc: 2 → 3  Res ⊊ K_2 (4 von 16)
                     3 → 4  UNVERGLEICHBAR:  |Res| = 18, davon 4 in K_3;  14 Einschränkungen liegen nicht in K_3
                     4 → 5  UNVERGLEICHBAR:  |Res| = 41, davon 4 in K_4
W2   Bahnen unter Umkehr und Drehsinn, zurückgezogen längs Φ (Klassen):
                      P_m   Φ_true*   Φ_false*   beide Richtungen   bis auf Drehung, Φ_true*
     3 → 4 (2 Kreise)  1      2         2           1                  1 → 2
     4 → 5 (88)       22     88        88          44                  4 → 5
     In jeder Lesung ist Φ*P_{m+1} feiner als P_m oder gleich, nie gröber;  echt feiner überall außer „beide Richtungen" bei 3 → 4.
```

**Wie die Sätze gehen.**  Alles über `.val` und `omega` mit atomaren Zielen;  die Ganzen sind konkrete Träger (`Bool × ℕ`,
`Option (Bool × ℕ)`) mit Ordnung als Fallunterscheidung, ohne Ordnungsinstanz aus Mathlib.  `ganzes_kein_glied`:  eine ordnungstreue
Abbildung schickt die untere Kopie streng steigend nach `Fin m`, also `(false, n)` auf einen Wert `≥ n`;  bei `n = m` unmöglich.
`kein_weg_zurueck` ist das Fixpunktargument von `SPar.odd_no_neg_compatible` im Ganzen.  `res_gleich` ist `HomClass.realize_term` über `homVon`.

**Profile:**  kein Satz trägt `Classical.choice` (Wachen unten);  `kein_weg_zurueck` ist axiomfrei.  `leG_iG` trug im ersten Lauf Choice:
`omega` an einem Iff-Ziel (Fallstrick 7, dritte Gestalt);  jetzt vier Fälle mit `decide_eq_true`/`decide_eq_false`.  Kein `native_decide`,
kein `sorry`, kein True-Feld.

**Kosten (lokal, M2 Max, `/usr/bin/time -l`):**  ganze Datei 3,5 s, 1,94 GB (Importgrundlinie wie `AkkretivitaetsBruecke`).

**Was die Zahlen erzwingt (Regel 11):**  `res_gleich` ist der Satz, dass Homomorphismen Termfunktionen respektieren (Lehrbuch);  das
Fixpunktargument ist Arithmetik (`2a = m` bei ungeradem m, `!b ≠ b`).  Kein Indiz für eine Quelle.

## ZUSAMMENSCHAU (unsere;  nicht im Lean)

Die Frage des Prompts kennt zwei Eigenschaften einer Stufenfolge (Gibbs Lecture 1951, nach dem Prompt):  (K) die höhere Stufe entscheidet
Neues über die niedere, (Z) die Zusammenfassung wird wieder Stufe.  Gemessen:  (Z) hat der Aufstieg des Bestands — das Ganze der geraden
Kette ist kein Glied (W3c), hat aber einen nächsten Schritt ins ungerade Ganze (W3e), der dort derselbe ist wie auf jeder Stufe.  (K) hängt
an der Einbettung:  längs der umkehrverträglichen ist der Aufstieg an den Operationen konservativ (W1), längs `castSucc` nicht vergleichbar
(gemessen);  an den Kreisen trennt die höhere Stufe, was die niedere nicht trennt (W2).

## UNSER

Die Doppelschritte `dg`, `du`, die Ganzen und ihre Ordnungen, die Lesung „Einschränkung des Klons", die Zerlegung der Kreise.

## NICHT

Kein Grenzobjekt des Aufstiegs der Ausgabe (der Aufstieg `m → m+1`);  die Ganzen hier sind die der zwei Doppelschritt-Ketten, die die Ausgabe
nicht führt.  Keine Aussage über andere Ketten.  Der Klon ist in W1 als Satz nur längs der verträglichen Einbettungen erfasst;  die Zahlen
für `castSucc` sind Rechnung ohne Brücke zum Klonbegriff.  Nicht Teil der Ausgabe Rev11.
-/

namespace Reformulation.Proemial.StufenZusammenfassung

open FirstOrder Language
open Reformulation.Proemial.TransjunctionCloneBound (L)
open Reformulation.Proemial.GeneralCloneBound (negFin)
open Reformulation.Proemial.StageParity (negFin_val eSym eSym_val)
open Reformulation.Proemial.StageAscent (w)

/-! ## W3 (a) — der gerade Doppelschritt `2k → 2k+2` -/

/-- Der gerade Doppelschritt:  unterhalb der Mitte fest, oberhalb um zwei verschoben;  die Lücke sind die zwei Mittelplätze. -/
def dg (k : ℕ) (a : Fin (2 * k)) : Fin (2 * (k + 1)) :=
  if a.val < k then ⟨a.val, by omega⟩ else ⟨a.val + 2, by have := a.isLt; omega⟩

theorem dg_val (k : ℕ) (a : Fin (2 * k)) : (dg k a).val = if a.val < k then a.val else a.val + 2 := by
  unfold dg; split_ifs <;> rfl

theorem dg_strictMono (k : ℕ) (a b : Fin (2 * k)) (h : a < b) : dg k a < dg k b := by
  rw [Fin.lt_def] at h ⊢
  simp only [dg_val]
  split_ifs <;> omega

theorem dg_negFin (k : ℕ) (a : Fin (2 * k)) : dg k (negFin (2 * k) a) = negFin (2 * (k + 1)) (dg k a) := by
  have := a.isLt
  refine Fin.eq_of_val_eq ?_
  simp only [dg_val, negFin_val]
  split_ifs <;> omega

/-- `n` Doppelschritte hintereinander. -/
def dgn (k : ℕ) : (n : ℕ) → Fin (2 * k) → Fin (2 * (k + n))
  | 0 => fun a => a
  | n + 1 => fun a => dg (k + n) (dgn k n a)

theorem dgn_val (k : ℕ) : ∀ (n : ℕ) (a : Fin (2 * k)), (dgn k n a).val = if a.val < k then a.val else a.val + 2 * n
  | 0, a => by show a.val = _; split_ifs <;> rfl
  | n + 1, a => by
    show (dg (k + n) (dgn k n a)).val = _
    rw [dg_val, dgn_val k n a]
    have := a.isLt
    split_ifs <;> omega

/-- (W3a) **Die Komposition beliebig vieler Doppelschritte ist ordnungstreu.** -/
theorem dgn_strictMono (k n : ℕ) (a b : Fin (2 * k)) (h : a < b) : dgn k n a < dgn k n b := by
  rw [Fin.lt_def] at h ⊢
  simp only [dgn_val]
  split_ifs <;> omega

/-- (W3a) **… und umkehrverträglich.** -/
theorem dgn_negFin (k n : ℕ) (a : Fin (2 * k)) : dgn k n (negFin (2 * k) a) = negFin (2 * (k + n)) (dgn k n a) := by
  have := a.isLt
  refine Fin.eq_of_val_eq ?_
  simp only [dgn_val, negFin_val]
  split_ifs <;> omega

/-! ## W3 (b), (c) — das Ganze der geraden Kette:  ω + ω*

Träger `Bool × ℕ`:  `(false, n)` ist die untere Kopie, aufsteigend;  `(true, n)` die obere, absteigend (`(true, 0)` ist das größte
Element).  Die Umkehr tauscht die Hälften. -/

/-- Die Ordnung von ω + ω*. -/
def ltG : Bool × ℕ → Bool × ℕ → Prop
  | (false, n), (false, n') => n < n'
  | (false, _), (true, _) => True
  | (true, _), (false, _) => False
  | (true, n), (true, n') => n' < n

/-- Die Umkehr auf dem Ganzen:  Tausch der Hälften. -/
def swapG (x : Bool × ℕ) : Bool × ℕ := (!x.1, x.2)

/-- Die gerade Stufe `2k` im Ganzen. -/
def iG (k : ℕ) (a : Fin (2 * k)) : Bool × ℕ := if a.val < k then (false, a.val) else (true, 2 * k - 1 - a.val)

/-- (W3b) **Jede gerade Stufe bettet ordnungstreu ins Ganze ein.** -/
theorem iG_strictMono (k : ℕ) (a b : Fin (2 * k)) (h : a < b) : ltG (iG k a) (iG k b) := by
  rw [Fin.lt_def] at h
  have := b.isLt
  unfold iG
  split_ifs <;> simp only [ltG] <;> omega

/-- (W3b) **… umkehrverträglich.** -/
theorem iG_negFin (k : ℕ) (a : Fin (2 * k)) : iG k (negFin (2 * k) a) = swapG (iG k a) := by
  have := a.isLt
  have hn := negFin_val (2 * k) a
  by_cases h : a.val < k
  · have h' : ¬ (negFin (2 * k) a).val < k := by omega
    unfold iG; rw [if_neg h', if_pos h]
    show (true, 2 * k - 1 - (negFin (2 * k) a).val) = (true, a.val)
    rw [hn]; congr 1; omega
  · have h' : (negFin (2 * k) a).val < k := by omega
    unfold iG; rw [if_pos h', if_neg h]
    show (false, (negFin (2 * k) a).val) = (false, 2 * k - 1 - a.val)
    rw [hn]

/-- (W3b) **… verträglich mit dem Doppelschritt.** -/
theorem iG_dg (k : ℕ) (a : Fin (2 * k)) : iG (k + 1) (dg k a) = iG k a := by
  have := a.isLt
  unfold iG
  simp only [dg_val]
  split_ifs <;> first | rfl | (simp only [Prod.mk.injEq, true_and]; omega)

/-- (W3b) **Die Stufen überdecken das Ganze.** -/
theorem iG_cover (x : Bool × ℕ) : ∃ k, ∃ a : Fin (2 * k), iG k a = x := by
  rcases x with ⟨b, n⟩
  cases b with
  | false => exact ⟨n + 1, ⟨n, by omega⟩, by unfold iG; rw [if_pos (by show n < n + 1; omega)]⟩
  | true =>
    refine ⟨n + 1, ⟨n + 1, by omega⟩, ?_⟩
    unfold iG
    rw [if_neg (by show ¬ n + 1 < n + 1; omega)]
    simp only [Prod.mk.injEq, true_and]
    show 2 * (n + 1) - 1 - (n + 1) = n
    omega

/-- Das Urbild eines Platzes der Stufe `k+1` außerhalb der zwei Mittelplätze. -/
theorem dg_surj_aussen (k : ℕ) (a : Fin (2 * (k + 1))) (h1 : a.val ≠ k) (h2 : a.val ≠ k + 1) :
    ∃ a' : Fin (2 * k), dg k a' = a := by
  have := a.isLt
  by_cases h : a.val < k
  · exact ⟨⟨a.val, by omega⟩, Fin.eq_of_val_eq (by rw [dg_val]; rw [if_pos h])⟩
  · refine ⟨⟨a.val - 2, by omega⟩, Fin.eq_of_val_eq ?_⟩
    rw [dg_val]; rw [if_neg (by show ¬ a.val - 2 < k; omega)]; show a.val - 2 + 2 = a.val; omega

/-- (W3b) **Das Ganze ist die gerichtete Vereinigung, als Menge:**  jede mit den Doppelschritten verträgliche Familie von Abbildungen der
Stufen faktorisiert eindeutig über das Ganze. -/
theorem ganzes_universell {X : Type} (f : ∀ k, Fin (2 * k) → X) (hf : ∀ k a, f (k + 1) (dg k a) = f k a) :
    ∃ F : Bool × ℕ → X, (∀ k a, F (iG k a) = f k a) ∧ ∀ G : Bool × ℕ → X, (∀ k a, G (iG k a) = f k a) → G = F := by
  let F : Bool × ℕ → X := fun x => match x with
    | (false, n) => f (n + 1) ⟨n, by omega⟩
    | (true, n) => f (n + 1) ⟨n + 1, by omega⟩
  have hF : ∀ k a, F (iG k a) = f k a := by
    intro k
    induction k with
    | zero => intro a; exact absurd a.isLt (by omega)
    | succ k ih =>
      intro a
      by_cases h1 : a.val = k
      · obtain ⟨v, hv⟩ := a
        simp only at h1
        subst v
        unfold iG
        rw [if_pos (by show k < k + 1; omega)]
      · by_cases h2 : a.val = k + 1
        · obtain ⟨v, hv⟩ := a
          simp only at h2
          subst v
          unfold iG
          rw [if_neg (by show ¬ k + 1 < k + 1; omega)]
          show F (true, 2 * (k + 1) - 1 - (k + 1)) = _
          rw [show 2 * (k + 1) - 1 - (k + 1) = k by omega]
        · obtain ⟨a', rfl⟩ := dg_surj_aussen k a h1 h2
          rw [iG_dg, ih a', hf]
  refine ⟨F, hF, fun G hG => funext fun x => ?_⟩
  obtain ⟨k, a, rfl⟩ := iG_cover x
  rw [hG, hF]

/-- (W3c) **Das Ganze ist keiner Stufe ordnungsgleich:**  es gibt nicht einmal eine ordnungstreue Abbildung des Ganzen in eine Stufe. -/
theorem ganzes_kein_glied (m : ℕ) (e : Bool × ℕ → Fin m) (he : ∀ x y, ltG x y → e x < e y) : False := by
  have hge : ∀ n, n ≤ (e (false, n)).val := by
    intro n
    induction n with
    | zero => omega
    | succ n ih =>
      have := he (false, n) (false, n + 1) (show n < n + 1 by omega)
      rw [Fin.lt_def] at this
      omega
  have := hge m
  have := (e (false, m)).isLt
  omega

/-! ## W3 (d) — die ungerade Kette:  der Doppelschritt `2k+1 → 2k+3`, das Ganze ω + 1 + ω* -/

/-- Der ungerade Doppelschritt:  unten fest, die Mitte auf die neue Mitte, oben um zwei verschoben. -/
def du (k : ℕ) (a : Fin (2 * k + 1)) : Fin (2 * (k + 1) + 1) :=
  if a.val < k then ⟨a.val, by omega⟩ else if a.val = k then ⟨k + 1, by omega⟩ else ⟨a.val + 2, by have := a.isLt; omega⟩

theorem du_val (k : ℕ) (a : Fin (2 * k + 1)) :
    (du k a).val = if a.val < k then a.val else if a.val = k then k + 1 else a.val + 2 := by
  unfold du; split_ifs <;> rfl

theorem du_strictMono (k : ℕ) (a b : Fin (2 * k + 1)) (h : a < b) : du k a < du k b := by
  rw [Fin.lt_def] at h ⊢
  simp only [du_val]
  split_ifs <;> omega

/-- (W3d) **Für ungerades m gibt es den Doppelschritt:**  ordnungstreu (`du_strictMono`) und umkehrverträglich, Fixpunkt auf Fixpunkt. -/
theorem du_negFin (k : ℕ) (a : Fin (2 * k + 1)) : du k (negFin (2 * k + 1) a) = negFin (2 * (k + 1) + 1) (du k a) := by
  have := a.isLt
  refine Fin.eq_of_val_eq ?_
  simp only [du_val, negFin_val]
  split_ifs <;> omega

/-- Die Ordnung von ω + 1 + ω*:  `none` ist die Mitte. -/
def ltU : Option (Bool × ℕ) → Option (Bool × ℕ) → Prop
  | some x, some y => ltG x y
  | some (false, _), none => True
  | some (true, _), none => False
  | none, some (false, _) => False
  | none, some (true, _) => True
  | none, none => False

/-- Die Umkehr auf dem ungeraden Ganzen:  die Hälften tauschen, die Mitte bleibt. -/
def swapU : Option (Bool × ℕ) → Option (Bool × ℕ) := Option.map swapG

/-- Die ungerade Stufe `2k+1` im Ganzen. -/
def iU (k : ℕ) (a : Fin (2 * k + 1)) : Option (Bool × ℕ) :=
  if a.val < k then some (false, a.val) else if a.val = k then none else some (true, 2 * k - a.val)

theorem iU_strictMono (k : ℕ) (a b : Fin (2 * k + 1)) (h : a < b) : ltU (iU k a) (iU k b) := by
  rw [Fin.lt_def] at h
  have := b.isLt
  unfold iU
  split_ifs <;> simp only [ltU, ltG] <;> omega

theorem iU_negFin (k : ℕ) (a : Fin (2 * k + 1)) : iU k (negFin (2 * k + 1) a) = swapU (iU k a) := by
  have := a.isLt
  have hn := negFin_val (2 * k + 1) a
  rcases Nat.lt_trichotomy a.val k with h | h | h
  · have h1 : ¬ (negFin (2 * k + 1) a).val < k := by omega
    have h2 : (negFin (2 * k + 1) a).val ≠ k := by omega
    unfold iU; rw [if_neg h1, if_neg h2, if_pos h]
    show some (true, 2 * k - (negFin (2 * k + 1) a).val) = some (true, a.val)
    rw [hn]; congr 2; omega
  · have h1 : ¬ (negFin (2 * k + 1) a).val < k := by omega
    have h2 : (negFin (2 * k + 1) a).val = k := by omega
    have h3 : ¬ a.val < k := by omega
    unfold iU; rw [if_neg h1, if_pos h2, if_neg h3, if_pos h]; rfl
  · have h1 : (negFin (2 * k + 1) a).val < k := by omega
    have h3 : ¬ a.val < k := by omega
    have h4 : a.val ≠ k := by omega
    unfold iU; rw [if_pos h1, if_neg h3, if_neg h4]
    show some (false, (negFin (2 * k + 1) a).val) = some (false, 2 * k - a.val)
    rw [hn]; congr 2

theorem iU_du (k : ℕ) (a : Fin (2 * k + 1)) : iU (k + 1) (du k a) = iU k a := by
  have := a.isLt
  have hd := du_val k a
  rcases Nat.lt_trichotomy a.val k with h | h | h
  · rw [if_pos h] at hd
    have h1 : (du k a).val < k + 1 := by omega
    unfold iU; rw [if_pos h1, if_pos h, hd]
  · rw [if_neg (by omega), if_pos h] at hd
    have h1 : ¬ (du k a).val < k + 1 := by omega
    have h2 : (du k a).val = k + 1 := by omega
    unfold iU; rw [if_neg h1, if_pos h2, if_neg (by omega), if_pos h]
  · rw [if_neg (by omega), if_neg (by omega)] at hd
    have h1 : ¬ (du k a).val < k + 1 := by omega
    have h2 : (du k a).val ≠ k + 1 := by omega
    unfold iU; rw [if_neg h1, if_neg h2, if_neg (by omega), if_neg (by omega)]
    show some (true, 2 * (k + 1) - (du k a).val) = some (true, 2 * k - a.val)
    rw [hd]; congr 2; omega

theorem iU_cover (x : Option (Bool × ℕ)) : ∃ k, ∃ a : Fin (2 * k + 1), iU k a = x := by
  rcases x with _ | ⟨b, n⟩
  · exact ⟨0, ⟨0, by omega⟩, by unfold iU; simp⟩
  · cases b with
    | false => exact ⟨n + 1, ⟨n, by omega⟩, by unfold iU; rw [if_pos (by show n < n + 1; omega)]⟩
    | true =>
      refine ⟨n + 1, ⟨n + 2, by omega⟩, ?_⟩
      unfold iU
      rw [if_neg (by show ¬ n + 2 < n + 1; omega), if_neg (by show ¬ n + 2 = n + 1; omega)]
      show some (true, 2 * (n + 1) - (n + 2)) = some (true, n)
      congr 2; omega

/-- (W3c, ungerade) **Auch das ungerade Ganze ist keiner Stufe ordnungsgleich.** -/
theorem ganzesU_kein_glied (m : ℕ) (e : Option (Bool × ℕ) → Fin m) (he : ∀ x y, ltU x y → e x < e y) : False :=
  ganzes_kein_glied m (fun x => e (some x)) (fun x y h => he (some x) (some y) h)

/-! ## W3 (e) — die Parität im Ganzen -/

/-- (W3e) **Vom ungeraden Ganzen führt keine umkehrverträgliche Abbildung ins gerade:**  die Mitte ist Fixpunkt der Umkehr, das gerade
Ganze hat keinen.  Für jede Abbildung, ohne Ordnung und ohne Injektivität. -/
theorem kein_weg_zurueck (f : Option (Bool × ℕ) → Bool × ℕ) : ¬ ∀ x, f (swapU x) = swapG (f x) := by
  intro h
  have h0 := h none
  have hv := congrArg Prod.fst h0
  simp only [swapU, Option.map_none, swapG] at hv
  cases hb : (f none).1 <;> rw [hb] at hv <;> exact Bool.noConfusion hv

/-- (W3e) **Vom geraden Ganzen ins ungerade führt eine:**  ordnungstreu, injektiv, umkehrverträglich. -/
theorem weg_hin :
    (∀ x : Bool × ℕ, some (swapG x) = swapU (some x)) ∧ (∀ x y, ltG x y → ltU (some x) (some y)) ∧
      Function.Injective (some : Bool × ℕ → Option (Bool × ℕ)) :=
  ⟨fun _ => rfl, fun _ _ h => h, Option.some_injective _⟩

/-- (W3e) **Und sie ist im Ganzen derselbe Schritt wie auf der Stufe:**  das gerade Ganze, ins ungerade gebracht, ist die gerade Stufe
`2k`, mit dem symmetrischen Stufenschritt `eSym` (`SPar.eSym_strictMono`, `SPar.eSym_negFin`) in die ungerade Stufe `2k+1` gebracht. -/
theorem weg_hin_eSym (k : ℕ) (a : Fin (2 * k)) : some (iG k a) = iU k (eSym (2 * k) a) := by
  have := a.isLt
  have he := eSym_val (2 * k) a
  have hk : 2 * k / 2 = k := by omega
  rw [hk] at he
  by_cases h : a.val < k
  · rw [if_pos h] at he
    have h1 : (eSym (2 * k) a).val < k := by omega
    unfold iG iU; rw [if_pos h, if_pos h1, he]
  · rw [if_neg h] at he
    have h1 : ¬ (eSym (2 * k) a).val < k := by omega
    have h2 : (eSym (2 * k) a).val ≠ k := by omega
    unfold iG iU; rw [if_neg h, if_neg h1, if_neg h2]
    show some (true, 2 * k - 1 - a.val) = some (true, 2 * k - (eSym (2 * k) a).val)
    rw [he]; congr 2; omega

/-! ## W3 (f) — der Zeuge auf dem Ganzen -/

/-- Vergleich auf ω + ω*, als `Bool`. -/
def leG : Bool × ℕ → Bool × ℕ → Bool
  | (false, n), (false, n') => decide (n ≤ n')
  | (false, _), (true, _) => true
  | (true, _), (false, _) => false
  | (true, n), (true, n') => decide (n' ≤ n)

def minG (x y : Bool × ℕ) : Bool × ℕ := if leG x y then x else y
def maxG (x y : Bool × ℕ) : Bool × ℕ := if leG x y then y else x

/-- Das unterste und das zweitunterste Element des Ganzen. -/
def ist0 : Bool × ℕ → Bool
  | (false, 0) => true
  | _ => false
def ist1 : Bool × ℕ → Bool
  | (false, 1) => true
  | _ => false

/-- Die Regel des Zeugen auf dem Ganzen:  Maximum auf dem untersten Paar, sonst Minimum. -/
def wG (x y : Bool × ℕ) : Bool × ℕ := if (ist0 x && ist1 y) || (ist1 x && ist0 y) then maxG x y else minG x y

theorem leG_iG (k : ℕ) (a b : Fin (2 * k)) : leG (iG k a) (iG k b) = decide (a.val ≤ b.val) := by
  have := a.isLt; have := b.isLt
  -- vier Fälle, je über `decide_eq_true`/`decide_eq_false`:  `omega` bekommt nur atomare Ziele (ein Iff-Ziel zöge Choice, Fallstrick 7)
  by_cases ha : a.val < k <;> by_cases hb : b.val < k
  · unfold iG; rw [if_pos ha, if_pos hb]; rfl
  · unfold iG; rw [if_pos ha, if_neg hb]
    show true = decide (a.val ≤ b.val)
    rw [decide_eq_true (by omega)]
  · unfold iG; rw [if_neg ha, if_pos hb]
    show false = decide (a.val ≤ b.val)
    rw [decide_eq_false (by omega)]
  · unfold iG; rw [if_neg ha, if_neg hb]
    show decide (2 * k - 1 - b.val ≤ 2 * k - 1 - a.val) = decide (a.val ≤ b.val)
    by_cases hab : a.val ≤ b.val
    · rw [decide_eq_true hab, decide_eq_true (by omega)]
    · rw [decide_eq_false hab, decide_eq_false (by omega)]

theorem iG_min (k : ℕ) (a b : Fin (2 * k)) : iG k (min a b) = minG (iG k a) (iG k b) := by
  unfold minG
  rw [leG_iG]
  by_cases h : a.val ≤ b.val
  · rw [decide_eq_true h, if_pos rfl]
    exact congrArg (iG k) (Fin.eq_of_val_eq (by rw [Fin.coe_min]; omega))
  · rw [decide_eq_false h, if_neg Bool.false_ne_true]
    exact congrArg (iG k) (Fin.eq_of_val_eq (by rw [Fin.coe_min]; omega))

theorem iG_max (k : ℕ) (a b : Fin (2 * k)) : iG k (max a b) = maxG (iG k a) (iG k b) := by
  unfold maxG
  rw [leG_iG]
  by_cases h : a.val ≤ b.val
  · rw [decide_eq_true h, if_pos rfl]
    exact congrArg (iG k) (Fin.eq_of_val_eq (by rw [Fin.coe_max]; omega))
  · rw [decide_eq_false h, if_neg Bool.false_ne_true]
    exact congrArg (iG k) (Fin.eq_of_val_eq (by rw [Fin.coe_max]; omega))

theorem ist0_iG (k : ℕ) (a : Fin (2 * k)) : ist0 (iG k a) = decide (a.val = 0) := by
  have := a.isLt
  unfold iG
  split_ifs with h
  · rcases Nat.eq_zero_or_pos a.val with h0 | h0
    · rw [h0]; rfl
    · obtain ⟨j, hj⟩ : ∃ j, a.val = j + 1 := ⟨a.val - 1, by omega⟩
      rw [hj]; symm; apply decide_eq_false; omega
  · symm; apply decide_eq_false; omega

theorem ist1_iG (k : ℕ) (hk : 2 ≤ k) (a : Fin (2 * k)) : ist1 (iG k a) = decide (a.val = 1) := by
  have := a.isLt
  unfold iG
  split_ifs with h
  · rcases Nat.lt_or_ge a.val 2 with h2 | h2
    · rcases Nat.lt_or_ge a.val 1 with h1 | h1
      · have : a.val = 0 := by omega
        rw [this]; rfl
      · have : a.val = 1 := by omega
        rw [this]; rfl
    · obtain ⟨j, hj⟩ : ∃ j, a.val = j + 2 := ⟨a.val - 2, by omega⟩
      rw [hj]; symm; apply decide_eq_false; omega
  · symm; apply decide_eq_false; omega

/-- (W3f) **Ab vier Werten stimmt die Regel auf dem Ganzen mit dem Zeugen jeder Stufe überein** (das Gegenstück zu `SAsc.w_castSucc` und `SPar.w_eSym`). -/
theorem w_iG (k : ℕ) (hk : 2 ≤ k) (a b : Fin (2 * k)) : iG k (w (2 * k) a b) = wG (iG k a) (iG k b) := by
  unfold w wG
  rw [ist0_iG k, ist1_iG k hk, ist1_iG k hk, ist0_iG k]
  by_cases h : (a.val = 0 ∧ b.val = 1) ∨ (a.val = 1 ∧ b.val = 0)
  · rw [if_pos h, iG_max, if_pos]
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [decide_eq_true h1, decide_eq_true h2]; rfl
    · rw [decide_eq_true h1, decide_eq_true h2, Bool.or_eq_true]; exact Or.inr rfl
  · rw [if_neg h, iG_min, if_neg]
    intro hc
    refine h ?_
    rw [Bool.or_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hc
    rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨of_decide_eq_true h1, of_decide_eq_true h2⟩
    · exact Or.inr ⟨of_decide_eq_true h1, of_decide_eq_true h2⟩

/-- (W3f, Grenze) **Bei zwei Werten stimmt sie nicht:**  dort liegt das unterste Paar der Stufe auf zwei Hälften des Ganzen. -/
theorem w_iG_eins : iG 1 (w 2 ⟨0, by omega⟩ ⟨1, by omega⟩) ≠ wG (iG 1 ⟨0, by omega⟩) (iG 1 ⟨1, by omega⟩) := by decide

/-! ## W1 — Konservativität an den Operationen

Der Klon von Kapitel 5:  die Termfunktionen der Signatur `{∧, ∨, ¬}` auf `Fin m` (`GCB.strucM`).  Vertauscht eine Abbildung
`e : Fin m → Fin n` mit `min`, `max` und der Umkehr, so ist sie ein Homomorphismus, und jeder Term vertauscht mit ihr.  Daraus:  längs einer
solchen Einbettung ist die Einschränkung des höheren Klons genau der niedere, in jeder Stelligkeit. -/

section W1

variable {m n : ℕ}

/-- Ein Homomorphismus der Signatur aus einer Abbildung, die mit `min`, `max` und der Umkehr vertauscht. -/
def homVon (e : Fin m → Fin n) (hmin : ∀ a b, e (min a b) = min (e a) (e b)) (hmax : ∀ a b, e (max a b) = max (e a) (e b))
    (hneg : ∀ a, e (negFin m a) = negFin n (e a)) : L.Hom (Fin m) (Fin n) where
  toFun := e
  map_fun' := by
    intro k f x
    match k, f with
    | 1, .neg => exact hneg (x 0)
    | 2, .and => exact hmin (x 0) (x 1)
    | 2, .or => exact hmax (x 0) (x 1)
  map_rel' := fun r => nomatch r

/-- (W1) **Jeder Term vertauscht mit einer solchen Abbildung**, in jeder Stelligkeit. -/
theorem realize_komm {α : Type} (e : Fin m → Fin n) (hmin : ∀ a b, e (min a b) = min (e a) (e b))
    (hmax : ∀ a b, e (max a b) = max (e a) (e b)) (hneg : ∀ a, e (negFin m a) = negFin n (e a)) (t : L.Term α) (v : α → Fin m) :
    t.realize (e ∘ v) = e (t.realize v) :=
  HomClass.realize_term (homVon e hmin hmax hneg)

theorem eSym_min (m : ℕ) (a b : Fin m) : eSym m (min a b) = min (eSym m a) (eSym m b) := by
  refine Fin.eq_of_val_eq ?_
  simp only [eSym_val, Fin.coe_min]
  split_ifs <;> omega

theorem eSym_max (m : ℕ) (a b : Fin m) : eSym m (max a b) = max (eSym m a) (eSym m b) := by
  refine Fin.eq_of_val_eq ?_
  simp only [eSym_val, Fin.coe_max]
  split_ifs <;> omega

/-- (W1) **Der Aufstieg ist längs `eSym` konservativ, bei geradem m und in jeder Stelligkeit:**  jede Termfunktion der höheren Stufe lässt
das Bild der niederen nicht los und ist dort die Termfunktion desselben Terms (`Res ⊆ K_m`), und jede Termfunktion der niederen ist so
eine Einschränkung (`K_m ⊆ Res`).  Beides ist dieselbe Gleichung. -/
theorem res_gleich (m : ℕ) (hm : m % 2 = 0) {α : Type} (t : L.Term α) (v : α → Fin m) :
    t.realize (fun i => eSym m (v i)) = eSym m (t.realize v) :=
  realize_komm (eSym m) (eSym_min m) (eSym_max m) (StageParity.eSym_negFin m hm) t v

/-- (W1) **Dasselbe für den geraden Doppelschritt.** -/
theorem res_gleich_dg (k : ℕ) {α : Type} (t : L.Term α) (v : α → Fin (2 * k)) :
    t.realize (fun i => dg k (v i)) = dg k (t.realize v) :=
  realize_komm (dg k)
    (fun a b => Fin.eq_of_val_eq (by simp only [dg_val, Fin.coe_min]; split_ifs <;> omega))
    (fun a b => Fin.eq_of_val_eq (by simp only [dg_val, Fin.coe_max]; split_ifs <;> omega))
    (dg_negFin k) t v

end W1

/-! ## W2 — Konservativität an den Kreisen, Eichung 3 → 4

`P_m`:  zwei Vollkreise gehören zusammen, wenn der eine in der Bahn des anderen unter Umkehr und Drehsinn liegt (die vier Lesungen, `GegenidentitaetProbe.bahn_ununterscheidbar`,
`SpiegelfesteAnordnungen.bahn_all`).  Die schärfere Lesung lässt in der höheren Stufe auch alle Drehungen der Wörter zu.  Vergleich als `Bool`, ohne `decide` über
Listenmitgliedschaft. -/

/-- Gleichheit zweier Negatorwörter, über die Werte. -/
def gleichW {k : ℕ} : List (Fin k) → List (Fin k) → Bool
  | [], [] => true
  | a :: p, b :: q => Nat.beq a.val b.val && gleichW p q
  | _, _ => false

/-- Die vier Lesungen eines Wortes. -/
def lesungen {k : ℕ} (x : List (Fin k)) : List (List (Fin k)) :=
  [x, GegenidentitaetProbe.umkehr x, GegenidentitaetProbe.dreh x, GegenidentitaetProbe.umkehr (GegenidentitaetProbe.dreh x)]

/-- `y` ist eine Lesung von `x`, bis auf eine Drehung des Wortes. -/
def inBahnDreh {k : ℕ} (x y : List (Fin k)) : Bool :=
  (lesungen x).any fun z => (List.range z.length).any fun r => gleichW (z.rotate r) y

/-- (W2) **Bei drei Werten liegen die zwei Vollkreise in einer Bahn** — die Umkehr führt (4) in (5) (`NegationCycle.tafelVI5_eq_mirror`). -/
theorem drei_eine_bahn : GegenidentitaetProbe.umkehr NegationCycle.tafelVI4 = NegationCycle.tafelVI5 := by decide

/-- (W2) **Nach dem Aufstieg trennen sie sich, in jeder Schubrichtung:**  das Bild von (5) ist keine Lesung des Bildes von (4), auch
nicht bis auf Drehung. -/
theorem drei_getrennt (b : Bool) :
    inBahnDreh (AkkretivitaetsBruecke.phi b NegationCycle.tafelVI4) (AkkretivitaetsBruecke.phi b NegationCycle.tafelVI5) = false := by
  cases b <;> decide

/-- (W2) **Über beide Schubrichtungen zusammen fallen sie wieder in eine Bahn:**  die Umkehr tauscht die Schubrichtung (`AkkretivitaetsBruecke.phi_umkehr`). -/
theorem drei_beide :
    GegenidentitaetProbe.umkehr (AkkretivitaetsBruecke.phi true NegationCycle.tafelVI4) =
      AkkretivitaetsBruecke.phi false NegationCycle.tafelVI5 := by
  rw [AkkretivitaetsBruecke.phi_umkehr, drei_eine_bahn]; rfl

end Reformulation.Proemial.StufenZusammenfassung

/-! ## Axiom-Wachen (gemessen, verbatim) -/

/-- info: 'Reformulation.Proemial.StufenZusammenfassung.dg_val' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.StufenZusammenfassung.dg_val

/-- info: 'Reformulation.Proemial.StufenZusammenfassung.dg_strictMono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.StufenZusammenfassung.dg_strictMono

/-- info: 'Reformulation.Proemial.StufenZusammenfassung.dg_negFin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.StufenZusammenfassung.dg_negFin

/-- info: 'Reformulation.Proemial.StufenZusammenfassung.dgn_val' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.StufenZusammenfassung.dgn_val

/-- info: 'Reformulation.Proemial.StufenZusammenfassung.dgn_strictMono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.StufenZusammenfassung.dgn_strictMono

/-- info: 'Reformulation.Proemial.StufenZusammenfassung.dgn_negFin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.StufenZusammenfassung.dgn_negFin

/-- info: 'Reformulation.Proemial.StufenZusammenfassung.iG_strictMono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.StufenZusammenfassung.iG_strictMono

/-- info: 'Reformulation.Proemial.StufenZusammenfassung.iG_negFin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.StufenZusammenfassung.iG_negFin

/-- info: 'Reformulation.Proemial.StufenZusammenfassung.iG_dg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.StufenZusammenfassung.iG_dg

/-- info: 'Reformulation.Proemial.StufenZusammenfassung.iG_cover' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.StufenZusammenfassung.iG_cover

/-- info: 'Reformulation.Proemial.StufenZusammenfassung.dg_surj_aussen' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.StufenZusammenfassung.dg_surj_aussen

/-- info: 'Reformulation.Proemial.StufenZusammenfassung.ganzes_universell' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.StufenZusammenfassung.ganzes_universell

/-- info: 'Reformulation.Proemial.StufenZusammenfassung.ganzes_kein_glied' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.StufenZusammenfassung.ganzes_kein_glied

/-- info: 'Reformulation.Proemial.StufenZusammenfassung.du_val' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.StufenZusammenfassung.du_val

/-- info: 'Reformulation.Proemial.StufenZusammenfassung.du_strictMono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.StufenZusammenfassung.du_strictMono

/-- info: 'Reformulation.Proemial.StufenZusammenfassung.du_negFin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.StufenZusammenfassung.du_negFin

/-- info: 'Reformulation.Proemial.StufenZusammenfassung.iU_strictMono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.StufenZusammenfassung.iU_strictMono

/-- info: 'Reformulation.Proemial.StufenZusammenfassung.iU_negFin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.StufenZusammenfassung.iU_negFin

/-- info: 'Reformulation.Proemial.StufenZusammenfassung.iU_du' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.StufenZusammenfassung.iU_du

/-- info: 'Reformulation.Proemial.StufenZusammenfassung.iU_cover' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.StufenZusammenfassung.iU_cover

/-- info: 'Reformulation.Proemial.StufenZusammenfassung.ganzesU_kein_glied' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.StufenZusammenfassung.ganzesU_kein_glied

/-- info: 'Reformulation.Proemial.StufenZusammenfassung.kein_weg_zurueck' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Proemial.StufenZusammenfassung.kein_weg_zurueck

/-- info: 'Reformulation.Proemial.StufenZusammenfassung.weg_hin' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.StufenZusammenfassung.weg_hin

/-- info: 'Reformulation.Proemial.StufenZusammenfassung.weg_hin_eSym' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.StufenZusammenfassung.weg_hin_eSym

/-- info: 'Reformulation.Proemial.StufenZusammenfassung.leG_iG' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.StufenZusammenfassung.leG_iG

/-- info: 'Reformulation.Proemial.StufenZusammenfassung.iG_min' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.StufenZusammenfassung.iG_min

/-- info: 'Reformulation.Proemial.StufenZusammenfassung.iG_max' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.StufenZusammenfassung.iG_max

/-- info: 'Reformulation.Proemial.StufenZusammenfassung.ist0_iG' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.StufenZusammenfassung.ist0_iG

/-- info: 'Reformulation.Proemial.StufenZusammenfassung.ist1_iG' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.StufenZusammenfassung.ist1_iG

/-- info: 'Reformulation.Proemial.StufenZusammenfassung.w_iG' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.StufenZusammenfassung.w_iG

/-- info: 'Reformulation.Proemial.StufenZusammenfassung.w_iG_eins' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.StufenZusammenfassung.w_iG_eins

/-- info: 'Reformulation.Proemial.StufenZusammenfassung.realize_komm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.StufenZusammenfassung.realize_komm

/-- info: 'Reformulation.Proemial.StufenZusammenfassung.eSym_min' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.StufenZusammenfassung.eSym_min

/-- info: 'Reformulation.Proemial.StufenZusammenfassung.eSym_max' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.StufenZusammenfassung.eSym_max

/-- info: 'Reformulation.Proemial.StufenZusammenfassung.res_gleich' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.StufenZusammenfassung.res_gleich

/-- info: 'Reformulation.Proemial.StufenZusammenfassung.res_gleich_dg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.StufenZusammenfassung.res_gleich_dg

/-- info: 'Reformulation.Proemial.StufenZusammenfassung.drei_eine_bahn' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.StufenZusammenfassung.drei_eine_bahn

/-- info: 'Reformulation.Proemial.StufenZusammenfassung.drei_getrennt' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.StufenZusammenfassung.drei_getrennt

/-- info: 'Reformulation.Proemial.StufenZusammenfassung.drei_beide' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.StufenZusammenfassung.drei_beide
