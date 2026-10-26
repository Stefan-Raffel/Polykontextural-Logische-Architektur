import Reformulation.Proemial.ErzeugteKetteProbe   -- Tower, stand, erzeugt, inFaser, regelNach, tower_ext, fwL; über Kenogram: IsRGS, isRGSAux, rgsList

/-!
# Proemial.SymmetrieGabelungProbe — vertauschbare Fortsetzungen an der Gabelung, verträglich mit Regel → Kette

STANDALONE, NICHT im Aggregat;  Target `Probes`.  AxiomGate unberührt.  Kleine Sonde nach
`KorpusRev2/Prompt_Instanz_Symmetrie_Gabelung_Sonde.md` (Mathematiker, 26.10.2026 06:23;  Architekt 06:22 „kleine Sonde").  Grundlage:
`KorpusRev2/Vorprobe_Symmetrie_an_der_Gabelung_Mathematiker.md` (06:17) und die Kratzdatei `T_Vorprobe_Skripte/Symmetrie_Gabelung_sym.py`;
Festlegung „symmetrisch" im Nachtrag zu `KorpusRev2/Instanz_Gegenstand_Relator_Relatum_mit_Nachtrag.md`.  Konsumiert `ErzeugteKetteProbe`
(`Tower`, `stand`, `erzeugt`, `inFaser`, `regelNach`, `tower_ext`, `fwL`, `forkWidth_fwL`) und `Kenogram` (`IsRGS`, `isRGSAux`,
`foldl_max_eq`, `rgsList`);  ändert nichts davon.

## WAS

Der **Kettenbaum**:  Knoten sind die RGS aller Längen, die Kinder von r sind `r ++ [k]` mit k ≤ max r + 1 (an [] nur 0).  An r ist k ≤ max r
eine **Wiederholung**, k = max r + 1 der **neue Wert**.  Die **Vertauschung** `tausch r k k'` ersetzt in jeder Kette mit Präfix
`r ++ [k]` die Stelle |r| durch k' und umgekehrt, und lässt alles andere stehen (`zeichenTausch` ist die Vertauschung zweier Zeichen).

```text
wiederholung_tausch   FOLGERUNG          S1⇐:  r ≠ [], k, k' ≤ max r  →  tausch r k k' erhält RGS (beide Richtungen), ist eine Involution,
                                         erhält Länge und Präfix-Ordnung, bildet r ++ [k] auf r ++ [k'] ab und hält jede Kette fest, die
                                         keine der beiden Fortsetzungen als Präfix hat — ein Automorphismus des Kettenbaums
neu_nicht_tauschbar   FOLGERUNG (dünn)   S1⇒, Mindestfassung:  r ≠ [] →  eine Wiederholung hat max r + 2 Fortsetzungen, der neue Wert
                                         max r + 3 (`forkWidth`)
paar_iff              FOLGERUNG (dünn)   S2:  zwei verschiedene Wiederholungen an r  ↔  r ≠ [] ∧ 1 ≤ max r
tausch_aequivariant   FOLGERUNG          S3:  erzeugt (τ·c) n = τ (erzeugt c n), für jede Regel c und jedes n
faser_tausch          FOLGERUNG (dünn)   S3, Folge:  inFaser c s ↔ inFaser (τ·c) (τ s)
eich_paare            EICHUNG (decide)   an `[0]` und [0,0] kein Paar;  an [0,1] genau (0,1);  an [0,1,2] drei Paare
eich_unterbaum        EICHUNG (decide)   Fortsetzungen der Länge |s| + 3:  [0,1,0] 37 = [0,1,1] 37 ≠ [0,1,2] 77;  [0,0] 15 ≠ [0,1] 37
eich_bruch            EICHUNG            die Regel nach [0,1,0] erzeugt [0,1,0], ihr τ-Bild (τ an [0,1], Wiederholungen 0, 1) [0,1,1]
gegen_neuer_wert      EICHUNG (decide)   Gegenprobe:  tausch [0,1] 0 2 (2 = neuer Wert) führt die RGS [0,1,2,3] auf [0,1,0,3], keine RGS
gegen_paar_null       EICHUNG            Gegenprobe:  paar_iff mit „0 ≤ max r" fällt an [0,0]
```

**Die Wirkung auf Regeln** (`wirk`, im Text τ·c):  an x wählt τ·c, was c an τ x wählt — an r selbst durch `zeichenTausch` zurückgeholt,
sonst unverändert.  Der Grund steht als Satz da (`tausch_snoc`):  τ (s ++ [j]) = τ s ++ [j], ausser an s = r, wo das angehängte Zeichen
selbst getauscht wird.  `tauschT` ist τ auf dem Turm.

**τ ist KEINE Umbenennung der Werte:**  [0,1,0] ↦ [0,1,1] ändert das Muster ABA ↦ ABB.  `ErzeugteKetteProbe.umtausch_identitaet` (G-2)
und `gabelung_nicht_vertauschbar` (G-3), beide über Umbenennungen, bleiben richtig und unberührt.  τ ist eine Symmetrie der LAGE (des
Baums der Wahlmöglichkeiten), nicht der Kenogramme.

## FESTLEGUNG „symmetrisch"

Mathematiker 26.10., Lesart (iv):  Tausch zweier Glieder gleicher Sorte, im selben Wechsel mit der Umkehr der Ordnung auf
Relator/Relatum — A20-4 (Definitionen §20, Fassung 25.10.).  **Diese Sonde liefert den TAUSCH, nicht die UMKEHR.**

## LESART

Buridans Lage:  zwei als Kenogramme verschiedene, als Alternativen gleiche Fortsetzungen (C&V S. 15 „two bundles of hay of absolutely
equal attractiveness" — Halbsatz Textschicht, Seite von Hermeneutes am Bild gelesen).  ZUORDNUNG, ungeprüft.  An einer symmetrischen
Gabelung fallen zusammen:  τ, die Notwendigkeit der Wahl ([T66], [T30]), der Verlust daneben (SA1 mit Zusatz).  Die Wahl bricht τ:  c und
τ·c erzeugen verschiedene Ketten (`eich_bruch`).  Ob Symmetriebruch Günthers „implies a reversal of the order" trifft:  OFFEN — Frage an
Horistes und Speculum.

## BEOBACHTUNG (kein Satz)

Symmetrische Gabelungen beginnen auf Stufe 2 (an [0,1]), der Verlust daneben ebenfalls — nicht aus demselben Grund:  auf einem Pfad durch
[0,0] gibt es auf Stufe 2 Verlust daneben, aber keine symmetrische Gabelung (`eich_paare`, `VerlustDanebenKuenftigProbe.daneben_iff`).

## NICHT

Kein Träger für §20;  nicht „A20-4 erfüllt" (S3 ist eine Kommutation, keine Umkehrung);  kein Text in Rev11.

**Verbotene Kurzformen:**  „τ ist Günthers symmetrischer Umtausch";  „Buridan formalisiert";  „A20-4 erfüllt";  „die Wahl kehrt die
Ordnung um" (statt:  bricht die Symmetrie — Lesart).

## Bauweise

Der RGS-Lauf über eine Verkettung (`isRGSAux_append`) trägt S1:  hinter einem nichtleeren r hängt die Gültigkeit von `r ++ k :: t` für
k ≤ max r nicht von k ab (`isRGS_wiederholung`).  Die Konjugation geht unmittelbar über `Choice` (abhängiger Untertyp);  eine Fassung über
`List ℕ`-Regeln war nicht nötig.  Fallunterscheidungen über `Nat.decEq` und `decEq` auf `List ℕ`;  `omega` nur an Zahlzielen.
Hilfssätze:  `foldr_max_start`, `max_append`, `tausch_form`, `tausch_sonst`, `form_oder_fest`, `zeichenTausch_zeichenTausch`,
`zeichenTausch_le`, `tausch_tausch`, `tausch_length`, `tausch_rgs`, `praefix_fall`, `tausch_praefix_mp`, `fwL_ne`, `tausch_nil`, `tausch_r`,
`max_tausch`, `tauschT_tauschT`, `tausch_eq_r`, `stand_wirk`.
Kein `sorry`, kein `Classical.choice`, kein `native_decide`, kein True-Feld.
-/

namespace Reformulation.Proemial.SymmetrieGabelungProbe

open Reformulation.Kenogram
open Reformulation.Proemial.TowerAsymmetryProbe (Tower)
open Reformulation.Proemial.KenogramForkProbe (Choice forkWidth)
open Reformulation.Proemial.ErzeugteKetteProbe

/-! ## Werkzeug:  der Lauf über eine Verkettung, das Maximum -/

theorem isRGSAux_append (m : ℕ) (r u : List ℕ) :
    isRGSAux m true (r ++ u) = (isRGSAux m true r && isRGSAux (r.foldl max m) true u) := by
  induction r generalizing m with
  | nil => simp only [List.nil_append, isRGSAux, List.foldl_nil, Bool.true_and]
  | cons a t ih =>
    simp only [List.cons_append, isRGSAux, List.foldl_cons, ih (max m a)]
    exact (Bool.and_assoc _ _ _).symm

theorem foldr_max_start (l : List ℕ) (b : ℕ) : l.foldr max b = max (l.foldr max 0) b := by
  induction l with
  | nil => simp only [List.foldr_nil]; omega
  | cons a t ih => simp only [List.foldr_cons, ih]; omega

theorem max_append (l u : List ℕ) : (l ++ u).foldr max 0 = max (l.foldr max 0) (u.foldr max 0) := by
  rw [List.foldr_append, foldr_max_start]

/-- **an einer nichtleeren Kette r sind zwei Wiederholungen als Fortsetzung gleichwertig:**  ob `r ++ k :: t` eine RGS ist, hängt
    für k ≤ max r nicht von k ab -/
theorem isRGS_wiederholung (r : List ℕ) (hr : r ≠ []) (k k' : ℕ) (hk : k ≤ r.foldr max 0) (hk' : k' ≤ r.foldr max 0)
    (t : List ℕ) : IsRGS (r ++ k :: t) ↔ IsRGS (r ++ k' :: t) := by
  match r, hr with
  | a :: r', _ =>
    have hM : r'.foldl max a = (a :: r').foldr max 0 := by
      rw [foldl_max_eq, List.foldr_cons]
    have e1 : max (r'.foldl max a) k = r'.foldl max a := by rw [hM]; omega
    have e2 : max (r'.foldl max a) k' = r'.foldl max a := by rw [hM]; omega
    have d1 : decide (k ≤ r'.foldl max a + 1) = true := decide_eq_true (by rw [hM]; omega)
    have d2 : decide (k' ≤ r'.foldl max a + 1) = true := decide_eq_true (by rw [hM]; omega)
    unfold IsRGS
    simp only [List.cons_append, isRGSAux, isRGSAux_append, d1, d2, e1, e2, Bool.true_and]

/-! ## Die Vertauschung -/

/-- der Tausch zweier Zeichen -/
def zeichenTausch (k k' j : ℕ) : ℕ := if j = k then k' else if j = k' then k else j

/-- **die Vertauschung zweier Fortsetzungen an r:**  `r ++ k :: t ↦ r ++ k' :: t` und umgekehrt, sonst nichts -/
def tausch (r : List ℕ) (k k' : ℕ) (s : List ℕ) : List ℕ :=
  match s.drop r.length with
  | a :: t => if s.take r.length = r then r ++ zeichenTausch k k' a :: t else s
  | [] => s

theorem tausch_form (r : List ℕ) (k k' a : ℕ) (t : List ℕ) :
    tausch r k k' (r ++ a :: t) = r ++ zeichenTausch k k' a :: t := by
  unfold tausch
  rw [List.drop_left]
  dsimp only
  rw [List.take_left, if_pos rfl]

theorem tausch_sonst (r : List ℕ) (k k' : ℕ) (s : List ℕ) (h : ∀ a t, s ≠ r ++ a :: t) : tausch r k k' s = s := by
  unfold tausch
  split
  · next a t heq =>
    rcases decEq (s.take r.length) r with he | he
    · rw [if_neg he]
    · exact absurd (by rw [← List.take_append_drop r.length s, he, heq]) (h a t)
  · rfl

/-- jede Kette hat die Form `r ++ a :: t`, oder der Tausch lässt sie stehen -/
theorem form_oder_fest (r : List ℕ) (s : List ℕ) : (∃ a t, s = r ++ a :: t) ∨ ∀ a t, s ≠ r ++ a :: t := by
  rcases h : s.drop r.length with _ | ⟨a, t⟩
  · right; intro a t e
    rw [e, List.drop_left] at h; exact List.cons_ne_nil _ _ h
  · rcases decEq (s.take r.length) r with he | he
    · right; intro a' t' e
      rw [e, List.take_left] at he; exact he rfl
    · left; exact ⟨a, t, by rw [← List.take_append_drop r.length s, he, h]⟩

theorem zeichenTausch_zeichenTausch (k k' j : ℕ) : zeichenTausch k k' (zeichenTausch k k' j) = j := by
  unfold zeichenTausch
  rcases Nat.decEq j k with h1 | h1
  · rw [if_neg h1]
    rcases Nat.decEq j k' with h2 | h2
    · rw [if_neg h2, if_neg h1, if_neg h2]
    · rw [if_pos h2]
      rcases Nat.decEq k k with h3 | h3
      · exact absurd rfl h3
      · rw [if_pos h3, h2]
  · rw [if_pos h1]
    rcases Nat.decEq k' k with h3 | h3
    · rw [if_neg h3, if_pos rfl, h1]
    · rw [if_pos h3, h3, h1]

theorem zeichenTausch_le (k k' j M : ℕ) (hk : k ≤ M) (hk' : k' ≤ M) (hj : j ≤ M) : zeichenTausch k k' j ≤ M := by
  unfold zeichenTausch
  rcases Nat.decEq j k with h1 | h1
  · rw [if_neg h1]
    rcases Nat.decEq j k' with h2 | h2
    · rw [if_neg h2]; exact hj
    · rw [if_pos h2]; exact hk
  · rw [if_pos h1]; exact hk'

/-! ## S1⇐ -/

theorem tausch_tausch (r : List ℕ) (k k' : ℕ) (s : List ℕ) : tausch r k k' (tausch r k k' s) = s := by
  rcases form_oder_fest r s with ⟨a, t, rfl⟩ | h
  · rw [tausch_form, tausch_form, zeichenTausch_zeichenTausch]
  · rw [tausch_sonst r k k' s h, tausch_sonst r k k' s h]

theorem tausch_length (r : List ℕ) (k k' : ℕ) (s : List ℕ) : (tausch r k k' s).length = s.length := by
  rcases form_oder_fest r s with ⟨a, t, rfl⟩ | h
  · rw [tausch_form]; simp only [List.length_append, List.length_cons]
  · rw [tausch_sonst r k k' s h]

theorem tausch_rgs (r : List ℕ) (hr : r ≠ []) (k k' : ℕ) (hk : k ≤ r.foldr max 0) (hk' : k' ≤ r.foldr max 0)
    (s : List ℕ) : IsRGS s ↔ IsRGS (tausch r k k' s) := by
  rcases form_oder_fest r s with ⟨a, t, rfl⟩ | h
  · rw [tausch_form]
    unfold zeichenTausch
    rcases Nat.decEq a k with h1 | h1
    · rw [if_neg h1]
      rcases Nat.decEq a k' with h2 | h2
      · rw [if_neg h2]
      · rw [if_pos h2, h2]; exact isRGS_wiederholung r hr k' k hk' hk t
    · rw [if_pos h1, h1]; exact isRGS_wiederholung r hr k k' hk hk' t
  · rw [tausch_sonst r k k' s h]

/-- ein Präfix von `r ++ a :: w` ist ein Präfix von r oder hat selbst die Form `r ++ a :: u` -/
theorem praefix_fall (r s w : List ℕ) (a : ℕ) (h : s <+: r ++ a :: w) : s <+: r ∨ ∃ u, s = r ++ a :: u := by
  rcases Nat.lt_or_ge r.length s.length with hl | hl
  · right
    have hp : r ++ [a] <+: s :=
      List.prefix_of_prefix_length_le (⟨w, by rw [List.append_assoc]; rfl⟩ : r ++ [a] <+: r ++ a :: w) h
        (by rw [List.length_append, List.length_singleton]; omega)
    obtain ⟨u, hu⟩ := hp
    exact ⟨u, by rw [← hu, List.append_assoc]; rfl⟩
  · left
    exact List.prefix_of_prefix_length_le h (List.prefix_append r (a :: w)) hl

theorem tausch_praefix_mp (r : List ℕ) (k k' : ℕ) (s t : List ℕ) (h : s <+: t) :
    tausch r k k' s <+: tausch r k k' t := by
  obtain ⟨v, rfl⟩ := h
  rcases form_oder_fest r s with ⟨a, u, rfl⟩ | hs
  · rw [show r ++ a :: u ++ v = r ++ a :: (u ++ v) by simp only [List.append_assoc, List.cons_append],
      tausch_form, tausch_form]
    exact ⟨v, by simp only [List.append_assoc, List.cons_append]⟩
  · rw [tausch_sonst r k k' s hs]
    rcases form_oder_fest r (s ++ v) with ⟨a, w, hw⟩ | ht
    · rw [hw, tausch_form]
      rcases praefix_fall r s w a (hw ▸ List.prefix_append s v) with hp | ⟨u, hu⟩
      · exact hp.trans (List.prefix_append r _)
      · exact absurd hu (hs a u)
    · rw [tausch_sonst r k k' _ ht]; exact List.prefix_append s v

/-- **S1⇐:**  an einer nichtleeren Kette r vertauscht `tausch r k k'` zwei Wiederholungen k, k' ≤ max r — ein Automorphismus
    des Kettenbaums:  er erhält RGS, ist eine Involution, erhält Länge und Präfix-Ordnung, bildet `r ++ [k]` auf `r ++ [k']` ab und
    hält alles fest, was keine der beiden Fortsetzungen als Präfix hat -/
theorem wiederholung_tausch (r : List ℕ) (hr : r ≠ []) (k k' : ℕ) (hk : k ≤ r.foldr max 0) (hk' : k' ≤ r.foldr max 0) :
    (∀ s, IsRGS s ↔ IsRGS (tausch r k k' s)) ∧ (∀ s, tausch r k k' (tausch r k k' s) = s) ∧
    (∀ s, (tausch r k k' s).length = s.length) ∧ (∀ s t, s <+: t ↔ tausch r k k' s <+: tausch r k k' t) ∧
    tausch r k k' (r ++ [k]) = r ++ [k'] ∧
    (∀ x, ¬ (r ++ [k] <+: x) → ¬ (r ++ [k'] <+: x) → tausch r k k' x = x) := by
  refine ⟨tausch_rgs r hr k k' hk hk', tausch_tausch r k k', tausch_length r k k', fun s t => ⟨tausch_praefix_mp r k k' s t,
    fun h => by have := tausch_praefix_mp r k k' _ _ h; rwa [tausch_tausch, tausch_tausch] at this⟩, ?_, ?_⟩
  · rw [tausch_form]; unfold zeichenTausch; rw [if_pos rfl]
  · intro x h1 h2
    rcases form_oder_fest r x with ⟨a, t, rfl⟩ | h
    · rw [tausch_form]; unfold zeichenTausch
      rcases Nat.decEq a k with e1 | e1
      · rw [if_neg e1]
        rcases Nat.decEq a k' with e2 | e2
        · rw [if_neg e2]
        · exact absurd ⟨t, by rw [e2, List.append_assoc]; rfl⟩ h2
      · exact absurd ⟨t, by rw [e1, List.append_assoc]; rfl⟩ h1
    · exact tausch_sonst r k k' x h

/-! ## S1⇒ (Mindestfassung) -/

theorem fwL_ne (l : List ℕ) (hl : l ≠ []) : fwL l = l.foldr max 0 + 2 := by
  unfold fwL
  have : (fun k => decide (l = [] → k = 0)) = fun _ => true := funext fun k => decide_eq_true (fun h => absurd h hl)
  rw [this, List.filter_true, List.length_range]

/-- **S1⇒, Mindestfassung:**  an einer nichtleeren Kette r hat jede Wiederholung max r + 2 Fortsetzungen, der neue Wert
    max r + 3 — kein Automorphismus des Baums führt das eine in das andere -/
theorem neu_nicht_tauschbar {n : ℕ} (x y : RGS n) (r : List ℕ) (hr : r ≠ []) (k : ℕ) (hk : k ≤ r.foldr max 0)
    (hx : x.val = r ++ [k]) (hy : y.val = r ++ [r.foldr max 0 + 1]) :
    forkWidth x = r.foldr max 0 + 2 ∧ forkWidth y = r.foldr max 0 + 3 := by
  rw [forkWidth_fwL, forkWidth_fwL, hx, hy, fwL_ne _ (List.append_ne_nil_of_left_ne_nil hr _),
    fwL_ne _ (List.append_ne_nil_of_left_ne_nil hr _), max_append, max_append]
  simp only [List.foldr_cons, List.foldr_nil]
  constructor <;> omega

/-! ## S2 -/

/-- **S2:**  an r gibt es zwei verschiedene Wiederholungen genau dann, wenn r nicht leer ist und sein Maximum mindestens 1 -/
theorem paar_iff (r : List ℕ) :
    (∃ k k', k ≠ k' ∧ k ≤ r.foldr max 0 ∧ k' ≤ r.foldr max 0) ↔ (r ≠ [] ∧ 1 ≤ r.foldr max 0) := by
  constructor
  · rintro ⟨k, k', hne, hk, hk'⟩
    have h1 : 1 ≤ r.foldr max 0 := by omega
    refine ⟨fun e => ?_, h1⟩
    rw [e, List.foldr_nil] at h1; exact absurd h1 (by decide)
  · intro h
    exact ⟨0, 1, by decide, Nat.zero_le _, h.2⟩

/-- die Paare k < k' von Wiederholungen an l -/
def paare (l : List ℕ) : List (ℕ × ℕ) :=
  (List.range (l.foldr max 0 + 1)).flatMap fun k =>
    ((List.range (l.foldr max 0 + 1)).filter fun k' => decide (k < k')).map fun k' => (k, k')

theorem eich_paare :
    paare [0] = [] ∧ paare [0, 0] = [] ∧ paare [0, 1] = [(0, 1)] ∧ paare [0, 1, 2] = [(0, 1), (0, 2), (1, 2)] := by
  decide

/-! ## S3:  die Wirkung auf Regeln -/

theorem tausch_nil (r : List ℕ) (k k' : ℕ) : tausch r k k' [] = [] :=
  tausch_sonst r k k' [] fun a t e => (List.append_ne_nil_of_right_ne_nil r (List.cons_ne_nil a t)) e.symm

theorem tausch_r (r : List ℕ) (k k' : ℕ) : tausch r k k' r = r :=
  tausch_sonst r k k' r fun a t e => by
    have := congrArg List.length e
    simp only [List.length_append, List.length_cons] at this; omega

theorem max_tausch (r : List ℕ) (k k' : ℕ) (hk : k ≤ r.foldr max 0) (hk' : k' ≤ r.foldr max 0) (s : List ℕ) :
    (tausch r k k' s).foldr max 0 = s.foldr max 0 := by
  rcases form_oder_fest r s with ⟨a, t, rfl⟩ | h
  · rw [tausch_form, max_append, max_append]
    simp only [List.foldr_cons]
    unfold zeichenTausch
    rcases Nat.decEq a k with h1 | h1
    · rw [if_neg h1]
      rcases Nat.decEq a k' with h2 | h2
      · rw [if_neg h2]
      · rw [if_pos h2]; subst h2; omega
    · rw [if_pos h1]; subst h1; omega
  · rw [tausch_sonst r k k' s h]

/-- τ auf dem Turm -/
def tauschT (r : List ℕ) (hr : r ≠ []) (k k' : ℕ) (hk : k ≤ r.foldr max 0) (hk' : k' ≤ r.foldr max 0) (x : Tower) : Tower :=
  ⟨x.1, ⟨tausch r k k' x.2.val, by rw [tausch_length]; exact x.2.property.1,
    (tausch_rgs r hr k k' hk hk' x.2.val).mp x.2.property.2⟩⟩

theorem tauschT_tauschT (r : List ℕ) (hr : r ≠ []) (k k' : ℕ) (hk : k ≤ r.foldr max 0) (hk' : k' ≤ r.foldr max 0)
    (x : Tower) : tauschT r hr k k' hk hk' (tauschT r hr k k' hk hk' x) = x :=
  tower_ext rfl (tausch_tausch r k k' x.2.val)

/-- **die Wirkung von τ auf eine Regel:**  an x wählt τ·c, was c an τ x wählt — an r selbst durch σ zurückgeholt, sonst unverändert -/
def wirk (r : List ℕ) (hr : r ≠ []) (k k' : ℕ) (hk : k ≤ r.foldr max 0) (hk' : k' ≤ r.foldr max 0) (c : Choice) : Choice :=
  fun x =>
  ⟨if x.2.val = r then zeichenTausch k k' (c (tauschT r hr k k' hk hk' x)).1 else (c (tauschT r hr k k' hk hk' x)).1, by
    have hb := (c (tauschT r hr k k' hk hk' x)).2
    change (c (tauschT r hr k k' hk hk' x)).1 ≤ (tausch r k k' x.2.val).foldr max 0 + 1 ∧
      (tausch r k k' x.2.val = [] → (c (tauschT r hr k k' hk hk' x)).1 = 0) at hb
    rw [max_tausch r k k' hk hk'] at hb
    rcases decEq x.2.val r with he | he
    · rw [if_neg he]
      exact ⟨hb.1, fun h0 => hb.2 (by rw [h0]; exact tausch_nil r k k')⟩
    · rw [if_pos he]
      refine ⟨zeichenTausch_le k k' _ _ (by rw [he]; omega) (by rw [he]; omega) hb.1, ?_⟩
      intro h0; exact absurd (he.symm.trans h0) hr⟩

theorem tausch_eq_r (r : List ℕ) (k k' : ℕ) (s : List ℕ) : tausch r k k' s = r ↔ s = r := by
  constructor
  · intro h; have := congrArg (tausch r k k') h; rwa [tausch_tausch, tausch_r] at this
  · intro h; rw [h]; exact tausch_r r k k'

/-- **τ und das Anhängen:**  an r selbst wird das angehängte Zeichen getauscht, sonst nicht -/
theorem tausch_snoc (r : List ℕ) (k k' : ℕ) (s : List ℕ) (j : ℕ) :
    tausch r k k' (s ++ [j]) = tausch r k k' s ++ [if s = r then zeichenTausch k k' j else j] := by
  rcases decEq s r with he | he
  · rw [if_neg he]
    rcases form_oder_fest r s with ⟨a, u, rfl⟩ | hs
    · rw [show r ++ a :: u ++ [j] = r ++ a :: (u ++ [j]) by simp only [List.append_assoc, List.cons_append],
        tausch_form, tausch_form]
      simp only [List.append_assoc, List.cons_append]
    · rw [tausch_sonst r k k' s hs]
      refine tausch_sonst r k k' _ fun a t e => ?_
      rcases praefix_fall r s t a (e ▸ List.prefix_append s [j]) with hp | ⟨u, hu⟩
      · have hl := congrArg List.length e
        simp only [List.length_append, List.length_cons, List.length_nil] at hl
        exact he (hp.eq_of_length (Nat.le_antisymm hp.length_le (by omega)))
      · exact hs a u hu
  · rw [if_pos he, he, tausch_r]
    exact tausch_form r k k' j []

theorem stand_wirk (r : List ℕ) (hr : r ≠ []) (k k' : ℕ) (hk : k ≤ r.foldr max 0) (hk' : k' ≤ r.foldr max 0) (c : Choice) :
    ∀ n, stand (wirk r hr k k' hk hk' c) n = tauschT r hr k k' hk hk' (stand c n)
  | 0 => tower_ext rfl (tausch_nil r k k').symm
  | n + 1 => by
    refine tower_ext (by rw [stand_fst]; exact (stand_fst c (n + 1)).symm) ?_
    rw [stand_succ_val, stand_wirk r hr k k' hk hk' c n]
    show tausch r k k' (stand c n).2.val ++ [(wirk r hr k k' hk hk' c (tauschT r hr k k' hk hk' (stand c n))).1] =
      tausch r k k' (stand c (n + 1)).2.val
    rw [stand_succ_val, tausch_snoc]
    show _ ++ [if tausch r k k' (stand c n).2.val = r then
        zeichenTausch k k' (c (tauschT r hr k k' hk hk' (tauschT r hr k k' hk hk' (stand c n)))).1
      else (c (tauschT r hr k k' hk hk' (tauschT r hr k k' hk hk' (stand c n)))).1] = _
    rw [tauschT_tauschT]
    rcases decEq (stand c n).2.val r with he | he
    · rw [if_neg (fun h => he ((tausch_eq_r r k k' _).mp h)), if_neg he]
    · rw [if_pos ((tausch_eq_r r k k' _).mpr he), if_pos he]

/-- **S3:  der Wechsel Regel → Kette ist τ-äquivariant** -/
theorem tausch_aequivariant (r : List ℕ) (hr : r ≠ []) (k k' : ℕ) (hk : k ≤ r.foldr max 0) (hk' : k' ≤ r.foldr max 0)
    (c : Choice) (n : ℕ) : erzeugt (wirk r hr k k' hk hk' c) n = tausch r k k' (erzeugt c n) := by
  unfold erzeugt; rw [stand_wirk]; rfl

/-- **S3, Folge:  τ führt die Faser über s in die Faser über τ s über** -/
theorem faser_tausch (r : List ℕ) (hr : r ≠ []) (k k' : ℕ) (hk : k ≤ r.foldr max 0) (hk' : k' ≤ r.foldr max 0)
    (c : Choice) (s : List ℕ) : inFaser c s ↔ inFaser (wirk r hr k k' hk hk' c) (tausch r k k' s) := by
  unfold inFaser
  rw [tausch_length, tausch_aequivariant]
  constructor
  · intro h; rw [h]
  · intro h; have := congrArg (tausch r k k') h; rwa [tausch_tausch, tausch_tausch] at this

/-! ## Eichungen -/

theorem isRGS_010 : IsRGS [0, 1, 0] := by decide

/-- **die Wahl bricht τ:**  die Regel nach [0,1,0] und ihr τ-Bild (τ an [0,1], Wiederholungen 0 und 1) erzeugen [0,1,0] und
    [0,1,1] -/
theorem eich_bruch :
    erzeugt (regelNach [0, 1, 0] isRGS_010) 3 = [0, 1, 0] ∧
    erzeugt (wirk [0, 1] (List.cons_ne_nil 0 [1]) 0 1 (by decide) (by decide) (regelNach [0, 1, 0] isRGS_010)) 3 = [0, 1, 1] := by
  have h : erzeugt (regelNach [0, 1, 0] isRGS_010) 3 = [0, 1, 0] := erzeugt_regelNach _ isRGS_010
  refine ⟨h, ?_⟩
  rw [tausch_aequivariant, h]
  decide

/-- die Zahl der RGS der Länge |s| + d mit Präfix s -/
def fortsetzungen (s : List ℕ) (d : ℕ) : ℕ :=
  ((rgsList (s.length + d)).filter fun l => decide (l.take s.length = s)).length

/-- **die Unterbäume unter den Kindern, bis Tiefe 3 gezählt:**  an [0,1] haben die zwei Wiederholungen gleich viele Fortsetzungen
    (37), der neue Wert mehr (77);  an `[0]` haben die zwei Kinder [0,0] und [0,1] verschieden viele (15 und 37) — dort kein Paar -/
theorem eich_unterbaum :
    fortsetzungen [0, 1, 0] 3 = 37 ∧ fortsetzungen [0, 1, 1] 3 = 37 ∧ fortsetzungen [0, 1, 2] 3 = 77 ∧
    fortsetzungen [0, 0] 3 = 15 ∧ fortsetzungen [0, 1] 3 = 37 := by
  decide

/-! ## Gegenproben -/

theorem isRGS_0123 : IsRGS [0, 1, 2, 3] := by decide

/-- **ein neuer Wert ist nicht tauschbar:**  `tausch [0,1] 0 2` (2 ist an [0,1] der neue Wert) führt die RGS [0,1,2,3] aus dem Baum -/
theorem gegen_neuer_wert : IsRGS [0, 1, 2, 3] ∧ tausch [0, 1] 0 2 [0, 1, 2, 3] = [0, 1, 0, 3] ∧ ¬ IsRGS [0, 1, 0, 3] := by
  decide

/-- **`paar_iff` mit „0 ≤ max r" fällt** (an [0,0]) -/
theorem gegen_paar_null :
    ¬ ∀ r : List ℕ, (∃ k k', k ≠ k' ∧ k ≤ r.foldr max 0 ∧ k' ≤ r.foldr max 0) ↔ (r ≠ [] ∧ 0 ≤ r.foldr max 0) := by
  intro H
  have h := (paar_iff [0, 0]).mp ((H [0, 0]).mpr ⟨List.cons_ne_nil 0 [0], Nat.zero_le _⟩)
  exact absurd h.2 (by decide)

end Reformulation.Proemial.SymmetrieGabelungProbe

/-! ## Axiom-Wachen (gemessen, verbatim) -/

/-- info: 'Reformulation.Proemial.SymmetrieGabelungProbe.isRGSAux_append' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.SymmetrieGabelungProbe.isRGSAux_append

/-- info: 'Reformulation.Proemial.SymmetrieGabelungProbe.foldr_max_start' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.SymmetrieGabelungProbe.foldr_max_start

/-- info: 'Reformulation.Proemial.SymmetrieGabelungProbe.max_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.SymmetrieGabelungProbe.max_append

/-- info: 'Reformulation.Proemial.SymmetrieGabelungProbe.isRGS_wiederholung' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.SymmetrieGabelungProbe.isRGS_wiederholung

/-- info: 'Reformulation.Proemial.SymmetrieGabelungProbe.tausch_form' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Proemial.SymmetrieGabelungProbe.tausch_form

/-- info: 'Reformulation.Proemial.SymmetrieGabelungProbe.tausch_sonst' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Proemial.SymmetrieGabelungProbe.tausch_sonst

/-- info: 'Reformulation.Proemial.SymmetrieGabelungProbe.form_oder_fest' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Proemial.SymmetrieGabelungProbe.form_oder_fest

/-- info: 'Reformulation.Proemial.SymmetrieGabelungProbe.zeichenTausch_zeichenTausch' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Proemial.SymmetrieGabelungProbe.zeichenTausch_zeichenTausch

/-- info: 'Reformulation.Proemial.SymmetrieGabelungProbe.zeichenTausch_le' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Proemial.SymmetrieGabelungProbe.zeichenTausch_le

/-- info: 'Reformulation.Proemial.SymmetrieGabelungProbe.tausch_tausch' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Proemial.SymmetrieGabelungProbe.tausch_tausch

/-- info: 'Reformulation.Proemial.SymmetrieGabelungProbe.tausch_length' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.SymmetrieGabelungProbe.tausch_length

/-- info: 'Reformulation.Proemial.SymmetrieGabelungProbe.tausch_rgs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.SymmetrieGabelungProbe.tausch_rgs

/-- info: 'Reformulation.Proemial.SymmetrieGabelungProbe.praefix_fall' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.SymmetrieGabelungProbe.praefix_fall

/-- info: 'Reformulation.Proemial.SymmetrieGabelungProbe.tausch_praefix_mp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.SymmetrieGabelungProbe.tausch_praefix_mp

/-- info: 'Reformulation.Proemial.SymmetrieGabelungProbe.wiederholung_tausch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.SymmetrieGabelungProbe.wiederholung_tausch

/-- info: 'Reformulation.Proemial.SymmetrieGabelungProbe.fwL_ne' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.SymmetrieGabelungProbe.fwL_ne

/-- info: 'Reformulation.Proemial.SymmetrieGabelungProbe.neu_nicht_tauschbar' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.SymmetrieGabelungProbe.neu_nicht_tauschbar

/-- info: 'Reformulation.Proemial.SymmetrieGabelungProbe.paar_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.SymmetrieGabelungProbe.paar_iff

/-- info: 'Reformulation.Proemial.SymmetrieGabelungProbe.eich_paare' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Proemial.SymmetrieGabelungProbe.eich_paare

/-- info: 'Reformulation.Proemial.SymmetrieGabelungProbe.tausch_nil' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.SymmetrieGabelungProbe.tausch_nil

/-- info: 'Reformulation.Proemial.SymmetrieGabelungProbe.tausch_r' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.SymmetrieGabelungProbe.tausch_r

/-- info: 'Reformulation.Proemial.SymmetrieGabelungProbe.max_tausch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.SymmetrieGabelungProbe.max_tausch

/-- info: 'Reformulation.Proemial.SymmetrieGabelungProbe.tauschT_tauschT' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.SymmetrieGabelungProbe.tauschT_tauschT

/-- info: 'Reformulation.Proemial.SymmetrieGabelungProbe.tausch_eq_r' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.SymmetrieGabelungProbe.tausch_eq_r

/-- info: 'Reformulation.Proemial.SymmetrieGabelungProbe.tausch_snoc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.SymmetrieGabelungProbe.tausch_snoc

/-- info: 'Reformulation.Proemial.SymmetrieGabelungProbe.stand_wirk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.SymmetrieGabelungProbe.stand_wirk

/-- info: 'Reformulation.Proemial.SymmetrieGabelungProbe.tausch_aequivariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.SymmetrieGabelungProbe.tausch_aequivariant

/-- info: 'Reformulation.Proemial.SymmetrieGabelungProbe.faser_tausch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.SymmetrieGabelungProbe.faser_tausch

/-- info: 'Reformulation.Proemial.SymmetrieGabelungProbe.isRGS_010' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Proemial.SymmetrieGabelungProbe.isRGS_010

/-- info: 'Reformulation.Proemial.SymmetrieGabelungProbe.eich_bruch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.SymmetrieGabelungProbe.eich_bruch

/-- info: 'Reformulation.Proemial.SymmetrieGabelungProbe.eich_unterbaum' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Proemial.SymmetrieGabelungProbe.eich_unterbaum

/-- info: 'Reformulation.Proemial.SymmetrieGabelungProbe.isRGS_0123' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Proemial.SymmetrieGabelungProbe.isRGS_0123

/-- info: 'Reformulation.Proemial.SymmetrieGabelungProbe.gegen_neuer_wert' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Proemial.SymmetrieGabelungProbe.gegen_neuer_wert

/-- info: 'Reformulation.Proemial.SymmetrieGabelungProbe.gegen_paar_null' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.SymmetrieGabelungProbe.gegen_paar_null
