import Reformulation.Proemial.ErzeugteKetteProbe   -- Tower, stand, erzeugt, inFaser, regelNach, tower_ext, fwL; über Kenogram: IsRGS, isRGSAux, rgsList

/-!
# Proemial.SymmetrieGabelungProbe — vertauschbare Fortsetzungen an der Gabelung, verträglich mit Regel → Kette

STANDALONE, NICHT im Aggregat;  Target `Probes`.  AxiomGate unberührt.  Kleine Sonde nach
`KorpusRev2/Prompt_Instanz_Symmetrie_Gabelung_Sonde.md` (Mathematiker, 26.10.2026 06:23;  Architekt 06:22 „kleine Sonde").  Grundlage:
`KorpusRev2/Vorprobe_Symmetrie_an_der_Gabelung_Mathematiker.md` (06:17) und die Kratzdatei `T_Vorprobe_Skripte/Symmetrie_Gabelung_sym.py`;
Festlegung „symmetrisch" im Nachtrag zu `KorpusRev2/Instanz_Gegenstand_Relator_Relatum_mit_Nachtrag.md`.  **Nachzug** nach
`KorpusRev2/Prompt_Instanz_Nachzug_Symmetrie_Gabelung.md` (Mathematiker 26.10. 08:11;  Architekt 08:10), Grundlage
`KorpusRev2/Horistes_Symmetriebruch_als_Umkehr.md` (07:36) und `KorpusRev2/Speculum_Symmetriebruch_als_Umkehr.md` (07:40):  das Korollar, die
dritte Option, der Kopf.  Konsumiert `ErzeugteKetteProbe`
(`Tower`, `stand`, `erzeugt`, `erzeugt_lokal`, `inFaser`, `regelNach`, `tower_ext`, `fwL`, `forkWidth_fwL`, `p01`) und `Kenogram` (`IsRGS`, `isRGSAux`,
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
korollar_invariant    FOLGERUNG (dünn)   K1 (Curies Prinzip, Horistes):  ist τ·c = c auf den Werten, so ist erzeugt c n τ-fest, für jedes n —
                                         der Wechsel Regel → Kette kann τ nicht brechen
eich_dritte_option    EICHUNG            K2:  an [0,1] die Regel `dritte` (1 an `[0]`, 2 an [0,1], sonst 0):  τ-invariant, erzeugt [0,1,2], und
                                         [0,1,2] ist τ-fest — gewählt wird, die Symmetrie bleibt;  die Kette läuft durch den neuen Wert
gegen_dritte_option   EICHUNG (decide)   Gegenprobe zu K2:  mit 0 statt 2 an [0,1] wählt c dort 0, τ·c dort 1 — nicht τ-invariant
```

**Die Wirkung auf Regeln** (`wirk`, im Text τ·c):  an x wählt τ·c, was c an τ x wählt — an r selbst durch `zeichenTausch` zurückgeholt,
sonst unverändert.  Der Grund steht als Satz da (`tausch_snoc`):  τ (s ++ [j]) = τ s ++ [j], ausser an s = r, wo das angehängte Zeichen
selbst getauscht wird.  `tauschT` ist τ auf dem Turm.

**τ ist KEINE Umbenennung der Werte:**  [0,1,0] ↦ [0,1,1] ändert das Muster ABA ↦ ABB.  `ErzeugteKetteProbe.umtausch_identitaet` (G-2)
und `gabelung_nicht_vertauschbar` (G-3), beide über Umbenennungen, bleiben richtig und unberührt.  τ ist eine Symmetrie der LAGE (des
Baums der Wahlmöglichkeiten), nicht der Kenogramme.

## FESTLEGUNG „symmetrisch"

Mathematiker 26.10., Lesart (iv):  Tausch zweier Glieder gleicher Sorte, im selben Wechsel mit der Umkehr der Ordnung auf
Relator/Relatum — A20-4 (Definitionen §20, Fassung 25.10.).  **Diese Sonde liefert den TAUSCH, nicht die UMKEHR** — und nach
`korollar_invariant` kann sie die Umkehr auch nicht liefern;  die Umkehr von S. 23 ist eine der Deutung.

## LESART

Buridans Lage — **mit dem Neuen**:  zwei als Kenogramme verschiedene, als Alternativen gleiche Fortsetzungen (C&V S. 15 „two bundles of
hay of absolutely equal attractiveness" — Halbsatz Textschicht, Seite von Hermeneutes am Bild gelesen).  ZUORDNUNG, ungeprüft.  An der
Gabelung gibt es eine dritte Option, die Buridans Esel nicht hat;  am Turm ist die Notwendigkeit der Wahl bewiesen, die des Bruchs nicht
(Horistes §3).  An einer symmetrischen Gabelung fallen zusammen:  τ, die Notwendigkeit der Wahl ([T66], [T30]), der Verlust daneben (SA1
mit Zusatz).  **Die Wahl bricht τ genau dann, wenn die Kette durch eine der zwei gleichwertigen Fortsetzungen läuft** (`eich_bruch`);
wählt die Regel den neuen Wert, bleibt τ (`eich_dritte_option`).  Der Wechsel selbst bricht τ nie (`korollar_invariant`).

**Symmetriebruch und Umkehr** (beantwortet:  Horistes, Speculum 26.10.):  Der Symmetriebruch hat die Gestalt von C&V S. 16 —
*„establishes an ordered relation between itself and the chosen object"* —, **Stiftung** einer Ordnung aus der neutralen Lage ([T27]);
**nicht** die *Umkehr* von S. 23 *„suffers a reversal"*.  Die Umkehr von S. 23 liegt zwischen den zwei Programmen (S. 17) und ist im
Algorithmus die **Umkehr der Deutung** von Relator und Relatum (S. 23:  *„permits us to reverse this interpretation"* — Erkenntniskalkül /
Willenskalkül).  Eine Deutung ist kein Term.  — LESART am Wortlaut (Speculum SB1, SB2);  Ortswert des Korollars:  am Turm wird kein
natürlich gebauter Satz „der Tausch bedingt die Umkehr" tragen (Horistes §1).

**τ und Günthers Umtausch** (Speculum SB4):  τ ist ein Kandidat für den **projizierten** Umtausch *„between two objects"* (C&V S. 16,
[T64];  S. 17 *„material content"*);  [T65] trifft τ nicht (τ ist keine Wertbelegung).  Ab max r ≥ 2 k-gliedrig:  UNSER, nach [T56].
— ZUORDNUNG mit Wortlautstütze;  die verbotene Kurzform „τ ist Günthers symmetrischer Umtausch" bleibt.

## ZUSAMMENSCHAU (nur Hinweis;  Speculum SB5)

Zwei Auflösungen der symmetrischen Gabelung:  eine Wiederholung wählen (bricht τ;  C&V S. 16 „establishes … relegating the other
alternate") / den neuen Wert wählen (lässt τ;  HKN „Verwerfung der Totalalternative", „Rejektionswert", „logischer Index des ontologisch
Neuen").  **Gegenstand verschieden** (HKN:  ein Wert an der schwachen Stelle einer Wertetafel;  hier:  eine Fortsetzung im Baum).  Die
HKN-Stelle ist bisher nur Textschicht (Bildlesung beantragt).  Verboten:  „der neue Wert ist ein Rejektionswert".

## BEOBACHTUNG (kein Satz)

Symmetrische Gabelungen beginnen auf Stufe 2 (an [0,1]), der Verlust daneben ebenfalls — nicht aus demselben Grund:  auf einem Pfad durch
[0,0] gibt es auf Stufe 2 Verlust daneben, aber keine symmetrische Gabelung (`eich_paare`, `VerlustDanebenKuenftigProbe.daneben_iff`).

## NICHT

Kein Träger für §20;  nicht „A20-4 erfüllt" (S3 ist eine Kommutation, keine Umkehrung);  kein Text in Rev11.

**Verbotene Kurzformen:**  „τ ist Günthers symmetrischer Umtausch";  „Buridan formalisiert";  „A20-4 erfüllt";  „die Wahl kehrt die
Ordnung um" (statt:  stiftet eine Ordnung, C&V S. 16 — Lesart).  Ergänzt (Horistes §4):  „die Wahl bricht die Symmetrie" ohne „durch eines
der gleichwertigen Glieder";  „der Wechsel bricht die Symmetrie";  „implies a reversal" / „Umkehr" für den Symmetriebruch;  „Buridans Esel
formalisiert";  „Symmetrie der Kenogramme".

## Bauweise

Der RGS-Lauf über eine Verkettung (`isRGSAux_append`) trägt S1:  hinter einem nichtleeren r hängt die Gültigkeit von `r ++ k :: t` für
k ≤ max r nicht von k ab (`isRGS_wiederholung`).  Die Konjugation geht unmittelbar über `Choice` (abhängiger Untertyp);  eine Fassung über
`List ℕ`-Regeln war nicht nötig.  Fallunterscheidungen über `Nat.decEq` und `decEq` auf `List ℕ`;  `omega` nur an Zahlzielen.
Hilfssätze:  `foldr_max_start`, `max_append`, `tausch_form`, `tausch_sonst`, `form_oder_fest`, `zeichenTausch_zeichenTausch`,
`zeichenTausch_le`, `tausch_tausch`, `tausch_length`, `tausch_rgs`, `praefix_fall`, `tausch_praefix_mp`, `fwL_ne`, `tausch_nil`, `tausch_r`,
`max_tausch`, `tauschT_tauschT`, `tausch_eq_r`, `stand_wirk`;  im Nachzug `dritteWert_zul`, `tausch01_kurz` (τ an [0,1] hält jede Kette
der Länge ≤ 2 fest), `dritteWert_tausch`, `hk01`, `hk01'`.  `korollar_invariant` braucht keinen neuen Hilfssatz:  dass `erzeugt` nur von
den Werten der Wahl abhängt, ist `ErzeugteKetteProbe.erzeugt_lokal`.  Teil (c) von `eich_dritte_option` ist über `korollar_invariant`
bewiesen, nicht nachgerechnet — die erste Instanz des Korollars.
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

/-- **die Wahl durch eine der zwei gleichwertigen Fortsetzungen bricht τ:**  die Regel nach [0,1,0] und ihr τ-Bild (τ an [0,1], Wiederholungen 0 und 1) erzeugen [0,1,0] und
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

/-! ## Nachzug 26.10.:  das Korollar und die dritte Option -/

/-- **K1 (Curies Prinzip):**  eine τ-invariante Regel erzeugt eine τ-feste Kette — der Wechsel Regel → Kette kann τ nicht brechen -/
theorem korollar_invariant (r : List ℕ) (hr : r ≠ []) (k k' : ℕ) (hk : k ≤ r.foldr max 0) (hk' : k' ≤ r.foldr max 0)
    (c : Choice) (h : ∀ x, (wirk r hr k k' hk hk' c x).1 = (c x).1) :
    ∀ n, tausch r k k' (erzeugt c n) = erzeugt c n := by
  intro n
  rw [← tausch_aequivariant r hr k k' hk hk' c n]
  exact erzeugt_lokal _ _ n fun x _ => h x

/-- die Werte der dritten Option:  1 an `[0]`, 2 an [0,1], sonst 0 -/
def dritteWert (l : List ℕ) : ℕ := if l = [0] then 1 else if l = [0, 1] then 2 else 0

theorem dritteWert_zul (l : List ℕ) : dritteWert l ≤ l.foldr max 0 + 1 ∧ (l = [] → dritteWert l = 0) := by
  unfold dritteWert
  rcases decEq l [0] with h1 | h1
  · rw [if_neg h1]
    rcases decEq l [0, 1] with h2 | h2
    · rw [if_neg h2]; exact ⟨Nat.zero_le _, fun _ => rfl⟩
    · rw [if_pos h2, h2]; decide
  · rw [if_pos h1, h1]; decide

/-- **die dritte Option an [0,1]:**  die Regel wählt an `[0]` die 1 und an [0,1] den neuen Wert 2 -/
def dritte : Choice := fun x => ⟨dritteWert x.2.val, dritteWert_zul x.2.val⟩

theorem tausch01_kurz (s l : List ℕ) (hl : l.length ≤ 2) : tausch [0, 1] 0 1 s = l ↔ s = l := by
  have hf : tausch [0, 1] 0 1 l = l := tausch_sonst _ _ _ l fun a t e => by
    have := congrArg List.length e; simp only [List.length_append, List.length_cons] at this; omega
  constructor
  · intro h; have := congrArg (tausch [0, 1] 0 1) h; rwa [tausch_tausch, hf] at this
  · intro h; rw [h, hf]

theorem dritteWert_tausch (s : List ℕ) : dritteWert (tausch [0, 1] 0 1 s) = dritteWert s := by
  unfold dritteWert
  rcases decEq s [0] with h1 | h1
  · rw [if_neg h1, if_neg (fun e => h1 ((tausch01_kurz s [0] (by decide)).mp e))]
    rcases decEq s [0, 1] with h2 | h2
    · rw [if_neg h2, if_neg (fun e => h2 ((tausch01_kurz s [0, 1] (by decide)).mp e))]
    · rw [if_pos h2, if_pos ((tausch01_kurz s [0, 1] (by decide)).mpr h2)]
  · rw [if_pos h1, if_pos ((tausch01_kurz s [0] (by decide)).mpr h1)]

theorem hk01 : (0 : ℕ) ≤ [0, 1].foldr max 0 := by decide
theorem hk01' : (1 : ℕ) ≤ [0, 1].foldr max 0 := by decide

/-- **K2:**  an der symmetrischen Gabelung [0,1] wird gewählt, und die Symmetrie bleibt — die Kette läuft durch den neuen Wert -/
theorem eich_dritte_option :
    (∀ x, (wirk [0, 1] (List.cons_ne_nil 0 [1]) 0 1 hk01 hk01' dritte x).1 = (dritte x).1) ∧
    erzeugt dritte 3 = [0, 1, 2] ∧ tausch [0, 1] 0 1 [0, 1, 2] = [0, 1, 2] := by
  have ha : ∀ x, (wirk [0, 1] (List.cons_ne_nil 0 [1]) 0 1 hk01 hk01' dritte x).1 = (dritte x).1 := by
    intro x
    show (if x.2.val = [0, 1] then zeichenTausch 0 1 (dritteWert (tausch [0, 1] 0 1 x.2.val))
      else dritteWert (tausch [0, 1] 0 1 x.2.val)) = dritteWert x.2.val
    rw [dritteWert_tausch]
    rcases decEq x.2.val [0, 1] with h | h
    · rw [if_neg h]
    · rw [if_pos h, h]; decide
  have hb : erzeugt dritte 3 = [0, 1, 2] := by decide
  refine ⟨ha, hb, ?_⟩
  have := korollar_invariant [0, 1] (List.cons_ne_nil 0 [1]) 0 1 hk01 hk01' dritte ha 3
  rwa [hb] at this

/-- die Regel der Gegenprobe:  1 an `[0]`, sonst 0 — an [0,1] die Wiederholung 0 statt des neuen Werts -/
def gegenDritte : Choice := fun x =>
  if h : x.2.val = [0] then ⟨1, by rw [h]; decide, by rw [h]; intro e; exact absurd e (by decide)⟩
  else ⟨0, Nat.zero_le _, fun _ => rfl⟩

/-- **Gegenprobe zu K2:**  mit 0 statt 2 an [0,1] ist die Regel nicht τ-invariant — an [0,1] wählt τ·c die 1 -/
theorem gegen_dritte_option :
    (gegenDritte p01).1 = 0 ∧ (wirk [0, 1] (List.cons_ne_nil 0 [1]) 0 1 hk01 hk01' gegenDritte p01).1 = 1 := by
  decide

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

/-- info: 'Reformulation.Proemial.SymmetrieGabelungProbe.korollar_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.SymmetrieGabelungProbe.korollar_invariant

/-- info: 'Reformulation.Proemial.SymmetrieGabelungProbe.dritteWert_zul' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Proemial.SymmetrieGabelungProbe.dritteWert_zul

/-- info: 'Reformulation.Proemial.SymmetrieGabelungProbe.tausch01_kurz' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.SymmetrieGabelungProbe.tausch01_kurz

/-- info: 'Reformulation.Proemial.SymmetrieGabelungProbe.dritteWert_tausch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.SymmetrieGabelungProbe.dritteWert_tausch

/-- info: 'Reformulation.Proemial.SymmetrieGabelungProbe.hk01' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Proemial.SymmetrieGabelungProbe.hk01

/-- info: 'Reformulation.Proemial.SymmetrieGabelungProbe.hk01'' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Proemial.SymmetrieGabelungProbe.hk01'

/-- info: 'Reformulation.Proemial.SymmetrieGabelungProbe.eich_dritte_option' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.SymmetrieGabelungProbe.eich_dritte_option

/-- info: 'Reformulation.Proemial.SymmetrieGabelungProbe.gegen_dritte_option' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.SymmetrieGabelungProbe.gegen_dritte_option
