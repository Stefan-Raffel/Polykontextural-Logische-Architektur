import Reformulation.Proemial.SymmetrieGabelungProbe   -- über ErzeugteKetteProbe:  erzeugt, inFaser;  über KenogramForkProbe:  Fork, Choice

/-!
# Proemial.RichtungProgrammProbe — Richtung statt Zuweisung:  Abstieg, Aufstieg, und was davon nur Baum ist

STANDALONE, NICHT im Aggregat;  Target `Probes`.  AxiomGate unberührt.  Sonde nach
`KorpusRev2/Prompt_Instanz_Richtung_Programm_Sonde.md` (Mathematiker, 26.10.2026 09:32;  Architekt 09:30 „Schreibe eine Sonde für die
Instanz, um der Fragestellung mehr Substanz zu verleihen.").  Anlass:  `KorpusRev2/Speculum_Rueckfrage_Anwendung_Zuweisung.md` (09:25,
SR2/SR3:  am Turm hängt das Programm an der RICHTUNG, nicht an der ZUWEISUNG).  Die Sonde misst die zwei Einwände des Mathematikers:
**E1 (Konverse)** — Abstieg und Aufstieg sind die zwei Leserichtungen EINER Kante;  **E2 (Generizität)** — „Abstieg bestimmt, Aufstieg
wählt" gilt in jedem verzweigten Baum.  Sie beweist nicht, dass Speculum recht hat.
Konsumiert `Kenogram` (`descent`, `extend`, `descent_extend`, `rgs_take_mem`, `isRGS_head`, `isRGSAux_concat`, `foldl_max_eq`),
`KenogramForkProbe` (`Fork`, `forkWidth`, `forkWidth_eq`, `forkWidth_of_nil`, `Choice`, `ascentBy`), `ErzeugteKetteProbe` (`erzeugt`,
`erzeugt_praefix`, `erzeugt_length`, `inFaser`, `tower_ext`);  ändert nichts davon.  Keine Bezeichner für Erkennen/Wollen:  die
Lean-Namen sind neutral, die Zuordnung zu Günther steht nur hier.

## Zählung

```text
Länge n der Kette r  =  Index des Turmpunkts ⟨n, r⟩  =  Stelle, an der die Regel der Relator-Stufe n wählt
SA1:  Stufe k  =  W k → RGS (k + 1)  —  die Wahl an Punkten der Länge k erzeugt Ketten der Länge k + 1
daneben_iff (Kettenlänge ≥ 3)  =  Ketten nach zwei Wahlen  =  Relatum der Stufe 2
```

## WAS

```text
Teil A — eine Kante, zwei Lesungen
kante_konvers           UMBENENNUNG        A0:  aufstieg r s ↔ kante r s (descent s = r) — die Aufstiegsrelation ist die Konverse der
                                           Abstiegsrelation.  E1, festgehalten.  (Der Beweis braucht `zerlege`, die Stufe bleibt:  die
                                           Aussage ist die Konverse, nicht mehr.)
schwellenleiter         ZUSAMMENSTELLUNG   A1:  (a) Länge 0:  genau eine Fortsetzung;  (b) Länge ≥ 1:  mindestens zwei;  (c) es gibt ein r
                                           der Länge n mit zwei verschiedenen Wiederholungen ⟺ n ≥ 2;  (d) an jedem nichtleeren r liegt
                                           genau eine Fortsetzung oberhalb der Wiederholungen, M + 1
abstieg_nach_aufstieg   INSTANZIIERUNG     A2 (i):  descent ∘ ascentBy c = id, für jede Wahlregel (`descent_extend`)
wiederherstellung       FOLGERUNG (dünn)   A2 (ii):  über nichtleerem r stellt der Aufstieg nach dem Abstieg genau die Fortsetzung wieder her,
                                           die c an r wählt;  von forkWidth r = M + 2 genau eine, die übrigen M + 1 nicht
Teil B — Rückblick
rueckblick              HEBUNG             B1:  (erzeugt c N).take k = erzeugt c k für k ≤ N (`erzeugt_praefix` als Gleichung)
rueckblick_faser        FOLGERUNG (dünn)   B2:  c' in der Faser über erzeugt c N  →  erzeugt c' k = erzeugt c k für alle k ≤ N
Teil C — Gegenmodelle FB (freier Binärbaum, List Bool) und FN (freier ℕ-Baum, List ℕ)
genau_ein_neuer         FOLGERUNG          C1:  über nichtleerer RGS r ist unter den Fortsetzungen genau EINE kein Glied von r:  M + 1
konvers_frei            FOLGERUNG (dünn)   A0 und A2 (i) in jedem freien Baum (jeder Typ α, also FB und FN)
rueckblick_frei         FOLGERUNG (dünn)   B1 in jedem freien Baum
fb_wurzel, fn_weite     EICHUNG            A1a fällt in FB (zwei Fortsetzungen an der Wurzel) und FN (unendlich viele, injektiv)
fb_kein_neuer           EICHUNG            C1 fällt in FB:  an [false, true] gibt es keinen neuen Wert
fn_unendlich_neu        FOLGERUNG (dünn)   C1 fällt in FN:  an jeder Kette beliebig grosse neue Werte
fb_wiederherstellung    EICHUNG (decide)   A2 (ii) in FB:  eine nicht wiederhergestellt, konstant
fn_wiederherstellung    FOLGERUNG (dünn)   A2 (ii) in FN:  unendlich viele nicht wiederhergestellt
Eichung und Muss-Fälle
eich_richtung           EICHUNG (decide)   an `[0]`, [0,1], [0,1,0,2]:  M + 1 = 1, 2, 3 nicht wiederhergestellt;  der neue Wert 1, 2, 3
gegen_zahl_wiederherstellung  EICHUNG     „M + 2 nicht wiederhergestellt" fällt an `[0]`
gegen_ein_neuer         EICHUNG (decide)   „zwei neue Werte" fällt an [0,1];  ohne RGS fällt C1:  über [0,2] zwei Werte ausserhalb, 1 und 3
gegen_schwelle_eins     EICHUNG            A1 (c) mit „n ≥ 1" fällt an n = 1
```

Hilfssätze:  `snoc_schranke` (das letzte Zeichen einer RGS ist über ihrem Rumpf zulässig), `mem_le_max`, `fork_eq_range`,
`filter_range_eq`, `filter_range_ne`, `zerlege` (jede Kette der Länge n + 1 ist die Fortsetzung ihres Abstiegs), `rgs_kurz_max`,
`isRGSAux_nullen`, `erzeugtF_length`.  Definitionen:  `kante`, `aufstieg`, `zeuge01`, `erzeugtF`, `q0`, `q01`, `q0102`.

## Die Tafel aus Teil C — gemessen

```text
                         Turm (RGS)                          FB (List Bool)                       FN (List ℕ)
A0  Konverse             Satz:  kante_konvers                Satz:  konvers_frei                  Satz:  konvers_frei
A1a Wurzel               Satz:  1 Fortsetzung (a)            Gegenbsp.:  fb_wurzel, 2             Gegenbsp.:  fn_weite, unendlich
A1b Wahl ab              Satz:  Länge ≥ 1 (b)                ab Länge 0 (fb_wurzel)               ab Länge 0 (fn_weite)
A1c Option ausserhalb    Satz:  GENAU EINE (d, C1)           Gegenbsp.:  KEINE an [false,true]    Satz:  beliebig grosse,
    der Wiederholungen                                       (fb_kein_neuer)                      unendlich viele (fn_unendlich_neu)
A2 (i)                   Satz:  abstieg_nach_aufstieg        Satz:  konvers_frei (→)              Satz:  konvers_frei (→)
A2 (ii) Zahl             Satz:  M + 1, präfixabhängig        Satz:  1, konstant                   Satz:  unendlich
                         (wiederherstellung, eich_richtung)  (fb_wiederherstellung)               (fn_wiederherstellung)
B1                       Satz:  rueckblick                   Satz:  rueckblick_frei               Satz:  rueckblick_frei
B2                       Satz:  rueckblick_faser             nicht gebaut                         nicht gebaut
```

**Befund zu E1 und E2.**  Generisch, also nur Baum, sind A0, A1b, A2 (i) und B1:  sie gelten in FB und FN wörtlich.  „Der Abstieg
bestimmt, der Aufstieg wählt" ist darum keine Eigenschaft des Turms.  E2 bestätigt.  **Turmeigen** sind drei Zahlen:  die Weite 1 an
der Wurzel (A1a), **genau ein** Wert ausserhalb der Wiederholungen (A1c, C1), und die präfixabhängige Zahl M + 1 der nicht
wiederhergestellten Fortsetzungen (A2 ii).  FB hat an einer Kette, in der beide Werte vorkamen, keinen neuen Wert;  FN hat unendlich
viele.  Der Turm hat genau einen, und das folgt aus der Dichtheit der RGS (`rgs_take_mem`).  Was die RICHTUNG am Turm trägt, ist
damit nicht das Richtungspaar selbst (E1:  Konverse), sondern die Zählstruktur der Gabelung.

## Die Schwellen, in einer Zählung (Stufe k = Länge des Punkts, an dem gewählt wird)

```text
Stufe 0    keine Wahl                                schwellenleiter (a), forkWidth_of_nil
Stufe 1    Wahl, umkehrbar                           schwellenleiter (b);  einsortig_moeglich_eins, stufe_zwei_injektiv
           (SA1 mit Zusatz:  „noch nicht proemial")  an `[0]`:  eine Wiederholung (0), ein neuer Wert (1) — noch keine Alternative von Wiederholungen
Stufe 2    Verlust daneben                           daneben_iff (Kettenlänge ≥ 3 = Relatum der Stufe 2), für JEDE Kette
           ab hier zwei Wiederholungen (n ≥ 2),      schwellenleiter (c), für EINIGE Punkte der Länge 2 ([0,1] ja, [0,0] nein)
           mit genau einer Option ausserhalb         schwellenleiter (d), genau_ein_neuer
```

**Die drei Schwellen fallen auf dieselben Stufen;  keine ist verschoben.**  Aber mit verschiedenem Quantor:  der Verlust daneben trifft
ab Stufe 2 **jede** Kette, die Alternative von Wiederholungen nur **einige** Punkte.  Das ist die Beobachtung aus
`SymmetrieGabelungProbe` (Pfad durch [0,0]), jetzt mit den Quantoren benannt.  Kein Satz verbindet die zwei Schwellen.

## ZUORDNUNG (je mit Quellenlesung)

- **Richtung als Programm** (Speculum SR3, 09:25):  der Abstieg als die Seite, die *„has not to add anything"* (C&V S. 12), der
  Aufstieg durch Wahl als *„supply this order by making a choice"* (C&V S. 16).  Gelesen:  Speculum, `KorpusRev1/c_and_v.pdf`,
  **Textschicht**;  Bild offen (Hermeneutes).  Die Sonde zeigt:  am Turm ist das Richtungspaar die Konverse einer Kante
  (`kante_konvers`), und die Einseitigkeit (der Abstieg ist Funktion, der Aufstieg nicht) gilt in jedem verzweigten Baum.
- **„exactly inverse"** (C&V S. 10, Textschicht, Speculum;  Bild offen) — **ungeprüft**:  am Turm sind Abstieg und Aufstieg nur
  einseitig invers (`abstieg_nach_aufstieg`:  Retraktion;  `wiederherstellung`:  kein Isomorphismus).  Das wäre die Turmgestalt von
  „Adjunktion, nicht Äquivalenz" in `AlphaGamma.ProemialAdjunction` (E&W S. 26–27).  Nur Vergleich;  die Sonde berührt AlphaGamma nicht.
  Die allgemeine Galois-Verbindung Bild ⊣ Urbild ist NICHT gebaut (Option O2 der Notiz `Optionen_A20-2_A20-4_Impl.md`, 20.9.:  sie gilt für jede Abbildung, ein Quantorentausch).
  Turmeigen ist allein die Zahl M + 1.
- **Rückblick** (B1) als „Erkenntnis = Rückblick auf Gewähltes" — LESART, zur Prüfung an Horistes freigegeben.  Gegen C&V S. 12
  (Textschicht, Speculum):  *„images … already preformed in the environment by the objects themselves … projected into the cognitive
  system"* trifft B1 **nur dann**, wenn man die erzeugte Kette als „environment" liest — eine eigene Lesart.
- **C1 und das Neue** — ungeprüft:  der kenogrammatische Grund dafür, dass das Neue am Turm EINES ist;  neue Werte sind bis auf
  Umbenennung gleich (`RelabelInvariance`).  Bezug zur Setzung „Kontextnegation" (Prompt an Custos 09:22;
  `KorpusRev2/Notiz_Kontextnegation_bei_Guenther_Impl.md`):  am Turm gibt es an jedem Punkt mit echter Wiederholungsalternative genau
  einen Ort, an dem die Alternative als ganze verlassen wird.  Verweis, nicht Satz:  `HeteroreferenzProbe.rejection_not_sufficient`.

## ZUSAMMENSCHAU (nur nennen, nicht gebaut)

Definitionen §8 führt ab m = 4 Werten m − 2 mögliche Rejektionswerte;  kenogrammatisch fallen sie an einer Gabelung zu EINEM neuen
Wert zusammen (C1).  Ob das zu §8 passt oder ihm widerspricht, ist eine Frage an Speculum, nicht an die Sonde.  Vergleich im Haus:
`TimeMeasure` Kopf K-M4 (E&W S. 21 kognitiv ↦ Umtausch, volitiv ↦ Ordnung, gegen *Als Wille* S. 3 — „genannt, nicht entschieden").

## NICHT

Keine Deutung als Term, kein Deutungsparameter;  keine Entscheidung, welches Programm welche Richtung ist;  `ProemialAdjunction` nicht
berührt;  kein „A20-4 erfüllt", kein „A20-6 erfüllt", kein §20-Träger;  kein Text in Rev11.

**Verbotene Kurzformen:**  „der Turm verwirft" (erlaubt:  „an r liegt genau eine Option ausserhalb der Alternative");  „der Abstieg ist
das Erkennen";  „der Aufstieg ist der Wille" (beides ZUORDNUNG, ungeprüft);  „Abstieg und Aufstieg sind invers" (nur einseitig);
„Richtung trägt das Programm, Turm-Befund" (generisch, siehe Tafel).

## Bauweise

`Fork r` über nichtleerem r ist der ganze Bereich 0 … M + 1 (`fork_eq_range`);  die Zählungen laufen über `filter_range_eq` und
`filter_range_ne`, ohne `Finset`.  **Ein Profilbefund beim Bau von C1:**  dieselbe Zeile mit `omega` im Kontext der Implikation
`k ≤ M → k ∈ r` (aus `rgs_take_mem`) zog `Classical.choice` (gefunden über `getUsedConstants` / `collectAxioms`:  ein `_proof_`-Term
mit `Classical.propDecidable`);  die Ungleichung VOR der Implikation berechnet, ist C1 `[propext, Quot.sound]` — Fallstrick 7,
Gestalt „Implikation als Hypothese", ein weiterer Beleg.
Kein `sorry`, kein `Classical.choice`, kein `native_decide`, kein True-Feld.
-/

namespace Reformulation.Proemial.RichtungProgrammProbe

open Reformulation.Kenogram
open Reformulation.Proemial.TowerAsymmetryProbe (Tower)
open Reformulation.Proemial.KenogramForkProbe (Choice ascentBy Fork forkWidth forkWidth_eq forkWidth_of_nil)
open Reformulation.Proemial.ErzeugteKetteProbe (erzeugt erzeugt_praefix erzeugt_length inFaser tower_ext)
open Reformulation.Proemial.SymmetrieGabelungProbe (paar_iff)

/-! ## Werkzeug -/

/-- das letzte Zeichen einer RGS ist zulässig über ihrem Rumpf -/
theorem snoc_schranke (l : List ℕ) (v : ℕ) (h : IsRGS (l ++ [v])) :
    v ≤ l.foldr max 0 + 1 ∧ (l = [] → v = 0) := by
  match l, h with
  | [], h =>
    have h0 : decide (v = 0) = true := by
      unfold IsRGS at h
      simp only [List.nil_append, isRGSAux, Bool.and_eq_true] at h
      exact h.1
    have : v = 0 := of_decide_eq_true h0
    exact ⟨by rw [this]; exact Nat.zero_le _, fun _ => this⟩
  | a :: t, h =>
    unfold IsRGS at h
    rw [show (a :: t) ++ [v] = a :: (t ++ [v]) from rfl] at h
    simp only [isRGSAux, isRGSAux_concat, Bool.and_eq_true, decide_eq_true_eq] at h
    refine ⟨?_, fun e => absurd e (List.cons_ne_nil a t)⟩
    have := h.2.2
    rw [foldl_max_eq] at this
    rw [List.foldr_cons]; exact this

/-- jedes Glied liegt unter dem Maximum -/
theorem mem_le_max : ∀ (l : List ℕ) (x : ℕ), x ∈ l → x ≤ l.foldr max 0
  | [], _, h => absurd h (List.not_mem_nil)
  | a :: t, x, h => by
    rw [List.foldr_cons]
    rcases List.mem_cons.mp h with e | e
    · rw [e]; exact Nat.le_max_left _ _
    · exact Nat.le_trans (mem_le_max t x e) (Nat.le_max_right _ _)

/-- über einer nichtleeren Kette ist die Gabelung der ganze Bereich 0 … M + 1 -/
theorem fork_eq_range {n : ℕ} (r : RGS n) (hne : r.val ≠ []) : Fork r = List.range (r.val.foldr max 0 + 2) :=
  List.filter_eq_self.mpr fun _ _ => decide_eq_true (fun h => absurd h hne)

theorem filter_range_eq (j : ℕ) : ∀ m, (List.range m).filter (fun k => decide (k = j)) = if j < m then [j] else []
  | 0 => by rw [if_neg (Nat.not_lt_zero j)]; rfl
  | m + 1 => by
    rw [List.range_succ, List.filter_append, filter_range_eq j m]
    rcases Nat.lt_trichotomy j m with h | h | h
    · rw [if_pos h, if_pos (Nat.lt_succ_of_lt h)]
      have : decide (m = j) = false := decide_eq_false (fun e => Nat.lt_irrefl _ (e ▸ h))
      simp only [List.filter_cons, List.filter_nil, this]; rfl
    · subst h
      rw [if_neg (Nat.lt_irrefl _), if_pos (Nat.lt_succ_self _)]
      simp only [List.filter_cons, List.filter_nil]; rfl
    · rw [if_neg (fun e => Nat.lt_asymm h e), if_neg (fun e => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h (Nat.le_of_lt_succ e)))]
      have : decide (m = j) = false := decide_eq_false (fun e => Nat.lt_irrefl _ (e ▸ h))
      simp only [List.filter_cons, List.filter_nil, this]; rfl

theorem filter_range_ne (j : ℕ) : ∀ m, j < m → ((List.range m).filter (fun k => decide (k ≠ j))).length = m - 1
  | 0, h => absurd h (Nat.not_lt_zero j)
  | m + 1, h => by
    rw [List.range_succ, List.filter_append, List.length_append, List.filter_cons, List.filter_nil]
    rcases Nat.lt_or_ge j m with h' | h'
    · rw [filter_range_ne j m h', if_pos (decide_eq_true (show m ≠ j from fun e => Nat.lt_irrefl _ (e ▸ h')))]
      show m - 1 + 1 = m + 1 - 1
      omega
    · have hj : j = m := by omega
      subst hj
      have h0 : (List.range j).filter (fun k => decide (k ≠ j)) = List.range j :=
        List.filter_eq_self.mpr fun k hk => decide_eq_true (show k ≠ j from fun e => Nat.lt_irrefl _ (e ▸ List.mem_range.mp hk))
      rw [h0, List.length_range, if_neg (fun e => (of_decide_eq_true e) rfl)]
      show j + 0 = j + 1 - 1
      omega

/-! ## Teil A — eine Kante, zwei Lesungen -/

/-- **A0, die Kante:**  s liegt über r -/
def kante {n : ℕ} (r : RGS n) (s : RGS (n + 1)) : Prop := descent s = r

/-- **A0, die Aufstiegslesung:**  s entsteht aus r durch eine zulässige Fortsetzung -/
def aufstieg {n : ℕ} (r : RGS n) (s : RGS (n + 1)) : Prop :=
  ∃ (k : ℕ) (hk : k ≤ r.val.foldr max 0 + 1) (h0 : r.val = [] → k = 0), extend r k hk h0 = s

/-- jede Kette der Länge n + 1 ist die Fortsetzung ihres Abstiegs -/
theorem zerlege {n : ℕ} (s : RGS (n + 1)) :
    ∃ (k : ℕ) (hk : k ≤ (descent s).val.foldr max 0 + 1) (h0 : (descent s).val = [] → k = 0), extend (descent s) k hk h0 = s := by
  have hne : s.val ≠ [] := fun e => by have := s.property.1; rw [e] at this; exact Nat.succ_ne_zero n this.symm
  have hs : s.val = s.val.dropLast ++ [s.val.getLast hne] := (List.dropLast_append_getLast hne).symm
  have hb := snoc_schranke s.val.dropLast (s.val.getLast hne) (hs ▸ s.property.2)
  exact ⟨s.val.getLast hne, hb.1, hb.2, Subtype.ext hs.symm⟩

/-- **A0:**  die Aufstiegsrelation ist die Konverse der Abstiegsrelation — UMBENENNUNG -/
theorem kante_konvers {n : ℕ} (r : RGS n) (s : RGS (n + 1)) : aufstieg r s ↔ kante r s := by
  constructor
  · rintro ⟨k, hk, h0, rfl⟩; exact descent_extend r k hk h0
  · intro h
    unfold kante at h; subst h
    exact zerlege s

theorem rgs_kurz_max {n : ℕ} (r : RGS n) (hn : n ≤ 1) : r.val.foldr max 0 = 0 := by
  have hl := r.property.1
  match h : r.val, hl with
  | [], _ => rfl
  | [a], _ =>
    have := isRGS_head r.property.2 (by rw [h]; exact Nat.zero_lt_succ 0)
    simp only [h] at this
    show max a 0 = 0
    rw [show a = 0 from this]; rfl
  | _ :: _ :: _, hl => simp only [List.length_cons] at hl; omega

theorem isRGSAux_nullen (m : ℕ) : ∀ j, isRGSAux m true (List.replicate j 0) = true
  | 0 => rfl
  | j + 1 => by
    show (decide (0 ≤ m + 1) && isRGSAux (max m 0) true (List.replicate j 0)) = true
    rw [Nat.max_zero, isRGSAux_nullen m j]; rfl

/-- der Zeuge für A1(c):  0, 1, dann Nullen -/
def zeuge01 (j : ℕ) : RGS (j + 2) :=
  ⟨0 :: 1 :: List.replicate j 0, by simp only [List.length_cons, List.length_replicate],
    by show (decide (0 = 0) && isRGSAux 0 true (1 :: List.replicate j 0)) = true
       show (true && (decide (1 ≤ 0 + 1) && isRGSAux (max 0 1) true (List.replicate j 0))) = true
       rw [isRGSAux_nullen]; rfl⟩

/-- **A1, die Schwellenleiter** an einem Punkt der Länge n:
    (a) n = 0:  genau eine Fortsetzung;  (b) n ≥ 1:  mindestens zwei;
    (c) es gibt ein r der Länge n mit zwei verschiedenen Wiederholungen  ⟺  n ≥ 2;
        an jedem nichtleeren r liegt genau eine Fortsetzung oberhalb der Wiederholungen, M + 1 -/
theorem schwellenleiter :
    (∀ r : RGS 0, forkWidth r = 1) ∧
    (∀ n (r : RGS n), 1 ≤ n → 2 ≤ forkWidth r) ∧
    (∀ n, (∃ r : RGS n, ∃ k k', k ≠ k' ∧ k ≤ r.val.foldr max 0 ∧ k' ≤ r.val.foldr max 0) ↔ 2 ≤ n) ∧
    (∀ n (r : RGS n), r.val ≠ [] → (Fork r).filter (fun k => decide (r.val.foldr max 0 < k)) = [r.val.foldr max 0 + 1]) := by
  refine ⟨fun r => forkWidth_of_nil r (List.length_eq_zero_iff.mp r.property.1), fun n r hn => ?_, fun n => ?_, fun n r hne => ?_⟩
  · have hne : r.val ≠ [] := fun e => by have := r.property.1; rw [e] at this; simp only [List.length_nil] at this; omega
    rw [forkWidth_eq r hne]; omega
  · constructor
    · rintro ⟨r, k, k', hne, hk, hk'⟩
      rcases Nat.lt_or_ge n 2 with h | h
      · have := rgs_kurz_max r (by omega); omega
      · exact h
    · intro h
      obtain ⟨j, rfl⟩ : ∃ j, n = j + 2 := ⟨n - 2, by omega⟩
      refine ⟨zeuge01 j, 0, 1, by decide, Nat.zero_le _, ?_⟩
      show 1 ≤ max 0 (max 1 ((List.replicate j 0).foldr max 0))
      omega
  · rw [fork_eq_range r hne]
    have : (List.range (r.val.foldr max 0 + 2)).filter (fun k => decide (r.val.foldr max 0 < k)) =
        (List.range (r.val.foldr max 0 + 2)).filter (fun k => decide (k = r.val.foldr max 0 + 1)) :=
      List.filter_congr fun k hk => by
        have := List.mem_range.mp hk
        rcases Nat.decEq k (r.val.foldr max 0 + 1) with e | e
        · rw [decide_eq_false e, decide_eq_false (by omega)]
        · rw [decide_eq_true e, decide_eq_true (by omega)]
    rw [this, filter_range_eq, if_pos (Nat.lt_succ_self _)]

/-- **A2 (i):**  der Abstieg nach dem Aufstieg ist die Identität, für jede Wahlregel -/
theorem abstieg_nach_aufstieg (c : Choice) (x : Tower) : descent (ascentBy c x).2 = x.2 :=
  descent_extend x.2 (c x).1 (c x).2.1 (c x).2.2

/-- **A2 (ii):**  von den Fortsetzungen über einem nichtleeren r stellt der Aufstieg nach dem Abstieg genau die wieder her, die die
    Regel an r wählt;  von den forkWidth r Fortsetzungen genau eine, die übrigen M + 1 nicht -/
theorem wiederherstellung (c : Choice) {n : ℕ} (r : RGS n) (hne : r.val ≠ []) :
    (∀ k hk h0, ascentBy c ⟨n, descent (extend r k hk h0)⟩ = ⟨n + 1, extend r k hk h0⟩ ↔ k = (c ⟨n, r⟩).1) ∧
    ((Fork r).filter (fun k => decide (k = (c ⟨n, r⟩).1))).length = 1 ∧
    ((Fork r).filter (fun k => decide (k ≠ (c ⟨n, r⟩).1))).length = r.val.foldr max 0 + 1 := by
  have hc : (c ⟨n, r⟩).1 < r.val.foldr max 0 + 2 := Nat.lt_succ_of_le (c ⟨n, r⟩).2.1
  refine ⟨fun k hk h0 => ?_, ?_, ?_⟩
  · rw [descent_extend]
    constructor
    · intro h
      have hv : r.val ++ [(c ⟨n, r⟩).1] = r.val ++ [k] := congrArg (fun y : Tower => y.2.val) h
      exact ((List.cons.inj (List.append_cancel_left hv)).1).symm
    · intro h
      exact tower_ext rfl (show r.val ++ [(c ⟨n, r⟩).1] = r.val ++ [k] by rw [h])
  · rw [fork_eq_range r hne, filter_range_eq, if_pos hc]; rfl
  · rw [fork_eq_range r hne, filter_range_ne _ _ hc]; omega

/-! ## Teil B — Rückblick -/

/-- **B1:**  das Präfix der Länge k der erzeugten Kette ist die nach k Schritten erzeugte -/
theorem rueckblick (c : Choice) (k N : ℕ) (h : k ≤ N) : (erzeugt c N).take k = erzeugt c k := by
  have hp := erzeugt_praefix c k N h
  rw [List.prefix_iff_eq_take.mp hp, erzeugt_length]

/-- **B2:**  Regeln derselben Faser über der Kette der Länge N haben dieselben Abstiegsbilder -/
theorem rueckblick_faser (c c' : Choice) (N : ℕ) (h : inFaser c' (erzeugt c N)) :
    ∀ k, k ≤ N → erzeugt c' k = erzeugt c k := by
  intro k hk
  unfold inFaser at h
  rw [erzeugt_length] at h
  rw [← rueckblick c' k N hk, ← rueckblick c k N hk, h]

/-! ## Teil C — Gegenmodelle:  was ist nur Baum? -/

/-- **A0 für jeden freien Baum:**  Aufstieg und Abstieg sind Konverse — auch in FB (`Bool`) und FN (`ℕ`) -/
theorem konvers_frei {α : Type} (l m : List α) : (∃ b, m = l ++ [b]) ↔ (m ≠ [] ∧ m.dropLast = l) := by
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨List.append_ne_nil_of_right_ne_nil l (List.cons_ne_nil b []), List.dropLast_concat⟩
  · rintro ⟨hne, hd⟩
    exact ⟨m.getLast hne, by rw [← hd]; exact (List.dropLast_append_getLast hne).symm⟩

/-- die erzeugte Kette im freien Baum -/
def erzeugtF {α : Type} (c : List α → α) : ℕ → List α
  | 0 => []
  | n + 1 => erzeugtF c n ++ [c (erzeugtF c n)]

theorem erzeugtF_length {α : Type} (c : List α → α) : ∀ n, (erzeugtF c n).length = n
  | 0 => rfl
  | n + 1 => by rw [erzeugtF, List.length_append, erzeugtF_length c n]; rfl

/-- **B1 für jeden freien Baum** -/
theorem rueckblick_frei {α : Type} (c : List α → α) : ∀ k N, k ≤ N → (erzeugtF c N).take k = erzeugtF c k
  | k, 0, h => by rw [Nat.le_zero.mp h]; rfl
  | k, N + 1, h => by
    rcases Nat.lt_or_ge k (N + 1) with h' | h'
    · rw [erzeugtF, List.take_append_of_le_length (by rw [erzeugtF_length]; omega)]
      exact rueckblick_frei c k N (by omega)
    · have : k = N + 1 := by omega
      subst this
      rw [List.take_of_length_le (by rw [erzeugtF_length])]

/-- **C1:**  über einer nichtleeren RGS ist unter den Fortsetzungen genau EINE kein Glied der Kette:  der neue Wert M + 1 -/
theorem genau_ein_neuer {n : ℕ} (r : RGS n) (hne : r.val ≠ []) :
    (Fork r).filter (fun k => decide (k ∉ r.val)) = [r.val.foldr max 0 + 1] := by
  rw [fork_eq_range r hne]
  have hlen : 0 < r.val.length := List.length_pos_iff.mpr hne
  have : (List.range (r.val.foldr max 0 + 2)).filter (fun k => decide (k ∉ r.val)) =
      (List.range (r.val.foldr max 0 + 2)).filter (fun k => decide (k = r.val.foldr max 0 + 1)) :=
    List.filter_congr fun k hk => by
      have hk' := List.mem_range.mp hk
      rcases Nat.decEq k (r.val.foldr max 0 + 1) with e | e
      · have hkle : k ≤ r.val.foldr max 0 := by omega
        have hm := rgs_take_mem r.property.2 r.val.length (le_refl _) hlen k
        rw [List.take_length] at hm
        rw [decide_eq_false e, decide_eq_false (show ¬ (k ∉ r.val) from fun hn => hn (hm hkle))]
      · have hn : k ∉ r.val := fun hm => by have := mem_le_max r.val k hm; omega
        rw [decide_eq_true e, decide_eq_true hn]
  rw [this, filter_range_eq, if_pos (Nat.lt_succ_self _)]

/-- **C, FB:**  im freien Binärbaum gibt es eine Kette, an der es KEINEN neuen Wert gibt -/
theorem fb_kein_neuer : ∃ l : List Bool, ∀ b : Bool, b ∈ l :=
  ⟨[false, true], by decide⟩

/-- **C, FN:**  im freien ℕ-Baum gibt es an jeder Kette beliebig grosse neue Werte -/
theorem fn_unendlich_neu (l : List ℕ) : ∀ N, ∃ k, N ≤ k ∧ k ∉ l := by
  intro N
  refine ⟨N + l.foldr max 0 + 1, by omega, fun h => ?_⟩
  have := mem_le_max l _ h
  omega

/-- **C, FB, A1a:**  schon an der Wurzel zwei Fortsetzungen -/
theorem fb_wurzel : ([] ++ [false] : List Bool) ≠ [] ++ [true] := by decide

/-- **C, FN, A1a:**  an jeder Kette unendlich viele Fortsetzungen -/
theorem fn_weite (l : List ℕ) : Function.Injective fun k : ℕ => l ++ [k] :=
  fun _ _ h => (List.cons.inj (List.append_cancel_left h)).1

/-- **C, FB, A2(ii):**  von den zwei Fortsetzungen wird eine nicht wiederhergestellt — konstant 1 -/
theorem fb_wiederherstellung : ∀ b : Bool, ([false, true].filter fun b' => decide (b' ≠ b)).length = 1 := by decide

/-- **C, FN, A2(ii):**  unendlich viele Fortsetzungen werden nicht wiederhergestellt -/
theorem fn_wiederherstellung (j : ℕ) : ∀ N, ∃ k, N ≤ k ∧ k ≠ j :=
  fun N => ⟨N + j + 1, by omega, by omega⟩

/-! ## Eichungen und Muss-Fälle -/

def q0 : RGS 1 := ⟨[0], by decide⟩
def q01 : RGS 2 := ⟨[0, 1], by decide⟩
def q0102 : RGS 4 := ⟨[0, 1, 0, 2], by decide⟩

/-- A2(ii) und C1 an drei Punkten:  M + 1 = 1, 2, 3 — die Zahl hängt vom Präfix ab -/
theorem eich_richtung :
    ((Fork q0).filter fun k => decide (k ≠ 0)).length = 1 ∧ ((Fork q01).filter fun k => decide (k ≠ 0)).length = 2 ∧
    ((Fork q0102).filter fun k => decide (k ≠ 0)).length = 3 ∧
    (Fork q0).filter (fun k => decide (k ∉ q0.val)) = [1] ∧ (Fork q01).filter (fun k => decide (k ∉ q01.val)) = [2] ∧
    (Fork q0102).filter (fun k => decide (k ∉ q0102.val)) = [3] := by
  decide

/-- **Muss-Fall A2(ii):**  „M + 2 nicht wiederhergestellt" fällt an `[0]` -/
theorem gegen_zahl_wiederherstellung : ((Fork q0).filter fun k => decide (k ≠ 0)).length ≠ 0 + 2 := by decide

/-- **Muss-Fall C1:**  „zwei neue Werte, M + 1 und M + 2" fällt an [0,1];  und ohne RGS fällt C1:  über [0,2] (keine RGS) liegen im
    Bereich 0 … 3 zwei Werte ausserhalb, 1 und 3 -/
theorem gegen_ein_neuer :
    (Fork q01).filter (fun k => decide (k ∉ q01.val)) ≠ [2, 3] ∧ ¬ IsRGS [0, 2] ∧
    (List.range 4).filter (fun k => decide (k ∉ [0, 2])) = [1, 3] := by
  decide

/-- **Muss-Fall A1(c):**  mit „n ≥ 1" statt „n ≥ 2" fällt die Schwelle an n = 1 -/
theorem gegen_schwelle_eins :
    ¬ ∀ n, (∃ r : RGS n, ∃ k k', k ≠ k' ∧ k ≤ r.val.foldr max 0 ∧ k' ≤ r.val.foldr max 0) ↔ 1 ≤ n := by
  intro H
  have := (schwellenleiter.2.2.1 1).mp ((H 1).mpr (le_refl _))
  omega

end Reformulation.Proemial.RichtungProgrammProbe

/-! ## Axiom-Wachen (gemessen, verbatim) -/

/-- info: 'Reformulation.Proemial.RichtungProgrammProbe.snoc_schranke' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.RichtungProgrammProbe.snoc_schranke

/-- info: 'Reformulation.Proemial.RichtungProgrammProbe.mem_le_max' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.RichtungProgrammProbe.mem_le_max

/-- info: 'Reformulation.Proemial.RichtungProgrammProbe.fork_eq_range' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.RichtungProgrammProbe.fork_eq_range

/-- info: 'Reformulation.Proemial.RichtungProgrammProbe.filter_range_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.RichtungProgrammProbe.filter_range_eq

/-- info: 'Reformulation.Proemial.RichtungProgrammProbe.filter_range_ne' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.RichtungProgrammProbe.filter_range_ne

/-- info: 'Reformulation.Proemial.RichtungProgrammProbe.zerlege' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.RichtungProgrammProbe.zerlege

/-- info: 'Reformulation.Proemial.RichtungProgrammProbe.kante_konvers' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.RichtungProgrammProbe.kante_konvers

/-- info: 'Reformulation.Proemial.RichtungProgrammProbe.rgs_kurz_max' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.RichtungProgrammProbe.rgs_kurz_max

/-- info: 'Reformulation.Proemial.RichtungProgrammProbe.isRGSAux_nullen' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.RichtungProgrammProbe.isRGSAux_nullen

/-- info: 'Reformulation.Proemial.RichtungProgrammProbe.schwellenleiter' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.RichtungProgrammProbe.schwellenleiter

/-- info: 'Reformulation.Proemial.RichtungProgrammProbe.abstieg_nach_aufstieg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.RichtungProgrammProbe.abstieg_nach_aufstieg

/-- info: 'Reformulation.Proemial.RichtungProgrammProbe.wiederherstellung' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.RichtungProgrammProbe.wiederherstellung

/-- info: 'Reformulation.Proemial.RichtungProgrammProbe.rueckblick' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.RichtungProgrammProbe.rueckblick

/-- info: 'Reformulation.Proemial.RichtungProgrammProbe.rueckblick_faser' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.RichtungProgrammProbe.rueckblick_faser

/-- info: 'Reformulation.Proemial.RichtungProgrammProbe.konvers_frei' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.RichtungProgrammProbe.konvers_frei

/-- info: 'Reformulation.Proemial.RichtungProgrammProbe.erzeugtF_length' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.RichtungProgrammProbe.erzeugtF_length

/-- info: 'Reformulation.Proemial.RichtungProgrammProbe.rueckblick_frei' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.RichtungProgrammProbe.rueckblick_frei

/-- info: 'Reformulation.Proemial.RichtungProgrammProbe.genau_ein_neuer' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.RichtungProgrammProbe.genau_ein_neuer

/-- info: 'Reformulation.Proemial.RichtungProgrammProbe.fb_kein_neuer' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.RichtungProgrammProbe.fb_kein_neuer

/-- info: 'Reformulation.Proemial.RichtungProgrammProbe.fn_unendlich_neu' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.RichtungProgrammProbe.fn_unendlich_neu

/-- info: 'Reformulation.Proemial.RichtungProgrammProbe.fb_wurzel' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Proemial.RichtungProgrammProbe.fb_wurzel

/-- info: 'Reformulation.Proemial.RichtungProgrammProbe.fn_weite' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Proemial.RichtungProgrammProbe.fn_weite

/-- info: 'Reformulation.Proemial.RichtungProgrammProbe.fb_wiederherstellung' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Proemial.RichtungProgrammProbe.fb_wiederherstellung

/-- info: 'Reformulation.Proemial.RichtungProgrammProbe.fn_wiederherstellung' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.RichtungProgrammProbe.fn_wiederherstellung

/-- info: 'Reformulation.Proemial.RichtungProgrammProbe.eich_richtung' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.RichtungProgrammProbe.eich_richtung

/-- info: 'Reformulation.Proemial.RichtungProgrammProbe.gegen_zahl_wiederherstellung' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Proemial.RichtungProgrammProbe.gegen_zahl_wiederherstellung

/-- info: 'Reformulation.Proemial.RichtungProgrammProbe.gegen_ein_neuer' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.RichtungProgrammProbe.gegen_ein_neuer

/-- info: 'Reformulation.Proemial.RichtungProgrammProbe.gegen_schwelle_eins' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.RichtungProgrammProbe.gegen_schwelle_eins
