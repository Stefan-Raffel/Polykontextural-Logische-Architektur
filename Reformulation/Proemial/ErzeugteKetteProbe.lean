import Reformulation.Proemial.UebergangMitInhaltProbe   -- waehleNeu, step_iter, stepNeu_iter; über KenogramForkProbe: Choice, ascentBy, Fork
import Reformulation.Proemial.DirectionChoice            -- factorsThroughUnit_iff_constant

/-!
# Proemial.ErzeugteKetteProbe — die erzeugte Kette einer Wahlregel, ihre Faser, die Retraktion, der Ein-Schritt, die Unit-Brücke

STANDALONE, NICHT im Aggregat; Target `Probes`. AxiomGate unberührt. Sonde nach
`KorpusRev2/Prompt_Instanz_Erzeugte_Kette_Bau.md` (Mathematiker, 24.10.2026 22:49;  Architekt 22:47).  Grundlage:
`KorpusRev2/Paragraph20_Turm_Antwort_Mathematiker_auf_Horistes_Speculum.md` (§2 Fasersatz, §3 Ein-Schritt, §4 Namen, §5 K-1),
`Vorprobe_Paragraph20_Traeger_Turm_beide_Richtungen.md` (§1, Nachtrag 22:28), Horistes H1–H5, Speculum S1–S4.
Konsumiert `KenogramForkProbe` (`Choice`, `ascentBy`, `forkWidth`), `UebergangMitInhaltProbe` (`waehleNeu`, `step_iter`),
`TowerAsymmetryProbe` (`Tower`, `step`), `Kenogram` (`isRGS_head`, `isRGS_getElem_le`, `isRGS_concat`), `DirectionChoice`
(`factorsThroughUnit_iff_constant`);  ändert nichts davon.

## WAS — Mathematik des Hauses über dem Turm

Eine Wahlregel `c : Choice` wählt an jedem Turmpunkt ein zulässiges nächstes Zeichen;  `ascentBy c` hängt es an.  **`erzeugt c n`**
ist die Kette, die `c` in `n` Schritten ab der leeren Kette hervorbringt — der Lauf einer Strategie innerhalb der Erzeugungs-Regel
„wiederholen oder neu setzen" (`Kenogram.Stream`, K-3, F-2).  Der Name stützt sich auf K-3, nicht auf EuW S. 7 (dort ist das Erzeugte
„ein Denken, das bloß mentales Bild ist" — die Wortfalle „Bild", Speculum S3).  Verwandt, nicht gleich:  `track` (NegationCycle,
SpurProbe) ist der Weg EINES Werts unter einem Negatorwort;  die Präfix-Spur von `KenogramForkProbe` ist das Bild unter `descent`;
`erzeugt` ist der Lauf EINER Regel.  Drei Gegenstände, kein gemeinsamer Name;  „Spur" steht darum hier nicht.

```text
erzeugt c n            die erzeugte Kette (Listenebene;  als RGS hätte sie den Typ RGS ((…).1), wie step_iter)
aufPfad r x            x liegt auf dem Pfad von r:  x.1 < |r| und x.2 = r.take x.1   (gleichwertig:  echtes Präfix von r, `aufPfad_iff`)
ueberschreibe r hr c₀  auf dem Pfad von r das nächste Zeichen von r, sonst c₀
regelNach r hr         ueberschreibe r hr waehleNull — eine Regel, die r erzeugt
```

## Die Sätze

```text
fasersatz_a        FOLGERUNG   erzeugt c |r| = r  ↔  ∀ i < |r|, c (r.take i) = r_i — die Regel liegt längs des Pfades fest
                               (Horistes H1;  Speculum:  „nah an der Definition" — (a) ist beinahe sie)
fasersatz_b        FOLGERUNG   ueberschreibe r hr c₀ erzeugt r, und stimmt abseits des Pfades mit c₀ überein
faser_iff          FOLGERUNG   erzeugt c |r| = r  ↔  c stimmt überall mit ueberschreibe r hr c überein:  frei sind GENAU die Punkte
                               abseits des Pfades (die Faser ist {ueberschreibe r hr c₀ | c₀} im Wert)
erzeugt_regelNach  FOLGERUNG   die Retraktion:  erzeugt (regelNach r hr) |r| = r
erzeugt_lokal      Hilfssatz   zwei Regeln, die unterhalb n übereinstimmen, erzeugen dieselbe Kette der Länge n;
erzeugt_lokal_pfad FOLGERUNG   die schärfere Fassung:  Übereinstimmung auf dem Pfad genügt
ein_schritt        FOLGERUNG   ascentBy c x = ascentBy c' x ↔ (c x).1 = (c' x).1 (Horistes H4:  E&W S. 26 kennt nur den einen Schritt)
ein_schritt_nicht_injektiv  FOLGERUNG (Zeuge, decide)  an [0,0] derselbe Schritt, an [0,1] verschiedene Wirkung
unit_ist_null, unit_erzeugt, unit_faktor_erzeugt   FOLGERUNG   eine Regel, deren Wert nicht vom Punkt abhängt, wählt überall 0 und
                               erzeugt [0, …, 0] (über step_iter;  die dritte Fassung über factorsThroughUnit_iff_constant)
stufe_zwei_injektiv  FOLGERUNG  an Stufe 2 trennt erzeugt die Wirkungen auf `[0]`
stufe_drei_faser   EICHUNG (decide)  an Stufe 3 nicht:  zwei Paare verschiedener Regeln mit derselben Kette
gabel_abseits      EICHUNG (decide)  die Gabelbreiten abseits des Pfades an Stufe 3:  forkWidth [0,1] = 3, forkWidth [0,0] = 2
```

**Die Produktformel** „|Faser über r| = Π der Gabelbreiten abseits des Pfades" ist der Zählschatten von `faser_iff` und hier KEIN Satz
(eine Wahlregel ist eine Funktion auf dem ganzen Turm;  die Zählung braucht ihr Segment unterhalb n als endliches Objekt, das der
Bestand nicht führt).  EICHUNG, gerechnet ausserhalb:  Stufe 3, 12 Segmente, 5 Fasern, je Produkt (3, 3, 2, 2, 2) — Mathematiker
(faser.py) und Instanz (Begutachtung 22:24) unabhängig;  Stufe 4, 2 592 Segmente, 15 Fasern, alle Produkt — Mathematiker.

## LESART (nur hier;  kein Dokstring eines Satzes trägt eine)

- Speculum S1:  Günthers zwei „exchange" — (I) der symmetrische [T27][T57][T63][T64], (II) der Wechsel, den R_pr bewirkt, „not mutual"
  [T49][T10].  Die Gabelung ↔ (I), der Übergang Regel ↔ Kette ↔ (II):  ZUORDNUNG.
- `faser_iff` / `fasersatz_b` als die Bindung von A20-4 („eine Aussage, in der die eine Bewegung die andere bedingt"):  ZUSAMMENSCHAU,
  in der BURIDAN-Modalität ([T30] „triggers … supply this order by making a choice"), NICHT in der von S. 23 („implies").
- Wort „Gabelung", nicht „Schwebe" ([T63] steht in der kognitiven Zeile;  hier volitiv, [T64]).
- „Ordnung" nur mit Index:  O1 (Index) / O2 (Aktualisierung).

## OFFEN (K-1) — die Rollen-Zuordnung

Der Bestand beschriftet den Aufstieg in einer Richtung (`AsymmetricDiscontexturalTransition`, Feld `ascent`;  `KenogramForkProbe`
§5), die Vorprobe 24.10. liest `erzeugt` (Regel → Kette) in der anderen, gestützt auf [T10].  Zwei verschiedene Pfeile (`step`:
Kette → Kette;  `erzeugt`:  Regel → Kette).  Dieses Modul schreibt KEINE der beiden Beschriftungen.  Entscheidung:  Hermeneutes am
Bild, Custos.

## NICHT

Kein Träger für §20;  „§20 ohne Träger" bleibt.  Keine Messung an K4′.  Kein Text in Rev11 (Horistes H5).  Keine Ledger-Zeile.
**Verboten:**  „Träger für §20", „fast ein Träger", „die Proemialrelation ist gebaut", „trägt A20-4", „Günthers Implikation",
„Buridan formalisiert", „Diskontexturalität aus der Stufe", „der erste Kandidat" ohne die Reihe der zwölf (Standsbericht 13.8.).

## Bauweise

`isRGS_take_frei`:  derselbe Satz wie `Kenogram.isRGS_take` (`Kenogram/PlaceSwap.lean`), der dort über `relabel` läuft und
`Classical.choice` trägt (gemessen);  hier per Induktion über `isRGS_concat`, ohne Choice.  `waehleNull`:  die Wahlregel „überall 0"
— der Bestand führt sie nur anonym (`step_eq_ascentBy_zero`).

Kein `sorry`, kein `Classical.choice`, kein `native_decide`, kein True-Feld.
-/

namespace Reformulation.Proemial.ErzeugteKetteProbe

open Reformulation.Kenogram
open Reformulation.Proemial.TowerAsymmetryProbe (Tower step)
open Reformulation.Proemial.KenogramForkProbe (Choice ascentBy forkWidth step_eq_ascentBy_zero)
open Reformulation.Proemial.UebergangMitInhaltProbe (waehleNeu step_iter)

/-! ## Werkzeug -/

/-- zwei Turmpunkte mit gleicher Stufe und gleicher Kette sind gleich -/
theorem tower_ext {x y : Tower} (h1 : x.1 = y.1) (h2 : x.2.val = y.2.val) : x = y := by
  obtain ⟨n, r⟩ := x
  obtain ⟨m, s⟩ := y
  simp only at h1 h2
  subst h1
  exact congrArg (Sigma.mk n) (Subtype.ext h2)

/-- Präfixe einer RGS sind RGS — choice-frei (`Kenogram.isRGS_take` trägt `Classical.choice`) -/
theorem isRGS_take_frei {l : List ℕ} (h : IsRGS l) : ∀ k, IsRGS (l.take k)
  | 0 => by rw [List.take_zero]; decide
  | k + 1 => by
    rcases Nat.lt_or_ge k l.length with hk | hk
    · rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some]
      refine isRGS_concat _ _ (isRGS_take_frei h k) ?_ ?_
      · rcases Nat.eq_zero_or_pos k with h0 | hpos
        · subst h0
          rw [isRGS_head h hk]
          exact Nat.zero_le _
        · exact isRGS_getElem_le h hk hpos
      · intro he
        have hlen : (l.take k).length = min k l.length := List.length_take
        rw [he, List.length_nil] at hlen
        have h0 : k = 0 := by omega
        subst h0
        exact isRGS_head h hk
    · rw [List.take_of_length_le (by omega)]
      exact h

/-- die leere Kette als Turmpunkt -/
def wurzel : Tower := ⟨0, ⟨[], by decide⟩⟩

/-- der Turmpunkt nach i Schritten unter c -/
def stand (c : Choice) (i : ℕ) : Tower := (ascentBy c)^[i] wurzel

/-- **die von c erzeugte Kette der Länge n** -/
def erzeugt (c : Choice) (n : ℕ) : List ℕ := (stand c n).2.val

theorem stand_succ (c : Choice) (i : ℕ) : stand c (i + 1) = ascentBy c (stand c i) :=
  Function.iterate_succ_apply' (ascentBy c) i wurzel

theorem stand_fst (c : Choice) : ∀ i, (stand c i).1 = i
  | 0 => rfl
  | i + 1 => by rw [stand_succ]; exact congrArg (· + 1) (stand_fst c i)

theorem stand_succ_val (c : Choice) (i : ℕ) :
    (stand c (i + 1)).2.val = (stand c i).2.val ++ [(c (stand c i)).1] := by
  rw [stand_succ]; rfl

theorem erzeugt_length (c : Choice) (n : ℕ) : (erzeugt c n).length = n := by
  exact (stand c n).2.property.1.trans (stand_fst c n)

/-- der Turmpunkt auf dem Pfad von r an Stelle i -/
def pfadPunkt (r : List ℕ) (hr : IsRGS r) (i : ℕ) (hi : i ≤ r.length) : Tower :=
  ⟨i, ⟨r.take i, by rw [List.length_take]; omega, isRGS_take_frei hr i⟩⟩

/-! ## Der Pfad -/

/-- x liegt auf dem Pfad von r:  ein echtes Präfix, als Stelle und Kette -/
def aufPfad (r : List ℕ) (x : Tower) : Prop := x.1 < r.length ∧ x.2.val = r.take x.1

instance (r : List ℕ) (x : Tower) : Decidable (aufPfad r x) := inferInstanceAs (Decidable (_ ∧ _))

theorem aufPfad_iff (r : List ℕ) (x : Tower) : aufPfad r x ↔ x.2.val <+: r ∧ x.2.val.length < r.length := by
  have hlen : x.2.val.length = x.1 := x.2.property.1
  rw [hlen, List.prefix_iff_eq_take, hlen]
  exact And.comm

theorem zul_schranke (r : List ℕ) (hr : IsRGS r) (x : Tower) (h1 : x.1 < r.length) (h2 : x.2.val = r.take x.1) :
    r[x.1] ≤ x.2.val.foldr max 0 + 1 := by
  rw [h2]
  rcases Nat.eq_zero_or_pos x.1 with h0 | hpos
  · have e : r[x.1] = 0 := by
      have := isRGS_head hr (by omega : 0 < r.length)
      simp only [h0]; exact this
    rw [e]; exact Nat.zero_le _
  · exact isRGS_getElem_le hr h1 hpos

theorem zul_null (r : List ℕ) (hr : IsRGS r) (x : Tower) (h1 : x.1 < r.length) :
    x.2.val = [] → r[x.1] = 0 := by
  intro he
  have hl : x.2.val.length = x.1 := x.2.property.1
  rw [he, List.length_nil] at hl
  have := isRGS_head hr (by omega : 0 < r.length)
  simp only [← hl]; exact this

/-- **die überschriebene Regel:**  auf dem Pfad von r das nächste Zeichen von r, sonst c₀ -/
def ueberschreibe (r : List ℕ) (hr : IsRGS r) (c₀ : Choice) : Choice := fun x =>
  if h : aufPfad r x then
    ⟨r[x.1]'h.1, zul_schranke r hr x h.1 h.2, zul_null r hr x h.1⟩
  else c₀ x

/-- die Wahlregel „überall 0" (im Bestand nur anonym:  `step_eq_ascentBy_zero`) -/
def waehleNull : Choice := fun _ => ⟨0, Nat.zero_le _, fun _ => rfl⟩

/-- **eine Regel, die r erzeugt** -/
def regelNach (r : List ℕ) (hr : IsRGS r) : Choice := ueberschreibe r hr waehleNull

/-! ## Der Fasersatz -/

theorem pfad_stand (c : Choice) (r : List ℕ) (hr : IsRGS r) :
    ∀ i (hi : i ≤ r.length),
      (∀ j (hj : j < i), (c (pfadPunkt r hr j (by omega))).1 = r[j]'(by omega)) ↔ (stand c i).2.val = r.take i
  | 0, _ => by
    constructor
    · intro _; rfl
    · intro _ j hj; omega
  | i + 1, hi => by
    have ih := pfad_stand c r hr i (by omega)
    have hpt : stand c i = pfadPunkt r hr i (by omega) → (c (stand c i)).1 = (c (pfadPunkt r hr i (by omega))).1 :=
      fun h => by rw [h]
    rw [stand_succ_val, List.take_add_one, List.getElem?_eq_getElem (by omega : i < r.length), Option.toList_some]
    constructor
    · intro H
      have hi' := ih.mp (fun j hj => H j (by omega))
      have heq : stand c i = pfadPunkt r hr i (by omega) := tower_ext (stand_fst c i) hi'
      rw [hpt heq, H i (by omega), hi']
    · intro H
      have hlen : (stand c i).2.val.length = (r.take i).length := by
        rw [List.length_take, (stand c i).2.property.1, stand_fst]; omega
      obtain ⟨h1, h2⟩ := List.append_inj H hlen
      have heq : stand c i = pfadPunkt r hr i (by omega) := tower_ext (stand_fst c i) h1
      intro j hj
      rcases Nat.lt_or_ge j i with hji | hji
      · exact ih.mpr h1 j hji
      · have hj' : j = i := by omega
        subst hj'
        have := List.cons.inj h2
        rw [← hpt heq]; exact this.1

/-- **Fasersatz (a).**  c erzeugt r genau dann, wenn c längs des Pfades von r die Zeichen von r wählt.  Beinahe die Definition. -/
theorem fasersatz_a (c : Choice) (r : List ℕ) (hr : IsRGS r) :
    erzeugt c r.length = r ↔ ∀ i (hi : i < r.length), (c (pfadPunkt r hr i (Nat.le_of_lt hi))).1 = r[i] := by
  have := pfad_stand c r hr r.length (le_refl _)
  rw [List.take_length] at this
  exact this.symm

theorem pfadPunkt_aufPfad (r : List ℕ) (hr : IsRGS r) (i : ℕ) (hi : i < r.length) :
    aufPfad r (pfadPunkt r hr i (Nat.le_of_lt hi)) := ⟨hi, rfl⟩

theorem ueberschreibe_pfad (r : List ℕ) (hr : IsRGS r) (c₀ : Choice) (x : Tower) (h : aufPfad r x) :
    (ueberschreibe r hr c₀ x).1 = r[x.1]'h.1 := by
  simp only [ueberschreibe, dif_pos h]

theorem ueberschreibe_abseits (r : List ℕ) (hr : IsRGS r) (c₀ : Choice) (x : Tower) (h : ¬ aufPfad r x) :
    (ueberschreibe r hr c₀ x).1 = (c₀ x).1 := by
  simp only [ueberschreibe, dif_neg h]

/-- **Fasersatz (b).**  Die überschriebene Regel erzeugt r, und abseits des Pfades ist sie c₀ — für jedes c₀. -/
theorem fasersatz_b (r : List ℕ) (hr : IsRGS r) (c₀ : Choice) :
    erzeugt (ueberschreibe r hr c₀) r.length = r ∧
      ∀ x, ¬ aufPfad r x → (ueberschreibe r hr c₀ x).1 = (c₀ x).1 := by
  refine ⟨(fasersatz_a _ r hr).mpr fun i hi => ?_, ueberschreibe_abseits r hr c₀⟩
  exact ueberschreibe_pfad r hr c₀ _ (pfadPunkt_aufPfad r hr i hi)

/-- **Die Faser über r:**  c erzeugt r genau dann, wenn c überall mit ihrer Überschreibung durch r übereinstimmt — frei sind genau
    die Punkte abseits des Pfades. -/
theorem faser_iff (c : Choice) (r : List ℕ) (hr : IsRGS r) :
    erzeugt c r.length = r ↔ ∀ x, (c x).1 = (ueberschreibe r hr c x).1 := by
  constructor
  · intro H x
    exact (Decidable.byCases (p := aufPfad r x)
      (fun h => by
        rw [ueberschreibe_pfad r hr c x h]
        have heq : x = pfadPunkt r hr x.1 (Nat.le_of_lt h.1) := tower_ext rfl h.2
        have := (fasersatz_a c r hr).mp H x.1 h.1
        rw [← heq] at this; exact this)
      (fun h => (ueberschreibe_abseits r hr c x h).symm))
  · intro H
    refine (fasersatz_a c r hr).mpr fun i hi => ?_
    rw [H]; exact ueberschreibe_pfad r hr c _ (pfadPunkt_aufPfad r hr i hi)

/-- **Die Retraktion.** -/
theorem erzeugt_regelNach (r : List ℕ) (hr : IsRGS r) : erzeugt (regelNach r hr) r.length = r :=
  (fasersatz_b r hr waehleNull).1

/-! ## Der Ein-Schritt und die Lokalität -/

/-- **Der Ein-Schritt.**  Zwei Regeln haben an x denselben Schritt genau dann, wenn sie dort dasselbe Zeichen wählen. -/
theorem ein_schritt (c c' : Choice) (x : Tower) : ascentBy c x = ascentBy c' x ↔ (c x).1 = (c' x).1 := by
  constructor
  · intro h
    have hv : x.2.val ++ [(c x).1] = x.2.val ++ [(c' x).1] := congrArg (fun y : Tower => y.2.val) h
    exact List.cons.inj (List.append_cancel_left hv) |>.1
  · intro h
    exact tower_ext rfl (by show x.2.val ++ [(c x).1] = x.2.val ++ [(c' x).1]; rw [h])

/-- **Lokalität.**  Regeln, die auf allen Punkten unterhalb n übereinstimmen, erzeugen dieselbe Kette der Länge n. -/
theorem erzeugt_lokal (c c' : Choice) (n : ℕ) (h : ∀ x : Tower, x.1 < n → (c x).1 = (c' x).1) :
    erzeugt c n = erzeugt c' n := by
  have key : ∀ i, i ≤ n → stand c i = stand c' i := by
    intro i
    induction i with
    | zero => intro _; rfl
    | succ i ih =>
      intro hi
      rw [stand_succ, stand_succ, ih (by omega)]
      exact (ein_schritt c c' _).mpr (h _ (by rw [stand_fst]; omega))
  exact congrArg (fun y : Tower => y.2.val) (key n (le_refl _))

/-- **Lokalität, schärfer:**  erzeugt c die Kette r, und stimmt c' mit c längs des Pfades von r überein, so erzeugt auch c' sie. -/
theorem erzeugt_lokal_pfad (c c' : Choice) (r : List ℕ) (hr : IsRGS r) (hc : erzeugt c r.length = r)
    (h : ∀ i (hi : i < r.length), (c (pfadPunkt r hr i (Nat.le_of_lt hi))).1 = (c' (pfadPunkt r hr i (Nat.le_of_lt hi))).1) :
    erzeugt c' r.length = r :=
  (fasersatz_a c' r hr).mpr fun i hi => (h i hi).symm.trans ((fasersatz_a c r hr).mp hc i hi)

/-! ## Die Unit-Brücke -/

/-- eine Regel, deren Wert nicht vom Punkt abhängt, wählt überall 0 (über der leeren Kette ist nur 0 zulässig) -/
theorem unit_ist_null (c : Choice) (h : ∃ k, ∀ x, (c x).1 = k) : ∀ x, (c x).1 = 0 := by
  obtain ⟨k, hk⟩ := h
  have h0 : (c wurzel).1 = 0 := (c wurzel).2.2 rfl
  intro x; rw [hk x, ← hk wurzel, h0]

theorem erzeugt_waehleNull (n : ℕ) : erzeugt waehleNull n = List.replicate n 0 := by
  have h : stand waehleNull n = step^[n] wurzel := by
    unfold stand; rw [step_eq_ascentBy_zero]; rfl
  unfold erzeugt; rw [h]; exact step_iter n

/-- **Die Unit-Brücke:**  eine Regel, deren Wert nicht vom Punkt abhängt, erzeugt [0, …, 0] -/
theorem unit_erzeugt (c : Choice) (h : ∃ k, ∀ x, (c x).1 = k) (n : ℕ) : erzeugt c n = List.replicate n 0 := by
  rw [← erzeugt_waehleNull n]
  exact erzeugt_lokal c waehleNull n fun x _ => unit_ist_null c h x

/-- dieselbe Brücke in der Gestalt von `DirectionChoice`:  durch `Unit` faktorisierend -/
theorem unit_faktor_erzeugt (c : Choice) (h : ∃ g : Unit → ℕ, ∀ x, (c x).1 = g ()) (n : ℕ) :
    erzeugt c n = List.replicate n 0 :=
  unit_erzeugt c ((DirectionChoice.factorsThroughUnit_iff_constant (fun x => (c x).1)).mp h) n

/-! ## Stufe 2 und Stufe 3 -/

/-- der Turmpunkt `[0]` -/
def p0 : Tower := ⟨1, ⟨[0], by decide⟩⟩
/-- der Turmpunkt [0,0] -/
def p00 : Tower := ⟨2, ⟨[0, 0], by decide⟩⟩
/-- der Turmpunkt [0,1] -/
def p01 : Tower := ⟨2, ⟨[0, 1], by decide⟩⟩

theorem stand_eins (c : Choice) : stand c 1 = p0 :=
  tower_ext rfl (by rw [stand_succ_val]; show [] ++ [(c wurzel).1] = [0]; rw [(c wurzel).2.2 rfl]; rfl)

theorem erzeugt_zwei (c : Choice) : erzeugt c 2 = [0, (c p0).1] := by
  unfold erzeugt; rw [stand_succ_val, stand_eins]; rfl

/-- **An Stufe 2 trennt erzeugt die Wirkungen auf `[0]`.** -/
theorem stufe_zwei_injektiv (c c' : Choice) : erzeugt c 2 = erzeugt c' 2 ↔ (c p0).1 = (c' p0).1 := by
  rw [erzeugt_zwei, erzeugt_zwei]
  constructor
  · intro h; exact (List.cons.inj (List.cons.inj h).2).1
  · intro h; rw [h]

/-- „0 überall, ausser 2 an [0,1]" -/
def nullAusser01 : Choice := fun x =>
  if h : x.2.val = [0, 1] then ⟨2, by rw [h]; decide, by rw [h]; intro h'; exact absurd h' (by decide)⟩
  else ⟨0, Nat.zero_le _, fun _ => rfl⟩

theorem isRGS_012 : IsRGS [0, 1, 2] := by decide

/-- **Stufe 3:**  zwei Paare verschiedener Regeln mit derselben erzeugten Kette — waehleNull und nullAusser01 ([0,0,0], verschieden
    an [0,1]);  regelNach [0,1,2] und waehleNeu ([0,1,2], verschieden an [0,0]). -/
theorem stufe_drei_faser :
    erzeugt waehleNull 3 = [0, 0, 0] ∧ erzeugt nullAusser01 3 = [0, 0, 0] ∧ (waehleNull p01).1 ≠ (nullAusser01 p01).1 ∧
    erzeugt (regelNach [0, 1, 2] isRGS_012) 3 = [0, 1, 2] ∧ erzeugt waehleNeu 3 = [0, 1, 2] ∧
    (regelNach [0, 1, 2] isRGS_012 p00).1 ≠ (waehleNeu p00).1 := by
  decide

/-- **Der Ein-Schritt ist nicht injektiv auf der Wirkung einer Stufe:**  waehleNull und regelNach [0,1,2] haben an [0,0] denselben
    Schritt und wählen an [0,1] verschieden. -/
theorem ein_schritt_nicht_injektiv :
    ascentBy waehleNull p00 = ascentBy (regelNach [0, 1, 2] isRGS_012) p00 ∧
    (waehleNull p01).1 ≠ (regelNach [0, 1, 2] isRGS_012 p01).1 :=
  ⟨(ein_schritt _ _ _).mpr (by decide), by decide⟩

/-- **Die Gabelbreiten abseits des Pfades an Stufe 3** -/
theorem gabel_abseits :
    forkWidth (⟨[0, 1], by decide⟩ : RGS 2) = 3 ∧ forkWidth (⟨[0, 0], by decide⟩ : RGS 2) = 2 := by
  decide

end Reformulation.Proemial.ErzeugteKetteProbe

/-! ## Axiom-Wachen (gemessen, verbatim) -/

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.tower_ext' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.tower_ext

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.isRGS_take_frei' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.isRGS_take_frei

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.stand_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.stand_succ

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.stand_fst' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.stand_fst

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.stand_succ_val' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.stand_succ_val

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.erzeugt_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.erzeugt_length

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.aufPfad_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.aufPfad_iff

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.zul_schranke' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.zul_schranke

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.zul_null' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.zul_null

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.pfad_stand' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.pfad_stand

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.fasersatz_a' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.fasersatz_a

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.pfadPunkt_aufPfad' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.pfadPunkt_aufPfad

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.ueberschreibe_pfad' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.ueberschreibe_pfad

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.ueberschreibe_abseits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.ueberschreibe_abseits

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.fasersatz_b' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.fasersatz_b

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.faser_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.faser_iff

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.erzeugt_regelNach' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.erzeugt_regelNach

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.ein_schritt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.ein_schritt

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.erzeugt_lokal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.erzeugt_lokal

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.erzeugt_lokal_pfad' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.erzeugt_lokal_pfad

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.unit_ist_null' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.unit_ist_null

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.erzeugt_waehleNull' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.erzeugt_waehleNull

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.unit_erzeugt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.unit_erzeugt

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.unit_faktor_erzeugt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.unit_faktor_erzeugt

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.stand_eins' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.stand_eins

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.erzeugt_zwei' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.erzeugt_zwei

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.stufe_zwei_injektiv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.stufe_zwei_injektiv

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.isRGS_012' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.isRGS_012

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.stufe_drei_faser' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.stufe_drei_faser

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.ein_schritt_nicht_injektiv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.ein_schritt_nicht_injektiv

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.gabel_abseits' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.gabel_abseits
