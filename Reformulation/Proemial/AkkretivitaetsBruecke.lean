import Reformulation.Proemial.GegenidentitaetProbe   -- spiegel, dreh, spiegel_full; über ThreeCycle: inv, gerichtet
import Reformulation.Proemial.NegationCycleSJT       -- blocks, stations_blocks, die Brücke ℕ ↔ Fin
import Mathlib.Data.List.Rotate                      -- List.rotate

/-!
# Proemial.AkkretivitaetsBruecke — der Aufstieg n → n+1 als Operation auf allen Vollkreisen

STANDALONE, NICHT im Aggregat; Target `Probes`. AxiomGate unberührt. Sonde nach
`KorpusRev2/Sondierung_Akkretivitaets_Bruecke_Prompt.md` (Mathematiker, 20. Oktober 2026) und
der Rechnung `KorpusRev2/Vorklaerung_Akkretivitaets_Bruecke_Rechnung.md`. Konsumiert
`NegationCycleSJT` (`blocks`, `stations_blocks`, die Brücke ℕ ↔ Fin), `NegationCycleLength`
(`inv`, `inv_negate_desc`) und `GegenidentitaetProbe` (`spiegel`, `dreh`, `spiegel_full`);
ändert nichts davon, auch nicht `sjtN_props`.

**Der Ertrag in einem Satz.** Die SJT-Rekursion des Bestandes, `Φ_true = phi true`, ist eine
Operation auf **allen** Vollkreisen, nicht nur die Rekursion einer besonderen Folge
(`phi_full`, `phi_false_full`), und sie trägt Spiegel und Drehsinn hindurch: der Spiegel
tauscht die Fegerichtung (`phi_spiegel`), der Drehsinn tauscht sie und dreht das Wort um
`m + 2` Stellen (`phi_dreh`).

## Die Sätze und ihre Stufen (CLAUDE.md §4)

| Satz | Aussage | Stufe |
|---|---|---|
| `full_even` (A0) | ein Vollkreis hat gerade Länge | FOLGERUNG (über `inv`; bisher nur über `full_length`, das Choice trägt) |
| `inv_negate_parity` | jeder Negator wechselt die Parität von `inv` | FOLGERUNG (`inv_negate_desc` in beiden Richtungen) |
| `blocks_spiegelN` (A1, ℕ) | Spiegel der Blöcke = Blöcke des Spiegels, Fegerichtung getauscht | FOLGERUNG |
| `blocks_drehN` (A2, ℕ) | `R ++ (Φ_true S)ʳ = Φ_false (Sʳ) ++ R`, `R = range n`, gerade Länge | FOLGERUNG |
| `blocks_propsN` (A4, ℕ) | der Schritt von `sjtN_props` für jedes Wort mit den fünf Eigenschaften | HEBUNG |
| `phi_full` (A4) | `phi true` hebt jeden Vollkreis | ZUSAMMENSTELLUNG (`blocks_propsN`, `full_even`, Brücke wie `sjt_full`) |
| `phi_spiegel` (A1) | `spiegel (phi b w) = phi (!b) (spiegel w)`, jedes Wort | ZUSAMMENSTELLUNG (`blocks_spiegelN`, Brücke) |
| `phi_dreh` (A2) | `dreh (phi true w) = (phi false (dreh w)).rotate (m+2)`, gerade Länge | ZUSAMMENSTELLUNG (`blocks_drehN`, `rotate_of_append`) |
| `phi_false_full` | `phi false` hebt jeden Vollkreis | ZUSAMMENSTELLUNG (A1, `spiegel_full`) |
| `phi_sjt` | `phi true (sjt (m+1)) = sjt (m+2)` | ZUSAMMENSTELLUNG (`sjt_val`, Definition) |
| `sjt_full_aus_phi` | `sjt_full`, neu aus `phi_full` | ZUSAMMENSTELLUNG (Induktion) |
| `aufstieg_spiegel`, `aufstieg_dreh` (A5) | die zwei Gleichungen, beide Seiten Vollkreise | ZUSAMMENSTELLUNG |
| `phi_sjt_zwei_gerichtet`, `phi_dreh_tafelVI4` | Eichungen | EICHUNG |

Hilfssätze: `range_map_rev`, `range_reverse_map_rev`, `blocks_append`, `rotate_of_append`,
`before_map`, `sw_castSucc`, `castSucc_ne_succ`, `sw_succ`, `inv_endpoint_parity`, `phi_val`,
`spiegel_val`.

**Ebene.** Die Wortidentitäten A1 und A2 stehen auf der ℕ-Ebene, wo `blocks` lebt; die
Fin-Fassungen gehen über `map_val_inj` und `toFin_val`. A4 hebt den Schritt von `sjtN_props`
auf der ℕ-Ebene und überträgt ihn wie `sjt_full`.

**Φ_false** wird nicht über `stations_blocks` bewiesen — dort beginnt `b = false` bei
`insertLast g 0`, nicht beim Ausgang —, sondern über A1: `phi false w = spiegel (phi true
(spiegel w))`.

**Nicht gebaut: `rotate_full`** (A3, die Drehung eines Vollkreises ist ein Vollkreis). Für A5
ist er nicht nötig: die gedrehte Seite von `aufstieg_dreh` ist gleich `dreh (phi true w)` und
damit ein Vollkreis. Allgemein bleibt A3 offen (Figur: Umbenennung der Stellen, nicht der
Werte). Ebenfalls nicht gebaut: die Zahlen der Vorklärung (176 Bilder, 88 Bahnen).

## ZUORDNUNG (nur hier, in keinem Satz)

IGN S. 9: Akkretivität als „Wiederholung mit Verwandlung“, aus der sich die Gegenidentität „immer
wieder in Strukturformen höherer und höherer Akkretvität“ erneuert (Wortlaut und Schreibung im
Kopf von `GegenidentitaetProbe`). Gelesen: der Aufstieg `phi` ist eine Operation auf allen
Kreisen, die Gegenidentität (Spiegel) und Gegen-Drehsinn hindurchträgt — auf der höheren Stufe
wieder als Gegenidentität und Gegen-Drehsinn, mit getauschter Anfangs-Wahl. Dass das Günthers
Akkretivität **ist**, sagt kein Satz. Nichts hier ist die zweite Negation (L07-4 offen).

Kein `sorry`, kein `native_decide`, kein `: True`-Feld, kein `axiom`.
-/

namespace Reformulation.Proemial.AkkretivitaetsBruecke

open Reformulation.Proemial.NegationCycle
open Reformulation.Proemial.GegenidentitaetProbe
open Reformulation.Proemial.NegationCycleSJT
open Reformulation.Proemial.NegationCycleLength (inv inv_negate_desc inv_origin negate_nodup negate_all Before
  Before.total)
open Reformulation.Proemial.NegationCycleTable (gerichtet)

-- ============================================================
-- §I — Der Spiegel tauscht die Fegerichtung (A1, ℕ-Ebene)
-- ============================================================

/-- `range` unter `i ↦ n − 1 − i` ist `range` rückwärts. -/
theorem range_map_rev (n : ℕ) : (List.range n).map (fun i => n - 1 - i) = (List.range n).reverse := by
  apply List.ext_getElem
  · rw [List.length_map, List.length_reverse]
  · intro k h1 h2
    rw [List.getElem_map, List.getElem_reverse, List.getElem_range, List.getElem_range,
      List.length_range]

theorem range_reverse_map_rev (n : ℕ) :
    (List.range n).reverse.map (fun i => n - 1 - i) = List.range n := by
  rw [List.map_reverse, range_map_rev, List.reverse_reverse]

/-- (A1, ℕ) **Der Spiegel der Blöcke sind die Blöcke des Spiegels, mit getauschter
Fegerichtung.** Große Buchstaben `< n`, kleine `< n − 1`. -/
theorem blocks_spiegelN (n : ℕ) : ∀ (S : List ℕ) (b : Bool), (∀ s ∈ S, s + 2 ≤ n) →
    (blocks (n + 1) b S).map (fun i => n - 1 - i) =
      blocks (n + 1) (!b) (S.map (fun s => n - 2 - s))
  | [], b, _ => by cases b <;> rfl
  | s :: ss, b, hS => by
    have hs : s + 2 ≤ n := hS s List.mem_cons_self
    have hss : ∀ t ∈ ss, t + 2 ≤ n := fun t ht => hS t (List.mem_cons_of_mem _ ht)
    cases b with
    | true =>
      rw [blocks_true_cons, List.map_cons, Bool.not_true, blocks_false_cons, List.map_append,
        List.map_append, range_reverse_map_rev, blocks_spiegelN n ss false hss, Bool.not_false]
      congr 2
      rw [List.map_cons, List.map_nil]
      congr 1
      omega
    | false =>
      rw [blocks_false_cons, List.map_cons, Bool.not_false, blocks_true_cons, List.map_append,
        List.map_append, range_map_rev, blocks_spiegelN n ss true hss, Bool.not_true]
      congr 2
      rw [List.map_cons, List.map_nil]
      congr 1
      omega

-- ============================================================
-- §II — Der Drehsinn tauscht die Fegerichtung und dreht das Wort (A2, ℕ-Ebene)
-- ============================================================

/-- Die Blöcke einer Verkettung. -/
theorem blocks_append (k : ℕ) : ∀ (A B : List ℕ) (b : Bool),
    blocks k b (A ++ B) = blocks k b A ++ blocks k (flipN b A.length) B
  | [], B, b => by cases b <;> rfl
  | s :: A, B, true => by
    show (List.range (k - 1)).reverse ++ [s + 1] ++ blocks k false (A ++ B) = _
    rw [blocks_append k A B false]
    show _ = ((List.range (k - 1)).reverse ++ [s + 1] ++ blocks k false A) ++ _
    simp only [List.append_assoc]
    rfl
  | s :: A, B, false => by
    show List.range (k - 1) ++ [s] ++ blocks k true (A ++ B) = _
    rw [blocks_append k A B true]
    show _ = (List.range (k - 1) ++ [s] ++ blocks k true A) ++ _
    simp only [List.append_assoc]
    rfl

/-- Die Kernidentität von A2, ohne Drehung: `R ++ (Φ_true S)ʳ = Φ_false (Sʳ) ++ R` mit
`R = range (n)`, für jedes Wort gerader Länge. -/
theorem blocks_drehN (n : ℕ) : ∀ (t : ℕ) (S : List ℕ), S.length = 2 * t →
    List.range n ++ (blocks (n + 1) true S).reverse =
      blocks (n + 1) false S.reverse ++ List.range n
  | 0, S, h => by
    rw [List.length_eq_zero_iff.mp (by omega : S.length = 0)]
    show List.range n ++ [] = [] ++ List.range n
    rw [List.append_nil, List.nil_append]
  | t + 1, s :: u :: ss, h => by
    have hl : ss.length = 2 * t := by
      rw [List.length_cons, List.length_cons] at h; omega
    have ih := blocks_drehN n t ss hl
    have hr : (s :: u :: ss).reverse = ss.reverse ++ [u, s] := by
      rw [List.reverse_cons, List.reverse_cons, List.append_assoc]; rfl
    rw [hr, blocks_append, List.length_reverse, hl, flipN_even]
    show List.range n ++ ((List.range (n + 1 - 1)).reverse ++ [s + 1] ++
        (List.range (n + 1 - 1) ++ [u] ++ blocks (n + 1) true ss)).reverse =
      blocks (n + 1) false ss.reverse ++
        (List.range (n + 1 - 1) ++ [u] ++ ((List.range (n + 1 - 1)).reverse ++ [s + 1] ++ [])) ++
          List.range n
    rw [show n + 1 - 1 = n from rfl]
    simp only [List.reverse_append, List.reverse_reverse, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.append_nil, List.append_assoc]
    rw [← List.append_assoc (List.range n), ih]
    simp only [List.append_assoc, List.cons_append]
  | t + 1, [], h => by rw [List.length_nil] at h; omega
  | t + 1, [_], h => by rw [List.length_singleton] at h; omega

/-- Ist `R ++ T = L ++ R` und `R` nicht länger als `L`, so ist `T` die Drehung von `L` um `|R|`. -/
theorem rotate_of_append {α : Type*} {R T L : List α} (h : R ++ T = L ++ R)
    (hl : R.length ≤ L.length) : L.rotate R.length = T := by
  rw [List.rotate_eq_drop_append_take hl]
  have h1 := congrArg (List.drop R.length) h
  rw [List.drop_left, List.drop_append_of_le_length hl] at h1
  have h2 := congrArg (List.take R.length) h
  rw [List.take_left, List.take_append_of_le_length hl] at h2
  rw [h1, ← h2]

-- ============================================================
-- §III — Ein Vollkreis hat gerade Länge, ohne `full_length` (A0)
-- ============================================================

/-- `Before` wandert mit `map`. -/
theorem before_map {α β : Type} (f : α → β) {x y : α} :
    ∀ {l : List α}, Before x y l → Before (f x) (f y) (l.map f)
  | [], h => h.elim
  | _ :: _, h => by
    rcases h with ⟨rfl, hy⟩ | h
    · exact Or.inl ⟨rfl, List.mem_map_of_mem hy⟩
    · exact Or.inr (before_map f h)

theorem sw_castSucc {m : ℕ} (i : Fin m) : sw i i.castSucc = i.succ := by
  unfold sw; rw [if_pos rfl]

theorem castSucc_ne_succ {m : ℕ} (i : Fin m) : i.castSucc ≠ i.succ := fun e => by
  have := congrArg Fin.val e
  rw [Fin.val_castSucc, Fin.val_succ] at this
  omega

theorem sw_succ {m : ℕ} (i : Fin m) : sw i i.succ = i.castSucc := by
  unfold sw; rw [if_neg (castSucc_ne_succ i).symm, if_pos rfl]

/-- **Jeder Negator wechselt die Parität von `inv`** auf einer vollständigen, wiederholungsfreien
Folge: steht `i+1` vor `i`, sinkt `inv` um eins (`inv_negate_desc`), sonst steigt es um eins
(derselbe Satz, auf `negate i l` angewandt). -/
theorem inv_negate_parity {m : ℕ} (i : Fin m) (l : List (Fin (m + 1))) (hnd : l.Nodup)
    (hall : ∀ v, v ∈ l) : (inv (negate i l) + 1) % 2 = inv l % 2 := by
  rcases Before.total (hall i.succ) (hall i.castSucc) (castSucc_ne_succ i).symm with h | h
  · have := inv_negate_desc i l hnd h
    omega
  · have h' : Before i.succ i.castSucc (negate i l) := by
      have := before_map (sw i) h
      rw [sw_castSucc, sw_succ] at this
      exact this
    have := inv_negate_desc i (negate i l) (negate_nodup i hnd) h'
    rw [negate_negate] at this
    omega

theorem inv_endpoint_parity {m : ℕ} : ∀ (w : List (Fin m)) (l : List (Fin (m + 1))),
    l.Nodup → (∀ v, v ∈ l) → (inv (endpoint w l) + w.length) % 2 = inv l % 2
  | [], l, _, _ => by show (inv l + 0) % 2 = inv l % 2; rw [Nat.add_zero]
  | i :: is, l, hnd, hall => by
    have ih := inv_endpoint_parity is (negate i l) (negate_nodup i hnd) (negate_all i hall)
    have hp := inv_negate_parity i l hnd hall
    show (inv (endpoint is (negate i l)) + (is.length + 1)) % 2 = inv l % 2
    omega

/-- (A0) **Ein Vollkreis hat gerade Länge** — über die Parität von `inv`, ohne `full_length`. -/
theorem full_even {m : ℕ} {w : List (Fin m)} (h : IsFullCycle w) : 2 ∣ w.length := by
  have := inv_endpoint_parity w (origin m) (origin_nodup m)
    (fun v => by show v ∈ List.finRange (m + 1); exact List.mem_finRange v)
  rw [h.closes, inv_origin] at this
  exact Nat.dvd_of_mod_eq_zero (by omega)

-- ============================================================
-- §IV — Φ hebt jeden Vollkreis (A4)
-- ============================================================

/-- (A4, ℕ) **Der Schritt von `sjtN_props`, für jedes Wort mit den fünf Eigenschaften** (HEBUNG;
`sjtN_props` bleibt unverändert). -/
theorem blocks_propsN (n : ℕ) (S : List ℕ) (hS : ∀ s ∈ S, s + 1 < n + 2)
    (hc : endpointN S (List.range (n + 2)) = List.range (n + 2))
    (hnd : (stationsN S (List.range (n + 2))).Nodup)
    (honly : ∀ l ∈ stationsN S (List.range (n + 2)), l.Perm (List.range (n + 2)))
    (hall : ∀ l, l.Perm (List.range (n + 2)) → l ∈ stationsN S (List.range (n + 2)))
    (hev : 2 ∣ S.length) :
    endpointN (blocks (n + 2 + 1) true S) (List.range (n + 2 + 1)) = List.range (n + 2 + 1) ∧
    (stationsN (blocks (n + 2 + 1) true S) (List.range (n + 2 + 1))).Nodup ∧
    (∀ l ∈ stationsN (blocks (n + 2 + 1) true S) (List.range (n + 2 + 1)),
      l.Perm (List.range (n + 2 + 1))) ∧
    (∀ l, l.Perm (List.range (n + 2 + 1)) →
      l ∈ stationsN (blocks (n + 2 + 1) true S) (List.range (n + 2 + 1))) ∧
    2 ∣ (blocks (n + 2 + 1) true S).length := by
  have hg : ∀ v ∈ List.range (n + 2), v < n + 2 := fun v hv => List.mem_range.mp hv
  obtain ⟨h1, h2⟩ := stations_blocks (n + 2) S true (List.range (n + 2)) hS hg
  rw [show topN (n + 2) true = n + 2 from rfl, insertLast_range] at h1 h2
  obtain ⟨t, ht⟩ := hev
  rw [hc, ht, flipN_even, show topN (n + 2) true = n + 2 from rfl, insertLast_range] at h2
  refine ⟨h2, ?_, ?_, ?_, ?_⟩
  · rw [h1]; exact nodup_planN _ true _ hnd
  · intro l hl
    rw [h1, mem_planN] at hl
    obtain ⟨g, hgm, j, hj, rfl⟩ := hl
    exact insertLast_perm (honly g hgm) (by omega)
  · intro l hl
    obtain ⟨g, j, hgp, hj, rfl⟩ := perm_decompose hl
    rw [h1, mem_planN]
    exact ⟨g, hall g hgp, j, by omega, rfl⟩
  · rw [length_blocks _ (by omega), ht]
    exact ⟨(n + 2 + 1) * t, Nat.mul_left_comm _ _ _⟩

/-- **Φ_b auf Negatorwörtern** (`m + 2` Werte → `m + 3` Werte): `b = true` fegt der neue Wert
zuerst nach links. `phi true` ist die Rekursion des Bestandes (`phi_sjt`). -/
def phi (b : Bool) {m : ℕ} (w : List (Fin (m + 1))) : List (Fin (m + 2)) :=
  toFin (m + 2) (blocks (m + 2 + 1) b (w.map Fin.val))

theorem phi_val (b : Bool) {m : ℕ} (w : List (Fin (m + 1))) :
    (phi b w).map Fin.val = blocks (m + 2 + 1) b (w.map Fin.val) := by
  apply toFin_val
  intro j hj
  have := blocks_lt (m + 2 + 1) b (w.map Fin.val) (by omega) (fun s hs => by
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp hs
    have := u.isLt
    omega) j hj
  omega

/-- `phi true` setzt die Rekursion des Bestandes fort. -/
theorem phi_sjt (m : ℕ) : phi true (sjt (m + 1)) = sjt (m + 2) := by
  unfold phi
  rw [sjt_val]
  rfl

/-- (A4) **Φ_true hebt jeden Vollkreis.** -/
theorem phi_full {m : ℕ} {w : List (Fin (m + 1))} (h : IsFullCycle w) :
    IsFullCycle (phi true w) := by
  have hst : (stations w (origin (m + 1))).map (List.map Fin.val) =
      stationsN (w.map Fin.val) (List.range (m + 2)) := by
    rw [stations_val, origin_val]
  have hc : endpointN (w.map Fin.val) (List.range (m + 2)) = List.range (m + 2) := by
    rw [← origin_val, ← endpoint_val, h.closes]
  have hnd : (stationsN (w.map Fin.val) (List.range (m + 2))).Nodup := by
    rw [← hst]; exact h.nodup.map map_val_inj
  have honly : ∀ l ∈ stationsN (w.map Fin.val) (List.range (m + 2)), l.Perm (List.range (m + 2)) := by
    intro l hl
    rw [← hst] at hl
    obtain ⟨l', hl', rfl⟩ := List.mem_map.mp hl
    have := (List.mem_permutations'.mp (h.only_arrangements l' hl')).map Fin.val
    rwa [origin_val] at this
  have hall : ∀ l, l.Perm (List.range (m + 2)) →
      l ∈ stationsN (w.map Fin.val) (List.range (m + 2)) := by
    intro l hl
    have hb : ∀ k ∈ l, k < m + 2 := fun k hk => List.mem_range.mp (hl.mem_iff.mp hk)
    have hv := toFin_val l hb
    have hp : (toFin (m + 2) l).Perm (origin (m + 1)) := perm_of_val (by rw [hv]; exact hl)
    have hm := h.all_arrangements _ (List.mem_permutations'.mpr hp)
    rw [← hst, ← hv]
    exact List.mem_map_of_mem hm
  have hev : 2 ∣ (w.map Fin.val).length := by rw [List.length_map]; exact full_even h
  have hS : ∀ s ∈ w.map Fin.val, s + 1 < m + 2 := fun s hs => by
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp hs
    have := u.isLt
    omega
  obtain ⟨hc', hnd', honly', hall', _⟩ := blocks_propsN m (w.map Fin.val) hS hc hnd honly hall hev
  have hst' : (stations (phi true w) (origin (m + 2))).map (List.map Fin.val) =
      stationsN (blocks (m + 2 + 1) true (w.map Fin.val)) (List.range (m + 2 + 1)) := by
    rw [stations_val, phi_val, origin_val]
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply map_val_inj
    rw [endpoint_val, phi_val, origin_val]; exact hc'
  · exact List.Nodup.of_map _ (hst' ▸ hnd')
  · intro l hl
    apply List.mem_permutations'.mpr
    apply perm_of_val
    exact honly' _ (hst' ▸ List.mem_map_of_mem hl)
  · intro l hl
    have hp := (List.mem_permutations'.mp hl).map Fin.val
    rw [origin_val] at hp
    have := hall' _ hp
    rw [← hst'] at this
    obtain ⟨l', hl', he⟩ := List.mem_map.mp this
    exact (map_val_inj he) ▸ hl'

-- ============================================================
-- §V — A1 und A2 auf Negatorwörtern
-- ============================================================

theorem spiegel_val {n : ℕ} (X : List (Fin n)) :
    (spiegel X).map Fin.val = (X.map Fin.val).map (fun i => n - 1 - i) := by
  unfold spiegel
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro i _
  show n - (i.val + 1) = n - 1 - i.val
  omega

/-- (A1) **Der Spiegel tauscht die Fegerichtung:** `spiegel (Φ_b w) = Φ_{¬b} (spiegel w)`, für
jedes Wort. -/
theorem phi_spiegel (b : Bool) {m : ℕ} (w : List (Fin (m + 1))) :
    spiegel (phi b w) = phi (!b) (spiegel w) := by
  apply map_val_inj
  rw [spiegel_val, phi_val, phi_val, spiegel_val]
  have hS : ∀ s ∈ w.map Fin.val, s + 2 ≤ m + 2 := fun s hs => by
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp hs
    have := u.isLt
    omega
  rw [blocks_spiegelN (m + 2) (w.map Fin.val) b hS]
  rfl

/-- (A1') **Φ_false hebt jeden Vollkreis** — über A1 und `spiegel_full`. -/
theorem phi_false_full {m : ℕ} {w : List (Fin (m + 1))} (h : IsFullCycle w) :
    IsFullCycle (phi false w) := by
  have e := phi_spiegel true (spiegel w)
  rw [spiegel_spiegel, Bool.not_true] at e
  rw [← e]
  exact spiegel_full (phi_full (spiegel_full h))

/-- (A2) **Der Drehsinn tauscht die Fegerichtung und dreht das Wort um `m + 2`**, für jedes Wort
gerader Länge. -/
theorem phi_dreh {m : ℕ} (w : List (Fin (m + 1))) (hev : 2 ∣ w.length) :
    dreh (phi true w) = (phi false (dreh w)).rotate (m + 2) := by
  apply map_val_inj
  unfold dreh
  rw [List.map_reverse, List.map_rotate, phi_val, phi_val, List.map_reverse]
  obtain ⟨t, ht⟩ := hev
  rcases Nat.eq_zero_or_pos t with h0 | hpos
  · subst h0
    have hw : w = [] := List.length_eq_zero_iff.mp (by omega)
    subst hw
    rfl
  · have hd := blocks_drehN (m + 2) t (w.map Fin.val) (by rw [List.length_map, ht])
    have hl : (List.range (m + 2)).length ≤ (blocks (m + 2 + 1) false (w.map Fin.val).reverse).length := by
      rw [List.length_range, length_blocks _ (by omega), List.length_reverse, List.length_map, ht]
      have : 1 ≤ 2 * t := by omega
      calc m + 2 ≤ (m + 2 + 1) * 1 := by omega
        _ ≤ (m + 2 + 1) * (2 * t) := Nat.mul_le_mul_left _ this
    have := rotate_of_append hd hl
    rw [List.length_range] at this
    exact this.symm

-- ============================================================
-- §VI — Zusammenstellung (A5) und Eichungen
-- ============================================================

/-- **Der Satz des Bestandes aus dem gehobenen:** `NegationCycleSJT.sjt_full`, neu bewiesen über
`phi_sjt` und `phi_full` (der Bestandssatz bleibt unverändert). -/
theorem sjt_full_aus_phi : ∀ m : ℕ, IsFullCycle (sjt (m + 1))
  | 0 => sjt1_full
  | m + 1 => phi_sjt m ▸ phi_full (sjt_full_aus_phi m)

/-- (A5) **Der Aufstieg und der Spiegel:** `Φ_true (spiegel w) = spiegel (Φ_false w)`; beide
Seiten sind Vollkreise. -/
theorem aufstieg_spiegel {m : ℕ} {w : List (Fin (m + 1))} (h : IsFullCycle w) :
    phi true (spiegel w) = spiegel (phi false w) ∧ IsFullCycle (phi true (spiegel w)) :=
  ⟨(phi_spiegel false w).symm, phi_full (spiegel_full h)⟩

/-- (A5) **Der Aufstieg und der Drehsinn:** `dreh (Φ_true w) = (Φ_false (dreh w)).rotate (m+2)`;
beide Seiten sind Vollkreise. -/
theorem aufstieg_dreh {m : ℕ} {w : List (Fin (m + 1))} (h : IsFullCycle w) :
    dreh (phi true w) = (phi false (dreh w)).rotate (m + 2) ∧
      IsFullCycle ((phi false (dreh w)).rotate (m + 2)) := by
  have e := phi_dreh w (full_even h)
  exact ⟨e, e ▸ reverse_full (phi_full h)⟩

/-- Eichung: beide Aufstiege des dreiwertigen SJT-Kreises liegen unter den 88 gerichteten. -/
theorem phi_sjt_zwei_gerichtet : phi true (sjt 2) ∈ gerichtet ∧ phi false (sjt 2) ∈ gerichtet := by
  decide +kernel

/-- Eichung: A2 an Günthers Folge (4). -/
theorem phi_dreh_tafelVI4 : dreh (phi true tafelVI4) = (phi false (dreh tafelVI4)).rotate 3 := by
  decide

-- ============================================================
-- Wachen — Axiom-Profile
-- ============================================================

/-! **Wachen.** Ist-Ausgabe des grünen Builds (v4.30.0-rc2), alle 27 Deklarationen. Kein
`Classical.choice`: kein `full_length` (A0 über `inv`), kein offenes `simp` (ein erster
`blocks_drehN` mit `simp at h` in den unmöglichen Fällen zog Choice). -/

/-- info: 'Reformulation.Proemial.AkkretivitaetsBruecke.range_map_rev' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms range_map_rev

/-- info: 'Reformulation.Proemial.AkkretivitaetsBruecke.range_reverse_map_rev' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms range_reverse_map_rev

/-- info: 'Reformulation.Proemial.AkkretivitaetsBruecke.blocks_spiegelN' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms blocks_spiegelN

/-- info: 'Reformulation.Proemial.AkkretivitaetsBruecke.blocks_append' depends on axioms: [propext] -/
#guard_msgs in #print axioms blocks_append

/-- info: 'Reformulation.Proemial.AkkretivitaetsBruecke.blocks_drehN' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms blocks_drehN

/-- info: 'Reformulation.Proemial.AkkretivitaetsBruecke.rotate_of_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms rotate_of_append

/-- info: 'Reformulation.Proemial.AkkretivitaetsBruecke.before_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms before_map

/-- info: 'Reformulation.Proemial.AkkretivitaetsBruecke.sw_castSucc' does not depend on any axioms -/
#guard_msgs in #print axioms sw_castSucc

/-- info: 'Reformulation.Proemial.AkkretivitaetsBruecke.castSucc_ne_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms castSucc_ne_succ

/-- info: 'Reformulation.Proemial.AkkretivitaetsBruecke.sw_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sw_succ

/-- info: 'Reformulation.Proemial.AkkretivitaetsBruecke.inv_negate_parity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms inv_negate_parity

/-- info: 'Reformulation.Proemial.AkkretivitaetsBruecke.inv_endpoint_parity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms inv_endpoint_parity

/-- info: 'Reformulation.Proemial.AkkretivitaetsBruecke.full_even' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms full_even

/-- info: 'Reformulation.Proemial.AkkretivitaetsBruecke.blocks_propsN' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms blocks_propsN

/-- info: 'Reformulation.Proemial.AkkretivitaetsBruecke.phi' does not depend on any axioms -/
#guard_msgs in #print axioms phi

/-- info: 'Reformulation.Proemial.AkkretivitaetsBruecke.phi_val' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms phi_val

/-- info: 'Reformulation.Proemial.AkkretivitaetsBruecke.phi_sjt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms phi_sjt

/-- info: 'Reformulation.Proemial.AkkretivitaetsBruecke.phi_full' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms phi_full

/-- info: 'Reformulation.Proemial.AkkretivitaetsBruecke.spiegel_val' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms spiegel_val

/-- info: 'Reformulation.Proemial.AkkretivitaetsBruecke.phi_spiegel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms phi_spiegel

/-- info: 'Reformulation.Proemial.AkkretivitaetsBruecke.phi_false_full' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms phi_false_full

/-- info: 'Reformulation.Proemial.AkkretivitaetsBruecke.phi_dreh' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms phi_dreh

/-- info: 'Reformulation.Proemial.AkkretivitaetsBruecke.sjt_full_aus_phi' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sjt_full_aus_phi

/-- info: 'Reformulation.Proemial.AkkretivitaetsBruecke.aufstieg_spiegel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms aufstieg_spiegel

/-- info: 'Reformulation.Proemial.AkkretivitaetsBruecke.aufstieg_dreh' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms aufstieg_dreh

/-- info: 'Reformulation.Proemial.AkkretivitaetsBruecke.phi_sjt_zwei_gerichtet' depends on axioms: [propext] -/
#guard_msgs in #print axioms phi_sjt_zwei_gerichtet

/-- info: 'Reformulation.Proemial.AkkretivitaetsBruecke.phi_dreh_tafelVI4' depends on axioms: [propext] -/
#guard_msgs in #print axioms phi_dreh_tafelVI4
end Reformulation.Proemial.AkkretivitaetsBruecke
