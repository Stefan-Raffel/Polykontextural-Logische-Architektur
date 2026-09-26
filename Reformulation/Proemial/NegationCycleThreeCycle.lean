import Reformulation.Proemial.NegationCycleCatalog
import Reformulation.Proemial.NegationCycleSearch

/-!
# Proemial.NegationCycleThreeCycle — die Kreisrelation, wo sie im Vollkreis steht, und Günthers drei Familien

**Stufen, je Satz am Beweis bestimmt** (26.9.2026; ersetzt die modulweite Marke „FOLGERUNG
(Teil 1 bis 3 und die gehobenen Sätze von Teil 4)"):
- `three_iff_adj` — FOLGERUNG — Dreierzyklus genau bei Nachbar-Negatoren, für jedes `m`.
- `no_double` — FOLGERUNG — kein Doppelnegator im Vollkreis ab zwei Negatoren.
- `no_double_wrap` — FOLGERUNG — dasselbe über das Ende; verbraucht `no_double` im Randfall.
- `abstand_zwei`, `abstand_zwei_wrap` — ZUSAMMENSTELLUNG — `three_of_ne2` und
  `no_double(_wrap)` bei zwei Negatoren.
- `verteilung_6_12_6_iff_all`, `verteilungen_vollstaendig_all` (Günthers Familiensatz),
  `gleich_nur_aussen_all` — ZUSAMMENSTELLUNG — die entschiedene Listenfassung über
  `gerichtet` angewandt auf `mem_gerichtet`.
- `zaehlsatz_all` — FOLGERUNG — die Schranken aus den vier Verteilungen.
- **EICHUNG**: `eich_three`, `gegenprobe_katalog` und die Listenfassungen von Teil 4.
Die übrigen Sätze sind nicht einzeln bestimmt. Gebaut auf Anordnung des Architekten
vom 25. September 2026 nach `KorpusRev2/Spec_N5_Kreisrelation.md` (Mathematiker) und der
Sondierung `KorpusRev2/Sondierung_N5_Kreisrelation_Impl.md` samt Nachtrag.

* **K1 — die Quelle.** IGN 1979, am Seitenbild geprüft. Der Katalog (S. 26 f.): `K l` bei
  `N 1·2`, `K r` bei `N 1·2·1·2`. S. 43: „Es ergeben sich so drei Familien von Hamiltonkreisen je
  nach der Häufigkeit des Auftretens der Operatoren" — Tafel (18): 10 oder 5 · 9 oder 9 · 5 oder
  10, dann 9 · 6 · 9, dann 6 · 12 · 6; „Von den drei Hamiltonkreisen, die wir im Folgenden
  anführen, gehört jeder zu einer anderen Familie." S. 48: „weil durch Fehlen des vermittelnden
  N2 nur ein Schein einer vierwertigen Systematik entsteht. In Wirklichkeit stehen 2 zweiwertige
  Systeme von N1 und N3 zusammenhanglos nebeneinander." S. 49: „N2 hat als logisches
  Verbindungsglied mehr zu leisten als die andern beiden Operatoren."
* **K2 — S1: die Kreisrelation entsteht genau dort, wo zwei Negatoren einen Wert teilen.** Für
  jede Wertzahl ergeben zwei verschiedene aufeinanderfolgende Negatoren genau dann einen
  Dreierzyklus, wenn sie Nachbarn sind (`three_iff_adj`). Die verneinende Hälfte hat einen
  Anker: Entfernte Negatoren ergeben eine Involution, zwei getrennte Vertauschungen
  (`invol_of_far`) — Günthers „zusammenhanglos nebeneinander" (S. 48). Die bejahende Hälfte sagt
  er nicht: *ZUORDNUNG.* Den geteilten Wert nennt er an der ausfallenden Stelle „logisches
  Verbindungsglied" (S. 49), an anderer Stelle „vermittelnd" (HKN S. 25). Zopfrelation
  (`NegationCycle.braid`), vermittelnder Wert (`NegationCycle.track_mediates`) und Kreisrelation
  hängen im Bestand an derselben Bedingung; dass Günther sie so bindet, sagt er nur von der
  ausfallenden Seite.
* **K3 — S4: der Grund für eine Regel des Katalogs.** Im Vollkreis folgen ab drei Werten nie
  zwei gleiche Negatoren aufeinander, auch nicht über das Ende (`no_double`, `no_double_wrap`).
  Bei drei Werten gibt es nur `N1` und `N2`, also nur Nachbarn: im Abstand 2 steht in jedem
  Vollkreis ein K (`abstand_zwei`, `abstand_zwei_wrap`). Das ist der Grund dafür, dass
  `NegationCycleCatalog.katalog_general` bei `k = 2` und `k = 4` keine Ausnahme hat — bisher war
  die Regel nur entschieden.
* **K4 — vier Werte: Günthers dritte Familie ist die Klasse „überall K".** Unter den
  vierwertigen Vollkreisen ist „im Abstand 2 überall ein K" dasselbe wie „`N2` an jeder zweiten
  Stelle" und wie „zwölf `N2`", und es ist genau die Verteilung 6-12-6 (`verteilung_6_12_6_iff_all`).
  Günthers Familie (S. 43) ist *QUELLENFEST* als Name und Verteilung; die Bindung an K ist
  unsere, Günther bestimmt die Familie durch Zählen.
* **K5 — Günthers drei Kreise.** Nur der dritte gehört zur Klasse „überall K"
  (`guenthers_drei`). Günther kommentiert das nicht. Auf S. 45 stellt er den dritten Kreis eher
  zum ersten und sagt, worin die Ähnlichkeit besteht: „dass in beiden Fällen drei Sektionen mit
  kontinuierlichem horizontalen Wertwechsel auftreten".
* **K6 — Günthers Familiensatz, bewiesen.** Jeder vierwertige Vollkreis gehört zu einer der
  drei Familien 10-9-5 (bzw. 5-9-10), 9-6-9, 6-12-6 (`verteilungen_vollstaendig_all`); und wenn zwei
  Operatoren gleich oft vorkommen, sind es `N1` und `N3` — „bestenfalls nur für den ersten und
  letzten möglich" (S. 43; `gleich_nur_aussen_all`). Gehoben über `full_iff_mem` und
  `alleB_perm_gerichtet` wie `NegationCycleSymmetry.mirror_all`. „Familie" ist Günthers Wort
  und steht darum im Kopf und in keinem Bezeichner (wie in `NegationCycleSymmetry`, K3); die
  Sätze heissen nach dem Gezählten, der Verteilung.
* **K6a — Günthers Zählsatz (S. 49), bewiesen.** „Ein Index dieser Tatsache ist das Faktum,
  dass in vierwertigen Vollkreisen N2 gelegentlich zwölf Mal auftreten muss, während die
  Operatoren N1 und N3 niemals öfter als zehn Mal benötigt werden und andererseits N2 niemals
  weniger als sechs Mal seine Umtauschfunktion ausüben kann, während N1 und N3 gelegentlich
  nur fünf Mal beansprucht werden" (S. 49, am Seitenbild). Die Schranken gelten für jeden
  vierwertigen Vollkreis (`zaehlsatz_all`, FOLGERUNG aus dem Familiensatz); erreicht werden sie
  von Günthers eigenen Kreisen (`zaehlsatz_erreicht`, EICHUNG). *Was der Satz nicht sagt:* das
  „mehr zu leisten" liegt in den Schranken — N2 hat die höhere Unter- und Obergrenze —, nicht
  in jedem einzelnen Kreis: im zweiten Kreis (9-6-9) kommt N2 seltener vor als N1 und N3
  (`n2_nicht_je_kreis`).
* **K7 — Nicht:** Günthers „kein stabiles Sein" (Definitionen §21, Abschnitt 8); K ist nicht
  der Hamiltonkreis (der Katalog steht auf dem Hamiltonkreis, K ist eine Relation zwischen
  Stationen); keine Beziehung der 16 Kreise „überall K" zu `rueckwaerts_vier`; warum gerade
  6-12-6, ist gemessen und nicht erklärt.

## Axiomprofil

Gemessen am grünen Bau, verbatim in den Wachen am Dateiende. **Kein Satz trägt
`Classical.choice`.** Teil 1 bis 3 tragen `[propext, Quot.sound]`, ausser
`not_three_of_invol`, `endpoint_append_list` und `stations_append_list` (axiomfrei). Die
Listenfassungen von Teil 4 (`decide +kernel` über `gerichtet`) tragen `[propext]`, die
gehobenen `[propext, Quot.sound]`. `IsThree` ist über Wertabbildungen definiert, nicht über
`Equiv.Perm` (Fallstrick 10: `Equiv.swap` und der Submonoid-Abschluss tragen Choice).
-/

namespace Reformulation.Proemial.NegationCycleThreeCycle

open Reformulation.Proemial.NegationCycle
open Reformulation.Proemial.NegationCycleCatalog
open Reformulation.Proemial.NegationCycleTable
open Reformulation.Proemial.NegationCycleSearch

-- ============================================================
-- Teil 1 — S1, für jede Wertzahl
-- ============================================================

section Eins

variable {m : ℕ}

/-- Ein **Dreierzyklus** auf den Werten: drei verschiedene Werte im Kreis, alle übrigen fest.
Über Wertabbildungen, nicht über `Equiv.Perm`. -/
def IsThree (σ : Fin (m + 1) → Fin (m + 1)) : Prop :=
  ∃ a b c : Fin (m + 1), a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ σ a = b ∧ σ b = c ∧ σ c = a ∧
    ∀ x, x ≠ a → x ≠ b → x ≠ c → σ x = x

instance (σ : Fin (m + 1) → Fin (m + 1)) : Decidable (IsThree σ) := by
  unfold IsThree; infer_instance

/-- Nachbarn, aufsteigend (`j = i + 1`), ergeben einen Dreierzyklus: `i → i+2 → i+1 → i`. -/
theorem three_of_adj (i j : Fin m) (h : j.val = i.val + 1) :
    IsThree (fun v => sw j (sw i v)) := by
  have hj : j.val + 1 < m + 1 := by omega
  refine ⟨i.castSucc, ⟨j.val + 1, hj⟩, i.succ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e; have := congrArg Fin.val e; simp only [Fin.val_castSucc] at this; omega
  · intro e; have := congrArg Fin.val e; simp only [Fin.val_succ] at this; omega
  · intro e; have := congrArg Fin.val e; simp only [Fin.val_castSucc, Fin.val_succ] at this; omega
  · apply Fin.ext; rw [sw_val, sw_val]; simp only [Fin.val_castSucc]; split_ifs <;> omega
  · apply Fin.ext; rw [sw_val, sw_val]; simp only [Fin.val_succ]; split_ifs <;> omega
  · apply Fin.ext; rw [sw_val, sw_val]; simp only [Fin.val_succ, Fin.val_castSucc]
    split_ifs <;> omega
  · intro x ha hb hc
    have ha' : x.val ≠ i.val := fun e => ha (Fin.ext (by simp only [Fin.val_castSucc]; exact e))
    have hb' : x.val ≠ j.val + 1 := fun e => hb (Fin.ext e)
    have hc' : x.val ≠ i.val + 1 := fun e => hc (Fin.ext (by simp only [Fin.val_succ]; exact e))
    clear ha hb hc
    apply Fin.ext; rw [sw_val, sw_val]; split_ifs <;> omega

/-- Nachbarn, absteigend (`i = j + 1`), ergeben einen Dreierzyklus: `j → j+1 → j+2 → j`. -/
theorem three_of_adj' (i j : Fin m) (h : i.val = j.val + 1) :
    IsThree (fun v => sw j (sw i v)) := by
  have hi : i.val + 1 < m + 1 := by omega
  refine ⟨j.castSucc, j.succ, ⟨i.val + 1, hi⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e; have := congrArg Fin.val e; simp only [Fin.val_castSucc, Fin.val_succ] at this; omega
  · intro e; have := congrArg Fin.val e; simp only [Fin.val_succ] at this; omega
  · intro e; have := congrArg Fin.val e; simp only [Fin.val_castSucc] at this; omega
  · apply Fin.ext; rw [sw_val, sw_val]; simp only [Fin.val_castSucc, Fin.val_succ]
    split_ifs <;> omega
  · apply Fin.ext; rw [sw_val, sw_val]; simp only [Fin.val_succ]; split_ifs <;> omega
  · apply Fin.ext; rw [sw_val, sw_val]; simp only [Fin.val_castSucc]; split_ifs <;> omega
  · intro x ha hb hc
    have ha' : x.val ≠ j.val := fun e => ha (Fin.ext (by simp only [Fin.val_castSucc]; exact e))
    have hb' : x.val ≠ j.val + 1 := fun e => hb (Fin.ext (by simp only [Fin.val_succ]; exact e))
    have hc' : x.val ≠ i.val + 1 := fun e => hc (Fin.ext e)
    clear ha hb hc
    apply Fin.ext; rw [sw_val, sw_val]; split_ifs <;> omega

/-- Entfernte Negatoren ergeben eine Involution — zwei getrennte Vertauschungen. -/
theorem invol_of_far (i j : Fin m) (h : i.val + 2 ≤ j.val) (v : Fin (m + 1)) :
    sw j (sw i (sw j (sw i v))) = v := by
  rw [comm_far i j h (sw i v), sw_sw, sw_sw]

/-- … in der anderen Reihenfolge ebenso. -/
theorem invol_of_far' (i j : Fin m) (h : j.val + 2 ≤ i.val) (v : Fin (m + 1)) :
    sw j (sw i (sw j (sw i v))) = v := by
  rw [comm_far j i h (sw j (sw i v)), sw_sw, sw_sw]

/-- Eine Involution ist kein Dreierzyklus. -/
theorem not_three_of_invol (σ : Fin (m + 1) → Fin (m + 1)) (h : ∀ v, σ (σ v) = v) :
    ¬ IsThree σ := by
  rintro ⟨a, b, c, _, _, hac, hab, hbc, _, _⟩
  apply hac
  have := h a
  rw [hab, hbc] at this
  exact this.symm

/-- Entfernte Negatoren ergeben keinen Dreierzyklus. -/
theorem not_three_of_far (i j : Fin m) (h : i.val + 2 ≤ j.val) :
    ¬ IsThree (fun v => sw j (sw i v)) :=
  not_three_of_invol _ (invol_of_far i j h)

/-- **S1 als ein Satz:** zwei verschiedene aufeinanderfolgende Negatoren ergeben genau dann
einen Dreierzyklus, wenn sie Nachbarn sind — für jede Wertzahl. -/
theorem three_iff_adj (i j : Fin m) (hij : i ≠ j) :
    IsThree (fun v => sw j (sw i v)) ↔ (j.val = i.val + 1 ∨ i.val = j.val + 1) := by
  have hv : i.val ≠ j.val := fun e => hij (Fin.ext e)
  constructor
  · intro h3
    by_cases h1 : j.val = i.val + 1
    · exact Or.inl h1
    · by_cases h2 : i.val = j.val + 1
      · exact Or.inr h2
      · exfalso
        by_cases h3' : i.val + 2 ≤ j.val
        · exact not_three_of_far i j h3' h3
        · have h4 : j.val + 2 ≤ i.val := by omega
          exact not_three_of_invol _ (invol_of_far' i j h4) h3
  · rintro (h | h)
    · exact three_of_adj i j h
    · exact three_of_adj' i j h

end Eins

/-- **Eichung:** bei drei Werten ist `IsThree` an allen Katalog-Relationen genau Günthers
Kreisrelation, `kat = Kl` oder `kat = Kr`. -/
theorem eich_three : ∀ j < 6, ∀ k ≤ 6,
    (IsThree (rel alt1 j k) ↔ (kat (rel alt1 j k) = some .Kl ∨ kat (rel alt1 j k) = some .Kr)) := by
  decide

-- ============================================================
-- Teil 2 — S2, ab drei Werten
-- ============================================================

section Zwei

variable {m : ℕ}

/-- `endpoint` über einer zusammengesetzten Folge (der allgemeine Fall zu
`NegationCycle.endpoint_append`, der nur `seq ++ [i]` kennt). Die ℕ-Fassung steht in
`NegationCycleSJT` (`endpointN_append`), die Brücke dort ist `endpoint_val`. -/
theorem endpoint_append_list : ∀ (u r : List (Fin m)) (l : List (Fin (m + 1))),
    endpoint (u ++ r) l = endpoint r (endpoint u l)
  | [], _, _ => rfl
  | i :: is, r, l => endpoint_append_list is r (negate i l)

/-- `stations` über einer zusammengesetzten Folge (der allgemeine Fall zu
`NegationCycle.stations_append`). Die ℕ-Fassung steht in `NegationCycleSJT`
(`stationsN_append`), die Brücke dort ist `stations_val`. -/
theorem stations_append_list : ∀ (u r : List (Fin m)) (l : List (Fin (m + 1))),
    stations (u ++ r) l = stations u l ++ stations r (endpoint u l)
  | [], _, _ => rfl
  | i :: is, r, l => by
    show l :: stations (is ++ r) (negate i l) = l :: (stations is (negate i l) ++ _)
    rw [stations_append_list is r (negate i l)]; rfl

/-- Ein Negator auf dem Ausgang ergibt eine Anordnung. -/
theorem negate_mem_perm (j : Fin m) : negate j (origin m) ∈ (origin m).permutations' :=
  List.mem_permutations'.2 (negate_perm j (origin m)
    (Reformulation.Proemial.NegationCycleSJT.origin_nodup m)
    (fun v => by simp only [origin, List.mem_finRange]))

/-- Ab drei Werten gibt es zu jedem Negator einen zweiten, der den Ausgang weder festlässt noch
wie der erste bewegt. -/
theorem negate_origin_ne (hm : 2 ≤ m) (i : Fin m) :
    ∃ j : Fin m, negate j (origin m) ≠ origin m ∧ negate j (origin m) ≠ negate i (origin m) := by
  have key : ∀ j : Fin m, j.val ≠ i.val →
      negate j (origin m) ≠ origin m ∧ negate j (origin m) ≠ negate i (origin m) := by
    intro j hji
    have h1 : ∀ f g : Fin (m + 1) → Fin (m + 1), (origin m).map f = (origin m).map g →
        f j.castSucc = g j.castSucc := fun f g h => (map_eq_iff origin_perm f g).1 h _
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have := h1 (sw j) id (by rw [List.map_id]; exact h)
      have e := congrArg Fin.val this
      rw [sw_val] at e; simp only [Fin.val_castSucc, id] at e; split_ifs at e <;> omega
    · have := h1 (sw j) (sw i) h
      have e := congrArg Fin.val this
      rw [sw_val, sw_val] at e; simp only [Fin.val_castSucc] at e; split_ifs at e <;> omega
  by_cases h0 : i.val = 0
  · exact ⟨⟨1, by omega⟩, key _ (by simp only; omega)⟩
  · exact ⟨⟨0, by omega⟩, key _ (by simp only; omega)⟩

/-- **S2:** ab drei Werten folgen im Vollkreis nie zwei gleiche Negatoren aufeinander. -/
theorem no_double (hm : 2 ≤ m) {w : List (Fin m)} (hw : IsFullCycle w)
    (u v : List (Fin m)) (i : Fin m) : w ≠ u ++ i :: i :: v := by
  intro he
  have hnd := hw.nodup
  have hcl := hw.closes
  rw [he] at hnd hcl
  rw [stations_append_list] at hnd
  rw [endpoint_append_list] at hcl
  have hs : stations (i :: i :: v) (endpoint u (origin m)) =
      endpoint u (origin m) :: negate i (endpoint u (origin m)) ::
        stations v (endpoint u (origin m)) := by
    show _ :: _ :: stations v (negate i (negate i _)) = _
    rw [negate_negate]
  rw [hs] at hnd
  obtain ⟨-, hr, hdis⟩ := List.nodup_append.1 hnd
  cases v with
  | cons k v' =>
    have : endpoint u (origin m) ∈ negate i (endpoint u (origin m)) ::
        stations (k :: v') (endpoint u (origin m)) :=
      List.mem_cons_of_mem _ (List.mem_cons_self ..)
    exact (List.nodup_cons.1 hr).1 this
  | nil =>
    have hx : endpoint u (origin m) = origin m := by
      have : endpoint [i, i] (endpoint u (origin m)) = endpoint u (origin m) := negate_negate i _
      rw [← this]; exact hcl
    cases u with
    | cons k u' =>
      exact hdis (origin m) (List.mem_cons_self ..) (origin m)
        (by rw [hx]; exact List.mem_cons_self ..) rfl
    | nil =>
      obtain ⟨j, hj1, hj2⟩ := negate_origin_ne hm i
      have hmem := hw.all_arrangements _ (negate_mem_perm j)
      rw [he] at hmem
      simp only [List.nil_append, stations, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with h | h
      · exact hj1 h
      · exact hj2 h

/-- **S2 über das Ende:** der letzte und der erste Negator eines Vollkreises sind verschieden. -/
theorem no_double_wrap (hm : 2 ≤ m) {w : List (Fin m)} (hw : IsFullCycle w)
    (v : List (Fin m)) (i : Fin m) : w ≠ i :: (v ++ [i]) := by
  intro he
  cases v with
  | nil => exact no_double hm hw [] [] i he
  | cons k v' =>
    have hnd := hw.nodup
    have hcl := hw.closes
    rw [he] at hnd hcl
    rw [← List.cons_append, stations_append] at hnd
    rw [← List.cons_append, endpoint_append] at hcl
    have hy : endpoint (i :: k :: v') (origin m) = negate i (origin m) := by
      have := congrArg (negate i) hcl
      rw [negate_negate] at this; exact this
    rw [hy] at hnd
    have hin : negate i (origin m) ∈ stations (i :: k :: v') (origin m) :=
      List.mem_cons_of_mem _ (List.mem_cons_self ..)
    exact (List.nodup_append.1 hnd).2.2 _ hin _ (List.mem_singleton_self _) rfl

end Zwei

-- ============================================================
-- Teil 3 — S4, bei drei Werten
-- ============================================================

/-- Bei zwei Negatoren sind verschiedene stets Nachbarn. -/
theorem three_of_ne2 (i j : Fin 2) (h : i ≠ j) : IsThree (fun v => sw j (sw i v)) := by
  have hv : i.val ≠ j.val := fun e => h (Fin.ext e)
  have hi := i.isLt; have hj := j.isLt
  by_cases hij : j.val = i.val + 1
  · exact three_of_adj i j hij
  · exact three_of_adj' i j (by omega)

/-- **S4:** bei drei Werten ist in jedem Vollkreis die Relation zweier aufeinanderfolgender
Negatoren ein Dreierzyklus — ohne Aufzählung. -/
theorem abstand_zwei (w : List (Fin 2)) (hw : IsFullCycle w) (u v : List (Fin 2)) (i j : Fin 2)
    (he : w = u ++ i :: j :: v) : IsThree (fun x => sw j (sw i x)) := by
  refine three_of_ne2 i j fun hij => ?_
  subst hij; exact no_double (le_refl 2) hw u v i he

/-- … auch über das Ende. -/
theorem abstand_zwei_wrap (w : List (Fin 2)) (hw : IsFullCycle w) (v : List (Fin 2)) (i j : Fin 2)
    (he : w = i :: (v ++ [j])) : IsThree (fun x => sw i (sw j x)) := by
  refine three_of_ne2 j i fun hij => ?_
  subst hij; exact no_double_wrap (le_refl 2) hw v j he

/-- **Eichung gegen den Katalog:** im Wechselweg sind die Relationen im Abstand 2 und 4
Dreierzyklen (verträglich mit `NegationCycleCatalog.katalog_general`). -/
theorem gegenprobe_katalog : ∀ j < 6, IsThree (rel alt1 j 2) ∧ IsThree (rel alt1 j 4) := by
  decide

-- ============================================================
-- Teil 4 — vier Werte, Günthers Familien
-- ============================================================

/-- Zwei Negatoren bei vier Werten sind entfernt: `N1` und `N3`. -/
def far (a b : Fin 3) : Bool := (a.val + 2 == b.val) || (b.val + 2 == a.val)

/-- Ein Vollkreis hat einen entfernten Nachbarschritt (zyklisch gelesen). -/
def hasFar : List (Fin 3) → Bool
  | [] => false
  | s@(x :: _) => ((s ++ [x]).zip ((s ++ [x]).drop 1)).any (fun p => far p.1 p.2)

/-- `N2` (Wert 1) an jeder zweiten Stelle, an den geraden oder an den ungeraden. -/
def altN2 (s : List (Fin 3)) : Bool :=
  ((List.range s.length).all fun k => k % 2 == 1 || s.getD k 0 == 1) ||
  ((List.range s.length).all fun k => k % 2 == 0 || s.getD k 0 == 1)

/-- Die Verteilung der Operatoren `N1`, `N2`, `N3` (Günthers Tafel (18)). -/
def vert (s : List (Fin 3)) : ℕ × ℕ × ℕ := (s.count 0, s.count 1, s.count 2)

/-- Eichung: 56 der 88 gerichteten Vollkreise haben einen entfernten Schritt, 32 keinen. -/
theorem zaehlung_vier : (gerichtet.filter hasFar).length = 56 ∧
    (gerichtet.filter (fun s => !hasFar s)).length = 32 := by decide +kernel

/-- Eichung: bis auf Drehsinn 28 und 16. -/
theorem zaehlung_vier_ungerichtet : (alleKreise.filter hasFar).length = 28 ∧
    (alleKreise.filter (fun s => !hasFar s)).length = 16 := by decide +kernel

/-- Eichung: „überall K" genau dann, wenn `N2` an jeder zweiten Stelle steht. -/
theorem ueberall_K_iff_alt : ∀ s ∈ gerichtet, (!hasFar s) = altN2 s := by decide +kernel

/-- Eichung: „überall K" genau dann, wenn genau zwölf `N2`. -/
theorem zwoelf_iff : ∀ s ∈ gerichtet, (!hasFar s) = (s.count 1 == 12) := by decide +kernel

/-- Eichung: „überall K" hat die Verteilung 6-12-6. -/
theorem verteilung : ∀ s ∈ gerichtet, hasFar s = false → vert s = (6, 12, 6) := by
  decide +kernel

/-- Eichung: Günthers dritter Kreis gehört zur Klasse „überall K", der erste und zweite nicht. -/
theorem guenthers_drei : kreis3 ∈ gerichtet ∧ hasFar kreis3 = false ∧
    kreis1 ∈ gerichtet ∧ hasFar kreis1 = true ∧ kreis2 ∈ gerichtet ∧ hasFar kreis2 = true := by
  decide +kernel

/-- Eichung: die dritte Familie ist genau die Klasse „überall K". -/
theorem verteilung_6_12_6_iff : ∀ s ∈ gerichtet, (vert s == (6, 12, 6)) = (!hasFar s) := by
  decide +kernel

/-- Eichung: jeder Vollkreis gehört zu einer der drei Familien (Tafel (18)). -/
theorem verteilungen_vollstaendig : ∀ s ∈ gerichtet,
    vert s = (10, 9, 5) ∨ vert s = (5, 9, 10) ∨ vert s = (9, 6, 9) ∨ vert s = (6, 12, 6) := by
  decide +kernel

/-- Eichung: gleich oft können nur `N1` und `N3` vorkommen. -/
theorem gleich_nur_aussen : ∀ s ∈ gerichtet, s.count 0 ≠ s.count 1 ∧ s.count 1 ≠ s.count 2 := by
  decide +kernel

/-- Jeder vierwertige Vollkreis steht in der Tafel. -/
theorem mem_gerichtet (seq : List (Fin 3)) (h : IsFullCycle seq) : seq ∈ gerichtet :=
  (List.Perm.mem_iff alleB_perm_gerichtet).mpr ((full_iff_mem seq).mp h)

/-- **Für jeden vierwertigen Vollkreis:** „überall K" genau dann, wenn `N2` an jeder zweiten
Stelle steht. -/
theorem ueberall_K_iff_alt_all (seq : List (Fin 3)) (h : IsFullCycle seq) :
    (!hasFar seq) = altN2 seq :=
  ueberall_K_iff_alt seq (mem_gerichtet seq h)

/-- **Für jeden vierwertigen Vollkreis:** „überall K" genau dann, wenn zwölf `N2`. -/
theorem zwoelf_iff_all (seq : List (Fin 3)) (h : IsFullCycle seq) :
    (!hasFar seq) = (seq.count 1 == 12) :=
  zwoelf_iff seq (mem_gerichtet seq h)

/-- **Günthers dritte Familie ist die Klasse „überall K"** — für jeden vierwertigen Vollkreis. -/
theorem verteilung_6_12_6_iff_all (seq : List (Fin 3)) (h : IsFullCycle seq) :
    (vert seq == (6, 12, 6)) = (!hasFar seq) :=
  verteilung_6_12_6_iff seq (mem_gerichtet seq h)

/-- **Günthers Familiensatz** (IGN S. 43): jeder vierwertige Vollkreis gehört zu einer der drei
Familien. -/
theorem verteilungen_vollstaendig_all (seq : List (Fin 3)) (h : IsFullCycle seq) :
    vert seq = (10, 9, 5) ∨ vert seq = (5, 9, 10) ∨ vert seq = (9, 6, 9) ∨
      vert seq = (6, 12, 6) :=
  verteilungen_vollstaendig seq (mem_gerichtet seq h)

/-- **„Bestenfalls nur für den ersten und letzten"** (S. 43): in jedem vierwertigen Vollkreis
kommt `N2` nie so oft vor wie `N1` oder `N3`. -/
theorem gleich_nur_aussen_all (seq : List (Fin 3)) (h : IsFullCycle seq) :
    seq.count 0 ≠ seq.count 1 ∧ seq.count 1 ≠ seq.count 2 :=
  gleich_nur_aussen seq (mem_gerichtet seq h)


/-- **Günthers Zählsatz** (IGN S. 49): in jedem vierwertigen Vollkreis kommen `N1` und `N3`
mindestens fünf- und höchstens zehnmal vor, `N2` mindestens sechs- und höchstens zwölfmal. -/
theorem zaehlsatz_all (seq : List (Fin 3)) (h : IsFullCycle seq) :
    5 ≤ seq.count 0 ∧ seq.count 0 ≤ 10 ∧ 5 ≤ seq.count 2 ∧ seq.count 2 ≤ 10 ∧
      6 ≤ seq.count 1 ∧ seq.count 1 ≤ 12 := by
  rcases verteilungen_vollstaendig_all seq h with e | e | e | e <;>
  · simp only [vert, Prod.mk.injEq] at e
    obtain ⟨h0, h1, h2⟩ := e
    rw [h0, h1, h2]
    decide

/-- Eichung: die Schranken werden erreicht, von Günthers eigenen Kreisen — `N1` zehnmal und
`N3` fünfmal im ersten, gespiegelt umgekehrt; `N2` sechsmal im zweiten, zwölfmal im dritten. -/
theorem zaehlsatz_erreicht :
    IsFullCycle kreis1 ∧ kreis1.count 0 = 10 ∧ kreis1.count 2 = 5 ∧
    IsFullCycle (kreis1.map Fin.rev) ∧ (kreis1.map Fin.rev).count 0 = 5 ∧
      (kreis1.map Fin.rev).count 2 = 10 ∧
    IsFullCycle kreis2 ∧ kreis2.count 1 = 6 ∧
    IsFullCycle kreis3 ∧ kreis3.count 1 = 12 :=
  ⟨kreis1_full, by decide, by decide, kreis1_mirror_full, by decide, by decide,
    kreis2_full, by decide, kreis3_full, by decide⟩

/-- Eichung: „mehr zu leisten" heisst nicht „in jedem Kreis öfter" — im zweiten Kreis kommt `N2`
seltener vor als `N1` und `N3`. -/
theorem n2_nicht_je_kreis :
    IsFullCycle kreis2 ∧ kreis2.count 1 < kreis2.count 0 ∧ kreis2.count 1 < kreis2.count 2 :=
  ⟨kreis2_full, by decide, by decide⟩

-- ============================================================
-- Wachen
-- ============================================================

/-- info: 'Reformulation.Proemial.NegationCycleThreeCycle.three_of_adj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms three_of_adj

/-- info: 'Reformulation.Proemial.NegationCycleThreeCycle.three_of_adj'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms three_of_adj'

/-- info: 'Reformulation.Proemial.NegationCycleThreeCycle.invol_of_far' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms invol_of_far

/-- info: 'Reformulation.Proemial.NegationCycleThreeCycle.invol_of_far'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms invol_of_far'

/-- info: 'Reformulation.Proemial.NegationCycleThreeCycle.not_three_of_invol' does not depend on any axioms -/
#guard_msgs in #print axioms not_three_of_invol

/-- info: 'Reformulation.Proemial.NegationCycleThreeCycle.not_three_of_far' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms not_three_of_far

/-- info: 'Reformulation.Proemial.NegationCycleThreeCycle.three_iff_adj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms three_iff_adj

/-- info: 'Reformulation.Proemial.NegationCycleThreeCycle.eich_three' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms eich_three

/-- info: 'Reformulation.Proemial.NegationCycleThreeCycle.endpoint_append_list' does not depend on any axioms -/
#guard_msgs in #print axioms endpoint_append_list

/-- info: 'Reformulation.Proemial.NegationCycleThreeCycle.stations_append_list' does not depend on any axioms -/
#guard_msgs in #print axioms stations_append_list

/-- info: 'Reformulation.Proemial.NegationCycleThreeCycle.negate_mem_perm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms negate_mem_perm

/-- info: 'Reformulation.Proemial.NegationCycleThreeCycle.negate_origin_ne' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms negate_origin_ne

/-- info: 'Reformulation.Proemial.NegationCycleThreeCycle.no_double' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms no_double

/-- info: 'Reformulation.Proemial.NegationCycleThreeCycle.no_double_wrap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms no_double_wrap

/-- info: 'Reformulation.Proemial.NegationCycleThreeCycle.three_of_ne2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms three_of_ne2

/-- info: 'Reformulation.Proemial.NegationCycleThreeCycle.abstand_zwei' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms abstand_zwei

/-- info: 'Reformulation.Proemial.NegationCycleThreeCycle.abstand_zwei_wrap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms abstand_zwei_wrap

/-- info: 'Reformulation.Proemial.NegationCycleThreeCycle.gegenprobe_katalog' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms gegenprobe_katalog

/-- info: 'Reformulation.Proemial.NegationCycleThreeCycle.zaehlung_vier' depends on axioms: [propext] -/
#guard_msgs in #print axioms zaehlung_vier

/-- info: 'Reformulation.Proemial.NegationCycleThreeCycle.zaehlung_vier_ungerichtet' depends on axioms: [propext] -/
#guard_msgs in #print axioms zaehlung_vier_ungerichtet

/-- info: 'Reformulation.Proemial.NegationCycleThreeCycle.ueberall_K_iff_alt' depends on axioms: [propext] -/
#guard_msgs in #print axioms ueberall_K_iff_alt

/-- info: 'Reformulation.Proemial.NegationCycleThreeCycle.zwoelf_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms zwoelf_iff

/-- info: 'Reformulation.Proemial.NegationCycleThreeCycle.verteilung' depends on axioms: [propext] -/
#guard_msgs in #print axioms verteilung

/-- info: 'Reformulation.Proemial.NegationCycleThreeCycle.guenthers_drei' depends on axioms: [propext] -/
#guard_msgs in #print axioms guenthers_drei

/-- info: 'Reformulation.Proemial.NegationCycleThreeCycle.verteilung_6_12_6_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms verteilung_6_12_6_iff

/-- info: 'Reformulation.Proemial.NegationCycleThreeCycle.verteilungen_vollstaendig' depends on axioms: [propext] -/
#guard_msgs in #print axioms verteilungen_vollstaendig

/-- info: 'Reformulation.Proemial.NegationCycleThreeCycle.gleich_nur_aussen' depends on axioms: [propext] -/
#guard_msgs in #print axioms gleich_nur_aussen

/-- info: 'Reformulation.Proemial.NegationCycleThreeCycle.mem_gerichtet' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms mem_gerichtet

/-- info: 'Reformulation.Proemial.NegationCycleThreeCycle.ueberall_K_iff_alt_all' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ueberall_K_iff_alt_all

/-- info: 'Reformulation.Proemial.NegationCycleThreeCycle.zwoelf_iff_all' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms zwoelf_iff_all

/-- info: 'Reformulation.Proemial.NegationCycleThreeCycle.verteilung_6_12_6_iff_all' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms verteilung_6_12_6_iff_all

/-- info: 'Reformulation.Proemial.NegationCycleThreeCycle.verteilungen_vollstaendig_all' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms verteilungen_vollstaendig_all

/-- info: 'Reformulation.Proemial.NegationCycleThreeCycle.gleich_nur_aussen_all' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms gleich_nur_aussen_all

/-- info: 'Reformulation.Proemial.NegationCycleThreeCycle.zaehlsatz_all' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms zaehlsatz_all

/-- info: 'Reformulation.Proemial.NegationCycleThreeCycle.zaehlsatz_erreicht' depends on axioms: [propext] -/
#guard_msgs in #print axioms zaehlsatz_erreicht

/-- info: 'Reformulation.Proemial.NegationCycleThreeCycle.n2_nicht_je_kreis' depends on axioms: [propext] -/
#guard_msgs in #print axioms n2_nicht_je_kreis

end Reformulation.Proemial.NegationCycleThreeCycle
