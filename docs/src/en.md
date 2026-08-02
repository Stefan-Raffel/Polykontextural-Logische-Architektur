---
lang: en
is-en: true
pagetitle: "The Mathematical Shape of the Architecture — PKL Rev2"
title: "The Mathematical Shape of the Architecture"
subtitle: "Polycontextural Logic in Lean 4 and Mathlib — Edition PKL Rev2"
dateline: "Translation of the German edition of 1 August 2026 · translated 1 August 2026 · All figures as of commit `e5ef3d7` · Edition Rev2"
description: "Polycontextural logic in Lean 4 and Mathlib. Edition PKL Rev2: two axes per claim, the series of bounds D–E4, the layer of applications with measured consumption, ledger and register of posits, domain separation."
abstract: |
  ::: callout
  **On the standing of this text.** The German edition is the original; this is its
  translation, and it carries its own date. Where the two diverge, the German edition holds
  and the divergence is a translation backlog, not a contradiction between two originals.
  Lean names, commands, axiom profiles and measured figures are not translated.
  :::
toc-title: "Contents"
toc-label: "Table of contents"
---

---

## What this paper is about {#about}

It is about a formalisation that labels its own claims, and about a reviewing practice meant
to be transferable. Its subject is the reformulation of Gotthard Günther's polycontextural
logic in a type-theoretic proof environment.

The project works with one definition, and it stands first — quoted from `README.md` at
commit `e5ef3d7`, where it is at home and not here. The binding wording is German; this is a
translation of it:

::: callout
A structure is **formally operative polycontextural** if it carries a family of local
contextures on which the relevant operations act classically or locally classically, and if
in addition a machine-checked theorem shows that the global interplay of these local
operations is not generable by any single intra-contextural term calculus.
:::

This definition is narrower than the world-picture Definition 6 of the source and stronger
than mere many-valuedness or plurality of roles. It is the measure for everything that
follows.

## Two axes per claim {#axes}

The previous edition labelled every claim by its **kind**. That no longer suffices.

**First axis — the kind:**

- **proved** — machine-verified theorem
- **measured** — machine-counted figure
- **computed** — exact calculation outside the corpus
- **posited** — explicit premise
- **source-verified** — verbatim in Günther, with citation
- **interpretation** — assignment of formal to conceptual
- **programme** — named, not built

**Second axis — the domain**, measured at the import closures and not at the directory:

- **aggregate** — inside the closure of the five default targets; the axiom gate checks it at
  build time
- **call target** — outside that closure, but reached by at least one call target; no gate,
  no assurance of gap-freeness
- **covered by no target** — in the tree, reached by no closure; no build touches it

Across these stands a mark that is not a closure value: **frozen** designates the branch
`PathC/`, shut down with explicit thawing conditions. A frozen module can nevertheless be
built — two of eighteen are reached through a call target.

The word *standalone* is deliberately avoided here. The filing convention of the corpus uses
it for a file that carries a posit and is consumed by no aggregate theorem; that is a
different question, and three such files are built today.

The reason for the second axis is not tidiness. **Proved** means something different in the
aggregate than in a call target: there a machine barrier applies, here it does not. A paper
that carries theorems of both domains without distinction claims for the one an assurance
that only the other has.

The two columns of the definition ledger — carrier status and assignment status — are a third
thing: they classify **carriers**, whereas the labels here classify **claims in running
text**. The ledger table is in `docs/definition-ledger.md` and is not repeated here.

---

## What this edition changes relative to the first {#changes}

The first edition is dated 24 July 2026 and measures all its figures at commit `e89ab47`. It
remains reachable under `docs/rev1/` and is not updated.

| | Edition Rev1 (24 July) | this edition (1 August) |
|---|---|---|
| labelling | one axis (kind) | **two axes** (kind and domain) |
| concept assignment | spread through running text | **compiler-checked ledger**, 19 of 19 paragraphs |
| posits | named | **registered**, with class and exit criterion |
| domain separation | not carried | **default targets, call targets, frozen, covered by no target** |
| applications | none | **two**, consumption measured at the proof term |
| morphogram bridge | programme | **three theorems, two definitions, one open row** |
| replicability | build on one machine | **build from a fresh, unauthenticated clone** |
| access | private | **public, Apache-2.0 and CC-BY-4.0** |

**What has not been added, and it stands here so that it need not be searched for:** the
proemial relation is not formalised; the compound contexture is present as a number sequence
and not built as a concept; the strong Definition 6 is open and is carried as open (ledger row
L06-1, carrier status `Open`).

---

## I · The ground: a combinatorics prior to logic {#i}

At the very bottom lies a structure that is not yet a logic: the kenogrammatic layer, a
combinatorics of empty places. Finite sequences are classified solely by which places repeat
which. No values, no negation, no truth; only distinguishability and repetition. Everything
later is an assignment on these patterns.

Günther distinguishes three granularities (**source-verified**). The **proto** structure
counts only how many distinct marks occur. The **deutero** structure records the repetition
profile. The **trito** structure retains the position-exact pattern. Only the third is fine
enough to serve as the ground of a logic: an assignment must be able to say which places carry
the same value.

<figure class="fig wide">
<div class="fig-scroll">
<svg viewBox="0 0 700 250" role="img" aria-label="The same sequence in three granularities">
  <defs><marker id="ah1" markerWidth="8" markerHeight="8" refX="7" refY="4" orient="auto">
    <path d="M0,0 L8,4 L0,8 z" fill="var(--stroke)"/></marker></defs>

  <text class="txs mut" x="112" y="30" text-anchor="end">sequence 1</text>
  <text class="txs mut" x="112" y="70" text-anchor="end">sequence 2</text>
  <text class="txs mut" x="112" y="110" text-anchor="end">normal form</text>

  <g class="box" fill="var(--f03)">
    <rect x="130" y="8"  width="42" height="32"/><rect x="180" y="8"  width="42" height="32"/>
    <rect x="230" y="8"  width="42" height="32"/><rect x="280" y="8"  width="42" height="32"/>
    <rect x="330" y="8"  width="42" height="32"/>
    <rect x="130" y="48" width="42" height="32"/><rect x="180" y="48" width="42" height="32"/>
    <rect x="230" y="48" width="42" height="32"/><rect x="280" y="48" width="42" height="32"/>
    <rect x="330" y="48" width="42" height="32"/>
  </g>
  <g class="box" fill="var(--f12)">
    <rect x="130" y="88" width="42" height="32"/><rect x="180" y="88" width="42" height="32"/>
    <rect x="230" y="88" width="42" height="32"/><rect x="280" y="88" width="42" height="32"/>
    <rect x="330" y="88" width="42" height="32"/>
  </g>
  <g class="t i" text-anchor="middle">
    <text x="151" y="30">a</text><text x="201" y="30">b</text><text x="251" y="30">b</text>
    <text x="301" y="30">a</text><text x="351" y="30">c</text>
    <text x="151" y="70">x</text><text x="201" y="70">y</text><text x="251" y="70">y</text>
    <text x="301" y="70">x</text><text x="351" y="70">z</text>
  </g>
  <g class="t" text-anchor="middle">
    <text x="151" y="110">0</text><text x="201" y="110">1</text><text x="251" y="110">1</text>
    <text x="301" y="110">0</text><text x="351" y="110">2</text>
  </g>

  <rect class="box" x="110" y="150" width="160" height="46" rx="5" fill="var(--f03)"/>
  <rect class="box" x="285" y="150" width="160" height="46" rx="5" fill="var(--f08)"/>
  <rect class="box" x="460" y="150" width="180" height="46" rx="5" fill="var(--f16)"/>
  <g text-anchor="middle">
    <text class="ts b" x="190" y="169">proto</text><text class="txs" x="190" y="185">3 marks</text>
    <text class="ts b" x="365" y="169">deutero</text><text class="txs" x="365" y="185">2, 2, 1</text>
    <text class="ts b" x="550" y="169">trito</text><text class="txs" x="550" y="185">0, 1, 1, 0, 2</text>
  </g>
  <line class="ln" x1="200" y1="222" x2="545" y2="222" marker-end="url(#ah1)"/>
  <text class="txs mut" x="372" y="240" text-anchor="middle">coarser → finer</text>
</svg>
</div>
<figcaption><span class="fignum">Figure 1</span> — The same sequence in three granularities:
proto, deutero and trito as an increasingly fine classification. The coarser ones are quotients
of the finest; only the finest can say which places carry the same value.</figcaption>
</figure>

Formally the trito structure is represented by a normal form: a sequence of natural numbers
beginning with `0` in which each new mark exceeds the previous maximum by exactly one — known
in combinatorics as a *restricted growth string*. The predicate is decidable, and the
canonisation is built as a procedure, not asserted (**proved · aggregate**; ledger row L16-1,
`K.relabel`, axiom-free profile).

### The built-in directional asymmetry

The maps between patterns are not symmetric. A pattern whose largest mark is `k` has exactly
`k+2` extensions — it repeats one of the existing marks or introduces a new one.
**Retraction, by contrast, is unique**: delete the last place and precisely one pattern
remains (**computed**).

This is no notational nicety but the structure itself: **ascent chooses, descent computes.**
Between the two directions lies not a change of sign but a difference in the kind of
determinacy. Günther calls one direction *evolutive*, the other *emanative*
(**source-verified**).

<figure class="fig wide">
<div class="fig-scroll">
<svg viewBox="0 0 700 260" role="img" aria-label="Retraction unique, extension branching">
  <defs><marker id="ah2" markerWidth="8" markerHeight="8" refX="7" refY="4" orient="auto">
    <path d="M0,0 L8,4 L0,8 z" fill="var(--stroke)"/></marker></defs>

  <g class="box" fill="var(--f03)">
    <rect x="20" y="116" width="30" height="28"/><rect x="54" y="116" width="30" height="28"/>
    <rect x="88" y="116" width="30" height="28"/>
  </g>
  <g class="ts" text-anchor="middle">
    <text x="35" y="135">0</text><text x="69" y="135">1</text><text x="103" y="135">1</text>
  </g>

  <line class="ln" x1="270" y1="130" x2="135" y2="130" marker-end="url(#ah2)"/>
  <text class="txs" x="203" y="121" text-anchor="middle">emanative</text>
  <text class="txs i mut" x="203" y="146" text-anchor="middle">unique</text>

  <text class="txs mut" x="278" y="103" text-anchor="start">pattern</text>
  <g class="box" fill="var(--f12)">
    <rect x="280" y="116" width="30" height="28"/><rect x="314" y="116" width="30" height="28"/>
    <rect x="348" y="116" width="30" height="28"/><rect x="382" y="116" width="30" height="28"/>
  </g>
  <g class="ts" text-anchor="middle">
    <text x="295" y="135">0</text><text x="329" y="135">1</text>
    <text x="363" y="135">1</text><text x="397" y="135">0</text>
  </g>

  <path class="ln" d="M418,130 C470,130 470,40 520,40"   marker-end="url(#ah2)"/>
  <path class="ln" d="M418,130 L520,130"                  marker-end="url(#ah2)"/>
  <path class="ln" d="M418,130 C470,130 470,220 520,220"  marker-end="url(#ah2)"/>

  <g class="box" fill="var(--f03)">
    <rect x="533" y="26"  width="26" height="28"/><rect x="562" y="26"  width="26" height="28"/>
    <rect x="591" y="26"  width="26" height="28"/><rect x="620" y="26"  width="26" height="28"/>
    <rect x="533" y="116" width="26" height="28"/><rect x="562" y="116" width="26" height="28"/>
    <rect x="591" y="116" width="26" height="28"/><rect x="620" y="116" width="26" height="28"/>
    <rect x="533" y="206" width="26" height="28"/><rect x="562" y="206" width="26" height="28"/>
    <rect x="591" y="206" width="26" height="28"/><rect x="620" y="206" width="26" height="28"/>
  </g>
  <g class="box" fill="var(--f20)">
    <rect x="649" y="26"  width="26" height="28"/>
    <rect x="649" y="116" width="26" height="28"/>
    <rect x="649" y="206" width="26" height="28"/>
  </g>
  <g class="txs" text-anchor="middle">
    <text x="546" y="45">0</text><text x="575" y="45">1</text><text x="604" y="45">1</text>
    <text x="633" y="45">0</text><text x="662" y="45">0</text>
    <text x="546" y="135">0</text><text x="575" y="135">1</text><text x="604" y="135">1</text>
    <text x="633" y="135">0</text><text x="662" y="135">1</text>
    <text x="546" y="225">0</text><text x="575" y="225">1</text><text x="604" y="225">1</text>
    <text x="633" y="225">0</text><text x="662" y="225">2</text>
  </g>

  <text class="txs" x="466" y="14" text-anchor="middle">evolutive</text>
  <text class="txs i mut" x="466" y="27" text-anchor="middle">branching</text>
</svg>
</div>
<figcaption><span class="fignum">Figure 2</span> — Retraction unique, extension branching. A
pattern whose largest mark is <em>k</em> has <em>k</em> + 2 extensions — any existing mark or a
new one — and exactly one retraction (<strong>computed</strong>).</figcaption>
</figure>

### The morphogram bridge

On the normal form sits pattern identity: two sequences carry the same morphogram if their
normal forms agree. The corpus carries six ledger rows for paragraph 16, three of them with
theorem character (**proved · aggregate**):

| Row | Carrier | Kind | Profile |
|---|---|---|---|
| L16-1 | `K.relabel` | definition | axiom-free |
| L16-2 | `K.rgs_unique_of_pattern` | theorem | `[propext, Quot.sound]` |
| L16-3 | `KM.SamePattern` | definition | — |
| L16-4 | `KM.samePattern_iff_pattern` | theorem | `[propext, Classical.choice, Quot.sound]` |
| L16-5 | `KM.samePattern_iff_common_nf` | theorem | `[propext, Classical.choice, Quot.sound]` |
| L16-6 | — | **open** | value assignment of morphograms not formalised |

**No quotient type.** The bridge is built as a normal-form semantics, not as a quotient; that
was a construction decision and not an embarrassment. L16-5 carries the note that the
characterisation via the common normal form depends on `List ℕ`, whereas L16-4 is
type-independent. The open row L16-6 stays open and appears in §X.

---

## II · Contextures: two discontexturalities, one of them proved {#ii}

A contexture is an assignment on the ground with the rank of a logic of its own.

### 1 · What discontexturality is not

Günther's most elementary case of discontexturality is the opposition of Being and Nothing —
and these two are for him **isomorphic** (**source-verified**). Between them there is a
complete, structure-preserving map, and they are discontextural nonetheless.

From this follows the formalisation decision that carries this paper: discontexturality
appears **not** as the non-existence of a map, but as **non-generability in the term clone** —
as the impossibility of assembling a mediating operation from intra-contextural means. What is
missing is not the map, but the path to it from within.

Two short forms are thereby excluded and are carried in the corpus as a construction
prohibition: `Disjoint K₁ K₂` fails because the elementary contextures overlap pairwise in
exactly one value and this overlap carries the proofs; `¬ ∃ f : K₁ → K₂` fails at the basic
case Being/Nothing.

### 2 · The first relation: symmetric, and proved

Günther names two fundamental relations. The first is the **exchange relation** between
elementary contextures: an unordered pair, symmetric, without directional sense
(**source-verified**).

::: theorem
[Theorem (E3).]{.label} For every `m ≥ 4`, a contexture-preserving, locally classical operation on
`m` values lies in the clone of the intra-contextural connectives if and only if it is the
minimum or the maximum.
(**proved · aggregate**; `GeneralCloneBound.locally_classical_in_clone_iff`)
:::

This is a **characterisation**, not an existence claim: the set of non-assemblable operations
is not merely non-empty but completely determined.

### 3 · The second relation: asymmetric, and divided

The second relation holds between contexture and trans-contexturality. Its standing is a
divided result: the **structural** part is available as a theorem, the **conceptual** part
remains modelling — that a change of stage is a change of contexture is closed by no theorem.
A contextural boundary never closes by theorem alone, but by definition plus theorem
(**posited**, marked as such in the corpus).

### 4 · Where the posit sits

::: callout
A two-element set of neighbouring values is an elementary contexture in Günther's sense.
(**posited** — the load-bearing choice of the entire series of bounds)
:::

There is a substantive reason for this choice, and it is not cut to fit after the fact: a
two-element set is closed under the local operations if and only if its two elements are
comparable. On incomparable pairs the minimum leaves the set — then it is no self-contained
connection and no contexture in the sense of the definitions. **The limit of the formalisation
lies in the concept, not in the proof.**

---

## III · The mode of proof: the differential {#iii}

How does one prove what is inalienably absent from a structure, without the self-contradiction
of a system certifying its own limit from within? Not positively within one system, but
**differentially between two**. For each structural feature a poor class is named and a pair
is exhibited: over all instances of the poor class the feature is impossible — as a
universally quantified theorem — and a rich witness carries it.

| the hard half | the easy half |
|---|---|
| `X` is impossible — universally quantified | `X` is exhibited — a construction |
| all strict orders, the generated clone | one concrete structure, built internally |

Three marks discipline the mode. **First**, the poor model is built internally, not asserted
in the metalanguage. **Second**, the result is conditional relative to the posited premises;
it symmetrises the sceptic, it does not compel him. **Third**, what is proved is the form,
never the naming — that a contexture-relative choice of operation is unreachable from local
means is a theorem; that this choice is called *mediation* remains **interpretation**. The
file in the corpus is therefore named `NonUniformCloneBound` and not `Mediation`.

<figure class="fig wide">
<div class="fig-scroll">
<svg viewBox="0 0 700 170" role="img" aria-label="Poor class and rich witness">
  <defs><marker id="ah3" markerWidth="9" markerHeight="9" refX="8" refY="4.5" orient="auto">
    <path d="M0,0 L9,4.5 L0,9 z" fill="var(--stroke)"/></marker></defs>

  <rect class="box" x="15" y="18" width="290" height="134" rx="6" fill="var(--f12)"/>
  <text class="t b" x="160" y="45" text-anchor="middle">poor class</text>
  <text class="ts mut" x="160" y="66" text-anchor="middle">all strict orders,</text>
  <text class="ts mut" x="160" y="81" text-anchor="middle">the generated clone</text>
  <text class="ts" x="160" y="112" text-anchor="middle"><tspan class="i">X</tspan> is impossible — universally quantified</text>
  <text class="ts b" x="160" y="132" text-anchor="middle">the hard half</text>

  <line class="ln" x1="315" y1="85" x2="385" y2="85" stroke-width="1.8" marker-end="url(#ah3)"/>
  <text class="t" x="350" y="74" text-anchor="middle">⊢</text>

  <rect class="box" x="395" y="18" width="290" height="134" rx="6" fill="var(--f03)"/>
  <text class="t b" x="540" y="45" text-anchor="middle">rich witness</text>
  <text class="ts mut" x="540" y="66" text-anchor="middle">one concrete structure,</text>
  <text class="ts mut" x="540" y="81" text-anchor="middle">built internally</text>
  <text class="ts" x="540" y="112" text-anchor="middle"><tspan class="i">X</tspan> is exhibited — a construction</text>
  <text class="ts mut" x="540" y="132" text-anchor="middle">the easy half</text>
</svg>
</div>
<figcaption><span class="fignum">Figure 3</span> — The differential and its two unequally heavy
halves. It is delivered only with the negative one.</figcaption>
</figure>

---

## IV · The witnesses: the series of bounds {#iv}

| | Theorem | Kind of non-internality | Reach |
|---|---|---|---|
| **D** | rejection does not lie in the clone | **transcendence** — it leaves the contexture | `m = 3` |
| **E1** | complete classification | **non-uniformity** — it stays and chooses differently | `m = 3` |
| **E2** | characterisation | exactly minimum and maximum | `m = 4` |
| **E3** | characterisation | exactly minimum and maximum | **all `m ≥ 4`** |
| **E4** | stage aggregation | face of application | `m = 4` |

All five: **proved · aggregate**.

### 1 · D — locating the first bound

The rejection operation refuses an offered pair of values as a whole and does not lie in the
clone over three values (**proved · aggregate**; the proof is arity-blind and runs via
contexture preservation).

Lying outside a clone is cheap in itself: in the binary fragment the clone comprises **82 of
19,683** operations, 0.42 per cent (**computed**). The claim does not rest on that. The basis
preserves three invariants, and every term over it preserves all three — not merely the
generators (**proved · aggregate**, by term induction). Rejection violates exactly one of them
and preserves the other two. It therefore lies not somewhere outside, but **at a determinate
place**.

A marginal note that arose while recomputing for this edition and is absent from Rev1: the
binary clone fragment has **the same size 82 at three, four, five and six values**
(**computed**). The number 82 is not a property of three-valuedness but of the signature.

<figure class="fig wide">
<div class="fig-scroll">
<svg viewBox="0 0 700 300" role="img" aria-label="The generated clone within all binary operations">
  <rect class="box" x="120" y="8" width="460" height="188" rx="8" fill="var(--f05)"/>
  <text class="ts" x="350" y="34" text-anchor="middle">all binary operations over three values: 19,683</text>

  <circle class="box" cx="300" cy="118" r="66" fill="var(--f16)"/>
  <text class="ts" x="300" y="108" text-anchor="middle">generated</text>
  <text class="ts" x="300" y="124" text-anchor="middle">clone</text>
  <text class="ts b" x="300" y="142" text-anchor="middle">82</text>

  <circle class="box" cx="470" cy="72" r="13" fill="var(--f35)"/>
  <text class="ts" x="492" y="76" text-anchor="start">rejection</text>

  <text class="txs" x="120" y="228" text-anchor="start">three invariants are preserved by <tspan class="i">every</tspan> term (<tspan class="b">proved · aggregate</tspan>):</text>
  <text class="txs" x="120" y="245" text-anchor="start">two-valued embedding · fixed point · tolerance relation</text>
  <text class="txs" x="120" y="266" text-anchor="start">rejection violates <tspan class="b">exactly one</tspan> and preserves the other two</text>
  <text class="txs mut" x="120" y="288" text-anchor="start">the clone size 82 holds equally at four, five and six values — it depends on the signature, not on the number of values</text>
</svg>
</div>
<figcaption><span class="fignum">Figure 4</span> — The location: not somewhere outside, but
beyond exactly one of three preserved invariants. Clone figures <strong>computed</strong>,
outside the corpus; the size 82 is a property of the signature and not of
three-valuedness.</figcaption>
</figure>

### 2 · E1 — the second reason, and the complete division

An operation can fail to be assemblable for **two distinct reasons**: by **transcendence** —
it leaves the elementary contexture (this is D) — or by **non-uniformity** — it preserves
every contexture, acts classically on each, and chooses different classical operations on
different contextures.

The second reason has a witness, and completely so: of the eight choice patterns over three
values exactly four are assemblable and exactly four are not (**proved · aggregate**; the
division is closed under negation conjugation — a transport lemma replaces three copies of a
proof by one theorem).

**The four reachable patterns are not an arbitrary four** (**computed**). Ordering the three
elementary contextures as `{0,1}`, `{0,2}`, `{1,2}`, they are `(min,min,min)`,
`(max,min,min)`, `(max,max,min)`, `(max,max,max)` — a chain of thresholds and not a scattered
selection.

### 3 · E2 and E3 — from existence to characterisation

At four values the picture tips: of the 64 locally classical operations **two** remain
assemblable, namely minimum and maximum themselves (**proved · aggregate**; verified
**computed**). At five values it is 2 of 1,024, at six 2 of 32,768 (**computed**).

The pattern counts are no accident: there are `2^C(m,2)` patterns, and `C(m,2) = m(m-1)/2` is
the number of elementary contextures of an `m`-valued system. The triangular numbers Günther
carries for compound contextures and for the hierarchy of ontologies stand here as the
exponent.

$$\textbf{E3:}\quad m \geq 4 \;\Longrightarrow\; \bigl(f \text{ in the clone} \iff f = \min \text{ or } f = \max\bigr)$$

E3 hangs on no fixed number of values — D and E1 stand at three values, E2 at four. Its proof
uses no `decide` and no case distinction on `m`; it runs over six families of edges with
closed-form breaking points and an induction on path length.

::: callout
**The threshold lies at four, and this is not an artefact.** At three values the statement
is *false* — there four of eight patterns are assemblable. At two values there is no witness
at all, because there is only one contexture. This meets Günther's own threshold: the
classical two-valued system does not yet represent a compound contexture, the second value
yields nothing new and stands unmediated over against the first (**source-verified**).
Mediation begins at three — here as a counted zero, not as a thesis.
:::

### 4 · Robustness: how much each bound claims

A non-generability bound hangs on its invariant. If the signature is extended by constants,
the bound survives precisely when the invariant is reflexive.

| Witness | Invariant | survives constants |
|---|---|---|
| D | one elementary contexture | **no** |
| E2, E3, E4 | neighbourhood with broken edges | **yes** |

A bound that falls to an added constant claims less than it appears to. The inspection is
written into the corpus as a duty before every new witness.

---

## V · The layer of applications, and what is measured in it {#v}

Two applications exist: a release policy over four authorisation levels and a source authority
over four evidence levels. Both are **aggregate**.

**The load-bearing claim is not that they exist.** It is: the applications **consume** the
generic theorem instead of reproducing its proof. That is measurable at the proof term and
nowhere else, and it is measured (**measured · aggregate**):

| Theorem | references in its term | |
|---|---|---|
| `PolicyCheck.freigabe_nicht_erzeugbar` | `GCB.locally_classical_in_clone_iff` | **yes** |
| `RAGAuthority.autoritaet_nicht_erzeugbar` | `GCB.locally_classical_in_clone_iff` | **yes** |
| `PolicyCheck.freigabe_nicht_erzeugbar_konstanten` | `GCB.constant_clone_min_or_max` | **yes** |
| `RAGAuthority.autoritaet_nicht_erzeugbar_konstanten` | `GCB.constant_clone_min_or_max` | **yes** |
| `PolicyCheck.freigabe_lokal` (counter-probe) | same target | **no** |
| `RAGAuthority.autoritaet_lokal` (counter-probe) | same target | **no** |

**The counter-probe is the point.** A route that reports `yes` everywhere measures nothing.
This one discriminates, and it does so at the prerequisite lemmas of the same files — at the
nearest non-hit and not at an arbitrarily distant counterpart.

### The limit in the same breath

The bound bites on linearly graded carriers from four levels upwards. From non-generability
follows **no** guarantee of security, legality, truth or retrieval. What the theorem says is:
a mixed policy is not assemblable from local, contexture-blind checkers — in whatever wiring
and to whatever depth. What it does not say is that the policy is right.

**On a lattice of equal-ranking roles the bound falls.** On the smallest non-distributive
lattice `M₃` — bottom, three incomparable elements, top — the binary clone fragment comprises
166 operations; over the seven comparable pairs **ten of them are locally classical, and eight
of those are neither infimum nor supremum** (**computed**). One witness can simply be written
down: the operation choosing the supremum on the lower edges and the infimum on the upper
ones. Exactly the pattern that E3 excludes on linear scales is assemblable here.

A transition graph of named roles without grading is **not** carried by this bound; what
remains provable there is reachability, and a type system achieves that too.

---

## VI · The ledger and the register: the concepts and their carriers {#vi}

Günther's concepts stand in a definitions edition with nineteen paragraphs. Which concept has
which Lean carrier is, in this edition, no longer spread through the running text but
**machine-checked**.

The ledger carries **79 rows**, **63 of them with a carrier** over 55 distinct carrier names,
and covers **19 of 19 paragraphs** (**measured**). The carrier statuses distribute over 45
theorems, 17 definitions, one posit and **16 open rows**.

**The paper does not establish this assignment itself.** It shows the mechanism that holds it;
the table is in `docs/definition-ledger.md` and there alone. Eight rules check it, six of them
in the doc lint and two at build time:

- **R1, R2** (build): every named carrier resolves in the environment, and its carrier status
  agrees with the kind of declaration.
- **R3** no assignment status `Theorem` — an assignment status is editorial and never
  compiler-checked, and must not call itself so.
- **R4** carrier status `Open` forces an empty carrier column.
- **R5** all nineteen paragraphs represented.
- **R6** carrier status `Theorem` forces a guard entry.
- **R7** every carrier row has exactly one matching reference in the reference file, and
  conversely; an orphaned reference is as much a violation as a missing one.
- **R8** every row ID occurs exactly once in both files.

R3 through R8 set the exit code of the lint; a violation turns the run red. **Sixteen open
rows stay open** — among them the strong Definition 6 (L06-1) and the value assignment of
morphograms (L16-6). An open row is not a defect of the ledger but its achievement.

### The register of posits

Posits do not disappear, they are registered. As measured, the aggregate carries **32 structure
fields of type `True`** (**measured · aggregate**), counted by environment query and not by
text search. They fall into two classes that do not say the same thing:

- **30 placeholders** — a deferred proof debt. Each needs an exit criterion: what would have
  to be the case for it to fall.
- **2 constitutive posits** — no proof owed, but a justification for why none is owed.

The load-bearing rule is not "the aggregate contains no posit" but **no theorem of the
aggregate depends on a posit**. A field of type `True` can enter no proof; why it must
nevertheless be marked is an epistemic and not a logical argument: what stands in the
aggregate reads as certified holdings.

Alongside this a standing probe: **no non-projection of the aggregate has conclusion `True`**
(**measured · aggregate**, value 0). It prevents declarations whose name claims more than
their statement. The probe carries its own counter-calculation: the same route reports 32 on
the projection side — a value whose answer is known.

---

## VII · Movement and time {#vii}

Over the web lies a modal triad as a stock of movement: **displacement** — the same structure
at another place; **reorganisation** — the same parts in another order; **irreversible
positing** — the step that is not taken back. Their compositions are smooth in exactly one
direction; there is no canonical interchange of directions.

Before that it is worth looking at the place where Günther first came upon the matter. In 1937
he sets three propositions about potency side by side, each immediately plausible on its own:
time is more powerful than will; thought is more powerful than time; will is more powerful
than thought. Take the first two together and it follows that thought is more powerful than
will — the third says the opposite. The three close into a circle (**source-verified**,
*Wahrheit, Wirklichkeit und Zeit*, Paris 1937).

**What the architecture makes of this is a differential and not a thesis.** What is proved is
the poor side: in every transitive, irreflexive relation — on every carrier, without exception
— a three-cycle is impossible, and there is likewise no relation-preserving image of such a
cycle into a strict order. That thought, will and time behave this way is not claimed; what is
claimed is: **if** they do, then no linear order is their measure — and not because none has
been found so far, but because none can exist.

<figure class="fig wide">
<div class="fig-scroll">
<svg viewBox="0 0 700 370" role="img" aria-label="The three propositions of potency as an intransitive cycle">
  <defs><marker id="ah5" markerWidth="8" markerHeight="8" refX="7" refY="4" orient="auto">
    <path d="M0,0 L8,4 L0,8 z" fill="var(--stroke)"/></marker></defs>

  <circle class="box" cx="350" cy="62"  r="42" fill="var(--f05)"/>
  <circle class="box" cx="212" cy="222" r="42" fill="var(--f05)"/>
  <circle class="box" cx="488" cy="222" r="42" fill="var(--f05)"/>
  <g class="ts" text-anchor="middle">
    <text x="350" y="67">thought</text><text x="212" y="227">time</text><text x="488" y="227">will</text>
  </g>

  <line class="ln" x1="323" y1="95"  x2="239" y2="189" marker-end="url(#ah5)"/>
  <line class="ln" x1="255" y1="222" x2="443" y2="222" marker-end="url(#ah5)"/>
  <line class="ln" x1="461" y1="189" x2="377" y2="95"  marker-end="url(#ah5)"/>

  <g class="txs mut" text-anchor="end">
    <text x="248" y="128">memory reaches back</text>
    <text x="248" y="142">to the beginning</text>
  </g>
  <g class="txs mut" text-anchor="middle">
    <text x="349" y="246">decisions fall</text>
    <text x="349" y="260"><tspan class="i">in</tspan> time</text>
  </g>
  <g class="txs mut" text-anchor="start">
    <text x="452" y="128">“that I think” rests on</text>
    <text x="452" y="142">“that I <tspan class="i">will</tspan> to think”</text>
  </g>

  <text class="txs" x="350" y="172" text-anchor="middle">≻ means</text>
  <text class="txs i" x="350" y="186" text-anchor="middle">more powerful than</text>

  <rect class="box" x="110" y="298" width="480" height="52" rx="5" fill="var(--f08)"/>
  <text class="txs" x="350" y="320" text-anchor="middle">Chaining the first two gives <tspan class="b">thought ≻ will</tspan> —</text>
  <text class="txs" x="350" y="337" text-anchor="middle">the third says the opposite. <tspan class="b">The cycle closes.</tspan></text>
</svg>
</div>
<figcaption><span class="fignum">Figure 5</span> — The three propositions of potency of 1937 and
their intransitive circle. What is proved is not the circle but its impossibility in every
transitive, irreflexive relation (<strong>proved · aggregate</strong>).</figcaption>
</figure>

### The carriers of this section

The load-bearing theorem of the potency cycle is
`Proemial.IntransitivityDifferential.no_cycle_in_strict_order`
(**proved · aggregate**, profile **axiom-free**): in every transitive, irreflexive relation a
three-cycle is impossible. That such a cycle also has no relation-preserving image into a
strict order is carried by `cyc3_not_representable` (**proved · aggregate**, `[propext]`);
that the cycle itself obtains is carried by `cyc3_holds`, `cyc3_irrefl` and
`cyc3_not_transitive` (same marks). All six theorems are guarded.

The absent interchange of directions is `Proemial.NoUniformSwap.no_uniform_swap`
(**proved · aggregate**, `[propext, Classical.choice, Quot.sound]`, guarded; the appeal to
`Classical.choice` comes from the category-theoretic machinery and not from the proof itself).
**The full name with module is no pedantry here:** a theorem of the same name lies in
`Diagnostics.SwapSatzProbe` — domain **call target**, unguarded, carried in the corpus as a
historical record. Whoever names it without the module leaves open which of the two he means,
and the second axis runs empty.

The modal triad lies at two places. This section rests on
`F3e.ModalTwoCategoryWithPullbacks` (**aggregate**); a version in the frozen branch
(`PathC.ModalTwoCategory`, `PathC.ModalTwoCategoryNegation`) remains outside the default
targets and carries nothing here.

---

## VIII · The safeguards: guards, profiles, domains {#viii}

An architecture that asserts impossibilities must be able to say what its proofs rest on — and
must prevent that from changing silently.

### The standing

::: stand
| Figure | Value | Domain |
|---|---:|---|
| checked (axiom gate) | **3018** constants | import tree of `Reformulation`, name-filtered |
| axiom guards, written | **396** in 45 files | `Reformulation/` **and** `Foreign/` |
| axiom guards, enforced | **386** in 44 files | import closure of the five default targets |
| statement pins | **44** | `Reformulation/` |
| theorems | **726** | `Reformulation/` alone |
| `def` | **318** | `Reformulation/` |
| build jobs | **1301** | the five default targets together |
| files | **163**, of which 160 `.lean` | `Reformulation/` and `Foreign/` |
| **declared gaps** | **0** | whitelist empty |
:::

**A warning belongs to the theorem count.** It does not compare with the figure of the
previous edition: that one ran over a different domain, and the counting route has since been
widened — it previously missed thirteen `private` declarations and six carrying an attribute,
and counted three quotations. Two changes lie between the two numbers, and setting them side
by side would show a growth that neither of them claims.

### The four mechanisms

**First, the axiom guards.** For every load-bearing theorem its axiom profile is measured and
frozen as an expectation; if the proof basis shifts silently, the build breaks. The guard
secures the basis, not the wording. The profile distribution over all 396 written guards
(**measured**):

| Profile | Guards |
|---|---:|
| `[propext, Quot.sound]` | 183 |
| `[propext]` | 84 |
| **axiom-free** | **66** |
| `[propext, Classical.choice, Quot.sound]` | 61 |
| `[Quot.sound]` | 2 |

The **66** answers "how many of the guarded profiles are axiom-free" and not "how many
theorems of the corpus are axiom-free"; the reference quantity 396 belongs beside it.
`Classical.choice` appears in 61 profiles — not forbidden, but declared.

**Second, the statement pins.** Guards secure the basis, not the formulation; a weakened
theorem with the same profile would pass. Pins nail down the full wording and break the build
on definitional drift.

**Third, the global gate.** It reports:

```text
AXIOM-GATE GRÜN — Aggregat Reformulation (3018 geprüfte Konstanten)
zieht kein sorryAx. Whitelist leer.
```

**Fourth, and new in this edition: the domain separation.** Five targets build on
`lake build`; five more run only when called. The assurance of the gate holds for the
aggregate and for no other domain.

| Target | Jobs | Default |
|---|---:|---|
| `Reformulation` | 1274 | yes |
| `AxiomGate` | 1275 | yes |
| `DefinitionLedger` | 1275 | yes |
| `Probes` | 1212 | yes |
| `F1Coalgebraic` | 671 | yes |
| `ForeignPeresMermin` | 677 | no |
| `Diagnostics` | 1506 | no |
| `MathlibExtensions` | 1289 | no |
| `PreC` | 1242 | no |
| `PathC` | 1388 | no |
| **`lake build` without argument** | **1301** | the five together |

**This table is not to be added up, and it shows why.** The five default targets sum to 5707
jobs; the joint build needs 1301. The factor 4.4 is the overlap of the import closures.
Whoever sums build outputs of several targets counts modules more than once.

### What a stranger's `grep` finds

Whoever searches the tree for `sorry` finds three numbers, and each answers a different
question (**measured**): **123** raw word occurrences over the whole tracked holdings, **95**
in the Lean sources, **27** affected declarations in eight files. The third is the
load-bearing one; the first two include prose — freeze notes, doc strings, the phrase
"sorry-free".

Within the Lean sources the 95 distribute over `PathC/` 53, `Proemial/` 27, `Reformulation/`
5, `Diagnostics/` 5, `F3e/` 4, `F3f/` 1.

**Two sentences belong to the frozen branch, and both are true.** The target `PathC` builds
green, 1388 jobs — and exactly one module of the branch lies in no target root and does not
compile. **Neither statement is an assurance of gap-freeness:** green here means *compiles*,
not *gap-free*, and for a call target there is no axiom gate. The same branch carries 53 of
the 95 occurrences.

### Replicability

A green build in the working directory says "green on my machine". More is measured: from a
fresh, unauthenticated clone of the public state the tree builds green in 39 seconds, **126
modules built and 0 replayed**, with the same gate line and an empty whitelist (**measured**).
It is a real build and not a replay of an intermediate state.

The number 126 is at the same time the size of the import closure of the five default targets,
computed from the `import` lines. **Both lists have been compared as sets and are equal** —
the `diff` of the sorted module names is empty (**measured**). The two routes share no step:
one reads source text and follows `import` lines transitively, the other reads the build output
of a fresh clone.

The domain map over all 161 project modules (**measured**):

| Domain | Modules |
|---|---:|
| aggregate | 126 |
| call target | 34 |
| covered by no target | 1 |

Across these, 18 modules lie in the frozen branch; two of them are built through a call
target, and one is reached by no target — it is the same module that does not compile. **The
domain cannot be read off the directory:** the target of the frozen branch reaches six modules
under `MathlibExtensions/` which are not frozen and build green through their own target.

That the ten unenforced guards lie entirely in one file outside the closure is the reason why
"enforced = 386" is justified via the **closure route** and not via the directory boundary:
that both yield the same value today is a coincidence and not an identity.

---

## IX · The instruments as a subject of their own {#ix}

Alongside the theorems something has arisen that knows nothing of Günther and could travel
further: a reviewing practice for the formalisation of philosophical texts. Whoever formalises
a thinker has a problem foreign to pure mathematics — **the interpretation outruns the term**.
A theorem is built, its name is chosen, and the name claims more than the theorem. Against
this gradient no resolutions help, only mechanisms.

### Rules, each from a misstep

1. **Look for the theorem first, then build only as much carrier as the theorem demands.** A
   base layer that no theorem requests is a renaming of the library.
2. **A trial build before every specification, in the target environment.**
3. **The specification names goal, constraints and pitfalls — not the wiring.**
4. **Specifications are reviewed too, not only builds.**
5. **A counting route that takes prose as its criterion is a time bomb.**
6. **Aggregate means free of posits.** A file enters the certified body if it carries no posit
   — not if the effort is small.
7. **The title outruns the theorem.**
8. **A route is counter-calculated before its result enters a document** — against a case
   whose answer is known from the source.
9. **A measuring probe checks an equation, not a number.**
10. **Equality of value between two routes is no evidence of equality of set.** Measured: two
    routes both yielded 49 and had no line in common.
11. **Build outputs of several targets are not summed.**

### The lint

A doc lint checks three groups over Markdown and Lean sources. Group (A) searches for claims of
rank and **reports** — currently 38 hits, each individually assessed, none with a reference set
outside the corpus's own holdings. Group (B) searches for a particular conceptual relapse near
set-theoretic trigger words and reports 0. Group (C) checks the ledger rules R3 to R8 and
**sets the exit code**.

::: callout
**Addendum, 2 August 2026.** The lint figures given here are measured at commit
`e5ef3d7` and are exactly reproducible with the route in force at that time. The
route has since been corrected in three respects: it was case-sensitive, its German keywords
did not match transliterated spellings, and it did not read the HTML editions. The group (A)
figure was therefore a lower bound and not a count. The zero of group (B) was an artefact of
the route; since the correction it is a count, and its reason can be named: in the whole
scanned body there is a single line in which the guarded keyword occurs at all, and it is the
line that describes the lint. Group (B) is thus a guard without an object. That is its work,
but it is not evidence.
:::

The split is deliberate: a claim of rank wants to be read and not enforced — a breaking lint
gets circumvented, a reporting one gets read. A contradiction between table and reference file,
by contrast, is objectively wrong, and whoever leaves it standing publishes an unchecked table.

### The list of errors

**The evidence that the review layers bite is the list of errors** — and it is continued, not
shortened. From the block that led to this edition:

- A route using `\b` in a tool mode that does not carry word boundaries: result 0
  instead of 153. Not a false result but an empty one — and an empty one looks like good news.
- A count with `grep -c`, which counts lines rather than occurrences: a hit running across a
  line break dropped out, five instead of six.
- An instruction in the imperative, read as a description of state: "goes live without further
  action" stood under the heading "Switching on".
- A route that reports the same thing before and after a change of state and therefore does not
  measure the change — its result was accidentally right. What carried the finding was the
  second route. Whoever runs two routes survives the failure of one.
- A provenance note for two figures that pointed at the wrong document.
- Five estimated instead of sixteen counted occurrences of a name.

**None of these errors was found by the instance that made it.**

---

## X · Reach and limit {#x}

What this architecture claims is conditional and is carried as such. It does not promise to
compel the sceptic to acknowledge an irreducibility; it promises to **symmetrise** him — from
the comfortable position *this reduces to the known* to the explicit position *I posit the one
encompassing logic*, which is itself a posit and as such no longer has precedence.

### The three limits

**First, mathematical: `M₃`.** The characterisation lives on linearly graded carriers and
falls on lattices of equal-ranking elements. This is not a proof gap but a counterexample —
and the breaking point is exactly the lattice shape an architecture of equal-ranking roles
would have.

**Second, hermeneutic: the identification.** That the two-element value set *is* Günther's
elementary contexture is settled by no theorem. The posit stands on grounded soil — closure
under the local operations is a substantive reason — but it remains a choice.

**Third, in principle: the spontaneity of enactment.** Not the will as a function, but solely
the *that* of enactment is no structural feature; there is no poorer model in which it is
missing as a position, because it is not a position.

### What is not built

The **proemial relation** — the core of Günther's theory — is not formalised. The **compound
contexture** is present as a number sequence and is not built as a concept. The strong
**Definition 6** is open and is carried as open. The **value assignment of morphograms** is an
open ledger row. **Sixteen ledger rows** stand on `Open`, and they are to remain there as long
as no carrier carries them.

A note that lies in the matter itself: the definitions edition gives for compound contextures
the formula `n(n+1)/2` and the sequence `1, 3, 6, 10, …` and states at the same time that a
compound contexture requires at least three values. The two do not agree; the first compound
contexture is the three-valued one, and the `1` belongs to the ontology sequence. The
architecture counts the elementary contextures of an `m`-valued system as `m(m-1)/2`; this is
compatible with Günther's series, but it is a **stipulation** and not a derivation.

### The picture

A ground that counts repetition and whose normalisation is built as a procedure; logics whose
separation is not posited but proved, in a form that withstands Günther's basic case; a mode of
proof that knows and carries its hard half; a series of witnesses grown from an existence claim
to a characterisation without a fixed number of values; a layer of applications whose
consumption is measured at the term; a ledger that holds nineteen paragraphs compiler-checked
and leaves sixteen rows open; a gate with no `sorryAx`; and three limits, none of which is a
defeat.

::: callout
**What is posited stands at the beginning; what is proved is counted; what is interpretation is
called so.**
:::

---

## Appendix · Counting routes {#appendix}

So that the figures are recomputable and not merely credible, each carries a route. All
statements hold at commit `e5ef3d7`; any build move renders every exhibited number silently out
of date, which is why each carries its standing.

| Quantity | Value | Route |
|---|---:|---|
| checked constants | 3018 | build output of the axiom gate |
| guards written | 396 / 45 files | `grep -rE '#guard_msgs.*in #print axioms'` over `Reformulation/` and `Foreign/` |
| guards enforced | 386 / 44 files | same route, restricted to the import closure of the five default targets |
| import closure | 126 of 161 modules | `import` lines followed transitively from the 21 target roots |
| axiom-free profiles | 66 of 396 guards | `grep -rc 'does not depend on any axioms'` |
| profile distribution | 183 / 84 / 66 / 61 / 2 | every guard read individually; sum 396 checked as an equation |
| theorems | 726 | `grep -rhE '^((private\|protected\|nonrec) +)?(@\[[^]]*\] +)?(theorem\|lemma) '` over `Reformulation/` |
| `def` | 318 | the same widening for `def` |
| statement pins | 44 | `grep -rc '^-- STATEMENT-PIN'` |
| build jobs | 1301 jointly | build output per target, **not summed**; per target see above |
| files | 163 / 160 `.lean` | file count over `Reformulation/` and `Foreign/` |
| `sorry` occurrences | 123 / 95 / 27 | word boundary `\bsorry\b`, occurrences (not lines), over `git ls-files` |
| posit fields | 32 = 30 + 2 | environment query over structure fields and projections |
| non-projections with conclusion `True` | 0 | same route, projection negated; counter-probe yields 32 |
| ledger | 79 rows / 63 pairs / 19 of 19 | doc lint group (C) |
| lint | (A) 38, (B) 0, (C) 0, exit 0 | one run |
| consumption of the applications | 4 hits / 2 non-hits | environment query with explicit `ConstantInfo` matching over type and proof term |
| clone build | 1301 jobs, 126 built / 0 replayed | `git clone`, `lake exe cache get`, `lake build`, unauthenticated |
| clone fragment `{min,max,neg}` | 82 at `m` = 3, 4, 5, 6 | closure of `{p₁,p₂}` under pointwise min, max, order reversal |
| locally classical in the clone | 4 of 8 · 2 of 64 · 2 of 1024 · 2 of 32,768 | the same enumeration, filtered for local classicality |
| `M₃` | 166 clone members, 10 locally classical, 8 of them neither infimum nor supremum | closure under infimum, supremum, order reversal on the five-element lattice |

**Three rules on counting.** First, counting is done through the shell, not with a library
function that skips blank lines. Second, **aggregate and corpus figures are kept apart**; the
aggregate is the certified import tree, the corpus additionally comprises the probes that carry
a marked posit. Third, **build outputs of several targets are not summed** — the 5707 in §VIII
stands there so that it stands nowhere else.

### Two points this edition has closed

**The equality of the two module lists is checked as a set**, not only as a number: the sorted
module names of the import closure and of the built lines of the clone build were compared, and
the `diff` is empty. The line "guards enforced" therefore holds — the route restricts to exactly
the set the build touches.

**The domain entries in §VII are present** and stand there. The carriers are named with full
name and module, because one theorem name of that section occurs twice in the tree — once in the
aggregate and guarded, once in a call target and unguarded.

