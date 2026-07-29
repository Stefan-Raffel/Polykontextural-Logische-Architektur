-- EINGEFROREN (29. Juli 2026): dieser Zweig wird nicht fortgeschrieben.
-- Status, Zahlen und die Bedingungen fuer ein Auftauen: docs/build-targets.md, Abschnitt PathC.
import Mathlib.Data.Fin.Basic
import Reformulation.PathC.GeometricTheory.Signature

/-!
# Reformulation.PathC.GeometricTheory.Formula

Terms and geometric formulas over a many-sorted signature.

## What this module carries

- `Term sig s` — terms of sort `s`, with `ℕ`-indexed de Bruijn variables and
  function application via `Fin`-indexed argument tuples.

- `GeometricFormula sig Γ` — formulas in context `Γ`. Six constructors:
  `top`, `bot`, `atom`, `conj`, `disj`, `exists_`.

- `GeometricFormula.disj₂` — binary disjunction.

- `GeometricFormula.disj_empty_eq_bot` — empty disjunction equals `bot`
  (deferred, β.2).

## Klasse-B findings

- **B-2/β** — Σ notation: signature variable named `sig`.
- **B-3/β** — Universe for `disj` index: formula lives in `Type (max u (max v w) + 1)`,
  index in `Type (max u (max v w))` — strict separation avoids universe inconsistency.
- **B-4/β** — `Bool`/`PEmpty` universes: `Bool : Type 0` and `PEmpty : Sort v` must
  be lifted to `Type (max u (max v w))` via `ULift` / explicit universe annotation.
- **B-5/β.2** — `disj_empty_eq_bot` stated as `sorry`.
- **B-6/β** — `Set (GeometricFormula ...)` rejected by strict positivity; replaced by
  `{ι : Type (max u (max v w))} → (ι → GeometricFormula sig Γ)`.
-/

namespace Reformulation.PathC.GeometricTheory

universe u v w

/-- Terms over `sig` of sort `s`, with de Bruijn `ℕ`-indexed variables. -/
inductive Term (sig : ManySortedSignature.{u, v, w}) : sig.sort → Type (max u v) where
  | var {s : sig.sort} : ℕ → Term sig s
  | app {args : List sig.sort} {result : sig.sort} :
      sig.func args result →
      (∀ i : Fin args.length, Term sig (args.get i)) →
      Term sig result

/-- Geometric formulas over `sig` with context `Γ`. `Γ` is an index (changes under
    `exists_`).

    Universe: `Type (max u (max v w) + 1)` — one level above `Type (max u (max v w))`.
    This gives the `disj` index type `{ι : Type (max u (max v w))}` a universe strictly
    below the formula universe, avoiding Lean 4's universe inconsistency check. -/
inductive GeometricFormula (sig : ManySortedSignature.{u, v, w}) :
    List sig.sort → Type (max u (max v w) + 1) where
  | top    {Γ} : GeometricFormula sig Γ
  | bot    {Γ} : GeometricFormula sig Γ
  | atom   {Γ} {args : List sig.sort} :
      sig.rel args →
      (∀ i : Fin args.length, Term sig (args.get i)) →
      GeometricFormula sig Γ
  | conj   {Γ} : GeometricFormula sig Γ → GeometricFormula sig Γ → GeometricFormula sig Γ
  /-- Indexed infinitary disjunction. `ι` is strictly below the formula universe,
      ensuring no universe paradox. Use `ULift` to lift small types (Bool, Fin n)
      to `Type (max u (max v w))` when needed. -/
  | disj   {Γ} {ι : Type (max u (max v w))} :
      (ι → GeometricFormula sig Γ) → GeometricFormula sig Γ
  | exists_ {Γ} (S : sig.sort) :
      GeometricFormula sig (S :: Γ) → GeometricFormula sig Γ

namespace GeometricFormula

variable {sig : ManySortedSignature.{u, v, w}}

/-- Binary disjunction via a `Bool`-indexed family.
    `Bool : Type 0` is lifted to `Type (max u (max v w))` via `ULift`. -/
def disj₂ {Γ : List sig.sort} (φ ψ : GeometricFormula sig Γ) : GeometricFormula sig Γ :=
  disj (ι := ULift.{max u (max v w)} Bool) (fun b => if b.down then φ else ψ)

/-- Empty disjunction equals `bot`. The indexing type is
    `PEmpty.{max u (max v w) + 1} : Type (max u (max v w))`.
    Stated as `sorry` (Klasse-B β.2): not definitionally equal in the indexed-family
    constructor form; requires structural reasoning. -/
theorem disj_empty_eq_bot {Γ : List sig.sort}
    (f : PEmpty.{max u (max v w) + 1} → GeometricFormula sig Γ) :
    (disj f : GeometricFormula sig Γ) = bot := by
  sorry

end GeometricFormula

-- ============================================================
-- C21: Substitution machinery
-- ============================================================

-- `sig` is not a `variable` inside `GeometricFormula` after the block closes;
-- declare it again for the following definitions.
variable {sig : ManySortedSignature.{u, v, w}}

/-!
## C21 — Substitution (Operation 1)

`TermSubst sig` is a de Bruijn substitution: it maps each ℕ-indexed variable
position together with a sort to a term of that sort. Sort-correctness is a
user invariant (not enforced by Lean's type system); the functions below are
correct for well-typed formulas.

**Klasse-B findings (C21)**
- **B-1/β** — `TermSubst sig` is sort-erased (`∀ n s, Term sig s`); explicit
  sort argument avoids the `{s}` implicit resolution issues in `lift`.
- **B-2/β** — `GeometricFormula.subst {Γ Δ}` uses phantom implicit contexts;
  Lean infers `Δ = S :: Δ` for the `exists_` case from the expected type.
- **B-3/ζ** — `subst_comp` (Klasse-D shift): `lift`-`subst` commutation lemma
  not proved here; deferred to C22.
-/

/-- A de Bruijn substitution: for each index `n` and sort `s`, a term of sort `s`.
    Sort-correctness invariant: for well-typed formulas in context `Γ`,
    `σ n (Γ.get ⟨n, _⟩)` should give the replacement for variable `n`. -/
abbrev TermSubst (sig : ManySortedSignature.{u, v, w}) : Type (max u v) :=
  ∀ (n : ℕ) (s : sig.sort), Term sig s

namespace Term

/-- Increment all free de Bruijn indices by one (shift for a new binder). -/
def shiftVar {s : sig.sort} : Term sig s → Term sig s
  | .var n    => .var (n + 1)
  | .app f as => .app f (fun i => (as i).shiftVar)

/-- Apply substitution `σ` to a term: replace each `var n` with `σ n s`. -/
def subst (σ : TermSubst sig) {s : sig.sort} : Term sig s → Term sig s
  | .var n    => σ n s
  | .app f as => .app f (fun i => (as i).subst σ)

@[simp]
theorem subst_var (σ : TermSubst sig) (n : ℕ) (s : sig.sort) :
    (Term.var (s := s) n).subst σ = σ n s := rfl

@[simp]
theorem subst_id {s : sig.sort} (t : Term sig s) :
    t.subst (fun n _ => .var n) = t := by
  induction t with
  | var n       => rfl
  | app f as ih => simp [Term.subst]; funext i; exact ih i

@[simp]
theorem shiftVar_var (n : ℕ) (s : sig.sort) :
    (Term.var (s := s) n).shiftVar = .var (n + 1) := rfl

/-- Composition of substitutions is associative for terms. -/
theorem subst_comp (σ τ : TermSubst sig) {s : sig.sort} (t : Term sig s) :
    (t.subst σ).subst τ = t.subst (fun n s => (σ n s).subst τ) := by
  induction t with
  | var n       => simp [Term.subst]
  | app f as ih => simp [Term.subst]; funext i; exact ih i

end Term

namespace TermSubst

/-- The identity substitution: variable `n` of sort `s` maps to `var n`. -/
def id (sig' : ManySortedSignature.{u, v, w}) : TermSubst sig' :=
  fun n _ => .var n

/-- Lift `σ` across a new bound variable of sort `S`:
    - position 0 (new variable) → `var 0`
    - position n+1            → shift the old substitution result -/
def lift (σ : TermSubst sig) (S : sig.sort) : TermSubst sig :=
  fun n s => match n with
    | 0     => .var 0
    | n + 1 => (σ n s).shiftVar

/-- Compose substitutions: first apply `σ`, then `τ` to the result. -/
def comp (σ τ : TermSubst sig) : TermSubst sig :=
  fun n s => (σ n s).subst τ

/-- Singleton substitution: replace variable 0 with `t`, shift the rest down.
    **Sort note**: position 0 in an extended context `S :: Γ` has sort `S`;
    for other positions (n+1), sort comes from `Γ.get n`. The dummy at
    wrong sorts is never accessed for well-typed formulas.
    Classical decidability is used for the sort equality check. -/
noncomputable def idCons {sig : ManySortedSignature.{u, v, w}}
    {s : sig.sort} (t : Term sig s) : TermSubst sig :=
  fun n s' => match n with
    | 0     =>
        haveI : DecidableEq sig.sort := Classical.decEq sig.sort
        if h : s = s' then h ▸ t else .var 0
    | n + 1 => .var n

/-- Weakening substitution: shifts all variables up by one.

    Sprach-Klassen-Substanz (F29): for weakening a formula from context `Γ` to `s :: Γ`.
    Distinct from `lift (id sig) s`, which equals `id sig` (see `id_lift`); `shift`
    genuinely maps variable `n` to `var (n+1)`, leaving position 0 free for the new
    binder. Used in the exE inference rule. -/
def shift : TermSubst sig :=
  fun n _ => Term.var (n + 1)

theorem id_lift (sig' : ManySortedSignature.{u, v, w}) (S : sig'.sort) :
    lift (TermSubst.id sig') S = TermSubst.id sig' := by
  funext n s
  cases n with
  | zero      => rfl
  | succ n    => simp [lift, TermSubst.id, Term.shiftVar]

end TermSubst

namespace GeometricFormula

/-- Substitute free variables in a formula according to `σ`.

    Maps `GeometricFormula sig Γ` to `GeometricFormula sig Δ`, where `Γ` and `Δ`
    are phantom type parameters tracking binding depth (not enforced by Lean).
    The `exists_` case lifts `σ` to account for the new bound variable.

    **Structural recursion**: the `disj` index family `f i` is a strict subterm;
    the `exists_` body `φ` is a strict subterm. No `decreasing_by` needed.
-/
def subst {Γ Δ : List sig.sort} (σ : TermSubst sig) :
    GeometricFormula sig Γ → GeometricFormula sig Δ
  | .top              => top
  | .bot              => bot
  | .atom r as        => atom r (fun i => (as i).subst σ)
  | .conj φ ψ         => conj (φ.subst σ) (ψ.subst σ)
  | .disj (ι := ι) f  => @disj sig Δ ι (fun i => (f i).subst σ)
  | .exists_ S φ      => exists_ S (φ.subst (σ.lift S))

-- Definitional simp lemmas for each constructor
-- Using fully-qualified constructor names avoids dot-notation ambiguity with Equiv.conj.

@[simp]
theorem subst_top {Γ Δ : List sig.sort} (σ : TermSubst sig) :
    (top (Γ := Γ) : GeometricFormula sig Γ).subst (Δ := Δ) σ = top := rfl

@[simp]
theorem subst_bot {Γ Δ : List sig.sort} (σ : TermSubst sig) :
    (bot (Γ := Γ) : GeometricFormula sig Γ).subst (Δ := Δ) σ = bot := rfl

@[simp]
theorem subst_atom {Γ Δ : List sig.sort} (σ : TermSubst sig)
    {args : List sig.sort} (r : sig.rel args)
    (as : ∀ i : Fin args.length, Term sig (args.get i)) :
    (atom r as : GeometricFormula sig Γ).subst (Δ := Δ) σ =
    atom r (fun i => (as i).subst σ) := rfl

@[simp]
theorem subst_conj {Γ Δ : List sig.sort} (σ : TermSubst sig)
    (φ ψ : GeometricFormula sig Γ) :
    (conj φ ψ).subst (Δ := Δ) σ = conj (φ.subst σ) (ψ.subst σ) := rfl

/-- Substitution commutes with indexed disjunction componentwise. -/
@[simp]
theorem disj_subst {Γ Δ : List sig.sort} {ι : Type (max u (max v w))}
    (σ : TermSubst sig) (f : ι → GeometricFormula sig Γ) :
    (GeometricFormula.disj f).subst (Δ := Δ) σ =
    @disj sig Δ ι (fun i => (f i).subst σ) := rfl

@[simp]
theorem subst_exists_ {Γ Δ : List sig.sort} (σ : TermSubst sig)
    (S : sig.sort) (φ : GeometricFormula sig (S :: Γ)) :
    (exists_ S φ).subst (Δ := Δ) σ = exists_ S (φ.subst (σ.lift S)) := rfl

/-- Substitution by the identity leaves a formula unchanged. -/
theorem subst_id {Γ : List sig.sort} (φ : GeometricFormula sig Γ) :
    (φ.subst (TermSubst.id sig) : GeometricFormula sig Γ) = φ := by
  induction φ with
  | top         => rfl
  | bot         => rfl
  | atom r as   =>
      simp only [GeometricFormula.subst_atom]
      congr 1; funext i; exact Term.subst_id (as i)
  | conj φ ψ ih_φ ih_ψ =>
      simp only [GeometricFormula.subst_conj]; rw [ih_φ, ih_ψ]
  | disj f ih   =>
      simp only [GeometricFormula.disj_subst]
      congr 1; funext i; exact ih i
  | exists_ S φ ih =>
      simp only [GeometricFormula.subst_exists_]
      congr 1
      rw [TermSubst.id_lift sig]
      exact ih

/-- Composition of substitutions (associativity of subst).

    **Klasse-D shift to C22**: the `exists_` case requires the `lift`-`subst`
    commutation lemma (`(t.shiftVar).subst (lift τ S) = (t.subst τ).shiftVar`),
    deferred with `sorry`. -/
theorem subst_comp {Γ Δ Θ : List sig.sort} (σ τ : TermSubst sig)
    (φ : GeometricFormula sig Γ) :
    ((φ.subst (Δ := Δ) σ).subst (Δ := Θ) τ) = φ.subst (σ.comp τ) := by
  induction φ with
  | top         => rfl
  | bot         => rfl
  | atom r as   =>
      simp only [GeometricFormula.subst_atom]
      congr 1; funext i
      exact Term.subst_comp σ τ (as i)
  | conj φ ψ ih_φ ih_ψ =>
      simp only [GeometricFormula.subst_conj]; rw [ih_φ, ih_ψ]
  | disj f ih   =>
      simp only [GeometricFormula.disj_subst]
      congr 1; funext i; exact ih i
  | exists_ S φ ih =>
      simp only [GeometricFormula.subst_exists_]
      congr 1
      -- Klasse-D shift to C22: lift-comp commutation
      sorry

end GeometricFormula

end Reformulation.PathC.GeometricTheory
