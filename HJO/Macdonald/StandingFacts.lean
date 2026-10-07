/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Ascent.Embedding
public import HJO.Macdonald.FiniteAlphabet
public meta import HJO.Attr

/-! # The standing nonvanishing facts about the two parameters

The standing convention fixes `𝕜 := ℚ(q, u)` with `q` and `u` *indeterminates* for the
symmetric-function theory and everything built on it, and with it come the nonvanishing facts that
the results below spend: `q` and `u` are invertible, `qu ≠ 1`, no power of `u` is `1`, the parameter
product `(1 - q)(1 - u)` is nonzero, each factor `1 - q^a u^{l+1}` of Macdonald's normalising
product is nonzero, and the eigenvalues `E_n(μ) = ∑_{i=1}^n q^{μ_i} u^{n-i}` of Macdonald's operator
are nonzero and pairwise distinct. None of them is to be threaded as a hypothesis: each is a
consequence of the standing convention. **This file is where they are proved**, and the rest of the
Macdonald theory in this library cites them from here.

## Where these facts are stated, and why

They are stated twice, and the general form is the primary one.

The primary statements take a pair `q u : L` in an arbitrary commutative ring together with
`AlgebraicIndependent ℤ ![q, u]`: the two parameters satisfy no nonzero integer polynomial relation.
That is the hypothesis this library already carries everywhere it meets a general coefficient
field -- the collinear and shuffle inputs are stated at it, `HJO.Ascent.ascend` builds the embedding
`𝕜 → L` out of it -- and it excludes exactly the specialised parameter values, such as `u = 1` and
`u = -1`, at which these facts fail.

The second statements instantiate the first at the standing field itself, which needs no hypothesis:
`HJO.Ascent.algebraicIndependent_param` says that the two parameters `paramQ K`, `paramU K` of a
field presented as a field of fractions of `ParamRing = ℚ[q, u]` *are* algebraically independent
over `ℤ`. So the general form is not a weakening of the hypothesis-free statements at `𝕜`; it
implies them, and the `…_param` corollaries below are those hypothesis-free readings.

Stating the general form first is what keeps the ascent out of the Macdonald theory: a result proved
at a general pair needs no embedding, and a result proved only at `𝕜` has to be transported. The
theory pays nothing for the generality -- the proofs are identical -- and the two spellings sit in
one file, so citing either is one name.

## The engine

Every fact here is one corollary of one lemma. `aeval_ne_zero` says that a nonzero integer
polynomial in two variables does not vanish at an algebraically independent pair, which is the
contrapositive of the definition of algebraic independence; `ne_zero_of_aeval_ne_zero` says that a
polynomial taking one nonzero value is nonzero. Composed as `aeval_ne_zero_of_witness`, they turn
each bullet into a line naming the polynomial and one integer point at which it does not vanish.
For every bullet below that point is `(0, 0)`, where each of `1 - q^a u^{l+1}` (with `l + 1 ≥ 1`),
`1 - u^k` (with `k ≥ 1`), `1 - qu` and `(1 - q)(1 - u)` takes the value `1`.

Comparing coefficients instead is the obvious route and a trap: `C c` normalises to `Int.cast c`,
after which `MvPolynomial.coeff_C` no longer matches and the goal is left half-simplified.

## Main definitions

* `HJO.Sym.cellArm`, `HJO.Sym.cellLeg`: the arm `a_μ(c)` and the leg `l_μ(c)` of a cell.
* `HJO.Sym.normalisingProduct`: Macdonald's normalising product `γ_μ`.

## Main results

* `HJO.Standing.aeval_ne_zero`, `HJO.Standing.aeval_ne_zero_of_witness`: the engine.
* `HJO.Standing.q_ne_zero`, `HJO.Standing.u_ne_zero`: the parameters are invertible.
* `HJO.Standing.q_mul_u_ne_one`: `qu ≠ 1`.
* `HJO.Standing.u_pow_succ_ne_one`: no positive power of `u` is `1`.
* `HJO.Standing.paramProduct_ne_zero`: `M = (1 - q)(1 - u) ≠ 0`.
* `HJO.Standing.one_sub_pow_mul_pow_succ_ne_zero`: each factor `1 - q^a u^{l+1}` is nonzero.
* `HJO.Standing.pow_ne_pow_succ`: `q^a ≠ u^{l+1}`, which is that factor after inverting `u`.
* `HJO.Sym.normalisingProduct_ne_zero`: `γ_μ ≠ 0`.
* `HJO.Standing.paramQ_ne_zero`, …, `HJO.Standing.eq_of_macdonaldEigenvalue_param_eq`: the same
  facts at the standing field, with no hypothesis.

## The eigenvalue half

The two eigenvalue bullets are already proved, in this same general form, as
`HJO.Sym.macdonaldEigenvalue_ne_zero` and `HJO.Sym.eq_of_macdonaldEigenvalue_eq` of
`HJO/Macdonald/FiniteAlphabet.lean`. They are not restated here; their
hypothesis-free readings at the standing field are, as `macdonaldEigenvalue_param_ne_zero` and
`eq_of_macdonaldEigenvalue_param_eq`, so that all the facts listed above can be cited from one
place. The index range of the injectivity statement is the natural one: `μ` and `ν` are compared
in an alphabet of `n` letters under `μ_{n+1} = ν_{n+1} = 0`, which on `0`-indexed rows is
`μ.rowLen n = ν.rowLen n = 0`, the indices the alphabet does not truncate.

## References

The convention `𝕜 := ℚ(q, u)`, the definitions `HJO.Sym.cellArm`, `HJO.Sym.cellLeg` and
`HJO.Sym.normalisingProduct`, and the lemma `HJO.Sym.normalisingProduct_ne_zero`. Each of these
facts fails at suitable specialised parameter values, but every such value satisfies a nonzero
integer polynomial relation, hence is not a point of `𝕜` and does not refute anything here.
-/

@[expose] public section

open MvPolynomial

namespace HJO.Standing

/-! ### The engine: a nonzero polynomial does not vanish at an independent pair -/

section Engine

variable {L : Type*} [CommRing L] {q u : L}

/-- **A nonzero integer polynomial in two variables does not vanish at an algebraically independent
pair.** This is the contrapositive of the definition of algebraic independence, which is injectivity
of evaluation, and it is the whole mathematical content of this file: each standing fact below is
this lemma applied to one explicit polynomial. -/
theorem aeval_ne_zero (hqu : AlgebraicIndependent ℤ ![q, u]) {P : MvPolynomial (Fin 2) ℤ}
    (hP : P ≠ 0) : aeval ![q, u] P ≠ 0 :=
  fun h => hP (hqu (by simpa using h))

/-- **A polynomial with one nonzero value is nonzero.** Each nonvanishing claim below is settled by
evaluating at a single explicit integer point, which ordinary arithmetic closes. -/
theorem ne_zero_of_aeval_ne_zero {P : MvPolynomial (Fin 2) ℤ} (v : Fin 2 → ℤ)
    (h : aeval v P ≠ 0) : P ≠ 0 := fun hP => h (by simp [hP])

/-- **The two halves composed**: a polynomial that is nonzero at some integer point `v` is nonzero
at an algebraically independent pair. Every standing fact below is one application of this, naming
the polynomial and the witnessing point. -/
theorem aeval_ne_zero_of_witness (hqu : AlgebraicIndependent ℤ ![q, u])
    {P : MvPolynomial (Fin 2) ℤ} (v : Fin 2 → ℤ) (h : aeval v P ≠ 0) :
    aeval ![q, u] P ≠ 0 :=
  aeval_ne_zero hqu (ne_zero_of_aeval_ne_zero v h)

end Engine

/-! ### The elementary standing facts -/

section Elementary

variable {L : Type*} [CommRing L] {q u : L}

/-- **The dinv parameter is nonzero**, hence invertible in a field: the polynomial `q` is nonzero,
taking the value `1` at `(1, 0)`. -/
theorem q_ne_zero (hqu : AlgebraicIndependent ℤ ![q, u]) : q ≠ 0 := by
  have := aeval_ne_zero_of_witness hqu (P := X 0) ![1, 0] (by simp)
  simpa using this

/-- **The area parameter is nonzero**, hence invertible in a field: the polynomial `u` is nonzero,
taking the value `1` at `(0, 1)`. -/
theorem u_ne_zero (hqu : AlgebraicIndependent ℤ ![q, u]) : u ≠ 0 := by
  have := aeval_ne_zero_of_witness hqu (P := X 1) ![0, 1] (by simp)
  simpa using this

/-- **The product of the two parameters is not `1`**: the polynomial `1 - qu` is nonzero, taking the
value `1` at `(0, 0)`. This is the value `qu = 1` at which the monic eigenfunction of Macdonald's
operator fails to exist. -/
theorem q_mul_u_ne_one (hqu : AlgebraicIndependent ℤ ![q, u]) : q * u ≠ 1 := fun h => by
  have := aeval_ne_zero_of_witness hqu (P := 1 - X 0 * X 1) ![0, 0] (by simp)
  simp [h] at this

/-- **No positive power of the area parameter is `1`**: the polynomial `1 - u^{k+1}` is nonzero,
taking the value `1` at `(0, 0)` because the exponent is positive. This is what excludes `u` a root
of unity, at which the plethystic division stops being defined. -/
theorem u_pow_succ_ne_one (hqu : AlgebraicIndependent ℤ ![q, u]) (k : ℕ) : u ^ (k + 1) ≠ 1 :=
  fun h => by
    have := aeval_ne_zero_of_witness hqu (P := 1 - X 1 ^ (k + 1)) ![0, 0] (by simp)
    simp [h] at this

/-- **No positive power of the dinv parameter is `1`**, by the same argument at the other
variable. -/
theorem q_pow_succ_ne_one (hqu : AlgebraicIndependent ℤ ![q, u]) (k : ℕ) : q ^ (k + 1) ≠ 1 :=
  fun h => by
    have := aeval_ne_zero_of_witness hqu (P := 1 - X 0 ^ (k + 1)) ![0, 0] (by simp)
    simp [h] at this

/-- **The parameter product `M = (1 - q)(1 - u)` is nonzero**: the polynomial `(1 - q)(1 - u)` is
nonzero, taking the value `1` at `(0, 0)`. `M ≠ 0` is the side condition the modified Macdonald
family is stated with; at a generic pair it is not a hypothesis but this. -/
theorem paramProduct_ne_zero (hqu : AlgebraicIndependent ℤ ![q, u]) :
    HJO.Sym.paramProduct q u ≠ 0 := by
  have := aeval_ne_zero_of_witness hqu (P := (1 - X 0) * (1 - X 1)) ![0, 0] (by simp)
  simpa [HJO.Sym.paramProduct] using this

/-- **Neither parameter is `1`**: the left factor of the parameter product is nonzero. -/
theorem one_sub_q_ne_zero (hqu : AlgebraicIndependent ℤ ![q, u]) : 1 - q ≠ 0 :=
  left_ne_zero_of_mul (paramProduct_ne_zero hqu)

/-- **Neither parameter is `1`**: the right factor of the parameter product is nonzero. -/
theorem one_sub_u_ne_zero (hqu : AlgebraicIndependent ℤ ![q, u]) : 1 - u ≠ 0 :=
  right_ne_zero_of_mul (paramProduct_ne_zero hqu)

/-- **Each factor of Macdonald's normalising product is nonzero**: `1 - q^a u^{l+1} ≠ 0` for every
`a` and every `l`, the exponent of `u` being positive. The polynomial `1 - Q^a U^{l+1}` takes the
value `1` at `(0, 0)` for exactly that reason, and at a specialised parameter the claim is false --
at `u = -1` the factor with `a = 0` and `l = 1` is `1 - u^2 = 0`, and at `u = 1` every factor with
`a = 0` vanishes. -/
theorem one_sub_pow_mul_pow_succ_ne_zero (hqu : AlgebraicIndependent ℤ ![q, u]) (a l : ℕ) :
    1 - q ^ a * u ^ (l + 1) ≠ 0 := by
  have := aeval_ne_zero_of_witness hqu (P := 1 - X 0 ^ a * X 1 ^ (l + 1)) ![0, 0] (by simp)
  simpa using this

/-- **A power of one parameter is never a positive power of the other**: `q^a ≠ u^{l+1}`. This is
the form the *inverted* normalising product needs: `1 - q^a u^{-l-1}` is
`-q^a u^{-l-1}(1 - q^{-a} u^{l+1})`, whose second factor is nonzero exactly when `q^a ≠ u^{l+1}`,
and that factor is not one of the shapes the module docstring lists. Two cases: at
`a = 0` it is `u^{l+1} ≠ 1`, and at `a ≥ 1` the polynomial `Q^a - U^{l+1}` takes the value `-1` at
`(0, 1)`. -/
theorem pow_ne_pow_succ (hqu : AlgebraicIndependent ℤ ![q, u]) (a l : ℕ) :
    q ^ a ≠ u ^ (l + 1) := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simpa using fun h => u_pow_succ_ne_one hqu l h.symm
  · obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    intro h
    have := aeval_ne_zero_of_witness hqu (P := X 0 ^ (b + 1) - X 1 ^ (l + 1)) ![0, 1] (by simp)
    simp [h] at this

end Elementary

end HJO.Standing

/-! ### The arm, the leg and Macdonald's normalising product -/

namespace HJO.Sym

/-- The **arm** of a cell of a partition: `cellArm μ (i, j) = μ.rowLen i - (j + 1)`, the number of
cells of `μ` in the same row strictly to the right of `(i, j)`. This is the arm
`a_μ(i, j) = μ_i - j` of `1`-indexed cells read on the `0`-indexed cells of `HJO.Sym.cells`, where
the `1`-indexed cell `(i, j)` is the pair `(i - 1, j - 1)` and `μ_i` is `rowLen (i - 1)`. Off the
cells of `μ` the truncated subtraction of `ℕ` makes the value `0`; on a cell it does not truncate,
which is `cellArm_add`. -/
@[hjo "def_mac_arm"]
def cellArm (μ : YoungDiagram) (c : ℕ × ℕ) : ℕ := μ.rowLen c.1 - (c.2 + 1)

/-- The **leg** of a cell of a partition: `cellLeg μ (i, j) = μ.colLen j - (i + 1)`, the number of
cells of `μ` in the same column strictly below `(i, j)`. This is the leg
`l_μ(i, j) = #\{i' > i : μ_{i'} ≥ j\}` of `1`-indexed cells read on the `0`-indexed cells of
`HJO.Sym.cells`: a pair `(i', j)` is a cell exactly when `i' < μ.colLen j`, so the cells counted are
the `i'` with `i < i' < μ.colLen j` and there are `μ.colLen j - (i + 1)` of them, which is
`cellLeg_eq_card`. Off the cells of `μ` the truncated subtraction of `ℕ` makes the value `0`; on a
cell it does not truncate, which is `cellLeg_add`. -/
@[hjo "def_mac_leg"]
def cellLeg (μ : YoungDiagram) (c : ℕ × ℕ) : ℕ := μ.colLen c.2 - (c.1 + 1)

/-- The arm does not truncate on a cell: the cells of row `i` strictly to the right of `(i, j)`,
together with `(i, j)` itself and the `j` cells to its left, are the whole row. -/
theorem cellArm_add (μ : YoungDiagram) {i j : ℕ} (h : (i, j) ∈ μ) :
    cellArm μ (i, j) + (j + 1) = μ.rowLen i := by
  rw [YoungDiagram.mem_iff_lt_rowLen] at h
  simp only [cellArm]
  omega

/-- The leg does not truncate on a cell: the cells of column `j` strictly below `(i, j)`, together
with `(i, j)` itself and the `i` cells above it, are the whole column. -/
theorem cellLeg_add (μ : YoungDiagram) {i j : ℕ} (h : (i, j) ∈ μ) :
    cellLeg μ (i, j) + (i + 1) = μ.colLen j := by
  rw [YoungDiagram.mem_iff_lt_colLen] at h
  simp only [cellLeg]
  omega

/-- **The leg counts the cells below**: `cellLeg μ (i, j)` is the number of rows `i' > i` whose
`j`-th cell belongs to `μ`. The window `Finset.range (μ.colLen j)` is exactly the set of such `i'`
by `YoungDiagram.mem_iff_lt_colLen`, so this is the count `#\{i' > i : μ_{i'} ≥ j\}` and the
closed form of the definition is a count and not a convention. -/
theorem cellLeg_eq_card (μ : YoungDiagram) (i j : ℕ) :
    cellLeg μ (i, j) = {i' ∈ Finset.range (μ.colLen j) | i < i'}.card := by
  have hset : {i' ∈ Finset.range (μ.colLen j) | i < i'} = Finset.Ioo i (μ.colLen j) := by
    ext i'
    simp [Finset.mem_Ioo, and_comm]
  rw [hset, Nat.card_Ioo]
  simp only [cellLeg]
  omega

/-- **Macdonald's normalising product**: `γ_μ = ∏_{c ∈ μ} (1 - q^{a_μ(c)} u^{l_μ(c)+1})`, the
normalising factor of Macdonald's Chapter VI, equation (8.1), a finite product over the cells of
`μ`, written `c` there with the partition as a subscript. The exponent of `u` is the leg plus one,
so it is positive on every cell; `γ_∅ = 1`. -/
@[hjo "def_mac_cmu"]
noncomputable def normalisingProduct {K : Type*} [CommRing K] (q u : K) (μ : YoungDiagram) : K :=
  ∏ c ∈ cells μ, (1 - q ^ cellArm μ c * u ^ (cellLeg μ c + 1))

/-- **Macdonald's normalising product is nonzero.**

Classically it is stated with no hypothesis on `q` and `u`, its proof read off the embedding of
`ℚ[q, u]` in `𝕜`; the hypothesis carried here is that embedding's content, and by
`normalisingProduct_param_ne_zero` it is discharged at the standing field, so the hypothesis-free
statement is obtained and not weakened. Over a general field the statement is genuinely false: at
`u = -1` the index `(1, 1)` contributes `1 - u^2 = 0` and at `u = 1` every factor of every nonempty
index vanishes.

Each factor is nonzero by `HJO.Standing.one_sub_pow_mul_pow_succ_ne_zero`, and a finite product of
nonzero elements of a domain is nonzero. -/
@[hjo "lem_mac_cmu_ne_zero"]
theorem normalisingProduct_ne_zero {L : Type*} [CommRing L] [IsDomain L] {q u : L}
    (hqu : AlgebraicIndependent ℤ ![q, u]) (μ : YoungDiagram) :
    normalisingProduct q u μ ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _c _ =>
    HJO.Standing.one_sub_pow_mul_pow_succ_ne_zero hqu _ _

end HJO.Sym

/-! ### The same facts at the standing field, with no hypothesis

At a field `K` presented as a field of fractions of `ParamRing = ℚ[q, u]` -- the standing
`𝕜 = ℚ(q, u)`, spelled as in `HJO/Ascent/Embedding.lean` -- the hypothesis above is a theorem,
`HJO.Ascent.algebraicIndependent_param`, so each standing fact holds outright. These are the
hypothesis-free statements, and they are what a result reading `𝕜` should cite.
-/

namespace HJO.Standing

open HJO.Ascent

variable (K : Type*) [Field K] [Algebra ParamRing K] [IsFractionRing ParamRing K]

/-- The dinv parameter of the standing field is nonzero, hence invertible. -/
theorem paramQ_ne_zero : paramQ K ≠ 0 := q_ne_zero (algebraicIndependent_param K)

/-- The area parameter of the standing field is nonzero, hence invertible. -/
theorem paramU_ne_zero : paramU K ≠ 0 := u_ne_zero (algebraicIndependent_param K)

/-- The product of the two parameters of the standing field is not `1`. -/
theorem paramQ_mul_paramU_ne_one : paramQ K * paramU K ≠ 1 :=
  q_mul_u_ne_one (algebraicIndependent_param K)

/-- No positive power of the area parameter of the standing field is `1`. -/
theorem paramU_pow_succ_ne_one (k : ℕ) : paramU K ^ (k + 1) ≠ 1 :=
  u_pow_succ_ne_one (algebraicIndependent_param K) k

/-- No positive power of the dinv parameter of the standing field is `1`. -/
theorem paramQ_pow_succ_ne_one (k : ℕ) : paramQ K ^ (k + 1) ≠ 1 :=
  q_pow_succ_ne_one (algebraicIndependent_param K) k

/-- The parameter product `M = (1 - q)(1 - u)` of the standing field is nonzero. -/
theorem paramProduct_param_ne_zero : HJO.Sym.paramProduct (paramQ K) (paramU K) ≠ 0 :=
  paramProduct_ne_zero (algebraicIndependent_param K)

/-- Each factor `1 - q^a u^{l+1}` of Macdonald's normalising product is nonzero at the standing
field. -/
theorem one_sub_pow_mul_pow_succ_param_ne_zero (a l : ℕ) :
    1 - paramQ K ^ a * paramU K ^ (l + 1) ≠ 0 :=
  one_sub_pow_mul_pow_succ_ne_zero (algebraicIndependent_param K) a l

/-- A power of one parameter of the standing field is never a positive power of the other, which is
the factor of the inverted normalising product. -/
theorem pow_ne_pow_succ_param (a l : ℕ) : paramQ K ^ a ≠ paramU K ^ (l + 1) :=
  pow_ne_pow_succ (algebraicIndependent_param K) a l

/-- **Macdonald's normalising product is nonzero at the standing field**, the hypothesis-free form
of `HJO.Sym.normalisingProduct_ne_zero`: no hypothesis on the parameters, the nonvanishing coming
from their being indeterminates. -/
theorem normalisingProduct_param_ne_zero (μ : YoungDiagram) :
    HJO.Sym.normalisingProduct (paramQ K) (paramU K) μ ≠ 0 :=
  HJO.Sym.normalisingProduct_ne_zero (algebraicIndependent_param K) μ

/-- **The eigenvalue of Macdonald's operator is nonzero at the standing field**, the hypothesis-free
form of the general statement `HJO.Sym.macdonaldEigenvalue_ne_zero`. -/
theorem macdonaldEigenvalue_param_ne_zero {n : ℕ} (hn : 0 < n) (μ : YoungDiagram) :
    HJO.Sym.macdonaldEigenvalue (paramQ K) (paramU K) n μ ≠ 0 :=
  HJO.Sym.macdonaldEigenvalue_ne_zero (algebraicIndependent_param K) hn μ

/-- **The eigenvalue determines the partition at the standing field**, the hypothesis-free
form of `HJO.Sym.eq_of_macdonaldEigenvalue_eq`: two partitions that the alphabet of `n` letters
does not truncate -- `μ_{n+1} = ν_{n+1} = 0`, here `μ.rowLen n = ν.rowLen n = 0` on `0`-indexed
rows -- and that have the same eigenvalue are equal. The general form is
`HJO.Sym.eq_of_macdonaldEigenvalue_eq`. -/
theorem eq_of_macdonaldEigenvalue_param_eq {n : ℕ} {μ ν : YoungDiagram} (hμ : μ.rowLen n = 0)
    (hν : ν.rowLen n = 0)
    (h : HJO.Sym.macdonaldEigenvalue (paramQ K) (paramU K) n μ =
      HJO.Sym.macdonaldEigenvalue (paramQ K) (paramU K) n ν) : μ = ν :=
  HJO.Sym.eq_of_macdonaldEigenvalue_eq (algebraicIndependent_param K) hμ hν h

end HJO.Standing
