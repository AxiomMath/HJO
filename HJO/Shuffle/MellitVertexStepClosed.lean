/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.MellitColumnElemSymmTwo
public import HJO.Shuffle.MellitShiftDop
public meta import HJO.Attr

/-! # The vertex step on `V_1` in closed form, `[T,A]` closed, and the `(a,1)` column inside the
`D_n`-algebra

`HJO/Shuffle/MellitVertexStepGeneral.lean` computes `T` on a monomial of `V_1` as a
**truncated** Jing generating function (`HJO.Sweep.vertexStep_auxVar_pow_mul_C_closed`):

`T(y_1^mCA) = ∑_{j<m}(uy_1)^jB_{m-j}(d^*_+(CA)) + (uy_1)^mT(CA)`,

and records that iterating fails because the cut-off is the `y_1`-degree of the argument while
`d^*_+` raises that degree. The remainder `T(CA)` is left un-evaluated, and it is the whole of the
obstruction: everything above it is the two-term recursion.

## The closed form

**This file evaluates the remainder.** The cut-off is traded for negative Hall--Littlewood indices:

`T(y_1^mCA) = ∑_{l ≥ 0}(quy_1)^l d^*_+(C B_{m-l}A)`
(`HJO.Sweep.vertexStep_auxVar_pow_mul_C_eq_sum_dplusStar`),

a **finite** sum for each `A` --- `B_r` kills `A` once `r` drops below minus the degree of the
displacement `β A` (`HJO.Sym.bop_eq_zero_of_lt_neg_natDegree`,
`HJO.Sweep.bopExt_eq_zero_of_lt`) --- and in particular at `m = 0`

`T(CA) = ∑_{l ≥ 0}(quy_1)^l d^*_+(C B_{-l}A)`   (`HJO.Sweep.vertexStep_C_eq_sum_dplusStar`).

Two things change. First, **every summand has the shape `d^*_+` of a constant**, i.e. the shape
`A = d^*_+{}^{(0)}d_-^{(1)}` produces, with no `N = d_-^{(2)}d^*_+{}^{(1)}` term left: of the two
orders of `B_m` against the shift, `T` is a series in the *first* alone,
`T = ∑_{l ≥ 0}(qu)^l(y_1·)^lA_{(-l)}` where `A_{(j)}(y_1^mCA) = d^*_+(CB_{m+j}A)` and
`A_{(0)} = A`. Second, the truncation is gone: the bound is the `Λ`-degree of `A`, not the
`y_1`-degree of the argument, so the two sides of the recursion have the *same* shape.

The proof is the vertex relation `HJO.Sweep.dplusStar_C_bop_sub` (`HJO.Sweep.alphabetShift_bopExt`
composed for the two letters of `d^*_+`) rescaled into a one-step recursion for the *residue*
`Q_i = d^*_+(CB_iA) - q·B_i(d^*_+(CA))`,

`Q_i = (1-q)d^*_+(CB_iA) + quy_1·Q_{i-1}`   (`HJO.Sweep.vertexRes_recursion`),

telescoped with the remainder carried (`HJO.Sweep.vertexRes_eq_sum`) and discharged once; `Q_m` is
`(1-q)T(y_1^mCA)` by `HJO.Sweep.scal_sub_mul_vertexStep_auxVar_pow_mul_C`. The `B_{m-R-1}A = 0` half
of the discharge comes from the `bopExt` half through
`HJO.Sweep.constantCoeff_dplusStar_C`. Cross-check:
`HJO.Sweep.vertexStep_auxVar_of_closed` reproves `HJO.Sweep.vertexStep_auxVar`.

## The lowering operator at a negative index, and the composition law

The closed form puts `T(y_1^mCA)` in the span of `y_1^ld^*_+(Cg)`, and re-applying `T` needs `T` on
`d^*_+(Cg)`, which is not a monomial. Expanding it monomial by monomial produces the operators
`E_n = ∑_i B_{n+i}∘γ_i` on `Λ`, where `d^*_+(Cg) = ∑_i y_1^iC(γ_ig)`. For `n ≥ 0` these are the
basic operators `D_n` of `HJO.Sym.DopInt`, because `E_n = d_-(y_1^n·)∘d^*_+` there. For `n < 0` the
*operator* `d_-(y_1^n·)` does not exist --- one cannot divide by `y_1` --- and the fix is to shift
the coefficient extraction instead of the argument:

* `HJO.Sweep.lowerCoeffInt` --- `d_-`'s extraction at an index `n ∈ ℤ`, sending `y^d` to
  `c_{n+d_0}y^{d - d_0}` with `c` the alternating elementary family. At `n = 0` it is
  `HJO.Sweep.lowerCoeff L 0` (`HJO.Sweep.lowerCoeffInt_zero`) and it absorbs a power of `y_1`
  (`HJO.Sweep.lowerCoeffInt_X_pow_mul`), which is the `n ≥ 0` realisation.
* `HJO.Sweep.dminusInt` --- that extraction after `τ^-_{1,1}`, so `d^{(n)}_-`; at `n = m ≥ 0` it is
  `d_-^{(1)}(y_1^m·)` (`HJO.Sweep.dminusInt_natCast`), and on a monomial it is
  `d^{(n)}_-(y_1^mCA) = C(B_{n+m}A)` (`HJO.Sweep.dminusInt_auxVar_pow_mul_C`) at every integer `n`.
* **The bridge** `HJO.Sweep.dminusInt_dplusStar_C`: `d^{(n)}_-(d^*_+(Cg)) = C(D_ng)` with `D_n` the
  integer-indexed `HJO.Sym.DopInt` (`HJO.Sym.DopInt` at `n ∈ ℤ`), **at every integer `n` and with no
  hypothesis on `q` or `u`**. The content is that the displacement of `HJO.Sym.Bop` composed with
  the displacement of `HJO.Sweep.dplusStar` is the displacement of `HJO.Sym.DopInt` ---
  `X - (q-1)/z` after `X + (q-1)u/z` is `X + M/z`, which is
  `HJO.Sweep.qshiftNeg_cycleShift_qshift_C` --- and that the extraction reads only the total
  exponent, the two pairing families agreeing by `HJO.Sym.elemSymmAlt_eq_esymmSigned`. Cross-check:
  `HJO.Sweep.dminus_auxVar_pow_mul_dplusStar_C_of_dminusInt` reproves the `n ≥ 0` family
  through this route.

Hence **the composition law** (`HJO.Sweep.vertexStep_auxVar_pow_mul_dplusStar_C_eq_sum`):

`T(y_1^jd^*_+(Cg)) = ∑_{l ≥ 0}(quy_1)^l d^*_+(C D_{j-l}g)`,

so `T` acts on the pairs `(j,g)` by `(j,g) ↦ ∑_l(qu)^l(l, D_{j-l}g)` --- a rule that does not read
the previous step. **`T^b` composes**, which the truncated form did not give. The general-`V_1`
statement, before the bridge is applied, is
`HJO.Sweep.vertexStep_auxVar_pow_mul_of_mem_piece_eq_sum`, and the hypothesis on `R` is
dischargeable for every large enough `R`
(`HJO.Sweep.exists_forall_bopExt_dplusStar_coeff_eq_zero`).

## `[T, A]` in closed form

`A∘T` and `T∘A` are both closed on the spanning family
(`HJO.Sweep.vertexA_vertexStep_auxVar_pow_mul_dplusStar_C`,
`HJO.Sweep.vertexStep_vertexA_auxVar_pow_mul_dplusStar_C`), hence
(`HJO.Sweep.comm_vertexStep_vertexA_auxVar_pow_mul_dplusStar_C`)

`[T,A](y_1^jd^*_+(Cg)) = ∑_{l ≥ 0}(quy_1)^ld^*_+(C D_{-l}D_jg)`
`  - d^*_+(C ∑_{l ≥ 0}(qu)^lD_lD_{j-l}g)`.

The `l = 0` terms of the two sums are both `d^*_+(CD_0D_jg)` and cancel, which is `A` commuting with
itself. Since `[N,A] = -(1-q)/q·[T,A]`
(`HJO.Sweep.comm_vertexN_vertexA_eq_smul_comm_vertexStep_vertexA`) this is a closed form for `[N,A]`
too. Before the bridge, on monomials, the second term alone is closed:
`HJO.Sweep.vertexA_vertexStep_auxVar_pow_mul_C`,
`HJO.Sweep.comm_vertexStep_vertexA_auxVar_pow_mul_C`.

## What this does to the `(a,1)` column

One step of the column's tower is closed inside the `D_n` at every `K, j ≥ 0`
(`HJO.Sweep.dminus_auxVar_pow_mul_vertexStep_auxVar_pow_mul_dplusStar_C`):

`d_-(y_1^KT(y_1^jd^*_+(Cg))) = ∑_{l ≥ 0}(qu)^lD_{K+l}(D_{j-l}g)`,

so iterating gives `ψ_b(f) = d_-(y_1T^b(Φf))` as
`∑_{l_1,…,l_b ≥ 0}(qu)^{l_1+⋯+l_b}D_{l_b+1}D_{l_{b-1}-l_b}⋯D_{l_1-l_2}D_{-l_1}f`, finite because
`D_n` shifts degree by `n` (`HJO.Sym.dopInt_shiftsDegree`). The case `b = 1` is proved here:

`ψ_1 = ∑_{l ≥ 0}(qu)^lD_{1+l}D_{-l}`   (`HJO.Sweep.psiCol_one_eq_sum_dopInt`),

and with `ψ_0 = D_1` (`HJO.Sweep.psiCol_zero`) the `b = 0` instance of `HJO.Sweep.ColumnCommutes`
becomes, at each `f`, an identity with no sweep module in it at all
(`HJO.Sweep.columnCommutes_zero_at_iff_dopInt`):

`M·∑_{l ≥ 0}(qu)^lD_{1+l}(D_{-l}f) = D_1(D_0f) - D_0(D_1f)`.

**That last statement is an equivalence, not a proof**: it is the `b = 0` clause of the column
translated, and its two sides are the two sides of that clause.
What it changes is the *category*: the statement is now an identity between compositions of
`HJO.Sym.DopInt`'s operators at integer indices, where `HJO.Sym.bop_pair_antisymm` and the
`HJO.Sym.bop_bop` family of `HJO/CMStructure/BopPairPhi.lean` are available, and where no operator
of the sweep module occurs. Everything before it in this file is an evaluation, not a translation:
the closed form, the bridge, the composition law and `[T,A]` each hold unconditionally (given the
stated support hypothesis and `q ≠ 1`) and none of them has the column as a hypothesis.

## Genericity

`HJO.Sym.bop_eq_zero_of_lt_neg_natDegree`, `HJO.Sweep.bopExt_eq_zero_of_lt`,
`HJO.Sweep.vertexRes_recursion`, `HJO.Sweep.vertexRes_eq_sum`, the whole
`HJO.Sweep.lowerCoeffInt` and `HJO.Sweep.dminusInt` construction and the bridge
`HJO.Sweep.dminusInt_dplusStar_C` carry **no hypothesis on `q` or `u`**. `q ≠ 1` enters the closed
form and everything after it, and it is real rather than an artefact: `HJO.Sweep.zop`'s scalar
`q/(1-q)` is `0` at `q = 1` in a field, so `T = A` there while the closed form's `l ≥ 1` terms do
not vanish. `q ≠ 0` and `u ≠ 0` appear only in `HJO.Sweep.psiCol_one_eq_sum_dopInt` and
`HJO.Sweep.columnCommutes_zero_at_iff_dopInt`, inherited from `HJO.Sweep.psiCol_eq`, where they
cancel `HJO.Sweep.slopeOperator`'s `(qu)^{-1}`. There is no hypothesis on `u - 1` anywhere, and
nothing here divides by `M`.

## What this file does not prove

`HJO.Mellit.lhsRewrite_sweepWitness` is **not** proved here: it is stated at a general `f` and a
general slope. `HJO.Mellit.shuffle_of_lhs_and_induction` has two binders, `hlhs`
and `hind`; nothing here touches `hind`, and `hlhs` is quantified over `1 < a < b`, so the `(a,1)`
column is not an instance of it either.

## References

Transcribing A. Mellit, *Toric braids and `(m, n)`-parking functions*, §3.
-/

@[expose] public section

namespace HJO.Sym

variable {K : Type*} [CommRing K] [Algebra ℚ K]

/-- **`B_r` vanishes below the displacement's degree.** -/
theorem bop_eq_zero_of_lt_neg_natDegree (q : K) (f : Lambda K) {r : ℤ}
    (hr : r < -((plethHallLittlewood q f).natDegree : ℤ)) : Bop q r f = 0 := by
  rw [bop_apply, Polynomial.sum]
  refine Finset.sum_eq_zero fun j hj => ?_
  have hj' : j ≤ (plethHallLittlewood q f).natDegree :=
    Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hj)
  rw [elemSymmAlt_of_neg (by omega), mul_zero]

theorem exists_bop_eq_zero (q : K) (f : Lambda K) :
    ∃ N : ℕ, ∀ r : ℤ, r < -(N : ℤ) → Bop q r f = 0 :=
  ⟨(plethHallLittlewood q f).natDegree, fun _ hr => bop_eq_zero_of_lt_neg_natDegree q f hr⟩

end HJO.Sym

namespace HJO.Sweep

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-! ### The coefficientwise extension vanishes at low index -/

/-- An explicit index below which `HJO.Sweep.bopExt` kills `F`: the largest degree, over the
`y`-monomials of `F`, of the displacement `β` of `HJO.Sym.Bop`. -/
noncomputable def bopExtBound (q : L) (F : Total L) : ℕ :=
  F.support.sup fun d => (Sym.plethHallLittlewood q (MvPolynomial.coeff d F)).natDegree

theorem bopExt_eq_zero_of_lt (q : L) (F : Total L) {r : ℤ}
    (hr : r < -((bopExtBound q F : ℕ) : ℤ)) : bopExt q r F = 0 := by
  refine MvPolynomial.ext _ _ fun d => ?_
  rw [coeff_bopExt, MvPolynomial.coeff_zero]
  by_cases hd : MvPolynomial.coeff d F = 0
  · rw [hd, map_zero]
  · refine Sym.bop_eq_zero_of_lt_neg_natDegree q _ ?_
    have hle : (Sym.plethHallLittlewood q (MvPolynomial.coeff d F)).natDegree ≤ bopExtBound q F :=
      Finset.le_sup (f := fun e =>
        (Sym.plethHallLittlewood q (MvPolynomial.coeff e F)).natDegree)
        (MvPolynomial.mem_support_iff.mpr hd)
    omega

theorem exists_bopExt_eq_zero (q : L) (F : Total L) :
    ∃ N : ℕ, ∀ r : ℤ, r < -(N : ℤ) → bopExt q r F = 0 :=
  ⟨bopExtBound q F, fun _ hr => bopExt_eq_zero_of_lt q F hr⟩

/-! ### The letter `quy_1` -/

omit [Algebra ℚ L] in
theorem scal_mul_starLetter_eq_smul (q u : L) :
    (scal q * starLetter u : Total L) = (q * u) • (auxVar 1 : Total L) := by
  rw [starLetter, smul_eq_scal_mul, scal_mul, mul_assoc]

omit [Algebra ℚ L] in
theorem scal_mul_starLetter_pow (q u : L) (l : ℕ) :
    (scal q * starLetter u : Total L) ^ l = ((q * u) ^ l) • ((auxVar 1 : Total L) ^ l) := by
  rw [scal_mul_starLetter_eq_smul, smul_pow]

/-! ### The residue of the vertex relation, and its telescoping -/

/-- The cleared vertex step at an *integer* index: `Q_i = d^*_+(CB_iA) - q·B_i(d^*_+(CA))`. -/
theorem vertexRes_recursion (q u : L) (i : ℤ) (A : Sym.Lambda L) :
    dplusStar q u 0 (MvPolynomial.C (Sym.Bop q i A) : Total L)
        - scal q * bopExt q i (dplusStar q u 0 (MvPolynomial.C A : Total L))
      = (1 - scal q) * dplusStar q u 0 (MvPolynomial.C (Sym.Bop q i A) : Total L)
        + (scal q * starLetter u)
          * (dplusStar q u 0 (MvPolynomial.C (Sym.Bop q (i - 1) A) : Total L)
              - scal q * bopExt q (i - 1) (dplusStar q u 0 (MvPolynomial.C A : Total L))) := by
  linear_combination (scal q : Total L) * dplusStar_C_bop_sub q u i A

theorem vertexRes_eq_sum (q u : L) (A : Sym.Lambda L) (i : ℤ) (R : ℕ) :
    dplusStar q u 0 (MvPolynomial.C (Sym.Bop q i A) : Total L)
        - scal q * bopExt q i (dplusStar q u 0 (MvPolynomial.C A : Total L))
      = (1 - scal q) * (∑ l ∈ Finset.range (R + 1), (scal q * starLetter u) ^ l
            * dplusStar q u 0 (MvPolynomial.C (Sym.Bop q (i - (l : ℤ)) A) : Total L))
        + (scal q * starLetter u) ^ (R + 1)
          * (dplusStar q u 0 (MvPolynomial.C (Sym.Bop q (i - ((R : ℤ) + 1)) A) : Total L)
              - scal q
                * bopExt q (i - ((R : ℤ) + 1))
                    (dplusStar q u 0 (MvPolynomial.C A : Total L))) := by
  induction R with
  | zero =>
      rw [Finset.sum_range_one]
      norm_num
      exact vertexRes_recursion q u i A
  | succ R ih =>
      conv_rhs => rw [Finset.sum_range_succ]
      rw [ih, vertexRes_recursion q u (i - ((R : ℤ) + 1)) A]
      push_cast
      ring_nf

/-! ### The closed form of the vertex step on `V_1` -/

/-- **The vertex step on a monomial of `V_1`, in closed form and with no truncation:**

`T(y_1^mCA) = ∑_{l ≥ 0}(quy_1)^l d^*_+(C B_{m-l}A)`. -/
@[hjo "lem_mellit_vertex_closed_form"]
theorem vertexStep_auxVar_pow_mul_C_eq_sum_dplusStar (hq1 : q ≠ 1) (m R : ℕ) (A : Sym.Lambda L)
    (hR : bopExt q ((m : ℤ) - ((R : ℤ) + 1)) (dplusStar q u 0 (MvPolynomial.C A : Total L)) = 0) :
    vertexStep q u ((auxVar 1 : Total L) ^ m * MvPolynomial.C A)
      = ∑ l ∈ Finset.range (R + 1), ((q * u) ^ l) •
          ((auxVar 1 : Total L) ^ l
            * dplusStar q u 0 (MvPolynomial.C (Sym.Bop q ((m : ℤ) - (l : ℤ)) A) : Total L)) := by
  have hne : (1 - scal q : Total L) ≠ 0 := by
    rw [show (1 - scal q : Total L) = scal (1 - q) from by rw [scal_sub, scal_one]]
    simp only [scal, ne_eq, MvPolynomial.C_eq_zero, sub_eq_zero]
    exact fun h => hq1 h.symm
  have hcc : MvPolynomial.coeff (0 : ℕ →₀ ℕ) (dplusStar q u 0 (MvPolynomial.C A : Total L)) = A :=
    constantCoeff_dplusStar_C q u 0 A
  have hB : Sym.Bop q ((m : ℤ) - ((R : ℤ) + 1)) A = 0 := by
    have h0 := congrArg (MvPolynomial.coeff (0 : ℕ →₀ ℕ)) hR
    rw [coeff_bopExt, MvPolynomial.coeff_zero, hcc] at h0
    exact h0
  have hres := vertexRes_eq_sum (q := q) (u := u) A (m : ℤ) R
  rw [hB, hR, map_zero, map_zero, mul_zero, sub_zero, mul_zero, add_zero] at hres
  have hT := scal_sub_mul_vertexStep_auxVar_pow_mul_C (q := q) (u := u) hq1 m A
  rw [hres] at hT
  have hgoal : (1 - scal q : Total L)
      * vertexStep q u ((auxVar 1 : Total L) ^ m * MvPolynomial.C A)
    = (1 - scal q : Total L) * ∑ l ∈ Finset.range (R + 1), ((q * u) ^ l) •
          ((auxVar 1 : Total L) ^ l
            * dplusStar q u 0 (MvPolynomial.C (Sym.Bop q ((m : ℤ) - (l : ℤ)) A) : Total L)) := by
    rw [hT, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [scal_mul_starLetter_pow, smul_mul_assoc, mul_smul_comm]
  exact mul_left_cancel₀ hne hgoal

/-- There is always such an `R`. -/
theorem exists_vertexStep_auxVar_pow_mul_C_eq_sum_dplusStar (hq1 : q ≠ 1) (m : ℕ)
    (A : Sym.Lambda L) :
    ∃ R : ℕ, vertexStep q u ((auxVar 1 : Total L) ^ m * MvPolynomial.C A)
      = ∑ l ∈ Finset.range (R + 1), ((q * u) ^ l) •
          ((auxVar 1 : Total L) ^ l
            * dplusStar q u 0 (MvPolynomial.C (Sym.Bop q ((m : ℤ) - (l : ℤ)) A) : Total L)) := by
  obtain ⟨N, hN⟩ := exists_bopExt_eq_zero q (dplusStar q u 0 (MvPolynomial.C A : Total L))
  refine ⟨m + N, vertexStep_auxVar_pow_mul_C_eq_sum_dplusStar hq1 m (m + N) A (hN _ ?_)⟩
  push_cast
  omega

/-- **The vertex step on the constants of `V_1`**, the `m = 0` case: `T(CA)` is *not* a two-term
expression but the whole series in the negative Hall--Littlewood indices,
`T(CA) = ∑_{l ≥ 0}(quy_1)^l d^*_+(C B_{-l}A)`. This is the datum the truncated form left
un-evaluated. -/
theorem vertexStep_C_eq_sum_dplusStar (hq1 : q ≠ 1) (R : ℕ) (A : Sym.Lambda L)
    (hR : bopExt q (-((R : ℤ) + 1)) (dplusStar q u 0 (MvPolynomial.C A : Total L)) = 0) :
    vertexStep q u (MvPolynomial.C A : Total L)
      = ∑ l ∈ Finset.range (R + 1), ((q * u) ^ l) •
          ((auxVar 1 : Total L) ^ l
            * dplusStar q u 0 (MvPolynomial.C (Sym.Bop q (-(l : ℤ)) A) : Total L)) := by
  have h := vertexStep_auxVar_pow_mul_C_eq_sum_dplusStar (q := q) (u := u) hq1 0 R A (by
    simpa using hR)
  rw [pow_zero, one_mul] at h
  rw [h]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [show ((0 : ℕ) : ℤ) - (l : ℤ) = -(l : ℤ) from by push_cast; ring]

/-! ### `d_-` on the image of the plethystic shift, at every power of `y_1` -/

/-- **`d_-(y_1^l d^*_+(Cg)) = C(D_lg)` at every `l ≥ 0`**: the
`HJO.Sweep.dop_eq_neg_dminusCM_auxVar_pow_dplusStar` family
(`HJO.Sweep.dop_succ_eq_dminus_auxVar_pow_dplusStar`) and its `l = 0` member
`HJO.Sweep.dop_zero_eq_dminus_dplusStar`, as one statement. -/
theorem dminus_auxVar_pow_mul_dplusStar_C (q u : L) (l : ℕ) (g : Sym.Lambda L) :
    dminus q 1 ((auxVar 1 : Total L) ^ l * dplusStar q u 0 (MvPolynomial.C g : Total L))
      = MvPolynomial.C (Sym.Dop q u l g) := by
  match l with
  | 0 => rw [pow_zero, one_mul, ← dop_zero_eq_dminus_dplusStar]
  | l + 1 => rw [← dop_succ_eq_dminus_auxVar_pow_dplusStar]

/-! ### `A ∘ T` factors through `Λ`, with an explicit `Λ`-side operator -/

/-- **`A(T(y_1^mCA)) = Φ(∑_l (qu)^l D_l B_{m-l}A)`.**

Composing the closed form with `HJO.Sweep.dminus_auxVar_pow_mul_dplusStar_C`: each summand
`(quy_1)^ld^*_+(CB_{m-l}A)` of `T(y_1^mCA)` is sent by `d_-` to `C(D_l(B_{m-l}A))`, so `A∘T` is the
plethystic shift applied to one explicit operator on `Λ` --- the Hall--Littlewood operators of
`HJO.Sym.Bop` and the basic operators of `HJO.Sym.DopInt`, paired index against index. -/
theorem vertexA_vertexStep_auxVar_pow_mul_C (hq1 : q ≠ 1) (m R : ℕ) (A : Sym.Lambda L)
    (hR : bopExt q ((m : ℤ) - ((R : ℤ) + 1)) (dplusStar q u 0 (MvPolynomial.C A : Total L)) = 0) :
    vertexA q u (vertexStep q u ((auxVar 1 : Total L) ^ m * MvPolynomial.C A))
      = dplusStar q u 0 (MvPolynomial.C (∑ l ∈ Finset.range (R + 1),
          ((q * u) ^ l) • Sym.Dop q u l (Sym.Bop q ((m : ℤ) - (l : ℤ)) A)) : Total L) := by
  rw [vertexA_apply, vertexStep_auxVar_pow_mul_C_eq_sum_dplusStar hq1 m R A hR]
  refine congrArg _ ?_
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_smul, dminus_auxVar_pow_mul_dplusStar_C, C_smul]

/-- **`[T, A]` on a monomial of `V_1`, in closed form up to one `T`-value on the image of the
shift.** The second term is fully explicit --- `Φ` of an operator on `Λ`; the first is `T` applied
to `Φ(CB_mA)`, and closing *it* is exactly the negative-index bridge discussed in the module
docstring. -/
theorem comm_vertexStep_vertexA_auxVar_pow_mul_C (hq1 : q ≠ 1) (m R : ℕ) (A : Sym.Lambda L)
    (hR : bopExt q ((m : ℤ) - ((R : ℤ) + 1)) (dplusStar q u 0 (MvPolynomial.C A : Total L)) = 0) :
    (vertexStep q u * vertexA q u - vertexA q u * vertexStep q u)
        ((auxVar 1 : Total L) ^ m * MvPolynomial.C A)
      = vertexStep q u (dplusStar q u 0 (MvPolynomial.C (Sym.Bop q (m : ℤ) A) : Total L))
        - dplusStar q u 0 (MvPolynomial.C (∑ l ∈ Finset.range (R + 1),
            ((q * u) ^ l) • Sym.Dop q u l (Sym.Bop q ((m : ℤ) - (l : ℤ)) A)) : Total L) := by
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
    vertexA_vertexStep_auxVar_pow_mul_C hq1 m R A hR, vertexA_apply,
    dminus_one_auxVar_pow_mul_C]

/-! ### Cross-check against the known value on `y_1` -/

/-- **Cross-check: the closed form reproves `HJO.Sweep.vertexStep_auxVar`.** -/
theorem vertexStep_auxVar_of_closed (hq1 : q ≠ 1) :
    vertexStep q u (auxVar 1 : Total L)
      = -(MvPolynomial.C (Sym.elemSymm L 1) : Total L) + u • (auxVar 1 : Total L) := by
  have hR : bopExt q ((1 : ℤ) - ((1 : ℤ) + 1))
      (dplusStar q u 0 (MvPolynomial.C (1 : Sym.Lambda L) : Total L)) = 0 := by
    rw [MvPolynomial.C_1, dplusStar_one, ← MvPolynomial.C_1 (σ := ℕ) (R := Sym.Lambda L),
      bopExt_C, Sym.bop_one, Sym.elemSymmAlt_of_neg (by norm_num), map_zero]
  have h := vertexStep_auxVar_pow_mul_C_eq_sum_dplusStar (q := q) (u := u) hq1 1 1 1 hR
  rw [MvPolynomial.C_1, mul_one, pow_one] at h
  rw [h, Finset.sum_range_succ, Finset.sum_range_one]
  norm_num [Sym.bop_one]
  rw [Sym.elemSymmAlt_zero, MvPolynomial.C_1, dplusStar_one,
    show Sym.elemSymmAlt L (1 : ℤ) = -(Sym.elemSymm L 1) from by
      rw [show ((1 : ℤ)) = ((1 : ℕ) : ℤ) from rfl, Sym.elemSymmAlt_natCast]; simp,
    map_neg, map_neg, dplusStar_C_elemSymm_one_smul, mul_one]
  match_scalars <;> ring

end HJO.Sweep

namespace HJO.Sym

variable {K : Type*} [Field K] [Algebra ℚ K]

/-- `HJO.Sym.elemSymmAlt` and `HJO.Sym.esymmSigned` are the same family, `(-1)^me_m` above `0` and
`0` below: `HJO.Sym.Bop` pairs against one and `HJO.Sym.DopInt` against the other. -/
theorem elemSymmAlt_eq_esymmSigned (m : ℤ) : elemSymmAlt K m = esymmSigned K m := by
  rw [elemSymmAlt, esymmSigned]

end HJO.Sym

namespace HJO.Sweep

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-! ### The coefficient extraction of `d_-` at an integer index -/

/-- **`d_-`'s coefficient extraction, shifted to an integer index.** On the `Λ`-basis of
`y`-monomials it sends `y^d` to `c_{n+d_0}` times `y^d` with the exponent of `y_1` deleted, where
`c_m` is the alternating elementary family of `HJO.Sym.elemSymmAlt`, read as `0` at a negative
index.
At `n = 0` it is `HJO.Sweep.lowerCoeff L 0` (`HJO.Sweep.lowerCoeffInt_zero`), and at `n = m ≥ 0` it
is that composed with multiplication by `y_1^m` (`HJO.Sweep.lowerCoeffInt_X_pow_mul`); at `n < 0`
there is no such realisation, which is the whole reason this declaration exists. -/
noncomputable def lowerCoeffInt (L : Type*) [Field L] [Algebra ℚ L] (n : ℤ) :
    Total L →ₗ[Sym.Lambda L] Total L :=
  (MvPolynomial.basisMonomials ℕ (Sym.Lambda L)).constr (Sym.Lambda L) fun d =>
    MvPolynomial.C (Sym.elemSymmAlt L (n + (d 0 : ℤ))) *
      MvPolynomial.monomial (Finsupp.erase 0 d) 1

theorem lowerCoeffInt_monomial (n : ℤ) (d : ℕ →₀ ℕ) :
    lowerCoeffInt L n (MvPolynomial.monomial d 1)
      = MvPolynomial.C (Sym.elemSymmAlt L (n + (d 0 : ℤ))) *
        MvPolynomial.monomial (Finsupp.erase 0 d) 1 := by
  have hb : (MvPolynomial.basisMonomials ℕ (Sym.Lambda L)) d
      = MvPolynomial.monomial d 1 := congrFun (MvPolynomial.coe_basisMonomials ℕ _) d
  rw [lowerCoeffInt, ← hb]
  exact Module.Basis.constr_basis _ _ _ _

/-- At `n = 0` the shifted extraction is `HJO.Sweep.lowerCoeff L 0`. -/
theorem lowerCoeffInt_zero (G : Total L) : lowerCoeffInt L 0 G = lowerCoeff L 0 G := by
  induction G using MvPolynomial.induction_on' with
  | monomial d a =>
      have hmon : MvPolynomial.monomial d a = a • MvPolynomial.monomial d (1 : Sym.Lambda L) := by
        rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
      rw [hmon, map_smul, map_smul, lowerCoeffInt_monomial, lowerCoeff_monomial,
        show ((0 : ℤ) + (d 0 : ℤ)) = ((d 0 : ℕ) : ℤ) from by ring, Sym.elemSymmAlt_natCast]
      simp only [map_mul, map_pow, map_neg, map_one]
  | add P Q hP hQ => rw [map_add, map_add, hP, hQ]

/-- **The shifted extraction absorbs a power of `y_1`**: `lowerCoeffInt n (y_1^mG)` is
`lowerCoeffInt (n+m) G`. -/
theorem lowerCoeffInt_X_pow_mul (n : ℤ) (m : ℕ) (G : Total L) :
    lowerCoeffInt L n ((MvPolynomial.X 0 : Total L) ^ m * G)
      = lowerCoeffInt L (n + m) G := by
  induction G using MvPolynomial.induction_on' with
  | monomial d a =>
      have hmon : MvPolynomial.monomial d a = a • MvPolynomial.monomial d (1 : Sym.Lambda L) := by
        rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
      have hXm : ((MvPolynomial.X 0 : Total L)) ^ m
          = MvPolynomial.monomial (Finsupp.single 0 m) 1 := MvPolynomial.X_pow_eq_monomial
      have herase : Finsupp.erase 0 (Finsupp.single 0 m + d) = Finsupp.erase 0 d := by
        rw [Finsupp.erase_add, Finsupp.erase_single, zero_add]
      have hzero : (Finsupp.single (0 : ℕ) m + d) 0 = m + d 0 := by
        rw [Finsupp.add_apply, Finsupp.single_eq_same]
      rw [hmon, mul_smul_comm, map_smul, map_smul, hXm, MvPolynomial.monomial_mul, one_mul,
        lowerCoeffInt_monomial, lowerCoeffInt_monomial, herase, hzero,
        show (n + ((m + d 0 : ℕ) : ℤ)) = (n + (m : ℤ)) + (d 0 : ℤ) from by push_cast; ring]
  | add P Q hP hQ => rw [mul_add, map_add, map_add, hP, hQ]

theorem lowerCoeffInt_one (n : ℤ) :
    lowerCoeffInt L n (1 : Total L) = MvPolynomial.C (Sym.elemSymmAlt L n) := by
  have h : (1 : Total L) = MvPolynomial.monomial (0 : ℕ →₀ ℕ) (1 : Sym.Lambda L) := by
    rw [MvPolynomial.monomial_zero', MvPolynomial.C_1]
  rw [h, lowerCoeffInt_monomial]
  simp

/-- **The shifted extraction on a power of `y_1`**: the single surviving term carries `c_{n+j}`. -/
theorem lowerCoeffInt_X_pow (n : ℤ) (j : ℕ) :
    lowerCoeffInt L n ((MvPolynomial.X 0 : Total L) ^ j)
      = MvPolynomial.C (Sym.elemSymmAlt L (n + (j : ℤ))) := by
  rw [show ((MvPolynomial.X 0 : Total L)) ^ j = (MvPolynomial.X 0 : Total L) ^ j * 1 from by
      rw [mul_one], lowerCoeffInt_X_pow_mul, lowerCoeffInt_one]

/-- **The shifted extraction is the pairing against `c_{n+·}`.** -/
theorem lowerCoeffInt_aeval (n : ℤ) (P : Polynomial (Sym.Lambda L)) :
    lowerCoeffInt L n (Polynomial.aeval (MvPolynomial.X 0 : Total L) P)
      = MvPolynomial.C (Sym.coeffPairing (fun j => Sym.elemSymmAlt L (n + (j : ℤ))) P) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add]; rw [hP, hQ]
  | monomial j a =>
    have hsmul : (algebraMap (Sym.Lambda L) (Total L) a) * (MvPolynomial.X 0 : Total L) ^ j
        = a • ((MvPolynomial.X 0 : Total L) ^ j) := (Algebra.smul_def a _).symm
    rw [Polynomial.aeval_monomial, hsmul, map_smul, lowerCoeffInt_X_pow,
      Sym.coeffPairing_monomial, Algebra.smul_def, MvPolynomial.algebraMap_eq, ← map_mul]

/-! ### The lowering operator at an integer index -/

/-- **`d_-` at an integer index**, `HJO.Sweep.dminus` with its coefficient extraction shifted by
`n ∈ ℤ`. At `n = m ≥ 0` it is `d_-^{(1)}(y_1^m·)` (`HJO.Sweep.dminusInt_natCast`). -/
noncomputable def dminusInt (q : L) (n : ℤ) : Module.End L (Total L) :=
  (lowerCoeffInt L n).restrictScalars L ∘ₗ (qshiftNeg q 1).toLinearMap

theorem dminusInt_apply (q : L) (n : ℤ) (F : Total L) :
    dminusInt q n F = lowerCoeffInt L n (qshiftNeg q 1 F) := rfl

omit [Algebra ℚ L] in
theorem auxVar_one_eq_X_zero : (auxVar 1 : Total L) = MvPolynomial.X 0 := by
  rw [auxVar, Nat.sub_self]

omit [Algebra ℚ L] in
theorem qshiftNeg_X_pow_mul (q : L) (m : ℕ) (F : Total L) :
    qshiftNeg q 1 ((MvPolynomial.X 0 : Total L) ^ m * F)
      = (MvPolynomial.X 0 : Total L) ^ m * qshiftNeg q 1 F := by
  rw [map_mul, map_pow, qshiftNeg_auxVar]

/-- **At a non-negative index the shifted lowering operator is `d_-` after multiplying by a power
of `y_1`.** So `HJO.Sweep.dminusInt` extends the family
`HJO.Sweep.dop_eq_neg_dminusCM_auxVar_pow_dplusStar` reads, and adds the indices below `0` that have
no such realisation. -/
theorem dminusInt_natCast (q : L) (m : ℕ) (F : Total L) :
    dminusInt q (m : ℤ) F = dminus q 1 ((auxVar 1 : Total L) ^ m * F) := by
  rw [dminusInt_apply, dminus_apply, Nat.sub_self, auxVar_one_eq_X_zero, qshiftNeg_X_pow_mul,
    ← lowerCoeffInt_zero, lowerCoeffInt_X_pow_mul, zero_add]

/-- **`d^{(n)}_-(y_1^mCA) = C(B_{n+m}A)` at every integer `n`**, the shifted form of
`HJO.Sweep.dminus_one_auxVar_pow_mul_C`. -/
theorem dminusInt_auxVar_pow_mul_C (q : L) (n : ℤ) (m : ℕ) (A : Sym.Lambda L) :
    dminusInt q n ((auxVar 1 : Total L) ^ m * MvPolynomial.C A)
      = MvPolynomial.C (Sym.Bop q (n + (m : ℤ)) A) := by
  have hqs : qshiftNeg q 1 (MvPolynomial.C A : Total L)
      = Polynomial.aeval (MvPolynomial.X 0 : Total L) (Sym.plethHallLittlewood q A) := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, qshiftNeg_C_eq]
    rfl
  rw [dminusInt_apply, auxVar_one_eq_X_zero, qshiftNeg_X_pow_mul, hqs,
    lowerCoeffInt_X_pow_mul, lowerCoeffInt_aeval, Sym.bop_apply]
  refine congrArg MvPolynomial.C ?_
  rfl

/-- **The bridge: `d^{(n)}_-` on the image of the plethystic shift is the basic operator `D_n` at
every integer index.**

`HJO.Sym.DopInt` is `HJO.Sym.DopInt` at `n ∈ ℤ`. The displacement of `HJO.Sym.Bop` composed with the
displacement of `HJO.Sweep.dplusStar` is the displacement of `HJO.Sym.DopInt` --- `X - (q-1)/z`
after `X + (q-1)u/z` is `X + M/z` (`HJO.Sweep.qshiftNeg_cycleShift_qshift_C`) --- and the extraction
reads only the total exponent, so the two pairings agree
(`HJO.Sym.elemSymmAlt_eq_esymmSigned`). **No hypothesis on `q` or `u`.**

At `n ≥ 0` this is the `HJO.Sweep.dop_eq_neg_dminusCM_auxVar_pow_dplusStar` family
(`HJO.Sweep.dminus_auxVar_pow_mul_dplusStar_C`); the content added is the indices below `0`. -/
@[hjo "lem_mellit_vertex_closed_form"]
theorem dminusInt_dplusStar_C (q u : L) (n : ℤ) (g : Sym.Lambda L) :
    dminusInt q n (dplusStar q u 0 (MvPolynomial.C g : Total L))
      = MvPolynomial.C (Sym.DopInt q u n g) := by
  have hstep : dminusInt q n (dplusStar q u 0 (MvPolynomial.C g : Total L))
      = lowerCoeffInt L n
          (Polynomial.aeval (MvPolynomial.X 0 : Total L) (Sym.plethShift q u g)) := by
    change lowerCoeffInt L n
      (qshiftNeg q 1 (cycleShift u 0 (qshift q 1 (MvPolynomial.C g : Total L)))) = _
    rw [qshiftNeg_cycleShift_qshift_C]
  rw [hstep, lowerCoeffInt_aeval]
  refine congrArg MvPolynomial.C ?_
  rw [Sym.DopInt, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  simp only [Sym.elemSymmAlt_eq_esymmSigned]

/-- **Cross-check: the bridge reproves the `n ≥ 0` family by a different route.**
`HJO.Sweep.dminus_auxVar_pow_mul_dplusStar_C` is
`HJO.Sweep.dop_eq_neg_dminusCM_auxVar_pow_dplusStar` and `HJO.Sweep.dop_zero_eq_dminus_dplusStar`
read off the sweep module directly; this recomputes it from the shifted pairing, through
`HJO.Sym.plethShift` and `HJO.Sym.esymmSigned`. The two routes agree, so the negative indices are
not an indexing slip. -/
theorem dminus_auxVar_pow_mul_dplusStar_C_of_dminusInt (q u : L) (l : ℕ) (g : Sym.Lambda L) :
    dminus q 1 ((auxVar 1 : Total L) ^ l * dplusStar q u 0 (MvPolynomial.C g : Total L))
      = MvPolynomial.C (Sym.Dop q u l g) := by
  rw [← dminusInt_natCast, dminusInt_dplusStar_C, Sym.dopInt_natCast]

/-! ### The closed form on the whole of `V_1`, and the composition law -/

/-- **The closed form of `T` on `y_1^jF` for an arbitrary `F ∈ V_1`:**

`T(y_1^jF) = ∑_{l ≥ 0}(quy_1)^l d^*_+(d^{(j-l)}_-F)`,

with `d^{(n)}_-` the shifted lowering operator of `HJO.Sweep.dminusInt`. Both sides are additive in
`F` and every monomial of `V_1` is a power of `y_1` times a constant
(`HJO.Sweep.exists_single_zero_of_mem_piece_one`), so this is
`HJO.Sweep.vertexStep_auxVar_pow_mul_C_eq_sum_dplusStar` summed over the support with the double sum
exchanged. -/
theorem vertexStep_auxVar_pow_mul_of_mem_piece_eq_sum (hq1 : q ≠ 1) (j R : ℕ) {F : Total L}
    (hF : F ∈ piece L 1)
    (hR : ∀ m : ℕ, bopExt q ((j : ℤ) + (m : ℤ) - ((R : ℤ) + 1))
        (dplusStar q u 0 (MvPolynomial.C (MvPolynomial.coeff (Finsupp.single 0 m) F) : Total L))
      = 0) :
    vertexStep q u ((auxVar 1 : Total L) ^ j * F)
      = ∑ l ∈ Finset.range (R + 1), ((q * u) ^ l) •
          ((auxVar 1 : Total L) ^ l * dplusStar q u 0 (dminusInt q ((j : ℤ) - (l : ℤ)) F)) := by
  have hmon : ∀ (m : ℕ) (a : Sym.Lambda L),
      MvPolynomial.monomial (Finsupp.single (0 : ℕ) m) a
        = (auxVar 1 : Total L) ^ m * MvPolynomial.C a := by
    intro m a
    rw [auxVar, Nat.sub_self, MvPolynomial.X_pow_eq_monomial, mul_comm,
      MvPolynomial.C_mul_monomial, mul_one]
  have key : ∀ d ∈ F.support,
      vertexStep q u ((auxVar 1 : Total L) ^ j
          * MvPolynomial.monomial d (MvPolynomial.coeff d F))
        = ∑ l ∈ Finset.range (R + 1), ((q * u) ^ l) • ((auxVar 1 : Total L) ^ l
            * dplusStar q u 0 (dminusInt q ((j : ℤ) - (l : ℤ))
                (MvPolynomial.monomial d (MvPolynomial.coeff d F)))) := by
    intro d hd
    obtain ⟨m, rfl⟩ := exists_single_zero_of_mem_piece_one hF hd
    have hjm : (auxVar 1 : Total L) ^ j
        * MvPolynomial.monomial (Finsupp.single (0 : ℕ) m)
            (MvPolynomial.coeff (Finsupp.single (0 : ℕ) m) F)
        = (auxVar 1 : Total L) ^ (j + m)
            * MvPolynomial.C (MvPolynomial.coeff (Finsupp.single (0 : ℕ) m) F) := by
      rw [hmon, ← mul_assoc, ← pow_add]
    rw [hjm, vertexStep_auxVar_pow_mul_C_eq_sum_dplusStar hq1 (j + m) R _ (by
      push_cast
      exact hR m)]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hmon, dminusInt_auxVar_pow_mul_C,
      show ((j : ℤ) - (l : ℤ)) + (m : ℤ) = ((j + m : ℕ) : ℤ) - (l : ℤ) from by push_cast; ring]
  have hL : vertexStep q u ((auxVar 1 : Total L) ^ j * F)
      = ∑ d ∈ F.support, ∑ l ∈ Finset.range (R + 1), ((q * u) ^ l) • ((auxVar 1 : Total L) ^ l
          * dplusStar q u 0 (dminusInt q ((j : ℤ) - (l : ℤ))
              (MvPolynomial.monomial d (MvPolynomial.coeff d F)))) := by
    conv_lhs => rw [F.as_sum]
    rw [Finset.mul_sum, map_sum]
    exact Finset.sum_congr rfl key
  rw [hL, Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  conv_rhs => rw [F.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum, Finset.smul_sum]

/-- **The composition law.** `T` carries `y_1^jd^*_+(Cg)` to a combination of the same shape:

`T(y_1^jd^*_+(Cg)) = ∑_{l ≥ 0}(quy_1)^l d^*_+(C D_{j-l}g)`,

with `D_n` the integer-indexed basic operator `HJO.Sym.DopInt` of `HJO.Sym.DopInt`. So `T` acts on
the pairs `(j, g)` by `(j,g) ↦ ∑_l(qu)^l(l, D_{j-l}g)`, a rule that does not read the previous
step --- which is what `T^b` needs in order to compose, and what the truncated form of
`HJO.Sweep.vertexStep_auxVar_pow_succ_mul_C` did not give. -/
@[hjo "lem_mellit_vertex_closed_form"]
theorem vertexStep_auxVar_pow_mul_dplusStar_C_eq_sum (hq1 : q ≠ 1) (j R : ℕ) (g : Sym.Lambda L)
    (hR : ∀ m : ℕ, bopExt q ((j : ℤ) + (m : ℤ) - ((R : ℤ) + 1))
        (dplusStar q u 0 (MvPolynomial.C (MvPolynomial.coeff (Finsupp.single 0 m)
          (dplusStar q u 0 (MvPolynomial.C g : Total L))) : Total L)) = 0) :
    vertexStep q u ((auxVar 1 : Total L) ^ j * dplusStar q u 0 (MvPolynomial.C g : Total L))
      = ∑ l ∈ Finset.range (R + 1), ((q * u) ^ l) •
          ((auxVar 1 : Total L) ^ l
            * dplusStar q u 0
                (MvPolynomial.C (Sym.DopInt q u ((j : ℤ) - (l : ℤ)) g) : Total L)) := by
  rw [vertexStep_auxVar_pow_mul_of_mem_piece_eq_sum hq1 j R
    (dplusStar_zero_C_mem_piece_one q u g) hR]
  exact Finset.sum_congr rfl fun l _ => by rw [dminusInt_dplusStar_C]

/-- The hypothesis of the closed form on `V_1` holds for every large enough `R`. -/
theorem exists_forall_bopExt_dplusStar_coeff_eq_zero (q u : L) (j : ℕ) (F : Total L) :
    ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → ∀ m : ℕ,
      bopExt q ((j : ℤ) + (m : ℤ) - ((R : ℤ) + 1))
          (dplusStar q u 0
            (MvPolynomial.C (MvPolynomial.coeff (Finsupp.single 0 m) F) : Total L)) = 0 := by
  classical
  set S : ℕ := F.support.sup fun d =>
    d 0 + bopExtBound q (dplusStar q u 0 (MvPolynomial.C (MvPolynomial.coeff d F) : Total L))
    with hS
  refine ⟨j + S, fun R hRle m => ?_⟩
  by_cases hm : (Finsupp.single (0 : ℕ) m) ∈ F.support
  · have hsup := Finset.le_sup (f := fun d =>
      d 0 + bopExtBound q (dplusStar q u 0 (MvPolynomial.C (MvPolynomial.coeff d F) : Total L))) hm
    rw [Finsupp.single_eq_same, ← hS] at hsup
    exact bopExt_eq_zero_of_lt q _ (by omega)
  · have hz : MvPolynomial.coeff (Finsupp.single (0 : ℕ) m) F = 0 := by
      by_contra hc
      exact hm (MvPolynomial.mem_support_iff.mpr hc)
    rw [hz, map_zero, map_zero, map_zero]

/-! ### One step of the tower, and `ψ_1` in closed form -/

/-- **One step of the `(a,1)` column's tower, closed.** For all `K, j ≥ 0`,

`d_-(y_1^K T(y_1^j d^*_+(Cg))) = ∑_{l ≥ 0}(qu)^l D_{K+l}(D_{j-l}g)`,

entirely inside the integer-indexed family `D_n` of `HJO.Sym.DopInt`. Iterating this is what puts
the whole sweep side of the column in that family; the outer `d_-(y_1^K ·)` is
`HJO.Sweep.dminus_auxVar_pow_mul_dplusStar_C`. -/
@[hjo "lem_mellit_vertex_closed_form"]
theorem dminus_auxVar_pow_mul_vertexStep_auxVar_pow_mul_dplusStar_C (hq1 : q ≠ 1) (K j R : ℕ)
    (g : Sym.Lambda L)
    (hR : ∀ m : ℕ, bopExt q ((j : ℤ) + (m : ℤ) - ((R : ℤ) + 1))
        (dplusStar q u 0 (MvPolynomial.C (MvPolynomial.coeff (Finsupp.single 0 m)
          (dplusStar q u 0 (MvPolynomial.C g : Total L))) : Total L)) = 0) :
    dminus q 1 ((auxVar 1 : Total L) ^ K
        * vertexStep q u ((auxVar 1 : Total L) ^ j
            * dplusStar q u 0 (MvPolynomial.C g : Total L)))
      = MvPolynomial.C (∑ l ∈ Finset.range (R + 1), ((q * u) ^ l) •
          Sym.DopInt q u ((K : ℤ) + (l : ℤ)) (Sym.DopInt q u ((j : ℤ) - (l : ℤ)) g)) := by
  rw [vertexStep_auxVar_pow_mul_dplusStar_C_eq_sum hq1 j R g hR, Finset.mul_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_smul_comm, map_smul, ← mul_assoc, ← pow_add, dminus_auxVar_pow_mul_dplusStar_C,
    ← Sym.dopInt_natCast, C_smul,
    show ((K + l : ℕ) : ℤ) = (K : ℤ) + (l : ℤ) from by push_cast; ring]

/-- **`ψ_1 = ∑_{l ≥ 0}(qu)^lD_{1+l}D_{-l}`**, the sweep side of the `(a,1)` column at the slope
`(2,1)`, in closed form inside the integer-indexed basic operators. The case `K = 1`, `j = 0` of
`HJO.Sweep.dminus_auxVar_pow_mul_vertexStep_auxVar_pow_mul_dplusStar_C`. -/
theorem psiCol_one_eq_sum_dopInt (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) (R : ℕ)
    (f : Sym.Lambda L)
    (hR : ∀ m : ℕ, bopExt q ((0 : ℤ) + (m : ℤ) - ((R : ℤ) + 1))
        (dplusStar q u 0 (MvPolynomial.C (MvPolynomial.coeff (Finsupp.single 0 m)
          (dplusStar q u 0 (MvPolynomial.C f : Total L))) : Total L)) = 0) :
    psiCol q u 1 f
      = MvPolynomial.C (∑ l ∈ Finset.range (R + 1), ((q * u) ^ l) •
          Sym.DopInt q u (1 + (l : ℤ)) (Sym.DopInt q u (-(l : ℤ)) f)) := by
  have h := dminus_auxVar_pow_mul_vertexStep_auxVar_pow_mul_dplusStar_C (q := q) (u := u)
    hq1 1 0 R f hR
  rw [pow_zero, one_mul, pow_one] at h
  simp only [Nat.cast_one, Nat.cast_zero, zero_sub] at h
  rw [psiCol_eq hq0 hu0 hq1 1 f]
  simp only [pow_one]
  exact h

/-- **The `b = 0` instance of `HJO.Sweep.ColumnCommutes` is an identity in the `D_n`-algebra.**

`ψ_0 = D_1` (`HJO.Sweep.psiCol_zero`), `A` computes `D_0` on `V_0`
(`HJO.Sweep.dop_zero_eq_dminus_dplusStar`) and `ψ_1` is the sum above, so the commutation at `b = 0`
and one `f` says exactly

`M·∑_{l ≥ 0}(qu)^lD_{1+l}(D_{-l}f) = D_1(D_0f) - D_0(D_1f)`,

with no sweep module left in it. Whether that holds is not settled here. -/
theorem columnCommutes_zero_at_iff_dopInt (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) (R : ℕ)
    (f : Sym.Lambda L)
    (hR : ∀ m : ℕ, bopExt q ((0 : ℤ) + (m : ℤ) - ((R : ℤ) + 1))
        (dplusStar q u 0 (MvPolynomial.C (MvPolynomial.coeff (Finsupp.single 0 m)
          (dplusStar q u 0 (MvPolynomial.C f : Total L))) : Total L)) = 0) :
    (((1 - q) * (1 - u)) • psiCol q u 1 f
        = psiCol q u 0 (Sym.Dop q u 0 f)
          - dminus q 1 (dplusStar q u 0 (psiCol q u 0 f)))
      ↔ ((1 - q) * (1 - u)) • (∑ l ∈ Finset.range (R + 1), ((q * u) ^ l) •
            Sym.DopInt q u (1 + (l : ℤ)) (Sym.DopInt q u (-(l : ℤ)) f))
          = Sym.Dop q u 1 (Sym.Dop q u 0 f) - Sym.Dop q u 0 (Sym.Dop q u 1 f) := by
  rw [psiCol_one_eq_sum_dopInt hq0 hu0 hq1 R f hR, psiCol_zero, psiCol_zero,
    ← dop_zero_eq_dminus_dplusStar, ← C_smul, ← map_sub]
  exact ⟨fun h => MvPolynomial.C_injective ℕ (Sym.Lambda L) h,
    fun h => congrArg MvPolynomial.C h⟩

/-! ### `[T, A]` in closed form -/

/-- **`A∘T` on the spanning family, closed:**
`A(T(y_1^jd^*_+(Cg))) = d^*_+(C ∑_l (qu)^lD_l(D_{j-l}g))`. -/
theorem vertexA_vertexStep_auxVar_pow_mul_dplusStar_C (hq1 : q ≠ 1) (j R : ℕ) (g : Sym.Lambda L)
    (hR : ∀ m : ℕ, bopExt q ((j : ℤ) + (m : ℤ) - ((R : ℤ) + 1))
        (dplusStar q u 0 (MvPolynomial.C (MvPolynomial.coeff (Finsupp.single 0 m)
          (dplusStar q u 0 (MvPolynomial.C g : Total L))) : Total L)) = 0) :
    vertexA q u (vertexStep q u ((auxVar 1 : Total L) ^ j
        * dplusStar q u 0 (MvPolynomial.C g : Total L)))
      = dplusStar q u 0 (MvPolynomial.C (∑ l ∈ Finset.range (R + 1), ((q * u) ^ l) •
          Sym.DopInt q u (l : ℤ) (Sym.DopInt q u ((j : ℤ) - (l : ℤ)) g)) : Total L) := by
  have h := dminus_auxVar_pow_mul_vertexStep_auxVar_pow_mul_dplusStar_C (q := q) (u := u)
    hq1 0 j R g hR
  rw [pow_zero, one_mul] at h
  simp only [Nat.cast_zero, zero_add] at h
  rw [vertexA_apply, h]

/-- **`T∘A` on the spanning family, closed:**
`T(A(y_1^jd^*_+(Cg))) = ∑_l (quy_1)^l d^*_+(C D_{-l}(D_jg))`, since `A(y_1^jd^*_+(Cg))` is
`d^*_+(C D_jg)` (`HJO.Sweep.dminus_auxVar_pow_mul_dplusStar_C`). -/
theorem vertexStep_vertexA_auxVar_pow_mul_dplusStar_C (hq1 : q ≠ 1) (j S : ℕ) (g : Sym.Lambda L)
    (hS : ∀ m : ℕ, bopExt q ((0 : ℤ) + (m : ℤ) - ((S : ℤ) + 1))
        (dplusStar q u 0 (MvPolynomial.C (MvPolynomial.coeff (Finsupp.single 0 m)
          (dplusStar q u 0
            (MvPolynomial.C (Sym.DopInt q u (j : ℤ) g) : Total L))) : Total L)) = 0) :
    vertexStep q u (vertexA q u ((auxVar 1 : Total L) ^ j
        * dplusStar q u 0 (MvPolynomial.C g : Total L)))
      = ∑ l ∈ Finset.range (S + 1), ((q * u) ^ l) • ((auxVar 1 : Total L) ^ l
          * dplusStar q u 0 (MvPolynomial.C
              (Sym.DopInt q u (-(l : ℤ)) (Sym.DopInt q u (j : ℤ) g)) : Total L)) := by
  have hA : vertexA q u ((auxVar 1 : Total L) ^ j
      * dplusStar q u 0 (MvPolynomial.C g : Total L))
      = (auxVar 1 : Total L) ^ 0
        * dplusStar q u 0 (MvPolynomial.C (Sym.DopInt q u (j : ℤ) g) : Total L) := by
    rw [pow_zero, one_mul, vertexA_apply, dminus_auxVar_pow_mul_dplusStar_C, Sym.dopInt_natCast]
  rw [hA, vertexStep_auxVar_pow_mul_dplusStar_C_eq_sum hq1 0 S _ hS]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [show ((0 : ℕ) : ℤ) - (l : ℤ) = -(l : ℤ) from by push_cast; ring]

/-- **`[T, A]` in closed form on the spanning family of `V_1`.**

`[T,A](y_1^jd^*_+(Cg)) = ∑_{l ≥ 0}(quy_1)^l d^*_+(C D_{-l}D_jg)`
`  - d^*_+(C ∑_{l ≥ 0}(qu)^lD_lD_{j-l}g)`,

both terms inside the integer-indexed basic operators `D_n` of `HJO.Sym.DopInt` — no sweep-module
operator survives except the plethystic shift carrying the answer back into `V_1`. The `l = 0` terms
of the two sums are `d^*_+(CD_0D_jg)` and cancel, which is the statement that `A` commutes with
itself. -/
@[hjo "lem_mellit_vertex_comm_closed"]
theorem comm_vertexStep_vertexA_auxVar_pow_mul_dplusStar_C (hq1 : q ≠ 1) (j R S : ℕ)
    (g : Sym.Lambda L)
    (hR : ∀ m : ℕ, bopExt q ((j : ℤ) + (m : ℤ) - ((R : ℤ) + 1))
        (dplusStar q u 0 (MvPolynomial.C (MvPolynomial.coeff (Finsupp.single 0 m)
          (dplusStar q u 0 (MvPolynomial.C g : Total L))) : Total L)) = 0)
    (hS : ∀ m : ℕ, bopExt q ((0 : ℤ) + (m : ℤ) - ((S : ℤ) + 1))
        (dplusStar q u 0 (MvPolynomial.C (MvPolynomial.coeff (Finsupp.single 0 m)
          (dplusStar q u 0
            (MvPolynomial.C (Sym.DopInt q u (j : ℤ) g) : Total L))) : Total L)) = 0) :
    (vertexStep q u * vertexA q u - vertexA q u * vertexStep q u)
        ((auxVar 1 : Total L) ^ j * dplusStar q u 0 (MvPolynomial.C g : Total L))
      = (∑ l ∈ Finset.range (S + 1), ((q * u) ^ l) • ((auxVar 1 : Total L) ^ l
            * dplusStar q u 0 (MvPolynomial.C
                (Sym.DopInt q u (-(l : ℤ)) (Sym.DopInt q u (j : ℤ) g)) : Total L)))
        - dplusStar q u 0 (MvPolynomial.C (∑ l ∈ Finset.range (R + 1), ((q * u) ^ l) •
            Sym.DopInt q u (l : ℤ) (Sym.DopInt q u ((j : ℤ) - (l : ℤ)) g)) : Total L) := by
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
    vertexStep_vertexA_auxVar_pow_mul_dplusStar_C hq1 j S g hS,
    vertexA_vertexStep_auxVar_pow_mul_dplusStar_C hq1 j R g hR]

end HJO.Sweep
