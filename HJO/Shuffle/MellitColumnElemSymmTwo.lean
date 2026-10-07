/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.MellitColumnCommutation
public import HJO.Shuffle.MellitSweepSecondZ
public import HJO.Shuffle.MellitNablaConjStarRefuted
public meta import HJO.Attr

/-! # `[N, A]` is `[T, A]` rescaled, `y_1 ∉ d^*_+(ιΛ)`, and the `(a,1)` column in degree `≤ 2`

`HJO/Shuffle/MellitColumnCommutation.lean` restates the `(a,1)` column of
`HJO.Mellit.lhsRewrite_sweepWitness` at a general `f` as a commutation and points to two things:
the commutator `[N, A]` of the two orders of `B_m` against `d^*_+`, which the telescoping route
would need as **further input**, and a test of the commutation at `f = e_2`, the smallest
coefficient with `D_0f ∉ Lf`. **This file settles both. The first is a restatement; the second
holds.**

## `[N, A]` is not independent input

`HJO.Sweep.zop` at `k = 1` has an empty train (`HJO.Braid.trainUp_self`), so
`z_1 = q/(1-q)(A - N)` outright (`HJO.Sweep.zopOneStar_one_eq_vertexA_sub_vertexN`), with
`A = d^*_+{}^{(0)}d_-^{(1)}` (`HJO.Sweep.vertexA`) and `N = d_-^{(2)}d^*_+{}^{(1)}`
(`HJO.Sweep.vertexN`). Hence `T = z_1 + A = (1-q)^{-1}(A - qN)`
(`HJO.Sweep.vertexStep_eq_vertexA_sub_smul_vertexN`) --- and since `A` commutes with itself,

**`[T, A] = -q/(1-q)·[N, A]`**   (`HJO.Sweep.comm_vertexStep_vertexA_eq_smul_comm_vertexN_vertexA`),

with the converse `[N, A] = -(1-q)/q·[T, A]` at `q ≠ 0`
(`HJO.Sweep.comm_vertexN_vertexA_eq_smul_comm_vertexStep_vertexA`).

The two commutators are **the same operator up to a nonzero scalar**. So `[N, A]` is not new input:
it is the telescoping obstruction `[T, A]` --- already known nonzero, on the image of the plethystic
shift, by `HJO.Sweep.vertexStep_dplusStar_dminus_ne` --- written in the other pair of letters. A
closed form for one is a closed form for the other, and this file obtains neither; what it
records is that looking for one is not a second problem. The transported value is
`[N, A]Φ(e_1) = -(1-q)uM(ιe_1 + qy_1)`
(`HJO.Sweep.comm_vertexN_vertexA_dplusStar_C_elemSymm_one`), nonzero at
`HJO.Sweep.comm_vertexN_vertexA_ne_zero`. Note the hypotheses: the identity needs only `q ≠ 1` (and
`q ≠ 0` for the division), strictly less than the column's own exclusions --- the asymmetry
that marks a restatement.

## `y_1 ∉ d^*_+(ιΛ)`, formalised

`HJO.Sweep.not_wideAt_auxVar` refutes the `V_1`-wide strengthening of the commutation at `v = y_1`,
and this does not refute the commutation itself because `y_1` is not in the image of `Φ`. Here
that is a theorem: the `y_1`-free part of `d^*_+(ιf)` is `f`
(`HJO.Sweep.constantCoeff_dplusStar_C`, at every level, no hypothesis on `q` or `u`), because
`d^*_+` is multiplicative on the constants and displaces each generator `p_{j+1}` by
`(q^{j+1}-1)(uy_1)^{j+1}`, which has no constant term. So `d^*_+(ιf) = y_1` would force `f = 0` and
then `0 = y_1` (`HJO.Sweep.dplusStar_C_ne_auxVar`,
`HJO.Sweep.auxVar_notMem_range_dplusStar_C`). The counterexample is outside the set
`HJO.Sweep.columnCommutes_zero_iff_wideAt` reads the identity on.

## The `(a,1)` column at `f = e_2` and `f = e_1^2`: it holds

`T` preserves the total degree of `V_1`, whose degree-two part is spanned by
`ιe_1^2, ιe_2, y_1ιe_1, y_1^2`. The three values

* `T(ιe_2) = -(1-q)ιe_1^2 + (1-q+q^2)ιe_2 + (1-q)u·y_1ιe_1`
  (`HJO.Sweep.vertexStep_C_elemSymm_two`),
* `T(ιe_1^2) = (2q-1)ιe_1^2 + (1-q)^2ιe_2 + (q-1)^2u·y_1ιe_1`
  (`HJO.Sweep.vertexStep_C_elemSymm_one_sq`),
* `T(y_1ιe_1) = -ιe_1^2 + (1-q)ιe_2 + u·y_1ιe_1`
  (`HJO.Sweep.vertexStep_auxVar_mul_C_elemSymm_one`), `T(y_1^2) = ιe_2 - u·y_1ιe_1 + u^2y_1^2`
  (`HJO.Sweep.vertexStep_auxVar_sq`)

are enough to evaluate `πZΦ` at both degree-two coefficients
(`HJO.Sweep.psiCol_one_elemSymm_two`, `HJO.Sweep.psiCol_one_elemSymm_one_sq`), the four
Hall--Littlewood values read being `B_1(e_1^2)`, `B_1(e_2)`, `B_2(e_1)`, `B_3(1)`. On the `Λ` side
`HJO.Sym.Qop`'s recursion `Q_{2,1} = M^{-1}(D_1D_0 - D_0D_1)` closes on `span(e_1^3, e_1e_2, e_3)`
off five `D`-values, three of them new here
(`HJO.Sym.dop_zero_elemSymm_three`, `HJO.Sym.dop_one_elemSymm_one_sq`,
`HJO.Sym.dop_zero_elemSymm_one_mul_two`, `HJO.Sym.dop_zero_elemSymm_one_cube`), giving
`HJO.Sym.qop_two_one_elemSymm_two` and `HJO.Sym.qop_two_one_elemSymm_one_sq`. **The two sides
agree**:

`HJO.Sweep.lhsSlopeAt_two_one_elemSymm_two`, `HJO.Sweep.lhsSlopeAt_two_one_elemSymm_one_sq`,

and with the vacuum and `f = e_1` already proved, `HJO.Mellit.lhsSlopeCarrier` being a submodule
gives the clause on all of `Λ` in degrees `≤ 2`
(`HJO.Sweep.lhsSlopeAt_two_one_of_deg_le_two`).

**Why this is a test and not a restatement.** At `f = e_1` the commutation holds for a degenerate
reason: `D_0(e_1) = (1-M)e_1` is a scalar multiple, so the second term's argument is not a new
argument and the identity collapses onto the `Λ`-side recursion. At `f = e_2` it does not:
`D_0(e_2) = e_2 - Me_1^2 - (q+u)Me_2` leaves the line, and the two sides are computed by disjoint
routes --- `T` and two `B`-values on one, `HJO.Sym.Qop`'s commutator and five `D`-values on the
other. The `Λ` side is symmetric under `q ↔ u` and the sweep side is nowhere visibly so, which is
what makes the agreement informative. Equivalently (`HJO.Sweep.columnCommutes_zero_at_elemSymm_two`)
it is the instance `b = 0`, `f = e_2` of `HJO.Sweep.ColumnCommutes`. No hypothesis is discharged:
both sides are evaluated and compared.

## Genericity

`q ≠ 0`, `u ≠ 0`, `q ≠ 1` are the letter `Z`'s, real for the reason recorded in
`MellitStraightMonomial.lean`; `M = (1-q)(1-u) ≠ 0` is `HJO.Sym.Qop`'s normalisation. The `T`-values
and the `d^*_+`-values carry `q ≠ 1` and nothing on `u`;
`HJO.Sweep.constantCoeff_dplusStar_C` and `HJO.Sweep.zopOneStar_one_eq_vertexA_sub_vertexN` carry
nothing at all. **No condition on `u - 1` anywhere.**

## Implementation notes

`HJO.Mellit.lhsRewrite_sweepWitness` is stated at a general `f` and a general slope; this file
proves its `(2,1)` clause in degrees `≤ 2`, and `HJO.Sweep.ColumnCommutes` --- which
`HJO.Sweep.columnCommutes_iff` shows is *equivalent* to the whole `(a,1)` column --- is not proved
here (it is `HJO.Sweep.columnCommutes`, in `HJO/Shuffle/MellitColumnChainTelescope.lean`).
`HJO.Mellit.shuffle_of_lhs_and_induction` has two binders, `hlhs` and `hind`; nothing here touches
`hind`, and `hlhs` is quantified over `1 < a < b`, so the `(a,1)` column is not even an instance of
it. What this serves is
`HJO.Mellit.lhsRewrite_sweepWitness`, indirectly and in one clause.
-/

@[expose] public section

namespace HJO.Sweep

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-! ### The two orders of `B_m` against `d^*_+` -/

/-- `A = d^*_+{}^{(0)}d_-^{(1)}`, the second summand of `HJO.Sweep.vertexStep` and the lift of `D_0`
along the plethystic shift (`HJO.Sweep.dplusStar_dminus_dplusStar_C`). -/
noncomputable def vertexA (q u : L) : Module.End L (Total L) :=
  dplusStar q u 0 * dminus q 1

/-- `N = d_-^{(2)}d^*_+{}^{(1)}`, the other order: on a monomial of `V_1` it is `B_m` applied
coefficientwise *after* the displacement (`HJO.Sweep.dminus_two_dplusStar_one_auxVar_pow_mul_C`),
where `A` applies it before. -/
noncomputable def vertexN (q u : L) : Module.End L (Total L) :=
  dminus q 2 * dplusStar q u 1

theorem vertexA_apply (q u : L) (F : Total L) :
    vertexA q u F = dplusStar q u 0 (dminus q 1 F) := rfl

theorem vertexN_apply (q u : L) (F : Total L) :
    vertexN q u F = dminus q 2 (dplusStar q u 1 F) := rfl

/-- **`z_1 = q/(1-q)·(A - N)` on `V_1`**: `HJO.Sweep.zop` at `k = 1`, the train being empty
(`HJO.Braid.trainUp_self`). No hypothesis on `q` or `u`. -/
theorem zopOneStar_one_eq_vertexA_sub_vertexN (q u : L) :
    zopOneStar q u 1 = (q / (1 - q)) • (vertexA q u - vertexN q u) := by
  rw [zopOneStar, show trainUpEnd q 1 1 = 1 from Braid.trainUp_self _ _ 1, mul_one, vertexA,
    vertexN]
  norm_num

/-- **`T = (1-q)^{-1}(A - qN)`**, the vertex step in the two orders. This is a *definitional*
rearrangement: `HJO.Sweep.vertexStep` is `z_1 + A` and `z_1` is `q/(1-q)(A - N)`, so the two
descriptions carry the same information. `q ≠ 1` only, and nothing on `u`. -/
theorem vertexStep_eq_vertexA_sub_smul_vertexN (hq1 : q ≠ 1) :
    vertexStep q u = (1 - q)⁻¹ • (vertexA q u - q • vertexN q u) := by
  have h1q : (1 : L) - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq1)
  rw [vertexStep, zopOneStar_one_eq_vertexA_sub_vertexN,
    show dplusStar q u 0 * dminus q 1 = vertexA q u from rfl]
  match_scalars <;> (field_simp; try ring)

/-- **`[T, A] = -q/(1-q)·[N, A]`.**

The commutator of the vertex step with `A` and the commutator of the two orders of `B_m` against the
plethystic shift are *the same operator up to the scalar* `-q/(1-q)` --- immediately from
`HJO.Sweep.vertexStep_eq_vertexA_sub_smul_vertexN`, since `A` commutes with itself.

**So `[N, A]` is not independent input for the `(a,1)` column.** It is the telescoping obstruction
`[T, A]` rescaled: a closed form for either is a closed form for the other, and
`HJO.Sweep.vertexStep_dplusStar_dminus_ne` already says both are nonzero. -/
theorem comm_vertexStep_vertexA_eq_smul_comm_vertexN_vertexA (hq1 : q ≠ 1) :
    vertexStep q u * vertexA q u - vertexA q u * vertexStep q u
      = (-(q / (1 - q))) • (vertexN q u * vertexA q u - vertexA q u * vertexN q u) := by
  have h1q : (1 : L) - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq1)
  rw [vertexStep_eq_vertexA_sub_smul_vertexN hq1]
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm]
  match_scalars <;> (field_simp; try ring)

/-- **`[N, A] = -(1-q)/q·[T, A]`**, the same statement read the other way. `q ≠ 0` is what the
division costs; `q ≠ 1` comes from `HJO.Sweep.zop`'s scalar. -/
theorem comm_vertexN_vertexA_eq_smul_comm_vertexStep_vertexA (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    vertexN q u * vertexA q u - vertexA q u * vertexN q u
      = (-((1 - q) / q)) • (vertexStep q u * vertexA q u - vertexA q u * vertexStep q u) := by
  have h1q : (1 : L) - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq1)
  rw [comm_vertexStep_vertexA_eq_smul_comm_vertexN_vertexA hq1, smul_smul]
  rw [show -((1 - q) / q) * -(q / (1 - q)) = 1 from by field_simp, one_smul]

/-- **`[N, A]Φ(e_1) = -(1-q)uM·(ιe_1 + qy_1)`**, the value of the commutator of the two orders on
the image of the plethystic shift, off the known `[T, A]`-value
`HJO.Sweep.vertexStep_dplusStar_dminus_comm_dplusStar_C_elemSymm_one` and the scalar identity
`HJO.Sweep.comm_vertexN_vertexA_eq_smul_comm_vertexStep_vertexA`. -/
theorem comm_vertexN_vertexA_dplusStar_C_elemSymm_one (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    (vertexN q u * vertexA q u - vertexA q u * vertexN q u)
        (dplusStar q u 0 (MvPolynomial.C (Sym.elemSymm L 1) : Total L))
      = (-((1 - q) * u * ((1 - q) * (1 - u))))
          • ((MvPolynomial.C (Sym.elemSymm L 1) : Total L) + q • (auxVar 1 : Total L)) := by
  have h1q : (1 : L) - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq1)
  rw [comm_vertexN_vertexA_eq_smul_comm_vertexStep_vertexA hq0 hq1, LinearMap.smul_apply,
    LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, vertexA_apply, vertexA_apply,
    vertexStep_dplusStar_dminus_comm_dplusStar_C_elemSymm_one hq1, smul_smul]
  congr 1
  field_simp

/-- **`[N, A] ≠ 0`.** The exclusions are the column's own. -/
theorem comm_vertexN_vertexA_ne_zero (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1)
    (hM : (1 - q) * (1 - u) ≠ 0) :
    vertexN q u * vertexA q u - vertexA q u * vertexN q u ≠ (0 : Module.End L (Total L)) := by
  intro h
  refine vertexStep_dplusStar_dminus_ne (L := L) hq0 hu0 hq1 hM ?_
  have hc := comm_vertexStep_vertexA_eq_smul_comm_vertexN_vertexA (q := q) (u := u) hq1
  rw [h, smul_zero] at hc
  have := congrArg (fun T : Module.End L (Total L) =>
    T (dplusStar q u 0 (MvPolynomial.C (Sym.elemSymm L 1) : Total L))) hc
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.zero_apply,
    sub_eq_zero] at this
  exact this

/-! ### `y_1` is not in the image of the plethystic shift -/

/-- **The `y_1`-free part of `d^*_+(ιf)` is `f`.** `d^*_+` on the constants is multiplicative
(`HJO.Sweep.dplusStar_C_mul`) and on a generator `p_{j+1}` it adds `(q^{j+1}-1)(uy_1)^{j+1}`
(`HJO.Sweep.qshift_powerSum`, `HJO.Sweep.cycleShift_auxVar_last`), a term with no constant part. So
setting every auxiliary variable to zero recovers the argument.

No hypothesis on `q` or `u`, and at every level `k`. -/
@[hjo "lem_mellit_pleth_image_constant"]
theorem constantCoeff_dplusStar_C (q u : L) (k : ℕ) (f : Sym.Lambda L) :
    MvPolynomial.constantCoeff (dplusStar q u k (MvPolynomial.C f : Total L)) = f := by
  induction f using MvPolynomial.induction_on with
  | C a =>
      rw [show (MvPolynomial.C (MvPolynomial.C a : Sym.Lambda L) : Total L) = scal a from rfl,
        scal_eq_algebraMap, ← dplusStarAlg_eq_dplusStar, AlgHom.commutes, ← scal_eq_algebraMap,
        scal]
      simp
  | add p r hp hr => rw [map_add, map_add, map_add, hp, hr]
  | mul_X p j hp =>
      have hgen : dplusStar q u k (MvPolynomial.C (MvPolynomial.X j : Sym.Lambda L) : Total L)
          = (MvPolynomial.C (MvPolynomial.X j : Sym.Lambda L) : Total L)
            + scal (q ^ (j + 1) - 1) * (scal u * (auxVar 1 : Total L)) ^ (j + 1) := by
        have hps : (MvPolynomial.X j : Sym.Lambda L) = Sym.powerSum L (j + 1) :=
          (Bglx.powerSum_succ_eq_X j).symm
        rw [hps, dplusStar_apply, qshift_powerSum, map_add, map_mul, map_pow,
          cycleShift_auxVar_last, show cycleShift u k (MvPolynomial.C (Sym.powerSum L (j + 1))
              : Total L) = MvPolynomial.C (Sym.powerSum L (j + 1)) from
            (cycleShift u k).commutes _,
          show cycleShift u k (scal (q ^ (j + 1) - 1) : Total L) = scal (q ^ (j + 1) - 1) from
            (cycleShift u k).commutes _]
      rw [dplusStar_C_mul, map_mul, hp, hgen, map_add]
      have hz : MvPolynomial.constantCoeff
          (scal (q ^ (j + 1) - 1) * (scal u * (auxVar 1 : Total L)) ^ (j + 1)) = 0 := by
        rw [map_mul, map_pow, map_mul]
        simp [auxVar, scal]
      rw [hz, add_zero]
      simp

/-- **`y_1 ∉ d^*_+(ι Λ)`.**

This is what shows that the counterexample
`HJO.Sweep.not_wideAt_auxVar` to the `V_1`-wide strengthening of the commutation sits *outside* the
set on which `HJO.Sweep.columnCommutes_zero_iff_wideAt` reads that identity, so it does not refute
`HJO.Sweep.ColumnCommutes`. Off `HJO.Sweep.constantCoeff_dplusStar_C`: the `y_1`-free part of
`d^*_+(ιf)` is `f`, and `y_1` has none, so `f` would be `0` and then `d^*_+(ι0) = 0 ≠ y_1`. -/
@[hjo "lem_mellit_pleth_image_constant"]
theorem dplusStar_C_ne_auxVar (q u : L) (k : ℕ) (f : Sym.Lambda L) :
    dplusStar q u k (MvPolynomial.C f : Total L) ≠ (auxVar 1 : Total L) := by
  intro h
  have hav : (auxVar 1 : Total L) = MvPolynomial.X 0 := by rw [auxVar]
  have hc := congrArg (MvPolynomial.constantCoeff (σ := ℕ) (R := Sym.Lambda L)) h
  rw [constantCoeff_dplusStar_C, hav] at hc
  have hf : f = 0 := by simpa using hc
  rw [hf, map_zero, map_zero] at h
  refine MvPolynomial.X_ne_zero (R := Sym.Lambda L) 0 ?_
  rw [← hav, ← h]

/-- **`y_1` is not an argument the commutation is ever asked about.** -/
theorem auxVar_notMem_range_dplusStar_C (q u : L) :
    (auxVar 1 : Total L) ∉
      Set.range (fun f : Sym.Lambda L => dplusStar q u 0 (MvPolynomial.C f : Total L)) := by
  rintro ⟨f, hf⟩
  exact dplusStar_C_ne_auxVar q u 0 f hf

end HJO.Sweep

namespace HJO.Sym

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-! ### The `Λ` side at `f = e_2`: `Q_{2,1}(e_2)` -/

/-- **`D_0(e_3) = e_3 - (1+q+u)Me_1e_2 - (q^2+qu+u^2)Me_3`.** `HJO.Sym.dop_elemSymm` at `k = 0`,
`r = 3`; the four kernel values are `1`, `M`, `-(q+u)M`, `(q^2+qu+u^2)M`, paired with
`e_0, -e_1, e_2, -e_3`. -/
theorem dop_zero_elemSymm_three (q u : L) :
    Dop q u 0 (elemSymm L 3)
      = elemSymm L 3 - ((1 + q + u) * ((1 - q) * (1 - u))) • (elemSymm L 1 * elemSymm L 2)
        - ((q ^ 2 + q * u + u ^ 2) * ((1 - q) * (1 - u))) • elemSymm L 3 := by
  rw [dop_elemSymm, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero, Bglx.paramPleth_elemSymm_zero,
    Bglx.paramPleth_elemSymm_one_eq, Bglx.paramPleth_elemSymm_two_eq,
    Bglx.paramPleth_elemSymm_three_eq]
  simp only [MvPolynomial.smul_eq_C_mul, map_sub, map_add, map_mul, map_neg, map_one, map_pow,
    Nat.sub_zero, Nat.sub_self]
  norm_num [elemSymm_zero L]
  ring

/-- **`D_1(e_1^2) = -e_1^3 + 2Me_1e_2 - M^2e_3`.** The Pieri rule `HJO.Sym.dop_elemSymm_one_mul` at
`k = 1`, `f = e_1`, reading `HJO.Sym.dop_one_elemSymm_one` and `HJO.Sym.dop_two_elemSymm_one`. -/
theorem dop_one_elemSymm_one_sq (q u : L) :
    Dop q u 1 (elemSymm L 1 * elemSymm L 1)
      = -(elemSymm L 1 * elemSymm L 1 * elemSymm L 1)
        + (2 * ((1 - q) * (1 - u))) • (elemSymm L 1 * elemSymm L 2)
        - (((1 - q) * (1 - u)) ^ 2) • elemSymm L 3 := by
  rw [dop_elemSymm_one_mul q u 1 (elemSymm L 1), dop_one_elemSymm_one, dop_two_elemSymm_one]
  simp only [MvPolynomial.smul_eq_C_mul, map_sub, map_mul, map_one, map_pow, map_ofNat]
  ring

/-- **`D_0(e_1e_2) = -Me_1^3 + (1 - (q+u)M + M(M-1))e_1e_2 + (q+u)M^2e_3`.** The Pieri rule at
`k = 0`, `f = e_2`, reading `HJO.Sym.dop_zero_elemSymm_two` and `HJO.Sym.dop_one_elemSymm_two`. -/
theorem dop_zero_elemSymm_one_mul_two (q u : L) :
    Dop q u 0 (elemSymm L 1 * elemSymm L 2)
      = (-((1 - q) * (1 - u))) • (elemSymm L 1 * elemSymm L 1 * elemSymm L 1)
        + (1 - (q + u) * ((1 - q) * (1 - u))
            + ((1 - q) * (1 - u)) * (((1 - q) * (1 - u)) - 1)) • (elemSymm L 1 * elemSymm L 2)
        + ((q + u) * ((1 - q) * (1 - u)) ^ 2) • elemSymm L 3 := by
  rw [dop_elemSymm_one_mul q u 0 (elemSymm L 2), dop_zero_elemSymm_two, dop_one_elemSymm_two]
  simp only [MvPolynomial.smul_eq_C_mul, map_sub, map_add, map_mul, map_neg, map_one, map_pow]
  ring

/-- **`Q_{2,1}(e_2) = Me_1^3 + c_2e_1e_2 + c_1e_3`**, with

`c_2 = -M^2 + (q+u)(1+q+u)M - 1`,   `c_1 = M(M + (q+u)(q^2+u^2))`.

`HJO.Sym.Qop`'s recursion on the column (`HJO.Sweep.qop_succ_succ_one` at `b = 0`) is
`Q_{2,1} = M^{-1}(D_1D_0 - D_0D_1)`, and the four values it reads at `e_2` are
`HJO.Sym.dop_zero_elemSymm_two`, `HJO.Sym.dop_one_elemSymm_two`,
`HJO.Sym.dop_one_elemSymm_one_sq`, `HJO.Sym.dop_zero_elemSymm_one_mul_two` and
`HJO.Sym.dop_zero_elemSymm_three`.

**This is the first `Λ`-side value of the `(a,1)` column at a coefficient with `D_0f ∉ Lf`**: at
`f = e_1` the recursion closes because `D_0(e_1)` is a scalar multiple of `e_1`; here it is not
(`HJO.Sym.dop_zero_elemSymm_two`). -/
theorem qop_two_one_elemSymm_two (hM : (1 - q) * (1 - u) ≠ 0) :
    Qop q u 2 1 (elemSymm L 2)
      = ((1 - q) * (1 - u)) • (elemSymm L 1 * elemSymm L 1 * elemSymm L 1)
        + (-((1 - q) * (1 - u)) ^ 2 + (q + u) * (1 + q + u) * ((1 - q) * (1 - u)) - 1)
            • (elemSymm L 1 * elemSymm L 2)
        + (((1 - q) * (1 - u)) * (((1 - q) * (1 - u)) + (q + u) * (q ^ 2 + u ^ 2)))
            • elemSymm L 3 := by
  have h := Sweep.qop_succ_succ_one (L := L) q u 0
  rw [show (0 : ℕ) + 2 = 2 from rfl, show (0 : ℕ) + 1 = 1 from rfl, qop_one] at h
  rw [h, LinearMap.smul_apply, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
    dop_zero_elemSymm_two, dop_one_elemSymm_two, map_sub, map_sub, map_smul, map_smul, map_add,
    map_smul, map_smul, dop_one_elemSymm_two, dop_one_elemSymm_one_sq,
    dop_zero_elemSymm_one_mul_two, dop_zero_elemSymm_three, inv_smul_eq_iff₀ hM]
  simp only [MvPolynomial.smul_eq_C_mul, map_sub, map_add, map_mul, map_neg, map_one, map_pow,
    map_ofNat]
  ring

end HJO.Sym

namespace HJO.Sym

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-! ### The Hall--Littlewood values the sweep side reads -/

/-- `B_0(e_2) = e_2 - (1-q)e_1^2 - q(1-q)e_2`: `HJO.Sym.bop_natCast` reads `B_m` as `D_m` at
`u = 0`, and `HJO.Sym.dop_zero_elemSymm_two` there. -/
theorem bop_zero_elemSymm_two (q : L) :
    Bop q ((0 : ℕ) : ℤ) (elemSymm L 2)
      = elemSymm L 2 - (1 - q) • (elemSymm L 1 * elemSymm L 1) - (q * (1 - q)) • elemSymm L 2 := by
  rw [bop_natCast, dop_zero_elemSymm_two]
  simp only [MvPolynomial.smul_eq_C_mul, map_sub, map_add, map_mul, map_one, map_zero]
  ring

/-- `B_1(e_2) = -qe_1e_2 + q(1-q)e_3`. -/
theorem bop_one_elemSymm_two (q : L) :
    Bop q ((1 : ℕ) : ℤ) (elemSymm L 2)
      = (-q) • (elemSymm L 1 * elemSymm L 2) + (q * (1 - q)) • elemSymm L 3 := by
  rw [bop_natCast, dop_one_elemSymm_two]
  simp only [MvPolynomial.smul_eq_C_mul, map_sub, map_add, map_neg, map_mul, map_one, map_zero]
  ring

/-- `B_1(e_1^2) = -e_1^3 + 2(1-q)e_1e_2 - (1-q)^2e_3`, off `HJO.Sym.dop_one_elemSymm_one_sq`. -/
theorem bop_one_elemSymm_one_sq (q : L) :
    Bop q ((1 : ℕ) : ℤ) (elemSymm L 1 * elemSymm L 1)
      = -(elemSymm L 1 * elemSymm L 1 * elemSymm L 1)
        + (2 * (1 - q)) • (elemSymm L 1 * elemSymm L 2) - ((1 - q) ^ 2) • elemSymm L 3 := by
  rw [bop_natCast, dop_one_elemSymm_one_sq]
  simp only [MvPolynomial.smul_eq_C_mul, map_sub, map_mul, map_one, map_zero,
    map_pow, map_ofNat]
  ring

end HJO.Sym

namespace HJO.Sweep

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-! ### The vertex step on the degree-two part of `V_1` -/

/-- `d^*_+(ιe_2) = ιe_2 + (q-1)u·y_1ιe_1 + (1-q)u^2·y_1^2`, the `y_1`-graded form of
`HJO.Sweep.dplusStar_C_elemSymm_two_sub` with the scalars as `•`. -/
theorem dplusStar_C_elemSymm_two_smul (q u : L) (k : ℕ) :
    dplusStar q u k (MvPolynomial.C (Sym.elemSymm L 2) : Total L)
      = (MvPolynomial.C (Sym.elemSymm L 2) : Total L)
        + ((q - 1) * u) • ((auxVar 1 : Total L) * MvPolynomial.C (Sym.elemSymm L 1))
        + ((1 - q) * u ^ 2) • ((auxVar 1 : Total L) ^ 2) := by
  have h := dplusStar_C_elemSymm_two_sub q u k
  simp only [smul_eq_scal_mul]
  linear_combination h

/-- **`T(ιe_2) = -(1-q)ιe_1^2 + (1-q+q^2)ιe_2 + (1-q)u·y_1ιe_1`.**

The two-term evaluation `HJO.Sweep.vertexStep_auxVar_pow_mul_C` at `m = 0`, `A = e_2`, cleared of
its `(1-q)^{-1}`: the `d^*_+` half reads `HJO.Sym.bop_zero_elemSymm_two` and then
`HJO.Sweep.dplusStar_C_mul` on `e_1^2`, and the `B_0` half reads
`HJO.Sweep.bopExt_auxVar_pow_mul_C` on the three `y_1`-graded pieces of `d^*_+(ιe_2)`. The `y_1^2`
components cancel, which is why the value stays inside `span(ιe_1^2, ιe_2, y_1ιe_1)`.

`q ≠ 1` and nothing on `u`. -/
theorem vertexStep_C_elemSymm_two (hq1 : q ≠ 1) :
    vertexStep q u (MvPolynomial.C (Sym.elemSymm L 2) : Total L)
      = (-(1 - q)) • ((MvPolynomial.C (Sym.elemSymm L 1) : Total L)
            * MvPolynomial.C (Sym.elemSymm L 1))
        + (1 - q + q ^ 2) • (MvPolynomial.C (Sym.elemSymm L 2) : Total L)
        + ((1 - q) * u) • ((auxVar 1 : Total L) * MvPolynomial.C (Sym.elemSymm L 1)) := by
  have hne : (1 - scal q : Total L) ≠ 0 := by
    rw [show (1 - scal q : Total L) = scal (1 - q) from by rw [scal_sub, scal_one]]
    simp only [scal, ne_eq, MvPolynomial.C_eq_zero, sub_eq_zero]
    exact fun h => hq1 h.symm
  -- `d^*_+` on the two constants, and on `e_1^2` by multiplicativity
  have hd1 : dplusStar q u 0 (MvPolynomial.C (Sym.elemSymm L 1) : Total L)
      = (MvPolynomial.C (Sym.elemSymm L 1) : Total L)
        + ((q - 1) * u) • (auxVar 1 : Total L) := dplusStar_C_elemSymm_one_smul q u 0
  have hd11 : dplusStar q u 0 (MvPolynomial.C (Sym.elemSymm L 1 * Sym.elemSymm L 1) : Total L)
      = ((MvPolynomial.C (Sym.elemSymm L 1) : Total L)
          + ((q - 1) * u) • (auxVar 1 : Total L))
        * ((MvPolynomial.C (Sym.elemSymm L 1) : Total L)
          + ((q - 1) * u) • (auxVar 1 : Total L)) := by
    rw [dplusStar_C_mul, hd1]
  -- the `d^*_+` half
  have hA : dplusStar q u 0
        (MvPolynomial.C (Sym.Bop q ((0 : ℕ) : ℤ) (Sym.elemSymm L 2)) : Total L)
      = dplusStar q u 0 (MvPolynomial.C (Sym.elemSymm L 2) : Total L)
        - (1 - q) • dplusStar q u 0
            (MvPolynomial.C (Sym.elemSymm L 1 * Sym.elemSymm L 1) : Total L)
        - (q * (1 - q)) • dplusStar q u 0 (MvPolynomial.C (Sym.elemSymm L 2) : Total L) := by
    rw [Sym.bop_zero_elemSymm_two]
    simp only [map_sub, C_smul, map_smul]
  -- the `B_0` half, on the `y_1`-graded pieces of `d^*_+(ιe_2)`
  have hgr : dplusStar q u 0 (MvPolynomial.C (Sym.elemSymm L 2) : Total L)
      = (auxVar 1 : Total L) ^ 0 * MvPolynomial.C (Sym.elemSymm L 2)
        + ((q - 1) * u) • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (Sym.elemSymm L 1))
        + ((1 - q) * u ^ 2) • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (1 : Sym.Lambda L)) := by
    rw [dplusStar_C_elemSymm_two_smul, pow_zero, one_mul, pow_one, MvPolynomial.C_1, mul_one]
  have hB : bopExt q ((0 : ℕ) : ℤ)
        (dplusStar q u 0 (MvPolynomial.C (Sym.elemSymm L 2) : Total L))
      = (MvPolynomial.C (Sym.Bop q ((0 : ℕ) : ℤ) (Sym.elemSymm L 2)) : Total L)
        + ((q - 1) * u) • ((auxVar 1 : Total L) * MvPolynomial.C (q • Sym.elemSymm L 1))
        + ((1 - q) * u ^ 2) • ((auxVar 1 : Total L) ^ 2) := by
    rw [hgr, map_add, map_add, map_smul, map_smul, bopExt_auxVar_pow_mul_C,
      bopExt_auxVar_pow_mul_C, bopExt_auxVar_pow_mul_C, pow_zero, one_mul, pow_one]
    rw [show Sym.Bop q ((0 : ℕ) : ℤ) (Sym.elemSymm L 1) = q • Sym.elemSymm L 1 from by
      rw [Nat.cast_zero, Sym.bop_zero_elemSymm_one, MvPolynomial.smul_eq_C_mul]]
    rw [show Sym.Bop q ((0 : ℕ) : ℤ) (1 : Sym.Lambda L) = 1 from by
      rw [Sym.bop_one, Nat.cast_zero, Sym.elemSymmAlt_zero]]
    rw [MvPolynomial.C_1, mul_one]
  have hBop2 : (MvPolynomial.C (Sym.Bop q ((0 : ℕ) : ℤ) (Sym.elemSymm L 2)) : Total L)
      = (MvPolynomial.C (Sym.elemSymm L 2) : Total L)
        - (1 - q) • ((MvPolynomial.C (Sym.elemSymm L 1) : Total L)
            * MvPolynomial.C (Sym.elemSymm L 1))
        - (q * (1 - q)) • (MvPolynomial.C (Sym.elemSymm L 2) : Total L) := by
    rw [Sym.bop_zero_elemSymm_two]
    simp only [map_sub, C_smul, map_mul]
  have hBop1 : (MvPolynomial.C (q • Sym.elemSymm L 1) : Total L)
      = q • (MvPolynomial.C (Sym.elemSymm L 1) : Total L) := C_smul q _
  refine mul_left_cancel₀ hne ?_
  have h := scal_sub_mul_vertexStep_auxVar_pow_mul_C (q := q) (u := u) hq1 0 (Sym.elemSymm L 2)
  rw [pow_zero, one_mul, hA, hB, hd11, dplusStar_C_elemSymm_two_smul, hBop2, hBop1] at h
  rw [h]
  simp only [smul_eq_scal_mul, scal_sub, scal_add, scal_mul, scal_neg, scal_one, scal_pow]
  ring

/-- `B_r(y_1) = y_1·ι(B_r1)`: the coefficientwise extension acts on the `Λ`-coefficient only. -/
theorem bopExt_auxVar_one (q : L) (r : ℤ) :
    bopExt q r (auxVar 1 : Total L)
      = (auxVar 1 : Total L) * MvPolynomial.C (Sym.Bop q r (1 : Sym.Lambda L)) := by
  have h := bopExt_auxVar_pow_mul_C q r 1 (1 : Sym.Lambda L)
  rw [pow_one, MvPolynomial.C_1, mul_one] at h
  exact h

/-- **`T(y_1ιe_1) = -ιe_1^2 + (1-q)ιe_2 + u·y_1ιe_1`.** The `y_1`-degree recursion
`HJO.Sweep.vertexStep_auxVar_pow_succ_mul_C` at `m = 0`, `A = e_1`: the two data are
`T(ιe_1) = qιe_1` (`HJO.Sweep.vertexStep_C_elemSymm_one`) and `B_1(d^*_+(ιe_1))`, whose two pieces
are `B_1(e_1) = -e_1^2 + (1-q)e_2` (`HJO.Sym.bop_one_elemSymm_one`) and `B_1(1) = -e_1`. The `qu`
of the first term cancels against the `-(q-1)u` of the second, leaving `u`. -/
theorem vertexStep_auxVar_mul_C_elemSymm_one (hq1 : q ≠ 1) :
    vertexStep q u ((auxVar 1 : Total L) * MvPolynomial.C (Sym.elemSymm L 1))
      = (-1 : L) • ((MvPolynomial.C (Sym.elemSymm L 1) : Total L)
            * MvPolynomial.C (Sym.elemSymm L 1))
        + (1 - q) • (MvPolynomial.C (Sym.elemSymm L 2) : Total L)
        + u • ((auxVar 1 : Total L) * MvPolynomial.C (Sym.elemSymm L 1)) := by
  have hb : bopExt q ((1 : ℤ)) (dplusStar q u 0 (MvPolynomial.C (Sym.elemSymm L 1) : Total L))
      = (-(1 : L)) • ((MvPolynomial.C (Sym.elemSymm L 1) : Total L)
            * MvPolynomial.C (Sym.elemSymm L 1))
        + (1 - q) • (MvPolynomial.C (Sym.elemSymm L 2) : Total L)
        + (-((q - 1) * u)) • ((auxVar 1 : Total L) * MvPolynomial.C (Sym.elemSymm L 1)) := by
    rw [dplusStar_C_elemSymm_one_smul, map_add, map_smul, bopExt_C, bopExt_auxVar_one,
      show Sym.Bop q (1 : ℤ) (1 : Sym.Lambda L) = -Sym.elemSymm L 1 from by
        rw [Sym.bop_one, show (1 : ℤ) = ((1 : ℕ) : ℤ) from by norm_num,
          Sym.elemSymmAlt_natCast]
        ring,
      Sym.bop_one_elemSymm_one]
    simp only [map_add, map_neg, map_mul, smul_eq_scal_mul, scal_sub, scal_neg, scal_one, scal_mul]
    rw [show (MvPolynomial.C (MvPolynomial.C (1 - q) : Sym.Lambda L) : Total L)
        = scal (1 - q) from rfl]
    rw [scal_sub, scal_one]
    ring
  have h := vertexStep_auxVar_pow_succ_mul_C (q := q) (u := u) hq1 0 (Sym.elemSymm L 1)
  rw [pow_zero, one_mul, pow_one, Nat.cast_zero, zero_add, vertexStep_C_elemSymm_one hq1, hb,
    starLetter_eq_smul] at h
  rw [h]
  simp only [smul_eq_scal_mul, scal_sub, scal_neg, scal_one, scal_mul]
  ring

/-- **`T(y_1^2) = ιe_2 - u·y_1ιe_1 + u^2y_1^2`**, the `m = 2` case of the closed form on the
`y_1`-axis `HJO.Sweep.vertexStep_auxVar_pow`. -/
theorem vertexStep_auxVar_sq (hq1 : q ≠ 1) :
    vertexStep q u ((auxVar 1 : Total L) ^ 2)
      = (MvPolynomial.C (Sym.elemSymm L 2) : Total L)
        + (-u) • ((auxVar 1 : Total L) * MvPolynomial.C (Sym.elemSymm L 1))
        + (u ^ 2) • ((auxVar 1 : Total L) ^ 2) := by
  have h := vertexStep_auxVar_pow (q := q) (u := u) hq1 2
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one] at h
  simp only [Sym.elemSymmAlt_natCast] at h
  rw [h]
  simp only [starLetter_eq_smul, smul_eq_scal_mul, scal_neg, scal_pow, map_neg, map_one, map_mul,
    map_pow]
  norm_num [Sym.elemSymm_zero L]
  ring

/-- **`T(d^*_+(ιe_2))`, the whole degree-two computation**: the four coefficients of the vertex step
on the plethystic shift of `e_2`, in the basis `ιe_1^2, ιe_2, y_1ιe_1, y_1^2` of the degree-two part
of `V_1`. The three values combined are `HJO.Sweep.vertexStep_C_elemSymm_two`,
`HJO.Sweep.vertexStep_auxVar_mul_C_elemSymm_one` and `HJO.Sweep.vertexStep_auxVar_sq`. -/
theorem vertexStep_dplusStar_C_elemSymm_two (hq1 : q ≠ 1) :
    vertexStep q u (dplusStar q u 0 (MvPolynomial.C (Sym.elemSymm L 2) : Total L))
      = ((q - 1) * (1 - u)) • ((MvPolynomial.C (Sym.elemSymm L 1) : Total L)
            * MvPolynomial.C (Sym.elemSymm L 1))
        + ((1 - q + q ^ 2) - (1 - q) ^ 2 * u + (1 - q) * u ^ 2)
            • (MvPolynomial.C (Sym.elemSymm L 2) : Total L)
        + ((1 - q) * u - (1 - q) * u ^ 2 - (1 - q) * u ^ 3)
            • ((auxVar 1 : Total L) * MvPolynomial.C (Sym.elemSymm L 1))
        + ((1 - q) * u ^ 4) • ((auxVar 1 : Total L) ^ 2) := by
  rw [dplusStar_C_elemSymm_two_smul, map_add, map_add, map_smul, map_smul,
    vertexStep_C_elemSymm_two hq1, vertexStep_auxVar_mul_C_elemSymm_one hq1,
    vertexStep_auxVar_sq hq1]
  simp only [smul_eq_scal_mul, scal_sub, scal_add, scal_neg, scal_one, scal_mul, scal_pow]
  ring

/-! ### The sweep side of the column at `f = e_2`, and the clause -/

/-- **The sweep side of the `(2,1)` clause at `f = e_2`:**

`πZΦ(e_2) = Me_1^3 + (-M^2 + (q+u)(1+q+u)M - 1)e_1e_2 + M(M + (q+u)(q^2+u^2))e_3`.

`HJO.Sweep.psiCol_eq` at `b = 1`, then `HJO.Sweep.vertexStep_dplusStar_C_elemSymm_two`, then the
outer `y_1` distributed over the four basis vectors and `d_-` read on each by
`HJO.Sweep.dminus_one_auxVar_pow_mul_C`; the four Hall--Littlewood values are
`HJO.Sym.bop_one_elemSymm_one_sq`, `HJO.Sym.bop_one_elemSymm_two`,
`HJO.Sym.bop_two_elemSymm_one` and `HJO.Sym.bop_three_one`. -/
theorem psiCol_one_elemSymm_two (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    psiCol q u 1 (Sym.elemSymm L 2)
      = ((1 - q) * (1 - u))
          • (MvPolynomial.C (Sym.elemSymm L 1 * Sym.elemSymm L 1 * Sym.elemSymm L 1) : Total L)
        + (-((1 - q) * (1 - u)) ^ 2 + (q + u) * (1 + q + u) * ((1 - q) * (1 - u)) - 1)
          • (MvPolynomial.C (Sym.elemSymm L 1 * Sym.elemSymm L 2) : Total L)
        + (((1 - q) * (1 - u)) * (((1 - q) * (1 - u)) + (q + u) * (q ^ 2 + u ^ 2)))
          • (MvPolynomial.C (Sym.elemSymm L 3) : Total L) := by
  have hmul : (auxVar 1 : Total L)
      * (((q - 1) * (1 - u)) • ((MvPolynomial.C (Sym.elemSymm L 1) : Total L)
            * MvPolynomial.C (Sym.elemSymm L 1))
        + ((1 - q + q ^ 2) - (1 - q) ^ 2 * u + (1 - q) * u ^ 2)
            • (MvPolynomial.C (Sym.elemSymm L 2) : Total L)
        + ((1 - q) * u - (1 - q) * u ^ 2 - (1 - q) * u ^ 3)
            • ((auxVar 1 : Total L) * MvPolynomial.C (Sym.elemSymm L 1))
        + ((1 - q) * u ^ 4) • ((auxVar 1 : Total L) ^ 2))
      = ((q - 1) * (1 - u))
          • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (Sym.elemSymm L 1 * Sym.elemSymm L 1))
        + ((1 - q + q ^ 2) - (1 - q) ^ 2 * u + (1 - q) * u ^ 2)
          • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (Sym.elemSymm L 2))
        + ((1 - q) * u - (1 - q) * u ^ 2 - (1 - q) * u ^ 3)
          • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (Sym.elemSymm L 1))
        + ((1 - q) * u ^ 4)
          • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (1 : Sym.Lambda L)) := by
    simp only [map_mul, MvPolynomial.C_1, smul_eq_scal_mul]
    ring
  have hb2e1 : Sym.Bop q ((2 : ℕ) : ℤ) (Sym.elemSymm L 1)
      = Sym.elemSymm L 1 * Sym.elemSymm L 2 - (1 - q) • Sym.elemSymm L 3 := by
    rw [Sym.bop_two_elemSymm_one, MvPolynomial.smul_eq_C_mul]
  have h2 : (scal (2 : L) : Total L) = 2 := by
    rw [scal_eq_algebraMap]
    exact map_ofNat _ 2
  rw [psiCol_eq hq0 hu0 hq1 1 (Sym.elemSymm L 2), pow_one,
    vertexStep_dplusStar_C_elemSymm_two hq1, hmul, map_add, map_add, map_add, map_smul, map_smul,
    map_smul, map_smul, dminus_one_auxVar_pow_mul_C, dminus_one_auxVar_pow_mul_C,
    dminus_one_auxVar_pow_mul_C, dminus_one_auxVar_pow_mul_C, Sym.bop_one_elemSymm_one_sq,
    Sym.bop_one_elemSymm_two, hb2e1, Sym.bop_three_one]
  simp only [map_add, map_sub, map_neg, C_smul, smul_eq_scal_mul, scal_sub, scal_add,
    scal_neg, scal_one, scal_mul, scal_pow, h2]
  ring

/-- **The clause `HJO.Mellit.lhsRewrite_sweepWitness` at the slope `(2,1)` and `f = e_2`.**

The `Λ` side is `HJO.Sym.qop_two_one_elemSymm_two`, the sweep side
`HJO.Sweep.psiCol_one_elemSymm_two`, **and they agree.**

This is the first test of the `(a,1)` column at a coefficient with `D_0f ∉ Lf`. At `f = e_1` the
commutation `HJO.Sweep.ColumnCommutes` holds for a degenerate reason
(`HJO.Sweep.columnCommutes_at_elemSymm_one`): `D_0(e_1)` is a scalar multiple of `e_1`, so the
term's argument is not a new argument. Here `D_0(e_2) = e_2 - Me_1^2 - (q+u)Me_2` leaves the line
(`HJO.Sym.dop_zero_elemSymm_two`), the two sides are computed independently --- the sweep side
through `T` and two Hall--Littlewood values, the `Λ` side through `HJO.Sym.Qop`'s commutator and
five `D`-values --- and the `q ↔ u` symmetry of the `Λ` side is not visible on the sweep side at
all. It is not a reduction: no hypothesis is discharged.

`q ≠ 0`, `u ≠ 0`, `q ≠ 1` are the letter `Z`'s, `M ≠ 0` is `HJO.Sym.Qop`'s normalisation. -/
theorem lhsSlopeAt_two_one_elemSymm_two (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1)
    (hM : (1 - q) * (1 - u) ≠ 0) : Mellit.LhsSlopeAt q u 2 1 (Sym.elemSymm L 2) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, lhsSlopeAt_succ_one_iff_psiCol,
    psiCol_one_elemSymm_two hq0 hu0 hq1, Sym.qop_two_one_elemSymm_two hM]
  simp only [map_add, C_smul]

/-- **The commutation `HJO.Sweep.ColumnCommutes` at `b = 0` and `f = e_2` holds** --- the first
instance of it at an argument the `e_1`-line does not see. Equivalent to
`HJO.Sweep.lhsSlopeAt_two_one_elemSymm_two` through `HJO.Sym.Qop`'s recursion, which is what makes
it an instance of the commutation rather than a separate claim. -/
theorem columnCommutes_zero_at_elemSymm_two (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1)
    (hM : (1 - q) * (1 - u) ≠ 0) :
    ((1 - q) * (1 - u)) • psiCol q u 1 (Sym.elemSymm L 2)
      = psiCol q u 0 (Sym.Dop q u 0 (Sym.elemSymm L 2))
        - dminus q 1 (dplusStar q u 0 (psiCol q u 0 (Sym.elemSymm L 2))) := by
  have h1 : psiCol q u 1 (Sym.elemSymm L 2)
      = MvPolynomial.C (Sym.Qop q u (1 + 1) 1 (Sym.elemSymm L 2)) := by
    have h := lhsSlopeAt_two_one_elemSymm_two hq0 hu0 hq1 hM
    rw [show (2 : ℕ) = 1 + 1 from rfl, lhsSlopeAt_succ_one_iff_psiCol] at h
    exact h.symm
  have h := qop_succ_succ_one (L := L) q u 0
  rw [show (0 : ℕ) + 2 = 1 + 1 from rfl, show (0 : ℕ) + 1 = 1 from rfl, Sym.qop_one] at h
  rw [h1, psiCol_zero, psiCol_zero, ← dop_zero_eq_dminus_dplusStar, ← C_smul, ← map_sub]
  refine congrArg MvPolynomial.C ?_
  rw [h, LinearMap.smul_apply, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
    smul_inv_smul₀ hM]

end HJO.Sweep


namespace HJO.Sym

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-! ### The other degree-two coefficient: `f = e_1^2` -/

/-- **`D_0(e_1^3) = (1-3M)e_1^3 + 3M^2e_1e_2 - M^3e_3`**, the Pieri rule at `k = 0`, `f = e_1^2`. -/
theorem dop_zero_elemSymm_one_cube (q u : L) :
    Dop q u 0 (elemSymm L 1 * elemSymm L 1 * elemSymm L 1)
      = (1 - 3 * ((1 - q) * (1 - u)))
          • (elemSymm L 1 * elemSymm L 1 * elemSymm L 1)
        + (3 * ((1 - q) * (1 - u)) ^ 2) • (elemSymm L 1 * elemSymm L 2)
        - (((1 - q) * (1 - u)) ^ 3) • elemSymm L 3 := by
  rw [show elemSymm L 1 * elemSymm L 1 * elemSymm L 1
      = elemSymm L 1 * (elemSymm L 1 * elemSymm L 1) from by ring,
    dop_elemSymm_one_mul q u 0 (elemSymm L 1 * elemSymm L 1), dop_zero_elemSymm_one_sq,
    dop_one_elemSymm_one_sq]
  simp only [MvPolynomial.smul_eq_C_mul, map_sub, map_mul, map_one, map_pow,
    map_ofNat]
  ring

/-- **`Q_{2,1}(e_1^2) = (2M-1)e_1^3 + (2(q+u)M - (2+q+u)M^2)e_1e_2`**
`+ M^2(1 - (q+u) - (q^2+qu+u^2))e_3`, the second degree-two coefficient. Same route as
`HJO.Sym.qop_two_one_elemSymm_two`, reading `HJO.Sym.dop_zero_elemSymm_one_sq`,
`HJO.Sym.dop_one_elemSymm_one_sq`, `HJO.Sym.dop_one_elemSymm_two`,
`HJO.Sym.dop_zero_elemSymm_one_cube`, `HJO.Sym.dop_zero_elemSymm_one_mul_two` and
`HJO.Sym.dop_zero_elemSymm_three`. -/
theorem qop_two_one_elemSymm_one_sq (hM : (1 - q) * (1 - u) ≠ 0) :
    Qop q u 2 1 (elemSymm L 1 * elemSymm L 1)
      = (2 * ((1 - q) * (1 - u)) - 1) • (elemSymm L 1 * elemSymm L 1 * elemSymm L 1)
        + (2 * (q + u) * ((1 - q) * (1 - u))
            - (2 + q + u) * ((1 - q) * (1 - u)) ^ 2) • (elemSymm L 1 * elemSymm L 2)
        + (((1 - q) * (1 - u)) ^ 2 * (1 - (q + u) - (q ^ 2 + q * u + u ^ 2))) • elemSymm L 3 := by
  have h := Sweep.qop_succ_succ_one (L := L) q u 0
  rw [show (0 : ℕ) + 2 = 2 from rfl, show (0 : ℕ) + 1 = 1 from rfl, qop_one] at h
  rw [h, LinearMap.smul_apply, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
    dop_zero_elemSymm_one_sq, dop_one_elemSymm_one_sq, map_add, map_smul, map_smul,
    dop_one_elemSymm_one_sq, dop_one_elemSymm_two, map_sub, map_add, map_neg, map_smul, map_smul,
    dop_zero_elemSymm_one_cube, dop_zero_elemSymm_one_mul_two, dop_zero_elemSymm_three,
    inv_smul_eq_iff₀ hM]
  simp only [MvPolynomial.smul_eq_C_mul, map_sub, map_add, map_neg, map_mul, map_one, map_pow,
    map_ofNat]
  ring

end HJO.Sym

namespace HJO.Sweep

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-- `d^*_+(ιe_1^2) = ιe_1^2 + 2(q-1)u·y_1ιe_1 + (q-1)^2u^2·y_1^2`, off multiplicativity. -/
theorem dplusStar_C_elemSymm_one_sq_smul (q u : L) :
    dplusStar q u 0 (MvPolynomial.C (Sym.elemSymm L 1 * Sym.elemSymm L 1) : Total L)
      = (MvPolynomial.C (Sym.elemSymm L 1 * Sym.elemSymm L 1) : Total L)
        + (2 * ((q - 1) * u)) • ((auxVar 1 : Total L) * MvPolynomial.C (Sym.elemSymm L 1))
        + (((q - 1) * u) ^ 2) • ((auxVar 1 : Total L) ^ 2) := by
  have h2 : (scal (2 : L) : Total L) = 2 := by
    rw [scal_eq_algebraMap]
    exact map_ofNat _ 2
  rw [dplusStar_C_mul, dplusStar_C_elemSymm_one_smul]
  simp only [map_mul, smul_eq_scal_mul, scal_mul, scal_sub, scal_one, scal_pow, h2]
  ring

/-- **`T(ιe_1^2) = (2q-1)ιe_1^2 + (1-q)^2ιe_2 + (q-1)^2u·y_1ιe_1`**, the two-term evaluation at
`m = 0`, `A = e_1^2`, with `B_0(e_1^2)` read off `HJO.Sym.dop_zero_elemSymm_one_sq` at `u = 0`. The
`y_1^2` component cancels here too. -/
theorem vertexStep_C_elemSymm_one_sq (hq1 : q ≠ 1) :
    vertexStep q u (MvPolynomial.C (Sym.elemSymm L 1 * Sym.elemSymm L 1) : Total L)
      = (2 * q - 1) • (MvPolynomial.C (Sym.elemSymm L 1 * Sym.elemSymm L 1) : Total L)
        + ((1 - q) ^ 2) • (MvPolynomial.C (Sym.elemSymm L 2) : Total L)
        + ((q - 1) ^ 2 * u) • ((auxVar 1 : Total L) * MvPolynomial.C (Sym.elemSymm L 1)) := by
  have hne : (1 - scal q : Total L) ≠ 0 := by
    rw [show (1 - scal q : Total L) = scal (1 - q) from by rw [scal_sub, scal_one]]
    simp only [scal, ne_eq, MvPolynomial.C_eq_zero, sub_eq_zero]
    exact fun h => hq1 h.symm
  have h2 : (scal (2 : L) : Total L) = 2 := by
    rw [scal_eq_algebraMap]
    exact map_ofNat _ 2
  have hb0 : Sym.Bop q ((0 : ℕ) : ℤ) (Sym.elemSymm L 1 * Sym.elemSymm L 1)
      = (2 * q - 1) • (Sym.elemSymm L 1 * Sym.elemSymm L 1) + ((1 - q) ^ 2) • Sym.elemSymm L 2 := by
    rw [Sym.bop_natCast, Sym.dop_zero_elemSymm_one_sq]
    simp only [MvPolynomial.smul_eq_C_mul, map_sub, map_mul, map_one, map_zero, map_pow,
      map_ofNat]
    ring
  have hA : dplusStar q u 0
        (MvPolynomial.C (Sym.Bop q ((0 : ℕ) : ℤ) (Sym.elemSymm L 1 * Sym.elemSymm L 1)) : Total L)
      = (2 * q - 1) • dplusStar q u 0
            (MvPolynomial.C (Sym.elemSymm L 1 * Sym.elemSymm L 1) : Total L)
        + ((1 - q) ^ 2) • dplusStar q u 0 (MvPolynomial.C (Sym.elemSymm L 2) : Total L) := by
    rw [hb0]
    simp only [map_add, C_smul, map_smul]
  have hgr : dplusStar q u 0 (MvPolynomial.C (Sym.elemSymm L 1 * Sym.elemSymm L 1) : Total L)
      = (auxVar 1 : Total L) ^ 0 * MvPolynomial.C (Sym.elemSymm L 1 * Sym.elemSymm L 1)
        + (2 * ((q - 1) * u)) • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (Sym.elemSymm L 1))
        + (((q - 1) * u) ^ 2) • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (1 : Sym.Lambda L)) := by
    rw [dplusStar_C_elemSymm_one_sq_smul, pow_zero, one_mul, pow_one, MvPolynomial.C_1, mul_one]
  have hB : bopExt q ((0 : ℕ) : ℤ)
        (dplusStar q u 0 (MvPolynomial.C (Sym.elemSymm L 1 * Sym.elemSymm L 1) : Total L))
      = (MvPolynomial.C (Sym.Bop q ((0 : ℕ) : ℤ) (Sym.elemSymm L 1 * Sym.elemSymm L 1)) : Total L)
        + (2 * ((q - 1) * u)) • ((auxVar 1 : Total L) * MvPolynomial.C (q • Sym.elemSymm L 1))
        + (((q - 1) * u) ^ 2) • ((auxVar 1 : Total L) ^ 2) := by
    rw [hgr, map_add, map_add, map_smul, map_smul, bopExt_auxVar_pow_mul_C,
      bopExt_auxVar_pow_mul_C, bopExt_auxVar_pow_mul_C, pow_zero, one_mul, pow_one]
    rw [show Sym.Bop q ((0 : ℕ) : ℤ) (Sym.elemSymm L 1) = q • Sym.elemSymm L 1 from by
      rw [Nat.cast_zero, Sym.bop_zero_elemSymm_one, MvPolynomial.smul_eq_C_mul]]
    rw [show Sym.Bop q ((0 : ℕ) : ℤ) (1 : Sym.Lambda L) = 1 from by
      rw [Sym.bop_one, Nat.cast_zero, Sym.elemSymmAlt_zero]]
    rw [MvPolynomial.C_1, mul_one]
  have hBop : (MvPolynomial.C
        (Sym.Bop q ((0 : ℕ) : ℤ) (Sym.elemSymm L 1 * Sym.elemSymm L 1)) : Total L)
      = (2 * q - 1) • (MvPolynomial.C (Sym.elemSymm L 1 * Sym.elemSymm L 1) : Total L)
        + ((1 - q) ^ 2) • (MvPolynomial.C (Sym.elemSymm L 2) : Total L) := by
    rw [hb0]
    simp only [map_add, C_smul]
  have hBop1 : (MvPolynomial.C (q • Sym.elemSymm L 1) : Total L)
      = q • (MvPolynomial.C (Sym.elemSymm L 1) : Total L) := C_smul q _
  refine mul_left_cancel₀ hne ?_
  have h := scal_sub_mul_vertexStep_auxVar_pow_mul_C (q := q) (u := u) hq1 0
    (Sym.elemSymm L 1 * Sym.elemSymm L 1)
  rw [pow_zero, one_mul, hA, hB, hBop, hBop1, dplusStar_C_elemSymm_one_sq_smul,
    dplusStar_C_elemSymm_two_smul] at h
  rw [h]
  simp only [smul_eq_scal_mul, scal_sub, scal_mul, scal_one, scal_pow, h2]
  ring

/-- **`T(d^*_+(ιe_1^2))`**, the four coefficients on the degree-two basis. -/
theorem vertexStep_dplusStar_C_elemSymm_one_sq (hq1 : q ≠ 1) :
    vertexStep q u (dplusStar q u 0 (MvPolynomial.C (Sym.elemSymm L 1 * Sym.elemSymm L 1)
        : Total L))
      = (2 * q - 1 - 2 * (q - 1) * u)
            • (MvPolynomial.C (Sym.elemSymm L 1 * Sym.elemSymm L 1) : Total L)
        + ((1 - q) ^ 2 * (1 - u) ^ 2) • (MvPolynomial.C (Sym.elemSymm L 2) : Total L)
        + ((q - 1) ^ 2 * u + 2 * (q - 1) * u ^ 2 - (q - 1) ^ 2 * u ^ 3)
            • ((auxVar 1 : Total L) * MvPolynomial.C (Sym.elemSymm L 1))
        + ((q - 1) ^ 2 * u ^ 4) • ((auxVar 1 : Total L) ^ 2) := by
  rw [dplusStar_C_elemSymm_one_sq_smul, map_add, map_add, map_smul, map_smul,
    vertexStep_C_elemSymm_one_sq hq1, vertexStep_auxVar_mul_C_elemSymm_one hq1,
    vertexStep_auxVar_sq hq1]
  have h2 : (scal (2 : L) : Total L) = 2 := by
    rw [scal_eq_algebraMap]
    exact map_ofNat _ 2
  simp only [map_mul, smul_eq_scal_mul, scal_sub, scal_add, scal_neg, scal_one, scal_mul, scal_pow,
    h2]
  ring

/-- **The sweep side of the `(2,1)` clause at `f = e_1^2`.** -/
theorem psiCol_one_elemSymm_one_sq (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    psiCol q u 1 (Sym.elemSymm L 1 * Sym.elemSymm L 1)
      = (2 * ((1 - q) * (1 - u)) - 1)
          • (MvPolynomial.C (Sym.elemSymm L 1 * Sym.elemSymm L 1 * Sym.elemSymm L 1) : Total L)
        + (2 * (q + u) * ((1 - q) * (1 - u))
            - (2 + q + u) * ((1 - q) * (1 - u)) ^ 2)
          • (MvPolynomial.C (Sym.elemSymm L 1 * Sym.elemSymm L 2) : Total L)
        + (((1 - q) * (1 - u)) ^ 2 * (1 - (q + u) - (q ^ 2 + q * u + u ^ 2)))
          • (MvPolynomial.C (Sym.elemSymm L 3) : Total L) := by
  have hb2e1 : Sym.Bop q ((2 : ℕ) : ℤ) (Sym.elemSymm L 1)
      = Sym.elemSymm L 1 * Sym.elemSymm L 2 - (1 - q) • Sym.elemSymm L 3 := by
    rw [Sym.bop_two_elemSymm_one, MvPolynomial.smul_eq_C_mul]
  have h2 : (scal (2 : L) : Total L) = 2 := by
    rw [scal_eq_algebraMap]
    exact map_ofNat _ 2
  have hmul : (auxVar 1 : Total L)
      * ((2 * q - 1 - 2 * (q - 1) * u)
            • (MvPolynomial.C (Sym.elemSymm L 1 * Sym.elemSymm L 1) : Total L)
        + ((1 - q) ^ 2 * (1 - u) ^ 2) • (MvPolynomial.C (Sym.elemSymm L 2) : Total L)
        + ((q - 1) ^ 2 * u + 2 * (q - 1) * u ^ 2 - (q - 1) ^ 2 * u ^ 3)
            • ((auxVar 1 : Total L) * MvPolynomial.C (Sym.elemSymm L 1))
        + ((q - 1) ^ 2 * u ^ 4) • ((auxVar 1 : Total L) ^ 2))
      = (2 * q - 1 - 2 * (q - 1) * u)
          • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (Sym.elemSymm L 1 * Sym.elemSymm L 1))
        + ((1 - q) ^ 2 * (1 - u) ^ 2)
          • ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (Sym.elemSymm L 2))
        + ((q - 1) ^ 2 * u + 2 * (q - 1) * u ^ 2 - (q - 1) ^ 2 * u ^ 3)
          • ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (Sym.elemSymm L 1))
        + ((q - 1) ^ 2 * u ^ 4)
          • ((auxVar 1 : Total L) ^ 3 * MvPolynomial.C (1 : Sym.Lambda L)) := by
    simp only [map_mul, MvPolynomial.C_1, smul_eq_scal_mul]
    ring
  rw [psiCol_eq hq0 hu0 hq1 1 (Sym.elemSymm L 1 * Sym.elemSymm L 1), pow_one,
    vertexStep_dplusStar_C_elemSymm_one_sq hq1, hmul, map_add, map_add, map_add, map_smul, map_smul,
    map_smul, map_smul, dminus_one_auxVar_pow_mul_C, dminus_one_auxVar_pow_mul_C,
    dminus_one_auxVar_pow_mul_C, dminus_one_auxVar_pow_mul_C, Sym.bop_one_elemSymm_one_sq,
    Sym.bop_one_elemSymm_two, hb2e1, Sym.bop_three_one]
  simp only [map_add, map_sub, map_neg, C_smul, smul_eq_scal_mul, scal_sub, scal_add,
    scal_neg, scal_one, scal_mul, scal_pow, h2]
  ring

/-- **The clause at the slope `(2,1)` and `f = e_1^2`**, the second degree-two coefficient: the
`Λ` side `HJO.Sym.qop_two_one_elemSymm_one_sq` and the sweep side
`HJO.Sweep.psiCol_one_elemSymm_one_sq` agree. -/
theorem lhsSlopeAt_two_one_elemSymm_one_sq (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1)
    (hM : (1 - q) * (1 - u) ≠ 0) :
    Mellit.LhsSlopeAt q u 2 1 (Sym.elemSymm L 1 * Sym.elemSymm L 1) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, lhsSlopeAt_succ_one_iff_psiCol,
    psiCol_one_elemSymm_one_sq hq0 hu0 hq1, Sym.qop_two_one_elemSymm_one_sq hM]
  simp only [map_add, C_smul]

/-- **The clause at the slope `(2,1)` and `f = 1`**, off the two known vacuum values
`HJO.Sweep.dminus_straightMonomial_slopeArg_one` and `HJO.Sym.qop_apply_one_of_snd_one`. -/
theorem lhsSlopeAt_two_one_one (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1)
    (hM : (1 - q) * (1 - u) ≠ 0) : Mellit.LhsSlopeAt q u 2 1 (1 : Sym.Lambda L) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, lhsSlopeAt_succ_one_iff_psiCol, psiCol,
    dminus_straightMonomial_slopeArg_one hq0 hu0 hq1 0 1,
    Sym.qop_apply_one_of_snd_one hM (by omega : 1 ≤ 1 + 1), map_neg]

/-- **The clause at the slope `(2,1)` holds on the whole of `Λ` in degrees `≤ 2`** --- every linear
combination of `1`, `e_1`, `e_1^2`, `e_2`.

`HJO.Mellit.lhsSlopeCarrier` is a submodule, so the four values
`HJO.Sweep.lhsSlopeAt_two_one_one`, `HJO.Sweep.lhsSlopeAt_succ_one_elemSymm_one`,
`HJO.Sweep.lhsSlopeAt_two_one_elemSymm_one_sq` and `HJO.Sweep.lhsSlopeAt_two_one_elemSymm_two`
propagate. Degree `2` is the first degree at which `D_0` fails to act by a scalar on each
`e`-monomial, so this is the first place the `(a,1)` commutation is tested rather than restated. -/
theorem lhsSlopeAt_two_one_of_deg_le_two (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1)
    (hM : (1 - q) * (1 - u) ≠ 0) (c₀ c₁ c₂ c₃ : L) :
    Mellit.LhsSlopeAt q u 2 1
      (c₀ • (1 : Sym.Lambda L) + c₁ • Sym.elemSymm L 1
        + c₂ • (Sym.elemSymm L 1 * Sym.elemSymm L 1) + c₃ • Sym.elemSymm L 2) := by
  have h0 : (1 : Sym.Lambda L) ∈ Mellit.lhsSlopeCarrier q u 2 1 :=
    lhsSlopeAt_two_one_one hq0 hu0 hq1 hM
  have h1 : Sym.elemSymm L 1 ∈ Mellit.lhsSlopeCarrier q u 2 1 :=
    lhsSlopeAt_succ_one_elemSymm_one hq0 hu0 hq1 hM 1
  have h2 : Sym.elemSymm L 1 * Sym.elemSymm L 1 ∈ Mellit.lhsSlopeCarrier q u 2 1 :=
    lhsSlopeAt_two_one_elemSymm_one_sq hq0 hu0 hq1 hM
  have h3 : Sym.elemSymm L 2 ∈ Mellit.lhsSlopeCarrier q u 2 1 :=
    lhsSlopeAt_two_one_elemSymm_two hq0 hu0 hq1 hM
  exact add_mem (add_mem (add_mem (Submodule.smul_mem _ c₀ h0) (Submodule.smul_mem _ c₁ h1))
    (Submodule.smul_mem _ c₂ h2)) (Submodule.smul_mem _ c₃ h3)

end HJO.Sweep
