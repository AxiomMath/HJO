/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.MellitSlopeGradingTwo
public import HJO.CMStructure.DminusSqBraid
public import HJO.Shuffle.SweepAppendWidth

/-! # The level-raising composite on the coprime row `a = 2`

`HJO.Sweep.lowerRun_two_stageTotal_levelKernelOne`
(`HJO/Shuffle/MellitLevelRaise.lean`) states the level-raising composite on the kernel witness
`F_0 = Ce_1 + qy_1` at **every** slope, as the slope operator read on the grading `2` applied to one
explicit vector, under `T_1` and two lowerings. This file strips that statement down to a bare
`Λ`-side functional, and supplies the reading of `z_1^{(2)}` the row `a = 2` needs.

## The descending train drops out

`HJO.Sweep.lowerRun_two_stageTotal_levelKernelOne_of_slope`: the `T_1` between the slope operator
and the two lowerings is **invisible** to the composite, because `d^♭_-d^♭_-T_{k-1} = d^♭_-d^♭_-`
(`HJO.Sweep.dminus_dminus_braid`) and
`HJO.Sweep.slopeOperator_mem_piece` puts the slope operator's value in `V_2`. So the composite is
`(-1)^{a-1} ct ∘ d_-^2 ∘ Ξ^{(2)}_{a,b}` on `HJO.Sweep.slopeArgTwo`, with no braid letter left.

## The functional is a pair of Hall--Littlewood operators

`HJO.Sweep.constantCoeff_lowerRun_two_C_mul_monomial`: on a monomial of `V_2`,

`ct(d_-^{(1)}d_-^{(2)}(C(A)y_1^my_2^n)) = B_m(B_n A)`,

the `y_1`-exponent giving the outer operator and the `y_2`-exponent the inner one. Together with the
previous paragraph this reduces the whole question to *expanding* `Ξ^{(2)}_{a,b}(slopeArgTwo)` into
monomials: no operator of the sweep survives the reduction.

## `z_1` on `V_2` is `z_1` on `V_1` with a spectator variable

`HJO.Sweep.zopOneStar_one_auxVar_pow_mul_C_eq_zCommTwo` reads
`HJO.Sweep.zCommTwo_monomial` against `HJO.Sweep.zopOneStar_one_auxVar_pow_mul_C`:

`y_2^m · z_1^{(1)}(y_1^nC(A)) = q/(1-q) · zCommTwo(C(A)y_1^my_2^n)`.

So the commutator half of `z_1` at the grading `2` carries **no new content** over the grading-one
evaluation: the `y_1`-exponent becomes the spectator `y_2^m`, the `y_2`-exponent becomes the index
of the grading-one operator, and the two differ by the scalar `q/(1-q)` alone. Unconditional — the
scalar sits on the side where it cannot be inverted.

## Genericity

Nothing in this file has a hypothesis on `q`, `u` or `M`. The inverse scalars `(qu)^{-1}` of
`HJO.Sweep.slopeOperator` and `q^k/(1-q)` of `HJO.Sweep.zop` are carried symbolically throughout,
and at `q = 0`, at `u = 0` and at `q = 1` they are `0` in a field, making the corresponding letter
the **zero map**: any evaluation that cancels them against the parameters does need all three
exclusions, and this file performs no such cancellation.

## References

This file builds on `HJO.Sweep.slopeOperator`, `HJO.Sweep.zop`, `HJO.Sym.Bop`, `HJO.Sweep.bopExt`,
`HJO.Sweep.dminus`, `HJO.Sweep.dminus_dminus_braid`.
-/

@[expose] public section

namespace HJO.Sweep

open HJO.Sym

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-! ### The `Λ`-side functional -/

/-- **`ct(d_-^{(1)}d_-^{(2)}(C(A)y_1^my_2^n)) = B_m(B_nA)`.** The two lowerings of
`HJO.Mellit.lowerRun` at `2` read the two auxiliary exponents against the Hall--Littlewood
operators, the `y_1`-exponent outermost, and the constant coefficient then reads off the value in
`Λ`. Unconditional. -/
@[hjo "lem_mellit_level_raise_train"]
theorem constantCoeff_lowerRun_two_C_mul_monomial (q : L) (m n : ℕ) (A : Sym.Lambda L) :
    MvPolynomial.constantCoeff (Mellit.lowerRun q 2
        ((auxVar 1 : Total L) ^ m * (auxVar 2 : Total L) ^ n * MvPolynomial.C A))
      = Sym.Bop q (m : ℤ) (Sym.Bop q (n : ℤ) A) := by
  rw [lowerRun_two_apply,
    show dminus q 1 (dminus q 2
        ((auxVar 1 : Total L) ^ m * (auxVar 2 : Total L) ^ n * MvPolynomial.C A))
      = bopExt q (m : ℤ) (bopExt q (n : ℤ) (MvPolynomial.C A : Total L)) from
      dminus_dminus_auxVar_pow_mul q 0 m n (C_mem_piece A 0),
    bopExt_C, bopExt_C, MvPolynomial.constantCoeff_C]

/-! ### The argument of the slope operator -/

/-- **The vector the slope operator is read on**, `-y_1d^*_+F_0` of
`HJO.Sweep.slopeArg_levelKernelOne`:

`-(Ce_1)y_1 - (q-1)uy_1^2 - qy_1y_2`.

It is slope-free: `HJO.Sweep.stageTotal_one_apply` puts it to the right of `Ξ_{a,b}` at every
`(a,b)`. -/
noncomputable def slopeArgTwo (q u : L) : Total L :=
  -(MvPolynomial.C (Sym.elemSymm L 1) * (auxVar 1 : Total L))
    - scal ((q - 1) * u) * (auxVar 1 : Total L) ^ 2
    - scal q * ((auxVar 1 : Total L) * (auxVar 2 : Total L))

theorem slopeArgTwo_mem_piece (q u : L) : slopeArgTwo q u ∈ piece L 2 := by
  have h1 : (auxVar 1 : Total L) ∈ piece L 2 := auxVar_mem_piece le_rfl (by omega)
  have h2 : (auxVar 2 : Total L) ∈ piece L 2 := auxVar_mem_piece (by omega) le_rfl
  rw [slopeArgTwo]
  exact sub_mem (sub_mem (neg_mem (mul_mem (C_mem_piece _ _) h1))
      (mul_mem (scal_mem_piece _ _) (pow_mem h1 2))) (mul_mem (scal_mem_piece _ _) (mul_mem h1 h2))

/-! ### The descending train drops out of the composite -/

/-- **The level-raising composite on the kernel witness, with no braid letter left.** At every
`(a,b)`:

`d_-^2G_{2,1}(F_0) = (-1)^{a-1}d_-^2(Ξ^{(2)}_{a,b}(slopeArgTwo))`.

The `T_1 = T_{2↘1}` of `HJO.Sweep.lowerRun_two_stageTotal_levelKernelOne` is killed by
`HJO.Sweep.dminus_dminus_braid`, whose hypothesis is supplied by
`HJO.Sweep.slopeOperator_mem_piece`. Unconditional. -/
@[hjo "lem_mellit_level_raise_train"]
theorem lowerRun_two_stageTotal_levelKernelOne_of_slope (q u : L) (a b : ℕ) :
    Mellit.lowerRun q 2 (Mellit.stageTotal q u a b 1 1 (levelKernelOne q))
      = ((-1 : L) ^ (a - 1)) •
          Mellit.lowerRun q 2 (slopeOperator q u 2 a b (slopeArgTwo q u)) := by
  have hmem : slopeOperator q u 2 a b (slopeArgTwo q u) ∈ piece L 2 :=
    slopeOperator_mem_piece q u (by omega) (slopeArgTwo_mem_piece q u)
  rw [lowerRun_two_stageTotal_levelKernelOne, lowerRun_two_apply, ← slopeArgTwo]
  refine congrArg (fun x => ((-1 : L) ^ (a - 1)) • x) ?_
  rw [show braidEnd q 1 (slopeOperator q u 2 a b (slopeArgTwo q u))
      = braid q 1 (slopeOperator q u 2 a b (slopeArgTwo q u)) from rfl]
  exact dminus_dminus_braid q 0 hmem

/-! ### `z_1` on `V_2` against `z_1` on `V_1` -/

/-- **`z_1` at the grading `2` is `z_1` at the grading `1` with a spectator variable.** For every
`m`, `n` and `A`,

`y_2^m · z_1^{(1)}(y_1^nC(A)) = q/(1-q) · zCommTwo(C(A)y_1^my_2^n)`,

with `HJO.Sweep.zCommTwo` the commutator half of `z_1^{(2)}`
(`HJO.Sweep.zopOneStar_two_eq`). Both sides are the same failure of `B_n` to commute with the
one-letter displacement `(q-1)uy_1`, the `y_1`-exponent of the grading-two monomial appearing only
as the untouched factor `y_2^m`.

The scalar `q/(1-q)` is on the left of the equation and is never inverted, so there is **no**
hypothesis on `q`: at `q = 0` and at `q = 1` both sides are `0`. -/
theorem zopOneStar_one_auxVar_pow_mul_C_eq_zCommTwo (q u : L) (m n : ℕ) (A : Sym.Lambda L) :
    (auxVar 2 : Total L) ^ m * zopOneStar q u 1 ((auxVar 1 : Total L) ^ n * MvPolynomial.C A)
      = (q / (1 - q)) •
          zCommTwo q u (MvPolynomial.C A * ((auxVar 1 : Total L) ^ m * (auxVar 2 : Total L) ^ n)) :=
  by rw [zopOneStar_one_auxVar_pow_mul_C, zCommTwo_monomial, mul_smul_comm]

/-! ### `T_1^{-1}` on the three monomials the argument is built from -/

omit [Algebra ℚ L] in
private theorem dividedDiff_one_eq {F G : Total L}
    (h : ((auxVar 2 : Total L) - auxVar 1) * G = F - swapAux L 1 F) :
    dividedDiff 1 F = G :=
  (dividedDiff_unique (i := 1) le_rfl (by
    rw [show (MvPolynomial.X 1 - MvPolynomial.X (1 - 1) : Total L)
        = (auxVar 2 : Total L) - auxVar 1 from rfl]
    exact h)).symm

omit [Algebra ℚ L] in
theorem swapAux_one_auxVar_one : swapAux L 1 (auxVar 1 : Total L) = (auxVar 2 : Total L) :=
  swapAux_auxVar_self le_rfl

omit [Algebra ℚ L] in
theorem dividedDiff_one_auxVar_one_sq :
    dividedDiff 1 ((auxVar 1 : Total L) ^ 2) = -((auxVar 1 : Total L) + auxVar 2) := by
  refine dividedDiff_one_eq ?_
  rw [map_pow, swapAux_one_auxVar_one]
  ring

omit [Algebra ℚ L] in
theorem dividedDiff_one_auxVar_one_cube :
    dividedDiff 1 ((auxVar 1 : Total L) ^ 3)
      = -((auxVar 1 : Total L) ^ 2 + auxVar 1 * auxVar 2 + (auxVar 2 : Total L) ^ 2) := by
  refine dividedDiff_one_eq ?_
  rw [map_pow, swapAux_one_auxVar_one]
  ring

omit [Algebra ℚ L] in
theorem dividedDiff_one_auxVar_one_sq_mul_two :
    dividedDiff 1 ((auxVar 1 : Total L) ^ 2 * auxVar 2) = -((auxVar 1 : Total L) * auxVar 2) := by
  refine dividedDiff_one_eq ?_
  rw [map_mul, map_pow, swapAux_one_auxVar_one, swapAux_one_auxVar_two]
  ring

omit [Algebra ℚ L] in
/-- `T_i^{-1}` as an `L`-linear map, read off `HJO.Sweep.braidInv_apply`. -/
theorem braidInvEnd_apply' (q : L) (i : ℕ) (F : Total L) :
    braidInvEnd q i F = scal q⁻¹ * (braidEnd q i F + scal (q - 1) * F) := by
  rw [braidInvEnd, LinearMap.restrictScalars_apply, braidInv_apply, braidEnd,
    LinearMap.restrictScalars_apply]

omit [Algebra ℚ L] in
/-- `T_i^{-1}` is `Λ`-linear. -/
theorem braidInvEnd_C_mul (q : L) (i : ℕ) (f : Sym.Lambda L) (F : Total L) :
    braidInvEnd q i (MvPolynomial.C f * F) = MvPolynomial.C f * braidInvEnd q i F := by
  have h := (braidInv q i).map_smul f F
  rw [braidInvEnd, LinearMap.restrictScalars_apply, LinearMap.restrictScalars_apply]
  simpa [MvPolynomial.smul_eq_C_mul] using h

omit [Algebra ℚ L] in
theorem braidInvEnd_scal_mul (q : L) (i : ℕ) (x : L) (F : Total L) :
    braidInvEnd q i (scal x * F) = scal x * braidInvEnd q i F :=
  braidInvEnd_C_mul q i _ F

omit [Algebra ℚ L] in
/-- **`T_1^{-1}(y_1^2) = q^{-1}(y_2^2 - (q-1)y_1y_2)`.** -/
theorem braidInvEnd_one_auxVar_one_sq (q : L) :
    braidInvEnd q 1 ((auxVar 1 : Total L) ^ 2)
      = scal q⁻¹ * ((auxVar 2 : Total L) ^ 2
          - scal (q - 1) * ((auxVar 1 : Total L) * auxVar 2)) := by
  rw [braidInvEnd_apply', braidEnd_apply', map_pow, swapAux_one_auxVar_one,
    dividedDiff_one_auxVar_one_sq]
  ring

omit [Algebra ℚ L] in
/-- **`T_1^{-1}(y_1^3) = q^{-1}(y_2^3 - (q-1)(y_1^2y_2 + y_1y_2^2))`.** -/
theorem braidInvEnd_one_auxVar_one_cube (q : L) :
    braidInvEnd q 1 ((auxVar 1 : Total L) ^ 3)
      = scal q⁻¹ * ((auxVar 2 : Total L) ^ 3
          - scal (q - 1) * ((auxVar 1 : Total L) ^ 2 * auxVar 2
            + (auxVar 1 : Total L) * (auxVar 2 : Total L) ^ 2)) := by
  rw [braidInvEnd_apply', braidEnd_apply', map_pow, swapAux_one_auxVar_one,
    dividedDiff_one_auxVar_one_cube]
  ring

omit [Algebra ℚ L] in
/-- **`T_1^{-1}(y_1^2y_2) = q^{-1}y_1y_2^2`**: here the `(q-1)` of the braid operator cancels
against the `(q-1)` of the inverse and a single monomial survives. -/
theorem braidInvEnd_one_auxVar_one_sq_mul_two (q : L) :
    braidInvEnd q 1 ((auxVar 1 : Total L) ^ 2 * auxVar 2)
      = scal q⁻¹ * ((auxVar 1 : Total L) * (auxVar 2 : Total L) ^ 2) := by
  rw [braidInvEnd_apply', braidEnd_apply', map_mul, map_pow, swapAux_one_auxVar_one,
    swapAux_one_auxVar_two, dividedDiff_one_auxVar_one_sq_mul_two]
  ring

/-! ### The defect `z_1` measures, evaluated -/

/-- **The quantity `z_1` measures**: the failure of the Hall--Littlewood operator `B_n` to commute
with the one-letter displacement `d^*_+{}^{(0)}`, on the coefficient `A`. This is the bracket of
`HJO.Sweep.zCommTwo_monomial` and of `HJO.Sweep.zopOneStar_one_auxVar_pow_mul_C`: one and the same
element of `V_1` reads `z_1` at both gradings. -/
noncomputable def zDefect (q u : L) (n : ℕ) (A : Sym.Lambda L) : Total L :=
  dplusStar q u 0 (MvPolynomial.C (Sym.Bop q (n : ℤ) A))
    - bopExt q (n : ℤ) (dplusStar q u 0 (MvPolynomial.C A))

/-- `HJO.Sweep.zCommTwo_monomial` in terms of `HJO.Sweep.zDefect`. -/
theorem zCommTwo_monomial' (q u : L) (m n : ℕ) (A : Sym.Lambda L) :
    zCommTwo q u (MvPolynomial.C A * ((auxVar 1 : Total L) ^ m * (auxVar 2 : Total L) ^ n))
      = (auxVar 2 : Total L) ^ m * zDefect q u n A :=
  zCommTwo_monomial q u m n A

theorem zDefect_smul (q u : L) (n : ℕ) (c : L) (A : Sym.Lambda L) :
    zDefect q u n (c • A) = c • zDefect q u n A := by
  rw [zDefect, zDefect, map_smul, C_smul, C_smul, map_smul, map_smul, map_smul, smul_sub]

theorem dplusStar_zero_one (q u : L) : dplusStar q u 0 (1 : Total L) = 1 := by
  rw [← dplusStarAlg_eq_dplusStar, map_one]

theorem bopExt_one' (q : L) (r : ℤ) :
    bopExt q r (1 : Total L) = MvPolynomial.C (Sym.Bop q r (1 : Sym.Lambda L)) := by
  rw [show (1 : Total L) = MvPolynomial.C (1 : Sym.Lambda L) from (map_one _).symm, bopExt_C]

/-- **The defect on the vacuum coefficient**: `B_n(1) = (-1)^ne_n` and `d^*_+` fixes `1`, so the
whole defect is `(-1)^n` times the displacement of `e_n`. -/
theorem zDefect_one (q u : L) (n : ℕ) :
    zDefect q u n (1 : Sym.Lambda L)
      = ((-1 : L) ^ n) • (dplusStar q u 0 (MvPolynomial.C (Sym.elemSymm L n))
          - MvPolynomial.C (Sym.elemSymm L n)) := by
  have hb : Sym.Bop q ((n : ℕ) : ℤ) (1 : Sym.Lambda L) = ((-1 : L) ^ n) • Sym.elemSymm L n := by
    rw [Sym.bop_one, Sym.elemSymmAlt_natCast, MvPolynomial.smul_eq_C_mul, map_pow, map_neg,
      map_one]
  rw [zDefect, MvPolynomial.C_1, dplusStar_zero_one, bopExt_one', hb, C_smul, map_smul, smul_sub]

theorem zDefect_one_one (q u : L) :
    zDefect q u 1 (1 : Sym.Lambda L) = -(scal ((q - 1) * u) * (auxVar 1 : Total L)) := by
  rw [zDefect_one, dplusStar_C_elemSymm_one, starLetter, ← scal_mul_eq_smul_total]
  simp only [scal, map_mul, map_sub, map_neg, map_one, map_pow]
  ring

theorem zDefect_two_one (q u : L) :
    zDefect q u 2 (1 : Sym.Lambda L)
      = scal ((q - 1) * u) * ((auxVar 1 : Total L) * MvPolynomial.C (Sym.elemSymm L 1))
        - scal ((q - 1) * u ^ 2) * (auxVar 1 : Total L) ^ 2 := by
  rw [zDefect_one, dplusStar_C_elemSymm_two, starLetter, ← scal_mul_eq_smul_total]
  simp only [scal, map_mul, map_sub, map_neg, map_one, map_pow]
  ring

theorem zDefect_three_one (q u : L) :
    zDefect q u 3 (1 : Sym.Lambda L)
      = -(scal ((q - 1) * u) * ((auxVar 1 : Total L) * MvPolynomial.C (Sym.elemSymm L 2)))
        + scal ((q - 1) * u ^ 2)
            * ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (Sym.elemSymm L 1))
        - scal ((q - 1) * u ^ 3) * (auxVar 1 : Total L) ^ 3 := by
  rw [zDefect_one, dplusStar_C_elemSymm_three, starLetter, ← scal_mul_eq_smul_total]
  simp only [scal, map_mul, map_sub, map_neg, map_one, map_pow]
  ring

/-- The second half of the defect at `A = e_1`: `B_n` applied coefficientwise to
`d^*_+{}^{(0)}(Ce_1) = Ce_1 + (q-1)uy_1`. -/
theorem bopExt_dplusStar_zero_C_elemSymm_one (q u : L) (n : ℕ) :
    bopExt q ((n : ℕ) : ℤ) (dplusStar q u 0 (MvPolynomial.C (Sym.elemSymm L 1) : Total L))
      = MvPolynomial.C (Sym.Bop q ((n : ℕ) : ℤ) (Sym.elemSymm L 1))
        + scal ((q - 1) * u) * ((auxVar 1 : Total L)
            * MvPolynomial.C (Sym.Bop q ((n : ℕ) : ℤ) (1 : Sym.Lambda L))) := by
  have hZ : (scal ((q - 1) * u) * (auxVar 1 : Total L)) ∈ auxSubalg L :=
    mul_mem (scal_mem_auxSubalg _) (auxVar_mem_auxSubalg 1)
  rw [dplusStar_C_elemSymm_one, starLetter, map_add, bopExt_C,
    show (scal (q - 1) : Total L) * (scal u * auxVar 1)
      = (scal ((q - 1) * u) * (auxVar 1 : Total L)) * 1 from by rw [mul_one, scal_mul]; ring,
    bopExt_auxSubalg_mul q _ hZ, bopExt_one']
  ring

/-- **`z_1`'s defect at `n = 1` on `e_1` is a single monomial**: the `y_1^2` terms cancel
identically and what survives is `-q(q-1)u·y_1e_1`. -/
theorem zDefect_one_elemSymm_one (q u : L) :
    zDefect q u 1 (Sym.elemSymm L 1)
      = -(scal (q * (q - 1) * u)
          * ((auxVar 1 : Total L) * MvPolynomial.C (Sym.elemSymm L 1))) := by
  have hb1 : Sym.Bop q ((1 : ℕ) : ℤ) (Sym.elemSymm L 1)
      = -(Sym.elemSymm L 1 * Sym.elemSymm L 1) + (1 - q) • Sym.elemSymm L 2 := by
    rw [MvPolynomial.smul_eq_C_mul]
    simpa using Sym.bop_one_elemSymm_one q
  have hb0 : Sym.Bop q ((1 : ℕ) : ℤ) (1 : Sym.Lambda L) = -Sym.elemSymm L 1 := by
    rw [Sym.bop_one, Sym.elemSymmAlt_natCast]; simp
  rw [zDefect, bopExt_dplusStar_zero_C_elemSymm_one, hb1, hb0, map_add, map_neg, map_mul, C_smul,
    map_add, map_neg, map_smul, dplusStar_mul, dplusStar_C_elemSymm_one,
    dplusStar_C_elemSymm_two, starLetter, map_neg]
  simp only [← scal_mul_eq_smul_total]
  simp only [scal, map_mul, map_sub, map_one]
  ring

/-- **`z_1`'s defect at `n = 2` on `e_1`**: the `y_1^3` terms cancel identically, and `e_3` — which
both halves carry — cancels with them. -/
theorem zDefect_two_elemSymm_one (q u : L) :
    zDefect q u 2 (Sym.elemSymm L 1)
      = scal ((q - 1) * u)
            * ((auxVar 1 : Total L) * (MvPolynomial.C (Sym.elemSymm L 1)
              * MvPolynomial.C (Sym.elemSymm L 1)))
        + scal ((q - 1) ^ 2 * u)
            * ((auxVar 1 : Total L) * MvPolynomial.C (Sym.elemSymm L 2))
        - scal ((q - 1) * u ^ 2)
            * ((auxVar 1 : Total L) ^ 2 * MvPolynomial.C (Sym.elemSymm L 1)) := by
  have hb1 : Sym.Bop q ((2 : ℕ) : ℤ) (Sym.elemSymm L 1)
      = Sym.elemSymm L 1 * Sym.elemSymm L 2 - (1 - q) • Sym.elemSymm L 3 := by
    rw [MvPolynomial.smul_eq_C_mul]
    exact Sym.bop_two_elemSymm_one q
  have hb0 : Sym.Bop q ((2 : ℕ) : ℤ) (1 : Sym.Lambda L) = Sym.elemSymm L 2 := by
    rw [Sym.bop_one, Sym.elemSymmAlt_natCast]; simp
  rw [zDefect, bopExt_dplusStar_zero_C_elemSymm_one, hb1, hb0, map_sub, map_mul, C_smul,
    map_sub, map_smul, dplusStar_mul, dplusStar_C_elemSymm_one,
    dplusStar_C_elemSymm_two, dplusStar_C_elemSymm_three, starLetter]
  simp only [← scal_mul_eq_smul_total]
  simp only [scal, map_mul, map_sub, map_one, map_pow]
  ring

end HJO.Sweep

end
