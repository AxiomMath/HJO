/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.MellitLevelRaiseTwoThree
public import HJO.Shuffle.MellitLhsCompInduction

/-! # The two-part clause at `(a,b) = (2,3)`: the sweep side, computed

`HJO.Mellit.qop_double_apply_one_of_lhsWord` reads the clause of
`HJO.Mellit.lhsRewrite_sweepWitness` at the composition `α = (1,1)` as one identity in `Λ`,

`(u+1)·Q_{a,b}(Q_{a,b}1) + u(q-1)·Q_{2a,2b}(1) = (qu+1)·ct(d_-^2G_{2,1}G_{1,1}(1))`.

This file computes the **right-hand side** at `(a,b) = (2,3)` outright, eliminating every sweep
operator and leaving a `Λ`-side expression in Hall--Littlewood operators.

## The seed

`HJO.Sweep.stageTotal_two_three_zero_one_one`: `G_{1,1}(1) = -e_1y_1^2 + uy_1^3`.

The stage at one part carries no `Z` factor (`HJO.Sweep.stageTotal_one_apply`), the descending
train `T_{1↘1}` is empty, and `HJO.Sweep.slopeOperator_two_odd` reads
`Ξ^{(1)}_{2,3} = (-y_1)(qu)^{-1}z_1^{(1)}(-y_1)` — so the seed is `(qu)^{-1}y_1z_1^{(1)}(y_1^2)`,
and `HJO.Sweep.zopOneStar_one_auxVar_sq'` evaluates the single `z`.

The consistency check is `HJO.Sweep.dminus_one_stageTotal_two_three_zero_one_one`: `d_-^{(1)}` of
the seed is the value of `HJO.Sym.qop_two_three_apply_one`, `Q_{2,3}(1) = -e_1e_2 + (1-q-u)e_3`.
That is the clause at the *one*-part composition recovered from the seed, and it is what pins the
sign conventions of the assembly.

## Genericity

`q ≠ 0`, `u ≠ 0`, `q ≠ 1` and nothing else, and all three are the inverse-becomes-zero hazard
rather than bookkeeping: at `q = 0` and at `u = 0` the letter `(qu)^{-1}z_1` of
`HJO.Sweep.slopeOperator` is the **zero map**, at `q = 1` the scalar `q^2/(1-q)` of `HJO.Sweep.zop`
is `0` and `z_1` is the zero map, and `q = 0` is needed again by `T_1^{-1} = (T_1+(q-1))/q`. At each
the sweep side genuinely collapses, so a clause asserting otherwise there is *false*, not vacuous.
Not needed: `M ≠ 0`, `qu ≠ 1`, `u ≠ 1`, `∀ r, IsUnit (q^{r+1}-1)`.

## What this file does not do

This is the `Λ`-side value of **one** side of **one** instance (`α = (1,1)`, `(a,b) = (2,3)`) of the
`hlhs` binder of `HJO.Mellit.shuffle_of_lhs_and_induction`, which quantifies over all coprime
`1 < a < b` and every composition. This file discharges neither binder of that theorem, `hlhs` or
`hind`.

## References

The definitions and results this file concerns: `HJO.Mellit.stage`, `HJO.Sweep.slopeOperator`,
`HJO.Sweep.zop`, `HJO.Sym.Bop`, `HJO.Mellit.lhsRewrite_sweepWitness` and
`HJO.Sweep.dminus_dminus_braid`.
-/

@[expose] public section

namespace HJO.Sweep

open HJO.Sym

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-! ### `z_1` on `y_1^2`, with the scalar cancelled -/

/-- **`z_1^{(1)}(y_1^2) = -qu·y_1e_1 + qu^2·y_1^2`.** `HJO.Sweep.zopOneStar_one_auxVar_sq'` reads
the single `z` letter as `q/(1-q)` times the displacement defect of `e_2`, which
`HJO.Sweep.dplusStar_C_elemSymm_two_sub` evaluates; the two occurrences of `1-q` cancel, which is
the only place `q ≠ 1` is spent. -/
theorem zopOneStar_one_auxVar_sq_eval (hq1 : q ≠ 1) :
    zopOneStar q u 1 ((auxVar 1 : Total L) ^ 2)
      = (-(q * u)) • ((auxVar 1 : Total L) * MvPolynomial.C (elemSymm L 1))
        + (q * u ^ 2) • (auxVar 1 : Total L) ^ 2 := by
  have h1q : (1 : L) - q ≠ 0 := sub_ne_zero.2 (Ne.symm hq1)
  have s1 : q / (1 - q) * ((q - 1) * u) = -(q * u) := by field_simp; ring
  have s2 : q / (1 - q) * ((1 - q) * u ^ 2) = q * u ^ 2 := by field_simp
  rw [zopOneStar_one_auxVar_sq', dplusStar_C_elemSymm_two_sub, mul_assoc,
    scal_mul_eq_smul_total, scal_mul_eq_smul_total, smul_add, smul_smul, smul_smul, s1, s2]

/-! ### The seed of the two-part stage word -/

/-- **`G_{1,1}(1) = -e_1y_1^2 + uy_1^3`** at `(a,b) = (2,3)`, the element of `V_1` the two-part
stage word is built on. See the module docstring. -/
@[hjo "lem_mellit_lhs_two_three_seed"]
theorem stageTotal_two_three_zero_one_one (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    Mellit.stageTotal q u 2 3 0 1 (1 : Total L)
      = -(MvPolynomial.C (elemSymm L 1) * (auxVar 1 : Total L) ^ 2)
        + u • (auxVar 1 : Total L) ^ 3 := by
  have hqu : q * u ≠ 0 := mul_ne_zero hq0 hu0
  have s3 : (q * u)⁻¹ * (-(q * u)) = -1 := by field_simp
  have s4 : (q * u)⁻¹ * (q * u ^ 2) = u := by field_simp
  have htrain : trainDownEnd q 1 1 = (1 : Module.End L (Total L)) :=
    Braid.trainDown_self _ _ 1
  have hslope : slopeOperator q u 1 2 3
      = (-LinearMap.mulLeft L (auxVar 1 : Total L)) ^ 1
        * ((q * u)⁻¹ • zopOneStar q u 1)
        * (-LinearMap.mulLeft L (auxVar 1 : Total L)) ^ 1 := by
    simpa using slopeOperator_two_odd q u 1 1
  rw [stageTotal_one_apply, htrain, Nat.zero_add, dplusStar_zero_one, mul_one, hslope]
  simp only [pow_one, Module.End.mul_apply, LinearMap.smul_apply, LinearMap.neg_apply,
    LinearMap.mulLeft_apply, Module.End.one_apply, mul_neg, neg_neg, map_neg, map_smul,
    smul_neg]
  rw [show (auxVar 1 : Total L) * (auxVar 1 : Total L) = (auxVar 1 : Total L) ^ 2 from
    (pow_two _).symm, zopOneStar_one_auxVar_sq_eval hq1,
    show ((-1 : L) ^ (2 - 1)) = -1 from by norm_num]
  rw [mul_add, mul_smul_comm, mul_smul_comm, smul_add, smul_smul, smul_smul, s3, s4]
  rw [show (auxVar 1 : Total L) * ((auxVar 1 : Total L) * MvPolynomial.C (elemSymm L 1))
      = MvPolynomial.C (elemSymm L 1) * (auxVar 1 : Total L) ^ 2 from by ring,
    show (auxVar 1 : Total L) * (auxVar 1 : Total L) ^ 2 = (auxVar 1 : Total L) ^ 3 from by ring]
  module

/-! ### The consistency check: one lowering of the seed is `Q_{2,3}(1)` -/

/-- **`d_-^{(1)}(G_{1,1}(1)) = Q_{2,3}(1)`.** The seed's two `y_1`-coefficients are read by
`B_2` and `B_3`: `B_2(e_1) = e_1e_2 - (1-q)e_3` and `B_3(1) = -e_3`, and the two `e_3` terms combine
to the `(1-q-u)e_3` of `HJO.Sym.qop_two_three_apply_one`.

This is the clause at the **one**-part composition, recovered from the seed rather than assumed, and
it is what certifies the sign conventions of the assembly in
`HJO.Sweep.stageTotal_two_three_zero_one_one`: a sign slip anywhere in the slope word, the
descending train or `(-1)^{a-1}` would break it. -/
@[hjo "lem_mellit_lhs_two_three_seed"]
theorem dminus_one_stageTotal_two_three_zero_one_one (hM : (1 - q) * (1 - u) ≠ 0) (hq0 : q ≠ 0)
    (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    dminus q 1 (Mellit.stageTotal q u 2 3 0 1 (1 : Total L))
      = MvPolynomial.C (Qop q u 2 3 (1 : Lambda L)) := by
  have hb2 : Bop q ((2 : ℕ) : ℤ) (elemSymm L 1)
      = elemSymm L 1 * elemSymm L 2 - (1 - q) • elemSymm L 3 := by
    rw [MvPolynomial.smul_eq_C_mul]; exact bop_two_elemSymm_one q
  have hb3 : Bop q ((3 : ℕ) : ℤ) (1 : Lambda L) = -elemSymm L 3 := by
    rw [bop_natCast_one]; norm_num
  rw [stageTotal_two_three_zero_one_one hq0 hu0 hq1, map_add, map_neg, map_smul,
    show (MvPolynomial.C (elemSymm L 1) : Total L) * (auxVar 1 : Total L) ^ 2
      = (auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 1) from by ring,
    show ((auxVar 1 : Total L) ^ 3) = (auxVar 1 : Total L) ^ 3 * MvPolynomial.C (1 : Lambda L) from
      by rw [MvPolynomial.C_1, mul_one],
    dminus_one_auxVar_pow_mul_C, dminus_one_auxVar_pow_mul_C, hb2, hb3,
    qop_two_three_apply_one hM]
  simp only [← scal_mul_eq_smul_total, scal, MvPolynomial.smul_eq_C_mul, map_sub, map_add,
    map_neg, map_mul, map_one]
  ring

/-! ### The two-part stage word -/

/-- **`G_{2,1}G_{1,1}(1)` is the stage word at `α = (1,1)`.** One step of
`HJO.Mellit.stageWordTotal_append`; unconditional. -/
theorem stageWordTotal_one_one (q u : L) (a b : ℕ) :
    Mellit.stageWordTotal q u a b [1, 1]
      = Mellit.stageTotal q u a b 1 1 (Mellit.stageTotal q u a b 0 1 (1 : Total L)) := by
  have hone : Mellit.stageWordTotal q u a b [1] = Mellit.stageTotal q u a b 0 1 (1 : Total L) := by
    rw [Mellit.stageWordTotal, Mellit.stageFromTotal, Mellit.stageFromTotal]
  have h := Mellit.stageWordTotal_append q u a b [1] 1
  rw [show ([1] ++ [1] : List ℕ) = [1, 1] from rfl, List.length_cons, List.length_nil,
    Nat.zero_add, hone] at h
  exact h

/-! ### The braid letter drops out at a general input of `V_1` -/

/-- **The level-raising composite at `A = 1`, with no braid letter left, at a general input.** The
generalisation of `HJO.Sweep.lowerRun_two_stageTotal_levelKernelOne_of_slope` off the kernel
witness: for every `G ∈ V_1` and every `(a,b)`,

`d_-^2G_{2,1}(G) = (-1)^{a-1}d_-^2(Ξ^{(2)}_{a,b}(-y_1d^*_+{}^{(1)}G))`.

The `T_1 = T_{2↘1}` of `HJO.Sweep.stageTotal_one_apply` is killed by
`HJO.Sweep.dminus_dminus_braid`, whose hypothesis comes from `HJO.Sweep.slopeOperator_mem_piece`
and `HJO.Sweep.dplusStar_mem_piece`. Unconditional. -/
theorem lowerRun_two_stageTotal_one_of_slope (q u : L) (a b : ℕ) {G : Total L}
    (hG : G ∈ piece L 1) :
    Mellit.lowerRun q 2 (Mellit.stageTotal q u a b 1 1 G)
      = ((-1 : L) ^ (a - 1)) •
          Mellit.lowerRun q 2
            (slopeOperator q u 2 a b (-((auxVar 1 : Total L) * dplusStar q u 1 G))) := by
  have harg : (-((auxVar 1 : Total L) * dplusStar q u 1 G)) ∈ piece L 2 :=
    neg_mem (mul_mem (auxVar_mem_piece le_rfl (by omega)) (dplusStar_mem_piece q u hG))
  have hmem : slopeOperator q u 2 a b (-((auxVar 1 : Total L) * dplusStar q u 1 G)) ∈ piece L 2 :=
    slopeOperator_mem_piece q u (by omega) harg
  rw [stageTotal_one_apply, show (1 : ℕ) + 1 = 2 from rfl, trainDownEnd_two_one, map_smul,
    lowerRun_two_apply, lowerRun_two_apply]
  refine congrArg (fun x => ((-1 : L) ^ (a - 1)) • x) ?_
  rw [show braidEnd q 1 (slopeOperator q u 2 a b (-((auxVar 1 : Total L) * dplusStar q u 1 G)))
      = braid q 1 (slopeOperator q u 2 a b (-((auxVar 1 : Total L) * dplusStar q u 1 G))) from rfl]
  exact dminus_dminus_braid q 0 hmem

/-! ### The vector the slope operator is read on -/

/-- **The argument of `Ξ^{(2)}_{2,3}` in the two-part stage word**, `-y_1d^*_+{}^{(1)}(G_{1,1}(1))`:

`e_1y_1y_2^2 + (q-1)uy_1^2y_2^2 - uy_1y_2^3`.

The analogue of `HJO.Sweep.slopeArgTwo` with the kernel witness replaced by the actual seed. Both
have three monomials, but of degree four rather than two, and the `y_2`-degrees are higher: that is
what makes the train act differently. -/
noncomputable def seedArgTwo (q u : L) : Total L :=
  MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) * (auxVar 2 : Total L) ^ 2)
    + scal ((q - 1) * u) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2)
    - u • ((auxVar 1 : Total L) * (auxVar 2 : Total L) ^ 3)

theorem seedArgTwo_mem_piece (q u : L) : seedArgTwo q u ∈ piece L 2 := by
  have h1 : (auxVar 1 : Total L) ∈ piece L 2 := auxVar_mem_piece le_rfl (by omega)
  have h2 : (auxVar 2 : Total L) ∈ piece L 2 := auxVar_mem_piece (by omega) le_rfl
  rw [seedArgTwo, ← scal_mul_eq_smul_total]
  exact sub_mem (add_mem (mul_mem (C_mem_piece _ _) (mul_mem h1 (pow_mem h2 2)))
      (mul_mem (scal_mem_piece _ _) (mul_mem (pow_mem h1 2) (pow_mem h2 2))))
    (mul_mem (scal_mem_piece _ _) (mul_mem h1 (pow_mem h2 3)))

/-- **`-y_1d^*_+{}^{(1)}(G_{1,1}(1)) = seedArgTwo`.** The level-`1` displacement raises the index of
the multiplier (`HJO.Sweep.dplusStar_one_auxVar_pow_mul_C`) and acts on the two `y_1`-coefficients
of the seed by `HJO.Sweep.dplusStar_C_elemSymm_one`; the constant coefficient `u` is fixed. -/
theorem neg_auxVar_one_mul_dplusStar_one_stageTotal (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    -((auxVar 1 : Total L) * dplusStar q u 1 (Mellit.stageTotal q u 2 3 0 1 (1 : Total L)))
      = seedArgTwo q u := by
  have hone : (auxVar 1 : Total L) ^ 3 = (auxVar 1 : Total L) ^ 3 * MvPolynomial.C (1 : Lambda L) :=
    by rw [MvPolynomial.C_1, mul_one]
  rw [stageTotal_two_three_zero_one_one hq0 hu0 hq1,
    show -(MvPolynomial.C (elemSymm L 1) * (auxVar 1 : Total L) ^ 2)
      = (auxVar 1 : Total L) ^ 2 * MvPolynomial.C (-(elemSymm L 1)) from by
      rw [MvPolynomial.C_neg]; ring,
    map_add, map_smul, hone, dplusStar_one_auxVar_pow_mul_C, dplusStar_one_auxVar_pow_mul_C,
    MvPolynomial.C_neg, map_neg, dplusStar_C_elemSymm_one, MvPolynomial.C_1, dplusStar_zero_one,
    starLetter, seedArgTwo]
  simp only [← scal_mul_eq_smul_total, scal_mul]
  ring

/-! ### `T_1^{-1}` on the three monomials of the argument -/

omit [Algebra ℚ L] in
private theorem divDiffOne {F G : Total L}
    (h : ((auxVar 2 : Total L) - auxVar 1) * G = F - swapAux L 1 F) :
    dividedDiff 1 F = G :=
  (dividedDiff_unique (i := 1) le_rfl (by
    rw [show (MvPolynomial.X 1 - MvPolynomial.X (1 - 1) : Total L)
        = (auxVar 2 : Total L) - auxVar 1 from rfl]
    exact h)).symm

omit [Algebra ℚ L] in
/-- **`T_1^{-1}(y_1^2y_2^2) = y_1^2y_2^2`.** The monomial is symmetric, so the braid operator is the
identity on it and `T_1^{-1}` multiplies by `q^{-1}(1 + (q-1)) = 1`. This is where `q ≠ 0` enters
the train. -/
theorem braidInvEnd_one_sq_sq (hq0 : q ≠ 0) :
    braidInvEnd q 1 ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2)
      = (auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2 := by
  have hdd : dividedDiff 1 ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2) = 0 := by
    refine divDiffOne ?_
    rw [map_mul, map_pow, map_pow, swapAux_one_auxVar_one, swapAux_one_auxVar_two]
    ring
  rw [braidInvEnd_apply', braidEnd_apply', map_mul, map_pow, map_pow, swapAux_one_auxVar_one,
    swapAux_one_auxVar_two, hdd]
  rw [show (scal (q - 1) : Total L) * (auxVar 1 : Total L) * 0 = 0 from by ring, add_zero,
    show ((auxVar 2 : Total L) ^ 2 * (auxVar 1 : Total L) ^ 2
        + (scal (q - 1) : Total L) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2))
      = scal q * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2) from by
      rw [show (scal q : Total L) = scal (q - 1) + 1 from by rw [scal_sub, scal_one]; ring]; ring,
    ← mul_assoc, ← scal_mul, inv_mul_cancel₀ hq0, scal_one, one_mul]

omit [Algebra ℚ L] in
/-- **`T_1^{-1}(y_1^3y_2^2) = q^{-1}y_1^2y_2^3`.** The `(q-1)` of the braid operator cancels against
the `(q-1)` of the inverse and a single monomial survives; no hypothesis on `q`. -/
theorem braidInvEnd_one_cube_sq (q : L) :
    braidInvEnd q 1 ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2)
      = scal q⁻¹ * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3) := by
  have hdd : dividedDiff 1 ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2)
      = -((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2) := by
    refine divDiffOne ?_
    rw [map_mul, map_pow, map_pow, swapAux_one_auxVar_one, swapAux_one_auxVar_two]
    ring
  rw [braidInvEnd_apply', braidEnd_apply', map_mul, map_pow, map_pow, swapAux_one_auxVar_one,
    swapAux_one_auxVar_two, hdd]
  ring

omit [Algebra ℚ L] in
/-- **`T_1^{-1}(y_1^2y_2^3) = y_1^3y_2^2 + q^{-1}(q-1)y_1^2y_2^3`.** -/
theorem braidInvEnd_one_sq_cube (hq0 : q ≠ 0) :
    braidInvEnd q 1 ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3)
      = (auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2
        + scal (q⁻¹ * (q - 1)) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3) := by
  have hdd : dividedDiff 1 ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3)
      = (auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2 := by
    refine divDiffOne ?_
    rw [map_mul, map_pow, map_pow, swapAux_one_auxVar_one, swapAux_one_auxVar_two]
    ring
  have hq : (scal q⁻¹ : Total L) * scal q = 1 := by
    rw [← scal_mul, inv_mul_cancel₀ hq0, scal_one]
  rw [braidInvEnd_apply', braidEnd_apply', map_mul, map_pow, map_pow, swapAux_one_auxVar_one,
    swapAux_one_auxVar_two, hdd,
    show ((auxVar 2 : Total L) ^ 2 * (auxVar 1 : Total L) ^ 3
          + (scal (q - 1) : Total L) * (auxVar 1 : Total L)
            * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2)
          + (scal (q - 1) : Total L) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3))
      = scal q * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2)
          + (scal (q - 1) : Total L) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3) from by
      rw [show (scal q : Total L) = scal (q - 1) + 1 from by rw [scal_sub, scal_one]; ring]; ring,
    mul_add, ← mul_assoc, hq, one_mul, ← mul_assoc, ← scal_mul]

/-- **`T_1^{-1}` on the whole argument: three monomials become two.** The two `y_1^2y_2^3` terms
— one from `T_1^{-1}(y_1^3y_2^2)` and one from `T_1^{-1}(y_1^2y_2^3)` — cancel **identically**,
which is the structural difference from the kernel witness, where three monomials become five
(`HJO.Sweep.braidInvEnd_one_neg_auxVar_one_mul_slopeArgTwo`). -/
theorem braidInvEnd_one_neg_auxVar_one_mul_seedArgTwo (hq0 : q ≠ 0) :
    braidInvEnd q 1 (-((auxVar 1 : Total L) * seedArgTwo q u))
      = -(MvPolynomial.C (elemSymm L 1)
            * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2))
        + u • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2) := by
  have hexp : -((auxVar 1 : Total L) * seedArgTwo q u)
      = MvPolynomial.C (-(elemSymm L 1))
            * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2)
        + scal (-((q - 1) * u)) * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2)
        + scal u * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3) := by
    rw [seedArgTwo, MvPolynomial.C_neg, ← scal_mul_eq_smul_total, scal_neg]
    ring
  rw [hexp, map_add, map_add, braidInvEnd_C_mul, braidInvEnd_scal_mul, braidInvEnd_scal_mul,
    braidInvEnd_one_sq_sq hq0, braidInvEnd_one_cube_sq, braidInvEnd_one_sq_cube hq0,
    MvPolynomial.C_neg, ← scal_mul_eq_smul_total]
  rw [show (scal (-((q - 1) * u)) : Total L)
        * (scal q⁻¹ * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3))
      = scal (-((q - 1) * u) * q⁻¹) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3) from by
      rw [← mul_assoc, ← scal_mul],
    show (scal u : Total L) * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2
        + scal (q⁻¹ * (q - 1)) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3))
      = scal u * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2)
        + scal (u * (q⁻¹ * (q - 1)))
            * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3) from by
      rw [mul_add, ← mul_assoc (scal u : Total L) (scal (q⁻¹ * (q - 1)) : Total L),
        ← scal_mul],
    show (-((q - 1) * u) * q⁻¹) = -(u * (q⁻¹ * (q - 1))) from by ring, scal_neg]
  ring

/-! ### The composite, as five compositions of Hall--Littlewood operators -/

/-- **The sweep side of the two-part clause, with every sweep operator discharged.** What is left is
a `Λ`-side expression `∑ c·B_jB_m(g)` with `j` the `y_1`-exponent and `m` the `y_2`-exponent of the
monomial it came from — **five** compositions, against the seven of the kernel witness
(`HJO.Sweep.constantCoeff_lowerRun_two_auxVar_one_mul_zCommTwo`), because the train's two
`y_1^2y_2^3` terms cancelled.

`q ≠ 0` is the train's, and nothing else is spent here. -/
theorem constantCoeff_lowerRun_two_auxVar_one_mul_zCommTwo_seedArgTwo (hq0 : q ≠ 0) :
    MvPolynomial.constantCoeff (Mellit.lowerRun q 2 ((auxVar 1 : Total L)
        * zCommTwo q u (braidInvEnd q 1 (-((auxVar 1 : Total L) * seedArgTwo q u)))))
      = (-((q - 1) * u)) •
          (Bop q ((2 : ℕ) : ℤ) (Bop q ((2 : ℕ) : ℤ) (elemSymm L 1 * elemSymm L 1))
            + (q - 1) • Bop q ((2 : ℕ) : ℤ) (Bop q ((2 : ℕ) : ℤ) (elemSymm L 2))
            - u • Bop q ((3 : ℕ) : ℤ) (Bop q ((2 : ℕ) : ℤ) (elemSymm L 1))
            - u • Bop q ((2 : ℕ) : ℤ) (Bop q ((3 : ℕ) : ℤ) (elemSymm L 1))
            + u ^ 2 • Bop q ((3 : ℕ) : ℤ) (Bop q ((3 : ℕ) : ℤ) (1 : Lambda L))) := by
  have hz : zCommTwo q u (braidInvEnd q 1 (-((auxVar 1 : Total L) * seedArgTwo q u)))
      = -((auxVar 2 : Total L) ^ 2 * zDefect q u 2 (elemSymm L 1))
        + u • ((auxVar 2 : Total L) ^ 3 * zDefect q u 2 (1 : Lambda L)) := by
    rw [braidInvEnd_one_neg_auxVar_one_mul_seedArgTwo hq0,
      show ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2)
        = MvPolynomial.C (1 : Lambda L) * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2) from
        by rw [MvPolynomial.C_1, one_mul],
      map_add, map_neg, map_smul, zCommTwo_monomial', zCommTwo_monomial']
  have hexp : (auxVar 1 : Total L) *
        (-((auxVar 2 : Total L) ^ 2 * zDefect q u 2 (elemSymm L 1))
          + u • ((auxVar 2 : Total L) ^ 3 * zDefect q u 2 (1 : Lambda L)))
      = (-((q - 1) * u)) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2
            * MvPolynomial.C (elemSymm L 1 * elemSymm L 1))
        + (-((q - 1) ^ 2 * u)) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2
            * MvPolynomial.C (elemSymm L 2))
        + ((q - 1) * u ^ 2) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2
            * MvPolynomial.C (elemSymm L 1))
        + ((q - 1) * u ^ 2) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3
            * MvPolynomial.C (elemSymm L 1))
        + (-((q - 1) * u ^ 3)) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 3
            * MvPolynomial.C (1 : Lambda L)) := by
    rw [zDefect_two_elemSymm_one, zDefect_two_one]
    simp only [← scal_mul_eq_smul_total, scal, map_mul, map_sub, map_neg, map_one, map_pow]
    ring
  rw [hz, hexp]
  simp only [constantCoeff_lowerRun_two_add, constantCoeff_lowerRun_two_smul,
    constantCoeff_lowerRun_two_C_mul_monomial]
  module

/-! ### The value of the sweep side at `α = (1,1)`, `(a,b) = (2,3)` -/

/-- **The two-part clause's right-hand side at `(a,b) = (2,3)`, computed.**

`ct(d_-^{(1)}d_-^{(2)}G_{2,1}G_{1,1}(1))`
`  = q·[B_2B_2(e_1^2) + (q-1)B_2B_2(e_2) - uB_3B_2(e_1) - uB_2B_3(e_1) + u^2B_3B_3(1)]`.

Every sweep operator is gone: the `Λ` side of `HJO.Mellit.qop_double_apply_one_of_lhsWord` at
`α = (1,1)` is now a finite expression in Hall--Littlewood operators.

The three hypotheses are exactly the module docstring's, and the scalar `q` is where the two
inverses `(qu)^{-1}` and `q^2/(1-q)` are finally cancelled against the `(q-1)u` the displacement
defect supplies. -/
@[hjo "lem_mellit_lhs_two_three_value"]
theorem constantCoeff_lowerRun_two_stageWordTotal_two_three (hq0 : q ≠ 0) (hu0 : u ≠ 0)
    (hq1 : q ≠ 1) :
    MvPolynomial.constantCoeff (Mellit.lowerRun q 2 (Mellit.stageWordTotal q u 2 3 [1, 1]))
      = q • (Bop q ((2 : ℕ) : ℤ) (Bop q ((2 : ℕ) : ℤ) (elemSymm L 1 * elemSymm L 1))
          + (q - 1) • Bop q ((2 : ℕ) : ℤ) (Bop q ((2 : ℕ) : ℤ) (elemSymm L 2))
          - u • Bop q ((3 : ℕ) : ℤ) (Bop q ((2 : ℕ) : ℤ) (elemSymm L 1))
          - u • Bop q ((2 : ℕ) : ℤ) (Bop q ((3 : ℕ) : ℤ) (elemSymm L 1))
          + u ^ 2 • Bop q ((3 : ℕ) : ℤ) (Bop q ((3 : ℕ) : ℤ) (1 : Lambda L))) := by
  have h1q : (1 : L) - q ≠ 0 := sub_ne_zero.2 (Ne.symm hq1)
  have hmem : Mellit.stageTotal q u 2 3 0 1 (1 : Total L) ∈ piece L 1 := by
    rw [stageTotal_two_three_zero_one_one hq0 hu0 hq1, ← scal_mul_eq_smul_total]
    exact add_mem (neg_mem (mul_mem (C_mem_piece _ _)
        (pow_mem (auxVar_mem_piece le_rfl le_rfl) 2)))
      (mul_mem (scal_mem_piece _ _) (pow_mem (auxVar_mem_piece le_rfl le_rfl) 3))
  rw [stageWordTotal_one_one, lowerRun_two_stageTotal_one_of_slope q u 2 3 hmem,
    neg_auxVar_one_mul_dplusStar_one_stageTotal hq0 hu0 hq1, slopeOperator_two_three_apply,
    constantCoeff_smul, constantCoeff_lowerRun_two_neg_smul,
    constantCoeff_lowerRun_two_auxVar_one_mul_zCommTwo_seedArgTwo hq0,
    show ((-1 : L) ^ (2 - 1)) = -1 from by norm_num, smul_neg, smul_smul, smul_smul,
    show (-1 : L) * ((q * u)⁻¹ * (q ^ 2 / (1 - q))) * -((q - 1) * u) = -q from by
      field_simp; ring,
    neg_smul, neg_neg]

end HJO.Sweep

end
