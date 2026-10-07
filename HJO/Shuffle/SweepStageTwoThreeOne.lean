/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.MellitLevelRaiseRow
public import HJO.Shuffle.SweepBraidMonomial

/-! # `G_{2,1}` at `(2,3)` on the invariant of the one-part colouring, in closed form

The `append` clause of `HJO.Mellit.SweepAppend` at `(a,b) = (2,3)`, `α = [1]`, `A = 1` compares the
invariant of the two-part colouring against `HJO.Mellit.stage` applied to the invariant of the
one-part one. The second of those is `HJO.Mellit.dsc_two_three_one`, the polynomial
`e_1y_1^2 - uy_1^3`; this file evaluates the stage on it:

**`G_{2,1}(e_1y_1^2 - uy_1^3) = -q y_1^2y_2^2((e_1 - uy_1)(e_1 - uy_2) + (q-1)e_2)`**

(`HJO.Mellit.stageTotal_two_three_one_one_base`), for every `q ∉ {0,1}` and every `u ≠ 0`.

`HJO/Collinear/CommutationTheorem.lean` records this as the one substantial computation standing
between the `α = []` instance `HJO.Mellit.sweepAppend_nil_two_three_one` and the first instance
whose base index set is not a singleton. It is the right-hand side of that instance, and it is what
a proof of the summed band identity of `HJO.Mellit.sweepAppend_of_forall_sum_band` has to meet.

## The shape of the answer, and why it is worth reading

Write `V(y) = y^2(e_1 - uy)` for the one-part invariant, so that the value above is

`-q(V(y_1)V(y_2) + (q-1)e_2y_1^2y_2^2)`.

The stage at `A = 1` therefore returns `-q` times the *product* of two copies of its argument,
one in each variable, corrected by a single multiple of `e_2` — and the correction is exactly the
term the one-variable data cannot see. Nothing in the derivation was arranged to produce that; it
is what the four operators leave behind.

## The four steps

1. `HJO.Mellit.dplusStar_one_base`: `d^{*(1)}_+` sends `e_1y_1^2 - uy_1^3` to
   `(e_1 + (q-1)uy_1)y_2^2 - uy_2^3`. The letter `(q-1)y_2` that `HJO.Sweep.qshift` adds to `e_1` is
   carried back to `y_1` by the wrap-around `cy_2(y_2) = uy_1` of `HJO.Sweep.cycleShift`, which is
   where the `u` in the coefficient of `y_1` comes from.
2. `HJO.Mellit.braidInvEnd_one_auxVar_sq_mul_dplusStar_one_base`: the train `T^*_{2↘1} = T_1^{-1}`
   inside `HJO.Sweep.zop` collapses that to `e_1y_1^2y_2^2 - uy_1^3y_2^2`. Three monomials go in and
   two come out: `y_1^2y_2^2` is `s_1`-symmetric so the letter fixes it, and the two contributions
   to `y_1^2y_2^3` — one from `T_1^{-1}(y_1^3y_2^2) = q^{-1}y_1^2y_2^3` and one from the
   two-term value `T_1^{-1}(y_1^2y_2^3)` — cancel identically. This is the only place `q ≠ 0` is
   spent on a braid letter.
3. `HJO.Mellit.zCommTwo_base`: the commutator half of `z_1` on `V_2` is
   `HJO.Sweep.zCommTwo_monomial'`, one reading of `HJO.Sweep.zDefect` per monomial, and the two
   values it needs are proved (`HJO.Sweep.zDefect_two_elemSymm_one`, `HJO.Sweep.zDefect_two_one`).
   The result is `(q-1)u·y_1y_2^2((e_1 - uy_1)(e_1 - uy_2) + (q-1)e_2)`. **`e_3` occurs in both
   halves of the defect and cancels**: `B_2(e_1) = e_1e_2 - (1-q)e_3` carries it into the first, the
   displacement of `e_3` carries it into the second, and the value has none.
4. `HJO.Mellit.stageTotal_two_three_one_one_base` assembles: the slope word `β_{2,3} = yzy` at the
   grading two (`HJO.Mellit.slopeOperator_two_three_grading_two`), then the descending train
   `T_{2↘1} = T_1`.

## The last letter is the identity, not multiplication by `q`

`T_{2↘1}` meets `y_1^2y_2^2((e_1-uy_1)(e_1-uy_2) + (q-1)e_2)`, which is `s_1`-symmetric, and
`HJO.Sweep.braid_eq_self_of_swapAux_eq` says `T_1` fixes it. It does **not** multiply it by `q`: the
eigenvalue `q` belongs to the *other* eigenspace of the Hecke letter, and `HJO.Sweep.braid` gives
`T_iF = s_iF + (q-1)y_i∂_iF` with `∂_iF = 0` here. A hand computation of this instance that assumed
the `q` produces an answer wrong by a factor of `q` and matching nothing.

## Genericity

`q ≠ 0`, `u ≠ 0`, `q ≠ 1`, all three irreducible and all three the field's `0⁻¹ = 0` rather than
bookkeeping.

* `q ≠ 1` is the `q^k/(1-q)` of `HJO.Sweep.zop`; at `q = 1` that scalar is undefined and `z_1` is
  the zero map, so the clause would be **false**, not vacuous.
* `q ≠ 0` twice over: for `T_1^{-1}` of `HJO.Sweep.braid`'s inverse to exist at all, and for the
  `(qu)^{-1}` of `HJO.Sweep.slopeOperator`.
* `u ≠ 0` for that same `(qu)^{-1}`: the whole of the assembly's scalar arithmetic is
  `(qu)^{-1}·q^2/(1-q)·(q-1)u = -q`, and it needs `u` to be invertible for the `u` of the
  displacement to cancel the `u^{-1}` of the letter.

The first three steps are weaker: steps 1 and 3 carry no hypothesis at all, and step 2 carries only
`q ≠ 0`.

## References

This file builds on `HJO.Mellit.stage`, `HJO.Mellit.replicatedLetter`, `HJO.Sweep.zop`,
`HJO.Sweep.slopeOperator`, `HJO.Sweep.dplusStar`, `HJO.Sweep.cycleShift`, `HJO.Sweep.braid`,
`HJO.Sweep.dminus`, `HJO.Sweep.qshift`. Transcribing A. Mellit, *Toric braids and `(m, n)`-parking
functions*, sections 4 and 6.
-/

@[expose] public section

namespace HJO.Mellit

open HJO.Sweep HJO.Sym

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-- **`d^{*(1)}_+(e_1y_1^2 - uy_1^3) = (e_1 + (q-1)uy_1)y_2^2 - uy_2^3`.**

`HJO.Sweep.dplusStar_one_auxVar_pow_mul_C` moves the power of `y_1` up to `y_2` and reads the
`Λ`-coefficient at the grading zero, where `HJO.Sweep.dplusStar_C_elemSymm_one` gives
`e_1 + (q-1)uy_1`: the letter `(q-1)y_2` of `HJO.Sweep.qshift` composed with the wrap-around
`cy_2(y_2) = uy_1` of `HJO.Sweep.cycleShift`. The scalar `u` of the second monomial is a constant of
the `Λ`-algebra and rides through.

Unconditional: no inverse occurs, and both sides are polynomial in `q` and `u`. -/
theorem dplusStar_one_base (q u : L) :
    dplusStar q u 1 (MvPolynomial.C (elemSymm L 1) * (auxVar 1 : Total L) ^ 2
        - scal u * (auxVar 1 : Total L) ^ 3)
      = (MvPolynomial.C (elemSymm L 1) + scal ((q - 1) * u) * (auxVar 1 : Total L))
            * (auxVar 2 : Total L) ^ 2
        - scal u * (auxVar 2 : Total L) ^ 3 := by
  have h1 : (MvPolynomial.C (elemSymm L 1) : Total L) * (auxVar 1 : Total L) ^ 2
      = (auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 1) := by ring
  have h2 : (scal u : Total L) * (auxVar 1 : Total L) ^ 3
      = (auxVar 1 : Total L) ^ 3 * MvPolynomial.C (MvPolynomial.C u : Lambda L) := by
    rw [scal]; ring
  have hu : dplusStar q u 0 (MvPolynomial.C (MvPolynomial.C u : Lambda L) : Total L) = scal u := by
    rw [← dplusStarAlg_eq_dplusStar, show (MvPolynomial.C (MvPolynomial.C u : Lambda L) : Total L)
      = algebraMap L (Total L) u from rfl, AlgHom.commutes]
    rfl
  rw [map_sub, h1, h2, dplusStar_one_auxVar_pow_mul_C, dplusStar_one_auxVar_pow_mul_C, hu,
    dplusStar_C_elemSymm_one, starLetter]
  rw [scal_mul]
  ring

/-- **`T_1^{-1}(y_1^2 d^{*(1)}_+(e_1y_1^2 - uy_1^3)) = e_1y_1^2y_2^2 - uy_1^3y_2^2`**, for
`q ≠ 0`.

Three monomials enter and two leave. `y_1^2y_2^2` is `s_1`-symmetric, so the inverted letter fixes
it (`HJO.Sweep.braidInv_eq_self_of_swapAux_eq`); the `(q-1)u y_1^3y_2^2` becomes
`(q-1)uq^{-1}y_1^2y_2^3` by `HJO.Sweep.braidInv_auxVar_pow_succ_mul_auxVar_pow`; and the
`-uy_1^2y_2^3` becomes `-uy_1^3y_2^2 - u(q-1)q^{-1}y_1^2y_2^3` by the two-term
`HJO.Sweep.braidInv_auxVar_pow_mul_auxVar_pow_succ`. The two `y_1^2y_2^3` terms are negatives and
cancel identically, at every `q` and `u`.

`q ≠ 0` is `HJO.Sweep.braid`'s inverse `T_i^{-1} = (T_i + (q-1))/q` needing to exist. -/
theorem braidInvEnd_one_auxVar_sq_mul_dplusStar_one_base (hq0 : q ≠ 0) :
    braidInvEnd q 1 ((auxVar 1 : Total L) ^ 2 *
        dplusStar q u 1 (MvPolynomial.C (elemSymm L 1) * (auxVar 1 : Total L) ^ 2
          - scal u * (auxVar 1 : Total L) ^ 3))
      = MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2)
        - scal u * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2) := by
  have hsplit : (auxVar 1 : Total L) ^ 2 *
      ((MvPolynomial.C (elemSymm L 1) + scal ((q - 1) * u) * (auxVar 1 : Total L))
            * (auxVar 2 : Total L) ^ 2
        - scal u * (auxVar 2 : Total L) ^ 3)
      = MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2)
        + scal ((q - 1) * u) * ((auxVar 1 : Total L) ^ (2 + 1) * (auxVar 2 : Total L) ^ 2)
        - scal u * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ (2 + 1)) := by ring
  have hsym : swapAux L 1 (MvPolynomial.C (elemSymm L 1)
      * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2))
      = MvPolynomial.C (elemSymm L 1)
        * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2) := by
    rw [map_mul, map_mul, map_pow, map_pow, swapAux_C, swapAux_one_auxVar_one,
      swapAux_one_auxVar_two]
    ring
  have hbi : ∀ F : Total L, braidInvEnd q 1 F = braidInv q 1 F := fun F => by
    rw [braidInvEnd, LinearMap.restrictScalars_apply]
  rw [dplusStar_one_base, hsplit, map_sub, map_add, hbi, hbi, hbi,
    braidInv_eq_self_of_swapAux_eq hq0 hsym, braidInv_scal_mul, braidInv_scal_mul,
    braidInv_auxVar_pow_succ_mul_auxVar_pow hq0 (le_refl 1) 2,
    braidInv_auxVar_pow_mul_auxVar_pow_succ hq0 (le_refl 1) 2]
  simp only [scal, map_mul, map_sub, map_one]
  ring

/-- **The commutator half of `z_1` on `V_2`, on the vector step two produced:**
`(d^{*(1)}_+d^{(2)}_- - d^{(3)}_-d^{*(2)}_+)(e_1y_1^2y_2^2 - uy_1^3y_2^2)`
`= (q-1)u·y_1y_2^2((e_1 - uy_1)(e_1 - uy_2) + (q-1)e_2)`.

`HJO.Sweep.zCommTwo_monomial'` sends each monomial `Ay_1^my_2^n` to `y_2^m` times the grading-one
defect `HJO.Sweep.zDefect` of `A` at `n`, so the whole value is the two proved defects
`HJO.Sweep.zDefect_two_elemSymm_one` and `HJO.Sweep.zDefect_two_one`, the second scaled by `u`
through `HJO.Sweep.zDefect_smul`. Note that the spectator exponent `m` differs between the two
monomials — `2` and `3` — which is why the answer is not a multiple of a single one of them.

**`e_3` cancels.** `B_2(e_1) = e_1e_2 - (1-q)e_3` puts it into `d^{*}_+d_-`, and the displacement
of `e_3` puts it into `d_-d^{*}_+`; the defect at `n = 2` on `e_1` has none, and neither has this.
So a value that looks as though it should need the degree-`3` symmetric functions does not.

Unconditional: both defects are polynomial identities in `q` and `u`, and this is a `Λ`-linear
combination of them. -/
theorem zCommTwo_base (q u : L) :
    zCommTwo q u (MvPolynomial.C (elemSymm L 1)
          * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2)
        - scal u * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2))
      = scal ((q - 1) * u) * ((auxVar 1 : Total L) * (auxVar 2 : Total L) ^ 2
          * ((MvPolynomial.C (elemSymm L 1) - scal u * (auxVar 1 : Total L))
              * (MvPolynomial.C (elemSymm L 1) - scal u * (auxVar 2 : Total L))
            + scal (q - 1) * MvPolynomial.C (elemSymm L 2))) := by
  have hC : (MvPolynomial.C u : Lambda L) = u • (1 : Lambda L) := by
    rw [MvPolynomial.smul_eq_C_mul, mul_one]
  have h2 : (scal u : Total L) * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2)
      = MvPolynomial.C (MvPolynomial.C u : Lambda L)
        * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2) := by
    rw [scal]
  rw [map_sub, h2, zCommTwo_monomial', zCommTwo_monomial', hC, zDefect_smul,
    zDefect_two_elemSymm_one, zDefect_two_one, ← scal_mul_eq_smul_total]
  simp only [scal, map_mul, map_sub, map_one, map_pow]
  ring

/-- **`Ξ^{(2)}_{2,3} = (-y_1)·(qu)^{-1}z^{(2)}_1·(-y_1)`**, the slope word `β_{2,3} = yzy` of
`HJO.Sweep.slopeOperator` read at the grading two. `HJO.Sweep.slopeOperator_two_odd` at `K = 2`,
`k = 1`; `HJO.Sweep.slopeOperator_two_three` is the same statement one grading lower.

Unconditional, the `(qu)^{-1}` being carried symbolically. -/
theorem slopeOperator_two_three_grading_two (q u : L) :
    slopeOperator q u 2 2 3
      = (-LinearMap.mulLeft L (auxVar 1 : Total L)) * ((q * u)⁻¹ • zopOneStar q u 2)
        * (-LinearMap.mulLeft L (auxVar 1 : Total L)) := by
  rw [show (3 : ℕ) = 2 * 1 + 1 from rfl, slopeOperator_two_odd, pow_one]

/-- **`G_{2,1}(e_1y_1^2 - uy_1^3) = -q y_1^2y_2^2((e_1 - uy_1)(e_1 - uy_2) + (q-1)e_2)`**, for
every `q ∉ {0,1}` and every `u ≠ 0`.

This is `HJO.Mellit.stage` at `(a,b) = (2,3)`, the grading `k = 1` and `A = 1`, applied to
`HJO.Mellit.dsc_two_three_one` — the right-hand side of the `α = [1]`, `A = 1` clause of
`HJO.Mellit.SweepAppend`, whose left-hand side is a sum over **four** paths and whose base index set
is the two-element `HJO.Mellit.aboveReturnPaths_two_three_one`. The earlier
`HJO.Mellit.sweepAppend_nil_two_three_one` cannot see any of that: there the base set is a
singleton.

`HJO.Sweep.stageTotal_one_apply` empties the `(Z^{(2)}_{2,3})^{A-1}` of `HJO.Mellit.stage` at
`A = 1`, so the whole word is one slope operator between two braid letters, and the three steps
above supply its value. The scalar arithmetic is a single identity,
`(qu)^{-1}·q^2/(1-q)·(q-1)u = -q`, and it is where all three exclusions are spent.

The last letter `T_{2↘1} = T_1` (`HJO.Sweep.trainDownEnd_two_one`) acts as the **identity** on the
answer, which is `s_1`-symmetric — not as multiplication by `q`. -/
theorem stageTotal_two_three_one_one_base (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    stageTotal q u 2 3 1 1 (MvPolynomial.C (elemSymm L 1) * (auxVar 1 : Total L) ^ 2
        - scal u * (auxVar 1 : Total L) ^ 3)
      = -(scal q * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2
          * ((MvPolynomial.C (elemSymm L 1) - scal u * (auxVar 1 : Total L))
              * (MvPolynomial.C (elemSymm L 1) - scal u * (auxVar 2 : Total L))
            + scal (q - 1) * MvPolynomial.C (elemSymm L 2)))) := by
  have h1q : (1 : L) - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq1)
  set K : Total L := (MvPolynomial.C (elemSymm L 1) - scal u * (auxVar 1 : Total L))
      * (MvPolynomial.C (elemSymm L 1) - scal u * (auxVar 2 : Total L))
    + scal (q - 1) * MvPolynomial.C (elemSymm L 2) with hK
  set M : Total L := (auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2 * K with hM
  have hsym : swapAux L 1 (scal q * M) = scal q * M := by
    rw [hM, hK]
    simp only [scal, map_mul, map_add, map_sub, map_pow, swapAux_C, swapAux_one_auxVar_one,
      swapAux_one_auxVar_two]
    ring
  have hsc : (scal ((q * u)⁻¹) : Total L)
      * (scal (q ^ 2 / (1 - q)) * scal ((q - 1) * u)) = -scal q := by
    rw [← scal_mul, ← scal_mul,
      show (q * u)⁻¹ * (q ^ 2 / (1 - q) * ((q - 1) * u)) = -q from by field_simp; ring, scal_neg]
  have hinner : zopOneStar q u 2 ((auxVar 1 : Total L) ^ 2 *
        dplusStar q u 1 (MvPolynomial.C (elemSymm L 1) * (auxVar 1 : Total L) ^ 2
          - scal u * (auxVar 1 : Total L) ^ 3))
      = (q ^ 2 / (1 - q)) • (scal ((q - 1) * u)
          * ((auxVar 1 : Total L) * (auxVar 2 : Total L) ^ 2 * K)) := by
    rw [zopOneStar_two_eq]
    simp only [LinearMap.smul_apply, Module.End.mul_apply]
    rw [braidInvEnd_one_auxVar_sq_mul_dplusStar_one_base hq0, zCommTwo_base, hK]
  have hslope : slopeOperator q u 2 2 3 (-((auxVar 1 : Total L) *
        dplusStar q u 1 (MvPolynomial.C (elemSymm L 1) * (auxVar 1 : Total L) ^ 2
          - scal u * (auxVar 1 : Total L) ^ 3)))
      = scal q * M := by
    rw [slopeOperator_two_three_grading_two]
    simp only [Module.End.mul_apply, LinearMap.neg_apply, LinearMap.mulLeft_apply,
      LinearMap.smul_apply]
    rw [show -((auxVar 1 : Total L) * -((auxVar 1 : Total L) *
            dplusStar q u 1 (MvPolynomial.C (elemSymm L 1) * (auxVar 1 : Total L) ^ 2
              - scal u * (auxVar 1 : Total L) ^ 3)))
        = (auxVar 1 : Total L) ^ 2 *
          dplusStar q u 1 (MvPolynomial.C (elemSymm L 1) * (auxVar 1 : Total L) ^ 2
            - scal u * (auxVar 1 : Total L) ^ 3) from by ring, hinner, hM]
    simp only [← scal_mul_eq_smul_total]
    linear_combination (-((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2 * K)) * hsc
  rw [stageTotal_one_apply, show (1 : ℕ) + 1 = 2 from rfl, hslope, trainDownEnd_two_one, braidEnd,
    LinearMap.restrictScalars_apply, braid_eq_self_of_swapAux_eq q hsym]
  norm_num

end HJO.Mellit

end
