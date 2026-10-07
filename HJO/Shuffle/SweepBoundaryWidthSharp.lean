/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepBlockExchange
public import HJO.Shuffle.SweepAppendTwoThree
public meta import HJO.Attr

/-!
# The round-boundary side condition is sharp: it cannot be weakened by one unit

`HJO.Mellit.tailRoundWord_stairWord` carries a staircase across the tail layer of a round under the
side condition

`c + #AC(ℓ) + m + δ + 1 ≤ HJO.Paths.sweepWidth w p + β`

at every point `p` of the layer, and `HJO.Mellit.not_tailRoundWord_stairWord_bound` shows that
condition **fails** at round `4` of `z = w = HJO.Mellit.baseTwoThreeB`, where the arriving staircase
has `m = δ = 1` and offset `0` and the operator is read at index `2`: the sharp per-point demand of
`HJO.Sweep.corner_stairWord` there is `c + m + δ + 1 = 3 ≤ 2`. It fails **by exactly one unit**, and
only at events of type `B` and `C` — rules `A`, `D` and `E` ask less. So the obvious question is
whether the `+1` is an artefact of the proof: rules `B` and `C` route through
`HJO.Sweep.dminus_cmAscWord_range`, whose reach is `T_j` with `j ≤ n - 2`, and if the true demand at
those rules were `c + m + δ ≤ n` like rule `A`'s then **every** violation of the round-boundary
condition would disappear and the round-local exchange would close.

**It is not an artefact. The `+1` is the truth, and this file exhibits the obstruction.**

## Main results

* `HJO.Sweep.not_dminus_braid_width`: `d^♭_-{}^{(2)}` does **not** commute with `T_1`, so
  `HJO.Sweep.dminus_stairWord` — and with it rule `B` — is false at `c + m + δ = n`. Witness `y_1`;
  nothing is assumed of `q`.
* `HJO.Sweep.not_corner_braid_width`: `Δ^{(2)}(T_1y_1) ≠ T_2(Δ^{(2)}y_1)` for every `q ≠ 1`, so
  `HJO.Sweep.corner_stairWord` — and with it rule `C` — is false at `c + m + δ = n`. The two sides
  are `-qy_1^2` and `-y_1y_3 + (q-1)y_1y_2`; the second carries `y_3` and the first cannot.
* `HJO.Sweep.not_dminus_stairWord_of_add_le`, `HJO.Sweep.not_corner_stairWord_of_add_le`: the same,
  stated as the refutation of the weakened lemmas.
* `HJO.Sweep.X_zero_eq_mul_shiftAux`: the witness vector `y_1` is `g·Σ_1F` with `g = y_1` `Λ`-free
  and in `V_1`, so it is of the two-block form the base layer hands to the boundary and the
  refutation is not answerable by restricting to the vectors that actually arrive.
* `HJO.Mellit.not_sweepOperatorShifted_stairWord_of_add_le`: **the round-boundary consequence.** At
  the very point the bound fails — the type-`C` point `(0,2)` of round `4` of
  `HJO.Mellit.baseTwoThreeB`, read at index `HJO.Paths.sweepWidth w p + β = 1 + 1 = 2` — the
  weakened condition `c + m + δ ≤ sweepWidth w p + β` **holds** (`2 ≤ 2`) and the identity it would
  license is **false**. The layer there is the single point `(0,2)`
  (`HJO.Mellit.tailRound_four_baseTwoThreeB`), so this is the whole layer identity, not one summand
  of it; and `HJO.Paths.sweepRight w (0,2) = 0`, so the rule-`C` scalar `q^{-a_P}` is `1` and the
  refutation is free of `q ≠ 0`.

## Why this closes the shape

The round-local exchange was the last identified route through the inter-round boundary: re-blocking
is refuted by `HJO.Sweep.not_dplus_shiftAux_mul_of_mem_piece`, carrying the correction outward by
`HJO.Mellit.not_tailRoundWord_stairWord_bound`, and the remaining hope was that the bound those
refutations violate is one unit too strong. It is not. The single letter `T_1` of the arriving
staircase sits at index `1`, and the operator at the arrival point reads `y_2` — through
`d^♭_-{}^{(3)}` in one half of the commutator `Δ^{(2)}` and `d^♭_-{}^{(2)}` in the other. `T_1`
moves `y_2`. The failure is therefore an overlap of the staircase with the variable the operator
extracts, and no bookkeeping removes it.

What survives is: a statement that **consumes** the staircase at the boundary must do so before the
tail layer's operators are applied, i.e. it must change the two-block decomposition itself, and the
decomposition it changes it to must be one in which the high block is still the base's own partially
computed vector. Nothing in this library produces such a decomposition.

## References

A. Mellit, *Toric braids and `(m, n)`-parking functions*, sections 4 and 6.
-/

@[expose] public section

namespace HJO.Sweep

open HJO.Sym

variable {L : Type*} [Field L] [Algebra ℚ L] {q : L}

/-! ### The two transpositions of the first three auxiliary variables, evaluated -/

section Swaps

private theorem swapIndex_one (n : ℕ) (h : n ≤ 2) :
    (Equiv.swap ((1 : ℕ) - 1) 1) n = if n = 0 then 1 else if n = 1 then 0 else n := by
  interval_cases n <;> decide

private theorem swapIndex_two (n : ℕ) (h : n ≤ 2) :
    (Equiv.swap ((2 : ℕ) - 1) 2) n = if n = 1 then 2 else if n = 2 then 1 else n := by
  interval_cases n <;> decide

end Swaps

/-! ### The braid operators on the monomials the boundary witness needs -/

section Braids

omit [Algebra ℚ L] in
/-- `∂_2(y_1y_3) = y_1`. -/
theorem dividedDiff_two_X_zero_mul_X_two :
    dividedDiff 2 ((MvPolynomial.X 0 * MvPolynomial.X 2 : Total L)) = MvPolynomial.X 0 := by
  refine (dividedDiff_unique (i := 2) (by omega) ?_).symm
  rw [map_mul, swapAux_X, swapAux_X, swapIndex_two 0 (by omega), swapIndex_two 2 (by omega)]
  norm_num; ring

omit [Algebra ℚ L] in
/-- **`T_2(y_1y_3) = qy_1y_2`.** -/
theorem braid_two_X_zero_mul_X_two :
    braid q 2 ((MvPolynomial.X 0 * MvPolynomial.X 2 : Total L))
      = scal q * (MvPolynomial.X 0 * MvPolynomial.X 1) := by
  rw [braid_apply, dividedDiff_two_X_zero_mul_X_two, map_mul, swapAux_X, swapAux_X,
    swapIndex_two 0 (by omega), swapIndex_two 2 (by omega)]
  norm_num
  rw [show (auxVar 2 : Total L) = MvPolynomial.X 1 from rfl,
    ← scal_one_add_scal_sub_one q, scal_one]
  ring

omit [Algebra ℚ L] in
/-- `∂_1(y_2y_3) = y_3`. -/
theorem dividedDiff_one_X_one_mul_X_two :
    dividedDiff 1 ((MvPolynomial.X 1 * MvPolynomial.X 2 : Total L)) = MvPolynomial.X 2 := by
  refine (dividedDiff_unique (i := 1) (by omega) ?_).symm
  rw [map_mul, swapAux_X, swapAux_X, swapIndex_one 1 (by omega), swapIndex_one 2 (by omega)]
  norm_num; ring

omit [Algebra ℚ L] in
/-- **`T_1(y_2y_3) = qy_1y_3`.** -/
theorem braid_one_X_one_mul_X_two :
    braid q 1 ((MvPolynomial.X 1 * MvPolynomial.X 2 : Total L))
      = scal q * (MvPolynomial.X 0 * MvPolynomial.X 2) := by
  rw [braid_apply, dividedDiff_one_X_one_mul_X_two, map_mul, swapAux_X, swapAux_X,
    swapIndex_one 1 (by omega), swapIndex_one 2 (by omega)]
  norm_num
  rw [show (auxVar 1 : Total L) = MvPolynomial.X 0 from rfl,
    ← scal_one_add_scal_sub_one q, scal_one]
  ring

omit [Algebra ℚ L] in
/-- `∂_2(y_2y_3) = 0`: the product is symmetric in the two variables `s_2` exchanges. -/
theorem dividedDiff_two_X_one_mul_X_two :
    dividedDiff 2 ((MvPolynomial.X 1 * MvPolynomial.X 2 : Total L)) = 0 := by
  refine (dividedDiff_unique (i := 2) (by omega) ?_).symm
  rw [map_mul, swapAux_X, swapAux_X, swapIndex_two 1 (by omega), swapIndex_two 2 (by omega)]
  norm_num; ring

omit [Algebra ℚ L] in
/-- **`T_2` fixes `y_2y_3`.** -/
theorem braid_two_X_one_mul_X_two :
    braid q 2 ((MvPolynomial.X 1 * MvPolynomial.X 2 : Total L))
      = MvPolynomial.X 1 * MvPolynomial.X 2 := by
  rw [braid_apply, dividedDiff_two_X_one_mul_X_two, map_mul, swapAux_X, swapAux_X,
    swapIndex_two 1 (by omega), swapIndex_two 2 (by omega)]
  norm_num; ring

omit [Algebra ℚ L] in
/-- `∂_2(y_1y_2) = -y_1`. -/
theorem dividedDiff_two_X_zero_mul_X_one :
    dividedDiff 2 ((MvPolynomial.X 0 * MvPolynomial.X 1 : Total L))
      = -(MvPolynomial.X 0 : Total L) := by
  refine (dividedDiff_unique (i := 2) (by omega) ?_).symm
  rw [map_mul, swapAux_X, swapAux_X, swapIndex_two 0 (by omega), swapIndex_two 1 (by omega)]
  norm_num; ring

omit [Algebra ℚ L] in
/-- **`T_2(y_1y_2) = y_1y_3 - (q-1)y_1y_2`.** This is the letter the staircase becomes on the far
side of the arrival point: it carries `y_3`, which is what the refutation below reads. -/
theorem braid_two_X_zero_mul_X_one :
    braid q 2 ((MvPolynomial.X 0 * MvPolynomial.X 1 : Total L))
      = MvPolynomial.X 0 * MvPolynomial.X 2
        - scal (q - 1) * (MvPolynomial.X 0 * MvPolynomial.X 1) := by
  rw [braid_apply, dividedDiff_two_X_zero_mul_X_one, map_mul, swapAux_X, swapAux_X,
    swapIndex_two 0 (by omega), swapIndex_two 1 (by omega)]
  norm_num
  rw [show (auxVar 2 : Total L) = MvPolynomial.X 1 from rfl]
  ring

omit [Algebra ℚ L] in
/-- **`T_1(y_1) = y_2 + (1-q)y_1`.** `HJO.Sweep.braid_auxVar_pow` at `n = 1`. -/
theorem braid_one_X_zero :
    braid q 1 (MvPolynomial.X 0 : Total L)
      = MvPolynomial.X 1 + scal (1 - q) * MvPolynomial.X 0 := by
  have h := braid_auxVar_pow q (i := 1) le_rfl 1
  rw [pow_one] at h
  simpa [auxVar, Finset.sum_range_one] using h

end Braids

/-! ### Rule `B` at the failing width: `d^♭_-` does not commute with the top letter -/

section RuleB

/-- `d^♭_-{}^{(2)}(y_2) = -e_1`. -/
theorem dminus_two_X_one :
    dminus q 2 (MvPolynomial.X 1 : Total L) = -(MvPolynomial.C (elemSymm L 1) : Total L) := by
  have h := dminus_auxVar_pow q 1 1
  rw [pow_one, show (1 : ℕ) + 1 = 2 from rfl, auxVar_two] at h
  rw [h]; ring

/-- **`d^♭_-{}^{(2)}` DOES NOT COMMUTE WITH `T_1`.** The two sides differ by `e_1 + y_2`:

`d^♭_-{}^{(2)}(T_1y_1) = -e_1 + (1-q)y_1` while `T_1(d^♭_-{}^{(2)}y_1) = y_2 + (1-q)y_1`.

`HJO.Sweep.dminus_braid` covers `T_i` for `i ≤ n - 2` only, and `T_{n-1}` moves `y_n`, the variable
`d^♭_-{}^{(n)}` extracts in; here `n = 2` and the letter is `T_1`. Nothing is assumed of `q`. -/
theorem not_dminus_braid_width :
    dminus q 2 (braid q 1 (MvPolynomial.X 0 : Total L))
      ≠ braid q 1 (dminus q 2 (MvPolynomial.X 0 : Total L)) := by
  rw [braid_one_X_zero, dminus_two_X_zero q, braid_one_X_zero, map_add, dminus_scal_mul,
    dminus_two_X_zero q, dminus_two_X_one]
  intro h
  have hne0 : ¬ ((0 : ℕ →₀ ℕ) = Finsupp.single 1 1) := by
    intro hh; exact absurd (congrArg (fun f : ℕ →₀ ℕ => f 1) hh) (by simp)
  have hne1 : ¬ ((Finsupp.single 0 1 : ℕ →₀ ℕ) = Finsupp.single 1 1) := by
    intro hh; exact absurd (congrArg (fun f : ℕ →₀ ℕ => f 1) hh) (by simp)
  have hc := congrArg (MvPolynomial.coeff (Finsupp.single 1 1)) h
  rw [show (scal (1 - q) : Total L) * MvPolynomial.X 0
        = MvPolynomial.monomial (Finsupp.single 0 1) (MvPolynomial.C (1 - q)) from by
      rw [← monomial_single_one_eq_X (L := L) 0, scal, MvPolynomial.C_mul_monomial, mul_one],
    show (MvPolynomial.X 1 : Total L)
        = MvPolynomial.monomial (Finsupp.single 1 1) 1 from (monomial_single_one_eq_X 1).symm] at hc
  simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_neg, MvPolynomial.coeff_C,
    MvPolynomial.coeff_monomial, hne0, hne1, ite_false, ite_true, neg_zero, zero_add] at hc
  exact one_ne_zero (by linear_combination -hc)

/-- **The weakened rule-`B` pass is false.** `HJO.Sweep.dminus_stairWord` asks
`c + m + δ + 1 ≤ n`; dropping the unit — putting rule `B` on rule `A`'s bound — makes the statement
untrue, already at `c = 0`, `m = δ = 1`, `n = 2`, where the weakened bound reads `2 ≤ 2`. -/
@[hjo "not_sweep_round_stair_pass_sharp"]
theorem not_dminus_stairWord_of_add_le :
    ¬ ∀ (δ c n m : ℕ), c + m + δ ≤ n → ∀ X : Total L,
        dminus q n (stairWord q δ c m X) = stairWord q δ c m (dminus q n X) := by
  intro h
  refine not_dminus_braid_width (q := q) ?_
  have key := h 1 0 2 1 (by omega) (MvPolynomial.X 0)
  rw [stairWord_one] at key
  norm_num [cmAscWord_self] at key
  simpa [braidEnd] using key

end RuleB

/-! ### Rule `C` at the failing width: `Δ^{(2)}` does not carry `T_1` to `T_2` -/

section RuleC

omit [Algebra ℚ L] in
/-- `d^♭_+{}^{(2)}(y_1) = -qy_1y_2`. -/
theorem dplus_two_X_zero :
    dplus q 2 (MvPolynomial.X 0 : Total L)
      = -(scal q * (MvPolynomial.X 0 * MvPolynomial.X 1)) := by
  rw [dplus_apply, show (2 : ℕ) + 1 = 3 from rfl, qshift_auxVar, auxVar_three,
    trainUpEnd_one_three, Module.End.mul_apply, braidEnd, braidEnd,
    LinearMap.restrictScalars_apply, LinearMap.restrictScalars_apply,
    show (MvPolynomial.X 2 : Total L) * MvPolynomial.X 0
      = MvPolynomial.X 0 * MvPolynomial.X 2 from by ring,
    braid_two_X_zero_mul_X_two, braid_scal_mul, braid_one_X_zero_mul_X_one]

omit [Algebra ℚ L] in
/-- `d^♭_+{}^{(2)}(y_2) = -qy_1y_3`. -/
theorem dplus_two_X_one :
    dplus q 2 (MvPolynomial.X 1 : Total L)
      = -(scal q * (MvPolynomial.X 0 * MvPolynomial.X 2)) := by
  rw [dplus_apply, show (2 : ℕ) + 1 = 3 from rfl, qshift_auxVar, auxVar_three,
    trainUpEnd_one_three, Module.End.mul_apply, braidEnd, braidEnd,
    LinearMap.restrictScalars_apply, LinearMap.restrictScalars_apply,
    show (MvPolynomial.X 2 : Total L) * MvPolynomial.X 1
      = MvPolynomial.X 1 * MvPolynomial.X 2 from by ring,
    braid_two_X_one_mul_X_two, braid_one_X_one_mul_X_two]

/-- `d^♭_-{}^{(3)}(y_1y_2) = y_1y_2`: the argument is free of `y_3`. -/
theorem dminus_three_X_zero_mul_X_one :
    dminus q 3 ((MvPolynomial.X 0 * MvPolynomial.X 1 : Total L))
      = MvPolynomial.X 0 * MvPolynomial.X 1 := by
  have hmem : (MvPolynomial.X 0 * MvPolynomial.X 1 : Total L) ∈ piece L 2 :=
    mul_mem (auxVar_mem_piece (i := 1) le_rfl (by omega))
      (auxVar_mem_piece (i := 2) (by omega) (by omega))
  have hform : (MvPolynomial.X 0 * MvPolynomial.X 1 : Total L)
      = (auxVar (2 + 1) : Total L) ^ 0 * (MvPolynomial.X 0 * MvPolynomial.X 1) := by
    rw [pow_zero, one_mul]
  rw [hform, show (3 : ℕ) = 2 + 1 from rfl, dminus_auxVar_pow_mul q 2 0 hmem,
    monomial_X_zero_X_one, bopExt_monomial_one, Nat.cast_zero,
    show elemSymmAlt L (0 : ℤ) = 1 from by
      rw [show ((0 : ℤ)) = ((0 : ℕ) : ℤ) from rfl, elemSymmAlt_natCast]
      simp [elemSymm_zero_eq_one],
    ← monomial_X_zero_X_one]
  simp

/-- `d^♭_-{}^{(3)}(y_1y_3) = -e_1y_1`. -/
theorem dminus_three_X_zero_mul_X_two :
    dminus q 3 ((MvPolynomial.X 0 * MvPolynomial.X 2 : Total L))
      = -(MvPolynomial.C (elemSymm L 1) * (MvPolynomial.X 0 : Total L)) := by
  have hmem : (MvPolynomial.X 0 : Total L) ∈ piece L 2 :=
    auxVar_mem_piece (i := 1) le_rfl (by omega)
  have hform : (MvPolynomial.X 0 * MvPolynomial.X 2 : Total L)
      = (auxVar (2 + 1) : Total L) ^ 1 * (MvPolynomial.X 0 : Total L) := by
    rw [show (2 : ℕ) + 1 = 3 from rfl, auxVar_three, pow_one]; ring
  rw [hform, show (3 : ℕ) = 2 + 1 from rfl, dminus_auxVar_pow_mul q 2 1 hmem,
    ← monomial_single_one_eq_X (L := L) 0, bopExt_monomial_one, Nat.cast_one, elemSymmAlt_one,
    MvPolynomial.C_neg, monomial_single_one_eq_X]
  ring

/-- `d^♭_+{}^{(1)}(e_1) = -qe_1y_1 - q(q-1)y_1^2 - (q-1)^2y_1y_2`: `τ_{2,2}` puts the letter
`(q-1)y_2` into `e_1 = p_1`, and `T_1` turns the resulting `y_2^2` into `qy_1^2 + (q-1)y_1y_2`. -/
theorem dplus_one_C_elemSymm_one :
    dplus q 1 (MvPolynomial.C (elemSymm L 1) : Total L)
      = -(scal q * (MvPolynomial.C (elemSymm L 1) * (MvPolynomial.X 0 : Total L)))
        - scal (q * (q - 1)) * (MvPolynomial.X 0 : Total L) ^ 2
        - scal ((q - 1) * (q - 1)) * (MvPolynomial.X 0 * MvPolynomial.X 1 : Total L) := by
  rw [dplus_apply, show (1 : ℕ) + 1 = 2 from rfl,
    show elemSymm L 1 = powerSum L 1 from elemSymm_one_eq_powerSum, qshift_two_powerSum,
    auxVar_two, trainUpEnd_one_two, braidEnd, LinearMap.restrictScalars_apply,
    show (MvPolynomial.X 1 : Total L)
        * (MvPolynomial.C (powerSum L 1) + scal (q - 1) * MvPolynomial.X 1)
      = MvPolynomial.C (powerSum L 1) * (MvPolynomial.X 1 : Total L)
        + scal (q - 1) * (MvPolynomial.X 1 : Total L) ^ 2 from by ring,
    map_add, braid_C_mul, braid_one_X_one q, braid_scal_mul, braid_one_X_one_sq q]
  rw [scal_mul, scal_mul]
  ring

/-- **`Δ^{(2)}(y_1) = -y_1y_2`**, for every `q ≠ 1`: the `e_1` of the two composites cancels and
the residue is `(1-q)y_1y_2`, which the normalisation `(q-1)^{-1}` turns into `-y_1y_2`. -/
theorem corner_two_X_zero (hq : q ≠ 1) :
    corner q 2 (MvPolynomial.X 0 : Total L) = -(MvPolynomial.X 0 * MvPolynomial.X 1) := by
  have hq' : q - 1 ≠ 0 := sub_ne_zero.2 hq
  have hs : (scal ((q - 1)⁻¹) : Total L) * scal q - scal ((q - 1)⁻¹) = 1 := by
    rw [← scal_mul, ← scal_sub, show (q - 1)⁻¹ * q - (q - 1)⁻¹ = 1 from by field_simp, scal_one]
  rw [corner_of_pos q (show (2 : ℕ) ≠ 0 by omega), LinearMap.smul_apply, LinearMap.sub_apply,
    Module.End.mul_apply, Module.End.mul_apply, show (2 : ℕ) + 1 = 3 from rfl,
    show (2 : ℕ) - 1 = 1 from rfl, dplus_two_X_zero, dminus_two_X_zero q, dplus_one_X_zero, map_neg,
    dminus_scal_mul, dminus_three_X_zero_mul_X_one, smul_eq_scal_mul]
  linear_combination (-(MvPolynomial.X 0 * MvPolynomial.X 1 : Total L)) * hs

/-- **`Δ^{(2)}(y_2) = -qy_1^2 - (q-1)y_1y_2`**, for every `q ≠ 1`. -/
theorem corner_two_X_one (hq : q ≠ 1) :
    corner q 2 (MvPolynomial.X 1 : Total L)
      = -(scal q * (MvPolynomial.X 0 : Total L) ^ 2)
        - scal (q - 1) * (MvPolynomial.X 0 * MvPolynomial.X 1 : Total L) := by
  have hq' : q - 1 ≠ 0 := sub_ne_zero.2 hq
  have hs1 : (scal ((q - 1)⁻¹) : Total L) * scal (q * (q - 1)) = scal q := by
    rw [← scal_mul]; congr 1; field_simp
  have hs2 : (scal ((q - 1)⁻¹) : Total L) * scal ((q - 1) * (q - 1)) = scal (q - 1) := by
    rw [← scal_mul]; congr 1; field_simp
  rw [corner_of_pos q (show (2 : ℕ) ≠ 0 by omega), LinearMap.smul_apply, LinearMap.sub_apply,
    Module.End.mul_apply, Module.End.mul_apply, show (2 : ℕ) + 1 = 3 from rfl,
    show (2 : ℕ) - 1 = 1 from rfl, dplus_two_X_one, dminus_two_X_one, map_neg, map_neg,
    dminus_scal_mul, dminus_three_X_zero_mul_X_two, dplus_one_C_elemSymm_one, smul_eq_scal_mul]
  linear_combination (-((MvPolynomial.X 0 : Total L) ^ 2)) * hs1
    + (-((MvPolynomial.X 0 * MvPolynomial.X 1 : Total L))) * hs2

/-- `Δ^{(2)}(T_1y_1) = -qy_1^2`: the two `y_1y_2` contributions cancel. -/
theorem corner_two_braid_one_X_zero (hq : q ≠ 1) :
    corner q 2 (braid q 1 (MvPolynomial.X 0 : Total L))
      = -(scal q * (MvPolynomial.X 0 : Total L) ^ 2) := by
  rw [braid_one_X_zero, map_add, ← smul_eq_scal_mul, map_smul, smul_eq_scal_mul,
    corner_two_X_zero hq, corner_two_X_one hq, show (1 : L) - q = -(q - 1) from by ring, scal_neg]
  ring

/-- **`Δ^{(2)}` DOES NOT CARRY `T_1` TO `T_2`.** For every `q ≠ 1`,

`Δ^{(2)}(T_1y_1) = -qy_1^2` while `T_2(Δ^{(2)}y_1) = -y_1y_3 + (q-1)y_1y_2`.

The right-hand side carries `y_3` and the left-hand side cannot: `Δ^{(2)}` lands in `V_2` and `T_2`
takes it out. `HJO.Sweep.corner_cmAscWord` asks `c + d + 2 ≤ n`, one unit more than
`HJO.Sweep.dplus_cmAscWord`, because both halves of the commutator
`Δ = (q-1)^{-1}(d^♭_-d^♭_+ - d^♭_+d^♭_-)` route through `HJO.Sweep.dminus_cmAscWord_range`, whose
reach is `T_j` with `j ≤ n - 2`. That unit is **not** an artefact of the proof. -/
theorem not_corner_braid_width (hq : q ≠ 1) :
    corner q 2 (braid q 1 (MvPolynomial.X 0 : Total L))
      ≠ braid q 2 (corner q 2 (MvPolynomial.X 0 : Total L)) := by
  rw [corner_two_braid_one_X_zero hq, corner_two_X_zero hq, map_neg, braid_two_X_zero_mul_X_one]
  intro h
  have hc := congrArg (MvPolynomial.coeff (Finsupp.single 0 1 + Finsupp.single 2 1)) h
  rw [show (scal q : Total L) * (MvPolynomial.X 0 : Total L) ^ 2
        = MvPolynomial.monomial (Finsupp.single 0 2) (MvPolynomial.C q) from by
      rw [MvPolynomial.X_pow_eq_monomial, scal, MvPolynomial.C_mul_monomial, mul_one],
    show (MvPolynomial.X 0 * MvPolynomial.X 2 : Total L)
        = MvPolynomial.monomial (Finsupp.single 0 1 + Finsupp.single 2 1) 1 from by
      rw [← monomial_single_one_eq_X (L := L) 0, ← monomial_single_one_eq_X (L := L) 2,
        MvPolynomial.monomial_mul, mul_one],
    show (scal (q - 1) : Total L) * (MvPolynomial.X 0 * MvPolynomial.X 1 : Total L)
        = MvPolynomial.monomial (Finsupp.single 0 1 + Finsupp.single 1 1)
            (MvPolynomial.C (q - 1)) from by
      rw [monomial_X_zero_X_one, scal, MvPolynomial.C_mul_monomial, mul_one]] at hc
  have hne1 : ¬ ((Finsupp.single 0 2 : ℕ →₀ ℕ)
      = Finsupp.single 0 1 + Finsupp.single 2 1) := by
    intro hh; exact absurd (congrArg (fun f : ℕ →₀ ℕ => f 2) hh) (by simp)
  have hne2 : ¬ ((Finsupp.single 0 1 + Finsupp.single 1 1 : ℕ →₀ ℕ)
      = Finsupp.single 0 1 + Finsupp.single 2 1) := by
    intro hh; exact absurd (congrArg (fun f : ℕ →₀ ℕ => f 2) hh) (by simp)
  simp only [MvPolynomial.coeff_neg, MvPolynomial.coeff_sub, MvPolynomial.coeff_monomial,
    hne1, hne2, ite_false, ite_true, neg_zero, sub_zero] at hc
  exact one_ne_zero (by linear_combination hc)

/-- **THE WITNESS VECTOR IS OF THE FORM THE BASE LAYER HANDS OVER.** `y_1` is `g·Σ_1F` with
`g = y_1` and `F = 1`, and `g` is `Λ`-free (`HJO.Sweep.auxSubalg`) and lies in `V_1` — exactly the
two-block shape `HJO.Sweep.dplus_shiftAux_mul` and `HJO.Mellit.exists_baseRound_shiftAux` produce at
`δ = 1`. So `HJO.Sweep.not_corner_braid_width` refutes the pass not merely on some vector of the
total space but on a vector of the very form the round boundary has to move.

Without this the refutation would be answerable by restricting the statement to the vectors that
actually arrive; with it, it is not. -/
@[hjo "not_sweep_round_stair_pass_sharp"]
theorem X_zero_eq_mul_shiftAux (L : Type*) [Field L] :
    ∃ g F : Total L, g ∈ auxSubalg L ∧ g ∈ piece L 1 ∧
      (MvPolynomial.X 0 : Total L) = g * shiftAux L 1 F :=
  ⟨MvPolynomial.X 0, 1, auxVar_mem_auxSubalg (L := L) 1,
    auxVar_mem_piece (i := 1) le_rfl le_rfl, by rw [map_one, mul_one]⟩

/-- **The weakened rule-`C` pass is false.** `HJO.Sweep.corner_stairWord` asks
`c + m + δ + 1 ≤ n`; dropping the unit makes the statement untrue, already at `c = 0`, `m = δ = 1`,
`n = 2`, where the weakened bound reads `2 ≤ 2` — which is exactly the instance the round boundary
needs. -/
@[hjo "not_sweep_round_stair_pass_sharp"]
theorem not_corner_stairWord_of_add_le (hq : q ≠ 1) :
    ¬ ∀ (δ c n m : ℕ), c + m + δ ≤ n → ∀ X : Total L,
        corner q n (stairWord q δ c m X) = stairWord q δ (c + 1) m (corner q n X) := by
  intro h
  refine not_corner_braid_width (q := q) hq ?_
  have key := h 1 0 2 1 (by omega) (MvPolynomial.X 0)
  rw [stairWord_one, stairWord_one] at key
  norm_num [cmAscWord_self] at key
  simpa [braidEnd] using key

end RuleC

end HJO.Sweep

/-! ### The round boundary: the weakened condition licenses a false identity -/

namespace HJO.Mellit

open HJO.Sweep HJO.Paths Finset

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-- The index shift the tail layer of round `4` of `HJO.Mellit.baseTwoThreeB` is read at:
`β_4 = #(HJO.Paths.baseLiveSteps z 4) = 1`. With `HJO.Paths.sweepWidth w (0,2) = 1` this is the
`2` of `HJO.Mellit.tailRound_four_baseTwoThreeB`. -/
theorem card_baseLiveSteps_baseTwoThreeB_four : #(baseLiveSteps baseTwoThreeB 4) = 1 := by decide

/-- **The arrival operator, named.** At the type-`C` point `(0,2)` of round `4` the raised operator
is `Δ^{(2)}` on the nose: its width is `1`, its shift `β_4` is `1`, and its exponent
`HJO.Paths.sweepRight w (0,2)` is `0`, so the rule-`C` scalar `q^{-a_P}` is `1`. **No hypothesis on
`q` is spent here** — in particular not `q ≠ 0`, which a nonzero exponent would have forced through
`q^{-a_P}`, an inverse that in a field silently makes the operator the zero map. -/
theorem sweepOperatorShifted_baseTwoThreeB_zero_two :
    sweepOperatorShifted q u baseTwoThreeB ((0, 2) : ℕ × ℕ) 1 = corner q 2 := by
  rw [sweepOperatorShifted_of_eventType_C baseTwoThreeB 1 eventType_baseTwoThreeB_zero_two,
    sweepRight_baseTwoThreeB_zero_two, sweepWidth_baseTwoThreeB_zero_two]
  norm_num

/-- **THE ROUND-BOUNDARY SIDE CONDITION IS SHARP.** At the point where
`HJO.Mellit.not_tailRoundWord_stairWord_bound` shows the condition of
`HJO.Mellit.tailRoundWord_stairWord` to fail — the type-`C` point `(0,2)` of round `4` of
`z = w = HJO.Mellit.baseTwoThreeB`, read at index `HJO.Paths.sweepWidth w p + β_4 = 2` — the
**weakened** condition `c + m + δ ≤ sweepWidth w p + β` is satisfied, `0 + 1 + 1 = 2 ≤ 2`, and the
identity it would license is **false**, on the vector `y_1`, for every `q ≠ 1`.

So the one-unit gap between the round-boundary obligation and the geometry is not slack in the
lemma: it is the truth about the operators. The arriving staircase at `δ = m = 1` and offset `0` is
the single letter `T_1` (`HJO.Mellit.stairWord_one_one_zero`) and the operator at the arrival point
extracts in `y_2`, which `T_1` moves; `HJO.Sweep.not_corner_braid_width` is that collision.

The vector is not an arbitrary one either: `HJO.Sweep.X_zero_eq_mul_shiftAux` puts `y_1` in the
two-block form `g·Σ_1F` with `g` `Λ`-free and in `V_1`, which is what
`HJO.Mellit.exists_baseRound_shiftAux` hands over at `δ = 1`.

Since the layer of round `4` is the single point `(0,2)`
(`HJO.Mellit.tailRound_four_baseTwoThreeB`), this is the whole layer identity and not one summand of
it. Together with `HJO.Sweep.not_dplus_shiftAux_mul_of_mem_piece` (re-blocking) and
`HJO.Mellit.not_tailRoundWord_stairWord_bound` (carrying outward) this closes the round-local
exchange: the correction cannot be commuted past the tail layer at any bound the geometry supplies,
and must be consumed before the layer acts. -/
@[hjo "not_sweep_round_stair_pass_sharp"]
theorem not_sweepOperatorShifted_stairWord_of_add_le (hq : q ≠ 1) :
    ¬ ∀ (w : Heights 2 3 1) (P : ℕ × ℕ) (β δ c m : ℕ),
        c + m + δ ≤ sweepWidth w P + β → ∀ X : Total L,
          sweepOperatorShifted q u w P β (stairWord q δ c m X)
            = stairWord q δ (c + acCount w [P]) m (sweepOperatorShifted q u w P β X) := by
  intro h
  refine not_corner_braid_width (q := q) hq ?_
  have hbd : 0 + 1 + 1 ≤ sweepWidth baseTwoThreeB ((0, 2) : ℕ × ℕ) + 1 := by
    rw [sweepWidth_baseTwoThreeB_zero_two]
  have key := h baseTwoThreeB (0, 2) 1 1 0 1 hbd (MvPolynomial.X 0)
  rw [sweepOperatorShifted_baseTwoThreeB_zero_two,
    acCount_cons_of_ac [] (Or.inr eventType_baseTwoThreeB_zero_two), acCount_nil,
    stairWord_one, stairWord_one] at key
  norm_num [cmAscWord_self] at key
  simpa [braidEnd] using key

end HJO.Mellit
