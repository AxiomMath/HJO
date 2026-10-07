/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CMStructure.VmodDplusRelations
public meta import HJO.Attr

/-! # The modified lowering operator is a section of the raising operator

Mellit's `HJO.Sweep.dminus_trainUpEnd_star_cmDPlus`: for `k ≥ 0` and `F ∈ V_k`,
`d^♭_-(T^*_{k+1↓1}(d_+F)) = F`, with `d_+` the unmodified raising operator of `HJO.Sweep.cmDPlus`,
`T^*_{k+1↓1}` the starred descending word of `HJO.Braid.wordDownStar` and `d^♭_-` the modified
lowering operator `HJO.Sweep.dminus`.

## Main results

* `HJO.Sweep.lowerCoeff_of_mem_piece` — the coefficient extraction of `d^♭_-` fixes `V_k`.
* `HJO.Sweep.dminus_trainUpEnd_star_cmDPlus`.

## Implementation notes

**The starred word is the one already identified.** `T^*_{k+1↓1}` is
`HJO.Sweep.trainUpEnd q (k+1) 1`, as `HJO.Sweep.trainUpEnd_eq_descendingWord` records, and
`HJO.Sweep.trainUpEnd_star_cmDPlus` — the computation `HJO.Sweep.dplus_eq_neg_cmAscWord_cmDPlus`
rests on — already says `T^*_{k+1↓1}(d_+F) = τ_{k+1,k+1}(F)`. So the first step of the proof is an
existing lemma, and what is left is the second half: `τ^-_{k+1,k+1}` inverts `τ_{k+1,k+1}`
(`HJO.Sweep.qshiftNeg_qshift`), and the coefficient extraction against `Exp[-y_{k+1}^{-1}X]` fixes
anything free of `y_{k+1}`.

**`F ∈ V_k` is load-bearing here**, unlike in `HJO.Sweep.dplus_eq_neg_cmAscWord_cmDPlus`, where the
file drops it. It is exactly what makes `lowerCoeff` fix `F`: the extraction reads off the
coefficient of `y_{k+1}^0` and multiplies by `e_0 = 1`, so it is the identity on the elements with
no `y_{k+1}` and on nothing else. The usual phrasing of the last step — "in the expansion demanded
by `HJO.Sweep.dminus` we have `F_0 = F` and `F_j = 0` for `j ≥ 1`" — is that membership.

## References

This file proves `HJO.Sweep.dminus_trainUpEnd_star_cmDPlus`, using `HJO.Sweep.piece`,
`HJO.Sweep.cmDPlus`, `HJO.Braid.wordDownStar` and `HJO.Sweep.dminus`; A. Mellit, *Toric braids and
`(m, n)`-parking functions*, §3.
-/

@[expose] public section

namespace HJO.Sweep

section Newton

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **The coefficient extraction fixes `1`.** The unit is the monomial at the zero exponent, so the
single surviving term carries `e_0 = 1` and the erased exponent is again zero. -/
theorem lowerCoeff_one (j : ℕ) : lowerCoeff L j (1 : Total L) = 1 := by
  have h1 : (1 : Total L) = MvPolynomial.monomial (0 : ℕ →₀ ℕ) 1 := by
    rw [MvPolynomial.monomial_zero', MvPolynomial.C_1]
  have he0 : Sym.elemSymm L 0 = 1 := by rw [Sym.elemSymm]
  rw [h1, lowerCoeff_monomial]
  simp [he0]

/-- **The coefficient extraction of `d^♭_-` fixes `V_k`**: `lowerCoeff L k F = F` for `F ∈ V_k`.
Writing `F = F * 1` and passing `F` through the extraction by
`HJO.Sweep.lowerCoeff_mul_of_mem_piece` — which is allowed exactly because `F` is free of
`y_{k+1}` — leaves `HJO.Sweep.lowerCoeff_one`. -/
theorem lowerCoeff_of_mem_piece {j : ℕ} {F : Total L} (hF : F ∈ piece L j) :
    lowerCoeff L j F = F := by
  calc lowerCoeff L j F = lowerCoeff L j (F * 1) := by rw [mul_one]
    _ = F * lowerCoeff L j 1 := lowerCoeff_mul_of_mem_piece hF 1
    _ = F := by rw [lowerCoeff_one, mul_one]

/-- **The modified lowering operator is a section of the raising operator**, the lemma
`HJO.Sweep.dminus_trainUpEnd_star_cmDPlus`: for `k ≥ 0` and `F ∈ V_k`,
`d^♭_-(T^*_{k+1↓1}(d_+F)) = F`.

`HJO.Sweep.trainUpEnd_star_cmDPlus` replaces `T^*_{k+1↓1}(d_+F)` by `τ_{k+1,k+1}(F)`,
`HJO.Sweep.qshiftNeg_qshift` cancels the substitution inside `d^♭_-`, and
`HJO.Sweep.lowerCoeff_of_mem_piece` leaves `F`. -/
@[hjo "lem_vmod_dminus_section"]
theorem dminus_trainUpEnd_star_cmDPlus (q : L) (hq : q ≠ 0) {k : ℕ} {F : Total L}
    (hF : F ∈ piece L k) :
    dminus q (k + 1) (trainUpEnd q (k + 1) 1 (cmDPlus q k F)) = F := by
  rw [trainUpEnd_star_cmDPlus q hq, dminus_succ_apply, qshiftNeg_qshift,
    lowerCoeff_of_mem_piece hF]

end Newton

end HJO.Sweep
