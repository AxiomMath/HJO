/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.MellitShiftGenerators
public meta import HJO.Attr

/-! # The inverse letter substitution and the lowering operator, away from the last letter

Two lemmas say the same kind of thing about the operators built on the *last* auxiliary
variable: they leave alone whatever is built on the earlier ones.

* `HJO.Sweep.qshiftNeg_braid`: `τ^-_{k,m}(T_iF) = T_i(τ^-_{k,m}F)` when `m ∉ {i, i+1}`.
* `HJO.Sweep.dminusCM_auxVar_mul`: `d_-(y_jF) = y_j d_-F` for `j ≤ k-1`.

## The first is the mirror of an existing lemma, and the mirror was already half built

The proof of `HJO.Sweep.qshiftNeg_braid` says only "identical to the proof of
`HJO.Sweep.qshift_braid`, with `HJO.Sweep.qshiftNeg` in place of `HJO.Sweep.qshift`". That is
correct, and the hardest of its three steps is already proved:
`HJO.Sweep.qshiftNeg_swapAux` (`HJO/Shuffle/BraidRelations.lean`) is the transposition step,
proved there alongside its unstarred twin `HJO.Sweep.qshift_swapAux`. This file adds the
divided-difference step and the assembly.

## The second is the coefficient extraction being linear over the earlier variables

`d_-` of `HJO.Sweep.dminusCM` is `HJO.Sweep.dminusCM`, the composite of `τ^-_{k,k}` with the
coefficient extraction `HJO.Sweep.lowerCoeffShift` at the index of `y_k`. The substitution is a
`𝕜[y]`-algebra map, so `y_j` passes it untouched; and the extraction is linear over anything free of
`y_k`, which is `HJO.Sweep.lowerCoeffShift_mul_of_mem_piece`. So the paragraph —
"since `j ≤ k-1` the elements `y_jF_m` again lie in `V_{k-1}`, so the expansion of
`τ^-_{k,k}(y_jF)` has `m`-th coefficient `y_jF_m`" — is those two facts meeting, with no expansion
written out.

## The index conventions

Both statements are written at `k + 1` rather than at `k` with a `k - 1` in the hypothesis. The
range `1 ≤ j ≤ k-1` on `V_k` becomes `1 ≤ j ≤ k` on `V_{k+1}`, which says the same thing and
reads no truncated subtraction. `HJO.Sweep.auxVar` reads `y_0` as `y_1`, so the hypothesis `1 ≤ m`
of the first lemma and `1 ≤ j` of the second are live and are not decoration.

The first lemma is stated on the total space, so the `k ≥ 2`, `i ≤ k-1` and `m ≤ k`
carry no content and are dropped, exactly as they are on `HJO.Sweep.qshift_braid`; the index `i` is
unrestricted because `T_0` is the identity.

## Main results

* `HJO.Sweep.qshiftNeg_dividedDiff`, `HJO.Sweep.qshiftNeg_braid`.
* `HJO.Sweep.dminusCM_auxVar_mul`.

## References

E. Carlsson and A. Mellit, *A proof of the
shuffle conjecture*, §5.
-/

@[expose] public section

namespace HJO.Sweep

section Field

variable {L : Type*} [Field L]

/-- **`τ^-_{k,m}` commutes with a distant divided difference.** The same argument as
`HJO.Sweep.qshift_dividedDiff`: apply the substitution to the defining equation
`(y_{i+1} - y_i)∂_iF = F - s_iF`, which it carries to the defining equation for `τ^-_{k,m}F`
because it fixes the auxiliary variables and commutes with `s_i` by
`HJO.Sweep.qshiftNeg_swapAux`, and then use that `y_{i+1} - y_i` is a nonzerodivisor, which is
`HJO.Sweep.dividedDiff_unique`. -/
theorem qshiftNeg_dividedDiff (q : L) {i m : ℕ} (hi : 1 ≤ i) (hm : 1 ≤ m) (h1 : m ≠ i)
    (h2 : m ≠ i + 1) (F : Total L) :
    qshiftNeg q m (dividedDiff i F) = dividedDiff i (qshiftNeg q m F) := by
  refine dividedDiff_unique hi ?_
  have h := congrArg (qshiftNeg q m) (dividedDiff_spec i F)
  rw [map_mul, map_sub, qshiftNeg_auxVar, qshiftNeg_auxVar, map_sub,
    qshiftNeg_swapAux q hm h1 h2] at h
  exact h

/-- **The inverse letter substitution commutes with a distant braid operator.** This is
`HJO.Sweep.qshiftNeg_braid`: for `m ∉ {i, i+1}`, `τ^-_{k,m}(T_iF) = T_i(τ^-_{k,m}F)`.

Expanding `T_i = s_i + (q-1)y_i∂_i`, the three pieces are
`HJO.Sweep.qshiftNeg_swapAux`, `HJO.Sweep.qshiftNeg_auxVar_apply` and
`HJO.Sweep.qshiftNeg_dividedDiff`; the scalar passes by `HJO.Sweep.qshiftNeg_scal`.

Stated on the total space, so the `k ≥ 2`, `i ≤ k-1` and `m ≤ k` carry no content; `i`
is unrestricted because `T_0` is the identity, and `1 ≤ m` is live because `HJO.Sweep.auxVar` reads
`y_0` as `y_1`. -/
@[hjo "lem_cm_qshift_neg_commute_braid"]
theorem qshiftNeg_braid (q : L) {i m : ℕ} (hm : 1 ≤ m) (h1 : m ≠ i) (h2 : m ≠ i + 1)
    (F : Total L) : qshiftNeg q m (braid q i F) = braid q i (qshiftNeg q m F) := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [braid_zero_index, braid_zero_index]
  rw [braid_apply, braid_apply, map_add, map_mul, map_mul, qshiftNeg_scal,
    qshiftNeg_auxVar_apply, qshiftNeg_dividedDiff q hi hm h1 h2, qshiftNeg_swapAux q hm h1 h2]

end Field

/-! ### The lowering operator is linear over the earlier variables -/

section Newton

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **The lowering operator is linear over the earlier variables.** This is
`HJO.Sweep.dminusCM_auxVar_mul`: `d_-(y_jF) = y_j d_-F` for `1 ≤ j ≤ k-1`, with `d_-` the operator
of `HJO.Sweep.dminusCM`.

Stated on `V_{k+1}`, where the `j ≤ k-1` is `j ≤ k` and no subtraction is truncated.
`τ^-_{k,k}` is a `𝕜[y]`-algebra map so it passes `y_j`, and the coefficient extraction is linear
over `V_k`, which contains `y_j`. -/
@[hjo "lem_cm_dminus_ymult"]
theorem dminusCM_auxVar_mul (q : L) {k j : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) (F : Total L) :
    dminusCM q (k + 1) ((auxVar j : Total L) * F) = auxVar j * dminusCM q (k + 1) F := by
  rw [dminusCM_succ_apply, dminusCM_succ_apply, map_mul, qshiftNeg_auxVar_apply,
    lowerCoeffShift_mul_of_mem_piece (auxVar_mem_piece hj hjk)]

/-- `HJO.Sweep.dminusCM_auxVar_mul` in the endomorphism monoid: `d_-y_j = y_jd_-` for
`1 ≤ j ≤ k`. -/
theorem dminusCM_mul_mulLeft_auxVar (q : L) {k j : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) :
    dminusCM q (k + 1) * LinearMap.mulLeft L (auxVar j : Total L)
      = LinearMap.mulLeft L (auxVar j : Total L) * dminusCM q (k + 1) :=
  LinearMap.ext fun F => dminusCM_auxVar_mul q hj hjk F

end Newton

end HJO.Sweep
