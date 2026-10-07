/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.BopModule
public import HJO.Shuffle.CMRaising
public import HJO.Shuffle.QShiftInverse
public meta import HJO.Attr

/-! # The lowering operator twice on a monomial, and `d_-d_+` on `V_0`

Two lemmas about Carlsson and Mellit's own lowering operator `d_-` of `HJO.Sweep.dminusCM`:
applied twice to `y_{k-1}^a y_k^b H` it is the composite `B_{a+1}B_{b+1}` of two Hall--Littlewood
operators, and composed with the raising operator on `V_0` it is multiplication by `e_1`.

## Main results

* `HJO.Sweep.dminusCM_dminusCM_auxVar_pow_mul`,
  `d_-(d_-(y_{k-1}^ay_k^bH)) = B_{a+1}(B_{b+1}(H))`.
* `HJO.Sweep.dminusCM_cmDPlus_C`, `d_-(d_+f) = e_1f`.

## Implementation notes

**The first lemma is `HJO.Sweep.dminusCM_auxVar_pow_mul` applied twice, and the sign cancels.** That
lemma is `d_-(y_k^iF) = -B_{i+1}F` for `F ∈ V_{k-1}`, so each application contributes one sign and
the two cancel — which is why the statement has none. Between the two applications the operator
`B_{b+1}` has to be moved past the remaining factor `y_{k-1}^a`, and that is its `𝕜[y]`-linearity
`HJO.Sweep.bopExt_monomial_mul`: `B_r` acts on the `Λ`-coefficients only. The hypotheses `k ≥ 2` and
`H ∈ Λ ⊗ 𝕜[y_1, …, y_{k-2}]` are read here at `k + 2`, so the hypothesis is `H ∈ V_k` with no
truncated subtraction anywhere.

**The second lemma needs the two substitutions to be inverse.** At `k = 0` the braid word of `d_+`
is empty, so `d_+f = τ_{1,1}(f)`, and `d_-` begins by applying `τ^-_{1,1}`; the two cancel by
`HJO.Sweep.qshiftNeg_qshift`, leaving the bare coefficient extraction on
the constant `f`. That extraction is `Λ`-linear and sends `1` to `e_1`, which is the claim.

## References

This file proves `HJO.Sweep.dminusCM_dminusCM_auxVar_pow_mul` and `HJO.Sweep.dminusCM_cmDPlus_C`,
about the braid relations on the module and the Dyck path algebra and its involution.
-/

@[expose] public section

namespace HJO.Sweep

section DminusSquare

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **The lowering operator twice on a monomial in the last two
variables.** `d_-(d_-(y_{k-1}^ay_k^bH)) = B_{a+1}(B_{b+1}(H))` for `H ∈ Λ ⊗ 𝕜[y_1, …, y_{k-2}]`,
read at the `k` equal to `k + 2` so that the hypothesis is `H ∈ V_k`.

Each application of `HJO.Sweep.dminusCM_auxVar_pow_mul` contributes a sign and the two cancel; in
between, `B_{b+1}` passes the factor `y_{k+1}^a` because the extension of `B_r` to the module is
`𝕜[y]`-linear. -/
@[hjo "lem_cm_dminus_sq_monomial"]
theorem dminusCM_dminusCM_auxVar_pow_mul (q : L) (k a b : ℕ) {H : Total L} (hH : H ∈ piece L k) :
    dminusCM q (k + 1) (dminusCM q (k + 2)
        ((auxVar (k + 1) : Total L) ^ a * (auxVar (k + 2) : Total L) ^ b * H))
      = bopExt q ((a : ℤ) + 1) (bopExt q ((b : ℤ) + 1) H) := by
  have hH1 : (auxVar (k + 1) : Total L) ^ a * H ∈ piece L (k + 1) :=
    mul_mem (pow_mem (auxVar_mem_piece (by omega) le_rfl) a) (piece_mono (by omega) hH)
  have key := dminusCM_auxVar_pow_mul q (k + 1) b hH1
  rw [show k + 1 + 1 = k + 2 from rfl] at key
  have hmono : (auxVar (k + 1) : Total L) ^ a = MvPolynomial.monomial (Finsupp.single k a) 1 := by
    rw [auxVar, Nat.add_sub_cancel, MvPolynomial.X_pow_eq_monomial]
  have hbop : bopExt q ((b : ℤ) + 1) H ∈ piece L k := bopExt_mem_piece q _ hH
  calc dminusCM q (k + 1) (dminusCM q (k + 2)
        ((auxVar (k + 1) : Total L) ^ a * (auxVar (k + 2) : Total L) ^ b * H))
      = dminusCM q (k + 1) (dminusCM q (k + 2)
          ((auxVar (k + 2) : Total L) ^ b * ((auxVar (k + 1) : Total L) ^ a * H))) := by
        rw [show (auxVar (k + 1) : Total L) ^ a * (auxVar (k + 2) : Total L) ^ b * H
          = (auxVar (k + 2) : Total L) ^ b * ((auxVar (k + 1) : Total L) ^ a * H) from by ring]
    _ = dminusCM q (k + 1) (-bopExt q ((b : ℤ) + 1) ((auxVar (k + 1) : Total L) ^ a * H)) := by
        rw [key]
    _ = -dminusCM q (k + 1) ((auxVar (k + 1) : Total L) ^ a * bopExt q ((b : ℤ) + 1) H) := by
        rw [map_neg, hmono, bopExt_monomial_mul, ← hmono]
    _ = bopExt q ((a : ℤ) + 1) (bopExt q ((b : ℤ) + 1) H) := by
        rw [dminusCM_auxVar_pow_mul q k a hbop, neg_neg]

/-- **The first elementary function from the operators.**
`d_-(d_+f) = e_1f` for every `f ∈ Λ = V_0`.

At `k = 0` the braid word of `d_+` is empty, so `d_+f = τ_{1,1}(f)`; `d_-` applies `τ^-_{1,1}`
first, and the two substitutions are inverse, so what is left is the coefficient extraction of
`HJO.Sweep.dminusCM` on the constant `f`. That extraction is `Λ`-linear and carries `1` to `e_1`. -/
@[hjo "lem_cm_e1_dminus_dplus"]
theorem dminusCM_cmDPlus_C (q : L) (f : Sym.Lambda L) :
    dminusCM q 1 (cmDPlus q 0 (MvPolynomial.C f))
      = MvPolynomial.C (Sym.elemSymm L 1 * f) := by
  have hstep : dminusCM q 1 (cmDPlus q 0 (MvPolynomial.C f))
      = lowerCoeffShift L 0 (MvPolynomial.C f) := by
    rw [cmDPlus_zero]
    change lowerCoeffShift L 0 (qshiftNeg q 1 (qshift q 1 (MvPolynomial.C f))) = _
    rw [qshiftNeg_qshift]
  have hone : lowerCoeffShift L 0 (1 : Total L) = MvPolynomial.C (Sym.elemSymm L 1) := by
    have h := lowerCoeffShift_monomial (L := L) 0 (0 : ℕ →₀ ℕ)
    rw [MvPolynomial.monomial_zero', MvPolynomial.C_1] at h
    simpa using h
  have hC : (MvPolynomial.C f : Total L) = f • (1 : Total L) := by
    rw [MvPolynomial.smul_eq_C_mul, mul_one]
  rw [hstep, hC, map_smul, hone, MvPolynomial.smul_eq_C_mul, ← map_mul, mul_comm f]

end DminusSquare

end HJO.Sweep
