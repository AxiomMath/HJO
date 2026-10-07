/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CMStructure.DminusSqBraid
public import HJO.CMStructure.TwistedStarMult
public import HJO.CMStructure.VmodCommutatorMod
public import HJO.CarlssonMellit.BopModified
public meta import HJO.Attr

/-! # The reduction machinery for Mellit's lowering operator

The two starred commutator relations `HJO.Sweep.dminusCM_starCommCM_braidInv` and
`HJO.Sweep.braidInv_starCommCM_dplusStar` are proved, in `HJO/CMStructure/StarConjRel1.lean` and
`HJO/CMStructure/StarConjRel2.lean`, for Carlsson and Mellit's own lowering operator `d_-` of
`HJO.Sweep.dminusCM` (pairing `F_j` with `e_{j+1}`). The commutator that
Mellit's `z_1` is built on (`HJO.Sweep.starComm`, hence `HJO.Sweep.zopOneStar`, hence
`HJO.Sweep.zop` and `HJO.Sweep.zRep`) uses instead the *modified* operator `d^♭_-` of
`HJO.Sweep.dminus` (pairing `F_j` with `e_j`), and **the
relations for one do not imply the relations for the other**: the bridge
`HJO.Sweep.dminusCM_eq_neg_dminus_auxVar_mul` expresses `d_-` in terms of `d^♭_-` *at argument*
`y_{k+1}F`, and multiplication by `y_{k+1}` is injective but not surjective on `V_{k+1}`, so a
relation known for `d_-` at every argument constrains `d^♭_-` only on the ideal `(y_{k+1})`. See
`HJO/CMStructure/BraidRepNotTotal.lean` for the proved half of that obstruction.

So the two relations have to be re-proved in Mellit's convention, and the three-stage
argument -- intertwine the twisted multiplications, shift the corners, evaluate on the
monomials in the last variables -- has to be re-run with `d^♭_-` in place of `d_-`. This file
carries the inputs of those stages that exist only for `d_-`.

## Main results

* `HJO.Sweep.dminus_twistedActionMult`, `HJO.Sweep.dminus_twistedActionMult_C` --
  `HJO.Sweep.dminusCM_twistedActionMult` for `d^♭_-`: the modified lowering operator preserves the
  twist.
* `HJO.Sweep.dminus_dminus_braidInv` -- `HJO.Sweep.dminus_dminus_braid` read in the inverted loops.

The third input of the reduction, `d^♭_-(d^♭_-(y_{k+1}^ay_{k+2}^bH)) = B_a(B_b(H))`, is already
proved as `HJO.Sweep.dminus_dminus_auxVar_pow_mul`
(`HJO/CMStructure/DminusSqBraid.lean`) -- with **no index shift and no sign**, where the
unmodified operator gives `B_{a+1}(B_{b+1}(H))`.

## Implementation notes

**Where the index shift goes.** `HJO.Sweep.dminus_auxVar_pow_mul` is `d^♭_-(y_{k+1}^iF) = B_iF`
against `HJO.Sweep.dminusCM_auxVar_pow_mul`'s `d_-(y_{k+1}^iF) = -B_{i+1}F`. Two consequences run
through everything below: the `B`-indices drop by one at each of the two applications, and the two
signs that cancelled in `HJO.Sweep.dminusCM_dminusCM_auxVar_pow_mul` are simply absent. Both
differences are uniform, which is why the later `ring`/`linear_combination` steps carry over
unchanged.

**Why `d^♭_-` preserves the twist for the same reason `d_-` does.** The only difference between the
two operators is which coefficient extraction follows `τ^-_{k+1,k+1}`, and both extractions are
`V_k`-linear -- `HJO.Sweep.lowerCoeff_mul_of_mem_piece` against
`HJO.Sweep.lowerCoeffShift_mul_of_mem_piece`. The substitution half
(`HJO.Sweep.qshiftNeg_twistedMult`) is shared outright, so the proof is the same four rewrites.

## References

The analogues proved here are those of `HJO.Sweep.dminusCM_twistedActionMult` and
`HJO.Sweep.dminusCM_dminusCM_auxVar_pow_mul`, read at `HJO.Sweep.dminus` rather than
`HJO.Sweep.dminusCM`, and `HJO.Sweep.dminus_dminus_braid`.
-/

@[expose] public section

namespace HJO.Sweep

/-! ### The modified lowering operator preserves the twist -/

section Twist

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **`HJO.Sweep.dminusCM_twistedActionMult` for the modified operator**:
`d^♭_-(f ∗_m G) = f ∗_m d^♭_-G` for `m ≤ k` and `f ∈ V_k`, read at rank `k+1` so that no truncated
subtraction occurs.

Verbatim the proof of `HJO.Sweep.dminusCM_twistedActionMult`, with the coefficient extraction of
`HJO.Sweep.dminusCM` replaced by that of `HJO.Sweep.dminus`: the substitution lowers the rank of the
twist (`HJO.Sweep.qshiftNeg_twistedMult`) and the extraction passes `σ_{m,k}(f)` because that
element lies in `V_k`, hence is free of `y_{k+1}` (`HJO.Sweep.lowerCoeff_mul_of_mem_piece`,
`HJO.Sweep.twistedMult_mem_piece`).

`m ≤ k` is load-bearing for exactly the reason it is at the unmodified operator: at `m = k+1` the
letter `y_{k+1}` sits in the dilated block, `τ^-_{k+1,k+1}` does not remove it, and the composite
is no twisting alphabet of rank `k`. -/
theorem dminus_twistedActionMult (q u : L) {m k : ℕ} (hmk : m ≤ k) {f : Total L}
    (hf : f ∈ piece L k) (G : Total L) :
    dminus q (k + 1) (twistedActionMult L q u m (k + 1) f G)
      = twistedActionMult L q u m k f (dminus q (k + 1) G) := by
  rw [twistedActionMult_apply, twistedActionMult_apply, dminus_succ_apply, dminus_succ_apply,
    map_mul, qshiftNeg_twistedMult q u hmk,
    lowerCoeff_mul_of_mem_piece (twistedMult_mem_piece q u hmk hf)]

/-- `HJO.Sweep.dminus_twistedActionMult` at `f ∈ Λ`, which is the form the reduction reads: a
coefficient from `Λ` lies in every graded piece. -/
theorem dminus_twistedActionMult_C (q u : L) {m k : ℕ} (hmk : m ≤ k) (f : Sym.Lambda L)
    (G : Total L) :
    dminus q (k + 1) (twistedActionMult L q u m (k + 1) (MvPolynomial.C f) G)
      = twistedActionMult L q u m k (MvPolynomial.C f) (dminus q (k + 1) G) :=
  dminus_twistedActionMult q u hmk (Subalgebra.algebraMap_mem _ f) G

end Twist

/-! ### The square relation against an inverted loop -/

section Inv

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **`d^{♭2}_-T_{k-1}^{-1} = d^{♭2}_-` on `V_k`**, `HJO.Sweep.dminus_dminus_braid` read in the
inverted loops. `T_{k-1}^{-1}` is an endomorphism of `V_k`, so `HJO.Sweep.dminus_dminus_braid`
applies to `T_{k-1}^{-1}F` and `T_{k-1}T_{k-1}^{-1} = 1` finishes -- the same two lines as
`HJO.Sweep.dminusCM_dminusCM_braidInv`. -/
theorem dminus_dminus_braidInv (q : L) (hq : q ≠ 0) (m : ℕ) {F : Total L}
    (hF : F ∈ piece L (m + 2)) :
    dminus q (m + 1) (dminus q (m + 2) (braidInv q (m + 1) F))
      = dminus q (m + 1) (dminus q (m + 2) F) := by
  have hmem : braidInv q (m + 1) F ∈ piece L (m + 2) :=
    braidInv_mem_piece q (by omega) hF
  have h := dminus_dminus_braid q m hmem
  rw [braid_braidInv q hq (m + 1)] at h
  exact h.symm

end Inv

end HJO.Sweep

end
