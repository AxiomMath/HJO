/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CMStructure.MellitLowerTwist
public import HJO.CMStructure.StarConjRel2
public meta import HJO.Attr

/-! # The second starred commutator relation in Mellit's convention

The `extra_raise` relation of `HJO.Sweep.IsDpaOperators` for the triple `(T_i^{-1}, d^♭_-, d^*_+)`:
for `k ≥ 1`, on `V_k`,

`T_1^{-1}(d^*_+d^♭_- - d^♭_-d^*_+)d^*_+ = q^{-1}d^*_+(d^*_+d^♭_- - d^♭_-d^*_+)`.

This is `HJO.Sweep.braidInv_starCommCM_dplusStar` with the lowering operator `HJO.Sweep.dminus`
(pairing `F_j` with `e_j`) in place of `HJO.Sweep.dminusCM` (pairing `F_j` with `e_{j+1}`). The
commutator here is the one `HJO.Sweep.starComm` names, hence the one `HJO.Sweep.zopOneStar`,
`HJO.Sweep.zop` and `HJO.Sweep.zRep` are built on; the starred action
`HJO.Sweep.exists_isDpaAction_star` is all-Carlsson--Mellit and realises its loop through
`HJO.Sweep.starCommCM` instead.

**It is not a corollary of `HJO.Sweep.braidInv_starCommCM_dplusStar`, and that is proved, not
stylistic.** The bridge `HJO.Sweep.dminusCM_eq_neg_dminus_auxVar_mul` reads
`d_-F = -d^♭_-(y_{k+1}F)`, so substituting it into the unmodified relation yields this one only *at
argument* `y_{k+1}F`; multiplication by `y_{k+1}` is injective but not surjective on `V_{k+1}`, so
what transports is the relation on the ideal `(y_{k+1})` and not on `V_{k+1}`. See
`HJO/CMStructure/BraidRepNotTotal.lean`.

## Main results

* `HJO.Sweep.braidInv_starComm_dplusStar` -- the relation.
* `HJO.Sweep.mellitConj2Left_eq_mellitConj2Right` -- the `A` vanishes on `V_{k+1}`,
  which is the relation with the braid inverse cleared.

## Implementation notes

**What changes and what does not.** The three-stage proof survives the change of
convention unaltered in its first two stages: the intertwining of the twisted multiplications is
`HJO.Sweep.dminus_twistedActionMult_C` in place of `HJO.Sweep.dminusCM_twistedActionMult_C`, and the
corner shifts are `HJO.Sweep.dminus_auxVar_mul` in place of `HJO.Sweep.dminusCM_auxVar_mul` -- the
two modified lemmas having the same shape as the two unmodified ones, because the only difference
between the operators is which `V_k`-linear coefficient extraction follows `τ^-_{k+1,k+1}`.

**The third stage is where the convention is visible, and it is where the change costs least.** The
evaluation reads `d^♭_-(y_{k+1}^a) = (-1)^ae_a = h_a[-X]` (`HJO.Sweep.dminus_auxVar_pow`) against
`d_-(y_{k+1}^a) = (-1)^ae_{a+1} = -h_{a+1}[-X]`, so the three occurrences of the lowering operator
each produce `+h_a[-X]` where they produced `-h_{a+1}[-X]`. Both the index shift and the sign are
uniform across the three terms, and the plethystic identity they cancel by --
`HJO.Sweep.starNegTwo_sub_braid_starNegOne`, which holds for every `n` -- is homogeneous. So the
same identity closes the computation, read at `n = a` rather than `n = a + 1` and added rather than
subtracted.

`q ≠ 0` is what makes `T_1^{-1}` an inverse and `q^{-1}` the scalar named; in Lean `q⁻¹ = 0` at
`q = 0` and the identity fails there rather than failing to typecheck. `F ∈ V_{k+1}` is
load-bearing: the reduction to the monomials `y_{k+1}^a` is a statement about `V_{k+1}`. No
`q + 1 ≠ 0` appears -- unlike the first relation, this one needs no division by `1 + q`.

## References

Lemma `HJO.Sweep.braidInv_starCommCM_dplusStar`, read at `HJO.Sweep.dminus` rather than
`HJO.Sweep.dminusCM`, and the remark on Mellit's `z`-relations at
`HJO.Sweep.braidRepRespects_mellit`. Transcribing E. Carlsson and A. Mellit, *A proof of the shuffle
conjecture*, §5, in A. Mellit's convention for the lowering operator.
-/

@[expose] public section

namespace HJO.Sweep

section Operators

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **`d^{*2}_+d^♭_- + qd^♭_-d^{*2}_+`**, the two terms of the `A` that carry no braid
operator, in Mellit's convention. On `V_{k+1}` it lands in `V_{k+2}`. -/
noncomputable def mellitConj2Left (q u : L) (k : ℕ) : Module.End L (Total L) :=
  dplusStar q u (k + 1) * dplusStar q u k * dminus q (k + 1)
    + q • (dminus q (k + 3) * dplusStar q u (k + 2) * dplusStar q u (k + 1))

/-- **`(T_1+q)d^*_+d^♭_-d^*_+`**, the middle term of the `A`, in Mellit's convention. -/
noncomputable def mellitConj2Right (q u : L) (k : ℕ) : Module.End L (Total L) :=
  (braidEnd q 1 + q • (1 : Module.End L (Total L)))
    * (dplusStar q u (k + 1) * dminus q (k + 2) * dplusStar q u (k + 1))

theorem mellitConj2Left_apply (q u : L) (k : ℕ) (F : Total L) :
    mellitConj2Left q u k F
      = dplusStar q u (k + 1) (dplusStar q u k (dminus q (k + 1) F))
        + q • dminus q (k + 3) (dplusStar q u (k + 2) (dplusStar q u (k + 1) F)) := rfl

theorem mellitConj2Right_apply (q u : L) (k : ℕ) (F : Total L) :
    mellitConj2Right q u k F
      = braid q 1 (dplusStar q u (k + 1) (dminus q (k + 2) (dplusStar q u (k + 1) F)))
        + q • dplusStar q u (k + 1) (dminus q (k + 2) (dplusStar q u (k + 1) F)) := rfl

/-- `d^♭_-(y_{k+1}^a) = h_a[-X]`: the value `HJO.Sweep.dminus_auxVar_pow` computes, written through
`HJO.Sweep.negAlphabet` so that the plethystic identity applies to it. `ω₋(h_n) = (-1)^ne_n` is
`HJO.Sym.plethNegate_completeHomog`.

**This is the one place the convention enters the evaluation.** The unmodified operator gives
`-h_{a+1}[-X]` (`HJO.Sweep.dminusCM_auxVar_pow_eq_negAlphabet`); here there is no index shift and no
sign. -/
theorem dminus_auxVar_pow_eq_negAlphabet (q : L) (k a : ℕ) :
    dminus q (k + 1) ((auxVar (k + 1) : Total L) ^ a)
      = negAlphabet L (Sym.completeHomog L a) := by
  rw [dminus_auxVar_pow, negAlphabet_completeHomog]

/-- **The two operators agree on the powers of the last variable.** The third stage of the
proof, in Mellit's convention: the three terms of `A` on `y_{k+1}^a` are the three
plethystic substitutions of `HJO.Sweep.starNegTwo_sub_braid_starNegOne` read at `n = a`, the
lowering operator producing `+h_a[-X]` at each of the three places it occurs and the starred
raisings carrying `y_{k+1}` up to `y_{k+3}`. -/
theorem mellitConj2Left_auxVar_pow (q u : L) (k a : ℕ) :
    mellitConj2Left q u k ((auxVar (k + 1) : Total L) ^ a)
      = mellitConj2Right q u k ((auxVar (k + 1) : Total L) ^ a) := by
  have hq : ∀ x : Total L, q • x = scal q * x := by
    intro x
    rw [scal_eq_algebraMap, Algebra.smul_def]
  have hs1 : dplusStar q u (k + 1) ((auxVar (k + 1) : Total L) ^ a)
      = (auxVar (k + 2) : Total L) ^ a := dplusStar_auxVar_pow q u (by omega) (le_refl _) a
  have hs2 : dplusStar q u (k + 2) ((auxVar (k + 2) : Total L) ^ a)
      = (auxVar (k + 3) : Total L) ^ a := dplusStar_auxVar_pow q u (by omega) (le_refl _) a
  have hd1 := dminus_auxVar_pow_eq_negAlphabet (L := L) q k a
  have hd2 := dminus_auxVar_pow_eq_negAlphabet (L := L) q (k + 1) a
  have hd3 := dminus_auxVar_pow_eq_negAlphabet (L := L) q (k + 2) a
  have htwo : dplusStar q u (k + 1) (dplusStar q u k (negAlphabet L (Sym.completeHomog L a)))
      = starNegTwo q u k (Sym.completeHomog L a) := by
    rw [starNegTwo, AlgHom.comp_apply, AlgHom.comp_apply, ← dplusStarAlg_eq_dplusStar,
      ← dplusStarAlg_eq_dplusStar]
  have hone : dplusStar q u (k + 1) (negAlphabet L (Sym.completeHomog L a))
      = starNegOne q u (k + 1) (Sym.completeHomog L a) := by
    rw [starNegOne, AlgHom.comp_apply, ← dplusStarAlg_eq_dplusStar]
  have hkey := starNegTwo_sub_braid_starNegOne (L := L) q u k (k + 1) a
  rw [mellitConj2Left_apply, mellitConj2Right_apply, hs1, hs2, hd1, hd2, hd3, htwo, hone, hq, hq]
  linear_combination hkey

/-! ### The hypotheses of the reduction -/

/-- **The corner shifts.** Both operators carry `y_i` to `y_{i+2}` for `1 ≤ i ≤ k`, two starred
raisings shifting the index twice and the lowering operator not at all. -/
theorem mellitConj2Left_auxVar_mul (q u : L) {i k : ℕ} (hi : 1 ≤ i) (hik : i ≤ k) (G : Total L) :
    mellitConj2Left q u k ((auxVar i : Total L) * G)
      = auxVar (i + 2) * mellitConj2Left q u k G := by
  have hi2 : i + 1 + 1 = i + 2 := by omega
  have hk3 : k + 3 = k + 2 + 1 := by omega
  rw [mellitConj2Left_apply, mellitConj2Left_apply, dminus_auxVar_mul q hi hik,
    dplusStar_auxVar_mul q u hi hik,
    dplusStar_auxVar_mul q u (by omega : 1 ≤ i + 1) (by omega : i + 1 ≤ k + 1),
    dplusStar_auxVar_mul q u hi (by omega : i ≤ k + 1),
    dplusStar_auxVar_mul q u (by omega : 1 ≤ i + 1) (by omega : i + 1 ≤ k + 2), hi2, hk3,
    dminus_auxVar_mul q (by omega : 1 ≤ i + 2) (by omega : i + 2 ≤ k + 2), mul_add,
    mul_smul_comm]

/-- The corner shifts for the braid term. `T_1` passes `y_{i+2}` because `s_1` fixes it, `i + 2`
being at least `3`. -/
theorem mellitConj2Right_auxVar_mul (q u : L) {i k : ℕ} (hi : 1 ≤ i) (hik : i ≤ k) (G : Total L) :
    mellitConj2Right q u k ((auxVar i : Total L) * G)
      = auxVar (i + 2) * mellitConj2Right q u k G := by
  have hi2 : i + 1 + 1 = i + 2 := by omega
  have hsw : swapAux L 1 (auxVar (i + 2) : Total L) = auxVar (i + 2) :=
    swapAux_auxVar_of_ne (by omega) (by omega) (by omega)
  rw [mellitConj2Right_apply, mellitConj2Right_apply,
    dplusStar_auxVar_mul q u hi (by omega : i ≤ k + 1),
    dminus_auxVar_mul q (by omega : 1 ≤ i + 1) (by omega : i + 1 ≤ k + 1),
    dplusStar_auxVar_mul q u (by omega : 1 ≤ i + 1) (by omega : i + 1 ≤ k + 1), hi2,
    braid_mul_of_swapAux_eq q hsw, mul_add, mul_smul_comm]

/-- **The intertwining of the twisted multiplications for the braid-free terms.** Each application
of `d^♭_-` leaves the index `m` alone and lowers `k`, each application of `d^*_+` raises both, so
both terms carry `∗_{0,k+1}` to `∗_{2,k+2}`. -/
theorem mellitConj2Left_twist_mul (q u : L) (k : ℕ) (c : Sym.Lambda L) (G : Total L) :
    mellitConj2Left q u k (twist L q (k + 1) c * G)
      = twistedMult q u 2 (k + 2) (MvPolynomial.C c) * mellitConj2Left q u k G := by
  have hc : (twist L q (k + 1) c : Total L) * G
      = twistedActionMult L q u 0 (k + 1) (MvPolynomial.C c) G := by
    rw [twistedActionMult_apply, twistedMult_C]
  have hk3 : k + 3 = k + 2 + 1 := by omega
  rw [mellitConj2Left_apply, mellitConj2Left_apply, hc,
    dminus_twistedActionMult_C q u (Nat.zero_le k) c G,
    dplusStar_twistedActionMult q u (Nat.zero_le k) c _,
    dplusStar_twistedActionMult q u (by omega : 1 ≤ k + 1) c _,
    dplusStar_twistedActionMult q u (by omega : 0 ≤ k + 1) c _,
    dplusStar_twistedActionMult q u (by omega : 1 ≤ k + 2) c _, hk3,
    dminus_twistedActionMult_C q u (by omega : 2 ≤ k + 2) c _,
    twistedActionMult_apply, twistedActionMult_apply, mul_add, mul_smul_comm]

/-- The intertwining for the braid term: the same chain, followed by `T_1` passing the multiplier,
which `HJO.Sweep.swapAux_one_twistedMult_C` says `s_1` fixes. -/
theorem mellitConj2Right_twist_mul (q u : L) (k : ℕ) (c : Sym.Lambda L) (G : Total L) :
    mellitConj2Right q u k (twist L q (k + 1) c * G)
      = twistedMult q u 2 (k + 2) (MvPolynomial.C c) * mellitConj2Right q u k G := by
  have hc : (twist L q (k + 1) c : Total L) * G
      = twistedActionMult L q u 0 (k + 1) (MvPolynomial.C c) G := by
    rw [twistedActionMult_apply, twistedMult_C]
  rw [mellitConj2Right_apply, mellitConj2Right_apply, hc,
    dplusStar_twistedActionMult q u (by omega : 0 ≤ k + 1) c G,
    dminus_twistedActionMult_C q u (by omega : 1 ≤ k + 1) c _,
    dplusStar_twistedActionMult q u (by omega : 1 ≤ k + 1) c _, twistedActionMult_apply]
  simp only [show (1 : ℕ) + 1 = 2 from rfl, show k + 1 + 1 = k + 2 from by omega]
  rw [braid_mul_of_swapAux_eq q (swapAux_one_twistedMult_C q u k c), mul_add, mul_smul_comm]

/-- **The `A` vanishes on `V_{k+1}`**, in Mellit's convention. The two halves agree on
every `F ∈ V_{k+1}`: they intertwine the twisted multiplications and shift the corners identically,
so by `HJO.Sweep.eq_of_agree_auxVar_pow` it is enough that they agree on the powers of `y_{k+1}`,
which is `HJO.Sweep.mellitConj2Left_auxVar_pow`. -/
theorem mellitConj2Left_eq_mellitConj2Right (q u : L) {k : ℕ} {F : Total L}
    (hF : F ∈ piece L (k + 1)) : mellitConj2Left q u k F = mellitConj2Right q u k F :=
  eq_of_agree_auxVar_pow q u (T := fun c => twistedMult q u 2 (k + 2) (MvPolynomial.C c))
    (S := fun i => auxVar (i + 2)) (mellitConj2Left_twist_mul q u k)
    (mellitConj2Right_twist_mul q u k)
    (fun _ hi hik G => mellitConj2Left_auxVar_mul q u hi hik G)
    (fun _ hi hik G => mellitConj2Right_auxVar_mul q u hi hik G)
    (mellitConj2Left_auxVar_pow q u k) hF

/-! ### The relation -/

/-- **The second starred commutator relation in Mellit's convention.** For `k ≥ 1`, on `V_k`,

`T_1^{-1}(d^*_+d^♭_- - d^♭_-d^*_+)d^*_+ = q^{-1}d^*_+(d^*_+d^♭_- - d^♭_-d^*_+)`,

read at `k = m + 1`, so that the hypothesis `k ≥ 1` is carried by the shape of the index. The
operators are `HJO.Sweep.dplusStar`, `HJO.Sweep.dminus`
(Mellit's `d^♭_-`) and `HJO.Sweep.braidInv` (`HJO.Sweep.braid`), each at the
level its argument lives at, and the commutator is `HJO.Sweep.starComm`.

This is the `extra_raise` field of `HJO.Sweep.IsDpaOperators` for the triple
`(T_i^{-1}, d^♭_-, d^*_+)` at the scalar `q^{-1}`, proved in this convention rather than transported
from `HJO.Sweep.braidInv_starCommCM_dplusStar` -- see the module docstring for why no transport
exists.

The proof is in three stages. Multiplying by `qT_1`, the relation is the vanishing
of `A = d^{*2}_+d^♭_- - (T_1+q)d^*_+d^♭_-d^*_+ + qd^♭_-d^{*2}_+`, which is
`HJO.Sweep.mellitConj2Left_eq_mellitConj2Right`; the one further ingredient of this last step is
that `T_1` fixes `d^{*2}_+` of an element of `V_m` (`HJO.Sweep.dplusStar_braidInv`'s
`HJO.Sweep.swapAux_one_dplusStar_dplusStar`, at `d^♭_-F ∈ V_m`), which is what turns
`T_1(d^{*2}_+d^♭_-F)` back into `d^{*2}_+d^♭_-F`. -/
theorem braidInv_starComm_dplusStar (q u : L) (hq : q ≠ 0) {k : ℕ} {F : Total L}
    (hF : F ∈ piece L (k + 1)) :
    braidInv q 1 (dplusStar q u (k + 1) (dminus q (k + 2) (dplusStar q u (k + 1) F))
        - dminus q (k + 3) (dplusStar q u (k + 2) (dplusStar q u (k + 1) F)))
      = q⁻¹ • (dplusStar q u (k + 1) (dplusStar q u k (dminus q (k + 1) F))
          - dplusStar q u (k + 1) (dminus q (k + 2) (dplusStar q u (k + 1) F))) := by
  have hA := mellitConj2Left_eq_mellitConj2Right q u hF
  rw [mellitConj2Left_apply, mellitConj2Right_apply] at hA
  set P := dplusStar q u (k + 1) (dplusStar q u k (dminus q (k + 1) F)) with hPdef
  set Q := dplusStar q u (k + 1) (dminus q (k + 2) (dplusStar q u (k + 1) F)) with hQdef
  set R := dminus q (k + 3) (dplusStar q u (k + 2) (dplusStar q u (k + 1) F)) with hRdef
  have hmem : dminus q (k + 1) F ∈ piece L k := dminus_mem_piece q (k + 1) hF
  have hPfix : braid q 1 P = P :=
    braid_of_swapAux_eq q (swapAux_one_dplusStar_dplusStar q u hmem)
  have hsmul : ∀ (x : L) (z : Total L), x • z = scal x * z := fun x z => by
    rw [scal_eq_algebraMap, Algebra.smul_def]
  have hqq : (scal q⁻¹ : Total L) * scal q = 1 := by
    rw [← scal_mul, inv_mul_cancel₀ hq, scal_one]
  rw [hsmul q, hsmul q] at hA
  have hbraid : braid q 1 (scal q⁻¹ * (P - Q)) = Q - R := by
    have hbQ : braid q 1 Q = P + scal q * R - scal q * Q := by rw [hA]; abel
    have hcollect : P - (P + scal q * R - scal q * Q) = scal q * (Q - R) := by ring
    rw [braid_scal_mul, map_sub, hPfix, hbQ, hcollect, ← mul_assoc, hqq, one_mul]
  rw [hsmul q⁻¹, ← hbraid, braidInv_braid q hq]

end Operators

end HJO.Sweep

end
