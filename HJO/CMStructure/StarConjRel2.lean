/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CMStructure.EvalReduction
public import HJO.CMStructure.DemazureIdentities
public import HJO.CMStructure.HbTwist
public import HJO.CMStructure.StarEasy
public import HJO.CMStructure.TwistedStarMult
public import HJO.CMStructure.QShiftNegBraid
public import HJO.CarlssonMellit.ConjugationOperator
public import HJO.CarlssonMellit.NegateHsymm
public meta import HJO.Attr

/-! # The second starred commutator relation

`HJO.Sweep.braidInv_starCommCM_dplusStar`: for `k ≥ 1`, on `V_k`,
`T_1^{-1}(d^*_+d_- - d_-d^*_+)d^*_+ = q^{-1}d^*_+(d^*_+d_- - d_-d^*_+)`.

## Main results

* `HJO.Sweep.braidInv_starCommCM_dplusStar`.
* `HJO.Sweep.starConj2Left_eq_starConj2Right`: the `A` vanishes on `V_{k+1}`, which is
  the relation with the braid inverse cleared.
* `HJO.Sweep.starNegTwo_sub_braid_starNegOne`: the plethystic identity the relation reduces to, the
  vanishing of `-h_n[-X - u(q-1)(y_1+y_2)] + (T_1+q)h_n[-X - u(q-1)y_1] - qh_n[-X]`.

## Implementation notes

The proof has three stages. Multiplying by `qT_1` turns the relation into the vanishing
of `A := d^{*2}_+d_- - (T_1+q)d^*_+d_-d^*_+ + qd_-d^{*2}_+` on `V_k`; the intertwining of the
twisted multiplications and the corner shifts reduce that to `A` on the monomials `y_k^a`; and
there the three terms are plethystic substitutions into `h_{a+1}`, which cancel by
`HJO.Sweep.braid_add_q_completeHomog_twist`.

This file carries the third stage. The three substitutions are named as `𝕜`-algebra maps
`Λ → V_*`: `HJO.Sweep.negAlphabet` is `f ↦ f[-X]`, and `HJO.Sweep.starNegOne`,
`HJO.Sweep.starNegTwo` are that followed by one and by two applications of `d^*_+`, which add the
letters `u(q-1)y_1` and `u(q-1)(y_1+y_2)`. The point of naming them is that
`HJO.Sym.completeHomog_add_alphabet` applies to any three ring maps whose values
on the power sums add up, so the expansion of `h_n` over the sum of alphabets is available for these
composites without any theory of plethysm on the total space.

`d_-(y_{k+1}^a) = (-1)^ae_{a+1}` (`HJO.Sweep.dminusCM_auxVar_pow`) is `-h_{a+1}[-X]`, which is where
`negAlphabet` enters: `ω₋(h_n) = (-1)^ne_n` is `HJO.Sym.plethNegate_completeHomog`.

## References

Transcribing E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, §5.
-/

@[expose] public section

namespace HJO.Sweep

section Substitutions

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **`f ↦ f[-X]`**, the negation of the alphabet, read in the total space: the `𝕜`-algebra map
`Λ → V_*` sending `p_r` to `-p_r`. It is the substitution the lowering operator produces, since
`d_-(y_{k+1}^a) = (-1)^ae_{a+1} = -h_{a+1}[-X]`. -/
noncomputable def negAlphabet (L : Type*) [Field L] : Sym.Lambda L →ₐ[L] Total L :=
  (IsScalarTower.toAlgHom L (Sym.Lambda L) (Total L)).comp (Sym.plethNegate L)

omit [Algebra ℚ L] in
/-- The negated alphabet is a `Λ`-scalar of the total space: `f[-X] = C(ω₋f)`. This is what makes
the braid operator, which is `Λ`-linear, pass it. -/
theorem negAlphabet_eq_C (f : Sym.Lambda L) :
    negAlphabet L f = MvPolynomial.C (Sym.plethNegate L f) := rfl

omit [Algebra ℚ L] in
theorem negAlphabet_powerSum (r : ℕ) :
    negAlphabet L (Sym.powerSum L r) = -MvPolynomial.C (Sym.powerSum L r) := by
  rw [negAlphabet, AlgHom.comp_apply, Sym.plethNegate_powerSum, map_neg]
  rfl

/-- **`h_n[-X] = (-1)^ne_n`**, `HJO.Sym.plethNegate_completeHomog` read in the total space. -/
theorem negAlphabet_completeHomog (n : ℕ) :
    negAlphabet L (Sym.completeHomog L n)
      = (-1 : Total L) ^ n * MvPolynomial.C (Sym.elemSymm L n) := by
  rw [negAlphabet_eq_C, Sym.plethNegate_completeHomog, map_mul, map_pow, map_neg, map_one]

/-- **`f ↦ f[-X + u(1-q)y_1]`**: the negated alphabet followed by one starred raising, which adds
the letter `u(q-1)y_1`. -/
noncomputable def starNegOne (q u : L) (k : ℕ) : Sym.Lambda L →ₐ[L] Total L :=
  (dplusStarAlg q u k).comp (negAlphabet L)

/-- **`f ↦ f[-X + u(1-q)(y_1+y_2)]`**: the negated alphabet followed by two starred raisings, the
second of which carries the letter added by the first from `y_1` to `y_2`. -/
noncomputable def starNegTwo (q u : L) (k : ℕ) : Sym.Lambda L →ₐ[L] Total L :=
  (dplusStarAlg q u (k + 1)).comp ((dplusStarAlg q u k).comp (negAlphabet L))

omit [Algebra ℚ L] in
/-- The power sums of the one-letter substitution: `-p_r` plus the letter `u(1-q)y_1` of
`HJO.Sweep.twistLetter`. -/
theorem starNegOne_powerSum (q u : L) (k : ℕ) {r : ℕ} (hr : 0 < r) :
    starNegOne q u k (Sym.powerSum L r)
      = negAlphabet L (Sym.powerSum L r) + twistLetter u q 1 r := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  rw [starNegOne, AlgHom.comp_apply, negAlphabet_powerSum, map_neg, dplusStarAlg_C_powerSum,
    twistLetter]
  simp only [scal_mul, scal_sub, scal_one, scal_pow, mul_pow]
  ring

omit [Algebra ℚ L] in
/-- The power sums of the two-letter substitution: `-p_r` plus the alphabet `u(1-q)(y_1+y_2)` of
`HJO.Sweep.twistLetterPair`. The second raising fixes the scalars, carries `y_1` to `y_2` — which is
`HJO.Sweep.dplusStarAlg_X_of_lt` at `0 < k+1` — and adds a further copy of the letter at `y_1`. -/
theorem starNegTwo_powerSum (q u : L) (k : ℕ) {r : ℕ} (hr : 0 < r) :
    starNegTwo q u k (Sym.powerSum L r)
      = negAlphabet L (Sym.powerSum L r) + twistLetterPair u q r := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  have hy : dplusStarAlg q u (k + 1) (auxVar 1 : Total L) = auxVar 2 := by
    rw [show (auxVar 1 : Total L) = MvPolynomial.X 0 from by rw [auxVar],
      dplusStarAlg_X_of_lt q u (show 0 < k + 1 by omega),
      show (MvPolynomial.X (0 + 1) : Total L) = auxVar 2 from by rw [auxVar]]
  rw [starNegTwo, AlgHom.comp_apply, AlgHom.comp_apply, negAlphabet_powerSum, map_neg,
    dplusStarAlg_C_powerSum, map_neg, map_add, dplusStarAlg_C_powerSum, map_mul, map_pow, map_mul,
    dplusStarAlg_scal, dplusStarAlg_scal, hy, twistLetterPair]
  simp only [scal_mul, scal_sub, scal_one, scal_pow, mul_pow]
  ring

/-- **The one-letter expansion**: `h_n[-X + u(1-q)y_1] = ∑_s h_{n-s}[-X]h_s[u(1-q)y_1]`. -/
theorem starNegOne_completeHomog (q u : L) (k n : ℕ) :
    starNegOne q u k (Sym.completeHomog L n)
      = ∑ s ∈ Finset.range (n + 1), negAlphabet L (Sym.completeHomog L (n - s))
          * alphabetEval (twistLetter u q 1) (Sym.completeHomog L s) :=
  Sym.completeHomog_add_alphabet (negAlphabet L) (alphabetEval (twistLetter u q 1))
    (starNegOne q u k)
    (fun j hj => by rw [starNegOne_powerSum q u k hj, alphabetEval_powerSum _ hj]) n

/-- **The two-letter expansion**:
`h_n[-X + u(1-q)(y_1+y_2)] = ∑_s h_{n-s}[-X] h_s[u(1-q)(y_1+y_2)]`. -/
theorem starNegTwo_completeHomog (q u : L) (k n : ℕ) :
    starNegTwo q u k (Sym.completeHomog L n)
      = ∑ s ∈ Finset.range (n + 1), negAlphabet L (Sym.completeHomog L (n - s))
          * alphabetEval (twistLetterPair u q) (Sym.completeHomog L s) :=
  Sym.completeHomog_add_alphabet (negAlphabet L) (alphabetEval (twistLetterPair u q))
    (starNegTwo q u k)
    (fun j hj => by rw [starNegTwo_powerSum q u k hj, alphabetEval_powerSum _ hj]) n

/-- **The vanishing the relation reduces to.** For every `n`,

`h_n[-X - u(q-1)(y_1+y_2)] - (T_1+q)h_n[-X - u(q-1)y_1] + qh_n[-X] = 0`.

Both plethysms expand over the sum of alphabets into `∑_s h_{n-s}[-X]` times a substitution into
`h_s`, and `T_1` is linear over `Λ`, so the `s`-th coefficient is
`h_s[u(1-q)(y_1+y_2)] - (T_1+q)h_s[u(1-q)y_1]`, which vanishes for `s ≥ 1` by
`HJO.Sweep.braid_add_q_completeHomog_twist`. At `s = 0` both substitutions give `1` and the
coefficient is `1 - (1 + q) = -q`, which is what the third term cancels. -/
theorem starNegTwo_sub_braid_starNegOne (q u : L) (k k' n : ℕ) :
    starNegTwo q u k (Sym.completeHomog L n)
        - (braid q 1 (starNegOne q u k' (Sym.completeHomog L n))
            + scal q * starNegOne q u k' (Sym.completeHomog L n))
      + scal q * negAlphabet L (Sym.completeHomog L n) = 0 := by
  have hbraid : braid q 1 (starNegOne q u k' (Sym.completeHomog L n))
      = ∑ s ∈ Finset.range (n + 1), negAlphabet L (Sym.completeHomog L (n - s))
          * braid q 1 (alphabetEval (twistLetter u q 1) (Sym.completeHomog L s)) := by
    rw [starNegOne_completeHomog, map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [negAlphabet_eq_C, ← MvPolynomial.smul_eq_C_mul, LinearMap.map_smul,
      MvPolynomial.smul_eq_C_mul]
  have hterm : ∀ s ∈ Finset.range (n + 1), s ≠ 0 →
      negAlphabet L (Sym.completeHomog L (n - s))
            * alphabetEval (twistLetterPair u q) (Sym.completeHomog L s)
          - (negAlphabet L (Sym.completeHomog L (n - s))
              * braid q 1 (alphabetEval (twistLetter u q 1) (Sym.completeHomog L s))
            + scal q * (negAlphabet L (Sym.completeHomog L (n - s))
              * alphabetEval (twistLetter u q 1) (Sym.completeHomog L s)))
        = 0 := by
    intro s _ hs
    rw [← braid_add_q_completeHomog_twist q u (Nat.pos_of_ne_zero hs)]
    ring
  have hzero : negAlphabet L (Sym.completeHomog L (n - 0))
          * alphabetEval (twistLetterPair u q) (Sym.completeHomog L 0)
        - (negAlphabet L (Sym.completeHomog L (n - 0))
            * braid q 1 (alphabetEval (twistLetter u q 1) (Sym.completeHomog L 0))
          + scal q * (negAlphabet L (Sym.completeHomog L (n - 0))
            * alphabetEval (twistLetter u q 1) (Sym.completeHomog L 0)))
      = -(scal q * negAlphabet L (Sym.completeHomog L n)) := by
    rw [alphabetEval_completeHomog_zero, alphabetEval_completeHomog_zero, braid_map_one,
      Nat.sub_zero]
    ring
  rw [hbraid, starNegTwo_completeHomog, starNegOne_completeHomog, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.sum_eq_single 0 hterm (by simp),
    hzero]
  ring

end Substitutions

/-! ### The operator the relation reduces to -/

section Operators

variable {L : Type*} [Field L] [Algebra ℚ L]

omit [Algebra ℚ L] in
/-- **`d^*_+(y_i^a) = y_{i+1}^a`** for `1 ≤ i ≤ k`: the corner shift of
`HJO.Sweep.dplusStar_braidInv` peeled a whole power, at `G = 1`. -/
theorem dplusStar_auxVar_pow (q u : L) {i k : ℕ} (hi : 1 ≤ i) (hik : i ≤ k) (a : ℕ) :
    dplusStar q u k ((auxVar i : Total L) ^ a) = (auxVar (i + 1) : Total L) ^ a := by
  have h := map_auxVar_pow_mul_of_map_auxVar_mul (Φ := dplusStar q u k) (i := i)
    (S := (auxVar (i + 1) : Total L)) (dplusStar_auxVar_mul q u hi hik) a 1
  rw [mul_one, dplusStar_map_one, mul_one] at h
  exact h

/-- **`d^{*2}_+d_- + qd_-d^{*2}_+`**, the two terms of the `A` that carry no braid
operator, as an endomorphism of the total space. On `V_{k+1}` it lands in `V_{k+2}`. -/
noncomputable def starConj2Left (q u : L) (k : ℕ) : Module.End L (Total L) :=
  dplusStar q u (k + 1) * dplusStar q u k * dminusCM q (k + 1)
    + q • (dminusCM q (k + 3) * dplusStar q u (k + 2) * dplusStar q u (k + 1))

/-- **`(T_1+q)d^*_+d_-d^*_+`**, the middle term of the `A`. -/
noncomputable def starConj2Right (q u : L) (k : ℕ) : Module.End L (Total L) :=
  (braidEnd q 1 + q • (1 : Module.End L (Total L)))
    * (dplusStar q u (k + 1) * dminusCM q (k + 2) * dplusStar q u (k + 1))

theorem starConj2Left_apply (q u : L) (k : ℕ) (F : Total L) :
    starConj2Left q u k F
      = dplusStar q u (k + 1) (dplusStar q u k (dminusCM q (k + 1) F))
        + q • dminusCM q (k + 3) (dplusStar q u (k + 2) (dplusStar q u (k + 1) F)) := rfl

theorem starConj2Right_apply (q u : L) (k : ℕ) (F : Total L) :
    starConj2Right q u k F
      = braid q 1 (dplusStar q u (k + 1) (dminusCM q (k + 2) (dplusStar q u (k + 1) F)))
        + q • dplusStar q u (k + 1) (dminusCM q (k + 2) (dplusStar q u (k + 1) F)) := rfl

/-- `d_-(y_{k+1}^a) = -h_{a+1}[-X]`: the value `HJO.Sweep.dminusCM_auxVar_pow` computes, written
through `HJO.Sweep.negAlphabet` so that the plethystic identity applies to it. `ω₋(h_n) = (-1)^ne_n`
is `HJO.Sym.plethNegate_completeHomog`. -/
theorem dminusCM_auxVar_pow_eq_negAlphabet (q : L) (k a : ℕ) :
    dminusCM q (k + 1) ((auxVar (k + 1) : Total L) ^ a)
      = -negAlphabet L (Sym.completeHomog L (a + 1)) := by
  rw [dminusCM_auxVar_pow, negAlphabet_completeHomog, pow_succ]
  ring

/-- **The two operators agree on the powers of the last variable.** This is the third stage of the
proof: the three terms of `A` on `y_{k+1}^a` are the three plethystic substitutions of
`HJO.Sweep.starNegTwo_sub_braid_starNegOne`, the lowering operator producing `-h_{a+1}[-X]` at each
of the three places it occurs and the starred raisings carrying `y_{k+1}` up to `y_{k+3}`. -/
theorem starConj2Left_auxVar_pow (q u : L) (k a : ℕ) :
    starConj2Left q u k ((auxVar (k + 1) : Total L) ^ a)
      = starConj2Right q u k ((auxVar (k + 1) : Total L) ^ a) := by
  have hq : ∀ x : Total L, q • x = scal q * x := by
    intro x
    rw [scal_eq_algebraMap, Algebra.smul_def]
  have hs1 : dplusStar q u (k + 1) ((auxVar (k + 1) : Total L) ^ a)
      = (auxVar (k + 2) : Total L) ^ a := dplusStar_auxVar_pow q u (by omega) (le_refl _) a
  have hs2 : dplusStar q u (k + 2) ((auxVar (k + 2) : Total L) ^ a)
      = (auxVar (k + 3) : Total L) ^ a := dplusStar_auxVar_pow q u (by omega) (le_refl _) a
  have hd1 := dminusCM_auxVar_pow_eq_negAlphabet (L := L) q k a
  have hd2 := dminusCM_auxVar_pow_eq_negAlphabet (L := L) q (k + 1) a
  have hd3 := dminusCM_auxVar_pow_eq_negAlphabet (L := L) q (k + 2) a
  have htwo : dplusStar q u (k + 1) (dplusStar q u k
        (-negAlphabet L (Sym.completeHomog L (a + 1))))
      = -starNegTwo q u k (Sym.completeHomog L (a + 1)) := by
    rw [starNegTwo, AlgHom.comp_apply, AlgHom.comp_apply, ← dplusStarAlg_eq_dplusStar,
      ← dplusStarAlg_eq_dplusStar, map_neg, map_neg]
  have hone : dplusStar q u (k + 1) (-negAlphabet L (Sym.completeHomog L (a + 1)))
      = -starNegOne q u (k + 1) (Sym.completeHomog L (a + 1)) := by
    rw [starNegOne, AlgHom.comp_apply, ← dplusStarAlg_eq_dplusStar, map_neg]
  have hkey := starNegTwo_sub_braid_starNegOne (L := L) q u k (k + 1) (a + 1)
  rw [starConj2Left_apply, starConj2Right_apply, hs1, hs2, hd1, hd2, hd3, htwo, hone, map_neg,
    hq, hq]
  linear_combination -hkey

/-! ### The hypotheses of the reduction -/

/-- **The corner shifts.** Both operators carry `y_i` to `y_{i+2}` for `1 ≤ i ≤ k`, two starred
raisings shifting the index twice and the lowering operator not at all. -/
theorem starConj2Left_auxVar_mul (q u : L) {i k : ℕ} (hi : 1 ≤ i) (hik : i ≤ k) (G : Total L) :
    starConj2Left q u k ((auxVar i : Total L) * G)
      = auxVar (i + 2) * starConj2Left q u k G := by
  have hi2 : i + 1 + 1 = i + 2 := by omega
  have hk3 : k + 3 = k + 2 + 1 := by omega
  rw [starConj2Left_apply, starConj2Left_apply, dminusCM_auxVar_mul q hi hik,
    dplusStar_auxVar_mul q u hi hik,
    dplusStar_auxVar_mul q u (by omega : 1 ≤ i + 1) (by omega : i + 1 ≤ k + 1),
    dplusStar_auxVar_mul q u hi (by omega : i ≤ k + 1),
    dplusStar_auxVar_mul q u (by omega : 1 ≤ i + 1) (by omega : i + 1 ≤ k + 2), hi2, hk3,
    dminusCM_auxVar_mul q (by omega : 1 ≤ i + 2) (by omega : i + 2 ≤ k + 2), mul_add,
    mul_smul_comm]

/-- The corner shifts for the braid term. `T_1` passes `y_{i+2}` because `s_1` fixes it, `i + 2`
being at least `3`. -/
theorem starConj2Right_auxVar_mul (q u : L) {i k : ℕ} (hi : 1 ≤ i) (hik : i ≤ k) (G : Total L) :
    starConj2Right q u k ((auxVar i : Total L) * G)
      = auxVar (i + 2) * starConj2Right q u k G := by
  have hi2 : i + 1 + 1 = i + 2 := by omega
  have hsw : swapAux L 1 (auxVar (i + 2) : Total L) = auxVar (i + 2) :=
    swapAux_auxVar_of_ne (by omega) (by omega) (by omega)
  rw [starConj2Right_apply, starConj2Right_apply,
    dplusStar_auxVar_mul q u hi (by omega : i ≤ k + 1),
    dminusCM_auxVar_mul q (by omega : 1 ≤ i + 1) (by omega : i + 1 ≤ k + 1),
    dplusStar_auxVar_mul q u (by omega : 1 ≤ i + 1) (by omega : i + 1 ≤ k + 1), hi2,
    braid_mul_of_swapAux_eq q hsw, mul_add, mul_smul_comm]

omit [Algebra ℚ L] in
/-- **`s_1` fixes the letters the twisted multiplication at `m = 2` adds**: the first two are
`u^r(y_1^r + y_2^r)`, symmetric in `y_1` and `y_2`, and the rest are `y_i^r` with `i ≥ 3`. -/
theorem swapAux_one_twistPowerSums (q u : L) (k r : ℕ) :
    swapAux L 1 (twistPowerSums q u 2 (k + 2) r) = twistPowerSums q u 2 (k + 2) r := by
  have hhead : swapAux L 1 (∑ i ∈ Finset.Icc 1 2, (auxVar i : Total L) ^ r)
      = ∑ i ∈ Finset.Icc 1 2, (auxVar i : Total L) ^ r := by
    have h12 : (∑ i ∈ Finset.Icc 1 2, (auxVar i : Total L) ^ r)
        = (auxVar 1 : Total L) ^ r + auxVar 2 ^ r := by
      rw [show Finset.Icc 1 2 = ({1, 2} : Finset ℕ) from rfl, Finset.sum_pair (by omega)]
    rw [h12, map_add, map_pow, map_pow, swapAux_auxVar_self (le_refl 1),
      swapAux_auxVar_succ (le_refl 1)]
    ring
  have htail : swapAux L 1 (∑ i ∈ Finset.Icc 3 (k + 2), (auxVar i : Total L) ^ r)
      = ∑ i ∈ Finset.Icc 3 (k + 2), (auxVar i : Total L) ^ r := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have h3 : 3 ≤ i := (Finset.mem_Icc.1 hi).1
    rw [map_pow, swapAux_auxVar_of_ne (by omega) (by omega) (by omega)]
  rw [twistPowerSums, map_mul, swapAux_scal, map_add, map_mul, swapAux_scal, hhead, htail]

omit [Algebra ℚ L] in
/-- **`s_1` fixes the twisted multiplier at `m = 2`.** The multiplier is the alphabet shift by the
letters above applied to `C c`, and `s_1` fixes `C c` and each letter. -/
theorem swapAux_one_twistedMult_C (q u : L) (k : ℕ) (c : Sym.Lambda L) :
    swapAux L 1 (twistedMult q u 2 (k + 2) (MvPolynomial.C c))
      = twistedMult q u 2 (k + 2) (MvPolynomial.C c) := by
  induction c using MvPolynomial.induction_on with
  | C x =>
    rw [show (MvPolynomial.C (MvPolynomial.C x : Sym.Lambda L) : Total L) = scal x from rfl,
      twistedMult, alphabetShift_scal, swapAux_scal]
  | add p r hp hr => rw [MvPolynomial.C_add, map_add, map_add, hp, hr]
  | mul_X p j hp =>
    have hpsj : (MvPolynomial.X j : Sym.Lambda L) = Sym.powerSum L (j + 1) := by
      rw [Sym.powerSum, Nat.add_sub_cancel]
    rw [MvPolynomial.C_mul, map_mul, map_mul, hp, hpsj, twistedMult, alphabetShift_powerSum,
      map_add, swapAux_C, swapAux_one_twistPowerSums]

/-- **The intertwining of the twisted multiplications for the braid-free terms.** Each application
of `d_-` leaves the index `m` alone and lowers `k`, each application of `d^*_+` raises both, so both
terms carry `∗_{0,k+1}` to `∗_{2,k+2}`. -/
theorem starConj2Left_twist_mul (q u : L) (k : ℕ) (c : Sym.Lambda L) (G : Total L) :
    starConj2Left q u k (twist L q (k + 1) c * G)
      = twistedMult q u 2 (k + 2) (MvPolynomial.C c) * starConj2Left q u k G := by
  have hc : (twist L q (k + 1) c : Total L) * G
      = twistedActionMult L q u 0 (k + 1) (MvPolynomial.C c) G := by
    rw [twistedActionMult_apply, twistedMult_C]
  have hk3 : k + 3 = k + 2 + 1 := by omega
  rw [starConj2Left_apply, starConj2Left_apply, hc,
    dminusCM_twistedActionMult_C q u (Nat.zero_le k) c G,
    dplusStar_twistedActionMult q u (Nat.zero_le k) c _,
    dplusStar_twistedActionMult q u (by omega : 1 ≤ k + 1) c _,
    dplusStar_twistedActionMult q u (by omega : 0 ≤ k + 1) c _,
    dplusStar_twistedActionMult q u (by omega : 1 ≤ k + 2) c _, hk3,
    dminusCM_twistedActionMult_C q u (by omega : 2 ≤ k + 2) c _,
    twistedActionMult_apply, twistedActionMult_apply, mul_add, mul_smul_comm]

/-- The intertwining for the braid term: the same chain, followed by `T_1` passing the multiplier,
which `HJO.Sweep.swapAux_one_twistedMult_C` says `s_1` fixes. -/
theorem starConj2Right_twist_mul (q u : L) (k : ℕ) (c : Sym.Lambda L) (G : Total L) :
    starConj2Right q u k (twist L q (k + 1) c * G)
      = twistedMult q u 2 (k + 2) (MvPolynomial.C c) * starConj2Right q u k G := by
  have hc : (twist L q (k + 1) c : Total L) * G
      = twistedActionMult L q u 0 (k + 1) (MvPolynomial.C c) G := by
    rw [twistedActionMult_apply, twistedMult_C]
  rw [starConj2Right_apply, starConj2Right_apply, hc,
    dplusStar_twistedActionMult q u (by omega : 0 ≤ k + 1) c G,
    dminusCM_twistedActionMult_C q u (by omega : 1 ≤ k + 1) c _,
    dplusStar_twistedActionMult q u (by omega : 1 ≤ k + 1) c _, twistedActionMult_apply]
  simp only [show (1 : ℕ) + 1 = 2 from rfl, show k + 1 + 1 = k + 2 from by omega]
  rw [braid_mul_of_swapAux_eq q (swapAux_one_twistedMult_C q u k c), mul_add, mul_smul_comm]

/-- **The `A` vanishes on `V_{k+1}`.** The two halves agree on every `F ∈ V_{k+1}`: they
intertwine the twisted multiplications and shift the corners identically
(`HJO.Sweep.starConj2Left_twist_mul`, `HJO.Sweep.starConj2Right_twist_mul`,
`HJO.Sweep.starConj2Left_auxVar_mul`, `HJO.Sweep.starConj2Right_auxVar_mul`), so by
`HJO.Sweep.eq_of_agree_auxVar_pow` it is enough that they agree on the powers of `y_{k+1}`, which is
`HJO.Sweep.starConj2Left_auxVar_pow`. -/
theorem starConj2Left_eq_starConj2Right (q u : L) {k : ℕ} {F : Total L}
    (hF : F ∈ piece L (k + 1)) : starConj2Left q u k F = starConj2Right q u k F :=
  eq_of_agree_auxVar_pow q u (T := fun c => twistedMult q u 2 (k + 2) (MvPolynomial.C c))
    (S := fun i => auxVar (i + 2)) (starConj2Left_twist_mul q u k)
    (starConj2Right_twist_mul q u k)
    (fun _ hi hik G => starConj2Left_auxVar_mul q u hi hik G)
    (fun _ hi hik G => starConj2Right_auxVar_mul q u hi hik G)
    (starConj2Left_auxVar_pow q u k) hF

/-! ### The relation -/

/-- **The second starred commutator relation.** For `k ≥ 1`, on `V_k`,

`T_1^{-1}(d^*_+d_- - d_-d^*_+)d^*_+ = q^{-1}d^*_+(d^*_+d_- - d_-d^*_+)`,

read at `k = m + 1`, so that the hypothesis `k ≥ 1` is carried by the shape of the index and not by
an inequality. The operators are `HJO.Sweep.dplusStar`, `HJO.Sweep.dminusCM` and
`HJO.Sweep.braidInv` (`HJO.Sweep.braid`), each at the level its argument lives at: `d^*_+` carries
`V_j` to `V_{j+1}` and `d_-` carries `V_j` to `V_{j-1}`, so the commutator on the left is read at
`V_{m+2}` and the one on the right at `V_{m+1}`.

`F ∈ V_{m+1}` is load-bearing — the reduction to the monomials `y_{m+1}^a` is a statement about
`V_{m+1}` — and so is `q ≠ 0`, which is what makes `T_1^{-1}` an inverse
(`HJO.Sweep.braid_braidInv`) and `q^{-1}` the scalar the relation names; in Lean `q⁻¹ = 0` at
`q = 0` and the identity fails there rather than failing to typecheck.

The proof is in three stages. Multiplying by `qT_1`, the relation is the vanishing
of `A = d^{*2}_+d_- - (T_1+q)d^*_+d_-d^*_+ + qd_-d^{*2}_+`, which is
`HJO.Sweep.starConj2Left_eq_starConj2Right`; the one further ingredient of this last step is that
`T_1` fixes `d^{*2}_+` of an element of `V_m` (`HJO.Sweep.dplusStar_braidInv`'s
`HJO.Sweep.swapAux_one_dplusStar_dplusStar`, at `d_-F ∈ V_m`), which is what turns
`T_1(d^{*2}_+d_-F)` back into `d^{*2}_+d_-F`. -/
@[hjo "lem_cm_star_conjrel2"]
theorem braidInv_starCommCM_dplusStar (q u : L) (hq : q ≠ 0) {k : ℕ} {F : Total L}
    (hF : F ∈ piece L (k + 1)) :
    braidInv q 1 (dplusStar q u (k + 1) (dminusCM q (k + 2) (dplusStar q u (k + 1) F))
        - dminusCM q (k + 3) (dplusStar q u (k + 2) (dplusStar q u (k + 1) F)))
      = q⁻¹ • (dplusStar q u (k + 1) (dplusStar q u k (dminusCM q (k + 1) F))
          - dplusStar q u (k + 1) (dminusCM q (k + 2) (dplusStar q u (k + 1) F))) := by
  have hA := starConj2Left_eq_starConj2Right q u hF
  rw [starConj2Left_apply, starConj2Right_apply] at hA
  set P := dplusStar q u (k + 1) (dplusStar q u k (dminusCM q (k + 1) F)) with hPdef
  set Q := dplusStar q u (k + 1) (dminusCM q (k + 2) (dplusStar q u (k + 1) F)) with hQdef
  set R := dminusCM q (k + 3) (dplusStar q u (k + 2) (dplusStar q u (k + 1) F)) with hRdef
  have hPfix : braid q 1 P = P :=
    braid_of_swapAux_eq q (swapAux_one_dplusStar_dplusStar q u (dminusCM_mem_piece q k hF))
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
