/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidValueBEResidual
public import HJO.Shuffle.MellitStarVertex
public import HJO.Shuffle.SweepRecognition
public import HJO.Shuffle.BraidCDLetterVacuum
public import HJO.Shuffle.BraidTypeBDictionary

/-! # Rule `BE` of the braid recursion: Mellit's cut-and-reconnect identity

Rule `BE` of `HJO.Mellit.braidValueColouring_sweepRecursionsFloor` relates three braids: the special
braid `B` of the lower colouring, the special braid `B''` of the type-`E` partner at the upper
level, and the special braid `B'` of the upper colouring, which has one strand more. Mellit cuts the
moving component of `B` just before and just after its passage near the puncture, leaving two common
pieces `B̃_1`, `B̃_2`, so that

`B = B̃_2 z_1ỹ_1 B̃_1`, `B'' = B̃_2 y_1z_1 B̃_1`,
`B' = φ_-(B̃_2) φ^*_+(T^*_{k↘1}B̃_1) T^*_{1↗k+1}`,

and then evaluates all three on the vacuum tower `d_+^k(1)`. The whole algebraic content is the
identity, in the double Dyck path algebra acting on `V_k`,

`z_1ỹ_1 = u y_1z_1 + uq^k d_- y_1d^*_+ T^*_{k↘1}`,

together with two intertwiners: `y_1d^*_+` intertwines `B` with `φ^*_+(B)`, and `d_-` intertwines
`φ_-(B)` with `B`. The first is `HJO.Sweep.braidRep_phiPlusStar_comp_negYOneDPlusStarPiece`. This
file proves the identity, the second intertwiner, the evaluation on the vacuum tower (Mellit's braid
rule for case `BE`, §5.3) and the bookkeeping of the prefactor, and reduces the floored `BE` clause
to the cut alone.

The identity is reduced to a bracket of `d^*_+` with `d^♭_-` against the last letter,
`d^*_+[d^♭_-, y_{k+1}] = d^♭_-(y_{k+2} - quy_1)d^*_+` on `V_{k+1}`, which on the spanning family
`y_{k+1}^m τ_{k+1,k+1}(M)`, `M ∈ V_k`, is the generating-function identity
`e_{m+1} - d^*_+(e_{m+1}) = uy_1(d^*_+(e_m) - qe_m)`, that is
`HJO.Sweep.dplusStar_C_elemSymm_succ_add`.

## Main results

* `HJO.Sweep.dplusStar_dminus_bracket` — the bracket identity on `V_{k+1}`.
* `HJO.Sweep.zopOneStar_ytilde` — Mellit's local identity
  `z_1ỹ_1 = u y_1z_1 + uq^k d_- y_1d^*_+T^*_{k↘1}` on `V_k`.
* `HJO.Sweep.braidRepMellit_braidGenZ_mul_braidYtilde` — the same identity in the braid
  representation `π_k` of `HJO.Sweep.braidRep`.
* `HJO.Sweep.dminus_zop` — `d^♭_- z_i = z_i d^♭_-` for `i ≤ k`, from `HJO.Dyck.Aq.yElt_mul_dMinus`.
* `HJO.Sweep.dminusIntertwines_toBraidMonoid` — `d^♭_-` intertwines `φ_-(B)` with `B` for every
  braid written in the letters of rank `k`.
* `HJO.Sweep.braidRepMellit_cut_dplusIter` — Mellit's braid rule for case `BE` (§5.3),
  `B d_+^k(1) = uB''d_+^k(1) + q^{-1/2}d_-B'd_+^{k+1}(1)`, for braids of the cut shape.
* `HJO.Mellit.braidValueOfData_eq_dminus_add_smul_of_cut` — rule `BE` for three braid values whose
  special braids have the cut shape and whose inversion exponents obey Mellit's two counts.
* `HJO.Mellit.braidValueColouring_sweepRecursionBEFloor_of_cut` — `SweepRecursionBEFloor` for the
  braid candidate, from the cut at every bracketed point.

## Implementation notes

Mellit's `φ_-` sends `T_i`, `y_i`, `z_i` of rank `k` to the same-named elements of rank `k + 1`. It
is used here only through a word in the letters of rank `k`, read at the two ranks by
`HJO.Braid.toBraidMonoid`; no homomorphism `𝔹_k^+(𝕋_0) → 𝔹_{k+1}^+(𝕋_0)` is constructed, and none
is needed, since the identity of rule `BE` only reads the image of one braid. Mellit's train
`T^*_{k+1↘2}` between `φ_-(B̃_2)` and `φ^*_+(B̃_1)` is absorbed into the second factor, as
`φ^*_+(T^*_{k↘1}) = T^*_{k+1↘2}`.

Mellit's parameter `t` is the `u` of this library. His normalisation `-(qt)^{-1}` of the
products `z_1ỹ_1` and `y_1z_1` is the one `HJO.Sweep.braidRep` builds into `π_k`, so it does not
appear.

## References

* [A. Mellit, *Toric braids and (m,n)-parking functions*][mellit2016], §5: the proof of rule `BE`
  (the braid rule for case `BE` in §5.3, Braid associated to a coloring) and Theorem 5.8.
* E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, §3.
-/

@[expose] public section

namespace HJO.Sweep

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- `d^♭_-(y_{k+1}^m τ_{k+1,k+1}(M)) = (-1)^m e_m M` for `M ∈ V_k`. -/
theorem dminus_auxVar_pow_mul_qshift (q : L) {k : ℕ} (m : ℕ) {M : Total L}
    (hM : M ∈ piece L k) :
    dminus q (k + 1) ((auxVar (k + 1) : Total L) ^ m * qshift q (k + 1) M)
      = (-1 : Total L) ^ m * MvPolynomial.C (Sym.elemSymm L m) * M := by
  rw [dminus_succ_apply, map_mul, map_pow, qshiftNeg_auxVar_apply, qshiftNeg_qshift, mul_comm,
    lowerCoeff_mul_of_mem_piece hM, lowerCoeff_auxVar_pow, mul_comm]

/-- `d^*_+` on `V_{k+1}` raises the index of a power of `y_{k+1}`. -/
theorem dplusStar_auxVar_pow_mul (q u : L) (k m : ℕ) (F : Total L) :
    dplusStar q u (k + 1) ((auxVar (k + 1) : Total L) ^ m * F)
      = (auxVar (k + 1 + 1) : Total L) ^ m * dplusStar q u (k + 1) F := by
  have h1 : dplusStarAlg q u (k + 1) (auxVar (k + 1) : Total L) = auxVar (k + 1 + 1) := by
    have h := dplusStar_auxVar_mul q u (i := k + 1) (k := k + 1) (by omega) le_rfl 1
    rw [mul_one, dplusStar_map_one, mul_one] at h
    exact h
  rw [← dplusStarAlg_eq_dplusStar, ← dplusStarAlg_eq_dplusStar, map_mul, map_pow, h1]

/-- The bracket identity on the generators `y_{k+1}^m τ_{k+1,k+1}(M)`, `M ∈ V_k`. -/
theorem dplusStar_dminus_bracket_of_gen (q u : L) {k : ℕ} (m : ℕ) {M : Total L}
    (hM : M ∈ piece L k) :
    dplusStar q u k (dminus q (k + 1) ((auxVar (k + 1) : Total L) *
          ((auxVar (k + 1) : Total L) ^ m * qshift q (k + 1) M)))
        - dminus q (k + 1 + 1) ((auxVar (k + 1 + 1) : Total L) *
          dplusStar q u (k + 1) ((auxVar (k + 1) : Total L) ^ m * qshift q (k + 1) M))
      = starLetter u * dplusStar q u k (dminus q (k + 1)
            ((auxVar (k + 1) : Total L) ^ m * qshift q (k + 1) M))
        - scal q * starLetter u * dminus q (k + 1 + 1)
            (dplusStar q u (k + 1) ((auxVar (k + 1) : Total L) ^ m * qshift q (k + 1) M)) := by
  have hSM : dplusStar q u k M ∈ piece L (k + 1) := dplusStar_mem_piece q u hM
  have hy : (auxVar (k + 1) : Total L) * ((auxVar (k + 1) : Total L) ^ m * qshift q (k + 1) M)
      = (auxVar (k + 1) : Total L) ^ (m + 1) * qshift q (k + 1) M := by ring
  have hS : dplusStar q u (k + 1) ((auxVar (k + 1) : Total L) ^ m * qshift q (k + 1) M)
      = (auxVar (k + 1 + 1) : Total L) ^ m * qshift q (k + 1 + 1) (dplusStar q u k M) := by
    rw [dplusStar_auxVar_pow_mul, dplusStar_qshift_of_mem_piece q u hM]
  have hyS : (auxVar (k + 1 + 1) : Total L) *
        ((auxVar (k + 1 + 1) : Total L) ^ m * qshift q (k + 1 + 1) (dplusStar q u k M))
      = (auxVar (k + 1 + 1) : Total L) ^ (m + 1) * qshift q (k + 1 + 1) (dplusStar q u k M) := by
    ring
  have hSalg : ∀ (n : ℕ), dplusStar q u k ((-1 : Total L) ^ n * MvPolynomial.C (Sym.elemSymm L n)
        * M) = (-1 : Total L) ^ n * dplusStar q u k (MvPolynomial.C (Sym.elemSymm L n))
          * dplusStar q u k M := by
    intro n
    rw [← dplusStarAlg_eq_dplusStar, ← dplusStarAlg_eq_dplusStar, ← dplusStarAlg_eq_dplusStar,
      map_mul, map_mul, map_pow, map_neg, map_one]
  have key := dplusStar_C_elemSymm_succ_add q u k m
  rw [hy, hS, hyS, dminus_auxVar_pow_mul_qshift q _ hM, dminus_auxVar_pow_mul_qshift q _ hM,
    dminus_auxVar_pow_mul_qshift q _ hSM, dminus_auxVar_pow_mul_qshift q _ hSM, hSalg, hSalg]
  linear_combination ((-1 : Total L) ^ (m + 1) * dplusStar q u k M) * key

omit [Algebra ℚ L] in
/-- A monomial of `V_{k+1}` splits off its power of `y_{k+1}`, the rest lying in `V_k`. -/
theorem monomial_eq_auxVar_pow_mul_of_lt {k : ℕ} {d : ℕ →₀ ℕ} (hd : ∀ n, d n ≠ 0 → n < k + 1)
    (c : Sym.Lambda L) :
    (MvPolynomial.monomial d c : Total L)
        = (auxVar (k + 1) : Total L) ^ d k * MvPolynomial.monomial (d.erase k) c
      ∧ (MvPolynomial.monomial (d.erase k) c : Total L) ∈ piece L k := by
  refine ⟨?_, monomial_mem_piece (fun n hn => ?_) c⟩
  · have hav : (auxVar (k + 1) : Total L) = MvPolynomial.X k := by rw [auxVar, Nat.add_sub_cancel]
    rw [hav, MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul, one_mul,
      Finsupp.single_add_erase]
  · have hnk : n ≠ k := by
      rintro rfl
      exact hn (Finsupp.erase_same)
    rw [Finsupp.erase_ne hnk] at hn
    have := hd n hn
    omega

/-- **The bracket of `d^*_+` with `d^♭_-` against the last letter.** On `V_{k+1}`,
`d^*_+[d^♭_-, y_{k+1}] = d^♭_-(y_{k+2} - quy_1)d^*_+`, written with the two `y`-letters moved
outside: `d^*_+ d^♭_- y_{k+1} - d^♭_- y_{k+2} d^*_+ = uy_1 d^*_+ d^♭_- - quy_1 d^♭_- d^*_+`. -/
theorem dplusStar_dminus_bracket (q u : L) {k : ℕ} {G : Total L} (hG : G ∈ piece L (k + 1)) :
    dplusStar q u k (dminus q (k + 1) ((auxVar (k + 1) : Total L) * G))
        - dminus q (k + 1 + 1) ((auxVar (k + 1 + 1) : Total L) * dplusStar q u (k + 1) G)
      = starLetter u * dplusStar q u k (dminus q (k + 1) G)
        - scal q * starLetter u * dminus q (k + 1 + 1) (dplusStar q u (k + 1) G) := by
  set Φ : Total L →ₗ[L] Total L :=
    dplusStar q u k ∘ₗ dminus q (k + 1) ∘ₗ LinearMap.mulLeft L (auxVar (k + 1) : Total L)
      - dminus q (k + 1 + 1) ∘ₗ LinearMap.mulLeft L (auxVar (k + 1 + 1) : Total L)
          ∘ₗ dplusStar q u (k + 1)
      - (LinearMap.mulLeft L (starLetter u) ∘ₗ dplusStar q u k ∘ₗ dminus q (k + 1)
        - LinearMap.mulLeft L (scal q * starLetter u) ∘ₗ dminus q (k + 1 + 1)
          ∘ₗ dplusStar q u (k + 1)) with hΦ
  have hΦapp : ∀ F, Φ F = (dplusStar q u k (dminus q (k + 1) ((auxVar (k + 1) : Total L) * F))
        - dminus q (k + 1 + 1) ((auxVar (k + 1 + 1) : Total L) * dplusStar q u (k + 1) F))
      - (starLetter u * dplusStar q u k (dminus q (k + 1) F)
        - scal q * starLetter u * dminus q (k + 1 + 1) (dplusStar q u (k + 1) F)) := fun F => rfl
  have hH : qshiftNeg q (k + 1) G ∈ piece L (k + 1) :=
    qshiftNeg_mem_piece q (by omega) le_rfl hG
  suffices h : Φ (qshift q (k + 1) (qshiftNeg q (k + 1) G)) = 0 by
    rw [qshift_qshiftNeg, hΦapp] at h
    exact sub_eq_zero.1 h
  set H := qshiftNeg q (k + 1) G
  rw [piece, MvPolynomial.mem_supported] at hH
  rw [MvPolynomial.as_sum H, map_sum, map_sum]
  refine Finset.sum_eq_zero fun d hd => ?_
  have hdlt : ∀ n, d n ≠ 0 → n < k + 1 := fun n hn =>
    hH (MvPolynomial.mem_vars_iff_mem_support n |>.2 ⟨d, hd, Finsupp.mem_support_iff.2 hn⟩)
  obtain ⟨hsplit, hmem⟩ := monomial_eq_auxVar_pow_mul_of_lt hdlt (MvPolynomial.coeff d H)
  rw [hsplit, map_mul, map_pow, qshift_auxVar_apply, hΦapp,
    dplusStar_dminus_bracket_of_gen q u _ hmem, sub_self]

/-- **Mellit's local identity for rule `BE`**,
`z_1ỹ_1 = u y_1z_1 + uq^k d_- y_1 d^*_+ T^*_{k↘1}` on `V_k`, at `k + 1`, with
`ỹ_1 = T_{1↗k} y_k T^*_{k↘1}` written out as an operator. -/
theorem zopOneStar_ytilde (q u : L) (hq : q ≠ 0) (hq1 : q ≠ 1) {k : ℕ} {F : Total L}
    (hF : F ∈ piece L (k + 1)) :
    zopOneStar q u (k + 1)
        (trainUpEnd q 1 (k + 1) ((auxVar (k + 1) : Total L) * trainUpEnd q (k + 1) 1 F))
      = u • ((auxVar 1 : Total L) * zopOneStar q u (k + 1) F)
        + (u * q ^ (k + 1)) • dminus q (k + 1 + 1)
            ((auxVar 1 : Total L) * dplusStar q u (k + 1) (trainUpEnd q (k + 1) 1 F)) := by
  set H := trainUpEnd q (k + 1) 1 F with hHdef
  have hH : H ∈ piece L (k + 1) := trainUpEnd_mem_piece q (by omega) (by omega) hF
  have hcancel : trainUpEnd q (k + 1) 1 (trainUpEnd q 1 (k + 1) ((auxVar (k + 1) : Total L) * H))
      = (auxVar (k + 1) : Total L) * H := by
    have h := LinearMap.congr_fun (trainUpEnd_star_mul_cmAscWord q hq k)
      ((auxVar (k + 1) : Total L) * H)
    rw [Module.End.mul_apply, Module.End.one_apply] at h
    exact h
  have hstar : dplusStar q u (k + 1) ((auxVar (k + 1) : Total L) * H)
      = (auxVar (k + 1 + 1) : Total L) * dplusStar q u (k + 1) H :=
    dplusStar_auxVar_mul q u (by omega) le_rfl H
  have hy1 : dminus q (k + 1 + 1) ((auxVar 1 : Total L) * dplusStar q u (k + 1) H)
      = (auxVar 1 : Total L) * dminus q (k + 1 + 1) (dplusStar q u (k + 1) H) :=
    dminus_auxVar_mul q (k := k + 1) (j := 1) le_rfl (by omega) _
  have hbr := dplusStar_dminus_bracket q u hH
  have hq1' : (1 : L) - q ≠ 0 := sub_ne_zero_of_ne (Ne.symm hq1)
  have hc : scal (q ^ (k + 1) / (1 - q)) * (1 - scal q) = (scal q : Total L) ^ (k + 1) := by
    rw [← scal_one, ← scal_sub, ← scal_mul, ← scal_pow, div_mul_cancel₀ _ hq1']
  simp only [zopOneStar, LinearMap.smul_apply, LinearMap.sub_apply, Module.End.mul_apply,
    Nat.add_sub_cancel]
  rw [hcancel, ← hHdef, hstar, hy1]
  rw [starLetter] at hbr
  simp only [smul_eq_scal_mul, scal_mul, scal_pow]
  linear_combination (scal (q ^ (k + 1) / (1 - q)) : Total L) * hbr
    + (scal u * (auxVar 1 : Total L) * dminus q (k + 1 + 1) (dplusStar q u (k + 1) H)) * hc

section Rep

open Braid

variable {q u r : L} {K : ℕ} {h : BraidRepRespects q u r K}

/-- `π_K(T^*_{K↘1}) = q^{(K-1)/2}T^*_{K↘1}`: the ascending train read downwards is the word in the
inverted letters `T̄_{K-1} ⋯ T̄_1`. -/
theorem representedBy_braidTrainUp_top (hK : 1 ≤ K) :
    RepresentedBy q u r K h (braidTrainUp K K 1) (r ^ (K - 1) • trainUpEnd q K 1) := by
  have hbase : RepresentedBy q u r K h
      ((((List.range' 1 (K - 1)).reverse).map (braidGenTinv K)).prod)
      ((((List.range' 1 (K - 1)).reverse).map fun i => (r : L) • braidInvEnd q i).prod) := by
    refine RepresentedBy.listProd _ fun i hi => ?_
    simp only [List.mem_reverse, List.mem_range'_1] at hi
    exact representedBy_braidGenTinv (by omega) (by omega)
  rw [show braidTrainUp K K 1 = (((List.range' 1 (K - 1)).reverse).map (braidGenTinv K)).prod from
    Braid.trainUp_top_eq_prod _ _ K hK]
  refine hbase.congr ?_
  rw [list_prod_map_smul, List.length_reverse, List.length_range',
    show trainUpEnd q K 1 = (((List.range' 1 (K - 1)).reverse).map (braidInvEnd q)).prod from
      Braid.trainUp_top_eq_prod _ _ K hK]

/-- `π_K(ỹ_1) = -T_{1↗K} y_K T^*_{K↘1}`: the two trains' half-powers of `q` cancel. -/
theorem representedBy_braidYtilde_one (hq : q ≠ 0) (hr : r * r = q) (hK : 1 ≤ K) :
    RepresentedBy q u r K h (braidYtilde K 1)
      (-(trainUpEnd q 1 K * LinearMap.mulLeft L (auxVar K : Total L) * trainUpEnd q K 1)) := by
  have hr0 : r ≠ 0 := fun h0 => hq (by rw [← hr, h0, zero_mul])
  rw [braidYtilde, braidTrainDown_self, one_mul]
  refine (((representedBy_braidTrainUp_bot hK).mul (representedBy_braidGenY_self hq hr hK)).mul
    (representedBy_braidTrainUp_top hK)).congr ?_
  rw [mul_neg, neg_mul, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul, inv_pow,
    inv_mul_cancel₀ (pow_ne_zero _ hr0), one_smul]

end Rep

/-- **Mellit's local identity for rule `BE`, in the braid representation.** On `V_{k+1}`,
`π(z_1ỹ_1) = u·π(y_1z_1) + q^{k/2}·d^♭_-(-y_1d^*_+)π(T^*_{k+1↘1})`. -/
theorem braidRepMellit_braidGenZ_mul_braidYtilde (q u : L) (hq : q ≠ 0) (hq1 : q ≠ 1)
    (hqp : q + 1 ≠ 0) {r : L} (hr : r * r = q) (hu : u ≠ 0) {k : ℕ} (x : pieceSub L (k + 1)) :
    ((braidRepMellit q u hq hq1 hqp hr (k + 1)
        (Braid.braidGenZ (k + 1) 1 * Braid.braidYtilde (k + 1) 1) x : pieceSub L (k + 1)) : Total L)
      = u • ((braidRepMellit q u hq hq1 hqp hr (k + 1)
          (Braid.braidGenY (k + 1) 1 * Braid.braidGenZ (k + 1) 1) x : pieceSub L (k + 1)) : Total L)
        + r ^ k • dminus q (k + 1 + 1) (negYOneDPlusStar q u (k + 1)
            ((braidRepMellit q u hq hq1 hqp hr (k + 1) (Braid.braidTrainUp (k + 1) (k + 1) 1) x :
              pieceSub L (k + 1)) : Total L)) := by
  set h := braidRepRespects_mellit q u hq hq1 hqp hr (k + 1)
  have hZY := (representedBy_braidGenZ (h := h) (by omega : 1 ≤ k + 1)).mul
    (representedBy_braidYtilde_one (h := h) hq hr (by omega : 1 ≤ k + 1))
  have hYZ := (representedBy_braidGenY (h := h) (by omega : 1 ≤ k + 1)).mul
    (representedBy_braidGenZ (h := h) (by omega : 1 ≤ k + 1))
  have hT := representedBy_braidTrainUp_top (h := h) (by omega : 1 ≤ k + 1)
  rw [braidRepMellit, hZY.apply, hYZ.apply, hT.apply]
  simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.neg_apply,
    LinearMap.mulLeft_apply, map_neg, map_smul, zop_one, Nat.add_sub_cancel,
    negYOneDPlusStar_apply]
  rw [zopOneStar_ytilde q u hq hq1 x.2]
  have e : (q * u)⁻¹ * (u * q ^ (k + 1)) = r ^ k * r ^ k := by
    rw [← mul_pow, hr]
    field_simp
    ring
  have e' : (scal ((q * u)⁻¹) * scal (u * q ^ (k + 1)) : Total L)
      = scal (r ^ k) * scal (r ^ k) := by
    rw [← scal_mul, ← scal_mul, e]
  simp only [smul_eq_scal_mul]
  linear_combination (-(dminus q (k + 1 + 1) ((auxVar 1 : Total L) *
    dplusStar q u (k + 1) (trainUpEnd q (k + 1) 1 (x : Total L))))) * e'

/-- `HJO.Sweep.braidRepMellit_braidGenZ_mul_braidYtilde` read in `V_{k+1}` itself. -/
theorem braidRepMellit_braidGenZ_mul_braidYtilde_piece (q u : L) (hq : q ≠ 0) (hq1 : q ≠ 1)
    (hqp : q + 1 ≠ 0) {r : L} (hr : r * r = q) (hu : u ≠ 0) {k : ℕ} (x : pieceSub L (k + 1)) :
    braidRepMellit q u hq hq1 hqp hr (k + 1)
        (Braid.braidGenZ (k + 1) 1 * Braid.braidYtilde (k + 1) 1) x
      = u • braidRepMellit q u hq hq1 hqp hr (k + 1)
          (Braid.braidGenY (k + 1) 1 * Braid.braidGenZ (k + 1) 1) x
        + r ^ k • dminusModPiece q (k + 1) (negYOneDPlusStarPiece q u (k + 1)
            (braidRepMellit q u hq hq1 hqp hr (k + 1) (Braid.braidTrainUp (k + 1) (k + 1) 1) x)) :=
  Subtype.ext (braidRepMellit_braidGenZ_mul_braidYtilde q u hq hq1 hqp hr hu x)

/-- **Mellit's braid rule for case `BE` (§5.3), at the level of the braid representation.** Let
`B̃_1, B̃_2 ∈ 𝔹_{k+1}^+(𝕋_0)` and let `X ∈ 𝔹_{k+2}^+(𝕋_0)` be intertwined with `B̃_2` by `d^♭_-`.
Then on the vacuum tower

`π(B̃_2 z_1ỹ_1 B̃_1) d_+^{k+1}(1) = u·π(B̃_2 y_1z_1 B̃_1) d_+^{k+1}(1)
  + q^{-1/2} d^♭_- π(X φ^*_+(T^*_{k+1↘1} B̃_1) T_{1↘k+2}) d_+^{k+2}(1)`.

The three braids are Mellit's `B`, `B''` and `B'` once the cut of the moving component is made. -/
theorem braidRepMellit_cut_dplusIter (q u : L) (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0)
    {r : L} (hr : r * r = q) (hu : u ≠ 0) {k : ℕ} (B₁ B₂ : Braid.BraidMonoid (k + 1))
    (X : Braid.BraidMonoid (k + 1 + 1))
    (hX : DminusIntertwines q u hq hq1 hqp hr (k + 1) X B₂) :
    ((braidRepMellit q u hq hq1 hqp hr (k + 1)
        (B₂ * (Braid.braidGenZ (k + 1) 1 * Braid.braidYtilde (k + 1) 1) * B₁)
        (dplusIterPiece q (k + 1)) : pieceSub L (k + 1)) : Total L)
      = u • ((braidRepMellit q u hq hq1 hqp hr (k + 1)
          (B₂ * (Braid.braidGenY (k + 1) 1 * Braid.braidGenZ (k + 1) 1) * B₁)
          (dplusIterPiece q (k + 1)) : pieceSub L (k + 1)) : Total L)
        + r⁻¹ • dminus q (k + 1 + 1) ((braidRepMellit q u hq hq1 hqp hr (k + 1 + 1)
            (X * Braid.phiPlusStar (k + 1) (by omega)
                (Braid.braidTrainUp (k + 1) (k + 1) 1 * B₁) *
              Braid.braidTrainDown (k + 1 + 1) 1 (k + 1 + 1))
            (dplusIterPiece q (k + 1 + 1)) : pieceSub L (k + 1 + 1)) : Total L) := by
  have hr0 : r ≠ 0 := fun h0 => hq (by rw [← hr, h0, zero_mul])
  have hTbot : braidRepMellit q u hq hq1 hqp hr (k + 1 + 1)
        (Braid.braidTrainDown (k + 1 + 1) 1 (k + 1 + 1)) (dplusIterPiece q (k + 1 + 1))
      = r ^ (k + 1) • dplusIterPiece q (k + 1 + 1) := by
    refine Subtype.ext ?_
    have h := (representedBy_braidTrainDown_bot (q := q) (u := u) (r := r)
      (h := braidRepRespects_mellit q u hq hq1 hqp hr (k + 1 + 1))
      (by omega : 1 ≤ k + 1 + 1)).apply (dplusIterPiece q (k + 1 + 1))
    refine h.trans ?_
    rw [LinearMap.smul_apply, coe_dplusIterPiece, trainDownEnd_bot_dplusIter q hq (k + 1),
      Submodule.coe_smul, coe_dplusIterPiece, Nat.add_sub_cancel]
  set π₁ := braidRepMellit q u hq hq1 hqp hr (k + 1)
  set π₂ := braidRepMellit q u hq hq1 hqp hr (k + 1 + 1)
  have hvac : (dplusIterPiece q (k + 1 + 1) : pieceSub L (k + 1 + 1))
      = negYOneDPlusStarPiece q u (k + 1) (dplusIterPiece q (k + 1)) :=
    Subtype.ext (dplus_dplusIter q u (k + 1))
  have hphi : ∀ (B : Braid.BraidMonoid (k + 1)) (w : pieceSub L (k + 1)),
      π₂ (Braid.phiPlusStar (k + 1) (by omega) B) (negYOneDPlusStarPiece q u (k + 1) w)
        = negYOneDPlusStarPiece q u (k + 1) (π₁ B w) := fun B w =>
    LinearMap.congr_fun (braidRep_phiPlusStar_comp_mellit q u hq hq1 hqp hr (by omega) B) w
  set x := π₁ B₁ (dplusIterPiece q (k + 1))
  set y := negYOneDPlusStarPiece q u (k + 1) (π₁ (Braid.braidTrainUp (k + 1) (k + 1) 1) x)
  have hL : π₁ (B₂ * (Braid.braidGenZ (k + 1) 1 * Braid.braidYtilde (k + 1) 1) * B₁)
        (dplusIterPiece q (k + 1))
      = u • π₁ B₂ (π₁ (Braid.braidGenY (k + 1) 1 * Braid.braidGenZ (k + 1) 1) x)
        + r ^ k • π₁ B₂ (dminusModPiece q (k + 1) y) := by
    rw [map_mul π₁ (B₂ * _) B₁, map_mul π₁ B₂, Module.End.mul_apply, Module.End.mul_apply,
      braidRepMellit_braidGenZ_mul_braidYtilde_piece q u hq hq1 hqp hr hu, map_add, map_smul,
      map_smul]
  have hE : π₁ (B₂ * (Braid.braidGenY (k + 1) 1 * Braid.braidGenZ (k + 1) 1) * B₁)
        (dplusIterPiece q (k + 1))
      = π₁ B₂ (π₁ (Braid.braidGenY (k + 1) 1 * Braid.braidGenZ (k + 1) 1) x) := by
    rw [map_mul π₁ (B₂ * _) B₁, map_mul π₁ B₂, Module.End.mul_apply, Module.End.mul_apply]
  have hU : π₂ (X * Braid.phiPlusStar (k + 1) (by omega)
          (Braid.braidTrainUp (k + 1) (k + 1) 1 * B₁) *
        Braid.braidTrainDown (k + 1 + 1) 1 (k + 1 + 1)) (dplusIterPiece q (k + 1 + 1))
      = r ^ (k + 1) • π₂ X y := by
    rw [map_mul π₂ (X * _), map_mul π₂ X, Module.End.mul_apply, Module.End.mul_apply, hTbot,
      map_smul, map_smul, hvac, hphi, map_mul π₁, Module.End.mul_apply]
  rw [hL, hE, hU, Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul, Submodule.coe_smul,
    map_smul, hX y, smul_smul, pow_succ', ← mul_assoc, inv_mul_cancel₀ hr0, one_mul]

/-! ### The lowering intertwiner of Mellit's `φ_-` -/

/-- **`d^♭_- z_i = z_i d^♭_-`** from `V_{k+1}` to `V_k`, for `1 ≤ i ≤ k`: the image of
`HJO.Dyck.Aq.yElt_mul_dMinus` under the Mellit-convention action, whose
corner elements are the `z_i` (`HJO.Sweep.map_yElt_ofPiece_mellit`). -/
theorem dminus_zop (q u : L) (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) {k i : ℕ}
    (hi : 1 ≤ i) (hik : i ≤ k) {F : Total L} (hF : F ∈ piece L (k + 1)) :
    dminus q (k + 1) (zop q u (k + 1) i F) = zop q u k i (dminus q (k + 1) F) := by
  obtain ⟨ρ, hact, hT, hD, hU⟩ := exists_isDpaAction_mellit q u hq hqp
  have hqi : (q⁻¹ : L) ≠ 0 := inv_ne_zero hq
  have hqi1 : (q⁻¹ - 1 : L) ≠ 0 := fun h => hq1 (inv_eq_one.1 (sub_eq_zero.1 h))
  let _ : Invertible (q⁻¹ : L) := invertibleOfNonzero hqi
  let _ : Invertible (q⁻¹ - 1 : L) := invertibleOfNonzero hqi1
  set Fp : pieceSub L (k + 1) := ⟨F, hF⟩
  have hm1 : zop q u (k + 1) i F ∈ pieceSub L (k + 1) := zop_mem_piece q u i hi (by omega) hF
  have hm2 : zop q u k i (dminus q (k + 1) F) ∈ pieceSub L k :=
    zop_mem_piece q u i hi hik (dminusModPiece q k Fp).2
  have h1 := map_yElt_ofPiece_mellit hact hT hD hU hq hq1 (k + 1 - i) i (by omega) hi Fp
    ⟨_, hm1⟩ rfl
  have h2 := map_yElt_ofPiece_mellit hact hT hD hU hq hq1 (k - i) i (by omega) hi
    (dminusModPiece q k Fp) ⟨_, hm2⟩ rfl
  have hrel := congrArg (fun f => ρ f (ofPiece L (k + 1) Fp))
    (Dyck.Aq.yElt_mul_dMinus (K := L) (q := q⁻¹) hi hik)
  simp only [map_mul, Module.End.mul_apply, hD, lowerVstar_ofPiece] at hrel
  rw [h2, h1, lowerVstar_ofPiece] at hrel
  have h := congrArg (toPiece L k) hrel
  rw [toPiece_ofPiece, toPiece_ofPiece] at h
  exact (congrArg Subtype.val h).symm

variable {q u : L} {hq : q ≠ 0} {hq1 : q ≠ 1} {hqp : q + 1 ≠ 0} {r : L} {hr : r * r = q}

/-- **The `z` letter is intertwined**: `z_i ↦ z_i` for `1 ≤ i ≤ k`, the hypothesis of
`HJO.Sweep.dminusIntertwines_braidGenZ_of_zop` being `HJO.Sweep.dminus_zop`. -/
theorem dminusIntertwines_braidGenZ {k i : ℕ} (hi : 1 ≤ i) (hik : i ≤ k) :
    DminusIntertwines q u hq hq1 hqp hr k (Braid.braidGenZ (k + 1) i) (Braid.braidGenZ k i) :=
  dminusIntertwines_braidGenZ_of_zop hi hik fun _ hF => dminus_zop q u hq hq1 hqp hi hik hF

/-- **Mellit's `φ_-` is intertwined by `d^♭_-`.** A word all of whose letters are in rank `k` names
an element of `𝔹_k^+(𝕋_0)` and, read at rank `k + 1`, the element Mellit calls `φ_-` of it;
`d^♭_-` intertwines the two. This is the right-hand square of Mellit's two commutative diagrams in
the proof of rule `BE`. -/
theorem dminusIntertwines_toBraidMonoid {k : ℕ} (w : FreeMonoid Braid.Letter)
    (hw : ∀ c ∈ w.toList, Braid.Letter.InRank k c) :
    DminusIntertwines q u hq hq1 hqp hr k (Braid.toBraidMonoid (k + 1) w)
      (Braid.toBraidMonoid k w) := by
  induction w using FreeMonoid.inductionOn' with
  | one => simpa only [map_one] using DminusIntertwines.one
  | of_mul c w ih =>
    rw [map_mul, map_mul]
    refine DminusIntertwines.mul ?_ (ih fun d hd => hw d (by simp [hd]))
    have hc := hw c (by simp)
    cases c with
    | T i => exact dminusIntertwines_braidGenT hc.1 hc.2
    | Tbar i => exact dminusIntertwines_braidGenTinv hc.1 hc.2
    | y1 => exact dminusIntertwines_braidGenY hc
    | z1 => exact dminusIntertwines_braidGenZ (i := 1) le_rfl hc

end HJO.Sweep

namespace HJO.Mellit

open ParkingFunctions Paths Sweep Braid Finset

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **Rule `BE` for the braid values of three special-braid data, given Mellit's cut.** If the
special braids of the lower data, the type-`E` data and the upper data are
`B̃_2 z_1ỹ_1 B̃_1`, `B̃_2 y_1z_1 B̃_1` and `X φ^*_+(T^*_{k+1↘1}B̃_1) T_{1↘k+2}` with `X`
intertwined with `B̃_2` by `d^♭_-`, and the inversion exponents of `HJO.Braid.invIni` and
`HJO.Braid.invFin` satisfy Mellit's two counts — the type-`E` exponent equal to the lower one,
the upper one smaller by one — then

`D(lower) = d^♭_-(D(upper)) + u·D(type E)`. -/
theorem braidValueOfData_eq_dminus_add_smul_of_cut (q u : L) {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1)
    (hqp : q + 1 ≠ 0) (hr : r * r = q) (hu : u ≠ 0) (a b N : ℕ) {k : ℕ}
    (vlo vE : Fin (k + 1) → ℚ) (αlo αE : Fin (k + 1) → ℕ) (vhi : Fin (k + 1 + 1) → ℚ)
    (αhi : Fin (k + 1 + 1) → ℕ) (B₁ B₂ : BraidMonoid (k + 1)) (X : BraidMonoid (k + 1 + 1))
    (hlo : specialBraid (sweepTheta a b N) vlo αlo
      = B₂ * (braidGenZ (k + 1) 1 * braidYtilde (k + 1) 1) * B₁)
    (hE : specialBraid (sweepTheta a b N) vE αE
      = B₂ * (braidGenY (k + 1) 1 * braidGenZ (k + 1) 1) * B₁)
    (hhi : specialBraid (sweepTheta a b N) vhi αhi
      = X * phiPlusStar (k + 1) (by omega) (braidTrainUp (k + 1) (k + 1) 1 * B₁) *
          braidTrainDown (k + 1 + 1) 1 (k + 1 + 1))
    (hX : DminusIntertwines q u hq hq1 hqp hr (k + 1) X B₂)
    (hinvE : (invFin (sweepTheta a b N) vE αE : ℤ) - invIni (sweepTheta a b N) vE αE
      = (invFin (sweepTheta a b N) vlo αlo : ℤ) - invIni (sweepTheta a b N) vlo αlo)
    (hinvhi : (invFin (sweepTheta a b N) vhi αhi : ℤ) - invIni (sweepTheta a b N) vhi αhi
      = (invFin (sweepTheta a b N) vlo αlo : ℤ) - invIni (sweepTheta a b N) vlo αlo - 1) :
    braidValueOfData q u hq hq1 hqp hr a b N vlo αlo
      = dminus q (k + 1 + 1) (braidValueOfData q u hq hq1 hqp hr a b N vhi αhi)
        + u • braidValueOfData q u hq hq1 hqp hr a b N vE αE := by
  have hr0 : r ≠ 0 := fun h0 => hq (by rw [← hr, h0, zero_mul])
  rw [braidValueOfData, braidValueOfData, braidValueOfData, hlo, hE, hhi, hinvE, hinvhi,
    braidRepMellit_cut_dplusIter q u hq hq1 hqp hr hu B₁ B₂ X hX, map_smul, smul_add,
    smul_comm _ u, smul_smul, smul_smul, zpow_sub_one₀ hr0, add_comm]

/-- **`HJO.Mellit.SweepRecursionBEFloor` for `HJO.Mellit.braidValueColouring`, from Mellit's cut
at every bracketed point.** The hypothesis `hcut` asks, at every type-`B`/type-`E` pair above the
floor with `k + 1` lower components, for a braid `B̃_1` and a word `w` in the letters of rank
`k + 1` such that the special braids of `HJO.Mellit.braidDataOfColouring` at the lower colouring,
the type-`E` colouring and the upper colouring are `w z_1ỹ_1 B̃_1`, `w y_1z_1 B̃_1` and
`w φ^*_+(T^*_{k+1↘1}B̃_1) T_{1↘k+2}` (the word `w` read at rank `k + 1` and at rank `k + 2`), and
for Mellit's two inversion counts.

`hcut` contains no operator: it is a statement about special braids in `𝔹^+(𝕋_0)` and about
inversion numbers. Everything algebraic in rule `BE` is discharged here — the identity
`z_1ỹ_1 = u y_1z_1 + uq^k d_- y_1d^*_+T^*_{k↘1}`, both intertwiners, the vacuum tower and the
prefactor. `hcut` is supplied by `HJO.Mellit.braidValueColouring_hcut`
(`HJO/Shuffle/BraidBECut.lean`), which gives the unconditional clause
`HJO.Mellit.braidValueColouring_sweepRecursionBEFloor`. -/
theorem braidValueColouring_sweepRecursionBEFloor_of_cut (q u : L) {r : L} (hq : q ≠ 0)
    (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) (hr : r * r = q) (hu : u ≠ 0) {a b N : ℕ} (ha : 0 < a)
    (hb : 0 < b) (hN : 0 < N)
    (hcut : ∀ (X Y : ℕ) (ηlo ηhi : ℚ), ((a * N : ℕ) : ℚ) < ηlo →
      Isolates a b N X Y ηlo ηhi → ∀ yB yE : Heights a b N, IsAboveDiagonal yB →
        IsAboveDiagonal yE → eventType yB (X, Y) = EventType.B →
          eventType yE (X, Y) = EventType.E → colouring yB ηlo = colouring yE ηlo →
            ∀ k : ℕ, #(colouringEast yB ηlo) = k + 1 →
              ∃ (B₁ : BraidMonoid (k + 1)) (w : FreeMonoid Letter),
                (∀ c ∈ w.toList, Letter.InRank (k + 1) c) ∧
                specialBraid (sweepTheta a b N) (braidDataOfColouring a b N yB ηlo (k + 1)).1
                    (braidDataOfColouring a b N yB ηlo (k + 1)).2
                  = toBraidMonoid (k + 1) w * (braidGenZ (k + 1) 1 * braidYtilde (k + 1) 1) * B₁ ∧
                specialBraid (sweepTheta a b N) (braidDataOfColouring a b N yE ηhi (k + 1)).1
                    (braidDataOfColouring a b N yE ηhi (k + 1)).2
                  = toBraidMonoid (k + 1) w * (braidGenY (k + 1) 1 * braidGenZ (k + 1) 1) * B₁ ∧
                specialBraid (sweepTheta a b N)
                    (braidDataOfColouring a b N yB ηhi (k + 1 + 1)).1
                    (braidDataOfColouring a b N yB ηhi (k + 1 + 1)).2
                  = toBraidMonoid (k + 1 + 1) w *
                      phiPlusStar (k + 1) (by omega) (braidTrainUp (k + 1) (k + 1) 1 * B₁) *
                      braidTrainDown (k + 1 + 1) 1 (k + 1 + 1) ∧
                (invFin (sweepTheta a b N) (braidDataOfColouring a b N yE ηhi (k + 1)).1
                      (braidDataOfColouring a b N yE ηhi (k + 1)).2 : ℤ)
                    - invIni (sweepTheta a b N) (braidDataOfColouring a b N yE ηhi (k + 1)).1
                      (braidDataOfColouring a b N yE ηhi (k + 1)).2
                  = (invFin (sweepTheta a b N) (braidDataOfColouring a b N yB ηlo (k + 1)).1
                      (braidDataOfColouring a b N yB ηlo (k + 1)).2 : ℤ)
                    - invIni (sweepTheta a b N) (braidDataOfColouring a b N yB ηlo (k + 1)).1
                      (braidDataOfColouring a b N yB ηlo (k + 1)).2 ∧
                (invFin (sweepTheta a b N) (braidDataOfColouring a b N yB ηhi (k + 1 + 1)).1
                      (braidDataOfColouring a b N yB ηhi (k + 1 + 1)).2 : ℤ)
                    - invIni (sweepTheta a b N)
                      (braidDataOfColouring a b N yB ηhi (k + 1 + 1)).1
                      (braidDataOfColouring a b N yB ηhi (k + 1 + 1)).2
                  = (invFin (sweepTheta a b N) (braidDataOfColouring a b N yB ηlo (k + 1)).1
                      (braidDataOfColouring a b N yB ηlo (k + 1)).2 : ℤ)
                    - invIni (sweepTheta a b N) (braidDataOfColouring a b N yB ηlo (k + 1)).1
                      (braidDataOfColouring a b N yB ηlo (k + 1)).2 - 1) :
    SweepRecursionBEFloor q u a b N (braidValueColouring q u hq hq1 hqp hr a b N) := by
  refine braidValueColouring_sweepRecursionBEFloor_of_move q u hq hq1 hqp hr ha hb hN ?_
  intro X Y ηlo ηhi hfloor hI yB yE hyB hyE hevB hevE hcol
  have hle := hI.typeBIndex_succ_le ha hb hN hfloor hyB hevB
  obtain ⟨k, hk⟩ : ∃ k, #(colouringEast yB ηlo) = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos
    (by omega)).symm⟩
  obtain ⟨B₁, w, hw, h1, h2, h3, h5, h6⟩ :=
    hcut X Y ηlo ηhi hfloor hI yB yE hyB hyE hevB hevE hcol k hk
  rw [hk]
  exact braidValueOfData_eq_dminus_add_smul_of_cut q u hq hq1 hqp hr hu a b N _ _ _ _ _ _ B₁ _ _
    h1 h2 h3 (dminusIntertwines_toBraidMonoid w hw) h5 h6

end HJO.Mellit

end
