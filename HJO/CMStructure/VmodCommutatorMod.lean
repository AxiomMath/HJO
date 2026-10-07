/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CMStructure.VmodDminusDplus
public import HJO.CMStructure.VmodDminusSection
public meta import HJO.Attr

/-! # The commutator of the modified operators

Mellit's `HJO.Sweep.dplus_dminus_sub_dminus_dplus`: for `k ≥ 1` and `F ∈ V_k`,
`(d^♭_+d^♭_- - d^♭_-d^♭_+)F = (q-1)T_{1↑k}(y_kF)`,
with `d^♭_±` the modified operators of `HJO.Sweep.dplus_eq_ascWord` and `HJO.Sweep.dminus` — that
is, `HJO.Sweep.dplus` and `HJO.Sweep.dminus` — and `T_{1↑k}` the ascending word of
`HJO.Braid.wordUp`.

This is the shape `HJO.Sweep.dminusCM_cmDPlus_sub_cmDPlus_dminusCM` has for the *unmodified* pair,
with `1-q` replaced by `q-1`, and it is derived from that lemma's ingredients rather than from the
lemma: comparing the two operators through `HJO.Sweep.dplus_eq_neg_cmAscWord_cmDPlus` turns each
side into the unmodified `d_+` wrapped in a word, `HJO.Sweep.dminus_cmDPlus` lets `d^♭_-` pass
`d_+`, and what is left is the single conjugation `qT_k^{-2} - 1 = (q-1)T_k^{-1}` followed by
`HJO.Sweep.dminus_trainUpEnd_star_cmDPlus`.

## Main results

* `HJO.Sweep.dplus_dminus_sub_dminus_dplus`.
* `HJO.Sweep.dminus_auxVar_mul`, `HJO.Sweep.dminus_cmAscWord`,
  `HJO.Sweep.dminus_trainUpEnd_star` — the three commutations the proof opens with.

## Implementation notes

**The three commutations of `d^♭_-`.** They are immediate from `HJO.Sweep.dminus` and
`HJO.Sweep.qshiftNeg`: on `V_{k+1}` the operator commutes with `T_i` for `i ≤ k-1` and with
multiplication by `y_j` for `j ≤ k`, because the substitution, the coefficient extraction and the
multiplication by `e_j` all leave `y_1, …, y_k` alone. Here the braid half is
`HJO.Sweep.dminus_braid`, extended to the inverted letters (`HJO.Sweep.dminus_braidInv`) and then to
the two words that occur — the ascending word `T_{1↑k}` and the starred descending word `T^*_{k↓1}`
— and the multiplier half is `HJO.Sweep.lowerCoeff_mul_of_mem_piece`.

**The operator identity `T_ky_{k+1}T_k^{-1} = qy_kT_k^{-2}` is not stated separately.**
What the proof uses is the single value `T_k(y_{k+1}T_k^{-2}G) = qy_kT_k^{-2}G`, which is
`HJO.Sweep.braid_auxVar_succ_mul_braid` read at `T_k^{-2}G`; and the cancellation
`qT_k^{-2} - 1 = (q-1)T_k^{-1}` is obtained from `T_k^{-1}` being a two-sided inverse rather than
from the Hecke relation, which is three lines shorter: applying `HJO.Sweep.braidInv_apply` once to
`T_k^{-1}(T_k^{-1}G)` and cancelling `T_kT_k^{-1} = 1` gives `qT_k^{-2}G = G + (q-1)T_k^{-1}G`
outright.

`q ≠ 0` is read, as it is in `HJO.Sweep.dplus_eq_neg_cmAscWord_cmDPlus` and
`HJO.Sweep.dminus_trainUpEnd_star_cmDPlus`: the starred words are words in the inverted letters,
which exist only then (`HJO.Sweep.braid_braidInv`). The argument as usually written assumes it
too. No `q ≠ 1` appears anywhere — both sides are polynomial in `q`.

## References

The lemma `HJO.Sweep.dplus_dminus_sub_dminus_dplus`, on the modified operators, using
`HJO.Sweep.piece`, `HJO.Sweep.qshiftNeg`, `HJO.Sweep.braid`, `HJO.Braid.wordUp`,
`HJO.Braid.wordDownStar`, `HJO.Sweep.dminus`, `HJO.Sweep.dplus_eq_ascWord`,
`HJO.Sweep.braid_braid_apply`, `HJO.Sweep.dplus_eq_neg_cmAscWord_cmDPlus`,
`HJO.Sweep.braid_auxVar_succ_mul_braid`, `HJO.Sweep.dminus_cmDPlus` and
`HJO.Sweep.dminus_trainUpEnd_star_cmDPlus`. Following A. Mellit, *Toric braids and
`(m, n)`-parking functions*, §3.
-/

@[expose] public section

namespace HJO.Sweep

section Field

variable {L : Type*} [Field L]

/-! ### Splitting the words at their last letter -/

/-- **The ascending word gives up its last letter**: `T_{1↑k+1}F = T_{1↑k}(T_kF)`, which is
`HJO.Sweep.cmAscWord_split` at `c = k` followed by `HJO.Sweep.cmAscWord_self`. -/
theorem cmAscWord_one_succ_apply (q : L) (m : ℕ) (F : Total L) :
    cmAscWord q 1 (m + 1) F = cmAscWord q 1 m (braid q (m + 1) F) := by
  have hsplit : cmAscWord q 1 (m + 1) = cmAscWord q 1 m * braidEnd q (m + 1) := by
    rw [cmAscWord_split q (c := m) (by omega) (by omega), cmAscWord_self]
  rw [hsplit]
  rfl

/-- **The starred descending word gives up its first letter**:
`T^*_{k+1↓1} = T_k^{-1}T^*_{k↓1}`, which is the concatenation of two adjacent descending index
ranges in the inverted letters. -/
theorem trainUpEnd_star_succ (q : L) (m : ℕ) :
    trainUpEnd q (m + 2) 1 = braidInvEnd q (m + 1) * trainUpEnd q (m + 1) 1 := by
  rw [trainUpEnd_eq_descendingWord q (m + 1), trainUpEnd_eq_descendingWord q m,
    ← Braid.descendingWord_succ_self (braidInvEnd q) (m + 1),
    Braid.descendingWord_mul (braidInvEnd q) (by omega) (by omega)]

/-- `HJO.Sweep.trainUpEnd_star_succ` applied, at the index shape
`HJO.Sweep.dplus_eq_neg_cmAscWord_cmDPlus` produces. -/
theorem trainUpEnd_star_succ_apply (q : L) (m : ℕ) (F : Total L) :
    trainUpEnd q (m + 1 + 1) 1 F = braidInv q (m + 1) (trainUpEnd q (m + 1) 1 F) :=
  LinearMap.congr_fun (trainUpEnd_star_succ q m) F

/-- **The cancellation `qT_i^{-2} = 1 + (q-1)T_i^{-1}`**, that is
`qT_k^{-2} - 1 = (q-1)T_k^{-1}`. One application of `HJO.Sweep.braidInv_apply` to the outer inverse
and the cancellation `T_iT_i^{-1} = 1` of `HJO.Sweep.braid_braidInv`; the Hecke relation is not
read. -/
theorem scal_mul_braidInv_braidInv (q : L) (hq : q ≠ 0) (i : ℕ) (F : Total L) :
    scal q * braidInv q i (braidInv q i F) = F + scal (q - 1) * braidInv q i F := by
  have hqq : (scal q : Total L) * scal q⁻¹ = 1 := by
    rw [← scal_mul, mul_inv_cancel₀ hq, scal_one]
  rw [braidInv_apply q i (braidInv q i F), braid_braidInv q hq i]
  linear_combination (F + scal (q - 1) * braidInv q i F) * hqq

end Field

section Newton

variable {L : Type*} [Field L] [Algebra ℚ L]

/-! ### The three commutations of the modified lowering operator -/

/-- **`d^♭_-` commutes with a scalar**, being `𝕜`-linear. -/
theorem dminus_scal_mul (q : L) (k : ℕ) (x : L) (F : Total L) :
    dminus q k (scal x * F) = scal x * dminus q k F := by
  rw [scal_eq_algebraMap, ← Algebra.smul_def, map_smul, Algebra.smul_def, ← scal_eq_algebraMap]

/-- **`d^♭_-` is linear over the variables it cannot reach**: `d^♭_-(y_jF) = y_jd^♭_-F` on `V_{k+1}`
for `1 ≤ j ≤ k`. The substitution `τ^-_{k+1,k+1}` fixes `y_j` and the extraction passes it
(`HJO.Sweep.lowerCoeff_mul_of_mem_piece`), which is exactly the reason: the coefficient
of `y_{k+1}^j` and the multiplication by `e_j` leave `y_1, …, y_k` alone. -/
theorem dminus_auxVar_mul (q : L) {k j : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) (F : Total L) :
    dminus q (k + 1) ((auxVar j : Total L) * F) = auxVar j * dminus q (k + 1) F := by
  rw [dminus_succ_apply, dminus_succ_apply, map_mul, qshiftNeg_auxVar_apply,
    lowerCoeff_mul_of_mem_piece (auxVar_mem_piece hj hjk)]

/-- `HJO.Sweep.dminus_auxVar_mul` at the top readable variable, `d^♭_-(y_{k+1}F) = y_{k+1}d^♭_-F` on
`V_{k+2}`, in the index shape the commutator proof uses. -/
theorem dminus_succ_auxVar_mul (q : L) (m : ℕ) (F : Total L) :
    dminus q (m + 2) ((auxVar (m + 1) : Total L) * F)
      = (auxVar (m + 1) : Total L) * dminus q (m + 2) F :=
  dminus_auxVar_mul q (by omega) (le_refl (m + 1)) F

/-- **`d^♭_-` commutes with the inverted braid operators** at the indices at which it commutes with
the braid operators themselves: `T_i^{-1}` is a `𝕜`-linear combination of `T_i` and the identity. -/
theorem dminus_braidInv (q : L) {k i : ℕ} (hik : i ≤ k) (F : Total L) :
    dminus q (k + 2) (braidInv q i F) = braidInv q i (dminus q (k + 2) F) := by
  rw [braidInv_apply q i F, braidInv_apply q i (dminus q (k + 2) F), dminus_scal_mul, map_add,
    dminus_braid q hik, dminus_scal_mul]

/-- `HJO.Sweep.dminus_braidInv` in the endomorphism monoid. -/
theorem dminus_mul_braidInvEnd (q : L) {k i : ℕ} (hik : i ≤ k) :
    dminus q (k + 2) * braidInvEnd q i = braidInvEnd q i * dminus q (k + 2) :=
  LinearMap.ext fun F => dminus_braidInv q hik F

/-- **`d^♭_-` commutes with the ascending word `T_{1↑b+1}`** for `b ≤ m`, read on `V_{m+2}`: every
letter is one `HJO.Sweep.dminus_braid` covers, and an element commuting with every letter commutes
with the product. -/
theorem dminus_mul_cmAscWord (q : L) {b m : ℕ} (hbm : b ≤ m) :
    dminus q (m + 2) * cmAscWord q 1 b = cmAscWord q 1 b * dminus q (m + 2) := by
  rw [cmAscWord_eq_ascendingWord q (by omega), Braid.ascendingWord]
  refine Braid.mul_prod_comm fun y hy => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
  rw [List.mem_range'_1] at hj
  exact dminus_mul_braidEnd q (by omega)

/-- `d^♭_-(T_{1↑b+1}F) = T_{1↑b+1}(d^♭_-F)`, the applied form. -/
theorem dminus_cmAscWord (q : L) {b m : ℕ} (hbm : b ≤ m) (F : Total L) :
    dminus q (m + 2) (cmAscWord q 1 b F) = cmAscWord q 1 b (dminus q (m + 2) F) :=
  LinearMap.congr_fun (dminus_mul_cmAscWord q hbm) F

/-- **`d^♭_-` commutes with the starred descending word `T^*_{m+1↓1}`**, whose letters are the
inverted `T_1^{-1}, …, T_m^{-1}`: the same argument as for the ascending word, through
`HJO.Sweep.dminus_mul_braidInvEnd`. -/
theorem dminus_mul_trainUpEnd_star (q : L) (m : ℕ) :
    dminus q (m + 2) * trainUpEnd q (m + 1) 1 = trainUpEnd q (m + 1) 1 * dminus q (m + 2) := by
  rw [trainUpEnd_eq_descendingWord q m, Braid.descendingWord]
  refine Braid.mul_prod_comm fun y hy => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
  rw [List.mem_reverse, List.mem_range'_1] at hj
  exact dminus_mul_braidInvEnd q (k := m) (by omega)

/-- `d^♭_-(T^*_{m+1↓1}F) = T^*_{m+1↓1}(d^♭_-F)`, the applied form. -/
theorem dminus_trainUpEnd_star (q : L) (m : ℕ) (F : Total L) :
    dminus q (m + 2) (trainUpEnd q (m + 1) 1 F)
      = trainUpEnd q (m + 1) 1 (dminus q (m + 2) F) :=
  LinearMap.congr_fun (dminus_mul_trainUpEnd_star q m) F

/-! ### The commutator -/

/-- **The commutator of the modified operators**, `HJO.Sweep.dplus_dminus_sub_dminus_dplus`: for
`k ≥ 1` and `F ∈ V_k`,
`(d^♭_+d^♭_- - d^♭_-d^♭_+)F = (q-1)T_{1↑k}(y_kF)`.

Read at `k = m + 1`, so that the ascending word is `T_{1↑m+1} = T_{1↑(m+1)}` of
`HJO.Sweep.cmAscWord` with nothing truncated, and the four operator indices — `d^♭_-` from `V_{m+1}`
then `d^♭_+` from `V_m`, and `d^♭_+` from `V_{m+1}` then `d^♭_-` from `V_{m+2}` — are written out.

The proof. `HJO.Sweep.dplus_eq_neg_cmAscWord_cmDPlus` at the vertices `m` and `m+1` writes both
terms with the unmodified `d_+` inside, `HJO.Sweep.dminus_cmDPlus` moves `d^♭_-` past that `d_+`,
and the three commutations above move it past the word and past `y_{m+1}`; the two terms then differ
only by the operator `-T^*_{m+1↓1} + qT_{m+1}^{-2}T^*_{m+1↓1}`, which is
`(q-1)T^*_{m+2↓1}` by `HJO.Sweep.scal_mul_braidInv_braidInv`, and
`HJO.Sweep.dminus_trainUpEnd_star_cmDPlus` evaluates `d^♭_-T^*_{m+2↓1}(d_+F)` to `F`. -/
@[hjo "lem_vmod_commutator_mod"]
theorem dplus_dminus_sub_dminus_dplus (q : L) (hq : q ≠ 0) (m : ℕ) {F : Total L}
    (hF : F ∈ piece L (m + 1)) :
    dplus q m (dminus q (m + 1) F) - dminus q (m + 2) (dplus q (m + 1) F)
      = scal (q - 1) * cmAscWord q 1 m ((auxVar (m + 1) : Total L) * F) := by
  have hA1 : dplus q m (dminus q (m + 1) F)
      = -cmAscWord q 1 m ((auxVar (m + 1) : Total L)
          * dminus q (m + 2) (trainUpEnd q (m + 1) 1 (cmDPlus q (m + 1) F))) := by
    rw [dplus_eq_neg_cmAscWord_cmDPlus q hq m (dminus q (m + 1) F), ← dminus_cmDPlus q m hF,
      ← dminus_trainUpEnd_star q m]
  have hA2 : dminus q (m + 2) (dplus q (m + 1) F)
      = -cmAscWord q 1 m ((auxVar (m + 1) : Total L)
          * dminus q (m + 2) (scal q * braidInv q (m + 1)
              (braidInv q (m + 1) (trainUpEnd q (m + 1) 1 (cmDPlus q (m + 1) F))))) := by
    have hconj : braid q (m + 1) ((auxVar (m + 2) : Total L)
          * braidInv q (m + 1) (trainUpEnd q (m + 1) 1 (cmDPlus q (m + 1) F)))
        = scal q * auxVar (m + 1) * braidInv q (m + 1)
            (braidInv q (m + 1) (trainUpEnd q (m + 1) 1 (cmDPlus q (m + 1) F))) := by
      have h := braid_auxVar_succ_mul_braid q (i := m + 1) (by omega)
        (braidInv q (m + 1)
          (braidInv q (m + 1) (trainUpEnd q (m + 1) 1 (cmDPlus q (m + 1) F))))
      rwa [braid_braidInv q hq (m + 1)] at h
    have hmove : (scal q : Total L) * auxVar (m + 1) * braidInv q (m + 1)
          (braidInv q (m + 1) (trainUpEnd q (m + 1) 1 (cmDPlus q (m + 1) F)))
        = (auxVar (m + 1) : Total L) * (scal q * braidInv q (m + 1)
            (braidInv q (m + 1) (trainUpEnd q (m + 1) 1 (cmDPlus q (m + 1) F)))) := by
      ring
    rw [dplus_eq_neg_cmAscWord_cmDPlus q hq (m + 1) F, trainUpEnd_star_succ_apply q m,
      show m + 1 + 1 = m + 2 from rfl, cmAscWord_one_succ_apply q m, hconj, hmove, map_neg,
      dminus_cmAscWord q (le_refl m), dminus_succ_auxVar_mul q m]
  have hsec : dminus q (m + 2) (trainUpEnd q (m + 2) 1 (cmDPlus q (m + 1) F)) = F :=
    dminus_trainUpEnd_star_cmDPlus q hq hF
  have hkey : scal q * braidInv q (m + 1)
        (braidInv q (m + 1) (trainUpEnd q (m + 1) 1 (cmDPlus q (m + 1) F)))
      - trainUpEnd q (m + 1) 1 (cmDPlus q (m + 1) F)
      = scal (q - 1) * trainUpEnd q (m + 2) 1 (cmDPlus q (m + 1) F) := by
    have hop : trainUpEnd q (m + 2) 1 (cmDPlus q (m + 1) F)
        = braidInv q (m + 1) (trainUpEnd q (m + 1) 1 (cmDPlus q (m + 1) F)) :=
      trainUpEnd_star_succ_apply q m _
    rw [hop, scal_mul_braidInv_braidInv q hq (m + 1)]
    ring
  have hfinal : cmAscWord q 1 m ((auxVar (m + 1) : Total L)
        * dminus q (m + 2) (scal q * braidInv q (m + 1)
            (braidInv q (m + 1) (trainUpEnd q (m + 1) 1 (cmDPlus q (m + 1) F)))))
      - cmAscWord q 1 m ((auxVar (m + 1) : Total L)
          * dminus q (m + 2) (trainUpEnd q (m + 1) 1 (cmDPlus q (m + 1) F)))
      = scal (q - 1) * cmAscWord q 1 m ((auxVar (m + 1) : Total L) * F) := by
    rw [← map_sub, ← mul_sub, ← map_sub, hkey, dminus_scal_mul, hsec,
      show (auxVar (m + 1) : Total L) * (scal (q - 1) * F)
        = scal (q - 1) * ((auxVar (m + 1) : Total L) * F) from by ring,
      cmAscWord_scal_mul]
  rw [hA1, hA2]
  linear_combination hfinal

end Newton

end HJO.Sweep

end
