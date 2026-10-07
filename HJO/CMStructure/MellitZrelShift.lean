/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CMStructure.StarZrelShift
public import HJO.CMStructure.VmodCommutatorMod
public import HJO.CMStructure.VmodDplusRelations
public import HJO.CMStructure.ZBraid

/-! # The mixed relation shift in Mellit's convention

`HJO.Sweep.trainDown_starCommCM_trainUp_cmDPlus` proves `HJO.Sweep.starCommCM_cmDPlus` in the
all-Carlsson--Mellit vocabulary: `d_+` of `HJO.Sweep.cmDPlus`, `d_-` of `HJO.Sweep.dminusCM`. This
file redoes its last three steps with Mellit's own operators — `d^♭_+` of
`HJO.Sweep.dplus_eq_ascWord` (`HJO.Sweep.dplus`) and `d^♭_-` of `HJO.Sweep.dminus` — and then
rewrites the outcome through `HJO.Sweep.zop` itself, so that the conclusion is a statement about
`HJO.Sweep.zop`: `d^♭_+z_i = z_{i+1}d^♭_+` on `V_k` for `1 ≤ i ≤ k`, prefactors included.

That last step is what the Carlsson--Mellit form cannot supply. The two `z_1`s are two different
operators (`HJO.Sweep.starCommCM_eq_neg_starComm_auxVar_mul` and the note under it), so a relation
about `HJO.Sweep.starCommCM` is not a relation about `HJO.Sweep.zopOneStar`; and the prefactor
`q^k/(1-q)` that `HJO.Sweep.zop` carries has to be shown to cancel, which it does exactly.

## Main results

* `HJO.Sweep.braid_one_dplusStar_dplus` — `T_1d^*_+d^♭_+ = d^♭_+d^*_+` on `V_k`, the relation
  between the two raising arrows in Mellit's convention.
* `HJO.Sweep.starComm_dplus` — **the relation at `i = 1`**:
  `[d^*_+, d^♭_-]d^♭_+ = T_1^{-1}d^♭_+[d^*_+, d^♭_-]` on `V_k`.
* `HJO.Sweep.trainDown_starComm_trainUp_dplus` — the relation at every `1 ≤ i ≤ k`, obtained from it
  by conjugating with the braid trains.
* `HJO.Sweep.dplus_zop` — **the form used later**: `d^♭_+z_i = z_{i+1}d^♭_+` on `V_k` for
  `1 ≤ i ≤ k`, with `z_i` the operator `HJO.Sweep.zop` and no scalar removed from either side.

## The letter `T_1` lands on the same side as in Carlsson and Mellit's convention

It is tempting to expect the two conventions to split at the left end in opposite senses, on the
ground that `d^♭_+` is written with `T_{1↗k+1}` (`HJO.Sweep.trainUpEnd`) where `d_+` is written with
the ascending word `T_{[1,k]}` (`HJO.Sweep.cmAscWord`). They do not: `HJO.Sweep.cmAscWord` is
*defined* as `cmAscWord q a b = trainUpEnd q a (b + 1)`, and `trainUpEnd q 1 (k + 1)` is above its
turning point, so it is the ascending word `T_1 ⋯ T_k` and not a word of inverses. The two raising
operators therefore carry the **same** word, and differ only by the sign and the extra letter
`y_{k+1}`:

`d_+F = T_{[1,k]}(τ_{k+1,k+1}F)` against `d^♭_+F = -T_{[1,k]}(y_{k+1}τ_{k+1,k+1}F)`.

Both extra factors are transparent to the computation — `d^*_+` passes the sign and raises the index
of `y_{k+1}` to `y_{k+2}` by `HJO.Sweep.dplusStar_auxVar_mul` — so the split of `T_{[1,k+1]}` into
`T_1T_{[2,k+1]}` is the same one, on the same side, and

`T_1d^*_+d^♭_+ = d^♭_+d^*_+` on `V_k`

with the `T_1` on the left of `d^*_+d^♭_+`, verbatim as in
`HJO.Sweep.braid_one_dplusStar_cmDPlus`. Consequently the relation at `i = 1` also comes out with
`T_1^{-1}` on the same side as `HJO.Sweep.starCommCM_cmDPlus`, and the whole chain is the
Carlsson--Mellit chain with the two operators swapped.

The one genuine sign difference between the conventions is in the commutator:
`HJO.Sweep.dplus_dminus_sub_dminus_dplus` reads
`d^♭_+d^♭_- - d^♭_-d^♭_+ = (q-1)T_{[1,k-1]}(y_k \cdot)` where
`HJO.Sweep.dminusCM_cmDPlus_sub_cmDPlus_dminusCM` reads
`d_-d_+ - d_+d_- = (1-q)T_{[1,k-1]}(y_k \cdot)`. Both say
`d_-d_+ = d_+d_- + (1-q)T_{[1,k-1]}(y_k \cdot)`, so the difference is a transposition of the two
sides and not a change of sign, and the proof below is the Carlsson--Mellit proof unchanged.

## `q ≠ 1` is not needed, and neither is any scalar bookkeeping beyond one cancellation

`HJO.Sweep.zop`'s `z_{i+1}` on `V_k` is `q^{-i}T_{i+1↘1}z_1T_{1↗i+1}` with
`z_1 = q^k/(1-q)[d^*_+, d^♭_-]T^*_{k↘1}` (`HJO.Sweep.zop_eq_conj`, `HJO.Sweep.zopOneStar_eq`), so
`d^♭_+z_i = z_{i+1}d^♭_+` on `V_k` carries the scalar `q^{1-i}q^k/(1-q)` on the left against
`q^{-i}q^{k+1}/(1-q)` on the right, and those are equal for every `q ≠ 0`. So `HJO.Sweep.dplus_zop`
is stated with the prefactors *in place* on both sides and needs only `q ≠ 0`; `q ≠ 1` never
appears, the factor `(1-q)^{-1}` being the same junk value on both sides when `q = 1`.

## References

Lemma `HJO.Sweep.starCommCM_cmDPlus`, read with
`HJO.Sweep.dplus_eq_ascWord`, `HJO.Sweep.dminus` and `HJO.Sweep.zop` in place of
`HJO.Sweep.cmDPlus`, `HJO.Sweep.dminusCM` and `HJO.Dyck.Tilde.Atilde`. Proved from
`HJO.Sweep.dplus_dminus_sub_dminus_dplus`, `HJO.Sweep.dplusStar_braidInv`,
`HJO.Sweep.dplus_braid_succ` and `HJO.Sweep.dminusCM_braid` for the modified lowering operator. In
Carlsson and Mellit's own convention the statement is
`HJO.Sweep.trainDown_starCommCM_trainUp_cmDPlus`. Transcribing E. Carlsson and A. Mellit, *A proof
of the shuffle conjecture*, Section 5, and A. Mellit, *Toric braids and `(m, n)`-parking functions*,
§3.6.
-/

@[expose] public section

namespace HJO.Sweep

section Field

variable {L : Type*} [Field L]

/-! ### Scalars against an inverted braid letter -/

/-- `T_i^{-1}` is linear over the scalars of `𝕜`, being a polynomial in `T_i`. -/
private theorem braidInv_scal_mul_apply (q : L) (i : ℕ) (x : L) (G : Total L) :
    braidInv q i (scal x * G) = scal x * braidInv q i G := by
  rw [braidInv_apply, braidInv_apply, braid_scal_mul]
  ring

/-- `T_{j↘1}` is the descending word in the uninverted letters as soon as `1 ≤ j`, the branch of
`HJO.Braid.trainDown` the trains of `HJO.Dyck.Tilde.Atilde` are read on. -/
private theorem trainDownEnd_pos_eq_descendingWord (q : L) {j : ℕ} (hj : 1 ≤ j) :
    trainDownEnd q j 1 = Braid.descendingWord (braidEnd q) j 1 := by
  rw [trainDownEnd, Braid.trainDown]
  exact ite_eq_left_of_eq_true _ _ (eq_true hj)

end Field

section Newton

variable {L : Type*} [Field L] [Algebra ℚ L]

/-! ### The modified raising operator against the braid trains -/

omit [Algebra ℚ L] in
/-- `d^♭_+T_j^{-1} = T_{j+1}^{-1}d^♭_+` for `1 ≤ j ≤ k-1`, `HJO.Sweep.dplus_braid_succ` read on an
inverted letter. -/
private theorem dplus_mul_braidInvEnd (q : L) (hq : q ≠ 0) {k j : ℕ} (hj : 1 ≤ j)
    (hjk : j + 1 ≤ k) :
    dplus q k * braidInvEnd q j = braidInvEnd q (j + 1) * dplus q k :=
  Braid.comm_shift_inv (braidEnd_mul_braidInvEnd q hq j)
    (braidInvEnd_mul_braidEnd q hq (j + 1)) (dplus_mul_braidEnd_succ q hj hjk)

omit [Algebra ℚ L] in
/-- **`T_{1↗i+1}d^♭_+ = T_1d^♭_+T_{1↗i}`** for `1 ≤ i ≤ k`: the ascending train absorbs the letter
`d^♭_+` produces at every index it passes, and the head letter `T_1` is what is left over. -/
private theorem trainUpEnd_one_succ_mul_dplus (q : L) {k i : ℕ} (hi : 1 ≤ i) (hik : i ≤ k) :
    trainUpEnd q 1 (i + 1) * dplus q k = braidEnd q 1 * dplus q k * trainUpEnd q 1 i := by
  have hshift : dplus q k * Braid.ascendingWord (braidEnd q) 1 i
      = Braid.ascendingWord (braidEnd q) 2 (i + 1) * dplus q k :=
    Braid.mul_ascendingWord (by omega) fun j hj hji =>
      dplus_mul_braidEnd_succ q hj (by omega)
  have hsplit : Braid.ascendingWord (braidEnd q) 1 (i + 1)
      = braidEnd q 1 * Braid.ascendingWord (braidEnd q) 2 (i + 1) := by
    rw [← Braid.ascendingWord_succ_self (braidEnd q) 1,
      Braid.ascendingWord_mul (braidEnd q) (by omega) (by omega)]
  rw [trainUpEnd_eq_ascendingWord q (show 1 ≤ i + 1 by omega),
    trainUpEnd_eq_ascendingWord q hi, hsplit]
  simp only [mul_assoc]
  rw [hshift]

omit [Algebra ℚ L] in
/-- **`d^♭_+T_{i↘1} = T_{i+1↘1}T_1^{-1}d^♭_+`** for `1 ≤ i ≤ k`: `d^♭_+` shifts every letter of the
descending train up by one, and the shifted train is `T_{i+1↘2} = T_{i+1↘1}T_1^{-1}`. -/
private theorem dplus_mul_trainDownEnd (q : L) (hq : q ≠ 0) {k i : ℕ} (hi : 1 ≤ i) (hik : i ≤ k) :
    dplus q k * trainDownEnd q i 1
      = trainDownEnd q (i + 1) 1 * braidInvEnd q 1 * dplus q k := by
  have hshift : dplus q k * Braid.descendingWord (braidEnd q) i 1
      = Braid.descendingWord (braidEnd q) (i + 1) 2 * dplus q k :=
    Braid.mul_descendingWord fun j hj hji => dplus_mul_braidEnd_succ q hj (by omega)
  have hsplit : Braid.descendingWord (braidEnd q) (i + 1) 1
      = Braid.descendingWord (braidEnd q) (i + 1) 2 * braidEnd q 1 := by
    rw [← Braid.descendingWord_succ_self (braidEnd q) 1,
      Braid.descendingWord_mul (braidEnd q) (by omega) (by omega)]
  have hsplit' : Braid.descendingWord (braidEnd q) (i + 1) 2
      = Braid.descendingWord (braidEnd q) (i + 1) 1 * braidInvEnd q 1 := by
    rw [hsplit, mul_assoc, braidEnd_mul_braidInvEnd q hq, mul_one]
  rw [trainDownEnd_pos_eq_descendingWord q hi,
    trainDownEnd_pos_eq_descendingWord q (show 1 ≤ i + 1 by omega), hshift, hsplit']

omit [Algebra ℚ L] in
/-- **`T^*_{k+1↘1}T_1d^♭_+ = d^♭_+T^*_{k↘1}`**: the starred train of the inverted letters is
shortened by the letter `T_1` to `T^*_{k+1↘2}`, and `d^♭_+` shifts every letter of `T^*_{k↘1}` into
exactly that word. -/
private theorem trainUpEnd_star_mul_braidEnd_one_mul_dplus (q : L) (hq : q ≠ 0) (c : ℕ) :
    trainUpEnd q (c + 1 + 1) 1 * braidEnd q 1 * dplus q (c + 1)
      = dplus q (c + 1) * trainUpEnd q (c + 1) 1 := by
  have hshift : dplus q (c + 1) * Braid.descendingWord (braidInvEnd q) (c + 1) 1
      = Braid.descendingWord (braidInvEnd q) (c + 1 + 1) 2 * dplus q (c + 1) :=
    Braid.mul_descendingWord fun j hj hjk => dplus_mul_braidInvEnd q hq hj (by omega)
  have hsplit : Braid.descendingWord (braidInvEnd q) (c + 1 + 1) 1
      = Braid.descendingWord (braidInvEnd q) (c + 1 + 1) 2 * braidInvEnd q 1 := by
    rw [← Braid.descendingWord_succ_self (braidInvEnd q) 1,
      Braid.descendingWord_mul (braidInvEnd q) (by omega) (by omega)]
  have hsplit' : Braid.descendingWord (braidInvEnd q) (c + 1 + 1) 1 * braidEnd q 1
      = Braid.descendingWord (braidInvEnd q) (c + 1 + 1) 2 := by
    rw [hsplit, mul_assoc, braidInvEnd_mul_braidEnd q hq, mul_one]
  rw [trainUpEnd_eq_descendingWord q (c + 1), trainUpEnd_eq_descendingWord q c, hsplit', ← hshift]

/-! ### `T_1d^*_+d^♭_+ = d^♭_+d^*_+` -/

/-- **`T_1d^*_+d^♭_+ = d^♭_+d^*_+` on `V_k`**, the Mellit-convention reading of
`HJO.Sweep.braid_one_dplusStar_cmDPlus`, with the letter `T_1` on the same side.

Both raising operators carry the ascending word `T_{[1,k]}`, `HJO.Sweep.cmAscWord` being
`trainUpEnd q a (b + 1)` and `trainUpEnd q 1 (k + 1)` being above its turning point; `d^♭_+` differs
from `d_+` only by the sign and the letter `y_{k+1}`, and `d^*_+` passes the sign and raises
`y_{k+1}` to `y_{k+2}` (`HJO.Sweep.dplusStar_auxVar_mul`). So the computation is the one of
`HJO.Sweep.braid_one_dplusStar_cmDPlus` verbatim: `d^*_+` conjugates the word into `T_{[2,k+1]}`
(`HJO.Sweep.dplusStar_mul_cmAscWord`) and passes the substitution at the cost of one index
(`HJO.Sweep.dplusStar_qshift_of_mem_piece`, which is where `F ∈ V_k` is read), and what is left is
`T_{[1,k+1]} = T_1T_{[2,k+1]}`. -/
theorem braid_one_dplusStar_dplus (q u : L) {k : ℕ} {F : Total L} (hF : F ∈ piece L k) :
    braid q 1 (dplusStar q u (k + 1) (dplus q k F)) = dplus q (k + 1) (dplusStar q u k F) := by
  have hstep : dplusStar q u (k + 1)
        (cmAscWord q 1 k ((auxVar (k + 1) : Total L) * qshift q (k + 1) F))
      = cmAscWord q 2 (k + 1) ((auxVar (k + 1 + 1) : Total L)
          * qshift q (k + 1 + 1) (dplusStar q u k F)) := by
    have h := LinearMap.congr_fun (dplusStar_mul_cmAscWord q u k)
      ((auxVar (k + 1) : Total L) * qshift q (k + 1) F)
    rw [Module.End.mul_apply, Module.End.mul_apply] at h
    rw [h, dplusStar_auxVar_mul q u (show 1 ≤ k + 1 by omega) le_rfl,
      dplusStar_qshift_of_mem_piece q u hF]
  rw [dplus_eq_ascWord q k F, dplus_eq_ascWord q (k + 1) (dplusStar q u k F)]
  simp only [map_neg]
  rw [hstep, cmAscWord_apply_succ_left q (show 1 ≤ k + 1 by omega)]

/-! ### The relation at the first index -/

/-- The commutator at a successor index, applied, with no truncated subtraction. -/
private theorem starComm_succ_apply (q u : L) (m : ℕ) (F : Total L) :
    starComm q u (m + 1) F
      = dplusStar q u m (dminus q (m + 1) F)
        - dminus q (m + 1 + 1) (dplusStar q u (m + 1) F) := rfl

/-- **The Mellit-convention relation at `i = 1`**: for `k ≥ 1` and `F ∈ V_k`, written at
`k = m + 1`,

`[d^*_+, d^♭_-](d^♭_+F) = T_1^{-1}(d^♭_+([d^*_+, d^♭_-]F))`,

with `d^♭_+` of `HJO.Sweep.dplus_eq_ascWord` and `d^♭_-` of `HJO.Sweep.dminus` — the two operators
`HJO.Sweep.zop` is written with. This is `HJO.Sweep.starCommCM_cmDPlus` with Mellit's operators in
place of Carlsson and Mellit's, and the letter `T_1^{-1}` lands on the same side.

Three rewrites, no plethysm and no spanning principle. `HJO.Sweep.dplus_dminus_sub_dminus_dplus`
moves `d^♭_-` past `d^♭_+` on `F` and again on `d^*_+F`, leaving the two `d^♭_+d^♭_-` halves and two
`(q-1)`-terms; `HJO.Sweep.braid_one_dplusStar_dplus` identifies the halves with the two terms of the
right-hand side — once on `F`, once on `d^♭_-F ∈ V_{k-1}`; and
`HJO.Sweep.dplusStar_cmAscWord_auxVar_mul`, which is convention-independent, cancels the two
`(q-1)`-terms against each other.

`q ≠ 0` is read only for the braid inverses; `q ≠ 1` is not read at all. -/
theorem starComm_dplus (q u : L) (hq : q ≠ 0) {m : ℕ} {F : Total L}
    (hF : F ∈ piece L (m + 1)) :
    starComm q u (m + 1 + 1) (dplus q (m + 1) F)
      = braidInv q 1 (dplus q (m + 1) (starComm q u (m + 1) F)) := by
  have hAmem : dminus q (m + 1) F ∈ piece L m := by
    simpa using dminus_mem_piece q (m + 1) hF
  have hGmem : dplusStar q u (m + 1) F ∈ piece L (m + 1 + 1) := dplusStar_mem_piece q u hF
  -- `HJO.Sweep.dplus_dminus_sub_dminus_dplus` on `F`
  have hc1 : dminus q (m + 1 + 1) (dplus q (m + 1) F)
      = dplus q m (dminus q (m + 1) F)
        - scal (q - 1) * cmAscWord q 1 m ((auxVar (m + 1) : Total L) * F) := by
    have h := dplus_dminus_sub_dminus_dplus q hq m hF
    linear_combination -h
  -- `HJO.Sweep.dplus_dminus_sub_dminus_dplus` on `d^*_+F`
  have hc2 : dminus q (m + 1 + 1 + 1) (dplus q (m + 1 + 1) (dplusStar q u (m + 1) F))
      = dplus q (m + 1) (dminus q (m + 1 + 1) (dplusStar q u (m + 1) F))
        - scal (q - 1) * cmAscWord q 1 (m + 1)
            ((auxVar (m + 1 + 1) : Total L) * dplusStar q u (m + 1) F) := by
    have h := dplus_dminus_sub_dminus_dplus q hq (m + 1) hGmem
    linear_combination -h
  -- `T_1d^*_+d^♭_+ = d^♭_+d^*_+` on `F`, read backwards
  have hs1 : dplusStar q u (m + 1 + 1) (dplus q (m + 1) F)
      = braidInv q 1 (dplus q (m + 1 + 1) (dplusStar q u (m + 1) F)) := by
    rw [← braid_one_dplusStar_dplus q u hF, braidInv_braid q hq]
  -- `T_1d^*_+d^♭_+ = d^♭_+d^*_+` on `d^♭_-F`
  have hs2 : dplusStar q u (m + 1) (dplus q m (dminus q (m + 1) F))
      = braidInv q 1 (dplus q (m + 1) (dplusStar q u m (dminus q (m + 1) F))) := by
    rw [← braid_one_dplusStar_dplus q u hAmem, braidInv_braid q hq]
  -- `d^♭_-` passes `T_1^{-1}` on `V_{k+2}`
  have hcomm : ∀ Z : Total L, dminus q (m + 1 + 1 + 1) (braidInv q 1 Z)
      = braidInv q 1 (dminus q (m + 1 + 1 + 1) Z) := by
    intro Z
    have h := LinearMap.congr_fun (Braid.comm_inv_right (braidEnd_mul_braidInvEnd q hq 1)
      (braidInvEnd_mul_braidEnd q hq 1)
      (dminus_mul_braidEnd q (show (1 : ℕ) ≤ m + 1 by omega))) Z
    rw [Module.End.mul_apply, Module.End.mul_apply] at h
    exact h
  -- the two `(q-1)`-terms
  have hleft : dplusStar q u (m + 1)
        (scal (q - 1) * cmAscWord q 1 m ((auxVar (m + 1) : Total L) * F))
      = scal (q - 1) * cmAscWord q 2 (m + 1)
          ((auxVar (m + 1 + 1) : Total L) * dplusStar q u (m + 1) F) := by
    rw [dplusStar_scal_mul, dplusStar_cmAscWord_auxVar_mul]
  have hright : braidInv q 1 (scal (q - 1) * cmAscWord q 1 (m + 1)
        ((auxVar (m + 1 + 1) : Total L) * dplusStar q u (m + 1) F))
      = scal (q - 1) * cmAscWord q 2 (m + 1)
          ((auxVar (m + 1 + 1) : Total L) * dplusStar q u (m + 1) F) := by
    rw [braidInv_scal_mul_apply, cmAscWord_apply_succ_left q (show 1 ≤ m + 1 by omega),
      braidInv_braid q hq]
  rw [starComm_succ_apply, starComm_succ_apply, hc1, hs1, hcomm, hc2, map_sub, map_sub,
    map_sub, map_sub, hs2, hleft, hright]
  abel

/-! ### The relation at every admissible index -/

/-- **The Mellit-convention relation at every `1 ≤ i ≤ k`**: for `k ≥ 1`, on `V_k`,

`T_{i+1↘1}C_{k+1}T^*_{k+1↘1}T_{1↗i+1}d^♭_+ = d^♭_+T_{i↘1}C_kT^*_{k↘1}T_{1↗i}`,

where `C_j` is the commutator `d^*_+d^♭_- - d^♭_-d^*_+` read on `V_j`. This is
`z_{i+1}d^♭_+ = d^♭_+z_i` with the prefactors of `HJO.Sweep.zop` stripped from both sides;
`HJO.Sweep.dplus_zop` puts them back.

Three train identities reduce it to `HJO.Sweep.starComm_dplus`, the case `i = 1`:
`T_{1↗i+1}d^♭_+ = T_1d^♭_+T_{1↗i}` and `d^♭_+T_{i↘1} = T_{i+1↘1}T_1^{-1}d^♭_+` move `d^♭_+` through
the two conjugating trains, and `T^*_{k+1↘1}T_1d^♭_+ = d^♭_+T^*_{k↘1}` moves it through the train of
`z_1`. Each reads only `d^♭_+T_j = T_{j+1}d^♭_+` (`HJO.Sweep.dplus_braid_succ`) at indices
`j ≤ i - 1 ≤ k - 1`, which is why the range `1 ≤ i ≤ k` is exact at the top end. -/
theorem trainDown_starComm_trainUp_dplus (q u : L) (hq : q ≠ 0) {k i : ℕ} (hi : 1 ≤ i)
    (hik : i ≤ k) {F : Total L} (hF : F ∈ piece L k) :
    trainDownEnd q (i + 1) 1 (starComm q u (k + 1)
        (trainUpEnd q (k + 1) 1 (trainUpEnd q 1 (i + 1) (dplus q k F))))
      = dplus q k (trainDownEnd q i 1 (starComm q u k
          (trainUpEnd q k 1 (trainUpEnd q 1 i F)))) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hmem : trainUpEnd q (m + 1) 1 (trainUpEnd q 1 i F) ∈ piece L (m + 1) :=
    trainUpEnd_mem_piece q (le_refl (m + 1)) (by omega)
      (trainUpEnd_mem_piece q (by omega) hik hF)
  have h1 := LinearMap.congr_fun (trainUpEnd_one_succ_mul_dplus q hi hik) F
  have h2 := LinearMap.congr_fun
    (trainUpEnd_star_mul_braidEnd_one_mul_dplus q hq m) (trainUpEnd q 1 i F)
  have h3 := LinearMap.congr_fun (dplus_mul_trainDownEnd q hq hi hik)
    (starComm q u (m + 1) (trainUpEnd q (m + 1) 1 (trainUpEnd q 1 i F)))
  have hbe : ∀ Z : Total L, braidInvEnd q 1 Z = braidInv q 1 Z := fun _ => rfl
  simp only [Module.End.mul_apply, hbe] at h1 h2 h3
  rw [h1, h2, starComm_dplus q u hq hmem, ← h3]

/-! ### The form used later: `z_i` itself -/

/-- **`d^♭_+z_i = z_{i+1}d^♭_+` on `V_k`** for `1 ≤ i ≤ k`, with `z_i` the operator
`HJO.Sweep.zop` and **no scalar removed from either side**. This is the mixed
relation `HJO.Sweep.starCommCM_cmDPlus` in the convention `HJO.Sweep.zop` and hence `HJO.Sweep.zRep`
are actually written in.

`HJO.Sweep.zop_eq_conj` unwinds the recursion to `z_{i+1} = q^{-i}T_{i+1↘1}z_1T_{1↗i+1}` and
`HJO.Sweep.zopOneStar_eq` expands `z_1` to `q^k/(1-q)[d^*_+, d^♭_-]T^*_{k↘1}`;
`HJO.Sweep.trainDown_starComm_trainUp_dplus` is the resulting identity of words, and the two
scalars — `q^{1-i}q^k/(1-q)` on the left against `q^{-i}q^{k+1}/(1-q)` on the right — are equal.

`q ≠ 0` is read for the braid inverses and for that cancellation. **`q ≠ 1` is not needed**: the
factor `(1-q)^{-1}` is the same value on both sides whatever it is. -/
theorem dplus_zop (q u : L) (hq : q ≠ 0) {k i : ℕ} (hi : 1 ≤ i) (hik : i ≤ k)
    {F : Total L} (hF : F ∈ piece L k) :
    dplus q k (zop q u k i F) = zop q u (k + 1) (i + 1) (dplus q k F) := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have hscal : (q ^ (j + 1))⁻¹ * (q ^ (k + 1) / (1 - q))
      = (q ^ j)⁻¹ * (q ^ k / (1 - q)) := by
    have h1 : (q ^ (j + 1))⁻¹ = q⁻¹ * (q ^ j)⁻¹ := by rw [pow_succ, mul_inv, mul_comm]
    have h2 : q ^ (k + 1) / (1 - q) = q * (q ^ k / (1 - q)) := by rw [pow_succ]; ring
    rw [h1, h2, mul_mul_mul_comm, inv_mul_cancel₀ hq, one_mul]
  rw [zop_eq_conj q u hq j (by omega), zop_eq_conj q u hq (j + 1) (by omega),
    zopOneStar_eq, zopOneStar_eq]
  simp only [LinearMap.smul_apply, Module.End.mul_apply, map_smul, smul_smul]
  rw [hscal, trainDown_starComm_trainUp_dplus q u hq (show 1 ≤ j + 1 by omega) hik hF]

end Newton

end Sweep

end HJO
