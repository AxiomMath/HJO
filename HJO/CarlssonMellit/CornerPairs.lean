/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.CornerCommute
public meta import HJO.Attr

/-! # A loop against the pair of corner elements it moves

`T_j` does not commute with `y_j` or with `y_{j+1}`, but it does commute with their *product*: the
two Hecke corrections are `(1-q)y_j` and `(q-1)y_j`, and they cancel once the corner elements are
known to commute. This file proves that, and records the §8.27 reading of the general commutation.

## Main results

* `HJO.Dyck.Aq.Tg_mul_yElt_pair`: `T_jy_jy_{j+1} = y_jy_{j+1}T_j`.
* `HJO.Dyck.Aq.yElt_mul_Tg_comm_mellit`: `y_iT_j𝟏_k = T_jy_i𝟏_k` for `2 ≤ j ≤ k-1` with
  `j ∉ {i-1, i}`.

## Implementation notes

**A gap in the §8.27 proof, worth recording.** `HJO.Dyck.Aq.yElt_mul_Tg_comm_mellit` is the same
claim as `HJO.Dyck.Aq.yElt_mul_Tg_comm` with `j` restricted to `2 ≤ j ≤ k-1`, and §8.27 gives it a
different proof: induction on `i`, using `y_{i+1} = qT_i^{-1}y_iT_i^{-1}` and
`T_jT_i = T_iT_j`. That step needs `|j - i| > 1`, and the hypothesis available at the target index
`i+1` is only `j ∉ {i, i+1}` — which leaves `j = i-1`, where neither `T_jT_i = T_iT_j` nor the
induction hypothesis (whose own range excludes `j = i-1`) is available. The text asserts
`j ≠ i-1` at that point without deriving it. The claim is true, and `j = i-1` is exactly the case
that needs the two-step braid move `HJO.Dyck.Aq.braid_conj_move` of the §8.22 proof, so
`HJO.Dyck.Aq.yElt_mul_Tg_comm` is what this lemma is proved from.

The pair identity is an abstract ring move: with `TX = YT + cX` and `TY = XT + dX` and `c + d = 0`,
`T` commutes with `XY` as soon as `X` and `Y` commute. Nothing about `𝔸_q` is read.

## References

E. Carlsson and
A. Mellit, *A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018) 661--697,
Section 3.
-/

@[expose] public section

namespace HJO.Dyck.Aq

/-- If `T` moves `X` to `Y` and `Y` to `X` with corrections that cancel, and `X` and `Y` commute,
then `T` commutes with `XY`. -/
theorem comm_pair_aux {K₀ : Type*} [CommRing K₀] {A₀ : Type*} [Ring A₀] [Algebra K₀ A₀]
    {T X Y : A₀} {c d : K₀} (hcd : c + d = 0) (hL : T * X = Y * T + c • X)
    (hR : T * Y = X * T + d • X) (hC : Y * X = X * Y) : T * (X * Y) = X * Y * T := by
  calc T * (X * Y) = T * X * Y := by rw [mul_assoc]
    _ = (Y * T + c • X) * Y := by rw [hL]
    _ = Y * (T * Y) + c • (X * Y) := by rw [add_mul, smul_mul_assoc, mul_assoc]
    _ = Y * (X * T + d • X) + c • (X * Y) := by rw [hR]
    _ = Y * X * T + d • (Y * X) + c • (X * Y) := by rw [mul_add, mul_smul_comm, ← mul_assoc]
    _ = X * Y * T + d • (X * Y) + c • (X * Y) := by rw [hC]
    _ = X * Y * T := by
        rw [add_assoc, ← add_smul, add_comm d c, hcd, zero_smul, add_zero]

variable {K : Type*} [CommRing K] {q : K} [Invertible q] [Invertible (q - 1)]

/-- **A loop commutes with the product of the two corner elements it moves**:
`T_jy_jy_{j+1} = y_jy_{j+1}T_j`. The two Hecke corrections are `(1-q)y_j` and `(q-1)y_j`; they
cancel once `y_j` and `y_{j+1}` are known to commute. -/
@[hjo "lem_cm_tj_commutes_yy"]
theorem Tg_mul_yElt_pair {k j : ℕ} (h1 : 1 ≤ j) (hjk : j < k) :
    Tg K q k (j - 1) * (yElt K q k j * yElt K q k (j + 1))
      = yElt K q k j * yElt K q k (j + 1) * Tg K q k (j - 1) :=
  comm_pair_aux (by ring) (Tg_mul_yElt h1 hjk) (Tg_mul_yElt_succ h1 hjk)
    (yElt_comm (by omega) (by omega) (by omega) (by omega))

/-- **`y_i` commutes with every loop that does not touch it**, in the §8.27 range `2 ≤ j ≤ k-1`.
§8.27 gives this lemma its own induction on `i`, but that induction does not reach the case
`j = i-1` — see this file's implementation notes — so it is proved here from the §8.22 form, whose
proof does cover it. -/
@[hjo "lem_dpa_y_braid"]
theorem yElt_mul_Tg_comm_mellit {k i s : ℕ} (h1 : 1 ≤ i) (hik : i ≤ k) (_hs1 : 1 ≤ s)
    (hs : s + 2 ≤ k) (hadm : s + 3 ≤ i ∨ i ≤ s) :
    yElt K q k i * Tg K q k s = Tg K q k s * yElt K q k i :=
  yElt_mul_Tg_comm h1 hik hs hadm

end HJO.Dyck.Aq
