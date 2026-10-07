/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CMStructure.CmCommutator
public import HJO.CMStructure.StarEasy
public import HJO.CMStructure.VmodGenerators
public import HJO.CMStructure.VmodRaising
public import HJO.CarlssonMellit.BopModified
public meta import HJO.Attr

/-! # The two kernel generators of Mellit's structure theorem, on the unit

Mellit's structure theorem presents `V_*` as `𝔸̃𝟏_0` modulo an explicit two-generator ideal
`ℐ`. This file evaluates the two generators of `ℐ` on the unit of `V_k`, which is the computation
the theorem's kernel inclusion rests on: with `d^♭_-`, `d^♭_+` the modified operators of
`HJO.Sweep.dminus` and `HJO.Sweep.dplus_eq_ascWord` and `d^*_+` the conjugate raising operator of
`HJO.Sweep.dplusStar`, for every `k ≥ 0`

* `d^♭_-(d^*_+(1)) = 1` in `V_k`, and
* `d^♭_+(1) + q^ky_1d^*_+(1) = 0` in `V_{k+1}`.

The first is `B_0(1) = e_0 = 1`: the starred raising operator fixes the unit, and the modified
lowering operator on `y_{k+1}^0 \cdot 1` is the Hall–Littlewood operator `B_0` at `1`, whose value
is the coefficient of `z^0` in `\sum_{n≥0}(-z)^ne_n`. The second is the whole ascending word
`T_{1↗k+1}` moved past the top variable at once, `T_{1↗k+1}(y_{k+1}) = q^ky_1T^*_{1↗k+1}(1)`, the
starred word fixing the unit letter by letter.

## Main results

* `HJO.Sweep.dminus_dplusStar_map_one` and
  `HJO.Sweep.dplus_map_one_add_auxVar_mul_dplusStar_map_one` — the two identities, in the shape
  `HJO.Sweep.dminus_dplusStar_map_one` states them.
* `HJO.Sweep.dplus_map_one` — the value `d^♭_+(1) = -q^ky_1` on its own, which is the second
  identity with the starred operator eliminated and the form wanted when computing `φ` on a word
  of `𝔸̃`.
* `HJO.Sweep.braidInv_map_one`, `HJO.Sweep.trainDownEnd_map_one` — the inverted braid letter and
  the starred ascending word fix the unit.

## Implementation notes

**The second identity reads `q ≠ 0`, which the statement as usually written does not display.** The
hypothesis enters twice, in the same place each time: through `HJO.Sweep.cmAscWord_auxVar_last_mul`,
whose per-letter conjugation `T_i(y_{i+1}H) = qy_iT_i^{-1}H` is an identity about the inverse; and
through `T_i^{-1}(1) = 1`, since `T_i^{-1} = q^{-1}(T_i + (q-1))` is a two-sided inverse of `T_i`
only when `q` is invertible. The usual proof names the second of these — "and hence
`T_i^{-1}(1) = 1`" — so it is the argument that needs `q ≠ 0`, not the encoding. The first identity
is free of it.

**`Algebra ℚ L` on the first identity is carried by `d^♭_-` itself.** The modified lowering
operator multiplies by the elementary symmetric functions `e_j`, and `HJO.Sym.elemSymm` defines
those from the power sums by Newton's identities, which divide by `j`; so `HJO.Sweep.dminus` is
defined only over a `ℚ`-algebra, and the hypothesis is the operator's rather than an extra demand of
this statement. The second identity does not mention `d^♭_-` and so does not carry it.

**The `1 ∈ V_k` is not a hypothesis but a value.** Both statements are read at the unit
of the total space, and `1` lies in every `piece L k`; where the membership is needed —
`HJO.Sweep.dminus_auxVar_pow_mul` asks for `F ∈ V_k` — it is discharged by `one_mem`. So no
graded-piece plumbing appears, and the identities hold verbatim in `HJO.Sweep.Total`.

**The parameter `u` of `d^*_+` is unconstrained.** The cyclic shift `cy_{k+1}` wraps `y_{k+1}` to
`uy_1`, and neither identity reads the wrapped letter: the first because `d^*_+(1) = 1` before any
letter is met, the second because `d^*_+` occurs only through that same value.

## References

This file proves `HJO.Sweep.dminus_dplusStar_map_one`, using `HJO.Sweep.dplusStar`,
`HJO.Sweep.dminus`, `HJO.Sweep.dplus_eq_ascWord`, `HJO.Sweep.exists_isDpaAction_mod` and
`HJO.Sweep.exists_isDpaAction_mellit`; its proof reads `HJO.Sym.elemSymm`, `HJO.Sweep.qshift`,
`HJO.Sym.Bop`, `HJO.Sweep.auxVar_sub_mul_braid`, `HJO.Sweep.dminus_auxVar_pow_mul`,
`HJO.Sweep.cmAscWord_auxVar_last_mul` and `HJO.Sweep.dplusStar_map_one`. A. Mellit, *Toric braids
and `(m, n)`-parking functions*, §3.
-/

@[expose] public section

namespace HJO.Sweep

section Field

variable {L : Type*} [Field L]

/-! ### The inverted braid letters and the starred ascending word fix the unit -/

/-- **`T_i^{-1}(1) = 1`**: `T_i` fixes the unit (`HJO.Sweep.braid_map_one`), so
`T_i^{-1}(1) = q^{-1}(1 + (q-1)) = 1`. This is the "and hence `T_i^{-1}(1) = 1`", whose
`q ≠ 0` is the invertibility of `T_i` itself. -/
theorem braidInv_map_one (q : L) (hq : q ≠ 0) (i : ℕ) : braidInv q i (1 : Total L) = 1 := by
  rw [braidInv_apply, braid_map_one, mul_one, ← scal_one (L := L), ← scal_add, ← scal_mul,
    show q⁻¹ * (1 + (q - 1)) = 1 by
      rw [show (1 : L) + (q - 1) = q by ring, inv_mul_cancel₀ hq]]

/-- **`T^*_{1↗b}(1) = 1`** for `b ≥ 1`, the starred ascending word being a product of inverted braid
letters. Induction along `HJO.Sweep.trainDownEnd_succ`, the base case `b = 1` being the empty
word. -/
theorem trainDownEnd_map_one (q : L) (hq : q ≠ 0) {b : ℕ} (hb : 1 ≤ b) :
    trainDownEnd q 1 b (1 : Total L) = 1 := by
  induction b with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le hb with h | h
    · rw [show n + 1 = 1 from h.symm, trainDownEnd, Braid.trainDown_self, Module.End.one_apply]
    · rw [trainDownEnd_succ q (by omega)]
      change trainDownEnd q 1 n (braidInv q n (1 : Total L)) = 1
      rw [braidInv_map_one q hq, ih (by omega)]

/-! ### The modified raising operator on the unit -/

/-- **`d^♭_+(1) = -q^ky_1`.** By `HJO.Sweep.dplus_eq_ascWord` and `HJO.Sweep.qshift` the value is
`-T_{1↗k+1}(y_{k+1})`, the substitution `τ_{k+1,k+1}` fixing the unit as an algebra map, and
`HJO.Sweep.cmAscWord_auxVar_last_mul` turns that into `-q^ky_1T^*_{1↗k+1}(1) = -q^ky_1`.

This is the second identity of `HJO.Sweep.dminus_dplusStar_map_one` with the starred operator
eliminated; it is the form that computes, `d^*_+` entering there only through `d^*_+(1) = 1`. -/
theorem dplus_map_one (q : L) (hq : q ≠ 0) (k : ℕ) :
    dplus q k (1 : Total L) = -(scal (q ^ k) * auxVar 1) := by
  rw [dplus_eq_ascWord, map_one, cmAscWord_auxVar_last_mul q hq k 1,
    trainDownEnd_map_one q hq (by omega), mul_one]

/-! ### The two generators of Mellit's kernel ideal, evaluated on the unit -/

section Newton

variable [Algebra ℚ L]

/-- **`d^♭_-(d^*_+(1)) = 1`**, the first identity of `HJO.Sweep.dminus_dplusStar_map_one`.

`HJO.Sweep.dplusStar_map_one` gives `d^*_+(1) = 1 ∈ V_{k+1}`, and `HJO.Sweep.dminus_auxVar_pow_mul`
at `i = 0` and `F = 1` reads `d^♭_-(1) = B_0(1)`, which by `HJO.Sym.Bop` is the coefficient of `z^0`
in `1[X-(q-1)/z]\sum_{n≥0}(-z)^ne_n = \sum_{n≥0}(-z)^ne_n`, namely `e_0 = 1` by
`HJO.Sym.elemSymm`. -/
@[hjo "lem_vmod_kernel_generators"]
theorem dminus_dplusStar_map_one (q u : L) (k : ℕ) :
    dminus q (k + 1) (dplusStar q u k (1 : Total L)) = 1 := by
  have h := dminus_auxVar_pow_mul q k 0 (one_mem (piece L k))
  rw [pow_zero, one_mul] at h
  rw [dplusStar_map_one, h, bopExt_one, Sym.elemSymmAlt_natCast, pow_zero, one_mul,
    Sym.elemSymm_zero, map_one]

omit [Algebra ℚ L] in
/-- **`d^♭_+(1) + q^ky_1d^*_+(1) = 0`**, the second identity of
`HJO.Sweep.dminus_dplusStar_map_one`: `HJO.Sweep.dplus_map_one` gives `d^♭_+(1) = -q^ky_1` and
`HJO.Sweep.dplusStar_map_one` gives `d^*_+(1) = 1`, so the second summand is `q^ky_1`. -/
@[hjo "lem_vmod_kernel_generators"]
theorem dplus_map_one_add_auxVar_mul_dplusStar_map_one (q u : L) (hq : q ≠ 0) (k : ℕ) :
    dplus q k (1 : Total L) + scal (q ^ k) * auxVar 1 * dplusStar q u k (1 : Total L) = 0 := by
  rw [dplusStar_map_one, mul_one, dplus_map_one q hq, neg_add_cancel]

end Newton

end Field

end HJO.Sweep
