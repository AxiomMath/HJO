/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.MellitStarVertex
public import HJO.Shuffle.MellitLhsSlopeMediant
public import HJO.Shuffle.SweepWitnessAppend
public import HJO.Collinear.EsymmIndependent
public meta import HJO.Attr

/-! # The straight monomials `πY^aZ^bΦ`, and what they are not

`HJO/Shuffle/MellitStarVertex.lean` proves `P = qu·YZ - ZY` on `V_1`, where `Y = -(y_1·)` and
`Z = (qu)^{-1}z_1` are the two letters of `HJO.Sweep.slopeOperator` and
`P = y_1d^*_+{}^{(0)}d_-^{(1)}` is the term the general clause `HJO.Mellit.LhsSlope` consumes. Read
as `ZY = qu·YZ - P`, that straightens every word in the two letters to the **straight monomials**
`Y^aZ^b` together with words containing `P`, whose matrix elements the induction hypothesis
supplies. So the clause family is equivalent to evaluating

`πY^aZ^bΦ`,   `Φ f = y_1d^*_+{}^{(0)}(Cf)` (`HJO.Mellit.slopeArg`),  `π = d_-^{(1)}`.

**This file evaluates them.** The answer is one operator iterated, and at the vacuum it is
independent of `b` — which refutes the natural guess about what they are.

## The evaluation

The vertex relation `HJO.Sweep.zopOneStar_one_auxVar_mul_of_mem_piece` says
`z_1(y_1G) = quy_1(z_1G + d^*_+{}^{(0)}(d_-^{(1)}G))` on `V_1`. The letter `Z` carries the
`(qu)^{-1}` that cancels the `qu`, so in the letters that identity reads

`Z(y_1G) = y_1·T(G)`,   `T := z_1 + d^*_+{}^{(0)}d_-^{(1)}`   (`HJO.Sweep.vertexStep`),

and `T` is an endomorphism of `V_1` (`HJO.Sweep.vertexStep_mem_piece`). **One `y_1` passes through
`Z` at the cost of replacing `z_1` by `T`**, so it passes through every power of `Z`, and since
`Φf = y_1·d^*_+(Cf)` already carries that `y_1`,

`Y^aZ^b(Φ f) = (-1)^a·y_1^{a+1}·T^b(d^*_+{}^{(0)}(Cf))`

(`HJO.Sweep.straightMonomial_slopeArg`). That is the whole evaluation: a single power of `y_1`
against the `b`-th iterate of `T`, with no word combinatorics left. `T` itself is computable on
`V_1` — `HJO.Sweep.vertexStep_auxVar_pow_mul_C` gives
`T(y_1^mCA) = (1-q)^{-1}(d^*_+(C(B_mA)) - q·B_m(d^*_+(CA)))` off the two halves of
`HJO.Sweep.zop` (`HJO.Sweep.dminus_one_auxVar_pow_mul_C`,
`HJO.Sweep.dminus_two_dplusStar_one_auxVar_pow_mul_C`), for `q ≠ 1`.

## The vacuum, in closed form

`T(1) = 1` (`HJO.Sweep.vertexStep_one`): the two halves of `HJO.Sweep.zop` agree on the unit, both
being `B_0(1) = e_0 = 1`, so `z_1(1) = 0` and `T(1) = d^*_+(d_-(1)) = 1`. Hence `T^b(1) = 1` and

`πY^aZ^bΦ(1) = -e_{a+1}`   for **every** `a, b ≥ 0`

(`HJO.Sweep.dminus_straightMonomial_slopeArg_one`). The value does not depend on `b` at all. That is
the file's main computation and it is unconditional in `b`.

## What that refutes

`Y^a` and `Z^b` are themselves slope operators — `Y^a = Ξ_{1,a+1}` and `Z^b = Ξ_{b+1,1}` by
`HJO.Mellit.slopeEval_one_left` and `HJO.Mellit.slopeEval_one_right` — and the word `Y^aZ^b` has
`a` letters `y` and `b` letters `z`, which is the letter count of `β_{b+1,a+1}`. So the natural
guess is that the straight monomial is the slope operator at `(b+1,a+1)`, i.e. that
`πY^aZ^bΦ = (-1)^{a}Q_{b+1,a+1}` in the sign convention of `HJO.Mellit.LhsSlope`. **It is false at
every `q` and `u`**, already at `a = b = 1`:

* `πYZΦ(1) = -e_2` (above);
* `Q_{2,2}(1) = e_1^2 + (q+u)e_2` (`HJO.Sym.qop_two_two_apply_one`), the non-coprime branch of
  `HJO.Sym.Qop` at `slopeSplit 2 2 = (1,0)`;

and `-e_2 = -(e_1^2 + (q+u)e_2)` would force `e_1^2 + (q+u-1)e_2 = 0`, which fails in `Λ` for every
scalar because the elementary symmetric functions freely generate it
(`HJO.Sym.elemSymmSub_injective`). This is `HJO.Sweep.not_qop_two_two_eq_straightMonomial`, and it
is stronger than an exact-arithmetic witness at a single point such as `(q,u) = (3/7,5/11)`: the
guess is wrong on the whole parameter space, not at a point.

The mechanism is visible in the two formulas. The straight monomial's value at the vacuum is
`b`-independent, while `Q_{b+1,a+1}(1)` is not — `Q_{1,a+1}(1) = (-1)^{a+1}e_{a+1}` at `b = 0` and
`Q_{2,2}(1) = e_1^2 + (q+u)e_2` at `a = b = 1` are not related by any substitution of `b`. So the
doubled slope is not reachable from width-`1` straight monomials.

Where it *does* come from is `HJO.Sym.Qop`'s own non-coprime branch, not the replicated actions: see
`HJO.Sym.qop_collinear_eq_bracket` and `HJO.Sweep.not_slopeActions_bridge` in
`HJO/Shuffle/MellitCollinearSplit.lean`. In particular it does not come from
`HJO.Sweep.exists_slopeActions`.

## The `(a,1)` column at the vacuum

`HJO/Shuffle/MellitLhsSlopeMediant.lean` records the `(a,1)` column with `a ≥ 2` as not
treated, and the straightening above needs it: `Z^b = Ξ_{b+1,1}` is one of the two boundary rows.
The `a = 0` case of the evaluation is `πZ^bΦ(1) = -e_1` for every `b`, so the clause at `(b+1,1)` at
`f = 1` says `Q_{b+1,1}(1) = -e_1` for every `b`. **That is a theorem**
(`HJO.Sym.qop_apply_one_of_snd_one`): `Split m 1 = (1,0)` (`HJO.Sym.split_snd_one`), so
`Q_{m,1} = M^{-1}(Q_{m-1,1}D_0 - D_0Q_{m-1,1})`, and at the vacuum `D_0(1) = 1` while
`D_0(e_1) = (1-M)e_1`, so the bracket is `-Me_1` at every `m`. Together with the evaluation above
this settles **the whole `(a,1)` column at `f = 1`, for every `a`** — the vacuum half of the
column, uniformly in `a` rather than one instance at a time. It does *not* settle the column at
a general `f`: nothing here evaluates `T` on `d^*_+(Cf)` for general `f`, and the `b`-independence
at the vacuum is exactly the reason `f = 1` cannot see the column's content.

## Genericity

* `HJO.Sweep.vertexStep_one` and `HJO.Sweep.zopOneStar_one_one`: **no hypothesis on `q` or `u`**.
  The scalar `q/(1-q)` of `HJO.Sweep.zop` is carried symbolically and multiplies `0`.
* `HJO.Sweep.vertexStep_auxVar_pow_mul_C`: `q ≠ 1`, and that exclusion is **real** — at `q = 1` the
  operator `T` degenerates to `d^*_+d_-`, which is the first of the formula's two summands alone.
* `HJO.Sweep.straightMonomial_slopeArg` and the vacuum evaluation: `q ≠ 1`, `q ≠ 0`, `u ≠ 0`, and
  **all three are necessary for the statement**, proved so by
  `HJO.Sweep.not_dminus_straightMonomial_slopeArg_one_of_zLetter_eq_zero` with
  `HJO.Sweep.zLetter_eq_zero_of_mul_eq_zero` and `HJO.Sweep.zLetter_eq_zero_of_q_eq_one`. The reason
  is the same for all three and is *not* the proof: the letter `Z = (qu)^{-1}z_1` of
  `HJO.Sweep.slopeOperator` is the zero map at each of them, so every `Z`-containing word
  collapses. The underlying content needs only `q ≠ 1` — that is the inverse-free
  `HJO.Sweep.zopOneStar_one_auxVar_mul_eq_vertexStep`. **No hypothesis on `u - 1` anywhere.**
* `HJO.Sym.qop_two_two_apply_one` and `HJO.Sym.qop_apply_one_of_snd_one`: `M = (1-q)(1-u) ≠ 0`, the
  normalisation of `HJO.Sym.Qop`, and nothing else. No hypothesis on `u` beyond that, and the
  refutation inherits exactly the union — `q ∉ {0,1}`, `u ∉ {0,1}`.

## What this file does not prove

The straight monomials are not slope words for `a, b ≥ 1` — that is the content of the refutation —
so they realise no slope-word statement; `HJO.Sym.Qop` is the definition of `Q_{m,n}` rather than of
any evaluation of it, and the general-slope form of
`HJO.Sweep.dop_eq_neg_dminusCM_auxVar_pow_dplusStar` is `HJO.Mellit.LhsSlope`, which is not proved
here.

## References

`HJO.Sweep.dop_eq_neg_dminusCM_auxVar_pow_dplusStar` (general slope), `HJO.Sweep.slopeOperator`,
`HJO.Sweep.zop`, `HJO.Sym.Qop`, `HJO.Sym.Split`, `HJO.Sweep.exists_slopeActions`. Transcribing A.
Mellit,
*Toric braids and `(m, n)`-parking functions*, §3, §6.
-/

@[expose] public section

namespace HJO.Sym

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-! ### Two values of the basic operator at index `0` -/

/-- **`D_0(e_1) = (1-M)e_1`.** `HJO.Sym.dop_elemSymm` at `k = 0`, `r = 1`: the two kernel values are
`κ(e_0) = 1` and `κ(e_1) = M`, paired with `e_0` and `-e_1`. This is the value the `(a,1)` column
turns on — `D_0` is the operator `HJO.Sym.Qop`'s split at `(m,1)` produces, `Split m 1` being
`(1,0)`. -/
theorem dop_zero_elemSymm_one (q u : L) :
    Dop q u 0 (elemSymm L 1) = (1 - (1 - q) * (1 - u)) • elemSymm L 1 := by
  rw [dop_elemSymm, Finset.sum_range_succ, Finset.sum_range_one,
    Bglx.paramPleth_elemSymm_zero, Bglx.paramPleth_elemSymm_one_eq]
  simp only [MvPolynomial.smul_eq_C_mul, map_sub, map_mul, map_one, Nat.sub_zero, Nat.sub_self]
  norm_num [elemSymm_zero]
  ring

/-- **`D_0(e_2) = e_2 - Me_1^2 - (q+u)Me_2`.** `HJO.Sym.dop_elemSymm` at `k = 0`, `r = 2`, reading
all three kernel values `1`, `M` and `-(q+u)M` against `e_0`, `-e_1` and `e_2`. This is the value
that makes `Q_{2,2}(1)` carry an `e_1^2`, which is what the straight monomial `πYZΦ` does not. -/
theorem dop_zero_elemSymm_two (q u : L) :
    Dop q u 0 (elemSymm L 2)
      = elemSymm L 2 - ((1 - q) * (1 - u)) • (elemSymm L 1 * elemSymm L 1)
        - ((q + u) * ((1 - q) * (1 - u))) • elemSymm L 2 := by
  rw [dop_elemSymm, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
    Bglx.paramPleth_elemSymm_zero, Bglx.paramPleth_elemSymm_one_eq,
    Bglx.paramPleth_elemSymm_two_eq]
  simp only [MvPolynomial.smul_eq_C_mul, map_sub, map_add, map_mul, map_neg, map_one,
    Nat.sub_zero, Nat.sub_self]
  norm_num [elemSymm_zero]
  ring

/-! ### The `(a,1)` column at the vacuum -/

/-- **`Q_{m,1}(1) = -e_1` for every `m ≥ 1`.**

`Split m 1 = (1,0)` (`HJO.Sym.split_snd_one`), so `HJO.Sym.Qop`'s primitive recursion at `(m,1)`
with `m ≥ 2` reads `Q_{m,1} = M^{-1}(Q_{m-1,1}D_0 - D_0Q_{m-1,1})`, `Q_{1,0}` being `D_0`. At the
vacuum `D_0(1) = e_0 = 1`, so the first branch is the inductive value `-e_1`, and the second is
`-D_0(e_1) = -(1-M)e_1` by `HJO.Sym.dop_zero_elemSymm_one`. The bracket is `-Me_1` at every `m`, so
the normalisation returns `-e_1` and the column is constant.

This is the `Λ`-side half of the `(a,1)` column at `f = 1`; the sweep side is
`HJO.Sweep.dminus_straightMonomial_slopeArg_one` at `a = 0`, whose value `-e_1` does not depend on
`b` either. `M ≠ 0` is the only hypothesis. -/
theorem qop_apply_one_of_snd_one (hM : (1 - q) * (1 - u) ≠ 0) {m : ℕ} (hm : 1 ≤ m) :
    Qop q u m 1 (1 : Lambda L) = -elemSymm L 1 := by
  induction m with
  | zero => omega
  | succ k ih =>
      rcases Nat.lt_or_ge k 1 with hk | hk
      · have hk0 : k = 0 := by omega
        rw [hk0, qop_one, dop_apply_one]
        norm_num
      · have hlt : 1 < k + 1 := by omega
        have hcop : Nat.Coprime (k + 1) 1 := Nat.coprime_one_right _
        have hprev := ih hk
        rw [qop_of_coprime q u hlt hcop, split_snd_one]
        simp only [Nat.add_sub_cancel, Nat.sub_zero]
        rw [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
          qop_of_le_one q u 0 (le_refl 1)]
        have hd0 : Dop q u 0 (1 : Lambda L) = 1 := by
          rw [dop_apply_one]
          norm_num [elemSymm_zero]
        rw [hd0, hprev, map_neg, dop_zero_elemSymm_one]
        rw [show -((1 - (1 - q) * (1 - u)) • elemSymm L 1)
            = -elemSymm L 1 + ((1 - q) * (1 - u)) • elemSymm L 1 from by
          simp only [MvPolynomial.smul_eq_C_mul, map_sub, map_mul, map_one]
          ring]
        rw [show (-elemSymm L 1 - (-elemSymm L 1 + ((1 - q) * (1 - u)) • elemSymm L 1))
            = ((1 - q) * (1 - u)) • -elemSymm L 1 from by
          simp only [MvPolynomial.smul_eq_C_mul, map_sub, map_mul, map_one]
          ring]
        rw [inv_smul_smul₀ hM]

/-! ### `Q_{2,2}` at the vacuum -/

/-- **`Q_{2,2}(1) = e_1^2 + (q+u)e_2`.**

`(2,2)` is *not* coprime, so `HJO.Sym.Qop` takes its extension branch
(`HJO.Sym.qop_of_not_coprime`): the split of the primitive pair `(1,1)` is `(1,0)`, giving
`Q_{2,2} = M^{-1}(D_2D_0 - D_0D_2)`. At the vacuum `D_0(1) = 1` and `D_2(1) = e_2`, so the bracket
is `e_2 - D_0(e_2)`, which `HJO.Sym.dop_zero_elemSymm_two` makes `Me_1^2 + (q+u)Me_2`.

`M ≠ 0` and nothing else. The `e_1^2` is the whole point: it is what the straight monomial `πYZΦ`
cannot produce, since its value at the vacuum is `-e_2`. -/
theorem qop_two_two_apply_one (hM : (1 - q) * (1 - u) ≠ 0) :
    Qop q u 2 2 (1 : Lambda L)
      = elemSymm L 1 * elemSymm L 1 + (q + u) • elemSymm L 2 := by
  have hnc : ¬ Nat.Coprime 2 2 := by decide
  have hsplit : slopeSplit 2 2 = ((1 : ℕ), (0 : ℕ)) := by
    rw [slopeSplit, show Nat.gcd 2 2 = 2 from rfl, show (2 : ℕ) / 2 = 1 from rfl, primitiveSplit]
    norm_num
  rw [qop_of_not_coprime q u (by norm_num) hnc, hsplit]
  simp only [Nat.sub_zero]
  rw [qopPrim_of_le_one q u 2 (le_refl 1), qopPrim_of_le_one q u 0 (le_refl 1)]
  have hd0 : Dop q u 0 (1 : Lambda L) = 1 := by
    rw [dop_apply_one]
    norm_num [elemSymm_zero]
  have hd2 : Dop q u 2 (1 : Lambda L) = elemSymm L 2 := by
    rw [dop_apply_one]
    norm_num
  rw [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
    hd0, hd2, dop_zero_elemSymm_two]
  rw [show (elemSymm L 2 - (elemSymm L 2 - ((1 - q) * (1 - u)) • (elemSymm L 1 * elemSymm L 1)
        - ((q + u) * ((1 - q) * (1 - u))) • elemSymm L 2))
      = ((1 - q) * (1 - u)) • (elemSymm L 1 * elemSymm L 1 + (q + u) • elemSymm L 2) from by
    simp only [MvPolynomial.smul_eq_C_mul, map_sub, map_add, map_mul, map_one]
    ring]
  rw [inv_smul_smul₀ hM]

/-! ### `e_1^2` and `e_2` are linearly independent -/

/-- **`e_1^2 + ce_2 ≠ 0` for every scalar `c`.** The substitution `p_k ↦ e_k` is injective over a
field of characteristic zero (`HJO.Sym.elemSymmSub_injective`), so a linear relation among the
`e`-monomials pulls back to one among the free generators `p_1^2` and `p_2`, and the coefficient of
`p_1^2` there is `1`.

This is what makes `HJO.Sweep.not_qop_two_two_eq_straightMonomial` hold at *every* `q` and `u`
rather than at a numeric point: the defect `e_1^2 + (q+u-1)e_2` is nonzero whatever `q + u` is. -/
theorem elemSymm_one_sq_add_smul_elemSymm_two_ne_zero (c : L) :
    elemSymm L 1 * elemSymm L 1 + c • elemSymm L 2 ≠ 0 := by
  intro h
  have hpre : elemSymmSub L (MvPolynomial.X 0 * MvPolynomial.X 0 + c • MvPolynomial.X 1)
      = elemSymm L 1 * elemSymm L 1 + c • elemSymm L 2 := by
    rw [map_add, map_mul, map_smul, elemSymmSub_X, elemSymmSub_X]
  have hzero : (MvPolynomial.X 0 * MvPolynomial.X 0 + c • MvPolynomial.X 1 : Lambda L) = 0 :=
    elemSymmSub_injective L (by rw [hpre, h, map_zero])
  have hev := congrArg (MvPolynomial.aeval fun i : ℕ => if i = 0 then (1 : L) else 0) hzero
  simp at hev

/-- **`e_{n+1} ≠ 0`.** Same route: `e_{n+1}` is the image of the free generator `p_{n+1}` under the
injective substitution `HJO.Sym.elemSymmSub`. Needed to say that the degenerate-parameter values of
the straight monomial are *wrong* and not merely different. -/
theorem elemSymm_succ_ne_zero (n : ℕ) : elemSymm L (n + 1) ≠ 0 := by
  intro h
  have hps := elemSymmSub_powerSum L (k := n + 1) (by omega)
  rw [h] at hps
  have h0 : (powerSum L (n + 1) : Lambda L) = 0 :=
    elemSymmSub_injective L (by rw [hps, map_zero])
  rw [Bglx.powerSum_succ_eq_X] at h0
  exact MvPolynomial.X_ne_zero _ h0

end HJO.Sym

namespace HJO.Sweep

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-! ### `T = z_1 + d^*_+ d_-`, the operator one `y_1` costs to pass through `Z` -/

/-- **The vertex step `T = z_1 + d^*_+{}^{(0)}d_-^{(1)}` on `V_1`.** The combination the vertex
relation `HJO.Sweep.zopOneStar_one_auxVar_mul_of_mem_piece` produces when a factor `y_1` is moved
out of `z_1`: that relation reads `z_1(y_1G) = quy_1·T(G)`, so `T` is what the letter `Z` becomes
once its argument's leading `y_1` has been extracted.

Neither summand alone is a letter of `HJO.Sweep.slopeOperator`; the sum is what the two letters
`Y` and `Z` generate, by `HJO.Sweep.auxVar_mul_dplusStar_dminus_of_mem_piece_one`. -/
noncomputable def vertexStep (q u : L) : Module.End L (Total L) :=
  zopOneStar q u 1 + dplusStar q u 0 * dminus q 1

theorem vertexStep_apply (q u : L) (G : Total L) :
    vertexStep q u G = zopOneStar q u 1 G + dplusStar q u 0 (dminus q 1 G) := rfl

/-- **`T` is an endomorphism of `V_1`.** `z_1` preserves `V_1` (`HJO.Sweep.zopOneStar_mem_piece`),
and `d^*_+{}^{(0)}d_-^{(1)}` goes `V_1 → V_0 → V_1`. -/
theorem vertexStep_mem_piece (q u : L) {G : Total L} (hG : G ∈ piece L 1) :
    vertexStep q u G ∈ piece L 1 :=
  add_mem (zopOneStar_mem_piece q u le_rfl hG)
    (dplusStar_mem_piece q u (dminus_mem_piece q 1 hG))

theorem vertexStep_pow_mem_piece (q u : L) (b : ℕ) {G : Total L} (hG : G ∈ piece L 1) :
    (vertexStep q u ^ b) G ∈ piece L 1 := by
  induction b with
  | zero => simpa using hG
  | succ c ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact vertexStep_mem_piece q u ih

/-- **`d_-(1) = 1`** at every level: the unit is `y_{k+1}^0·C1`, and `B_0(1) = e_0 = 1`. -/
theorem dminus_one (q : L) (k : ℕ) : dminus q (k + 1) (1 : Total L) = 1 := by
  have h := dminus_auxVar_pow_mul_C q k 0 (1 : Sym.Lambda L)
  rw [pow_zero, one_mul, MvPolynomial.C_1] at h
  rw [h, show Sym.Bop q ((0 : ℕ) : ℤ) (1 : Sym.Lambda L) = 1 from by
      rw [Sym.bop_one, Sym.elemSymmAlt_natCast]
      simp [Sym.elemSymm_zero],
    map_one]

/-- **`z_1(1) = 0` on `V_1`.** The train of `HJO.Sweep.zop` at `k = 1` is empty
(`HJO.Braid.trainUp_self`), `d^*_+` fixes the unit, and both lowering operators send it to the unit
(`HJO.Sweep.dminus_one`), so the two halves of the commutator cancel.

**No hypothesis on `q` or `u`**: the scalar `q/(1-q)` multiplies `0`. -/
theorem zopOneStar_one_one (q u : L) : zopOneStar q u 1 (1 : Total L) = 0 := by
  rw [zopOneStar, show trainUpEnd q 1 1 = 1 from Braid.trainUp_self _ _ 1, mul_one]
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.mul_apply, pow_one,
    Nat.sub_self]
  rw [dminus_one q 0, dplusStar_one, show (1 : ℕ) + 1 = 2 from rfl, dplusStar_one,
    dminus_one q 1, sub_self, smul_zero]

/-- **The vacuum is a fixed point of `T`: `T(1) = 1`.** `z_1(1) = 0` and
`d^*_+{}^{(0)}(d_-^{(1)}(1)) = 1`. This is the one fact that makes the straight monomials computable
at the vacuum, and it is why their value there does not depend on `b`.

**No hypothesis on `q` or `u`.** -/
theorem vertexStep_one (q u : L) : vertexStep q u (1 : Total L) = 1 := by
  rw [vertexStep_apply, zopOneStar_one_one, dminus_one q 0, dplusStar_one, zero_add]

theorem vertexStep_pow_one (q u : L) (b : ℕ) : (vertexStep q u ^ b) (1 : Total L) = 1 := by
  induction b with
  | zero => simp
  | succ c ih =>
      rw [pow_succ, Module.End.mul_apply, vertexStep_one, ih]

/-- **`T` on a monomial of `V_1` with arbitrary `Λ`-coefficient:**

`T(y_1^mCA) = (1-q)^{-1}(d^*_+{}^{(0)}(C(B_mA)) - q·B_m(d^*_+{}^{(0)}(CA)))`.

The two halves of `HJO.Sweep.zop` are `HJO.Sweep.dminus_one_auxVar_pow_mul_C` and
`HJO.Sweep.dminus_two_dplusStar_one_auxVar_pow_mul_C`, and the `d^*_+{}^{(0)}d_-^{(1)}` summand of
`T` is the first of them again — so `T` is the *same* two Hall–Littlewood values the commutator
carries, recombined with `q` in place of `1` and the scalar `(1-q)^{-1}` in place of `q/(1-q)`.

`q ≠ 1` is **real** here and not an artefact of clearing denominators: at `q = 1` the scalar of
`HJO.Sweep.zop` vanishes, so `T` degenerates to `d^*_+{}^{(0)}d_-^{(1)}`, which is the *first*
summand alone — the right-hand side, cleared of its `(1-q)^{-1}`, would read
`d^*_+(C(B_mA)) = B_m(d^*_+(CA))`, and that is the vertex relation's *undisplaced* case, not an
identity. No hypothesis on `u`. -/
theorem vertexStep_auxVar_pow_mul_C (hq1 : q ≠ 1) (m : ℕ) (A : Sym.Lambda L) :
    vertexStep q u ((auxVar 1 : Total L) ^ m * MvPolynomial.C A)
      = (1 - q)⁻¹ • (dplusStar q u 0 (MvPolynomial.C (Sym.Bop q (m : ℤ) A))
          - q • bopExt q (m : ℤ) (dplusStar q u 0 (MvPolynomial.C A : Total L))) := by
  have h1q : (1 : L) - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq1)
  rw [vertexStep_apply, zopOneStar_one_auxVar_pow_mul_C, dminus_one_auxVar_pow_mul_C]
  match_scalars <;> (field_simp; try ring)

/-! ### The straight monomials -/

/-- **The straight monomial `Y^aZ^b`**, `Y = -(y_1·)` and `Z = (qu)^{-1}z_1` the two letters of
`HJO.Sweep.slopeOperator` at `k = 1`.

These are not slope operators for `a, b ≥ 1` — `HJO.Sweep.not_qop_two_two_eq_straightMonomial` — but
they are what the rewriting rule `ZY = qu·YZ - P` of
`HJO.Sweep.auxVar_mul_dplusStar_dminus_of_mem_piece_one` straightens every word in the two letters
to. Their two boundary rows *are* slope operators: `Y^a = Ξ_{1,a+1}` and `Z^b = Ξ_{b+1,1}` by
`HJO.Mellit.slopeEval_one_left` and `HJO.Mellit.slopeEval_one_right`. -/
noncomputable def straightMonomial (q u : L) (a b : ℕ) : Module.End L (Total L) :=
  (-LinearMap.mulLeft L (auxVar 1 : Total L)) ^ a * ((q * u)⁻¹ • zop q u 1 1) ^ b

/-- **One `y_1` passes through the letter `Z` at the cost of replacing `z_1` by `T`:**
`Z(y_1G) = y_1·T(G)` on `V_1`.

This is `HJO.Sweep.zopOneStar_one_auxVar_mul_of_mem_piece` with the `(qu)^{-1}` of
`HJO.Sweep.slopeOperator` cancelled against the `qu` the vertex relation produces — which is the
only thing `q ≠ 0` and `u ≠ 0` are spent on here, no inverse surviving in the conclusion. `q ≠ 1` is
the real hypothesis, inherited from `HJO.Sweep.zop`'s scalar. -/
theorem zLetter_auxVar_mul (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) {G : Total L}
    (hG : G ∈ piece L 1) :
    ((q * u)⁻¹ • zop q u 1 1) ((auxVar 1 : Total L) * G)
      = (auxVar 1 : Total L) * vertexStep q u G := by
  rw [LinearMap.smul_apply, zop_one, zopOneStar_one_auxVar_mul_of_mem_piece hq1 hG,
    show (scal (q * u) : Total L) = algebraMap L (Total L) (q * u) from rfl,
    ← Algebra.smul_def, smul_mul_assoc, smul_smul, inv_mul_cancel₀ (mul_ne_zero hq0 hu0),
    one_smul, vertexStep_apply]

/-- **`Z^b(y_1G) = y_1·T^b(G)` on `V_1`**: the same `y_1` passes through every power of `Z`, `T`
being an endomorphism of `V_1` (`HJO.Sweep.vertexStep_mem_piece`). -/
theorem zLetter_pow_auxVar_mul (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) (b : ℕ) {G : Total L}
    (hG : G ∈ piece L 1) :
    (((q * u)⁻¹ • zop q u 1 1) ^ b) ((auxVar 1 : Total L) * G)
      = (auxVar 1 : Total L) * ((vertexStep q u ^ b) G) := by
  induction b with
  | zero => simp
  | succ c ih =>
      rw [pow_succ', Module.End.mul_apply, ih,
        zLetter_auxVar_mul hq0 hu0 hq1 (vertexStep_pow_mem_piece q u c hG),
        pow_succ', Module.End.mul_apply]

/-- **The straight monomial on the clause's argument, in closed form:**

`Y^aZ^b(y_1d^*_+{}^{(0)}(Cf)) = (-1)^a·y_1^{a+1}·T^b(d^*_+{}^{(0)}(Cf))`.

`HJO.Mellit.slopeArg` already carries the factor `y_1` that
`HJO.Sweep.zLetter_pow_auxVar_mul` moves through `Z^b`, and `Y^a` is multiplication by `(-y_1)^a`
(`HJO.Mellit.neg_mulLeft_pow_apply`). So the whole word collapses to one power of `y_1` against one
iterate of `T`, with no word combinatorics left: **this is the evaluation of the straight
monomials.** -/
@[hjo "lem_mellit_straight_monomial"]
theorem straightMonomial_slopeArg (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) (a b : ℕ)
    (f : Sym.Lambda L) :
    straightMonomial q u a b (Mellit.slopeArg q u f)
      = ((-1 : L) ^ a) • ((auxVar 1 : Total L) ^ (a + 1) *
          ((vertexStep q u ^ b) (dplusStar q u 0 (MvPolynomial.C f : Total L)))) := by
  have hmem : dplusStar q u 0 (MvPolynomial.C f : Total L) ∈ piece L 1 :=
    dplusStar_zero_C_mem_piece_one q u f
  rw [straightMonomial, Module.End.mul_apply, Mellit.slopeArg_def,
    zLetter_pow_auxVar_mul hq0 hu0 hq1 b hmem, Mellit.neg_mulLeft_pow_apply,
    show (-(auxVar 1 : Total L)) ^ a = algebraMap L (Total L) ((-1 : L) ^ a)
        * (auxVar 1 : Total L) ^ a from by
      rw [neg_pow, map_pow, map_neg, map_one],
    Algebra.smul_def, pow_succ]
  ring

/-! ### The vacuum value, and what it refutes -/

/-- **`πY^aZ^bΦ(1) = -e_{a+1}` for every `a` and `b`.**

`Φ1 = y_1` (`HJO.Mellit.slopeArg_one`), `d^*_+{}^{(0)}(C1) = 1`, and `T(1) = 1`
(`HJO.Sweep.vertexStep_one`), so the closed form of
`HJO.Sweep.straightMonomial_slopeArg` collapses to `(-1)^ay_1^{a+1}`, whose `d_-` is
`(-1)^a(-1)^{a+1}Ce_{a+1} = -Ce_{a+1}` by `HJO.Sweep.dminus_auxVar_pow`.

**The value does not depend on `b`.** At `b = 0` it is the clause at `(1,a+1)`
(`HJO.Mellit.lhsSlope_one_left` at `f = 1`); at `a = 0` it is the clause at `(b+1,1)`, whose `Λ`
side `HJO.Sym.qop_apply_one_of_snd_one` is likewise constant in `b`. For `a, b ≥ 1` the
`b`-independence is what refutes the identification with the slope operator at `(b+1,a+1)`. -/
@[hjo "lem_mellit_straight_monomial"]
theorem dminus_straightMonomial_slopeArg_one (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) (a b : ℕ) :
    dminus q 1 (straightMonomial q u a b (Mellit.slopeArg q u (1 : Sym.Lambda L)))
      = -(MvPolynomial.C (Sym.elemSymm L (a + 1)) : Total L) := by
  rw [straightMonomial_slopeArg hq0 hu0 hq1, MvPolynomial.C_1, dplusStar_one,
    vertexStep_pow_one, mul_one, map_smul, dminus_auxVar_pow q 0 (a + 1),
    show ((-1 : Total L) ^ (a + 1)) = algebraMap L (Total L) ((-1 : L) ^ (a + 1)) from by
      rw [map_pow, map_neg, map_one],
    ← Algebra.smul_def, smul_smul,
    show ((-1 : L) ^ a * (-1 : L) ^ (a + 1)) = -1 from by
      rw [← pow_add, show a + (a + 1) = 2 * a + 1 from by ring, pow_succ, pow_mul]
      norm_num]
  rw [neg_one_smul]

/-- **The straight monomial `πYZΦ` is NOT the slope operator at the doubled slope `(2,2)`, at any
`q` and `u`.**

In the sign convention of `HJO.Mellit.LhsSlope`, identifying `Y^aZ^b` with `Ξ_{b+1,a+1}` would give
`C(Q_{b+1,a+1}f) = (-1)^{a}·d_-(Y^aZ^b(Φf))` — the word `Y^aZ^b` having `a` letters `y` and `b`
letters `z`, which is the letter count of `β_{b+1,a+1}`. At `a = b = 1` and `f = 1` the two sides
are `C(Q_{2,2}1) = C(e_1^2 + (q+u)e_2)` (`HJO.Sym.qop_two_two_apply_one`) and
`-d_-(YZ(Φ1)) = Ce_2` (`HJO.Sweep.dminus_straightMonomial_slopeArg_one`), and their difference is
`C(e_1^2 + (q+u-1)e_2)`, nonzero for every scalar by
`HJO.Sym.elemSymm_one_sq_add_smul_elemSymm_two_ne_zero`.

So the failure is **not** at special parameters: it is uniform on the whole parameter space, which
is strictly stronger than an exact-arithmetic witness at a single point such as
`(q,u) = (3/7,5/11)`. The consequence is that the doubled slope is not reachable from width-`1`
straight monomials.

**It does not follow that it has to come from `HJO.Sweep.exists_slopeActions`.**
`HJO.Sym.qop_collinear_eq_bracket` writes the doubled slope as
`M^{-1}` times a commutator of slope operators at two *coprime* slopes, by `HJO.Sym.Qop`'s own
branch; and `HJO.Sweep.not_slopeActions_bridge` shows the replicated actions do not supply it at the
index `(2a,2b)`, that index being unconstrained by `HJO.Sweep.exists_slopeActions`. Both are in
`HJO/Shuffle/MellitCollinearSplit.lean`.

Genericity: `M ≠ 0` for the `Q` side, `q ≠ 0`, `u ≠ 0`, `q ≠ 1` for the sweep side — i.e. exactly
`q ∉ {0,1}` and `u ∉ {0,1}`, the same band the proved instances of the clause carry. -/
theorem not_qop_two_two_eq_straightMonomial (hM : (1 - q) * (1 - u) ≠ 0) (hq0 : q ≠ 0)
    (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    (MvPolynomial.C (Sym.Qop q u 2 2 (1 : Sym.Lambda L)) : Total L)
      ≠ ((-1 : L) ^ (1 : ℕ)) •
        dminus q 1 (straightMonomial q u 1 1 (Mellit.slopeArg q u (1 : Sym.Lambda L))) := by
  rw [dminus_straightMonomial_slopeArg_one hq0 hu0 hq1, Sym.qop_two_two_apply_one hM]
  intro h
  refine Sym.elemSymm_one_sq_add_smul_elemSymm_two_ne_zero (q + u - 1) ?_
  have hC : (MvPolynomial.C (Sym.elemSymm L 1 * Sym.elemSymm L 1
      + (q + u - 1) • Sym.elemSymm L 2) : Total L) = 0 := by
    simp only [map_add, map_mul, MvPolynomial.smul_eq_C_mul, map_sub, map_one]
    rw [show ((1 : ℕ) + 1) = 2 from rfl] at h
    simp only [pow_one, neg_smul, one_smul, neg_neg] at h
    simp only [MvPolynomial.smul_eq_C_mul, map_add, map_mul] at h
    linear_combination h
  exact (map_eq_zero_iff _ (MvPolynomial.C_injective ℕ (Sym.Lambda L))).1 hC

/-! ### Which exclusions are real, and which are the normalisation's

The three hypotheses `q ≠ 1`, `q ≠ 0`, `u ≠ 0` of
`HJO.Sweep.dminus_straightMonomial_slopeArg_one` are **all necessary for the statement**, and for
one reason that has nothing to do with the proofs above: the letter `Z = (qu)^{-1}z_1` of
`HJO.Sweep.slopeOperator` is the **zero map** at each of them — at `qu = 0` because the field
convention makes `0^{-1} = 0`, and at `q = 1` because the scalar `q^k/(1-q)` of `HJO.Sweep.zop` is
`q^k/0 = 0`. So every straight monomial with `b ≥ 1` collapses to `0` there, while the asserted
value `-Ce_{a+1}` is nonzero (`HJO.Sym.elemSymm_succ_ne_zero`).

That is the distinction the blanket phrase "artefact of cancellation" hides, and it goes the *other*
way from the usual case: `q ≠ 0` and `u ≠ 0` are not needed by the mathematics — the inverse-free
`HJO.Sweep.zopOneStar_one_auxVar_mul_eq_vertexStep` carries the same content with only `q ≠ 1` — but
they *are* needed by any statement written in the letters of `HJO.Sweep.slopeOperator`, because
those letters are themselves degenerate there. `q ≠ 1` is real in both senses.
-/

/-- **The inverse-free form of the vertex relation**, in terms of `T`: `z_1(y_1G) = qu·y_1·T(G)` on
`V_1`, with **no hypothesis on `q` or `u` beyond `q ≠ 1`**.

This is `HJO.Sweep.zopOneStar_one_auxVar_mul_of_mem_piece` with `HJO.Sweep.vertexStep` named and the
scalar written as an `L`-action rather than a constant of `Total L`. It is the evidence that `q ≠ 0`
and `u ≠ 0` in `HJO.Sweep.zLetter_auxVar_mul` belong to the *letter* `(qu)^{-1}z_1` and not to the
content. -/
theorem zopOneStar_one_auxVar_mul_eq_vertexStep (hq1 : q ≠ 1) {G : Total L}
    (hG : G ∈ piece L 1) :
    zopOneStar q u 1 ((auxVar 1 : Total L) * G)
      = (q * u) • ((auxVar 1 : Total L) * vertexStep q u G) := by
  rw [zopOneStar_one_auxVar_mul_of_mem_piece hq1 hG,
    show (scal (q * u) : Total L) = algebraMap L (Total L) (q * u) from rfl,
    ← Algebra.smul_def, smul_mul_assoc, vertexStep_apply]

/-- **`z_1 = 0` at `q = 1`**, in a field: the scalar `q^k/(1-q)` of `HJO.Sweep.zop` is `q^k/0 = 0`.
This is why `q ≠ 1` is a real exclusion for every statement about `z_1` and not a proof artefact. -/
theorem zopOneStar_eq_zero_of_q_eq_one (u : L) (k : ℕ) :
    (zopOneStar (1 : L) u k : Module.End L (Total L)) = 0 := by
  rw [zopOneStar, sub_self, div_zero, zero_smul]

/-- **The letter `Z` of `HJO.Sweep.slopeOperator` is the zero map at `qu = 0`**, the field
convention `0^{-1} = 0` applied to its normalisation. -/
theorem zLetter_eq_zero_of_mul_eq_zero (h : q * u = 0) :
    (((q * u)⁻¹ • zop q u 1 1 : Module.End L (Total L))) = 0 := by
  rw [h, inv_zero, zero_smul]

/-- **The letter `Z` is the zero map at `q = 1`**, by `HJO.Sweep.zopOneStar_eq_zero_of_q_eq_one`. -/
theorem zLetter_eq_zero_of_q_eq_one (u : L) :
    ((((1 : L) * u)⁻¹ • zop (1 : L) u 1 1 : Module.End L (Total L))) = 0 := by
  rw [zop_one, zopOneStar_eq_zero_of_q_eq_one, smul_zero]

/-- **Every straight monomial with `b ≥ 1` vanishes once the letter `Z` does.** -/
theorem straightMonomial_eq_zero_of_zLetter_eq_zero
    (h : (((q * u)⁻¹ • zop q u 1 1 : Module.End L (Total L))) = 0) (a b : ℕ) :
    (straightMonomial q u a (b + 1) : Module.End L (Total L)) = 0 := by
  rw [straightMonomial, pow_succ, h, mul_zero, mul_zero]

/-- **The vacuum evaluation is FALSE wherever the letter `Z` degenerates**, for every `a` and every
`b ≥ 1`: the left-hand side is `0` and the asserted value `-Ce_{a+1}` is not
(`HJO.Sym.elemSymm_succ_ne_zero`).

With `HJO.Sweep.zLetter_eq_zero_of_mul_eq_zero` and `HJO.Sweep.zLetter_eq_zero_of_q_eq_one` this
covers `q = 0`, `u = 0` and `q = 1`, which are exactly the three hypotheses of
`HJO.Sweep.dminus_straightMonomial_slopeArg_one`. So none of them is removable, and the reason is
the same for all three — the letter `(qu)^{-1}z_1` of `HJO.Sweep.slopeOperator` is itself the zero
map there. `u = 1` is **not** among them: nothing in this section excludes it. -/
theorem not_dminus_straightMonomial_slopeArg_one_of_zLetter_eq_zero
    (h : (((q * u)⁻¹ • zop q u 1 1 : Module.End L (Total L))) = 0) (a b : ℕ) :
    dminus q 1 (straightMonomial q u a (b + 1) (Mellit.slopeArg q u (1 : Sym.Lambda L)))
      ≠ -(MvPolynomial.C (Sym.elemSymm L (a + 1)) : Total L) := by
  rw [straightMonomial_eq_zero_of_zLetter_eq_zero h, LinearMap.zero_apply, map_zero]
  intro hc
  refine Sym.elemSymm_succ_ne_zero (L := L) a ?_
  have hC : (MvPolynomial.C (Sym.elemSymm L (a + 1)) : Total L) = 0 := by
    linear_combination hc
  exact (map_eq_zero_iff _ (MvPolynomial.C_injective ℕ (Sym.Lambda L))).1 hC

end HJO.Sweep
