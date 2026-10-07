/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepBraidMonomial
public import HJO.Shuffle.SweepInductionInstanceTwo
public import HJO.Shuffle.SweepPairIterate

/-! # The inverted braid letter on an arbitrary monomial pair

`HJO/Shuffle/SweepBraidMonomial.lean` evaluates the *forward* letter `T_i` at every index and
every pair of exponents, but the *inverted* letter `T_i^{-1}` only at the two **adjacent** pairs
`(b+1,b)` and `(b,b+1)`. That is what `HJO/Shuffle/SweepPairIterate.lean` lacks: its vectors
`HJO.Sweep.pairArgTwo` and `HJO.Sweep.pairArgSucc` are `T_i^{-1}` applied to something, so the
two-part sweep side cannot be made explicit without `T_1^{-1}(y_1^ay_2^b)` at arbitrary `(a,b)`.

This file supplies it, and **with no case split in any statement**, although the evident closed
form needs "a case split on `a ≥ b` and a length-`|a-b|` sum".

## The spelling that removes the case split

The divided difference of a monomial pair is a *difference of two initial-segment sums*:

`∂_i(y_i^ay_{i+1}^b) = ∑_{t<b} y_i^ty_{i+1}^{a+b-1-t} - ∑_{t<a} y_i^ty_{i+1}^{a+b-1-t}`

(`HJO.Sweep.pairBlock`, `HJO.Sweep.dividedDiff_auxVar_pow_mul_auxVar_pow_pair`). Both sums run over
`Finset.range`, so **neither the statement nor any use of it ever compares `a` with `b`**:
whichever of the two ranges is the longer, the shorter one cancels inside it and what survives is
the signed `Finset.Ico` block of length `|a-b|`. The case split is confined to the *proof*, where
it is two citations of `HJO.Sweep.dividedDiff_auxVar_pow_mul_auxVar_pow` and its primed
variant. The alternative spelling — `(-1)^{[a>b]}` times a sum of length `a-b` — needs the
comparison in the statement, so every use would inherit it.

At `a = b` both sums are equal and `∂_i` vanishes, which is
`HJO.Sweep.dividedDiff_eq_zero_of_swapAux_eq` on a symmetric monomial; no separate lemma is needed.

## What is proved

* `HJO.Sweep.dividedDiff_auxVar_pow_mul_auxVar_pow_pair` — `∂_i` at every `(a,b)`, every `i ≥ 1`.
* `HJO.Sweep.braid_auxVar_pow_mul_auxVar_pow_pair` — `T_i(y_i^ay_{i+1}^b)` at every `(a,b)`; this
  subsumes `HJO.Sweep.braid_auxVar_pow_mul_auxVar_pow` and its primed variant, which are its two
  parametrised halves.
* `HJO.Sweep.braidInv_auxVar_pow_mul_auxVar_pow_pair` — **the target**:
  `T_i^{-1}(y_i^ay_{i+1}^b) = q^{-1}(y_i^by_{i+1}^a + (q-1)(y_i^ay_{i+1}^b + y_i·pairBlock))`,
  at every `(a,b)` and every `i ≥ 1`, and **hypothesis-free**, together with its `L`-linear spelling
  `HJO.Sweep.braidInvEnd_auxVar_pow_mul_auxVar_pow_pair`.
* `HJO.Sweep.braidInvEnd_one_of_mem_piece_two` — `T_1^{-1}` on the whole of `V_2`, as a sum over the
  support, which is what the two-part vectors are actually applied to.
* `HJO.Sweep.pairArgTwo_eq` and `HJO.Sweep.pairArgSucc_eq` — the two vectors of
  `HJO/Shuffle/SweepPairIterate.lean` with `T_1^{-1}` **gone**, and with it the last operator
  standing between `HJO.Sweep.constantCoeff_lowerRun_two_stageWordTotal_pair_one` /
  `_pair_succ` and a fully explicit two-part sweep side.
* `HJO.Sweep.pairBlock_add_right` and `HJO.Sweep.pairBlock_add_left` — the unified block IS the
  geometric sum of `HJO.Sweep.dividedDiff_auxVar_pow_mul_auxVar_pow`, in both parametrisations; with
  the offset-one and offset-two evaluations `HJO.Sweep.pairBlock_succ_self`, `pairBlock_self_succ`,
  `pairBlock_add_two_self`, `pairBlock_self_add_two`, which are the forms one rewrites with.
* `HJO.Sweep.swapAux_one_stageWordTotal_two_three_one_one` and
  `HJO.Sweep.braidEnd_one_stageWordTotal_two_three_one_one` — the `[1,1]` stage word is
  `s_1`-symmetric, so `T_1` **fixes** it; hence `HJO.Sweep.pairArgSucc_one_zero`, the step vector of
  the `B`-recursion at the first step with the *inner* braid letter deleted as well.

## What is NOT claimed

**No new explicit value of the sweep side.** `ct(d_-^2(G_{2,B}G_{1,A}(1)))` is still not an explicit
element of `Λ` at `(A,B) = (2,1)`, `(1,2)` or `(2,2)`, and this file does not close any of them. The
reason is precise and is *not* the braid letter any more: what is missing is
`HJO.Sweep.zDefect q u n A` at `(n,A) = (2, e_1^2)`, `(2, e_2)` and `(3, e_1)` — the `B`-word table
in the `e`-basis. The entries available are `HJO.Sweep.zDefect_one_one`, `zDefect_two_one`,
`zDefect_three_one`, `zDefect_one_elemSymm_one` and `zDefect_two_elemSymm_one`, and none of the
three needed entries is among them. Nothing here says a closed form in `A` or `B` exists; the
one-part family already has `2, 9, 26` `e`-monomials at `A = 1, 2, 3`.

## Genericity: why the target needs no hypothesis

`T_i^{-1} = (T_i + (q-1))/q` does need `q ≠ 0` *to be the inverse of `T_i`*. But it does not need it
to be **evaluated**: `HJO.Sweep.braidInv` is defined as `scal q⁻¹ ∘ (T_i + (q-1))` at every `q`, and
the closed form above keeps that `q^{-1}` on the right **symbolically**, under the same `scal q⁻¹`
the definition carries. So at `q = 0`, where a field's `0⁻¹ = 0` makes `HJO.Sweep.braidInv 0 i` the
zero map, both sides are `0` and the statement is true rather than false. Nothing here mentions `u`,
`q = 1`, or positivity of `a`, `b` or the parts.

The two adjacent-pair values of `HJO/Shuffle/SweepBraidMonomial.lean` are the opposite case and
the check below shows exactly why:
`HJO.Sweep.braidInv_auxVar_pow_succ_mul_auxVar_pow` comes out of the general formula with **no**
hypothesis, because there the `(q-1)` term cancels against the block; whereas
`HJO.Sweep.braidInv_auxVar_pow_mul_auxVar_pow_succ` genuinely spends `q ≠ 0`, because there a
`q^{-1}·q` must be cancelled. So the hypothesis belongs to the *statement that cancels an inverse*,
not to the evaluation.

## Consistency checks

`HJO.Sweep.braidInv_auxVar_pow_succ_mul_auxVar_pow_of_pair` and
`HJO.Sweep.braidInv_auxVar_pow_mul_auxVar_pow_succ_of_pair` re-derive both adjacent-pair values of
`HJO/Shuffle/SweepBraidMonomial.lean` *through* the general formula, and
`HJO.Sweep.braidInv_auxVar_pow_succ_mul_auxVar_pow_of_pair_eq`,
`HJO.Sweep.braidInv_auxVar_pow_mul_auxVar_pow_succ_of_pair_eq` check by `rfl` that each statement is
literally the `Prop` of the earlier statement — which `rfl` can do only if they are identical. A
sign error in `HJO.Sweep.pairBlock`, or the two ranges interchanged, would make the first of these
unprovable: it is the value at which the `(q-1)` block must cancel *exactly*, leaving a bare
monomial.

Three further checks run against the hand computations at `i = 1`, which are proved by
`HJO.Sweep.dividedDiff_unique` with no general machinery in them at all:
`HJO.Sweep.braidInvEnd_one_sq_sq_of_pair`, `braidInvEnd_one_cube_sq_of_pair` and
`braidInvEnd_one_sq_cube_of_pair`, each with its `rfl` `Prop`-identity check. And the fifth,
`HJO.Sweep.braidInvEnd_one_neg_auxVar_one_mul_seedArgTwo_of_pair`, is at a real **vector** rather
than a monomial: the three-monomial `-y_1·HJO.Sweep.seedArgTwo` with coefficients in `e_1`, `q` and
`u`, whose hand-computed value has only two monomials because a `y_1^2y_2^3` term cancels between
the two *opposite* signs of the block at offset one. A sign error there would leave that term
behind.

## References

A. Mellit, *Toric braids and `(m,n)`-parking functions*, §3.2. -/

@[expose] public section

namespace HJO.Sweep

open MvPolynomial

section Field

variable {L : Type*} [Field L] {q : L}

/-! ### The signed block -/

/-- **The signed geometric block of a monomial pair**,

`pairBlock i a b = ∑_{t<b} y_i^ty_{i+1}^{a+b-1-t} - ∑_{t<a} y_i^ty_{i+1}^{a+b-1-t}`.

Both sums run over `Finset.range`, so no comparison of `a` with `b` occurs: this is the whole reason
the closed forms below have no case split. The shorter range cancels termwise inside the longer one,
leaving `±` the `Finset.Ico`-block of length `|a-b|` — with the sign `-` when `a > b`, `+` when
`b > a`, and the block empty when `a = b`.

The truncated subtraction `a + b - 1 - t` is correct without a side condition: `t` ranges below
`max a b`, so `t ≤ a + b - 1` whenever the term occurs, and at `a = b = 0` both sums are empty. -/
noncomputable def pairBlock (L : Type*) [Field L] (i a b : ℕ) : Total L :=
  ∑ t ∈ Finset.range b,
      (auxVar i : Total L) ^ t * (auxVar (i + 1) : Total L) ^ (a + b - 1 - t)
    - ∑ t ∈ Finset.range a,
      (auxVar i : Total L) ^ t * (auxVar (i + 1) : Total L) ^ (a + b - 1 - t)

/-- **The block is antisymmetric in the pair.** `pairBlock i b a = -pairBlock i a b`, immediate from
the definition since `a + b = b + a`. This is `HJO.Sweep.dividedDiff_swapAux` read on a monomial,
and it is the one identity a user needs in place of the case split. -/
theorem pairBlock_swap (i a b : ℕ) : pairBlock L i b a = -pairBlock L i a b := by
  rw [pairBlock, pairBlock, show b + a = a + b from by omega]
  ring

/-- **The block vanishes on a symmetric pair.** `HJO.Sweep.pairBlock_swap` at `a = b`, and the
reason no `a = b` case appears anywhere below. -/
theorem pairBlock_self (i a : ℕ) : pairBlock L i a a = 0 := by
  rw [pairBlock, sub_self]

/-! ### The divided difference at every exponent pair -/

/-- **`∂_i(y_i^ay_{i+1}^b) = pairBlock i a b` at EVERY pair `(a,b)` and every index `i ≥ 1`.**

The closed form of `HJO.Sweep.dividedDiffₗ` on an arbitrary monomial pair, with **no case split in
the statement**: `HJO.Sweep.dividedDiff_auxVar_pow_mul_auxVar_pow` and its primed variant
give it on the two parametrised halves `(b+c,b)` and `(b,b+c)`, and the two initial-segment sums of
`HJO.Sweep.pairBlock` reproduce each of those by cancelling the common `Finset.range` prefix.

`1 ≤ i` is the range condition in the definition of `∂_i`; at the unread index `0` the convention
`y_0 = y_1` makes `∂_0` the zero map (`HJO.Sweep.dividedDiff_zero_index`) while the block need not
vanish, so the hypothesis is real. No hypothesis on `q`, and none on `a` or `b`. -/
theorem dividedDiff_auxVar_pow_mul_auxVar_pow_pair {i : ℕ} (hi : 1 ≤ i) (a b : ℕ) :
    dividedDiff i ((auxVar i : Total L) ^ a * (auxVar (i + 1) : Total L) ^ b)
      = pairBlock L i a b := by
  rw [pairBlock]
  rcases Nat.le_total b a with hba | hab
  · obtain ⟨c, rfl⟩ : ∃ c, a = b + c := ⟨a - b, by omega⟩
    rw [dividedDiff_auxVar_pow_mul_auxVar_pow hi b c,
      show Finset.range (b + c) = Finset.range b ∪ Finset.Ico b (b + c) from by
        rw [Finset.range_eq_Ico, Finset.range_eq_Ico, Finset.Ico_union_Ico_eq_Ico (by omega)
          (by omega)],
      Finset.sum_union (by
        rw [Finset.range_eq_Ico]
        exact Finset.Ico_disjoint_Ico_consecutive 0 b (b + c))]
    rw [Finset.sum_Ico_eq_sum_range, Finset.mul_sum]
    rw [show ∀ x y : Total L, x - (x + y) = -y from fun x y => by ring]
    congr 1
    refine Finset.sum_congr (by congr 1; omega) fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [show b + c + b - 1 - (b + j) = b + (c - 1 - j) from by omega, pow_add, pow_add]
    ring
  · obtain ⟨c, rfl⟩ : ∃ c, b = a + c := ⟨b - a, by omega⟩
    rw [dividedDiff_auxVar_pow_mul_auxVar_pow' hi a c,
      show Finset.range (a + c) = Finset.range a ∪ Finset.Ico a (a + c) from by
        rw [Finset.range_eq_Ico, Finset.range_eq_Ico, Finset.Ico_union_Ico_eq_Ico (by omega)
          (by omega)],
      Finset.sum_union (by
        rw [Finset.range_eq_Ico]
        exact Finset.Ico_disjoint_Ico_consecutive 0 a (a + c))]
    rw [Finset.sum_Ico_eq_sum_range, Finset.mul_sum]
    rw [show ∀ x y : Total L, x + y - x = y from fun x y => by ring]
    refine Finset.sum_congr (by congr 1; omega) fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [show a + (a + c) - 1 - (a + j) = a + (c - 1 - j) from by omega, pow_add, pow_add]
    ring

/-! ### The braid letter and its inverse at every exponent pair -/

/-- **`T_i(y_i^ay_{i+1}^b) = y_i^by_{i+1}^a + (q-1)y_i·pairBlock i a b` at EVERY pair `(a,b)`.**

`HJO.Sweep.braid` read with `HJO.Sweep.dividedDiff_auxVar_pow_mul_auxVar_pow_pair`. This subsumes
`HJO.Sweep.braid_auxVar_pow_mul_auxVar_pow` and
`HJO.Sweep.braid_auxVar_pow_mul_auxVar_pow'`, which are this statement at `(b+c,b)` and `(b,b+c)`;
the sign difference between those two is carried here by `HJO.Sweep.pairBlock_swap` rather than by
two theorems. Unconditional in `q`. -/
theorem braid_auxVar_pow_mul_auxVar_pow_pair (q : L) {i : ℕ} (hi : 1 ≤ i) (a b : ℕ) :
    braid q i ((auxVar i : Total L) ^ a * (auxVar (i + 1) : Total L) ^ b)
      = (auxVar i : Total L) ^ b * (auxVar (i + 1) : Total L) ^ a
        + scal (q - 1) * auxVar i * pairBlock L i a b := by
  rw [braid_apply, dividedDiff_auxVar_pow_mul_auxVar_pow_pair hi, map_mul, map_pow, map_pow,
    swapAux_auxVar_self hi, swapAux_auxVar_succ hi]
  ring

/-- **THE TARGET: `T_i^{-1}` on an arbitrary monomial pair, at every `(a,b)`, hypothesis-free.**

`T_i^{-1}(y_i^ay_{i+1}^b) = q^{-1}(y_i^by_{i+1}^a + (q-1)(y_i^ay_{i+1}^b + y_i·pairBlock i a b))`.

This is the closed form for `T_1^{-1}(y_1^ay_2^b)` at arbitrary `(a,b)` that
`HJO/Shuffle/SweepPairIterate.lean` needs, and the shape one would expect it to need — a case split
on `a ≥ b` and a length-`|a-b|` sum — is not needed: `HJO.Sweep.pairBlock` carries that sum as a
difference of two initial segments, and no comparison of `a` with `b` occurs.

**No hypothesis at all, and in particular not `q ≠ 0`.** `HJO.Sweep.braidInv` is
`scal q^{-1} ∘ (T_i + (q-1))` by definition at every `q`, and the `q^{-1}` here is the *same*
symbolic `scal q^{-1}`; so at `q = 0`, where `0^{-1} = 0` in a field makes both sides the zero
map, this reads `0 = 0`. `q ≠ 0` is what makes this map the inverse of `T_i`
(`HJO.Sweep.braid_braidInv`), which is a different statement and not used here. `1 ≤ i` is `∂_i`'s
range condition, inherited from the divided-difference formula above. -/
theorem braidInv_auxVar_pow_mul_auxVar_pow_pair (q : L) {i : ℕ} (hi : 1 ≤ i) (a b : ℕ) :
    braidInv q i ((auxVar i : Total L) ^ a * (auxVar (i + 1) : Total L) ^ b)
      = scal q⁻¹ * ((auxVar i : Total L) ^ b * (auxVar (i + 1) : Total L) ^ a
          + scal (q - 1) * ((auxVar i : Total L) ^ a * (auxVar (i + 1) : Total L) ^ b
              + auxVar i * pairBlock L i a b)) := by
  rw [braidInv_apply, braid_auxVar_pow_mul_auxVar_pow_pair q hi]
  ring

/-- `HJO.Sweep.braidInv_auxVar_pow_mul_auxVar_pow_pair` at the `L`-linear spelling
`HJO.Sweep.braidInvEnd`, which is the shape the trains and `HJO.Sweep.zop` compose.
Unconditional. -/
theorem braidInvEnd_auxVar_pow_mul_auxVar_pow_pair (q : L) {i : ℕ} (hi : 1 ≤ i) (a b : ℕ) :
    braidInvEnd q i ((auxVar i : Total L) ^ a * (auxVar (i + 1) : Total L) ^ b)
      = scal q⁻¹ * ((auxVar i : Total L) ^ b * (auxVar (i + 1) : Total L) ^ a
          + scal (q - 1) * ((auxVar i : Total L) ^ a * (auxVar (i + 1) : Total L) ^ b
              + auxVar i * pairBlock L i a b)) :=
  braidInv_auxVar_pow_mul_auxVar_pow_pair q hi a b

/-! ### The block against the parametrised geometric sum -/

/-- **The unified block IS the geometric sum**, in the descending parametrisation:
`pairBlock i (b+c) b = -y_i^by_{i+1}^b∑_{j<c}y_i^jy_{i+1}^{c-1-j}`.

Both sides are `∂_i` of the same monomial — the left by
`HJO.Sweep.dividedDiff_auxVar_pow_mul_auxVar_pow_pair`, the right by
`HJO.Sweep.dividedDiff_auxVar_pow_mul_auxVar_pow` — so this is the statement that the
case-split-free spelling and the parametrised one agree, and it is the bridge every use of the
parametrised shape needs.
`1 ≤ i` comes from reading both through `∂_i`. -/
theorem pairBlock_add_right {i : ℕ} (hi : 1 ≤ i) (b c : ℕ) :
    pairBlock L i (b + c) b
      = -((auxVar i : Total L) ^ b * (auxVar (i + 1) : Total L) ^ b *
          ∑ j ∈ Finset.range c,
            (auxVar i : Total L) ^ j * (auxVar (i + 1) : Total L) ^ (c - 1 - j)) := by
  rw [← dividedDiff_auxVar_pow_mul_auxVar_pow_pair (L := L) hi,
    dividedDiff_auxVar_pow_mul_auxVar_pow hi]

/-- **The unified block IS the geometric sum**, in the ascending parametrisation:
`pairBlock i b (b+c) = +y_i^by_{i+1}^b∑_{j<c}y_i^jy_{i+1}^{c-1-j}`. Read through
`HJO.Sweep.dividedDiff_auxVar_pow_mul_auxVar_pow'`; the sign is the only difference from
`HJO.Sweep.pairBlock_add_right`, as `HJO.Sweep.pairBlock_swap` predicts. -/
theorem pairBlock_add_left {i : ℕ} (hi : 1 ≤ i) (b c : ℕ) :
    pairBlock L i b (b + c)
      = (auxVar i : Total L) ^ b * (auxVar (i + 1) : Total L) ^ b *
          ∑ j ∈ Finset.range c,
            (auxVar i : Total L) ^ j * (auxVar (i + 1) : Total L) ^ (c - 1 - j) := by
  rw [← dividedDiff_auxVar_pow_mul_auxVar_pow_pair (L := L) hi,
    dividedDiff_auxVar_pow_mul_auxVar_pow' hi]

/-- `pairBlock i (b+1) b = -y_i^by_{i+1}^b`: the offset-one block, proved straight off the
definition, so it holds at every index including `0`. -/
theorem pairBlock_succ_self (i b : ℕ) :
    pairBlock L i (b + 1) b = -((auxVar i : Total L) ^ b * (auxVar (i + 1) : Total L) ^ b) := by
  rw [pairBlock, Finset.sum_range_succ, show b + 1 + b - 1 - b = b from by omega]
  ring

/-- `pairBlock i b (b+1) = y_i^by_{i+1}^b`, the other offset-one block. Every index. -/
theorem pairBlock_self_succ (i b : ℕ) :
    pairBlock L i b (b + 1) = (auxVar i : Total L) ^ b * (auxVar (i + 1) : Total L) ^ b := by
  rw [pairBlock, Finset.sum_range_succ, show b + (b + 1) - 1 - b = b from by omega]
  ring

/-- `pairBlock i (b+2) b = -y_i^by_{i+1}^b(y_i + y_{i+1})`: the offset-two block, the first one that
is not a single monomial. Every index. -/
theorem pairBlock_add_two_self (i b : ℕ) :
    pairBlock L i (b + 2) b
      = -((auxVar i : Total L) ^ b * (auxVar (i + 1) : Total L) ^ b
          * ((auxVar i : Total L) + auxVar (i + 1))) := by
  rw [pairBlock, Finset.sum_range_succ, Finset.sum_range_succ,
    show b + 2 + b - 1 - b = b + 1 from by omega,
    show b + 2 + b - 1 - (b + 1) = b from by omega]
  ring

/-- `pairBlock i b (b+2) = y_i^by_{i+1}^b(y_i + y_{i+1})`. Every index. -/
theorem pairBlock_self_add_two (i b : ℕ) :
    pairBlock L i b (b + 2)
      = (auxVar i : Total L) ^ b * (auxVar (i + 1) : Total L) ^ b
          * ((auxVar i : Total L) + auxVar (i + 1)) := by
  rw [pairBlock, Finset.sum_range_succ, Finset.sum_range_succ,
    show b + (b + 2) - 1 - b = b + 1 from by omega,
    show b + (b + 2) - 1 - (b + 1) = b from by omega]
  ring

/-! ### Consistency checks: both adjacent-pair values, re-derived -/

/-- **Check, the sharp one.** The value
`T_i^{-1}(y_i^{b+1}y_{i+1}^b) = q^{-1}y_i^by_{i+1}^{b+1}`, re-derived *through*
`HJO.Sweep.braidInv_auxVar_pow_mul_auxVar_pow_pair`.

Word for word `HJO.Sweep.braidInv_auxVar_pow_succ_mul_auxVar_pow`, hypotheses included, but reached
from the general formula. This is the value that a sign error in `HJO.Sweep.pairBlock` cannot
survive: at `(a,b) = (b+1,b)` the block is exactly `-y_i^by_{i+1}^b`, and the `(q-1)y_i·pairBlock`
term must cancel the `(q-1)y_i^{b+1}y_{i+1}^b` term **exactly**, leaving a bare monomial. With the
two ranges interchanged the block would be `+y_i^by_{i+1}^b` and the two terms would add rather
than cancel, leaving `(2q-2)` where the true value has nothing.

Note what this check also shows, and it is a genuine strengthening rather than bookkeeping: the
general formula produces this value with **no** hypothesis on `q` at all, which is
`HJO.Sweep.braidInv_auxVar_pow_succ_mul_auxVar_pow_pair` just below; the `q ≠ 0` of
`HJO.Sweep.braidInv_auxVar_pow_succ_mul_auxVar_pow` turns out to be unnecessary, and the check
carries it only so that the `rfl` check below can compare the two `Prop`s. -/
theorem braidInv_auxVar_pow_succ_mul_auxVar_pow_pair (q : L) {i : ℕ} (hi : 1 ≤ i) (b : ℕ) :
    braidInv q i ((auxVar i : Total L) ^ (b + 1) * (auxVar (i + 1) : Total L) ^ b)
      = scal q⁻¹ * ((auxVar i : Total L) ^ b * (auxVar (i + 1) : Total L) ^ (b + 1)) := by
  rw [braidInv_auxVar_pow_mul_auxVar_pow_pair q hi, pairBlock_succ_self,
    show (auxVar i : Total L) * -((auxVar i : Total L) ^ b * (auxVar (i + 1) : Total L) ^ b)
      = -((auxVar i : Total L) ^ (b + 1) * (auxVar (i + 1) : Total L) ^ b) from by ring]
  ring

/-- The statement of `HJO.Sweep.braidInv_auxVar_pow_succ_mul_auxVar_pow`, reached through
`HJO.Sweep.braidInv_auxVar_pow_succ_mul_auxVar_pow_pair`. The hypothesis `q ≠ 0` is that statement's
and is **not used**: it is present so that
`HJO.Sweep.braidInv_auxVar_pow_succ_mul_auxVar_pow_of_pair_eq` can compare the two `Prop`s by
`rfl`. -/
theorem braidInv_auxVar_pow_succ_mul_auxVar_pow_of_pair (_hq : q ≠ 0) {i : ℕ} (hi : 1 ≤ i) (b : ℕ) :
    braidInv q i ((auxVar i : Total L) ^ (b + 1) * (auxVar (i + 1) : Total L) ^ b)
      = scal q⁻¹ * ((auxVar i : Total L) ^ b * (auxVar (i + 1) : Total L) ^ (b + 1)) :=
  braidInv_auxVar_pow_succ_mul_auxVar_pow_pair q hi b

/-- **The two routes to `T_i^{-1}(y_i^{b+1}y_{i+1}^b)` are the same `Prop`.** `rfl` typechecks
only if the statement of `HJO.Sweep.braidInv_auxVar_pow_succ_mul_auxVar_pow_of_pair`, proved
through the general formula, is *identical* to
`HJO.Sweep.braidInv_auxVar_pow_succ_mul_auxVar_pow`'s — hypotheses and all. Stronger than comparing
printed coefficients by eye. -/
theorem braidInv_auxVar_pow_succ_mul_auxVar_pow_of_pair_eq (hq : q ≠ 0) {i : ℕ} (hi : 1 ≤ i)
    (b : ℕ) :
    braidInv_auxVar_pow_succ_mul_auxVar_pow_of_pair (L := L) hq hi b
      = braidInv_auxVar_pow_succ_mul_auxVar_pow (L := L) hq hi b :=
  rfl

/-- **Check, the other ordering: the value
`T_i^{-1}(y_i^by_{i+1}^{b+1}) = y_i^{b+1}y_{i+1}^b + (q-1)q^{-1}y_i^by_{i+1}^{b+1}` re-derived
through the general formula.**

Here the block is `+y_i^by_{i+1}^b`, the two `(q-1)`-terms **add** rather than cancel, and the
`q^{-1}·q = 1` that turns `q^{-1}(1 + (q-1))y_i^{b+1}y_{i+1}^b` into `y_i^{b+1}y_{i+1}^b` is where
`q ≠ 0` is genuinely spent — exactly as in `HJO.Sweep.braidInv_auxVar_pow_mul_auxVar_pow_succ`,
which carries it.

Together with the check above this pins the block's sign in both directions: the same
`HJO.Sweep.pairBlock` has to cancel at one ordering and double at the other. -/
theorem braidInv_auxVar_pow_mul_auxVar_pow_succ_of_pair (hq : q ≠ 0) {i : ℕ} (hi : 1 ≤ i) (b : ℕ) :
    braidInv q i ((auxVar i : Total L) ^ b * (auxVar (i + 1) : Total L) ^ (b + 1))
      = (auxVar i : Total L) ^ (b + 1) * (auxVar (i + 1) : Total L) ^ b
        + scal ((q - 1) * q⁻¹)
          * ((auxVar i : Total L) ^ b * (auxVar (i + 1) : Total L) ^ (b + 1)) := by
  have hq' : (scal q⁻¹ : Total L) * scal q = 1 := by
    rw [← scal_mul, inv_mul_cancel₀ hq, scal_one]
  have hqs : (scal q : Total L) = 1 + scal (q - 1) := by
    rw [← scal_one (L := L), ← scal_add]
    congr 1
    ring
  rw [braidInv_auxVar_pow_mul_auxVar_pow_pair q hi, pairBlock_self_succ, scal_mul,
    show (auxVar i : Total L) * ((auxVar i : Total L) ^ b * (auxVar (i + 1) : Total L) ^ b)
      = (auxVar i : Total L) ^ (b + 1) * (auxVar (i + 1) : Total L) ^ b from by ring]
  linear_combination ((auxVar i : Total L) ^ (b + 1) * (auxVar (i + 1) : Total L) ^ b) * hq'
    - ((scal q⁻¹ : Total L) * ((auxVar i : Total L) ^ (b + 1)
        * (auxVar (i + 1) : Total L) ^ b)) * hqs

/-- **The two routes to `T_i^{-1}(y_i^by_{i+1}^{b+1})` are the same `Prop`**, by `rfl` against
`HJO.Sweep.braidInv_auxVar_pow_mul_auxVar_pow_succ`. -/
theorem braidInv_auxVar_pow_mul_auxVar_pow_succ_of_pair_eq (hq : q ≠ 0) {i : ℕ} (hi : 1 ≤ i)
    (b : ℕ) :
    braidInv_auxVar_pow_mul_auxVar_pow_succ_of_pair (L := L) hq hi b
      = braidInv_auxVar_pow_mul_auxVar_pow_succ (L := L) hq hi b :=
  rfl

/-- **`T_i^{-1}` fixes a symmetric monomial**, the `a = b` instance: `HJO.Sweep.pairBlock_self`
makes the block vanish, so the value is `q^{-1}(1 + (q-1))` times the monomial, which is the
monomial once `q ≠ 0` cancels it. This is `HJO.Sweep.braidInv_eq_self_of_swapAux_eq` reached
through the general formula, and a third check on the block: the two initial-segment sums must be
*equal*, not merely of equal length. -/
theorem braidInv_auxVar_pow_mul_auxVar_pow_self_of_pair (hq : q ≠ 0) {i : ℕ} (hi : 1 ≤ i) (a : ℕ) :
    braidInv q i ((auxVar i : Total L) ^ a * (auxVar (i + 1) : Total L) ^ a)
      = (auxVar i : Total L) ^ a * (auxVar (i + 1) : Total L) ^ a := by
  have hq' : (scal q⁻¹ : Total L) * scal q = 1 := by
    rw [← scal_mul, inv_mul_cancel₀ hq, scal_one]
  have hqs : (scal q : Total L) = 1 + scal (q - 1) := by
    rw [← scal_one (L := L), ← scal_add]
    congr 1
    ring
  rw [braidInv_auxVar_pow_mul_auxVar_pow_pair q hi, pairBlock_self]
  linear_combination ((auxVar i : Total L) ^ a * (auxVar (i + 1) : Total L) ^ a) * hq'
    - ((scal q⁻¹ : Total L) * ((auxVar i : Total L) ^ a
        * (auxVar (i + 1) : Total L) ^ a)) * hqs

/-! ### The letter at the index `1`, and the three hand-computed values -/

/-- `HJO.Sweep.braidInvEnd_auxVar_pow_mul_auxVar_pow_pair` at `i = 1`, with `y_2` spelled `auxVar 2`
rather than `auxVar (1+1)`. Syntax, not mathematics — but rewriting is syntactic, and
every statement at the grading `2` writes `auxVar 2`. Unconditional. -/
theorem braidInvEnd_one_auxVar_pow_mul_auxVar_pow_pair (q : L) (a b : ℕ) :
    braidInvEnd q 1 ((auxVar 1 : Total L) ^ a * (auxVar 2 : Total L) ^ b)
      = scal q⁻¹ * ((auxVar 1 : Total L) ^ b * (auxVar 2 : Total L) ^ a
          + scal (q - 1) * ((auxVar 1 : Total L) ^ a * (auxVar 2 : Total L) ^ b
              + auxVar 1 * pairBlock L 1 a b)) := by
  have h := braidInvEnd_auxVar_pow_mul_auxVar_pow_pair (L := L) q (i := 1) le_rfl a b
  rwa [show (1 : ℕ) + 1 = 2 from rfl] at h

/-- **Check: `T_1^{-1}(y_1^2y_2^2) = y_1^2y_2^2`, re-derived through the general
formula.**

Word for word `HJO.Sweep.braidInvEnd_one_sq_sq`, whose proof pins `∂_1(y_1^2y_2^2) = 0` by
hand off `HJO.Sweep.dividedDiff_unique` with no general machinery in it. Here it is
`HJO.Sweep.pairBlock_self` — the two initial-segment sums of `HJO.Sweep.pairBlock` being *equal*,
not merely of equal length — followed by the `q^{-1}(1 + (q-1)) = 1` that spends its
`q ≠ 0`. -/
theorem braidInvEnd_one_sq_sq_of_pair (hq0 : q ≠ 0) :
    braidInvEnd q 1 ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2)
      = (auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2 := by
  have hq' : (scal q⁻¹ : Total L) * scal q = 1 := by
    rw [← scal_mul, inv_mul_cancel₀ hq0, scal_one]
  have hqs : (scal q : Total L) = 1 + scal (q - 1) := by
    rw [← scal_one (L := L), ← scal_add]
    congr 1
    ring
  rw [braidInvEnd_one_auxVar_pow_mul_auxVar_pow_pair q 2 2, pairBlock_self]
  linear_combination ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2) * hq'
    - ((scal q⁻¹ : Total L) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2)) * hqs

/-- `HJO.Sweep.braidInvEnd_one_sq_sq_of_pair` and
`HJO.Sweep.braidInvEnd_one_sq_sq` are the same `Prop`. -/
theorem braidInvEnd_one_sq_sq_of_pair_eq (hq0 : q ≠ 0) :
    braidInvEnd_one_sq_sq_of_pair (L := L) hq0 = braidInvEnd_one_sq_sq (L := L) hq0 :=
  rfl

/-- **Check: `T_1^{-1}(y_1^3y_2^2) = q^{-1}y_1^2y_2^3`, re-derived through the general
formula.**

Word for word `HJO.Sweep.braidInvEnd_one_cube_sq`, which is the value at which the `(q-1)`
terms must cancel **identically** and a single bare monomial survive. Here the cancellation is
`HJO.Sweep.pairBlock_succ_self` at `b = 2`: `pairBlock 1 3 2 = -y_1^2y_2^2`, and
`(q-1)y_1·(-y_1^2y_2^2)` has to annihilate `(q-1)y_1^3y_2^2` exactly. With the block's sign reversed
this statement would be false, so this is the tightest of the checks. Unconditional, as
`HJO.Sweep.braidInvEnd_one_cube_sq` is. -/
theorem braidInvEnd_one_cube_sq_of_pair (q : L) :
    braidInvEnd q 1 ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2)
      = scal q⁻¹ * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3) := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, braidInvEnd_one_auxVar_pow_mul_auxVar_pow_pair q (2 + 1) 2,
    pairBlock_succ_self]
  ring

/-- `HJO.Sweep.braidInvEnd_one_cube_sq_of_pair` and
`HJO.Sweep.braidInvEnd_one_cube_sq` are the same `Prop`. -/
theorem braidInvEnd_one_cube_sq_of_pair_eq (q : L) :
    braidInvEnd_one_cube_sq_of_pair (L := L) q = braidInvEnd_one_cube_sq (L := L) q :=
  rfl

/-- **Check: `T_1^{-1}(y_1^2y_2^3) = y_1^3y_2^2 + q^{-1}(q-1)y_1^2y_2^3`, re-derived
through the general formula.**

The mirror of `HJO.Sweep.braidInvEnd_one_cube_sq_of_pair`: `HJO.Sweep.pairBlock_self_succ` gives
`pairBlock 1 2 3 = +y_1^2y_2^2`, the two `(q-1)`-terms **add**, and `q ≠ 0` is genuinely spent on
the `q^{-1}·q` that clears the leading monomial — exactly as in `HJO.Sweep.braidInvEnd_one_sq_cube`.
Together with the previous check this pins the block's sign in both directions at a hand
computation. -/
theorem braidInvEnd_one_sq_cube_of_pair (hq0 : q ≠ 0) :
    braidInvEnd q 1 ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3)
      = (auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2
        + scal (q⁻¹ * (q - 1)) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3) := by
  have hq' : (scal q⁻¹ : Total L) * scal q = 1 := by
    rw [← scal_mul, inv_mul_cancel₀ hq0, scal_one]
  have hqs : (scal q : Total L) = 1 + scal (q - 1) := by
    rw [← scal_one (L := L), ← scal_add]
    congr 1
    ring
  rw [show (3 : ℕ) = 2 + 1 from rfl, braidInvEnd_one_auxVar_pow_mul_auxVar_pow_pair q 2 (2 + 1),
    pairBlock_self_succ, scal_mul]
  linear_combination ((auxVar 1 : Total L) ^ (2 + 1) * (auxVar 2 : Total L) ^ 2) * hq'
    - ((scal q⁻¹ : Total L)
        * ((auxVar 1 : Total L) ^ (2 + 1) * (auxVar 2 : Total L) ^ 2)) * hqs

/-- `HJO.Sweep.braidInvEnd_one_sq_cube_of_pair` and
`HJO.Sweep.braidInvEnd_one_sq_cube` are the same `Prop`. -/
theorem braidInvEnd_one_sq_cube_of_pair_eq (hq0 : q ≠ 0) :
    braidInvEnd_one_sq_cube_of_pair (L := L) hq0 = braidInvEnd_one_sq_cube (L := L) hq0 :=
  rfl

/-! ### `T_1^{-1}` on the whole of `V_2` -/

/-- `T_i^{-1}` is `Λ`-linear, so a coefficient passes through it — the inverted companion of
`HJO.Sweep.braid_C_mul`. -/
theorem braidInv_C_mul (q : L) (i : ℕ) (c : Sym.Lambda L) (F : Total L) :
    braidInv q i (MvPolynomial.C c * F) = MvPolynomial.C c * braidInv q i F := by
  rw [← MvPolynomial.smul_eq_C_mul, map_smul, MvPolynomial.smul_eq_C_mul]

/-- **`T_1^{-1}` on an arbitrary element of `V_2`, as a sum over its support.**

Every monomial of `V_2` is `y_1^my_2^n` (`HJO.Sweep.exists_pair_of_mem_piece_two`), so the general
pair formula `HJO.Sweep.braidInv_auxVar_pow_mul_auxVar_pow_pair` applies termwise and the
coefficients pass through by `HJO.Sweep.braidInv_C_mul`. This is the shape in which the two-part
vectors of `HJO/Shuffle/SweepPairIterate.lean` actually meet the inverted letter: neither of
them is a monomial, and without this the letter could only be evaluated on one.

`G ∈ V_2` is not decoration — on a monomial carrying `y_3` the pair `(d 0, d 1)` is not the whole
exponent. **Unconditional**: the `q^{-1}` is the symbolic one of `HJO.Sweep.braidInv`. -/
theorem braidInvEnd_one_of_mem_piece_two (q : L) {G : Total L} (hG : G ∈ piece L 2) :
    braidInvEnd q 1 G
      = ∑ d ∈ G.support, MvPolynomial.C (MvPolynomial.coeff d G)
          * (scal q⁻¹ * ((auxVar 1 : Total L) ^ (d 1) * (auxVar 2 : Total L) ^ (d 0)
              + scal (q - 1) * ((auxVar 1 : Total L) ^ (d 0) * (auxVar 2 : Total L) ^ (d 1)
                  + auxVar 1 * pairBlock L 1 (d 0) (d 1)))) := by
  have hone : (1 : ℕ) + 1 = 2 := rfl
  conv_lhs => rw [G.as_sum]
  rw [map_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  obtain ⟨m, n, rfl⟩ := exists_pair_of_mem_piece_two hG hd
  have hmon : (MvPolynomial.monomial (Finsupp.single 0 m + Finsupp.single 1 n)
        (MvPolynomial.coeff (Finsupp.single 0 m + Finsupp.single 1 n) G) : Total L)
      = MvPolynomial.C (MvPolynomial.coeff (Finsupp.single 0 m + Finsupp.single 1 n) G)
        * ((auxVar 1 : Total L) ^ m * (auxVar (1 + 1) : Total L) ^ n) := by
    rw [hone, monomial_pair_eq]
    ring
  rw [show braidInvEnd q 1 (MvPolynomial.monomial (Finsupp.single 0 m + Finsupp.single 1 n)
        (MvPolynomial.coeff (Finsupp.single 0 m + Finsupp.single 1 n) G) : Total L)
      = braidInv q 1 (MvPolynomial.monomial (Finsupp.single 0 m + Finsupp.single 1 n)
        (MvPolynomial.coeff (Finsupp.single 0 m + Finsupp.single 1 n) G) : Total L) from rfl,
    hmon, braidInv_C_mul, braidInv_auxVar_pow_mul_auxVar_pow_pair q le_rfl, hone]
  simp

end Field

/-! ### The two-part vectors, with the inverted letter gone -/

section TwoPart

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

open HJO.Sym HJO.Mellit

/-- **Check at a real vector: `T_1^{-1}(-y_1·seedArgTwo)`, re-derived through the general
formula.**

The strongest of the checks, because the target is not a monomial but the actual three-monomial
vector `-y_1·(e_1y_1y_2^2 + (q-1)uy_1^2y_2^2 - uy_1y_2^3)` of `HJO.Sweep.seedArgTwo`, coefficients
in
`e_1`, `q` and `u` — and the value has only **two** monomials, the two `y_1^2y_2^3` terms
having cancelled identically. That cancellation is between the output of `T_1^{-1}(y_1^3y_2^2)` and
the output of `T_1^{-1}(y_1^2y_2^3)`, i.e. between the two *opposite* signs of
`HJO.Sweep.pairBlock` at offset one: `HJO.Sweep.pairBlock_succ_self` and
`HJO.Sweep.pairBlock_self_succ`. A sign error in either would leave a spurious `y_1^2y_2^3` term
with coefficient in `u` and `q^{-1}`, and this statement would be false.

Word for word `HJO.Sweep.braidInvEnd_one_neg_auxVar_one_mul_seedArgTwo`, whose own proof runs on
three hand computations off `HJO.Sweep.dividedDiff_unique`; here the three are
`HJO.Sweep.braidInvEnd_one_sq_sq_of_pair`, `HJO.Sweep.braidInvEnd_one_cube_sq_of_pair` and
`HJO.Sweep.braidInvEnd_one_sq_cube_of_pair`, each of which came out of the general formula.
`q ≠ 0` is the train's and that of
`HJO.Sweep.braidInvEnd_one_neg_auxVar_one_mul_seedArgTwo`. -/
theorem braidInvEnd_one_neg_auxVar_one_mul_seedArgTwo_of_pair (hq0 : q ≠ 0) :
    braidInvEnd q 1 (-((auxVar 1 : Total L) * seedArgTwo q u))
      = -(MvPolynomial.C (elemSymm L 1)
            * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2))
        + u • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2) := by
  have hexp : -((auxVar 1 : Total L) * seedArgTwo q u)
      = MvPolynomial.C (-(elemSymm L 1))
            * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2)
        + scal (-((q - 1) * u)) * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2)
        + scal u * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3) := by
    rw [seedArgTwo, MvPolynomial.C_neg, ← scal_mul_eq_smul_total, scal_neg]
    ring
  rw [hexp, map_add, map_add, braidInvEnd_C_mul, braidInvEnd_scal_mul, braidInvEnd_scal_mul,
    braidInvEnd_one_sq_sq_of_pair hq0, braidInvEnd_one_cube_sq_of_pair q,
    braidInvEnd_one_sq_cube_of_pair hq0, MvPolynomial.C_neg, ← scal_mul_eq_smul_total]
  rw [show (scal (-((q - 1) * u)) : Total L)
        * (scal q⁻¹ * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3))
      = scal (-((q - 1) * u) * q⁻¹) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3) from by
      rw [← mul_assoc, ← scal_mul],
    show (scal u : Total L) * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2
        + scal (q⁻¹ * (q - 1)) * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3))
      = scal u * ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 2)
        + scal (u * (q⁻¹ * (q - 1)))
            * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 3) from by
      rw [mul_add, ← mul_assoc (scal u : Total L) (scal (q⁻¹ * (q - 1)) : Total L),
        ← scal_mul],
    show (-((q - 1) * u) * q⁻¹) = -(u * (q⁻¹ * (q - 1))) from by ring, scal_neg]
  ring

/-- `HJO.Sweep.braidInvEnd_one_neg_auxVar_one_mul_seedArgTwo_of_pair` and
`HJO.Sweep.braidInvEnd_one_neg_auxVar_one_mul_seedArgTwo` are the same `Prop`, by `rfl`. -/
theorem braidInvEnd_one_neg_auxVar_one_mul_seedArgTwo_of_pair_eq (hq0 : q ≠ 0) :
    braidInvEnd_one_neg_auxVar_one_mul_seedArgTwo_of_pair (L := L) (u := u) hq0
      = braidInvEnd_one_neg_auxVar_one_mul_seedArgTwo (L := L) (u := u) hq0 :=
  rfl

/-- **`HJO.Sweep.pairArgTwo` made explicit at every `A`: no `T_1^{-1}`.**

The vector the level-two slope operator is read on at the composition `[A,1]`,
`T_1^{-1}(y_1^2d^*_+{}^{(1)}G_{1,A}(1))`, written out as a sum of monomials over the support of the
inner vector `y_1^2d^*_+{}^{(1)}G_{1,A}(1)` — which `HJO.Sweep.pairArgTwo_mem_piece`'s own
ingredients put in `V_2`, so `HJO.Sweep.braidInvEnd_one_of_mem_piece_two` applies.

With this, `HJO.Sweep.constantCoeff_lowerRun_two_stageWordTotal_pair_one` — the sweep side of the
`hlhs` clause at `[A,1]` — has **no braid operator left** on its right-hand side: what remains is
`HJO.Sym.Bop` on `Λ`, the displacement `d^*_+{}^{(0)}` and `HJO.Sweep.bopExt` inside
`HJO.Sweep.zDefect`, and the single `d^*_+{}^{(1)}` of the stage.

**Unconditional**, at every `A`, and `A` need not be positive. -/
theorem pairArgTwo_eq (q u : L) (A : ℕ) :
    pairArgTwo q u A
      = ∑ d ∈ ((auxVar 1 : Total L) ^ 2
            * dplusStar q u 1 (Mellit.stageWordTotal q u 2 3 [A])).support,
          MvPolynomial.C (MvPolynomial.coeff d ((auxVar 1 : Total L) ^ 2
              * dplusStar q u 1 (Mellit.stageWordTotal q u 2 3 [A])))
            * (scal q⁻¹ * ((auxVar 1 : Total L) ^ (d 1) * (auxVar 2 : Total L) ^ (d 0)
                + scal (q - 1) * ((auxVar 1 : Total L) ^ (d 0) * (auxVar 2 : Total L) ^ (d 1)
                    + auxVar 1 * pairBlock L 1 (d 0) (d 1)))) :=
  braidInvEnd_one_of_mem_piece_two q
    (mul_mem (pow_mem (auxVar_mem_piece le_rfl (by omega)) 2)
      (dplusStar_mem_piece q u (Mellit.stageWordTotal_singleton_mem_piece q u 2 3 A)))

/-- **`HJO.Sweep.pairArgSucc` made explicit at every `(A,B)`: no `T_1^{-1}`.**

The same for the *step* vector of the recursion in the second part,
`T_1^{-1}(y_1^2z_1^{(2)}(T_1(G_{2,B+1}G_{1,A}(1))))`. With this, the only sweep operator surviving
on the right of `HJO.Sweep.constantCoeff_lowerRun_two_stageWordTotal_pair_succ` is the *inner*
`z_1^{(2)}`, which `HJO.Sweep.zopOneStar_two_of_mem_piece` already turns into `Λ`-level data — so
the two-part recursion is explicit at every `(A,B)` up to that one expansion.

**Unconditional**, at every `A` and `B`, positive or not. -/
theorem pairArgSucc_eq (q u : L) (A B : ℕ) :
    pairArgSucc q u A B
      = ∑ d ∈ ((auxVar 1 : Total L) ^ 2
            * zopOneStar q u 2 (braidEnd q 1
              (Mellit.stageWordTotal q u 2 3 [A, B + 1]))).support,
          MvPolynomial.C (MvPolynomial.coeff d ((auxVar 1 : Total L) ^ 2
              * zopOneStar q u 2 (braidEnd q 1
                (Mellit.stageWordTotal q u 2 3 [A, B + 1]))))
            * (scal q⁻¹ * ((auxVar 1 : Total L) ^ (d 1) * (auxVar 2 : Total L) ^ (d 0)
                + scal (q - 1) * ((auxVar 1 : Total L) ^ (d 0) * (auxVar 2 : Total L) ^ (d 1)
                    + auxVar 1 * pairBlock L 1 (d 0) (d 1)))) :=
  braidInvEnd_one_of_mem_piece_two q
    (mul_mem (pow_mem (auxVar_mem_piece le_rfl (by omega)) 2)
      (zopOneStar_mem_piece q u (by omega) (braidEnd_mem_piece q le_rfl (by omega)
        (Mellit.stageWordTotal_pair_mem_piece q u 2 3 A (B + 1)))))

/-! ### The step vector at the first step: the inner braid letter is invisible too -/

/-- **The `[1,1]` stage word is symmetric in `y_1` and `y_2`.**

Read off the five-monomial value `HJO.Sweep.stageWordTotal_two_three_one_one`: the three
`s_1`-invariant monomials `y_1^2y_2^2`, `y_1^3y_2^3` carry `e_1^2`, `e_2` and `1`, and the pair
`y_1^3y_2^2`, `y_1^2y_2^3` carries the **same** coefficient `-que_1`, so the pair is symmetric as a
sum. This is the same phenomenon as `HJO.Sweep.swapAux_seedValueTwo`, of which this vector is a
scalar multiple.

`q ≠ 0`, `u ≠ 0`, `q ≠ 1` are the hypotheses of that value, each an inverse that becomes the zero
map. -/
theorem swapAux_one_stageWordTotal_two_three_one_one (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    swapAux L 1 (Mellit.stageWordTotal q u 2 3 [1, 1])
      = Mellit.stageWordTotal q u 2 3 [1, 1] := by
  rw [stageWordTotal_two_three_one_one hq0 hu0 hq1]
  simp only [← scal_mul_eq_smul_total, map_add, map_sub, map_mul, map_pow, swapAux_scal, swapAux_C,
    swapAux_one_auxVar_one, swapAux_one_auxVar_two]
  ring

/-- **`T_1` fixes the `[1,1]` stage word**, `HJO.Sweep.braidEnd_one_of_swapAux_eq` at
`HJO.Sweep.swapAux_one_stageWordTotal_two_three_one_one`.

This is the *trap* described in `HJO/Shuffle/SweepBraidMonomial.lean`, here in the useful direction:
on an `s_1`-symmetric vector the letter acts as `1`, **not** as multiplication by `q`, so the inner
braid letter of the step from `[1,1]` to `[1,2]` contributes nothing at all. -/
theorem braidEnd_one_stageWordTotal_two_three_one_one (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    braidEnd q 1 (Mellit.stageWordTotal q u 2 3 [1, 1])
      = Mellit.stageWordTotal q u 2 3 [1, 1] :=
  braidEnd_one_of_swapAux_eq q (swapAux_one_stageWordTotal_two_three_one_one hq0 hu0 hq1)

/-- **`T_1^{-1}` fixes the `[1,1]` stage word** too, `HJO.Sweep.braidInv_eq_self_of_swapAux_eq`. The
extra `q ≠ 0` this needs over `HJO.Sweep.braidEnd_one_stageWordTotal_two_three_one_one` is already
spent by `HJO.Sweep.stageWordTotal_two_three_one_one`. -/
theorem braidInvEnd_one_stageWordTotal_two_three_one_one (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    braidInvEnd q 1 (Mellit.stageWordTotal q u 2 3 [1, 1])
      = Mellit.stageWordTotal q u 2 3 [1, 1] :=
  braidInv_eq_self_of_swapAux_eq hq0
    (swapAux_one_stageWordTotal_two_three_one_one hq0 hu0 hq1)

/-- **The step vector of the `B`-recursion at `(A,B) = (1,0)`, with the inner braid letter gone**:

`pairArgSucc q u 1 0 = T_1^{-1}(y_1^2·z_1^{(2)}(G_{2,1}G_{1,1}(1)))`.

The definition has `T_1^{-1}(y_1^2·z_1^{(2)}(T_1(G_{2,1}G_{1,1}(1))))`, and
`HJO.Sweep.braidEnd_one_stageWordTotal_two_three_one_one` deletes the inner `T_1` outright — so at
the **first** step of the recursion in the second part only *one* braid letter survives, the outer
`T_1^{-1}`, and that one is evaluated at every monomial by
`HJO.Sweep.braidInvEnd_one_auxVar_pow_mul_auxVar_pow_pair`.

What this does *not* do is decide `ct(d_-^2(G_{2,2}G_{1,1}(1)))` as an element of `Λ`: that still
needs `HJO.Sweep.zDefect q u n A` at `(n,A) = (2, e_1^2)`, `(2, e_2)` and `(3, e_1)`, none of which
is available — the entries available are `HJO.Sweep.zDefect_two_one`, `zDefect_three_one`,
`zDefect_one_elemSymm_one`, `zDefect_two_elemSymm_one` and `zDefect_one_one`. That is the `B`-word
table in the `e`-basis, and it is what remains.

`q ≠ 0`, `u ≠ 0`, `q ≠ 1`, all three hypotheses of the `[1,1]` value
`HJO.Sweep.stageWordTotal_two_three_one_one`. -/
theorem pairArgSucc_one_zero (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    pairArgSucc q u 1 0
      = braidInvEnd q 1 ((auxVar 1 : Total L) ^ 2
          * zopOneStar q u 2 (Mellit.stageWordTotal q u 2 3 [1, 1])) := by
  rw [pairArgSucc, show (0 : ℕ) + 1 = 1 from rfl,
    braidEnd_one_stageWordTotal_two_three_one_one hq0 hu0 hq1]

end TwoPart

end HJO.Sweep

end
