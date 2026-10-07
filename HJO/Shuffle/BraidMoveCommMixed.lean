/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidMoveCommAbove
public meta import HJO.Attr

/-! # Exchanging the moves of two points on opposite sides of the puncture

The last of the three cases of `HJO.Braid.braidWord_pair_comm`: one point below the puncture,
contributing a `z` and rising, against one point above it, contributing a `ỹ` and falling. Unlike
the two equal-sign cases this is not a block commutation — `HJO.Braid.BraidMonoid` carries no
relation between a `z` and
a `ỹ`, and there is none to carry: the two letters interact through
`HJO.Braid.braidYtilde_zy`, `ỹ_1 T_1 z_1 = T_1 z_1 T_1 ỹ_1 T_1`.

## Main results

* `HJO.Braid.block_pair_eq_normal` — the normalisation: a product of two move-blocks whose letters
  have closed forms `g_m = T_{m↘1} g_1 T_{1↗m}` collapses, after one collision, to
  `T_{P↘1} T_{Q'↘2} g_1 T_1 h_1 T_{2↗m'} T_{1↗n}`.
* `HJO.Braid.ytildeZNormal_eq_zYtildeNormal` — the two normal forms agree. This is where
  `HJO.Braid.braidYtilde_zy` is spent, and it is the whole algebraic content of the case.
* `HJO.Braid.braidWord_pair_comm_of_lt_gt_theta` — the exchange lemma for a point below the
  puncture against one above it.
* `HJO.Braid.braidWord_pair_comm` — **the exchange lemma in the two-move form**: all
  three cases.
* `HJO.Braid.braidWord_swap` — the same read on a sequence of moves.

## Implementation notes

### The four sub-cases are two normal forms

Write `x = w_i < θ < w_j = y`, `x' = nx(x) = x + 1 - θ` and `y' = nx(y) = y - θ`. For `w` in
`(0,1)^k` the comparison `x'` against `y'` is **forced**: `x' - y' = x + 1 - y > 0`, so the two
points always cross, and the configuration is never the separated one of the two equal-sign cases.
What is left open is `x'` against `y` and `x` against `y'`, and all four combinations occur — the
first needs `θ > 1/2` to fail, the second `θ < 1/2`.

Writing `ε` for the indicator of `y' ≤ x` and `δ` for that of `y ≤ x'`, and `a₁ < a₂` for the two
initial ranks and `a₂' < a₁'` for the two final ones, the two orders are
`T_{a₁'↘a₁+ε} 𝗓_{a₁+ε} · T_{a₂'+1-ε↘a₂} ỹ_{a₂}` and
`T_{a₂'↘a₂-δ} ỹ_{a₂-δ} · T_{a₁'-1+δ↘a₁} 𝗓_{a₁}`. So `ε` moves only the first, `δ` only the second,
and the four sub-cases are **two** claims about each side rather than four about the pair: each side
normalises, for either value of its indicator, to one word in which `ỹ_1 T_1 𝗓_1` respectively
`𝗓_1 T_1 ỹ_1` stands alone between two trains. That collapse is `block_pair_eq_normal` used four
times, the collision index quadruple being `(1, m, n, 1)` each time and the two branches of
`HJO.Braid.collideIndex_one_down_one` being exactly the two values of the indicator.

### Two train identities

`HJO.Braid.trainUp_one_mul_trainUp_one`, `T_{1↗b} T_{1↗a} = T_{2↗a+1} T_{1↗b}` for `a < b`, is the
reverse-word mirror of `HJO.Braid.trainDown_one_mul_trainDown_one` and is **not** an instance of
`HJO.Braid.trainUp_overtake`: overtaking shifts the train that is passed *from the left*, and here
it is the train on the right that shifts. It is proved by the same induction, one letter at a time,
with `HJO.Braid.trainUp_mul_gen` raising the letter across the long train.
`HJO.Braid.trainUp_one_mul_trainDown_one_of_lt` and `..._of_gt` are
`HJO.Braid.IsBraidSystem.collide` at `(1, m, n, 1)`, whose collision indices depend only on whether
`m < n` or `n < m`.

## References

Lemma `HJO.Braid.braidWord_pair_comm`, using
`HJO.Braid.braidYtilde_zy`, `HJO.Braid.braidTrainDown_mul_braidGenZ`,
`HJO.Braid.braidTrainDown_mul_braidYtilde`, `HJO.Braid.IsBraidSystem.collide`,
`HJO.Braid.trainUp_overtake`, `HJO.Braid.trainUp_mul_trainUp`, `HJO.Braid.trainDown_mul_trainDown`,
`HJO.Braid.braidGenZ_eq_trainDown_mul_mul_trainUp`, `HJO.Braid.braidYtilde`. Transcribing A.
Mellit, *Toric braids and `(m, n)`-parking functions*, Lemma 5.9 — Mellit's own case (iii),
whose normal form `T_{a₂'↘1} T_{a₁'↘2} ỹ_1 T_1 z_1 T_{2↗a₂} T_{1↗a₁}` is the one used here.
-/

@[expose] public section

namespace HJO.Braid

/-! ### Two train identities -/

section Trains

variable {M : Type*} [Monoid M] {k : ℕ} {T Tinv : ℕ → M}

/-- **`T_{1↗b} T_{1↗a} = T_{2↗a+1} T_{1↗b}` for `1 ≤ a < b ≤ k`**: the short ascending train based
at `1` raises both its indices by one as it moves to the *left* of the long one.

This is not `HJO.Braid.trainUp_overtake`, which raises the indices of the train that moves to the
right; it is the word-reversal mirror of `HJO.Braid.trainDown_one_mul_trainDown_one`. Induction on
`a`: the step splits the top letter `T_a` off the short train, carries it across the long train by
`HJO.Braid.trainUp_mul_gen` — which raises it to `T_{a+1}`, the hypothesis `a + 1 < b` being what
that needs — and glues it back on top of the raised train. -/
theorem trainUp_one_mul_trainUp_one (h : IsBraidSystem k T Tinv) :
    ∀ a, 1 ≤ a → ∀ {b : ℕ}, a < b → b ≤ k →
      trainUp T Tinv 1 b * trainUp T Tinv 1 a
        = trainUp T Tinv 2 (a + 1) * trainUp T Tinv 1 b := by
  intro a ha
  induction a, ha using Nat.le_induction with
  | base =>
    intro b _ _
    rw [trainUp_self, trainUp_self, mul_one, one_mul]
  | succ a ha ih =>
    intro b hab hbk
    have hglue : trainUp T Tinv 2 (a + 1) * T (a + 1) = trainUp T Tinv 2 (a + 1 + 1) := by
      have := trainUp_mul_trainUp (T := T) (Tinv := Tinv) h (a := 2) (b := a + 1) (c := a + 1 + 1)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      rwa [show trainUp T Tinv (a + 1) (a + 1 + 1) = T (a + 1) from trainUp_self_succ T Tinv _]
        at this
    rw [← trainUp_one_mul_gen h ha (by omega), ← mul_assoc, ih (by omega) hbk, mul_assoc,
      trainUp_mul_gen h (by omega) (by omega) (by omega) hbk, ← mul_assoc, hglue]

/-- The collision indices of `(1, m, n, 1)` when the ascending train stops below the descending one:
the descending index is unchanged and the ascending one rises by one. -/
theorem collideIndex_one_down_one_of_lt {m n : ℤ} (hm : 1 ≤ m) (hmn : m < n) :
    collideIndex 1 m n 1 = (2, m + 1, n, 1) := by
  rw [collideIndex_eq,
    indexShift_fix (p := 1) (q := m) (x := n) (by omega) (by omega) (by omega),
    indexShift_up (p := 1) (q := n) (x := m) (by omega) (by omega) (by omega),
    indexShift_up (p := 1) (q := n) (x := 1) (by omega) (by omega) (by omega),
    indexShift_fix (p := 1 + 1) (q := m + 1) (x := 1) (by omega) (by omega) (by omega)]
  norm_num

/-- The collision indices of `(1, m, n, 1)` when the ascending train reaches past the descending
one: the ascending index is unchanged and the descending one rises by one. -/
theorem collideIndex_one_down_one_of_gt {m n : ℤ} (hn : 1 ≤ n) (hnm : n < m) :
    collideIndex 1 m n 1 = (2, m, n + 1, 1) := by
  rw [collideIndex_eq,
    indexShift_up (p := 1) (q := m) (x := n) (by omega) (by omega) (by omega),
    indexShift_fix (p := 1) (q := n) (x := m) (by omega) (by omega) (by omega),
    indexShift_up (p := 1) (q := n + 1) (x := 1) (by omega) (by omega) (by omega),
    indexShift_fix (p := 1 + 1) (q := m) (x := 1) (by omega) (by omega) (by omega)]
  norm_num

/-- **`T_{1↗m} T_{n↘1} = T_{n↘1} T_{2↗m+1}` for `1 ≤ m < n ≤ k`**: `HJO.Braid.IsBraidSystem.collide`
at `(1, m, n, 1)` on the branch where the ascending train stops below the descending one, so the
descending train is unchanged and the ascending one is raised. -/
theorem trainUp_one_mul_trainDown_one_of_lt (h : IsBraidSystem k T Tinv) {m n : ℕ} (hm : 1 ≤ m)
    (hmn : m < n) (hnk : n ≤ k) :
    trainUp T Tinv 1 m * trainDown T Tinv n 1
      = trainDown T Tinv n 1 * trainUp T Tinv 2 (m + 1) :=
  h.collide (by omega) (by omega) hm (by omega) (by omega) hnk (by omega) (by omega) (by omega)
    (by push_cast
        exact collideIndex_one_down_one_of_lt (by omega) (by exact_mod_cast hmn))

/-- **`T_{1↗m} T_{n↘1} = T_{n+1↘1} T_{2↗m}` for `1 ≤ n < m ≤ k`**: the other branch of
`HJO.Braid.IsBraidSystem.collide` at `(1, m, n, 1)`, where the ascending train reaches past the
descending one, so the ascending train is unchanged and the descending one is raised. -/
theorem trainUp_one_mul_trainDown_one_of_gt (h : IsBraidSystem k T Tinv) {m n : ℕ} (hn : 1 ≤ n)
    (hnm : n < m) (hmk : m ≤ k) :
    trainUp T Tinv 1 m * trainDown T Tinv n 1
      = trainDown T Tinv (n + 1) 1 * trainUp T Tinv 2 m :=
  h.collide (by omega) (by omega) (by omega) hmk hn (by omega) (by omega) (by omega) (by omega)
    (by push_cast
        exact collideIndex_one_down_one_of_gt (by omega) (by exact_mod_cast hnm))

end Trains

/-! ### The normalisation of a pair of blocks -/

/-- **A pair of move-blocks collapses to one normal form.** Each block is a descending train
followed by a letter with a closed form `g_m = T_{m↘1} g_1 T_{1↗m}` —
`HJO.Braid.braidGenZ_eq_trainDown_mul_mul_trainUp` for `z` and `HJO.Braid.braidYtilde` for `ỹ` — so
the outer train glues onto the inner one on each side and what is left between the two base letters
is one ascending–descending product, which `HJO.Braid.IsBraidSystem.collide` turns round. The two
base letters then sit adjacent, separated only by `T_1`, with every remaining train far from index
`1`.

Stated with the eight facts as hypotheses so that the four sub-cases of the mixed exchange lemma are
four instantiations of one calculation. -/
theorem block_pair_eq_normal {k P m Q n Q' m' : ℕ} {Gm G1 Hn H1 : BraidMonoid k}
    (hG : Gm = braidTrainDown k m 1 * G1 * braidTrainUp k 1 m)
    (hH : Hn = braidTrainDown k n 1 * H1 * braidTrainUp k 1 n)
    (hgP : braidTrainDown k P m * braidTrainDown k m 1 = braidTrainDown k P 1)
    (hgQ : braidTrainDown k Q n * braidTrainDown k n 1 = braidTrainDown k Q 1)
    (hcol : braidTrainUp k 1 m * braidTrainDown k Q 1
      = braidTrainDown k Q' 1 * braidTrainUp k 2 m')
    (hd : braidTrainDown k Q' 2 * braidGenT k 1 = braidTrainDown k Q' 1)
    (hGc : G1 * braidTrainDown k Q' 2 = braidTrainDown k Q' 2 * G1)
    (hHc : braidTrainUp k 2 m' * H1 = H1 * braidTrainUp k 2 m') :
    braidTrainDown k P m * Gm * (braidTrainDown k Q n * Hn)
      = braidTrainDown k P 1 * braidTrainDown k Q' 2 * G1 * braidGenT k 1 * H1
        * braidTrainUp k 2 m' * braidTrainUp k 1 n := by
  calc braidTrainDown k P m * Gm * (braidTrainDown k Q n * Hn)
      = braidTrainDown k P m * braidTrainDown k m 1 * G1
          * (braidTrainUp k 1 m * (braidTrainDown k Q n * braidTrainDown k n 1
            * (H1 * braidTrainUp k 1 n))) := by rw [hG, hH]; simp only [mul_assoc]
    _ = braidTrainDown k P 1 * G1 * (braidTrainUp k 1 m * braidTrainDown k Q 1
          * (H1 * braidTrainUp k 1 n)) := by rw [hgP, hgQ]; simp only [mul_assoc]
    _ = braidTrainDown k P 1 * G1 * (braidTrainDown k Q' 2 * braidGenT k 1
          * braidTrainUp k 2 m' * (H1 * braidTrainUp k 1 n)) := by rw [hcol, ← hd]
    _ = braidTrainDown k P 1 * (G1 * braidTrainDown k Q' 2) * braidGenT k 1
          * (braidTrainUp k 2 m' * H1) * braidTrainUp k 1 n := by simp only [mul_assoc]
    _ = braidTrainDown k P 1 * braidTrainDown k Q' 2 * G1 * braidGenT k 1 * H1
          * braidTrainUp k 2 m' * braidTrainUp k 1 n := by
        rw [hGc, hHc]; simp only [mul_assoc]

/-- **The two normal forms agree.** This is the whole algebraic content of the mixed case:
`HJO.Braid.braidYtilde_zy` exchanges the two base letters at index `1`, the two `T_1`'s it produces
glue onto the neighbouring trains, and the two resulting pairs of like trains are turned round by
`HJO.Braid.trainUp_overtake` (`HJO.Braid.trainDown_one_mul_trainDown_one`) and its ascending mirror
`HJO.Braid.trainUp_one_mul_trainUp_one`. -/
theorem ytildeZNormal_eq_zYtildeNormal {k a₁ a₂ a₁' a₂' : ℕ} (ha₁ : 1 ≤ a₁) (ha₁₂ : a₁ < a₂)
    (ha₂k : a₂ ≤ k) (ha₂' : 1 ≤ a₂') (ha' : a₂' < a₁') (ha₁'k : a₁' ≤ k) :
    braidTrainDown k a₂' 1 * braidTrainDown k a₁' 2 * braidYtilde k 1 * braidGenT k 1
          * braidGenZ k 1 * braidTrainUp k 2 a₂ * braidTrainUp k 1 a₁
      = braidTrainDown k a₁' 1 * braidTrainDown k (a₂' + 1) 2 * braidGenZ k 1 * braidGenT k 1
          * braidYtilde k 1 * braidTrainUp k 2 (a₁ + 1) * braidTrainUp k 1 a₂ := by
  have hsys := isBraidSystem_braidGenT k
  have hzy : braidYtilde k 1 * braidGenT k 1 * braidGenZ k 1
      = braidGenT k 1 * braidGenZ k 1 * braidGenT k 1 * braidYtilde k 1 * braidGenT k 1 :=
    braidYtilde_zy (by omega)
  have hdglue : braidTrainDown k a₁' 2 * braidGenT k 1 = braidTrainDown k a₁' 1 :=
    trainDown_two_mul_gen hsys (by omega) ha₁'k
  have huglue : braidGenT k 1 * braidTrainUp k 2 a₂ = braidTrainUp k 1 a₂ := by
    have h2 : braidTrainUp k 1 2 = braidGenT k 1 := trainUp_self_succ (braidGenT k) _ 1
    rw [← h2]
    exact trainUp_mul_trainUp (T := braidGenT k) (Tinv := braidGenTinv k) hsys (a := 1) (b := 2)
      (c := a₂) (by omega) (by omega) (by omega) (by omega) (by omega) ha₂k
  have hdown : braidTrainDown k a₂' 1 * braidTrainDown k a₁' 1
      = braidTrainDown k a₁' 1 * braidTrainDown k (a₂' + 1) 2 :=
    trainDown_one_mul_trainDown_one hsys ha₂' ha' ha₁'k
  have hup : braidTrainUp k 1 a₂ * braidTrainUp k 1 a₁
      = braidTrainUp k 2 (a₁ + 1) * braidTrainUp k 1 a₂ :=
    trainUp_one_mul_trainUp_one hsys a₁ ha₁ ha₁₂ ha₂k
  calc braidTrainDown k a₂' 1 * braidTrainDown k a₁' 2 * braidYtilde k 1 * braidGenT k 1
          * braidGenZ k 1 * braidTrainUp k 2 a₂ * braidTrainUp k 1 a₁
      = braidTrainDown k a₂' 1 * braidTrainDown k a₁' 2
          * (braidYtilde k 1 * braidGenT k 1 * braidGenZ k 1)
          * (braidTrainUp k 2 a₂ * braidTrainUp k 1 a₁) := by simp only [mul_assoc]
    _ = braidTrainDown k a₂' 1 * (braidTrainDown k a₁' 2 * braidGenT k 1) * braidGenZ k 1
          * braidGenT k 1 * braidYtilde k 1 * (braidGenT k 1 * braidTrainUp k 2 a₂)
          * braidTrainUp k 1 a₁ := by rw [hzy]; simp only [mul_assoc]
    _ = braidTrainDown k a₂' 1 * braidTrainDown k a₁' 1 * braidGenZ k 1 * braidGenT k 1
          * braidYtilde k 1 * braidTrainUp k 1 a₂ * braidTrainUp k 1 a₁ := by
        rw [hdglue, huglue]
    _ = braidTrainDown k a₁' 1 * braidTrainDown k (a₂' + 1) 2 * braidGenZ k 1 * braidGenT k 1
          * braidYtilde k 1 * braidTrainUp k 1 a₂ * braidTrainUp k 1 a₁ := by rw [hdown]
    _ = braidTrainDown k a₁' 1 * braidTrainDown k (a₂' + 1) 2 * braidGenZ k 1 * braidGenT k 1
          * braidYtilde k 1 * (braidTrainUp k 1 a₂ * braidTrainUp k 1 a₁) := mul_assoc _ _ _
    _ = braidTrainDown k a₁' 1 * braidTrainDown k (a₂' + 1) 2 * braidGenZ k 1 * braidGenT k 1
          * braidYtilde k 1 * (braidTrainUp k 2 (a₁ + 1) * braidTrainUp k 1 a₂) := by rw [hup]
    _ = braidTrainDown k a₁' 1 * braidTrainDown k (a₂' + 1) 2 * braidGenZ k 1 * braidGenT k 1
          * braidYtilde k 1 * braidTrainUp k 2 (a₁ + 1) * braidTrainUp k 1 a₂ :=
        (mul_assoc _ _ _).symm

/-! ### The four sub-cases, two normal forms -/

/-- The `ỹ`-then-`z` order in the sub-case where the `ỹ`-block's train stops below the `z`-block's:
Mellit's case (iii)(a), where `y < x'` and the upper point's rank drops to `a₂ - 1 = c`. -/
theorem ytildeZBlock_eq_normal_of_lt {k a₁ c a₁' a₂' : ℕ} (ha₁ : 1 ≤ a₁) (ha₁k : a₁ ≤ k)
    (hc : 1 ≤ c) (hck : c + 1 ≤ k) (ha₂' : 1 ≤ a₂') (ha₂'k : a₂' ≤ k) (hca₁' : c < a₁')
    (ha₁'k : a₁' ≤ k) :
    braidTrainDown k a₂' c * braidYtilde k c * (braidTrainDown k a₁' a₁ * braidGenZ k a₁)
      = braidTrainDown k a₂' 1 * braidTrainDown k a₁' 2 * braidYtilde k 1 * braidGenT k 1
        * braidGenZ k 1 * braidTrainUp k 2 (c + 1) * braidTrainUp k 1 a₁ := by
  have hsys := isBraidSystem_braidGenT k
  exact block_pair_eq_normal (braidYtilde_eq_trainDown_one_mul hc (by omega))
    (braidGenZ_eq_trainDown_mul_mul_trainUp k a₁ ha₁ ha₁k)
    (trainDown_mul_trainDown hsys ha₂' ha₂'k hc (by omega) (by omega) (by omega))
    (trainDown_mul_trainDown hsys (by omega) ha₁'k ha₁ ha₁k (by omega) (by omega))
    (trainUp_one_mul_trainDown_one_of_lt hsys hc hca₁' ha₁'k)
    (trainDown_two_mul_gen hsys (by omega) ha₁'k)
    (braidYtilde_comm_trainDown (by omega) (by omega) (by omega) ha₁'k (by omega) (by omega)
      (by omega))
    (braidGenZ_comm_trainUp (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)).symm

/-- The `ỹ`-then-`z` order in the sub-case where the `ỹ`-block's train reaches past the `z`-block's:
Mellit's case (iii)(b), where `x' < y` and the lower point's final rank is `a₁' = e + 1`. -/
theorem ytildeZBlock_eq_normal_of_gt {k a₁ a₂ e a₂' : ℕ} (ha₁ : 1 ≤ a₁) (ha₁k : a₁ ≤ k)
    (he : 1 ≤ e) (hea₂ : e < a₂) (ha₂k : a₂ ≤ k) (ha₂' : 1 ≤ a₂') (ha₂'k : a₂' ≤ k) :
    braidTrainDown k a₂' a₂ * braidYtilde k a₂ * (braidTrainDown k e a₁ * braidGenZ k a₁)
      = braidTrainDown k a₂' 1 * braidTrainDown k (e + 1) 2 * braidYtilde k 1 * braidGenT k 1
        * braidGenZ k 1 * braidTrainUp k 2 a₂ * braidTrainUp k 1 a₁ := by
  have hsys := isBraidSystem_braidGenT k
  exact block_pair_eq_normal (braidYtilde_eq_trainDown_one_mul (by omega) ha₂k)
    (braidGenZ_eq_trainDown_mul_mul_trainUp k a₁ ha₁ ha₁k)
    (trainDown_mul_trainDown hsys ha₂' ha₂'k (by omega) ha₂k (by omega) (by omega))
    (trainDown_mul_trainDown hsys he (by omega) ha₁ ha₁k (by omega) (by omega))
    (trainUp_one_mul_trainDown_one_of_gt hsys he hea₂ ha₂k)
    (trainDown_two_mul_gen hsys (by omega) (by omega))
    (braidYtilde_comm_trainDown (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega))
    (braidGenZ_comm_trainUp (by omega) (by omega) (by omega) (by omega) (by omega) ha₂k
      (by omega)).symm

/-- The `z`-then-`ỹ` order in the sub-case where the `z`-block's train stops below the `ỹ`-block's:
Mellit's case (iii)(a'), where `x < y'` and the upper point's rank before its move is
`a₂' + 1`. -/
theorem zYtildeBlock_eq_normal_of_lt {k a₁ a₂ a₁' a₂' : ℕ} (ha₁ : 1 ≤ a₁) (ha₁a₂' : a₁ ≤ a₂')
    (ha₂' : 1 ≤ a₂') (ha₂'k : a₂' + 1 ≤ k) (ha₂ : 1 ≤ a₂) (ha₂k : a₂ ≤ k) (ha₁' : 1 ≤ a₁')
    (ha₁'k : a₁' ≤ k) :
    braidTrainDown k a₁' a₁ * braidGenZ k a₁ * (braidTrainDown k (a₂' + 1) a₂ * braidYtilde k a₂)
      = braidTrainDown k a₁' 1 * braidTrainDown k (a₂' + 1) 2 * braidGenZ k 1 * braidGenT k 1
        * braidYtilde k 1 * braidTrainUp k 2 (a₁ + 1) * braidTrainUp k 1 a₂ := by
  have hsys := isBraidSystem_braidGenT k
  exact block_pair_eq_normal (braidGenZ_eq_trainDown_mul_mul_trainUp k a₁ ha₁ (by omega))
    (braidYtilde_eq_trainDown_one_mul ha₂ ha₂k)
    (trainDown_mul_trainDown hsys ha₁' ha₁'k ha₁ (by omega) (by omega) (by omega))
    (trainDown_mul_trainDown hsys (by omega) ha₂'k ha₂ ha₂k (by omega) (by omega))
    (trainUp_one_mul_trainDown_one_of_lt hsys ha₁ (by omega) ha₂'k)
    (trainDown_two_mul_gen hsys (by omega) ha₂'k)
    (braidGenZ_comm_trainDown (by omega) (by omega) (by omega) ha₂'k (by omega) (by omega)
      (by omega))
    (braidYtilde_comm_trainUp (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)).symm

/-- The `z`-then-`ỹ` order in the sub-case where the `z`-block's train reaches past the `ỹ`-block's:
Mellit's case (iii)(b'), where `y' < x` and the lower point's rank before its move is
`a₁ + 1`. -/
theorem zYtildeBlock_eq_normal_of_gt {k a₁ a₂ a₁' a₂' : ℕ} (ha₂' : 1 ≤ a₂') (ha₂'a₁ : a₂' ≤ a₁)
    (ha₁k : a₁ + 1 ≤ k) (ha₂ : 1 ≤ a₂) (ha₂k : a₂ ≤ k) (ha₁' : 1 ≤ a₁') (ha₁'k : a₁' ≤ k) :
    braidTrainDown k a₁' (a₁ + 1) * braidGenZ k (a₁ + 1)
        * (braidTrainDown k a₂' a₂ * braidYtilde k a₂)
      = braidTrainDown k a₁' 1 * braidTrainDown k (a₂' + 1) 2 * braidGenZ k 1 * braidGenT k 1
        * braidYtilde k 1 * braidTrainUp k 2 (a₁ + 1) * braidTrainUp k 1 a₂ := by
  have hsys := isBraidSystem_braidGenT k
  exact block_pair_eq_normal
    (braidGenZ_eq_trainDown_mul_mul_trainUp k (a₁ + 1) (by omega) ha₁k)
    (braidYtilde_eq_trainDown_one_mul ha₂ ha₂k)
    (trainDown_mul_trainDown hsys ha₁' ha₁'k (by omega) ha₁k (by omega) (by omega))
    (trainDown_mul_trainDown hsys ha₂' (by omega) ha₂ ha₂k (by omega) (by omega))
    (trainUp_one_mul_trainDown_one_of_gt hsys ha₂' (by omega) ha₁k)
    (trainDown_two_mul_gen hsys (by omega) (by omega))
    (braidGenZ_comm_trainDown (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega))
    (braidYtilde_comm_trainUp (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)).symm

/-! ### The exchange lemma across the puncture -/

/-- **The moves of a point below the puncture and a point above it may be exchanged.** With
`w_i < θ < w_j` the lower point contributes a `z` and rises, the upper one a `ỹ` and falls.

The hypothesis `w_j < w_i + 1` — which `HJO.Braid.IsSpecialBraidData`'s `w ∈ (0,1)^k` supplies — is
what forces `nx(w_j) < nx(w_i)`: the two points *always* cross, so there is no separated
configuration here. The two comparisons left open are `nx(w_i)` against `w_j` and `w_i` against
`nx(w_j)`, and they move the two sides independently: each side has two shapes, each shape has one
normal form, and the two normal forms agree by `HJO.Braid.ytildeZNormal_eq_zYtildeNormal`. -/
theorem braidWord_pair_comm_of_lt_gt_theta {θ : ℚ} {k : ℕ} {w : Fin k → ℚ} {i j : Fin k}
    (hij : i ≠ j) (hxθ : w i < θ) (hyθ : θ < w j) (hsum : w j < w i + 1)
    (hne1 : nextCrossing θ (w i) ≠ w j) (hne2 : nextCrossing θ (w j) ≠ w i) :
    braidWord θ w [i, j] = braidWord θ w [j, i] := by
  have hx' : nextCrossing θ (w i) = w i + 1 - θ := by
    simp only [nextCrossing, not_lt.2 hxθ.le, ite_false]
  have hy' : nextCrossing θ (w j) = w j - θ := by
    simp only [nextCrossing, hyθ, ite_true]
  have hxy : w i < w j := hxθ.trans hyθ
  have hy'x' : nextCrossing θ (w j) < nextCrossing θ (w i) := by rw [hx', hy']; linarith
  have hui : moveOne θ w i i = nextCrossing θ (w i) := moveOne_self ..
  have huj : moveOne θ w i j = w j := moveOne_of_ne θ w (Ne.symm hij)
  have hvi : moveOne θ w j i = w i := moveOne_of_ne θ w hij
  have hvj : moveOne θ w j j = nextCrossing θ (w j) := moveOne_self ..
  have hfin : moveOne θ (moveOne θ w j) i = moveOne θ (moveOne θ w i) j := moveOne_comm θ w hij
  have hfi : moveOne θ (moveOne θ w j) i i = nextCrossing θ (w i) := by rw [moveOne_self, hvi]
  have hfj : moveOne θ (moveOne θ w j) i j = nextCrossing θ (w j) := by
    rw [moveOne_of_ne θ _ (Ne.symm hij), hvj]
  -- The four rank equations.
  have E1 : entryRank (moveOne θ w j) i + (if w j ≤ w i then 1 else 0)
      = entryRank w i + (if nextCrossing θ (w j) ≤ w i then 1 else 0) :=
    entryRank_update_of_ne w hij _
  have E2 : entryRank (moveOne θ w i) j + (if w i ≤ w j then 1 else 0)
      = entryRank w j + (if nextCrossing θ (w i) ≤ w j then 1 else 0) :=
    entryRank_update_of_ne w (Ne.symm hij) _
  have E3 : entryRank (moveOne θ (moveOne θ w i) j) i
        + (if moveOne θ w i j ≤ moveOne θ w i i then 1 else 0)
      = entryRank (moveOne θ w i) i
        + (if nextCrossing θ (moveOne θ w i j) ≤ moveOne θ w i i then 1 else 0) :=
    entryRank_update_of_ne (moveOne θ w i) hij _
  have E4 : entryRank (moveOne θ (moveOne θ w j) i) j
        + (if moveOne θ w j i ≤ moveOne θ w j j then 1 else 0)
      = entryRank (moveOne θ w j) j
        + (if nextCrossing θ (moveOne θ w j i) ≤ moveOne θ w j j then 1 else 0) :=
    entryRank_update_of_ne (moveOne θ w j) (Ne.symm hij) _
  rw [hui, huj, ← hfin] at E3
  rw [hvi, hvj] at E4
  simp only [show ¬(w j ≤ w i) from by linarith, hxy.le, hy'x'.le,
    show ¬(nextCrossing θ (w i) ≤ nextCrossing θ (w j)) from by linarith,
    ite_true, ite_false, add_zero] at E1 E2 E3 E4
  -- The rank bounds, which are all the arithmetic the four sub-cases need.
  have hA1 : 1 ≤ entryRank w i := entryRank_pos ..
  have hBk : entryRank w j ≤ k := entryRank_le ..
  have hA'1 : 1 ≤ entryRank (moveOne θ w i) i := entryRank_pos ..
  have hBi1 : 1 ≤ entryRank (moveOne θ w i) j := entryRank_pos ..
  have hFj1 : 1 ≤ entryRank (moveOne θ (moveOne θ w j) i) j := entryRank_pos ..
  have hFik : entryRank (moveOne θ (moveOne θ w j) i) i ≤ k := entryRank_le ..
  have hAB : entryRank w i < entryRank w j := (entryRank_lt_entryRank_iff w i j).2 hxy
  have hFF : entryRank (moveOne θ (moveOne θ w j) i) j
      < entryRank (moveOne θ (moveOne θ w j) i) i :=
    (entryRank_lt_entryRank_iff _ j i).2 (by rw [hfi, hfj]; exact hy'x')
  rw [braidWord_pair, braidWord_pair,
    braidStep_of_lt (show moveOne θ w j i < θ by rw [hvi]; exact hxθ),
    braidStep_of_gt hyθ, braidStep_of_gt (show θ < moveOne θ w i j by rw [huj]; exact hyθ),
    braidStep_of_lt hxθ, ← hfin]
  rcases lt_or_gt_of_ne hne2 with hε | hε
  · -- `nx(w_j) < w_i`: the upper point falls below the lower one.
    have hAj : entryRank (moveOne θ w j) i = entryRank w i + 1 := by
      simp only [hε.le, ite_true] at E1; omega
    have hB' : entryRank (moveOne θ w j) j = entryRank (moveOne θ (moveOne θ w j) i) j := by
      simp only [show ¬(w i ≤ nextCrossing θ (w j)) from by linarith, ite_false, add_zero] at E4
      omega
    have hFjA : entryRank (moveOne θ (moveOne θ w j) i) j ≤ entryRank w i := by
      have := (entryRank_lt_entryRank_iff (moveOne θ w j) j i).2 (by rw [hvi, hvj]; exact hε)
      omega
    rcases lt_or_gt_of_ne hne1 with hδ | hδ
    · -- `nx(w_i) < w_j`: the lower point stays below the upper one's old place.
      have hBi : entryRank (moveOne θ w i) j = entryRank w j := by
        simp only [hδ.le, ite_true] at E2; omega
      have hFi : entryRank (moveOne θ (moveOne θ w j) i) i
          = entryRank (moveOne θ w i) i + 1 := by
        simp only [show ¬(w j ≤ nextCrossing θ (w i)) from by linarith, ite_false,
          add_zero] at E3
        omega
      have hA'B : entryRank (moveOne θ w i) i < entryRank (moveOne θ w i) j :=
        (entryRank_lt_entryRank_iff (moveOne θ w i) i j).2 (by rw [hui, huj]; exact hδ)
      rw [hAj, hB', hBi, hFi,
        zYtildeBlock_eq_normal_of_gt hFj1 hFjA (by omega) (by omega) hBk (by omega) (by omega),
        ytildeZBlock_eq_normal_of_gt hA1 (by omega) (by omega) (by omega) hBk hFj1 (by omega)]
      exact (ytildeZNormal_eq_zYtildeNormal hA1 hAB hBk hFj1 (by omega) (by omega)).symm
    · -- `w_j < nx(w_i)`: the lower point rises past the upper one's old place.
      have hB : entryRank w j = entryRank (moveOne θ w i) j + 1 := by
        simp only [show ¬(nextCrossing θ (w i) ≤ w j) from by linarith, ite_false,
          add_zero] at E2
        omega
      have hFi : entryRank (moveOne θ (moveOne θ w j) i) i = entryRank (moveOne θ w i) i := by
        simp only [hδ.le, ite_true] at E3
        omega
      have hBA' : entryRank (moveOne θ w i) j < entryRank (moveOne θ w i) i :=
        (entryRank_lt_entryRank_iff (moveOne θ w i) j i).2 (by rw [hui, huj]; exact hδ)
      rw [hAj, hB', hB, hFi,
        zYtildeBlock_eq_normal_of_gt hFj1 hFjA (by omega) (by omega) (by omega) (by omega)
          (by omega),
        ytildeZBlock_eq_normal_of_lt hA1 (by omega) (by omega) (by omega) hFj1 (by omega)
          (by omega) (by omega)]
      exact (ytildeZNormal_eq_zYtildeNormal hA1 (by omega) (by omega) hFj1 (by omega)
        (by omega)).symm
  · -- `w_i < nx(w_j)`: the upper point stays above the lower one.
    have hAj : entryRank (moveOne θ w j) i = entryRank w i := by
      simp only [show ¬(nextCrossing θ (w j) ≤ w i) from by linarith, ite_false, add_zero] at E1
      omega
    have hB' : entryRank (moveOne θ w j) j
        = entryRank (moveOne θ (moveOne θ w j) i) j + 1 := by
      simp only [hε.le, ite_true] at E4
      omega
    have hAFj : entryRank w i ≤ entryRank (moveOne θ (moveOne θ w j) i) j := by
      have := (entryRank_lt_entryRank_iff (moveOne θ w j) i j).2 (by rw [hvi, hvj]; exact hε)
      omega
    rcases lt_or_gt_of_ne hne1 with hδ | hδ
    · have hBi : entryRank (moveOne θ w i) j = entryRank w j := by
        simp only [hδ.le, ite_true] at E2; omega
      have hFi : entryRank (moveOne θ (moveOne θ w j) i) i
          = entryRank (moveOne θ w i) i + 1 := by
        simp only [show ¬(w j ≤ nextCrossing θ (w i)) from by linarith, ite_false,
          add_zero] at E3
        omega
      have hA'B : entryRank (moveOne θ w i) i < entryRank (moveOne θ w i) j :=
        (entryRank_lt_entryRank_iff (moveOne θ w i) i j).2 (by rw [hui, huj]; exact hδ)
      rw [hAj, hB', hBi, hFi,
        zYtildeBlock_eq_normal_of_lt hA1 hAFj hFj1 (by omega) (by omega) hBk (by omega)
          (by omega),
        ytildeZBlock_eq_normal_of_gt hA1 (by omega) (by omega) (by omega) hBk hFj1 (by omega)]
      exact (ytildeZNormal_eq_zYtildeNormal hA1 hAB hBk hFj1 (by omega) (by omega)).symm
    · have hB : entryRank w j = entryRank (moveOne θ w i) j + 1 := by
        simp only [show ¬(nextCrossing θ (w i) ≤ w j) from by linarith, ite_false,
          add_zero] at E2
        omega
      have hFi : entryRank (moveOne θ (moveOne θ w j) i) i = entryRank (moveOne θ w i) i := by
        simp only [hδ.le, ite_true] at E3
        omega
      have hBA' : entryRank (moveOne θ w i) j < entryRank (moveOne θ w i) i :=
        (entryRank_lt_entryRank_iff (moveOne θ w i) j i).2 (by rw [hui, huj]; exact hδ)
      rw [hAj, hB', hB, hFi,
        zYtildeBlock_eq_normal_of_lt hA1 hAFj hFj1 (by omega) (by omega) (by omega) (by omega)
          (by omega),
        ytildeZBlock_eq_normal_of_lt hA1 (by omega) (by omega) (by omega) hFj1 (by omega)
          (by omega) (by omega)]
      exact (ytildeZNormal_eq_zYtildeNormal hA1 (by omega) (by omega) hFj1 (by omega)
        (by omega)).symm

/-! ### `HJO.Braid.braidWord_pair_comm`: all three cases -/

/-- **The two-move form: the moves of two distinct points may be
exchanged.** `b_{i,j}(w) = b_{j,i}(w)` for `i ≠ j`, provided neither moving entry sits on the
puncture and the four numbers `w_i`, `w_j`, `nx(w_i)`, `nx(w_j)` avoid the three collisions that
`HJO.Braid.IsSpecialBraidData`'s admissibility excludes.

The three cases of the sign of `w_i - θ` and `w_j - θ` are
`HJO.Braid.braidWord_pair_comm_of_lt_theta'` (both below),
`HJO.Braid.braidWord_pair_comm_of_gt_theta'` (both above) and
`HJO.Braid.braidWord_pair_comm_of_lt_gt_theta` (one of each, in either order); the fourth pair of
signs does not exist, the conclusion being symmetric in `i` and `j`. The hypothesis
`w ∈ (0,1)^k` is spent only in the mixed case, where it is what says the two points cross. -/
@[hjo "lem_braid_move_comm"]
theorem braidWord_pair_comm {θ : ℚ} {k : ℕ} {w : Fin k → ℚ} {i j : Fin k} (hij : i ≠ j)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hw : ∀ t, w t ∈ Set.Ioo (0 : ℚ) 1) (hiθ : w i ≠ θ)
    (hjθ : w j ≠ θ) (hne0 : w i ≠ w j) (hne1 : nextCrossing θ (w i) ≠ w j)
    (hne2 : nextCrossing θ (w j) ≠ w i) :
    braidWord θ w [i, j] = braidWord θ w [j, i] := by
  rcases lt_or_gt_of_ne hiθ with hi | hi
  · rcases lt_or_gt_of_ne hjθ with hj | hj
    · exact braidWord_pair_comm_of_lt_theta' hij hθ1 hi hj hne0 hne1 (Ne.symm hne2)
    · exact braidWord_pair_comm_of_lt_gt_theta hij hi hj
        (by have := (hw i).1; have := (hw j).2; linarith) hne1 hne2
  · rcases lt_or_gt_of_ne hjθ with hj | hj
    · exact (braidWord_pair_comm_of_lt_gt_theta (Ne.symm hij) hj hi
        (by have := (hw j).1; have := (hw i).2; linarith) hne2 hne1).symm
    · exact braidWord_pair_comm_of_gt_theta' hij hθ0 hi hj hne0 hne2 hne1

/-- **`HJO.Braid.braidWord_pair_comm`, the sequence form: exchanging two adjacent moves of distinct
points leaves the braid of the sequence unchanged.** The moves of the suffix are performed first, so
every hypothesis is read at the tuple the suffix has advanced — which is the form
`HJO.Braid.IsAdmissibleMoveSeq` supplies, and the form
`HJO.Braid.braidWord_swap_of_lt_theta` already has. -/
@[hjo "lem_braid_move_comm"]
theorem braidWord_swap {θ : ℚ} {k : ℕ} (w : Fin k → ℚ) {i j : Fin k} (hij : i ≠ j)
    (l₁ l₂ : List (Fin k)) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hw : ∀ t, moveTuple θ w l₂ t ∈ Set.Ioo (0 : ℚ) 1)
    (hiθ : moveTuple θ w l₂ i ≠ θ) (hjθ : moveTuple θ w l₂ j ≠ θ)
    (hne0 : moveTuple θ w l₂ i ≠ moveTuple θ w l₂ j)
    (hne1 : nextCrossing θ (moveTuple θ w l₂ i) ≠ moveTuple θ w l₂ j)
    (hne2 : nextCrossing θ (moveTuple θ w l₂ j) ≠ moveTuple θ w l₂ i) :
    braidWord θ w (l₁ ++ i :: j :: l₂) = braidWord θ w (l₁ ++ j :: i :: l₂) :=
  braidWord_swap_of_pair_comm θ w hij l₁ l₂
    (braidWord_pair_comm hij hθ0 hθ1 hw hiθ hjθ hne0 hne1 hne2)

/-- **The hypotheses are satisfiable, and in the mixed case.** At `θ = 1/2` the tuple
`(2/5, 4/5)` has one entry on each side of the puncture and meets every admissibility clause, so
`HJO.Braid.braidWord_pair_comm` does fire; the conclusion is a genuine identity in
`𝔹_2^+(𝕋_0)` and not a conditional nothing satisfies. -/
theorem braidWord_pair_comm_example :
    braidWord (1 / 2 : ℚ) (![2 / 5, 4 / 5] : Fin 2 → ℚ) [0, 1]
      = braidWord (1 / 2 : ℚ) (![2 / 5, 4 / 5] : Fin 2 → ℚ) [1, 0] := by
  refine braidWord_pair_comm (by decide) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [Fin.forall_fin_two]; norm_num [Set.mem_Ioo]
  all_goals norm_num [nextCrossing]

end HJO.Braid
