/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidSpecial
public import HJO.Shuffle.BraidTrainRules
public import HJO.Shuffle.BraidTrainCollide
public import Mathlib.Tactic.Linarith
public meta import HJO.Attr

/-! # Exchanging the moves of two distinct points

`HJO.Braid.specialBraid` fixes the order in which the points of special-braid data move **by their
index**: `HJO.Braid.braidWord` performs the last entry of the sequence first, so the moves of index
`0` come last in time and stand leftmost. Moving a component from one index to another therefore
commutes its whole run of moves past the runs of the other points, and that is a statement about
braids and not bookkeeping — `HJO.Braid.braidStep` is read at the *intermediate* tuples, and those
differ between the two orders.

This file is the exchange lemma for **one** pair of moves, and the reduction of the list-level
statement to it.

## Main results

* `HJO.Braid.moveOne_comm` — the tuple-level half, which *is* routine: two moves at distinct
  indices update distinct entries, so the tuple after both is independent of the order.
* `HJO.Braid.braidWord_swap_of_pair_comm` — the reduction: if the two-move words agree at the tuple
  the suffix has already advanced, then exchanging the two adjacent entries anywhere in a sequence
  of moves leaves the braid unchanged. Letter-type agnostic, so it serves all three cases.
* `HJO.Braid.braidWord_pair_comm_of_lt_theta` — **the exchange lemma for two points below the
  puncture**, `HJO.Braid.braidWord_swap_of_lt_theta`: if both moving entries are `< θ` then the two
  orders give the same braid.
* `HJO.Braid.braidWord_swap_of_lt_theta` — the same, read on a sequence of moves.
* `HJO.Braid.zBlock_comm_of_separated`, `HJO.Braid.zBlock_comm_of_overtake` — the two algebraic
  cores, and the two configurations the geometry leaves: the point that moves first either stays
  below the other one or overtakes it.
* `HJO.Braid.ytilde_z_exchange_two` — the kernel witness that the remaining *mixed* case is
  Mellit's one mixed relation and nothing else: at rank `2` the identity the exchange lemma needs
  for a `z`-move against a `ỹ`-move is `HJO.Braid.BraidMonoid`'s
  `𝗓_1 T_1 𝗒_1 T̄_1 = T̄_1 𝗒_1 T̄_1 𝗓_1`.

## Implementation notes

### Only three cases survive, and the fourth is excluded by the puncture

Write `x = w_i`, `y = w_j` and suppose `x < y` — the conclusion is symmetric in `i` and `j`, so this
is no loss. The move of a point below `θ` contributes a `z` and *raises* its value by `1 - θ`; the
move of a point above `θ` contributes a `ỹ` and *lowers* it by `θ`. So there are a priori four
letter-type pairs, and the pair "`x` above the puncture, `y` below it" is empty: `θ < x` and
`x < y` force `θ < y`. What is left is `z`–`z` (this file), `z`–`ỹ` and `ỹ`–`ỹ`.

### The two configurations of the `z`–`z` case

With `x < y < θ` the four values are ordered `x < y`, `x < x'`, `y < y'`, `x' < y'` and `x < y'`;
the one comparison the arithmetic does not settle is `x'` against `y`. If `x' < y` the runs do not
interleave: each point's rank is the same whether or not the other has moved, and the two braids are
literally the same two factors in the two orders, so the content is the commutation of two letter
blocks whose rank ranges are separated (`zBlock_comm_of_separated`). If `y < x'` the first point
overtakes the second, the intermediate ranks genuinely differ, and the identity is a collision of
trains — `HJO.Braid.IsBraidSystem.collide` at the quadruple of `HJO.Braid.collideIndex_overtake` —
together with `HJO.Braid.BraidMonoid`'s `𝗓_i 𝗓_j = 𝗓_j 𝗓_i` (`zBlock_comm_of_overtake`).

### What the other two cases need, and why they are not here

Both remaining cases read a `ỹ`. The `z`-family carries three relations of `HJO.Braid.BraidMonoid`
— `𝗓_i T_j = T_j 𝗓_i` for `i ∉ {j, j+1}`, `𝗓_i 𝗓_j = 𝗓_j 𝗓_i`, and the `T`–`z` rule — and the
proofs below spend all three. For the `ỹ`-family only the `T`–`ỹ` rule
(`HJO.Braid.braidTrainDown_mul_braidYtilde`) is a relation; `ỹ_a T_j = T_j ỹ_a` and
`ỹ_a ỹ_b = ỹ_b ỹ_a` are **not** relations of `HJO.Braid.BraidMonoid`.

They are, however, **theorems**: `HJO.Braid.braidYtilde_comm_T` in
`HJO/Shuffle/BraidYtildeComm.lean` and `HJO.Braid.braidYtilde_comm` in
`HJO/Shuffle/BraidYtildeMellit.lean`, both in full generality in the rank. An earlier reading
of this paragraph said each rests on the centrality of a full twist; it does not. The whole
braid-group input is that the pure braid `T_{1↗k}T_{k↘1}` commutes with `T_j` for `j ≥ 2`
(`HJO.Braid.braidLoop_one_comm_T`, two train shifts), after which the commutation propagates from
index to index by the braid relation alone.

The mixed `z`–`ỹ` case needs a third thing, which is `HJO.Braid.braidYtilde_zy`:
`ỹ_1 T_1 z_1 = T_1 z_1 T_1 ỹ_1 T_1`. Mellit's own argument reduces the general-index mixed case to
that rank-`1` identity by the `T`–`z` and `T`–`ỹ` rules and the train gluings, so it is the entire
algebraic content of the case. `ytilde_z_exchange_two` below remains the rank-`2` witness that the
mixed case asks for that relation and nothing further.

What the two cases still lack is therefore **not algebra but geometry**: the rank arithmetic above
the puncture, and the `ỹ`-analogues of `zBlock_comm_of_separated` and `zBlock_comm_of_overtake`. In
the `ỹ` branch of `HJO.Braid.braidStep` the ranks *fall* rather than rise and the descending train
is on its inverted branch, so that arithmetic is mirrored rather than copied. It is not done.

## References

The lemmas `HJO.Braid.braidWord_pair_comm` and `HJO.Braid.braidWord_swap_of_lt_theta` on special
braids, using `HJO.Braid.braidStep`, `HJO.Braid.braidWord`, `HJO.Braid.specialBraid`,
`HJO.Braid.entryRank`, `HJO.Braid.moveStage`, `HJO.Braid.BraidMonoid`, `HJO.Braid.braidGenT`,
`HJO.Braid.braidYtilde`, `HJO.Braid.braidTrainDown_mul_braidGenZ`, `HJO.Braid.trainDown_far_comm`,
`HJO.Braid.IsBraidSystem.collide`.
-/

@[expose] public section

namespace HJO.Braid

open Finset

/-! ### The rank of an entry after one entry of the tuple is changed -/

/-- The rank of an entry as a sum of indicators, which is the form in which one entry of the tuple
can be split off. -/
theorem entryRank_eq_sum {α : Type*} [LinearOrder α] {k : ℕ} (w : Fin k → α) (i : Fin k) :
    entryRank w i = ∑ t : Fin k, if w t ≤ w i then 1 else 0 := by
  rw [entryRank, card_filter]

/-- **Changing the `j`-th entry moves the rank of the `i`-th by the one comparison against it.**
For `i ≠ j` the only term of `HJO.Braid.entryRank_eq_sum` that changes is the one at `j`, so the
rank before and after differ by the two indicators `w_j ≤ w_i` and `c ≤ w_i`. -/
theorem entryRank_update_of_ne {α : Type*} [LinearOrder α] {k : ℕ} (w : Fin k → α) {i j : Fin k}
    (hij : i ≠ j) (c : α) :
    entryRank (Function.update w j c) i + (if w j ≤ w i then 1 else 0)
      = entryRank w i + (if c ≤ w i then 1 else 0) := by
  have hui : Function.update w j c i = w i := Function.update_of_ne hij _ _
  rw [entryRank_eq_sum, entryRank_eq_sum, hui,
    ← Finset.sum_erase_add _ _ (Finset.mem_univ j), ← Finset.sum_erase_add _ _ (Finset.mem_univ j),
    Finset.sum_congr rfl (fun t ht => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase ht)] :
      ∀ t ∈ (Finset.univ.erase j),
        (if Function.update w j c t ≤ w i then 1 else 0) = (if w t ≤ w i then 1 else 0))]
  simp only [Function.update_self]
  omega

/-- Raising an entry does not lower its own rank. -/
theorem entryRank_le_entryRank_update {α : Type*} [LinearOrder α] {k : ℕ} (w : Fin k → α)
    (j : Fin k) {c : α} (h : w j ≤ c) :
    entryRank w j ≤ entryRank (Function.update w j c) j := by
  have hjj : Function.update w j c j = c := Function.update_self ..
  rw [entryRank, entryRank, hjj]
  refine card_le_card fun t ht => ?_
  rw [mem_filter] at ht ⊢
  refine ⟨mem_univ t, ?_⟩
  by_cases htj : t = j
  · subst htj; rw [hjj]
  · rw [Function.update_of_ne htj]; exact ht.2.trans h

/-! ### The tuple-level half -/

/-- **Moves at distinct indices commute on the position tuple.** This is the part of the exchange
that really is bookkeeping: `HJO.Braid.moveOne` updates one entry, and updates at distinct indices
commute. -/
theorem moveOne_comm (θ : ℚ) {k : ℕ} (w : Fin k → ℚ) {i j : Fin k} (hij : i ≠ j) :
    moveOne θ (moveOne θ w j) i = moveOne θ (moveOne θ w i) j := by
  unfold moveOne
  rw [Function.update_of_ne hij, Function.update_of_ne (Ne.symm hij), Function.update_comm hij]

/-- Two moves at distinct indices leave the tuple of a whole sequence unchanged when exchanged. -/
theorem moveTuple_swap (θ : ℚ) {k : ℕ} (w : Fin k → ℚ) {i j : Fin k} (hij : i ≠ j)
    (l : List (Fin k)) : moveTuple θ w (i :: j :: l) = moveTuple θ w (j :: i :: l) := by
  rw [moveTuple_cons, moveTuple_cons, moveTuple_cons, moveTuple_cons, moveOne_comm θ _ hij]

/-! ### The reduction of the list-level statement to one pair -/

/-- **Exchanging two adjacent moves reduces to the two-move word.** The suffix's moves are performed
first, so the pair is read at the tuple the suffix has advanced; the prefix's factor then sees the
same tuple in both orders by `HJO.Braid.moveOne_comm`. Nothing here is about the letter types, so
this is the reduction for all three cases of the exchange lemma. -/
theorem braidWord_swap_of_pair_comm (θ : ℚ) {k : ℕ} (w : Fin k → ℚ) {i j : Fin k} (hij : i ≠ j)
    (l₁ l₂ : List (Fin k))
    (h : braidWord θ (moveTuple θ w l₂) [i, j] = braidWord θ (moveTuple θ w l₂) [j, i]) :
    braidWord θ w (l₁ ++ i :: j :: l₂) = braidWord θ w (l₁ ++ j :: i :: l₂) := by
  have hpair : braidWord θ w (i :: j :: l₂) = braidWord θ w (j :: i :: l₂) := by
    rw [show i :: j :: l₂ = [i, j] ++ l₂ from rfl, show j :: i :: l₂ = [j, i] ++ l₂ from rfl,
      braidWord_append, braidWord_append, h]
  rw [braidWord_append, braidWord_append, hpair, moveTuple_swap θ w hij l₂]

/-! ### The index shift at three arguments -/

/-- The index shift at an argument strictly between its two indices. -/
theorem indexShift_up {p q x : ℤ} (_hx : x ≠ q) (h1 : p ≤ x) (h2 : x < q) :
    indexShift p q x = x + 1 := by
  unfold indexShift; split_ifs <;> omega

/-- The index shift at an argument strictly between its two indices, the other way round. -/
theorem indexShift_down {p q x : ℤ} (_hx : x ≠ q) (h1 : x ≤ p) (h2 : q < x) :
    indexShift p q x = x - 1 := by
  unfold indexShift; split_ifs <;> omega

/-- The index shift fixes an argument outside the range of its two indices. -/
theorem indexShift_fix {p q x : ℤ} (hx : x ≠ q) (h : ¬(p ≤ x ∧ x < q)) (h' : ¬(p ≥ x ∧ x > q)) :
    indexShift p q x = x := by
  unfold indexShift; split_ifs <;> omega

/-- **The collision indices of the overtaking configuration.** With `A ≤ B ≤ A' ≤ B'` the ascending
train `T_{B'+1↗B}` meets the descending train `T_{A'+1↘A}` in the quadruple
`(B'+1, B+1, A', A)`: only the two inner indices move, each by one. -/
theorem collideIndex_overtake {A A' B B' : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B) (hBA' : B ≤ A')
    (hA'B' : A' ≤ B') :
    collideIndex ((B' + 1 : ℕ) : ℤ) ((B : ℕ) : ℤ) ((A' + 1 : ℕ) : ℤ) ((A : ℕ) : ℤ)
      = (((B' + 1 : ℕ) : ℤ), ((B + 1 : ℕ) : ℤ), ((A' : ℕ) : ℤ), ((A : ℕ) : ℤ)) := by
  have hA' : (A : ℤ) ≤ B := by exact_mod_cast hAB
  have hB' : (B : ℤ) ≤ A' := by exact_mod_cast hBA'
  have hC' : (A' : ℤ) ≤ B' := by exact_mod_cast hA'B'
  have hA0 : (1 : ℤ) ≤ A := by exact_mod_cast hA
  have e3 : indexShift ((B' + 1 : ℕ) : ℤ) ((B : ℕ) : ℤ) ((A' + 1 : ℕ) : ℤ) = ((A' : ℕ) : ℤ) := by
    rw [indexShift_down (by push_cast; omega) (by push_cast; omega) (by push_cast; omega)]
    push_cast; ring
  rw [collideIndex_eq, e3,
    indexShift_fix (p := ((A : ℕ) : ℤ)) (q := ((A' : ℕ) : ℤ)) (x := ((B' + 1 : ℕ) : ℤ))
      (by push_cast; omega) (by push_cast; omega) (by push_cast; omega),
    indexShift_up (p := ((A : ℕ) : ℤ)) (q := ((A' + 1 : ℕ) : ℤ)) (x := ((B : ℕ) : ℤ))
      (by omega) (by omega) (by push_cast; omega),
    indexShift_fix (p := ((B' + 1 : ℕ) : ℤ)) (q := ((B : ℕ) : ℤ) + 1) (x := ((A : ℕ) : ℤ))
      (by omega) (by push_cast; omega) (by push_cast; omega)]
  norm_num

/-! ### An element against a whole train -/

section Trains

variable {M : Type*} [Monoid M] {k : ℕ} {T Tinv : ℕ → M}

/-- **An element commuting with every letter a descending train reads commutes with the train.**
The train's letters are `T_j` for `min(c,d) ≤ j ≤ max(c,d) - 1`, uninverted on one branch and
inverted on the other; `HJO.Braid.comm_inv_right` carries the commutation to the inverses. -/
theorem IsBraidSystem.comm_trainDown (h : IsBraidSystem k T Tinv) {x : M} {c d : ℕ}
    (hc : 1 ≤ c) (_hck : c ≤ k) (_hd : 1 ≤ d) (hdk : d ≤ k)
    (hx : ∀ j, min c d ≤ j → j + 1 ≤ max c d → x * T j = T j * x) :
    x * trainDown T Tinv c d = trainDown T Tinv c d * x := by
  unfold trainDown
  split_ifs with hdc
  · refine mul_prod_comm fun y hy => ?_
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
    rw [List.mem_reverse, List.mem_range'_1] at hj
    exact hx j (by omega) (by omega)
  · refine mul_prod_comm fun y hy => ?_
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
    rw [List.mem_range'_1] at hj
    exact comm_inv_right (h.mul_inv j (by omega) (by omega)) (h.inv_mul j (by omega) (by omega))
      (hx j (by omega) (by omega))

/-- The ascending form of `HJO.Braid.IsBraidSystem.comm_trainDown`. -/
theorem IsBraidSystem.comm_trainUp (h : IsBraidSystem k T Tinv) {x : M} {c d : ℕ}
    (_hc : 1 ≤ c) (hck : c ≤ k) (hd : 1 ≤ d) (_hdk : d ≤ k)
    (hx : ∀ j, min c d ≤ j → j + 1 ≤ max c d → x * T j = T j * x) :
    x * trainUp T Tinv c d = trainUp T Tinv c d * x := by
  unfold trainUp
  split_ifs with hcd
  · refine mul_prod_comm fun y hy => ?_
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
    rw [List.mem_range'_1] at hj
    exact hx j (by omega) (by omega)
  · refine mul_prod_comm fun y hy => ?_
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
    rw [List.mem_reverse, List.mem_range'_1] at hj
    exact comm_inv_right (h.mul_inv j (by omega) (by omega)) (h.inv_mul j (by omega) (by omega))
      (hx j (by omega) (by omega))

/-- **Two descending trains with separated index ranges commute**, by `HJO.Braid.trainDown_far_comm`
letter by letter. -/
theorem IsBraidSystem.trainDown_comm_trainDown (h : IsBraidSystem k T Tinv) {a b c d : ℕ}
    (ha : 1 ≤ a)
    (hak : a ≤ k) (hb : 1 ≤ b) (hbk : b ≤ k) (hc : 1 ≤ c) (hck : c ≤ k) (hd : 1 ≤ d) (hdk : d ≤ k)
    (hfar : max a b + 1 ≤ min c d ∨ max c d + 1 ≤ min a b) :
    trainDown T Tinv a b * trainDown T Tinv c d = trainDown T Tinv c d * trainDown T Tinv a b :=
  h.comm_trainDown hc hck hd hdk fun j _ _ =>
    (trainDown_far_comm h (by omega) (by omega) ha hak hb hbk (by omega)).symm

end Trains

/-- `z_a` commutes with a descending train all of whose letters are far from `a`. -/
theorem braidGenZ_comm_trainDown {k a c d : ℕ} (ha : 1 ≤ a) (hak : a ≤ k) (hc : 1 ≤ c)
    (hck : c ≤ k) (hd : 1 ≤ d) (hdk : d ≤ k) (hfar : a + 1 ≤ min c d ∨ max c d + 1 ≤ a) :
    braidGenZ k a * braidTrainDown k c d = braidTrainDown k c d * braidGenZ k a :=
  (isBraidSystem_braidGenT k).comm_trainDown hc hck hd hdk fun j _ _ =>
    braidGenZ_comm_T ha hak (by omega) (by omega) (by omega) (by omega)

/-- `z_a` commutes with an ascending train all of whose letters are far from `a`. -/
theorem braidGenZ_comm_trainUp {k a c d : ℕ} (ha : 1 ≤ a) (hak : a ≤ k) (hc : 1 ≤ c)
    (hck : c ≤ k) (hd : 1 ≤ d) (hdk : d ≤ k) (hfar : a + 1 ≤ min c d ∨ max c d + 1 ≤ a) :
    braidGenZ k a * braidTrainUp k c d = braidTrainUp k c d * braidGenZ k a :=
  (isBraidSystem_braidGenT k).comm_trainUp hc hck hd hdk fun j _ _ =>
    braidGenZ_comm_T ha hak (by omega) (by omega) (by omega) (by omega)

/-! ### The two algebraic cores of the `z`–`z` case -/

/-- **The letter blocks of two `z`-moves with separated rank ranges commute.** Each block is a
descending train followed by a `z`, and the hypothesis puts every letter of the first block at
distance at least two from every letter of the second; the two `z`'s commute by
`HJO.Braid.BraidMonoid`. -/
theorem zBlock_comm_of_separated {k a a' b b' : ℕ} (ha : 1 ≤ a) (hak : a ≤ k) (ha' : 1 ≤ a')
    (ha'k : a' ≤ k) (hb : 1 ≤ b) (hbk : b ≤ k) (hb' : 1 ≤ b') (hb'k : b' ≤ k)
    (hsep : max a a' + 1 ≤ min b b') :
    braidTrainDown k a' a * braidGenZ k a * (braidTrainDown k b' b * braidGenZ k b)
      = braidTrainDown k b' b * braidGenZ k b * (braidTrainDown k a' a * braidGenZ k a) := by
  have hsys := isBraidSystem_braidGenT k
  calc braidTrainDown k a' a * braidGenZ k a * (braidTrainDown k b' b * braidGenZ k b)
      = braidTrainDown k a' a * (braidGenZ k a * braidTrainDown k b' b) * braidGenZ k b := by
        simp only [mul_assoc]
    _ = braidTrainDown k a' a * braidTrainDown k b' b * (braidGenZ k a * braidGenZ k b) := by
        rw [braidGenZ_comm_trainDown ha hak hb' hb'k hb hbk (by omega)]; simp only [mul_assoc]
    _ = braidTrainDown k b' b * braidTrainDown k a' a * (braidGenZ k b * braidGenZ k a) := by
        rw [hsys.trainDown_comm_trainDown ha' ha'k ha hak hb' hb'k hb hbk (by omega),
          braidGenZ_comm ha hak hb hbk]
    _ = braidTrainDown k b' b * braidGenZ k b * (braidTrainDown k a' a * braidGenZ k a) := by
        simp only [mul_assoc]
        congr 1
        rw [← mul_assoc, ← braidGenZ_comm_trainDown hb hbk ha' ha'k ha hak (by omega), mul_assoc]

/-- **The overtaking configuration of the `z`–`z` case.** Here the intermediate ranks differ between
the two orders: the point at rank `A` ends at `A'`, passing the point at rank `B`, which therefore
stands at `B` in one order and at `B + 1` in the other. The identity is
`HJO.Braid.IsBraidSystem.collide` at `HJO.Braid.collideIndex_overtake`, with the `T`–`z` rule
pulling the outer `z` to the front on both sides and `𝗓_i 𝗓_j = 𝗓_j 𝗓_i` exchanging the two
`z`'s. -/
theorem zBlock_comm_of_overtake {k A A' B B' : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hAB : A ≤ B)
    (hBA' : B ≤ A') (hA'B' : A' ≤ B') (hA'k : A' + 1 ≤ k) (hB'k : B' + 1 ≤ k) :
    braidTrainDown k A' A * braidGenZ k A
        * (braidTrainDown k (B' + 1) (B + 1) * braidGenZ k (B + 1))
      = braidTrainDown k (B' + 1) B * braidGenZ k B
        * (braidTrainDown k (A' + 1) A * braidGenZ k A) := by
  have hsys := isBraidSystem_braidGenT k
  have hcol := hsys.collide (a := B' + 1) (b := B) (c := A' + 1) (d := A) (a' := B' + 1)
    (b' := B + 1) (c' := A') (d' := A) (by omega) (by omega) hB (by omega) (by omega) (by omega)
    hA (by omega) (by omega) (collideIndex_overtake hA hAB hBA' hA'B')
  rw [braidTrainDown_mul_braidGenZ (k := k) (a := B' + 1) (b := B + 1) (by omega) (by omega)
      (by omega) (by omega),
    braidTrainDown_mul_braidGenZ (k := k) (a := B' + 1) (b := B) (by omega) (by omega) hB
      (by omega)]
  calc braidTrainDown k A' A * braidGenZ k A
          * (braidGenZ k (B' + 1) * braidTrainUp k (B' + 1) (B + 1))
      = braidTrainDown k A' A * (braidGenZ k A * braidGenZ k (B' + 1))
          * braidTrainUp k (B' + 1) (B + 1) := by simp only [mul_assoc]
    _ = braidTrainDown k A' A * braidGenZ k (B' + 1) * braidGenZ k A
          * braidTrainUp k (B' + 1) (B + 1) := by
        rw [braidGenZ_comm hA (by omega) (by omega) (by omega)]; simp only [mul_assoc]
    _ = braidGenZ k (B' + 1) * braidTrainDown k A' A
          * (braidGenZ k A * braidTrainUp k (B' + 1) (B + 1)) := by
        rw [← braidGenZ_comm_trainDown (a := B' + 1) (c := A') (d := A) (by omega) (by omega)
          (by omega) (by omega) hA (by omega) (by omega)]
        simp only [mul_assoc]
    _ = braidGenZ k (B' + 1) * (braidTrainDown k A' A * braidTrainUp k (B' + 1) (B + 1))
          * braidGenZ k A := by
        rw [braidGenZ_comm_trainUp (a := A) (c := B' + 1) (d := B + 1) hA (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega)]
        simp only [mul_assoc]
    _ = braidGenZ k (B' + 1) * (braidTrainUp k (B' + 1) B * braidTrainDown k (A' + 1) A)
          * braidGenZ k A := by rw [hcol]
    _ = braidGenZ k (B' + 1) * braidTrainUp k (B' + 1) B
          * (braidTrainDown k (A' + 1) A * braidGenZ k A) := by simp only [mul_assoc]

/-! ### The exchange lemma for two points below the puncture -/

/-- **The moves of two distinct points below the puncture may be exchanged**, in the ordered case:
if `w_i < w_j < θ` then the two-move words `(i, j)` and `(j, i)` name the same braid.

Both points contribute a `z`, and both values rise by `1 - θ`, so the four numbers in play are
ordered `w_i < w_j`, `w_i < nx(w_i)`, `w_j < nx(w_j)`, `nx(w_i) < nx(w_j)` and `w_i < nx(w_j)`. The
one comparison left open is `nx(w_i)` against `w_j`, and it is the case division: below it the two
runs do not interleave and the content is `HJO.Braid.zBlock_comm_of_separated`; above it the first
point overtakes the second and the content is `HJO.Braid.zBlock_comm_of_overtake`. -/
theorem braidWord_pair_comm_of_lt_theta {θ : ℚ} {k : ℕ} {w : Fin k → ℚ} {i j : Fin k}
    (hij : i ≠ j) (hθ1 : θ < 1) (hxθ : w i < θ) (hyθ : w j < θ) (hxy : w i < w j)
    (hne : nextCrossing θ (w i) ≠ w j) :
    braidWord θ w [i, j] = braidWord θ w [j, i] := by
  have hx' : nextCrossing θ (w i) = w i + 1 - θ := by
    simp only [nextCrossing, not_lt.2 hxθ.le, ite_false]
  have hy' : nextCrossing θ (w j) = w j + 1 - θ := by
    simp only [nextCrossing, not_lt.2 hyθ.le, ite_false]
  have hyy' : w j < nextCrossing θ (w j) := by rw [hy']; linarith
  have hx'y' : nextCrossing θ (w i) < nextCrossing θ (w j) := by rw [hx', hy']; linarith
  have hxy' : w i < nextCrossing θ (w j) := hxy.trans hyy'
  have hui : moveOne θ w i i = nextCrossing θ (w i) := moveOne_self ..
  have huj : moveOne θ w i j = w j := moveOne_of_ne θ w (Ne.symm hij)
  have hvi : moveOne θ w j i = w i := moveOne_of_ne θ w hij
  have hvj : moveOne θ w j j = nextCrossing θ (w j) := moveOne_self ..
  have hfin : moveOne θ (moveOne θ w j) i = moveOne θ (moveOne θ w i) j := moveOne_comm θ w hij
  have hfi : moveOne θ (moveOne θ w j) i i = nextCrossing θ (w i) := by rw [moveOne_self, hvi]
  have hfj : moveOne θ (moveOne θ w j) i j = nextCrossing θ (w j) := by
    rw [moveOne_of_ne θ _ (Ne.symm hij), hvj]
  -- The four rank equations: one comparison against the other point each time.
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
  have i1 : ¬(w j ≤ w i) := by linarith
  have i2 : ¬(nextCrossing θ (w j) ≤ w i) := by linarith
  have i4 : ¬(nextCrossing θ (w j) ≤ nextCrossing θ (w i)) := by linarith
  simp only [i1, i2, i4, hxy.le, hxy'.le, hx'y'.le, ite_true, ite_false, add_zero] at E1 E2 E3 E4
  have hE4 : entryRank (moveOne θ (moveOne θ w j) i) j = entryRank (moveOne θ w j) j := by omega
  -- The braid of each of the four steps.
  rw [braidWord_pair, braidWord_pair,
    braidStep_of_lt (show moveOne θ w j i < θ by rw [hvi]; exact hxθ),
    braidStep_of_lt hyθ, braidStep_of_lt (show moveOne θ w i j < θ by rw [huj]; exact hyθ),
    braidStep_of_lt hxθ, ← hfin, E1, hE4]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- The runs do not interleave.
    have hE2 : entryRank (moveOne θ w i) j = entryRank w j := by
      simp only [hlt.le, ite_true] at E2
      omega
    have hE3 : entryRank (moveOne θ (moveOne θ w j) i) i = entryRank (moveOne θ w i) i := by
      simp only [show ¬(w j ≤ nextCrossing θ (w i)) from by linarith, ite_false, add_zero] at E3
      omega
    rw [hE2, hE3]
    refine zBlock_comm_of_separated (entryRank_pos _ _) (entryRank_le _ _) (entryRank_pos _ _)
      (entryRank_le _ _) (entryRank_pos _ _) (entryRank_le _ _) (entryRank_pos _ _)
      (entryRank_le _ _) ?_
    have c1 : entryRank w i < entryRank w j := (entryRank_lt_entryRank_iff w i j).2 hxy
    have c2 : entryRank (moveOne θ w i) i < entryRank w j := by
      rw [← hE2]
      exact (entryRank_lt_entryRank_iff _ i j).2 (by rw [hui, huj]; exact hlt)
    have c3 : entryRank w j ≤ entryRank (moveOne θ w j) j :=
      entryRank_le_entryRank_update w j hyy'.le
    omega
  · -- The first point overtakes the second.
    have hE2 : entryRank (moveOne θ w i) j + 1 = entryRank w j := by
      simp only [show ¬(nextCrossing θ (w i) ≤ w j) from by linarith, ite_false, add_zero] at E2
      omega
    have hE3 : entryRank (moveOne θ (moveOne θ w j) i) i + 1 = entryRank (moveOne θ w i) i := by
      simp only [hgt.le, ite_true] at E3
      omega
    obtain ⟨B', hB'⟩ : ∃ B', entryRank (moveOne θ w j) j = B' + 1 :=
      ⟨entryRank (moveOne θ w j) j - 1, by have := entryRank_pos (moveOne θ w j) j; omega⟩
    rw [← hE2, ← hE3, hB']
    refine zBlock_comm_of_overtake (entryRank_pos _ _) (entryRank_pos _ _) ?_ ?_ ?_ ?_ ?_
    · have := (entryRank_lt_entryRank_iff w i j).2 hxy
      omega
    · have := (entryRank_lt_entryRank_iff (moveOne θ w i) j i).2 (by rw [hui, huj]; exact hgt)
      omega
    · have := (entryRank_lt_entryRank_iff (moveOne θ (moveOne θ w j) i) i j).2
        (by rw [hfi, hfj]; exact hx'y')
      omega
    · rw [hE3]; exact entryRank_le _ _
    · rw [← hB']; exact entryRank_le _ _

/-- **The moves of two distinct points below the puncture may be exchanged.** The ordered form
`HJO.Braid.braidWord_pair_comm_of_lt_theta` read without a choice of which entry is the smaller;
the conclusion is symmetric in `i` and `j`, so the two orderings are the same statement. -/
theorem braidWord_pair_comm_of_lt_theta' {θ : ℚ} {k : ℕ} {w : Fin k → ℚ} {i j : Fin k}
    (hij : i ≠ j) (hθ1 : θ < 1) (hxθ : w i < θ) (hyθ : w j < θ) (hne0 : w i ≠ w j)
    (hne1 : nextCrossing θ (w i) ≠ w j) (hne2 : w i ≠ nextCrossing θ (w j)) :
    braidWord θ w [i, j] = braidWord θ w [j, i] := by
  rcases lt_or_gt_of_ne hne0 with h | h
  · exact braidWord_pair_comm_of_lt_theta hij hθ1 hxθ hyθ h hne1
  · exact (braidWord_pair_comm_of_lt_theta (Ne.symm hij) hθ1 hyθ hxθ h (Ne.symm hne2)).symm

/-- **Exchanging two adjacent moves of distinct points both below the
puncture leaves the braid of the sequence unchanged.** The moves of the suffix are performed first,
so the hypotheses are read at the tuple the suffix has advanced. -/
@[hjo "lem_braid_move_comm_below"]
theorem braidWord_swap_of_lt_theta {θ : ℚ} {k : ℕ} (w : Fin k → ℚ) {i j : Fin k} (hij : i ≠ j)
    (l₁ l₂ : List (Fin k)) (hθ1 : θ < 1)
    (hxθ : moveTuple θ w l₂ i < θ) (hyθ : moveTuple θ w l₂ j < θ)
    (hne0 : moveTuple θ w l₂ i ≠ moveTuple θ w l₂ j)
    (hne1 : nextCrossing θ (moveTuple θ w l₂ i) ≠ moveTuple θ w l₂ j)
    (hne2 : moveTuple θ w l₂ i ≠ nextCrossing θ (moveTuple θ w l₂ j)) :
    braidWord θ w (l₁ ++ i :: j :: l₂) = braidWord θ w (l₁ ++ j :: i :: l₂) :=
  braidWord_swap_of_pair_comm θ w hij l₁ l₂
    (braidWord_pair_comm_of_lt_theta' hij hθ1 hxθ hyθ hne0 hne1 hne2)

/-! ### The mixed case is Mellit's one mixed relation -/

/-- **The kernel witness for the mixed case.** `T_{1↘2} ỹ_2 z_1 = T_{2↘1} z_1 ỹ_2` in
`𝔹_2^+(𝕋_0)`, which is the identity the exchange lemma asks for at rank `2` when a point below the
puncture overtakes a point above it: the lower point starts at rank `1` and ends at rank `2`, so its
block is `T_{2↘1} z_1`, while the upper point starts at rank `2` and ends at rank `1`, so its block
is `T_{1↘2} ỹ_2`, and the two orders put the two blocks the two ways round.

It is exactly `HJO.Braid.BraidMonoid`'s one mixed relation `𝗓_1 T_1 𝗒_1 T̄_1 = T̄_1 𝗒_1 T̄_1 𝗓_1`
and nothing else: at rank `2`, `ỹ_2 = T_1 𝗒_1 T̄_1`, so the relation reads
`z_1 ỹ_2 = T̄_1 T̄_1 ỹ_2 z_1`, and one cancellation on each side turns both into `𝗒_1 T̄_1 z_1`.

So the mixed case of the exchange lemma is true, and what it is owed is a general-index form of that
relation. -/
theorem ytilde_z_exchange_two :
    braidTrainDown 2 1 2 * braidYtilde 2 2 * braidGenZ 2 1
      = braidTrainDown 2 2 1 * braidGenZ 2 1 * braidYtilde 2 2 := by
  have hT : braidGenT 2 1 * braidGenTinv 2 1 = 1 := braidGenT_mul_inv le_rfl le_rfl
  have hT' : braidGenTinv 2 1 * braidGenT 2 1 = 1 := braidGenT_inv_mul le_rfl le_rfl
  have hu12 : braidTrainUp 2 1 2 = braidGenT 2 1 := by
    simp [braidTrainUp, trainUp, ascendingWord]
  have hd2 : braidTrainDown 2 2 1 = braidGenT 2 1 := by
    simp [braidTrainDown, trainDown, descendingWord]
  have hd1 : braidTrainDown 2 1 2 = braidGenTinv 2 1 := by
    simp [braidTrainDown, trainDown, ascendingWord]
  have hy2 : braidGenY 2 2 = braidGenTinv 2 1 * braidGenY 2 1 * braidGenTinv 2 1 := by
    simpa using braidGenY_succ 2 0
  have hy : braidYtilde 2 2 = braidGenT 2 1 * braidGenY 2 1 * braidGenTinv 2 1 := by
    rw [braidYtilde, hd2, hu12, hy2, braidTrainUp_self, mul_one]
    simp only [mul_assoc]
    rw [← mul_assoc (braidGenT 2 1) (braidGenTinv 2 1), hT, one_mul]
  have hzy := braidGen_zy (k := 2) le_rfl
  have hL : braidGenTinv 2 1 * (braidGenT 2 1 * braidGenY 2 1 * braidGenTinv 2 1) * braidGenZ 2 1
      = braidGenY 2 1 * (braidGenTinv 2 1 * braidGenZ 2 1) := by
    simp only [mul_assoc]
    rw [← mul_assoc (braidGenTinv 2 1) (braidGenT 2 1), hT', one_mul]
  have hR : braidGenT 2 1 * braidGenZ 2 1 * (braidGenT 2 1 * braidGenY 2 1 * braidGenTinv 2 1)
      = braidGenY 2 1 * (braidGenTinv 2 1 * braidGenZ 2 1) := by
    rw [show braidGenT 2 1 * braidGenZ 2 1 * (braidGenT 2 1 * braidGenY 2 1 * braidGenTinv 2 1)
        = braidGenT 2 1 * (braidGenZ 2 1 * braidGenT 2 1 * braidGenY 2 1 * braidGenTinv 2 1) by
      simp only [mul_assoc], hzy]
    simp only [mul_assoc]
    rw [← mul_assoc (braidGenT 2 1) (braidGenTinv 2 1), hT, one_mul]
  rw [hd1, hd2, hy, hL, hR]

end HJO.Braid
