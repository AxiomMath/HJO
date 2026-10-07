/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidClosedForms
public meta import HJO.Attr

/-! # Moving one generator through a descending train

`HJO/Shuffle/BraidTrainRelations.lean` moves a generator through an *ascending* train
(`HJO.Braid.trainUp_mul_gen`) and, one letter at a time, through a whole short ascending train
(`HJO.Braid.trainUp_overtake`). This file is the four rules for a *descending* train, which are what
the collision lemma of Mellit's Section 5 splits into:

* the generator shifts, its index moving by one, when it is strictly inside the train's range
  (`HJO.Braid.IsBraidSystem.gen_shift_pos`, `HJO.Braid.IsBraidSystem.gen_shift_neg`);
* the train grows by one letter and spits out a two-letter ascending train, when the generator sits
  exactly at the boundary (`HJO.Braid.IsBraidSystem.gen_split_pos`,
  `HJO.Braid.IsBraidSystem.gen_split_neg`).

"Positive" and "negative" are the two branches of `HJO.Braid.trainDown`: `T_{c↘d}` is a word in the
uninverted letters when `d < c` and in the inverted ones when `c < d`, and the two branches move a
generator in opposite directions.

## Main results

* `HJO.Braid.IsBraidSystem.gen_shift_pos`, `HJO.Braid.IsBraidSystem.gen_shift_pos_inv` —
  the two signs of `T_j^ε T_{c↘d} = T_{c↘d} T_{j+1}^ε`.
* `HJO.Braid.IsBraidSystem.gen_shift_neg`, `HJO.Braid.IsBraidSystem.gen_shift_neg_inv` —
  the two signs of `T_j^ε T_{c↘d} = T_{c↘d} T_{j-1}^ε`.
* `HJO.Braid.IsBraidSystem.gen_split_pos`, `HJO.Braid.IsBraidSystem.gen_split_pos_inv` —
  the two signs of
  `T_{d-1}^ε T_{c↘d} = T_{c↘d+ε} T_{d-ε↗d+ε}`.
* `HJO.Braid.IsBraidSystem.gen_split_neg`, `HJO.Braid.IsBraidSystem.gen_split_neg_inv` —
  the two signs of `T_d^ε T_{c↘d} = T_{c↘d+ε} T_{d-ε↗d+ε}`.

## Implementation notes

### The orientation is checked, not assumed

Each of the four rules moves an index in a direction that the mirror rule moves the other way, and
swapping two of them produces a statement that is false rather than ill-typed — the same hazard
`HJO.Braid.braidGenZ_four` and `HJO.Braid.braidGenY_four` exist for. So each rule is followed by a
check at a small index with every train written out as a product of letters:
`HJO.Braid.IsBraidSystem.gen_shift_pos_four`, `HJO.Braid.IsBraidSystem.gen_shift_neg_three`,
`HJO.Braid.IsBraidSystem.gen_split_pos_three`, `HJO.Braid.IsBraidSystem.gen_split_neg_three`. For
the two split rules the check is stated at `ε = -1`, because at `ε = 1` both sides of the identity
are the same word and the check would be vacuous.

### The index `j` is shifted by one in two of the four

`HJO.Braid.IsBraidSystem.gen_shift_neg` reads `T_j^ε T_{c↘d} = T_{c↘d} T_{j-1}^ε` for
`c + 1 ≤ j ≤ d - 1`, and
`HJO.Braid.IsBraidSystem.gen_split_pos`/`HJO.Braid.IsBraidSystem.gen_split_neg` read `T_{d-1}^ε` and
`T_{c↘d}` with `d ≥ 2`. Here the moving generator of the first is `T_{j+1}` and the trains of the
other two are written at `d = e + 1`, so that no index below is a truncated subtraction on `ℕ`. The
substitution is the only change; `1 ≤ e` and `c ≤ j` are the `d ≥ 2` and `c + 1 ≤ j` read at the
shifted index.

The side conditions `d + ε ≤ k` on the two split rules are not hypotheses here: in both
the train's own bounds already give them. For `HJO.Braid.IsBraidSystem.gen_split_pos`, `d < c ≤ k`
gives `d + 1 ≤ k`; for `HJO.Braid.IsBraidSystem.gen_split_neg`, `d ≤ k - 1` is the hypothesis
`e + 2 ≤ k`, and `d - 1 ≤ k` follows.

## References

Transcribing A.
Mellit, *Toric braids and `(m, n)`-parking functions*, Section 5.
-/

@[expose] public section

namespace HJO.Braid

variable {M : Type*} [Monoid M]

/-! ### Two monoid facts -/

/-- If `x` commutes with `y` and `x'` is a two-sided inverse of `x`, then `x'` commutes with `y`.
The mirror of `HJO.Braid.comm_inv_right`, inverting the *left* factor, which is what carries far
commutation from `T_i` to `T_i^{-1}`. -/
theorem comm_inv_left {x x' y : M} (hx : x * x' = 1) (hx' : x' * x = 1) (h : x * y = y * x) :
    x' * y = y * x' :=
  calc x' * y = x' * (y * x * x') := by rw [mul_assoc y x x', hx, mul_one]
    _ = x' * (x * y * x') := by rw [h]
    _ = x' * x * (y * x') := by simp only [mul_assoc]
    _ = y * x' := by rw [hx', one_mul]

/-- **Moving a letter rightwards through a three-block word, changing it as it passes the middle
block.** The shape all four rules below share: the letter commutes with the outer blocks and the
middle block converts it. -/
theorem mul_three_shift {x x' X W Y : M} (hX : x * X = X * x) (hW : x * W = W * x')
    (hY : x' * Y = Y * x') : x * (X * (W * Y)) = X * (W * Y) * x' :=
  calc x * (X * (W * Y)) = x * X * (W * Y) := (mul_assoc _ _ _).symm
    _ = X * x * (W * Y) := by rw [hX]
    _ = X * (x * W * Y) := by simp only [mul_assoc]
    _ = X * (W * x' * Y) := by rw [hW]
    _ = X * (W * (Y * x')) := by rw [mul_assoc, hY]
    _ = X * (W * Y) * x' := by simp only [mul_assoc]

/-! ### The two-letter trains -/

/-- `T_{a↗a+2} = T_a T_{a+1}`, the first branch of `HJO.Braid.trainUp` at a range of length two. -/
theorem trainUp_self_add_two (T Tinv : ℕ → M) (a : ℕ) :
    trainUp T Tinv a (a + 2) = T a * T (a + 1) := by
  simp [trainUp, ascendingWord, List.range']

/-- `T_{a+2↗a} = T_{a+1}^{-1} T_a^{-1}`, the second branch of `HJO.Braid.trainUp` at a range of
length two: the inverted letters in *decreasing* order of index. -/
theorem trainUp_add_two_self (T Tinv : ℕ → M) (a : ℕ) :
    trainUp T Tinv (a + 2) a = Tinv (a + 1) * Tinv a := by
  simp [trainUp, descendingWord, List.range']

/-- `T_{a+2↘a} = T_{a+1} T_a`, the first branch of `HJO.Braid.trainDown` at a range of length
two. -/
theorem trainDown_add_two_self (T Tinv : ℕ → M) (a : ℕ) :
    trainDown T Tinv (a + 2) a = T (a + 1) * T a := by
  simp [trainDown, descendingWord, List.range']

/-- `T_{a↘a+2} = T_a^{-1} T_{a+1}^{-1}`, the second branch of `HJO.Braid.trainDown` at a range of
length two: the inverted letters in *increasing* order of index. -/
theorem trainDown_self_add_two (T Tinv : ℕ → M) (a : ℕ) :
    trainDown T Tinv a (a + 2) = Tinv a * Tinv (a + 1) := by
  simp [trainDown, ascendingWord, List.range']

variable {k : ℕ} {T Tinv : ℕ → M}

/-- **A far inverted generator commutes with a descending train**, `HJO.Braid.trainDown_far_comm`
for `T_i^{-1}`: the "conjugating that identity by `T_i` shows `T_i^{-1}` commutes with it as
well, so `T_i^ε` does". -/
theorem trainDown_far_comm_inv (h : IsBraidSystem k T Tinv) {a b i : ℕ} (hi : 1 ≤ i)
    (hik : i + 1 ≤ k) (ha : 1 ≤ a) (hak : a ≤ k) (hb : 1 ≤ b) (hbk : b ≤ k)
    (hfar : i + 2 ≤ min a b ∨ max a b + 1 ≤ i) :
    Tinv i * trainDown T Tinv a b = trainDown T Tinv a b * Tinv i :=
  comm_inv_left (h.mul_inv i hi hik) (h.inv_mul i hi hik)
    (trainDown_far_comm h hi hik ha hak hb hbk hfar)

/-! ### A generator shifts up through a positive descending train -/

section ShiftPos

variable {c d j : ℕ}

/-- The factorisation `T_{c↘d} = T_{c↘j+2} T_{j+2↘j} T_{j↘d}`, with the middle train
written out as the two letters `T_{j+1} T_j`. -/
private theorem trainDown_split_pos (h : IsBraidSystem k T Tinv) (hd : 1 ≤ d) (hdj : d ≤ j)
    (hjc : j + 2 ≤ c) (hck : c ≤ k) :
    trainDown T Tinv c d
      = trainDown T Tinv c (j + 2) * (T (j + 1) * T j * trainDown T Tinv j d) := by
  have hinner : trainDown T Tinv (j + 2) j * trainDown T Tinv j d = trainDown T Tinv (j + 2) d :=
    trainDown_mul_trainDown h (by omega) (by omega) (by omega) (by omega) hd (by omega)
  have houter :
      trainDown T Tinv c (j + 2) * trainDown T Tinv (j + 2) d = trainDown T Tinv c d :=
    trainDown_mul_trainDown h (by omega) hck (by omega) (by omega) hd (by omega)
  rw [← houter, ← hinner, trainDown_add_two_self]

/-- **A generator shifts up through a positive descending train**, which is
`HJO.Braid.IsBraidSystem.gen_shift_pos` at `ε = 1`: for `d ≤ j ≤ c - 2` with `1 ≤ d < c ≤ k`,
`T_j T_{c↘d} = T_{c↘d} T_{j+1}`.

The train splits as `T_{c↘j+2} (T_{j+1}T_j) T_{j↘d}`; `T_j` commutes with the first block and
`T_{j+1}` with the third by `HJO.Braid.trainDown_far_comm`, and the middle block is the braid
relation `T_j(T_{j+1}T_j) = (T_{j+1}T_j)T_{j+1}`. -/
@[hjo "lem_train_gen_shift_pos"]
theorem IsBraidSystem.gen_shift_pos (h : IsBraidSystem k T Tinv) (hd : 1 ≤ d) (hdj : d ≤ j)
    (hjc : j + 2 ≤ c) (hck : c ≤ k) :
    T j * trainDown T Tinv c d = trainDown T Tinv c d * T (j + 1) := by
  have hj : 1 ≤ j := le_trans hd hdj
  have hjk : j + 2 ≤ k := le_trans hjc hck
  rw [trainDown_split_pos h hd hdj hjc hck]
  refine mul_three_shift (x := T j) (x' := T (j + 1))
    (trainDown_far_comm h hj (by omega) (by omega) hck (by omega) (by omega)
      (Or.inl (by omega))) ?_
    (trainDown_far_comm h (by omega) (by omega) hj (by omega) hd (by omega) (Or.inr (by omega)))
  rw [← mul_assoc]
  exact h.braid_pair_pos hj hjk

/-- **A generator shifts up through a positive descending train**, at `ε = -1`:
`T_j^{-1} T_{c↘d} = T_{c↘d} T_{j+1}^{-1}`. The same three blocks, with
`HJO.Braid.IsBraidSystem.braid_pair_neg` in the middle. -/
@[hjo "lem_train_gen_shift_pos"]
theorem IsBraidSystem.gen_shift_pos_inv (h : IsBraidSystem k T Tinv) (hd : 1 ≤ d) (hdj : d ≤ j)
    (hjc : j + 2 ≤ c) (hck : c ≤ k) :
    Tinv j * trainDown T Tinv c d = trainDown T Tinv c d * Tinv (j + 1) := by
  have hj : 1 ≤ j := le_trans hd hdj
  have hjk : j + 2 ≤ k := le_trans hjc hck
  rw [trainDown_split_pos h hd hdj hjc hck]
  refine mul_three_shift (x := Tinv j) (x' := Tinv (j + 1))
    (trainDown_far_comm_inv h hj (by omega) (by omega) hck (by omega) (by omega)
      (Or.inl (by omega))) ?_
    (trainDown_far_comm_inv h (by omega) (by omega) hj (by omega) hd (by omega)
      (Or.inr (by omega)))
  rw [← mul_assoc]
  exact h.braid_pair_neg hj hjk

end ShiftPos

/-- **The orientation of `HJO.Braid.IsBraidSystem.gen_shift_pos`**, at `c = 4`, `d = 1`, `j = 1` and
rank `4` with the train written out: `T_1 (T_3T_2T_1) = (T_3T_2T_1) T_2`. The generator's index
goes *up*, and it does so on the *right* of the train. -/
theorem IsBraidSystem.gen_shift_pos_four (h : IsBraidSystem 4 T Tinv) :
    T 1 * (T 3 * T 2 * T 1) = T 3 * T 2 * T 1 * T 2 := by
  have hgen := h.gen_shift_pos (c := 4) (d := 1) (j := 1) le_rfl le_rfl (by omega) le_rfl
  rwa [trainDown_four_one] at hgen

/-! ### A generator shifts down through a negative descending train -/

section ShiftNeg

variable {c d j : ℕ}

/-- The factorisation `T_{c↘d} = T_{c↘j} T_{j↘j+2} T_{j+2↘d}` at the shifted index,
with the middle train written out as the two inverted letters `T_j^{-1} T_{j+1}^{-1}`. -/
private theorem trainDown_split_neg (h : IsBraidSystem k T Tinv) (hc : 1 ≤ c) (hcj : c ≤ j)
    (hjd : j + 2 ≤ d) (hdk : d ≤ k) :
    trainDown T Tinv c d
      = trainDown T Tinv c j * (Tinv j * Tinv (j + 1) * trainDown T Tinv (j + 2) d) := by
  have hinner : trainDown T Tinv j (j + 2) * trainDown T Tinv (j + 2) d = trainDown T Tinv j d :=
    trainDown_mul_trainDown h (by omega) (by omega) (by omega) (by omega) (by omega) hdk
  have houter : trainDown T Tinv c j * trainDown T Tinv j d = trainDown T Tinv c d :=
    trainDown_mul_trainDown h hc (by omega) (by omega) (by omega) (by omega) hdk
  rw [← houter, ← hinner, trainDown_self_add_two]

/-- **A generator shifts down through a negative descending train**, which is
`HJO.Braid.IsBraidSystem.gen_shift_neg` at `ε = 1`: for `c ≤ j` and `j + 2 ≤ d ≤ k` with `1 ≤ c`,
`T_{j+1} T_{c↘d} = T_{c↘d} T_j`.

The moving letter is `T_j` for `c + 1 ≤ j ≤ d - 1`; here it is `T_{j+1}`, which is the
same statement with no truncated subtraction. The train splits as
`T_{c↘j}(T_j^{-1}T_{j+1}^{-1})T_{j+2↘d}`, and the middle block is
`HJO.Braid.IsBraidSystem.braid_mirror_pos` for the inverted braid system of
`HJO.Braid.IsBraidSystem.inverses`. -/
@[hjo "lem_train_gen_shift_neg"]
theorem IsBraidSystem.gen_shift_neg (h : IsBraidSystem k T Tinv) (hc : 1 ≤ c) (hcj : c ≤ j)
    (hjd : j + 2 ≤ d) (hdk : d ≤ k) :
    T (j + 1) * trainDown T Tinv c d = trainDown T Tinv c d * T j := by
  have hj : 1 ≤ j := le_trans hc hcj
  have hjk : j + 2 ≤ k := le_trans hjd hdk
  rw [trainDown_split_neg h hc hcj hjd hdk]
  refine mul_three_shift (x := T (j + 1)) (x' := T j)
    (trainDown_far_comm h (by omega) (by omega) hc (by omega) hj (by omega)
      (Or.inr (by omega))) ?_
    (trainDown_far_comm h hj (by omega) (by omega) (by omega) (by omega) hdk (Or.inl (by omega)))
  rw [← mul_assoc]
  exact h.inverses.braid_mirror_neg hj hjk

/-- **A generator shifts down through a negative descending train**, at `ε = -1`:
`T_{j+1}^{-1} T_{c↘d} = T_{c↘d} T_j^{-1}`, the middle block now being
`HJO.Braid.IsBraidSystem.braid_mirror_pos` for the inverted braid system. -/
@[hjo "lem_train_gen_shift_neg"]
theorem IsBraidSystem.gen_shift_neg_inv (h : IsBraidSystem k T Tinv) (hc : 1 ≤ c) (hcj : c ≤ j)
    (hjd : j + 2 ≤ d) (hdk : d ≤ k) :
    Tinv (j + 1) * trainDown T Tinv c d = trainDown T Tinv c d * Tinv j := by
  have hj : 1 ≤ j := le_trans hc hcj
  have hjk : j + 2 ≤ k := le_trans hjd hdk
  rw [trainDown_split_neg h hc hcj hjd hdk]
  refine mul_three_shift (x := Tinv (j + 1)) (x' := Tinv j)
    (trainDown_far_comm_inv h (by omega) (by omega) hc (by omega) hj (by omega)
      (Or.inr (by omega))) ?_
    (trainDown_far_comm_inv h hj (by omega) (by omega) (by omega) (by omega) hdk
      (Or.inl (by omega)))
  rw [← mul_assoc]
  exact h.inverses.braid_mirror_pos hj hjk

end ShiftNeg

/-- **The orientation of `HJO.Braid.IsBraidSystem.gen_shift_neg`**, at `c = 1`, `d = 3`, `j = 1` and
rank `3` with the train written out: `T_2 (T_1^{-1}T_2^{-1}) = (T_1^{-1}T_2^{-1}) T_1`. Against a
negative train the generator's index goes *down*. -/
theorem IsBraidSystem.gen_shift_neg_three (h : IsBraidSystem 3 T Tinv) :
    T 2 * (Tinv 1 * Tinv 2) = Tinv 1 * Tinv 2 * T 1 := by
  have hgen := h.gen_shift_neg (c := 1) (d := 3) (j := 1) le_rfl le_rfl (by omega) le_rfl
  rwa [show trainDown T Tinv 1 3 = Tinv 1 * Tinv 2 from trainDown_self_add_two T Tinv 1] at hgen

/-! ### Splitting a positive descending train at its tail -/

section SplitPos

variable {c e : ℕ}

/-- **Splitting a positive descending train at its tail**, which is
`HJO.Braid.IsBraidSystem.gen_split_pos` at `ε = 1`, written at `d = e + 1`:
`T_e T_{c↘e+1} = T_{c↘e+2} T_{e↗e+2}`.

No braid relation is used at this sign: the train splits as `T_{c↘e+2}T_{e+1}`, the letter `T_e`
commutes past the first factor by `HJO.Braid.trainDown_far_comm`, and `T_eT_{e+1}` is the ascending
train `T_{e↗e+2}` of `HJO.Braid.trainUp`. -/
@[hjo "lem_train_gen_split_pos"]
theorem IsBraidSystem.gen_split_pos (h : IsBraidSystem k T Tinv) (he : 1 ≤ e) (hec : e + 2 ≤ c)
    (hck : c ≤ k) :
    T e * trainDown T Tinv c (e + 1) = trainDown T Tinv c (e + 2) * trainUp T Tinv e (e + 2) := by
  have hsplit : trainDown T Tinv c (e + 2) * T (e + 1) = trainDown T Tinv c (e + 1) := by
    have hglue := trainDown_mul_trainDown (T := T) (Tinv := Tinv) h (a := c) (b := e + 2)
      (c := e + 1) (by omega) hck (by omega) (by omega) (by omega) (by omega)
    rwa [trainDown_succ_self] at hglue
  have hcomm : T e * trainDown T Tinv c (e + 2) = trainDown T Tinv c (e + 2) * T e :=
    trainDown_far_comm h he (by omega) (by omega) hck (by omega) (by omega) (Or.inl (by omega))
  rw [← hsplit, trainUp_self_add_two, ← mul_assoc, hcomm]
  simp only [mul_assoc]

/-- **Splitting a positive descending train at its tail**, at `ε = -1`:
`T_e^{-1} T_{c↘e+1} = T_{c↘e} T_{e+2↗e}`.

Here the train on the right is one letter *longer* than the one on the left, and the ascending
train it spits out is the inverted pair `T_{e+1}^{-1}T_e^{-1}`. What is left after the two trains
are written out is `T_e^{-1}T_{e+1} = T_{e+1}T_eT_{e+1}^{-1}T_e^{-1}`, which is
`HJO.Braid.IsBraidSystem.braid_pair_neg` with one cancellation. -/
@[hjo "lem_train_gen_split_pos"]
theorem IsBraidSystem.gen_split_pos_inv (h : IsBraidSystem k T Tinv) (he : 1 ≤ e)
    (hec : e + 2 ≤ c) (hck : c ≤ k) :
    Tinv e * trainDown T Tinv c (e + 1)
      = trainDown T Tinv c e * trainUp T Tinv (e + 2) e := by
  have hsplit1 : trainDown T Tinv c (e + 2) * T (e + 1) = trainDown T Tinv c (e + 1) := by
    have hglue := trainDown_mul_trainDown (T := T) (Tinv := Tinv) h (a := c) (b := e + 2)
      (c := e + 1) (by omega) hck (by omega) (by omega) (by omega) (by omega)
    rwa [trainDown_succ_self] at hglue
  have hsplit2 : trainDown T Tinv c (e + 2) * (T (e + 1) * T e) = trainDown T Tinv c e := by
    have hglue := trainDown_mul_trainDown (T := T) (Tinv := Tinv) h (a := c) (b := e + 2)
      (c := e) (by omega) hck (by omega) (by omega) he (by omega)
    rwa [trainDown_add_two_self] at hglue
  have hcomm : Tinv e * trainDown T Tinv c (e + 2) = trainDown T Tinv c (e + 2) * Tinv e :=
    trainDown_far_comm_inv h he (by omega) (by omega) hck (by omega) (by omega)
      (Or.inl (by omega))
  have hkey : Tinv e * T (e + 1) = T (e + 1) * T e * (Tinv (e + 1) * Tinv e) :=
    calc Tinv e * T (e + 1) = Tinv e * T (e + 1) * (T e * Tinv e) := by
          rw [h.mul_inv e he (by omega), mul_one]
      _ = Tinv e * T (e + 1) * T e * Tinv e := by simp only [mul_assoc]
      _ = T (e + 1) * T e * Tinv (e + 1) * Tinv e := by rw [h.braid_pair_neg he (by omega)]
      _ = T (e + 1) * T e * (Tinv (e + 1) * Tinv e) := mul_assoc _ _ _
  rw [← hsplit1, ← hsplit2, trainUp_add_two_self, ← mul_assoc, hcomm]
  simp only [mul_assoc, hkey]

end SplitPos

/-- **The orientation of `HJO.Braid.IsBraidSystem.gen_split_pos`**, at `ε = -1`, `c = 3`, `e = 1`
and rank `3` with every train written out: `T_1^{-1} T_2 = (T_2T_1)(T_2^{-1}T_1^{-1})`. At `ε = 1`
both sides are the same word, so this sign is the one that pins the orientation. -/
theorem IsBraidSystem.gen_split_pos_three (h : IsBraidSystem 3 T Tinv) :
    Tinv 1 * T 2 = T 2 * T 1 * (Tinv 2 * Tinv 1) := by
  have hgen := h.gen_split_pos_inv (c := 3) (e := 1) le_rfl (by omega) le_rfl
  rwa [show trainDown T Tinv 3 2 = T 2 from trainDown_succ_self T Tinv 2,
    show trainDown T Tinv 3 1 = T 2 * T 1 from trainDown_add_two_self T Tinv 1,
    show trainUp T Tinv 3 1 = Tinv 2 * Tinv 1 from trainUp_add_two_self T Tinv 1] at hgen

/-! ### Splitting a negative descending train at its tail -/

section SplitNeg

variable {c e : ℕ}

/-- **Splitting a negative descending train at its tail**, which is
`HJO.Braid.IsBraidSystem.gen_split_neg` at `ε = 1`, written at `d = e + 1`:
`T_{e+1} T_{c↘e+1} = T_{c↘e+2} T_{e↗e+2}`.

The train splits as `T_{c↘e}T_e^{-1}`, and what is left after both sides are written out is
`T_{e+1}T_e^{-1} = T_e^{-1}T_{e+1}^{-1}T_eT_{e+1}`, which is
`HJO.Braid.IsBraidSystem.braid_mirror_neg` multiplied on the left by `T_e^{-1}`. -/
@[hjo "lem_train_gen_split_neg"]
theorem IsBraidSystem.gen_split_neg (h : IsBraidSystem k T Tinv) (hc : 1 ≤ c) (hce : c ≤ e)
    (hek : e + 2 ≤ k) :
    T (e + 1) * trainDown T Tinv c (e + 1)
      = trainDown T Tinv c (e + 2) * trainUp T Tinv e (e + 2) := by
  have he : 1 ≤ e := le_trans hc hce
  have hsplit1 : trainDown T Tinv c e * Tinv e = trainDown T Tinv c (e + 1) := by
    have hglue := trainDown_mul_trainDown (T := T) (Tinv := Tinv) h (a := c) (b := e)
      (c := e + 1) hc (by omega) he (by omega) (by omega) (by omega)
    rwa [trainDown_self_succ] at hglue
  have hsplit2 : trainDown T Tinv c e * (Tinv e * Tinv (e + 1)) = trainDown T Tinv c (e + 2) := by
    have hglue := trainDown_mul_trainDown (T := T) (Tinv := Tinv) h (a := c) (b := e)
      (c := e + 2) hc (by omega) he (by omega) (by omega) hek
    rwa [trainDown_self_add_two] at hglue
  have hcomm : T (e + 1) * trainDown T Tinv c e = trainDown T Tinv c e * T (e + 1) :=
    trainDown_far_comm h (by omega) (by omega) hc (by omega) he (by omega) (Or.inr (by omega))
  have hkey : T (e + 1) * Tinv e = Tinv e * Tinv (e + 1) * (T e * T (e + 1)) :=
    calc T (e + 1) * Tinv e = Tinv e * T e * (T (e + 1) * Tinv e) := by
          rw [h.inv_mul e he (by omega), one_mul]
      _ = Tinv e * (T e * T (e + 1) * Tinv e) := by simp only [mul_assoc]
      _ = Tinv e * (Tinv (e + 1) * T e * T (e + 1)) := by
          rw [h.braid_mirror_neg he hek]
      _ = Tinv e * Tinv (e + 1) * (T e * T (e + 1)) := by simp only [mul_assoc]
  rw [← hsplit1, ← hsplit2, trainUp_self_add_two, ← mul_assoc, hcomm]
  simp only [mul_assoc, hkey]

/-- **Splitting a negative descending train at its tail**, at `ε = -1`:
`T_{e+1}^{-1} T_{c↘e+1} = T_{c↘e} T_{e+2↗e}`.

No braid relation is used at this sign: the train splits as `T_{c↘e}T_e^{-1}`, the letter
`T_{e+1}^{-1}` commutes past the first factor, and `T_{e+1}^{-1}T_e^{-1}` is the ascending train
`T_{e+2↗e}`. -/
@[hjo "lem_train_gen_split_neg"]
theorem IsBraidSystem.gen_split_neg_inv (h : IsBraidSystem k T Tinv) (hc : 1 ≤ c) (hce : c ≤ e)
    (hek : e + 2 ≤ k) :
    Tinv (e + 1) * trainDown T Tinv c (e + 1)
      = trainDown T Tinv c e * trainUp T Tinv (e + 2) e := by
  have he : 1 ≤ e := le_trans hc hce
  have hsplit : trainDown T Tinv c e * Tinv e = trainDown T Tinv c (e + 1) := by
    have hglue := trainDown_mul_trainDown (T := T) (Tinv := Tinv) h (a := c) (b := e)
      (c := e + 1) hc (by omega) he (by omega) (by omega) (by omega)
    rwa [trainDown_self_succ] at hglue
  have hcomm : Tinv (e + 1) * trainDown T Tinv c e = trainDown T Tinv c e * Tinv (e + 1) :=
    trainDown_far_comm_inv h (by omega) (by omega) hc (by omega) he (by omega)
      (Or.inr (by omega))
  rw [← hsplit, trainUp_add_two_self, ← mul_assoc, hcomm]
  simp only [mul_assoc]

end SplitNeg

/-- **The orientation of `HJO.Braid.IsBraidSystem.gen_split_neg`**, at `ε = 1`, `c = 1`, `e = 1` and
rank `3` with every train written out: `T_2 T_1^{-1} = (T_1^{-1}T_2^{-1})(T_1T_2)`. At `ε = -1` both
sides are the same word, so this sign is the one that pins the orientation. -/
theorem IsBraidSystem.gen_split_neg_three (h : IsBraidSystem 3 T Tinv) :
    T 2 * Tinv 1 = Tinv 1 * Tinv 2 * (T 1 * T 2) := by
  have hgen := h.gen_split_neg (c := 1) (e := 1) le_rfl le_rfl (by omega)
  rwa [show trainDown T Tinv 1 2 = Tinv 1 from trainDown_self_succ T Tinv 1,
    show trainDown T Tinv 1 3 = Tinv 1 * Tinv 2 from trainDown_self_add_two T Tinv 1,
    show trainUp T Tinv 1 3 = T 1 * T 2 from trainUp_self_add_two T Tinv 1] at hgen

end HJO.Braid
