/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import HJO.Shuffle.BraidTrain

/-! # The train algebra: gluing, inverting, and moving a generator through a train

`HJO/Shuffle/BraidTrain.lean` defines `HJO.Braid.trainUp` and `HJO.Braid.trainDown` and proves
what holds of them as *words*: the boundary cases, the two closed forms, and the duality
`HJO.Braid.trainUp_inv_eq_trainDown`. It proves nothing about composing two trains. This file is
that algebra.

## Main results

* `HJO.Braid.trainUp_mul_trainUp`, `HJO.Braid.trainDown_mul_trainDown` — gluing,
  `T_{a↗b}T_{b↗c} = T_{a↗c}` and its descending twin (`HJO.Braid.trainUp_mul_trainUp`,
  `HJO.Braid.trainDown_mul_trainDown`).
* `HJO.Braid.trainUp_mul_trainUp_self`, `HJO.Braid.trainDown_mul_trainDown_self` — the inverse of a
  train is the train read backwards (`HJO.Braid.trainUp_mul_trainUp_self`, and the descending form).
  In particular `T_{b↘1}T_{1↘b} = 1`, which is what makes `HJO.Mellit.replicatedLetter` a
  conjugation.
* `HJO.Braid.trainUp_eq_trainUp_one_mul`, `HJO.Braid.trainDown_eq_trainDown_one_mul` — the
  factorisations through the base point, `HJO.Braid.trainUp_eq_trainUp_one_mul` and
  `HJO.Braid.trainDown_eq_trainDown_one_mul`.
* `HJO.Braid.trainUp_far_comm`, `HJO.Braid.trainDown_far_comm` — a far generator commutes with a
  train (`HJO.Braid.trainUp_far_comm`, `HJO.Braid.trainDown_far_comm`).
* `HJO.Braid.trainUp_mul_gen` — a generator shifts through an ascending train that straddles it,
  `T_{a↗b}T_i = T_{i+1}T_{a↗b}` (`HJO.Braid.trainUp_mul_gen`), and `HJO.Braid.trainUp_overtake` —
  `T_{a↗b}T_{c↗d} = T_{c↗d}T_{a+1↗b+1}` (`HJO.Braid.trainUp_overtake`), which is that shift applied
  to every letter of the short train at once.
* `HJO.Braid.trainUp_eq_trainDown_of_adjacent` — one letter read as either train
  (`HJO.Braid.trainUp_eq_trainDown_of_adjacent`), and
  `HJO.Braid.IsBraidSystem.braid_mirror_pos`/`_neg`, the two signs of
  `T_{j+1}^εT_jT_{j+1} = T_jT_{j+1}T_j^ε` (`HJO.Braid.IsBraidSystem.braid_mirror_pos`).
* `HJO.Braid.indexShift_comm_adjacent`, `HJO.Braid.indexShift_ne_head`,
  `HJO.Braid.indexShift_congr_head`, `HJO.Braid.indexShift_congr_tail` — the four arithmetic facts
  about `HJO.Braid.indexShift` that the collision bookkeeping runs on.

## Method

Everything separates into two layers, and keeping them apart is what makes the gluing short.

The **word layer** knows no relations. `HJO.Braid.ascendingWord_mul` and
`HJO.Braid.descendingWord_mul` are pure `List.range'` arithmetic: concatenating two adjacent index
ranges gives the third. They are what splits a train at any interior point, in either direction, and
they are used in both directions — to assemble and to factor.

The **relation layer** is two telescopes. `HJO.Braid.ascendingWord_mul_descendingWord` and
`HJO.Braid.descendingWord_mul_ascendingWord` say that a word and its reverse-with-inverted-letters
cancel, by induction peeling one letter off the inside or the outside. Everything else is these plus
a case split: `HJO.Braid.trainUp_mul_trainUp` is six cases on the orderings of `a`, `b`, `c`, and
each is one splitting followed by one telescope.

The descending statements are not reproved. `HJO.Braid.trainUp_inv_eq_trainDown` already says
`trainUp Tinv T = trainDown T Tinv`, and `IsBraidSystem.inverses` says the swapped pair is a braid
system, so each descending result is its ascending counterpart applied to `(Tinv, T)`.

## Index conventions

The trains are total in `a` and `b`; the `1 ≤ a, b ≤ k` appears as hypotheses exactly
where a relation of the braid system is read, which is where it is needed — a train that leaves
`[1, k]` would ask for a letter the system says nothing about. `|b - c| = 1` is written as the
disjunction `b = c + 1 ∨ c = b + 1`, which is that condition on `ℕ`, and the `σ` lemmas keep
`|x - y| = 1` over `ℤ` because `HJO.Braid.indexShift` is defined there.
-/

@[expose] public section

namespace HJO.Braid

section Monoid

variable {M : Type*} [Monoid M]

/-! ### Two monoid facts about named inverses -/

/-- If `x` commutes with `y` and `y'` is a two-sided inverse of `y`, then `x` commutes with `y'`.
Without a group instance this is how far commutation is transported to the inverted letters, which
the second branch of both trains is made of. -/
theorem comm_inv_right {x y y' : M} (hy : y * y' = 1) (hy' : y' * y = 1) (h : x * y = y * x) :
    x * y' = y' * x :=
  calc x * y' = y' * y * (x * y') := by rw [hy', one_mul]
    _ = y' * (y * x) * y' := by simp only [mul_assoc]
    _ = y' * (x * y) * y' := by rw [h]
    _ = y' * x * (y * y') := by simp only [mul_assoc]
    _ = y' * x := by rw [hy, mul_one]

/-- An element that commutes with every entry of a list commutes with the list's product. -/
theorem mul_prod_comm {x : M} {l : List M} (h : ∀ y ∈ l, x * y = y * x) :
    x * l.prod = l.prod * x := by
  induction l with
  | nil => simp
  | cons y l ih =>
    have hy : x * y = y * x := h y (List.mem_cons_self ..)
    have hl : ∀ z ∈ l, x * z = z * x := fun z hz => h z (List.mem_cons_of_mem _ hz)
    rw [List.prod_cons, ← mul_assoc, hy, mul_assoc, ih hl, mul_assoc]

/-! ### The word layer: splitting an index range -/

/-- A one-letter ascending word. -/
theorem ascendingWord_succ_self (T : ℕ → M) (a : ℕ) : ascendingWord T a (a + 1) = T a := by
  simp [ascendingWord]

/-- A one-letter descending word. -/
theorem descendingWord_succ_self (T : ℕ → M) (a : ℕ) : descendingWord T (a + 1) a = T a := by
  simp [descendingWord]

/-- A two-letter ascending word. -/
theorem ascendingWord_add_two (T : ℕ → M) (a : ℕ) :
    ascendingWord T a (a + 2) = T a * T (a + 1) := by
  simp [ascendingWord, List.range']

/-- **Adjacent ascending words concatenate.** Pure `List.range'` arithmetic: no relation of the
braid system is read. -/
theorem ascendingWord_mul (T : ℕ → M) {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    ascendingWord T a b * ascendingWord T b c = ascendingWord T a c := by
  have hsplit : List.range' a (b - a) ++ List.range' b (c - b) = List.range' a (c - a) := by
    have h := @List.range'_append a (b - a) (c - b) 1
    rw [one_mul, show a + (b - a) = b by omega, show b - a + (c - b) = c - a by omega] at h
    exact h
  rw [ascendingWord, ascendingWord, ascendingWord, ← List.prod_append, ← List.map_append, hsplit]

/-- **Adjacent descending words concatenate.** The outer range comes first, so the concatenation is
of the reversed lists in the other order. -/
theorem descendingWord_mul (T : ℕ → M) {a b c : ℕ} (hcb : c ≤ b) (hba : b ≤ a) :
    descendingWord T a b * descendingWord T b c = descendingWord T a c := by
  have hsplit : List.range' c (b - c) ++ List.range' b (a - b) = List.range' c (a - c) := by
    have h := @List.range'_append c (b - c) (a - b) 1
    rw [one_mul, show c + (b - c) = b by omega, show b - c + (a - b) = a - c by omega] at h
    exact h
  rw [descendingWord, descendingWord, descendingWord, ← List.prod_append, ← List.map_append,
    ← List.reverse_append, hsplit]

/-! ### The relation layer: the two telescopes -/

variable {k : ℕ} {T Tinv : ℕ → M}

/-- **An ascending word cancels the descending word of the inverted letters.** Induction peeling the
innermost letter: `(T_a ⋯ T_{b-1})(T_{b-1}^{-1} ⋯ T_a^{-1}) = 1`. -/
theorem ascendingWord_mul_descendingWord (a : ℕ) :
    ∀ n : ℕ, (∀ i, a ≤ i → i < a + n → T i * Tinv i = 1) →
      ascendingWord T a (a + n) * descendingWord Tinv (a + n) a = 1 := by
  intro n
  induction n with
  | zero => intro _; simp [ascendingWord, descendingWord]
  | succ n ih =>
    intro hinv
    rw [show a + (n + 1) = a + n + 1 from by omega]
    have hasc : ascendingWord T a (a + n + 1)
        = ascendingWord T a (a + n) * T (a + n) := by
      rw [← ascendingWord_succ_self T (a + n),
        ascendingWord_mul T (by omega) (by omega : a + n ≤ a + n + 1)]
    have hdesc : descendingWord Tinv (a + n + 1) a
        = Tinv (a + n) * descendingWord Tinv (a + n) a := by
      rw [← descendingWord_succ_self Tinv (a + n),
        descendingWord_mul Tinv (by omega) (by omega : a + n ≤ a + n + 1)]
    rw [hasc, hdesc, mul_assoc, ← mul_assoc (T (a + n)), hinv (a + n) (by omega) (by omega),
      one_mul]
    exact ih fun i h1 h2 => hinv i h1 (by omega)

/-- **A descending word cancels the ascending word of the letters it inverts.** Induction peeling
the outermost letter: `(T_{b-1}^{-1} ⋯ T_a^{-1})(T_a ⋯ T_{b-1}) = 1`. -/
theorem descendingWord_mul_ascendingWord (a : ℕ) :
    ∀ n : ℕ, (∀ i, a ≤ i → i < a + n → Tinv i * T i = 1) →
      descendingWord Tinv (a + n) a * ascendingWord T a (a + n) = 1 := by
  intro n
  induction n with
  | zero => intro _; simp [ascendingWord, descendingWord]
  | succ n ih =>
    intro hinv
    rw [show a + (n + 1) = a + n + 1 from by omega]
    have hasc : ascendingWord T a (a + n + 1)
        = ascendingWord T a (a + n) * T (a + n) := by
      rw [← ascendingWord_succ_self T (a + n),
        ascendingWord_mul T (by omega) (by omega : a + n ≤ a + n + 1)]
    have hdesc : descendingWord Tinv (a + n + 1) a
        = Tinv (a + n) * descendingWord Tinv (a + n) a := by
      rw [← descendingWord_succ_self Tinv (a + n),
        descendingWord_mul Tinv (by omega) (by omega : a + n ≤ a + n + 1)]
    rw [hasc, hdesc, mul_assoc, ← mul_assoc (descendingWord Tinv (a + n) a),
      ih fun i h1 h2 => hinv i h1 (by omega), one_mul,
      hinv (a + n) (by omega) (by omega)]

/-- The telescope in the form the gluing uses: `T_a ⋯ T_{b-1}` against its inverse word. -/
theorem ascendingWord_mul_descendingWord' (h : IsBraidSystem k T Tinv) {a b : ℕ} (ha : 1 ≤ a)
    (hab : a ≤ b) (hbk : b ≤ k) : ascendingWord T a b * descendingWord Tinv b a = 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, b = a + n := ⟨b - a, by omega⟩
  exact ascendingWord_mul_descendingWord a n fun i h1 h2 =>
    h.mul_inv i (by omega) (by omega)

/-- The other telescope in the form the gluing uses. -/
theorem descendingWord_mul_ascendingWord' (h : IsBraidSystem k T Tinv) {a b : ℕ} (hb : 1 ≤ b)
    (hba : b ≤ a) (hak : a ≤ k) : descendingWord Tinv a b * ascendingWord T b a = 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, a = b + n := ⟨a - b, by omega⟩
  exact descendingWord_mul_ascendingWord b n fun i h1 h2 =>
    h.inv_mul i (by omega) (by omega)

/-! ### Gluing -/

/-- **Gluing, ascending**: `T_{a↗b}T_{b↗c} = T_{a↗c}`, `HJO.Braid.trainUp_mul_trainUp`.

Six cases on the orderings of `a`, `b`, `c`; each is one application of
`HJO.Braid.ascendingWord_mul` or `HJO.Braid.descendingWord_mul` to split off the part that survives,
followed by one telescope to cancel the part that does not. -/
@[hjo "lem_train_glue_up"]
theorem trainUp_mul_trainUp (h : IsBraidSystem k T Tinv) {a b c : ℕ} (ha : 1 ≤ a) (hak : a ≤ k)
    (hb : 1 ≤ b) (hbk : b ≤ k) (hc : 1 ≤ c) (hck : c ≤ k) :
    trainUp T Tinv a b * trainUp T Tinv b c = trainUp T Tinv a c := by
  unfold trainUp
  split_ifs with hab hbc hac hac hbc hac hac
  · exact ascendingWord_mul T hab hbc
  · omega
  · rw [← ascendingWord_mul T hac (by omega : c ≤ b), mul_assoc,
      ascendingWord_mul_descendingWord' h hc (by omega) hbk, mul_one]
  · rw [← descendingWord_mul Tinv (by omega : c ≤ a) (by omega : a ≤ b), ← mul_assoc,
      ascendingWord_mul_descendingWord' h ha hab hbk, one_mul]
  · rw [← ascendingWord_mul T (by omega : b ≤ a) hac, ← mul_assoc,
      descendingWord_mul_ascendingWord' h hb (by omega) hak, one_mul]
  · rw [← descendingWord_mul Tinv (by omega : b ≤ c) (by omega : c ≤ a), mul_assoc,
      descendingWord_mul_ascendingWord' h hb hbc hck, mul_one]
  · omega
  · exact descendingWord_mul Tinv (by omega) (by omega)

/-- **Gluing, descending**: `T_{a↘b}T_{b↘c} = T_{a↘c}`, `HJO.Braid.trainDown_mul_trainDown`. By
`HJO.Braid.trainUp_inv_eq_trainDown` this is `HJO.Braid.trainUp_mul_trainUp` for the swapped pair,
which `IsBraidSystem.inverses` says is a braid system. -/
@[hjo "lem_train_glue_down"]
theorem trainDown_mul_trainDown (h : IsBraidSystem k T Tinv) {a b c : ℕ} (ha : 1 ≤ a) (hak : a ≤ k)
    (hb : 1 ≤ b) (hbk : b ≤ k) (hc : 1 ≤ c) (hck : c ≤ k) :
    trainDown T Tinv a b * trainDown T Tinv b c = trainDown T Tinv a c := by
  rw [← trainUp_inv_eq_trainDown, ← trainUp_inv_eq_trainDown, ← trainUp_inv_eq_trainDown]
  exact trainUp_mul_trainUp h.inverses ha hak hb hbk hc hck

/-! ### Inverses of trains -/

/-- **The inverse of an ascending train is the train read backwards**, `(T_{a↗b})^{-1} = T_{b↗a}`:
`HJO.Braid.trainUp_mul_trainUp_self`, stated as the two cancellations that a monoid with named
inverses can say. -/
@[hjo "lem_train_inv_up"]
theorem trainUp_mul_trainUp_self (h : IsBraidSystem k T Tinv) {a b : ℕ} (ha : 1 ≤ a) (hak : a ≤ k)
    (hb : 1 ≤ b) (hbk : b ≤ k) : trainUp T Tinv a b * trainUp T Tinv b a = 1 := by
  rw [trainUp_mul_trainUp h ha hak hb hbk ha hak, trainUp_self]

/-- **The inverse of a descending train is the train read backwards**, `(T_{a↘b})^{-1} = T_{b↘a}`.
At `b = 1` this is `T_{a↘1}T_{1↘a} = 1`, which is what makes the `q^{-k}T_{k+1↘1}(·)T_{1↗k+1}` of
`HJO.Mellit.replicatedLetter` a conjugation rather than a two-sided multiplication. -/
theorem trainDown_mul_trainDown_self (h : IsBraidSystem k T Tinv) {a b : ℕ} (ha : 1 ≤ a)
    (hak : a ≤ k) (hb : 1 ≤ b) (hbk : b ≤ k) :
    trainDown T Tinv a b * trainDown T Tinv b a = 1 := by
  rw [trainDown_mul_trainDown h ha hak hb hbk ha hak, trainDown_self]

/-! ### The factorisations through the base point -/

/-- **Ascending trains factor through the base point**, `T_{a↗b} = T_{a↗1}T_{1↗b}`. Its
`(T_{1↗a})^{-1}` is `T_{a↗1}`, by `HJO.Braid.trainUp_mul_trainUp_self` at `b = 1`. -/
@[hjo "lem_train_unfold"]
theorem trainUp_eq_trainUp_one_mul (h : IsBraidSystem k T Tinv) {a b : ℕ} (ha : 1 ≤ a)
    (hak : a ≤ k) (hb : 1 ≤ b) (hbk : b ≤ k) :
    trainUp T Tinv a b = trainUp T Tinv a 1 * trainUp T Tinv 1 b :=
  (trainUp_mul_trainUp h ha hak le_rfl (by omega) hb hbk).symm

/-- **Descending trains factor through the base point**, `T_{a↘b} = T_{a↘1}T_{1↘b}`; here
 `(T_{b↘1})^{-1}` is `T_{1↘b}` by
`HJO.Braid.trainDown_mul_trainDown_self`. -/
@[hjo "lem_train_unfold_down"]
theorem trainDown_eq_trainDown_one_mul (h : IsBraidSystem k T Tinv) {a b : ℕ} (ha : 1 ≤ a)
    (hak : a ≤ k) (hb : 1 ≤ b) (hbk : b ≤ k) :
    trainDown T Tinv a b = trainDown T Tinv a 1 * trainDown T Tinv 1 b :=
  (trainDown_mul_trainDown h ha hak le_rfl (by omega) hb hbk).symm

/-! ### A far generator commutes with a train -/

/-- A generator commutes with any product of far letters. -/
theorem mul_prod_T_comm (h : IsBraidSystem k T Tinv) {i : ℕ} (hi : 1 ≤ i) (hik : i + 1 ≤ k)
    {l : List ℕ} (hl : ∀ j ∈ l, 1 ≤ j ∧ j + 1 ≤ k ∧ (i + 2 ≤ j ∨ j + 2 ≤ i)) :
    T i * (l.map T).prod = (l.map T).prod * T i := by
  refine mul_prod_comm fun y hy => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
  obtain ⟨hj1, hjk, hfar⟩ := hl j hj
  rcases hfar with hfar | hfar
  · exact h.far_comm i j hi hfar hjk
  · exact (h.far_comm j i hj1 hfar hik).symm

/-- A generator commutes with any product of far inverted letters, by
`HJO.Braid.comm_inv_right`. -/
theorem mul_prod_Tinv_comm (h : IsBraidSystem k T Tinv) {i : ℕ} (hi : 1 ≤ i) (hik : i + 1 ≤ k)
    {l : List ℕ} (hl : ∀ j ∈ l, 1 ≤ j ∧ j + 1 ≤ k ∧ (i + 2 ≤ j ∨ j + 2 ≤ i)) :
    T i * (l.map Tinv).prod = (l.map Tinv).prod * T i := by
  refine mul_prod_comm fun y hy => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
  obtain ⟨hj1, hjk, hfar⟩ := hl j hj
  refine comm_inv_right (h.mul_inv j hj1 hjk) (h.inv_mul j hj1 hjk) ?_
  rcases hfar with hfar | hfar
  · exact h.far_comm i j hi hfar hjk
  · exact (h.far_comm j i hj1 hfar hik).symm

/-- **A far generator commutes with an ascending train**, `HJO.Braid.trainUp_far_comm`. The
train reads only the indices in `[min(a,b), max(a,b) - 1]`, and the hypothesis puts every one of
them at distance at least two from `i`. -/
@[hjo "lem_train_far_up"]
theorem trainUp_far_comm (h : IsBraidSystem k T Tinv) {a b i : ℕ} (hi : 1 ≤ i) (hik : i + 1 ≤ k)
    (ha : 1 ≤ a) (hak : a ≤ k) (hb : 1 ≤ b) (hbk : b ≤ k)
    (hfar : i + 2 ≤ min a b ∨ max a b + 1 ≤ i) :
    T i * trainUp T Tinv a b = trainUp T Tinv a b * T i := by
  unfold trainUp
  split_ifs with hab
  · refine mul_prod_T_comm h hi hik fun j hj => ?_
    rw [List.mem_range'_1] at hj
    refine ⟨by omega, by omega, ?_⟩
    rcases hfar with hfar | hfar
    · left; omega
    · right; omega
  · refine mul_prod_Tinv_comm h hi hik fun j hj => ?_
    rw [List.mem_reverse, List.mem_range'_1] at hj
    refine ⟨by omega, by omega, ?_⟩
    rcases hfar with hfar | hfar
    · left; omega
    · right; omega

/-- **A far generator commutes with a descending train**, `HJO.Braid.trainDown_far_comm`, by
`HJO.Braid.trainUp_inv_eq_trainDown` from the ascending form. -/
@[hjo "lem_train_far_down"]
theorem trainDown_far_comm (h : IsBraidSystem k T Tinv) {a b i : ℕ} (hi : 1 ≤ i) (hik : i + 1 ≤ k)
    (ha : 1 ≤ a) (hak : a ≤ k) (hb : 1 ≤ b) (hbk : b ≤ k)
    (hfar : i + 2 ≤ min a b ∨ max a b + 1 ≤ i) :
    T i * trainDown T Tinv a b = trainDown T Tinv a b * T i := by
  unfold trainDown
  split_ifs with hba
  · refine mul_prod_T_comm h hi hik fun j hj => ?_
    rw [List.mem_reverse, List.mem_range'_1] at hj
    refine ⟨by omega, by omega, ?_⟩
    rcases hfar with hfar | hfar
    · left; omega
    · right; omega
  · refine mul_prod_Tinv_comm h hi hik fun j hj => ?_
    rw [List.mem_range'_1] at hj
    refine ⟨by omega, by omega, ?_⟩
    rcases hfar with hfar | hfar
    · left; omega
    · right; omega

/-! ### One letter read as either train, and the mirrored braid pair -/

/-- **A single letter read as either train**, `HJO.Braid.trainUp_eq_trainDown_of_adjacent`: for
`|b - c| = 1`, `T_{c↗b} = T_{b↘c}`. Both sides are one letter, uninverted if `b = c + 1` and
inverted if `c = b + 1`. -/
@[hjo "lem_train_adjacent"]
theorem trainUp_eq_trainDown_of_adjacent (T Tinv : ℕ → M) {b c : ℕ}
    (hbc : b = c + 1 ∨ c = b + 1) : trainUp T Tinv c b = trainDown T Tinv b c := by
  rcases hbc with rfl | rfl
  · have h1 : c ≤ c + 1 := by omega
    rw [trainUp, trainDown]
    split_ifs
    rw [ascendingWord_succ_self, descendingWord_succ_self]
  · rw [trainUp_succ_self, trainDown_self_succ]

/-- **A generator conjugated by the mirrored adjacent pair**, at `ε = 1`: this is the braid relation
of `HJO.Braid.IsBraidSystem` read from the other side. -/
@[hjo "lem_train_braid_mirror"]
theorem IsBraidSystem.braid_mirror_pos (h : IsBraidSystem k T Tinv) {j : ℕ} (hj : 1 ≤ j)
    (hjk : j + 2 ≤ k) : T (j + 1) * T j * T (j + 1) = T j * T (j + 1) * T j :=
  (h.braid j hj hjk).symm

/-- **A generator conjugated by the mirrored adjacent pair**, at `ε = -1`:
`T_{j+1}^{-1}T_jT_{j+1} = T_jT_{j+1}T_j^{-1}`. The braid relation moves the inverse across the
pair and the named inverses cancel; no group instance is used. -/
@[hjo "lem_train_braid_mirror"]
theorem IsBraidSystem.braid_mirror_neg (h : IsBraidSystem k T Tinv) {j : ℕ} (hj : 1 ≤ j)
    (hjk : j + 2 ≤ k) : Tinv (j + 1) * T j * T (j + 1) = T j * T (j + 1) * Tinv j := by
  have key : T j * T (j + 1) = T (j + 1) * T j * T (j + 1) * Tinv j := by
    rw [← h.braid j hj hjk, mul_assoc (T j * T (j + 1)) (T j) (Tinv j),
      h.mul_inv j hj (by omega), mul_one]
  calc Tinv (j + 1) * T j * T (j + 1) = Tinv (j + 1) * (T j * T (j + 1)) := mul_assoc _ _ _
    _ = Tinv (j + 1) * (T (j + 1) * T j * T (j + 1) * Tinv j) := by rw [key]
    _ = T j * T (j + 1) * Tinv j := by
        simp only [mul_assoc]
        exact mul_mul_cancel_of_mul_eq_one (h.inv_mul (j + 1) (by omega) (by omega)) _

/-! ### A generator shifts through an ascending train -/

/-- **A generator shifts through an ascending word that straddles it**, with the three relations
the argument reads passed in as hypotheses rather than drawn from a braid system: the braid relation
at `i`, the commutation of `T_i` with the letters above `i + 1`, and the commutation of `T_{i+1}`
with the letters below `i`.

Split the word as `T_{a↗i}·T_iT_{i+1}·T_{i+2↗b}`. The tail commutes with `T_i` and the head with
`T_{i+1}`, and what is left in the middle is exactly the braid relation.

`HJO.Braid.trainUp_mul_gen` is this with the hypotheses read off a `HJO.Braid.IsBraidSystem`, which
is the form the train algebra uses. They are kept apart because a braid system also names two-sided
inverses: the braid operators of `HJO.Sweep` satisfy both relations for **every** `q` and are
invertible only for `q ≠ 0`, so `HJO.Sweep.cmAscWord_mul_braidEnd` — which is this statement
for the word `T_{[1,k]}` — would acquire a hypothesis it does not have if it were routed through
`IsBraidSystem`. -/
theorem ascendingWord_mul_gen {T : ℕ → M} {a b i : ℕ} (hai : a ≤ i) (hib : i + 1 < b)
    (hbraid : T i * T (i + 1) * T i = T (i + 1) * T i * T (i + 1))
    (htail : ∀ j, i + 2 ≤ j → j < b → T i * T j = T j * T i)
    (hhead : ∀ j, a ≤ j → j + 2 ≤ i + 1 → T (i + 1) * T j = T j * T (i + 1)) :
    ascendingWord T a b * T i = T (i + 1) * ascendingWord T a b := by
  have hsplit : ascendingWord T a b
      = ascendingWord T a i * (T i * T (i + 1)) * ascendingWord T (i + 2) b := by
    rw [← ascendingWord_add_two T i, ascendingWord_mul T hai (by omega : i ≤ i + 2),
      ascendingWord_mul T (by omega : a ≤ i + 2) (by omega : i + 2 ≤ b)]
  have htail' : T i * ascendingWord T (i + 2) b = ascendingWord T (i + 2) b * T i := by
    rw [ascendingWord]
    refine mul_prod_comm fun y hy => ?_
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
    rw [List.mem_range'_1] at hj
    exact htail j (by omega) (by omega)
  have hhead' : T (i + 1) * ascendingWord T a i = ascendingWord T a i * T (i + 1) := by
    rw [ascendingWord]
    refine mul_prod_comm fun y hy => ?_
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
    rw [List.mem_range'_1] at hj
    exact hhead j (by omega) (by omega)
  have hmove : ascendingWord T a i * (T (i + 1) * T i * T (i + 1))
      = T (i + 1) * (ascendingWord T a i * (T i * T (i + 1))) :=
    calc ascendingWord T a i * (T (i + 1) * T i * T (i + 1))
        = ascendingWord T a i * T (i + 1) * (T i * T (i + 1)) := by simp only [mul_assoc]
      _ = T (i + 1) * ascendingWord T a i * (T i * T (i + 1)) := by rw [← hhead']
      _ = T (i + 1) * (ascendingWord T a i * (T i * T (i + 1))) := by simp only [mul_assoc]
  rw [hsplit]
  calc ascendingWord T a i * (T i * T (i + 1)) * ascendingWord T (i + 2) b * T i
      = ascendingWord T a i * (T i * T (i + 1)) * (ascendingWord T (i + 2) b * T i) :=
        mul_assoc _ _ _
    _ = ascendingWord T a i * (T i * T (i + 1)) * (T i * ascendingWord T (i + 2) b) := by
        rw [htail']
    _ = ascendingWord T a i * (T i * T (i + 1) * T i) * ascendingWord T (i + 2) b := by
        simp only [mul_assoc]
    _ = ascendingWord T a i * (T (i + 1) * T i * T (i + 1)) * ascendingWord T (i + 2) b := by
        rw [hbraid]
    _ = T (i + 1) * (ascendingWord T a i * (T i * T (i + 1)) * ascendingWord T (i + 2) b) := by
        rw [hmove]
        simp only [mul_assoc]

/-- **A generator shifts through an ascending train that straddles it**:
  `T_{a↗b}T_i = T_{i+1}T_{a↗b}` for `1 ≤ a ≤ i` and `i + 1 < b ≤ k`.

The train is on its ascending branch, `a ≤ i < b`, so this is
`HJO.Braid.ascendingWord_mul_gen` with the braid relation and the two far commutations read off the
braid system — where the rank bounds `j + 1 ≤ k` come from `j < b ≤ k`. -/
@[hjo "lem_train_shift_up"]
theorem trainUp_mul_gen (h : IsBraidSystem k T Tinv) {a b i : ℕ} (ha : 1 ≤ a) (hai : a ≤ i)
    (hib : i + 1 < b) (hbk : b ≤ k) :
    trainUp T Tinv a b * T i = T (i + 1) * trainUp T Tinv a b := by
  have hw : trainUp T Tinv a b = ascendingWord T a b := by
    rw [trainUp]
    split_ifs with hif
    · rfl
    · exact absurd (show a ≤ b by omega) hif
  rw [hw]
  exact ascendingWord_mul_gen hai hib (h.braid i (by omega) (by omega))
    (fun j hij hjb => h.far_comm i j (by omega) hij (by omega))
    (fun j haj hji => (h.far_comm j (i + 1) (by omega) (by omega) (by omega)).symm)

/-! ### Overtaking -/

/-- A conjugation read from the other side: from `wx = yw` with `w` invertible, `xw' = w'y`. -/
theorem conj_swap {w w' x y : M} (hww : w * w' = 1) (hw'w : w' * w = 1) (h : w * x = y * w) :
    x * w' = w' * y :=
  calc x * w' = w' * w * (x * w') := by rw [hw'w, one_mul]
    _ = w' * (w * x) * w' := by simp only [mul_assoc]
    _ = w' * (y * w) * w' := by rw [h]
    _ = w' * y * (w * w') := by simp only [mul_assoc]
    _ = w' * y := by rw [hww, mul_one]

/-- Conjugation shifts an inverted letter exactly as it shifts the letter. -/
theorem comm_shift_inv {x y y' yi yi' : M} (hy : y * yi = 1) (hy' : yi' * y' = 1)
    (h : x * y = y' * x) : x * yi = yi' * x :=
  calc x * yi = yi' * y' * (x * yi) := by rw [hy', one_mul]
    _ = yi' * (y' * x) * yi := by simp only [mul_assoc]
    _ = yi' * (x * y) * yi := by rw [h]
    _ = yi' * x * (y * yi) := by simp only [mul_assoc]
    _ = yi' * x := by rw [hy, mul_one]

/-- Moving an element rightwards through a product of letters, shifting each as it passes. -/
theorem mul_prod_shift {x : M} {f g : ℕ → M} {l : List ℕ}
    (h : ∀ j ∈ l, x * f j = g j * x) : x * (l.map f).prod = (l.map g).prod * x := by
  induction l with
  | nil => simp
  | cons j l ih =>
    have hj : x * f j = g j * x := h j (List.mem_cons_self ..)
    have hl : ∀ z ∈ l, x * f z = g z * x := fun z hz => h z (List.mem_cons_of_mem _ hz)
    simp only [List.map_cons, List.prod_cons]
    rw [← mul_assoc, hj, mul_assoc, ih hl, mul_assoc]

/-- Shifting an index range by one. -/
theorem map_range'_succ (s n : ℕ) : (List.range' s n).map (· + 1) = List.range' (s + 1) n := by
  have h := @List.map_add_range' 1 s n 1
  simpa [Nat.add_comm] using h

/-- `HJO.Braid.trainUp_mul_gen` for an inverted letter: the long train shifts `T_i^{-1}` to
`T_{i+1}^{-1}`. -/
theorem trainUp_mul_gen_inv (h : IsBraidSystem k T Tinv) {c d i : ℕ} (hd : 1 ≤ d) (hdi : d ≤ i)
    (hic : i + 1 < c) (hck : c ≤ k) :
    trainUp T Tinv d c * Tinv i = Tinv (i + 1) * trainUp T Tinv d c :=
  comm_shift_inv (h.mul_inv i (by omega) (by omega)) (h.inv_mul (i + 1) (by omega) (by omega))
    (trainUp_mul_gen h hd hdi hic hck)

/-- **A long word conjugates a short ascending word into its shift**, with the shift of each single
letter passed in: every letter of `T_a ⋯ T_{b-1}` moves to the next index, and the shifted word is
`T_{a+1} ⋯ T_b` because shifting an index range by one is `HJO.Braid.map_range'_succ`.

Stated for an arbitrary `W` rather than for a train, so that it serves both
`HJO.Braid.trainUp_long_mul_trainUp` and `HJO.Sweep.cmAscWord_word_shift`, whose long factor is
a word and not a train. -/
theorem mul_ascendingWord {T : ℕ → M} {W : M} {a b : ℕ} (hab : a ≤ b)
    (key : ∀ i, a ≤ i → i < b → W * T i = T (i + 1) * W) :
    W * ascendingWord T a b = ascendingWord T (a + 1) (b + 1) * W := by
  have h1 : ascendingWord T a b = ((List.range' a (b - a)).map T).prod := rfl
  have h2 : ascendingWord T (a + 1) (b + 1)
      = ((List.range' a (b - a)).map (T ∘ (· + 1))).prod := by
    rw [ascendingWord, show b + 1 - (a + 1) = b - a from by omega,
      ← map_range'_succ a (b - a), List.map_map]
  rw [h1, h2]
  refine mul_prod_shift fun j hj => ?_
  rw [List.mem_range'_1] at hj
  exact key j (by omega) (by omega)

/-- **The long ascending train conjugates a short train into its shift.** Every letter of
`T_{a↗b}` has an index in `[d, c-1)`, so `HJO.Braid.trainUp_mul_gen` applies to each of them — to
the inverted ones through `HJO.Braid.trainUp_mul_gen_inv` — and the shifted word is `T_{a+1↗b+1}`
because shifting an index range by one is `HJO.Braid.map_range'_succ`. -/
theorem trainUp_long_mul_trainUp (h : IsBraidSystem k T Tinv) {a b c d : ℕ} (hd : 1 ≤ d)
    (hda : d ≤ a) (hac : a < c) (hdb : d ≤ b) (hbc : b < c) (hck : c ≤ k) :
    trainUp T Tinv d c * trainUp T Tinv a b
      = trainUp T Tinv (a + 1) (b + 1) * trainUp T Tinv d c := by
  have key : ∀ i, d ≤ i → i + 1 < c →
      trainUp T Tinv d c * T i = T (i + 1) * trainUp T Tinv d c :=
    fun i h1 h2 => trainUp_mul_gen h hd h1 h2 hck
  have keyinv : ∀ i, d ≤ i → i + 1 < c →
      trainUp T Tinv d c * Tinv i = Tinv (i + 1) * trainUp T Tinv d c :=
    fun i h1 h2 => trainUp_mul_gen_inv h hd h1 h2 hck
  rcases Nat.lt_or_ge b a with hba | hba
  · have h1 : trainUp T Tinv a b = ((List.range' b (a - b)).reverse.map Tinv).prod := by
      rw [trainUp]
      split_ifs with hif
      · exact absurd hif (by omega)
      · rfl
    have h2 : trainUp T Tinv (a + 1) (b + 1)
        = ((List.range' (b + 1) (a - b)).reverse.map Tinv).prod := by
      rw [trainUp]
      split_ifs with hif
      · exact absurd hif (by omega)
      · rw [descendingWord, show a + 1 - (b + 1) = a - b from by omega]
    rw [h1, h2, ← map_range'_succ b (a - b), ← List.map_reverse, List.map_map]
    refine mul_prod_shift fun j hj => ?_
    rw [List.mem_reverse, List.mem_range'_1] at hj
    exact keyinv j (by omega) (by omega)
  · have h1 : trainUp T Tinv a b = ascendingWord T a b := by
      rw [trainUp]
      split_ifs with hif
      · rfl
      · exact absurd (show a ≤ b from hba) hif
    have h2 : trainUp T Tinv (a + 1) (b + 1) = ascendingWord T (a + 1) (b + 1) := by
      rw [trainUp]
      split_ifs with hif
      · rfl
      · exact absurd (show a + 1 ≤ b + 1 by omega) hif
    rw [h1, h2]
    exact mul_ascendingWord hba fun i h1' h2' => key i (by omega) (by omega)

/-- **Overtaking**, `HJO.Braid.trainUp_overtake`: for `d ≤ a, b < c`,
`T_{a↗b}T_{c↗d} = T_{c↗d}T_{a+1↗b+1}`.

`T_{c↗d}` is the two-sided inverse of the long train `T_{d↗c}` by
`HJO.Braid.trainUp_mul_trainUp_self`, so this is `HJO.Braid.trainUp_long_mul_trainUp` read from the
other side. -/
@[hjo "lem_train_overtake"]
theorem trainUp_overtake (h : IsBraidSystem k T Tinv) {a b c d : ℕ} (hd : 1 ≤ d) (hda : d ≤ a)
    (hac : a < c) (hdb : d ≤ b) (hbc : b < c) (hck : c ≤ k) :
    trainUp T Tinv a b * trainUp T Tinv c d
      = trainUp T Tinv c d * trainUp T Tinv (a + 1) (b + 1) :=
  conj_swap (trainUp_mul_trainUp_self h hd (by omega) (by omega) hck)
    (trainUp_mul_trainUp_self h (by omega) hck hd (by omega))
    (trainUp_long_mul_trainUp h hd hda hac hdb hbc hck)

end Monoid

/-! ### The arithmetic of the index shift -/

/-- **The shift never returns its own head**, `HJO.Braid.indexShift_ne_head`: for `x ≠ q`,
`σ_{p,q}(x) ≠ p`. This is what makes the collision bookkeeping of `HJO.Braid.collideIndex`
well founded — a shifted index is never the index that was shifted to. -/
@[hjo "lem_train_sigma_ne"]
theorem indexShift_ne_head {p q x : ℤ} (hx : x ≠ q) : indexShift p q x ≠ p := by
  unfold indexShift
  split_ifs <;> omega

/-- **The shift is symmetric in two adjacent arguments**: for `|x - y| = 1`,
  `σ_{p,x}(y) = σ_{p,y}(x)`. -/
@[hjo "lem_train_sigma_adjacent"]
theorem indexShift_comm_adjacent {p x y : ℤ} (hxy : |x - y| = 1) :
    indexShift p x y = indexShift p y x := by
  rw [abs_eq (by norm_num : (0 : ℤ) ≤ 1)] at hxy
  unfold indexShift
  split_ifs <;> omega

/-- **Moving the head of a shift by one**, `HJO.Braid.indexShift_congr_head`: for
`|p - p'| = 1` and `x` outside `{q, p, p'}`, `σ_{p,q}(x) = σ_{p',q}(x)`. -/
@[hjo "lem_train_sigma_head"]
theorem indexShift_congr_head {p p' q x : ℤ} (hpp : |p - p'| = 1) (hxq : x ≠ q) (hxp : x ≠ p)
    (hxp' : x ≠ p') : indexShift p q x = indexShift p' q x := by
  rw [abs_eq (by norm_num : (0 : ℤ) ≤ 1)] at hpp
  unfold indexShift
  split_ifs <;> omega

/-- **Moving the tail of a shift by one**, `HJO.Braid.indexShift_congr_tail`: for
`|q - q'| = 1` and `x` outside `{q, q'}`, `σ_{p,q}(x) = σ_{p,q'}(x)`. -/
@[hjo "lem_train_sigma_tail"]
theorem indexShift_congr_tail {p q q' x : ℤ} (hqq : |q - q'| = 1) (hxq : x ≠ q) (hxq' : x ≠ q') :
    indexShift p q x = indexShift p q' x := by
  rw [abs_eq (by norm_num : (0 : ℤ) ≤ 1)] at hqq
  unfold indexShift
  split_ifs <;> omega

end HJO.Braid

end
