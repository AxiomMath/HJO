/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Order.Field.Rat
public meta import HJO.Attr

/-! # Braid systems and their trains, abstractly

Mellit's Section 5 computes with *trains*: words in a braid system read either upwards or downwards
through a range of indices. This file is the abstract layer of that section. The letters live in an
arbitrary monoid, not on the module the rest of the section acts on, and nothing here knows what
they are; only the relations `T_i T_{i+1} T_i = T_{i+1} T_i T_{i+1}`, the far commutations, and the
existence of named inverses are used.

The train notation is Mellit's, with one simplification. He writes `T_{a↗b}`, `T_{a↘b}`, `T*_{a↗b}`
and `T*_{a↘b}`, where the star inverts each letter in place, and then extends the unstarred symbols
to `a > b` by declaring them to be the starred ones. Under `trainUp` and `trainDown` the starred
symbols are redundant: `T*_{a↗b}` is `T_{a↘b}` and `T*_{a↘b}` is `T_{a↗b}`, for all `a` and `b` and
both orders. Only the two unstarred families appear here, each a single closed formula rather than a
convention plus an extension, and `trainUp_inv_eq_trainDown` is exactly that redundancy.

## Main definitions

* `HJO.Braid.IsBraidSystem`: a braid system of rank `k` in a monoid, with named inverses.
* `HJO.Braid.trainUp`, `HJO.Braid.trainDown`: the ascending train `T_{a↗b}` and the descending
  train `T_{a↘b}`.
* `HJO.Braid.indexShift`: the index shift `σ_{a,b}` on the integers.
* `HJO.Braid.collideIndex`: the collision indices of an integer quadruple.
* `HJO.Braid.nextCrossing`: the next crossing `nx_θ` of the antidiagonal.

## Main results

* `HJO.Braid.IsBraidSystem.inverses`: the letterwise inverses of a braid system form one.
* `HJO.Braid.trainUp_inv_eq_trainDown`: inverting the letters exchanges the two families.
* `HJO.Braid.IsBraidSystem.braid_pair_pos`, `HJO.Braid.IsBraidSystem.braid_pair_neg`: the two
  signs of `T_j^ε T_{j+1} T_j = T_{j+1} T_j T_{j+1}^ε`.
* `HJO.Braid.trainUp_one_eq_prod`, `HJO.Braid.trainDown_one_eq_prod`: the two trains used
  throughout, `T_{1↗k} = T_1 T_2 ⋯ T_{k-1}` and `T_{k↘1} = T_{k-1} ⋯ T_1`, are what the
  closed formulas give.

## Implementation notes

The tuple `(T_1, …, T_{k-1})` is carried as a **total** function `T : ℕ → M` together with the rank
`k`, the relations being imposed only on `1 ≤ i ≤ k - 1`; the values outside that range are
unconstrained and no formula below is ever applied to one in a way that matters. `Fin (k - 1)` would
be closer to the letter of the definition and would put a bound proof and a coercion on every index
of every train, including the `a - 1` and `b - 1` that the two trains take and the `i + 1` of the
braid relation. On `ℕ` a train with `1 ≤ a, b ≤ k` reads only indices in `[min a b, max a b - 1]`,
which is contained in `[1, k - 1]`, so the totality costs no faithfulness.

The index bounds are written without truncated subtraction: `i + 1 ≤ k` for the usual
`i ≤ k - 1`, and `i + 2 ≤ k` for `i ≤ k - 2`. For `k ≥ 1` these say the same thing, and at `k = 1`,
where `k - 2` truncates to `0` on `ℕ`, both readings make the braid relation vacuous.

Invertibility is carried as a **named** two-sided inverse `Tinv : ℕ → M`, not as `IsUnit (T i)`:
`trainUp` and `trainDown` are words in the `T_i^{-1}` as much as in the `T_i`, so the inverse has to
be a function one can apply, and an existential would have to be skolemised before either
definition could be written at all. Assuming `Group M` would name the inverse too, and is not
available: the operators the rest of Section 5 builds are invertible one by one but do not form a
group, so `Monoid` together with `Tinv` is the structure that actually acts. The two cancellation
laws are therefore hypotheses, and the four lemmas `mul_mul_cancel_of_mul_eq_one`,
`right_inv_congr`, `mul_pair_mul_rev` and `mul_triple_mul_rev` are the group-free substitutes for
`inv_inv`, `mul_inv_rev` and cancellation.

Far commutation is one field, stated for `i + 2 ≤ j`, rather than the symmetric
`|i - j| ≥ 2`. The two are equivalent: the equation for the pair `(j, i)` is the equation for
`(i, j)` read backwards.

`trainUp` and `trainDown` take the two letter functions and no braid hypothesis, since the words are
defined whether or not the relations hold; `IsBraidSystem` enters only in the lemmas.

`indexShift` and `collideIndex` are over `ℤ`, as they are usually stated, and `nextCrossing` over
`ℚ`, which is where the levels live: `θ` is fixed by `θ(s + 1) = 1` for a positive
integer `s`, hence rational.

## References

Mellit's braid monoid and the train identities: the definitions `HJO.Braid.IsBraidSystem`,
`HJO.Braid.trainUp`, `HJO.Braid.trainDown`, `HJO.Braid.indexShift`, `HJO.Braid.collideIndex`,
`HJO.Braid.nextCrossing` and the lemmas `HJO.Braid.IsBraidSystem.inverses`,
`HJO.Braid.trainUp_inv_eq_trainDown`, `HJO.Braid.IsBraidSystem.braid_pair_pos`.
-/

@[expose] public section

namespace HJO.Braid

section Letters

variable {M : Type*} [Monoid M]

/-- In a monoid, a named right inverse cancels the factor to its left inside a product: if
`x * y = 1` then `x * (y * z) = z`. Without a group instance this replaces `inv_mul_cancel_left`. -/
theorem mul_mul_cancel_of_mul_eq_one {x y : M} (h : x * y = 1) (z : M) : x * (y * z) = z := by
  rw [← mul_assoc, h, one_mul]

/-- Two-sided inverses of equal elements agree: if `x * x' = 1`, `y' * y = 1` and `x = y`, then
`x' = y'`. This is how an identity between words is inverted with no group instance available. -/
theorem right_inv_congr {x x' y y' : M} (hx : x * x' = 1) (hy : y' * y = 1) (h : x = y) : x' = y' :=
  calc x' = y' * y * x' := by rw [hy, one_mul]
    _ = y' * (x * x') := by rw [mul_assoc, ← h]
    _ = y' := by rw [hx, mul_one]

/-- The reversed product of the named inverses is a right inverse of a product of two letters. -/
theorem mul_pair_mul_rev {a a' b b' : M} (ha : a * a' = 1) (hb : b * b' = 1) :
    a * b * (b' * a') = 1 := by
  simp only [mul_assoc]
  rw [mul_mul_cancel_of_mul_eq_one hb, ha]

/-- The reversed product of the named inverses is a right inverse of a product of three letters. -/
theorem mul_triple_mul_rev {a a' b b' c c' : M} (ha : a * a' = 1) (hb : b * b' = 1)
    (hc : c * c' = 1) : a * b * c * (c' * b' * a') = 1 := by
  simp only [mul_assoc]
  rw [mul_mul_cancel_of_mul_eq_one hc, mul_mul_cancel_of_mul_eq_one hb, ha]

/-- A braid system of rank `k` in the monoid `M`: a tuple `(T_1, …, T_{k-1})` of invertible elements
satisfying `T_i T_{i+1} T_i = T_{i+1} T_i T_{i+1}` for `1 ≤ i ≤ k - 2` and `T_i T_j = T_j T_i`
whenever `1 ≤ i, j ≤ k - 1` and `|i - j| ≥ 2`.

The tuple is a total function `T : ℕ → M`, the relations being imposed only for `1 ≤ i ≤ k - 1`,
and invertibility is the named two-sided inverse `Tinv`, because the trains below are words in the
inverses and need to apply them. Far commutation is stated once, for `i + 2 ≤ j`; the usual
`|i - j| ≥ 2` adds only the same equation read backwards. The bounds avoid truncated subtraction:
`i + 1 ≤ k` is `i ≤ k - 1` and `i + 2 ≤ k` is `i ≤ k - 2`, which agree with the usual bounds for
`k ≥ 1` and make the braid relation vacuous at `k = 1` under either reading. -/
@[hjo "def_braid_system"]
structure IsBraidSystem (k : ℕ) (T Tinv : ℕ → M) : Prop where
  /-- `Tinv i` is a right inverse of `T i`, for `1 ≤ i ≤ k - 1`. -/
  mul_inv : ∀ i, 1 ≤ i → i + 1 ≤ k → T i * Tinv i = 1
  /-- `Tinv i` is a left inverse of `T i`, for `1 ≤ i ≤ k - 1`. -/
  inv_mul : ∀ i, 1 ≤ i → i + 1 ≤ k → Tinv i * T i = 1
  /-- The braid relation, for `1 ≤ i ≤ k - 2`. -/
  braid : ∀ i, 1 ≤ i → i + 2 ≤ k → T i * T (i + 1) * T i = T (i + 1) * T i * T (i + 1)
  /-- Far commutation, for `1 ≤ i`, `i + 2 ≤ j` and `j ≤ k - 1`. -/
  far_comm : ∀ i j, 1 ≤ i → i + 2 ≤ j → j + 1 ≤ k → T i * T j = T j * T i

/-- The word `T_a T_{a+1} ⋯ T_{b-1}`, ascending through the half-open index range `[a, b)`, and the
empty product `1` when `b ≤ a`. Scaffolding for `trainUp` and `trainDown`, which is where the
case split lives. -/
def ascendingWord (T : ℕ → M) (a b : ℕ) : M := ((List.range' a (b - a)).map T).prod

/-- The word `T_{a-1} T_{a-2} ⋯ T_b`, descending through the half-open index range `[b, a)`, and
the empty product `1` when `a ≤ b`. Scaffolding for `trainUp` and `trainDown`. -/
def descendingWord (T : ℕ → M) (a b : ℕ) : M := ((List.range' b (a - b)).reverse.map T).prod

/-- The ascending train `T_{a↗b}` of the braid system `(T, Tinv)`: the word `T_a T_{a+1} ⋯ T_{b-1}`
when `a ≤ b`, and the word `T_{a-1}^{-1} T_{a-2}^{-1} ⋯ T_b^{-1}` when `a > b`, the empty product
being the identity, so that `T_{a↗a} = 1` (`trainUp_self`).

The side condition `1 ≤ a, b ≤ k` is not carried in the type; the formula is total, and
the rank enters only through the lemmas that use the relations. The inverses are the named `Tinv` of
`IsBraidSystem`, which is what makes the second branch a closed word rather than a convention. No
braid relation is used: this is a word in the letters. -/
@[hjo "def_train_up"]
def trainUp (T Tinv : ℕ → M) (a b : ℕ) : M :=
  if a ≤ b then ascendingWord T a b else descendingWord Tinv a b

/-- The descending train `T_{a↘b}` of the braid system `(T, Tinv)`: the word `T_{a-1} T_{a-2} ⋯ T_b`
when `a ≥ b`, and the word `T_a^{-1} T_{a+1}^{-1} ⋯ T_{b-1}^{-1}` when `a < b`, the empty product
being the identity, so that `T_{a↘a} = 1` (`trainDown_self`).

The order of the factors is part of the definition and the two branches are genuinely different
words, not reverses of one another. As with `trainUp`, the `1 ≤ a, b ≤ k` is not carried
in the type and the inverses are the named `Tinv`. -/
@[hjo "def_train_down"]
def trainDown (T Tinv : ℕ → M) (a b : ℕ) : M :=
  if b ≤ a then descendingWord T a b else ascendingWord Tinv a b

/-- A train that does not move is empty: `T_{a↗a} = 1`. -/
theorem trainUp_self (T Tinv : ℕ → M) (a : ℕ) : trainUp T Tinv a a = 1 := by
  simp [trainUp, ascendingWord]

/-- A train that does not move is empty: `T_{a↘a} = 1`. -/
theorem trainDown_self (T Tinv : ℕ → M) (a : ℕ) : trainDown T Tinv a a = 1 := by
  simp [trainDown, descendingWord]

/-- The boundary of the empty-product convention on the second branch of `HJO.Braid.trainUp`: at
`a = b + 1` the word `T_{a-1}^{-1} ⋯ T_b^{-1}` is the single letter `T_b^{-1}`, not the identity.
Together with `trainUp_self` this pins down where the first branch stops and the second starts. -/
theorem trainUp_succ_self (T Tinv : ℕ → M) (b : ℕ) : trainUp T Tinv (b + 1) b = Tinv b := by
  simp [trainUp, descendingWord]

/-- The boundary of the empty-product convention on the second branch of `HJO.Braid.trainDown`: at
`b = a + 1` the word `T_a^{-1} ⋯ T_{b-1}^{-1}` is the single letter `T_a^{-1}`. -/
theorem trainDown_self_succ (T Tinv : ℕ → M) (a : ℕ) : trainDown T Tinv a (a + 1) = Tinv a := by
  simp [trainDown, ascendingWord]

/-- The first of the two trains used throughout:
`T_{1↗k} = T_1 T_2 ⋯ T_{k-1}`. -/
theorem trainUp_one_eq_prod (T Tinv : ℕ → M) (k : ℕ) (hk : 1 ≤ k) :
    trainUp T Tinv 1 k = ((List.range' 1 (k - 1)).map T).prod := by
  simp [trainUp, ascendingWord, hk]

/-- The second of the two trains used throughout:
`T_{k↘1} = T_{k-1} T_{k-2} ⋯ T_1`, the letters in decreasing order of index. -/
theorem trainDown_one_eq_prod (T Tinv : ℕ → M) (k : ℕ) (hk : 1 ≤ k) :
    trainDown T Tinv k 1 = ((List.range' 1 (k - 1)).reverse.map T).prod := by
  simp [trainDown, descendingWord, hk]

/-- The ascending train from `1` to `4` is the word `T_1 T_2 T_3`: the general formula at a small
rank, checking the index range of `HJO.Braid.trainUp` against the definition by hand. -/
theorem trainUp_one_four (T Tinv : ℕ → M) : trainUp T Tinv 1 4 = T 1 * T 2 * T 3 := by
  simp [trainUp, ascendingWord, List.range', mul_assoc]

/-- The descending train from `4` to `1` is the word `T_3 T_2 T_1`: the general formula at a small
rank, checking the index range of `HJO.Braid.trainDown` against the definition by hand. -/
theorem trainDown_four_one (T Tinv : ℕ → M) : trainDown T Tinv 4 1 = T 3 * T 2 * T 1 := by
  simp [trainDown, descendingWord, List.range', mul_assoc]

variable {k : ℕ} {T Tinv : ℕ → M}

/-- The letterwise inverses of a braid system form a braid system of the same rank: if
`(T_1, …, T_{k-1})` is a braid system with inverses `(T_1^{-1}, …, T_{k-1}^{-1})`, then the pair
read the other way round is one too. Inverting an identity between words is `right_inv_congr`,
which stands in for `mul_inv_rev` in the absence of a group instance. -/
@[hjo "lem_train_inverses"]
theorem IsBraidSystem.inverses (h : IsBraidSystem k T Tinv) : IsBraidSystem k Tinv T where
  mul_inv i hi hik := h.inv_mul i hi hik
  inv_mul i hi hik := h.mul_inv i hi hik
  braid i hi hik := by
    have h1 : 1 ≤ i + 1 := by omega
    have hik0 : i + 1 ≤ k := by omega
    have hik1 : i + 1 + 1 ≤ k := by omega
    exact right_inv_congr
      (mul_triple_mul_rev (h.mul_inv i hi hik0) (h.mul_inv (i + 1) h1 hik1)
        (h.mul_inv i hi hik0))
      (mul_triple_mul_rev (h.inv_mul (i + 1) h1 hik1) (h.inv_mul i hi hik0)
        (h.inv_mul (i + 1) h1 hik1))
      (h.braid i hi hik)
  far_comm i j hi hij hjk := by
    have hj : 1 ≤ j := by omega
    have hik : i + 1 ≤ k := by omega
    exact (right_inv_congr (mul_pair_mul_rev (h.mul_inv i hi hik) (h.mul_inv j hj hjk))
      (mul_pair_mul_rev (h.inv_mul i hi hik) (h.inv_mul j hj hjk))
      (h.far_comm i j hi hij hjk)).symm

/-- Inverting the letters exchanges the two trains: the ascending train from `a` to `b` of the
braid system `(Tinv, T)` is the descending train `T_{a↘b}` of `(T, Tinv)`.

This is where Mellit's starred symbols go: `T*_{a↗b}`, his `T_{a↗b}` with each letter inverted, is
`T_{a↘b}`. The identity holds for all `a` and `b` and needs no braid relation, both definitions
being words: at `a = b` both sides are the empty product, and off the diagonal each side takes the
branch the other one does not. `IsBraidSystem.inverses` is what says the left-hand side is a train
of a braid system at all. -/
@[hjo "lem_train_dual"]
theorem trainUp_inv_eq_trainDown (T Tinv : ℕ → M) (a b : ℕ) :
    trainUp Tinv T a b = trainDown T Tinv a b := by
  unfold trainUp trainDown
  split_ifs with h1 h2 h2
  · obtain rfl : a = b := le_antisymm h1 h2
    simp [ascendingWord, descendingWord]
  · rfl
  · rfl
  · omega

/-- A generator conjugated by an adjacent pair, at `ε = 1`: `T_j T_{j+1} T_j = T_{j+1} T_j T_{j+1}`,
which is the braid relation of `HJO.Braid.IsBraidSystem` itself. Stated so that the two signs of
`T_j^ε T_{j+1} T_j = T_{j+1} T_j T_{j+1}^ε` are both present. -/
@[hjo "lem_train_braid_pair"]
theorem IsBraidSystem.braid_pair_pos (h : IsBraidSystem k T Tinv) {j : ℕ} (hj : 1 ≤ j)
    (hjk : j + 2 ≤ k) : T j * T (j + 1) * T j = T (j + 1) * T j * T (j + 1) :=
  h.braid j hj hjk

/-- A generator conjugated by an adjacent pair, at `ε = -1`:
`T_j^{-1} T_{j+1} T_j = T_{j+1} T_j T_{j+1}^{-1}` for `1 ≤ j ≤ k - 2`. The braid relation moves
`T_{j+1}^{-1}` across the pair, and the named left inverse of `T_j` then cancels; no group instance
is needed, only the two cancellation laws of `HJO.Braid.IsBraidSystem`. -/
@[hjo "lem_train_braid_pair"]
theorem IsBraidSystem.braid_pair_neg (h : IsBraidSystem k T Tinv) {j : ℕ} (hj : 1 ≤ j)
    (hjk : j + 2 ≤ k) : Tinv j * T (j + 1) * T j = T (j + 1) * T j * Tinv (j + 1) := by
  have hj1 : 1 ≤ j + 1 := by omega
  have hjk0 : j + 1 ≤ k := by omega
  have hjk1 : j + 1 + 1 ≤ k := by omega
  have key : T (j + 1) * T j = T j * T (j + 1) * T j * Tinv (j + 1) := by
    rw [h.braid j hj hjk, mul_assoc (T (j + 1) * T j) (T (j + 1)) (Tinv (j + 1)),
      h.mul_inv (j + 1) hj1 hjk1, mul_one]
  calc Tinv j * T (j + 1) * T j = Tinv j * (T (j + 1) * T j) := mul_assoc _ _ _
    _ = Tinv j * (T j * T (j + 1) * T j * Tinv (j + 1)) := by rw [key]
    _ = T (j + 1) * T j * Tinv (j + 1) := by
        simp only [mul_assoc]
        exact mul_mul_cancel_of_mul_eq_one (h.inv_mul j hj hjk0) _

end Letters

/-- The index shift `σ_{a,b}(c)`: it is `a` if `c = b`; `c + 1` if `c ≠ b` and `a ≤ c < b`; `c - 1`
if `c ≠ b` and `a ≥ c > b`; and `c` otherwise.

Mellit defines `σ_{a,b}(c)` only for `c ≠ b`, by the last three clauses. The first clause is a
convention that makes the map total, so that the collision indices of `collideIndex` need no side
condition; wherever Mellit's definition applies the convention is not used, and there the two
readings agree. The four clauses are
exhaustive by the final one, and mutually exclusive: the first is separated from the others by
`c = b`, and the second and third ask for `c < b` and `c > b` respectively. -/
@[hjo "def_train_sigma"]
def indexShift (a b c : ℤ) : ℤ :=
  if c = b then a
  else if a ≤ c ∧ c < b then c + 1
  else if a ≥ c ∧ c > b then c - 1
  else c

/-- The collision indices `(a', b', c', d')` of an integer quadruple `(a, b, c, d)`:
`c' = σ_{a,b}(c)`, `b' = σ_{d,c}(b)`, `a' = σ_{d,c'}(a)` and `d' = σ_{a',b'}(d)`.

The four components are written in the dependency order `c' → b' → a' → d'`, which is not the order
they are listed in: `a'` needs `c'`, and `d'` needs both `a'` and `b'`. Written out with
those dependencies expanded, the quadruple is the display of `collideIndex_eq`, which verifies
component by component that the expanded display and the definition agree. -/
@[hjo "def_train_collide_index"]
def collideIndex (a b c d : ℤ) : ℤ × ℤ × ℤ × ℤ :=
  let c' := indexShift a b c
  let b' := indexShift d c b
  let a' := indexShift d c' a
  let d' := indexShift a' b' d
  (a', b', c', d')

/-- The displayed quadruple for the collision indices, with the dependencies expanded:
`(σ_{d,σ_{a,b}(c)}(a), σ_{d,c}(b), σ_{a,b}(c), σ_{σ_{d,σ_{a,b}(c)}(a),σ_{d,c}(b)}(d))`. It agrees
with `collideIndex` component by component, so the expanded display and
`HJO.Braid.collideIndex` are the same definition. -/
theorem collideIndex_eq (a b c d : ℤ) :
    collideIndex a b c d =
      (indexShift d (indexShift a b c) a, indexShift d c b, indexShift a b c,
        indexShift (indexShift d (indexShift a b c) a) (indexShift d c b) d) := rfl

/-- The next crossing `nx_θ(x)`: `x - θ` if `x > θ`, and `x + 1 - θ` if `x < θ`. Following the line
of slope `s` downwards from the point of the antidiagonal recorded by `x` returns to the
antidiagonal at the point recorded by `nx_θ(x)`, where `θ(s + 1) = 1`.

The side conditions `0 < θ < 1`, `x ∈ (0, 1)` and `x ≠ θ` are not carried in the type.
The value at `x = θ` falls into the second branch and is `1`; it is meaningless, and the excluded
case is exactly the trajectory through the puncture. The conditions are supplied by the
special-braid data, whose admissibility is the requirement that every iterate appearing in it lies
in `(0, 1)` and differs from `θ`, so that no evaluation here is at the excluded argument. -/
@[hjo "def_train_next"]
def nextCrossing (θ x : ℚ) : ℚ := if θ < x then x - θ else x + 1 - θ

end HJO.Braid
