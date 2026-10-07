/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidData

/-! # The `z`-words, the position pair, and admissibility of a sequence of moves

Three items of the special-braid vocabulary that `HJO/Shuffle/BraidData.lean` does not
define: the `z`-words of the braid monoid — the mirror of the `y`-words under
`T̄_i ↦ T_i`, `y_1 ↦ z_1` — the pair of position tuples a piece of special-braid data starts and
ends at, and the condition on a sequence of elementary moves that makes every move in it defined.

## Main results

* `HJO.Braid.zWord`.
* `HJO.Braid.positionPair`.
* `HJO.Braid.IsAdmissibleMoveSeq`.
* `HJO.Braid.injective_of_isSpecialBraidData` and
  `HJO.Braid.injective_positionPair_snd_of_isSpecialBraidData` — the two position tuples of
  special-braid data have pairwise distinct entries, which is what the `HJO.Braid.entryRank` of
  `HJO.Braid.invIni` and `HJO.Braid.invFin` is read against.

## Implementation notes

**Truncated subtraction.** The final position tuple is `nx_θ^{α_i - 1}(v_i)`, and `α_i - 1` is a
subtraction in `ℕ`. `HJO.Braid.IsSpecialBraidData.one_le_mult` — the `α ∈ ℤ_{≥1}^k` —
makes it the honest predecessor wherever the definition is used; off that hypothesis `α_i = 0`
gives the zeroth iterate, that is `v_i` itself, rather than a step backwards. Nothing below reads
the definition without the hypothesis, and
`HJO.Braid.positionPair_snd_of_mult_eq_one` records the first value.

`zWord 0 = 1` is a junk value in the same way `HJO.Braid.yWord 0` is: the family starts
at `𝗓_1` and `F_0` is the trivial monoid, so there is no `𝗓_0`.

The admissibility of a sequence indexes the moves as `HJO.Braid.moveStage_succ` does: passing from
`w^{(r)}` to `w^{(r+1)}` advances the entry at `l[l.length - r - 1]`, which is `i_{l-r}` in the
`1`-based numbering of the sequence `(i_1, …, i_l)`.

## References

This file formalises `HJO.Braid.zWord`, `HJO.Braid.yWord`, `HJO.Braid.BraidMonoid`,
`HJO.Braid.positionPair`, `HJO.Braid.IsSpecialBraidData`, `HJO.Braid.IsAdmissibleMoveSeq`,
`HJO.Braid.moveStage` and `HJO.Braid.nextCrossing`.
-/

@[expose] public section

namespace HJO.Braid

/-! ### The `z`-words -/

/-- **The `z`-words `𝗓_1, …, 𝗓_k` of the braid monoid**: `𝗓_1 = z_1` and `𝗓_{i+1} = T_i 𝗓_i T_i`,
as elements of the free monoid on `HJO.Braid.Letter`.

This is `HJO.Braid.zWord`, the mirror of `HJO.Braid.yWord` under `T̄_i ↦ T_i` and
`y_1 ↦ z_1`. The asymmetry is part of the definition: the `y`-words are conjugated by the *inverse*
generators and the `z`-words by the generators themselves, which is what makes the last relation of
`HJO.Braid.BraidMonoid`, `𝗓_1 T_1 𝗒_1 T̄_1 = T̄_1 𝗒_1 T̄_1 𝗓_1`, say something.

`zWord 0` is the empty word, a junk value, exactly as `HJO.Braid.yWord 0` is. -/
@[hjo "def_braid_zword"]
def zWord : ℕ → FreeMonoid Letter
  | 0 => 1
  | 1 => FreeMonoid.of Letter.z1
  | (i + 2) =>
    FreeMonoid.of (Letter.T (i + 1)) * zWord (i + 1) * FreeMonoid.of (Letter.T (i + 1))

/-- `𝗓_1 = z_1`. -/
theorem zWord_one : zWord 1 = FreeMonoid.of Letter.z1 := rfl

/-- The recursion `𝗓_{i+1} = T_i 𝗓_i T_i`, for `i ≥ 1`. -/
theorem zWord_succ (i : ℕ) :
    zWord (i + 2) =
      FreeMonoid.of (Letter.T (i + 1)) * zWord (i + 1) * FreeMonoid.of (Letter.T (i + 1)) := rfl

/-- `𝗓_2 = T_1 z_1 T_1`, written out. -/
theorem zWord_two : zWord 2 = FreeMonoid.ofList [Letter.T 1, Letter.z1, Letter.T 1] := rfl

/-- `𝗓_3 = T_2 T_1 z_1 T_1 T_2`, written out. -/
theorem zWord_three :
    zWord 3 = FreeMonoid.ofList
      [Letter.T 2, Letter.T 1, Letter.z1, Letter.T 1, Letter.T 2] := rfl

/-- `𝗓_i` has length `2i - 1`, as `HJO.Braid.yWord` does. -/
theorem length_zWord (i : ℕ) : (zWord (i + 1)).length = 2 * i + 1 := by
  induction i with
  | zero => rfl
  | succ n ih =>
    rw [zWord_succ]
    simp only [FreeMonoid.length_mul, FreeMonoid.length_of] at ih ⊢
    omega

/-- **The `z`-words are the `y`-words with the letters exchanged.** Applying the monoid
homomorphism `T̄_i ↦ T_i`, `y_1 ↦ z_1` to `𝗒_i` gives `𝗓_i`, which is what "mirror" means and what
makes the two families the two halves of one alphabet. -/
theorem map_yWord_eq_zWord (i : ℕ) :
    FreeMonoid.map (fun c => match c with
      | Letter.T j => Letter.Tbar j
      | Letter.Tbar j => Letter.T j
      | Letter.y1 => Letter.z1
      | Letter.z1 => Letter.y1) (yWord i) = zWord i := by
  induction i using yWord.induct with
  | case1 => rfl
  | case2 => rfl
  | case3 n ih => rw [yWord_succ, zWord_succ, ← ih]; simp

/-! ### The position pair of special-braid data -/

/-- **The position pair of special-braid data.** `HJO.Braid.positionPair`: for
`(v, α)` of rank `k` at slope `s`, the pair `(v, (nx_θ^{α_i - 1}(v_i))_i)`, whose first member is
the *initial* position tuple and whose second is the *final* one.

The second component is the last of the `α_i` crossings the `i`-th component of the colouring makes
with the antidiagonal, `v_i` being the first; `HJO.Braid.invIni` and `HJO.Braid.invFin`
count the inversions of the two.

`α_i - 1` is `ℕ`-subtraction, honest under `HJO.Braid.IsSpecialBraidData.one_le_mult`; see the
module docstring. -/
@[hjo "def_braid_positions"]
def positionPair (θ : ℚ) {k : ℕ} (v : Fin k → ℚ) (α : Fin k → ℕ) : (Fin k → ℚ) × (Fin k → ℚ) :=
  (v, fun i => (nextCrossing θ)^[α i - 1] (v i))

/-- The initial position tuple is `v` itself. -/
@[simp]
theorem positionPair_fst (θ : ℚ) {k : ℕ} (v : Fin k → ℚ) (α : Fin k → ℕ) :
    (positionPair θ v α).1 = v := rfl

/-- The final position tuple reads off the `(α_i - 1)`-st iterate. -/
@[simp]
theorem positionPair_snd (θ : ℚ) {k : ℕ} (v : Fin k → ℚ) (α : Fin k → ℕ) (i : Fin k) :
    (positionPair θ v α).2 i = (nextCrossing θ)^[α i - 1] (v i) := rfl

/-- At a multiplicity of `1` the component crosses the antidiagonal once, and the final position of
that entry is its initial position. -/
theorem positionPair_snd_of_mult_eq_one {θ : ℚ} {k : ℕ} {v : Fin k → ℚ} {α : Fin k → ℕ}
    {i : Fin k} (h : α i = 1) : (positionPair θ v α).2 i = v i := by
  rw [positionPair_snd, h]
  rfl

/-- **The initial position tuple has pairwise distinct entries.** This is the `j = j' = 0` case of
the distinctness clause of `HJO.Braid.IsSpecialBraidData`, available because every multiplicity is
at least `1`. -/
theorem injective_of_isSpecialBraidData {s θ : ℚ} {k : ℕ} {v : Fin k → ℚ} {α : Fin k → ℕ}
    (h : IsSpecialBraidData s θ k v α) : Function.Injective v := by
  intro i i' hii
  exact (h.injective i i' 0 0 (h.one_le_mult i) (h.one_le_mult i') hii).1

/-- **The final position tuple has pairwise distinct entries.** The `α_i - 1` st iterate is one of
the `α_1 + ⋯ + α_k` numbers the distinctness clause of `HJO.Braid.IsSpecialBraidData` ranges over,
since `α_i - 1 < α_i` whenever `α_i ≥ 1`. -/
theorem injective_positionPair_snd_of_isSpecialBraidData {s θ : ℚ} {k : ℕ} {v : Fin k → ℚ}
    {α : Fin k → ℕ} (h : IsSpecialBraidData s θ k v α) :
    Function.Injective (positionPair θ v α).2 := by
  intro i i' hii
  have hi : α i - 1 < α i := by have := h.one_le_mult i; omega
  have hi' : α i' - 1 < α i' := by have := h.one_le_mult i'; omega
  exact (h.injective i i' _ _ hi hi' hii).1

/-! ### Admissibility of a sequence of moves -/

/-- **Admissible sequence.** `HJO.Braid.IsAdmissibleMoveSeq`: the sequence
`(i_1, …, i_l)` is admissible for `w` if the entries of `w^{(r)}` are pairwise distinct for every
`0 ≤ r ≤ l`, and the entry of `w^{(r)}` that the next move advances differs from `θ` for every
`0 ≤ r ≤ l - 1`.

The second clause is what makes each `HJO.Braid.nextCrossing` appearing in the sequence defined in
the sense, and the first is what makes each `HJO.Braid.entryRank` in `HJO.Braid.braidStep` a rank
of a tuple of pairwise distinct numbers, as that definition requires.

The advanced index is `l[l.length - r - 1]`, the `i_{l-r}`: the *last* index of the
sequence is the move performed *first*, and `HJO.Braid.moveStage_succ` is the recursion this
numbering makes true. -/
@[hjo "def_braid_admissible_seq"]
structure IsAdmissibleMoveSeq (θ : ℚ) {k : ℕ} (w : Fin k → ℚ) (l : List (Fin k)) : Prop where
  /-- Every intermediate tuple has pairwise distinct entries. -/
  injective_moveStage : ∀ r ≤ l.length, Function.Injective (moveStage θ w l r)
  /-- The entry each move advances is not the puncture. -/
  ne_theta : ∀ (r : ℕ) (hr : r < l.length),
    moveStage θ w l r (l[l.length - r - 1]'(by omega)) ≠ θ

/-- **The empty sequence is admissible** for a tuple with pairwise distinct entries: there is no
move to make, and the only stage is `w` itself. -/
theorem isAdmissibleMoveSeq_nil {θ : ℚ} {k : ℕ} {w : Fin k → ℚ} (hw : Function.Injective w) :
    IsAdmissibleMoveSeq θ w [] where
  injective_moveStage r hr := by
    rw [show r = 0 by simpa using hr, moveStage_zero]
    exact hw
  ne_theta r hr := absurd hr (by simp)

/-- The tuple an admissible sequence starts from has pairwise distinct entries: the `r = 0` clause
of `HJO.Braid.IsAdmissibleMoveSeq`. -/
theorem IsAdmissibleMoveSeq.injective_base {θ : ℚ} {k : ℕ} {w : Fin k → ℚ} {l : List (Fin k)}
    (h : IsAdmissibleMoveSeq θ w l) : Function.Injective w := by
  have := h.injective_moveStage 0 (Nat.zero_le _)
  rwa [moveStage_zero] at this

end HJO.Braid
