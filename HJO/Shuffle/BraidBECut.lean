/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidBEReconnect
public import HJO.Shuffle.BraidAppendOffset
public import HJO.Shuffle.BraidTypeDGapFree

/-! # Rule `BE`: the cut of the moving component

At a type-`B`/type-`E` pair of the level recursion three special braids meet: the braid `B` of the
lower colouring, of rank `k`, the braid `B''` of the type-`E` partner at the upper level, of rank
`k`, and the braid `B'` of the upper colouring, of rank `k + 1`. Mellit cuts the moving component
of `B` just before and just after its passage near the puncture into two common pieces, and finds

`B = w z_1ỹ_1 B̃_1`, `B'' = w y_1z_1 B̃_1`, `B' = φ_-(w) φ^*_+(T^*_{k↘1} B̃_1) T^*_{1↗k+1}`,

together with two inversion counts. `HJO.Mellit.braidValueColouring_sweepRecursionBEFloor_of_cut`
reduces the floored clause `(B,E)` of the recursion to exactly this statement about special braids,
the hypothesis `hcut`. This file proves it, and with it the floored clause.

The upper data `(v', α')` is the reference. By the type-`B` row of the dictionary the lower data is
`v' ∘ j.castSucc.succAbove`, rigidly shifted by the level drop `δ`, with the two adjacent
multiplicities `α'_j`, `α'_{j+1}` merged to `α'_j + α'_{j+1} + 1`; the type-`E` data is the same
tuple without the shift. So the merged strand of the lower data runs along the upper strand `j + 1`
to its end `X_1`, which lies just below the puncture, passes the puncture in two moves, and then
runs along the upper strand `j` from its start `X_2 = X_1 + 1 - 2θ`. Every other position is a
position of the upper data, and none of them lies between the puncture and the shift.

* In the lower data the two moves are a `ỹ` from rank `a_1` to rank `1` and a `z` from rank `1` to
  rank `a_2`; in the type-`E` data they are a `z` from rank `a_1` to rank `k` and a `ỹ` from rank
  `k` to rank `a_2`. Both read `T_{a_2↘1} (·) T_{1↗a_1}` with `z_1ỹ_1`, respectively `y_1z_1`, in
  between, and the rest of the two braids agree, the rigid shift crossing the puncture nowhere
  else.
* In the upper data the moves before the cut are made with the start `X_2` of the second piece
  fixed at the top of the tuple, which is Mellit's Proposition `phiplus2`
  (`HJO.Braid.braidWord_map_succAbove_mul_trainDown_one_of_le`), and the moves after the cut with
  the end `X_1` of the first piece fixed just below the puncture, which is Mellit's Proposition
  `phiminus` (`HJO.Braid.trainUp_top_mul_braidWord_map_succAbove`). The two conjugating trains
  collide into `T_{a_2↘1} T^*_{k+1↘a_1+1}` whichever of `X_1`, `X_2` is the larger.

## Main definitions

* `HJO.Braid.phiMinus` — Mellit's `φ_-`, the homomorphism `𝔹_k^+(𝕋_0) → 𝔹_{k+1}^+(𝕋_0)` reading a
  word of rank `k` at rank `k + 1`.

## Main results

* `HJO.Braid.phiMinus_toBraidMonoid`, `HJO.Braid.exists_inRank_word` — `φ_-` of an element is the
  rank-`(k + 1)` reading of any word of rank `k` naming it.
* `HJO.Braid.phiMinus_braidYtilde_mul_trainUp_top` — `φ_-(ỹ_a) T^*_{k+1↘i} = T^*_{k+1↘i} ỹ_{a+1}`.
* `HJO.Braid.trainUp_top_mul_braidStep_succAbove`,
  `HJO.Braid.trainUp_top_mul_braidWord_map_succAbove` — Mellit's Proposition `phiminus`, for one
  move and for a sequence of moves.
* `HJO.Braid.braidStep_pair_lower`, `HJO.Braid.braidStep_pair_typeE` — the local factors.
* `HJO.Braid.trainUp_top_mul_trainDown_one_of_le`, `HJO.Braid.trainUp_top_mul_trainDown_one_of_ge`
  — the reconnection of the two pieces.
* `HJO.Braid.specialBraid_cut`, `HJO.Braid.invFin_sub_invIni_cut` — the cut and Mellit's two
  inversion counts, for abstract special-braid data with the positions arranged as above.
* `HJO.Mellit.Isolates.cut_of_bePair` — the same for the data of colourings at a bracketed point.
* `HJO.Mellit.braidValueColouring_hcut` — the hypothesis `hcut` of
  `HJO.Mellit.braidValueColouring_sweepRecursionBEFloor_of_cut`.
* `HJO.Mellit.braidValueColouring_sweepRecursionBEFloor` — the floored clause `(B,E)` for the braid
  candidate.

## Implementation notes

`φ_-` is a homomorphism here, not only a reading of words: the assignment sends a letter out of
rank `k` to the identity, so it respects the out-of-rank family of the presentation as well as
Mellit's nine. It is not the identity on the commuting lifts — `φ_-(ỹ_k) = T̄_k ỹ_{k+1} T_k`
(`HJO.Braid.phiMinus_braidYtilde_self`) — and this is where Proposition `phiminus` does its work.

`HJO.Braid.specialBraid` fixes the order of the moves, the strand of largest index moving first. The
cut needs the moves of the merged strand split around the passage, so the move sequence is
rearranged: the braid of special-braid data depends only on how often each index moves
(`HJO.Braid.braidWord_perm_of_isSpecialBraidData`). The first piece consists of the moves of the
strands above `j` and the first `α'_{j+1} - 1` moves of the strand `j`, the second of the remaining
moves of the strand `j` and the moves of the strands below it.

Mellit places the fixed points of Propositions `phiminus` and `phiplus2` at the puncture and at the
start. The colourings put them only near there; what the two propositions read is that no moving
point lies between `X_1` and the puncture, and that every moving point lies below `X_2 + θ`. Both
follow from the isolation of the bracketed point, through
`HJO.Mellit.sameSide_levelDropShift_of_ne`: the only lattice point whose position the level drop
carries across the puncture is `(X, Y + 1)`, the end of the upper strand `j + 1`.

The statement of `HJO.Mellit.braidValueColouring_sweepRecursionBEFloor` carries `a < b`, which is
not used.

## References

* [A. Mellit, *Toric braids and (m,n)-parking functions*][mellit2016], §5: Propositions `phiminus`
  and `phiplus2`, the transformations B and E, and the proof of Theorem 5.8.
-/

@[expose] public section

namespace HJO.Braid

/-! ### Mellit's `φ_-` -/

/-- The assignment of Mellit's `φ_-` on the letters: a letter of rank `k` goes to the same letter
at rank `k + 1`, and a letter out of rank `k` to the identity, which is what makes the assignment
respect `HJO.Braid.BraidRel.out_of_rank`. -/
def phiMinusLetter (k : ℕ) (c : Letter) : BraidMonoid (k + 1) :=
  if Letter.InRank k c then toBraidMonoid (k + 1) (FreeMonoid.of c) else 1

/-- The assignment on the free monoid. -/
def phiMinusFree (k : ℕ) : FreeMonoid Letter →* BraidMonoid (k + 1) :=
  FreeMonoid.lift (phiMinusLetter k)

/-- `phiMinusFree k` sends a generator `c` of the free monoid to `phiMinusLetter k c`. -/
@[simp]
theorem phiMinusFree_of (k : ℕ) (c : Letter) :
    phiMinusFree k (FreeMonoid.of c) = phiMinusLetter k c := rfl

/-- A letter of rank `k` is a letter of rank `k + 1`. -/
theorem Letter.InRank.succ {k : ℕ} {c : Letter} (h : Letter.InRank k c) :
    Letter.InRank (k + 1) c := by
  cases c <;> simp only [Letter.InRank] at h ⊢ <;> omega

/-- **On a word of rank `k` the assignment is the word read at rank `k + 1`.** -/
theorem phiMinusFree_of_inRank {k : ℕ} {w : FreeMonoid Letter}
    (hw : ∀ c ∈ w.toList, Letter.InRank k c) :
    phiMinusFree k w = toBraidMonoid (k + 1) w := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | of_mul c w ih =>
    rw [map_mul, map_mul, ih fun d hd => hw d (by simp [hd]), phiMinusFree_of]
    simp only [phiMinusLetter, hw c (by simp), ite_true]

/-- The letters of `𝗒_i` are of rank `k` for `1 ≤ i ≤ k`. -/
theorem inRank_yWord {k : ℕ} : ∀ i, 1 ≤ i → i ≤ k → ∀ c ∈ (yWord i).toList, Letter.InRank k c
  | 1, _, hk, c, hc => by
    simp only [yWord_one, FreeMonoid.toList_of, List.mem_singleton] at hc
    subst hc
    simp only [Letter.InRank]
    omega
  | (i + 2), _, hk, c, hc => by
    simp only [yWord_succ, FreeMonoid.toList_mul, FreeMonoid.toList_of, List.mem_append,
      List.mem_singleton] at hc
    rcases hc with (rfl | hc) | rfl
    · simp only [Letter.InRank]; omega
    · exact inRank_yWord (i + 1) (by omega) (by omega) c hc
    · simp only [Letter.InRank]; omega

/-- The letters of `𝗓_i` are of rank `k` for `1 ≤ i ≤ k`. -/
theorem inRank_zWord {k : ℕ} : ∀ i, 1 ≤ i → i ≤ k → ∀ c ∈ (zWord i).toList, Letter.InRank k c
  | 1, _, hk, c, hc => by
    simp only [zWord_one, FreeMonoid.toList_of, List.mem_singleton] at hc
    subst hc
    simp only [Letter.InRank]
    omega
  | (i + 2), _, hk, c, hc => by
    simp only [zWord_succ, FreeMonoid.toList_mul, FreeMonoid.toList_of, List.mem_append,
      List.mem_singleton] at hc
    rcases hc with (rfl | hc) | rfl
    · simp only [Letter.InRank]; omega
    · exact inRank_zWord (i + 1) (by omega) (by omega) c hc
    · simp only [Letter.InRank]; omega

/-- **The assignment respects the presentation of `HJO.Braid.BraidMonoid`.** Every family but the
out-of-rank one relates two words of rank `k`, and the same family relates them at rank `k + 1`;
the out-of-rank letters go to the identity by construction. -/
theorem phiMinusFree_respects {k : ℕ} {x y : FreeMonoid Letter} (hrel : BraidRel k x y) :
    phiMinusFree k x = phiMinusFree k y := by
  have hT : ∀ i, 1 ≤ i → i + 1 ≤ k → ∀ c ∈ (FreeMonoid.of (Letter.T i)).toList,
      Letter.InRank k c := fun i hi hik c hc => by
    simp only [FreeMonoid.toList_of, List.mem_singleton] at hc
    subst hc
    exact ⟨hi, hik⟩
  have hTbar : ∀ i, 1 ≤ i → i + 1 ≤ k → ∀ c ∈ (FreeMonoid.of (Letter.Tbar i)).toList,
      Letter.InRank k c := fun i hi hik c hc => by
    simp only [FreeMonoid.toList_of, List.mem_singleton] at hc
    subst hc
    exact ⟨hi, hik⟩
  have hmul : ∀ u v : FreeMonoid Letter, (∀ c ∈ u.toList, Letter.InRank k c) →
      (∀ c ∈ v.toList, Letter.InRank k c) → ∀ c ∈ (u * v).toList, Letter.InRank k c :=
    fun u v hu hv c hc => by
      rw [FreeMonoid.toList_mul, List.mem_append] at hc
      exact hc.elim (hu c) (hv c)
  have hone : ∀ c ∈ (1 : FreeMonoid Letter).toList, Letter.InRank k c := by simp
  induction hrel with
  | mul_inv i hi hik =>
    rw [phiMinusFree_of_inRank (hmul _ _ (hT i hi hik) (hTbar i hi hik)),
      phiMinusFree_of_inRank hone]
    exact toBraidMonoid_eq_of_rel (BraidRel.mul_inv i hi (by omega))
  | inv_mul i hi hik =>
    rw [phiMinusFree_of_inRank (hmul _ _ (hTbar i hi hik) (hT i hi hik)),
      phiMinusFree_of_inRank hone]
    exact toBraidMonoid_eq_of_rel (BraidRel.inv_mul i hi (by omega))
  | braid i hi hik =>
    rw [phiMinusFree_of_inRank (hmul _ _ (hmul _ _ (hT i hi (by omega))
        (hT (i + 1) (by omega) (by omega))) (hT i hi (by omega))),
      phiMinusFree_of_inRank (hmul _ _ (hmul _ _ (hT (i + 1) (by omega) (by omega))
        (hT i hi (by omega))) (hT (i + 1) (by omega) (by omega)))]
    exact toBraidMonoid_eq_of_rel (BraidRel.braid i hi (by omega))
  | far_comm i j hi hij hjk =>
    rw [phiMinusFree_of_inRank (hmul _ _ (hT i hi (by omega)) (hT j (by omega) hjk)),
      phiMinusFree_of_inRank (hmul _ _ (hT j (by omega) hjk) (hT i hi (by omega)))]
    exact toBraidMonoid_eq_of_rel (BraidRel.far_comm i j hi hij (by omega))
  | yWord_comm_T i j hi hik hj hjk hne hne' =>
    rw [phiMinusFree_of_inRank (hmul _ _ (inRank_yWord i hi hik) (hT j hj hjk)),
      phiMinusFree_of_inRank (hmul _ _ (hT j hj hjk) (inRank_yWord i hi hik))]
    exact toBraidMonoid_eq_of_rel
      (BraidRel.yWord_comm_T i j hi (by omega) hj (by omega) hne hne')
  | zWord_comm_T i j hi hik hj hjk hne hne' =>
    rw [phiMinusFree_of_inRank (hmul _ _ (inRank_zWord i hi hik) (hT j hj hjk)),
      phiMinusFree_of_inRank (hmul _ _ (hT j hj hjk) (inRank_zWord i hi hik))]
    exact toBraidMonoid_eq_of_rel
      (BraidRel.zWord_comm_T i j hi (by omega) hj (by omega) hne hne')
  | yWord_comm i j hi hik hj hjk =>
    rw [phiMinusFree_of_inRank (hmul _ _ (inRank_yWord i hi hik) (inRank_yWord j hj hjk)),
      phiMinusFree_of_inRank (hmul _ _ (inRank_yWord j hj hjk) (inRank_yWord i hi hik))]
    exact toBraidMonoid_eq_of_rel (BraidRel.yWord_comm i j hi (by omega) hj (by omega))
  | zWord_comm i j hi hik hj hjk =>
    rw [phiMinusFree_of_inRank (hmul _ _ (inRank_zWord i hi hik) (inRank_zWord j hj hjk)),
      phiMinusFree_of_inRank (hmul _ _ (inRank_zWord j hj hjk) (inRank_zWord i hi hik))]
    exact toBraidMonoid_eq_of_rel (BraidRel.zWord_comm i j hi (by omega) hj (by omega))
  | zy hk2 =>
    have hz := inRank_zWord (k := k) 1 le_rfl (by omega)
    have hy := inRank_yWord (k := k) 1 le_rfl (by omega)
    have h1 := hT 1 le_rfl (by omega)
    have h1' := hTbar 1 le_rfl (by omega)
    rw [phiMinusFree_of_inRank (hmul _ _ (hmul _ _ (hmul _ _ hz h1) hy) h1'),
      phiMinusFree_of_inRank (hmul _ _ (hmul _ _ (hmul _ _ h1' hy) h1') hz)]
    exact toBraidMonoid_eq_of_rel (BraidRel.zy (by omega))
  | out_of_rank c hc =>
    rw [map_one, phiMinusFree_of]
    simp only [phiMinusLetter, hc, ite_false]

/-- **Mellit's homomorphism `φ_-`**: `𝔹_k^+(𝕋_0) → 𝔹_{k+1}^+(𝕋_0)`, sending `T_i`, `T̄_i`, `y_1`
and `z_1` of rank `k` to the same-named elements of rank `k + 1`. It is induced by the identity on
the words of rank `k`, `HJO.Braid.phiMinus_toBraidMonoid`. -/
def phiMinus (k : ℕ) : BraidMonoid k →* BraidMonoid (k + 1) :=
  Con.lift _ (phiMinusFree k)
    (Con.conGen_le.2 fun _x _y hxy => (Con.ker_rel _).2 (phiMinusFree_respects hxy))

/-- `φ_-` sends the class of a word `x` of rank `k` to `phiMinusFree k x`. -/
@[simp]
theorem phiMinus_apply (k : ℕ) (x : FreeMonoid Letter) :
    phiMinus k (toBraidMonoid k x) = phiMinusFree k x :=
  Con.lift_coe _ _

/-- **`φ_-` reads a word of rank `k` at rank `k + 1`.** -/
theorem phiMinus_toBraidMonoid {k : ℕ} {w : FreeMonoid Letter}
    (hw : ∀ c ∈ w.toList, Letter.InRank k c) :
    phiMinus k (toBraidMonoid k w) = toBraidMonoid (k + 1) w := by
  rw [phiMinus_apply, phiMinusFree_of_inRank hw]

/-- **Every element of `𝔹_k^+(𝕋_0)` is named by a word of rank `k`**: the letters out of rank name
the identity and may be deleted. -/
theorem exists_inRank_word {k : ℕ} (x : BraidMonoid k) :
    ∃ w : FreeMonoid Letter, (∀ c ∈ w.toList, Letter.InRank k c) ∧ toBraidMonoid k w = x := by
  obtain ⟨w, rfl⟩ := toBraidMonoid_surjective k x
  induction w using FreeMonoid.inductionOn' with
  | one => exact ⟨1, by simp, rfl⟩
  | of_mul c w ih =>
    obtain ⟨w', hw', hw'eq⟩ := ih
    by_cases hc : Letter.InRank k c
    · refine ⟨FreeMonoid.of c * w', fun d hd => ?_, by rw [map_mul, map_mul, hw'eq]⟩
      rw [FreeMonoid.toList_mul, FreeMonoid.toList_of, List.singleton_append, List.mem_cons] at hd
      rcases hd with rfl | hd
      · exact hc
      · exact hw' d hd
    · refine ⟨w', hw', ?_⟩
      rw [map_mul, toBraidMonoid_eq_of_rel (BraidRel.out_of_rank c hc), map_one, one_mul, hw'eq]

/-- `φ_-(T_i) = T_i`. -/
theorem phiMinus_braidGenT {k i : ℕ} (hi : 1 ≤ i) (hik : i + 1 ≤ k) :
    phiMinus k (braidGenT k i) = braidGenT (k + 1) i :=
  phiMinus_toBraidMonoid fun c hc => by
    simp only [FreeMonoid.toList_of, List.mem_singleton] at hc
    subst hc
    exact ⟨hi, hik⟩

/-- `φ_-(T̄_i) = T̄_i`. -/
theorem phiMinus_braidGenTinv {k i : ℕ} (hi : 1 ≤ i) (hik : i + 1 ≤ k) :
    phiMinus k (braidGenTinv k i) = braidGenTinv (k + 1) i :=
  phiMinus_toBraidMonoid fun c hc => by
    simp only [FreeMonoid.toList_of, List.mem_singleton] at hc
    subst hc
    exact ⟨hi, hik⟩

/-- `φ_-(y_i) = y_i` for `1 ≤ i ≤ k`. -/
theorem phiMinus_braidGenY {k i : ℕ} (hi : 1 ≤ i) (hik : i ≤ k) :
    phiMinus k (braidGenY k i) = braidGenY (k + 1) i :=
  phiMinus_toBraidMonoid (inRank_yWord i hi hik)

/-- `φ_-(z_i) = z_i` for `1 ≤ i ≤ k`. -/
theorem phiMinus_braidGenZ {k i : ℕ} (hi : 1 ≤ i) (hik : i ≤ k) :
    phiMinus k (braidGenZ k i) = braidGenZ (k + 1) i :=
  phiMinus_toBraidMonoid (inRank_zWord i hi hik)

/-- A homomorphism carries an ascending word letter by letter. -/
theorem map_ascendingWord_same {M N : Type*} [Monoid M] [Monoid N] (f : M →* N) (T : ℕ → M)
    (T' : ℕ → N) {a b : ℕ} (hT : ∀ j, a ≤ j → j < b → f (T j) = T' j) :
    f (ascendingWord T a b) = ascendingWord T' a b := by
  rw [ascendingWord, ascendingWord, map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun j hj => ?_
  rw [List.mem_range'_1] at hj
  exact hT j hj.1 (by omega)

/-- A homomorphism carries a descending word letter by letter. -/
theorem map_descendingWord_same {M N : Type*} [Monoid M] [Monoid N] (f : M →* N) (T : ℕ → M)
    (T' : ℕ → N) {a b : ℕ} (hT : ∀ j, b ≤ j → j < a → f (T j) = T' j) :
    f (descendingWord T a b) = descendingWord T' a b := by
  rw [descendingWord, descendingWord, map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun j hj => ?_
  rw [List.mem_reverse, List.mem_range'_1] at hj
  exact hT j hj.1 (by omega)

/-- `φ_-` carries a descending train of rank `k` to the same train of rank `k + 1`. -/
theorem phiMinus_braidTrainDown {k a b : ℕ} (ha : 1 ≤ a) (hak : a ≤ k) (hb : 1 ≤ b)
    (hbk : b ≤ k) : phiMinus k (braidTrainDown k a b) = braidTrainDown (k + 1) a b := by
  rw [braidTrainDown, braidTrainDown, trainDown, trainDown]
  split_ifs
  · exact map_descendingWord_same _ _ _ fun j hj hja => phiMinus_braidGenT (by omega) (by omega)
  · exact map_ascendingWord_same _ _ _ fun j hj hjb =>
      phiMinus_braidGenTinv (by omega) (by omega)

/-- `φ_-` carries an ascending train of rank `k` to the same train of rank `k + 1`. -/
theorem phiMinus_braidTrainUp {k a b : ℕ} (ha : 1 ≤ a) (hak : a ≤ k) (hb : 1 ≤ b)
    (hbk : b ≤ k) : phiMinus k (braidTrainUp k a b) = braidTrainUp (k + 1) a b := by
  rw [braidTrainUp, braidTrainUp, trainUp, trainUp]
  split_ifs
  · exact map_ascendingWord_same _ _ _ fun j hj hjb => phiMinus_braidGenT (by omega) (by omega)
  · exact map_descendingWord_same _ _ _ fun j hj hja =>
      phiMinus_braidGenTinv (by omega) (by omega)

/-- **`φ_-(ỹ_a) = T_{a↘1}T_{1↗k}y_kT_{k↗a}` read at rank `k + 1`**: the commuting lift of rank `k`
is not the commuting lift of rank `k + 1`, its loop stopping one strand short. -/
theorem phiMinus_braidYtilde {k a : ℕ} (ha : 1 ≤ a) (hak : a ≤ k) :
    phiMinus k (braidYtilde k a)
      = braidTrainDown (k + 1) a 1 * braidTrainUp (k + 1) 1 k * braidGenY (k + 1) k *
          braidTrainUp (k + 1) k a := by
  rw [braidYtilde, map_mul, map_mul, map_mul, phiMinus_braidTrainDown ha hak le_rfl (by omega),
    phiMinus_braidTrainUp le_rfl (by omega) (by omega) le_rfl,
    phiMinus_braidGenY (by omega) le_rfl, phiMinus_braidTrainUp (by omega) le_rfl ha hak]


/-! ### The trains of Mellit's Proposition `phiminus`

Throughout, `T^*_{k+1↘i}` is `HJO.Braid.braidTrainUp (k + 1) (k + 1) i`, the word
`T̄_k T̄_{k-1} ⋯ T̄_i`, which is the identity at `i = k + 1`. -/

section PhiMinusTrains

variable {k : ℕ}

/-- A generator commuting with every letter `T̄_j`, `b ≤ j < a`, commutes with `T_{a↗b}`. -/
theorem comm_trainUp_of_le {M : Type*} [Monoid M] {T Tinv : ℕ → M} {x : M} {a b : ℕ}
    (hba : b ≤ a) (hT : ∀ j, b ≤ j → j < a → x * Tinv j = Tinv j * x) :
    x * trainUp T Tinv a b = trainUp T Tinv a b * x := by
  rw [trainUp]
  split_ifs with hab
  · have : a = b := le_antisymm hab hba
    subst this
    simp [ascendingWord]
  · rw [descendingWord]
    refine mul_prod_comm fun y hy => ?_
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
    rw [List.mem_reverse, List.mem_range'_1] at hj
    exact hT j hj.1 (by omega)

/-- `z_a` commutes with `T^*_{k+1↘i}` once `a < i`: every letter of the train sits at least two
places above `a - 1`. -/
theorem braidGenZ_comm_trainUp_top {a i : ℕ} (ha : 1 ≤ a) (hai : a < i) (hik : i ≤ k + 1) :
    braidGenZ (k + 1) a * braidTrainUp (k + 1) (k + 1) i
      = braidTrainUp (k + 1) (k + 1) i * braidGenZ (k + 1) a := by
  refine comm_trainUp_of_le hik fun j hj hjk => ?_
  refine comm_inv_right (braidGenT_mul_inv (by omega) (by omega))
    (braidGenT_inv_mul (by omega) (by omega)) ?_
  exact braidGenZ_comm_T ha (by omega) (by omega) (by omega) (by omega) (by omega)

/-- The second clause of `HJO.Braid.indexShift`. -/
theorem indexShift_of_lt_of_le {p q x : ℤ} (hpx : p ≤ x) (hxq : x < q) :
    indexShift p q x = x + 1 := by
  unfold indexShift
  split_ifs <;> omega

/-- The third clause of `HJO.Braid.indexShift`. -/
theorem indexShift_of_gt_of_le {p q x : ℤ} (hxp : x ≤ p) (hqx : q < x) :
    indexShift p q x = x - 1 := by
  unfold indexShift
  split_ifs <;> omega

/-- The last clause of `HJO.Braid.indexShift`, below both indices. -/
theorem indexShift_of_lt_of_lt {p q x : ℤ} (hxp : x < p) (hxq : x < q) :
    indexShift p q x = x := by
  unfold indexShift
  split_ifs <;> omega

/-- The last clause of `HJO.Braid.indexShift`, above both indices. -/
theorem indexShift_of_gt_of_gt {p q x : ℤ} (hpx : p < x) (hqx : q < x) :
    indexShift p q x = x := by
  unfold indexShift
  split_ifs <;> omega

/-- `(z1)`: `T^*_{k+1↘i}` commutes with `T_{a'↘a}` when both `a, a' < i`. -/
theorem trainUp_top_mul_trainDown_of_lt {a a' i : ℕ} (ha : 1 ≤ a) (ha' : 1 ≤ a') (hai : a < i)
    (ha'i : a' < i) (hik : i ≤ k + 1) :
    braidTrainUp (k + 1) (k + 1) i * braidTrainDown (k + 1) a' a
      = braidTrainDown (k + 1) a' a * braidTrainUp (k + 1) (k + 1) i := by
  have hcol : collideIndex ((k + 1 : ℕ) : ℤ) (i : ℤ) (a' : ℤ) (a : ℤ)
      = (((k + 1 : ℕ) : ℤ), (i : ℤ), (a' : ℤ), (a : ℤ)) := by
    have h1 : indexShift ((k + 1 : ℕ) : ℤ) (i : ℤ) (a' : ℤ) = a' :=
      indexShift_of_lt_of_lt (by push_cast; omega) (by omega)
    have h2 : indexShift (a : ℤ) (a' : ℤ) (i : ℤ) = i := by
      rcases lt_or_ge a a' with h | h
      · exact indexShift_of_gt_of_gt (by omega) (by omega)
      · exact indexShift_of_gt_of_gt (by omega) (by omega)
    have h3 : indexShift (a : ℤ) (a' : ℤ) ((k + 1 : ℕ) : ℤ) = ((k + 1 : ℕ) : ℤ) :=
      indexShift_of_gt_of_gt (by push_cast; omega) (by push_cast; omega)
    have h4 : indexShift ((k + 1 : ℕ) : ℤ) (i : ℤ) (a : ℤ) = a :=
      indexShift_of_lt_of_lt (by push_cast; omega) (by omega)
    rw [collideIndex_eq, h1, h2, h3, h4]
  exact (isBraidSystem_braidGenT (k + 1)).collide (by omega) le_rfl (by omega) hik ha'
    (by omega) ha (by omega) (by omega) hcol

/-- `(z2)`: `T^*_{k+1↘i-1} T_{a'+1↘a} = T_{a'↘a} T^*_{k+1↘i}` when `a < i ≤ a' + 1`. -/
theorem trainUp_top_pred_mul_trainDown {a a' i : ℕ} (ha : 1 ≤ a) (hai : a < i)
    (hia' : i ≤ a' + 1) (ha'k : a' ≤ k) :
    braidTrainUp (k + 1) (k + 1) (i - 1) * braidTrainDown (k + 1) (a' + 1) a
      = braidTrainDown (k + 1) a' a * braidTrainUp (k + 1) (k + 1) i := by
  have hcol : collideIndex ((k + 1 : ℕ) : ℤ) ((i - 1 : ℕ) : ℤ) ((a' + 1 : ℕ) : ℤ) (a : ℤ)
      = (((k + 1 : ℕ) : ℤ), (i : ℤ), (a' : ℤ), (a : ℤ)) := by
    have h1 : indexShift ((k + 1 : ℕ) : ℤ) ((i - 1 : ℕ) : ℤ) ((a' + 1 : ℕ) : ℤ) = a' := by
      rw [indexShift_of_gt_of_le (by omega) (by omega)]
      push_cast
      ring
    have h2 : indexShift (a : ℤ) ((a' + 1 : ℕ) : ℤ) ((i - 1 : ℕ) : ℤ) = i := by
      rw [indexShift_of_lt_of_le (by omega) (by omega)]
      omega
    have h3 : indexShift (a : ℤ) (a' : ℤ) ((k + 1 : ℕ) : ℤ) = ((k + 1 : ℕ) : ℤ) :=
      indexShift_of_gt_of_gt (by push_cast; omega) (by push_cast; omega)
    have h4 : indexShift ((k + 1 : ℕ) : ℤ) (i : ℤ) (a : ℤ) = a :=
      indexShift_of_lt_of_lt (by push_cast; omega) (by omega)
    rw [collideIndex_eq, h1, h2, h3, h4]
  exact (isBraidSystem_braidGenT (k + 1)).collide (by omega) le_rfl (by omega) (by omega)
    (by omega) (by omega) ha (by omega) (by omega) hcol

/-- `(y1)`: `T^*_{k+1↘i+1} T_{a'↘a+1} = T_{a'↘a} T^*_{k+1↘i}` when `a' ≤ i ≤ a ≤ k`. -/
theorem trainUp_top_succ_mul_trainDown {a a' i : ℕ} (hi : 1 ≤ i) (ha' : 1 ≤ a') (ha'i : a' ≤ i)
    (hia : i ≤ a) (hak : a ≤ k) :
    braidTrainUp (k + 1) (k + 1) (i + 1) * braidTrainDown (k + 1) a' (a + 1)
      = braidTrainDown (k + 1) a' a * braidTrainUp (k + 1) (k + 1) i := by
  have h := isBraidSystem_braidGenT (k + 1)
  rcases lt_or_eq_of_le hak with hak' | rfl
  · have hcol : collideIndex ((k + 1 : ℕ) : ℤ) ((i + 1 : ℕ) : ℤ) (a' : ℤ) ((a + 1 : ℕ) : ℤ)
        = (((k + 1 : ℕ) : ℤ), (i : ℤ), (a' : ℤ), (a : ℤ)) := by
      have h1 : indexShift ((k + 1 : ℕ) : ℤ) ((i + 1 : ℕ) : ℤ) (a' : ℤ) = a' :=
        indexShift_of_lt_of_lt (by push_cast; omega) (by push_cast; omega)
      have h2 : indexShift ((a + 1 : ℕ) : ℤ) (a' : ℤ) ((i + 1 : ℕ) : ℤ) = i := by
        rw [indexShift_of_gt_of_le (by push_cast; omega) (by push_cast; omega)]
        push_cast
        ring
      have h3 : indexShift ((a + 1 : ℕ) : ℤ) (a' : ℤ) ((k + 1 : ℕ) : ℤ) = ((k + 1 : ℕ) : ℤ) :=
        indexShift_of_gt_of_gt (by push_cast; omega) (by push_cast; omega)
      have h4 : indexShift ((k + 1 : ℕ) : ℤ) (i : ℤ) ((a + 1 : ℕ) : ℤ) = a := by
        rw [indexShift_of_gt_of_le (by push_cast; omega) (by push_cast; omega)]
        push_cast
        ring
      rw [collideIndex_eq, h1, h2, h3, h4]
    exact h.collide (by omega) le_rfl (by omega) (by omega) ha' (by omega) (by omega) (by omega)
      (by omega) hcol
  · have hcol : collideIndex ((a + 1 : ℕ) : ℤ) ((i + 1 : ℕ) : ℤ) (a' : ℤ) ((a + 1 : ℕ) : ℤ)
        = ((a : ℤ), (i : ℤ), (a' : ℤ), ((a + 1 : ℕ) : ℤ)) := by
      have h1 : indexShift ((a + 1 : ℕ) : ℤ) ((i + 1 : ℕ) : ℤ) (a' : ℤ) = a' :=
        indexShift_of_lt_of_lt (by push_cast; omega) (by push_cast; omega)
      have h2 : indexShift ((a + 1 : ℕ) : ℤ) (a' : ℤ) ((i + 1 : ℕ) : ℤ) = i := by
        rw [indexShift_of_gt_of_le (by push_cast; omega) (by push_cast; omega)]
        push_cast
        ring
      have h3 : indexShift ((a + 1 : ℕ) : ℤ) (a' : ℤ) ((a + 1 : ℕ) : ℤ) = a := by
        rw [indexShift_of_gt_of_le (by push_cast; omega) (by push_cast; omega)]
        push_cast
        ring
      have h4 : indexShift (a : ℤ) (i : ℤ) ((a + 1 : ℕ) : ℤ) = ((a + 1 : ℕ) : ℤ) :=
        indexShift_of_gt_of_gt (by push_cast; omega) (by push_cast; omega)
      rw [collideIndex_eq, h1, h2, h3, h4]
    rw [h.collide (by omega) le_rfl (by omega) (by omega) ha' (by omega) (by omega) (by omega)
      (by omega) hcol]
    -- `T_{a'↘a+1} T_{a↗i} = T_{a'↘a} T_{a+1↗i}`: glue the letter `T̄_a` across
    rw [← trainDown_mul_trainDown h ha' (by omega) (by omega : 1 ≤ a) (by omega) (by omega)
        le_rfl, trainDown_self_succ, mul_assoc,
      ← trainUp_succ_self (braidGenT (a + 1)) (braidGenTinv (a + 1)) a,
      trainUp_mul_trainUp h (a := a + 1) (b := a) (c := i) (by omega) le_rfl (by omega)
        (by omega) hi (by omega)]

/-- `(y2)`: `T^*_{k+1↘i} T_{a'+1↘a+1} = T_{a'↘a} T^*_{k+1↘i}` when `i ≤ a' ≤ a ≤ k`. -/
theorem trainUp_top_mul_trainDown_succ {a a' i : ℕ} (hi : 1 ≤ i) (hia' : i ≤ a') (ha'a : a' ≤ a)
    (hak : a ≤ k) :
    braidTrainUp (k + 1) (k + 1) i * braidTrainDown (k + 1) (a' + 1) (a + 1)
      = braidTrainDown (k + 1) a' a * braidTrainUp (k + 1) (k + 1) i := by
  have h := isBraidSystem_braidGenT (k + 1)
  rcases lt_or_eq_of_le hak with hak' | rfl
  · have hcol : collideIndex ((k + 1 : ℕ) : ℤ) (i : ℤ) ((a' + 1 : ℕ) : ℤ) ((a + 1 : ℕ) : ℤ)
        = (((k + 1 : ℕ) : ℤ), (i : ℤ), (a' : ℤ), (a : ℤ)) := by
      have h1 : indexShift ((k + 1 : ℕ) : ℤ) (i : ℤ) ((a' + 1 : ℕ) : ℤ) = a' := by
        rw [indexShift_of_gt_of_le (by push_cast; omega) (by push_cast; omega)]
        push_cast
        ring
      have h2 : indexShift ((a + 1 : ℕ) : ℤ) ((a' + 1 : ℕ) : ℤ) (i : ℤ) = i :=
        indexShift_of_lt_of_lt (by push_cast; omega) (by push_cast; omega)
      have h3 : indexShift ((a + 1 : ℕ) : ℤ) (a' : ℤ) ((k + 1 : ℕ) : ℤ) = ((k + 1 : ℕ) : ℤ) :=
        indexShift_of_gt_of_gt (by push_cast; omega) (by push_cast; omega)
      have h4 : indexShift ((k + 1 : ℕ) : ℤ) (i : ℤ) ((a + 1 : ℕ) : ℤ) = a := by
        rw [indexShift_of_gt_of_le (by push_cast; omega) (by push_cast; omega)]
        push_cast
        ring
      rw [collideIndex_eq, h1, h2, h3, h4]
    exact h.collide (by omega) le_rfl hi (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) hcol
  · have hcol : collideIndex ((a + 1 : ℕ) : ℤ) (i : ℤ) ((a' + 1 : ℕ) : ℤ) ((a + 1 : ℕ) : ℤ)
        = ((a : ℤ), (i : ℤ), (a' : ℤ), ((a + 1 : ℕ) : ℤ)) := by
      have h1 : indexShift ((a + 1 : ℕ) : ℤ) (i : ℤ) ((a' + 1 : ℕ) : ℤ) = a' := by
        rw [indexShift_of_gt_of_le (by push_cast; omega) (by push_cast; omega)]
        push_cast
        ring
      have h2 : indexShift ((a + 1 : ℕ) : ℤ) ((a' + 1 : ℕ) : ℤ) (i : ℤ) = i :=
        indexShift_of_lt_of_lt (by push_cast; omega) (by push_cast; omega)
      have h3 : indexShift ((a + 1 : ℕ) : ℤ) (a' : ℤ) ((a + 1 : ℕ) : ℤ) = a := by
        rw [indexShift_of_gt_of_le (by push_cast; omega) (by push_cast; omega)]
        push_cast
        ring
      have h4 : indexShift (a : ℤ) (i : ℤ) ((a + 1 : ℕ) : ℤ) = ((a + 1 : ℕ) : ℤ) :=
        indexShift_of_gt_of_gt (by push_cast; omega) (by push_cast; omega)
      rw [collideIndex_eq, h1, h2, h3, h4]
    rw [h.collide (by omega) le_rfl hi (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) hcol]
    rw [← trainDown_mul_trainDown h (by omega : 1 ≤ a') (by omega) (by omega : 1 ≤ a) (by omega)
        (by omega) le_rfl, trainDown_self_succ, mul_assoc,
      ← trainUp_succ_self (braidGenT (a + 1)) (braidGenTinv (a + 1)) a,
      trainUp_mul_trainUp h (a := a + 1) (b := a) (c := i) (by omega) le_rfl (by omega)
        (by omega) hi (by omega)]

/-- **`φ_-(ỹ_k) = T̄_k ỹ_{k+1} T_k`**, Mellit's own reading of `φ_-` on the top commuting lift. -/
theorem phiMinus_braidYtilde_self (hk : 1 ≤ k) :
    phiMinus k (braidYtilde k k)
      = braidGenTinv (k + 1) k * braidYtilde (k + 1) (k + 1) * braidGenT (k + 1) k := by
  have h := isBraidSystem_braidGenT (k + 1)
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have eD : braidTrainDown (m + 1 + 1) (m + 1 + 1) 1
      = braidGenT (m + 1 + 1) (m + 1) * braidTrainDown (m + 1 + 1) (m + 1) 1 := by
    rw [← trainDown_succ_self (braidGenT (m + 1 + 1)) (braidGenTinv (m + 1 + 1)) (m + 1)]
    exact (trainDown_mul_trainDown h (a := m + 1 + 1) (b := m + 1) (c := 1) (by omega) le_rfl
      (by omega) (by omega) le_rfl (by omega)).symm
  have eU : braidTrainUp (m + 1 + 1) 1 (m + 1 + 1)
      = braidTrainUp (m + 1 + 1) 1 (m + 1) * braidGenT (m + 1 + 1) (m + 1) := by
    rw [← trainUp_self_succ (braidGenT (m + 1 + 1)) (braidGenTinv (m + 1 + 1)) (m + 1)]
    exact (trainUp_mul_trainUp h (a := 1) (b := m + 1) (c := m + 1 + 1) le_rfl (by omega)
      (by omega) (by omega) (by omega) le_rfl).symm
  rw [phiMinus_braidYtilde hk le_rfl, braidTrainUp_self, mul_one, braidYtilde_self, eD, eU,
    braidGenY_succ (m + 1 + 1) m]
  have e1 : braidGenTinv (m + 1 + 1) (m + 1) * braidGenT (m + 1 + 1) (m + 1) = 1 :=
    braidGenT_inv_mul (by omega) le_rfl
  have e2 : braidGenT (m + 1 + 1) (m + 1) * braidGenTinv (m + 1 + 1) (m + 1) = 1 :=
    braidGenT_mul_inv (by omega) le_rfl
  simp only [mul_assoc]
  rw [mul_mul_cancel_of_mul_eq_one e1, mul_mul_cancel_of_mul_eq_one e2, e1, mul_one]

/-- **The `ỹ`-letter against `T^*_{k+1↘i}`**: `φ_-(ỹ_a) T^*_{k+1↘i} = T^*_{k+1↘i} ỹ_{a+1}` for
`1 ≤ i ≤ a ≤ k`. This is the computation in the second half of Mellit's proof of Proposition
`phiminus`: `φ_-(ỹ_a) = T_{a↘k+1} ỹ_{k+1} T_k T_{k↗a}`, after which the identity is a collision of
trains on either side of the commuting lift `ỹ_{k+1}`. -/
theorem phiMinus_braidYtilde_mul_trainUp_top (hk : 1 ≤ k) {a i : ℕ} (hi : 1 ≤ i) (hia : i ≤ a)
    (hak : a ≤ k) :
    phiMinus k (braidYtilde k a) * braidTrainUp (k + 1) (k + 1) i
      = braidTrainUp (k + 1) (k + 1) i * braidYtilde (k + 1) (a + 1) := by
  have h := isBraidSystem_braidGenT (k + 1)
  have eD : braidTrainDown (k + 1) a k * braidGenTinv (k + 1) k
      = braidTrainDown (k + 1) a (k + 1) := by
    rw [← trainDown_self_succ (braidGenT (k + 1)) (braidGenTinv (k + 1)) k]
    exact trainDown_mul_trainDown h (a := a) (b := k) (c := k + 1) (by omega) (by omega) hk
      (by omega) (by omega) le_rfl
  have hΨ : phiMinus k (braidYtilde k a)
      = braidTrainDown (k + 1) a (k + 1) * braidYtilde (k + 1) (k + 1) *
          braidGenT (k + 1) k * braidTrainUp (k + 1) k a := by
    rw [braidYtilde_eq_trainDown_mul_mul_trainUp (k := k) (a := k) (b := a) hk le_rfl
        (by omega) hak, map_mul, map_mul, phiMinus_braidTrainDown (by omega) hak hk le_rfl,
      phiMinus_braidYtilde_self hk, phiMinus_braidTrainUp hk le_rfl (by omega) hak, ← eD]
    simp only [mul_assoc]
  have hY : braidYtilde (k + 1) (a + 1)
      = braidTrainDown (k + 1) (a + 1) (k + 1) * braidYtilde (k + 1) (k + 1) *
          braidTrainUp (k + 1) (k + 1) (a + 1) :=
    braidYtilde_eq_trainDown_mul_mul_trainUp (k := k + 1) (a := k + 1) (b := a + 1) (by omega)
      le_rfl (by omega) (by omega)
  have hI : braidTrainUp (k + 1) (k + 1) i * braidTrainDown (k + 1) (a + 1) (k + 1)
      = braidTrainDown (k + 1) a (k + 1) * braidTrainUp (k + 1) k i := by
    have hcol : collideIndex ((k + 1 : ℕ) : ℤ) (i : ℤ) ((a + 1 : ℕ) : ℤ) ((k + 1 : ℕ) : ℤ)
        = ((k : ℤ), (i : ℤ), (a : ℤ), ((k + 1 : ℕ) : ℤ)) := by
      have h1 : indexShift ((k + 1 : ℕ) : ℤ) (i : ℤ) ((a + 1 : ℕ) : ℤ) = a := by
        rw [indexShift_of_gt_of_le (by push_cast; omega) (by push_cast; omega)]
        push_cast
        ring
      have h2 : indexShift ((k + 1 : ℕ) : ℤ) ((a + 1 : ℕ) : ℤ) (i : ℤ) = i :=
        indexShift_of_lt_of_lt (by push_cast; omega) (by push_cast; omega)
      have h3 : indexShift ((k + 1 : ℕ) : ℤ) (a : ℤ) ((k + 1 : ℕ) : ℤ) = k := by
        rw [indexShift_of_gt_of_le le_rfl (by push_cast; omega)]
        push_cast
        ring
      have h4 : indexShift (k : ℤ) (i : ℤ) ((k + 1 : ℕ) : ℤ) = ((k + 1 : ℕ) : ℤ) :=
        indexShift_of_gt_of_gt (by push_cast; omega) (by push_cast; omega)
      rw [collideIndex_eq, h1, h2, h3, h4]
    exact h.collide (by omega) le_rfl hi (by omega) (by omega) (by omega) (by omega) le_rfl
      (by omega) hcol
  have hsplit : braidTrainUp (k + 1) (k + 1) i
      = braidGenTinv (k + 1) k * braidTrainUp (k + 1) k i := by
    rw [← trainUp_succ_self (braidGenT (k + 1)) (braidGenTinv (k + 1)) k]
    exact (trainUp_mul_trainUp h (a := k + 1) (b := k) (c := i) (by omega) le_rfl hk
      (by omega) hi (by omega)).symm
  have hov : braidTrainUp (k + 1) k a * braidTrainUp (k + 1) (k + 1) i
      = braidTrainUp (k + 1) (k + 1) i * braidTrainUp (k + 1) (k + 1) (a + 1) :=
    trainUp_overtake h (a := k) (b := a) (c := k + 1) (d := i) hi (by omega) (by omega) hia
      (by omega) le_rfl
  have hII : braidTrainUp (k + 1) k i * braidTrainUp (k + 1) (k + 1) (a + 1)
      = braidGenT (k + 1) k * braidTrainUp (k + 1) k a * braidTrainUp (k + 1) (k + 1) i := by
    rw [mul_assoc, hov, hsplit, ← mul_assoc, ← mul_assoc,
      braidGenT_mul_inv hk le_rfl, one_mul]
  have hcomm : braidYtilde (k + 1) (k + 1) * braidTrainUp (k + 1) k i
      = braidTrainUp (k + 1) k i * braidYtilde (k + 1) (k + 1) :=
    braidYtilde_comm_trainUp (by omega) le_rfl hk (by omega) hi (by omega) (Or.inr (by omega))
  rw [hΨ, hY]
  calc braidTrainDown (k + 1) a (k + 1) * braidYtilde (k + 1) (k + 1) * braidGenT (k + 1) k *
          braidTrainUp (k + 1) k a * braidTrainUp (k + 1) (k + 1) i
        = braidTrainDown (k + 1) a (k + 1) * braidYtilde (k + 1) (k + 1) *
            (braidGenT (k + 1) k * braidTrainUp (k + 1) k a * braidTrainUp (k + 1) (k + 1) i) := by
          simp only [mul_assoc]
      _ = braidTrainDown (k + 1) a (k + 1) * (braidYtilde (k + 1) (k + 1) *
            braidTrainUp (k + 1) k i) * braidTrainUp (k + 1) (k + 1) (a + 1) := by
          rw [← hII]; simp only [mul_assoc]
      _ = braidTrainUp (k + 1) (k + 1) i * braidTrainDown (k + 1) (a + 1) (k + 1) *
            braidYtilde (k + 1) (k + 1) * braidTrainUp (k + 1) (k + 1) (a + 1) := by
          rw [hcomm, hI]; simp only [mul_assoc]
      _ = _ := by simp only [mul_assoc]

/-! ### Mellit's Proposition `phiminus` for one move -/

/-- **`(z1)`, `(z2)`, `(y1)`, `(y2)` in one statement**: the braid of one elementary move of the
smaller tuple, carried through `φ_-`, against the train `T^*_{k+1↘i}` of the fixed point. -/
theorem trainUp_top_mul_braidStep_z_of_lt {a a' i : ℕ} (ha : 1 ≤ a)
    (ha' : 1 ≤ a') (hai : a < i) (ha'i : a' < i) (hik : i ≤ k + 1) :
    braidTrainUp (k + 1) (k + 1) i * (braidTrainDown (k + 1) a' a * braidGenZ (k + 1) a)
      = phiMinus k (braidTrainDown k a' a * braidGenZ k a) * braidTrainUp (k + 1) (k + 1) i := by
  rw [map_mul, phiMinus_braidTrainDown ha' (by omega) ha (by omega),
    phiMinus_braidGenZ ha (by omega), ← mul_assoc,
    trainUp_top_mul_trainDown_of_lt ha ha' hai ha'i hik, mul_assoc, mul_assoc,
    braidGenZ_comm_trainUp_top ha hai hik]

/-- `(z2)`: a `z`-move carrying the point over the fixed one, whose rank drops by one. -/
theorem trainUp_top_mul_braidStep_z_of_le {a a' i : ℕ} (ha : 1 ≤ a) (hai : a < i)
    (hia' : i ≤ a' + 1) (ha'k : a' ≤ k) :
    braidTrainUp (k + 1) (k + 1) (i - 1) *
        (braidTrainDown (k + 1) (a' + 1) a * braidGenZ (k + 1) a)
      = phiMinus k (braidTrainDown k a' a * braidGenZ k a) * braidTrainUp (k + 1) (k + 1) i := by
  rw [map_mul, phiMinus_braidTrainDown (by omega) ha'k ha (by omega),
    phiMinus_braidGenZ ha (by omega), ← mul_assoc,
    trainUp_top_pred_mul_trainDown ha hai hia' ha'k, mul_assoc, mul_assoc,
    braidGenZ_comm_trainUp_top ha hai (by omega)]

/-- `(y1)`: a `ỹ`-move carrying the point below the fixed one, whose rank rises by one. -/
theorem trainUp_top_mul_braidStep_y_of_ge (hk : 1 ≤ k) {a a' i : ℕ} (hi : 1 ≤ i)
    (ha' : 1 ≤ a') (ha'i : a' ≤ i) (hia : i ≤ a) (hak : a ≤ k) :
    braidTrainUp (k + 1) (k + 1) (i + 1) *
        (braidTrainDown (k + 1) a' (a + 1) * braidYtilde (k + 1) (a + 1))
      = phiMinus k (braidTrainDown k a' a * braidYtilde k a) *
          braidTrainUp (k + 1) (k + 1) i := by
  rw [map_mul, phiMinus_braidTrainDown ha' (by omega) (by omega) hak, mul_assoc,
    phiMinus_braidYtilde_mul_trainUp_top hk hi hia hak, ← mul_assoc, ← mul_assoc,
    trainUp_top_succ_mul_trainDown hi ha' ha'i hia hak]

/-- `(y2)`: a `ỹ`-move keeping the point above the fixed one. -/
theorem trainUp_top_mul_braidStep_y_of_le (hk : 1 ≤ k) {a a' i : ℕ} (hi : 1 ≤ i)
    (hia' : i ≤ a') (ha'a : a' ≤ a) (hak : a ≤ k) :
    braidTrainUp (k + 1) (k + 1) i *
        (braidTrainDown (k + 1) (a' + 1) (a + 1) * braidYtilde (k + 1) (a + 1))
      = phiMinus k (braidTrainDown k a' a * braidYtilde k a) *
          braidTrainUp (k + 1) (k + 1) i := by
  rw [map_mul, phiMinus_braidTrainDown (by omega) (by omega) (by omega) hak, mul_assoc,
    phiMinus_braidYtilde_mul_trainUp_top hk hi (hia'.trans ha'a) hak, ← mul_assoc, ← mul_assoc,
    trainUp_top_mul_trainDown_succ hi hia' ha'a hak]

end PhiMinusTrains


/-! ### Mellit's Proposition `phiminus`: one move, then a sequence of moves -/

section PhiMinusMove

open Finset

variable {θ : ℚ} {k : ℕ}

/-- **One elementary move against a fixed point just below the puncture**, Mellit's
Proposition `phiminus` at one move: for a tuple `U` of distinct points with `U_s < θ`, and a move
at `m = s.succAbove t₀` whose point, if it is below the puncture, is below `U_s` too,
`T^*_{k+1↘i'} b_m(U) = φ_-(b_{t₀}(U ∘ s.succAbove)) T^*_{k+1↘i}`, where `i` and `i'` are the ranks
of the fixed point before and after the move.

Mellit puts the fixed point at the puncture itself; what the computation reads is only that no
moving point lies between it and the puncture, which is the hypothesis `hz`. -/
theorem trainUp_top_mul_braidStep_succAbove (hk : 1 ≤ k) (hθ : 0 ≤ θ) (s : Fin (k + 1))
    (U : Fin (k + 1) → ℚ) (t₀ : Fin k) (hs : U s < θ)
    (hz : U (s.succAbove t₀) < θ → U (s.succAbove t₀) < U s)
    (hne : U (s.succAbove t₀) ≠ θ) (hinj' : Function.Injective (moveOne θ U (s.succAbove t₀))) :
    braidTrainUp (k + 1) (k + 1) (entryRank (moveOne θ U (s.succAbove t₀)) s) *
        braidStep θ U (s.succAbove t₀)
      = phiMinus k (braidStep θ (U ∘ s.succAbove) t₀) *
          braidTrainUp (k + 1) (k + 1) (entryRank U s) := by
  have hms : s.succAbove t₀ ≠ s := s.succAbove_ne t₀
  have hU's : moveOne θ U (s.succAbove t₀) s = U s := moveOne_of_ne θ U (Ne.symm hms)
  have hcomp : moveOne θ U (s.succAbove t₀) ∘ s.succAbove = moveOne θ (U ∘ s.succAbove) t₀ :=
    moveOne_comp_succAbove U s t₀
  have hrm : entryRank U (s.succAbove t₀)
      = entryRank (U ∘ s.succAbove) t₀ + (if U s ≤ U (s.succAbove t₀) then 1 else 0) :=
    entryRank_succAbove U s t₀
  have hrm' : entryRank (moveOne θ U (s.succAbove t₀)) (s.succAbove t₀)
      = entryRank (moveOne θ (U ∘ s.succAbove) t₀) t₀
        + (if U s ≤ nextCrossing θ (U (s.succAbove t₀)) then 1 else 0) := by
    rw [entryRank_succAbove (moveOne θ U (s.succAbove t₀)) s t₀, hcomp, hU's, moveOne_self]
  have his : entryRank U s = #{t | (U ∘ s.succAbove) t ≤ U s} + 1 := entryRank_self_succAbove U s
  have his' : entryRank (moveOne θ U (s.succAbove t₀)) s
      = #{t | moveOne θ (U ∘ s.succAbove) t₀ t ≤ U s} + 1 := by
    rw [entryRank_self_succAbove (moveOne θ U (s.succAbove t₀)) s, hcomp, hU's]
  have hcard := card_filter_moveOne_add (θ := θ) (U ∘ s.succAbove) t₀ (U s)
  have hA1 : 1 ≤ entryRank (U ∘ s.succAbove) t₀ := entryRank_pos _ _
  have hAk : entryRank (U ∘ s.succAbove) t₀ ≤ k := entryRank_le _ _
  have hA'1 : 1 ≤ entryRank (moveOne θ (U ∘ s.succAbove) t₀) t₀ := entryRank_pos _ _
  have hA'k : entryRank (moveOne θ (U ∘ s.succAbove) t₀) t₀ ≤ k := entryRank_le _ _
  have hCk : #{t | (U ∘ s.succAbove) t ≤ U s} ≤ k := by
    have h : #{t | (U ∘ s.succAbove) t ≤ U s} ≤ #(Finset.univ : Finset (Fin k)) :=
      Finset.card_filter_le _ _
    simpa using h
  have hC'k : #{t | moveOne θ (U ∘ s.succAbove) t₀ t ≤ U s} ≤ k := by
    have h : #{t | moveOne θ (U ∘ s.succAbove) t₀ t ≤ U s}
        ≤ #(Finset.univ : Finset (Fin k)) := Finset.card_filter_le _ _
    simpa using h
  -- the moved point is not the fixed one
  have hx'ne : nextCrossing θ (U (s.succAbove t₀)) ≠ U s := by
    intro h
    have := hinj' (show moveOne θ U (s.succAbove t₀) (s.succAbove t₀)
      = moveOne θ U (s.succAbove t₀) s by rw [moveOne_self, hU's, h])
    exact hms this
  rcases lt_or_gt_of_ne hne with hxθ | hxθ
  · -- the `z` branch: the point is below the fixed one
    have hxX : U (s.succAbove t₀) < U s := hz hxθ
    have hif : (if U s ≤ U (s.succAbove t₀) then 1 else 0) = 0 :=
      ite_eq_right_of_eq_false _ _ (eq_false (by simpa using hxX))
    have hifc : (if (U ∘ s.succAbove) t₀ ≤ U s then 1 else 0) = 1 :=
      ite_eq_left_of_eq_true _ _ (eq_true hxX.le)
    have hM1 : entryRank (U ∘ s.succAbove) t₀ ≤ #{t | (U ∘ s.succAbove) t ≤ U s} :=
      entryRank_le_card_filter hxX.le
    rw [braidStep_of_lt hxθ, braidStep_of_lt (show (U ∘ s.succAbove) t₀ < θ from hxθ)]
    rcases lt_or_gt_of_ne hx'ne with hx'X | hx'X
    · -- `(z1)`: the point stays below the fixed one
      have hif' : (if U s ≤ nextCrossing θ (U (s.succAbove t₀)) then 1 else 0) = 0 :=
        ite_eq_right_of_eq_false _ _ (eq_false (by simpa using hx'X))
      have hifc' : (if nextCrossing θ ((U ∘ s.succAbove) t₀) ≤ U s then 1 else 0) = 1 :=
        ite_eq_left_of_eq_true _ _ (eq_true hx'X.le)
      have hM1' : entryRank (moveOne θ (U ∘ s.succAbove) t₀) t₀
          ≤ #{t | moveOne θ (U ∘ s.succAbove) t₀ t ≤ U s} := by
        refine entryRank_le_card_filter ?_
        rw [moveOne_self]
        exact hx'X.le
      rw [hifc, hifc'] at hcard
      have heq : #{t | moveOne θ (U ∘ s.succAbove) t₀ t ≤ U s}
          = #{t | (U ∘ s.succAbove) t ≤ U s} := by omega
      simp only [hrm, hrm', hif, hif', his, his', heq, Nat.add_zero]
      exact trainUp_top_mul_braidStep_z_of_lt hA1 hA'1 (by omega) (by omega) (by omega)
    · -- `(z2)`: the point jumps over the fixed one, whose rank drops by one
      have hif' : (if U s ≤ nextCrossing θ (U (s.succAbove t₀)) then 1 else 0) = 1 :=
        ite_eq_left_of_eq_true _ _ (eq_true hx'X.le)
      have hifc' : (if nextCrossing θ ((U ∘ s.succAbove) t₀) ≤ U s then 1 else 0) = 0 :=
        ite_eq_right_of_eq_false _ _ (eq_false (by simpa using hx'X))
      have hM2' : #{t | moveOne θ (U ∘ s.succAbove) t₀ t ≤ U s} + 1
          ≤ entryRank (moveOne θ (U ∘ s.succAbove) t₀) t₀ := by
        refine card_filter_lt_entryRank ?_
        rwa [moveOne_self]
      rw [hifc, hifc'] at hcard
      have heq : #{t | moveOne θ (U ∘ s.succAbove) t₀ t ≤ U s} + 1
          = #{t | (U ∘ s.succAbove) t ≤ U s} := by omega
      simp only [hrm, hrm', hif, hif', his, his', heq, Nat.add_zero]
      have := trainUp_top_mul_braidStep_z_of_le (k := k) hA1
        (show entryRank (U ∘ s.succAbove) t₀ < #{t | (U ∘ s.succAbove) t ≤ U s} + 1 by omega)
        (show #{t | (U ∘ s.succAbove) t ≤ U s} + 1
          ≤ entryRank (moveOne θ (U ∘ s.succAbove) t₀) t₀ + 1 by omega) hA'k
      rwa [show #{t | (U ∘ s.succAbove) t ≤ U s} + 1 - 1 = #{t | (U ∘ s.succAbove) t ≤ U s}
        by omega] at this
  · -- the `ỹ` branch: the point is above the puncture, hence above the fixed one
    have hxX : U s < U (s.succAbove t₀) := hs.trans hxθ
    have hif : (if U s ≤ U (s.succAbove t₀) then 1 else 0) = 1 :=
      ite_eq_left_of_eq_true _ _ (eq_true hxX.le)
    have hifc : (if (U ∘ s.succAbove) t₀ ≤ U s then 1 else 0) = 0 :=
      ite_eq_right_of_eq_false _ _ (eq_false (by simpa using hxX))
    have hM2 : #{t | (U ∘ s.succAbove) t ≤ U s} + 1 ≤ entryRank (U ∘ s.succAbove) t₀ :=
      card_filter_lt_entryRank hxX
    -- the rank cannot rise: the point moves down
    have hA'A : entryRank (moveOne θ (U ∘ s.succAbove) t₀) t₀ ≤ entryRank (U ∘ s.succAbove) t₀ := by
      refine Finset.card_le_card fun t ht => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
      rw [moveOne_self, nextCrossing_of_gt (show θ < (U ∘ s.succAbove) t₀ from hxθ)] at ht
      by_cases htt : t = t₀
      · subst htt
        exact le_rfl
      · rw [moveOne_of_ne _ _ htt] at ht
        linarith
    rw [braidStep_of_gt hxθ, braidStep_of_gt (show θ < (U ∘ s.succAbove) t₀ from hxθ)]
    rcases lt_or_gt_of_ne hx'ne with hx'X | hx'X
    · -- `(y1)`: the point drops below the fixed one, whose rank rises by one
      have hif' : (if U s ≤ nextCrossing θ (U (s.succAbove t₀)) then 1 else 0) = 0 :=
        ite_eq_right_of_eq_false _ _ (eq_false (by simpa using hx'X))
      have hifc' : (if nextCrossing θ ((U ∘ s.succAbove) t₀) ≤ U s then 1 else 0) = 1 :=
        ite_eq_left_of_eq_true _ _ (eq_true hx'X.le)
      have hM1' : entryRank (moveOne θ (U ∘ s.succAbove) t₀) t₀
          ≤ #{t | moveOne θ (U ∘ s.succAbove) t₀ t ≤ U s} := by
        refine entryRank_le_card_filter ?_
        rw [moveOne_self]
        exact hx'X.le
      rw [hifc, hifc'] at hcard
      have heq : #{t | moveOne θ (U ∘ s.succAbove) t₀ t ≤ U s}
          = #{t | (U ∘ s.succAbove) t ≤ U s} + 1 := by omega
      simp only [hrm, hrm', hif, hif', his, his', heq, Nat.add_zero]
      exact trainUp_top_mul_braidStep_y_of_ge hk (by omega) hA'1 (by omega) (by omega) hAk
    · -- `(y2)`: the point stays above the fixed one
      have hif' : (if U s ≤ nextCrossing θ (U (s.succAbove t₀)) then 1 else 0) = 1 :=
        ite_eq_left_of_eq_true _ _ (eq_true hx'X.le)
      have hifc' : (if nextCrossing θ ((U ∘ s.succAbove) t₀) ≤ U s then 1 else 0) = 0 :=
        ite_eq_right_of_eq_false _ _ (eq_false (by simpa using hx'X))
      have hM2' : #{t | moveOne θ (U ∘ s.succAbove) t₀ t ≤ U s} + 1
          ≤ entryRank (moveOne θ (U ∘ s.succAbove) t₀) t₀ := by
        refine card_filter_lt_entryRank ?_
        rwa [moveOne_self]
      rw [hifc, hifc'] at hcard
      have heq : #{t | moveOne θ (U ∘ s.succAbove) t₀ t ≤ U s}
          = #{t | (U ∘ s.succAbove) t ≤ U s} := by omega
      simp only [hrm, hrm', hif, hif', his, his', heq]
      exact trainUp_top_mul_braidStep_y_of_le hk (by omega) (by omega) hA'A hAk

/-- **Mellit's Proposition `phiminus`** for a sequence of moves: if a point `U_s < θ` never moves
and no moving point ever lies between it and the puncture, then
`T^*_{k+1↘i'} b_{l}(U) = φ_-(b_l(U ∘ s.succAbove)) T^*_{k+1↘i}`, with `i`, `i'` the ranks of the
fixed point in the initial and the final tuple. -/
theorem trainUp_top_mul_braidWord_map_succAbove (hk : 1 ≤ k) (hθ : 0 ≤ θ) (s : Fin (k + 1))
    (U : Fin (k + 1) → ℚ) (hs : U s < θ) :
    ∀ l : List (Fin k),
      (∀ l' : List (Fin k), l' <:+ l → Function.Injective (moveTuple θ U (l'.map s.succAbove))) →
      (∀ (t₀ : Fin k) (l' : List (Fin k)), t₀ :: l' <:+ l →
        moveTuple θ U (l'.map s.succAbove) (s.succAbove t₀) ≠ θ) →
      (∀ (t₀ : Fin k) (l' : List (Fin k)), t₀ :: l' <:+ l →
        moveTuple θ U (l'.map s.succAbove) (s.succAbove t₀) < θ →
          moveTuple θ U (l'.map s.succAbove) (s.succAbove t₀) < U s) →
      braidTrainUp (k + 1) (k + 1) (entryRank (moveTuple θ U (l.map s.succAbove)) s) *
          braidWord θ U (l.map s.succAbove)
        = phiMinus k (braidWord θ (U ∘ s.succAbove) l) *
            braidTrainUp (k + 1) (k + 1) (entryRank U s)
  | [], _, _, _ => by simp
  | t₀ :: l, hinj, hne, hz => by
    have ih := trainUp_top_mul_braidWord_map_succAbove hk hθ s U hs l
      (fun l' hl' => hinj l' (hl'.trans (List.suffix_cons t₀ l)))
      (fun t l' hl' => hne t l' (hl'.trans (List.suffix_cons t₀ l)))
      (fun t l' hl' => hz t l' (hl'.trans (List.suffix_cons t₀ l)))
    have hfix : moveTuple θ U (l.map s.succAbove) s = U s := moveTuple_map_succAbove_self U s l
    have hstep := trainUp_top_mul_braidStep_succAbove hk hθ s (moveTuple θ U (l.map s.succAbove)) t₀
      (by rw [hfix]; exact hs) (by rw [hfix]; exact hz t₀ l List.suffix_rfl)
      (hne t₀ l List.suffix_rfl) (hinj (t₀ :: l) List.suffix_rfl)
    rw [moveTuple_comp_succAbove] at hstep
    rw [List.map_cons, braidWord_cons, braidWord_cons, moveTuple_cons, ← mul_assoc, hstep,
      mul_assoc, ih, map_mul, mul_assoc]

end PhiMinusMove


/-! ### The local factors of the cut, and the reconnection of the trains -/

section CutAlgebra

variable {k : ℕ}

/-- **The local factor of the lower braid**: the passage `ỹ_{a_1}`, `z_1` of the moving point near
the puncture, read with its trains, is `T_{a_2↘1} z_1ỹ_1 T_{1↗a_1}`. -/
theorem braidStep_pair_lower {a₁ a₂ : ℕ} (ha₁ : 1 ≤ a₁) (ha₁k : a₁ ≤ k) :
    braidTrainDown k a₂ 1 * braidGenZ k 1 * (braidTrainDown k 1 a₁ * braidYtilde k a₁)
      = braidTrainDown k a₂ 1 * (braidGenZ k 1 * braidYtilde k 1) * braidTrainUp k 1 a₁ := by
  rw [braidTrainDown_mul_braidYtilde le_rfl (by omega) ha₁ ha₁k]
  simp only [mul_assoc]

/-- **The local factor of the type-`E` braid**: the passage `z_{a_1}`, `ỹ_k` of the moving point
near the puncture, read with its trains, is `T_{a_2↘1} y_1z_1 T_{1↗a_1}` — the same trains as the
lower braid, with `z_1ỹ_1` replaced by `y_1z_1`. -/
theorem braidStep_pair_typeE {a₁ a₂ : ℕ} (ha₁ : 1 ≤ a₁) (ha₁k : a₁ ≤ k) (ha₂ : 1 ≤ a₂)
    (ha₂k : a₂ ≤ k) :
    braidTrainDown k a₂ k * braidYtilde k k * (braidTrainDown k k a₁ * braidGenZ k a₁)
      = braidTrainDown k a₂ 1 * (braidGenY k 1 * braidGenZ k 1) * braidTrainUp k 1 a₁ := by
  have h := isBraidSystem_braidGenT k
  have hk : 1 ≤ k := ha₁.trans ha₁k
  have hD1 : braidTrainDown k a₂ k * braidTrainDown k k 1 = braidTrainDown k a₂ 1 :=
    trainDown_mul_trainDown h ha₂ ha₂k hk le_rfl le_rfl hk
  have hD2 : braidTrainDown k k a₁ * braidTrainDown k a₁ 1 = braidTrainDown k k 1 :=
    trainDown_mul_trainDown h hk le_rfl ha₁ ha₁k le_rfl hk
  have hy : braidTrainUp k 1 k * braidGenY k k * braidTrainDown k k 1 = braidGenY k 1 := by
    rw [braidGenY_eq_trainUp_mul_mul_trainDown k k hk le_rfl]
    have e1 : braidTrainUp k 1 k * braidTrainUp k k 1 = 1 :=
      trainUp_mul_trainUp_self h le_rfl hk hk le_rfl
    have e2 : braidTrainDown k 1 k * braidTrainDown k k 1 = 1 :=
      trainDown_mul_trainDown_self h le_rfl hk hk le_rfl
    simp only [mul_assoc]
    rw [mul_mul_cancel_of_mul_eq_one e1, e2, mul_one]
  rw [braidYtilde_self, braidGenZ_eq_trainDown_one_mul ha₁ ha₁k]
  calc braidTrainDown k a₂ k * (braidTrainDown k k 1 * braidTrainUp k 1 k * braidGenY k k) *
        (braidTrainDown k k a₁ * (braidTrainDown k a₁ 1 * braidGenZ k 1 * braidTrainUp k 1 a₁))
      = (braidTrainDown k a₂ k * braidTrainDown k k 1) * (braidTrainUp k 1 k * braidGenY k k *
          (braidTrainDown k k a₁ * braidTrainDown k a₁ 1)) * braidGenZ k 1 *
            braidTrainUp k 1 a₁ := by simp only [mul_assoc]
    _ = braidTrainDown k a₂ 1 * (braidTrainUp k 1 k * braidGenY k k * braidTrainDown k k 1) *
          braidGenZ k 1 * braidTrainUp k 1 a₁ := by rw [hD1, hD2]
    _ = _ := by rw [hy]; simp only [mul_assoc]

/-- **The reconnection, when the end of the first piece lies above the start of the second.**
`T^*_{k+1↘a_1+1}` and `T_{a_2↘1}` commute when `a_2 ≤ a_1`. -/
theorem trainUp_top_mul_trainDown_one_of_le {a₁ a₂ : ℕ} (ha₂ : 1 ≤ a₂) (ha₂a₁ : a₂ ≤ a₁)
    (ha₁k : a₁ ≤ k) :
    braidTrainUp (k + 1) (k + 1) (a₁ + 1) * braidTrainDown (k + 1) a₂ 1
      = braidTrainDown (k + 1) a₂ 1 * braidTrainUp (k + 1) (k + 1) (a₁ + 1) := by
  have hcol : collideIndex ((k + 1 : ℕ) : ℤ) ((a₁ + 1 : ℕ) : ℤ) (a₂ : ℤ) ((1 : ℕ) : ℤ)
      = (((k + 1 : ℕ) : ℤ), ((a₁ + 1 : ℕ) : ℤ), (a₂ : ℤ), ((1 : ℕ) : ℤ)) := by
    have h1 : indexShift ((k + 1 : ℕ) : ℤ) ((a₁ + 1 : ℕ) : ℤ) (a₂ : ℤ) = a₂ :=
      indexShift_of_lt_of_lt (by push_cast; omega) (by push_cast; omega)
    have h2 : indexShift ((1 : ℕ) : ℤ) (a₂ : ℤ) ((a₁ + 1 : ℕ) : ℤ) = ((a₁ + 1 : ℕ) : ℤ) :=
      indexShift_of_gt_of_gt (by push_cast; omega) (by push_cast; omega)
    have h3 : indexShift ((1 : ℕ) : ℤ) (a₂ : ℤ) ((k + 1 : ℕ) : ℤ) = ((k + 1 : ℕ) : ℤ) :=
      indexShift_of_gt_of_gt (by push_cast; omega) (by push_cast; omega)
    have h4 : indexShift ((k + 1 : ℕ) : ℤ) ((a₁ + 1 : ℕ) : ℤ) ((1 : ℕ) : ℤ) = ((1 : ℕ) : ℤ) :=
      indexShift_of_lt_of_lt (by push_cast; omega) (by push_cast; omega)
    rw [collideIndex_eq, h1, h2, h3, h4]
  exact (isBraidSystem_braidGenT (k + 1)).collide (by omega) le_rfl (by omega) (by omega) ha₂
    (by omega) le_rfl (by omega) (by omega) hcol

/-- **The reconnection, when the end of the first piece lies below the start of the second**:
`T^*_{k+1↘a_1} T_{a_2+1↘1} = T_{a_2↘1} T^*_{k+1↘a_1+1}` when `a_1 ≤ a_2`. Mellit's observation
that the composite of the two trains "does not depend on whether `X_1 > X_2`" is this lemma
together with `HJO.Braid.trainUp_top_mul_trainDown_one_of_le`. -/
theorem trainUp_top_mul_trainDown_one_of_ge {a₁ a₂ : ℕ} (ha₁ : 1 ≤ a₁) (ha₁a₂ : a₁ ≤ a₂)
    (ha₂k : a₂ ≤ k) :
    braidTrainUp (k + 1) (k + 1) a₁ * braidTrainDown (k + 1) (a₂ + 1) 1
      = braidTrainDown (k + 1) a₂ 1 * braidTrainUp (k + 1) (k + 1) (a₁ + 1) := by
  have hcol : collideIndex ((k + 1 : ℕ) : ℤ) (a₁ : ℤ) ((a₂ + 1 : ℕ) : ℤ) ((1 : ℕ) : ℤ)
      = (((k + 1 : ℕ) : ℤ), ((a₁ + 1 : ℕ) : ℤ), (a₂ : ℤ), ((1 : ℕ) : ℤ)) := by
    have h1 : indexShift ((k + 1 : ℕ) : ℤ) (a₁ : ℤ) ((a₂ + 1 : ℕ) : ℤ) = a₂ := by
      rw [indexShift_of_gt_of_le (by push_cast; omega) (by push_cast; omega)]
      push_cast
      ring
    have h2 : indexShift ((1 : ℕ) : ℤ) ((a₂ + 1 : ℕ) : ℤ) (a₁ : ℤ) = ((a₁ + 1 : ℕ) : ℤ) := by
      rw [indexShift_of_lt_of_le (by push_cast; omega) (by push_cast; omega)]
      push_cast
      ring
    have h3 : indexShift ((1 : ℕ) : ℤ) (a₂ : ℤ) ((k + 1 : ℕ) : ℤ) = ((k + 1 : ℕ) : ℤ) :=
      indexShift_of_gt_of_gt (by push_cast; omega) (by push_cast; omega)
    have h4 : indexShift ((k + 1 : ℕ) : ℤ) ((a₁ + 1 : ℕ) : ℤ) ((1 : ℕ) : ℤ) = ((1 : ℕ) : ℤ) :=
      indexShift_of_lt_of_lt (by push_cast; omega) (by push_cast; omega)
    rw [collideIndex_eq, h1, h2, h3, h4]
  exact (isBraidSystem_braidGenT (k + 1)).collide (by omega) le_rfl ha₁ (by omega) (by omega)
    (by omega) le_rfl (by omega) (by omega) hcol

end CutAlgebra


/-! ### The cut of the moving component, for abstract special-braid data -/

section Cut

open Finset

variable {s θ : ℚ} {K : ℕ}

/-- The moves of a suffix are performed first. -/
theorem moveTuple_append (θ : ℚ) {k : ℕ} (w : Fin k → ℚ) (l₁ l₂ : List (Fin k)) :
    moveTuple θ w (l₁ ++ l₂) = moveTuple θ (moveTuple θ w l₂) l₁ := by
  rw [moveTuple, moveTuple, moveTuple, List.foldr_append]

/-- `j.castSucc` and `j.succ` delete to the same index away from `j`. -/
theorem castSucc_succAbove_eq_succ_succAbove {j i : Fin K} (h : i ≠ j) :
    j.castSucc.succAbove i = j.succ.succAbove i := by
  rcases lt_or_gt_of_ne h with h | h
  · rw [Fin.succAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_castSucc_iff.2 h),
      Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_def]; simp; omega)]
  · rw [Fin.succAbove_of_le_castSucc _ _ (Fin.castSucc_le_castSucc_iff.2 h.le),
      Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_def]; simp; omega)]

/-- An iterate tuple of special-braid data, read below the multiplicities, is injective. -/
theorem IsSpecialBraidData.injective_iterate {k : ℕ} {v : Fin k → ℚ} {α : Fin k → ℕ}
    (h : IsSpecialBraidData s θ k v α) (c : Fin k → ℕ) (hc : ∀ t, c t < α t) :
    Function.Injective fun t => (nextCrossing θ)^[c t] (v t) :=
  fun t t' heq => (h.injective t t' (c t) (c t') (hc t) (hc t') heq).1

end Cut


/-! ### The cut of the moving component: the lists, the braids, the inversions -/

section CutData

open Finset

variable {s θ : ℚ} {K : ℕ}

/-- **The two pieces of the cut, counted.** The first piece `l₁` performs `p` moves of the index
`j` and every move of the indices above `j`; the second `l₂` every move of the indices below
`j` and `q` moves of `j`. -/
theorem count_cut_lists (α : Fin K → ℕ) (j : Fin K) (p q : ℕ) (i : Fin K) :
    (List.replicate p j ++ (specialMoveList α).filter (fun t => decide (j < t))).count i
        = (if i = j then p else 0) + (if j < i then α i - 1 else 0) ∧
      ((specialMoveList α).filter (fun t => decide (t < j)) ++ List.replicate q j).count i
        = (if i < j then α i - 1 else 0) + (if i = j then q else 0) := by
  have hr : ∀ n, (List.replicate n j).count i = if i = j then n else 0 := by
    intro n
    rw [List.count_replicate]
    by_cases h : i = j
    · subst h; simp
    · simp [h, Ne.symm h]
  have hf1 : ((specialMoveList α).filter (fun t => decide (j < t))).count i
      = if j < i then α i - 1 else 0 := by
    split_ifs with h
    · rw [List.count_filter (by simpa using h), count_specialMoveList]
    · exact List.count_eq_zero.2 (fun hm => h (by simpa using (List.mem_filter.1 hm).2))
  have hf2 : ((specialMoveList α).filter (fun t => decide (t < j))).count i
      = if i < j then α i - 1 else 0 := by
    split_ifs with h
    · rw [List.count_filter (by simpa using h), count_specialMoveList]
    · exact List.count_eq_zero.2 (fun hm => h (by simpa using (List.mem_filter.1 hm).2))
  rw [List.count_append, List.count_append, hr, hr, hf1, hf2]
  exact ⟨rfl, rfl⟩


/-- **Mellit's cut of the moving component, for abstract special-braid data.** Let `(v', α')` be
special-braid data of rank `K + 1` and `j : Fin K`; let the lower data be `v'` with the index
`j.castSucc` deleted and shifted by `δ`, the type-`E` data the same without the shift, both with
the multiplicities `α'_j`, `α'_{j+1}` merged into `α'_j + α'_{j+1} + 1`. Suppose that the end `X_1`
of the upper strand `j.succ` lies below the puncture and within `δ` of it, that the start of the
upper strand `j.castSucc` is `X_1 + 1 - 2θ`, that no other stage of the upper data is carried
across the puncture by the shift, that every initial position lies below `1 - θ`, and that
`j.castSucc` is the top of the initial tuple and `j.succ` the top of the final one. Then the three
special braids are `w z_1ỹ_1 B̃_1`, `w y_1z_1 B̃_1` and `w φ^*_+(T^*_{K↘1}B̃_1) T_{1↘K+1}`, with
`w` a word of rank `K` read at the two ranks. -/
theorem specialBraid_cut (hK : 1 ≤ K) (j : Fin K) (v' : Fin (K + 1) → ℚ) (α' : Fin (K + 1) → ℕ)
    (δ : ℚ) (hdU : IsSpecialBraidData s θ (K + 1) v' α')
    (hdE : IsSpecialBraidData s θ K (fun i => v' (j.castSucc.succAbove i))
      (Function.update (fun i => α' (j.castSucc.succAbove i)) j
        (α' j.castSucc + α' j.succ + 1)))
    (hdL : IsSpecialBraidData s θ K (fun i => v' (j.castSucc.succAbove i) + δ)
      (Function.update (fun i => α' (j.castSucc.succAbove i)) j
        (α' j.castSucc + α' j.succ + 1)))
    (hside : ∀ (t : Fin (K + 1)) (m : ℕ), m < α' t → (t = j.succ → m ≠ α' j.succ - 1) →
      SameSide θ δ ((nextCrossing θ)^[m] (v' t)))
    (hX : (nextCrossing θ)^[α' j.succ - 1] (v' j.succ) < θ)
    (hXδ : θ < (nextCrossing θ)^[α' j.succ - 1] (v' j.succ) + δ)
    (hXδ' : (nextCrossing θ)^[α' j.succ - 1] (v' j.succ) + δ < θ + θ)
    (hX₂ : v' j.castSucc = (nextCrossing θ)^[α' j.succ - 1] (v' j.succ) + 1 - θ - θ)
    (hinit : ∀ t, v' t < 1 - θ)
    (hmax : ∀ t, t ≠ j.castSucc → v' t < v' j.castSucc)
    (hmaxfin : ∀ t, t ≠ j.succ →
      (nextCrossing θ)^[α' t - 1] (v' t) < (nextCrossing θ)^[α' j.succ - 1] (v' j.succ)) :
    ∃ (B₁ : BraidMonoid K) (w : FreeMonoid Letter), (∀ c ∈ w.toList, Letter.InRank K c) ∧
      specialBraid θ (fun i => v' (j.castSucc.succAbove i) + δ)
          (Function.update (fun i => α' (j.castSucc.succAbove i)) j
            (α' j.castSucc + α' j.succ + 1))
        = toBraidMonoid K w * (braidGenZ K 1 * braidYtilde K 1) * B₁ ∧
      specialBraid θ (fun i => v' (j.castSucc.succAbove i))
          (Function.update (fun i => α' (j.castSucc.succAbove i)) j
            (α' j.castSucc + α' j.succ + 1))
        = toBraidMonoid K w * (braidGenY K 1 * braidGenZ K 1) * B₁ ∧
      specialBraid θ v' α'
        = toBraidMonoid (K + 1) w * phiPlusStar K hK (braidTrainUp K K 1 * B₁) *
            braidTrainDown (K + 1) 1 (K + 1) := by
  set J : Fin (K + 1) := j.castSucc with hJ
  set J' : Fin (K + 1) := j.succ with hJ'
  set αL : Fin K → ℕ := Function.update (fun i => α' (J.succAbove i)) j (α' J + α' J' + 1)
    with hαL
  set vE : Fin K → ℚ := fun i => v' (J.succAbove i) with hvE
  set X₁ := (nextCrossing θ)^[α' J' - 1] (v' J') with hX₁
  set p := α' J' - 1 with hp
  set q := α' J - 1 with hq
  have hθ := hdU.theta_mem_Ioo
  have hJsA : J.succAbove j = J' := Fin.succAbove_castSucc_self j
  have hJ'sA : J'.succAbove j = J := Fin.succAbove_succ_self j
  have hsA : ∀ i, i ≠ j → J.succAbove i = J'.succAbove i := fun i h =>
    castSucc_succAbove_eq_succ_succAbove h
  have hJJ' : J ≠ J' := by
    intro h
    have := congrArg Fin.val h
    simp [J, J'] at this
  have hsAne : ∀ i, i ≠ j → J.succAbove i ≠ J' := fun i h h' =>
    h (Fin.succAbove_right_injective (h'.trans hJsA.symm))
  have hpos : ∀ t, 1 ≤ α' t := hdU.one_le_mult
  have hαj : αL j = α' J + α' J' + 1 := by simp [αL]
  have hαi : ∀ i, i ≠ j → αL i = α' (J.succAbove i) := fun i h => by
    simp [αL, Function.update_of_ne h]
  have hvEj : vE j = v' J' := by simp [vE, hJsA]
  have hX₁pos : 0 < X₁ := (hdU.iterate_mem_Ioo J' p (by have := hpos J'; omega)).1
  have hvJpos : 0 < v' J := (hdU.mem_Ioo J).1
  -- the two lists of the cut
  set l₁ : List (Fin K) :=
    List.replicate p j ++ (specialMoveList αL).filter (fun t => decide (j < t)) with hl₁
  set l₂ : List (Fin K) :=
    (specialMoveList αL).filter (fun t => decide (t < j)) ++ List.replicate q j with hl₂
  have hc₁ : ∀ i, l₁.count i = (if i = j then p else 0) + (if j < i then αL i - 1 else 0) :=
    fun i => (count_cut_lists αL j p q i).1
  have hc₂ : ∀ i, l₂.count i = (if i < j then αL i - 1 else 0) + (if i = j then q else 0) :=
    fun i => (count_cut_lists αL j p q i).2
  clear_value l₁ l₂
  -- the move multisets
  have hpermL : (specialMoveList αL).Perm (l₂ ++ ([j, j] ++ l₁)) := by
    rw [List.perm_iff_count]
    intro i
    rw [count_specialMoveList, List.count_append, List.count_append, hc₁, hc₂]
    by_cases hij : i = j
    · subst hij
      have h2 : [i, i].count i = 2 := by simp
      rw [h2, hαj]
      simp
      have := hpos J; have := hpos J'
      omega
    · have h2 : [j, j].count i = 0 := List.count_eq_zero.2 (by simp [hij])
      rw [h2]
      rcases lt_or_gt_of_ne hij with h | h
      · simp [hij, h, not_lt.2 h.le]
      · simp [hij, h, not_lt.2 h.le]
  have hcountNotMem : ∀ (s' : Fin (K + 1)) (l : List (Fin K)),
      (l.map s'.succAbove).count s' = 0 := fun s' l => List.count_eq_zero.2 fun hm => by
    obtain ⟨i, _, hi⟩ := List.mem_map.1 hm
    exact Fin.succAbove_ne s' i hi
  have hcountMap : ∀ (s' : Fin (K + 1)) (l : List (Fin K)) (i : Fin K),
      (l.map s'.succAbove).count (s'.succAbove i) = l.count i := fun s' l i =>
    List.count_map_of_injective l _ Fin.succAbove_right_injective i
  have hpermU : (specialMoveList α').Perm
      (l₂.map J'.succAbove ++ l₁.map J.succAbove) := by
    rw [List.perm_iff_count]
    intro t
    rw [count_specialMoveList, List.count_append]
    by_cases htJ : t = J
    · rw [htJ, hcountNotMem, ← hJ'sA, hcountMap, hc₂]
      simp [hJ'sA, hq]
    · by_cases htJ' : t = J'
      · rw [htJ', hcountNotMem, ← hJsA, hcountMap, hc₁]
        simp [hJsA, hp]
      · obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq htJ
        have hij : i ≠ j := fun h => htJ' (by rw [h, hJsA])
        rw [hcountMap, hsA i hij, hcountMap, hc₁, hc₂, ← hsA i hij, ← hαi i hij]
        rcases lt_or_gt_of_ne hij with h | h
        · simp [hij, h, not_lt.2 h.le]
        · simp [hij, h, not_lt.2 h.le]
  -- the moves of `l₁` cross the puncture nowhere under the shift
  have hcnt : ∀ (l : List (Fin K)) (i : Fin K) (l' : List (Fin K)), i :: l' <:+ l →
      l'.count i + 1 ≤ l.count i := fun l i l' hl' => by
    have := hl'.count_le i
    rwa [List.count_cons_self] at this
  have hS₁ : ∀ (i : Fin K) (l' : List (Fin K)), i :: l' <:+ l₁ →
      SameSide θ δ (moveTuple θ vE l' i) := by
    intro i l' hl'
    have h := hcnt l₁ i l' hl'
    rw [moveTuple_apply_eq_iterate]
    rw [hc₁] at h
    by_cases hij : i = j
    · rw [hij, hvEj]
      rw [hij] at h
      simp only [ite_true, lt_irrefl, ite_false, add_zero] at h
      exact hside J' _ (by omega) (fun _ => by omega)
    · simp only [hij, ite_false, zero_add] at h
      split_ifs at h with hji
      · rw [hαi i hij] at h
        exact hside (J.succAbove i) _ (by omega) (fun h' => absurd h' (hsAne i hij))
      · omega
  have hP1 : ∀ t, moveTuple θ (fun i => vE i + δ) l₁ t = moveTuple θ vE l₁ t + δ :=
    moveTuple_add_of_sameSide_move θ δ vE l₁ hS₁
  have hW1 : braidWord θ (fun i => vE i + δ) l₁ = braidWord θ vE l₁ :=
    braidWord_congr_add_of_move θ δ vE l₁ hS₁
  set v₁ := moveTuple θ (fun i => vE i + δ) l₁ with hv₁
  set vE₁ := moveTuple θ vE l₁ with hvE₁def
  have hvE₁ : ∀ t, vE₁ t = (nextCrossing θ)^[l₁.count t] (vE t) := fun t =>
    moveTuple_apply_eq_iterate vE l₁ t
  have hcnt₁ : ∀ t, l₁.count t < αL t := fun t => by
    rw [hc₁]
    by_cases htj : t = j
    · rw [htj, hαj]; simp; omega
    · have := hdE.one_le_mult t
      simp only [htj, ite_false, zero_add]
      split_ifs <;> omega
  have hvE₁j : vE₁ j = X₁ := by
    rw [hvE₁, hc₁, hvEj]
    simp [hX₁]
  have hv₁j : v₁ j = X₁ + δ := by rw [hP1, hvE₁j]
  have hvE₁pos : ∀ t, 0 < vE₁ t := fun t => by
    rw [hvE₁]; exact (hdE.iterate_mem_Ioo t _ (hcnt₁ t)).1
  have hvE₁lt : ∀ t, t ≠ j → vE₁ t < X₁ + 1 - θ := by
    intro t ht
    rw [hvE₁, hc₁]
    simp only [ht, ite_false, zero_add]
    split_ifs with hjt
    · rw [hαi t ht]
      have h1 := hmaxfin (J.succAbove t) (hsAne t ht)
      have h2 := hθ.2
      change (nextCrossing θ)^[α' (J.succAbove t) - 1] (v' (J.succAbove t)) < X₁ + 1 - θ
      linarith
    · simp only [Function.iterate_zero, id_eq]
      have := hinit (J.succAbove t)
      change v' (J.succAbove t) < X₁ + 1 - θ
      linarith
  -- the two moves near the puncture, in the lower data
  have hrank1 : entryRank (moveOne θ v₁ j) j = 1 := by
    refine entryRank_eq_one_of_forall_ne_lt _ _ fun t ht => ?_
    rw [moveOne_self, moveOne_of_ne _ _ ht, hv₁j, nextCrossing_of_gt hXδ, hP1]
    linarith [hvE₁pos t]
  have hmid1 : braidStep θ v₁ j
      = braidTrainDown K 1 (entryRank v₁ j) * braidYtilde K (entryRank v₁ j) := by
    rw [braidStep_of_gt (by rw [hv₁j]; exact hXδ), hrank1]
  have hlow1 : moveOne θ v₁ j j < θ := by
    rw [moveOne_self, hv₁j, nextCrossing_of_gt hXδ]; linarith
  have hmid2 : braidStep θ (moveOne θ v₁ j) j
      = braidTrainDown K (entryRank (moveOne θ (moveOne θ v₁ j) j) j) 1 * braidGenZ K 1 := by
    rw [braidStep_of_lt hlow1, hrank1]
  -- the two moves near the puncture, in the type-`E` data
  have hrankE1 : entryRank (moveOne θ vE₁ j) j = K := by
    refine entryRank_eq_card_of_forall_le _ _ fun t => ?_
    by_cases ht : t = j
    · rw [ht]
    · rw [moveOne_of_ne _ _ ht, moveOne_self, hvE₁j, nextCrossing_of_lt hX]
      exact (hvE₁lt t ht).le
  have hmidE1 : braidStep θ vE₁ j
      = braidTrainDown K K (entryRank vE₁ j) * braidGenZ K (entryRank vE₁ j) := by
    rw [braidStep_of_lt (by rw [hvE₁j]; exact hX), hrankE1]
  have hhighE : θ < moveOne θ vE₁ j j := by
    rw [moveOne_self, hvE₁j, nextCrossing_of_lt hX]; linarith
  have hmidE2 : braidStep θ (moveOne θ vE₁ j) j
      = braidTrainDown K (entryRank (moveOne θ (moveOne θ vE₁ j) j) j) K * braidYtilde K K := by
    rw [braidStep_of_gt hhighE, hrankE1]
  -- after the two moves the shift is restored
  set v₂ := moveOne θ (moveOne θ v₁ j) j with hv₂
  set vE₂ := moveOne θ (moveOne θ vE₁ j) j with hvE₂
  have hP2 : ∀ t, v₂ t = vE₂ t + δ := by
    intro t
    by_cases ht : t = j
    · rw [ht, hv₂, hvE₂, moveOne_self, moveOne_self, moveOne_self, moveOne_self, hv₁j, hvE₁j,
        nextCrossing_of_gt hXδ, nextCrossing_of_lt (by linarith : X₁ + δ - θ < θ),
        nextCrossing_of_lt hX, nextCrossing_of_gt (by linarith : θ < X₁ + 1 - θ)]
      ring
    · rw [hv₂, hvE₂, moveOne_of_ne _ _ ht, moveOne_of_ne _ _ ht, moveOne_of_ne _ _ ht,
        moveOne_of_ne _ _ ht, hP1]
  have hvE₂j : vE₂ j = v' J := by
    rw [hvE₂, moveOne_self, moveOne_self, hvE₁j, nextCrossing_of_lt hX,
      nextCrossing_of_gt (by linarith : θ < X₁ + 1 - θ), hX₂]
  have hvE₂ne : ∀ t, t ≠ j → vE₂ t = vE₁ t := fun t ht => by
    rw [hvE₂, moveOne_of_ne _ _ ht, moveOne_of_ne _ _ ht]
  have hra₁ : entryRank v₁ j = entryRank vE₁ j := entryRank_congr_add hP1 j
  have hra₂ : entryRank v₂ j = entryRank vE₂ j := entryRank_congr_add hP2 j
  set a₁ := entryRank vE₁ j with ha₁
  set a₂ := entryRank vE₂ j with ha₂
  have ha₁1 : 1 ≤ a₁ := entryRank_pos _ _
  have ha₁K : a₁ ≤ K := entryRank_le _ _
  have ha₂1 : 1 ≤ a₂ := entryRank_pos _ _
  have ha₂K : a₂ ≤ K := entryRank_le _ _
  -- the moves of `l₂` cross the puncture nowhere under the shift
  have hS₂ : ∀ (i : Fin K) (l' : List (Fin K)), i :: l' <:+ l₂ →
      SameSide θ δ (moveTuple θ vE₂ l' i) := by
    intro i l' hl'
    have h := hcnt l₂ i l' hl'
    rw [moveTuple_apply_eq_iterate]
    rw [hc₂] at h
    by_cases hij : i = j
    · rw [hij, hvE₂j]
      rw [hij] at h
      simp only [ite_true, lt_irrefl, ite_false, zero_add] at h
      exact hside J _ (by omega) (fun h' => absurd h' hJJ')
    · simp only [hij, ite_false, add_zero] at h
      split_ifs at h with hji
      · rw [hvE₂ne i hij, hvE₁, hc₁]
        simp only [hij, ite_false, zero_add, not_lt.2 hji.le, Function.iterate_zero, id_eq]
        rw [hαi i hij] at h
        exact hside (J.succAbove i) _ (by omega) (fun h' => absurd h' (hsAne i hij))
      · omega
  have hW2 : braidWord θ v₂ l₂ = braidWord θ vE₂ l₂ := by
    rw [show v₂ = fun t => vE₂ t + δ from funext hP2]
    exact braidWord_congr_add_of_move θ δ vE₂ l₂ hS₂
  -- the lower and the type-`E` braid
  have hlow : specialBraid θ (fun i => vE i + δ) αL
      = braidWord θ vE₂ l₂ * (braidTrainDown K a₂ 1 * (braidGenZ K 1 * braidYtilde K 1) *
          braidTrainUp K 1 a₁) * braidWord θ vE l₁ := by
    rw [specialBraid, braidWord_perm_of_isSpecialBraidData hdL
        (fun t => (count_specialMoveList αL t).le) hpermL, braidWord_append, braidWord_append,
      show moveTuple θ (fun i => vE i + δ) ([j, j] ++ l₁) = v₂ from rfl, hW2, braidWord_pair,
      hmid2, hmid1, hra₂, hra₁, braidStep_pair_lower ha₁1 ha₁K, hW1]
    simp only [mul_assoc]
  have hE : specialBraid θ vE αL
      = braidWord θ vE₂ l₂ * (braidTrainDown K a₂ 1 * (braidGenY K 1 * braidGenZ K 1) *
          braidTrainUp K 1 a₁) * braidWord θ vE l₁ := by
    rw [specialBraid, braidWord_perm_of_isSpecialBraidData hdE
        (fun t => (count_specialMoveList αL t).le) hpermL, braidWord_append, braidWord_append,
      show moveTuple θ vE ([j, j] ++ l₁) = vE₂ from rfl, braidWord_pair,
      hmidE2, hmidE1, braidStep_pair_typeE ha₁1 ha₁K ha₂1 ha₂K]
    simp only [mul_assoc]
  -- the upper braid: the stage tuples
  set L₁ := l₁.map J.succAbove with hL₁
  set L₂ := l₂.map J'.succAbove with hL₂
  have hcU : ∀ t, (L₂ ++ L₁).count t = α' t - 1 := fun t =>
    (hpermU.count t).symm.trans (count_specialMoveList α' t)
  have hsufU : ∀ l, l <:+ L₂ ++ L₁ → ∀ t, l.count t + 1 ≤ α' t := fun l hl t => by
    have h1 := hl.count_le t
    rw [hcU] at h1
    have := hpos t
    omega
  have hmtU : ∀ (l : List (Fin (K + 1))) (t : Fin (K + 1)),
      moveTuple θ v' l t = (nextCrossing θ)^[l.count t] (v' t) :=
    fun l t => moveTuple_apply_eq_iterate v' l t
  have hinjU : ∀ l, l <:+ L₂ ++ L₁ → Function.Injective (moveTuple θ v' l) := fun l hl => by
    rw [show moveTuple θ v' l = fun t => (nextCrossing θ)^[l.count t] (v' t) from
      funext (hmtU l)]
    exact hdU.injective_iterate _ fun t => by have := hsufU l hl t; omega
  have hIooU : ∀ l, l <:+ L₂ ++ L₁ → ∀ t, moveTuple θ v' l t ∈ Set.Ioo (0 : ℚ) 1 :=
    fun l hl t => by
      rw [hmtU]
      exact hdU.iterate_mem_Ioo t _ (by have := hsufU l hl t; omega)
  have hneU : ∀ l, l <:+ L₂ ++ L₁ → ∀ t, moveTuple θ v' l t ≠ θ := fun l hl t => by
    rw [hmtU]
    exact hdU.ne_theta t _ (by have := hsufU l hl t; omega)
  have hsuf₁ : ∀ l', l' <:+ l₁ → l'.map J.succAbove <:+ L₂ ++ L₁ := fun l' hl' =>
    (hl'.map _).trans (List.suffix_append _ _)
  have hsuf₂ : ∀ l', l' <:+ l₂ → l'.map J'.succAbove ++ L₁ <:+ L₂ ++ L₁ := fun l' hl' =>
    List.suffix_append_self_iff.mpr (hl'.map _)
  -- a move-start stage lies below `v' J + θ`
  have hgapStage : ∀ (T : Fin (K + 1)) (m : ℕ), m + 1 < α' T →
      (nextCrossing θ)^[m] (v' T) < v' J + θ := by
    intro T m hm
    rw [hX₂]
    rcases m with _ | m
    · simp only [Function.iterate_zero, id_eq]
      linarith [hinit T]
    · rw [Function.iterate_succ_apply']
      have hy := hdU.iterate_mem_Ioo T m (by omega)
      have hyθ := hdU.ne_theta T m (by omega)
      rcases lt_or_gt_of_ne hyθ with h | h
      · have hS := hside T m (by omega) (fun hT => by rw [hT] at hm; omega)
        have h3 : (nextCrossing θ)^[m] (v' T) + δ < θ := hS.1.1 h
        rw [nextCrossing_of_lt h]
        linarith
      · rw [nextCrossing_of_gt h]
        linarith [hy.2]
  -- the first piece, with the second piece's starting point fixed: Mellit's `φ^*_+`
  have hrkJ : entryRank v' J = K + 1 := entryRank_eq_card_of_forall_le _ _ fun t => by
    by_cases h : t = J
    · rw [h]
    · exact (hmax t h).le
  have hU₁ := braidWord_map_succAbove_mul_trainDown_one_of_le hK J v' (by linarith [hinit J]) l₁
    (fun l' hl' => hinjU _ (hsuf₁ l' hl'))
    (fun l' hl' t => hIooU _ (hsuf₁ l' hl') t)
    (fun t₀ l' hl' => hneU _ (hsuf₁ l' ((List.suffix_cons t₀ l').trans hl')) _)
    (fun t₀ l' hl' => by
      rw [hmtU, hcountMap]
      refine hgapStage _ _ ?_
      have := hsufU _ (hsuf₁ _ hl') (J.succAbove t₀)
      rw [List.map_cons, List.count_cons_self, hcountMap] at this
      omega)
  rw [hrkJ] at hU₁
  -- the second piece, with the first piece's end point fixed: Mellit's `φ_-`
  set v'₁ := moveTuple θ v' L₁ with hv'₁
  have hv'₁app : ∀ l, moveTuple θ v'₁ l = moveTuple θ v' (l ++ L₁) := fun l =>
    (moveTuple_append θ v' l L₁).symm
  have hL₁J' : L₁.count J' = p := by
    rw [← hJsA, hcountMap, hc₁]
    simp
  have hv'₁J' : v'₁ J' = X₁ := by rw [hv'₁, hmtU, hL₁J']
  have hcomp₂ : v'₁ ∘ J'.succAbove = vE₂ := by
    funext i
    rw [Function.comp_apply, hv'₁, hmtU]
    by_cases hij : i = j
    · rw [hij, hJ'sA, hcountNotMem, hvE₂j]
      rfl
    · rw [← hsA i hij, hcountMap, hvE₂ne i hij, hvE₁]
  have hU₂ := trainUp_top_mul_braidWord_map_succAbove hK hθ.1.le J' v'₁
    (by rw [hv'₁J']; exact hX) l₂
    (fun l' hl' => by rw [hv'₁app]; exact hinjU _ (hsuf₂ l' hl'))
    (fun t₀ l' hl' => by
      rw [hv'₁app]; exact hneU _ (hsuf₂ l' ((List.suffix_cons t₀ l').trans hl')) _)
    (fun t₀ l' hl' hlt => by
      rw [hv'₁J']
      rw [hv'₁app, hmtU] at hlt ⊢
      have hb := hsufU _ (hsuf₂ _ hl') (J'.succAbove t₀)
      rw [List.map_cons, List.cons_append, List.count_cons_self] at hb
      have hS := hside (J'.succAbove t₀)
        ((l'.map J'.succAbove ++ L₁).count (J'.succAbove t₀)) (by omega)
        (fun h => absurd h (Fin.succAbove_ne J' t₀))
      have h3 := hS.1.1 hlt
      linarith)
  have hrkfin : entryRank (moveTuple θ v'₁ L₂) J' = K + 1 := by
    refine entryRank_eq_card_of_forall_le _ _ fun t => ?_
    rw [hv'₁app, hmtU, hmtU, hcU, hcU]
    by_cases h : t = J'
    · rw [h]
    · exact (hmaxfin t h).le
  rw [hrkfin, braidTrainUp_self, one_mul, hcomp₂] at hU₂
  -- the reconnection of the two pieces
  have hcomp₁ : v'₁ ∘ J.succAbove = vE₁ := moveTuple_comp_succAbove v' J l₁
  have hv'₁J : v'₁ J = v' J := moveTuple_map_succAbove_self v' J l₁
  have ha₁' : entryRank v'₁ J' = a₁ + (if v' J ≤ X₁ then 1 else 0) := by
    have h := entryRank_succAbove v'₁ J j
    rw [hJsA, hcomp₁, hv'₁J, hv'₁J'] at h
    exact h
  have ha₂' : entryRank v'₁ J = a₂ + (if X₁ ≤ v' J then 1 else 0) := by
    have h := entryRank_succAbove v'₁ J' j
    rw [hJ'sA, hcomp₂, hv'₁J, hv'₁J'] at h
    exact h
  have hne12 : v' J ≠ X₁ := by
    intro h
    have := hinjU L₁ (List.suffix_append _ _) (show v'₁ J = v'₁ J' by rw [hv'₁J, hv'₁J', h])
    exact hJJ' this
  have hcoll : braidTrainUp (K + 1) (K + 1) (entryRank v'₁ J') *
        braidTrainDown (K + 1) (entryRank v'₁ J) 1
      = braidTrainDown (K + 1) a₂ 1 * braidTrainUp (K + 1) (K + 1) (a₁ + 1) := by
    rcases lt_or_gt_of_ne hne12 with h | h
    · have ha₂a₁ : a₂ ≤ a₁ := by
        refine Finset.card_le_card fun t ht => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
        by_cases htj : t = j
        · rw [htj]
        · rw [hvE₂ne t htj, hvE₂j] at ht
          rw [hvE₁j]
          linarith
      rw [ha₁', ha₂']
      simp only [h.le, not_le.2 h, ite_true, ite_false, add_zero]
      exact trainUp_top_mul_trainDown_one_of_le ha₂1 ha₂a₁ ha₁K
    · have ha₁a₂ : a₁ ≤ a₂ := by
        refine Finset.card_le_card fun t ht => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
        by_cases htj : t = j
        · rw [htj]
        · rw [hvE₁j] at ht
          rw [hvE₂ne t htj, hvE₂j]
          linarith
      rw [ha₁', ha₂']
      simp only [h.le, not_le.2 h, ite_true, ite_false, add_zero]
      exact trainUp_top_mul_trainDown_one_of_ge ha₁1 ha₁a₂ ha₂K
  -- assembly
  obtain ⟨w, hw, hweq⟩ := exists_inRank_word (braidWord θ vE₂ l₂ * braidTrainDown K a₂ 1)
  refine ⟨braidTrainUp K 1 a₁ * braidWord θ vE l₁, w, hw, ?_, ?_, ?_⟩
  · change specialBraid θ (fun i => vE i + δ) αL = _
    rw [hlow, hweq]
    simp only [mul_assoc]
  · rw [hE, hweq]
    simp only [mul_assoc]
  · have e1 : braidTrainDown (K + 1) (K + 1) 1 * braidTrainDown (K + 1) 1 (K + 1) = 1 :=
      trainDown_mul_trainDown_self (isBraidSystem_braidGenT (K + 1)) (by omega) le_rfl le_rfl
        (by omega)
    have hU₁' : braidWord θ v' L₁
        = braidTrainDown (K + 1) (entryRank v'₁ J) 1 * phiPlusStar K hK (braidWord θ vE l₁) *
            braidTrainDown (K + 1) 1 (K + 1) := by
      calc braidWord θ v' L₁
          = braidWord θ v' L₁ * (braidTrainDown (K + 1) (K + 1) 1 *
              braidTrainDown (K + 1) 1 (K + 1)) := by rw [e1, mul_one]
        _ = _ := by rw [← mul_assoc, hU₁]; rfl
    have hphiplus : phiPlusStar K hK (braidTrainUp K K 1 * (braidTrainUp K 1 a₁ *
          braidWord θ vE l₁))
        = braidTrainUp (K + 1) (K + 1) (a₁ + 1) * phiPlusStar K hK (braidWord θ vE l₁) := by
      rw [← mul_assoc, trainUp_mul_trainUp (isBraidSystem_braidGenT K) (a := K) (b := 1)
          (c := a₁) hK le_rfl le_rfl hK ha₁1 ha₁K, map_mul,
        phiPlusStar_braidTrainUp hK hK ha₁1]
    have hw' : toBraidMonoid (K + 1) w
        = phiMinus K (braidWord θ vE₂ l₂) * braidTrainDown (K + 1) a₂ 1 := by
      rw [← phiMinus_toBraidMonoid hw, hweq, map_mul, phiMinus_braidTrainDown ha₂1 ha₂K le_rfl hK]
    rw [specialBraid, braidWord_perm_of_isSpecialBraidData hdU
        (fun t => (count_specialMoveList α' t).le) hpermU, braidWord_append, hU₂, hU₁', hphiplus,
      hw']
    calc phiMinus K (braidWord θ vE₂ l₂) * braidTrainUp (K + 1) (K + 1) (entryRank v'₁ J') *
          (braidTrainDown (K + 1) (entryRank v'₁ J) 1 * phiPlusStar K hK (braidWord θ vE l₁) *
            braidTrainDown (K + 1) 1 (K + 1))
        = phiMinus K (braidWord θ vE₂ l₂) * (braidTrainUp (K + 1) (K + 1) (entryRank v'₁ J') *
            braidTrainDown (K + 1) (entryRank v'₁ J) 1) * phiPlusStar K hK (braidWord θ vE l₁) *
              braidTrainDown (K + 1) 1 (K + 1) := by simp only [mul_assoc]
      _ = _ := by rw [hcoll]; simp only [mul_assoc]


/-- **Inserting a strict maximum adds `#\{t > j\}` inversions**: the mirror of
`HJO.Braid.tupleInversions_of_forall_lt`. -/
theorem tupleInversions_of_forall_gt {u : Fin (K + 1) → ℚ} {j : Fin (K + 1)}
    (h : ∀ t : Fin K, u (j.succAbove t) < u j) :
    tupleInversions u = tupleInversions (u ∘ j.succAbove) + #{t : Fin (K + 1) | j < t} := by
  classical
  have hmono := Fin.strictMono_succAbove j
  have hsplit : {p ∈ (univ : Finset (Fin (K + 1) × Fin (K + 1))) | p.1 < p.2 ∧ u p.2 < u p.1}
      = ({p ∈ (univ : Finset (Fin K × Fin K)) |
            p.1 < p.2 ∧ (u ∘ j.succAbove) p.2 < (u ∘ j.succAbove) p.1}.image
          fun p => (j.succAbove p.1, j.succAbove p.2))
        ∪ ({t ∈ (univ : Finset (Fin (K + 1))) | j < t}.image fun t => (j, t)) := by
    ext ⟨p1, p2⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_image,
      Function.comp_apply, Prod.mk.injEq]
    constructor
    · rintro ⟨h12, hu⟩
      by_cases h1 : p1 = j
      · subst h1
        exact Or.inr ⟨p2, h12, rfl, rfl⟩
      · have h2 : p2 ≠ j := by
          rintro rfl
          obtain ⟨t, ht⟩ := Fin.exists_succAbove_eq h1
          exact absurd hu (not_lt.2 (ht ▸ h t).le)
        obtain ⟨t1, ht1⟩ := Fin.exists_succAbove_eq h1
        obtain ⟨t2, ht2⟩ := Fin.exists_succAbove_eq h2
        refine Or.inl ⟨(t1, t2), ⟨?_, ?_⟩, ht1, ht2⟩
        · exact hmono.lt_iff_lt.1 (by rwa [ht1, ht2])
        · rwa [ht1, ht2]
    · rintro (⟨⟨t1, t2⟩, ⟨h12, hu⟩, rfl, rfl⟩ | ⟨t, ht, rfl, rfl⟩)
      · exact ⟨hmono h12, hu⟩
      · obtain ⟨t', ht'⟩ := Fin.exists_succAbove_eq (ne_of_gt ht)
        exact ⟨ht, ht' ▸ h t'⟩
  have hdisj : Disjoint
      (({p ∈ (univ : Finset (Fin K × Fin K)) |
          p.1 < p.2 ∧ (u ∘ j.succAbove) p.2 < (u ∘ j.succAbove) p.1}.image
        fun p => (j.succAbove p.1, j.succAbove p.2)))
      (({t ∈ (univ : Finset (Fin (K + 1))) | j < t}.image fun t => (j, t))) := by
    refine Finset.disjoint_left.2 fun p hp hq => ?_
    obtain ⟨⟨t1, t2⟩, -, hp'⟩ := Finset.mem_image.1 hp
    obtain ⟨t, -, hq'⟩ := Finset.mem_image.1 hq
    rw [← hp'] at hq'
    exact j.succAbove_ne t1 (congrArg Prod.fst hq').symm
  rw [tupleInversions_eq_card_lt, tupleInversions_eq_card_lt, hsplit,
    Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ fun p p' hpp => Prod.ext
      (j.succAbove_right_injective (congrArg Prod.fst hpp))
      (j.succAbove_right_injective (congrArg Prod.snd hpp)),
    Finset.card_image_of_injective _ fun t t' htt => congrArg Prod.snd htt]


theorem card_castSucc_lt_eq_card_succ_lt_add_one (j : Fin K) :
    #{t : Fin (K + 1) | j.castSucc < t} = #{t : Fin (K + 1) | j.succ < t} + 1 := by
  have h : (Finset.univ.filter fun t : Fin (K + 1) => j.castSucc < t)
      = insert j.succ (Finset.univ.filter fun t : Fin (K + 1) => j.succ < t) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.lt_def,
      Fin.val_castSucc, Fin.val_succ, Fin.ext_iff]
    omega
  rw [h, Finset.card_insert_of_notMem (by simp)]

/-- **Mellit's two inversion counts for rule `BE`**, for the abstract data of
`HJO.Braid.specialBraid_cut`: the type-`E` data has the lower data's `inv_fin - inv_ini`, and the
upper data has one less. -/
theorem invFin_sub_invIni_cut (j : Fin K) (v' : Fin (K + 1) → ℚ) (α' : Fin (K + 1) → ℕ)
    (δ : ℚ) (hdU : IsSpecialBraidData s θ (K + 1) v' α')
    (hside : ∀ (t : Fin (K + 1)) (m : ℕ), m < α' t → (t = j.succ → m ≠ α' j.succ - 1) →
      SameSide θ δ ((nextCrossing θ)^[m] (v' t)))
    (hX : (nextCrossing θ)^[α' j.succ - 1] (v' j.succ) < θ)
    (hXδ : θ < (nextCrossing θ)^[α' j.succ - 1] (v' j.succ) + δ)
    (hXδ' : (nextCrossing θ)^[α' j.succ - 1] (v' j.succ) + δ < θ + θ)
    (hX₂ : v' j.castSucc = (nextCrossing θ)^[α' j.succ - 1] (v' j.succ) + 1 - θ - θ)
    (hmax : ∀ t, t ≠ j.castSucc → v' t < v' j.castSucc)
    (hmaxfin : ∀ t, t ≠ j.succ →
      (nextCrossing θ)^[α' t - 1] (v' t) < (nextCrossing θ)^[α' j.succ - 1] (v' j.succ)) :
    ((invFin θ (fun i => v' (j.castSucc.succAbove i))
          (Function.update (fun i => α' (j.castSucc.succAbove i)) j
            (α' j.castSucc + α' j.succ + 1)) : ℤ)
        - invIni θ (fun i => v' (j.castSucc.succAbove i))
          (Function.update (fun i => α' (j.castSucc.succAbove i)) j
            (α' j.castSucc + α' j.succ + 1))
      = (invFin θ (fun i => v' (j.castSucc.succAbove i) + δ)
          (Function.update (fun i => α' (j.castSucc.succAbove i)) j
            (α' j.castSucc + α' j.succ + 1)) : ℤ)
        - invIni θ (fun i => v' (j.castSucc.succAbove i) + δ)
          (Function.update (fun i => α' (j.castSucc.succAbove i)) j
            (α' j.castSucc + α' j.succ + 1))) ∧
    ((invFin θ v' α' : ℤ) - invIni θ v' α'
      = (invFin θ (fun i => v' (j.castSucc.succAbove i) + δ)
          (Function.update (fun i => α' (j.castSucc.succAbove i)) j
            (α' j.castSucc + α' j.succ + 1)) : ℤ)
        - invIni θ (fun i => v' (j.castSucc.succAbove i) + δ)
          (Function.update (fun i => α' (j.castSucc.succAbove i)) j
            (α' j.castSucc + α' j.succ + 1)) - 1) := by
  set J : Fin (K + 1) := j.castSucc with hJ
  set J' : Fin (K + 1) := j.succ with hJ'
  set αL : Fin K → ℕ := Function.update (fun i => α' (J.succAbove i)) j (α' J + α' J' + 1)
    with hαL
  set vE : Fin K → ℚ := fun i => v' (J.succAbove i) with hvE
  set X₁ := (nextCrossing θ)^[α' J' - 1] (v' J') with hX₁
  set p := α' J' - 1 with hp
  set q := α' J - 1 with hq
  have hJsA : J.succAbove j = J' := Fin.succAbove_castSucc_self j
  have hJ'sA : J'.succAbove j = J := Fin.succAbove_succ_self j
  have hsAne : ∀ i, i ≠ j → J.succAbove i ≠ J' := fun i h h' =>
    h (Fin.succAbove_right_injective (h'.trans hJsA.symm))
  have hJJ' : J ≠ J' := by
    intro h
    have := congrArg Fin.val h
    simp [J, J'] at this
  have hpos : ∀ t, 1 ≤ α' t := hdU.one_le_mult
  have hαj : αL j - 1 = q + (2 + p) := by
    simp only [αL, Function.update_self]
    have := hpos J; have := hpos J'
    omega
  have hαi : ∀ i, i ≠ j → αL i = α' (J.succAbove i) := fun i h => by
    simp [αL, Function.update_of_ne h]
  have hvEj : vE j = v' J' := by simp [vE, hJsA]
  have hvJpos : 0 < v' J := (hdU.mem_Ioo J).1
  -- the shift commutes with the iterates up to the end of the strand `J'`
  have hpre : (nextCrossing θ)^[p] (vE j + δ) = X₁ + δ := by
    rw [hvEj]
    exact iterate_nextCrossing_add p fun m hm => hside J' m (by omega) (fun _ => by omega)
  have hpass : (nextCrossing θ)^[2] (X₁ + δ) = v' J + δ := by
    rw [Function.iterate_succ_apply', Function.iterate_one, nextCrossing_of_gt hXδ,
      nextCrossing_of_lt (by linarith : X₁ + δ - θ < θ), hX₂]
    ring
  have hpassE : (nextCrossing θ)^[2] X₁ = v' J := by
    rw [Function.iterate_succ_apply', Function.iterate_one, nextCrossing_of_lt hX,
      nextCrossing_of_gt (by linarith : θ < X₁ + 1 - θ), hX₂]
  have hfinE : ∀ i, (nextCrossing θ)^[αL i - 1] (vE i + δ)
      = (nextCrossing θ)^[αL i - 1] (vE i) + δ := by
    intro i
    by_cases hij : i = j
    · rw [hij, hαj, Function.iterate_add_apply, Function.iterate_add_apply, hpre, hpass,
        Function.iterate_add_apply, Function.iterate_add_apply, hvEj, ← hX₁, hpassE]
      exact iterate_nextCrossing_add q fun m hm =>
        hside J m (by omega) (fun h => absurd h hJJ')
    · rw [hαi i hij]
      exact iterate_nextCrossing_add _ fun m hm =>
        hside (J.succAbove i) m (by omega) (fun h => absurd h (hsAne i hij))
  have hini : invIni θ (fun i => vE i + δ) αL = invIni θ vE αL := invIni_congr_add θ δ vE αL
  have hfin : invFin θ (fun i => vE i + δ) αL = invFin θ vE αL := by
    rw [invFin_eq_tupleInversions, invFin_eq_tupleInversions]
    exact tupleInversions_congr_add hfinE
  refine ⟨by rw [hini, hfin], ?_⟩
  -- the upper data: the strand `J` is the top of the initial tuple, `J'` of the final one
  have hiniU : invIni θ v' α' = invIni θ vE αL + #{t : Fin (K + 1) | J < t} := by
    rw [invIni_eq_tupleInversions, invIni_eq_tupleInversions,
      tupleInversions_of_forall_gt (u := v') (j := J) fun t => hmax _ (Fin.succAbove_ne J t)]
    rfl
  have hcompF : (fun t => (nextCrossing θ)^[α' t - 1] (v' t)) ∘ J'.succAbove
      = fun i => (nextCrossing θ)^[αL i - 1] (vE i) := by
    funext i
    rw [Function.comp_apply]
    by_cases hij : i = j
    · rw [hij, hJ'sA, hαj, Function.iterate_add_apply, Function.iterate_add_apply, hvEj,
        ← hX₁, hpassE]
    · rw [← castSucc_succAbove_eq_succ_succAbove hij, hαi i hij]
  have hfinU : invFin θ v' α' = invFin θ vE αL + #{t : Fin (K + 1) | J' < t} := by
    rw [invFin_eq_tupleInversions, invFin_eq_tupleInversions,
      tupleInversions_of_forall_gt (u := fun t => (nextCrossing θ)^[α' t - 1] (v' t)) (j := J')
        fun t => hmaxfin _ (Fin.succAbove_ne J' t), hcompF]
  rw [hini, hfin, hiniU, hfinU, card_castSucc_lt_eq_card_succ_lt_add_one j]
  push_cast
  ring


end CutData

end HJO.Braid

namespace HJO.Mellit

open ParkingFunctions Paths Sweep Braid Finset

variable {a b N X Y : ℕ} {ηlo ηhi : ℚ}

/-- One attack window of rank is one `θ` of position. -/
theorem levelPosition_add_attackWindow (ha : 0 < a) (hN : 0 < N) (η r : ℚ) :
    levelPosition a b N η (r + ((attackWindow a N : ℕ) : ℚ))
      = levelPosition a b N η r + sweepTheta a b N := by
  have hM := rankDen_pos (a := a) (N := N) ha hN
  rw [levelPosition, levelPosition, cast_attackWindow_eq]
  field_simp
  ring

/-- **The final position of a component is the normalised rank of the lattice point above its
crossed north step**, as a `HJO.Mellit.levelPosition`. -/
theorem positionPair_snd_braidDataOfColouring_eq_levelPosition (ha : 0 < a) (hb : 0 < b)
    (hN : 0 < N) {η : ℚ} (hη : IsAdmissibleLevel η) (hηN : ((a * N : ℕ) : ℚ) < η)
    {y : Heights a b N} (hy : IsAboveDiagonal y) {k : ℕ} (i : Fin k)
    (hi : (i : ℕ) < #(colouringNorth y η)) :
    (positionPair (sweepTheta a b N) (braidDataOfColouring a b N y η k).1
        (braidDataOfColouring a b N y η k).2).2 i
      = levelPosition a b N η (((pointRank a b N (colStep (colouringNorth y η) (i : ℕ)) : ℤ) : ℚ)
          + ((attackWindow a N : ℕ) : ℚ)) := by
  rw [positionPair_snd_braidDataOfColouring_eq_div ha hb hN hη hηN hy i hi,
    levelPosition_eq_div_rankSpan ha hb hN, crossDen]
  push_cast
  ring_nf


namespace Isolates

/-- **Mellit's cut at a bracketed point.** At a type-`B`/type-`E` pair above the floor, the special
braids and the inversion counts of the lower colouring, the type-`E` colouring at the upper level
and the upper colouring are as in `HJO.Braid.specialBraid_cut` and
`HJO.Braid.invFin_sub_invIni_cut`. The hypotheses of those two are read off the colourings: the
data through the type-`B` row of the dictionary (`HJO.Mellit.Isolates.braidData_of_eventType_B`)
and its type-`E` counterpart, the positions near the puncture through the ranks of `(X, Y)`,
`(X - 1, Y)` and `(X, Y + 1)`, and the absence of any other crossing of the puncture through
`HJO.Mellit.sameSide_levelDropShift_of_ne`. -/
theorem cut_of_bePair (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) (hI : Isolates a b N X Y ηlo ηhi)
    (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {yB yE : Heights a b N} (hyB : IsAboveDiagonal yB)
    (hyE : IsAboveDiagonal yE) (hevB : eventType yB (X, Y) = EventType.B)
    (hevE : eventType yE (X, Y) = EventType.E) (hcol : colouring yB ηlo = colouring yE ηlo)
    {k : ℕ} (hk : #(colouringEast yB ηlo) = k + 1) :
    ∃ (B₁ : BraidMonoid (k + 1)) (w : FreeMonoid Letter),
      (∀ c ∈ w.toList, Letter.InRank (k + 1) c) ∧
      specialBraid (sweepTheta a b N) (braidDataOfColouring a b N yB ηlo (k + 1)).1
          (braidDataOfColouring a b N yB ηlo (k + 1)).2
        = toBraidMonoid (k + 1) w * (braidGenZ (k + 1) 1 * braidYtilde (k + 1) 1) * B₁ ∧
      specialBraid (sweepTheta a b N) (braidDataOfColouring a b N yE ηhi (k + 1)).1
          (braidDataOfColouring a b N yE ηhi (k + 1)).2
        = toBraidMonoid (k + 1) w * (braidGenY (k + 1) 1 * braidGenZ (k + 1) 1) * B₁ ∧
      specialBraid (sweepTheta a b N)
          (braidDataOfColouring a b N yB ηhi (k + 1 + 1)).1
          (braidDataOfColouring a b N yB ηhi (k + 1 + 1)).2
        = toBraidMonoid (k + 1 + 1) w *
            phiPlusStar (k + 1) (by omega) (braidTrainUp (k + 1) (k + 1) 1 * B₁) *
            braidTrainDown (k + 1 + 1) 1 (k + 1 + 1) ∧
      (invFin (sweepTheta a b N) (braidDataOfColouring a b N yE ηhi (k + 1)).1
            (braidDataOfColouring a b N yE ηhi (k + 1)).2 : ℤ)
          - invIni (sweepTheta a b N) (braidDataOfColouring a b N yE ηhi (k + 1)).1
            (braidDataOfColouring a b N yE ηhi (k + 1)).2
        = (invFin (sweepTheta a b N) (braidDataOfColouring a b N yB ηlo (k + 1)).1
            (braidDataOfColouring a b N yB ηlo (k + 1)).2 : ℤ)
          - invIni (sweepTheta a b N) (braidDataOfColouring a b N yB ηlo (k + 1)).1
            (braidDataOfColouring a b N yB ηlo (k + 1)).2 ∧
      (invFin (sweepTheta a b N) (braidDataOfColouring a b N yB ηhi (k + 1 + 1)).1
            (braidDataOfColouring a b N yB ηhi (k + 1 + 1)).2 : ℤ)
          - invIni (sweepTheta a b N)
            (braidDataOfColouring a b N yB ηhi (k + 1 + 1)).1
            (braidDataOfColouring a b N yB ηhi (k + 1 + 1)).2
        = (invFin (sweepTheta a b N) (braidDataOfColouring a b N yB ηlo (k + 1)).1
            (braidDataOfColouring a b N yB ηlo (k + 1)).2 : ℤ)
          - invIni (sweepTheta a b N) (braidDataOfColouring a b N yB ηlo (k + 1)).1
            (braidDataOfColouring a b N yB ηlo (k + 1)).2 - 1 := by
  have hX0 : 0 < X := hI.pos_fst_of_eventType_B_of_lt hηlo hyB hevB
  have hηhi : ((a * N : ℕ) : ℚ) < ηhi := hηlo.trans (hI.ltP.trans hI.Plt)
  have hlopos : (0 : ℚ) < ηlo := lt_of_le_of_lt (Nat.cast_nonneg _) hηlo
  have hhipos : (0 : ℚ) < ηhi := lt_of_le_of_lt (Nat.cast_nonneg _) hηhi
  have hle := hI.typeBIndex_succ_le ha hb hN hηlo hyB hevB
  rw [hk] at hle
  have hcardE : #(colouringEast yB ηhi) = k + 1 + 1 := by
    rw [hI.card_colouringEast_of_eventType_B ha hb hN hX0 hevB, hk]
  have hcardNlo : #(colouringNorth yB ηlo) = k + 1 := by
    rw [card_colouringNorth_eq_card_colouringEast hb hN hI.lo hηlo hyB, hk]
  have hcardN : #(colouringNorth yB ηhi) = k + 1 + 1 := by
    rw [hI.card_colouringNorth_of_eventType_B ha hN hevB, hcardNlo]
  have hEE : colouringEast yE ηhi = colouringEast yB ηlo :=
    hI.colouringEast_eq_of_bePair ha hN hyE hevE hcol
  have hcardNE : #(colouringNorth yE ηhi) = k + 1 := by
    rw [card_colouringNorth_eq_card_colouringEast hb hN hI.hi hηhi hyE, hEE, hk]
  set j : Fin (k + 1) := ⟨typeBIndex yB ηlo X, by omega⟩ with hj
  set v' := (braidDataOfColouring a b N yB ηhi (k + 1 + 1)).1 with hv'
  set α' := (braidDataOfColouring a b N yB ηhi (k + 1 + 1)).2 with hα'
  set δ := levelDropShift a b N ηlo ηhi with hδ
  have hdU : IsSpecialBraidData (sweepSlope a b N) (sweepTheta a b N) (k + 1 + 1) v' α' :=
    isSpecialBraidData_braidDataOfColouring_of_card ha hb hN hI.hi hηhi hyB hcardN
  -- the lower data, through the dictionary
  have hlo := hI.braidData_of_eventType_B ha hb hN hηlo hyB hevB hk j.castSucc j.succ
    (by simp [hj]) (by simp [hj]) j (by simp [hj])
  rw [← hv', ← hα', ← hδ] at hlo
  -- the type-`E` data
  have hEdata : braidDataOfColouring a b N yE ηhi (k + 1)
      = ((fun i => v' (j.castSucc.succAbove i)),
        Function.update (fun i => α' (j.castSucc.succAbove i)) j
          (α' j.castSucc + α' j.succ + 1)) := by
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · have hiE : (i : ℕ) < #(colouringEast yE ηhi) := by rw [hEE, hk]; exact i.isLt
      have hiL : (i : ℕ) < #(colouringEast yB ηlo) := by rw [hk]; exact i.isLt
      have h1 := braidDataOfColouring_fst_eq_levelPosition ha hb hN hI.hi hhipos i hiE
      have h2 := braidDataOfColouring_fst_eq_levelPosition ha hb hN hI.lo hlopos i hiL
      rw [hEE] at h1
      rw [levelPosition_eq_add_levelDropShift ηlo ηhi, ← hδ, ← h1] at h2
      have h3 := congrArg (fun d => d.1 i) hlo
      simp only at h3
      dsimp only
      linarith
    · have h1 := hI.braidData_bePair_snd ha hb hN hηlo hyE hevE hcol hk i
      rw [h1, hlo]
  -- the geometry of the upper data
  have hJval : ((j.castSucc : Fin (k + 1 + 1)) : ℕ) = typeBIndex yB ηlo X := by simp [hj]
  have hJ'val : ((j.succ : Fin (k + 1 + 1)) : ℕ) = typeBIndex yB ηlo X + 1 := by simp [hj]
  have hPnorth : colStep (colouringNorth yB ηhi) ((j.succ : Fin (k + 1 + 1)) : ℕ) = (X, Y) := by
    rw [hJ'val]; exact hI.colStep_colouringNorth_hi_typeBIndex_succ ha hb hN hηlo hyB hevB
  have hPeast : colStep (colouringEast yB ηhi) ((j.castSucc : Fin (k + 1 + 1)) : ℕ)
      = (X - 1, Y) := by
    rw [hJval]; exact hI.colStep_colouringEast_hi_typeBIndex ha hb hN hX0 hevB
  have hfin : ∀ t : Fin (k + 1 + 1), (nextCrossing (sweepTheta a b N))^[α' t - 1] (v' t)
      = levelPosition a b N ηhi
          (((pointRank a b N (colStep (colouringNorth yB ηhi) (t : ℕ)) : ℤ) : ℚ)
            + ((attackWindow a N : ℕ) : ℚ)) := fun t =>
    positionPair_snd_braidDataOfColouring_eq_levelPosition ha hb hN hI.hi hηhi hyB t
      (by rw [hcardN]; exact t.isLt)
  have hX₁eq : (nextCrossing (sweepTheta a b N))^[α' j.succ - 1] (v' j.succ)
      = levelPosition a b N ηhi (((pointRank a b N (X, Y) : ℤ) : ℚ)
          + ((attackWindow a N : ℕ) : ℚ)) := by
    rw [hfin, hPnorth]
  have hX : (nextCrossing (sweepTheta a b N))^[α' j.succ - 1] (v' j.succ) < sweepTheta a b N := by
    rw [hX₁eq]
    exact (levelPosition_lt_sweepTheta_iff ha hb hN _ _).2 (by linarith [hI.Plt])
  have hXδ : sweepTheta a b N
      < (nextCrossing (sweepTheta a b N))^[α' j.succ - 1] (v' j.succ) + δ := by
    rw [hX₁eq, hδ, ← levelPosition_eq_add_levelDropShift]
    exact (sweepTheta_lt_levelPosition_iff ha hb hN _ _).2 (by linarith [hI.ltP])
  have hXδ' : (nextCrossing (sweepTheta a b N))^[α' j.succ - 1] (v' j.succ) + δ
      < sweepTheta a b N + sweepTheta a b N := by
    rw [hX₁eq, hδ, ← levelPosition_eq_add_levelDropShift, levelPosition_add_attackWindow ha hN]
    have := levelPosition_lt_sweepTheta (b := b) ha hb hN
      (hI.pointRank_lt_lo_add_attackWindow ha hb hN hlopos.le)
    linarith
  have hX₂ : v' j.castSucc = (nextCrossing (sweepTheta a b N))^[α' j.succ - 1] (v' j.succ)
      + 1 - sweepTheta a b N - sweepTheta a b N := by
    rw [hv', hI.braidData_fst_typeBIndex ha hb hN hηlo hyB hevB hk j.castSucc hJval, ← hv',
      hX₁eq, levelPosition_add_attackWindow ha hN]
    have h2 := cast_pointRank_succ_fst a b N (X - 1) Y
    rw [show X - 1 + 1 = X from by omega] at h2
    rw [show ((pointRank a b N ((X - 1 : ℕ), Y) : ℤ) : ℚ)
        = ((pointRank a b N (X, Y) : ℤ) : ℚ) + ((b : ℚ) * ((a : ℚ) * N + 1) * N - 1) by linarith,
      levelPosition_add_bMN_sub_one ha hb hN]
    ring
  have hinit : ∀ t, v' t < 1 - sweepTheta a b N := fun t =>
    braidDataOfColouring_fst_lt_one_sub_sweepTheta ha hb hN hI.hi hhipos t
      (by rw [hcardE]; exact t.isLt)
  have hmax : ∀ t, t ≠ j.castSucc → v' t < v' j.castSucc := by
    intro t ht
    refine lt_of_le_of_ne ?_ fun h => ht (hdU.injective t _ 0 0 (hdU.one_le_mult t)
      (hdU.one_le_mult _) h).1
    rw [hv', braidDataOfColouring_fst_eq_levelPosition ha hb hN hI.hi hhipos t
        (by rw [hcardE]; exact t.isLt),
      braidDataOfColouring_fst_eq_levelPosition ha hb hN hI.hi hhipos j.castSucc
        (by rw [hcardE]; exact j.castSucc.isLt), hPeast]
    exact levelPosition_le_levelPosition ha hb hN ηhi
      (hI.pointRank_colStep_le_of_eventType_D hX0 hcardE t)
  have hmaxfin : ∀ t, t ≠ j.succ → (nextCrossing (sweepTheta a b N))^[α' t - 1] (v' t)
      < (nextCrossing (sweepTheta a b N))^[α' j.succ - 1] (v' j.succ) := by
    intro t ht
    refine lt_of_le_of_ne ?_ fun h => ht (injective_positionPair_snd_of_isSpecialBraidData hdU h)
    rw [hfin t, hX₁eq]
    refine levelPosition_le_levelPosition ha hb hN ηhi ?_
    have hmem : colStep (colouringNorth yB ηhi) (t : ℕ) ∈ colouringNorth yB ηhi :=
      colStep_mem (by rw [hcardN]; exact t.isLt)
    obtain ⟨x, w, hxw⟩ : ∃ x w, colStep (colouringNorth yB ηhi) (t : ℕ) = (x, w) := ⟨_, _, rfl⟩
    rw [hxw] at hmem ⊢
    have hlt : ((pointRank a b N (x, w) : ℤ) : ℚ) < ηhi := (Finset.mem_filter.1 hmem).2.1
    obtain ⟨hxa, -, hwht⟩ := mem_northSteps_iff.1 (Finset.mem_filter.1 hmem).1
    have := hI.le_pointRank (Q := (x, w)) hxa.le ((hwht.trans_le (ht_le_mul yB _)).le) hlt
    linarith
  have hside : ∀ (t : Fin (k + 1 + 1)) (m : ℕ), m < α' t → (t = j.succ → m ≠ α' j.succ - 1) →
      SameSide (sweepTheta a b N) δ ((nextCrossing (sweepTheta a b N))^[m] (v' t)) := by
    intro t m hm hne
    obtain ⟨x, yy, hsum, hbot, hx, hyy0, hyyle, -, hfr⟩ :=
      exists_pointRank_iterate_nextCrossing_eq_sub ha hb hN hI.hi hηhi hyB hcardE t
        (m := m) (show m ≤ α' t - 1 by omega)
    rw [hfr]
    refine sameSide_levelDropShift_of_ne ha hb hN hI hx.le
      (le_trans (hyyle.trans (ht_le_mul yB _)) (by omega)) hyy0 ?_
    intro hQ
    have hx1 : x = X := congrArg Prod.fst hQ
    have hy1 : yy = Y + 1 := congrArg Prod.snd hQ
    have hsum' : (x : ℤ) + (yy : ℤ) = (X : ℤ) + (Y : ℤ) + 1 := by
      rw [hx1, hy1]; push_cast; ring
    have hbotJ' : componentBotIndex a b N yB ηhi ((j.succ : Fin (k + 1 + 1)) : ℕ)
        = (X : ℤ) + (Y : ℤ) + 1 := by
      rw [hJ'val]; exact hI.componentBotIndex_hi_typeBIndex_succ ha hb hN hηlo hyB hevB
    have hJ'lt : ((j.succ : Fin (k + 1 + 1)) : ℕ) < #(colouringNorth yB ηhi) := by
      rw [hcardN]; exact j.succ.isLt
    have htlt : (t : ℕ) < #(colouringNorth yB ηhi) := by rw [hcardN]; exact t.isLt
    have hleJ' := componentBotIndex_le_componentTopIndex ha hb hN hI.hi hηhi hyB hJ'lt
    have hlet := componentBotIndex_le_componentTopIndex ha hb hN hI.hi hηhi hyB htlt
    have hαt := braidDataOfColouring_snd_eq_toNat a b N yB ηhi (k + 1 + 1) t
    rw [← hα'] at hαt
    rcases lt_trichotomy (t : ℕ) ((j.succ : Fin (k + 1 + 1)) : ℕ) with hlt | heq | hgt
    · have := componentTopIndex_lt_componentBotIndex ha hb hN hI.hi hηhi hyB hJ'lt hlt
      omega
    · have hteq : t = j.succ := Fin.ext heq
      have hm' := hne hteq
      rw [hteq] at hsum hαt hm
      rw [hbotJ'] at hleJ'
      omega
    · have := componentTopIndex_lt_componentBotIndex ha hb hN hI.hi hηhi hyB htlt hgt
      omega
  -- the two smaller data are special-braid data
  have hdE := isSpecialBraidData_braidDataOfColouring_of_card ha hb hN hI.hi hηhi hyE hcardNE
  rw [hEdata] at hdE
  have hdL := isSpecialBraidData_braidDataOfColouring_of_card ha hb hN hI.lo hηlo hyB hcardNlo
  rw [hlo] at hdL
  obtain ⟨B₁, w, hw, h1, h2, h3⟩ := specialBraid_cut (by omega : 1 ≤ k + 1) j v' α' δ hdU hdE hdL
    hside hX hXδ hXδ' hX₂ hinit hmax hmaxfin
  obtain ⟨i1, i2⟩ := invFin_sub_invIni_cut j v' α' δ hdU hside hX hXδ hXδ' hX₂ hmax hmaxfin
  refine ⟨B₁, w, hw, ?_, ?_, h3, ?_, ?_⟩
  · rw [hlo]; exact h1
  · rw [hEdata]; exact h2
  · rw [hEdata, hlo]; exact i1
  · rw [hlo]; exact i2

end Isolates

/-- **Mellit's cut, at every bracketed point**: the hypothesis `hcut` of
`HJO.Mellit.braidValueColouring_sweepRecursionBEFloor_of_cut`, discharged. At every
type-`B`/type-`E` pair above the floor the special braids of the lower colouring, the type-`E`
colouring and the upper colouring are `w z_1ỹ_1 B̃_1`, `w y_1z_1 B̃_1` and
`w φ^*_+(T^*_{k+1↘1}B̃_1) T_{1↘k+2}`, and Mellit's two inversion counts hold; see
`HJO.Mellit.Isolates.cut_of_bePair`. -/
theorem braidValueColouring_hcut {a b N : ℕ} (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) :
    ∀ (X Y : ℕ) (ηlo ηhi : ℚ), ((a * N : ℕ) : ℚ) < ηlo →
      Isolates a b N X Y ηlo ηhi → ∀ yB yE : Heights a b N, IsAboveDiagonal yB →
        IsAboveDiagonal yE → eventType yB (X, Y) = EventType.B →
          eventType yE (X, Y) = EventType.E → colouring yB ηlo = colouring yE ηlo →
            ∀ k : ℕ, #(colouringEast yB ηlo) = k + 1 →
              ∃ (B₁ : BraidMonoid (k + 1)) (w : FreeMonoid Letter),
                (∀ c ∈ w.toList, Letter.InRank (k + 1) c) ∧
                specialBraid (sweepTheta a b N) (braidDataOfColouring a b N yB ηlo (k + 1)).1
                    (braidDataOfColouring a b N yB ηlo (k + 1)).2
                  = toBraidMonoid (k + 1) w * (braidGenZ (k + 1) 1 * braidYtilde (k + 1) 1) * B₁ ∧
                specialBraid (sweepTheta a b N) (braidDataOfColouring a b N yE ηhi (k + 1)).1
                    (braidDataOfColouring a b N yE ηhi (k + 1)).2
                  = toBraidMonoid (k + 1) w * (braidGenY (k + 1) 1 * braidGenZ (k + 1) 1) * B₁ ∧
                specialBraid (sweepTheta a b N)
                    (braidDataOfColouring a b N yB ηhi (k + 1 + 1)).1
                    (braidDataOfColouring a b N yB ηhi (k + 1 + 1)).2
                  = toBraidMonoid (k + 1 + 1) w *
                      phiPlusStar (k + 1) (by omega) (braidTrainUp (k + 1) (k + 1) 1 * B₁) *
                      braidTrainDown (k + 1 + 1) 1 (k + 1 + 1) ∧
                (invFin (sweepTheta a b N) (braidDataOfColouring a b N yE ηhi (k + 1)).1
                      (braidDataOfColouring a b N yE ηhi (k + 1)).2 : ℤ)
                    - invIni (sweepTheta a b N) (braidDataOfColouring a b N yE ηhi (k + 1)).1
                      (braidDataOfColouring a b N yE ηhi (k + 1)).2
                  = (invFin (sweepTheta a b N) (braidDataOfColouring a b N yB ηlo (k + 1)).1
                      (braidDataOfColouring a b N yB ηlo (k + 1)).2 : ℤ)
                    - invIni (sweepTheta a b N) (braidDataOfColouring a b N yB ηlo (k + 1)).1
                      (braidDataOfColouring a b N yB ηlo (k + 1)).2 ∧
                (invFin (sweepTheta a b N) (braidDataOfColouring a b N yB ηhi (k + 1 + 1)).1
                      (braidDataOfColouring a b N yB ηhi (k + 1 + 1)).2 : ℤ)
                    - invIni (sweepTheta a b N)
                      (braidDataOfColouring a b N yB ηhi (k + 1 + 1)).1
                      (braidDataOfColouring a b N yB ηhi (k + 1 + 1)).2
                  = (invFin (sweepTheta a b N) (braidDataOfColouring a b N yB ηlo (k + 1)).1
                      (braidDataOfColouring a b N yB ηlo (k + 1)).2 : ℤ)
                    - invIni (sweepTheta a b N) (braidDataOfColouring a b N yB ηlo (k + 1)).1
                      (braidDataOfColouring a b N yB ηlo (k + 1)).2 - 1 :=
  fun _ _ _ _ hfloor hI _ _ hyB hyE hevB hevE hcol _ hk =>
    hI.cut_of_bePair ha hb hN hfloor hyB hyE hevB hevE hcol hk

/-- **The floored `BE` clause of the level recursion holds for the braid candidate**:
`HJO.Mellit.braidValueColouring_sweepRecursionBEFloor_of_cut` with its hypothesis discharged by
`HJO.Mellit.braidValueColouring_hcut`. The hypothesis `a < b` is not used. -/
theorem braidValueColouring_sweepRecursionBEFloor {L : Type*} [Field L] [Algebra ℚ L] (q u : L)
    {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) (hr : r * r = q) (hu : u ≠ 0)
    {a b N : ℕ} (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) (_hab : a < b) :
    SweepRecursionBEFloor q u a b N (braidValueColouring q u hq hq1 hqp hr a b N) :=
  braidValueColouring_sweepRecursionBEFloor_of_cut q u hq hq1 hqp hr hu ha hb hN
    (braidValueColouring_hcut ha hb hN)

end HJO.Mellit

end
