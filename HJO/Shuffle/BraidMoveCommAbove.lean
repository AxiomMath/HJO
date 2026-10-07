/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidYtildeMellit
public meta import HJO.Attr

/-! # Exchanging the moves of two distinct points above the puncture

`HJO/Shuffle/BraidMoveComm.lean` reduces the exchange lemma `HJO.Braid.braidWord_pair_comm` to one
adjacent pair of moves (`HJO.Braid.braidWord_swap_of_pair_comm`, letter-type agnostic) and settles
the case of two points **below** the puncture. Of the three surviving letter-type pairs — the fourth
is empty, since `θ < w_i` and `w_i < w_j` force `θ < w_j` — this file settles the case of two points
**above** it, where both moves read a `ỹ`.

## Main results

* `HJO.Braid.ytildeBlock_comm_of_separated` — the `ỹ`-analogue of
  `HJO.Braid.zBlock_comm_of_separated`: two `ỹ`-blocks whose rank ranges are separated commute.
* `HJO.Braid.ytildeBlock_comm_of_overtake` — the `ỹ`-analogue of
  `HJO.Braid.zBlock_comm_of_overtake`, and the case where the intermediate ranks genuinely differ.
* `HJO.Braid.braidWord_pair_comm_of_gt_theta` — **the exchange lemma for two points above the
  puncture**: if both moving entries are `> θ` then the two orders give the same braid.
* `HJO.Braid.braidWord_swap_of_gt_theta` — the same, read on a sequence of moves.

## Implementation notes

### The arithmetic is mirrored, not copied

Write `x = w_i`, `y = w_j` and suppose `x < y`. Above the puncture `HJO.Braid.nextCrossing` reads
`nx_θ(x) = x - θ`, so both values **fall** and each point's rank **falls**: the descending train
`T_{a'↘a}` of `HJO.Braid.braidStep` has `a' ≤ a` and is therefore on its *inverted* branch, the word
`T̄_{a'} ⋯ T̄_{a-1}`.

With `0 < θ` the five settled comparisons are `x < y`, `x' < x`, `y' < y`, `x' < y'` and `x' < y`,
and the sixth — `y'` against `x` — is the case division. It is the *upper* point that can overtake,
by falling below the lower one, where below the puncture it was the lower point that overtook by
rising above the upper one. So the two configurations are the mirror images of the two of the
`z`–`z` case, and the four intermediate ranks come out in the opposite order: below the puncture the
quadruple is `A ≤ B ≤ A' ≤ B'`, here it is `A' ≤ B' ≤ A < B`.

### One collision again, and again only the inner indices move

`HJO.Braid.ytildeBlock_comm_of_overtake` reduces, exactly as its `z`-analogue does, to a single
`HJO.Braid.IsBraidSystem.collide`. The quadruple is different: there it was `(B'+1, B, A'+1, A)`,
here it is `(A', A+1, B', B)`, with collision indices `(A', A, B'+1, B)` — again only the two inner
indices move, and again each by one. `HJO.Braid.collideIndex_overtake_above` is that computation.

What carries the two `ỹ`'s past the trains is not a relation of `HJO.Braid.BraidMonoid`, as it was
for the `z`'s, but the two theorems of `HJO/Shuffle/BraidYtildeComm.lean` and
`HJO/Shuffle/BraidYtildeMellit.lean`: `HJO.Braid.braidYtilde_comm_trainDown`,
`HJO.Braid.braidYtilde_comm_trainUp` and `HJO.Braid.braidYtilde_comm`. With those in hand the
separated configuration is a genuine copy of `HJO.Braid.zBlock_comm_of_separated`, hypothesis shape
included; the overtaking one is not, and its proof is the `HJO.Braid.braidTrainDown_mul_braidYtilde`
normalisation `T_{a'↘a} ỹ_a = ỹ_{a'} T_{a'↗a}` of both blocks followed by the collision.

### What is still missing from `HJO.Braid.braidWord_pair_comm`

The third case, `x < θ < y`, is not here. Its geometry is *not* a third copy: above the puncture a
point falls and below it a point rises, so in that configuration `x' > y'` always — the two points
always cross — and the two comparisons left open are `x'` against `y` and `x` against `y'`, all
four combinations of which occur. Writing `ε = [y' ≤ x]` and `δ = [y ≤ x']`, the four sub-cases are
one two-parameter identity,
`T_{A'+1-δ↘A+ε} 𝗓_{A+ε} · T_{B'↘B} ỹ_B = T_{B'-1+ε↘B-δ} ỹ_{B-δ} · T_{A'↘A} 𝗓_A`,
whose algebraic content is `HJO.Braid.braidYtilde_zy` at a general index rather than any
commutation. See `HJO.Braid.ytilde_z_exchange_two` for the rank-`2` witness.

## References

Part of the proof of the exchange lemma `HJO.Braid.braidWord_pair_comm` for special braids, using
`HJO.Braid.braidStep`, `HJO.Braid.braidWord`, `HJO.Braid.entryRank`, `HJO.Braid.moveStage`,
`HJO.Braid.braidYtilde`, `HJO.Braid.nextCrossing`, `HJO.Braid.braidTrainDown_mul_braidYtilde`,
`HJO.Braid.IsBraidSystem.collide`, `HJO.Braid.braidYtilde_comm_T`, `HJO.Braid.braidYtilde_comm`.
-/

@[expose] public section

namespace HJO.Braid

/-! ### The collision indices of the overtaking configuration above the puncture -/

/-- **The collision indices of the overtaking configuration above the puncture.** With
`a ≤ b ≤ c < d` the ascending train `T_{a↗c+1}` meets the descending train `T_{b↘d}` in the
quadruple `(a, c, b+1, d)`: only the two inner indices move, each by one.

The `z`-side mirror is `HJO.Braid.collideIndex_overtake`, whose quadruple is the other one. -/
theorem collideIndex_overtake_above {a b c d : ℤ} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c < d) :
    collideIndex a (c + 1) b d = (a, c, b + 1, d) := by
  have e3 : indexShift a (c + 1) b = b + 1 :=
    indexShift_up (by omega) (by omega) (by omega)
  have e2 : indexShift d b (c + 1) = c := by
    rw [indexShift_down (by omega) (by omega) (by omega)]; omega
  rw [collideIndex_eq, e3, e2,
    indexShift_fix (p := d) (q := b + 1) (x := a) (by omega) (by omega) (by omega),
    indexShift_fix (p := a) (q := c) (x := d) (by omega) (by omega) (by omega)]

/-! ### The two algebraic cores of the `ỹ`–`ỹ` case -/

/-- **The letter blocks of two `ỹ`-moves with separated rank ranges commute**, the `ỹ`-analogue of
`HJO.Braid.zBlock_comm_of_separated` with the same hypothesis shape. Each block is a descending
train followed by a `ỹ`, and the hypothesis puts every letter of the first block at distance at
least two from every letter of the second; the two `ỹ`'s commute by
`HJO.Braid.braidYtilde_comm`. -/
theorem ytildeBlock_comm_of_separated {k a a' b b' : ℕ} (ha : 1 ≤ a) (hak : a ≤ k) (ha' : 1 ≤ a')
    (ha'k : a' ≤ k) (hb : 1 ≤ b) (hbk : b ≤ k) (hb' : 1 ≤ b') (hb'k : b' ≤ k)
    (hsep : max a a' + 1 ≤ min b b') :
    braidTrainDown k a' a * braidYtilde k a * (braidTrainDown k b' b * braidYtilde k b)
      = braidTrainDown k b' b * braidYtilde k b * (braidTrainDown k a' a * braidYtilde k a) := by
  have hsys := isBraidSystem_braidGenT k
  calc braidTrainDown k a' a * braidYtilde k a * (braidTrainDown k b' b * braidYtilde k b)
      = braidTrainDown k a' a * (braidYtilde k a * braidTrainDown k b' b) * braidYtilde k b := by
        simp only [mul_assoc]
    _ = braidTrainDown k a' a * braidTrainDown k b' b * (braidYtilde k a * braidYtilde k b) := by
        rw [braidYtilde_comm_trainDown ha hak hb' hb'k hb hbk (by omega)]; simp only [mul_assoc]
    _ = braidTrainDown k b' b * braidTrainDown k a' a * (braidYtilde k b * braidYtilde k a) := by
        rw [hsys.trainDown_comm_trainDown ha' ha'k ha hak hb' hb'k hb hbk (by omega),
          braidYtilde_comm ha hak hb hbk]
    _ = braidTrainDown k b' b * braidYtilde k b * (braidTrainDown k a' a * braidYtilde k a) := by
        simp only [mul_assoc]
        congr 1
        rw [← mul_assoc, ← braidYtilde_comm_trainDown hb hbk ha' ha'k ha hak (by omega), mul_assoc]

/-- **The overtaking configuration of the `ỹ`–`ỹ` case.** Here the intermediate ranks differ between
the two orders: the point at rank `d` ends at `b`, passing the point at rank `c`, which therefore
stands at `c` in one order and at `c + 1` in the other.

`HJO.Braid.braidTrainDown_mul_braidYtilde` normalises both blocks of the first factor to
`ỹ_{a} T_{a↗·}`, after which the left-hand side carries the ascending–descending product
`T_{a↗c+1} T_{b↘d}` and the right-hand side the descending–ascending product
`T_{b+1↘d} T_{a↗c}`; those are the two sides of `HJO.Braid.IsBraidSystem.collide` at
`HJO.Braid.collideIndex_overtake_above`. The two `ỹ`'s are carried into place by
`HJO.Braid.braidYtilde_comm_trainDown`, `HJO.Braid.braidYtilde_comm_trainUp` and
`HJO.Braid.braidYtilde_comm`, every letter they pass being far from their index. -/
theorem ytildeBlock_comm_of_overtake {k a b c d : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (hcd : c < d) (hdk : d ≤ k) :
    braidTrainDown k a (c + 1) * braidYtilde k (c + 1) * (braidTrainDown k b d * braidYtilde k d)
      = braidTrainDown k (b + 1) d * braidYtilde k d
        * (braidTrainDown k a c * braidYtilde k c) := by
  have hsys := isBraidSystem_braidGenT k
  have hcol : braidTrainUp k a (c + 1) * braidTrainDown k b d
      = braidTrainDown k (b + 1) d * braidTrainUp k a c :=
    hsys.collide (a := a) (b := c + 1) (c := b) (d := d) (a' := a) (b' := c) (c' := b + 1)
      (d' := d) ha (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hdk
      (by omega)
      (by push_cast; exact collideIndex_overtake_above (by omega) (by omega) (by omega))
  have hDfar : braidYtilde k a * braidTrainDown k (b + 1) d
      = braidTrainDown k (b + 1) d * braidYtilde k a :=
    braidYtilde_comm_trainDown ha (by omega) (by omega) (by omega) (by omega) hdk (by omega)
  have hUfar : braidYtilde k d * braidTrainUp k a c = braidTrainUp k a c * braidYtilde k d :=
    braidYtilde_comm_trainUp (a := d) (c := a) (d := c) (by omega) hdk ha (by omega) (by omega)
      (by omega) (by omega)
  have hYY : braidYtilde k a * braidYtilde k d = braidYtilde k d * braidYtilde k a :=
    braidYtilde_comm ha (by omega) (by omega) hdk
  rw [braidTrainDown_mul_braidYtilde (k := k) (a := a) (b := c + 1) ha (by omega) (by omega)
      (by omega),
    braidTrainDown_mul_braidYtilde (k := k) (a := a) (b := c) ha (by omega) (by omega) (by omega)]
  calc braidYtilde k a * braidTrainUp k a (c + 1) * (braidTrainDown k b d * braidYtilde k d)
      = braidYtilde k a * (braidTrainUp k a (c + 1) * braidTrainDown k b d) * braidYtilde k d := by
        simp only [mul_assoc]
    _ = braidYtilde k a * braidTrainDown k (b + 1) d * braidTrainUp k a c * braidYtilde k d := by
        rw [hcol]; simp only [mul_assoc]
    _ = braidTrainDown k (b + 1) d * (braidYtilde k a * (braidTrainUp k a c
          * braidYtilde k d)) := by rw [hDfar]; simp only [mul_assoc]
    _ = braidTrainDown k (b + 1) d * (braidYtilde k d * braidYtilde k a
          * braidTrainUp k a c) := by
        rw [← hUfar, ← mul_assoc (braidYtilde k a), hYY]
    _ = braidTrainDown k (b + 1) d * braidYtilde k d * (braidYtilde k a
          * braidTrainUp k a c) := by simp only [mul_assoc]

/-! ### The exchange lemma for two points above the puncture -/

/-- **The moves of two distinct points above the puncture may be exchanged**, in the ordered case:
if `θ < w_i < w_j` then the two-move words `(i, j)` and `(j, i)` name the same braid.

Both points contribute a `ỹ`, and both values fall by `θ`, so the five settled comparisons are
`w_i < w_j`, `nx(w_i) < w_i`, `nx(w_j) < w_j`, `nx(w_i) < nx(w_j)` and `nx(w_i) < w_j`. The one left
open is `nx(w_j)` against `w_i`, and it is the case division: above it the two runs do not
interleave and the content is `HJO.Braid.ytildeBlock_comm_of_separated`; below it the *upper* point
falls past the lower one and the content is `HJO.Braid.ytildeBlock_comm_of_overtake`. -/
theorem braidWord_pair_comm_of_gt_theta {θ : ℚ} {k : ℕ} {w : Fin k → ℚ} {i j : Fin k}
    (hij : i ≠ j) (hθ0 : 0 < θ) (hxθ : θ < w i) (hyθ : θ < w j) (hxy : w i < w j)
    (hne : nextCrossing θ (w j) ≠ w i) :
    braidWord θ w [i, j] = braidWord θ w [j, i] := by
  have hx' : nextCrossing θ (w i) = w i - θ := by
    simp only [nextCrossing, hxθ, ite_true]
  have hy' : nextCrossing θ (w j) = w j - θ := by
    simp only [nextCrossing, hyθ, ite_true]
  have hxx' : nextCrossing θ (w i) < w i := by rw [hx']; linarith
  have hyy' : nextCrossing θ (w j) < w j := by rw [hy']; linarith
  have hx'y' : nextCrossing θ (w i) < nextCrossing θ (w j) := by rw [hx', hy']; linarith
  have hx'y : nextCrossing θ (w i) < w j := hxx'.trans hxy
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
  have i3 : ¬(w j ≤ nextCrossing θ (w i)) := by linarith
  have i4 : ¬(nextCrossing θ (w j) ≤ nextCrossing θ (w i)) := by linarith
  simp only [i1, i3, i4, hxy.le, hx'y.le, hx'y'.le, ite_true, ite_false, add_zero] at E1 E2 E3 E4
  have hE2 : entryRank (moveOne θ w i) j = entryRank w j := by omega
  have hE3 : entryRank (moveOne θ (moveOne θ w j) i) i = entryRank (moveOne θ w i) i := by omega
  -- The braid of each of the four steps.
  rw [braidWord_pair, braidWord_pair,
    braidStep_of_gt (show θ < moveOne θ w j i by rw [hvi]; exact hxθ),
    braidStep_of_gt hyθ, braidStep_of_gt (show θ < moveOne θ w i j by rw [huj]; exact hyθ),
    braidStep_of_gt hxθ, ← hfin, hE2, hE3]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- The upper point falls past the lower one.
    have hE1 : entryRank (moveOne θ w j) i = entryRank w i + 1 := by
      simp only [hlt.le, ite_true] at E1
      omega
    have hE4 : entryRank (moveOne θ (moveOne θ w j) i) j = entryRank (moveOne θ w j) j + 1 := by
      simp only [show ¬(w i ≤ nextCrossing θ (w j)) from by linarith, ite_false, add_zero] at E4
      omega
    rw [hE1, hE4]
    refine ytildeBlock_comm_of_overtake (entryRank_pos _ _) ?_ ?_ ?_ (entryRank_le _ _)
    · -- `A' ≤ B'`, read in the final tuple.
      have := (entryRank_lt_entryRank_iff (moveOne θ (moveOne θ w j) i) i j).2
        (by rw [hfi, hfj]; exact hx'y')
      rw [hE3, hE4] at this
      omega
    · -- `B' ≤ A`, read in the tuple `j` has already advanced.
      have := (entryRank_lt_entryRank_iff (moveOne θ w j) j i).2 (by rw [hvi, hvj]; exact hlt)
      rw [hE1] at this
      omega
    · exact (entryRank_lt_entryRank_iff w i j).2 hxy
  · -- The runs do not interleave.
    have hE1 : entryRank (moveOne θ w j) i = entryRank w i := by
      simp only [show ¬(nextCrossing θ (w j) ≤ w i) from by linarith, ite_false, add_zero] at E1
      omega
    have hE4 : entryRank (moveOne θ (moveOne θ w j) i) j = entryRank (moveOne θ w j) j := by
      simp only [hgt.le, ite_true] at E4
      omega
    rw [hE1, hE4]
    refine ytildeBlock_comm_of_separated (entryRank_pos _ _) (entryRank_le _ _) (entryRank_pos _ _)
      (entryRank_le _ _) (entryRank_pos _ _) (entryRank_le _ _) (entryRank_pos _ _)
      (entryRank_le _ _) ?_
    have c1 : entryRank w i < entryRank w j := (entryRank_lt_entryRank_iff w i j).2 hxy
    have c2 : entryRank w i < entryRank (moveOne θ w j) j := by
      have := (entryRank_lt_entryRank_iff (moveOne θ w j) i j).2 (by rw [hvi, hvj]; exact hgt)
      rw [hE1] at this
      omega
    have c3 : entryRank (moveOne θ w i) i < entryRank w j := by
      have := (entryRank_lt_entryRank_iff (moveOne θ w i) i j).2 (by rw [hui, huj]; exact hx'y)
      rw [hE2] at this
      omega
    have c4 : entryRank (moveOne θ w i) i < entryRank (moveOne θ w j) j := by
      have := (entryRank_lt_entryRank_iff (moveOne θ (moveOne θ w j) i) i j).2
        (by rw [hfi, hfj]; exact hx'y')
      rw [hE3, hE4] at this
      omega
    omega

/-- **The moves of two distinct points above the puncture may be exchanged.** The ordered form
`HJO.Braid.braidWord_pair_comm_of_gt_theta` read without a choice of which entry is the smaller;
the conclusion is symmetric in `i` and `j`, so the two orderings are the same statement. -/
theorem braidWord_pair_comm_of_gt_theta' {θ : ℚ} {k : ℕ} {w : Fin k → ℚ} {i j : Fin k}
    (hij : i ≠ j) (hθ0 : 0 < θ) (hxθ : θ < w i) (hyθ : θ < w j) (hne0 : w i ≠ w j)
    (hne1 : nextCrossing θ (w j) ≠ w i) (hne2 : nextCrossing θ (w i) ≠ w j) :
    braidWord θ w [i, j] = braidWord θ w [j, i] := by
  rcases lt_or_gt_of_ne hne0 with h | h
  · exact braidWord_pair_comm_of_gt_theta hij hθ0 hxθ hyθ h hne1
  · exact (braidWord_pair_comm_of_gt_theta (Ne.symm hij) hθ0 hyθ hxθ h hne2).symm

/-- **Exchanging two adjacent moves of distinct points both above the puncture leaves the braid of
the sequence unchanged.** The moves of the suffix are performed first, so the hypotheses are read at
the tuple the suffix has advanced. This is the `ỹ`–`ỹ` half of `HJO.Braid.braidWord_pair_comm`, the
`z`–`z` half being `HJO.Braid.braidWord_swap_of_lt_theta`. -/
theorem braidWord_swap_of_gt_theta {θ : ℚ} {k : ℕ} (w : Fin k → ℚ) {i j : Fin k} (hij : i ≠ j)
    (l₁ l₂ : List (Fin k)) (hθ0 : 0 < θ)
    (hxθ : θ < moveTuple θ w l₂ i) (hyθ : θ < moveTuple θ w l₂ j)
    (hne0 : moveTuple θ w l₂ i ≠ moveTuple θ w l₂ j)
    (hne1 : nextCrossing θ (moveTuple θ w l₂ j) ≠ moveTuple θ w l₂ i)
    (hne2 : nextCrossing θ (moveTuple θ w l₂ i) ≠ moveTuple θ w l₂ j) :
    braidWord θ w (l₁ ++ i :: j :: l₂) = braidWord θ w (l₁ ++ j :: i :: l₂) :=
  braidWord_swap_of_pair_comm θ w hij l₁ l₂
    (braidWord_pair_comm_of_gt_theta' hij hθ0 hxθ hyθ hne0 hne1 hne2)

end HJO.Braid
