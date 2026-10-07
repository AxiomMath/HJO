/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.ColouringWidth
public import HJO.Shuffle.SweepAppendWidth
public import HJO.Shuffle.MellitRem41

/-!
# The grading of the band identity: the fibre is homogeneous

`HJO.Mellit.sweepAppend_of_forall_band` (`HJO/Shuffle/SweepAppendWidth.lean`) reduces
`HJO.Mellit.SweepAppend` to two per-path identities, of which `hband` is the one off the `α = []`
corner. Its left-hand side is a **sum over the tails** of the truncation and its right-hand side is
a single vector, so before any algebra one has to know that the summands all live in one graded
piece of `HJO.Sweep.Total L`. If they did not, a sum of inhomogeneous vectors would be being equated
with a homogeneous one and `hband` would be false.

This file settles that, and the answer is that the fibre **is** homogeneous.

## Why this is the question worth asking

`HJO/Collinear/CommutationTheorem.lean` records that the *termwise* route to
`HJO.Mellit.SweepAppend` — comparing the sweep of an extended path with the sweep of its truncation,
one event at a time — is obstructed by the grading and not by a missing lemma:
`HJO.Mellit.stageTotal_mem_piece` raises the index by exactly one however large `A` is, while the
width shift of `HJO.Paths.sweepWidth_appendHeights_eq` runs over a whole band and **varies with the
tail** (`HJO.Paths.card_liveSteps_high_appendHeights_ne` exhibits two tails in one fibre whose
corrections are `2` and `1`). The band form is the response to that objection. So the first thing to
check about it is whether the same objection reappears, and the content of this file is that it does
not: the width correction varies across the fibre, but the *total* grading does not.

The two are consistent because the grading of `HJO.Mellit.partialSweepWord` is not read off the
width corrections at all. By `HJO.Mellit.partialSweepWord_mem_piece` it is
`HJO.Mellit.levelWidth`, the number of north steps the level line crosses, and
`HJO.Mellit.levelWidth_sepLevel_eq_length` below computes that to be `α.length` — a function of the
return composition alone, blind to which path of that composition is taken.

## The computation

At the separating level `η = aN + 1/2` a north step `u` of an above-diagonal path is crossed exactly
when its foot lies **on** the diagonal (`HJO.Mellit.mem_colouringNorth_sepLevel_iff`). Neither half
of `HJO.Mellit.colouringNorth`'s condition needs new arithmetic:

* `rk̂(u) < η` is `HJO.Mellit.separatesDiagonal_sepLevel'` read at `u`, with the strictness supplied
  by `HJO.Mellit.pointRank_ne_of_isAdmissibleLevel` — an integer is never a half-integer;
* `η < rk̂(u) + ω` is the *same* statement read at the **head** `u + (0,1)`, because
  `HJO.Paths.abovePointRank_succ` says the attack window is exactly the rank difference between a
  north step's foot and its head. On an above-diagonal path it is therefore automatic.

Coprimality then locates those feet. `a·i = b·s` with `a` coprime to `b` forces `a ∣ s`, so the foot
is `(a·k, b·k)` and the path meets the diagonal at rank `k`; `HJO.Paths.HasAboveReturns` says the
ranks where it does so are exactly the prefix sums of `α`. The feet in range are the prefix sums
below `N`, of which there are `α.length` — the last prefix sum being `N` itself, whose column `aN`
carries no north step. Counting them is `HJO.Mellit.card_filter_mem_scanl`.

## What this does and does not give

It gives that both sides of `hband` are homogeneous of the same degree `α.length + 1`
(`HJO.Mellit.partialSweepWord_appendHeights_mem_piece` and
`HJO.Mellit.stageTotal_partialSweepWord_mem_piece`), uniformly in the tail. That is a **necessary**
condition for `hband`, now discharged, and it is the one the termwise route failed. It is not
sufficient and is not offered as progress on the identity itself: the interleaving of the base's
band events with the tail's, and the width corrections inside the band, are untouched here.

Nothing in this file needs `q ≠ 1`, and that is not an oversight. `HJO.Sweep.corner` is
`(q-1)⁻¹` times a difference of composites, so at `q = 1` it is the zero map — but the zero vector
lies in every piece, so the grading statements survive the degeneration. The `q ≠ 1` that
`HJO.Mellit.SweepAppend` genuinely needs (`HJO.Mellit.not_sweepAppend_one_left`) is a statement
about the identity, not about its grading.

## References

A. Mellit, *Toric braids and `(m, n)`-parking functions*, section 4.
-/

@[expose] public section

open Finset

namespace HJO.Mellit

open ParkingFunctions Paths Sweep

variable {a b N : ℕ}

/-! ### A north step is crossed by the separating level exactly at the diagonal -/

/-- **The head of a north step outranks its foot by exactly the attack window.** A restatement of
`HJO.Paths.abovePointRank_succ` in the form `HJO.Mellit.colouringNorth`'s second condition wants: it
turns that condition into the first condition read at the head, so both halves of a crossing become
instances of `HJO.Mellit.SeparatesDiagonal`. -/
theorem pointRank_add_attackWindow (a b N : ℕ) (P : ℕ × ℕ) :
    (pointRank a b N P : ℚ) + (attackWindow a N : ℚ)
      = ((pointRank a b N (P.1, P.2 + 1) : ℤ) : ℚ) := by
  have h : pointRank a b N (P.1, P.2 + 1) = pointRank a b N P + attackWindow a N :=
    abovePointRank_succ a b N P.1 P.2
  rw [h]
  push_cast
  ring

/-- **At the separating level, a north step of an above-diagonal path is crossed exactly when its
foot lies on the diagonal.** This is the whole geometric content of the grading computation, and
neither direction is an arithmetic accident: `HJO.Mellit.separatesDiagonal_sepLevel'` decides both
halves of `HJO.Mellit.colouringNorth`'s condition, the first at the foot and — through
`HJO.Mellit.pointRank_add_attackWindow` — the second at the head.

The second half is automatic: the head of a north step of an above-diagonal path is always strictly
above the diagonal, since its foot is weakly above it and `0 < a`. So the crossings are cut out by
the first half alone, which says the foot is *weakly below* the diagonal — and weakly above and
weakly below is on. -/
theorem mem_colouringNorth_sepLevel_iff {y : Heights a b N} (hy : IsAboveDiagonal y) (ha : 0 < a)
    {P : ℕ × ℕ} :
    P ∈ colouringNorth y (sepLevel a N) ↔ P ∈ northSteps y ∧ (a : ℤ) * P.2 = (b : ℤ) * P.1 := by
  have hsep := separatesDiagonal_sepLevel' a b N
  have hadm := isAdmissibleLevel_sepLevel a N
  -- the two conditions of `colouringNorth`, both read through `SeparatesDiagonal`
  have key : ∀ Q : ℕ × ℕ, Q ∈ northSteps y →
      (Q.1 ≤ a * N ∧ Q.2 ≤ b * N ∧ Q.2 + 1 ≤ b * N ∧ (b : ℤ) * Q.1 ≤ (a : ℤ) * Q.2) := by
    intro Q hQ
    obtain ⟨hx, hfoot, hhead⟩ := mem_northSteps_iff.1 hQ
    refine ⟨hx.le, le_trans hhead.le (ht_le_mul y _), le_trans hhead (ht_le_mul y _), ?_⟩
    have h1 : b * Q.1 ≤ a * ht y Q.1 := hy.2.2.2 Q.1 hx.le
    have h2 : a * ht y Q.1 ≤ a * Q.2 := Nat.mul_le_mul_left a hfoot
    exact_mod_cast le_trans h1 h2
  constructor
  · intro hP
    rw [colouringNorth, mem_filter] at hP
    obtain ⟨hns, hlt, -⟩ := hP
    obtain ⟨hxle, hyle, -, habove⟩ := key P hns
    refine ⟨hns, ?_⟩
    have hiff := hsep P.1 P.2 hxle hyle habove
    -- `hlt` says the level is not outranked, so the foot is not strictly above the diagonal
    have hnot : ¬ ((b : ℤ) * P.1 < (a : ℤ) * P.2) := fun h => asymm hlt (hiff.2 h)
    exact le_antisymm (not_lt.1 hnot) habove
  · rintro ⟨hns, hdiag⟩
    obtain ⟨hxle, hyle, hhead', habove⟩ := key P hns
    rw [colouringNorth, mem_filter]
    refine ⟨hns, ?_, ?_⟩
    · -- the foot is weakly below the diagonal, so it does not outrank the level; and a rank is
      -- never a half-integer, so the inequality is strict
      have hiff := hsep P.1 P.2 hxle hyle habove
      have hnot : ¬ (sepLevel a N < ((pointRank a b N P : ℤ) : ℚ)) := fun h =>
        absurd (hiff.1 h) (by rw [hdiag]; exact lt_irrefl _)
      exact lt_of_le_of_ne (not_lt.1 hnot)
        (pointRank_ne_of_isAdmissibleLevel hadm a b N hxle hyle)
    · -- the head is strictly above the diagonal, since `0 < a`
      rw [pointRank_add_attackWindow]
      have ha' : (0 : ℤ) < (a : ℤ) := by exact_mod_cast ha
      have hstep : (b : ℤ) * (P.1, P.2 + 1).1 ≤ (a : ℤ) * (P.1, P.2 + 1).2 := by
        simp only []
        push_cast
        linarith [hdiag]
      refine (hsep P.1 (P.2 + 1) hxle hhead' hstep).2 ?_
      push_cast
      linarith [hdiag]

/-! ### The crossed north steps are the return columns -/

/-- **The crossed north steps of a path of return composition `α`, listed.** They are the feet
`(a·k, b·k)` at the prefix sums `k < N` of `α`: the level line crosses a north step exactly at the
diagonal (`HJO.Mellit.mem_colouringNorth_sepLevel_iff`), coprimality puts a diagonal lattice point
at `(a·k, b·k)`, and `HJO.Paths.HasAboveReturns` says the ranks `k` where the path meets the
diagonal are exactly the prefix sums.

The prefix sum `N` itself is excluded, and not by hand: its column is `aN`, the right edge of the
rectangle, which carries no north step. Every other prefix sum's column does carry one — at a return
the path is *on* the diagonal, so it must climb before the next column or fall below it. -/
theorem colouringNorth_sepLevel_eq_image (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b)
    {α : List ℕ} {y : Heights a b N} (hy : HasAboveReturns α y) :
    colouringNorth y (sepLevel a N)
      = {k ∈ range N | k ∈ α.scanl (· + ·) 0}.image fun k => (a * k, b * k) := by
  obtain ⟨hyd, -, hsum, hret⟩ := hy
  ext P
  obtain ⟨x, i⟩ := P
  rw [mem_colouringNorth_sepLevel_iff hyd ha, mem_image]
  constructor
  · rintro ⟨hns, hdiag⟩
    obtain ⟨hx, hfoot, hhead⟩ := mem_northSteps_iff.1 hns
    simp only [] at hx hfoot hhead
    have hnat : a * i = b * x := by exact_mod_cast hdiag
    -- coprimality: `a ∣ b * x` and `a` coprime to `b`, so `a ∣ x`
    obtain ⟨k, rfl⟩ : a ∣ x :=
      Nat.Coprime.dvd_of_dvd_mul_left hab (Dvd.intro i (by omega))
    have hk2 : i = b * k := by
      have h : a * i = a * (b * k) := by rw [hnat]; ring
      exact Nat.eq_of_mul_eq_mul_left ha h
    have hkN : k < N := by
      by_contra hcon
      exact absurd hx (not_lt.2 (Nat.mul_le_mul_left a (by omega)))
    -- the foot of a crossed north step is the path's own height there
    have hht : ht y (a * k) = b * k := by
      have h1 : b * (a * k) ≤ a * ht y (a * k) := hyd.2.2.2 _ hx.le
      have h2 : a * ht y (a * k) ≤ a * i := Nat.mul_le_mul_left a hfoot
      have h3 : a * ht y (a * k) ≤ a * (b * k) := by rw [hk2] at h2; exact h2
      have h4 : a * (b * k) ≤ a * ht y (a * k) := by
        calc a * (b * k) = b * (a * k) := by ring
        _ ≤ a * ht y (a * k) := h1
      exact Nat.eq_of_mul_eq_mul_left ha (le_antisymm h3 h4)
    exact ⟨k, mem_filter.2 ⟨mem_range.2 hkN, (hret k hkN.le).1 hht⟩, by rw [hk2]⟩
  · rintro ⟨k, hk, heq⟩
    obtain ⟨hkN, hscan⟩ := mem_filter.1 hk
    rw [mem_range] at hkN
    obtain ⟨rfl, rfl⟩ : x = a * k ∧ i = b * k := by
      rw [Prod.ext_iff] at heq; exact ⟨heq.1.symm, heq.2.symm⟩
    have hht : ht y (a * k) = b * k := (hret k hkN.le).2 hscan
    have hxlt : a * k < a * N := mul_lt_mul_of_pos_left hkN ha
    -- at a return the path must climb: otherwise the next column falls below the diagonal
    have hclimb : b * k < ht y (a * k + 1) := by
      have h := hyd.2.2.2 (a * k + 1) (by omega)
      by_contra hcon
      have h2 : a * ht y (a * k + 1) ≤ a * (b * k) := Nat.mul_le_mul_left a (by omega)
      have h3 : b * (a * k + 1) = a * (b * k) + b := by ring
      omega
    refine ⟨mem_northSteps_iff.2 ⟨hxlt, by rw [hht], hclimb⟩, ?_⟩
    simp only []
    push_cast
    ring

/-- **The level width of a path of return composition `α` is the number of parts of `α`.** The
grading fact `hband` needs: the number of north steps the separating level crosses depends on the
return composition alone and not on which path of that composition is taken, so the whole fibre of
`HJO.Mellit.sum_aboveReturnPaths_append_singleton` is homogeneous.

`HJO.Mellit.card_filter_mem_scanl` counts the prefix sums in `{0, …, N}` as `α.length + 1`; the one
dropped here is `N`, which is a prefix sum because `α` sums to `N`. -/
theorem levelWidth_sepLevel_eq_length (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b)
    {α : List ℕ} {y : Heights a b N} (hy : HasAboveReturns α y) :
    levelWidth y (sepLevel a N) = α.length := by
  have hpos : ∀ x ∈ α, 0 < x := hy.2.1
  have hsum : α.sum = N := hy.2.2.1
  have hNmem : N ∈ α.scanl (· + ·) 0 :=
    (mem_scanl_add_iff α 0 N).2 ⟨α.length, le_rfl, by simpa using hsum⟩
  have hsplit : {k ∈ range (N + 1) | k ∈ α.scanl (· + ·) 0}
      = insert N {k ∈ range N | k ∈ α.scanl (· + ·) 0} := by
    ext k
    simp only [mem_filter, mem_range, mem_insert]
    constructor
    · rintro ⟨hk, hs⟩
      rcases Nat.lt_or_ge k N with h | h
      · exact Or.inr ⟨h, hs⟩
      · exact Or.inl (by omega)
    · rintro (rfl | ⟨hk, hs⟩)
      · exact ⟨by omega, hNmem⟩
      · exact ⟨by omega, hs⟩
  have hnot : N ∉ {k ∈ range N | k ∈ α.scanl (· + ·) 0} := by
    simp only [mem_filter, mem_range]
    omega
  have hcard := card_filter_mem_scanl (N := N) hpos hsum
  rw [hsplit, card_insert_of_notMem hnot] at hcard
  rw [levelWidth, colouringNorth_sepLevel_eq_image hab ha hb hy,
    card_image_of_injective _ fun k l h =>
      Nat.eq_of_mul_eq_mul_left ha (congrArg Prod.fst h)]
  omega

/-! ### Both sides of `hband` are homogeneous of degree `α.length + 1` -/

section Piece

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-- **The partial sweep word of a path of return composition `α` lands in `V_{ℓ}`**, `ℓ` the number
of parts. `HJO.Mellit.partialSweepWord_mem_piece` at the level width computed by
`HJO.Mellit.levelWidth_sepLevel_eq_length`. -/
theorem partialSweepWord_sepLevel_mem_piece (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b)
    (hN : 0 < N) {α : List ℕ} {y : Heights a b N} (hy : HasAboveReturns α y) :
    partialSweepWord q u y (sepLevel a N) (1 : Total L) ∈ piece L α.length := by
  have h := partialSweepWord_mem_piece q u hy.1 ha hN (isAdmissibleLevel_sepLevel a N)
    (F := (1 : Total L)) (one_mem _)
  rwa [levelWidth_sepLevel_eq_length hab ha hb hy] at h

/-- **The left-hand side of `hband` is homogeneous of degree `ℓ + 1`, uniformly in the tail.** Every
summand of the sum over the tails lies in one and the same graded piece, whichever tail it comes
from — although the width correction the tail applies inside the band does *not* have that
independence (`HJO.Paths.card_liveSteps_high_appendHeights_ne`). The two facts live at different
levels: the correction moves individual event operators, the grading is read off the level width,
and `HJO.Mellit.levelWidth_sepLevel_eq_length` shows the level width sees only the return
composition. -/
theorem partialSweepWord_appendHeights_mem_piece {A : ℕ} (hab : Nat.Coprime a b) (ha : 0 < a)
    (hb : 0 < b) (hN : 0 < N) (hA : 0 < A) {α : List ℕ} {z : Heights a b N} {w : Heights a b A}
    (hz : HasAboveReturns α z) (hw : HasAboveReturns [A] w) :
    partialSweepWord q u (appendHeights z w) (sepLevel a (N + A)) (1 : Total L)
      ∈ piece L (α.length + 1) := by
  have hy : HasAboveReturns (α ++ [A]) (appendHeights z w) := hasAboveReturns_appendHeights hz hw
  have h := partialSweepWord_sepLevel_mem_piece (q := q) (u := u) hab ha hb
    (show 0 < N + A by omega) hy
  simpa using h

/-- **The left-hand side of `hband`, as it stands, lies in `V_{ℓ+1}`.** The sum over the fibre of
`HJO.Mellit.sum_aboveReturnPaths_append_singleton`, every summand of it in one piece by
`HJO.Mellit.partialSweepWord_appendHeights_mem_piece`, so the sum is too. -/
theorem sum_partialSweepWord_appendHeights_mem_piece {A : ℕ} (hab : Nat.Coprime a b) (ha : 0 < a)
    (hb : 0 < b) (hN : 0 < N) (hA : 0 < A) {α : List ℕ} {z : Heights a b N}
    (hz : HasAboveReturns α z) :
    ∑ w ∈ aboveReturnPaths a b A [A],
        partialSweepWord q u (appendHeights z w) (sepLevel a (N + A)) (1 : Total L)
      ∈ piece L (α.length + 1) :=
  sum_mem fun _ hw =>
    partialSweepWord_appendHeights_mem_piece hab ha hb hN hA hz (mem_aboveReturnPaths_iff.1 hw)

/-- **The right-hand side of `hband` is homogeneous of the same degree `ℓ + 1`.** The stage raises
the grading by exactly one (`HJO.Mellit.stageTotal_mem_piece`) and the scalar of
`HJO.Mellit.braidRep_specialBraid_dplusIter` does not move it, so the identity of `hband` is between
two vectors of one degree.

This is the point at which the grading objection recorded in `HJO/Collinear/CommutationTheorem.lean`
is answered rather than evaded. Against the *termwise* comparison the objection is decisive: the
stage raises the index by one however large `A` is, while the width shift runs over a band. The band
identity is not termwise — it equates a *sum* over the fibre with one vector — and for the sum the
only grading question is whether the fibre is homogeneous, which
`HJO.Mellit.partialSweepWord_appendHeights_mem_piece` answers yes. -/
theorem stageTotal_partialSweepWord_mem_piece {A : ℕ} (hab : Nat.Coprime a b) (ha : 0 < a)
    (hb : 0 < b) (hN : 0 < N) {α : List ℕ} {z : Heights a b N} (hz : HasAboveReturns α z)
    (c : L) :
    c • stageTotal q u a b α.length A
        (partialSweepWord q u z (sepLevel a N) (1 : Total L)) ∈ piece L (α.length + 1) :=
  smul_mem_piece (stageTotal_mem_piece q u a b α.length A
    (partialSweepWord_sepLevel_mem_piece hab ha hb hN hz))

end Piece

end HJO.Mellit

end
