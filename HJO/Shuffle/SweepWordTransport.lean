/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepCharWord
public import HJO.SweepBlocks.Block
public import HJO.SweepBlocks.Transport
public meta import HJO.Attr

/-! # The scalar-free sweep word is the word of the partner, at the vacuum

The central step of the proof of
`HJO.Mellit.constantCoeff_psiWord_one_mem_lambdaComp_and_map_eq_sweepChar`: the composite
`Ψ(P̂) = Ψ_{P̂}(P_M) ∘ ⋯ ∘ Ψ_{P̂}(P_1)` of `HJO.Mellit.psiWord` and the word `Ξ_{P̂', S(P̂)}` of
`HJO.Sweep.markedWordOp` take the same value at the vacuum `1`.

## Main results

* `HJO.Mellit.psiWord_one_eq_markedWordOp_one`: the display, which is the hypothesis `hword` of
  `HJO/Shuffle/SweepCharWord.lean`.
* `HJO.Sweep.corner_transport`: `Δ(Y_kF) = Y_k(Δ'F)`, the type-`C` transport step, the companion
  of `HJO.Sweep.dplus_transport` and `HJO.Sweep.dminus_transport` in
  `HJO/SweepBlocks/Transport.lean`.
* `HJO.Paths.wordPosition_eq_sum_blockSize`, `HJO.Paths.eq_of_wordPosition_eq`: the word position at
  an event is the total block size below it, and it separates the events. Both are companions of
  `HJO.Paths.wordBlock_biUnion_eq` in `HJO/SweepBlocks/Block.lean`.
* `HJO.Mellit.constantCoeff_psiWord_one_mem_lambdaComp_and_map_eq_sweepChar_of_cor46_alone`,
  `HJO.Mellit.sweepComputes_of_cor46_alone`,
  `HJO.Mellit.constantCoeff_sweepWord_one_mem_lambdaComp_and_map_eq_smul_sweepChar_of_cor46_alone`:
  `HJO.Mellit.constantCoeff_psiWord_one_mem_lambdaComp_and_map_eq_sweepChar` and
  `HJO.Mellit.sweepComputes` with `HJO.Mellit.map_constantCoeff_markedWordOp'` as the one remaining
  input.

## Orientation

**The two composites are not equal as operators.** Mellit's `d^♭_±` are not Carlsson and Mellit's
`d_±`; the transport `Y_k` of `HJO.Sweep.transport` intervenes at every intermediate index and only
becomes the identity at the two ends, where the index is `0`. So the statement is an equation at
`1`, and the proof is an induction whose invariant carries `Y_k`.

## The shape of the induction

Both composites are read as `List.foldl`s in the order in which the factors act. The rightmost
factor of a `List.prod` in `Module.End` acts first, so for either word the action order is the
*reverse* of the list: `HJO.Mellit.foldl_apply_eq_prod_map_reverse` turns each product applied to a
vector into a `foldl` along that reverse.

On the sweep side the list is the decreasing-rank listing `Ds` of `Sw(P̂)`; the points of event type
`D` and `E` contribute the identity, so it may be thinned to the listing `Es` of
`HJO.Paths.eventPoints` (`HJO.Mellit.foldl_filter_of_eq_one`). On the Carlsson–Mellit side the list
is `[2n-1, …, 0]`, the word positions in decreasing order.

The induction runs along the suffixes of `Es`, which is legitimate because
`HJO.Paths.wordPosition_eq_sum_blockSize` identifies `pos_{P̂}(P)` with the sum of the block sizes
over the events of rank at most `rk̂(P)` — so a suffix of `Es` consumes exactly the word positions
`[1, p]` with `p` the sum of its block sizes, which is the word position at its head. What the step
needs at an event `P` with `p = pos_{P̂}(P)`:

* the level is the width: the private `two_mul_northBelow_eq_add_sweepWidth` says
  `2·#{k : x'_k + k < p} = p + k_{P̂}(P)`, so `k_{P̂}(P)` is the level `HJO.Dyck.wordLevel` gives
  the position `p - 1`. This is the index count of the induction, done as a count rather than a
  recursion: both sides are `F - H` with `F` the feet and `H` the heads the sweep has passed.
* which letter sits at `p - 1`, and whether it is the north step of a marked corner: the private
  `isMarkedNorth_partnerPath_iff` is the type-`C` half — `s` is a marked north position exactly when
  `s + 1` is the word position of a type-`C` event — and `exists_partnerPath_add_eq_iff` is the
  letter itself.
* the transport identity for the factor: `HJO.Sweep.dplus_transport` at type `A`,
  `HJO.Sweep.dminus_transport` at type `B`, and `HJO.Sweep.corner_transport` — both of them in turn
  — at type `C`.

## Implementation notes

*No `q`-invertibility is needed.* The three transport identities are linear rewritings valid at
every `q`, including `q = 1`, where both corner operators are `(q-1)⁻¹ = 0` times a commutator and
the identity reads `0 = 0`. The hypothesis `q ≠ 0` reappears only downstream, in
`HJO.Mellit.sweepWord_eq_smul_psiWord`, where the two powers of `q` are collected.

*The degenerate rectangle is separated out.* `HJO.Paths.mul_pos_of_isAboveDiagonal` derives
`0 < a * N` from the existence of a north step, so `0 < b * N` gives the `0 < a` and `0 < N` that
`HJO.Paths.wordBlock_biUnion_eq` asks for; at `b * N = 0` the path has no north step, every swept
point has type `D` or `E`, and both words are the empty product.

*The remaining input.* The results below carry the content of
`HJO.Mellit.map_constantCoeff_markedWordOp'` as the single hypothesis `hcor46`. That statement is
proved in `HJO/CarlssonMellit/LoweringSumClosed.lean`, and
`HJO.Mellit.constantCoeff_psiWord_one_mem_lambdaComp_and_map_eq_sweepChar` is assembled from it in
`HJO/Shuffle/SweepComputesClosed.lean`.

## References

A. Mellit, *Toric braids and `(m, n)`-parking functions*, section "The sweep process".
-/

@[expose] public section

open Finset

namespace HJO.Sweep

variable {L : Type*} [Field L] [Algebra ℚ L]

/-! ### The transport of the corner operator -/

/-- **The transport carries the corner operator to the modified one.** For `k ≥ 1`,
`Δ(Y_k F) = Y_k(Δ' F)` with `Δ` the operator of `HJO.Sweep.corner` and `Δ'` the commutator
`HJO.Sweep.cmCorner` built from Carlsson and Mellit's `d_±`.

This is the type-`C` step of the proof of
`HJO.Mellit.constantCoeff_psiWord_one_mem_lambdaComp_and_map_eq_sweepChar`:
`HJO.Sweep.dplus_transport` and `HJO.Sweep.dminus_transport` applied in turn along each of the two
composites, `d^♭_-d^♭_+(Y_kF) = Y_k(d_-d_+F)` and `d^♭_+d^♭_-(Y_kF) = Y_k(d_+d_-F)`, and then `Y_k`
pulled through `(q-1)^{-1}`, which it commutes with because it is multiplication by an element of
the ring. -/
theorem corner_transport (q : L) (k : ℕ) (F : Total L) :
    corner q (k + 1) (transport L (k + 1) F) = transport L (k + 1) (cmCorner q (k + 1) F) := by
  have hup : dminus q (k + 1 + 1) (dplus q (k + 1) (transport L (k + 1) F))
      = transport L (k + 1) (dminusCM q (k + 1 + 1) (cmDPlus q (k + 1) F)) := by
    rw [dplus_transport, dminus_transport]
  have hdn : dplus q k (dminus q (k + 1) (transport L (k + 1) F))
      = transport L (k + 1) (cmDPlus q k (dminusCM q (k + 1) F)) := by
    rw [dminus_transport, dplus_transport]
  have hsmul : ∀ (c : L) (G : Total L), transport L (k + 1) (c • G) = c • transport L (k + 1) G :=
    fun c G => by rw [transport_apply, transport_apply]; exact mul_smul_comm c _ G
  have hcor : corner q (k + 1) = (q - 1)⁻¹ •
      (dminus q (k + 1 + 1) * dplus q (k + 1) - dplus q k * dminus q (k + 1)) := by
    rw [corner]
    simp only [Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel]
  have hcm : cmCorner q (k + 1) = (q - 1)⁻¹ •
      (dminusCM q (k + 1 + 1) * cmDPlus q (k + 1) - cmDPlus q k * dminusCM q (k + 1)) := by
    rw [cmCorner, Nat.add_sub_cancel]
  rw [hcor, hcm, LinearMap.smul_apply, LinearMap.smul_apply, hsmul]
  congr 1
  simp only [LinearMap.sub_apply, Module.End.mul_apply, map_sub, hup, hdn]

end HJO.Sweep

namespace HJO.Paths

open ParkingFunctions

variable {a b N : ℕ}

/-! ### The word position, read through the blocks -/

/-- The word position is monotone in the above-diagonal rank: both of its counts are counts of
north steps below a rank threshold. -/
theorem wordPosition_mono (y : Heights a b N) {Q P : ℕ × ℕ}
    (h : abovePointRank a b N Q.1 Q.2 ≤ abovePointRank a b N P.1 P.2) :
    wordPosition y Q ≤ wordPosition y P := by
  rw [wordPosition, wordPosition]
  exact Nat.add_le_add
    (card_le_card (monotone_filter_right _ fun u _ hu => hu.trans h))
    (card_le_card (monotone_filter_right _ fun u _ hu => hu.trans h))

/-- The word position at an event is the largest element of its own block. -/
theorem wordPosition_mem_wordBlock {y : Heights a b N} (hy : IsAboveDiagonal y) {P : ℕ × ℕ}
    (hP : P ∈ sweptRegion y) (hD : eventType y P ≠ EventType.D)
    (hE : eventType y P ≠ EventType.E) : wordPosition y P ∈ wordBlock y P := by
  have h1 := blockSize_le_wordPosition hy hP hD hE
  have h2 := blockSize_pos y P
  rw [mem_wordBlock]
  omega

/-- **The word position at an event is the total block size below it.** The blocks of the events of
rank at most `rk̂(P)` are pairwise disjoint with union `{1, …, pos_{P̂}(P)}`: each of them lies
there because the word position is monotone in the rank, and nothing is missing because a position
`r ≤ pos_{P̂}(P)` lies in *some* block by `HJO.Paths.wordBlock_biUnion_eq`, and in a block of larger
rank it would exceed `pos_{P̂}(P)` by `HJO.Paths.lt_of_mem_wordBlock_of_rank_lt`.

This is what licenses the induction of this file along the suffixes of the event listing: the sum of
the block sizes over a suffix is the word position at its head. -/
theorem wordPosition_eq_sum_blockSize {y : Heights a b N} (hy : IsAboveDiagonal y) (ha : 0 < a)
    (hN : 0 < N) {P : ℕ × ℕ} (hP : P ∈ eventPoints y) :
    wordPosition y P = ∑ Q ∈ {Q ∈ eventPoints y |
      abovePointRank a b N Q.1 Q.2 ≤ abovePointRank a b N P.1 P.2}, blockSize y Q := by
  classical
  obtain ⟨hPs, hPD, hPE⟩ := mem_eventPoints.1 hP
  have hPmem := wordPosition_mem_wordBlock hy hPs hPD hPE
  have hkey : ({Q ∈ eventPoints y | abovePointRank a b N Q.1 Q.2 ≤
      abovePointRank a b N P.1 P.2}).biUnion (wordBlock y) =
        Finset.Icc 1 (wordPosition y P) := by
    ext r
    simp only [mem_biUnion, mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨Q, ⟨hQe, hQr⟩, hr⟩
      obtain ⟨hQs, hQD, hQE⟩ := mem_eventPoints.1 hQe
      have h1 := blockSize_le_wordPosition hy hQs hQD hQE
      have h2 := blockSize_pos y Q
      have h3 := wordPosition_mono y hQr
      rw [mem_wordBlock] at hr
      omega
    · rintro ⟨hr1, hr2⟩
      have hr2n : r ≤ 2 * (b * N) := by
        have := wordPosition_le y P
        rw [card_northSteps hy] at this
        omega
      have hmem : r ∈ (eventPoints y).biUnion (wordBlock y) := by
        rw [wordBlock_biUnion_eq hy ha hN]
        exact Finset.mem_Icc.2 ⟨hr1, hr2n⟩
      obtain ⟨Q, hQe, hr⟩ := mem_biUnion.1 hmem
      obtain ⟨hQs, hQD, hQE⟩ := mem_eventPoints.1 hQe
      refine ⟨Q, ⟨hQe, ?_⟩, hr⟩
      by_contra hlt
      exact absurd (lt_of_mem_wordBlock_of_rank_lt hy hQs hQD hQE (by omega) hr hPmem) (by omega)
  have hcard := congrArg Finset.card hkey
  rw [Finset.card_biUnion fun Q hQ Q' hQ' hne =>
      disjoint_wordBlock hy ha hN (mem_filter.1 hQ).1 (mem_filter.1 hQ').1 hne,
    Nat.card_Icc] at hcard
  rw [← Finset.sum_congr rfl fun Q hQ => card_wordBlock hy (mem_eventPoints.1 (mem_filter.1 hQ).1).1
    (mem_eventPoints.1 (mem_filter.1 hQ).1).2.1 (mem_eventPoints.1 (mem_filter.1 hQ).1).2.2]
  omega

/-- **The word position separates the events.** Two events with the same word position coincide:
the position is strictly monotone in the rank across events by
`HJO.Paths.wordPosition_add_blockSize_le`, and the rank itself is injective on the strip. -/
theorem eq_of_wordPosition_eq {y : Heights a b N} (hy : IsAboveDiagonal y) (ha : 0 < a) (hN : 0 < N)
    {P P' : ℕ × ℕ} (hP : P ∈ eventPoints y) (hP' : P' ∈ eventPoints y)
    (h : wordPosition y P = wordPosition y P') : P = P' := by
  obtain ⟨hPs, hPD, hPE⟩ := mem_eventPoints.1 hP
  obtain ⟨hP's, hP'D, hP'E⟩ := mem_eventPoints.1 hP'
  have hrk : abovePointRank a b N P.1 P.2 = abovePointRank a b N P'.1 P'.2 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := wordPosition_add_blockSize_le hy hP's hP'D hP'E hlt
      have := blockSize_pos y P'
      omega
    · have := wordPosition_add_blockSize_le hy hPs hPD hPE hlt
      have := blockSize_pos y P
      omega
  obtain ⟨h1, h2⟩ := abovePointRank_injOn (b := b) ha hN (mem_sweptRegion.1 hPs).1
    (mem_sweptRegion.1 hP's).1 hrk
  exact Prod.ext h1 h2

end HJO.Paths

namespace HJO.Mellit

open ParkingFunctions Paths Sweep

variable {L : Type*} [Field L] [Algebra ℚ L] {a b N : ℕ}

/-! ### Reading an ordered product as a fold -/

omit [Algebra ℚ L] in
/-- **A product of operators applied to a vector is a fold along the reversed list.** In
`Module.End` the rightmost factor of a product acts first, so `F_0 ⋯ F_{m-1}` applied to `G`
consumes the indices from `m - 1` down to `0`; that is a `List.foldl` along the reverse. Both the
sweep word and the word of the partner are read this way. -/
theorem foldl_apply_eq_prod_map_reverse {α : Type*} (f : α → Module.End L (Total L)) :
    ∀ (l : List α) (G : Total L), l.foldl (fun H P => f P H) G = ((l.reverse.map f).prod) G := by
  intro l
  induction l with
  | nil => intro G; simp
  | cons P t ih =>
    intro G
    rw [List.foldl_cons, ih, List.reverse_cons, List.map_append, List.prod_append]
    simp

omit [Algebra ℚ L] in
/-- **Factors equal to the identity may be dropped from a fold.** The points of event type `D` and
`E` contribute the identity to the scalar-free sweep word, which is how its fold is thinned to a
fold over the events. -/
theorem foldl_filter_of_eq_one {α : Type*} (f : α → Module.End L (Total L)) (p : α → Bool) :
    ∀ (l : List α), (∀ P ∈ l, ¬p P → f P = 1) → ∀ G : Total L,
      l.foldl (fun H P => f P H) G = (l.filter p).foldl (fun H P => f P H) G := by
  intro l
  induction l with
  | nil => intro _ G; rfl
  | cons P t ih =>
    intro hone G
    have ht : ∀ Q ∈ t, ¬p Q → f Q = 1 := fun Q hQ => hone Q (List.mem_cons_of_mem _ hQ)
    by_cases hP : p P
    · rw [List.filter_cons_of_pos hP, List.foldl_cons, List.foldl_cons, ih ht]
    · rw [List.filter_cons_of_neg (by simpa using hP), List.foldl_cons, ih ht,
        hone P List.mem_cons_self (by simpa using hP)]
      rfl

/-! ### The level at a word position -/

/-- The number of north steps of the step word of `x` at positions strictly below `p`: the count
`HJO.Dyck.northCount` shifted so that `p = 0` is the empty count. -/
private def northBelow {n : ℕ} (x : Fin n → ℕ) (p : ℕ) : ℕ := #{k : Fin n | x k + (k : ℕ) < p}

private theorem northBelow_zero {n : ℕ} (x : Fin n → ℕ) : northBelow x 0 = 0 := by
  rw [northBelow, card_eq_zero, filter_eq_empty_iff]
  exact fun {k} _ => by omega

private theorem northBelow_succ {n : ℕ} (x : Fin n → ℕ) (s : ℕ) :
    northBelow x (s + 1) = Dyck.northCount x s := by
  rw [northBelow, Dyck.northCount]
  refine congrArg _ ?_
  ext k
  simp only [mem_filter_univ]
  omega

/-- The count below `p` grows by one across a north step and not at all across an east step. -/
private theorem northBelow_succ_eq {n : ℕ} {x : Fin n → ℕ} (h : Dyck.IsSquareDyck n x) (s : ℕ) :
    northBelow x (s + 1) =
      northBelow x s + (if ∃ k : Fin n, x k + (k : ℕ) = s then 1 else 0) := by
  classical
  have hsub : ({k : Fin n | x k + (k : ℕ) < s} : Finset (Fin n)) ⊆
      ({k : Fin n | x k + (k : ℕ) < s + 1} : Finset (Fin n)) :=
    fun k hk => by rw [mem_filter_univ] at hk ⊢; omega
  have hsdiff : ({k : Fin n | x k + (k : ℕ) < s + 1} : Finset (Fin n)) \
      ({k : Fin n | x k + (k : ℕ) < s} : Finset (Fin n))
      = ({k : Fin n | x k + (k : ℕ) = s} : Finset (Fin n)) := by
    ext k
    simp only [mem_sdiff, mem_filter_univ]
    omega
  have hcard : #({k : Fin n | x k + (k : ℕ) = s} : Finset (Fin n)) =
      if ∃ k : Fin n, x k + (k : ℕ) = s then 1 else 0 := by
    split_ifs with hex
    · obtain ⟨k, hk⟩ := hex
      refine card_eq_one.2 ⟨k, ?_⟩
      ext k'
      simp only [mem_filter_univ, mem_singleton]
      exact ⟨fun hk' => h.strictMono_add_index.injective (by rw [hk', hk]),
        fun hk' => by rw [hk']; exact hk⟩
    · rw [card_eq_zero, filter_eq_empty_iff]
      exact fun {k} _ hk => hex ⟨k, hk⟩
  have hkey := card_sdiff_add_card_eq_card hsub
  rw [hsdiff, hcard] at hkey
  rw [northBelow, northBelow]
  omega


/-! ### The level at an event is its width -/

/-- The foot of a north step is an event: it carries type `B` or `C` by
`HJO.Paths.mem_northSteps_iff_eventType`. -/
private theorem stepFoot_mem_eventPoints {y : Heights a b N} (hy : IsAboveDiagonal y)
    (i : Fin (b * N)) : stepFoot y i ∈ eventPoints y := by
  have hmem : stepFoot y i ∈ northSteps y := by
    rw [northSteps_eq_image hy]
    exact mem_image_of_mem _ (mem_univ i)
  have hsw : stepFoot y i ∈ sweptRegion y := (mem_sweptRegion_of_mem_northSteps hy hmem).1
  refine mem_eventPoints.2 ⟨hsw, ?_, ?_⟩ <;>
    rcases (mem_northSteps_iff_eventType hsw).1 hmem with h | h <;> rw [h] <;> simp

/-- `HJO.Paths.wordPosition_stepFoot` at the north step sitting at a given rank-order position: the
word position there is `x'_p + p + 1`, so the `0`-based word position of that step is `x'_p + p`. -/
private theorem wordPosition_stepFoot_stepAt {y : Heights a b N} (hy : IsAboveDiagonal y)
    (k : Fin (b * N)) :
    wordPosition y (stepFoot y (stepAt hy k)) = partnerPath y k + (k : ℕ) + 1 := by
  rw [wordPosition_stepFoot hy (stepAt hy k), stepIndex_stepAt, partnerPath]
  omega

/-- **The word position orders the north steps as the rank does.** One direction is monotonicity of
the position; the other is `HJO.Paths.wordPosition_add_blockSize_le` at the north step, which is an
event. -/
private theorem wordPosition_stepFoot_le_iff {y : Heights a b N} (hy : IsAboveDiagonal y)
    (P : ℕ × ℕ) (i : Fin (b * N)) :
    wordPosition y (stepFoot y i) ≤ wordPosition y P ↔
      abovePointRank a b N (stepFoot y i).1 (stepFoot y i).2 ≤ abovePointRank a b N P.1 P.2 := by
  obtain ⟨hFs, hFD, hFE⟩ := mem_eventPoints.1 (stepFoot_mem_eventPoints hy i)
  refine ⟨fun hle => ?_, fun h => wordPosition_mono y h⟩
  by_contra hlt
  have h1 := wordPosition_add_blockSize_le hy (Q := P) hFs hFD hFE (by omega)
  have h2 := blockSize_pos y (stepFoot y i)
  omega

/-- **The north steps of the partner below a word position are the north steps of the path the
sweep has passed.** The bijection is `HJO.Paths.wordPosition_stepFoot`, which identifies the
`0`-based word position of the `p`-th north step of `P̂'` with `x'_p + p`. -/
private theorem northBelow_partnerPath_eq {y : Heights a b N} (hy : IsAboveDiagonal y)
    (P : ℕ × ℕ) :
    northBelow (partnerPath y) (wordPosition y P) =
      #{u ∈ northSteps y | abovePointRank a b N u.1 u.2 ≤ abovePointRank a b N P.1 P.2} := by
  classical
  rw [northBelow]
  refine card_nbij (fun k => stepFoot y (stepAt hy k)) (fun k hk => ?_) (fun k _ k' _ hkk => ?_)
    (fun u hu => ?_)
  · simp only [Finset.mem_coe, mem_filter_univ] at hk
    simp only [Finset.mem_coe]
    refine mem_filter.2 ⟨?_, (wordPosition_stepFoot_le_iff hy P (stepAt hy k)).1 ?_⟩
    · rw [northSteps_eq_image hy]
      exact mem_image_of_mem _ (mem_univ _)
    · rw [wordPosition_stepFoot_stepAt hy k]
      omega
  · have h1 : stepAt hy k = stepAt hy k' := stepFoot_injective y hkk
    have h2 := congrArg (stepIndex y) h1
    rwa [stepIndex_stepAt, stepIndex_stepAt] at h2
  · obtain ⟨hun, hur⟩ := mem_filter.1 (Finset.mem_coe.1 hu)
    rw [northSteps_eq_image hy] at hun
    obtain ⟨i, -, rfl⟩ := mem_image.1 hun
    refine ⟨stepIndex y i, Finset.mem_coe.2 ((mem_filter_univ _).2 ?_),
      by simp only [stepAt_stepIndex]⟩
    have h1 := wordPosition_stepFoot_stepAt hy (stepIndex y i)
    rw [stepAt_stepIndex] at h1
    have h2 := (wordPosition_stepFoot_le_iff hy P i).2 hur
    omega

/-- **The level at an event is the width there.** The index count of the
induction, done as a count: with `F` the north steps whose foot and `H` those whose head the sweep
has passed, `pos_{P̂}(P) = F + H` by `HJO.Paths.wordPosition`, `F = k_{P̂}(P) + H` because a north
step counted by `F` and not live at `P` is one counted by `H`, and `F` is the number of north steps
of `P̂'` below the word position by `HJO.Mellit.northBelow_partnerPath_eq`. So
`2F = pos_{P̂}(P) + k_{P̂}(P)`, which is the statement that `HJO.Dyck.wordLevel` at the position
`pos_{P̂}(P) - 1` is the width. -/
private theorem two_mul_northBelow_eq_add_sweepWidth {y : Heights a b N} (hy : IsAboveDiagonal y)
    (P : ℕ × ℕ) : 2 * northBelow (partnerPath y) (wordPosition y P)
      = wordPosition y P + sweepWidth y P := by
  classical
  have hF := northBelow_partnerPath_eq hy P
  have he1 : {u ∈ {u ∈ northSteps y | abovePointRank a b N u.1 u.2 ≤
        abovePointRank a b N P.1 P.2} | abovePointRank a b N P.1 P.2 <
        abovePointRank a b N u.1 u.2 + attackWindow a N} = liveSteps y P := by
    rw [liveSteps, filter_filter]
  have he2 : {u ∈ {u ∈ northSteps y | abovePointRank a b N u.1 u.2 ≤
        abovePointRank a b N P.1 P.2} | ¬(abovePointRank a b N P.1 P.2 <
        abovePointRank a b N u.1 u.2 + attackWindow a N)}
      = {u ∈ northSteps y | abovePointRank a b N u.1 u.2 + attackWindow a N ≤
        abovePointRank a b N P.1 P.2} := by
    rw [filter_filter]
    refine filter_congr fun u _ => ?_
    have hω : (0 : ℤ) ≤ (attackWindow a N : ℤ) := Int.natCast_nonneg _
    omega
  have hc := card_filter_add_card_filter_not
    (s := {u ∈ northSteps y | abovePointRank a b N u.1 u.2 ≤ abovePointRank a b N P.1 P.2})
    (fun u => abovePointRank a b N P.1 P.2 < abovePointRank a b N u.1 u.2 + attackWindow a N)
  rw [he1, he2] at hc
  have hpos : wordPosition y P =
      #{u ∈ northSteps y | abovePointRank a b N u.1 u.2 ≤ abovePointRank a b N P.1 P.2} +
        #{u ∈ northSteps y | abovePointRank a b N u.1 u.2 + attackWindow a N ≤
          abovePointRank a b N P.1 P.2} := rfl
  have hw : sweepWidth y P = #(liveSteps y P) := rfl
  omega

/-! ### Which letter sits at the word position of an event -/

/-- A position of the step word of the partner carries a north step exactly when it is one below
the word position of a north step of the path: `HJO.Paths.wordPosition_stepFoot` again. -/
private theorem exists_partnerPath_add_eq_iff {y : Heights a b N} (hy : IsAboveDiagonal y)
    (s : ℕ) : (∃ k : Fin (b * N), partnerPath y k + (k : ℕ) = s) ↔
      ∃ i : Fin (b * N), wordPosition y (stepFoot y i) = s + 1 := by
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨stepAt hy k, by rw [wordPosition_stepFoot_stepAt hy k, hk]⟩
  · rintro ⟨i, hi⟩
    refine ⟨stepIndex y i, ?_⟩
    have h1 := wordPosition_stepFoot_stepAt hy (stepIndex y i)
    rw [stepAt_stepIndex, hi] at h1
    omega

/-- **The marked north positions of the partner are the type-`C` events.** The marking
step, in the form the word of `HJO.Sweep.markedWordOp` reads it: `s` is the position of the
north step of a corner of `P̂'` marked by `S(P̂)` exactly when `s + 1` is the word position of a
type-`C` event.

One direction is `HJO.Paths.eventType_stepFoot_eq_C_iff`, the other
`HJO.Paths.attackPartner_stepIndex_and_mem_corner_of_mem_sweepMarked` — the entry `x'_j = i + 1` at
a marked pair `(i, j)`, which makes `(x'_j - 1, j) = (i, j)` a cell of `S(P̂)` and a corner of
`P̂'`. -/
private theorem isMarkedNorth_partnerPath_iff {y : Heights a b N} (hy : IsAboveDiagonal y)
    (s : ℕ) : Dyck.IsMarkedNorth (partnerPath y) (markedPositions y) s ↔
      ∃ i : Fin (b * N), eventType y (stepFoot y i) = EventType.C ∧
        wordPosition y (stepFoot y i) = s + 1 := by
  constructor
  · rintro ⟨k, -, hmem, hks⟩
    simp only [markedPositions, mem_image] at hmem
    obtain ⟨⟨s₀, t₀⟩, hst, hpair⟩ := hmem
    have hk : (stepIndex y t₀ : ℕ) = (k : ℕ) := (Prod.ext_iff.1 hpair).2
    have hkeq : stepIndex y t₀ = k := Fin.val_injective hk
    refine ⟨t₀, (eventType_stepFoot_eq_C_iff hy t₀).2 ⟨s₀, hst⟩, ?_⟩
    have h1 := wordPosition_stepFoot_stepAt hy (stepIndex y t₀)
    rw [stepAt_stepIndex, hkeq] at h1
    omega
  · rintro ⟨i, hC, hpos⟩
    obtain ⟨s₀, hst⟩ := (eventType_stepFoot_eq_C_iff hy i).1 hC
    obtain ⟨hentry, hcorner⟩ := attackPartner_stepIndex_and_mem_corner_of_mem_sweepMarked hy hst
    have hpp : partnerPath y (stepIndex y i) = (stepIndex y s₀ : ℕ) + 1 := hentry
    obtain ⟨k', hk', hk'eq⟩ := Dyck.mem_corner.1 hcorner
    have hk'val : (k' : ℕ) = (stepIndex y i : ℕ) := ((Prod.ext_iff.1 hk'eq).2).symm
    have hk'idx : k' = stepIndex y i := Fin.val_injective hk'val
    refine ⟨stepIndex y i, hk'idx ▸ hk', ?_, ?_⟩
    · simp only [markedPositions, mem_image]
      exact ⟨(s₀, i), hst, by rw [hpp]; simp⟩
    · have h1 := wordPosition_stepFoot_stepAt hy (stepIndex y i)
      rw [stepAt_stepIndex, hpos] at h1
      omega


/-! ### The factor at the top position of the block of an event -/

/-- At an event the block does not run off the left end of the word, so its top position exists. -/
private theorem one_le_wordPosition {y : Heights a b N} (hy : IsAboveDiagonal y) {P : ℕ × ℕ}
    (hP : P ∈ eventPoints y) : 1 ≤ wordPosition y P := by
  obtain ⟨hPs, hPD, hPE⟩ := mem_eventPoints.1 hP
  have h1 := blockSize_le_wordPosition hy hPs hPD hPE
  have h2 := blockSize_pos y P
  omega

/-- The letter of the step word of the partner at a position inside the word. -/
private theorem getD_stepWord_partnerPath {y : Heights a b N} {s : ℕ} (hs : s < 2 * (b * N)) :
    (Dyck.stepWord (partnerPath y)).getD s DyckStep.D
      = if ∃ k : Fin (b * N), partnerPath y k + (k : ℕ) = s then DyckStep.U else DyckStep.D := by
  have hlen : s < (Dyck.stepWord (partnerPath y)).length := by
    rw [Dyck.length_stepWord]
    exact hs
  rw [List.getD_eq_getElem _ _ hlen, Dyck.getElem_stepWord]

/-- **A type-`C` event marks the top position of its block.** -/
private theorem isMarkedNorth_pred_of_eventType_C {y : Heights a b N} (hy : IsAboveDiagonal y)
    {P : ℕ × ℕ} (hP : P ∈ eventPoints y) (hC : eventType y P = EventType.C) :
    Dyck.IsMarkedNorth (partnerPath y) (markedPositions y) (wordPosition y P - 1) := by
  obtain ⟨hPs, hPD, hPE⟩ := mem_eventPoints.1 hP
  have hmem : P ∈ northSteps y := (mem_northSteps_iff_eventType hPs).2 (Or.inr hC)
  rw [northSteps_eq_image hy] at hmem
  obtain ⟨i, -, hPi⟩ := mem_image.1 hmem
  have hone := one_le_wordPosition hy hP
  refine (isMarkedNorth_partnerPath_iff hy _).2 ⟨i, by rw [hPi]; exact hC, ?_⟩
  rw [hPi]
  omega

/-- **An event of type other than `C` does not mark the top position of its block.** Were it marked,
the type-`C` event whose block the position tops would share a word position with this one, and the
word position separates the events. -/
private theorem not_isMarkedNorth_pred {y : Heights a b N} (hy : IsAboveDiagonal y) (ha : 0 < a)
    (hN : 0 < N) {P : ℕ × ℕ} (hP : P ∈ eventPoints y) (hne : eventType y P ≠ EventType.C) :
    ¬Dyck.IsMarkedNorth (partnerPath y) (markedPositions y) (wordPosition y P - 1) := by
  intro hm
  obtain ⟨i, hC, hpos⟩ := (isMarkedNorth_partnerPath_iff hy _).1 hm
  have hone := one_le_wordPosition hy hP
  have heq : wordPosition y (stepFoot y i) = wordPosition y P := by omega
  have hEq := eq_of_wordPosition_eq hy ha hN (stepFoot_mem_eventPoints hy i) hP heq
  rw [hEq] at hC
  exact hne hC

/-- **An event of type other than `C` does not mark the position just above its block.** That
position tops the block of the next event up; if it were a marked north position, the type-`C` event
it belongs to would have a block meeting this one, and distinct events have disjoint blocks. -/
private theorem not_isMarkedNorth_wordPosition {y : Heights a b N} (hy : IsAboveDiagonal y)
    (ha : 0 < a) (hN : 0 < N) {P : ℕ × ℕ} (hP : P ∈ eventPoints y)
    (hne : eventType y P ≠ EventType.C) :
    ¬Dyck.IsMarkedNorth (partnerPath y) (markedPositions y) (wordPosition y P) := by
  intro hm
  obtain ⟨i, hC, hpos⟩ := (isMarkedNorth_partnerPath_iff hy _).1 hm
  obtain ⟨hPs, hPD, hPE⟩ := mem_eventPoints.1 hP
  have hFe := stepFoot_mem_eventPoints hy i
  have hone := one_le_wordPosition hy hP
  have hδ : blockSize y (stepFoot y i) = 2 := by simp [blockSize, hC]
  have hmem1 : wordPosition y P ∈ wordBlock y (stepFoot y i) := by
    rw [mem_wordBlock, hδ, hpos]
    omega
  have hmem2 : wordPosition y P ∈ wordBlock y P := wordPosition_mem_wordBlock hy hPs hPD hPE
  have hEq : stepFoot y i = P := by
    by_contra hne'
    exact Finset.disjoint_left.1 (disjoint_wordBlock hy ha hN hFe hP hne') hmem1 hmem2
  rw [hEq] at hC
  exact hne hC

/-- **The top position of the block of a type-`A` event carries an east step.** A north step of the
partner there would be the top position of the block of a north step of the path, which is an event
of type `B` or `C`, and the word position separates the events. -/
private theorem not_exists_partnerPath_pred {y : Heights a b N} (hy : IsAboveDiagonal y)
    (ha : 0 < a) (hN : 0 < N) {P : ℕ × ℕ} (hP : P ∈ eventPoints y)
    (hA : eventType y P = EventType.A) :
    ¬∃ k : Fin (b * N), partnerPath y k + (k : ℕ) = wordPosition y P - 1 := by
  rintro h
  obtain ⟨i, hpos⟩ := (exists_partnerPath_add_eq_iff hy _).1 h
  have hone := one_le_wordPosition hy hP
  have hFe := stepFoot_mem_eventPoints hy i
  have heq : wordPosition y (stepFoot y i) = wordPosition y P := by omega
  have hEq := eq_of_wordPosition_eq hy ha hN hFe hP heq
  have hmem : stepFoot y i ∈ northSteps y := by
    rw [northSteps_eq_image hy]
    exact mem_image_of_mem _ (mem_univ i)
  rcases (mem_northSteps_iff_eventType (mem_eventPoints.1 hFe).1).1 hmem with h1 | h1 <;>
    rw [hEq, hA] at h1 <;> exact absurd h1 (by simp)

/-- **The top position of the block of a type-`B` or type-`C` event carries a north step.** Such an
event is the foot of a north step by `HJO.Paths.mem_northSteps_iff_eventType`, and
`HJO.Paths.wordPosition_stepFoot` puts the `j`-th north step of the partner at the `0`-based
position `x'_j + j`. -/
private theorem exists_partnerPath_pred_of_foot {y : Heights a b N} (hy : IsAboveDiagonal y)
    {P : ℕ × ℕ} (hP : P ∈ eventPoints y)
    (hfoot : eventType y P = EventType.B ∨ eventType y P = EventType.C) :
    ∃ k : Fin (b * N), partnerPath y k + (k : ℕ) = wordPosition y P - 1 := by
  obtain ⟨hPs, hPD, hPE⟩ := mem_eventPoints.1 hP
  have hmem : P ∈ northSteps y := (mem_northSteps_iff_eventType hPs).2 hfoot
  rw [northSteps_eq_image hy] at hmem
  obtain ⟨i, -, hPi⟩ := mem_image.1 hmem
  have hone := one_le_wordPosition hy hP
  exact (exists_partnerPath_add_eq_iff hy _).2 ⟨i, by rw [hPi]; omega⟩

/-- **The lower position of the block of a type-`C` event carries an east step.** The sign
`ε_{r-1} = +` of the word, here `HJO.Dyck.IsSquareDyck.northPos_pred_ne` at the marked corner. -/
private theorem not_exists_partnerPath_sub_two {y : Heights a b N} (hy : IsAboveDiagonal y)
    {P : ℕ × ℕ} (hP : P ∈ eventPoints y) (hC : eventType y P = EventType.C) :
    ¬∃ k : Fin (b * N), partnerPath y k + (k : ℕ) = wordPosition y P - 2 := by
  obtain ⟨hPs, hPD, hPE⟩ := mem_eventPoints.1 hP
  have hδ : blockSize y P = 2 := by simp [blockSize, hC]
  have hδle := blockSize_le_wordPosition hy hPs hPD hPE
  obtain ⟨k, hk, -, hks⟩ := isMarkedNorth_pred_of_eventType_C hy hP hC
  rintro ⟨k', hk'⟩
  exact (isSquareDyck_partnerPath hy).northPos_pred_ne hk k' (by omega)


/-! ### The suffixes of the event listing -/

/-- **The total block size over a suffix of the event listing is the word position at its head.**
The elements of the suffix are exactly the events of rank at most `rk̂(P)` — those above it in the
decreasing listing have larger rank — and
`HJO.Paths.wordPosition_eq_sum_blockSize` sums the block sizes over that set. -/
private theorem blockSum_eq_wordPosition {y : Heights a b N} (hy : IsAboveDiagonal y) (ha : 0 < a)
    (hN : 0 < N) {Es : List (ℕ × ℕ)} (hE1 : ∀ P ∈ Es, P ∈ eventPoints y) (hE2 : Es.Nodup)
    (hE3 : Es.Pairwise fun A B => abovePointRank a b N B.1 B.2 < abovePointRank a b N A.1 A.2)
    (hE4 : ∀ P ∈ eventPoints y, P ∈ Es) {P : ℕ × ℕ} {Rs : List (ℕ × ℕ)}
    (hsuf : (P :: Rs) <:+ Es) :
    ((P :: Rs).map (blockSize y)).sum = wordPosition y P := by
  classical
  have hsub : (P :: Rs).Sublist Es := hsuf.sublist
  have hnd : (P :: Rs).Nodup := hE2.sublist hsub
  have hpw : (P :: Rs).Pairwise
      fun A B => abovePointRank a b N B.1 B.2 < abovePointRank a b N A.1 A.2 :=
    hE3.sublist hsub
  obtain ⟨pre, hpre⟩ := hsuf
  have hfin : (P :: Rs).toFinset = {Q ∈ eventPoints y |
      abovePointRank a b N Q.1 Q.2 ≤ abovePointRank a b N P.1 P.2} := by
    ext Q
    simp only [List.mem_toFinset, mem_filter]
    refine ⟨fun hQ => ⟨hE1 Q (hsub.mem hQ), ?_⟩, ?_⟩
    · rcases List.mem_cons.1 hQ with rfl | hQ'
      · exact le_rfl
      · exact le_of_lt (List.rel_of_pairwise_cons hpw hQ')
    · rintro ⟨hQe, hQr⟩
      have hQEs : Q ∈ Es := hE4 Q hQe
      rw [← hpre, List.mem_append] at hQEs
      rcases hQEs with hQpre | hQtail
      · exfalso
        have hpwEs := hE3
        rw [← hpre] at hpwEs
        have hlt := (List.pairwise_append.1 hpwEs).2.2 Q hQpre P List.mem_cons_self
        omega
      · exact hQtail
  rw [← List.sum_toFinset _ hnd, hfin,
    ← wordPosition_eq_sum_blockSize hy ha hN (hE1 P (hsub.mem List.mem_cons_self))]


/-! ### The induction -/

private theorem range_reverse_succ (m : ℕ) :
    (List.range (m + 1)).reverse = m :: (List.range m).reverse := by
  rw [List.range_succ, List.reverse_append]
  simp

/-- The width at the foot of a north step is positive: the step is live at its own foot. -/
private theorem one_le_sweepWidth_of_mem_northSteps {y : Heights a b N} {P : ℕ × ℕ}
    (hP : P ∈ northSteps y) : 1 ≤ sweepWidth y P := by
  rw [sweepWidth]
  exact card_pos.2 ⟨P, (mem_liveSteps_iff_eq_of_fst_eq hP rfl).2 rfl⟩

/-- **The transport induction.** Along a suffix of the decreasing-rank listing of the events, the
partial composite of the scalar-free sweep word at `Y_k(F)` is the partial composite of the word of
the partner at `F`, the positions consumed being the `p` lowest ones with `p` the total block
size of the suffix — and the level `k` being pinned by
`HJO.Mellit.two_mul_northBelow_eq_add_sweepWidth` as the width at the head.

This is the transport step of the proof read from the far end: the
`F♭_l = Y_{k_{l+1}}(F_l)` for `l` counting up from `0` is this statement for the suffix of length
`L - l`, and the three cases are its three cases. -/
private theorem foldl_psiOperator_eq_foldl_markedFactor (q : L) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (ha : 0 < a) (hN : 0 < N) {Es : List (ℕ × ℕ)}
    (hE1 : ∀ P ∈ Es, P ∈ eventPoints y) (hE2 : Es.Nodup)
    (hE3 : Es.Pairwise fun A B => abovePointRank a b N B.1 B.2 < abovePointRank a b N A.1 A.2)
    (hE4 : ∀ P ∈ eventPoints y, P ∈ Es) :
    ∀ Rs : List (ℕ × ℕ), Rs <:+ Es → ∀ (k : ℕ) (F : Total L),
      2 * northBelow (partnerPath y) ((Rs.map (blockSize y)).sum)
          = (Rs.map (blockSize y)).sum + k →
      Rs.foldl (fun G P => psiOperator q y P G) (transport L k F)
        = (List.range ((Rs.map (blockSize y)).sum)).reverse.foldl
            (fun G s => markedFactor q (partnerPath y) (markedPositions y) s G) F := by
  intro Rs
  induction Rs with
  | nil =>
    intro _ k F hk
    rw [List.map_nil, List.sum_nil, northBelow_zero] at hk
    rw [List.map_nil, List.sum_nil, List.range_zero, List.reverse_nil, List.foldl_nil,
      List.foldl_nil, show k = 0 from by omega, transport_zero]
  | cons P Rs' ih =>
    intro hsuf k F hk
    have hsuf' : Rs' <:+ Es := (List.suffix_cons P Rs').trans hsuf
    have hP : P ∈ eventPoints y := hE1 P (hsuf.sublist.mem List.mem_cons_self)
    obtain ⟨hPs, hPD, hPE⟩ := mem_eventPoints.1 hP
    have hp : ((P :: Rs').map (blockSize y)).sum = wordPosition y P :=
      blockSum_eq_wordPosition hy ha hN hE1 hE2 hE3 hE4 hsuf
    have hr : blockSize y P + (Rs'.map (blockSize y)).sum = wordPosition y P := by
      rw [← hp, List.map_cons, List.sum_cons]
    have hone := one_le_wordPosition hy hP
    have hδle := blockSize_le_wordPosition hy hPs hPD hPE
    have hwidth := two_mul_northBelow_eq_add_sweepWidth hy P
    rw [hp] at hk
    have hkw : k = sweepWidth y P := by omega
    have hlen : wordPosition y P - 1 < 2 * (b * N) := by
      have h1 := wordPosition_le y P
      rw [card_northSteps hy] at h1
      omega
    have hlev : Dyck.wordLevel (partnerPath y) (wordPosition y P - 1) = k := by
      rw [Dyck.wordLevel, ← northBelow_succ,
        show wordPosition y P - 1 + 1 = wordPosition y P from by omega]
      omega
    have hstep := northBelow_succ_eq (isSquareDyck_partnerPath hy) (wordPosition y P - 1)
    rw [show wordPosition y P - 1 + 1 = wordPosition y P from by omega] at hstep
    rw [hp, List.foldl_cons]
    rcases hev : eventType y P with _ | _ | _ | _ | _
    · -- type `A`: one position, an east step, the factor `d_+`
      have hδ : blockSize y P = 1 := by simp [blockSize, hev]
      have hnoN := not_exists_partnerPath_pred hy ha hN hP hev
      have hnm1 := not_isMarkedNorth_pred hy ha hN hP (by rw [hev]; decide)
      have hnm2 := not_isMarkedNorth_wordPosition hy ha hN hP (by rw [hev]; decide)
      obtain ⟨d, hd⟩ : ∃ d, wordPosition y P = d + 1 := ⟨wordPosition y P - 1, by omega⟩
      have hd1 : wordPosition y P - 1 = d := by omega
      rw [ite_eq_right hnoN, Nat.add_zero] at hstep
      rw [hd1] at hnoN hlev hnm1 hstep
      rw [hd] at hnm2 hstep hk
      have hrs : (Rs'.map (blockSize y)).sum = d := by omega
      have hfac : markedFactor q (partnerPath y) (markedPositions y) d = cmDPlus q k := by
        rw [markedFactor, ite_eq_right hnm1, ite_eq_right hnm2,
          getD_stepWord_partnerPath (by omega : d < 2 * (b * N)), ite_eq_right hnoN, hlev, stepOp_D]
      have hpsi : psiOperator q y P (transport L k F) = transport L (k + 1) (cmDPlus q k F) := by
        simp only [psiOperator, hev]
        rw [← hkw, dplus_transport]
      have hres := ih hsuf' (k + 1) (cmDPlus q k F) (by rw [hrs]; omega)
      rw [hrs] at hres
      rw [hpsi, hd, range_reverse_succ, List.foldl_cons, hfac, hres]
    · -- type `B`: one position, a north step, the factor `d_-`
      have hδ : blockSize y P = 1 := by simp [blockSize, hev]
      have hyesN := exists_partnerPath_pred_of_foot hy hP (Or.inl hev)
      have hnm1 := not_isMarkedNorth_pred hy ha hN hP (by rw [hev]; decide)
      have hnm2 := not_isMarkedNorth_wordPosition hy ha hN hP (by rw [hev]; decide)
      have hk1 : 1 ≤ k := by
        rw [hkw]
        exact one_le_sweepWidth_of_mem_northSteps
          ((mem_northSteps_iff_eventType hPs).2 (Or.inl hev))
      obtain ⟨m, hm⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      obtain ⟨d, hd⟩ : ∃ d, wordPosition y P = d + 1 := ⟨wordPosition y P - 1, by omega⟩
      have hd1 : wordPosition y P - 1 = d := by omega
      rw [ite_eq_left hyesN] at hstep
      rw [hd1] at hyesN hlev hnm1 hstep
      rw [hd] at hnm2 hstep hk
      have hrs : (Rs'.map (blockSize y)).sum = d := by omega
      have hfac : markedFactor q (partnerPath y) (markedPositions y) d = dminusCM q k := by
        rw [markedFactor, ite_eq_right hnm1, ite_eq_right hnm2,
          getD_stepWord_partnerPath (by omega : d < 2 * (b * N)), ite_eq_left hyesN, hlev, stepOp_U]
      have hpsi : psiOperator q y P (transport L k F) = transport L m (dminusCM q k F) := by
        simp only [psiOperator, hev]
        rw [← hkw, hm, dminus_transport]
      have hres := ih hsuf' m (dminusCM q k F) (by rw [hrs]; omega)
      rw [hrs] at hres
      rw [hpsi, hd, range_reverse_succ, List.foldl_cons, hfac, hres]
    · -- type `C`: a pair of positions, the factor `Δ`
      have hδ : blockSize y P = 2 := by simp [blockSize, hev]
      have hm1 := isMarkedNorth_pred_of_eventType_C hy hP hev
      have hnoN2 := not_exists_partnerPath_sub_two hy hP hev
      have hyesN := exists_partnerPath_pred_of_foot hy hP (Or.inr hev)
      have hk1 : 1 ≤ k := by
        rw [hkw]
        exact one_le_sweepWidth_of_mem_northSteps
          ((mem_northSteps_iff_eventType hPs).2 (Or.inr hev))
      obtain ⟨m, hm⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      obtain ⟨d, hd⟩ : ∃ d, wordPosition y P = d + 2 := ⟨wordPosition y P - 2, by omega⟩
      have hd1 : wordPosition y P - 1 = d + 1 := by omega
      have hd2 : wordPosition y P - 2 = d := by omega
      have hstep2 := northBelow_succ_eq (isSquareDyck_partnerPath hy) d
      rw [ite_eq_left hyesN] at hstep
      rw [hd1] at hyesN hlev hm1 hstep
      rw [hd2] at hnoN2
      rw [ite_eq_right hnoN2, Nat.add_zero] at hstep2
      rw [hd] at hstep hk
      have hnm0 : ¬Dyck.IsMarkedNorth (partnerPath y) (markedPositions y) d := fun hc =>
        (isSquareDyck_partnerPath hy).not_isMarkedNorth_succ hc hm1
      have hrs : (Rs'.map (blockSize y)).sum = d := by omega
      have hfac1 : markedFactor q (partnerPath y) (markedPositions y) (d + 1) = cmCorner q k := by
        rw [markedFactor, ite_eq_left hm1, hlev]
      have hfac0 : markedFactor q (partnerPath y) (markedPositions y) d = 1 := by
        rw [markedFactor, ite_eq_right hnm0, ite_eq_left hm1]
      have hpsi : psiOperator q y P (transport L k F) = transport L k (cmCorner q k F) := by
        simp only [psiOperator, hev]
        rw [← hkw, hm, corner_transport]
      have hres := ih hsuf' k (cmCorner q k F) (by rw [hrs]; omega)
      rw [hrs] at hres
      rw [hpsi, hd, show d + 2 = d + 1 + 1 from rfl, range_reverse_succ, List.foldl_cons,
        range_reverse_succ, List.foldl_cons, hfac1, hfac0, Module.End.one_apply, hres]
    · exact absurd hev hPD
    · exact absurd hev hPE


/-! ### The two words as folds -/

omit [Algebra ℚ L] in
/-- The word of `HJO.Sweep.markedWordOp` applied to a vector, as a fold consuming the positions from
the top down. -/
private theorem prod_ofFn_apply_eq_foldl (f : ℕ → Module.End L (Total L)) (m : ℕ) (G : Total L) :
    (List.ofFn fun s : Fin m => f (s : ℕ)).prod G
      = (List.range m).reverse.foldl (fun H s => f s H) G := by
  rw [foldl_apply_eq_prod_map_reverse, List.reverse_reverse, List.ofFn_eq_map,
    ← List.map_coe_finRange_eq_range, List.map_map]
  rfl

/-- The events of the sweep in strictly decreasing order of above-diagonal rank: the
`Q_1, …, Q_L`, cut out of the decreasing listing of `Sw(P̂)` by dropping the points of event type
`D` and `E`, which contribute the identity. -/
private noncomputable def eventList (a b N : ℕ) (y : Heights a b N) : List (ℕ × ℕ) :=
  (sortByRank a b N (sweptRegion y)).reverse.filter
    fun P => decide (eventType y P ≠ EventType.D ∧ eventType y P ≠ EventType.E)

private theorem mem_eventList {y : Heights a b N} {P : ℕ × ℕ} :
    P ∈ eventList a b N y ↔ P ∈ eventPoints y := by
  rw [eventList, List.mem_filter, List.mem_reverse, mem_eventPoints]
  simp only [decide_eq_true_eq, mem_sortByRank]

private theorem nodup_eventList (y : Heights a b N) : (eventList a b N y).Nodup :=
  (List.nodup_reverse.2 (sortByRank_nodup a b N (sweptRegion y))).filter _

private theorem toFinset_eventList {y : Heights a b N} :
    (eventList a b N y).toFinset = eventPoints y := by
  ext P
  rw [List.mem_toFinset, mem_eventList]

/-- The event listing is strictly decreasing in the rank: `HJO.Mellit.sortByRank` is weakly sorted,
and the rank is injective on the strip, so no two distinct events share a rank. -/
private theorem pairwise_eventList {y : Heights a b N} (ha : 0 < a) (hN : 0 < N) :
    (eventList a b N y).Pairwise
      fun A B => abovePointRank a b N B.1 B.2 < abovePointRank a b N A.1 A.2 := by
  have hweak : (eventList a b N y).Pairwise
      fun A B => pointRank a b N B ≤ pointRank a b N A :=
    (sortByRank_reverse_pairwise a b N (sweptRegion y)).sublist List.filter_sublist
  rw [List.pairwise_iff_forall_sublist]
  intro A B hsub
  have hA : A ∈ eventList a b N y := hsub.mem (by simp)
  have hB : B ∈ eventList a b N y := hsub.mem (by simp)
  have hAs : A ∈ sweptRegion y := (mem_eventPoints.1 (mem_eventList.1 hA)).1
  have hBs : B ∈ sweptRegion y := (mem_eventPoints.1 (mem_eventList.1 hB)).1
  have hle : pointRank a b N B ≤ pointRank a b N A :=
    (List.pairwise_iff_forall_sublist.1 hweak) hsub
  have hne : A ≠ B := (List.pairwise_iff_forall_sublist.1 (nodup_eventList y)) hsub
  rcases eq_or_lt_of_le hle with heq | hlt
  · exact absurd (Prod.ext (abovePointRank_injOn (b := b) ha hN (mem_sweptRegion.1 hAs).1
      (mem_sweptRegion.1 hBs).1 heq.symm).1 (abovePointRank_injOn (b := b) ha hN
        (mem_sweptRegion.1 hAs).1 (mem_sweptRegion.1 hBs).1 heq.symm).2) hne
  · exact hlt

/-- **The scalar-free sweep word at the vacuum is the fold over the events.** The points of event
type `D` and `E` contribute the identity, so they drop out. -/
private theorem psiWord_one_eq_foldl (q : L) {y : Heights a b N} :
    psiWord q y (1 : Total L)
      = (eventList a b N y).foldl (fun G P => psiOperator q y P G) (1 : Total L) := by
  have hone : ∀ P ∈ (sortByRank a b N (sweptRegion y)).reverse,
      ¬(decide (eventType y P ≠ EventType.D ∧ eventType y P ≠ EventType.E) = true) →
        psiOperator q y P = 1 := by
    intro P _ hnp
    simp only [decide_eq_true_eq, not_and, not_not] at hnp
    rcases hev : eventType y P with _ | _ | _ | _ | _
    · exact absurd (hnp (by rw [hev]; decide)) (by rw [hev]; decide)
    · exact absurd (hnp (by rw [hev]; decide)) (by rw [hev]; decide)
    · exact absurd (hnp (by rw [hev]; decide)) (by rw [hev]; decide)
    · simp only [psiOperator, hev]
    · simp only [psiOperator, hev]
  rw [eventList, ← foldl_filter_of_eq_one (psiOperator q y) _ _ hone,
    foldl_apply_eq_prod_map_reverse, List.reverse_reverse, psiWord]


/-! ### The identification of the two words at the vacuum -/

/-- **The scalar-free sweep word and the word of the partner agree at the vacuum.** The central
step of the proof of
`HJO.Mellit.constantCoeff_psiWord_one_mem_lambdaComp_and_map_eq_sweepChar`:
`(Ψ_{P̂}(P_M) ∘ ⋯ ∘ Ψ_{P̂}(P_1))(1) = Ξ_{P̂', S(P̂)}(1)`, with `P̂'` the square partner
`HJO.Mellit.partnerPath` and `S(P̂)` the marked set `HJO.Mellit.markedPositions`.

This is the hypothesis `hword` of
`HJO.Mellit.map_constantCoeff_psiWord_eq_sweepChar_of_cor46`, and it is an equation at `1` and not
an identity of operators: the transport `Y_k` of `HJO.Sweep.transport` intervenes at every
intermediate index, and only at the two ends, where the index is `0`, is it the identity.

Everything is carried by `HJO.Mellit.foldl_psiOperator_eq_foldl_markedFactor`. On the degenerate
rectangle `bN = 0` the path has no north step, so by `HJO.Paths.mem_northSteps_iff_eventType` and
`HJO.Paths.isSweepHead_iff_eventType` every swept point has event type `D` or `E`, and both words
are the empty product. -/
theorem psiWord_one_eq_markedWordOp_one (q : L) {y : Heights a b N} (hy : IsAboveDiagonal y) :
    psiWord q y (1 : Total L)
      = Sweep.markedWordOp q (partnerPath y) (markedPositions y) (1 : Total L) := by
  rcases Nat.eq_zero_or_pos (b * N) with h0 | h0
  · have hne : northSteps y = ∅ := by
      rw [← Finset.card_eq_zero, card_northSteps hy, h0]
    have hall : ∀ e ∈ (sortByRank a b N (sweptRegion y)).map (psiOperator q y), e = 1 := by
      intro e he
      obtain ⟨P, hPl, rfl⟩ := List.mem_map.1 he
      have hPs : P ∈ sweptRegion y := mem_sortByRank.1 hPl
      rcases hev : eventType y P with _ | _ | _ | _ | _
      · obtain ⟨u, hu, -⟩ := (isSweepHead_iff_eventType hy hPs).2 (Or.inl hev)
        rw [hne] at hu
        exact absurd hu (notMem_empty _)
      · have h1 := (mem_northSteps_iff_eventType hPs).2 (Or.inl hev)
        rw [hne] at h1
        exact absurd h1 (notMem_empty _)
      · have h1 := (mem_northSteps_iff_eventType hPs).2 (Or.inr hev)
        rw [hne] at h1
        exact absurd h1 (notMem_empty _)
      · simp only [psiOperator, hev]
      · simp only [psiOperator, hev]
    rw [psiWord, List.prod_eq_one hall, markedWordOp_eq_one_of_eq_zero q h0]
  · have hpos := mul_pos_of_isAboveDiagonal hy (⟨0, h0⟩ : Fin (b * N))
    have ha : 0 < a := Nat.pos_of_ne_zero fun hc => by simp [hc] at hpos
    have hN : 0 < N := Nat.pos_of_ne_zero fun hc => by simp [hc] at hpos
    have hsum : ((eventList a b N y).map (blockSize y)).sum = 2 * (b * N) := by
      rw [← List.sum_toFinset _ (nodup_eventList y), toFinset_eventList,
        sum_blockSize_eventPoints hy]
    have hnb : northBelow (partnerPath y) (2 * (b * N)) = b * N := by
      have hallk : ∀ k ∈ (univ : Finset (Fin (b * N))),
          partnerPath y k + (k : ℕ) < 2 * (b * N) := by
        intro k _
        have := (isSquareDyck_partnerPath hy).add_index_add_one_lt_two_mul k
        omega
      rw [northBelow, filter_true_of_mem hallk, card_univ, Fintype.card_fin]
    have hmain := foldl_psiOperator_eq_foldl_markedFactor q hy ha hN
      (fun P hP => mem_eventList.1 hP) (nodup_eventList y) (pairwise_eventList ha hN)
      (fun P hP => mem_eventList.2 hP) (eventList a b N y) (List.suffix_refl _) 0
      (1 : Total L) (by rw [hsum, hnb]; omega)
    rw [transport_zero, hsum] at hmain
    rw [psiWord_one_eq_foldl q, hmain, Sweep.markedWordOp_eq_prod,
      prod_ofFn_apply_eq_foldl
        (fun s => Sweep.markedFactor q (partnerPath y) (markedPositions y) s)]

/-! ### `HJO.Mellit.constantCoeff_psiWord_one_mem_lambdaComp_and_map_eq_sweepChar` and
`HJO.Mellit.sweepComputes` modulo `HJO.Mellit.map_constantCoeff_markedWordOp'` -/

/-- **`HJO.Mellit.constantCoeff_psiWord_one_mem_lambdaComp_and_map_eq_sweepChar` modulo
`HJO.Mellit.map_constantCoeff_markedWordOp'` alone.** The whole of the lemma in the encoding
`HJO.Mellit.sweepComputes` uses, with the identification of the two words discharged by
`HJO.Mellit.psiWord_one_eq_markedWordOp_one`: the element `f = (Ψ_{P̂}(P_M) ∘ ⋯ ∘ Ψ_{P̂}(P_1))(1)`
of `Λ` is homogeneous of degree `bN` and every realisation carries it to `χ(P̂)`.

The hypothesis `hcor46` is the content of `HJO.Mellit.map_constantCoeff_markedWordOp'`. -/
theorem constantCoeff_psiWord_one_mem_lambdaComp_and_map_eq_sweepChar_of_cor46_alone (q : L)
    {y : Heights a b N} (hy : IsAboveDiagonal y)
    {ι : Sym.Lambda L →ₐ[L] Sym.AlphabetSeries L} (hι : Sym.IsRealisation ι)
    (hcor46 : ∀ {n : ℕ} (x : Fin n → ℕ) (T : Finset (ℕ × ℕ)), 1 ≤ n → Dyck.IsSquareDyck n x →
      T ⊆ Dyck.corner x →
      ι (MvPolynomial.constantCoeff (Sweep.markedWordOp q x T (1 : Total L)))
        = Dyck.pathMarkedCharSeries q x T) :
    MvPolynomial.constantCoeff (psiWord q y (1 : Total L)) ∈ Sym.LambdaComp L (b * N) ∧
      ι (MvPolynomial.constantCoeff (psiWord q y (1 : Total L))) = sweepChar q y :=
  constantCoeff_psiWord_one_mem_lambdaComp_and_map_eq_sweepChar_of_cor46 q hy hι
    (psiWord_one_eq_markedWordOp_one q hy) hcor46

/-- **`HJO.Mellit.SweepComputes` modulo `HJO.Mellit.map_constantCoeff_markedWordOp'` alone.** One of
the three hypotheses of `HJO.Mellit.shuffle_of_three`, with nothing left on the sweep side but
`HJO.Mellit.map_constantCoeff_markedWordOp'`.

`q ≠ 0` is what collecting the scalars of `HJO.Mellit.sweepOperator` costs; every consumer has it,
`shuffle_of_three` asking for `SweepComputes` only under `AlgebraicIndependent ℤ ![q, u]`. -/
theorem sweepComputes_of_cor46_alone (q u : L) (hq : q ≠ 0)
    (hcor46 : ∀ ι : Sym.Lambda L →ₐ[L] Sym.AlphabetSeries L, Sym.IsRealisation ι →
      ∀ {n : ℕ} (x : Fin n → ℕ) (T : Finset (ℕ × ℕ)), 1 ≤ n → Dyck.IsSquareDyck n x →
        T ⊆ Dyck.corner x →
        ι (MvPolynomial.constantCoeff (Sweep.markedWordOp q x T (1 : Total L)))
          = Dyck.pathMarkedCharSeries q x T) :
    SweepComputes q u a b :=
  sweepComputes_of_cor46 q u hq (fun _ _ hy => psiWord_one_eq_markedWordOp_one q hy) hcor46

/-- **`HJO.Mellit.sweepComputes` modulo `HJO.Mellit.map_constantCoeff_markedWordOp'` alone.** The
statement: for an above-diagonal `(aN, bN)`-path `y` and a realisation `ι`, the
element `f = W(P̂)(1)` of `Λ` is homogeneous of degree `bN` and
`ι(f) = u^{ârea(P̂)} q^{ĥ(P̂) - max t̂dinv(P̂)} χ(P̂)`.

The hypothesis `hcor46` is the content of `HJO.Mellit.map_constantCoeff_markedWordOp'`. -/
theorem constantCoeff_sweepWord_one_mem_lambdaComp_and_map_eq_smul_sweepChar_of_cor46_alone
    (q u : L) (hq : q ≠ 0) {y : Heights a b N} (hy : IsAboveDiagonal y)
    {ι : Sym.Lambda L →ₐ[L] Sym.AlphabetSeries L} (hι : Sym.IsRealisation ι)
    (hcor46 : ∀ {n : ℕ} (x : Fin n → ℕ) (T : Finset (ℕ × ℕ)), 1 ≤ n → Dyck.IsSquareDyck n x →
      T ⊆ Dyck.corner x →
      ι (MvPolynomial.constantCoeff (Sweep.markedWordOp q x T (1 : Total L)))
        = Dyck.pathMarkedCharSeries q x T) :
    MvPolynomial.constantCoeff (sweepWord q u y (1 : Total L)) ∈ Sym.LambdaComp L (b * N) ∧
      ι (MvPolynomial.constantCoeff (sweepWord q u y (1 : Total L))) =
        (u ^ aboveArea y * q ^ ((aboveHookCount y : ℤ) - (aboveMaxTdinv y : ℤ))) •
          sweepChar q y :=
  constantCoeff_sweepWord_one_mem_lambdaComp_and_map_eq_smul_sweepChar_of_cor46 q u hq hy hι
    (psiWord_one_eq_markedWordOp_one q hy) hcor46

end HJO.Mellit
