/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidCDLetterRank
public import HJO.Shuffle.CornerClosedForm
public import HJO.Shuffle.MellitAppend
public import HJO.Shuffle.BraidTypeAOrbit
public meta import HJO.Attr

/-! # `T_{1↘k} ỹ_k` against `Δ^{(k)}`: the type-`C` clause, closed

`HJO/Shuffle/BraidCDLetterRank.lean` leaves the type-`C` clause of
`HJO.Mellit.braidValueColouring_sweepRecursionsFloor` hanging on one hypothesis `htrain`, with no
geometry in it: that `π_k` of the letter `T_{1↘k} ỹ_k`, applied to the braid value of the **lower
positions with the upper multiplicities** and scaled by the `r`-power the two `HJO.Braid.invFin`
counts differ by, is `q^{-(k-1-j)}Δ^{(k)}` of the upper braid value. **This file discharges it, and
the clause with it.**

## The two sides are the same word, and the scalars agree

Three computations, each of which would silently move the `q`-power if it were off:

1. **The word collapses.** `HJO.Braid.braidTrainDown_one_mul_braidYtilde_self`:
   `T_{1↘k} ỹ_k = T_{1↗k} y_k`, because `HJO.Braid.braidYtilde` at the top index begins with
   `T_{k↘1}` and `T_{1↘k}T_{k↘1} = 1` (`HJO.Braid.trainDown_mul_trainDown_self`). So
   `HJO.Mellit.coe_braidRepMellit_braidTrainDown_one_mul_braidYtilde` reads `π_k` of the letter as
   `-q^{-(k-1)/2}T_{1↗k}(y_k·)`, the `y` being multiplication by `-y_k`
   (`HJO.Sweep.yRepTotal_eq_neg_mulLeft`) and each of the `k-1` inverted braid letters carrying an
   `r`. And `HJO.Sweep.corner_eq_neg_cmAscWord_auxVar_mul` reads `Δ^{(k)}` as `-T_{1↗k}(y_k·)`
   (`HJO.Mellit.corner_eq_neg_trainUpEnd_auxVar_mul`, the same operator with `HJO.Sweep.cmAscWord`
   unfolded). **The two sides carry the same operator, signs included** — nothing is matched "up to"
   anything.
2. **The `r`-power is `2j - (k-1)`.** `HJO.Mellit.Isolates.invFin_sub_invFin_of_eventType_C`. The
   mixed final tuple has the moving entry at the top and the raised one has it at the bottom — that
   is what `HJO/Shuffle/BraidCDLetterRank.lean` proved to get the index and the train — so the
   `k-1-j` inversions above `j` die and the `j` below it are born
   (`HJO.Braid.tupleInversions_sub_tupleInversions_of_top_bot`). The rank-`k` statement there is
   weak; `HJO.Mellit.Isolates.lt_positionPair_snd_of_eventType_C` supplies the strict maximality the
   inversion count needs, and rank `1` already *is* strict minimality
   (`HJO.Braid.forall_ne_lt_of_entryRank_eq_one`).
3. **They reconcile.** `r^{2j-(k-1)}·r^{-(k-1)} = q^{-(k-1-j)}` (`HJO.Mellit.zpow_sub_mul_inv_pow`),
   which is `HJO.Mellit.sweepOperator`'s own exponent. So after step 1 the identity is the equality
   of two applications of ONE operator to two braid values, with no scalar left over.

## The last residual, and why the standard rigid shift could not reach it

What remains is `braidValueOfData v_- α_+ = braidValueOfData v_+ α_+`: the mixed data is the upper
data with every position raised by `HJO.Mellit.levelDropShift`, and
`HJO.Mellit.braidValueOfData_congr_add` says such a shift is invisible — provided it carries no
stage position across the puncture. **At type `C` it carries exactly one.** The last stage of the
moving index is the crossing `(X, Y+1)`, whose normalised rank sits *above* `θ` at the lower level
and *below* it at the upper one; that is the very fact
`HJO.Mellit.Isolates.braidStep_positionPair_snd_of_eventType_C` uses to read the letter as a `ỹ`.

So the hypothesis of `HJO.Mellit.braidValueOfData_congr_add` is unusable as stated, and the repair
is not a strengthening of the geometry but a **sharpening of the algebra**:
`HJO.Braid.braidWord_cons` evaluates `HJO.Braid.braidStep` at the tuple the *remaining* moves have
reached, so no letter ever sees an entry at its own last stage.
`HJO.Braid.specialBraid_congr_add_of_iterate_lt` and `HJO.Mellit.braidValueOfData_congr_add_of_lt`
carry the condition only at the stages a move starts from — `m < α_i - 1` rather than `m ≤ α_i - 1`
— and that is exactly what a type-`C` drop supplies
(`HJO.Mellit.Isolates.sameSide_iterate_of_eventType_C`, via the crossing-index bookkeeping of
`HJO.Mellit.exists_pointRank_iterate_nextCrossing_eq_sub`). The moving index's last stage is the one
excluded point; every other index misses `(X, Y+1)` because distinct components share no crossing
index.

## What is closed, and what is not

`HJO.Mellit.Isolates.braidValueColouring_eq_sweepOperator_of_eventType_C_of_win` is the type-`C`
clause with no hypothesis about the braid at all, the index `j` constructed rather than assumed; and
`..._of_lt` / `..._of_succ` discharge the inherited window bound `hwin` from `a < b` or from
`η_+ = η_- + 1` respectively. **The scope limit of `hwin` is inherited, not widened**: for `b ≤ a`
with a level gap above `1` the entry-rank identity of
`HJO/Shuffle/BraidCDLetterRank.lean` is unproved, and so is this clause.

**This does not prove `HJO.Mellit.braidValueColouring_sweepRecursionsFloor`.** With the type-`A`
clause (`HJO.Mellit.Isolates.braidValueColouring_eq_sweepOperator_of_eventType_A_uncond`) two of its
four clauses are closed; the type-`D` clause, the origin, the unswept clause and all six recursions
are untouched.

## Genericity

`q ≠ 0`, `q ≠ 1`, `q + 1 ≠ 0`, `r * r = q` and nothing else — `HJO.Sweep.braidRep`'s own exclusions,
which the clause being closed already carried. `q ≠ 1` is spent on the `(q-1)^{-1}` of
`HJO.Sweep.corner`; `q ≠ 0` is spent twice over, on `HJO.Sweep.yRepTotal_eq_neg_mulLeft`, on
`HJO.Sweep.corner_eq_neg_cmAscWord_auxVar_mul` and on `r ≠ 0` inside the `zpow`. No new inverse is
introduced: every scalar here is a `zpow` of `r`, so no letter becomes the zero map at a parameter
where the unreduced clause's letters did not. The geometry is `ℕ`, `ℤ` and `ℚ` and needs `0 < a`,
`0 < b`, `0 < N` only.

## References

A. Mellit, *Toric braids and `(m, n)`-parking functions*, section 5.
-/

@[expose] public section

open Finset

namespace HJO.Braid

variable {k : ℕ}

/-- **`T_{1↘k} ỹ_k = T_{1↗k} y_k`.** -/
theorem braidTrainDown_one_mul_braidYtilde_self (hk : 1 ≤ k) :
    braidTrainDown k 1 k * braidYtilde k k = braidTrainUp k 1 k * braidGenY k k := by
  rw [braidYtilde_self, ← mul_assoc, ← mul_assoc,
    trainDown_mul_trainDown_self (isBraidSystem_braidGenT k) le_rfl hk hk le_rfl, one_mul]

/-- **Rank `1` is strict minimality.** `HJO.Braid.entryRank` counts the entries weakly below the
given one, so a count of `1` says the entry itself is the only one, i.e. every other entry is
strictly above. The converse of `HJO.Braid.entryRank_eq_one_of_forall_ne_lt`. -/
theorem forall_ne_lt_of_entryRank_eq_one {α : Type*} [LinearOrder α] (w : Fin k → α) (i : Fin k)
    (h : entryRank w i = 1) : ∀ t, t ≠ i → w i < w t := by
  intro t ht
  rw [entryRank, Finset.card_eq_one] at h
  obtain ⟨c, hc⟩ := h
  have hi : i ∈ ({c} : Finset (Fin k)) := by
    rw [← hc]; exact Finset.mem_filter.2 ⟨Finset.mem_univ _, le_rfl⟩
  by_contra hcon
  have ht' : t ∈ ({c} : Finset (Fin k)) := by
    rw [← hc]; exact Finset.mem_filter.2 ⟨Finset.mem_univ _, le_of_not_gt hcon⟩
  exact ht ((Finset.mem_singleton.1 ht').trans (Finset.mem_singleton.1 hi).symm)

/-! ### The inversion count when one entry travels from the top to the bottom -/

/-- The pairs with first coordinate `j` and second above it are counted by `Ioi j`. -/
private theorem card_pair_fst_eq (k : ℕ) (j : Fin k) :
    #{p ∈ (univ : Finset (Fin k × Fin k)) | p.1 = j ∧ j < p.2} = #(Finset.Ioi j) := by
  refine Finset.card_bij (fun p _ => p.2) (fun p hp => ?_) (fun p hp p' hp' he => ?_)
    (fun t ht => ⟨(j, t), by simpa using Finset.mem_Ioi.1 ht, rfl⟩)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    exact Finset.mem_Ioi.2 hp.2
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hp'
    exact Prod.ext (hp.1.trans hp'.1.symm) he

/-- The pairs with second coordinate `j` and first below it are counted by `Iio j`. -/
private theorem card_pair_snd_eq (k : ℕ) (j : Fin k) :
    #{p ∈ (univ : Finset (Fin k × Fin k)) | p.2 = j ∧ p.1 < j} = #(Finset.Iio j) := by
  refine Finset.card_bij (fun p _ => p.1) (fun p hp => ?_) (fun p hp p' hp' he => ?_)
    (fun t ht => ⟨(t, j), by simpa using Finset.mem_Iio.1 ht, rfl⟩)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    exact Finset.mem_Iio.2 hp.2
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hp'
    exact Prod.ext he (hp.1.trans hp'.1.symm)

/-- The inversions of `w` at index pairs avoiding `j`: the part of the count that a change at
`j` alone cannot touch. -/
def offInversions {k : ℕ} (w : Fin k → ℚ) (j : Fin k) : ℕ :=
  #{p ∈ (univ : Finset (Fin k × Fin k)) |
    (p.1 < p.2 ∧ w p.2 < w p.1) ∧ p.1 ≠ j ∧ p.2 ≠ j}

theorem offInversions_congr {k : ℕ} {w w' : Fin k → ℚ} {j : Fin k}
    (h : ∀ i, i ≠ j → w' i = w i) : offInversions w' j = offInversions w j := by
  unfold offInversions
  refine Finset.card_nbij id (fun p hp => ?_) Function.injective_id.injOn (fun p hp => ?_)
  · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, id_eq] at hp ⊢
    exact ⟨⟨hp.1.1, by rw [← h _ hp.2.2, ← h _ hp.2.1]; exact hp.1.2⟩, hp.2⟩
  · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, id_eq] at hp ⊢
    exact ⟨p, ⟨⟨hp.1.1, by rw [h _ hp.2.2, h _ hp.2.1]; exact hp.1.2⟩, hp.2⟩, rfl⟩

/-- **An entry that is the strict maximum contributes `k - 1 - j` inversions.** Every pair
`(j, t)` with `j < t` is inverted and no pair `(t, j)` is. -/
theorem tupleInversions_eq_offInversions_add_card_Ioi {k : ℕ} {w : Fin k → ℚ} {j : Fin k}
    (hmax : ∀ i, i ≠ j → w i < w j) :
    tupleInversions w = offInversions w j + #(Finset.Ioi j) := by
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := {p ∈ (univ : Finset (Fin k × Fin k)) | p.1 < p.2 ∧ w p.2 < w p.1})
    (fun p : Fin k × Fin k => p.1 ≠ j ∧ p.2 ≠ j)
  rw [Finset.filter_filter, Finset.filter_filter] at hsplit
  rw [tupleInversions_eq_card_lt, ← hsplit, ← card_pair_fst_eq k j, offInversions]
  congr 1
  refine Finset.card_nbij id (fun p hp => ?_) Function.injective_id.injOn (fun p hp => ?_)
  · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, id_eq, not_and,
      not_not] at hp ⊢
    obtain ⟨⟨hlt, hw⟩, hne⟩ := hp
    by_cases hp1 : p.1 = j
    · exact ⟨hp1, hp1 ▸ hlt⟩
    · rw [hne hp1] at hw
      exact absurd hw (asymm (hmax p.1 hp1))
  · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, id_eq, not_and,
      not_not] at hp ⊢
    obtain ⟨hp1, hlt⟩ := hp
    have hne2 : p.2 ≠ j := fun hc => absurd (hc ▸ hlt) (lt_irrefl _)
    refine ⟨p, ⟨⟨hp1 ▸ hlt, ?_⟩, fun hc => absurd hp1 hc⟩, rfl⟩
    rw [hp1]
    exact hmax p.2 hne2

/-- **An entry that is the strict minimum contributes `j` inversions.** Every pair `(t, j)` with
`t < j` is inverted and no pair `(j, t)` is. -/
theorem tupleInversions_eq_offInversions_add_card_Iio {k : ℕ} {w : Fin k → ℚ} {j : Fin k}
    (hmin : ∀ i, i ≠ j → w j < w i) :
    tupleInversions w = offInversions w j + #(Finset.Iio j) := by
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := {p ∈ (univ : Finset (Fin k × Fin k)) | p.1 < p.2 ∧ w p.2 < w p.1})
    (fun p : Fin k × Fin k => p.1 ≠ j ∧ p.2 ≠ j)
  rw [Finset.filter_filter, Finset.filter_filter] at hsplit
  rw [tupleInversions_eq_card_lt, ← hsplit, ← card_pair_snd_eq k j, offInversions]
  congr 1
  refine Finset.card_nbij id (fun p hp => ?_) Function.injective_id.injOn (fun p hp => ?_)
  · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, id_eq, not_and,
      not_not] at hp ⊢
    obtain ⟨⟨hlt, hw⟩, hne⟩ := hp
    by_cases hp2 : p.2 = j
    · exact ⟨hp2, hp2 ▸ hlt⟩
    · have hp1 : p.1 = j := by by_contra hc; exact hp2 (hne hc)
      rw [hp1] at hw
      exact absurd hw (asymm (hmin p.2 hp2))
  · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, id_eq, not_and,
      not_not] at hp ⊢
    obtain ⟨hp2, hlt⟩ := hp
    have hne1 : p.1 ≠ j := fun hc => absurd (hc ▸ hlt) (lt_irrefl _)
    refine ⟨p, ⟨⟨hp2 ▸ hlt, ?_⟩, fun _ => hp2⟩, rfl⟩
    rw [hp2]
    exact hmin p.1 hne1

/-- **THE INVERSION COUNT OF A TOP-TO-BOTTOM MOVE.** If `w'` agrees with `w` off the index `j`,
the `j`-th entry of `w` is the strict maximum and the `j`-th entry of `w'` is the strict minimum,
then the inversion count changes by `j - (k - 1 - j)`: the `k - 1 - j` inversions `(j, t)` with
`t > j` are destroyed and the `j` inversions `(t, j)` with `t < j` are created. Everything else is
untouched. -/
theorem tupleInversions_sub_tupleInversions_of_top_bot {k : ℕ} {w w' : Fin k → ℚ} {j : Fin k}
    (hagree : ∀ i, i ≠ j → w' i = w i) (hmax : ∀ i, i ≠ j → w i < w j)
    (hmin : ∀ i, i ≠ j → w' j < w' i) :
    (tupleInversions w' : ℤ) - (tupleInversions w : ℤ)
      = ((j : ℕ) : ℤ) - ((k - 1 - (j : ℕ) : ℕ) : ℤ) := by
  rw [tupleInversions_eq_offInversions_add_card_Iio hmin,
    tupleInversions_eq_offInversions_add_card_Ioi hmax, offInversions_congr hagree,
    Fin.card_Iio, Fin.card_Ioi]
  omega

/-! ### The rigid shift, needing the puncture condition only at the stages a move STARTS from

`HJO.Braid.specialBraid_congr_add` asks `HJO.Braid.SameSide` at every stage of every entry,
including the LAST one, `α_i - 1`. That stage is never read: `HJO.Braid.braidWord_cons` evaluates
`HJO.Braid.braidStep` at the tuple the *remaining* moves have reached, so the tuple a letter sees
has the moving entry at a stage strictly below its last. The variants below carry the hypothesis
only at those stages, and that is exactly what a type-`C` drop can supply — at the moving index the
last stage is the crossing `(X, Y+1)`, which is the ONE point the rigid shift does carry across the
puncture. -/

/-- `HJO.Braid.moveTuple_add_of_sameSide` with the condition imposed only at the tuple each move
starts from, for the index that move carries. -/
theorem moveTuple_add_of_sameSide_move {k : ℕ} (θ c : ℚ) (w : Fin k → ℚ) :
    ∀ l : List (Fin k),
      (∀ (i : Fin k) (l' : List (Fin k)), i :: l' <:+ l → SameSide θ c (moveTuple θ w l' i)) →
      ∀ t : Fin k, moveTuple θ (fun j => w j + c) l t = moveTuple θ w l t + c
  | [], _, _ => rfl
  | i :: rest, hl, t => by
      rw [moveTuple_cons, moveTuple_cons]
      exact moveOne_add_of_sameSide θ
        (moveTuple_add_of_sameSide_move θ c w rest
          (fun s l' hl' => hl s l' (hl'.trans (List.suffix_cons i rest))))
        (hl i rest List.suffix_rfl) t

/-- `HJO.Braid.braidWord_congr_add` with the condition imposed only at the tuple each move starts
from. -/
theorem braidWord_congr_add_of_move {k : ℕ} (θ c : ℚ) (w : Fin k → ℚ) :
    ∀ l : List (Fin k),
      (∀ (i : Fin k) (l' : List (Fin k)), i :: l' <:+ l → SameSide θ c (moveTuple θ w l' i)) →
      braidWord θ (fun j => w j + c) l = braidWord θ w l
  | [], _ => rfl
  | i :: rest, hl => by
      rw [braidWord_cons, braidWord_cons,
        braidWord_congr_add_of_move θ c w rest
          (fun s l' hl' => hl s l' (hl'.trans (List.suffix_cons i rest))),
        braidStep_congr_add
          (moveTuple_add_of_sameSide_move θ c w rest
            (fun s l' hl' => hl s l' (hl'.trans (List.suffix_cons i rest))))
          (hl i rest List.suffix_rfl)]

/-- **The special braid is unchanged by a rigid shift that crosses the puncture at no stage a move
starts from.** `HJO.Braid.specialBraid_congr_add_of_iterate` with `≤ α_i - 1` weakened to
`< α_i - 1`: a suffix of `HJO.Braid.specialBraid`'s move list that still has a copy of `i` to
perform has seen at most `α_i - 2` of them. -/
theorem specialBraid_congr_add_of_iterate_lt {k : ℕ} (θ c : ℚ) (v : Fin k → ℚ) (α : Fin k → ℕ)
    (h : ∀ (i : Fin k) (m : ℕ), m < α i - 1 → SameSide θ c ((nextCrossing θ)^[m] (v i))) :
    specialBraid θ (fun j => v j + c) α = specialBraid θ v α := by
  refine braidWord_congr_add_of_move θ c v (specialMoveList α) fun i l' hl' => ?_
  rw [moveTuple_apply_eq_iterate]
  refine h i _ ?_
  have hcount : (i :: l').count i ≤ (specialMoveList α).count i := hl'.sublist.count_le i
  rw [List.count_cons_self, count_specialMoveList] at hcount
  omega

end HJO.Braid

namespace HJO.Sweep

open Braid

variable {L : Type*} [Field L] [Algebra ℚ L] {q u r : L} {K : ℕ}
variable {h : BraidRepRespects q u r K}

/-- `π_K(y_K)` is multiplication by `-y_K`. -/
theorem representedBy_braidGenY_self (hq : q ≠ 0) (hr : r * r = q) (hK : 1 ≤ K) :
    RepresentedBy q u r K h (braidGenY K K)
      (-LinearMap.mulLeft L (auxVar K : Total L)) := fun x => by
  rw [braidRep_y, coe_yRep, yRepTotal_eq_neg_mulLeft q u hq hr hK le_rfl]

/-- `π_K(T_{1↘K} ỹ_K) = -q^{-(K-1)/2} T_{1↗K} ∘ (y_K · )`. -/
theorem representedBy_braidTrainDown_one_mul_braidYtilde (hq : q ≠ 0) (hr : r * r = q)
    (hK : 1 ≤ K) :
    RepresentedBy q u r K h (braidTrainDown K 1 K * braidYtilde K K)
      (-((r⁻¹ : L) ^ (K - 1) •
        (trainUpEnd q 1 K * LinearMap.mulLeft L (auxVar K : Total L)))) := by
  rw [braidTrainDown_one_mul_braidYtilde_self hK]
  refine ((representedBy_braidTrainUp_bot hK).mul
    (representedBy_braidGenY_self hq hr hK)).congr ?_
  rw [mul_neg, smul_mul_assoc]

end HJO.Sweep

namespace HJO.Mellit

open Braid Finset ParkingFunctions Paths Sweep

variable {a b N : ℕ}

/-- **The braid value is unchanged by a rigid shift that crosses the puncture at no stage a move
starts from.** `HJO.Mellit.braidValueOfData_congr_add` with `≤ α_i - 1` weakened to `< α_i - 1`:
`HJO.Braid.specialBraid_congr_add_of_iterate_lt` for the braid, and `HJO.Braid.invFin_congr_add` —
which already asked only for the strict bound — for the prefactor. -/
theorem braidValueOfData_congr_add_of_lt {L : Type*} [Field L] [Algebra ℚ L] (q u : L) {r : L}
    (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) (hr : r * r = q) (a b N : ℕ) {k : ℕ}
    (v : Fin k → ℚ) (α : Fin k → ℕ) (c : ℚ)
    (h : ∀ (i : Fin k) (m : ℕ), m < α i - 1 →
      SameSide (sweepTheta a b N) c ((nextCrossing (sweepTheta a b N))^[m] (v i))) :
    braidValueOfData q u hq hq1 hqp hr a b N (fun j => v j + c) α
      = braidValueOfData q u hq hq1 hqp hr a b N v α := by
  rw [braidValueOfData, braidValueOfData, specialBraid_congr_add_of_iterate_lt _ c v α h,
    invIni_congr_add, invFin_congr_add _ c v α h]

/-! ### Every stage crossing, with its index named -/

/-- **`HJO.Mellit.exists_pointRank_iterate_nextCrossing` with the crossing index returned.** The
`m`-th stage of the `i`-th component realises the crossing of index `componentTop - m`, and at a
type-`C` drop the whole argument turns on comparing that index with `X + Y + 1`, the bottom index of
the moving component. -/
theorem exists_pointRank_iterate_nextCrossing_eq_sub (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    {η : ℚ} (hη : IsAdmissibleLevel η) (hηa : ((a * N : ℕ) : ℚ) < η) {y : Heights a b N}
    (hy : IsAboveDiagonal y) {k : ℕ} (hk : #(colouringEast y η) = k) (i : Fin k) {m : ℕ}
    (hm : m ≤ (braidDataOfColouring a b N y η k).2 i - 1) :
    ∃ x yy : ℕ, (x : ℤ) + (yy : ℤ) = componentTopIndex a b N y η (i : ℕ) - (m : ℤ) ∧
      componentBotIndex a b N y η (i : ℕ) ≤ (x : ℤ) + (yy : ℤ) ∧
      x < a * N ∧ 0 < yy ∧ yy ≤ ht y (x + 1) ∧
      η < ((pointRank a b N (x, yy) : ℤ) : ℚ) ∧
      (nextCrossing (sweepTheta a b N))^[m] ((braidDataOfColouring a b N y η k).1 i)
        = levelPosition a b N η ((pointRank a b N (x, yy) : ℤ) : ℚ) := by
  have hηpos : 0 < η := lt_of_le_of_lt (Nat.cast_nonneg _) hηa
  have hiN : (i : ℕ) < #(colouringNorth y η) := by
    rw [card_colouringNorth_eq_card_colouringEast hb hN hη hηa hy, hk]; exact i.isLt
  have hle := componentBotIndex_le_componentTopIndex ha hb hN hη hηa hy hiN
  rw [braidDataOfColouring_snd_eq_toNat a b N y η k i] at hm
  have hmle : componentBotIndex a b N y η (i : ℕ)
      ≤ componentTopIndex a b N y η (i : ℕ) - (m : ℤ) := by omega
  obtain ⟨x, yy, hsum, hx, hyy0, hyyle, hrk, hfr⟩ :=
    exists_pointRank_of_le_componentTopIndex ha hb hN hη hηa hy hiN hmle (by omega)
  refine ⟨x, yy, hsum, by omega, hx, hyy0, hyyle, hrk, ?_⟩
  rw [braidDataOfColouring_fst,
    iterate_nextCrossing_fract_crossingAbscissa ha hb hN hη hηpos y (i : ℕ) hmle]
  exact hfr

namespace Isolates

variable {X Y : ℕ} {ηlo ηhi : ℚ}

/-! ### The moving entry is the strict maximum, not merely a maximum -/

/-- **At a type-`C` drop the moving entry of the mixed final tuple is STRICTLY above every other
one.** `HJO.Mellit.Isolates.entryRank_positionPair_snd_of_eventType_C` records the consequence
`rk = k`, which is a weak statement; the inversion count needs the strict inequality, and the
proof gives it: the other entries sit at `(rk̂(u_i) + ω - ηlo)/D` with `rk̂(u_i) < ηlo`, the moving
one at `(rk̂(P) + ω - ηlo)/D` with `ηlo < rk̂(P)`. -/
theorem lt_positionPair_snd_of_eventType_C (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.C) {k : ℕ}
    (hk : #(colouringEast y ηhi) = k) (j : Fin k)
    (hj : colStep (colouringNorth y ηhi) (j : ℕ) = (X, Y))
    (hwin : ((pointRank a b N (X, Y) : ℤ) : ℚ)
      < ηlo + ((b : ℚ) * ((a : ℚ) * N + 1) * N - 1)) (i : Fin k) (hne : i ≠ j) :
    (positionPair (sweepTheta a b N) (braidDataOfColouring a b N y ηlo k).1
        (braidDataOfColouring a b N y ηhi k).2).2 i
      < (positionPair (sweepTheta a b N) (braidDataOfColouring a b N y ηlo k).1
        (braidDataOfColouring a b N y ηhi k).2).2 j := by
  have hηhi : ((a * N : ℕ) : ℚ) < ηhi := hηlo.trans (hI.ltP.trans hI.Plt)
  have hD := crossDen_pos (a := a) (b := b) (N := N) ha hb hN
  have hkN : #(colouringNorth y ηhi) = k := by
    rw [card_colouringNorth_eq_card_colouringEast hb hN hI.hi hηhi hy]; exact hk
  have hkNlo : #(colouringNorth y ηlo) = k := by
    rw [hI.card_colouringNorth_of_eventType_C ha hN hev]; exact hkN
  rw [hI.positionPair_snd_of_eventType_C_of_ne ha hb hN hηlo hy hev hk j hj i hne,
    hI.positionPair_snd_of_eventType_C_self ha hb hN hηlo hy hev hk j hj hwin,
    div_lt_div_iff_of_pos_right hD]
  have hmem := colStep_mem (S := colouringNorth y ηlo) (show (i : ℕ) < #(colouringNorth y ηlo) by
    rw [hkNlo]; exact i.isLt)
  have hlt : ((pointRank a b N (colStep (colouringNorth y ηlo) (i : ℕ)) : ℤ) : ℚ) < ηlo :=
    (Finset.mem_filter.1 hmem).2.1
  have := hI.ltP
  linarith

/-! ### The rigid shift of a type-`C` drop crosses the puncture at ONE stage only -/

/-- **The `hside` obligation of a type-`C` event, at every stage a move starts from.** The level
drop raises every position by `HJO.Mellit.levelDropShift`, and by
`HJO.Mellit.sameSide_levelDropShift_of_ne` the only lattice point whose normalised rank that shift
can carry across the puncture is `(X, Y + 1)`. That point realises the crossing of index
`X + Y + 1`, which is the **bottom** index of the moving component
(`HJO.Mellit.Isolates.componentBotIndex_of_eventType_C`) — so it is the `α_j - 1`-st stage of the
index `j`, and no stage a move starts from. Away from `j` it is not a crossing of the component at
all, distinct components sharing no index
(`HJO.Mellit.componentTopIndex_lt_componentBotIndex`).

**This is why the sharpened rigid shift is needed and not an optimisation.** At the last stage of
the index `j` the conclusion is FALSE: the mixed final tuple sits above the puncture
(`HJO.Mellit.Isolates.braidStep_positionPair_snd_of_eventType_C` reads a `ỹ` there) and the upper
one below it. -/
theorem sameSide_iterate_of_eventType_C (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.C) {k : ℕ}
    (hk : #(colouringEast y ηhi) = k) (j : Fin k)
    (hj : colStep (colouringNorth y ηhi) (j : ℕ) = (X, Y)) (t : Fin k) (m : ℕ)
    (hm : m < (braidDataOfColouring a b N y ηhi k).2 t - 1) :
    SameSide (sweepTheta a b N) (levelDropShift a b N ηlo ηhi)
      ((nextCrossing (sweepTheta a b N))^[m] ((braidDataOfColouring a b N y ηhi k).1 t)) := by
  have hηhi : ((a * N : ℕ) : ℚ) < ηhi := hηlo.trans (hI.ltP.trans hI.Plt)
  have hlopos : (0 : ℚ) < ηlo := lt_of_le_of_lt (Nat.cast_nonneg _) hηlo
  have hhipos : (0 : ℚ) < ηhi := lt_of_le_of_lt (Nat.cast_nonneg _) hηhi
  have hkN : #(colouringNorth y ηhi) = k := by
    rw [card_colouringNorth_eq_card_colouringEast hb hN hI.hi hηhi hy]; exact hk
  have hjlt : (j : ℕ) < #(colouringNorth y ηhi) := by rw [hkN]; exact j.isLt
  have htlt : (t : ℕ) < #(colouringNorth y ηhi) := by rw [hkN]; exact t.isLt
  obtain ⟨x, yy, hsum, hbot, hx, hyy0, hyyle, hrk, hfr⟩ :=
    exists_pointRank_iterate_nextCrossing_eq_sub ha hb hN hI.hi hηhi hy hk t (le_of_lt hm)
  rw [hfr]
  refine sameSide_levelDropShift_of_ne ha hb hN hI hx.le
    (le_trans (hyyle.trans (ht_le_mul y _)) (by omega)) hyy0 ?_
  intro hQ
  have hx1 : x = X := congrArg Prod.fst hQ
  have hy1 : yy = Y + 1 := congrArg Prod.snd hQ
  have hsum' : (x : ℤ) + (yy : ℤ) = (X : ℤ) + (Y : ℤ) + 1 := by
    rw [hx1, hy1]
    push_cast
    ring
  have hbotj : componentBotIndex a b N y ηhi (j : ℕ) = (X : ℤ) + (Y : ℤ) + 1 :=
    (hI.componentBotIndex_of_eventType_C ha hb hN hlopos hhipos hev hjlt hj).2.1
  have hlej := componentBotIndex_le_componentTopIndex ha hb hN hI.hi hηhi hy hjlt
  have hlet := componentBotIndex_le_componentTopIndex ha hb hN hI.hi hηhi hy htlt
  rw [braidDataOfColouring_snd_eq_toNat a b N y ηhi k t] at hm
  rcases lt_trichotomy (t : ℕ) (j : ℕ) with hlt | heq | hgt
  · have hcmp := componentTopIndex_lt_componentBotIndex ha hb hN hI.hi hηhi hy hjlt hlt
    omega
  · rw [heq] at hsum hm hlet
    omega
  · have hcmp := componentTopIndex_lt_componentBotIndex ha hb hN hI.hi hηhi hy htlt hgt
    omega

/-! ### The `r`-power of the type-`C` residual, evaluated -/

/-- **THE `r`-POWER OF `htrain`, EVALUATED: `2j - (k - 1)`.** The two `HJO.Braid.invFin` counts
of the type-`C` residual differ by exactly `j - (k - 1 - j)`.

The mixed final tuple has the moving entry at the **top**
(`HJO.Mellit.Isolates.lt_positionPair_snd_of_eventType_C`) and the once-moved tuple — which
`HJO.Braid.positionPair_snd_update_succ` identifies with the final tuple of the *raised*
multiplicities — has it at the **bottom**
(`HJO.Mellit.Isolates.entryRank_moveOne_positionPair_snd_of_eventType_C`, read through
`HJO.Braid.forall_ne_lt_of_entryRank_eq_one`). So
`HJO.Braid.tupleInversions_sub_tupleInversions_of_top_bot` applies verbatim: the `k - 1 - j`
inversions above `j` die and the `j` below it are born. -/
theorem invFin_sub_invFin_of_eventType_C (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.C) {k : ℕ}
    (hk : #(colouringEast y ηhi) = k) (j : Fin k)
    (hj : colStep (colouringNorth y ηhi) (j : ℕ) = (X, Y))
    (hwin : ((pointRank a b N (X, Y) : ℤ) : ℚ)
      < ηlo + ((b : ℚ) * ((a : ℚ) * N + 1) * N - 1)) :
    ((invFin (sweepTheta a b N) (braidDataOfColouring a b N y ηlo k).1
          (Function.update (braidDataOfColouring a b N y ηhi k).2 j
            ((braidDataOfColouring a b N y ηhi k).2 j + 1)) : ℤ)
        - (invFin (sweepTheta a b N) (braidDataOfColouring a b N y ηlo k).1
            (braidDataOfColouring a b N y ηhi k).2 : ℤ))
      = ((j : ℕ) : ℤ) - ((k - 1 - (j : ℕ) : ℕ) : ℤ) := by
  have hηhi : ((a * N : ℕ) : ℚ) < ηhi := hηlo.trans (hI.ltP.trans hI.Plt)
  have hkN : #(colouringNorth y ηhi) = k := by
    rw [card_colouringNorth_eq_card_colouringEast hb hN hI.hi hηhi hy]; exact hk
  have hdatahi := isSpecialBraidData_braidDataOfColouring_of_card ha hb hN hI.hi hηhi hy hkN
  rw [invFin, invFin,
    positionPair_snd_update_succ _ _ j (hdatahi.one_le_mult j)]
  exact tupleInversions_sub_tupleInversions_of_top_bot
    (fun i hne => moveOne_of_ne _ _ hne)
    (fun i hne => hI.lt_positionPair_snd_of_eventType_C ha hb hN hηlo hy hev hk j hj hwin i hne)
    (forall_ne_lt_of_entryRank_eq_one _ _
      (hI.entryRank_moveOne_positionPair_snd_of_eventType_C ha hb hN hηlo hy hev hk j hj))

end Isolates

section Value

variable {L : Type*} [Field L] [Algebra ℚ L]

omit [Algebra ℚ L] in
/-- The scalar reconciliation of the type-`C` residual: `r^{2j-(k-1)} · r^{-(k-1)} = q^{-(k-1-j)}`,
`r` being a square root of `q`. -/
theorem zpow_sub_mul_inv_pow (q : L) {r : L} (hq : q ≠ 0) (hr : r * r = q) {k : ℕ} (j : Fin k) :
    r ^ (((j : ℕ) : ℤ) - ((k - 1 - (j : ℕ) : ℕ) : ℤ)) * (r⁻¹ : L) ^ (k - 1)
      = q ^ (-((k - 1 - (j : ℕ) : ℕ) : ℤ)) := by
  have hr0 : r ≠ 0 := ne_zero_of_sq_eq hq hr
  have hjlt := j.isLt
  have hq2 : q ^ (-((k - 1 - (j : ℕ) : ℕ) : ℤ))
      = r ^ (-((k - 1 - (j : ℕ) : ℕ) : ℤ)) * r ^ (-((k - 1 - (j : ℕ) : ℕ) : ℤ)) := by
    rw [← hr, mul_zpow]
  rw [hq2, ← zpow_add₀ hr0, inv_pow, ← zpow_natCast r (k - 1), ← zpow_neg, ← zpow_add₀ hr0]
  congr 1
  omega

/-- **`π_k(T_{1↘k} ỹ_k)` in closed form on `V_k`: `-q^{-(k-1)/2} T_{1↗k}(y_k · )`.** The braid word
collapses by `HJO.Braid.braidTrainDown_one_mul_braidYtilde_self` — the descending train of the
letter cancels the one inside `ỹ_k` — and what is left is exactly the word
`HJO.Sweep.corner_eq_neg_cmAscWord_auxVar_mul` states `Δ^{(k)}` with, times the `r`-power the `k-1`
inverted letters of `T_{1↘k}` carry. -/
theorem coe_braidRepMellit_braidTrainDown_one_mul_braidYtilde (q u : L) {r : L} (hq : q ≠ 0)
    (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) (hr : r * r = q) {k : ℕ} (hk : 1 ≤ k) (x : pieceSub L k) :
    ((braidRepMellit q u hq hq1 hqp hr k (braidTrainDown k 1 k * braidYtilde k k) x
        : pieceSub L k) : Total L)
      = -((r⁻¹ : L) ^ (k - 1) • trainUpEnd q 1 k ((auxVar k : Total L) * (x : Total L))) := by
  rw [braidRepMellit, (representedBy_braidTrainDown_one_mul_braidYtilde hq hr hk).apply]
  simp only [LinearMap.neg_apply, LinearMap.smul_apply, Module.End.mul_apply,
    LinearMap.mulLeft_apply]

/-- `HJO.Mellit.coe_braidRepMellit_braidTrainDown_one_mul_braidYtilde` read at an element of `V_k`
presented as a vector of the total space together with its membership, which is the shape the
type-`C` residual is written in. -/
theorem coe_braidRepMellit_braidTrainDown_one_mul_braidYtilde_mk (q u : L) {r : L} (hq : q ≠ 0)
    (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) (hr : r * r = q) {k : ℕ} (hk : 1 ≤ k) (F : Total L)
    (hF : F ∈ pieceSub L k) :
    ((braidRepMellit q u hq hq1 hqp hr k (braidTrainDown k 1 k * braidYtilde k k) ⟨F, hF⟩
        : pieceSub L k) : Total L)
      = -((r⁻¹ : L) ^ (k - 1) • trainUpEnd q 1 k ((auxVar k : Total L) * F)) :=
  coe_braidRepMellit_braidTrainDown_one_mul_braidYtilde q u hq hq1 hqp hr hk ⟨F, hF⟩

/-- **`Δ^{(k)}` on `V_k` with the ascending word written as a train.**
`HJO.Sweep.corner_eq_neg_cmAscWord_auxVar_mul` at `k = m + 1`, with `HJO.Sweep.cmAscWord q 1 m`
unfolded to `HJO.Sweep.trainUpEnd q 1 k` — the same operator the braid letter produces. -/
theorem corner_eq_neg_trainUpEnd_auxVar_mul {q : L} (hq : q ≠ 0) (hq1 : q ≠ 1) {k : ℕ}
    (hk : 1 ≤ k) {F : Total L} (hF : F ∈ piece L k) :
    corner q k F = -(trainUpEnd q 1 k ((auxVar k : Total L) * F)) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [corner_eq_neg_cmAscWord_auxVar_mul hq hq1 m hF, cmAscWord]

namespace Isolates

variable {X Y : ℕ} {ηlo ηhi : ℚ}

/-- **THE TYPE-`C` RESIDUAL `htrain`, DISCHARGED FROM ONE EQUALITY OF BRAID VALUES.** The letter,
the train, the corner and both scalars are all resolved here; the single hypothesis `hmixed` that
remains carries no braid word, no `HJO.Sweep.corner`, no train and no scalar — it says the braid
value of the **mixed** data (the lower positions with the upper multiplicities) is the braid value
of the **upper** data, which is the rigid-shift invariance of `HJO.Braid.specialBraid` at a type-`C`
drop.

Three computations meet:

* the word — `T_{1↘k} ỹ_k = T_{1↗k} y_k` (`HJO.Braid.braidTrainDown_one_mul_braidYtilde_self`), so
  `π_k` of it is `-q^{-(k-1)/2}T_{1↗k}(y_k·)`
  (`HJO.Mellit.coe_braidRepMellit_braidTrainDown_one_mul_braidYtilde`), and `Δ^{(k)}` is
  `-T_{1↗k}(y_k·)` (`HJO.Mellit.corner_eq_neg_trainUpEnd_auxVar_mul`): **the same operator on both
  sides, signs included**;
* the `r`-power — `HJO.Mellit.Isolates.invFin_sub_invFin_of_eventType_C` evaluates the difference of
  the two `HJO.Braid.invFin` counts as `j - (k-1-j) = 2j - (k-1)`;
* the reconciliation — `r^{2j-(k-1)}·r^{-(k-1)} = q^{-(k-1-j)}`
  (`HJO.Mellit.zpow_sub_mul_inv_pow`), which is `HJO.Mellit.sweepOperator`'s own `q^{-a_{P̂}}`.
  Nothing is left over: had the entry rank, the train or the sign been off by one this would not
  close. -/
theorem braidTrain_eq_corner_of_eventType_C (q u : L) {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1)
    (hqp : q + 1 ≠ 0) (hr : r * r = q) (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.C) {k : ℕ}
    (hk : #(colouringEast y ηhi) = k) (j : Fin k)
    (hj : colStep (colouringNorth y ηhi) (j : ℕ) = (X, Y))
    (hwin : ((pointRank a b N (X, Y) : ℤ) : ℚ)
      < ηlo + ((b : ℚ) * ((a : ℚ) * N + 1) * N - 1))
    (hmixed : braidValueOfData q u hq hq1 hqp hr a b N (braidDataOfColouring a b N y ηlo k).1
          (braidDataOfColouring a b N y ηhi k).2
        = braidValueOfData q u hq hq1 hqp hr a b N (braidDataOfColouring a b N y ηhi k).1
          (braidDataOfColouring a b N y ηhi k).2) :
    r ^ ((invFin (sweepTheta a b N) (braidDataOfColouring a b N y ηlo k).1
            (Function.update (braidDataOfColouring a b N y ηhi k).2 j
              ((braidDataOfColouring a b N y ηhi k).2 j + 1)) : ℤ)
          - (invFin (sweepTheta a b N) (braidDataOfColouring a b N y ηlo k).1
              (braidDataOfColouring a b N y ηhi k).2 : ℤ)) •
        ((braidRepMellit q u hq hq1 hqp hr k (braidTrainDown k 1 k * braidYtilde k k)
            ⟨braidValueOfData q u hq hq1 hqp hr a b N (braidDataOfColouring a b N y ηlo k).1
                (braidDataOfColouring a b N y ηhi k).2,
              braidValueOfData_mem_pieceSub q u hq hq1 hqp hr a b N _ _⟩ : pieceSub L k)
          : Total L)
      = q ^ (-((k - 1 - (j : ℕ) : ℕ) : ℤ)) • corner q k
          (braidValueOfData q u hq hq1 hqp hr a b N (braidDataOfColouring a b N y ηhi k).1
            (braidDataOfColouring a b N y ηhi k).2) := by
  have hk1 : 1 ≤ k := Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt
  rw [hI.invFin_sub_invFin_of_eventType_C ha hb hN hηlo hy hev hk j hj hwin,
    coe_braidRepMellit_braidTrainDown_one_mul_braidYtilde_mk q u hq hq1 hqp hr hk1, hmixed,
    corner_eq_neg_trainUpEnd_auxVar_mul hq hq1 hk1
      (braidValueOfData_mem_pieceSub q u hq hq1 hqp hr a b N _ _),
    smul_neg, smul_neg, smul_smul, zpow_sub_mul_inv_pow q hq hr j]

/-! ### The mixed braid value is the upper braid value -/

/-- **THE RESIDUAL `hmixed`, DISCHARGED: at a type-`C` drop the braid value of the lower positions
with the upper multiplicities is the braid value of the upper data.**

The two data differ by the rigid shift `HJO.Mellit.levelDropShift`
(`HJO.Mellit.Isolates.braidData_fst_eq_add_of_eventType_C`), and
`HJO.Mellit.braidValueOfData_congr_add_of_lt` says a rigid shift is invisible to
`HJO.Braid.specialBraid` and to both inversion counts `HJO.Braid.invIni` and `HJO.Braid.invFin`
provided it crosses the puncture at no stage a move starts from — which is
`HJO.Mellit.Isolates.sameSide_iterate_of_eventType_C`.

The ONE stage it does cross is the last one of the moving index, and no letter reads that stage: it
is where the extra letter of the equal-rank raise sits, and it is precisely the `ỹ` that
`HJO.Mellit.Isolates.braidStep_positionPair_snd_of_eventType_C` evaluates. So this identity and that
one are the two halves of the same bookkeeping, and neither weakens the other. -/
theorem braidValueOfData_mixed_eq_of_eventType_C {L : Type*} [Field L] [Algebra ℚ L] (q u : L)
    {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) (hr : r * r = q) (ha : 0 < a) (hb : 0 < b)
    (hN : 0 < N) (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo)
    {y : Heights a b N} (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.C) {k : ℕ}
    (hk : #(colouringEast y ηhi) = k) (j : Fin k)
    (hj : colStep (colouringNorth y ηhi) (j : ℕ) = (X, Y)) :
    braidValueOfData q u hq hq1 hqp hr a b N (braidDataOfColouring a b N y ηlo k).1
        (braidDataOfColouring a b N y ηhi k).2
      = braidValueOfData q u hq hq1 hqp hr a b N (braidDataOfColouring a b N y ηhi k).1
        (braidDataOfColouring a b N y ηhi k).2 := by
  have hlopos : (0 : ℚ) < ηlo := lt_of_le_of_lt (Nat.cast_nonneg _) hηlo
  have hfst : (braidDataOfColouring a b N y ηlo k).1
      = fun i => (braidDataOfColouring a b N y ηhi k).1 i + levelDropShift a b N ηlo ηhi :=
    funext fun i => hI.braidData_fst_eq_add_of_eventType_C ha hb hN hlopos hev i
      (by rw [hk]; exact i.isLt)
  rw [hfst]
  exact braidValueOfData_congr_add_of_lt q u hq hq1 hqp hr a b N _ _ _
    fun t m hm => hI.sameSide_iterate_of_eventType_C ha hb hN hηlo hy hev hk j hj t m hm

/-- **`htrain` OF
`HJO.Mellit.Isolates.braidValueColouring_eq_sweepOperator_of_eventType_C_of_train`, DISCHARGED**, in
general and with no hypothesis beyond the clause's own and `hwin`:
`HJO.Mellit.Isolates.braidTrain_eq_corner_of_eventType_C` with `hmixed` supplied by
`HJO.Mellit.Isolates.braidValueOfData_mixed_eq_of_eventType_C`. This is the whole remaining content
that `HJO/Shuffle/BraidCDLetterRank.lean` left open. -/
theorem braidTrain_eq_corner_of_eventType_C_of_win (q u : L) {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1)
    (hqp : q + 1 ≠ 0) (hr : r * r = q) (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.C) {k : ℕ}
    (hk : #(colouringEast y ηhi) = k) (j : Fin k)
    (hj : colStep (colouringNorth y ηhi) (j : ℕ) = (X, Y))
    (hwin : ((pointRank a b N (X, Y) : ℤ) : ℚ)
      < ηlo + ((b : ℚ) * ((a : ℚ) * N + 1) * N - 1)) :
    r ^ ((invFin (sweepTheta a b N) (braidDataOfColouring a b N y ηlo k).1
            (Function.update (braidDataOfColouring a b N y ηhi k).2 j
              ((braidDataOfColouring a b N y ηhi k).2 j + 1)) : ℤ)
          - (invFin (sweepTheta a b N) (braidDataOfColouring a b N y ηlo k).1
              (braidDataOfColouring a b N y ηhi k).2 : ℤ)) •
        ((braidRepMellit q u hq hq1 hqp hr k (braidTrainDown k 1 k * braidYtilde k k)
            ⟨braidValueOfData q u hq hq1 hqp hr a b N (braidDataOfColouring a b N y ηlo k).1
                (braidDataOfColouring a b N y ηhi k).2,
              braidValueOfData_mem_pieceSub q u hq hq1 hqp hr a b N _ _⟩ : pieceSub L k)
          : Total L)
      = q ^ (-((k - 1 - (j : ℕ) : ℕ) : ℤ)) • corner q k
          (braidValueOfData q u hq hq1 hqp hr a b N (braidDataOfColouring a b N y ηhi k).1
            (braidDataOfColouring a b N y ηhi k).2) :=
  hI.braidTrain_eq_corner_of_eventType_C q u hq hq1 hqp hr ha hb hN hηlo hy hev hk j hj hwin
    (hI.braidValueOfData_mixed_eq_of_eventType_C q u hq hq1 hqp hr ha hb hN hηlo hy hev hk j hj)

/-! ### The type-`C` clause -/

/-- **THE TYPE-`C` CLAUSE OF `HJO.Mellit.braidValueColouring_sweepRecursionsFloor`, with no
hypothesis about the braid.** Every hypothesis is about the event — the two levels isolate the
point, the path is above the diagonal, the event type is `C` — together with `hwin`, the window
bound inherited from `HJO/Shuffle/BraidCDLetterRank.lean` and discharged below from `a < b` or from
consecutive levels. The index `j` of the moving component is constructed rather than assumed
(`HJO.Mellit.Isolates.mem_colouringNorth_hi_of_eventType_C` and `HJO.Mellit.exists_colStep`).

`htrain` of `HJO.Mellit.Isolates.braidValueColouring_eq_sweepOperator_of_eventType_C_of_train` is
supplied by `HJO.Mellit.Isolates.braidTrain_eq_corner_of_eventType_C` and
`HJO.Mellit.Isolates.braidValueOfData_mixed_eq_of_eventType_C`.

**This does not prove `HJO.Mellit.braidValueColouring_sweepRecursionsFloor`**, which has four
clauses and six recursions;
with the type-`A` clause
(`HJO.Mellit.Isolates.braidValueColouring_eq_sweepOperator_of_eventType_A_uncond`) this closes two
of the four, and the type-`D`, origin and unswept clauses are untouched. -/
theorem braidValueColouring_eq_sweepOperator_of_eventType_C_of_win {L : Type*} [Field L]
    [Algebra ℚ L] (q u : L) {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) (hr : r * r = q)
    (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) (hI : Isolates a b N X Y ηlo ηhi)
    (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N} (hy : IsAboveDiagonal y)
    (hev : eventType y (X, Y) = EventType.C)
    (hwin : ((pointRank a b N (X, Y) : ℤ) : ℚ)
      < ηlo + ((b : ℚ) * ((a : ℚ) * N + 1) * N - 1)) :
    braidValueColouring q u hq hq1 hqp hr a b N ηlo (colouring y ηlo)
      = sweepOperator q u y (X, Y)
          (braidValueColouring q u hq hq1 hqp hr a b N ηhi (colouring y ηhi)) := by
  have hηhi : ((a * N : ℕ) : ℚ) < ηhi := hηlo.trans (hI.ltP.trans hI.Plt)
  have hkN : #(colouringNorth y ηhi) = #(colouringEast y ηhi) :=
    card_colouringNorth_eq_card_colouringEast hb hN hI.hi hηhi hy
  obtain ⟨i, hi, hie⟩ := exists_colStep (hI.mem_colouringNorth_hi_of_eventType_C ha hN hev)
  have hilt : i < #(colouringEast y ηhi) := by rw [← hkN]; exact hi
  exact hI.braidValueColouring_eq_sweepOperator_of_eventType_C_of_train q u hq hq1 hqp hr ha hb hN
    hηlo hy hev rfl (⟨i, hilt⟩ : Fin #(colouringEast y ηhi)) hie hwin
    (hI.braidTrain_eq_corner_of_eventType_C q u hq hq1 hqp hr ha hb hN hηlo hy hev rfl
      (⟨i, hilt⟩ : Fin #(colouringEast y ηhi)) hie hwin
      (hI.braidValueOfData_mixed_eq_of_eventType_C q u hq hq1 hqp hr ha hb hN hηlo hy hev rfl
        (⟨i, hilt⟩ : Fin #(colouringEast y ηhi)) hie))

/-- **The type-`C` clause at `a < b`**, the range `HJO.Mellit.shuffle_of_lhs_and_induction`
quantifies over: `hwin` comes from `HJO.Mellit.Isolates.pointRank_lt_add_of_eventType_C_of_lt`. -/
theorem braidValueColouring_eq_sweepOperator_of_eventType_C_of_lt {L : Type*} [Field L]
    [Algebra ℚ L] (q u : L) {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) (hr : r * r = q)
    (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) (hab : a < b) (hI : Isolates a b N X Y ηlo ηhi)
    (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N} (hy : IsAboveDiagonal y)
    (hev : eventType y (X, Y) = EventType.C) :
    braidValueColouring q u hq hq1 hqp hr a b N ηlo (colouring y ηlo)
      = sweepOperator q u y (X, Y)
          (braidValueColouring q u hq hq1 hqp hr a b N ηhi (colouring y ηhi)) :=
  hI.braidValueColouring_eq_sweepOperator_of_eventType_C_of_win q u hq hq1 hqp hr ha hb hN hηlo hy
    hev (hI.pointRank_lt_add_of_eventType_C_of_lt ha hN hab hev)

/-- **The type-`C` clause at consecutive levels**, with no relation between `a` and `b` at all:
`hwin` comes from `HJO.Mellit.Isolates.pointRank_lt_add_of_eventType_C_of_succ`. -/
theorem braidValueColouring_eq_sweepOperator_of_eventType_C_of_succ {L : Type*} [Field L]
    [Algebra ℚ L] (q u : L) {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) (hr : r * r = q)
    (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) (hI : Isolates a b N X Y ηlo ηhi)
    (hstep : ηhi = ηlo + 1) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.C) :
    braidValueColouring q u hq hq1 hqp hr a b N ηlo (colouring y ηlo)
      = sweepOperator q u y (X, Y)
          (braidValueColouring q u hq hq1 hqp hr a b N ηhi (colouring y ηhi)) :=
  hI.braidValueColouring_eq_sweepOperator_of_eventType_C_of_win q u hq hq1 hqp hr ha hb hN hηlo hy
    hev (hI.pointRank_lt_add_of_eventType_C_of_succ ha hb hN hstep)

end Isolates

end Value

/-! ### Consistency check: the decided witness through the general theorems

The one *computation* proper here is the change in the inversion count, and a sign or an off-by-one
in it would be invisible in the final statement — it would simply move the `q`-power. So it is
re-derived at the decided `a = 2`, `b = 3`, `N = 1` witness of
`HJO/Shuffle/BraidCDIndicesWitness.lean` and checked against the value computed by hand from the two
positions `13/28` and `9/28`, with the general theorem unused on the decided side and the ad-hoc
computation unused on the general side. The `rfl` between the two proof terms typechecks only if the
two statements are literally the same `Prop`.

The `z`-count is a second, free check: `HJO.Mellit.zCount_cdPathC_lo` computes the `z`-count of the
lower type-`C` braid as `0`, and the letter this file evaluates is
`T_{1↘2} ỹ_2` — a `ỹ`, contributing no `z`. Had the letter come out a `z` the two would disagree. -/

section Witness

open Braid Finset ParkingFunctions Paths Sweep

/-- The inversion count of a rank-`2` tuple whose second entry is below its first is `1`: the one
pair `(0, 1)` is inverted. Computed from `HJO.Braid.tupleInversions_eq_card_lt` alone. -/
private theorem tupleInversions_two_of_lt {w : Fin 2 → ℚ} (h : w 1 < w 0) :
    tupleInversions w = 1 := by
  rw [tupleInversions_eq_card_lt]
  refine Finset.card_eq_one.2 ⟨((0 : Fin 2), (1 : Fin 2)), Finset.eq_singleton_iff_unique_mem.2
    ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, by decide, h⟩, fun p hp => ?_⟩⟩
  obtain ⟨-, hlt, -⟩ := Finset.mem_filter.1 hp
  have h1 := p.1.isLt
  have h2 := p.2.isLt
  have hlt' : (p.1 : ℕ) < (p.2 : ℕ) := hlt
  refine Prod.ext (Fin.val_injective ?_) (Fin.val_injective ?_)
  · change (p.1 : ℕ) = 0
    omega
  · change (p.2 : ℕ) = 1
    omega

/-- The inversion count of a rank-`2` tuple whose first entry is weakly below its second is `0`. -/
private theorem tupleInversions_two_of_le {w : Fin 2 → ℚ} (h : w 0 ≤ w 1) :
    tupleInversions w = 0 := by
  rw [tupleInversions_eq_card_lt, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro p hp
  obtain ⟨-, hlt, hw⟩ := Finset.mem_filter.1 hp
  have h1 := p.1.isLt
  have h2 := p.2.isLt
  have hlt' : (p.1 : ℕ) < (p.2 : ℕ) := hlt
  rw [show p.1 = (0 : Fin 2) from Fin.val_injective (show (p.1 : ℕ) = 0 by omega),
    show p.2 = (1 : Fin 2) from Fin.val_injective (show (p.2 : ℕ) = 1 by omega)] at hw
  exact absurd hw (not_lt.2 h)

/-- **The `r`-power of the type-`C` residual at the decided witness, computed by hand.** Every upper
multiplicity is `1`, so the mixed final tuple is the lower initial tuple `(13/28, 9/28)`, whose one
pair is inverted; raising the multiplicity at `0` moves that entry to
`13/28 - θ = 13/28 - 12/28 = 1/28`, below `9/28`, and the inversion is destroyed. So the difference
is `0 - 1 = -1`. -/
theorem invFin_sub_invFin_cdPathC_decided :
    ((invFin (sweepTheta 2 3 1) (braidDataOfColouring 2 3 1 cdPathC cdLoC 2).1
          (Function.update (braidDataOfColouring 2 3 1 cdPathC cdHiC 2).2 0
            ((braidDataOfColouring 2 3 1 cdPathC cdHiC 2).2 0 + 1)) : ℤ)
        - (invFin (sweepTheta 2 3 1) (braidDataOfColouring 2 3 1 cdPathC cdLoC 2).1
            (braidDataOfColouring 2 3 1 cdPathC cdHiC 2).2 : ℤ))
      = -1 := by
  have hfin : (positionPair (sweepTheta 2 3 1) (braidDataOfColouring 2 3 1 cdPathC cdLoC 2).1
      (braidDataOfColouring 2 3 1 cdPathC cdHiC 2).2).2
      = (braidDataOfColouring 2 3 1 cdPathC cdLoC 2).1 :=
    funext fun t => positionPair_snd_of_mult_eq_one (braidData_cdPathC_hi_snd_eq_one t)
  have h1 : invFin (sweepTheta 2 3 1) (braidDataOfColouring 2 3 1 cdPathC cdLoC 2).1
      (braidDataOfColouring 2 3 1 cdPathC cdHiC 2).2 = 1 := by
    rw [invFin, hfin]
    refine tupleInversions_two_of_lt ?_
    rw [braidData_cdPathC_lo_fst_zero, braidData_cdPathC_lo_fst_one]
    norm_num
  have h2 : invFin (sweepTheta 2 3 1) (braidDataOfColouring 2 3 1 cdPathC cdLoC 2).1
      (Function.update (braidDataOfColouring 2 3 1 cdPathC cdHiC 2).2 0
        ((braidDataOfColouring 2 3 1 cdPathC cdHiC 2).2 0 + 1)) = 0 := by
    rw [invFin, positionPair_snd_update_succ _ _ 0
      (by rw [braidData_cdPathC_hi_snd_eq_one]), hfin]
    refine tupleInversions_two_of_le ?_
    rw [moveOne_self, moveOne_of_ne _ _ (by decide), braidData_cdPathC_lo_fst_zero,
      braidData_cdPathC_lo_fst_one, sweepTheta_cd, nextCrossing]
    norm_num
  rw [h1, h2]
  norm_num

/-- **The same through the general inversion formula.**
`HJO.Mellit.Isolates.invFin_sub_invFin_of_eventType_C` gives
`j - (k - 1 - j) = 0 - (2 - 1 - 0) = -1`, with the positions never mentioned. -/
theorem invFin_sub_invFin_cdPathC_via_general :
    ((invFin (sweepTheta 2 3 1) (braidDataOfColouring 2 3 1 cdPathC cdLoC 2).1
          (Function.update (braidDataOfColouring 2 3 1 cdPathC cdHiC 2).2 0
            ((braidDataOfColouring 2 3 1 cdPathC cdHiC 2).2 0 + 1)) : ℤ)
        - (invFin (sweepTheta 2 3 1) (braidDataOfColouring 2 3 1 cdPathC cdLoC 2).1
            (braidDataOfColouring 2 3 1 cdPathC cdHiC 2).2 : ℤ))
      = -1 := by
  rw [isolates_cdPathC.invFin_sub_invFin_of_eventType_C (by norm_num) (by norm_num) (by norm_num)
      lt_cdLoC isAboveDiagonal_cdPathC eventType_cdPathC card_colouringEast_cdPathC_hi 0
      colStep_colouringNorth_cdPathC_hi_zero
      (isolates_cdPathC.pointRank_lt_add_of_eventType_C_of_lt (by norm_num) (by norm_num)
        (by norm_num) eventType_cdPathC)]
  norm_num

/-- The two readings are the same statement, so the general inversion formula gives the decided
value. -/
example : invFin_sub_invFin_cdPathC_decided = invFin_sub_invFin_cdPathC_via_general := rfl

/-- **The type-`C` clause at the decided witness, through the unconditional theorem.** The
counterpart of `HJO.Mellit.gap_typeA_uncond` for type `C`: every hypothesis is discharged by
`decide` or `norm_num` on the witness. -/
theorem sweep_typeC_cdPathC {L : Type*} [Field L] [Algebra ℚ L] (q u : L) {r : L} (hq : q ≠ 0)
    (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) (hr : r * r = q) :
    braidValueColouring q u hq hq1 hqp hr 2 3 1 cdLoC (colouring cdPathC cdLoC)
      = sweepOperator q u cdPathC (0, 1)
          (braidValueColouring q u hq hq1 hqp hr 2 3 1 cdHiC (colouring cdPathC cdHiC)) :=
  isolates_cdPathC.braidValueColouring_eq_sweepOperator_of_eventType_C_of_lt q u hq hq1 hqp hr
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) lt_cdLoC isAboveDiagonal_cdPathC
    eventType_cdPathC

/-- The same through the *other* discharge of the window hypothesis: the witness's two levels are
consecutive, so no relation between `a` and `b` is used. -/
theorem sweep_typeC_cdPathC_of_succ {L : Type*} [Field L] [Algebra ℚ L] (q u : L) {r : L}
    (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) (hr : r * r = q) :
    braidValueColouring q u hq hq1 hqp hr 2 3 1 cdLoC (colouring cdPathC cdLoC)
      = sweepOperator q u cdPathC (0, 1)
          (braidValueColouring q u hq hq1 hqp hr 2 3 1 cdHiC (colouring cdPathC cdHiC)) :=
  isolates_cdPathC.braidValueColouring_eq_sweepOperator_of_eventType_C_of_succ q u hq hq1 hqp hr
    (by norm_num) (by norm_num) (by norm_num) cdLoC_lt_cdHiC lt_cdLoC isAboveDiagonal_cdPathC
    eventType_cdPathC

/-- The two discharges give the same statement. -/
example {L : Type*} [Field L] [Algebra ℚ L] (q u : L) {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1)
    (hqp : q + 1 ≠ 0) (hr : r * r = q) :
    sweep_typeC_cdPathC q u hq hq1 hqp hr (r := r) = sweep_typeC_cdPathC_of_succ q u hq hq1 hqp hr
      (r := r) := rfl

end Witness

end HJO.Mellit

end
