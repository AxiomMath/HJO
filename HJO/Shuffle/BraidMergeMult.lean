/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidTypeBMerge
public import HJO.Shuffle.BraidCDLetterResidual
public meta import HJO.Attr

/-!
# Merging two adjacent multiplicities

Raising the multiplicity `α_j` of a special-braid datum by `m` multiplies its special braid by an
explicit `m`-letter word at the index `j`. Merging two adjacent entries `j`, `j + 1` of `β` with a
`+1` is such a raise of the data with `j` deleted, by `β_j + 1`. At a type-`B` event this expresses
the lower braid value through the upper one with the index `j` deleted.

## Main results

* `HJO.Braid.specialBraid_update_add_left`: the special braid of a multiplicity raised by `m`.
* `HJO.Braid.specialBraid_merge`: the special braid of two merged adjacent entries.
* `HJO.Braid.length_specialMoveList_merge`: merging adds exactly two moves.
* `HJO.Mellit.braidValueOfData_merge`: the braid value of two merged adjacent entries.
* `HJO.Mellit.Isolates.braidValueOfData_lo_eq_letters_of_eventType_B`: the lower braid value at a
  type-`B` event as a letter word applied to the upper data with `j` deleted.
* `HJO.Mellit.braidValueColouring_sweepRecursionBEFloor_of_letters`: the floored rule `BE`, given
  the letter identity at every bracketed point.
-/

@[expose] public section

open Finset

namespace HJO.Braid

variable {k : ℕ}

/-! ### The move multiset of a multiplicity raised by `m` -/

/-- **Raising `α_j` by `m` adds `m` copies of `j` to the move sequence.** The iterate of
`HJO.Braid.specialMoveList_update_succ_perm`; `1 ≤ α_j` is needed for the same reason, the
truncated subtraction of `HJO.Braid.specialMoveList` being honest only there. -/
theorem specialMoveList_update_add_perm (α : Fin k → ℕ) (j : Fin k) (hα : 1 ≤ α j) (m : ℕ) :
    (specialMoveList (Function.update α j (α j + m))).Perm
      (List.replicate m j ++ specialMoveList α) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hαj : Function.update α j (α j + m) j = α j + m := by simp
    have hup : Function.update (Function.update α j (α j + m)) j
          (Function.update α j (α j + m) j + 1)
        = Function.update α j (α j + (m + 1)) := by
      rw [hαj, Function.update_idem]
      congr 1
    have h1 := specialMoveList_update_succ_perm (Function.update α j (α j + m)) j
      (by rw [hαj]; omega)
    rw [hup] at h1
    refine h1.trans ?_
    rw [List.replicate_succ, List.cons_append]
    exact ih.cons j

/-- The same multiset with the `m` extra copies of `j` written at the **end** of the sequence, the
reading in which the extra moves are performed *first*. -/
theorem specialMoveList_update_add_perm_append (α : Fin k → ℕ) (j : Fin k) (hα : 1 ≤ α j) (m : ℕ) :
    (specialMoveList (Function.update α j (α j + m))).Perm
      (specialMoveList α ++ List.replicate m j) :=
  (specialMoveList_update_add_perm α j hα m).trans List.perm_append_comm

/-- **The number of moves grows by exactly `m`.** -/
theorem length_specialMoveList_update_add (α : Fin k → ℕ) (j : Fin k) (hα : 1 ≤ α j) (m : ℕ) :
    (specialMoveList (Function.update α j (α j + m))).length
      = m + (specialMoveList α).length := by
  rw [(specialMoveList_update_add_perm α j hα m).length_eq, List.length_append,
    List.length_replicate]

/-- **Deleting the index `j` removes exactly `α_j - 1` moves.** -/
theorem length_specialMoveList_succAbove (β : Fin (k + 1) → ℕ) (j : Fin (k + 1)) :
    (specialMoveList fun i => β (j.succAbove i)).length + (β j - 1)
      = (specialMoveList β).length := by
  rw [length_specialMoveList, length_specialMoveList,
    Fin.sum_univ_succAbove (fun i => β i - 1) j, add_comm]

/-! ### The two decompositions of the merged special braid -/

/-- **THE MERGE IDENTITY IN THE BRAID MONOID, with the extra letters on the left.** Raising the
multiplicity of the single index `j` by `m` multiplies `B_{s,v,α}` on the left by the
`m`-letter word of `HJO.Braid.braidWord` at the index `j`, read at the **final** position tuple
`v^fin` of `HJO.Braid.positionPair` for the *unraised* `α`.

At `m = 1` this is `HJO.Braid.specialBraid_update_succ_left`. -/
theorem specialBraid_update_add_left {s θ : ℚ} {v : Fin k → ℚ} {α : Fin k → ℕ} (j : Fin k)
    (hα : 1 ≤ α j) (m : ℕ)
    (hdata : IsSpecialBraidData s θ k v (Function.update α j (α j + m))) :
    specialBraid θ v (Function.update α j (α j + m))
      = braidWord θ (positionPair θ v α).2 (List.replicate m j) * specialBraid θ v α := by
  rw [specialBraid,
    braidWord_perm_of_isSpecialBraidData hdata (fun t => (count_specialMoveList _ t).le)
      (specialMoveList_update_add_perm α j hα m),
    braidWord_append, moveTuple_specialMoveList, specialBraid]

/-- **The merge identity with the extra letters on the right**: the `m` added moves performed
*first* in time, so their word stands rightmost and is read at the initial tuple `v` itself, the
rest being the special braid of the `m`-times-moved tuple at the unraised multiplicities.

At `m = 1` this is `HJO.Braid.specialBraid_update_succ_right`. -/
theorem specialBraid_update_add_right {s θ : ℚ} {v : Fin k → ℚ} {α : Fin k → ℕ} (j : Fin k)
    (hα : 1 ≤ α j) (m : ℕ)
    (hdata : IsSpecialBraidData s θ k v (Function.update α j (α j + m))) :
    specialBraid θ v (Function.update α j (α j + m))
      = specialBraid θ (moveTuple θ v (List.replicate m j)) α
        * braidWord θ v (List.replicate m j) := by
  rw [specialBraid,
    braidWord_perm_of_isSpecialBraidData hdata (fun t => (count_specialMoveList _ t).le)
      (specialMoveList_update_add_perm_append α j hα m),
    braidWord_append, specialBraid]

/-! ### The merge of two adjacent entries -/

/-- `j.succAbove` sends the index `i₀` sitting at `j` to `j + 1`: the merged component of a
type-`B` level rise carries the position of the **upper** component `j + 1`. -/
theorem succAbove_eq_of_val_eq (j j' : Fin (k + 1)) (i₀ : Fin k) (hj' : (j' : ℕ) = (j : ℕ) + 1)
    (hi₀ : (i₀ : ℕ) = (j : ℕ)) : j.succAbove i₀ = j' := by
  refine Fin.ext ?_
  rw [Fin.succAbove_of_le_castSucc _ _
      (show j ≤ i₀.castSucc from by rw [Fin.le_def, Fin.val_castSucc, hi₀]),
    Fin.val_succ, hi₀, hj']

/-- **Merging the two adjacent entries `j`, `j + 1` of `β` with a `+1` is raising the surviving
multiplicity by `β_j + 1`.** The surviving index is `i₀`, sitting at `j` in the smaller range, and
`HJO.Braid.succAbove_eq_of_val_eq` identifies its undeleted multiplicity as `β_{j+1}`; so
`β_j + β_{j+1} + 1 = β_{j+1} + (β_j + 1)`, and the merge is an instance of the `+m` raise. -/
theorem update_succAbove_merge_eq (β : Fin (k + 1) → ℕ) (j j' : Fin (k + 1)) (i₀ : Fin k)
    (hj' : (j' : ℕ) = (j : ℕ) + 1) (hi₀ : (i₀ : ℕ) = (j : ℕ)) :
    Function.update (fun i => β (j.succAbove i)) i₀ (β j + β j' + 1)
      = Function.update (fun i => β (j.succAbove i)) i₀ (β (j.succAbove i₀) + (β j + 1)) := by
  rw [succAbove_eq_of_val_eq j j' i₀ hj' hi₀]
  congr 1
  omega

/-- **THE `+2` LETTER GAP OF A MERGE, from the decomposition alone.** Deleting the index `j` from
`β` removes `β_j - 1` moves (`HJO.Braid.length_specialMoveList_succAbove`) and the merge then puts
`β_j + 1` back (`HJO.Braid.length_specialMoveList_update_add`), so the merged sequence carries
exactly `2` moves more than `β`'s.

This is the arithmetic a `+1` in place of the `+2` fails, and it is the arithmetic the type-`A`
reading fails: there the two insertion indices coincide, nothing is deleted, and the gap is `0`. -/
theorem length_specialMoveList_merge (β : Fin (k + 1) → ℕ) (j j' : Fin (k + 1)) (i₀ : Fin k)
    (hj' : (j' : ℕ) = (j : ℕ) + 1) (hi₀ : (i₀ : ℕ) = (j : ℕ)) (hβj : 1 ≤ β j) (hβj' : 1 ≤ β j') :
    (specialMoveList (Function.update (fun i => β (j.succAbove i)) i₀ (β j + β j' + 1))).length
      = (specialMoveList β).length + 2 := by
  have hval : β (j.succAbove i₀) = β j' := by rw [succAbove_eq_of_val_eq j j' i₀ hj' hi₀]
  have hraise := length_specialMoveList_update_add (fun i => β (j.succAbove i)) i₀
    (by rw [hval]; omega) (β j + 1)
  have hdel := length_specialMoveList_succAbove β j
  rw [update_succAbove_merge_eq β j j' i₀ hj' hi₀, hraise]
  omega

/-- **THE MERGE IDENTITY IN THE BRAID MONOID, IN THE TYPE-`B` SHAPE.** The special braid of the
merged data is the special braid of the data with the index `j` deleted, multiplied on the left by
an explicit word of `β_j + 1` letters of `HJO.Braid.braidStep`, all at the single index `i₀` and
read at the final position tuple of the deleted data.

The two extra letters of `HJO.Mellit.Isolates.length_specialMoveList_of_eventType_B` are the two by
which `β_j + 1` exceeds the `β_j - 1` letters the deletion removed. -/
theorem specialBraid_merge {s θ : ℚ} {v : Fin k → ℚ} (β : Fin (k + 1) → ℕ) (j j' : Fin (k + 1))
    (i₀ : Fin k) (hj' : (j' : ℕ) = (j : ℕ) + 1) (hi₀ : (i₀ : ℕ) = (j : ℕ)) (hβj' : 1 ≤ β j')
    (hdata : IsSpecialBraidData s θ k v
      (Function.update (fun i => β (j.succAbove i)) i₀ (β j + β j' + 1))) :
    specialBraid θ v (Function.update (fun i => β (j.succAbove i)) i₀ (β j + β j' + 1))
      = braidWord θ (positionPair θ v fun i => β (j.succAbove i)).2
            (List.replicate (β j + 1) i₀)
          * specialBraid θ v fun i => β (j.succAbove i) := by
  have hval : β (j.succAbove i₀) = β j' := by rw [succAbove_eq_of_val_eq j j' i₀ hj' hi₀]
  rw [update_succAbove_merge_eq β j j' i₀ hj' hi₀] at hdata ⊢
  exact specialBraid_update_add_left i₀ (by rw [hval]; omega) (β j + 1) hdata

end HJO.Braid

namespace HJO.Mellit

open ParkingFunctions Paths Sweep Braid

variable {L : Type*} [Field L] [Algebra ℚ L]

/-! ### The merge identity at the level of the braid value -/

/-- **THE MERGE IDENTITY AT THE LEVEL OF THE SPECIAL-BRAID DATA.** Raising the multiplicity of the
single index `j` by `m` applies to the braid value `π_k` of an explicit `m`-letter word of
`HJO.Braid.braidWord` — read at the final position tuple of `HJO.Braid.positionPair` for
the *unraised* `α` — and multiplies by the `r`-power the two `HJO.Braid.invFin` counts differ by;
`HJO.Braid.invIni` is the same on both sides, reading only `v`.

At `m = 1` this is `HJO.Mellit.braidValueOfData_update_succ_left`. -/
theorem braidValueOfData_update_add_left (q u : L) {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1)
    (hqp : q + 1 ≠ 0) (hr : r * r = q) (a b N : ℕ) {k : ℕ} {v : Fin k → ℚ} {α : Fin k → ℕ}
    (j : Fin k) (hα : 1 ≤ α j) (m : ℕ)
    (hdata : IsSpecialBraidData (sweepSlope a b N) (sweepTheta a b N) k v
      (Function.update α j (α j + m))) :
    braidValueOfData q u hq hq1 hqp hr a b N v (Function.update α j (α j + m))
      = r ^ ((invFin (sweepTheta a b N) v (Function.update α j (α j + m)) : ℤ)
            - (invFin (sweepTheta a b N) v α : ℤ)) •
          ((braidRepMellit q u hq hq1 hqp hr k
              (braidWord (sweepTheta a b N) (positionPair (sweepTheta a b N) v α).2
                (List.replicate m j))
              ⟨braidValueOfData q u hq hq1 hqp hr a b N v α,
                braidValueOfData_mem_pieceSub q u hq hq1 hqp hr a b N v α⟩ : pieceSub L k)
            : Total L) := by
  have hr0 : r ≠ 0 := ne_zero_of_sq_eq hq hr
  have hval : (⟨braidValueOfData q u hq hq1 hqp hr a b N v α,
        braidValueOfData_mem_pieceSub q u hq hq1 hqp hr a b N v α⟩ : pieceSub L k)
      = (r ^ ((invFin (sweepTheta a b N) v α : ℤ) - (invIni (sweepTheta a b N) v α : ℤ)))
          • braidRepMellit q u hq hq1 hqp hr k (specialBraid (sweepTheta a b N) v α)
              (dplusIterPiece q k) := Subtype.ext rfl
  rw [hval, map_smul, Submodule.coe_smul, smul_smul, ← zpow_add₀ hr0, braidValueOfData,
    specialBraid_update_add_left j hα m hdata, map_mul, Module.End.mul_apply,
    invIni_eq_tupleInversions, invIni_eq_tupleInversions]
  congr 2
  ring

/-- **The merge identity at the level of the braid value, with the letters on the vacuum.** The `m`
added moves performed *first* in time: their word acts on the vacuum vector of
`HJO.Mellit.braidValueOfData` and the rest of the braid is the special braid of the
`m`-times-moved tuple.

At `m = 1` this is `HJO.Mellit.braidValueOfData_update_succ_right`. -/
theorem braidValueOfData_update_add_right (q u : L) {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1)
    (hqp : q + 1 ≠ 0) (hr : r * r = q) (a b N : ℕ) {k : ℕ} {v : Fin k → ℚ} {α : Fin k → ℕ}
    (j : Fin k) (hα : 1 ≤ α j) (m : ℕ)
    (hdata : IsSpecialBraidData (sweepSlope a b N) (sweepTheta a b N) k v
      (Function.update α j (α j + m))) :
    braidValueOfData q u hq hq1 hqp hr a b N v (Function.update α j (α j + m))
      = r ^ ((invFin (sweepTheta a b N) v (Function.update α j (α j + m)) : ℤ)
            - (invIni (sweepTheta a b N) v α : ℤ)) •
          ((braidRepMellit q u hq hq1 hqp hr k
              (specialBraid (sweepTheta a b N)
                (moveTuple (sweepTheta a b N) v (List.replicate m j)) α)
              (braidRepMellit q u hq hq1 hqp hr k
                (braidWord (sweepTheta a b N) v (List.replicate m j))
                (dplusIterPiece q k)) : pieceSub L k)
            : Total L) := by
  rw [braidValueOfData, specialBraid_update_add_right j hα m hdata, map_mul,
    Module.End.mul_apply, invIni_eq_tupleInversions, invIni_eq_tupleInversions]

/-! ### The merge identity in the type-`B` shape -/

/-- **THE MERGE IDENTITY AT THE LEVEL OF THE SPECIAL-BRAID DATA, IN THE TYPE-`B` SHAPE.** The braid
value of the data whose multiplicities are `β` with the two adjacent entries `j`, `j + 1` merged
with a `+1` is the braid value of the data with `j` deleted, acted on by `π_k` of an explicit
word of `β_j + 1` letters of `HJO.Braid.braidStep` at the single index `i₀`, and scaled by the
`r`-power the two `HJO.Braid.invFin` counts differ by.

This is the merge counterpart of `HJO.Mellit.braidValueOfData_succAbove_eq_dplus`, which is the
*insertion* counterpart: there the inserted entry has multiplicity `1` and the operator is `d^♭_+`;
here two entries are merged and the operator is `π_k` of a word whose length the merge names. -/
theorem braidValueOfData_merge (q u : L) {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0)
    (hr : r * r = q) (a b N : ℕ) {k : ℕ} (v : Fin k → ℚ) (β : Fin (k + 1) → ℕ)
    (j j' : Fin (k + 1)) (i₀ : Fin k) (hj' : (j' : ℕ) = (j : ℕ) + 1) (hi₀ : (i₀ : ℕ) = (j : ℕ))
    (hβj' : 1 ≤ β j')
    (hdata : IsSpecialBraidData (sweepSlope a b N) (sweepTheta a b N) k v
      (Function.update (fun i => β (j.succAbove i)) i₀ (β j + β j' + 1))) :
    braidValueOfData q u hq hq1 hqp hr a b N v
        (Function.update (fun i => β (j.succAbove i)) i₀ (β j + β j' + 1))
      = r ^ ((invFin (sweepTheta a b N) v
              (Function.update (fun i => β (j.succAbove i)) i₀ (β j + β j' + 1)) : ℤ)
            - (invFin (sweepTheta a b N) v (fun i => β (j.succAbove i)) : ℤ)) •
          ((braidRepMellit q u hq hq1 hqp hr k
              (braidWord (sweepTheta a b N)
                (positionPair (sweepTheta a b N) v fun i => β (j.succAbove i)).2
                (List.replicate (β j + 1) i₀))
              ⟨braidValueOfData q u hq hq1 hqp hr a b N v fun i => β (j.succAbove i),
                braidValueOfData_mem_pieceSub q u hq hq1 hqp hr a b N v
                  fun i => β (j.succAbove i)⟩ : pieceSub L k)
            : Total L) := by
  have hval : β (j.succAbove i₀) = β j' := by rw [succAbove_eq_of_val_eq j j' i₀ hj' hi₀]
  rw [update_succAbove_merge_eq β j j' i₀ hj' hi₀] at hdata ⊢
  exact braidValueOfData_update_add_left q u hq hq1 hqp hr a b N i₀ (by rw [hval]; omega)
    (β j + 1) hdata

namespace Isolates

variable {a b N X Y : ℕ} {ηlo ηhi : ℚ}

/-! ### The type-`B` letter gap, re-derived from the merge -/

/-- **The `+2` letter gap of a type-`B` level rise, re-derived from the merge decomposition.**
`HJO.Mellit.Isolates.length_specialMoveList_of_bePair` proves the same equation from the total
crossing count and the width; this route reads it off
`HJO.Braid.length_specialMoveList_merge` instead — the deletion of the index `j` removes
`α_hi(j) - 1` moves and the merge puts `α_hi(j) + 1` back. The two routes state the same equation,
which the `rfl` below checks. -/
theorem length_specialMoveList_of_bePair_of_merge (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo)
    {yB : Heights a b N} (hyB : IsAboveDiagonal yB)
    (hevB : eventType yB (X, Y) = EventType.B) {k : ℕ}
    (hk : #(colouringEast yB ηlo) = k) :
    (Braid.specialMoveList (braidDataOfColouring a b N yB ηhi (k + 1)).2).length + 2
      = (Braid.specialMoveList (braidDataOfColouring a b N yB ηlo k).2).length := by
  have hηhi : ((a * N : ℕ) : ℚ) < ηhi := hηlo.trans (hI.ltP.trans hI.Plt)
  have hNlo : #(colouringNorth yB ηlo) = k := by
    rw [card_colouringNorth_eq_card_colouringEast hb hN hI.lo hηlo hyB, hk]
  have hNhi : #(colouringNorth yB ηhi) = k + 1 := by
    rw [hI.card_colouringNorth_of_eventType_B ha hN hevB, hNlo]
  have hle := hI.typeBIndex_succ_le ha hb hN hηlo hyB hevB (y := yB)
  rw [hk] at hle
  have hdatahi := isSpecialBraidData_braidDataOfColouring_of_card ha hb hN hI.hi hηhi hyB hNhi
  have h2 : (braidDataOfColouring a b N yB ηlo k).2
      = Function.update
          (fun i => (braidDataOfColouring a b N yB ηhi (k + 1)).2
            ((⟨typeBIndex yB ηlo X, by omega⟩ : Fin (k + 1)).succAbove i))
          ⟨typeBIndex yB ηlo X, by omega⟩
          ((braidDataOfColouring a b N yB ηhi (k + 1)).2 ⟨typeBIndex yB ηlo X, by omega⟩
            + (braidDataOfColouring a b N yB ηhi (k + 1)).2
                ⟨typeBIndex yB ηlo X + 1, by omega⟩ + 1) := by
    rw [hI.braidData_of_eventType_B ha hb hN hηlo hyB hevB hk ⟨typeBIndex yB ηlo X, by omega⟩
      ⟨typeBIndex yB ηlo X + 1, by omega⟩ rfl rfl ⟨typeBIndex yB ηlo X, by omega⟩ rfl]
  rw [h2, Braid.length_specialMoveList_merge _ _ ⟨typeBIndex yB ηlo X + 1, by omega⟩ _ rfl rfl
    (hdatahi.one_le_mult _) (hdatahi.one_le_mult _)]

/-- **The two routes to the type-`B` letter gap state the same equation.** -/
example : @length_specialMoveList_of_bePair_of_merge = @length_specialMoveList_of_bePair := rfl

/-! ### The lower braid value of a type-`B` event, with the extra letters named -/

/-- **THE TYPE-`B` MERGE THEOREM IN SITU.** At a type-`B` event above the floor, the braid value of
the *lower* special-braid data is `π_k` of an explicit word of `α_hi(j) + 1` letters of
`HJO.Braid.braidStep`, all at the single index `i₀`, applied to the braid value of the *upper* data
with the index `j` deleted — times the `r`-power the two `HJO.Braid.invFin` counts differ by.

Everything on the right reads the upper colouring only, apart from the rigid rotation
`HJO.Mellit.levelDropShift`. It is the merge counterpart of
`HJO.Mellit.braidValueOfData_succAbove_eq_dplus`, which does the same job at type `A` with `d^♭_+`
in place of the letter word; `HJO.Mellit.Isolates.braidData_of_eventType_B` is what makes the two
data tuples related in the first place. -/
theorem braidValueOfData_lo_eq_letters_of_eventType_B {L : Type*} [Field L] [Algebra ℚ L]
    (q u : L) {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) (hr : r * r = q) (ha : 0 < a)
    (hb : 0 < b) (hN : 0 < N) (hI : Isolates a b N X Y ηlo ηhi)
    (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N} (hy : IsAboveDiagonal y)
    (hev : eventType y (X, Y) = EventType.B) {k : ℕ} (hk : #(colouringEast y ηlo) = k)
    (j j' : Fin (k + 1)) (i₀ : Fin k) (hj : (j : ℕ) = typeBIndex y ηlo X)
    (hj' : (j' : ℕ) = typeBIndex y ηlo X + 1) (hi₀ : (i₀ : ℕ) = typeBIndex y ηlo X) :
    braidValueOfData q u hq hq1 hqp hr a b N (braidDataOfColouring a b N y ηlo k).1
        (braidDataOfColouring a b N y ηlo k).2
      = r ^ ((invFin (sweepTheta a b N)
                (fun i => (braidDataOfColouring a b N y ηhi (k + 1)).1 (j.succAbove i)
                  + levelDropShift a b N ηlo ηhi)
                (Function.update
                  (fun i => (braidDataOfColouring a b N y ηhi (k + 1)).2 (j.succAbove i)) i₀
                  ((braidDataOfColouring a b N y ηhi (k + 1)).2 j
                    + (braidDataOfColouring a b N y ηhi (k + 1)).2 j' + 1)) : ℤ)
            - (invFin (sweepTheta a b N)
                (fun i => (braidDataOfColouring a b N y ηhi (k + 1)).1 (j.succAbove i)
                  + levelDropShift a b N ηlo ηhi)
                (fun i => (braidDataOfColouring a b N y ηhi (k + 1)).2
                  (j.succAbove i)) : ℤ)) •
          ((braidRepMellit q u hq hq1 hqp hr k
              (Braid.braidWord (sweepTheta a b N)
                (Braid.positionPair (sweepTheta a b N)
                  (fun i => (braidDataOfColouring a b N y ηhi (k + 1)).1 (j.succAbove i)
                    + levelDropShift a b N ηlo ηhi)
                  fun i => (braidDataOfColouring a b N y ηhi (k + 1)).2 (j.succAbove i)).2
                (List.replicate ((braidDataOfColouring a b N y ηhi (k + 1)).2 j + 1) i₀))
              ⟨braidValueOfData q u hq hq1 hqp hr a b N
                  (fun i => (braidDataOfColouring a b N y ηhi (k + 1)).1 (j.succAbove i)
                    + levelDropShift a b N ηlo ηhi)
                  fun i => (braidDataOfColouring a b N y ηhi (k + 1)).2 (j.succAbove i),
                braidValueOfData_mem_pieceSub q u hq hq1 hqp hr a b N _ _⟩ : pieceSub L k)
            : Total L) := by
  have hηhi : ((a * N : ℕ) : ℚ) < ηhi := hηlo.trans (hI.ltP.trans hI.Plt)
  have hNlo : #(colouringNorth y ηlo) = k := by
    rw [card_colouringNorth_eq_card_colouringEast hb hN hI.lo hηlo hy, hk]
  have hNhi : #(colouringNorth y ηhi) = k + 1 := by
    rw [hI.card_colouringNorth_of_eventType_B ha hN hev, hNlo]
  have hdatahi := isSpecialBraidData_braidDataOfColouring_of_card ha hb hN hI.hi hηhi hy hNhi
  have hdatalo := isSpecialBraidData_braidDataOfColouring_of_card ha hb hN hI.lo hηlo hy hNlo
  have hdict := hI.braidData_of_eventType_B ha hb hN hηlo hy hev hk j j' hj hj' i₀ hi₀
  have h1 : (braidDataOfColouring a b N y ηlo k).1
      = fun i => (braidDataOfColouring a b N y ηhi (k + 1)).1 (j.succAbove i)
          + levelDropShift a b N ηlo ηhi := by rw [hdict]
  have h2 : (braidDataOfColouring a b N y ηlo k).2
      = Function.update
          (fun i => (braidDataOfColouring a b N y ηhi (k + 1)).2 (j.succAbove i)) i₀
          ((braidDataOfColouring a b N y ηhi (k + 1)).2 j
            + (braidDataOfColouring a b N y ηhi (k + 1)).2 j' + 1) := by rw [hdict]
  rw [h1, h2] at hdatalo
  rw [h1, h2]
  exact braidValueOfData_merge q u hq hq1 hqp hr a b N _ _ j j' i₀ (by omega) (by omega)
    (hdatahi.one_le_mult j') hdatalo

/-! ### Rule `BE` at one bracketed point, with the merged multiplicity eliminated -/

/-- **Rule `BE` at one bracketed point, with the merge discharged.** The hypothesis `hmerge` of
`HJO.Mellit.Isolates.braidValueColouring_eq_dminus_add_smul_of_merge` is traded for `hletters`,
whose left-hand side is no longer a braid value of merged data but the explicit letter word of
`HJO.Mellit.Isolates.braidValueOfData_lo_eq_letters_of_eventType_B` applied to the braid value of
the upper data with the index `j` deleted.

That trade is a *theorem*, not a change of vocabulary: `hmerge` follows from `hletters` through the
merge identity, whose proof is `HJO.Braid.specialBraid_merge`. -/
theorem braidValueColouring_eq_dminus_add_smul_of_letters {L : Type*} [Field L] [Algebra ℚ L]
    (q u : L) {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) (hr : r * r = q) (ha : 0 < a)
    (hb : 0 < b) (hN : 0 < N) (hI : Isolates a b N X Y ηlo ηhi)
    (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {yB yE : Heights a b N} (hyB : IsAboveDiagonal yB)
    (hyE : IsAboveDiagonal yE) (hevB : eventType yB (X, Y) = EventType.B)
    (hevE : eventType yE (X, Y) = EventType.E) (hcol : colouring yB ηlo = colouring yE ηlo)
    {k : ℕ} (hk : #(colouringEast yB ηlo) = k) (j j' : Fin (k + 1))
    (hj : (j : ℕ) = typeBIndex yB ηlo X) (hj' : (j' : ℕ) = typeBIndex yB ηlo X + 1) (i₀ : Fin k)
    (hi₀ : (i₀ : ℕ) = typeBIndex yB ηlo X)
    (hletters : r ^ ((invFin (sweepTheta a b N)
                (fun i => (braidDataOfColouring a b N yB ηhi (k + 1)).1 (j.succAbove i)
                  + levelDropShift a b N ηlo ηhi)
                (Function.update
                  (fun i => (braidDataOfColouring a b N yB ηhi (k + 1)).2 (j.succAbove i)) i₀
                  ((braidDataOfColouring a b N yB ηhi (k + 1)).2 j
                    + (braidDataOfColouring a b N yB ηhi (k + 1)).2 j' + 1)) : ℤ)
            - (invFin (sweepTheta a b N)
                (fun i => (braidDataOfColouring a b N yB ηhi (k + 1)).1 (j.succAbove i)
                  + levelDropShift a b N ηlo ηhi)
                (fun i => (braidDataOfColouring a b N yB ηhi (k + 1)).2
                  (j.succAbove i)) : ℤ)) •
          ((braidRepMellit q u hq hq1 hqp hr k
              (Braid.braidWord (sweepTheta a b N)
                (Braid.positionPair (sweepTheta a b N)
                  (fun i => (braidDataOfColouring a b N yB ηhi (k + 1)).1 (j.succAbove i)
                    + levelDropShift a b N ηlo ηhi)
                  fun i => (braidDataOfColouring a b N yB ηhi (k + 1)).2 (j.succAbove i)).2
                (List.replicate ((braidDataOfColouring a b N yB ηhi (k + 1)).2 j + 1) i₀))
              ⟨braidValueOfData q u hq hq1 hqp hr a b N
                  (fun i => (braidDataOfColouring a b N yB ηhi (k + 1)).1 (j.succAbove i)
                    + levelDropShift a b N ηlo ηhi)
                  fun i => (braidDataOfColouring a b N yB ηhi (k + 1)).2 (j.succAbove i),
                braidValueOfData_mem_pieceSub q u hq hq1 hqp hr a b N _ _⟩ : pieceSub L k)
            : Total L)
        = dminus q (k + 1) (braidValueOfData q u hq hq1 hqp hr a b N
              (braidDataOfColouring a b N yB ηhi (k + 1)).1
              (braidDataOfColouring a b N yB ηhi (k + 1)).2)
          + u • braidValueOfData q u hq hq1 hqp hr a b N
              (braidDataOfColouring a b N yE ηhi k).1
              (braidDataOfColouring a b N yE ηhi k).2) :
    braidValueColouring q u hq hq1 hqp hr a b N ηlo (colouring yB ηlo)
      = dminus q (sweepWidth yB (X, Y))
          (braidValueColouring q u hq hq1 hqp hr a b N ηhi (colouring yB ηhi))
        + u • braidValueColouring q u hq hq1 hqp hr a b N ηhi (colouring yE ηhi) := by
  have hηhi : ((a * N : ℕ) : ℚ) < ηhi := hηlo.trans (hI.ltP.trans hI.Plt)
  have hNlo : #(colouringNorth yB ηlo) = k := by
    rw [card_colouringNorth_eq_card_colouringEast hb hN hI.lo hηlo hyB, hk]
  have hNhi : #(colouringNorth yB ηhi) = k + 1 := by
    rw [hI.card_colouringNorth_of_eventType_B ha hN hevB, hNlo]
  have hdatahi := isSpecialBraidData_braidDataOfColouring_of_card ha hb hN hI.hi hηhi hyB hNhi
  have hdatalo := isSpecialBraidData_braidDataOfColouring_of_card ha hb hN hI.lo hηlo hyB hNlo
  have hdict := hI.braidData_of_eventType_B ha hb hN hηlo hyB hevB hk j j' hj hj' i₀ hi₀
  have h1 : (braidDataOfColouring a b N yB ηlo k).1
      = fun i => (braidDataOfColouring a b N yB ηhi (k + 1)).1 (j.succAbove i)
          + levelDropShift a b N ηlo ηhi := by rw [hdict]
  have h2 : (braidDataOfColouring a b N yB ηlo k).2
      = Function.update
          (fun i => (braidDataOfColouring a b N yB ηhi (k + 1)).2 (j.succAbove i)) i₀
          ((braidDataOfColouring a b N yB ηhi (k + 1)).2 j
            + (braidDataOfColouring a b N yB ηhi (k + 1)).2 j' + 1) := by rw [hdict]
  rw [h1, h2] at hdatalo
  refine hI.braidValueColouring_eq_dminus_add_smul_of_merge q u hq hq1 hqp hr ha hb hN hηlo hyB
    hyE hevB hevE hcol hk j j' hj hj' i₀ hi₀ ?_
  exact (braidValueOfData_merge q u hq hq1 hqp hr a b N _ _ j j' i₀ (by omega) (by omega)
    (hdatahi.one_le_mult j') hdatalo).trans hletters

end Isolates

/-! ### The floored clause, with the merged multiplicity eliminated -/

/-- **`HJO.Mellit.SweepRecursionBEFloor` for `HJO.Mellit.braidValueColouring`, given the letter
identity at every bracketed point.** This is
`HJO.Mellit.braidValueColouring_sweepRecursionBEFloor_of_merge` with its hypothesis discharged
through the merge identity: what the clause now asks for is an identity between `π_k` of an
explicit `α_hi(j) + 1`-letter word of `HJO.Braid.braidStep` applied to the braid value of the upper
data with the index `j` deleted, and the `d^♭_-`-and-`u` combination of the two upper braid values.

No merged multiplicity survives in the hypothesis. What does survive is the word itself, and it is
where the whole remaining content of rule `BE` sits. -/
theorem braidValueColouring_sweepRecursionBEFloor_of_letters {L : Type*} [Field L] [Algebra ℚ L]
    (q u : L) {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) (hr : r * r = q) {a b N : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hletters : ∀ (X Y : ℕ) (ηlo ηhi : ℚ), ((a * N : ℕ) : ℚ) < ηlo →
      Isolates a b N X Y ηlo ηhi → ∀ yB yE : Heights a b N, IsAboveDiagonal yB →
        IsAboveDiagonal yE → eventType yB (X, Y) = EventType.B →
          eventType yE (X, Y) = EventType.E → colouring yB ηlo = colouring yE ηlo →
            ∀ (j j' : Fin (#(colouringEast yB ηlo) + 1))
              (i₀ : Fin #(colouringEast yB ηlo)),
              (j : ℕ) = typeBIndex yB ηlo X → (j' : ℕ) = typeBIndex yB ηlo X + 1 →
                (i₀ : ℕ) = typeBIndex yB ηlo X →
                  r ^ ((invFin (sweepTheta a b N)
                          (fun i => (braidDataOfColouring a b N yB ηhi
                              (#(colouringEast yB ηlo) + 1)).1 (j.succAbove i)
                            + levelDropShift a b N ηlo ηhi)
                          (Function.update
                            (fun i => (braidDataOfColouring a b N yB ηhi
                              (#(colouringEast yB ηlo) + 1)).2 (j.succAbove i)) i₀
                            ((braidDataOfColouring a b N yB ηhi
                                (#(colouringEast yB ηlo) + 1)).2 j
                              + (braidDataOfColouring a b N yB ηhi
                                (#(colouringEast yB ηlo) + 1)).2 j' + 1)) : ℤ)
                        - (invFin (sweepTheta a b N)
                          (fun i => (braidDataOfColouring a b N yB ηhi
                              (#(colouringEast yB ηlo) + 1)).1 (j.succAbove i)
                            + levelDropShift a b N ηlo ηhi)
                          (fun i => (braidDataOfColouring a b N yB ηhi
                            (#(colouringEast yB ηlo) + 1)).2 (j.succAbove i)) : ℤ)) •
                    ((braidRepMellit q u hq hq1 hqp hr #(colouringEast yB ηlo)
                        (Braid.braidWord (sweepTheta a b N)
                          (Braid.positionPair (sweepTheta a b N)
                            (fun i => (braidDataOfColouring a b N yB ηhi
                                (#(colouringEast yB ηlo) + 1)).1 (j.succAbove i)
                              + levelDropShift a b N ηlo ηhi)
                            fun i => (braidDataOfColouring a b N yB ηhi
                              (#(colouringEast yB ηlo) + 1)).2 (j.succAbove i)).2
                          (List.replicate ((braidDataOfColouring a b N yB ηhi
                            (#(colouringEast yB ηlo) + 1)).2 j + 1) i₀))
                        ⟨braidValueOfData q u hq hq1 hqp hr a b N
                            (fun i => (braidDataOfColouring a b N yB ηhi
                                (#(colouringEast yB ηlo) + 1)).1 (j.succAbove i)
                              + levelDropShift a b N ηlo ηhi)
                            fun i => (braidDataOfColouring a b N yB ηhi
                              (#(colouringEast yB ηlo) + 1)).2 (j.succAbove i),
                          braidValueOfData_mem_pieceSub q u hq hq1 hqp hr a b N _ _⟩ :
                        pieceSub L #(colouringEast yB ηlo)) : Total L)
                    = dminus q (#(colouringEast yB ηlo) + 1)
                        (braidValueOfData q u hq hq1 hqp hr a b N
                          (braidDataOfColouring a b N yB ηhi
                            (#(colouringEast yB ηlo) + 1)).1
                          (braidDataOfColouring a b N yB ηhi
                            (#(colouringEast yB ηlo) + 1)).2)
                      + u • braidValueOfData q u hq hq1 hqp hr a b N
                          (braidDataOfColouring a b N yE ηhi #(colouringEast yB ηlo)).1
                          (braidDataOfColouring a b N yE ηhi #(colouringEast yB ηlo)).2) :
    SweepRecursionBEFloor q u a b N (braidValueColouring q u hq hq1 hqp hr a b N) := by
  intro P ηlo ηhi hfloor hlo hhi hP1 hP2 hltP hPlt hiso yB yE hyB hyE _ hevB hevE hcol
  obtain ⟨X, Y⟩ := P
  have hI : Isolates a b N X Y ηlo ηhi := ⟨hlo, hhi, hltP, hPlt, hiso, hP1, hP2⟩
  have hle := hI.typeBIndex_succ_le ha hb hN hfloor hyB hevB (y := yB)
  exact hI.braidValueColouring_eq_dminus_add_smul_of_letters q u hq hq1 hqp hr ha hb hN hfloor hyB
    hyE hevB hevE hcol rfl ⟨typeBIndex yB ηlo X, by omega⟩ ⟨typeBIndex yB ηlo X + 1, by omega⟩
    rfl rfl ⟨typeBIndex yB ηlo X, by omega⟩ rfl
    (hletters X Y ηlo ηhi hfloor hI yB yE hyB hyE hevB hevE hcol _ _ _ rfl rfl rfl)

/-! ### Consistency check at the decided configuration

The `2 × 3` configuration `HJO.Mellit.dsc_eq_dminus_add_smul_example` is stated at: the paths
`(0,2,3)` and `(0,3,3)`, the point `P = (1, 2)` of rank `4`, the levels `7/2` and `9/2`. There
`k = 1`, the lower data has one component and the upper data two, and `j = 0`.

The lower special braid is produced twice. Once from the ad-hoc letter count
`HJO.Mellit.length_specialMoveList_be_witness_adhoc`, which is computed from the two total
crossing counts and the two widths with no merge used: rank `1` and three moves, so the move
sequence is three copies of the index `0`. And once from `HJO.Braid.specialBraid_merge`, where the
*only* inputs are the two upper multiplicities `2` and `1`: the word length is `α_hi(0) + 1 = 3`
and the residual special braid is the identity because the deleted data has every multiplicity `1`.

A `+2` in place of the `+1` of the multiplicity split gives a four-letter word, and the type-`A`
reading — the two insertion indices equal, so nothing deleted — gives `α_hi(0) - 1 = 1` letter. -/

/-- The lower move sequence of the type-`B` witness, from the ad-hoc letter count: rank `1` and
three moves, so the sequence is three copies of the index `0`. -/
theorem specialMoveList_be_witness_lo_adhoc :
    Braid.specialMoveList (braidDataOfColouring 2 3 1 (![0, 2, 3] : Heights 2 3 1) (7 / 2) 1).2
      = List.replicate 3 0 := by
  have hrep : Braid.specialMoveList
        (braidDataOfColouring 2 3 1 (![0, 2, 3] : Heights 2 3 1) (7 / 2) 1).2
      = List.replicate
          ((braidDataOfColouring 2 3 1 (![0, 2, 3] : Heights 2 3 1) (7 / 2) 1).2 0 - 1) 0 := by
    refine List.eq_replicate_iff.2 ⟨?_, fun t _ => Fin.eq_zero t⟩
    rw [Braid.length_specialMoveList, Fin.sum_univ_one]
  have hlen := length_specialMoveList_be_witness_adhoc.2
  rw [hrep, List.length_replicate] at hlen
  rw [hrep, hlen]

/-- **The lower special braid of the type-`B` witness is a three-letter word at the single index
`0`**, read straight off the ad-hoc move sequence. -/
theorem specialBraid_be_witness_lo_decided :
    Braid.specialBraid (sweepTheta 2 3 1)
        (braidDataOfColouring 2 3 1 (![0, 2, 3] : Heights 2 3 1) (7 / 2) 1).1
        (braidDataOfColouring 2 3 1 (![0, 2, 3] : Heights 2 3 1) (7 / 2) 1).2
      = Braid.braidWord (sweepTheta 2 3 1)
          (braidDataOfColouring 2 3 1 (![0, 2, 3] : Heights 2 3 1) (7 / 2) 1).1
          (List.replicate 3 0) := by
  rw [Braid.specialBraid, specialMoveList_be_witness_lo_adhoc]

/-- **The same through `HJO.Braid.specialBraid_merge`**, with the ad-hoc route unused: the two
upper multiplicities `2` and `1` give a word of `2 + 1 = 3` letters at the index `0` and a residual
special braid of `1`. -/
theorem specialBraid_be_witness_lo_via_merge :
    Braid.specialBraid (sweepTheta 2 3 1)
        (braidDataOfColouring 2 3 1 (![0, 2, 3] : Heights 2 3 1) (7 / 2) 1).1
        (braidDataOfColouring 2 3 1 (![0, 2, 3] : Heights 2 3 1) (7 / 2) 1).2
      = Braid.braidWord (sweepTheta 2 3 1)
          (braidDataOfColouring 2 3 1 (![0, 2, 3] : Heights 2 3 1) (7 / 2) 1).1
          (List.replicate 3 0) := by
  have hy : IsAboveDiagonal (![0, 2, 3] : Heights 2 3 1) := by decide
  have hev : eventType (![0, 2, 3] : Heights 2 3 1) (1, 2) = EventType.B := by decide
  have hkE : #(colouringEast (![0, 2, 3] : Heights 2 3 1) (7 / 2)) = 1 := by
    rw [colouringEast_be_witness.1]; decide
  have hkN : #(colouringNorth (![0, 2, 3] : Heights 2 3 1) (7 / 2)) = 1 := by
    rw [colouringNorth_be_witness.1]; decide
  obtain ⟨hβ0, hβ1⟩ := braidData_snd_hi_be_witness_adhoc
  have hsucc : (0 : Fin 2).succAbove (0 : Fin 1) = 1 := by decide
  have hone : ∀ i : Fin 1,
      (braidDataOfColouring 2 3 1 (![0, 2, 3] : Heights 2 3 1) (9 / 2) 2).2
        ((0 : Fin 2).succAbove i) = 1 := by
    intro i
    have hi : i = 0 := Fin.eq_zero i
    subst hi
    rw [hsucc]
    exact hβ1
  have hdict := isolates_be_witness.braidData_of_eventType_B (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hy hev hkE 0 1 (by simp [typeBIndex_be_witness])
    (by simp [typeBIndex_be_witness]) 0 (by simp [typeBIndex_be_witness])
  have h1 : (braidDataOfColouring 2 3 1 (![0, 2, 3] : Heights 2 3 1) (7 / 2) 1).1
      = fun i => (braidDataOfColouring 2 3 1 (![0, 2, 3] : Heights 2 3 1) (9 / 2) 2).1
          ((0 : Fin 2).succAbove i) + levelDropShift 2 3 1 (7 / 2) (9 / 2) := by rw [hdict]
  have h2 : (braidDataOfColouring 2 3 1 (![0, 2, 3] : Heights 2 3 1) (7 / 2) 1).2
      = Function.update
          (fun i => (braidDataOfColouring 2 3 1 (![0, 2, 3] : Heights 2 3 1) (9 / 2) 2).2
            ((0 : Fin 2).succAbove i)) 0
          ((braidDataOfColouring 2 3 1 (![0, 2, 3] : Heights 2 3 1) (9 / 2) 2).2 0
            + (braidDataOfColouring 2 3 1 (![0, 2, 3] : Heights 2 3 1) (9 / 2) 2).2 1
            + 1) := by rw [hdict]
  have hdatalo := isSpecialBraidData_braidDataOfColouring_of_card (a := 2) (b := 3) (N := 1)
    (by norm_num) (by norm_num) (by norm_num) isolates_be_witness.lo (by norm_num) hy hkN
  rw [h1, h2] at hdatalo
  have hmerge := Braid.specialBraid_merge
    (braidDataOfColouring 2 3 1 (![0, 2, 3] : Heights 2 3 1) (9 / 2) 2).2 0 1 0 rfl rfl
    (by omega) hdatalo
  have hpos : (Braid.positionPair (sweepTheta 2 3 1)
        (fun i => (braidDataOfColouring 2 3 1 (![0, 2, 3] : Heights 2 3 1) (9 / 2) 2).1
          ((0 : Fin 2).succAbove i) + levelDropShift 2 3 1 (7 / 2) (9 / 2))
        fun i => (braidDataOfColouring 2 3 1 (![0, 2, 3] : Heights 2 3 1) (9 / 2) 2).2
          ((0 : Fin 2).succAbove i)).2
      = fun i => (braidDataOfColouring 2 3 1 (![0, 2, 3] : Heights 2 3 1) (9 / 2) 2).1
          ((0 : Fin 2).succAbove i) + levelDropShift 2 3 1 (7 / 2) (9 / 2) :=
    funext fun t => Braid.positionPair_snd_of_mult_eq_one (hone t)
  rw [h1, h2, hmerge, Braid.specialBraid_of_forall_eq_one hone, mul_one, hpos, hβ0]

/-- **The two routes state the same identity.** -/
example : specialBraid_be_witness_lo_decided = specialBraid_be_witness_lo_via_merge := rfl

end HJO.Mellit

end
