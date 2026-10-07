/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidMoveCommPerm
public import HJO.Shuffle.BraidValueColouring
public meta import HJO.Attr

/-! # Raising one multiplicity by one, at unchanged rank

`HJO.Sweep.DplusIntertwines` is the **rank-raise** intertwiner: the type-`A` clause of
`HJO.Mellit.braidValueColouring_sweepRecursionsFloor` inserts a bottom entry into the special-braid
data, the rank goes from `k` to `k + 1`, and `HJO.Mellit.braidValueOfData_succAbove_eq_dplus` reads
the value of the inserted data as `d^♭_+` of the value of the deleted one.

The type-`C` and type-`D` clauses need the other move. There the rank does **not** change: the two
colourings have the same number of components, the positions move rigidly, and exactly one
multiplicity goes up by one — `HJO.Mellit.Isolates.braidData_snd_succ_of_eventType_C` and its
type-`D` twin. This file is what that does to `HJO.Braid.specialBraid`, and the answer is one extra
letter of `HJO.Braid.braidStep`.

## The two decompositions, and why there are two

`HJO.Braid.specialMoveList` lists the moves in increasing order of index, and the head of the list
is the move performed *last* (`HJO.Braid.braidWord_cons`). Raising `α_j` by one adds one copy of `j`
to the multiset of moves, and `HJO.Braid.braidWord_perm_of_isSpecialBraidData` says the ordering
costs nothing, so the extra move may be placed at either end of the sequence:

* `HJO.Braid.specialBraid_update_succ_left` — the extra move performed **last**, so its letter
  stands **leftmost** and is read at the tuple all the *other* moves have reached, which is the
  final position tuple `(v, v^fin)` of `HJO.Braid.positionPair` **for the unraised `α`**.
* `HJO.Braid.specialBraid_update_succ_right` — the extra move performed **first**, so its letter
  stands **rightmost** and is read at the initial tuple `v` itself, the rest of the braid then being
  the special braid of the once-moved tuple `HJO.Braid.moveOne θ v j`.

Both are needed, and which one a clause wants is decided by the geometry rather than by taste. At a
type-`C` drop the *bottom* crossing index of the component falls by one while the top index stands
still (`HJO.Mellit.Isolates.componentBotIndex_of_eventType_C`), so `v` is the upper `v` rigidly
rotated and the added crossing is the **last** iterate: the left form applies, with the unraised
data on the right. At a type-`D` drop the *top* index rises by one and the bottom index stands still
(`HJO.Mellit.Isolates.componentTopIndex_of_eventType_D`), so the added crossing is `v` itself and
the *old* `v` is `HJO.Braid.nextCrossing` of the new one — that is
`HJO.Mellit.Isolates.braidData_fst_succ_of_eventType_D`'s fractional part, read backwards. There the
right form applies, and `HJO.Braid.moveOne θ v j` is the rotated upper tuple.

## What the extra letter is

`HJO.Braid.braidStep θ w j = T_{a'↘a} · (z_a or ỹ_a)`, the generator being a `z` when `w j < θ` and
a `ỹ` when `θ < w j`. So the added letter is a `z` exactly when the position the extra move starts
from lies below the puncture. That is the letter-level reading of
`HJO.Mellit.Isolates.zCount_sub_eq_zero_of_eventType_C` (`ζ` unchanged, so the added letter is a
`ỹ`) and `HJO.Mellit.Isolates.zCount_sub_eq_one_of_eventType_D` (`ζ` up one, so a `z`), and the two
decompositions place the letter at the two tuples at which those two readings come out right.

## Genericity

Nothing here inverts anything. `HJO.Braid.specialBraid_update_succ_left` and
`HJO.Braid.specialBraid_update_succ_right` are identities in `HJO.Braid.BraidMonoid k`, with `ℚ`
positions: no field `L`, no `q`, hence no bad parameter. The value-level
`HJO.Mellit.braidValueOfData_update_succ_left` carries `HJO.Sweep.braidRep`'s own exclusions and no
others — `q ≠ 0`, `q ≠ 1`, `q + 1 ≠ 0`, `r * r = q` — and the one inverse it evaluates is `r⁻¹`
inside the `zpow`, which is legitimate because `r ≠ 0` follows from `r * r = q ≠ 0`. The
`(q - 1)⁻¹` of `HJO.Sweep.corner` and the `q/(1-q)` of `HJO.Sweep.zop` do not appear.

## References

Transcribing A. Mellit, *Toric braids and `(m, n)`-parking functions*, section 5.
-/

@[expose] public section

namespace HJO.Braid

variable {k : ℕ}

/-! ### The move multiset of a raised multiplicity -/

/-- **Raising `α_j` by one adds one copy of `j` to the move sequence.** The two sequences are
permutations of one another, which by `HJO.Braid.braidWord_perm_of_isSpecialBraidData` is all the
braid can see. `1 ≤ α_j` is `HJO.Braid.IsSpecialBraidData.one_le_mult` at the *unraised* data and is
genuinely needed: at `α_j = 0` the truncated subtraction lists no copy of `j` on the left and one on
the right. -/
theorem specialMoveList_update_succ_perm (α : Fin k → ℕ) (j : Fin k) (hα : 1 ≤ α j) :
    (specialMoveList (Function.update α j (α j + 1))).Perm (j :: specialMoveList α) := by
  classical
  refine (List.perm_iff_count).2 fun t => ?_
  rw [count_specialMoveList]
  by_cases h : t = j
  · subst h
    rw [List.count_cons_self, count_specialMoveList, Function.update_self]
    omega
  · rw [List.count_cons_of_ne (Ne.symm h), count_specialMoveList, Function.update_of_ne h]

/-- The same multiset with the extra copy of `j` written at the **end** of the sequence, which is
the reading in which the extra move is performed *first*. -/
theorem specialMoveList_update_succ_perm_append (α : Fin k → ℕ) (j : Fin k) (hα : 1 ≤ α j) :
    (specialMoveList (Function.update α j (α j + 1))).Perm (specialMoveList α ++ [j]) :=
  (specialMoveList_update_succ_perm α j hα).trans (List.perm_append_singleton j _).symm

/-! ### The two decompositions of the raised special braid -/

/-- **The equal-rank raise, with the extra letter on the left.** Raising the multiplicity of the
single index `j` by one multiplies `B_{s,v,α}` on the left by one letter of `HJO.Braid.braidStep`,
read at the **final** position tuple `v^fin` of `HJO.Braid.positionPair` for the *unraised* `α`.

This is the equal-rank analogue of `HJO.Mellit.braidValueOfData_succAbove_eq_dplus`'s braid half:
there the rank rises and every index of every letter is raised; here the rank stands still and one
letter is appended. -/
theorem specialBraid_update_succ_left {s θ : ℚ} {v : Fin k → ℚ} {α : Fin k → ℕ} (j : Fin k)
    (hα : 1 ≤ α j)
    (hdata : IsSpecialBraidData s θ k v (Function.update α j (α j + 1))) :
    specialBraid θ v (Function.update α j (α j + 1))
      = braidStep θ (positionPair θ v α).2 j * specialBraid θ v α := by
  rw [specialBraid,
    braidWord_perm_of_isSpecialBraidData hdata (fun t => (count_specialMoveList _ t).le)
      (specialMoveList_update_succ_perm α j hα),
    braidWord_cons, moveTuple_specialMoveList, specialBraid]

/-- **The equal-rank raise, with the extra letter on the right.** The same added move performed
*first* in time: its letter stands rightmost and is read at the initial tuple `v`, and what remains
is the special braid of the once-moved tuple `HJO.Braid.moveOne θ v j` at the *unraised*
multiplicities. -/
theorem specialBraid_update_succ_right {s θ : ℚ} {v : Fin k → ℚ} {α : Fin k → ℕ} (j : Fin k)
    (hα : 1 ≤ α j)
    (hdata : IsSpecialBraidData s θ k v (Function.update α j (α j + 1))) :
    specialBraid θ v (Function.update α j (α j + 1))
      = specialBraid θ (moveOne θ v j) α * braidStep θ v j := by
  rw [specialBraid,
    braidWord_perm_of_isSpecialBraidData hdata (fun t => (count_specialMoveList _ t).le)
      (specialMoveList_update_succ_perm_append α j hα),
    braidWord_append, braidWord_singleton, specialBraid, moveTuple_cons, moveTuple_nil]

end HJO.Braid

namespace HJO.Mellit

open ParkingFunctions Paths Sweep Braid

variable {L : Type*} [Field L] [Algebra ℚ L]

/-! ### The braid value of a raised multiplicity -/

/-- The braid value of special-braid data lies in the graded piece `V_k` it is read in. -/
theorem braidValueOfData_mem_pieceSub (q u : L) {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1)
    (hqp : q + 1 ≠ 0) (hr : r * r = q) (a b N : ℕ) {k : ℕ} (v : Fin k → ℚ) (α : Fin k → ℕ) :
    braidValueOfData q u hq hq1 hqp hr a b N v α ∈ pieceSub L k := by
  rw [braidValueOfData]
  exact Submodule.smul_mem _ _
    (braidRepMellit q u hq hq1 hqp hr k
      (specialBraid (sweepTheta a b N) v α) (dplusIterPiece q k)).2

omit [Algebra ℚ L] in
/-- `r ≠ 0`, which is all the inverses inside the `zpow` prefactor of `HJO.Mellit.braidValueOfData`
need: `r * r = q` and `q ≠ 0`. -/
theorem ne_zero_of_sq_eq {q r : L} (hq : q ≠ 0) (hr : r * r = q) : r ≠ 0 := fun h =>
  hq (by rw [← hr, h, mul_zero])

/-- **The equal-rank raise at the level of the braid value, with the extra letter as an operator.**
Raising the multiplicity of the single index `j` by one applies to the braid value one letter of
`HJO.Braid.braidStep` — read at the final position tuple of `HJO.Braid.positionPair` for
the *unraised* `α` — and multiplies by the `r`-power the two `HJO.Braid.invFin` counts differ by.
`HJO.Braid.invIni` is the same on both sides, reading only `v`.

This is the equal-rank analogue of `HJO.Mellit.braidValueOfData_succAbove_eq_dplus`. There the
operator is `d^♭_+` and the rank rises; here it is `π_k` of one letter and the rank stands still. -/
theorem braidValueOfData_update_succ_left (q u : L) {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1)
    (hqp : q + 1 ≠ 0) (hr : r * r = q) (a b N : ℕ) {k : ℕ} {v : Fin k → ℚ} {α : Fin k → ℕ}
    (j : Fin k) (hα : 1 ≤ α j)
    (hdata : IsSpecialBraidData (sweepSlope a b N) (sweepTheta a b N) k v
      (Function.update α j (α j + 1))) :
    braidValueOfData q u hq hq1 hqp hr a b N v (Function.update α j (α j + 1))
      = r ^ ((invFin (sweepTheta a b N) v (Function.update α j (α j + 1)) : ℤ)
            - (invFin (sweepTheta a b N) v α : ℤ)) •
          ((braidRepMellit q u hq hq1 hqp hr k
              (braidStep (sweepTheta a b N) (positionPair (sweepTheta a b N) v α).2 j)
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
    specialBraid_update_succ_left j hα hdata, map_mul, Module.End.mul_apply,
    invIni_eq_tupleInversions, invIni_eq_tupleInversions]
  congr 2
  ring

/-- **The equal-rank raise at the level of the braid value, with the extra letter on the vacuum.**
The same added move performed *first* in time: the letter acts on the vacuum vector of
`HJO.Mellit.braidValueOfData` and the rest of the braid is the special braid of the once-moved
tuple. This is the form a type-`D` drop asks for, where the added crossing is the new `v` itself and
the *old* `v` is `HJO.Braid.nextCrossing` of it. No membership side condition is needed, both
`π_k`'s being read on the graded piece directly. -/
theorem braidValueOfData_update_succ_right (q u : L) {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1)
    (hqp : q + 1 ≠ 0) (hr : r * r = q) (a b N : ℕ) {k : ℕ} {v : Fin k → ℚ} {α : Fin k → ℕ}
    (j : Fin k) (hα : 1 ≤ α j)
    (hdata : IsSpecialBraidData (sweepSlope a b N) (sweepTheta a b N) k v
      (Function.update α j (α j + 1))) :
    braidValueOfData q u hq hq1 hqp hr a b N v (Function.update α j (α j + 1))
      = r ^ ((invFin (sweepTheta a b N) v (Function.update α j (α j + 1)) : ℤ)
            - (invIni (sweepTheta a b N) v α : ℤ)) •
          ((braidRepMellit q u hq hq1 hqp hr k
              (specialBraid (sweepTheta a b N) (moveOne (sweepTheta a b N) v j) α)
              (braidRepMellit q u hq hq1 hqp hr k
                (braidStep (sweepTheta a b N) v j) (dplusIterPiece q k)) : pieceSub L k)
            : Total L) := by
  rw [braidValueOfData, specialBraid_update_succ_right j hα hdata, map_mul, Module.End.mul_apply,
    invIni_eq_tupleInversions, invIni_eq_tupleInversions]

end HJO.Mellit
