/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidBottomInsert
public import HJO.Shuffle.BraidPhiInsert
public import HJO.Shuffle.BraidValueColouring
public import HJO.Shuffle.BraidYtildeMellit
public import HJO.Shuffle.MellitAppend
public import HJO.CMStructure.MellitZrelShift
public import HJO.CMStructure.VmodDplusRelations
public meta import HJO.Attr

/-! # The intertwiner of `d^♭_+` with the braid rank raise

A type-`A` event of the level recursion inserts a **bottom** entry into the special-braid data, and
`HJO/Shuffle/BraidBottomInsert.lean` shows what that does to the braid: the inserted component
contributes no letter, and every retained component's letter is the same letter with **every index
raised by one** (`HJO.Braid.braidStep_succAbove_of_forall_lt`). This file turns that index raise
into an operator identity: `d^♭_+` — the raising operator `HJO.Sweep.dplus`,
which is the operator rule `A` of `HJO.Mellit.dsc_lo_eq_dplus_dsc_hi` applies — intertwines `π_k` of
a braid with `π_{k+1}` of its raise, letter by letter and then along a whole word.

`T_i ↦ T_{i+1}`, `ỹ_a ↦ ỹ_{a+1}`, `z_a ↦ z_{a+1}`

is the raise, and all three kinds are covered.

## Why this is not a homomorphism of `𝔹^+_k(𝕋_0)`

`HJO.Braid.phiPlusStar` is the homomorphism raising the index of every
*generator*, and it is **not** this map: `HJO.Braid.phiPlusStar_braidYtilde_one` gives
`φ^*_+(ỹ_1) = T̄_1ỹ_1T_1`, a conjugate of `ỹ_1` at the same index, where the raise wants `ỹ_2`. The
two differ by replacing one `T̄_1` by `T_1`, which is the `T_1^2` of
`HJO.Braid.phiPlusStar_braidYtilde`; and that discrepancy is exactly the difference between the two
vertical arrows, `HJO.Mellit.dplus_ne_negYOneDPlusStar_auxVar_one_sq` showing that `d_+` and the
`-y_1d^*_+` of `HJO.Sweep.braidRep_phiPlusStar_comp_negYOneDPlusStarPiece` are different maps
`V_1 → V_2`.

The raise is a homomorphism on the generators `T_i`, `T̄_i`, `z_1` — there it agrees with `φ^*_+` —
but on `y_1` it must send the letter to `T_1y_1T̄_1`, and then `φ^*_+`'s image of `y_k` is not the
raise's. Rather than build a second homomorphism and discharge the ten relation families of
`HJO.Braid.BraidMonoid` again, this file carries the raise as a **relation** between a rank-`k`
braid and a rank-`(k+1)` braid, `HJO.Sweep.DplusIntertwines`, which is all that is needed: it is
multiplicative (`HJO.Sweep.DplusIntertwines.mul`), so it assembles along trains, words and the
special braid exactly as a homomorphism would, and it is the *statement* of the diagram rather
than a map that has to be constructed.

## The three letters, and where each comes from

* `T_i` — `HJO.Sweep.dplus_braid_succ`, `HJO.Sweep.dplus_mul_braidEnd_succ`. The two `q^{-1/2}` of
  `HJO.Sweep.braidRep` are the same on both sides, so nothing is spent.
* `T̄_i` — the same identity inverted, which is where `q ≠ 0` is read.
* `y_1 ↦ T_1y_1T̄_1` — `HJO.Sweep.dplus_auxVar_one_mul`. **This is the whole
  content of the `ỹ` case**: the loop `Λ̄_1` of `HJO.Braid.braidYtilde` is a word in the `T̄`, so it
  raises by the second bullet, and the trailing `T̄_1T_1` of
  `HJO.Braid.braidYtilde_succ_eq_raise` cancels.
* `z_a ↦ z_{a+1}` — `HJO.Sweep.starCommCM_cmDPlus` in the convention `HJO.Sweep.zop` is written in,
  proved as `HJO.Sweep.dplus_zop`. No train assembly is needed here: `HJO.Braid.braidGenZ` *is* the
  letter of `HJO.Braid.braidStep` at the raised index.

## The `z` half is not optional

`HJO.Mellit.not_exists_eventType_A_forall_move_lt_sweepTheta`
(`HJO/Shuffle/BraidTypeABelowThetaVacuous.lean`) shows that no component of a type-`A` event
has **all** of its moves below the puncture, which empties the regime in which
`HJO.Braid.specialBraid_eq_phiPlusStar_of_lt` applies to the whole braid. It does **not** say the
moves are all above: a component may have some moves below `θ` and some above, and then its braid
carries `z` letters. So the intertwiner is needed at all three letter kinds, and every
statement below about a word or a special braid carries no condition on which side of `θ` the moves
lie.

## Genericity

The exclusions are exactly `HJO.Sweep.braidRepMellit`'s — `q ≠ 0`, `q ≠ 1`, `q + 1 ≠ 0`,
`r * r = q` — because `π_k` does not exist without them, plus nothing. `q ≠ 0` is spent on the braid
inverses (`HJO.Sweep.braidInvEnd_mul_braidEnd`) and on `r^{-1}r = 1`, which needs `r ≠ 0` and gets
it from `q ≠ 0` and `r * r = q`.

**`u ≠ 0` is not spent, and no inverse in `u` is evaluated.** The `(qu)^{-1}` that
`HJO.Sweep.braidRep` puts on each `z` letter appears once on each side of the `z` diagram and is
never cancelled: `HJO.Sweep.dplus_zop` carries no scalar at all, and
`HJO.Sweep.zRepTotal_eq_smul_zop` strips the constant uniformly. The `(q-1)^{-1}` of
`HJO.Sweep.corner` never appears, and the `q^k/(1-q)` inside `HJO.Sweep.zopOneStar` is the same
value on both sides whatever it is. So no clause below is the degenerate identity between two zero
maps; the witness file `HJO/Shuffle/BraidRankRaiseWitness.lean` exhibits a nonzero value.

## What is here and what is not

`HJO.Mellit.braidValueOfData_succAbove_eq_dplus` is the type-`A` identity **at the level of the
special-braid data**: at a bottom insertion of a fixed point, the braid value of the inserted data
is `d^♭_+` of the braid value of the deleted data, with no condition on which side of `θ` the moves
lie. What is *not* done is the geometry: identifying a type-`A` event's two colourings with such a
pair `(w, β)` and `(w ∘ σ_j, β ∘ σ_j)`, which is what would turn this into the clause of
`HJO.Mellit.braidValueColouring_sweepRecursionsFloor` stated for `HJO.Mellit.braidValueColouring`.
That statement covers four clauses, and the type-`A` clause alone is not the whole of it.

## References

This file concerns `HJO.Mellit.braidValueColouring_sweepRecursionsFloor`,
`HJO.Mellit.Isolates.pointRank_le`, `HJO.Mellit.dsc_lo_eq_dplus_dsc_hi`,
`HJO.Sweep.braidRep_phiPlusStar_comp_negYOneDPlusStarPiece`, `HJO.Sweep.dplus_braid_succ`,
`HJO.Sweep.dplus_auxVar_one_mul`, `HJO.Sweep.starCommCM_cmDPlus`, `HJO.Braid.braidStep`,
`HJO.Braid.braidWord`, `HJO.Braid.specialBraid`, `HJO.Braid.braidYtilde`, `HJO.Sweep.braidRep`,
`HJO.Sweep.zop`, `HJO.Sweep.dplus`, `HJO.Braid.phiPlusStar`. Transcribing A. Mellit, *Toric braids
and `(m, n)`-parking functions*, section 5.
-/

@[expose] public section

namespace HJO.Sweep

open Braid

variable {L : Type*} [Field L] [Algebra ℚ L]

/-! ### The relation -/

/-- `d^♭_+` intertwines `X ∈ 𝔹^+_k(𝕋_0)` with `Y ∈ 𝔹^+_{k+1}(𝕋_0)`. -/
def DplusIntertwines (q u : L) (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) {r : L}
    (hr : r * r = q) (k : ℕ) (X : BraidMonoid k) (Y : BraidMonoid (k + 1)) : Prop :=
  ∀ x : pieceSub L k,
    ((braidRepMellit q u hq hq1 hqp hr (k + 1) Y
        ⟨dplus q k (x : Total L), dplus_mem_piece q k x.2⟩ : pieceSub L (k + 1)) : Total L)
      = dplus q k ((braidRepMellit q u hq hq1 hqp hr k X x : pieceSub L k) : Total L)

variable {q u : L} {hq : q ≠ 0} {hq1 : q ≠ 1} {hqp : q + 1 ≠ 0} {r : L} {hr : r * r = q} {k : ℕ}

/-- The relation from two `HJO.Sweep.RepresentedBy` readings and one operator identity. -/
theorem DplusIntertwines.of_representedBy {X : BraidMonoid k} {Y : BraidMonoid (k + 1)}
    {gX gY : Module.End L (Total L)}
    (hX : RepresentedBy q u r k (braidRepRespects_mellit q u hq hq1 hqp hr k) X gX)
    (hY : RepresentedBy q u r (k + 1)
      (braidRepRespects_mellit q u hq hq1 hqp hr (k + 1)) Y gY)
    (hcomm : gY * dplus q k = dplus q k * gX) :
    DplusIntertwines q u hq hq1 hqp hr k X Y := fun x => by
  rw [braidRepMellit, braidRepMellit, hY.apply, hX.apply]
  exact LinearMap.congr_fun hcomm (x : Total L)

/-- The same, when the operator identity is available only on the graded piece — which is what
`HJO.Sweep.starCommCM_cmDPlus` gives for the `z` letter. -/
theorem DplusIntertwines.of_representedBy_piece {X : BraidMonoid k} {Y : BraidMonoid (k + 1)}
    {gX gY : Module.End L (Total L)}
    (hX : RepresentedBy q u r k (braidRepRespects_mellit q u hq hq1 hqp hr k) X gX)
    (hY : RepresentedBy q u r (k + 1)
      (braidRepRespects_mellit q u hq hq1 hqp hr (k + 1)) Y gY)
    (hcomm : ∀ F ∈ piece L k, gY (dplus q k F) = dplus q k (gX F)) :
    DplusIntertwines q u hq hq1 hqp hr k X Y := fun x => by
  rw [braidRepMellit, braidRepMellit, hY.apply, hX.apply]
  exact hcomm (x : Total L) x.2

/-- The empty word is intertwined with the empty word, which is what an out-of-rank letter and the
empty train and the empty move sequence all reduce to. -/
theorem DplusIntertwines.one : DplusIntertwines q u hq hq1 hqp hr k 1 1 := fun x => by
  simp only [map_one, Module.End.one_apply]

/-- **The relation is multiplicative.** This is what lets it stand in for a homomorphism: the inner
factor's value already lies in `V_k`, so the outer one is read at it with no side condition. -/
theorem DplusIntertwines.mul {X X' : BraidMonoid k} {Y Y' : BraidMonoid (k + 1)}
    (hX : DplusIntertwines q u hq hq1 hqp hr k X Y)
    (hX' : DplusIntertwines q u hq hq1 hqp hr k X' Y') :
    DplusIntertwines q u hq hq1 hqp hr k (X * X') (Y * Y') := by
  intro x
  have h' : (braidRepMellit q u hq hq1 hqp hr (k + 1) Y'
      ⟨dplus q k (x : Total L), dplus_mem_piece q k x.2⟩ : pieceSub L (k + 1))
      = ⟨dplus q k ((braidRepMellit q u hq hq1 hqp hr k X' x : pieceSub L k) : Total L),
          dplus_mem_piece q k (braidRepMellit q u hq hq1 hqp hr k X' x).2⟩ :=
    Subtype.ext (hX' x)
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, h', hX]

/-- The relation transported along an identity of the rank-`(k+1)` braid. -/
theorem DplusIntertwines.congr {X : BraidMonoid k} {Y Y' : BraidMonoid (k + 1)}
    (hX : DplusIntertwines q u hq hq1 hqp hr k X Y) (h : Y = Y') :
    DplusIntertwines q u hq hq1 hqp hr k X Y' := by rw [← h]; exact hX

/-- The relation transported along an identity of the rank-`k` braid. -/
theorem DplusIntertwines.congr_left {X X' : BraidMonoid k} {Y : BraidMonoid (k + 1)}
    (hX : DplusIntertwines q u hq hq1 hqp hr k X Y) (h : X = X') :
    DplusIntertwines q u hq hq1 hqp hr k X' Y := by rw [← h]; exact hX

/-- A product along a list is intertwined with the corresponding product, which is how the words of
`HJO.Braid.trainUp` and `HJO.Braid.trainDown` are handled. -/
theorem DplusIntertwines.listProd {ι : Type*} {f : ι → BraidMonoid k}
    {g : ι → BraidMonoid (k + 1)} (l : List ι)
    (hl : ∀ i ∈ l, DplusIntertwines q u hq hq1 hqp hr k (f i) (g i)) :
    DplusIntertwines q u hq hq1 hqp hr k ((l.map f).prod) ((l.map g).prod) := by
  induction l with
  | nil => simpa only [List.map_nil, List.prod_nil] using DplusIntertwines.one
  | cons i t ih =>
    simp only [List.map_cons, List.prod_cons]
    exact (hl i (List.mem_cons_self ..)).mul (ih fun j hj => hl j (List.mem_cons_of_mem _ hj))

/-! ### The `T` and `T̄` letters -/

/-- The `T` letter, at every index, in rank and out of it. -/
theorem dplusIntertwines_braidGenT {i : ℕ} (hi : 1 ≤ i) :
    DplusIntertwines q u hq hq1 hqp hr k (braidGenT k i) (braidGenT (k + 1) (i + 1)) := by
  by_cases hik : i + 1 ≤ k
  · refine DplusIntertwines.of_representedBy (representedBy_braidGenT hi hik)
      (representedBy_braidGenT (by omega) (by omega)) ?_
    rw [smul_mul_assoc, mul_smul_comm, dplus_mul_braidEnd_succ q hi hik]
  · rw [braidGenT_of_lt (by omega), braidGenT_of_lt (by omega)]
    exact DplusIntertwines.one

/-- The `T̄` letter: the inverse of the `T` relation, which is where `q ≠ 0` is spent. -/
theorem dplusIntertwines_braidGenTinv {i : ℕ} (hi : 1 ≤ i) :
    DplusIntertwines q u hq hq1 hqp hr k (braidGenTinv k i) (braidGenTinv (k + 1) (i + 1)) := by
  by_cases hik : i + 1 ≤ k
  · refine DplusIntertwines.of_representedBy (representedBy_braidGenTinv hi hik)
      (representedBy_braidGenTinv (by omega) (by omega)) ?_
    have key : braidInvEnd q (i + 1) * dplus q k = dplus q k * braidInvEnd q i := by
      refine LinearMap.ext fun F => ?_
      have hF : braidEnd q i (braidInvEnd q i F) = F :=
        LinearMap.congr_fun (braidEnd_mul_braidInvEnd q hq i) F
      have h2 : braidEnd q (i + 1) (dplus q k (braidInvEnd q i F)) = dplus q k F := by
        have h3 := LinearMap.congr_fun (dplus_mul_braidEnd_succ q hi hik) (braidInvEnd q i F)
        rw [Module.End.mul_apply, Module.End.mul_apply, hF] at h3
        exact h3.symm
      have h4 := LinearMap.congr_fun (braidInvEnd_mul_braidEnd q hq (i + 1))
        (dplus q k (braidInvEnd q i F))
      rw [Module.End.mul_apply, Module.End.one_apply] at h4
      rw [Module.End.mul_apply, Module.End.mul_apply, ← h2, h4]
    rw [smul_mul_assoc, mul_smul_comm, key]
  · rw [braidGenTinv_of_not_inRank (by simp only [Letter.InRank]; omega),
      braidGenTinv_of_not_inRank (by simp only [Letter.InRank]; omega)]
    exact DplusIntertwines.one

/-! ### The `y_1` letter: the extra `T_1` -/

/-- **`d^♭_+` sends `y_1` to `T_1y_1T̄_1` and not to `y_2`.** This is
`HJO.Sweep.dplus_auxVar_one_mul` read as a rank raise, and the `T_1` in front is exactly the letter
that `HJO.Braid.phiPlusStar_braidYtilde_one` has as a `T̄_1`. -/
theorem dplusIntertwines_braidGenY (hk : 1 ≤ k) :
    DplusIntertwines q u hq hq1 hqp hr k (braidGenY k 1)
      (braidGenT (k + 1) 1 * braidGenY (k + 1) 1 * braidGenTinv (k + 1) 1) := by
  have hr0 : r ≠ 0 := fun h => hq (by rw [← hr, h, mul_zero])
  refine DplusIntertwines.of_representedBy (representedBy_braidGenY hk)
    (((representedBy_braidGenT (K := k + 1) (le_refl 1) (by omega)).mul
      (representedBy_braidGenY (by omega))).mul
      (representedBy_braidGenTinv (le_refl 1) (by omega))) ?_
  refine LinearMap.ext fun F => ?_
  simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.neg_apply,
    LinearMap.mulLeft_apply, mul_smul_comm, map_neg, smul_neg, smul_smul,
    mul_inv_cancel₀ hr0, one_smul, braidEnd, braidInvEnd, LinearMap.restrictScalars_apply]
  rw [dplus_auxVar_one_mul q hq hk F]

/-! ### The trains -/

/-- An ascending word is intertwined with the ascending word one index up, given the letters. This
is `HJO.Braid.map_ascendingWord` for the relation rather than for a homomorphism. -/
theorem dplusIntertwines_ascendingWord {T : ℕ → BraidMonoid k} {T' : ℕ → BraidMonoid (k + 1)}
    (hT : ∀ j, 1 ≤ j → DplusIntertwines q u hq hq1 hqp hr k (T j) (T' (j + 1))) {a b : ℕ}
    (ha : 1 ≤ a) :
    DplusIntertwines q u hq hq1 hqp hr k (ascendingWord T a b)
      (ascendingWord T' (a + 1) (b + 1)) := by
  rw [ascendingWord, ascendingWord, show b + 1 - (a + 1) = b - a from by omega,
    ← map_range'_succ a (b - a), List.map_map]
  refine DplusIntertwines.listProd _ fun j hj => ?_
  rw [List.mem_range'_1] at hj
  exact hT j (by omega)

/-- A descending word is intertwined with the descending word one index up. -/
theorem dplusIntertwines_descendingWord {T : ℕ → BraidMonoid k} {T' : ℕ → BraidMonoid (k + 1)}
    (hT : ∀ j, 1 ≤ j → DplusIntertwines q u hq hq1 hqp hr k (T j) (T' (j + 1))) {a b : ℕ}
    (hb : 1 ≤ b) :
    DplusIntertwines q u hq hq1 hqp hr k (descendingWord T a b)
      (descendingWord T' (a + 1) (b + 1)) := by
  rw [descendingWord, descendingWord, show a + 1 - (b + 1) = a - b from by omega,
    ← map_range'_succ b (a - b), ← List.map_reverse, List.map_map]
  refine DplusIntertwines.listProd _ fun j hj => ?_
  rw [List.mem_reverse, List.mem_range'_1] at hj
  exact hT j (by omega)

/-- **Both indices of a descending train rise by one.** -/
theorem dplusIntertwines_braidTrainDown {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    DplusIntertwines q u hq hq1 hqp hr k (braidTrainDown k a b)
      (braidTrainDown (k + 1) (a + 1) (b + 1)) := by
  change DplusIntertwines q u hq hq1 hqp hr k (trainDown _ _ a b)
    (trainDown _ _ (a + 1) (b + 1))
  unfold trainDown
  split_ifs with h h' h'
  · exact dplusIntertwines_descendingWord (fun j hj => dplusIntertwines_braidGenT hj) hb
  · omega
  · omega
  · exact dplusIntertwines_ascendingWord (fun j hj => dplusIntertwines_braidGenTinv hj) ha

/-- **Both indices of an ascending train rise by one.** -/
theorem dplusIntertwines_braidTrainUp {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    DplusIntertwines q u hq hq1 hqp hr k (braidTrainUp k a b)
      (braidTrainUp (k + 1) (a + 1) (b + 1)) := by
  change DplusIntertwines q u hq hq1 hqp hr k (trainUp _ _ a b)
    (trainUp _ _ (a + 1) (b + 1))
  unfold trainUp
  split_ifs with h h' h'
  · exact dplusIntertwines_ascendingWord (fun j hj => dplusIntertwines_braidGenT hj) ha
  · omega
  · omega
  · exact dplusIntertwines_descendingWord (fun j hj => dplusIntertwines_braidGenTinv hj) hb

/-! ### The four trains `ỹ` is built from -/

/-- `T_{a↘1}` against `T_{a+1↘2}`, the outer train of `HJO.Braid.braidYtilde`. -/
theorem dplusIntertwines_braidTrainDown_one {a : ℕ} (ha : 1 ≤ a) :
    DplusIntertwines q u hq hq1 hqp hr k (braidTrainDown k a 1)
      (braidTrainDown (k + 1) (a + 1) 2) :=
  dplusIntertwines_braidTrainDown ha (le_refl 1)

/-- `T_{1↗a}` against `T_{2↗a+1}`, the other outer train of `HJO.Braid.braidYtilde`. -/
theorem dplusIntertwines_braidTrainUp_one {a : ℕ} (ha : 1 ≤ a) :
    DplusIntertwines q u hq hq1 hqp hr k (braidTrainUp k 1 a)
      (braidTrainUp (k + 1) 2 (a + 1)) :=
  dplusIntertwines_braidTrainUp (le_refl 1) ha

/-- `T_{1↘k}` against `T_{2↘k+1}`, the first half of the loop `Λ̄_1`. Both indices rise, and the
top one rises because the *rank* rises: this is the step that has no analogue for a map defined on
the generators. -/
theorem dplusIntertwines_braidTrainDown_top (hk : 1 ≤ k) :
    DplusIntertwines q u hq hq1 hqp hr k (braidTrainDown k 1 k)
      (braidTrainDown (k + 1) 2 (k + 1)) :=
  dplusIntertwines_braidTrainDown (le_refl 1) hk

/-- `T_{k↗1}` against `T_{k+1↗2}`, the second half of the loop `Λ̄_1`. -/
theorem dplusIntertwines_braidTrainUp_top (hk : 1 ≤ k) :
    DplusIntertwines q u hq hq1 hqp hr k (braidTrainUp k k 1)
      (braidTrainUp (k + 1) (k + 1) 2) :=
  dplusIntertwines_braidTrainUp hk (le_refl 1)

end HJO.Sweep

namespace HJO.Braid

variable {k : ℕ}

/-! ### The two shapes of `ỹ` the intertwiner compares -/

/-- **`ỹ_a` split into the four trains and `y_1`.** `HJO.Braid.braidTrainDown_mul_braidYtilde` at
the base `1` followed by `HJO.Braid.braidYtilde_one_eq`, with the loop `Λ̄_1` written out. -/
theorem braidYtilde_eq_trainDown_mul_genY_mul_loop (hk : 1 ≤ k) {a : ℕ} (ha : 1 ≤ a)
    (hak : a ≤ k) :
    braidYtilde k a = braidTrainDown k a 1 *
      (braidGenY k 1 * (braidTrainDown k 1 k * braidTrainUp k k 1)) * braidTrainUp k 1 a := by
  rw [braidYtilde_eq_trainDown_one_mul ha hak, braidYtilde_one_eq hk, braidLoopInv, mul_assoc]

/-- **`ỹ_{a+1}` at rank `k+1` is the letterwise raise of that split.** Every index rises by one
and the `y_1` becomes `T_1y_1T̄_1`: the head letter `T_1` of the descending train and the head
letter `T_1` of the ascending train are pulled out of `T_{a+1↘1}` and `T_{1↗a+1}`, the `T̄_1` of the
loop's two ends is likewise pulled out, and the trailing `T̄_1T_1` cancels.

Against `HJO.Braid.phiPlusStar_braidYtilde_one` this is the whole difference between the rank raise
and `HJO.Braid.phiPlusStar`: there the middle letter is `T̄_1`, here it is `T_1`. -/
theorem braidYtilde_succ_eq_raise {a : ℕ} (ha : 1 ≤ a) (hak : a ≤ k) :
    braidYtilde (k + 1) (a + 1) = braidTrainDown (k + 1) (a + 1) 2 *
      ((braidGenT (k + 1) 1 * braidGenY (k + 1) 1 * braidGenTinv (k + 1) 1) *
        (braidTrainDown (k + 1) 2 (k + 1) * braidTrainUp (k + 1) (k + 1) 2)) *
      braidTrainUp (k + 1) 2 (a + 1) := by
  have hsys := isBraidSystem_braidGenT (k + 1)
  have hD1 : braidTrainDown (k + 1) (a + 1) 2 * braidGenT (k + 1) 1
      = braidTrainDown (k + 1) (a + 1) 1 :=
    trainDown_two_mul_gen hsys (by omega) (by omega)
  have hU1 : braidGenT (k + 1) 1 * braidTrainUp (k + 1) 2 (a + 1)
      = braidTrainUp (k + 1) 1 (a + 1) := by
    have hglue := trainUp_mul_trainUp (T := braidGenT (k + 1)) (Tinv := braidGenTinv (k + 1))
      hsys (a := 1) (b := 2) (c := a + 1) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)
    have h12 : trainUp (braidGenT (k + 1)) (braidGenTinv (k + 1)) 1 2 = braidGenT (k + 1) 1 :=
      trainUp_self_succ _ _ 1
    rwa [h12] at hglue
  have hD2 : braidGenTinv (k + 1) 1 * braidTrainDown (k + 1) 2 (k + 1)
      = braidTrainDown (k + 1) 1 (k + 1) := by
    have hglue := trainDown_mul_trainDown (T := braidGenT (k + 1)) (Tinv := braidGenTinv (k + 1))
      hsys (a := 1) (b := 2) (c := k + 1) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)
    have h12 : trainDown (braidGenT (k + 1)) (braidGenTinv (k + 1)) 1 2
        = braidGenTinv (k + 1) 1 := trainDown_self_succ _ _ 1
    rwa [h12] at hglue
  have hU2 : braidTrainUp (k + 1) (k + 1) 2 * braidGenTinv (k + 1) 1
      = braidTrainUp (k + 1) (k + 1) 1 := by
    have hglue := trainUp_mul_trainUp (T := braidGenT (k + 1)) (Tinv := braidGenTinv (k + 1))
      hsys (a := k + 1) (b := 2) (c := 1) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)
    have h21 : trainUp (braidGenT (k + 1)) (braidGenTinv (k + 1)) 2 1
        = braidGenTinv (k + 1) 1 := trainUp_succ_self _ _ 1
    rwa [h21] at hglue
  have hTT : braidGenTinv (k + 1) 1 * braidGenT (k + 1) 1 = 1 :=
    braidGenT_inv_mul (le_refl 1) (by omega)
  rw [braidYtilde_eq_trainDown_mul_genY_mul_loop (by omega) (show 1 ≤ a + 1 by omega)
      (by omega), ← hD1, ← hU1, ← hD2, ← hU2]
  simp only [mul_assoc]
  rw [mul_mul_cancel_of_mul_eq_one hTT]

end HJO.Braid

namespace HJO.Sweep

open Braid

variable {L : Type*} [Field L] [Algebra ℚ L]
variable {q u : L} {hq : q ≠ 0} {hq1 : q ≠ 1} {hqp : q + 1 ≠ 0} {r : L} {hr : r * r = q} {k : ℕ}

/-! ### The `ỹ` letter -/

/-- **`d^♭_+` intertwines `ỹ_a` with `ỹ_{a+1}`**, the `ỹ` half of the rank raise. -/
theorem dplusIntertwines_braidYtilde (hk : 1 ≤ k) {a : ℕ} (ha : 1 ≤ a) (hak : a ≤ k) :
    DplusIntertwines q u hq hq1 hqp hr k (braidYtilde k a) (braidYtilde (k + 1) (a + 1)) := by
  refine (((dplusIntertwines_braidTrainDown_one ha).mul
    ((dplusIntertwines_braidGenY hk).mul
      ((dplusIntertwines_braidTrainDown_top hk).mul
        (dplusIntertwines_braidTrainUp_top hk)))).mul
    (dplusIntertwines_braidTrainUp_one ha)).congr_left ?_ |>.congr ?_
  · exact (braidYtilde_eq_trainDown_mul_genY_mul_loop hk ha hak).symm
  · exact (braidYtilde_succ_eq_raise ha hak).symm

/-! ### The `z` letter -/

/-- `π_k(z_i) = (qu)^{-1}z_i` for `1 ≤ i ≤ k`, in the form `HJO.Sweep.RepresentedBy` asks for. -/
theorem representedBy_braidGenZ_of_le {i : ℕ} (hi : 1 ≤ i) (hik : i ≤ k) :
    RepresentedBy q u r k (braidRepRespects_mellit q u hq hq1 hqp hr k) (braidGenZ k i)
      ((q * u)⁻¹ • zop q u k i) := fun x => by
  rw [braidRep_z, coe_zRep, zRepTotal_eq_smul_zop q u hr i hi hik, LinearMap.smul_apply]

/-- **`d^♭_+` intertwines `z_i` with `z_{i+1}`**, the `z` half of the rank raise.

This is `HJO.Sweep.dplus_zop` (`HJO.Sweep.starCommCM_cmDPlus` in the convention `HJO.Sweep.zop` is
written in), which carries **no scalar on either side**, so the `(qu)^{-1}` of
`HJO.Sweep.braidRep`'s `z` letter is the same constant on the two sides of the diagram and is never
inverted: **`u ≠ 0` is not spent**. The prediction that the `z` letters would force it and evaluate
`(qu)^{-1}` is wrong for the same reason it was wrong for the prefactor — the letters are
transported, not computed.

Unlike the `ỹ` letter, no train assembly is needed: `HJO.Braid.braidGenZ` *is* the letter of
`HJO.Braid.braidStep` at the raised index. -/
theorem dplusIntertwines_braidGenZ {i : ℕ} (hi : 1 ≤ i) (hik : i ≤ k) :
    DplusIntertwines q u hq hq1 hqp hr k (braidGenZ k i) (braidGenZ (k + 1) (i + 1)) := by
  refine DplusIntertwines.of_representedBy_piece
    (representedBy_braidGenZ_of_le (hq := hq) (hq1 := hq1) (hqp := hqp) (hr := hr) hi hik)
    (representedBy_braidGenZ_of_le (hq := hq) (hq1 := hq1) (hqp := hqp) (hr := hr)
      (show 1 ≤ i + 1 by omega) (show i + 1 ≤ k + 1 by omega)) fun F hF => ?_
  rw [LinearMap.smul_apply, LinearMap.smul_apply, map_smul, dplus_zop q u hq hi hik hF]

/-! ### One move of a bottom insertion -/

variable {θ : ℚ}

/-- **`d^♭_+` intertwines one retained move with the same move of the inserted data**, whichever
side of the puncture the moving entry is on. `HJO.Braid.braidStep_succAbove_of_forall_lt` says the
inserted letter is the deleted one with every index raised by one, and each kind of index the letter
carries — the two ends of the descending train and the index of the `z` or the `ỹ` — is
intertwined. The `z` branch reads `HJO.Sweep.dplusIntertwines_braidGenZ` and the `ỹ` branch
`HJO.Sweep.dplusIntertwines_braidYtilde`. -/
theorem dplusIntertwines_braidStep_succAbove (hk : 1 ≤ k) {w : Fin (k + 1) → ℚ} {j : Fin (k + 1)}
    {t₀ : Fin k} (hmin : ∀ t : Fin k, w j < w (j.succAbove t))
    (hafter : w j < nextCrossing θ (w (j.succAbove t₀))) :
    DplusIntertwines q u hq hq1 hqp hr k (braidStep θ (w ∘ j.succAbove) t₀)
      (braidStep θ w (j.succAbove t₀)) := by
  have hp1 : 1 ≤ entryRank (moveOne θ (w ∘ j.succAbove) t₀) t₀ := entryRank_pos _ _
  have hp2 : 1 ≤ entryRank (w ∘ j.succAbove) t₀ := entryRank_pos _ _
  have hle : entryRank (w ∘ j.succAbove) t₀ ≤ k := entryRank_le _ _
  by_cases hθ : (w ∘ j.succAbove) t₀ < θ
  · refine ((dplusIntertwines_braidTrainDown hp1 hp2).mul
      (dplusIntertwines_braidGenZ hp2 hle)).congr_left ?_ |>.congr ?_
    · rw [braidStep, ite_eq_left_of_eq_true _ _ (eq_true hθ)]
    · rw [braidStep_succAbove_of_forall_lt hmin hafter, ite_eq_left_of_eq_true _ _ (eq_true hθ)]
  · refine ((dplusIntertwines_braidTrainDown hp1 hp2).mul
      (dplusIntertwines_braidYtilde hk hp2 hle)).congr_left ?_ |>.congr ?_
    · rw [braidStep, ite_eq_right_of_eq_false _ _ (eq_false hθ)]
    · rw [braidStep_succAbove_of_forall_lt hmin hafter, ite_eq_right_of_eq_false _ _ (eq_false hθ)]

/-! ### A whole sequence of moves -/

/-- **`d^♭_+` intertwines the braid of a sequence of retained moves with the braid of the same
sequence in the inserted data.** The only hypothesis is that the inserted entry stays the strict
minimum, read at every suffix, which is what the induction consumes; the inserted entry is never
moved (`HJO.Braid.moveTuple_map_succAbove_self`), so the minimality clause at the suffix `t₀ :: lt`
is the statement that the move at `t₀` leaves it minimal.

Against `HJO.Braid.braidWord_map_succAbove_eq_phiPlusStar_of_lt`, which is the same bookkeeping for
`HJO.Braid.phiPlusStar` and is available only below the puncture, this carries **no** condition on
which side of `θ` the moves are. -/
theorem dplusIntertwines_braidWord_map_succAbove (hk : 1 ≤ k) (j : Fin (k + 1))
    (w : Fin (k + 1) → ℚ) :
    ∀ l : List (Fin k),
      (∀ lt, lt <:+ l → ∀ t : Fin k, moveTuple θ w (lt.map j.succAbove) j
          < moveTuple θ w (lt.map j.succAbove) (j.succAbove t)) →
      DplusIntertwines q u hq hq1 hqp hr k (braidWord θ (w ∘ j.succAbove) l)
        (braidWord θ w (l.map j.succAbove)) := by
  intro l
  induction l with
  | nil => intro _; simpa only [List.map_nil, braidWord_nil] using DplusIntertwines.one
  | cons t₀ l ih =>
    intro hmin
    have hsuf : l <:+ t₀ :: l := List.suffix_cons t₀ l
    have ihl := ih fun lt hlt => hmin lt (hlt.trans hsuf)
    have hafter : moveTuple θ w (l.map j.succAbove) j
        < nextCrossing θ (moveTuple θ w (l.map j.succAbove) (j.succAbove t₀)) := by
      have h := hmin (t₀ :: l) (List.suffix_refl _) t₀
      rw [List.map_cons, moveTuple_cons, moveOne_of_ne θ _ (Ne.symm (j.succAbove_ne t₀)),
        moveOne_self] at h
      exact h
    have hstep := dplusIntertwines_braidStep_succAbove (q := q) (u := u) (hq := hq) (hq1 := hq1)
      (hqp := hqp) (hr := hr) hk (w := moveTuple θ w (l.map j.succAbove)) (j := j) (t₀ := t₀)
      (hmin l hsuf) hafter
    rw [moveTuple_comp_succAbove] at hstep
    rw [List.map_cons, braidWord_cons, braidWord_cons]
    exact hstep.mul ihl

/-! ### The special braid of a bottom insertion -/

/-- **`d^♭_+` intertwines the special braid of the deleted data with the special braid of the
inserted data**, at a bottom insertion of a fixed point. The inserted index has multiplicity `1`, so
`HJO.Braid.specialMoveList_eq_map_succAbove` identifies the two sequences of moves. -/
theorem dplusIntertwines_specialBraid (hk : 1 ≤ k) (j : Fin (k + 1)) (w : Fin (k + 1) → ℚ)
    (β : Fin (k + 1) → ℕ) (hβj : β j = 1)
    (hmin : ∀ lt, lt <:+ specialMoveList (β ∘ j.succAbove) → ∀ t : Fin k,
      moveTuple θ w (lt.map j.succAbove) j
        < moveTuple θ w (lt.map j.succAbove) (j.succAbove t)) :
    DplusIntertwines q u hq hq1 hqp hr k (specialBraid θ (w ∘ j.succAbove) (β ∘ j.succAbove))
      (specialBraid θ w β) := by
  rw [specialBraid, specialBraid, specialMoveList_eq_map_succAbove j β hβj]
  exact dplusIntertwines_braidWord_map_succAbove hk j w _ hmin

end HJO.Sweep

namespace HJO.Mellit

open ParkingFunctions Paths Sweep Braid

variable {L : Type*} [Field L] [Algebra ℚ L]
variable {q u : L} {hq : q ≠ 0} {hq1 : q ≠ 1} {hqp : q + 1 ≠ 0} {r : L} {hr : r * r = q} {k : ℕ}

/-! ### The braid value of a bottom insertion above the puncture -/

/-- **THE TYPE-`A` IDENTITY AT THE LEVEL OF THE SPECIAL-BRAID DATA.** At a bottom insertion of a
fixed point whose retained moves all lie above the puncture, the braid value of the inserted data
is `d^♭_+` of the braid value of the deleted data:

`D(w, β) = d^♭_+(D(w ∘ σ_j, β ∘ σ_j))`.

Both halves of `HJO.Mellit.braidValueOfData` transform: the prefactor
`q^{(inv_fin − inv_ini)/2}` is unchanged (`HJO.Braid.invFin_sub_invIni_of_forall_lt`), and the
braid itself is intertwined letter by letter
(`HJO.Sweep.dplusIntertwines_specialBraid`), the vacuum tower being
`d_+^{k+1}(1) = d^♭_+(d_+^k(1))` by `HJO.Sweep.dplusIter`'s own recursion.

This is the operator identity the type-`A` clause of
`HJO.Mellit.braidValueColouring_sweepRecursionsFloor` needs above `θ`, stated for the data rather
than for a colouring; what is *not* done here is the identification of a type-`A` event's two
colourings with such a pair `(w, β)` and `(w ∘ σ_j, β ∘ σ_j)`. -/
theorem braidValueOfData_succAbove_eq_dplus (hk : 1 ≤ k) (a b N : ℕ) (j : Fin (k + 1))
    (w : Fin (k + 1) → ℚ) (β : Fin (k + 1) → ℕ) (hβj : β j = 1)
    (hini : ∀ t : Fin k, w j < w (j.succAbove t))
    (hfin : ∀ t : Fin k, w j < (nextCrossing (sweepTheta a b N))^[β (j.succAbove t) - 1]
      (w (j.succAbove t)))
    (hmin : ∀ lt, lt <:+ specialMoveList (β ∘ j.succAbove) → ∀ t : Fin k,
      moveTuple (sweepTheta a b N) w (lt.map j.succAbove) j
        < moveTuple (sweepTheta a b N) w (lt.map j.succAbove) (j.succAbove t)) :
    braidValueOfData q u hq hq1 hqp hr a b N w β
      = dplus q k (braidValueOfData q u hq hq1 hqp hr a b N (w ∘ j.succAbove)
          (β ∘ j.succAbove)) := by
  have hvac : (dplusIterPiece q (k + 1) : pieceSub L (k + 1))
      = ⟨dplus q k ((dplusIterPiece q k : pieceSub L k) : Total L),
          dplus_mem_piece q k (dplusIterPiece q k).2⟩ := Subtype.ext rfl
  have hkey := dplusIntertwines_specialBraid (q := q) (u := u) (hq := hq) (hq1 := hq1)
    (hqp := hqp) (hr := hr) (θ := sweepTheta a b N) hk j w β hβj hmin (dplusIterPiece q k)
  rw [braidValueOfData, braidValueOfData,
    invFin_sub_invIni_of_forall_lt j w β hβj hini hfin, map_smul, hvac, hkey]

end HJO.Mellit

end
