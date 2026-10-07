/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidRankRaise
public import HJO.Shuffle.SweepWidthThreeFour
public import HJO.CMStructure.VmodActionMod
public meta import HJO.Attr

/-! # The intertwiner of `d^♭_-` with the braid rank lowering, and what it cannot reach

`HJO.Sweep.DplusIntertwines` (`HJO/Shuffle/BraidRankRaise.lean`) is the raising intertwiner
that closes the type-`A` clause of the level recursion at the level of the special-braid data
(`HJO.Mellit.braidValueOfData_succAbove_eq_dplus`). Rule `BE` of Mellit's Theorem 4.2 carries
`d^♭_-` instead, and `HJO.Mellit.Isolates.braidValueColouring_eq_dminus_add_smul_of_move` reduces
that rule at one bracketed point to a single identity `hmove` between braid values, for which there
is no ready-made `d_-` counterpart of `HJO.Sweep.dplusIntertwines_specialBraid`.

This file builds the counterpart, as far as it exists, and shows **exactly where it stops** — which
is much earlier than the raising side, and early enough that the counterpart alone cannot discharge
`hmove`.

## The relation, and why it is an equal-index relation

`d^♭_-` maps `V_{k+1}` to `V_k`, so the relation compares a rank-`(k+1)` braid with a rank-`k`
braid: `HJO.Sweep.DminusIntertwines q u … k X Y` says
`d^♭_-∘π_{k+1}(X) = π_k(Y)∘d^♭_-`. It is multiplicative (`HJO.Sweep.DminusIntertwines.mul`) for
the same reason the raising one is — the inner factor's value already lies in the piece the outer
one is read on — so it assembles along words and trains exactly as a homomorphism would.

Unlike the raise, the index does **not** move: `T_i ↦ T_i`, `T̄_i ↦ T̄_i`, `y_1 ↦ y_1`. The three
operator identities are already available and have the *same* index range in each case:

* `T_i` — `HJO.Sweep.dminus_mul_braidEnd` (`HJO.Sweep.dminusCM_braid` for `HJO.Sweep.dminus`),
  valid for `i + 1 ≤ k`;
* `T̄_i` — `HJO.Sweep.dminus_mul_braidInvEnd`, the same range;
* `y_1` — `HJO.Sweep.dminus_auxVar_mul` at `j = 1`, which needs `1 ≤ k`.

## The two places it stops, and neither is slack

**The top index `T_k`.** At rank `k + 1` the letters `T_k`, `T̄_k` are in rank; at rank `k` they are
not. And `d^♭_-` genuinely does not commute with `T_k` on `V_{k+1}`: the extraction of `d^♭_-` reads
the variable `y_{k+1}`, which is one of the two variables `T_k` moves. The docstring of
`HJO/CMStructure/DminusBraid.lean` records that the index bound there is exact and the
statement false at the next index. So `HJO.Sweep.dminusIntertwines_braidGenT` asks `i + 1 ≤ k` and
`HJO.Sweep.dminusIntertwines_braidGenT_of_lt` disposes of `k + 1 ≤ i`, where both letters are out of
rank; the single index `i = k` is open, and it is open because the identity is false there.

**The `z` letter.** `HJO.Sweep.dplusIntertwines_braidGenZ` rests on `HJO.Sweep.dplus_zop`
(`HJO.Sweep.starCommCM_cmDPlus` in the convention `HJO.Sweep.zop` is written in). There is no
`d^♭_-` analogue of that lemma, and it is not the same statement read backwards:
`HJO.Sweep.zopOneStar` carries the rank-dependent prefactor `q^k/(1-q)`, so the two sides of any
such diagram differ by a factor `q` before anything is computed, and `z_1` on `V_{k+1}` is written
with the train `T^*_{(k+1)↘1} = T̄_1⋯T̄_k`, whose top letter is exactly the one `d^♭_-` does not
commute with (`HJO.Sweep.dminus_mul_trainUpEnd_star` reaches only `T^*_{k↘1}`).
`HJO.Sweep.dminusIntertwines_braidGenZ_of_zop` therefore states the letter *conditionally on* that
missing operator identity.

**The `ỹ` letter, as a consequence of the first.** `HJO.Braid.braidYtilde (k+1) a` contains the loop
`Λ̄_1 = T_{1↘k+1}T_{k+1↗1}`, whose letters run up to index `k`
(`HJO.Sweep.dminusIntertwines_braidTrainDown` asks `max a b ≤ k`). So at rank `k + 1` the loop is
out of reach and the `ỹ` letter is not intertwined letterwise either. Since every *move* of
`HJO.Braid.braidStep` contributes a `z` or a `ỹ`, the outcome is that **no move-letter of a
rank-`(k+1)` special braid is intertwined by this relation**; what is intertwined is the trains, at
indices below `k`.

## The vacuum tower is not preserved: `d^♭_-(d_+^{k+1}(1)) = e_1·d_+^k(1)`

`HJO.Sweep.dminus_dplusIter` evaluates the one remaining ingredient, and the answer is not the
vacuum. `HJO.Mellit.braidValueOfData` applies `π_k` to `HJO.Sweep.dplusIterPiece`, and where the
raising side had `d_+^{k+1}(1) = d^♭_+(d_+^k(1))` on the nose, here

`d^♭_-(d_+^{k+1}(1)) = e_1·d_+^k(1)`,

an extra factor of the first elementary symmetric function. (This is
`HJO.Sweep.dminusCM_cmDPlus_C` — `d_-d_+ = e_1` — at every rank rather than only on `V_0`, and for
the modified pair `HJO.Sweep.dminus`/`HJO.Sweep.dplus` rather than the Carlsson--Mellit pair;
`HJO.Sweep.dminusCM_cmDPlus_C` itself is the rank-`0` Carlsson--Mellit statement.) It is proved
from the closed form `HJO.Sweep.dminus_auxVarProd`.

So `HJO.Sweep.dminus_braidValueOfData_of_dminusIntertwines` — the bridge a completed intertwiner
would feed — produces `π_k(Y)` applied to `e_1·d_+^k(1)`, packaged as
`HJO.Sweep.braidValueElemSymmOfData`, and that is not a `HJO.Mellit.braidValueOfData` at all. The
`e_1` cannot be pulled out in general: the braid operators are `Λ`-linear on the `T` and `y` letters
but the `z` letter is built from `HJO.Sweep.dplusStar`, which acts on the alphabet.

## What this says about `hmove`

Together with `HJO/Shuffle/BraidTypeBMoveCount.lean`, which shows the rank-`k` special braid of
a type-`B` event carries **two more moves** than the rank-`(k+1)` one, the conclusion is that
`hmove` is not of the type-`A` shape: it is not the statement that one special braid is the
letterwise image of the other under a lowering map. No amount of the relation built here closes it.
That is a statement about the shape of the obligation, not about its truth. The floored rule-`BE`
clause is proved by another route, the cut of `HJO/Shuffle/BraidBECut.lean`, as
`HJO.Mellit.braidValueColouring_sweepRecursionBEFloor`.

## Genericity

The exclusions are `HJO.Sweep.braidRepMellit`'s and nothing more: `q ≠ 0`, `q ≠ 1`, `q + 1 ≠ 0`,
`r * r = q`. No inverse in `u` is evaluated anywhere below — the `(qu)^{-1}` of
`HJO.Sweep.braidRep`'s `z` letter appears on both sides of the conditional `z` clause and is never
cancelled — and no `(q-1)^{-1}` is reached, so no clause here is an identity between two zero maps
at a bad parameter.

**This file closes no clause of the level recursion.**
`HJO.Mellit.braidValueColouring_sweepRecursionsFloor` covers the whole level recursion and this
file closes none of its clauses; it is proved as
`HJO.Mellit.braidValueColouring_sweepRecursionsFloor` (`HJO/Shuffle/MellitThm58Closed.lean`),
its `BE` and unswept floored clauses being `HJO.Mellit.braidValueColouring_sweepRecursionBEFloor`
(`HJO/Shuffle/BraidBECut.lean`) and `HJO.Mellit.braidValueColouring_sweepRecursionUnsweptFloor`
(`HJO/Shuffle/BraidUnsweptFloor.lean`). `HJO.Sweep.starCommCM_cmDPlus` is the raising lemma and is
not restated here.

## References

A. Mellit, *Toric braids and `(m, n)`-parking functions*, Sections 4 and 5, and E. Carlsson and A.
Mellit, *A proof of the shuffle conjecture*, Section 5.
-/

@[expose] public section

namespace HJO.Sweep

open Braid

variable {L : Type*} [Field L] [Algebra ℚ L]

/-! ### `d^♭_-` on the vacuum tower -/

/-- **`d^♭_-(d_+^{k+1}(1)) = e_1·d_+^k(1)`.** The vacuum tower `HJO.Sweep.dplusIter` is *not*
preserved by the lowering operator: it picks up the first elementary symmetric function.

`HJO.Sweep.dminusCM_cmDPlus_C` at every rank and for the modified lowering operator of
`HJO.Sweep.dminus`, where `HJO.Sweep.dminusCM_cmDPlus_C` itself is the rank-`0` statement for
the Carlsson--Mellit pair. The proof is the closed form
`HJO.Sweep.dminus_auxVarProd` — `d^♭_-(y_1⋯y_{k+1}) = -e_1y_1⋯y_k` — read through
`HJO.Sweep.dplusIter_eq_smul_auxVarProd`, whose sign `(-1)^{k+1}` cancels the one in front of
`e_1`. -/
theorem dminus_dplusIter (q : L) (k : ℕ) :
    dminus q (k + 1) (dplusIter q (k + 1))
      = MvPolynomial.C (Sym.elemSymm L 1) * dplusIter q k := by
  rw [dplusIter_eq_smul_auxVarProd, dplusIter_eq_smul_auxVarProd, map_smul, dminus_auxVarProd,
    smul_neg, pow_succ, mul_comm ((-1 : L) ^ k) (-1), neg_one_mul, neg_smul, neg_neg,
    mul_smul_comm]

/-- `HJO.Sweep.dminus_dplusIter` read on the graded piece, the shape
`HJO.Mellit.braidValueOfData` presents the vacuum in. -/
theorem dminus_dplusIterPiece (q : L) (k : ℕ) :
    dminus q (k + 1) ((dplusIterPiece q (k + 1) : pieceSub L (k + 1)) : Total L)
      = MvPolynomial.C (Sym.elemSymm L 1) * ((dplusIterPiece q k : pieceSub L k) : Total L) := by
  rw [coe_dplusIterPiece, coe_dplusIterPiece]
  exact dminus_dplusIter q k

/-- `e_1·d_+^k(1) ∈ V_k`: the vacuum is in the piece and the piece is a `Λ`-subalgebra. -/
theorem elemSymm_mul_dplusIter_mem_piece (q : L) (k : ℕ) :
    MvPolynomial.C (Sym.elemSymm L 1) * dplusIter q k ∈ piece L k := by
  refine mul_mem ?_ (dplusIter_mem_piece q k)
  rw [← MvPolynomial.algebraMap_eq]
  exact (piece L k).algebraMap_mem _

/-- `e_1·d_+^k(1)` as an element of `V_k`: what `d^♭_-` sends the vacuum tower of `V_{k+1}` to. -/
noncomputable def elemSymmDplusIterPiece (q : L) (k : ℕ) : pieceSub L k :=
  ⟨MvPolynomial.C (Sym.elemSymm L 1) * dplusIter q k, elemSymm_mul_dplusIter_mem_piece q k⟩

theorem coe_elemSymmDplusIterPiece (q : L) (k : ℕ) :
    ((elemSymmDplusIterPiece q k : pieceSub L k) : Total L)
      = MvPolynomial.C (Sym.elemSymm L 1) * dplusIter q k := rfl

/-! ### The relation -/

/-- `d^♭_-` intertwines `X ∈ 𝔹^+_{k+1}(𝕋_0)` with `Y ∈ 𝔹^+_k(𝕋_0)`: the lowering companion of
`HJO.Sweep.DplusIntertwines`, carried as a relation between a rank-`(k+1)` braid and a rank-`k`
braid rather than as a map, for the same reason. -/
def DminusIntertwines (q u : L) (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) {r : L}
    (hr : r * r = q) (k : ℕ) (X : BraidMonoid (k + 1)) (Y : BraidMonoid k) : Prop :=
  ∀ x : pieceSub L (k + 1),
    dminus q (k + 1)
        ((braidRepMellit q u hq hq1 hqp hr (k + 1) X x : pieceSub L (k + 1)) : Total L)
      = ((braidRepMellit q u hq hq1 hqp hr k Y (dminusModPiece q k x) : pieceSub L k) : Total L)

variable {q u : L} {hq : q ≠ 0} {hq1 : q ≠ 1} {hqp : q + 1 ≠ 0} {r : L} {hr : r * r = q} {k : ℕ}

/-- The relation from two `HJO.Sweep.RepresentedBy` readings and one operator identity. -/
theorem DminusIntertwines.of_representedBy {X : BraidMonoid (k + 1)} {Y : BraidMonoid k}
    {gX gY : Module.End L (Total L)}
    (hX : RepresentedBy q u r (k + 1)
      (braidRepRespects_mellit q u hq hq1 hqp hr (k + 1)) X gX)
    (hY : RepresentedBy q u r k (braidRepRespects_mellit q u hq hq1 hqp hr k) Y gY)
    (hcomm : dminus q (k + 1) * gX = gY * dminus q (k + 1)) :
    DminusIntertwines q u hq hq1 hqp hr k X Y := fun x => by
  rw [braidRepMellit, braidRepMellit, hX.apply, hY.apply]
  exact LinearMap.congr_fun hcomm (x : Total L)

/-- The same, when the operator identity is available only on the graded piece — which is the shape
any `z`-letter clause will have. -/
theorem DminusIntertwines.of_representedBy_piece {X : BraidMonoid (k + 1)} {Y : BraidMonoid k}
    {gX gY : Module.End L (Total L)}
    (hX : RepresentedBy q u r (k + 1)
      (braidRepRespects_mellit q u hq hq1 hqp hr (k + 1)) X gX)
    (hY : RepresentedBy q u r k (braidRepRespects_mellit q u hq hq1 hqp hr k) Y gY)
    (hcomm : ∀ F ∈ piece L (k + 1),
      dminus q (k + 1) (gX F) = gY (dminus q (k + 1) F)) :
    DminusIntertwines q u hq hq1 hqp hr k X Y := fun x => by
  rw [braidRepMellit, braidRepMellit, hX.apply, hY.apply]
  exact hcomm (x : Total L) x.2

/-- The empty word is intertwined with the empty word. -/
theorem DminusIntertwines.one : DminusIntertwines q u hq hq1 hqp hr k 1 1 := fun x => by
  simp only [map_one, Module.End.one_apply, coe_dminusModPiece]

/-- **The relation is multiplicative**, which is what lets it stand in for a homomorphism. -/
theorem DminusIntertwines.mul {X X' : BraidMonoid (k + 1)} {Y Y' : BraidMonoid k}
    (hX : DminusIntertwines q u hq hq1 hqp hr k X Y)
    (hX' : DminusIntertwines q u hq hq1 hqp hr k X' Y') :
    DminusIntertwines q u hq hq1 hqp hr k (X * X') (Y * Y') := by
  intro x
  have h' : dminusModPiece q k (braidRepMellit q u hq hq1 hqp hr (k + 1) X' x)
      = braidRepMellit q u hq hq1 hqp hr k Y' (dminusModPiece q k x) :=
    Subtype.ext (hX' x)
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hX, ← h']

/-- The relation transported along an identity of the rank-`k` braid. -/
theorem DminusIntertwines.congr {X : BraidMonoid (k + 1)} {Y Y' : BraidMonoid k}
    (hX : DminusIntertwines q u hq hq1 hqp hr k X Y) (h : Y = Y') :
    DminusIntertwines q u hq hq1 hqp hr k X Y' := by rw [← h]; exact hX

/-- The relation transported along an identity of the rank-`(k+1)` braid. -/
theorem DminusIntertwines.congr_left {X X' : BraidMonoid (k + 1)} {Y : BraidMonoid k}
    (hX : DminusIntertwines q u hq hq1 hqp hr k X Y) (h : X = X') :
    DminusIntertwines q u hq hq1 hqp hr k X' Y := by rw [← h]; exact hX

/-- A product along a list is intertwined with the corresponding product, which is how the words of
`HJO.Braid.trainUp` and `HJO.Braid.trainDown` are handled. -/
theorem DminusIntertwines.listProd {ι : Type*} {f : ι → BraidMonoid (k + 1)}
    {g : ι → BraidMonoid k} (l : List ι)
    (hl : ∀ i ∈ l, DminusIntertwines q u hq hq1 hqp hr k (f i) (g i)) :
    DminusIntertwines q u hq hq1 hqp hr k ((l.map f).prod) ((l.map g).prod) := by
  induction l with
  | nil => simpa only [List.map_nil, List.prod_nil] using DminusIntertwines.one
  | cons i t ih =>
    simp only [List.map_cons, List.prod_cons]
    exact (hl i (List.mem_cons_self ..)).mul (ih fun j hj => hl j (List.mem_cons_of_mem _ hj))

/-! ### The `T` and `T̄` letters, at the same index

The index range is `1 ≤ i` and `i + 1 ≤ k`, which is exactly the range of
`HJO.Sweep.dminus_mul_braidEnd` read on `V_{k+1}`, and it is exact: at `i = k` the operator
identity is false, `T_k` moving the variable `d^♭_-` extracts. -/

/-- **The `T` letter, at every index `d^♭_-` reaches**: `T_i ↦ T_i`, for `i + 1 ≤ k`. -/
theorem dminusIntertwines_braidGenT {i : ℕ} (hi : 1 ≤ i) (hik : i + 1 ≤ k) :
    DminusIntertwines q u hq hq1 hqp hr k (braidGenT (k + 1) i) (braidGenT k i) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  refine DminusIntertwines.of_representedBy (representedBy_braidGenT hi (by omega))
    (representedBy_braidGenT hi (by omega)) ?_
  rw [mul_smul_comm, smul_mul_assoc,
    show m + 1 + 1 = m + 2 from rfl, dminus_mul_braidEnd q (k := m) (by omega)]

/-- **The `T̄` letter, at the same range**, the identity inverted. -/
theorem dminusIntertwines_braidGenTinv {i : ℕ} (hi : 1 ≤ i) (hik : i + 1 ≤ k) :
    DminusIntertwines q u hq hq1 hqp hr k (braidGenTinv (k + 1) i) (braidGenTinv k i) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  refine DminusIntertwines.of_representedBy (representedBy_braidGenTinv hi (by omega))
    (representedBy_braidGenTinv hi (by omega)) ?_
  rw [mul_smul_comm, smul_mul_assoc,
    show m + 1 + 1 = m + 2 from rfl, dminus_mul_braidInvEnd q (k := m) (by omega)]

/-- **Above both ranks there is nothing to say**: for `k + 1 ≤ i` the letter `T_i` is out of rank at
`k + 1` as well as at `k`, so both names are the identity. With
`HJO.Sweep.dminusIntertwines_braidGenT` this leaves exactly the single index `i = k` open. -/
theorem dminusIntertwines_braidGenT_of_lt {i : ℕ} (hik : k + 1 ≤ i) :
    DminusIntertwines q u hq hq1 hqp hr k (braidGenT (k + 1) i) (braidGenT k i) := by
  rw [braidGenT_of_lt (by omega), braidGenT_of_lt (by omega)]
  exact DminusIntertwines.one

/-- The same for `T̄`. -/
theorem dminusIntertwines_braidGenTinv_of_lt {i : ℕ} (hik : k + 1 ≤ i) :
    DminusIntertwines q u hq hq1 hqp hr k (braidGenTinv (k + 1) i) (braidGenTinv k i) := by
  rw [braidGenTinv_of_not_inRank (by simp only [Letter.InRank]; omega),
    braidGenTinv_of_not_inRank (by simp only [Letter.InRank]; omega)]
  exact DminusIntertwines.one

/-! ### The `y_1` letter -/

/-- **`y_1 ↦ y_1`.** `HJO.Sweep.dminus_auxVar_mul` at `j = 1`: the substitution fixes `y_1` and the
extraction passes it, `1` being below the index the extraction reads. The one hypothesis is
`1 ≤ k`, which is what puts `y_1` in rank at the lower rank too. -/
theorem dminusIntertwines_braidGenY (hk : 1 ≤ k) :
    DminusIntertwines q u hq hq1 hqp hr k (braidGenY (k + 1) 1) (braidGenY k 1) := by
  refine DminusIntertwines.of_representedBy (representedBy_braidGenY (by omega))
    (representedBy_braidGenY hk) ?_
  refine LinearMap.ext fun F => ?_
  simp only [Module.End.mul_apply, LinearMap.neg_apply, LinearMap.mulLeft_apply, map_neg]
  rw [dminus_auxVar_mul q (le_refl 1) hk]

/-! ### The trains

Every index is unchanged, so an ascending word is intertwined with the *same* ascending word. The
bound is that the whole index range stays below the top: `b ≤ k` for `T_{a↗b}`-shaped words and
`a ≤ k` for `T_{a↘b}`-shaped ones. -/

/-- An ascending word is intertwined with the same ascending word, given the letters. -/
theorem dminusIntertwines_ascendingWord {T : ℕ → BraidMonoid (k + 1)} {T' : ℕ → BraidMonoid k}
    (hT : ∀ j, 1 ≤ j → j + 1 ≤ k → DminusIntertwines q u hq hq1 hqp hr k (T j) (T' j)) {a b : ℕ}
    (ha : 1 ≤ a) (hb : b ≤ k) :
    DminusIntertwines q u hq hq1 hqp hr k (ascendingWord T a b) (ascendingWord T' a b) := by
  rw [ascendingWord, ascendingWord]
  refine DminusIntertwines.listProd _ fun j hj => ?_
  rw [List.mem_range'_1] at hj
  exact hT j (by omega) (by omega)

/-- A descending word is intertwined with the same descending word. -/
theorem dminusIntertwines_descendingWord {T : ℕ → BraidMonoid (k + 1)} {T' : ℕ → BraidMonoid k}
    (hT : ∀ j, 1 ≤ j → j + 1 ≤ k → DminusIntertwines q u hq hq1 hqp hr k (T j) (T' j)) {a b : ℕ}
    (hb : 1 ≤ b) (ha : a ≤ k) :
    DminusIntertwines q u hq hq1 hqp hr k (descendingWord T a b) (descendingWord T' a b) := by
  rw [descendingWord, descendingWord]
  refine DminusIntertwines.listProd _ fun j hj => ?_
  rw [List.mem_reverse, List.mem_range'_1] at hj
  exact hT j (by omega) (by omega)

/-- **A descending train keeps both indices**, provided the whole range stays below the top. -/
theorem dminusIntertwines_braidTrainDown {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hak : a ≤ k)
    (hbk : b ≤ k) :
    DminusIntertwines q u hq hq1 hqp hr k (braidTrainDown (k + 1) a b) (braidTrainDown k a b) := by
  change DminusIntertwines q u hq hq1 hqp hr k (trainDown _ _ a b) (trainDown _ _ a b)
  unfold trainDown
  split_ifs with h
  · exact dminusIntertwines_descendingWord (fun j hj hjk => dminusIntertwines_braidGenT hj hjk)
      hb hak
  · exact dminusIntertwines_ascendingWord (fun j hj hjk => dminusIntertwines_braidGenTinv hj hjk)
      ha hbk

/-- **An ascending train keeps both indices**, under the same bound. -/
theorem dminusIntertwines_braidTrainUp {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hak : a ≤ k)
    (hbk : b ≤ k) :
    DminusIntertwines q u hq hq1 hqp hr k (braidTrainUp (k + 1) a b) (braidTrainUp k a b) := by
  change DminusIntertwines q u hq hq1 hqp hr k (trainUp _ _ a b) (trainUp _ _ a b)
  unfold trainUp
  split_ifs with h
  · exact dminusIntertwines_ascendingWord (fun j hj hjk => dminusIntertwines_braidGenT hj hjk)
      ha hbk
  · exact dminusIntertwines_descendingWord (fun j hj hjk => dminusIntertwines_braidGenTinv hj hjk)
      hb hak

/-! ### The `z` letter, conditionally

This is the obligation. `HJO.Sweep.dplus_zop` is the raising lemma (`HJO.Sweep.starCommCM_cmDPlus`
in the convention of `HJO.Sweep.zop`); nothing corresponds to it on the lowering side, and the
hypothesis below is precisely what would.

Two reasons it is not the raising lemma read backwards. `HJO.Sweep.zop` carries the prefactor
`q^k/(1-q)` of `HJO.Sweep.zopOneStar`, which is rank-dependent, so the two sides of the square
differ by a factor `q` before any operator is moved; and `z_1` on `V_{k+1}` is conjugated by
`T^*_{(k+1)↘1} = T̄_1⋯T̄_k`, whose top letter is the one index `d^♭_-` does not commute with, the
lemma `HJO.Sweep.dminus_mul_trainUpEnd_star` reaching only `T^*_{k↘1}`. -/

/-- **The `z` letter given the lowering `z`-relation.** The hypothesis `hz` is the missing operator
identity, stated on the graded piece exactly as `HJO.Sweep.dplus_zop` is; given it, the letter is
intertwined at the same index, and the `(qu)^{-1}` of `HJO.Sweep.braidRep` is the same constant on
both sides and is never inverted, so `u ≠ 0` is not spent. -/
theorem dminusIntertwines_braidGenZ_of_zop {i : ℕ} (hi : 1 ≤ i) (hik : i ≤ k)
    (hz : ∀ F ∈ piece L (k + 1),
      dminus q (k + 1) (zop q u (k + 1) i F) = zop q u k i (dminus q (k + 1) F)) :
    DminusIntertwines q u hq hq1 hqp hr k (braidGenZ (k + 1) i) (braidGenZ k i) := by
  refine DminusIntertwines.of_representedBy_piece
    (representedBy_braidGenZ_of_le (hq := hq) (hq1 := hq1) (hqp := hqp) (hr := hr) hi
      (show i ≤ k + 1 by omega))
    (representedBy_braidGenZ_of_le (hq := hq) (hq1 := hq1) (hqp := hqp) (hr := hr) hi hik)
    fun F hF => ?_
  rw [LinearMap.smul_apply, LinearMap.smul_apply, map_smul, hz F hF]

/-! ### The bridge to the braid value, and the `e_1` it carries -/

/-- **The braid value of a datum with the vacuum displaced by `e_1`.** Verbatim
`HJO.Mellit.braidValueOfData` — same prefactor, same rank-`k` representation — except that `π_k` is
applied to `e_1·d_+^k(1)` instead of to `d_+^k(1)`, and the braid is supplied separately rather than
being the special braid of the datum. This is what `d^♭_-` of a rank-`(k+1)` braid value is, and it
is the shape the residual of rule `BE` has to be stated in. -/
noncomputable def braidValueElemSymmOfData (q u : L) (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0)
    {r : L} (hr : r * r = q) (a b N : ℕ) {k : ℕ} (Y : BraidMonoid k) (v : Fin (k + 1) → ℚ)
    (α : Fin (k + 1) → ℕ) : Total L :=
  r ^ ((invFin (Mellit.sweepTheta a b N) v α : ℤ) - (invIni (Mellit.sweepTheta a b N) v α : ℤ)) •
    ((braidRepMellit q u hq hq1 hqp hr k Y (elemSymmDplusIterPiece q k) : pieceSub L k) : Total L)

/-- **What a completed intertwiner would give.** If the rank-`(k+1)` special braid of a datum is
intertwined with the rank-`k` special braid of another, then `d^♭_-` of the first datum's braid
value is the second braid's operator applied to `e_1·d_+^k(1)` — **not** to `d_+^k(1)`, so **not**
`HJO.Mellit.braidValueOfData` at the second datum.

The prefactor of `HJO.Mellit.braidValueOfData` passes untouched, `d^♭_-` being `L`-linear; the whole
discrepancy is the `e_1` of `HJO.Sweep.dminus_dplusIter`, and it cannot be pulled back out through
`π_k`, which is `Λ`-linear on the `T` and `y` letters but not on the `z` letter, that being built
from `HJO.Sweep.dplusStar` and acting on the alphabet.

This is the precise sense in which the lowering side is not the mirror of
`HJO.Mellit.braidValueOfData_succAbove_eq_dplus`. -/
theorem dminus_braidValueOfData_of_dminusIntertwines (a b N : ℕ)
    {v : Fin (k + 1) → ℚ} {α : Fin (k + 1) → ℕ} {Y : BraidMonoid k}
    (hXY : DminusIntertwines q u hq hq1 hqp hr k
      (specialBraid (Mellit.sweepTheta a b N) v α) Y) :
    dminus q (k + 1) (Mellit.braidValueOfData q u hq hq1 hqp hr a b N v α)
      = braidValueElemSymmOfData q u hq hq1 hqp hr a b N Y v α := by
  have hvac : dminusModPiece q k (dplusIterPiece q (k + 1)) = elemSymmDplusIterPiece q k := by
    refine Subtype.ext ?_
    rw [coe_dminusModPiece, dminus_dplusIterPiece, coe_elemSymmDplusIterPiece, coe_dplusIterPiece]
  rw [Mellit.braidValueOfData, braidValueElemSymmOfData, map_smul,
    hXY (dplusIterPiece q (k + 1)), hvac]

end HJO.Sweep

end
