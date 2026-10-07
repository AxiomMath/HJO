/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidAppendLetters
public import HJO.Shuffle.MellitDplusVacuum
public import HJO.Shuffle.MellitPhiIntertwinePiece
public meta import HJO.Attr

/-! # `HJO.Mellit.braidRep_specialBraid_dplusIter`: the append-a-part recursion

`HJO.Mellit.braidRep_specialBraid_dplusIter` applies the braid representation `π_{k+1}` of
`HJO.Sweep.braidRep` to the identity of `HJO.Braid.IsAppendSetup.specialBraid_eq_appendRhs` and
evaluates at the vacuum tower `d_+^{k+1}(1)`:

`π_{k+1}(B_{s,w,β}) d_+^{k+1}(1)
  = (-1)^{(a-1)A}(qu)^{1-A} (Z^{(k+1)}_{a,b})^{A-1} T_{k+1↘1} Ω(1;a,b) π_k(B_{s,v,α}) d_+^k(1)`.

`HJO.Mellit.braidRep_specialBraid_dplusIter` is that identity, with the operator standing to the
left of the last factor written as `HJO.Mellit.stageTotal` — the word
`(Z^{(k+1)}_{a,b})^{A-1}T_{k+1↘1}Ω(1;a,b)` in operators defined elsewhere, which
`HJO/Shuffle/SweepWitnessAppend.lean` computes to be `HJO.Mellit.stage` on the grading `k`.
`HJO.Mellit.sweepIn_braidRep_specialBraid` is the same identity with the stage
`HJO.Mellit.stage` itself and an arbitrary replication family, which is the statement verbatim.

## The route, and where each input is spent

* `HJO.Braid.IsAppendSetup.specialBraid_eq_appendRhs`
  (`HJO.Braid.IsAppendSetup.specialBraid_eq_appendRhs`, and its `k = 0` clause
  `HJO.Braid.IsAppendSetup.specialBraid_eq_slopeBraid_pow'`) rewrites the left-hand side as the word
  `HJO.Braid.appendRhs`.
* `HJO.Sweep.braidRep` is a monoid homomorphism, so the word's image is the product of its letters'
  images. `HJO.Sweep.RepresentedBy` is the bookkeeping: the image of an element of
  `𝔹^+_K(𝕋_0)` under `HJO.Sweep.braidRep`, read through the inclusion `V_K ↪ V_*`, is a named
  endomorphism of `HJO.Sweep.Total`. It is multiplicative with no side condition, since the
  operator is only ever applied to a coerced element.
* The three trains contribute the half-powers of `q`: each has `k` letters, so
  `π_{k+1}(T_{k+1↘1}) = q^{-k/2}T_{k+1↘1}`, `π_{k+1}(T_{1↗k+1}) = q^{-k/2}T_{1↗k+1}` and
  `π_{k+1}(T_{1↘k+1}) = q^{+k/2}T_{1↘k+1}` (`HJO.Sweep.representedBy_braidTrainDown_top`,
  `HJO.Sweep.representedBy_braidTrainUp_bot`, `HJO.Sweep.representedBy_braidTrainDown_bot`). The
  designated square root is the parameter `r` of `HJO.Sweep.braidRep`, and **it does not occur in
  the conclusion**: the two `q^{-k/2}` of each round multiply to the `q^{-k}` that
  `HJO.Mellit.replicatedLetter` carries, and the `q^{+k/2}` of the tail's `T_{1↘k+1}` cancels
  against the `q^{-k/2}` of its `T_{k+1↘1}`.
* `HJO.Sweep.braid_dplusIter` is what makes that last cancellation legitimate:
  `T_{1↘k+1}` is the word `T̄_1⋯T̄_k` and every one of its letters fixes `d_+^{k+1}(1)`
  (`HJO.Sweep.trainDownEnd_bot_dplusIter`, off `HJO.Sweep.braid_dplusIter`).
* `HJO.Sweep.dplus_dplusIter` turns `d_+^{k+1}(1)` into `(-y_1d^*_+)d_+^k(1)`
  (`HJO.Sweep.dplusIterPiece_succ`) and `HJO.Sweep.braidRep_phiPlusStar_comp_negYOneDPlusStarPiece`
  then carries `π_{k+1}(φ^*_+(B))` across it.
* `HJO.Braid.slopeBraid` goes to `HJO.Sweep.slopeOperator` at the rank it is read at
  (`HJO.Sweep.representedBy_slopeBraid`), and `HJO.Mellit.euclid` — already spent inside
  `HJO.Mellit.replOneTotal` and `HJO.Mellit.replTwoTotal` — turns `Ξ_{a,b}(-y_1d^*_+)` into
  `(-1)^{a-1}Ω(1;a,b)` and `Ξ_{a,b}(-y_1)(qu)^{-1}z_1` into `(-1)^{a-1}(qu)^{-1}Ω(2;a,b)`.
* The sign and the power of `qu` are assembled by `HJO.Mellit.append_scalar`:
  `((qu)^{-1}(-1)^{a-1})^{A-1}(-1)^{a-1} = (-1)^{(a-1)A}(qu)^{1-A}`.

## One statement, not two, and why `k = 0` is included

The printed statement runs at `k ≥ 0` while `HJO.Braid.phiPlusStar` needs `k ≥ 1`, so
`HJO.Braid.IsAppendSetup.specialBraid_eq_appendRhs` is two clauses. The *conclusion* of this
statement names neither `φ^*_+` nor a train it cannot form, so the two clauses assemble into one
theorem here, proved by cases on `k`: at `k = 0` the deleted data is the empty tuple, `π_0` is the
unique homomorphism out of the trivial monoid (`HJO.Sweep.braidRep_zero`), `d_+^0(1) = 1`, and both
conjugating trains are the identity (`HJO.Mellit.trainDownEnd_one_one`).

## The side conditions, and whether they are free downstream

* `q ≠ 0`, `q ≠ 1`, `q + 1 ≠ 0` and a designated `r` with `r^2 = q`: these are what
  `HJO.Sweep.braidRepMellit` needs, i.e. what `HJO.Sweep.braidRepRespects_mellit` needs. The first
  three are free under the `AlgebraicIndependent ℤ ![q, u]` of `HJO.Mellit.MellitInput`; the square
  root is part of the definition — `HJO.Sweep.braidRep`'s codomain is
  `End(V_k ⊗_𝕜 𝕜[q^{1/2}])` — and it is eliminable from the conclusion but not from the statement,
  since `π_k` cannot be written without it.
* `HJO.Braid.IsAppendSetup` together with `HJO.Braid.IsSpecialBraidData`, the part `β_0 = A(a+b)-1`,
  the entry `w_0 = 1-θ-δ`, the separation clause `hgap` and the two clustering clauses: these are
  exactly the hypotheses of `HJO.Braid.IsAppendSetup.specialBraid_eq_appendRhs` as widened there.
  Nothing is added here.
  **The appended entry is not required to be `1-θ`**: `δ ≥ 0` is free, subject to the `drift` and
  `cluster_hi` clauses of `HJO.Braid.IsAppendSetup` and to `hgap`, which says no iterate of another
  point of the data lies between `w_0` and `1-θ`. That widening is what a consumer needs, no
  colouring ever supplying `w_0 = 1-θ`
  (`HJO.Mellit.fract_crossingAbscissa_componentTopIndex_last_lt`); `HJO.Braid.gap_of_grid`
  discharges `hgap` from a grid condition on the positions.
* **No hypothesis on `qu` is needed**, and none is carried: `(qu)^{-1}` occurs only as a scalar
  that is factored out, never divided by. This matches `HJO.Mellit.euclid` and
  `HJO/Shuffle/MellitStageInduction.lean`.

## What this does not do

It does not close `HJO.Mellit.BraidClosedForm`. That asks the `append` field of
`HJO.Mellit.IsBraidValue` of a braid value `B` which `HJO.Mellit.IsColouringValue` forces to be
`D_{η,c_α}`, and identifying `D_{η,c_α}` with `π_ℓ(B_{s,v,α^{br}})d_+^ℓ(1)` is
`HJO.Mellit.braidValueColouring_eq_dsc_floor`, proved elsewhere
(`HJO.Mellit.braidValueColouring_eq_dsc_floor`, `HJO/Shuffle/MellitThm58Closed.lean`). What is
proved here is the recursion for the braid value itself.

## References

The lemma `HJO.Mellit.braidRep_specialBraid_dplusIter`, the append-a-part recursion, using
`HJO.Braid.trainUp`, `HJO.Braid.trainDown`, `HJO.Sweep.piece`, `HJO.Sweep.braid`, `HJO.Sweep.dplus`,
`HJO.Braid.IsSpecialBraidData`, `HJO.Braid.specialBraid`, `HJO.Sweep.braidRep`,
`HJO.Mellit.IsReplicationFamily`, `HJO.Mellit.replicatedLetter` and
`HJO.Braid.IsAppendSetup.specialBraid_eq_appendRhs`; and in the proof `HJO.Braid.slopeBraid`,
`HJO.Sweep.slopeOperator`, `HJO.Sweep.isBraidSystem_braidEnd`, `HJO.Sweep.braid_dplusIter`,
`HJO.Sweep.dplus_dplusIter`, `HJO.Sweep.braidRep_phiPlusStar_comp_negYOneDPlusStarPiece` and
`HJO.Mellit.euclid`. Transcribing A. Mellit, *Toric braids and `(m, n)`-parking functions*, §6.
-/

@[expose] public section

namespace HJO.Braid

variable {M : Type*} [Monoid M]

/-- **The ascending branch of `HJO.Braid.trainDown` at the bottom index**:
`T_{1↘k} = T_1^{-1}T_2^{-1}⋯T_{k-1}^{-1}` for `k ≥ 1`. At `k = 1` the two branches of
`HJO.Braid.trainDown` meet, both being the empty product, so no case split survives into the
statement. -/
theorem trainDown_bot_eq_prod (T Tinv : ℕ → M) {k : ℕ} (hk : 1 ≤ k) :
    trainDown T Tinv 1 k = ((List.range' 1 (k - 1)).map Tinv).prod := by
  by_cases hk1 : k = 1
  · subst hk1
    simp [trainDown, descendingWord]
  · rw [trainDown, ite_eq_right (show ¬ k ≤ 1 by omega), ascendingWord]

end HJO.Braid

namespace HJO.Sweep

open Braid

variable {L : Type*} [Field L] [Algebra ℚ L]

/-! ### `d_+^k(1)` as an element of `V_k` -/

/-- **The vacuum tower `d_+^{k}(1)` as an element of `V_k`**, which is where `HJO.Sweep.braidRep`
reads it. Membership is `HJO.Sweep.dplusIter_mem_piece`. -/
noncomputable def dplusIterPiece (q : L) (k : ℕ) : pieceSub L k :=
  ⟨dplusIter q k, dplusIter_mem_piece q k⟩

omit [Algebra ℚ L] in
@[simp]
theorem coe_dplusIterPiece (q : L) (k : ℕ) :
    (dplusIterPiece q k : Total L) = dplusIter q k := rfl

omit [Algebra ℚ L] in
/-- **`HJO.Sweep.dplus_dplusIter` at the codomain**:
`d_+^{k+1}(1) = (-y_1d^*_+) d_+^{k}(1)` in `V_{k+1}`. -/
theorem dplusIterPiece_succ (q u : L) (k : ℕ) :
    dplusIterPiece q (k + 1) = negYOneDPlusStarPiece q u k (dplusIterPiece q k) := by
  refine Subtype.ext ?_
  rw [coe_dplusIterPiece, coe_negYOneDPlusStarPiece, coe_dplusIterPiece, negYOneDPlusStar_apply,
    dplusIter]
  exact dplus_dplusIter q u k

/-! ### Every letter of `T_{1↘k+1}` fixes the vacuum tower -/

omit [Algebra ℚ L] in
/-- **The inverse braid operators below the top fix `d_+^{j}(1)`**, the inverted form of
`HJO.Sweep.braid_dplusIter`: apply `T_i^{-1}` to `T_i d_+^j(1) = d_+^j(1)`. -/
theorem braidInvEnd_dplusIter (q : L) (hq : q ≠ 0) {i j : ℕ} (hi : 1 ≤ i) (hij : i + 1 ≤ j) :
    braidInvEnd q i (dplusIter q j) = dplusIter q j := by
  have hE : braidEnd q i (dplusIter q j) = dplusIter q j := braid_dplusIter q hi hij
  calc braidInvEnd q i (dplusIter q j)
      = braidInvEnd q i (braidEnd q i (dplusIter q j)) := by rw [hE]
    _ = (braidInvEnd q i * braidEnd q i) (dplusIter q j) := by rw [Module.End.mul_apply]
    _ = dplusIter q j := by rw [braidInvEnd_mul_braidEnd q hq, Module.End.one_apply]

omit [Algebra ℚ L] in
/-- A word in the inverse braid operators, all of whose indices lie below `j`, fixes `d_+^j(1)`. -/
theorem list_prod_braidInvEnd_dplusIter (q : L) (hq : q ≠ 0) {j : ℕ} (l : List ℕ)
    (hl : ∀ i ∈ l, 1 ≤ i ∧ i + 1 ≤ j) :
    ((l.map (braidInvEnd q)).prod) (dplusIter q j) = dplusIter q j := by
  induction l with
  | nil => simp
  | cons i t ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply,
      ih fun m hm => hl m (List.mem_cons_of_mem _ hm)]
    obtain ⟨h1, h2⟩ := hl i (List.mem_cons_self ..)
    exact braidInvEnd_dplusIter q hq h1 h2

omit [Algebra ℚ L] in
/-- **`T_{1↘k+1}` fixes `d_+^{k+1}(1)`.** The train is the word `T_1^{-1}⋯T_k^{-1}` by
`HJO.Braid.trainDown_bot_eq_prod`, and every index it reads is below `k+1`. -/
theorem trainDownEnd_bot_dplusIter (q : L) (hq : q ≠ 0) (k : ℕ) :
    trainDownEnd q 1 (k + 1) (dplusIter q (k + 1)) = dplusIter q (k + 1) := by
  rw [trainDownEnd, Braid.trainDown_bot_eq_prod _ _ (Nat.le_add_left 1 k), Nat.add_sub_cancel]
  refine list_prod_braidInvEnd_dplusIter q hq _ fun i hi => ?_
  simp only [List.mem_range'_1] at hi
  omega

/-! ### The image of a braid word, as an operator on the total space

`HJO.Sweep.braidRep` is typed at `Module.End L (pieceSub L K)`, while every operator of the argument
is an endomorphism of `HJO.Sweep.Total`. This predicate is the bridge, and it is
multiplicative with no membership side condition, because the operator is only ever applied to a
coerced element. -/

/-- **`X` is represented by `g`**: `π_K(X)` read through `V_K ↪ V_*` is the operator `g`. -/
def RepresentedBy (q u r : L) (K : ℕ) (h : BraidRepRespects q u r K) (X : BraidMonoid K)
    (g : Module.End L (Total L)) : Prop :=
  ∀ x : pieceSub L K, (braidRep q u r K h X x : Total L) = g x

variable {q u r : L} {K : ℕ} {h : BraidRepRespects q u r K}

/-- The predicate, read at a vector. Stated so that `rw` can use it without unfolding the
definition. -/
theorem RepresentedBy.apply {X : BraidMonoid K} {g : Module.End L (Total L)}
    (hX : RepresentedBy q u r K h X g) (x : pieceSub L K) :
    ((braidRep q u r K h X x : pieceSub L K) : Total L) = g x := hX x

theorem RepresentedBy.one : RepresentedBy q u r K h 1 1 := fun x => by
  simp only [map_one, Module.End.one_apply]

/-- **The predicate is multiplicative.** No shape condition on either operator is needed: the outer
one is applied to the coercion of the inner one's value. -/
theorem RepresentedBy.mul {X Y : BraidMonoid K} {g g' : Module.End L (Total L)}
    (hX : RepresentedBy q u r K h X g) (hY : RepresentedBy q u r K h Y g') :
    RepresentedBy q u r K h (X * Y) (g * g') := fun x => by
  rw [map_mul, Module.End.mul_apply, hX, hY, Module.End.mul_apply]

theorem RepresentedBy.pow {X : BraidMonoid K} {g : Module.End L (Total L)}
    (hX : RepresentedBy q u r K h X g) (n : ℕ) : RepresentedBy q u r K h (X ^ n) (g ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using RepresentedBy.one
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact ih.mul hX

theorem RepresentedBy.congr {X : BraidMonoid K} {g g' : Module.End L (Total L)}
    (hX : RepresentedBy q u r K h X g) (hg : g = g') : RepresentedBy q u r K h X g' := by
  rw [← hg]; exact hX

/-- A product along a list is represented by the corresponding product. -/
theorem RepresentedBy.listProd {ι : Type*} {f : ι → BraidMonoid K}
    {g : ι → Module.End L (Total L)} (l : List ι)
    (hl : ∀ i ∈ l, RepresentedBy q u r K h (f i) (g i)) :
    RepresentedBy q u r K h ((l.map f).prod) ((l.map g).prod) := by
  induction l with
  | nil => simpa only [List.map_nil, List.prod_nil] using RepresentedBy.one
  | cons i t ih =>
    simp only [List.map_cons, List.prod_cons]
    exact (hl i (List.mem_cons_self ..)).mul (ih fun j hj => hl j (List.mem_cons_of_mem _ hj))

omit [Algebra ℚ L] in
/-- The scalars of a list of scaled operators collect into a power. -/
theorem list_prod_map_smul {ι : Type*} (c : L) (g : ι → Module.End L (Total L)) (l : List ι) :
    (l.map fun i => c • g i).prod = c ^ l.length • (l.map g).prod := by
  induction l with
  | nil => simp
  | cons i t ih =>
    simp only [List.map_cons, List.prod_cons, ih, List.length_cons]
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, pow_succ']

/-! #### The four generators -/

theorem representedBy_braidGenT {i : ℕ} (hi : 1 ≤ i) (hiK : i + 1 ≤ K) :
    RepresentedBy q u r K h (braidGenT K i) (r⁻¹ • braidEnd q i) := fun x => by
  rw [coe_braidRep_T q u r h hi hiK, LinearMap.smul_apply]

theorem representedBy_braidGenTinv {i : ℕ} (hi : 1 ≤ i) (hiK : i + 1 ≤ K) :
    RepresentedBy q u r K h (braidGenTinv K i) (r • braidInvEnd q i) := fun x => by
  rw [coe_braidRep_Tbar q u r h hi hiK, LinearMap.smul_apply]

theorem representedBy_braidGenY (hK : 1 ≤ K) :
    RepresentedBy q u r K h (braidGenY K 1)
      (-LinearMap.mulLeft L (auxVar 1 : Total L)) := fun x => by
  rw [braidRep_y, coe_yRep, yRepTotal_one q u r hK]

theorem representedBy_braidGenZ (hK : 1 ≤ K) :
    RepresentedBy q u r K h (braidGenZ K 1) ((q * u)⁻¹ • zop q u K 1) := fun x => by
  rw [braidRep_z, coe_zRep, zRepTotal_one q u r hK, LinearMap.smul_apply]

/-! #### The three trains

Each train has `K - 1` letters, so each contributes `r^{∓(K-1)}`, which is
`q^{∓k/2}` at `K = k+1`. -/

/-- `π_K(T_{K↘1}) = q^{-(K-1)/2}T_{K↘1}`. -/
theorem representedBy_braidTrainDown_top (hK : 1 ≤ K) :
    RepresentedBy q u r K h (braidTrainDown K K 1)
      ((r⁻¹ : L) ^ (K - 1) • trainDownEnd q K 1) := by
  have hbase : RepresentedBy q u r K h
      ((((List.range' 1 (K - 1)).reverse).map (braidGenT K)).prod)
      ((((List.range' 1 (K - 1)).reverse).map fun i => (r⁻¹ : L) • braidEnd q i).prod) := by
    refine RepresentedBy.listProd _ fun i hi => ?_
    simp only [List.mem_reverse, List.mem_range'_1] at hi
    exact representedBy_braidGenT (by omega) (by omega)
  rw [show braidTrainDown K K 1
      = (((List.range' 1 (K - 1)).reverse).map (braidGenT K)).prod from
    Braid.trainDown_one_eq_prod _ _ K hK]
  refine hbase.congr ?_
  rw [list_prod_map_smul, List.length_reverse, List.length_range',
    show trainDownEnd q K 1 = (((List.range' 1 (K - 1)).reverse).map (braidEnd q)).prod from
      Braid.trainDown_one_eq_prod _ _ K hK]

/-- `π_K(T_{1↗K}) = q^{-(K-1)/2}T_{1↗K}`. -/
theorem representedBy_braidTrainUp_bot (hK : 1 ≤ K) :
    RepresentedBy q u r K h (braidTrainUp K 1 K)
      ((r⁻¹ : L) ^ (K - 1) • trainUpEnd q 1 K) := by
  have hbase : RepresentedBy q u r K h
      (((List.range' 1 (K - 1)).map (braidGenT K)).prod)
      (((List.range' 1 (K - 1)).map fun i => (r⁻¹ : L) • braidEnd q i).prod) := by
    refine RepresentedBy.listProd _ fun i hi => ?_
    simp only [List.mem_range'_1] at hi
    exact representedBy_braidGenT (by omega) (by omega)
  rw [show braidTrainUp K 1 K = ((List.range' 1 (K - 1)).map (braidGenT K)).prod from
    Braid.trainUp_one_eq_prod _ _ K hK]
  refine hbase.congr ?_
  rw [list_prod_map_smul, List.length_range',
    show trainUpEnd q 1 K = ((List.range' 1 (K - 1)).map (braidEnd q)).prod from
      Braid.trainUp_one_eq_prod _ _ K hK]

/-- `π_K(T_{1↘K}) = q^{+(K-1)/2}T_{1↘K}`: the one train of the recursion written with the inverted
letters, hence the one whose half-power of `q` has the other sign. -/
theorem representedBy_braidTrainDown_bot (hK : 1 ≤ K) :
    RepresentedBy q u r K h (braidTrainDown K 1 K) (r ^ (K - 1) • trainDownEnd q 1 K) := by
  have hbase : RepresentedBy q u r K h
      (((List.range' 1 (K - 1)).map (braidGenTinv K)).prod)
      (((List.range' 1 (K - 1)).map fun i => (r : L) • braidInvEnd q i).prod) := by
    refine RepresentedBy.listProd _ fun i hi => ?_
    simp only [List.mem_range'_1] at hi
    exact representedBy_braidGenTinv (by omega) (by omega)
  rw [show braidTrainDown K 1 K = ((List.range' 1 (K - 1)).map (braidGenTinv K)).prod from
    Braid.trainDown_bot_eq_prod _ _ hK]
  refine hbase.congr ?_
  rw [list_prod_map_smul, List.length_range',
    show trainDownEnd q 1 K = ((List.range' 1 (K - 1)).map (braidInvEnd q)).prod from
      Braid.trainDown_bot_eq_prod _ _ hK]

/-! #### The slope braid

`HJO.Braid.slopeBraid` and `HJO.Sweep.slopeOperator` are the same list read through two
assignments that agree letter by letter, which is how the second is defined. -/

/-- **`π_K(b_{m,n}) = Ξ^{(K)}_{m,n}`**, at every rank `K ≥ 1`. The rank-one case is
`HJO.Sweep.coe_braidRep_slopeBraid_one`; the general one is the same computation, and it is what
`HJO.Mellit.braidRep_specialBraid_dplusIter` reads at `K = k+1`. -/
theorem representedBy_slopeBraid (hK : 1 ≤ K) (m n : ℕ) :
    RepresentedBy q u r K h (slopeBraid K m n) (slopeOperator q u K m n) := by
  rw [slopeBraid, slopeOperator]
  refine RepresentedBy.listProd _ fun l _ => ?_
  cases l with
  | y => exact representedBy_braidGenY hK
  | z => exact representedBy_braidGenZ hK

end HJO.Sweep

namespace HJO.Mellit

open HJO.Sweep Braid

variable {L : Type*} [Field L] [Algebra ℚ L]

/-! ### The two operator identities `HJO.Mellit.euclid` buys

`HJO.Mellit.replOneTotal` and `HJO.Mellit.replTwoTotal` are `Ω(1;a,b)` and `Ω(2;a,b)` written out,
each carrying the sign `(-1)^{a-1}` that `HJO.Mellit.euclid` produces. The two lemmas below read
them backwards, which is the direction the computation needs: the slope operator applied to the
`(1,1)` value is the sign times the `(a,b)` value. -/

omit [Algebra ℚ L] in
/-- The sign of `HJO.Mellit.euclid` squares to `1`. -/
private theorem sign_sq (a : ℕ) : ((-1 : L) ^ (a - 1)) * ((-1 : L) ^ (a - 1)) = 1 := by
  rw [← pow_add, ← two_mul, pow_mul]
  simp

/-- **`Ξ_{a,b}(-y_1d^*_+) = (-1)^{a-1}Ω(1;a,b)`**, the factor to the right of the power in the
computation. -/
theorem slopeOperator_negYOneDPlusStar (q u : L) (a b k : ℕ) (F : Total L) :
    slopeOperator q u (k + 1) a b (negYOneDPlusStar q u k F)
      = (-1 : L) ^ (a - 1) • replOneTotal q u a b k F := by
  rw [replOneTotal, LinearMap.smul_apply, smul_smul, sign_sq, one_smul, Module.End.mul_apply]
  rfl

/-- The word of one round with every scalar and sign stripped off, which is the shape both sides of
`HJO.Mellit.representedBy_round` normalise to. -/
private noncomputable def roundWord (q u : L) (a b k : ℕ) : Module.End L (Total L) :=
  trainDownEnd q (k + 1) 1 * (slopeOperator q u (k + 1) a b *
    (LinearMap.mulLeft L (auxVar 1 : Total L) * (zopOneStar q u (k + 1) * trainUpEnd q 1 (k + 1))))

/-- **`Z^{(k+1)}_{a,b}` in terms of the stripped word.** `HJO.Mellit.replicatedLetter` at the
witness carries the `q^{-k}` of its two trains, the sign of `HJO.Mellit.euclid` and the sign of
`Ω(2;1,1) = -y_1z_1`. -/
private theorem replicatedTotal_eq_smul_roundWord (q u : L) (a b k : ℕ) :
    replicatedTotal q u a b k
      = (-(q ^ (-(k : ℤ)) * (-1 : L) ^ (a - 1))) • roundWord q u a b k := by
  rw [replicatedTotal, replTwoTotal, roundWord]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, neg_mul, mul_neg, smul_neg, neg_smul,
    mul_assoc]

/-! ### The round of the recursion

`T_{k+1↘1}b_{a,b}y_1z_1T_{1↗k+1}` goes to `(-1)^{a-1}(qu)^{-1}Z^{(k+1)}_{a,b}`: the two trains
contribute the `q^{-k}` of `HJO.Mellit.replicatedLetter`, and the letters between them the sign and
the `(qu)^{-1}`. -/

/-- **The image of one round.**
`π_{k+1}(T_{k+1↘1}b_{a,b}y_1z_1T_{1↗k+1}) = (-1)^{a-1}(qu)^{-1}Z^{(k+1)}_{a,b}`. -/
theorem representedBy_round {q u r : L} (hq : q ≠ 0) (hr : r * r = q) {k : ℕ}
    (h : BraidRepRespects q u r (k + 1)) (a b : ℕ) :
    RepresentedBy q u r (k + 1) h
      (braidTrainDown (k + 1) (k + 1) 1 * slopeBraid (k + 1) a b * braidGenY (k + 1) 1 *
        braidGenZ (k + 1) 1 * braidTrainUp (k + 1) 1 (k + 1))
      (((q * u)⁻¹ * (-1 : L) ^ (a - 1)) • replicatedTotal q u a b k) := by
  have hrne : r ≠ 0 := fun hz => hq (by rw [← hr, hz, mul_zero])
  have hk1 : 1 ≤ k + 1 := Nat.le_add_left 1 k
  have hbase :=
    ((((representedBy_braidTrainDown_top (q := q) (u := u) (r := r) (h := h) hk1).mul
      (representedBy_slopeBraid (q := q) (u := u) (r := r) (h := h) hk1 a b)).mul
      (representedBy_braidGenY (q := q) (u := u) (r := r) (h := h) hk1)).mul
      (representedBy_braidGenZ (q := q) (u := u) (r := r) (h := h) hk1)).mul
      (representedBy_braidTrainUp_bot (q := q) (u := u) (r := r) (h := h) hk1)
  have hrr : (r⁻¹ : L) ^ k * (r⁻¹ : L) ^ k = q ^ (-(k : ℤ)) := by
    rw [← mul_pow, ← mul_inv, hr, zpow_neg, zpow_natCast, inv_pow]
  have hs : ((-1 : L) ^ (a - 1)) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  refine hbase.congr ?_
  rw [replicatedTotal_eq_smul_roundWord, roundWord, zop_one]
  simp only [Nat.add_sub_cancel, smul_mul_assoc, mul_smul_comm, smul_smul, neg_mul, mul_neg,
    smul_neg, neg_smul, mul_assoc]
  rw [show (q * u)⁻¹ * ((-1 : L) ^ (a - 1) * (q ^ (-(k : ℤ)) * (-1 : L) ^ (a - 1)))
      = (r⁻¹ : L) ^ k * ((q * u)⁻¹ * (r⁻¹ : L) ^ k) from by
    rw [← hrr]
    linear_combination ((q * u)⁻¹ * (r⁻¹ : L) ^ k * (r⁻¹ : L) ^ k) * hs]

/-! ### The scalar -/

omit [Algebra ℚ L] in
/-- **The scalar of `HJO.Mellit.braidRep_specialBraid_dplusIter`.** `A - 1` rounds each contribute
`(-1)^{a-1}(qu)^{-1}` and the tail one further `(-1)^{a-1}`, which is `(-1)^{(a-1)A}(qu)^{1-A}`. The
exponent `1 - A` is nonpositive, so no hypothesis on `qu` is needed. -/
theorem append_scalar (q u : L) (a : ℕ) {A : ℕ} (hA : 1 ≤ A) :
    ((q * u)⁻¹ * (-1 : L) ^ (a - 1)) ^ (A - 1) * (-1 : L) ^ (a - 1)
      = (-1 : L) ^ ((a - 1) * A) * (q * u) ^ (1 - (A : ℤ)) := by
  obtain ⟨n, rfl⟩ : ∃ n, A = n + 1 := ⟨A - 1, by omega⟩
  have h1 : (1 : ℤ) - ((n + 1 : ℕ) : ℤ) = -(n : ℤ) := by push_cast; ring
  have h2 : (a - 1) * (n + 1) = (a - 1) * n + (a - 1) := by ring
  rw [Nat.add_sub_cancel, h1, zpow_neg, zpow_natCast, ← inv_pow, mul_pow, ← pow_mul, h2, pow_add]
  ring

/-! ### The assembly -/

/-- `G_{k+1,A}` applied to a vector, unfolded. -/
theorem stageTotal_apply (q u : L) (a b k A : ℕ) (F : Total L) :
    stageTotal q u a b k A F
      = (replicatedTotal q u a b k ^ (A - 1))
          (trainDownEnd q (k + 1) 1 (replOneTotal q u a b k F)) := by
  rw [stageTotal, Module.End.mul_apply, Module.End.mul_apply]

/-- **The assembly step**, shared by the two cases of
`HJO.Braid.IsAppendSetup.specialBraid_eq_appendRhs`: given the value of the tail and the value of
one round, the value of `round^{A-1}·tail` is the right-hand side of the recursion. -/
theorem assemble_append {q u r : L} {k A a b : ℕ} (hA : 1 ≤ A)
    {h : BraidRepRespects q u r (k + 1)} {Tail Round : BraidMonoid (k + 1)} {X : Total L}
    (hTail : ((braidRep q u r (k + 1) h Tail (dplusIterPiece q (k + 1)) :
        pieceSub L (k + 1)) : Total L)
      = (-1 : L) ^ (a - 1) • trainDownEnd q (k + 1) 1 (replOneTotal q u a b k X))
    (hRound : RepresentedBy q u r (k + 1) h Round
      (((q * u)⁻¹ * (-1 : L) ^ (a - 1)) • replicatedTotal q u a b k)) :
    ((braidRep q u r (k + 1) h (Round ^ (A - 1) * Tail) (dplusIterPiece q (k + 1)) :
        pieceSub L (k + 1)) : Total L)
      = ((-1 : L) ^ ((a - 1) * A) * (q * u) ^ (1 - (A : ℤ))) • stageTotal q u a b k A X := by
  rw [map_mul, Module.End.mul_apply, hRound.pow (A - 1), hTail, smul_pow, LinearMap.smul_apply,
    map_smul, smul_smul, append_scalar q u a hA, stageTotal_apply]

/-! ### The two tails -/

/-- **The tail at `k ≥ 1`.** `π_{k+1}(T_{k+1↘1}b_{a,b}φ^*_+(B)T_{1↘k+1})d_+^{k+1}(1)`: the two
outer trains' half-powers of `q` cancel, `HJO.Sweep.dplus_dplusIter` and
`HJO.Sweep.braidRep_phiPlusStar_comp_negYOneDPlusStarPiece` carry `π_{k+1}(φ^*_+(B))` past
`-y_1d^*_+`, and `HJO.Mellit.euclid` turns `Ξ_{a,b}(-y_1d^*_+)` into `(-1)^{a-1}Ω(1;a,b)`. -/
theorem tail_value {q u r : L} (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) (hr : r * r = q)
    {k : ℕ} (hk : 1 ≤ k) (h : BraidRepRespects q u r k) (h' : BraidRepRespects q u r (k + 1))
    (a b : ℕ) (B : BraidMonoid k) :
    ((braidRep q u r (k + 1) h'
        (braidTrainDown (k + 1) (k + 1) 1 * slopeBraid (k + 1) a b * phiPlusStar k hk B *
          braidTrainDown (k + 1) 1 (k + 1)) (dplusIterPiece q (k + 1)) :
        pieceSub L (k + 1)) : Total L)
      = (-1 : L) ^ (a - 1) • trainDownEnd q (k + 1) 1 (replOneTotal q u a b k
          ((braidRep q u r k h B (dplusIterPiece q k) : pieceSub L k) : Total L)) := by
  have hrne : r ≠ 0 := fun hz => hq (by rw [← hr, hz, mul_zero])
  have hk1 : 1 ≤ k + 1 := Nat.le_add_left 1 k
  have hTD : RepresentedBy q u r (k + 1) h' (braidTrainDown (k + 1) (k + 1) 1)
      ((r⁻¹ : L) ^ k • trainDownEnd q (k + 1) 1) := by
    simpa only [Nat.add_sub_cancel] using
      representedBy_braidTrainDown_top (q := q) (u := u) (r := r) (h := h') hk1
  have hS : RepresentedBy q u r (k + 1) h' (slopeBraid (k + 1) a b)
      (slopeOperator q u (k + 1) a b) :=
    representedBy_slopeBraid (q := q) (u := u) (r := r) (h := h') hk1 a b
  have hTDb : RepresentedBy q u r (k + 1) h' (braidTrainDown (k + 1) 1 (k + 1))
      (r ^ k • trainDownEnd q 1 (k + 1)) := by
    simpa only [Nat.add_sub_cancel] using
      representedBy_braidTrainDown_bot (q := q) (u := u) (r := r) (h := h') hk1
  -- the bottom train scales the vacuum tower by `q^{k/2}`, every letter of it fixing the tower
  have hbot : braidRep q u r (k + 1) h' (braidTrainDown (k + 1) 1 (k + 1))
      (dplusIterPiece q (k + 1)) = r ^ k • dplusIterPiece q (k + 1) := by
    refine Subtype.ext ?_
    rw [hTDb.apply, LinearMap.smul_apply, coe_dplusIterPiece, trainDownEnd_bot_dplusIter q hq,
      Submodule.coe_smul, coe_dplusIterPiece]
  -- `HJO.Sweep.braidRep_phiPlusStar_comp_negYOneDPlusStarPiece` across `HJO.Sweep.dplus_dplusIter`
  have hphi : braidRep q u r (k + 1) h' (phiPlusStar k hk B) (dplusIterPiece q (k + 1))
      = negYOneDPlusStarPiece q u k (braidRep q u r k h B (dplusIterPiece q k)) := by
    rw [dplusIterPiece_succ q u k]
    exact LinearMap.congr_fun
      (braidRep_phiPlusStar_comp_negYOneDPlusStarPiece q u hq hq1 hqp hr hk h h' B)
      (dplusIterPiece q k)
  rw [map_mul, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, Module.End.mul_apply,
    hbot, map_smul, hphi, map_smul, hTD.apply, LinearMap.smul_apply, Submodule.coe_smul, map_smul,
    hS.apply, coe_negYOneDPlusStarPiece, slopeOperator_negYOneDPlusStar, map_smul, smul_smul,
    smul_smul, inv_pow, inv_mul_cancel₀ (pow_ne_zero k hrne), one_mul]

/-- **The tail at `k = 0`.** The recursion's `φ^*_+(B_{s,v,α})` and all four trains are the
identity, so
the tail is the bare slope braid and the vacuum tower is `d_+^1(1) = (-y_1d^*_+)(1)`. -/
theorem tail_value_zero {q u r : L} (h' : BraidRepRespects q u r 1) (a b : ℕ) :
    ((braidRep q u r 1 h' (slopeBraid 1 a b) (dplusIterPiece q 1) : pieceSub L 1) : Total L)
      = (-1 : L) ^ (a - 1) • trainDownEnd q 1 1 (replOneTotal q u a b 0 (1 : Total L)) := by
  have hS : ∀ x : pieceSub L 1,
      ((braidRep q u r 1 h' (slopeBraid 1 a b) x : pieceSub L 1) : Total L)
        = slopeOperator q u 1 a b x :=
    representedBy_slopeBraid (q := q) (u := u) (r := r) (h := h') le_rfl a b
  rw [hS, dplusIterPiece_succ q u 0, coe_negYOneDPlusStarPiece, coe_dplusIterPiece,
    show dplusIter q 0 = (1 : Total L) from rfl, slopeOperator_negYOneDPlusStar,
    trainDownEnd_one_one, Module.End.one_apply]

/-! ### The recursion -/

variable {q u r : L} {a b A k : ℕ} {e δ θ : ℚ}

/-- **`HJO.Mellit.braidRep_specialBraid_dplusIter`, with the well-definedness of
`HJO.Sweep.braidRep` still a hypothesis.** The unconditional form is
`HJO.Mellit.braidRep_specialBraid_dplusIter`, which supplies it from
`HJO.Sweep.braidRepRespects_mellit`; the two statements are the same one, `BraidRepRespects` being a
`Prop`. -/
theorem braidRep_specialBraid_dplusIter_aux (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0)
    (hr : r * r = q) {w : Fin (k + 1) → ℚ} (H : IsAppendSetup a b A k e δ θ w) {s : ℚ}
    {w₀ : Fin (k + 1) → ℚ} {β : Fin (k + 1) → ℕ}
    (hdata : IsSpecialBraidData s θ (k + 1) w₀ β) (hβ : β 0 = A * (a + b) - 1)
    (hw₀ : w₀ 0 = 1 - θ - δ)
    (hgap : ∀ (t : Fin k) (i : ℕ), i + 1 < β t.succ →
      (nextCrossing θ)^[i] (w₀ t.succ) < w₀ 0 + θ)
    (hstart : ∀ t : Fin k, w₀ t.succ < w₀ 0)
    (hmove : moveTuple θ w₀ ((specialMoveList (β ∘ Fin.succ)).map Fin.succ) = w)
    (h : BraidRepRespects q u r k) (h' : BraidRepRespects q u r (k + 1)) :
    ((braidRep q u r (k + 1) h' (specialBraid θ w₀ β)
        (dplusIterPiece q (k + 1)) : pieceSub L (k + 1)) : Total L)
      = ((-1 : L) ^ ((a - 1) * A) * (q * u) ^ (1 - (A : ℤ))) • stageTotal q u a b k A
          ((braidRep q u r k h (specialBraid θ (w₀ ∘ Fin.succ) (β ∘ Fin.succ))
            (dplusIterPiece q k) : pieceSub L k) : Total L) := by
  have hround := representedBy_round (u := u) hq hr h' a b
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · -- `k = 0`: no other point; both conjugating trains of the round are the identity
    have hw : w₀ = w := by
      rw [← hmove, show (specialMoveList (β ∘ Fin.succ)).map Fin.succ = [] from rfl, moveTuple_nil]
    subst hw
    have hX : ((braidRep q u r 0 h (specialBraid θ (w₀ ∘ Fin.succ) (β ∘ Fin.succ))
        (dplusIterPiece q 0) : pieceSub L 0) : Total L) = 1 := by
      rw [braidRep_zero, Module.End.one_apply, coe_dplusIterPiece]
      rfl
    have hR : braidTrainDown 1 1 1 * slopeBraid 1 a b * braidGenY 1 1 * braidGenZ 1 1 *
        braidTrainUp 1 1 1 = slopeBraid 1 a b * braidGenY 1 1 * braidGenZ 1 1 := by
      rw [braidTrainDown_self, braidTrainUp_self, one_mul, mul_one]
    have hsb : specialBraid θ w₀ β
        = (braidTrainDown 1 1 1 * slopeBraid 1 a b * braidGenY 1 1 * braidGenZ 1 1 *
            braidTrainUp 1 1 1) ^ (A - 1) * slopeBraid 1 a b := by
      rw [hR]
      exact H.specialBraid_eq_slopeBraid_pow' hβ
    rw [hsb, hX]
    exact assemble_append (u := u) H.one_le_A (tail_value_zero h' a b) hround
  · -- `k ≥ 1`: the recursion as stated
    rw [H.specialBraid_eq_appendRhs hk hdata hβ hw₀ hgap hstart hmove, appendRhs,
      show ∀ X Y Z W V : BraidMonoid (k + 1), V ^ (A - 1) * X * Y * Z * W
          = V ^ (A - 1) * (X * Y * Z * W) from fun X Y Z W V => by simp only [mul_assoc]]
    exact assemble_append (u := u) H.one_le_A (tail_value hq hq1 hqp hr hk h h' a b _) hround

/-- **The append-a-part recursion.** For special-braid data `(w₀, β)` of rank
`k+1` satisfying the hypotheses of `HJO.Braid.IsAppendSetup.specialBraid_eq_appendRhs` — the
appended point at `1-θ-δ` weakly below the start `1-θ`, above every other entry and separated
from `1-θ` by no other position of the data, carrying the part `β_0 = A(a+b)-1`, and the other
points clustered at the finish —

`π_{k+1}(B_{s,w₀,β}) d_+^{k+1}(1)
  = (-1)^{(a-1)A}(qu)^{1-A}(Z^{(k+1)}_{a,b})^{A-1}T_{k+1↘1}Ω(1;a,b) π_k(B_{s,v,α}) d_+^k(1)`,

with `(v, α) = (w₀ ∘ Fin.succ, β ∘ Fin.succ)` the deleted rank-`k` data and the operator standing
to the left of the last factor written as `HJO.Mellit.stageTotal`, which is `HJO.Mellit.stage` on
the grading `k` by `HJO.Mellit.sweepWitness_stage_sweepIn`. The `Ω`-form is
`HJO.Mellit.sweepIn_braidRep_specialBraid`.

**Both cases of the composition are here.** At `k = 0` there is no other point,
`HJO.Braid.phiPlusStar` is not defined and all four trains are the identity; the conclusion names
none of those, so the `k = 0` clause
`HJO.Braid.IsAppendSetup.specialBraid_eq_slopeBraid_pow'` assembles into the same statement, with
`π_0` the unique homomorphism out of the trivial monoid and `d_+^0(1) = 1`.

**The parameter `r` is the `q^{1/2}`** and does not occur in the right-hand side: the
half-powers the three trains contribute cancel exactly, the tail's `T_{1↘k+1}` against its
`T_{k+1↘1}` and each round's two into the `q^{-k}` of `HJO.Mellit.replicatedLetter`. -/
@[hjo "lem_mellit_append"]
theorem braidRep_specialBraid_dplusIter (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0)
    (hr : r * r = q) {w : Fin (k + 1) → ℚ} (H : IsAppendSetup a b A k e δ θ w) {s : ℚ}
    {w₀ : Fin (k + 1) → ℚ} {β : Fin (k + 1) → ℕ}
    (hdata : IsSpecialBraidData s θ (k + 1) w₀ β) (hβ : β 0 = A * (a + b) - 1)
    (hw₀ : w₀ 0 = 1 - θ - δ)
    (hgap : ∀ (t : Fin k) (i : ℕ), i + 1 < β t.succ →
      (nextCrossing θ)^[i] (w₀ t.succ) < w₀ 0 + θ)
    (hstart : ∀ t : Fin k, w₀ t.succ < w₀ 0)
    (hmove : moveTuple θ w₀ ((specialMoveList (β ∘ Fin.succ)).map Fin.succ) = w) :
    ((braidRepMellit q u hq hq1 hqp hr (k + 1) (specialBraid θ w₀ β)
        (dplusIterPiece q (k + 1)) : pieceSub L (k + 1)) : Total L)
      = ((-1 : L) ^ ((a - 1) * A) * (q * u) ^ (1 - (A : ℤ))) • stageTotal q u a b k A
          ((braidRepMellit q u hq hq1 hqp hr k (specialBraid θ (w₀ ∘ Fin.succ) (β ∘ Fin.succ))
            (dplusIterPiece q k) : pieceSub L k) : Total L) :=
  braidRep_specialBraid_dplusIter_aux hq hq1 hqp hr H hdata hβ hw₀ hgap hstart hmove
    (braidRepRespects_mellit q u hq hq1 hqp hr k)
    (braidRepRespects_mellit q u hq hq1 hqp hr (k + 1))

/-- **`HJO.Mellit.braidRep_specialBraid_dplusIter` with `Ω` itself**, which is the recursion
verbatim: for every replication family `Ω` of the sweep system `HJO.Mellit.sweepWitness`,

`π_{k+1}(B_{s,w₀,β}) d_+^{k+1}(1)
  = (-1)^{(a-1)A}(qu)^{1-A} G_{k+1,A}\big(π_k(B_{s,v,α}) d_+^k(1)\big)`

with `G_{k+1,A} = (Z^{(k+1)}_{a,b})^{A-1}T_{k+1↘1}Ω(1;a,b)` the stage `HJO.Mellit.stage`,
read in the grading it belongs to through `HJO.Mellit.sweepIn`.

The two forms are equivalent, `HJO.Mellit.sweepIn` being injective
(`HJO.Mellit.sweepIn_injective`); which replication family is used does not matter, since
`HJO.Mellit.euclid` pins both of the values the stage reads
(`HJO.Mellit.sweepWitness_stage_sweepIn`). -/
@[hjo "lem_mellit_append"]
theorem sweepIn_braidRep_specialBraid (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0)
    (hr : r * r = q)
    {Ω : ℕ → ℕ → ℕ → ((sweepWitness q u a b).W →ₗ[L] (sweepWitness q u a b).W)}
    (hΩ : IsReplicationFamily (sweepWitness q u a b) Ω)
    {w : Fin (k + 1) → ℚ} (H : IsAppendSetup a b A k e δ θ w) {s : ℚ}
    {w₀ : Fin (k + 1) → ℚ} {β : Fin (k + 1) → ℕ}
    (hdata : IsSpecialBraidData s θ (k + 1) w₀ β) (hβ : β 0 = A * (a + b) - 1)
    (hw₀ : w₀ 0 = 1 - θ - δ)
    (hgap : ∀ (t : Fin k) (i : ℕ), i + 1 < β t.succ →
      (nextCrossing θ)^[i] (w₀ t.succ) < w₀ 0 + θ)
    (hstart : ∀ t : Fin k, w₀ t.succ < w₀ 0)
    (hmove : moveTuple θ w₀ ((specialMoveList (β ∘ Fin.succ)).map Fin.succ) = w) :
    sweepIn q u a b (k + 1)
        ((braidRepMellit q u hq hq1 hqp hr (k + 1) (specialBraid θ w₀ β)
          (dplusIterPiece q (k + 1)) : pieceSub L (k + 1)) : Total L)
      = ((-1 : L) ^ ((a - 1) * A) * (q * u) ^ (1 - (A : ℤ))) •
          stage (sweepWitness q u a b) Ω a b k A (sweepIn q u a b k
            ((braidRepMellit q u hq hq1 hqp hr k (specialBraid θ (w₀ ∘ Fin.succ) (β ∘ Fin.succ))
              (dplusIterPiece q k) : pieceSub L k) : Total L)) := by
  rw [sweepWitness_stage_sweepIn H.coprime H.one_le_a H.one_le_b hΩ,
    braidRep_specialBraid_dplusIter hq hq1 hqp hr H hdata hβ hw₀ hgap hstart hmove, map_smul]

end HJO.Mellit

end
