/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.Parameters
public import HJO.CarlssonMellit.SweepCM
public import HJO.CarlssonMellit.BraidInverse
public import HJO.CMStructure.DpaActionBuild
public import HJO.Shuffle.CMRaising
public import HJO.Shuffle.MellitShiftGenerators
public meta import HJO.Attr

/-! # The conjugation operator on `V_*`

`HJO.Sweep.IsConjugationOperator`: an additive map `𝒩 : V_* → V_*` is a *conjugation operator* if it
is antilinear over the bar of `HJO.Sym.paramInvLambda`, is an involution, fixes `1 ∈ V_0`, commutes
with `d_-`, carries `d_+` to `d_+^*`, preserves each summand `V_k`, and carries each loop `T_i` to
its polynomial inverse `T̂_i = q⁻¹(T_i + (q - 1))` of `HJO.Dyck.braidInvGen`.

## `V_*` and not the total space, and why that matters here

Everywhere else in this library the operators of the layer are endomorphisms of the one space
`HJO.Sweep.Total`, and the domains and codomains are membership statements. This predicate is the
exception, because `𝒩` is an operator on `V_*`, pinned by its *letterwise action* there, and
applying `𝒩` to an element of the algebra does not typecheck. So the predicate below is about
`HJO.Sweep.Vstar`, the direct sum `⨁_k V_k` of `HJO.Sweep.Vstar` — the summands are independent
there, whereas the pieces `HJO.Sweep.piece` are nested inside `Total` and their union is all of it.

That forces the three operators to be assembled as endomorphisms of the direct sum, which is what
`HJO.Sweep.dminusVstar`, `HJO.Sweep.cmDPlusVstar` and `HJO.Sweep.dplusStarVstar` are: on each
summand the existing operator, with its codomain given by the membership lemma, and `d_-` killing
the summand `V_0`, there being no summand below it.

**The two intertwining clauses are stated on the summands, not on all of `V_*`.** The definition
asks `𝒩(d_-F) = d_-𝒩(F)` for `F ∈ V_k` with `k ≥ 1` and `𝒩(d_+F) = d_+^*𝒩(F)` for `F ∈ V_k` with
`k ≥ 0`, and the fields say exactly that. Given the summand clause the two readings agree — at
`F ∈ V_0` the left side of the first is `𝒩(0) = 0` and the right side is `d_-` of an element of
`V_0`, which is `0` too — but the summand form matches the definition, so it is kept.

**The loop clause is stated on all of `V_*`.** The definition writes `𝒩(T_iF) = T̂_i𝒩(F)` with no
restriction on `F`, `T_i` and `T̂_i` being elements of the algebra acting on `V_*`. The loop `T_i`
at the vertex `k` acts as `HJO.Sweep.loopVstar (HJO.Sweep.braidModPiece q) k i` — the operator
`T_i` of `V_k` on that summand, `0` on the others — and `T̂_i = q⁻¹(T_i + (q - 1)e_k)` as the
corresponding combination with the projection `HJO.Sweep.pieceProj` onto `V_k`. The inverse of
`q` is the field inverse `q⁻¹`, so the predicate needs no `[Invertible q]`; when `q` is a unit the
operator is `HJO.Dyck.braidInvGen` of the loop and the projection
(`HJO.Sweep.IsConjugationOperator.map_loop_braidInvGen`).

## What is not asked

Nothing here asserts that a conjugation operator exists; one is constructed at
`HJO.Sweep.exists_isConjugationOperator` and this predicate is a hypothesis for its consumers,
exactly as `HJO.Sym.IsMacdonaldConjugator` and `HJO.Sym.IsIndexShift` are. Nor is `𝒩` asked to send
`y_i` to `z_i`, which holds of its construction but the definition does not ask.

## Main definitions

* `HJO.Sweep.dminusVstar`, `HJO.Sweep.cmDPlusVstar`, `HJO.Sweep.dplusStarVstar`: the three
  operators of `HJO.Sweep.dminusCM`, `HJO.Sweep.cmDPlus` and `HJO.Sweep.dplusStar` as endomorphisms
  of `V_*`.
* `HJO.Sweep.oneVstar`: the element `1` of `V_0` inside `V_*`, which is the `1` of `𝒩(1) = 1`.
* `HJO.Sweep.IsConjugationOperator`, with its seven clauses.

## Main results

* `HJO.Sweep.IsConjugationOperator.pieceProj_comm`: `𝒩` commutes with each projection `e_k`.
* `HJO.Sweep.IsConjugationOperator.map_loop_braidInvGen`: the loop clause with
  `HJO.Dyck.braidInvGen`.

## References

This file formalises the definition `HJO.Sweep.IsConjugationOperator`, using `HJO.Sweep.Vstar`,
`HJO.Sym.paramInvLambda`, `HJO.Sweep.cmDPlus`, `HJO.Sweep.dminusCM`, `HJO.Sweep.dplusStar`,
`HJO.Dyck.braidInvGen`, and its consumer `HJO.Sweep.conjugation_eq_signGrading_conjugator_omegaBar`.
-/

@[expose] public section

namespace HJO.Sweep

/-! ### The lowering operator drops the level -/

section Piece

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **`d_-` carries `V_{k+1}` into `V_k`**, the codomain `HJO.Sweep.dminusCM` gives it. It is the
codomain of the modified operator (`HJO.Sweep.dminus_mem_piece`) read through the comparison
`d_-F = -d^♭_-(y_{k+1}F)` of `HJO.Sweep.dminusCM_eq_neg_dminus_auxVar_mul`: multiplying by `y_{k+1}`
stays inside `V_{k+1}`. -/
theorem dminusCM_mem_piece (q : L) (k : ℕ) {F : Total L} (hF : F ∈ piece L (k + 1)) :
    dminusCM q (k + 1) F ∈ piece L k := by
  rw [dminusCM_eq_neg_dminus_auxVar_mul]
  refine neg_mem ?_
  have h := dminus_mem_piece q (k + 1)
    (mul_mem (auxVar_mem_piece (by omega) le_rfl) hF)
  simpa using h

/-- `d_-` as a map between the graded pieces, `V_{k+1} → V_k`. -/
noncomputable def dminusPiece (q : L) (k : ℕ) : pieceSub L (k + 1) →ₗ[L] pieceSub L k :=
  (dminusCM q (k + 1)).restrict fun _ hx => dminusCM_mem_piece q k hx

/-- `d_+` as a map between the graded pieces, `V_k → V_{k+1}`. -/
noncomputable def cmDPlusPiece (q : L) (k : ℕ) : pieceSub L k →ₗ[L] pieceSub L (k + 1) :=
  (cmDPlus q k).restrict fun _ hx => cmDPlus_mem_piece q k hx

/-- `d_+^*` as a map between the graded pieces, `V_k → V_{k+1}`. -/
noncomputable def dplusStarPiece (q u : L) (k : ℕ) : pieceSub L k →ₗ[L] pieceSub L (k + 1) :=
  (dplusStar q u k).restrict fun _ hx => dplusStar_mem_piece q u hx

@[simp]
theorem coe_dminusPiece (q : L) (k : ℕ) (F : pieceSub L (k + 1)) :
    (dminusPiece q k F : Total L) = dminusCM q (k + 1) F := rfl

omit [Algebra ℚ L] in
@[simp]
theorem coe_cmDPlusPiece (q : L) (k : ℕ) (F : pieceSub L k) :
    (cmDPlusPiece q k F : Total L) = cmDPlus q k F := rfl

omit [Algebra ℚ L] in
@[simp]
theorem coe_dplusStarPiece (q u : L) (k : ℕ) (F : pieceSub L k) :
    (dplusStarPiece q u k F : Total L) = dplusStar q u k F := rfl

end Piece

/-! ### The three operators on `V_*` -/

section Vstar

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- The level family of `d_-`: on `V_{k+1}` the lowering operator into `V_k`, and `0` on `V_0`. -/
noncomputable def dminusLevel (q : L) (k : ℕ) : pieceSub L k →ₗ[L] Vstar L :=
  match k with
  | 0 => 0
  | k + 1 => (ofPiece L k).comp (dminusPiece q k)

theorem dminusLevel_zero (q : L) : dminusLevel q 0 = 0 := rfl

theorem dminusLevel_succ (q : L) (k : ℕ) :
    dminusLevel q (k + 1) = (ofPiece L k).comp (dminusPiece q k) := rfl

/-- The level family of `d_+`: on `V_k` the raising operator into `V_{k+1}`. -/
noncomputable def cmDPlusLevel (q : L) (k : ℕ) : pieceSub L k →ₗ[L] Vstar L :=
  (ofPiece L (k + 1)).comp (cmDPlusPiece q k)

/-- The level family of `d_+^*`: on `V_k` the starred raising operator into `V_{k+1}`. -/
noncomputable def dplusStarLevel (q u : L) (k : ℕ) : pieceSub L k →ₗ[L] Vstar L :=
  (ofPiece L (k + 1)).comp (dplusStarPiece q u k)

/-- **`d_-` as an endomorphism of `V_*`**: on the summand `V_{k+1}` it is the lowering operator of
`HJO.Sweep.dminusCM` into the summand `V_k`, and it kills `V_0`, there being no summand below it. -/
noncomputable def dminusVstar (q : L) : Vstar L →ₗ[L] Vstar L :=
  DirectSum.toModule L ℕ (Vstar L) (dminusLevel q)

/-- **`d_+` as an endomorphism of `V_*`**: on the summand `V_k` it is the raising operator of
`HJO.Sweep.cmDPlus` into the summand `V_{k+1}`. -/
noncomputable def cmDPlusVstar (q : L) : Vstar L →ₗ[L] Vstar L :=
  DirectSum.toModule L ℕ (Vstar L) (cmDPlusLevel q)

/-- **`d_+^*` as an endomorphism of `V_*`**: on the summand `V_k` it is the starred raising operator
of `HJO.Sweep.dplusStar` into the summand `V_{k+1}`. -/
noncomputable def dplusStarVstar (q u : L) : Vstar L →ₗ[L] Vstar L :=
  DirectSum.toModule L ℕ (Vstar L) (dplusStarLevel q u)

theorem dminusVstar_ofPiece (q : L) (k : ℕ) (F : pieceSub L (k + 1)) :
    dminusVstar q (ofPiece L (k + 1) F) = ofPiece L k (dminusPiece q k F) := by
  rw [dminusVstar, ofPiece, DirectSum.toModule_lof, dminusLevel_succ, LinearMap.comp_apply]

theorem dminusVstar_ofPiece_zero (q : L) (F : pieceSub L 0) :
    dminusVstar q (ofPiece L 0 F) = 0 := by
  rw [dminusVstar, ofPiece, DirectSum.toModule_lof, dminusLevel_zero, LinearMap.zero_apply]

omit [Algebra ℚ L] in
theorem cmDPlusVstar_ofPiece (q : L) (k : ℕ) (F : pieceSub L k) :
    cmDPlusVstar q (ofPiece L k F) = ofPiece L (k + 1) (cmDPlusPiece q k F) := by
  rw [cmDPlusVstar, ofPiece, DirectSum.toModule_lof, cmDPlusLevel, LinearMap.comp_apply]

omit [Algebra ℚ L] in
theorem dplusStarVstar_ofPiece (q u : L) (k : ℕ) (F : pieceSub L k) :
    dplusStarVstar q u (ofPiece L k F) = ofPiece L (k + 1) (dplusStarPiece q u k F) := by
  rw [dplusStarVstar, ofPiece, DirectSum.toModule_lof, dplusStarLevel, LinearMap.comp_apply]

/-- **The element `1` of `V_0` inside `V_*`**, which is the `1` of the clause `𝒩(1) = 1`. `V_*` is
not a ring, so the `1` of that clause has to be named: it is the unit of `Λ = V_0` read in the
zeroth summand. -/
noncomputable def oneVstar (L : Type*) [Field L] : Vstar L :=
  ofPiece L 0 ⟨1, one_mem (piece L 0)⟩

end Vstar

/-! ### The conjugation operator -/

section Conjugation

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **A conjugation operator.** An additive map `𝒩 : V_* → V_*` is a
conjugation operator if

* it is antilinear over the bar `σ` of `HJO.Sym.paramInvLambda`: `𝒩(cF) = c̄𝒩(F)`;
* it is an involution: `𝒩(𝒩(F)) = F`;
* it fixes `1 ∈ V_0`;
* it commutes with `d_-` on every summand `V_{k+1}`;
* it carries `d_+` to `d_+^*` on every summand `V_k`;
* it preserves every summand: `𝒩(V_k) ⊆ V_k`;
* it carries each loop `T_i` to its polynomial inverse `T̂_i = q⁻¹(T_i + (q - 1))` of
  `HJO.Dyck.braidInvGen`: `𝒩(T_iF) = T̂_i𝒩(F)`.

Nothing here asserts that such an `𝒩` exists; that is `HJO.Sweep.exists_isConjugationOperator`.

The two intertwining clauses are quantified over the summands and not over all of `V_*`, for the
reason in the module docstring. The loop clause is read on all of `V_*`, as the definition states
it: the loop `T_i` at the vertex `k` acts as `T_i` on `V_k` and as `0` on every other summand, and
`T̂_i` acts as `q⁻¹(T_i + (q - 1)e_k)`, with `e_k` the projection onto `V_k`. -/
@[hjo "def_cm_conjugation"]
structure IsConjugationOperator (q u : L) (σ : L ≃+* L) (N : Vstar L →+ Vstar L) : Prop where
  /-- `𝒩(cF) = c̄𝒩(F)`: `𝒩` is antilinear over the bar of `HJO.Sym.paramInvLambda`. -/
  map_smul : ∀ (c : L) (F : Vstar L), N (c • F) = σ c • N F
  /-- `𝒩(𝒩(F)) = F`. -/
  involutive : ∀ F : Vstar L, N (N F) = F
  /-- `𝒩(1) = 1`, the `1` being the unit of `V_0`. -/
  map_one : N (oneVstar L) = oneVstar L
  /-- `𝒩(d_-F) = d_-𝒩(F)` for every `F ∈ V_k` with `k ≥ 1`. -/
  map_dminus : ∀ (k : ℕ) (F : pieceSub L (k + 1)),
    N (dminusVstar q (ofPiece L (k + 1) F)) = dminusVstar q (N (ofPiece L (k + 1) F))
  /-- `𝒩(d_+F) = d_+^*𝒩(F)` for every `F ∈ V_k` with `k ≥ 0`. -/
  map_dplus : ∀ (k : ℕ) (F : pieceSub L k),
    N (cmDPlusVstar q (ofPiece L k F)) = dplusStarVstar q u (N (ofPiece L k F))
  /-- `𝒩(V_k) ⊆ V_k` for every `k`. -/
  map_piece : ∀ (k : ℕ) (F : pieceSub L k),
    ∃ G : pieceSub L k, N (ofPiece L k F) = ofPiece L k G
  /-- `𝒩(T_iF) = T̂_i𝒩(F)`, with `T̂_i = q⁻¹(T_i + (q - 1)e_k)`, for the loop `T_i` at every
  vertex `k ≥ 2`, `1 ≤ i ≤ k - 1` (written `i + 2 ≤ k` in the shifted indexing of the loops). -/
  map_loop : ∀ {k i : ℕ}, i + 2 ≤ k → ∀ F : Vstar L,
    N (loopVstar (braidModPiece q) k i F)
      = q⁻¹ • (loopVstar (braidModPiece q) k i (N F) + (q - 1) • pieceProj L k (N F))

namespace IsConjugationOperator

variable {q u : L} {σ : L ≃+* L} {N : Vstar L →+ Vstar L}

/-- **`𝒩` lands in the summand it started in**, the summand clause in the form the other clauses
consume: `𝒩(F)` for `F ∈ V_k` is its own projection onto `V_k`. -/
theorem ofPiece_toPiece (hN : IsConjugationOperator q u σ N) (k : ℕ) (F : pieceSub L k) :
    N (ofPiece L k F) = ofPiece L k (toPiece L k (N (ofPiece L k F))) := by
  obtain ⟨G, hG⟩ := hN.map_piece k F
  rw [hG, toPiece_ofPiece]

/-- **`𝒩` commutes with the projections `e_k`**: the summand clause read on all of `V_*`, by
additivity of `𝒩` over the direct sum. -/
theorem pieceProj_comm (hN : IsConjugationOperator q u σ N) (k : ℕ) (F : Vstar L) :
    N (pieceProj L k F) = pieceProj L k (N F) := by
  induction F using DirectSum.induction_on with
  | zero => simp
  | of l x =>
    change N (pieceProj L k (ofPiece L l x)) = pieceProj L k (N (ofPiece L l x))
    obtain ⟨G, hG⟩ := hN.map_piece l x
    rw [hG]
    by_cases hlk : l = k
    · subst hlk
      rw [pieceProj_ofPiece, pieceProj_ofPiece, hG]
    · rw [pieceProj_ofPiece_of_ne hlk, pieceProj_ofPiece_of_ne hlk, map_zero]
  | add F G hF hG => rw [map_add, map_add, hF, hG, map_add, map_add]

/-- **The loop clause with the polynomial inverse of `HJO.Dyck.braidInvGen`**: when `q` is a unit,
the operator `q⁻¹(T_i + (q - 1)e_k)` of the clause is `HJO.Dyck.braidInvGen` of the loop and the
projection. -/
theorem map_loop_braidInvGen [Invertible q] (hN : IsConjugationOperator q u σ N) {k i : ℕ}
    (hik : i + 2 ≤ k) (F : Vstar L) :
    N (loopVstar (braidModPiece q) k i F)
      = Dyck.braidInvGen L q (loopVstar (braidModPiece q) k i) (pieceProj L k) (N F) := by
  rw [hN.map_loop hik, Dyck.braidInvGen, invOf_eq_inv]
  rfl

end IsConjugationOperator

end Conjugation

end HJO.Sweep
