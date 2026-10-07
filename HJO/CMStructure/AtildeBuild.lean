/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CMStructure.StarAction
public import HJO.CarlssonMellit.DPATildeIdeals
public meta import HJO.Attr

/-! # Building an action of the extended Dyck path algebra out of three mixed relations

`HJO.Dyck.Tilde.Atilde` presents `Ã` as a `RingQuot` of the free algebra on the arrows of the
enlarged quiver, by three groups of relations: Carlsson and Mellit's list in the unstarred
generators, the same list read after the substitution `q ↦ q⁻¹`, `d₊ ↦ d₊^*`, `T_i ↦ T_i⁻¹`, and the
three mixed relations. So producing an action of `Ã` on `V_*` means: send each generator to an
operator, lift through `FreeAlgebra.lift`, and check those three groups together with the quiver's
own structure.

Two of the three groups are already proved, as `HJO.Sweep.exists_isDpaAction_cm` and the action half
of `HJO.Sweep.exists_isDpaAction_star`: `HJO.Sweep.isDpaOperators_cm` and
`HJO.Sweep.isDpaOperators_star` are exactly Carlsson and Mellit's list for the two operator
families. This file does the plumbing once — the quiver's nine relations, the transport of
`HJO.Dyck.SourceRel` along the lift, and the descent to the `RingQuot` — leaving the three mixed
relations as hypotheses, which is what `HJO.CMStructure.AtildeMixed` discharges.

## Main definitions

* `HJO.Dyck.SourceRel.map` — Carlsson and Mellit's relation list transports along an algebra map.
  This is what makes the starred group a *statement* about the lift rather than a second
  transcription.
* `HJO.Sweep.genOpTilde` — the assignment of the generators of the enlarged quiver to operators.
* `HJO.Sweep.tinvVstar`, `HJO.Sweep.yOpVstar`, `HJO.Sweep.zOpVstar` — the images under the lift of
  the polynomial inverse `T̂_{i+1}` and of the corner elements `y_i` and `z_i` of
  `HJO.Dyck.Tilde.Atilde`.

## Main results

* `HJO.Sweep.IsDpaOperators.eq_of_sourceRel` — Carlsson and Mellit's relations, read on `V_*`, hold
  for any triple of operator families satisfying `HJO.Sweep.IsDpaOperators`, for any loop family
  agreeing with it inside the quiver's range.
* `HJO.Sweep.exists_action_atilde_of_mixed` — the construction: the two proved groups plus the three
  mixed relations give an action of `Ã` on `V_*`.

## Implementation notes

**The loop family of the starred group is not `T_i⁻¹` outside the quiver's range.**
`HJO.Dyck.Tilde.Atilde` substitutes `T_i ↦ T̂_i = q⁻¹(T_i + (q-1)e_k)`, and at `k ≤ i + 1`, where
the quiver has no loop and `T_i = 0`, that formula is `q⁻¹(q-1)e_k` and not `0`. So the starred
group cannot be read off `HJO.Sweep.braidInvModPiece` directly. It need not be: every occurrence of
a loop inside
`HJO.Dyck.SourceRel` carries the range hypothesis `i + 2 ≤ k` — including the three that look
unrestricted, `T_1d₊²`, `d₋²T_{k-1}` and the two commutator relations, whose indices are `0` at the
vertex `k + 2` and `m` at the vertex `m + 2` — so agreement inside the range is all that is used,
which is the hypothesis `hT'` of `HJO.Sweep.IsDpaOperators.eq_of_sourceRel`.

## References

This file builds the definitions `HJO.Dyck.Tilde.Atilde` and `HJO.Dyck.Aq`, with `HJO.Sweep.Vstar`;
the result it serves is the action half of `HJO.Standing.exists_action_atilde_ker_eq_param`.
E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, §3 and §5.
-/

@[expose] public section

namespace HJO.Dyck

/-! ### Carlsson and Mellit's relations transport along an algebra map -/

section Map

variable {K : Type*} [CommRing K] {A : Type*} [Ring A] [Algebra K A]
  {B : Type*} [Ring B] [Algebra K B] (f : A →ₐ[K] B)
  {E U D : ℕ → A} {T : ℕ → ℕ → A} {E' U' D' : ℕ → B} {T' : ℕ → ℕ → B} {q : K}

/-- **Carlsson and Mellit's relations transport along an algebra map**: if `f` carries each family
to the corresponding one, then every instance of `HJO.Dyck.SourceRel` in the first family is an
instance in the second, at the same scalar. Applied to `FreeAlgebra.lift` this is what turns "the
operators satisfy the starred group" into a statement about the two proved relation packages. -/
theorem SourceRel.map (hE : ∀ n, f (E n) = E' n) (hU : ∀ n, f (U n) = U' n)
    (hD : ∀ n, f (D n) = D' n) (hT : ∀ n i, f (T n i) = T' n i) {x y : A}
    (h : SourceRel q E U D T x y) : SourceRel q E' U' D' T' (f x) (f y) := by
  induction h with
  | vertex_mul_up k =>
    simp only [map_mul, hE, hU]
    exact SourceRel.vertex_mul_up k
  | up_mul_vertex k =>
    simp only [map_mul, hU, hE]
    exact SourceRel.up_mul_vertex k
  | quadratic h =>
    simp only [map_mul, map_sub, map_add, map_smul, hT, hE, map_zero]
    exact SourceRel.quadratic h
  | braid_braid h =>
    simp only [map_mul, hT]
    exact SourceRel.braid_braid h
  | braid_comm hi hj hij =>
    simp only [map_mul, hT]
    exact SourceRel.braid_comm hi hj hij
  | braid_down h =>
    simp only [map_mul, hT, hD]
    exact SourceRel.braid_down h
  | up_braid h =>
    simp only [map_mul, hT, hU]
    exact SourceRel.up_braid h
  | braid_up_up k =>
    simp only [map_mul, hT, hU]
    exact SourceRel.braid_up_up k
  | down_down_braid m =>
    simp only [map_mul, hT, hD]
    exact SourceRel.down_down_braid m
  | down_delta j =>
    simp only [map_mul, map_smul, map_commOf f hU hD, hD, hT]
    exact SourceRel.down_delta j
  | braid_delta m =>
    simp only [map_mul, map_smul, map_commOf f hU hD, hU, hT]
    exact SourceRel.braid_delta m

end Map

end HJO.Dyck

namespace HJO.Sweep

/-! ### Carlsson and Mellit's relations, read on `V_*` -/

section SourceVstar

variable {L : Type*} [CommRing L] {q' : L}
  {T : ∀ k : ℕ, ℕ → (pieceSub L k →ₗ[L] pieceSub L k)}
  {D : ∀ k : ℕ, pieceSub L (k + 1) →ₗ[L] pieceSub L k}
  {U : ∀ k : ℕ, pieceSub L k →ₗ[L] pieceSub L (k + 1)}

/-- **Carlsson and Mellit's relations hold on `V_*` for any triple satisfying the nine relations**,
at any loop family agreeing with the given one inside the quiver's range `i + 2 ≤ k`. That range
covers every occurrence of a loop in `HJO.Dyck.SourceRel`, which is why the starred group can be
read at `HJO.Dyck.Tilde.Atilde`'s substituted family `T̂` even though `T̂` is not `T⁻¹` outside the
range. -/
theorem IsDpaOperators.eq_of_sourceRel (h : IsDpaOperators q' T D U)
    {T' : ℕ → ℕ → Module.End L (Vstar L)}
    (hT' : ∀ k i : ℕ, i + 2 ≤ k → T' k i = loopVstar T k i) {x y : Module.End L (Vstar L)}
    (hr : Dyck.SourceRel q' (pieceProj L) (raiseVstar U) (lowerVstar D) T' x y) : x = y := by
  induction hr with
  | vertex_mul_up k => exact pieceProj_mul_raiseVstar k
  | up_mul_vertex k => exact raiseVstar_mul_pieceProj k
  | quadratic hik =>
    rw [hT' _ _ hik]
    exact h.loopVstar_quadratic hik
  | braid_braid hik =>
    rw [hT' _ _ (by omega), hT' _ _ (by omega)]
    exact h.loopVstar_braid hik
  | braid_comm hi hj hij =>
    rw [hT' _ _ hi, hT' _ _ hj]
    exact h.loopVstar_comm hi hj hij
  | braid_down him =>
    rw [hT' _ _ him, hT' _ _ (by omega)]
    exact h.loopVstar_mul_lowerVstar him
  | up_braid hik =>
    rw [hT' _ _ hik, hT' _ _ (by omega)]
    exact h.raiseVstar_mul_loopVstar hik
  | braid_up_up k =>
    rw [hT' _ _ (by omega)]
    exact h.loopVstar_mul_raiseVstar_raiseVstar k
  | down_down_braid m =>
    rw [hT' _ _ (by omega)]
    exact h.lowerVstar_lowerVstar_mul_loopVstar m
  | down_delta j =>
    rw [hT' _ _ (by omega)]
    exact h.lowerVstar_mul_deltaVstar_mul_loopVstar j
  | braid_delta m =>
    rw [hT' _ _ (by omega)]
    exact h.loopVstar_mul_deltaVstar_mul_raiseVstar m

end SourceVstar

/-! ### The substituted loop family and the two corner families, on `V_*` -/

section Families

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **The image of `HJO.Dyck.Tilde.Atilde`'s substituted loop `T̂_{i+1}`** on `V_*`: the polynomial
inverse `q⁻¹(T_{i+1} + (q-1)𝟏_k)` of the Demazure--Lusztig operator at the vertex `k`. Inside the
quiver's range this is `HJO.Sweep.braidInvModPiece` read on `V_*`
(`HJO.Sweep.tinvVstar_eq_loopVstar`); outside it, where the quiver has no loop, it is
`q⁻¹(q-1)𝟏_k` and not `0`. -/
noncomputable def tinvVstar (q : L) [Invertible q] (k i : ℕ) : Module.End L (Vstar L) :=
  Dyck.tinvOf q ⅟q (loopVstar (braidModPiece q) k i) (pieceProj L k)

/-- **The image of the corner element `y_i`** of `HJO.Dyck.Aq.yElt` at the vertex `k`, on `V_*`:
`HJO.Dyck.cornerOf` at the unstarred operator families. -/
noncomputable def yOpVstar (q : L) [Invertible q] [Invertible (q - 1)] (k i : ℕ) :
    Module.End L (Vstar L) :=
  Dyck.cornerOf q ⅟q ⅟(q - 1) (pieceProj L) (raiseVstar (cmDPlusPiece q))
    (lowerVstar (dminusPiece q)) (loopVstar (braidModPiece q)) k i

/-- **The image of the corner element `z_i`** of `HJO.Dyck.Tilde.Atilde` at the vertex `k`, on
`V_*`: `HJO.Dyck.cornerOf` at the starred operator families and the substituted scalars `q⁻¹ ↦ q`
and `(q⁻¹-1)⁻¹ = -q(q-1)⁻¹`. -/
noncomputable def zOpVstar (q u : L) [Invertible q] [Invertible (q - 1)] (k i : ℕ) :
    Module.End L (Vstar L) :=
  Dyck.cornerOf (⅟q) q (-(q * ⅟(q - 1))) (pieceProj L) (raiseVstar (dplusStarPiece q u))
    (lowerVstar (dminusPiece q)) (tinvVstar q) k i

variable (q : L) [Invertible q]

omit [Algebra ℚ L] in
/-- **The substituted loop kills every summand but the one its vertex names.** -/
theorem tinvVstar_apply_ofPiece_of_ne {k l : ℕ} (hl : l ≠ k) (i : ℕ) (F : pieceSub L l) :
    tinvVstar q k i (ofPiece L l F) = 0 := by
  rw [tinvVstar, Dyck.tinvOf, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.smul_apply,
    loopVstar_ofPiece_of_ne i hl, pieceProj_ofPiece_of_ne hl, smul_zero, add_zero, smul_zero]

omit [Algebra ℚ L] in
/-- **Inside the quiver's range the substituted loop is the inverted loop.** -/
theorem tinvVstar_eq_loopVstar {k i : ℕ} (h : i + 2 ≤ k) :
    tinvVstar q k i = loopVstar (braidInvModPiece q) k i := by
  have hq : q ≠ 0 := Invertible.ne_zero q
  refine vstar_ext fun l F => ?_
  rw [tinvVstar, Dyck.tinvOf, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.smul_apply]
  rcases eq_or_ne l k with rfl | hl
  · rw [loopVstar_ofPiece, pieceProj_ofPiece, loopVstar_ofPiece, ← map_smul, ← map_add, ← map_smul]
    refine ofPiece_congr ?_
    rw [SetLike.val_smul, AddMemClass.coe_add, SetLike.val_smul, coe_braidModPiece q h,
      coe_braidInvModPiece q h, smul_eq_scal_mul, smul_eq_scal_mul, braidInv_apply,
      invOf_eq_inv]
  · rw [loopVstar_ofPiece_of_ne _ hl, pieceProj_ofPiece_of_ne hl, loopVstar_ofPiece_of_ne _ hl,
      smul_zero, add_zero, smul_zero]

end Families

/-! ### The action -/

section Build

variable {L : Type*} [Field L] [Algebra ℚ L] (q u : L) [Invertible q] [Invertible (q - 1)]

/-- The assignment of the generators of the enlarged quiver of `HJO.Dyck.Tilde.Atilde` to operators
on `V_*`: the idempotent at the vertex `k` to the projection onto `V_k`, the two raising arrows to
`d_+` and `d^*_+`, the lowering arrow to `d_-`, and the loops to the Demazure--Lusztig operators. -/
noncomputable def genOpTilde : Dyck.Tilde.Gen → Module.End L (Vstar L)
  | .vertex k => pieceProj L k
  | .up k => raiseVstar (cmDPlusPiece q) k
  | .upStar k => raiseVstar (dplusStarPiece q u) k
  | .down k => lowerVstar (dminusPiece q) k
  | .braid k i => loopVstar (braidModPiece q) k i

/-- The lift of `HJO.Sweep.genOpTilde` to the free algebra on the enlarged quiver. -/
noncomputable def liftTilde : FreeAlgebra L Dyck.Tilde.Gen →ₐ[L] Module.End L (Vstar L) :=
  FreeAlgebra.lift L (genOpTilde q u)

omit [Invertible q] [Invertible (q - 1)] in
@[simp] theorem liftTilde_freeE (k : ℕ) :
    liftTilde q u (Dyck.Tilde.freeE L k) = pieceProj L k := FreeAlgebra.lift_ι_apply _ _

omit [Invertible q] [Invertible (q - 1)] in
@[simp] theorem liftTilde_freeUp (k : ℕ) :
    liftTilde q u (Dyck.Tilde.freeUp L k) = raiseVstar (cmDPlusPiece q) k :=
  FreeAlgebra.lift_ι_apply _ _

omit [Invertible q] [Invertible (q - 1)] in
@[simp] theorem liftTilde_freeUpStar (k : ℕ) :
    liftTilde q u (Dyck.Tilde.freeUpStar L k) = raiseVstar (dplusStarPiece q u) k :=
  FreeAlgebra.lift_ι_apply _ _

omit [Invertible q] [Invertible (q - 1)] in
@[simp] theorem liftTilde_freeDown (k : ℕ) :
    liftTilde q u (Dyck.Tilde.freeDown L k) = lowerVstar (dminusPiece q) k :=
  FreeAlgebra.lift_ι_apply _ _

omit [Invertible q] [Invertible (q - 1)] in
@[simp] theorem liftTilde_freeT (k i : ℕ) :
    liftTilde q u (Dyck.Tilde.freeT L k i) = loopVstar (braidModPiece q) k i :=
  FreeAlgebra.lift_ι_apply _ _

omit [Invertible (q - 1)] in
@[simp] theorem liftTilde_freeTinv (k i : ℕ) :
    liftTilde q u (Dyck.Tilde.freeTinv L q k i) = tinvVstar q k i :=
  Dyck.map_tinvOf (A := FreeAlgebra L Dyck.Tilde.Gen) (B := Module.End L (Vstar L))
    (liftTilde q u) q ⅟q (liftTilde_freeT q u k i) (liftTilde_freeE q u k)

@[simp] theorem liftTilde_freeY (k i : ℕ) :
    liftTilde q u (Dyck.Tilde.freeY L q k i) = yOpVstar q k i :=
  Dyck.map_cornerOf (A := FreeAlgebra L Dyck.Tilde.Gen) (B := Module.End L (Vstar L))
    (liftTilde q u) q ⅟q ⅟(q - 1) (liftTilde_freeE q u) (liftTilde_freeUp q u)
    (liftTilde_freeDown q u) (liftTilde_freeT q u) k i

@[simp] theorem liftTilde_freeZ (k i : ℕ) :
    liftTilde q u (Dyck.Tilde.freeZ L q k i) = zOpVstar q u k i :=
  Dyck.map_cornerOf (A := FreeAlgebra L Dyck.Tilde.Gen) (B := Module.End L (Vstar L))
    (liftTilde q u) (⅟q) q (-(q * ⅟(q - 1))) (liftTilde_freeE q u) (liftTilde_freeUpStar q u)
    (liftTilde_freeDown q u) (liftTilde_freeTinv q u) k i

/-- **Every relation of `HJO.Dyck.Tilde.Atilde` holds for the assignment**, given the three mixed
ones. The quiver's own structure is the two computations `𝟏_k𝟏_k = 𝟏_k` and `𝟏_k𝟏_l = 0` together
with the sandwiching of each arrow; the unstarred group is `HJO.Sweep.exists_isDpaAction_cm`'s nine
relations and the starred group is the action half of `HJO.Sweep.exists_isDpaAction_star`'s, both
through `HJO.Sweep.IsDpaOperators.eq_of_sourceRel`. -/
theorem liftTilde_rel (hq1 : q + 1 ≠ 0)
    (hz : ∀ k i : ℕ, 1 ≤ i → i ≤ k →
      zOpVstar q u (k + 1) (i + 1) * raiseVstar (cmDPlusPiece q) k
        = raiseVstar (cmDPlusPiece q) k * zOpVstar q u k i)
    (hy : ∀ k i : ℕ, 1 ≤ i → i ≤ k →
      yOpVstar q (k + 1) (i + 1) * raiseVstar (dplusStarPiece q u) k
        = raiseVstar (dplusStarPiece q u) k * yOpVstar q k i)
    (htop : ∀ k : ℕ, zOpVstar q u (k + 1) 1 * raiseVstar (cmDPlusPiece q) k
        = (-(u * q ^ (k + 1)) : L) • (yOpVstar q (k + 1) 1 * raiseVstar (dplusStarPiece q u) k))
    {x y : FreeAlgebra L Dyck.Tilde.Gen} (hxy : Dyck.Tilde.Rel L q u x y) :
    liftTilde q u x = liftTilde q u y := by
  have hq : q ≠ 0 := Invertible.ne_zero q
  cases hxy with
  | vertex_mul_self k =>
    simp only [map_mul, liftTilde_freeE]
    exact pieceProj_mul_pieceProj k
  | vertex_mul_vertex hkl =>
    simp only [map_mul, map_zero, liftTilde_freeE]
    exact pieceProj_mul_pieceProj_of_ne (Ne.symm hkl)
  | vertex_mul_down k =>
    simp only [map_mul, liftTilde_freeE, liftTilde_freeDown]
    exact pieceProj_mul_lowerVstar k
  | down_mul_vertex k =>
    simp only [map_mul, liftTilde_freeE, liftTilde_freeDown]
    exact lowerVstar_mul_pieceProj k
  | vertex_mul_braid k i =>
    simp only [map_mul, liftTilde_freeE, liftTilde_freeT]
    exact pieceProj_mul_loopVstar k i
  | braid_mul_vertex k i =>
    simp only [map_mul, liftTilde_freeE, liftTilde_freeT]
    exact loopVstar_mul_pieceProj k i
  | braid_eq_zero hki =>
    simp only [map_zero, liftTilde_freeT]
    exact (isDpaOperators_cm q).loopVstar_eq_zero hki
  | source h =>
    refine (isDpaOperators_cm q).eq_of_sourceRel (fun _ _ _ => rfl) ?_
    exact h.map (A := FreeAlgebra L Dyck.Tilde.Gen) (B := Module.End L (Vstar L))
      (liftTilde q u) (liftTilde_freeE q u) (liftTilde_freeUp q u)
      (liftTilde_freeDown q u) (liftTilde_freeT q u)
  | sourceStar h =>
    have hstar : IsDpaOperators (⅟q : L) (braidInvModPiece q) (dminusPiece q)
        (dplusStarPiece q u) := by
      rw [invOf_eq_inv]
      exact isDpaOperators_star q u hq hq1
    refine hstar.eq_of_sourceRel (fun _ _ hki => tinvVstar_eq_loopVstar q hki) ?_
    exact h.map (A := FreeAlgebra L Dyck.Tilde.Gen) (B := Module.End L (Vstar L))
      (liftTilde q u) (liftTilde_freeE q u) (liftTilde_freeUpStar q u)
      (liftTilde_freeDown q u) (liftTilde_freeTinv q u)
  | mixed_z h1 h2 =>
    simp only [map_mul, liftTilde_freeZ, liftTilde_freeUp]
    exact hz _ _ h1 h2
  | mixed_y h1 h2 =>
    simp only [map_mul, liftTilde_freeY, liftTilde_freeUpStar]
    exact hy _ _ h1 h2
  | mixed_top k =>
    simp only [map_mul, map_smul, liftTilde_freeZ, liftTilde_freeY, liftTilde_freeUp,
      liftTilde_freeUpStar]
    exact htop k

/-- **The three mixed relations give an action of `Ã` on `V_*`**: the descent of
`HJO.Sweep.liftTilde` to `HJO.Dyck.Tilde.Atilde`'s quotient, sending the idempotent at the vertex
`k` to the projection onto `V_k`, the loops to the Demazure--Lusztig operators, the lowering arrow
to `d_-` of `HJO.Sweep.dminusCM`, the raising arrow to `d_+` of `HJO.Sweep.cmDPlus` and the second
raising arrow to `d^*_+` of `HJO.Sweep.dplusStar`. -/
theorem exists_action_atilde_of_mixed (hq1 : q + 1 ≠ 0)
    (hz : ∀ k i : ℕ, 1 ≤ i → i ≤ k →
      zOpVstar q u (k + 1) (i + 1) * raiseVstar (cmDPlusPiece q) k
        = raiseVstar (cmDPlusPiece q) k * zOpVstar q u k i)
    (hy : ∀ k i : ℕ, 1 ≤ i → i ≤ k →
      yOpVstar q (k + 1) (i + 1) * raiseVstar (dplusStarPiece q u) k
        = raiseVstar (dplusStarPiece q u) k * yOpVstar q k i)
    (htop : ∀ k : ℕ, zOpVstar q u (k + 1) 1 * raiseVstar (cmDPlusPiece q) k
        = (-(u * q ^ (k + 1)) : L) • (yOpVstar q (k + 1) 1 * raiseVstar (dplusStarPiece q u) k)) :
    ∃ ρ : Dyck.Tilde.Atilde L q u →ₐ[L] Module.End L (Vstar L),
      (∀ k : ℕ, ρ (Dyck.Tilde.Atilde.e L q u k) = pieceProj L k)
      ∧ (∀ k i : ℕ, ρ (Dyck.Tilde.Atilde.Tg L q u k i) = loopVstar (braidModPiece q) k i)
      ∧ (∀ k : ℕ, ρ (Dyck.Tilde.Atilde.dMinus L q u k) = lowerVstar (dminusPiece q) k)
      ∧ (∀ k : ℕ, ρ (Dyck.Tilde.Atilde.dPlus L q u k) = raiseVstar (cmDPlusPiece q) k)
      ∧ (∀ k : ℕ, ρ (Dyck.Tilde.Atilde.dPlusStar L q u k)
          = raiseVstar (dplusStarPiece q u) k) := by
  refine ⟨RingQuot.liftAlgHom L ⟨liftTilde q u, fun _ _ hr =>
    liftTilde_rel q u hq1 hz hy htop hr⟩, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    intros
    first
      | rw [Dyck.Tilde.Atilde.e, Dyck.Tilde.Atilde.mk,
          RingQuot.liftAlgHom_mkAlgHom_apply, liftTilde_freeE]
      | rw [Dyck.Tilde.Atilde.Tg, Dyck.Tilde.Atilde.mk,
          RingQuot.liftAlgHom_mkAlgHom_apply, liftTilde_freeT]
      | rw [Dyck.Tilde.Atilde.dMinus, Dyck.Tilde.Atilde.mk,
          RingQuot.liftAlgHom_mkAlgHom_apply, liftTilde_freeDown]
      | rw [Dyck.Tilde.Atilde.dPlus, Dyck.Tilde.Atilde.mk,
          RingQuot.liftAlgHom_mkAlgHom_apply, liftTilde_freeUp]
      | rw [Dyck.Tilde.Atilde.dPlusStar, Dyck.Tilde.Atilde.mk,
          RingQuot.liftAlgHom_mkAlgHom_apply, liftTilde_freeUpStar]

end Build

end HJO.Sweep

end
