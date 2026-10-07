/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CMStructure.VmodIntertwined
public import HJO.CMStructure.KernelGenerators
public import HJO.CMStructure.Thm52Injective
public import HJO.CarlssonMellit.DpaStructurePrelim
public meta import HJO.Attr

/-! # The structure of the double module

Mellit's structure theorem for the double module (Theorem 3.6 of the paper). The modified pair
`(ρ^♭, ρ^{♭*})` of `HJO.Sweep.exists_isIntertwinedPair_vmod` defines an action of the extended Dyck
path algebra `Ã` of `HJO.Dyck.Tilde.Atilde` on `V_* = ⨁_k V_k`; let `φ : Ã𝟏_0 → V_*` send `x` to
`ρ(x)(1)`. Then the kernel of `φ` is the left submodule

`𝓘 = ⟨(d₋d₊^* - 𝟏_k)d₊^{*k}𝟏_0, (d₊ + q^ky_1d₊^*)d₊^{*k}𝟏_0 : k ≥ 0⟩`

of `HJO.Dyck.Tilde.Atilde.mellitKernel`, and `Ã𝟏_0/𝓘 → V_*` is an isomorphism.

The proof follows the paper. `𝓘 ⊆ ker φ` is `HJO.Sweep.dminus_dplusStar_map_one`, `d₊^{*k}(1) = 1`
and `y_1` acting by multiplication. The displayed elements

`d₋^m y_1^{a_1} ⋯ y_k^{a_k} y_{k+1}^{l_1+1} ⋯ y_{k+m}^{l_m+1} d₊^{*k+m}𝟏_0`,
`l_1 ≥ ⋯ ≥ l_m ≥ 0`,

evaluate to the basis of `HJO.Sweep.exists_basis_vstar_prod_bop` at the same index, since
`d^♭_-(y_j^{r+1}g) = B_{r+1}g`; this gives the surjectivity of `φ` and its injectivity on their
span. It remains that they span `Ã𝟏_0` modulo `𝓘`. Write `v_n = d₊^{*n}𝟏_0`. The span `S` of the
words `d₋^m y^b v_{k+m}` with arbitrary exponents, together with `𝓘`, is closed under left
multiplication by every generator of `Ã`:

* under `e`, `T_i`, `y_i`, `d₋` by the relations of `𝔸_q` read through `𝔸_q → Ã`, the loops
  being absorbed by the vacuum, `T_iv_n = v_n` (the starred `T_1d₊² = d₊²`, `d₊T_i = T_{i+1}d₊`);
* under `d₊`, which passes the letters `e, T, y, d₋` into `levelAlg + levelAlg·d₊` and meets the
  vacuum as `d₊v_n ≡ -q^ny_1v_{n+1}` by the second family of `𝓘`;
* under `d₊^*`, which passes the same letters into the span of `b·d₊^*` and `b·z_i` with `b`
  unstarred; on the vacuum the first raises the tower and the second lies in `𝓘`, because
  `z_n = (q^{-1}-1)^{-1}T̂(d₊^*d₋ - d₋d₊^*)` and both terms return `v_n` by the first family, the
  lower `z_i` following by `z_i = qT̂_iz_{i+1}T̂_i`.

Within `S`, an ascent in the tail is exchanged by the Hecke straightening of `𝔸_q` for monomials
of smaller weight `∑ s·b_s`, the loop being absorbed on the left by `d₋^m` and on the right by the
vacuum; and a zero last tail exponent is removed by the first family of `𝓘`, decreasing `m`.

## Main definitions

* `HJO.Sweep.structureWord`: the displayed element at an index of
  `HJO.Sweep.exists_basis_vstar_prod_bop`.
* `HJO.Sweep.StructureSpanning`: the spanning statement.
* `HJO.Dyck.Tilde.Atilde.starNormalWord`: `d₋^m y^b d₊^{*k+m}𝟏_0`, for an arbitrary exponent
  function.

## Main results

* `HJO.Sweep.exists_action_atilde_mod`: the modified pair defines an action of `Ã`.
* `HJO.Sweep.mellitKernel_le_ker_evalOne`: `𝓘 ⊆ ker φ`.
* `HJO.Sweep.map_evalOne_atildeE0_eq_top`: `φ` is surjective.
* `HJO.Sweep.evalOne_structureWord`: the displayed elements evaluate to the basis.
* `HJO.Dyck.Tilde.Atilde.zElt_mul_dPlusStarPow_zero_mem`: `z_iv_n ∈ 𝓘`.
* `HJO.Dyck.Tilde.Atilde.atildeE0_le_posStarNormalSpan_sup`: the spanning.
* `HJO.Sweep.dpaStructure_of_spanning`, `HJO.Sweep.dpaStructure`: the theorem.

## Implementation notes

The step for `d₊^*` moves the starred corner elements `z_i` past `T`, `y` and `d₋`. Those moves
are the starred images of facts about `𝔸_q`, obtained through a star swap of `Ã`, which exists
when the base carries a ring involution inverting `q` and `u` (`HJO.Sym.paramInvLambda`), as
`ℚ(q,u)` does. `HJO.Sweep.dpaStructure` carries that hypothesis;
`HJO.Sweep.dpaStructure_of_spanning` does not, and everything except the spanning statement is
proved without it.

`q ≠ 0`, `q ≠ 1` are `Invertible q` and `Invertible (q - 1)`, which `Ã` itself needs, and
`q + 1 ≠ 0` is inherited from `HJO.Sweep.exists_isDpaAction_mellit`.

The kernel is stated for `φ` restricted to `Ã𝟏_0 = Ã·𝟏_0`, the submodule
`HJO.Dyck.Tilde.Atilde.atildeE0`, and `𝓘` is read inside it; `𝓘 ⊆ Ã𝟏_0` is
`HJO.Dyck.Tilde.Atilde.mellitKernel_le_atildeE0`. The isomorphism is the induced map, pinned by
its values on classes.

## References

A. Mellit, *Toric braids and `(m, n)`-parking functions*, arXiv:1604.07456, Theorem 3.6, whose
proof refers to E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, J. Amer. Math. Soc.
**31** (2018) 661--697, Theorem 7.3 and Lemma 5.6.
-/

@[expose] public section

namespace HJO.Sweep

/-! ### The action of `Ã` defined by the modified pair -/

section ModAction

variable {L : Type*} [Field L] [Algebra ℚ L] (q u : L) [Invertible q] [Invertible (q - 1)]

/-- The assignment of the generators of the enlarged quiver of `HJO.Dyck.Tilde.Atilde` to the
operators of the modified pair `(ρ^♭, ρ^{♭*})`: the idempotents to the projections, `d₊` to `d^♭_+`,
`d₊^*` to `d^*_+`, `d₋` to `d^♭_-` and the loops to the Demazure--Lusztig operators. -/
noncomputable def genOpTildeMod : Dyck.Tilde.Gen → Module.End L (Vstar L)
  | .vertex k => pieceProj L k
  | .up k => raiseVstar (dplusModPiece q) k
  | .upStar k => raiseVstar (dplusStarPiece q u) k
  | .down k => lowerVstar (dminusModPiece q) k
  | .braid k i => loopVstar (braidModPiece q) k i

/-- The lift of `HJO.Sweep.genOpTildeMod` to the free algebra on the enlarged quiver. -/
noncomputable def liftTildeMod : FreeAlgebra L Dyck.Tilde.Gen →ₐ[L] Module.End L (Vstar L) :=
  FreeAlgebra.lift L (genOpTildeMod q u)

omit [Invertible q] [Invertible (q - 1)] in
/-- `HJO.Sweep.liftTildeMod` sends the idempotent `𝟏_k` to the projection onto `V_k`. -/
@[simp] theorem liftTildeMod_freeE (k : ℕ) :
    liftTildeMod q u (Dyck.Tilde.freeE L k) = pieceProj L k := FreeAlgebra.lift_ι_apply _ _

omit [Invertible q] [Invertible (q - 1)] in
/-- `HJO.Sweep.liftTildeMod` sends `d₊` at level `k` to `d^♭_+`. -/
@[simp] theorem liftTildeMod_freeUp (k : ℕ) :
    liftTildeMod q u (Dyck.Tilde.freeUp L k) = raiseVstar (dplusModPiece q) k :=
  FreeAlgebra.lift_ι_apply _ _

omit [Invertible q] [Invertible (q - 1)] in
/-- `HJO.Sweep.liftTildeMod` sends `d₊^*` at level `k` to `d^*_+`. -/
@[simp] theorem liftTildeMod_freeUpStar (k : ℕ) :
    liftTildeMod q u (Dyck.Tilde.freeUpStar L k) = raiseVstar (dplusStarPiece q u) k :=
  FreeAlgebra.lift_ι_apply _ _

omit [Invertible q] [Invertible (q - 1)] in
/-- `HJO.Sweep.liftTildeMod` sends `d₋` at level `k` to `d^♭_-`. -/
@[simp] theorem liftTildeMod_freeDown (k : ℕ) :
    liftTildeMod q u (Dyck.Tilde.freeDown L k) = lowerVstar (dminusModPiece q) k :=
  FreeAlgebra.lift_ι_apply _ _

omit [Invertible q] [Invertible (q - 1)] in
/-- `HJO.Sweep.liftTildeMod` sends the loop `T_i` at level `k` to the Demazure--Lusztig operator
of the modified pair. -/
@[simp] theorem liftTildeMod_freeT (k i : ℕ) :
    liftTildeMod q u (Dyck.Tilde.freeT L k i) = loopVstar (braidModPiece q) k i :=
  FreeAlgebra.lift_ι_apply _ _

omit [Invertible (q - 1)] in
/-- `HJO.Sweep.liftTildeMod` sends the inverse loop `T_i^{-1}` at level `k` to the inverse of the
Demazure--Lusztig operator. -/
@[simp] theorem liftTildeMod_freeTinv (k i : ℕ) :
    liftTildeMod q u (Dyck.Tilde.freeTinv L q k i) = tinvVstar q k i :=
  Dyck.map_tinvOf (A := FreeAlgebra L Dyck.Tilde.Gen) (B := Module.End L (Vstar L))
    (liftTildeMod q u) q ⅟q (liftTildeMod_freeT q u k i) (liftTildeMod_freeE q u k)

/-- `HJO.Sweep.liftTildeMod` sends the corner element `y_i` at level `k` to the corner element
built from the images of `𝟏`, `d₊`, `d₋` and the loops. -/
theorem liftTildeMod_freeY (k i : ℕ) :
    liftTildeMod q u (Dyck.Tilde.freeY L q k i)
      = Dyck.cornerOf q ⅟q ⅟(q - 1) (pieceProj L) (raiseVstar (dplusModPiece q))
          (lowerVstar (dminusModPiece q)) (loopVstar (braidModPiece q)) k i :=
  Dyck.map_cornerOf (A := FreeAlgebra L Dyck.Tilde.Gen) (B := Module.End L (Vstar L))
    (liftTildeMod q u) q ⅟q ⅟(q - 1) (liftTildeMod_freeE q u) (liftTildeMod_freeUp q u)
    (liftTildeMod_freeDown q u) (liftTildeMod_freeT q u) k i

/-- `HJO.Sweep.liftTildeMod` sends the starred corner element `z_i` at level `k` to the corner
element built, with `q` replaced by `q^{-1}`, from the images of `𝟏`, `d₊^*`, `d₋` and the inverse
loops. -/
theorem liftTildeMod_freeZ (k i : ℕ) :
    liftTildeMod q u (Dyck.Tilde.freeZ L q k i)
      = Dyck.cornerOf (⅟q) q (-(q * ⅟(q - 1))) (pieceProj L) (raiseVstar (dplusStarPiece q u))
          (lowerVstar (dminusModPiece q)) (tinvVstar q) k i :=
  Dyck.map_cornerOf (A := FreeAlgebra L Dyck.Tilde.Gen) (B := Module.End L (Vstar L))
    (liftTildeMod q u) (⅟q) q (-(q * ⅟(q - 1))) (liftTildeMod_freeE q u)
    (liftTildeMod_freeUpStar q u) (liftTildeMod_freeDown q u) (liftTildeMod_freeTinv q u) k i

/-- **Every relation of `HJO.Dyck.Tilde.Atilde` holds for the modified assignment.** The unstarred
group is `HJO.Sweep.isDpaOperators_mod`, the starred group `HJO.Sweep.isDpaOperators_mellit`, and
the three mixed relations are three of the five conditions of
`HJO.Sweep.exists_isIntertwinedPair_vmod`, read off the pair
`HJO.Sweep.exists_isIntertwinedPair_vmod` through the identification of its corner elements with the
corner elements of the lift. -/
theorem liftTildeMod_rel (hq1 : q + 1 ≠ 0) {x y : FreeAlgebra L Dyck.Tilde.Gen}
    (hxy : Dyck.Tilde.Rel L q u x y) : liftTildeMod q u x = liftTildeMod q u y := by
  have hq : q ≠ 0 := Invertible.ne_zero q
  obtain ⟨ρ, ρ', hpair, hT, hD, hU, hT', hD', hU'⟩ := exists_isIntertwinedPair_vmod q u hq1
  have hy : ∀ k i : ℕ, ρ (Dyck.Aq.yElt L q k i)
      = Dyck.cornerOf q ⅟q ⅟(q - 1) (pieceProj L) (raiseVstar (dplusModPiece q))
          (lowerVstar (dminusModPiece q)) (loopVstar (braidModPiece q)) k i := by
    intro k i
    rw [← Dyck.Aq.cornerOf_eq_yElt]
    exact Dyck.map_cornerOf (A := Dyck.Aq L q) (B := Module.End L (Vstar L)) ρ
      (E := Dyck.Aq.e L q) (U := Dyck.Aq.dPlus L q) (D := Dyck.Aq.dMinus L q)
      (T := Dyck.Aq.Tg L q) q ⅟q ⅟(q - 1) hpair.isAction.map_e hU hD hT k i
  have hz : ∀ k i : ℕ, 1 ≤ i → ρ' (Dyck.Aq.yElt L (⅟q) k i)
      = Dyck.cornerOf (⅟q) q (-(q * ⅟(q - 1))) (pieceProj L) (raiseVstar (dplusStarPiece q u))
          (lowerVstar (dminusModPiece q)) (tinvVstar q) k i := by
    intro k i hi
    rw [← Dyck.Aq.cornerOf_eq_yElt]
    rw [Dyck.map_cornerOf (A := Dyck.Aq L (⅟q)) (B := Module.End L (Vstar L)) ρ'
      (E := Dyck.Aq.e L (⅟q)) (U := Dyck.Aq.dPlus L (⅟q)) (D := Dyck.Aq.dMinus L (⅟q))
      (T := Dyck.Aq.Tg L (⅟q)) (⅟q) ⅟(⅟q) ⅟(⅟q - 1) hpair.isActionStar.map_e hU' hD' hT' k i]
    exact Dyck.cornerOf_congr (⅟q) q (-(q * ⅟(q - 1))) _ _ _
      (fun n j hj => (tinvVstar_eq_loopVstar q hj).symm) hi
  cases hxy with
  | vertex_mul_self k =>
    simp only [map_mul, liftTildeMod_freeE]
    exact pieceProj_mul_pieceProj k
  | vertex_mul_vertex hkl =>
    simp only [map_mul, map_zero, liftTildeMod_freeE]
    exact pieceProj_mul_pieceProj_of_ne (Ne.symm hkl)
  | vertex_mul_down k =>
    simp only [map_mul, liftTildeMod_freeE, liftTildeMod_freeDown]
    exact pieceProj_mul_lowerVstar k
  | down_mul_vertex k =>
    simp only [map_mul, liftTildeMod_freeE, liftTildeMod_freeDown]
    exact lowerVstar_mul_pieceProj k
  | vertex_mul_braid k i =>
    simp only [map_mul, liftTildeMod_freeE, liftTildeMod_freeT]
    exact pieceProj_mul_loopVstar k i
  | braid_mul_vertex k i =>
    simp only [map_mul, liftTildeMod_freeE, liftTildeMod_freeT]
    exact loopVstar_mul_pieceProj k i
  | braid_eq_zero hki =>
    simp only [map_zero, liftTildeMod_freeT]
    exact (isDpaOperators_mod q hq).loopVstar_eq_zero hki
  | source h =>
    refine (isDpaOperators_mod q hq).eq_of_sourceRel (fun _ _ _ => rfl) ?_
    exact h.map (A := FreeAlgebra L Dyck.Tilde.Gen) (B := Module.End L (Vstar L))
      (liftTildeMod q u) (liftTildeMod_freeE q u) (liftTildeMod_freeUp q u)
      (liftTildeMod_freeDown q u) (liftTildeMod_freeT q u)
  | sourceStar h =>
    have hstar : IsDpaOperators (⅟q : L) (braidInvModPiece q) (dminusModPiece q)
        (dplusStarPiece q u) := by
      rw [invOf_eq_inv]
      exact isDpaOperators_mellit q u hq hq1
    refine hstar.eq_of_sourceRel (fun _ _ hki => tinvVstar_eq_loopVstar q hki) ?_
    exact h.map (A := FreeAlgebra L Dyck.Tilde.Gen) (B := Module.End L (Vstar L))
      (liftTildeMod q u) (liftTildeMod_freeE q u) (liftTildeMod_freeUpStar q u)
      (liftTildeMod_freeDown q u) (liftTildeMod_freeTinv q u)
  | mixed_z h1 h2 =>
    simp only [map_mul, liftTildeMod_freeZ, liftTildeMod_freeUp]
    have h := hpair.dPlus_mul_zElt _ _ h1 h2
    rw [hU, hz _ _ h1, hz _ _ (by omega)] at h
    exact h.symm
  | mixed_y h1 h2 =>
    simp only [map_mul, liftTildeMod_freeY, liftTildeMod_freeUpStar]
    have h := hpair.dPlusStar_mul_yElt _ _ h1 h2
    rw [hU', hy, hy] at h
    exact h.symm
  | mixed_top k =>
    simp only [map_mul, map_smul, liftTildeMod_freeZ, liftTildeMod_freeY, liftTildeMod_freeUp,
      liftTildeMod_freeUpStar]
    have h := hpair.zElt_one_mul_dPlus k
    rw [hU, hU', hy, hz _ _ le_rfl] at h
    exact h

/-- **The modified pair defines an action of `Ã` on `V_*`**: the descent of
`HJO.Sweep.liftTildeMod` to the quotient `HJO.Dyck.Tilde.Atilde`. This is the well-definedness of
the map `φ` of `HJO.Standing.dpaStructure_param`: by `HJO.Sweep.exists_isIntertwinedPair_vmod` the
operators `T_i`, `d^♭_-`, `d^♭_+`, `d^*_+` satisfy every relation of `Ã`. -/
theorem exists_action_atilde_mod (hq1 : q + 1 ≠ 0) :
    ∃ ρ : Dyck.Tilde.Atilde L q u →ₐ[L] Module.End L (Vstar L),
      (∀ k : ℕ, ρ (Dyck.Tilde.Atilde.e L q u k) = pieceProj L k)
      ∧ (∀ k i : ℕ, ρ (Dyck.Tilde.Atilde.Tg L q u k i) = loopVstar (braidModPiece q) k i)
      ∧ (∀ k : ℕ, ρ (Dyck.Tilde.Atilde.dMinus L q u k) = lowerVstar (dminusModPiece q) k)
      ∧ (∀ k : ℕ, ρ (Dyck.Tilde.Atilde.dPlus L q u k) = raiseVstar (dplusModPiece q) k)
      ∧ (∀ k : ℕ, ρ (Dyck.Tilde.Atilde.dPlusStar L q u k)
          = raiseVstar (dplusStarPiece q u) k) := by
  refine ⟨RingQuot.liftAlgHom L ⟨liftTildeMod q u, fun _ _ hr =>
    liftTildeMod_rel q u hq1 hr⟩, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    intros
    first
      | rw [Dyck.Tilde.Atilde.e, Dyck.Tilde.Atilde.mk,
          RingQuot.liftAlgHom_mkAlgHom_apply, liftTildeMod_freeE]
      | rw [Dyck.Tilde.Atilde.Tg, Dyck.Tilde.Atilde.mk,
          RingQuot.liftAlgHom_mkAlgHom_apply, liftTildeMod_freeT]
      | rw [Dyck.Tilde.Atilde.dMinus, Dyck.Tilde.Atilde.mk,
          RingQuot.liftAlgHom_mkAlgHom_apply, liftTildeMod_freeDown]
      | rw [Dyck.Tilde.Atilde.dPlus, Dyck.Tilde.Atilde.mk,
          RingQuot.liftAlgHom_mkAlgHom_apply, liftTildeMod_freeUp]
      | rw [Dyck.Tilde.Atilde.dPlusStar, Dyck.Tilde.Atilde.mk,
          RingQuot.liftAlgHom_mkAlgHom_apply, liftTildeMod_freeUpStar]

end ModAction

end HJO.Sweep

namespace HJO.Sweep

open Dyck.Tilde

/-! ### The evaluation map of the modified action -/

section Eval

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L} [Invertible q] [Invertible (q - 1)]
  {ρ : Atilde L q u →ₐ[L] Module.End L (Vstar L)}
  (hρe : ∀ k : ℕ, ρ (Atilde.e L q u k) = pieceProj L k)
  (hρT : ∀ k i : ℕ, ρ (Atilde.Tg L q u k i) = loopVstar (braidModPiece q) k i)
  (hρD : ∀ k : ℕ, ρ (Atilde.dMinus L q u k) = lowerVstar (dminusModPiece q) k)
  (hρU : ∀ k : ℕ, ρ (Atilde.dPlus L q u k) = raiseVstar (dplusModPiece q) k)
  (hρS : ∀ k : ℕ, ρ (Atilde.dPlusStar L q u k) = raiseVstar (dplusStarPiece q u) k)

omit [Algebra ℚ L] in
include hρe in
/-- The restriction of the action along `𝔸_q → Ã` is an action of `𝔸_q`. -/
theorem isDpaAction_comp_toTilde : IsDpaAction q (ρ.comp (Dyck.toTilde L q u)) :=
  ⟨fun k => by rw [AlgHom.comp_apply, Dyck.toTilde_e, hρe]⟩

include hρe hρT hρD hρU in
/-- **The corner elements `y_i` of `Ã` act by multiplication by the variables**,
`HJO.Sweep.map_yElt_eq_auxMulPiece` read through `𝔸_q → Ã`. -/
theorem map_yElt_atilde_eq_auxMulPiece {k i : ℕ} (h1 : 1 ≤ i) (hik : i ≤ k) :
    ρ (Atilde.yElt L q u k i) = loopVstar (auxMulPiece L) k i := by
  rw [← Dyck.toTilde_yElt, ← AlgHom.comp_apply]
  exact map_yElt_eq_auxMulPiece (isDpaAction_comp_toTilde hρe)
    (fun k i => by rw [AlgHom.comp_apply, Dyck.toTilde_Tg, hρT])
    (fun k => by rw [AlgHom.comp_apply, Dyck.toTilde_dMinus, hρD])
    (fun k => by rw [AlgHom.comp_apply, Dyck.toTilde_dPlus, hρU]) h1 hik

omit [Algebra ℚ L] in
include hρe hρS in
/-- **`d_+^{*m}𝟏_0` evaluates to `1 ∈ V_m`**, by `HJO.Sweep.dplusStar_map_one` and induction. -/
theorem evalOne_dPlusStarPow_zero (m : ℕ) :
    evalOne ρ (Atilde.dPlusStarPow L q u 0 m) = oneAt L m := by
  induction m with
  | zero => exact evalOne_e_zero ρ hρe
  | succ m ih =>
    rw [Atilde.dPlusStarPow_succ, evalOne_mul, ih, zero_add, hρS, oneAt_eq,
      raiseVstar_ofPiece, oneAt_eq]
    refine congrArg (ofPiece L (m + 1)) (Subtype.ext ?_)
    rw [coe_dplusStarPiece]
    exact dplusStar_map_one q u m

include hρe hρD hρS in
/-- The first family of generators of `𝓘` is annihilated: `d^♭_-d^*_+(1) = 1`. -/
theorem evalOne_mellitKernel_gen_one (k : ℕ) :
    evalOne ρ ((Atilde.dMinus L q u k * Atilde.dPlusStar L q u k - Atilde.e L q u k) *
      Atilde.dPlusStarPow L q u 0 k) = 0 := by
  rw [evalOne_mul, evalOne_dPlusStarPow_zero hρe hρS, map_sub, map_mul, hρD, hρS, hρe,
    LinearMap.sub_apply, Module.End.mul_apply, oneAt_eq, raiseVstar_ofPiece,
    lowerVstar_ofPiece, pieceProj_ofPiece, sub_eq_zero]
  refine congrArg (ofPiece L k) (Subtype.ext ?_)
  rw [coe_dminusModPiece, coe_dplusStarPiece]
  exact dminus_dplusStar_map_one q u k

include hρe hρT hρD hρU hρS in
/-- The second family of generators of `𝓘` is annihilated: `d^♭_+(1) + q^ky_1d^*_+(1) = 0`. -/
theorem evalOne_mellitKernel_gen_two (k : ℕ) :
    evalOne ρ ((Atilde.dPlus L q u k + (q ^ k) • (Atilde.yElt L q u (k + 1) 1 *
      Atilde.dPlusStar L q u k)) * Atilde.dPlusStarPow L q u 0 k) = 0 := by
  have hq : q ≠ 0 := Invertible.ne_zero q
  rw [evalOne_mul, evalOne_dPlusStarPow_zero hρe hρS, map_add, map_smul, map_mul, hρU, hρS,
    map_yElt_atilde_eq_auxMulPiece hρe hρT hρD hρU le_rfl (by omega), LinearMap.add_apply,
    LinearMap.smul_apply, Module.End.mul_apply, oneAt_eq, raiseVstar_ofPiece,
    raiseVstar_ofPiece, loopVstar_ofPiece, ← map_smul, ← map_add]
  convert map_zero (ofPiece L (k + 1))
  refine Subtype.ext ?_
  rw [AddMemClass.coe_add, SetLike.val_smul, coe_auxMulPiece le_rfl (by omega),
    coe_dplusModPiece, coe_dplusStarPiece, smul_eq_scal_mul, ← mul_assoc,
    ZeroMemClass.coe_zero]
  exact dplus_map_one_add_auxVar_mul_dplusStar_map_one q u hq k

include hρe hρT hρD hρU hρS in
/-- **`𝓘` annihilates `1`.** -/
theorem mellitKernel_le_annOne : Atilde.mellitKernel L q u ≤ annOne ρ := by
  refine Ideal.span_le.2 ?_
  rintro _ (⟨k, rfl⟩ | ⟨k, rfl⟩)
  · exact evalOne_mellitKernel_gen_one hρe hρD hρS k
  · exact evalOne_mellitKernel_gen_two hρe hρT hρD hρU hρS k

include hρe hρT hρD hρU hρS in
/-- **`𝓘 ⊆ ker φ`**, the first half of `HJO.Standing.dpaStructure_param`. -/
theorem mellitKernel_le_ker_evalOne :
    (Atilde.mellitKernel L q u).restrictScalars L ≤ LinearMap.ker (evalOne ρ) :=
  fun _ hx => mellitKernel_le_annOne hρe hρT hρD hρU hρS hx

/-! ### Surjectivity -/

omit [Algebra ℚ L] in
/-- The image of `Ã𝟏_0` is stable under the action. -/
theorem action_mem_map_evalOne (a : Atilde L q u) {v : Vstar L}
    (hv : v ∈ Submodule.map (evalOne ρ) (Atilde.atildeE0 L q u)) :
    ρ a v ∈ Submodule.map (evalOne ρ) (Atilde.atildeE0 L q u) := by
  obtain ⟨x, hx, rfl⟩ := hv
  refine ⟨a * x, ?_, evalOne_mul ρ a x⟩
  rw [SetLike.mem_coe, Atilde.mem_atildeE0_iff] at hx ⊢
  rw [mul_assoc, hx]

include hρe hρT hρD hρU in
/-- If `G ∈ V_k` lies in the image of `Ã𝟏_0`, then so does `x_i^n G` for `1 ≤ i ≤ k`. -/
theorem auxVar_pow_mul_mem_map_evalOne {k i : ℕ} (h1 : 1 ≤ i) (hik : i ≤ k) (n : ℕ)
    (G : pieceSub L k)
    (hG : ofPiece L k G ∈ Submodule.map (evalOne ρ) (Atilde.atildeE0 L q u)) :
    ∀ F : pieceSub L k, (F : Total L) = (auxVar i : Total L) ^ n * G →
      ofPiece L k F ∈ Submodule.map (evalOne ρ) (Atilde.atildeE0 L q u) := by
  induction n with
  | zero =>
    intro F hF
    rw [pow_zero, one_mul] at hF
    rwa [Subtype.ext hF]
  | succ n ih =>
    intro F hF
    have hmem : (auxVar i : Total L) ^ n * (G : Total L) ∈ pieceSub L k :=
      mem_pieceSub_of_mem_piece
        (auxVar_pow_mul_mem_piece h1 hik n (mem_piece_of_mem_pieceSub G.2))
    have h := action_mem_map_evalOne (Atilde.yElt L q u k i) (ih ⟨_, hmem⟩ rfl)
    rw [map_yElt_atilde_eq_auxMulPiece hρe hρT hρD hρU h1 hik, loopVstar_ofPiece] at h
    convert h using 2
    refine Subtype.ext ?_
    rw [coe_auxMulPiece h1 hik, hF, pow_succ',
      mul_assoc (auxVar i : Total L) ((auxVar i : Total L) ^ n) (G : Total L)]

include hρe hρT hρD hρU in
/-- If `G ∈ V_k` lies in the image of `Ã𝟏_0`, then so does `x_1^{a_1} ⋯ x_k^{a_k} G`. -/
theorem prod_auxVar_mul_mem_map_evalOne {k : ℕ} (a : Fin k →₀ ℕ) :
    ∀ F G : pieceSub L k,
      ofPiece L k G ∈ Submodule.map (evalOne ρ) (Atilde.atildeE0 L q u) →
      (F : Total L) = (a.prod fun j n => (auxVar ((j : ℕ) + 1) : Total L) ^ n) * G →
      ofPiece L k F ∈ Submodule.map (evalOne ρ) (Atilde.atildeE0 L q u) := by
  refine Finsupp.induction a ?_ ?_
  · intro F G hG hF
    rw [Finsupp.prod_zero_index, one_mul] at hF
    rwa [Subtype.ext hF]
  · intro i n b _ _ ih F G hG hF
    have hprod : ((Finsupp.single i n + b).prod
          fun j m => (auxVar ((j : ℕ) + 1) : Total L) ^ m)
        = (auxVar ((i : ℕ) + 1) : Total L) ^ n *
          (b.prod fun j m => (auxVar ((j : ℕ) + 1) : Total L) ^ m) := by
      rw [Finsupp.prod_add_index'
          (h := fun (j : Fin k) (m : ℕ) => (auxVar ((j : ℕ) + 1) : Total L) ^ m)
          (fun j => pow_zero _) (fun j m₁ m₂ => pow_add _ m₁ m₂),
        Finsupp.prod_single_index
          (h := fun (j : Fin k) (m : ℕ) => (auxVar ((j : ℕ) + 1) : Total L) ^ m) (pow_zero _)]
    have hmem : (b.prod fun j m => (auxVar ((j : ℕ) + 1) : Total L) ^ m) * (G : Total L)
        ∈ pieceSub L k :=
      mem_pieceSub_of_mem_piece
        (mul_mem (prod_auxVar_mem_piece b) (mem_piece_of_mem_pieceSub G.2))
    refine auxVar_pow_mul_mem_map_evalOne hρe hρT hρD hρU (Nat.le_add_left 1 _) i.2 n
      ⟨_, hmem⟩ (ih _ G hG rfl) F ?_
    rw [hF, hprod, mul_assoc]

include hρe hρT hρD hρU hρS in
/-- **Every vector of the basis of `HJO.Sweep.exists_basis_vstar_prod_bop` is in the image of
`Ã𝟏_0`.** The vector `y^a B_{l_1+1}(⋯B_{l_m+1}(1)⋯)` is the value of
`d_-^m y_1^{a_1} ⋯ y_k^{a_k} y_{k+1}^{l_1+1} ⋯ y_{k+m}^{l_m+1} d_+^{*k+m}𝟏_0`: `d_+^{*k+m}𝟏_0`
evaluates to `1`, and `d^♭_-(y_j^{r+1}g) = B_{r+1}g` (`HJO.Sweep.dminus_auxVar_pow_mul`). -/
theorem ofPiece_mem_map_evalOne :
    ∀ (l : List ℕ) (k : ℕ) (a : Fin k →₀ ℕ) (F : pieceSub L k),
      (F : Total L) = (a.prod fun j n => (auxVar ((j : ℕ) + 1) : Total L) ^ n) *
        algebraMap (Sym.Lambda L) (Total L)
          (((l.map (· + 1)).map fun r : ℕ => Sym.Bop q (r : ℤ)).prod 1) →
      ofPiece L k F ∈ Submodule.map (evalOne ρ) (Atilde.atildeE0 L q u) := by
  intro l
  induction l with
  | nil =>
    intro k a F hF
    refine prod_auxVar_mul_mem_map_evalOne hρe hρT hρD hρU a F (oneAtPiece L k)
      ⟨Atilde.dPlusStarPow L q u 0 k, ?_, evalOne_dPlusStarPow_zero hρe hρS k⟩ ?_
    · rw [SetLike.mem_coe, Atilde.mem_atildeE0_iff, Atilde.dPlusStarPow_mul_e]
    · rw [hF, coe_oneAtPiece, mul_one]
      simp
  | cons r l ih =>
    intro k a F hF
    obtain ⟨g, hg⟩ : ∃ g : Sym.Lambda L,
        ((l.map (· + 1)).map fun s : ℕ => Sym.Bop q (s : ℤ)).prod 1 = g := ⟨_, rfl⟩
    rw [hg] at ih
    have hhead : ((((r :: l).map (· + 1)).map fun s : ℕ => Sym.Bop q (s : ℤ)).prod 1
        : Sym.Lambda L) = Sym.Bop q (((r + 1 : ℕ)) : ℤ) g := by
      rw [List.map_cons, List.map_cons, List.prod_cons, Module.End.mul_apply, hg]
    have hmem : (auxVar (k + 1) : Total L) ^ (r + 1) * algebraMap (Sym.Lambda L) (Total L) g
        ∈ pieceSub L (k + 1) :=
      mem_pieceSub_of_mem_piece (auxVar_pow_mul_mem_piece (Nat.le_add_left 1 k) le_rfl (r + 1)
        (algebraMap_mem_piece g (k + 1)))
    have hmem2 : algebraMap (Sym.Lambda L) (Total L) (Sym.Bop q (((r + 1 : ℕ)) : ℤ) g)
        ∈ pieceSub L k :=
      mem_pieceSub_of_mem_piece (algebraMap_mem_piece _ k)
    have hstep : ofPiece L (k + 1) ⟨_, hmem⟩
        ∈ Submodule.map (evalOne ρ) (Atilde.atildeE0 L q u) := by
      refine ih (k + 1) (Finsupp.single (Fin.last k) (r + 1)) ⟨_, hmem⟩ ?_
      rw [Finsupp.prod_single_index
        (h := fun (j : Fin (k + 1)) (m : ℕ) => (auxVar ((j : ℕ) + 1) : Total L) ^ m)
        (pow_zero _), Fin.val_last]
    have hlower := action_mem_map_evalOne (Atilde.dMinus L q u k) hstep
    rw [hρD, lowerVstar_ofPiece] at hlower
    have hBop : dminusModPiece q k ⟨_, hmem⟩ = (⟨_, hmem2⟩ : pieceSub L k) := by
      refine Subtype.ext ?_
      change dminus q (k + 1) ((auxVar (k + 1) : Total L) ^ (r + 1)
          * algebraMap (Sym.Lambda L) (Total L) g)
        = algebraMap (Sym.Lambda L) (Total L) (Sym.Bop q (((r + 1 : ℕ)) : ℤ) g)
      rw [MvPolynomial.algebraMap_eq, dminus_auxVar_pow_mul_C]
    rw [hBop] at hlower
    refine prod_auxVar_mul_mem_map_evalOne hρe hρT hρD hρU a F ⟨_, hmem2⟩ hlower ?_
    rw [hF, hhead]

include hρe hρT hρD hρU hρS in
/-- **`φ` is surjective**: its image contains the basis of
`HJO.Sweep.exists_basis_vstar_prod_bop`. -/
theorem map_evalOne_atildeE0_eq_top :
    Submodule.map (evalOne ρ) (Atilde.atildeE0 L q u) = ⊤ := by
  obtain ⟨B, hB⟩ := exists_basis_vstar_prod_bop (L := L) q
  rw [eq_top_iff, ← B.span_eq, Submodule.span_le]
  rintro _ ⟨⟨k, a, l⟩, rfl⟩
  obtain ⟨F, hF1, hF2⟩ := hB k a l
  rw [hF1]
  refine ofPiece_mem_map_evalOne hρe hρT hρD hρU hρS l.1 k a F ?_
  rw [hF2, Finsupp.prod_fintype _ (fun (j : Fin k) (m : ℕ) => (auxVar ((j : ℕ) + 1) : Total L) ^ m)
    fun j => pow_zero _]

end Eval

end HJO.Sweep

/-! ### The displayed elements and their values -/

namespace HJO.Sweep

open Dyck.Tilde

section Words

/-- The exponent function of the element of `HJO.Standing.dpaStructure_param` at the index
`(k, a, l)`: `a_1, …, a_k` at the head and `l_1 + 1, …, l_m + 1` at the tail, so that the tail
exponents are positive and weakly decreasing when `l` is. -/
def structureExponent (k : ℕ) (a : Fin k →₀ ℕ) (l : List ℕ) (s : ℕ) : ℕ :=
  if h : 1 ≤ s ∧ s ≤ k then a ⟨s - 1, by omega⟩ else l.getD (s - k - 1) 0 + 1

/-- The exponent of `y_{j+1}` for `j < k` is the head exponent `a_{j+1}`. -/
theorem structureExponent_head {k : ℕ} (a : Fin k →₀ ℕ) (l : List ℕ) (j : Fin k) :
    structureExponent k a l ((j : ℕ) + 1) = a j := by
  rw [structureExponent]
  split_ifs with h
  · congr 1
  · exact absurd ⟨by omega, j.2⟩ h

/-- The exponent of `y_{k+1+i}` is `l_{i+1} + 1`, read as `1` past the end of `l`. -/
theorem structureExponent_tail (k : ℕ) (a : Fin k →₀ ℕ) (l : List ℕ) (i : ℕ) :
    structureExponent k a l (k + 1 + i) = l.getD i 0 + 1 := by
  rw [structureExponent]
  split_ifs with h
  · omega
  · congr 2
    omega

/-- The product of `f` over the list `[1, …, k]` is `∏_{j < k} f (j + 1)`. -/
theorem prod_range'_one_map {M : Type*} [CommMonoid M] (f : ℕ → M) :
    ∀ k : ℕ, ((List.range' 1 k).map f).prod = ∏ j : Fin k, f ((j : ℕ) + 1)
  | 0 => by simp
  | k + 1 => by
    rw [List.range'_concat, List.map_append, List.prod_append, prod_range'_one_map f k,
      Fin.prod_univ_castSucc]
    simp [Nat.add_comm 1 k]

theorem map_range_getD_succ (l : List ℕ) :
    (List.range l.length).map (fun i => l.getD i 0 + 1) = l.map (· + 1) := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp only [List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem _ _ (by simpa using h1)]

variable (L : Type*) [Field L] (q u : L) [Invertible q] [Invertible (q - 1)]

/-- **The element `d_-^m y_1^{a_1} ⋯ y_k^{a_k} y_{k+1}^{l_1+1} ⋯ y_{k+m}^{l_m+1} d_+^{*k+m}𝟏_0`
of `Ã𝟏_0`**, `m` being the length of `l`: the displayed element of the proof of
`HJO.Standing.dpaStructure_param`, its tail exponents `l_i + 1` positive. -/
noncomputable def structureWord (k : ℕ) (a : Fin k →₀ ℕ) (l : List ℕ) : Atilde L q u :=
  Dyck.toTilde L q u (Dyck.Aq.dMinusPow L q k l.length *
      Dyck.Aq.yMon L q (k + l.length) (structureExponent k a l)) *
    Atilde.dPlusStarPow L q u 0 (k + l.length)

/-- The displayed element lies in `Ã𝟏_0`. -/
theorem structureWord_mem_atildeE0 (k : ℕ) (a : Fin k →₀ ℕ) (l : List ℕ) :
    structureWord L q u k a l ∈ Atilde.atildeE0 L q u := by
  rw [Atilde.mem_atildeE0_iff, structureWord, mul_assoc, Atilde.dPlusStarPow_mul_e]

end Words

section WordEval

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L} [Invertible q] [Invertible (q - 1)]

theorem dminus_auxVar_pow_mul_left (q : L) {k j : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) (n : ℕ)
    (F : Total L) :
    dminus q (k + 1) ((auxVar j : Total L) ^ n * F)
      = (auxVar j : Total L) ^ n * dminus q (k + 1) F := by
  induction n with
  | zero => rw [pow_zero, one_mul, one_mul]
  | succ n ih => rw [pow_succ', mul_assoc, dminus_auxVar_mul q hj hjk, ih, mul_assoc]

theorem dminus_prod_auxVar_pow_mul (q : L) {k : ℕ} (b : ℕ → ℕ) :
    ∀ l : List ℕ, (∀ s ∈ l, 1 ≤ s ∧ s ≤ k) → ∀ F : Total L,
      dminus q (k + 1) ((l.map fun s => (auxVar s : Total L) ^ b s).prod * F)
        = (l.map fun s => (auxVar s : Total L) ^ b s).prod * dminus q (k + 1) F := by
  intro l
  induction l with
  | nil => intro _ F; simp
  | cons s t ih =>
    intro hl F
    obtain ⟨hs1, hsk⟩ := hl s List.mem_cons_self
    rw [List.map_cons, List.prod_cons, mul_assoc, dminus_auxVar_pow_mul_left q hs1 hsk,
      ih (fun r hr => hl r (List.mem_cons_of_mem _ hr)), mul_assoc]

variable {ρb : Dyck.Aq L q →ₐ[L] Module.End L (Vstar L)} (hact : IsDpaAction q ρb)
  (hT : ∀ k i : ℕ, ρb (Dyck.Aq.Tg L q k i) = loopVstar (braidModPiece q) k i)
  (hD : ∀ k : ℕ, ρb (Dyck.Aq.dMinus L q k) = lowerVstar (dminusModPiece q) k)
  (hU : ∀ k : ℕ, ρb (Dyck.Aq.dPlus L q k) = raiseVstar (dplusModPiece q) k)

include hact hT hD hU in
/-- **A product of corner elements acts by multiplication by the variables**, in the modified
action. -/
theorem map_yProd_ofPiece_vmod {k : ℕ} (b : ℕ → ℕ) :
    ∀ l : List ℕ, (∀ s ∈ l, 1 ≤ s ∧ s ≤ k) → ∀ F : pieceSub L k,
      ∃ G : pieceSub L k, ρb (Dyck.Aq.yProd L q k b l) (ofPiece L k F) = ofPiece L k G ∧
        (G : Total L) = (l.map fun s => (auxVar s : Total L) ^ b s).prod * F := by
  intro l
  induction l with
  | nil => intro _ F; exact ⟨F, by rw [Dyck.Aq.yProd_nil, map_one]; rfl, by simp⟩
  | cons s t ih =>
    intro hl F
    obtain ⟨hs1, hsk⟩ := hl s List.mem_cons_self
    obtain ⟨G, hG, hGv⟩ := ih (fun r hr => hl r (List.mem_cons_of_mem _ hr)) F
    refine ⟨(auxMulPiece L k s ^ b s) G, ?_, ?_⟩
    · rw [Dyck.Aq.yProd_cons, map_mul, Module.End.mul_apply, hG, map_pow,
        map_yElt_eq_auxMulPiece hact hT hD hU hs1 hsk, loopVstar_pow_ofPiece]
    · rw [coe_auxMulPiece_pow hs1 hsk, hGv, List.map_cons, List.prod_cons, mul_assoc]

variable {ρ : Atilde L q u →ₐ[L] Module.End L (Vstar L)}
  (hρe : ∀ k : ℕ, ρ (Atilde.e L q u k) = pieceProj L k)
  (hρT : ∀ k i : ℕ, ρ (Atilde.Tg L q u k i) = loopVstar (braidModPiece q) k i)
  (hρD : ∀ k : ℕ, ρ (Atilde.dMinus L q u k) = lowerVstar (dminusModPiece q) k)
  (hρU : ∀ k : ℕ, ρ (Atilde.dPlus L q u k) = raiseVstar (dplusModPiece q) k)
  (hρS : ∀ k : ℕ, ρ (Atilde.dPlusStar L q u k) = raiseVstar (dplusStarPiece q u) k)

include hρe hρT hρD hρU hρS in
/-- **The value of `d_-^m y^b d_+^{*k+m}𝟏_0`**: it is
`y_1^{b_1} ⋯ y_k^{b_k} B_{b_{k+1}}(⋯ B_{b_{k+m}}(1)⋯) ∈ V_k`. The starred tower evaluates to `1`,
the corner elements multiply, and each lowering `d^♭_-` passes the earlier variables and turns
`y_j^r g` into `B_r g` (`HJO.Sweep.dminus_auxVar_pow_mul`). -/
theorem evalOne_toTilde_mul_dPlusStarPow (b : ℕ → ℕ) (m : ℕ) :
    ∀ k : ℕ, ∃ F : pieceSub L k,
      evalOne ρ (Dyck.toTilde L q u (Dyck.Aq.dMinusPow L q k m * Dyck.Aq.yMon L q (k + m) b) *
        Atilde.dPlusStarPow L q u 0 (k + m)) = ofPiece L k F ∧
      (F : Total L) = ((List.range' 1 k).map fun s => (auxVar s : Total L) ^ b s).prod *
        algebraMap (Sym.Lambda L) (Total L)
          ((((List.range m).map fun i => b (k + 1 + i)).map
            fun r : ℕ => Sym.Bop q (r : ℤ)).prod 1) := by
  have hact := isDpaAction_comp_toTilde (u := u) hρe
  have hT : ∀ k i : ℕ, (ρ.comp (Dyck.toTilde L q u)) (Dyck.Aq.Tg L q k i)
      = loopVstar (braidModPiece q) k i := fun k i => by
    rw [AlgHom.comp_apply, Dyck.toTilde_Tg, hρT]
  have hD : ∀ k : ℕ, (ρ.comp (Dyck.toTilde L q u)) (Dyck.Aq.dMinus L q k)
      = lowerVstar (dminusModPiece q) k := fun k => by
    rw [AlgHom.comp_apply, Dyck.toTilde_dMinus, hρD]
  have hU : ∀ k : ℕ, (ρ.comp (Dyck.toTilde L q u)) (Dyck.Aq.dPlus L q k)
      = raiseVstar (dplusModPiece q) k := fun k => by
    rw [AlgHom.comp_apply, Dyck.toTilde_dPlus, hρU]
  induction m with
  | zero =>
    intro k
    obtain ⟨G, hG, hGv⟩ := map_yProd_ofPiece_vmod hact hT hD hU (k := k) b (List.range' 1 k)
      (fun s hs => Dyck.Aq.mem_range'_one_bounds hs) (oneAtPiece L k)
    refine ⟨G, ?_, ?_⟩
    · rw [Dyck.Aq.dMinusPow_zero, Nat.add_zero, evalOne_mul,
        evalOne_dPlusStarPow_zero hρe hρS, ← AlgHom.comp_apply, map_mul, Module.End.mul_apply,
        Dyck.Aq.yMon, show oneAt L k = ofPiece L k (oneAtPiece L k) from rfl, hG,
        hact.map_e, pieceProj_ofPiece]
    · rw [hGv]; simp
  | succ m ih =>
    intro k
    obtain ⟨G, hG, hGv⟩ := ih (k + 1)
    refine ⟨dminusModPiece q k G, ?_, ?_⟩
    · rw [Dyck.Aq.dMinusPow_succ_left, show k + (m + 1) = k + 1 + m from by omega,
        mul_assoc (Dyck.Aq.dMinus L q k), map_mul (Dyck.toTilde L q u),
        mul_assoc (Dyck.toTilde L q u (Dyck.Aq.dMinus L q k)), evalOne_mul, hG,
        Dyck.toTilde_dMinus, hρD, lowerVstar_ofPiece]
    · have hr : List.range' 1 (k + 1) = List.range' 1 k ++ [k + 1] := by
        rw [List.range'_concat]; congr 2; omega
      have hl : (List.range (m + 1)).map (fun i => b (k + 1 + i))
          = b (k + 1) :: (List.range m).map (fun i => b (k + 1 + 1 + i)) := by
        rw [List.range_succ_eq_map, List.map_cons, List.map_map]
        congr 1
        refine List.map_congr_left fun i _ => ?_
        simp only [Function.comp_apply, Nat.succ_eq_add_one]
        congr 1
        omega
      rw [coe_dminusModPiece, hGv, hr, List.map_append, List.prod_append,
        List.map_singleton, List.prod_singleton, mul_assoc,
        dminus_prod_auxVar_pow_mul q b _ (fun s hs => Dyck.Aq.mem_range'_one_bounds hs),
        MvPolynomial.algebraMap_eq, dminus_auxVar_pow_mul_C, hl,
        List.map_cons, List.prod_cons, Module.End.mul_apply]

include hρe hρT hρD hρU hρS in
/-- **The displayed element at `(k, a, l)` evaluates to `y^a B_{l_1+1}(⋯B_{l_m+1}(1)⋯)`**, the
vector of `HJO.Sweep.exists_basis_vstar_prod_bop` at the same index. -/
theorem evalOne_structureWord (k : ℕ) (a : Fin k →₀ ℕ) (l : List ℕ) :
    ∃ F : pieceSub L k, evalOne ρ (structureWord L q u k a l) = ofPiece L k F ∧
      (F : Total L) = (∏ j : Fin k, (auxVar ((j : ℕ) + 1) : Total L) ^ a j) *
        algebraMap (Sym.Lambda L) (Total L)
          (((l.map (· + 1)).map fun r : ℕ => Sym.Bop q (r : ℤ)).prod 1) := by
  obtain ⟨F, hF, hFv⟩ := evalOne_toTilde_mul_dPlusStarPow hρe hρT hρD hρU hρS
    (structureExponent k a l) l.length k
  refine ⟨F, hF, ?_⟩
  rw [hFv, prod_range'_one_map _ k]
  simp only [structureExponent_head, structureExponent_tail, map_range_getD_succ]

end WordEval

/-! ### The structure theorem, from the spanning statement -/

section Reduction

variable {L : Type*} [Field L] [Algebra ℚ L] (q u : L) [Invertible q] [Invertible (q - 1)]

/-- **The spanning half of `HJO.Standing.dpaStructure_param`**: the displayed elements
`d_-^m y_1^{a_1} ⋯ y_k^{a_k} y_{k+1}^{l_1+1} ⋯ y_{k+m}^{l_m+1} d_+^{*k+m}𝟏_0`, with `l` weakly
decreasing, span `Ã𝟏_0` modulo `𝓘`. -/
def StructureSpanning : Prop :=
  Atilde.atildeE0 L q u ≤
    Submodule.span L (Set.range fun i : Σ k : ℕ, (Fin k →₀ ℕ) × {l : List ℕ // l.SortedGE} =>
      structureWord L q u i.1 i.2.1 i.2.2.1) ⊔ (Atilde.mellitKernel L q u).restrictScalars L

/-- **`HJO.Standing.dpaStructure_param`, given the spanning statement.** The modified pair defines
an action `ρ` of `Ã` on `V_*`; the kernel of `φ : Ã𝟏_0 → V_*, x ↦ ρ(x)(1)` is `𝓘`, and the induced
map `Ã𝟏_0/𝓘 → V_*` is a linear isomorphism.

`𝓘 ⊆ ker φ` and the surjectivity of `φ` are unconditional
(`HJO.Sweep.mellitKernel_le_ker_evalOne`, `HJO.Sweep.map_evalOne_atildeE0_eq_top`). The displayed
elements evaluate to the basis of `HJO.Sweep.exists_basis_vstar_prod_bop`
(`HJO.Sweep.evalOne_structureWord`), so `φ` is injective on their span, and `hspan` then places the
kernel inside `𝓘`. -/
theorem dpaStructure_of_spanning (hq1 : q + 1 ≠ 0) (hspan : StructureSpanning q u) :
    ∃ ρ : Atilde L q u →ₐ[L] Module.End L (Vstar L),
      (∀ k : ℕ, ρ (Atilde.e L q u k) = pieceProj L k)
      ∧ (∀ k i : ℕ, ρ (Atilde.Tg L q u k i) = loopVstar (braidModPiece q) k i)
      ∧ (∀ k : ℕ, ρ (Atilde.dMinus L q u k) = lowerVstar (dminusModPiece q) k)
      ∧ (∀ k : ℕ, ρ (Atilde.dPlus L q u k) = raiseVstar (dplusModPiece q) k)
      ∧ (∀ k : ℕ, ρ (Atilde.dPlusStar L q u k) = raiseVstar (dplusStarPiece q u) k)
      ∧ LinearMap.ker ((evalOne ρ).domRestrict (Atilde.atildeE0 L q u))
          = ((Atilde.mellitKernel L q u).restrictScalars L).comap (Atilde.atildeE0 L q u).subtype
      ∧ ∃ e : (Atilde.atildeE0 L q u ⧸ ((Atilde.mellitKernel L q u).restrictScalars L).comap
            (Atilde.atildeE0 L q u).subtype) ≃ₗ[L] Vstar L,
          ∀ x : Atilde.atildeE0 L q u, e (Submodule.Quotient.mk x) = evalOne ρ x := by
  obtain ⟨ρ, hρe, hρT, hρD, hρU, hρS⟩ := exists_action_atilde_mod q u hq1
  obtain ⟨B, hB⟩ := exists_basis_vstar_prod_bop (L := L) q
  set w : (Σ k : ℕ, (Fin k →₀ ℕ) × {l : List ℕ // l.SortedGE}) → Atilde L q u :=
    fun i => structureWord L q u i.1 i.2.1 i.2.2.1 with hw
  have hwB : ∀ i, evalOne ρ (w i) = B i := by
    rintro ⟨k, a, l⟩
    obtain ⟨F, hF, hFv⟩ := evalOne_structureWord hρe hρT hρD hρU hρS k a l.1
    obtain ⟨F', hF', hF'v⟩ := hB k a l
    rw [hw, hF, hF']
    exact ofPiece_congr (hFv.trans hF'v.symm)
  set ψ : Vstar L →ₗ[L] Atilde L q u := B.constr L w with hψ
  have hφψ : (evalOne ρ).comp ψ = LinearMap.id :=
    B.ext fun i => by rw [LinearMap.comp_apply, hψ, Module.Basis.constr_basis, hwB]; rfl
  have hrange : Submodule.span L (Set.range w) = LinearMap.range ψ := by
    rw [hψ, Module.Basis.constr_range]
  set N := ((Atilde.mellitKernel L q u).restrictScalars L).comap (Atilde.atildeE0 L q u).subtype
  have hker : LinearMap.ker ((evalOne ρ).domRestrict (Atilde.atildeE0 L q u)) = N := by
    refine le_antisymm ?_ ?_
    · intro x hx
      rw [LinearMap.mem_ker, LinearMap.domRestrict_apply] at hx
      have hx' := hspan x.2
      rw [hrange] at hx'
      obtain ⟨s, ⟨v, rfl⟩, r, hr, hsr⟩ := Submodule.mem_sup.1 hx'
      have hr0 : evalOne ρ r = 0 := mellitKernel_le_ker_evalOne hρe hρT hρD hρU hρS hr
      have hv : v = 0 := by
        have h := congrArg (evalOne ρ) hsr
        rw [map_add, hr0, add_zero, hx, ← LinearMap.comp_apply, hφψ, LinearMap.id_apply] at h
        exact h
      change (x : Atilde L q u) ∈ (Atilde.mellitKernel L q u).restrictScalars L
      rw [← hsr, hv, map_zero, zero_add]
      exact hr
    · intro x hx
      exact mellitKernel_le_ker_evalOne hρe hρT hρD hρU hρS hx
  have hsurj : Function.Surjective ((evalOne ρ).domRestrict (Atilde.atildeE0 L q u)) := by
    intro v
    have hv : v ∈ Submodule.map (evalOne ρ) (Atilde.atildeE0 L q u) := by
      rw [map_evalOne_atildeE0_eq_top hρe hρT hρD hρU hρS]; trivial
    obtain ⟨x, hx, rfl⟩ := hv
    exact ⟨⟨x, hx⟩, rfl⟩
  refine ⟨ρ, hρe, hρT, hρD, hρU, hρS, hker,
    (Submodule.quotEquivOfEq _ _ hker.symm).trans
      (LinearMap.quotKerEquivOfSurjective _ hsurj), fun x => ?_⟩
  rw [LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk, LinearMap.domRestrict_apply]

end Reduction

end HJO.Sweep

/-! ### The spanning statement -/

namespace HJO.Dyck.Aq

variable {K : Type*} [CommRing K] {q : K} [Invertible q] [Invertible (q - 1)]

theorem yElt_pow_mul_dMinus {n s : ℕ} (h1 : 1 ≤ s) (hs : s ≤ n) (c : ℕ) :
    dMinus K q n * yElt K q (n + 1) s ^ c = yElt K q n s ^ c * dMinus K q n := by
  have h : yElt K q n s * dMinus K q n = dMinus K q n * yElt K q (n + 1) s := by
    have := yElt_mul_dMinusPow (K := K) (q := q) h1 hs 1
    rwa [dMinusPow_succ, dMinusPow_zero, Nat.add_zero, e_mul_dMinus] at this
  induction c with
  | zero => rw [pow_zero, pow_zero, mul_one, one_mul]
  | succ c ih => rw [pow_succ, ← mul_assoc, ih, mul_assoc, ← h, ← mul_assoc, ← pow_succ]

theorem dMinus_mul_yProd {n : ℕ} (b : ℕ → ℕ) :
    ∀ l : List ℕ, (∀ s ∈ l, 1 ≤ s ∧ s ≤ n) →
      dMinus K q n * yProd K q (n + 1) b l = yProd K q n b l * dMinus K q n := by
  intro l
  induction l with
  | nil => intro _; rw [yProd_nil, yProd_nil, mul_one, one_mul]
  | cons s t ih =>
    intro hl
    obtain ⟨h1, h2⟩ := hl s List.mem_cons_self
    rw [yProd_cons, yProd_cons, ← mul_assoc, yElt_pow_mul_dMinus h1 h2, mul_assoc,
      ih (fun r hr => hl r (List.mem_cons_of_mem _ hr)), mul_assoc]

/-- **A lowering arrow passes a corner monomial free of the last variable.** -/
theorem dMinus_mul_yMon_of_eq_zero {n : ℕ} {b : ℕ → ℕ} (hb : b (n + 1) = 0) :
    dMinus K q n * yMon K q (n + 1) b = yMon K q n b * dMinus K q n := by
  have hr : List.range' 1 (n + 1) = List.range' 1 n ++ [n + 1] := by
    rw [List.range'_concat]; congr 2; omega
  have hsplit : yMon K q (n + 1) b = yProd K q (n + 1) b (List.range' 1 n) := by
    rw [yMon, hr, yProd, List.map_append, List.prod_append, List.map_singleton,
      List.prod_singleton, hb, pow_zero, mul_one, yProd]
  rw [hsplit, dMinus_mul_yProd b _ (fun s hs => by
    obtain ⟨h1, h2⟩ := mem_range'_one_bounds hs; exact ⟨h1, h2⟩), yMon]

end HJO.Dyck.Aq

namespace HJO.Dyck.Tilde.Atilde

variable {K : Type*} [CommRing K] {q u : K} [Invertible q] [Invertible (q - 1)]

/-! #### The starred vacuum tower -/

theorem dPlusStarPow_zero_succ (n : ℕ) :
    dPlusStarPow K q u 0 (n + 1) = dPlusStar K q u n * dPlusStarPow K q u 0 n := by
  rw [dPlusStarPow_succ, Nat.zero_add]

theorem e_mul_dPlusStarPow_zero (n : ℕ) :
    e K q u n * dPlusStarPow K q u 0 n = dPlusStarPow K q u 0 n := by
  cases n with
  | zero => exact e_mul_self 0
  | succ n => rw [dPlusStarPow_zero_succ, ← mul_assoc, e_mul_dPlusStar]

theorem mul_dPlusStarPow_zero_of_ne {x : Atilde K q u} {j n : ℕ} (hx : x * e K q u j = x)
    (h : j ≠ n) : x * dPlusStarPow K q u 0 n = 0 := by
  rw [← hx, mul_assoc, ← e_mul_dPlusStarPow_zero n, ← mul_assoc (e K q u j), e_mul_e_of_ne h,
    zero_mul, mul_zero]

/-- **The inverted loops fix the starred vacuum**: `T̂_i d₊^{*n}𝟏_0 = d₊^{*n}𝟏_0`, the starred
`T_1d₊²= d₊²` and `d₊T_i = T_{i+1}d₊`. -/
theorem Tinv_mul_dPlusStarPow_zero :
    ∀ n i : ℕ, i + 2 ≤ n → Tinv K q u n i * dPlusStarPow K q u 0 n = dPlusStarPow K q u 0 n := by
  intro n
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    intro i hi
    rcases i with _ | i
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      have hr : Tinv K q u (k + 1 + 1) 0 * (dPlusStar K q u (k + 1) * dPlusStar K q u k)
          = dPlusStar K q u (k + 1) * dPlusStar K q u k :=
        eq_of_sourceRelStar (SourceRel.braid_up_up k)
      rw [dPlusStarPow_zero_succ, dPlusStarPow_zero_succ, ← mul_assoc (dPlusStar K q u (k + 1)),
        ← mul_assoc (Tinv K q u (k + 1 + 1) 0), hr]
    · have hr : dPlusStar K q u n * Tinv K q u n i
          = Tinv K q u (n + 1) (i + 1) * dPlusStar K q u n :=
        eq_of_sourceRelStar (SourceRel.up_braid (by omega : i + 2 ≤ n))
      rw [dPlusStarPow_zero_succ, ← mul_assoc, ← hr, mul_assoc, ih i (by omega)]

/-- **The loops fix the starred vacuum.** -/
theorem Tg_mul_dPlusStarPow_zero {n i : ℕ} (h : i + 2 ≤ n) :
    Tg K q u n i * dPlusStarPow K q u 0 n = dPlusStarPow K q u 0 n := by
  rw [Tg_eq_tinvOf_Tinv, smul_mul_assoc, add_mul, smul_mul_assoc, Tinv_mul_dPlusStarPow_zero n i h,
    e_mul_dPlusStarPow_zero, ← one_smul K (dPlusStarPow K q u 0 n), smul_smul, mul_one,
    ← add_smul, smul_smul, add_sub_cancel, mul_invOf_self, one_smul]

/-! #### The starred corner elements kill the starred vacuum modulo `𝓘` -/

theorem mellitKernel_gen_one_eq (j : ℕ) :
    (dMinus K q u j * dPlusStar K q u j - e K q u j) * dPlusStarPow K q u 0 j
      = dMinus K q u j * dPlusStarPow K q u 0 (j + 1) - dPlusStarPow K q u 0 j := by
  rw [sub_mul, mul_assoc, ← dPlusStarPow_zero_succ, e_mul_dPlusStarPow_zero]

theorem dMinus_mul_dPlusStarPow_sub_mem (j : ℕ) :
    dMinus K q u j * dPlusStarPow K q u 0 (j + 1) - dPlusStarPow K q u 0 j
      ∈ mellitKernel K q u := by
  rw [← mellitKernel_gen_one_eq]
  exact Ideal.subset_span (Or.inl ⟨j, rfl⟩)

/-- The second family of `𝓘`: `d₊d₊^{*j}𝟏_0 + q^jy_1d₊^{*j+1}𝟏_0 ∈ 𝓘`. -/
theorem dPlus_mul_dPlusStarPow_add_mem (j : ℕ) :
    dPlus K q u j * dPlusStarPow K q u 0 j
        + (q ^ j) • (yElt K q u (j + 1) 1 * dPlusStarPow K q u 0 (j + 1))
      ∈ mellitKernel K q u := by
  have h : (dPlus K q u j + (q ^ j) • (yElt K q u (j + 1) 1 * dPlusStar K q u j)) *
      dPlusStarPow K q u 0 j ∈ mellitKernel K q u := Ideal.subset_span (Or.inr ⟨j, rfl⟩)
  rwa [add_mul, smul_mul_assoc, mul_assoc, ← dPlusStarPow_zero_succ] at h

/-- **`z_i d₊^{*n}𝟏_0 ∈ 𝓘`** for `1 ≤ i ≤ n`: the top one is `(q^{-1}-1)^{-1}T̂(d₊^*d₋ - d₋d₊^*)`
and both terms return the vacuum by the first family of `𝓘`; the lower ones follow by
`z_i = qT̂_iz_{i+1}T̂_i` and `T̂_i` fixing the vacuum. -/
theorem zElt_mul_dPlusStarPow_zero_mem {n : ℕ} :
    ∀ (d i : ℕ), i + d = n → 1 ≤ i →
      zElt K q u n i * dPlusStarPow K q u 0 n ∈ mellitKernel K q u := by
  intro d
  induction d with
  | zero =>
    intro i hin h1
    obtain rfl : i = n := by omega
    obtain ⟨p, rfl⟩ : ∃ p, i = p + 1 := ⟨i - 1, by omega⟩
    have hcomm : commOf (dPlusStar K q u) (dMinus K q u) p * dPlusStarPow K q u 0 (p + 1)
        = dPlusStar K q u p * (dMinus K q u p * dPlusStarPow K q u 0 (p + 1)
            - dPlusStarPow K q u 0 p)
          - (dMinus K q u (p + 1) * dPlusStarPow K q u 0 (p + 1 + 1)
            - dPlusStarPow K q u 0 (p + 1)) := by
      simp only [commOf, sub_mul, mul_sub, mul_assoc, ← dPlusStarPow_zero_succ]
      abel
    have hmem : commOf (dPlusStar K q u) (dMinus K q u) p * dPlusStarPow K q u 0 (p + 1)
        ∈ mellitKernel K q u := by
      rw [hcomm]
      exact sub_mem (Ideal.mul_mem_left _ _ (dMinus_mul_dPlusStarPow_sub_mem p))
        (dMinus_mul_dPlusStarPow_sub_mem (p + 1))
    rw [zElt, cornerOf_self_eq, smul_mul_assoc, mul_assoc, mul_assoc, e_mul_dPlusStarPow_zero,
      Nat.add_sub_cancel]
    exact Submodule.smul_of_tower_mem _ _ (Ideal.mul_mem_left _ _ hmem)
  | succ d ih =>
    intro i hin h1
    have hrec : zElt K q u n i
        = q • (Tinv K q u n (i - 1) * zElt K q u n (i + 1) * Tinv K q u n (i - 1)) := by
      rw [zElt, zElt, cornerOf, cornerOf, show n - i = (n - (i + 1)) + 1 from by omega,
        cornerAux, show n - (n - (i + 1)) - 2 = i - 1 from by omega]
    rw [hrec, smul_mul_assoc, mul_assoc, Tinv_mul_dPlusStarPow_zero n (i - 1) (by omega),
      mul_assoc]
    exact Submodule.smul_of_tower_mem _ _
      (Ideal.mul_mem_left _ _ (ih (i + 1) (by omega) (by omega)))

/-! #### The starred normal-form words -/

variable (K q u) in
/-- **The starred normal-form word** `d₋^m y_1^{b_1} ⋯ y_{k+m}^{b_{k+m}} d₊^{*k+m}𝟏_0`, the
lowering block and the corner monomial being read in `𝔸_q`. -/
noncomputable def starNormalWord (k m : ℕ) (b : ℕ → ℕ) : Atilde K q u :=
  HJO.Dyck.toTilde K q u (Aq.dMinusPow K q k m * Aq.yMon K q (k + m) b) *
    dPlusStarPow K q u 0 (k + m)

variable (K q u) in
/-- The span of the starred normal-form words. -/
noncomputable def starNormalSpan : Submodule K (Atilde K q u) :=
  Submodule.span K {x | ∃ k m b, x = starNormalWord K q u k m b}

/-- Every starred normal-form word lies in their span. -/
theorem starNormalWord_mem (k m : ℕ) (b : ℕ → ℕ) :
    starNormalWord K q u k m b ∈ starNormalSpan K q u :=
  Submodule.subset_span ⟨k, m, b, rfl⟩

/-- With no lowering and zero exponents, the starred normal-form word is `d₊^{*n}𝟏_0`. -/
theorem starNormalWord_zero (n : ℕ) :
    starNormalWord K q u n 0 (fun _ => 0) = dPlusStarPow K q u 0 n := by
  rw [starNormalWord, Aq.dMinusPow_zero, Aq.yMon_zero, mul_one, Nat.add_zero, HJO.Dyck.toTilde_e,
    e_mul_dPlusStarPow_zero]

theorem dPlusStarPow_mem_starNormalSpan (n : ℕ) :
    dPlusStarPow K q u 0 n ∈ starNormalSpan K q u := by
  rw [← starNormalWord_zero]; exact starNormalWord_mem _ _ _

/-- Left multiplication of a starred normal-form word by the image of `x ∈ 𝔸_q` multiplies its
`𝔸_q`-part by `x`. -/
theorem toTilde_mul_starNormalWord (x : Aq K q) (k m : ℕ) (b : ℕ → ℕ) :
    HJO.Dyck.toTilde K q u x * starNormalWord K q u k m b
      = HJO.Dyck.toTilde K q u (x * (Aq.dMinusPow K q k m * Aq.yMon K q (k + m) b)) *
        dPlusStarPow K q u 0 (k + m) := by
  rw [starNormalWord, ← mul_assoc, ← map_mul]

theorem toTilde_e_mul_starNormalWord_of_ne {l k : ℕ} (h : l ≠ k) (m : ℕ) (b : ℕ → ℕ) :
    HJO.Dyck.toTilde K q u (Aq.e K q l) * starNormalWord K q u k m b = 0 := by
  rw [toTilde_mul_starNormalWord, ← mul_assoc, ← Aq.e_mul_dMinusPow k m, ← mul_assoc,
    Aq.e_mul_e_of_ne h, zero_mul, zero_mul, map_zero, zero_mul]

theorem toTilde_mul_starNormalWord_of_ne {x : Aq K q} {l k : ℕ} (hx : x * Aq.e K q l = x)
    (h : l ≠ k) (m : ℕ) (b : ℕ → ℕ) :
    HJO.Dyck.toTilde K q u x * starNormalWord K q u k m b = 0 := by
  rw [← hx, map_mul, mul_assoc, toTilde_e_mul_starNormalWord_of_ne h, mul_zero]

/-- The lowering block and a span of corner monomials with a trailing loop, applied to the
vacuum: the trailing loop is absorbed. -/
theorem toTilde_dMinusPow_mul_mem_of_straighten {k m j N : ℕ} (hj : j + 2 ≤ k + m) {z : Aq K q}
    (hz : z ∈ Submodule.span K (Aq.straightenSet K q (k + m) (j + 1) N)) :
    HJO.Dyck.toTilde K q u (Aq.dMinusPow K q k m * z) * dPlusStarPow K q u 0 (k + m)
      ∈ starNormalSpan K q u := by
  refine Submodule.span_induction
    (p := fun z _ => HJO.Dyck.toTilde K q u (Aq.dMinusPow K q k m * z) *
      dPlusStarPow K q u 0 (k + m) ∈ starNormalSpan K q u) ?_ ?_ ?_ ?_ hz
  · rintro z ⟨b, -, hz | hz⟩
    · rw [hz, Nat.add_sub_cancel, ← mul_assoc, map_mul, mul_assoc, HJO.Dyck.toTilde_Tg,
        Tg_mul_dPlusStarPow_zero hj]
      exact starNormalWord_mem k m b
    · rw [hz]; exact starNormalWord_mem k m b
  · rw [mul_zero, map_zero, zero_mul]; exact zero_mem _
  · intro x y _ _ hx hy; rw [mul_add, map_add, add_mul]; exact add_mem hx hy
  · intro c x _ hx; rw [mul_smul_comm, map_smul, smul_mul_assoc]; exact Submodule.smul_mem _ c hx

/-- The span of the starred normal-form words is stable under left multiplication by each `T_s`. -/
theorem toTilde_Tg_mul_starNormalWord_mem (l s k m : ℕ) (b : ℕ → ℕ) :
    HJO.Dyck.toTilde K q u (Aq.Tg K q l s) * starNormalWord K q u k m b
      ∈ starNormalSpan K q u := by
  rcases eq_or_ne l k with rfl | h
  · rcases Nat.lt_or_ge (s + 1) l with hs | hs
    · rw [toTilde_mul_starNormalWord, ← mul_assoc, Aq.Tg_mul_dMinusPow (by omega) m, mul_assoc]
      exact toTilde_dMinusPow_mul_mem_of_straighten (by omega)
        (Aq.Tg_mul_yMon_mem_span (k := l + m) (i := s + 1) (by omega) (by omega) b)
    · rw [Aq.Tg_eq_zero (by omega), map_zero, zero_mul]; exact zero_mem _
  · rw [toTilde_mul_starNormalWord_of_ne (Aq.Tg_mul_e l s) h]; exact zero_mem _

/-- Left multiplication by `y_r`, `1 ≤ r ≤ l`, sends a starred normal-form word into their span. -/
theorem toTilde_yElt_mul_starNormalWord_mem {l r : ℕ} (h1 : 1 ≤ r) (hrl : r ≤ l) (k m : ℕ)
    (b : ℕ → ℕ) :
    HJO.Dyck.toTilde K q u (Aq.yElt K q l r) * starNormalWord K q u k m b
      ∈ starNormalSpan K q u := by
  rcases eq_or_ne l k with rfl | h
  · rw [toTilde_mul_starNormalWord, ← mul_assoc, Aq.yElt_mul_dMinusPow h1 hrl m, mul_assoc,
      ← Aq.yMon_of_succ (K := K) (q := q) h1 (by omega : r ≤ l + m)
        (b' := Function.update b r (b r + 1)) (Function.update_self r (b r + 1) b)
        (fun s hs => Function.update_of_ne hs (b r + 1) b)]
    exact starNormalWord_mem l m _
  · rw [toTilde_mul_starNormalWord_of_ne (Aq.yElt_mul_e l r) h]; exact zero_mem _

/-- Left multiplication by `d₋` sends a starred normal-form word into their span. -/
theorem toTilde_dMinus_mul_starNormalWord_mem (l k m : ℕ) (b : ℕ → ℕ) :
    HJO.Dyck.toTilde K q u (Aq.dMinus K q l) * starNormalWord K q u k m b
      ∈ starNormalSpan K q u := by
  rcases eq_or_ne k (l + 1) with rfl | h
  · rw [toTilde_mul_starNormalWord, ← mul_assoc, ← Aq.dMinusPow_succ_left,
      show l + 1 + m = l + (m + 1) from by omega]
    exact starNormalWord_mem l (m + 1) b
  · rw [toTilde_mul_starNormalWord_of_ne (Aq.dMinus_mul_e l) (Ne.symm h)]; exact zero_mem _

/-- If left multiplication by `a` sends every starred normal-form word into their span, it
preserves the span. -/
theorem mul_mem_starNormalSpan_of_word {a : Atilde K q u}
    (ha : ∀ k m b, a * starNormalWord K q u k m b ∈ starNormalSpan K q u) {x : Atilde K q u}
    (hx : x ∈ starNormalSpan K q u) : a * x ∈ starNormalSpan K q u := by
  refine Submodule.span_induction (p := fun x _ => a * x ∈ starNormalSpan K q u) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨k, m, b, rfl⟩; exact ha k m b
  · rw [mul_zero]; exact zero_mem _
  · intro x y _ _ hx hy; rw [mul_add]; exact add_mem hx hy
  · intro c x _ hx; rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx

/-- **The starred normal-form words span a left `levelAlg`-module.** -/
theorem levelAlg_mul_mem_starNormalSpan {a : Atilde K q u} (ha : a ∈ levelAlg K q u)
    {x : Atilde K q u} (hx : x ∈ starNormalSpan K q u) : a * x ∈ starNormalSpan K q u := by
  induction ha using Algebra.adjoin_induction generalizing x with
  | mem z hz =>
    refine mul_mem_starNormalSpan_of_word ?_ hx
    intro k m b
    obtain ⟨l, rfl⟩ | ⟨l, s, rfl⟩ | ⟨l, j, hj1, hjl, rfl⟩ | ⟨l, rfl⟩ := hz
    · rcases eq_or_ne l k with rfl | h
      · rw [← HJO.Dyck.toTilde_e, toTilde_mul_starNormalWord, ← mul_assoc, Aq.e_mul_dMinusPow]
        exact starNormalWord_mem _ _ _
      · rw [← HJO.Dyck.toTilde_e, toTilde_e_mul_starNormalWord_of_ne h]; exact zero_mem _
    · rw [← HJO.Dyck.toTilde_Tg]; exact toTilde_Tg_mul_starNormalWord_mem l s k m b
    · rw [← HJO.Dyck.toTilde_yElt]; exact toTilde_yElt_mul_starNormalWord_mem hj1 hjl k m b
    · rw [← HJO.Dyck.toTilde_dMinus]; exact toTilde_dMinus_mul_starNormalWord_mem l k m b
  | algebraMap r =>
    rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    exact Submodule.smul_mem _ r hx
  | add y z _ _ hy hz => rw [add_mul]; exact add_mem (hy hx) (hz hx)
  | mul y z _ _ hy hz => rw [mul_assoc]; exact hy (hz hx)

/-- The image of the lowering block `d₋^m` lies in `levelAlg`. -/
theorem toTilde_dMinusPow_mem_levelAlg (k : ℕ) :
    ∀ m, HJO.Dyck.toTilde K q u (Aq.dMinusPow K q k m) ∈ levelAlg K q u
  | 0 => by rw [Aq.dMinusPow_zero, HJO.Dyck.toTilde_e]; exact e_mem_levelAlg k
  | m + 1 => by
    rw [Aq.dMinusPow_succ, map_mul, HJO.Dyck.toTilde_dMinus]
    exact mul_mem (toTilde_dMinusPow_mem_levelAlg k m) (dMinus_mem_levelAlg _)

/-- The image of a product of powers of corner elements `y_s`, `1 ≤ s ≤ n`, lies in `levelAlg`. -/
theorem toTilde_yProd_mem_levelAlg {n : ℕ} (b : ℕ → ℕ) :
    ∀ l : List ℕ, (∀ s ∈ l, 1 ≤ s ∧ s ≤ n) →
      HJO.Dyck.toTilde K q u (Aq.yProd K q n b l) ∈ levelAlg K q u := by
  intro l
  induction l with
  | nil => intro _; rw [Aq.yProd_nil, map_one]; exact one_mem _
  | cons s t ih =>
    intro hl
    obtain ⟨h1, h2⟩ := hl s List.mem_cons_self
    rw [Aq.yProd_cons, map_mul, map_pow, HJO.Dyck.toTilde_yElt]
    exact mul_mem (pow_mem (yElt_mem_levelAlg h1 h2) _)
      (ih fun r hr => hl r (List.mem_cons_of_mem _ hr))

/-- The image of `d₋^m y^b` lies in `levelAlg`. -/
theorem toTilde_normal_mem_levelAlg (k m : ℕ) (b : ℕ → ℕ) :
    HJO.Dyck.toTilde K q u (Aq.dMinusPow K q k m * Aq.yMon K q (k + m) b) ∈ levelAlg K q u := by
  rw [map_mul]
  exact mul_mem (toTilde_dMinusPow_mem_levelAlg k m)
    (toTilde_yProd_mem_levelAlg b _ fun s hs => Aq.mem_range'_one_bounds hs)

/-! #### The span modulo `𝓘` is a left `Ã`-submodule -/

variable (K q u) in
/-- The span of the starred normal-form words, together with `𝓘`. -/
noncomputable def starNormalSup : Submodule K (Atilde K q u) :=
  starNormalSpan K q u ⊔ (mellitKernel K q u).restrictScalars K

/-- If left multiplication by `a` sends the span of the starred normal-form words into the span
modulo `𝓘`, it preserves the span modulo `𝓘`. -/
theorem mul_mem_starNormalSup_of {a : Atilde K q u}
    (ha : ∀ x ∈ starNormalSpan K q u, a * x ∈ starNormalSup K q u) {y : Atilde K q u}
    (hy : y ∈ starNormalSup K q u) : a * y ∈ starNormalSup K q u := by
  obtain ⟨s, hs, r, hr, rfl⟩ := Submodule.mem_sup.1 hy
  rw [mul_add]
  exact add_mem (ha s hs) (Submodule.mem_sup_right (Ideal.mul_mem_left _ a hr))

/-- The span of the starred normal-form words modulo `𝓘` is a left `levelAlg`-module. -/
theorem levelAlg_mul_mem_starNormalSup {a : Atilde K q u} (ha : a ∈ levelAlg K q u)
    {y : Atilde K q u} (hy : y ∈ starNormalSup K q u) : a * y ∈ starNormalSup K q u :=
  mul_mem_starNormalSup_of (fun _ hx =>
    Submodule.mem_sup_left (levelAlg_mul_mem_starNormalSpan ha hx)) hy

/-- **`d₊` preserves the span modulo `𝓘`**: `d₊a ∈ levelAlg + levelAlg·d₊` for `a ∈ levelAlg`,
and `d₊d₊^{*n}𝟏_0 ≡ -q^ny_1d₊^{*n+1}𝟏_0` modulo the second family of `𝓘`. -/
theorem dPlus_mul_mem_starNormalSup (l : ℕ) {y : Atilde K q u} (hy : y ∈ starNormalSup K q u) :
    dPlus K q u l * y ∈ starNormalSup K q u := by
  refine mul_mem_starNormalSup_of (fun x hx => ?_) hy
  refine Submodule.span_induction (p := fun x _ => dPlus K q u l * x ∈ starNormalSup K q u)
    ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨k, m, b, rfl⟩
    rw [starNormalWord, ← mul_assoc]
    have hP := dPlus_mul_mem_levelPlus
      (toTilde_normal_mem_levelAlg (K := K) (q := q) (u := u) k m b) l
    refine Submodule.span_induction
      (p := fun z _ => z * dPlusStarPow K q u 0 (k + m) ∈ starNormalSup K q u) ?_ ?_ ?_ ?_ hP
    · rintro z (hz | ⟨a, ha, j, rfl⟩)
      · exact Submodule.mem_sup_left
          (levelAlg_mul_mem_starNormalSpan hz (dPlusStarPow_mem_starNormalSpan _))
      · rw [mul_assoc]
        rcases eq_or_ne j (k + m) with hj | hj
        · rw [hj]
          have hsplit : dPlus K q u (k + m) * dPlusStarPow K q u 0 (k + m)
              = (dPlus K q u (k + m) * dPlusStarPow K q u 0 (k + m)
                  + (q ^ (k + m)) • (yElt K q u (k + m + 1) 1 *
                    dPlusStarPow K q u 0 (k + m + 1)))
                - (q ^ (k + m)) • (yElt K q u (k + m + 1) 1 *
                    dPlusStarPow K q u 0 (k + m + 1)) := by abel
          rw [hsplit, mul_sub]
          refine sub_mem (Submodule.mem_sup_right (Ideal.mul_mem_left _ a
            (dPlus_mul_dPlusStarPow_add_mem (k + m)))) ?_
          rw [mul_smul_comm, ← mul_assoc]
          exact Submodule.smul_mem _ _ (Submodule.mem_sup_left
            (levelAlg_mul_mem_starNormalSpan (mul_mem ha (yElt_mem_levelAlg le_rfl (by omega)))
              (dPlusStarPow_mem_starNormalSpan _)))
        · rw [mul_dPlusStarPow_zero_of_ne (dPlus_mul_e j) hj, mul_zero]; exact zero_mem _
    · rw [zero_mul]; exact zero_mem _
    · intro x y _ _ hx hy; rw [add_mul]; exact add_mem hx hy
    · intro c x _ hx; rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx
  · rw [mul_zero]; exact zero_mem _
  · intro x y _ _ hx hy; rw [mul_add]; exact add_mem hx hy
  · intro c x _ hx; rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx

/-- **The image of `𝔸_q` preserves the span modulo `𝓘`.** -/
theorem unstarredAlg_mul_mem_starNormalSup {b : Atilde K q u} (hb : b ∈ unstarredAlg K q u)
    {y : Atilde K q u} (hy : y ∈ starNormalSup K q u) : b * y ∈ starNormalSup K q u := by
  obtain ⟨x, rfl⟩ := hb
  obtain ⟨w, rfl⟩ := RingQuot.mkAlgHom_surjective K (HJO.Dyck.Rel K q) x
  change HJO.Dyck.toTilde K q u (Aq.mk K q w) * y ∈ _
  rw [HJO.Dyck.toTilde_mk]
  induction w using FreeAlgebra.induction generalizing y with
  | grade0 r =>
    rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    exact Submodule.smul_mem _ r hy
  | grade1 g =>
    rw [show HJO.Dyck.freeToTilde K q u (FreeAlgebra.ι K g) = HJO.Dyck.genToTilde K q u g from
      FreeAlgebra.lift_ι_apply _ _]
    cases g with
    | vertex l => exact levelAlg_mul_mem_starNormalSup (e_mem_levelAlg l) hy
    | up l => exact dPlus_mul_mem_starNormalSup l hy
    | down l => exact levelAlg_mul_mem_starNormalSup (dMinus_mem_levelAlg l) hy
    | braid l i => exact levelAlg_mul_mem_starNormalSup (Tg_mem_levelAlg l i) hy
  | mul a b ha hb => rw [map_mul, mul_assoc]; exact ha (hb hy)
  | add a b ha hb => rw [map_add, add_mul]; exact add_mem (ha hy) (hb hy)

section StarSwap

variable {bar : K ≃+* K} {σ : Atilde K q u →+ Atilde K q u}
  (h : IsStarSwap q bar (e K q u) (dPlus K q u) (dPlusStar K q u) (dMinus K q u) (Tg K q u) σ)
  (hbar : bar q = ⅟q)

include h hbar

/-- **`d₊^*` preserves the span modulo `𝓘`.** Pushed rightwards through the letters of a word of
`levelAlg`, it lands in `starMod`, the span of `b·d₊^*` and `b·z_i` with `b` unstarred; on the
vacuum the first raises the tower and the second lies in `𝓘`. -/
theorem dPlusStar_mul_mem_starNormalSup (l : ℕ) {y : Atilde K q u}
    (hy : y ∈ starNormalSup K q u) : dPlusStar K q u l * y ∈ starNormalSup K q u := by
  refine mul_mem_starNormalSup_of (fun x hx => ?_) hy
  refine Submodule.span_induction (p := fun x _ => dPlusStar K q u l * x ∈ starNormalSup K q u)
    ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨k, m, b, rfl⟩
    rw [starNormalWord, ← mul_assoc]
    have hS := dPlusStar_mul_mem_starMod h hbar l
      (toTilde_normal_mem_levelAlg (K := K) (q := q) (u := u) k m b)
    refine Submodule.span_induction
      (p := fun z _ => z * dPlusStarPow K q u 0 (k + m) ∈ starNormalSup K q u) ?_ ?_ ?_ ?_ hS
    · rintro z (⟨c, hc, j, rfl⟩ | ⟨c, hc, j, i, hi1, hij, rfl⟩)
      · rw [mul_assoc]
        rcases eq_or_ne j (k + m) with hj | hj
        · rw [hj, ← dPlusStarPow_zero_succ]
          exact unstarredAlg_mul_mem_starNormalSup hc
            (Submodule.mem_sup_left (dPlusStarPow_mem_starNormalSpan _))
        · rw [mul_dPlusStarPow_zero_of_ne (dPlusStar_mul_e j) hj, mul_zero]; exact zero_mem _
      · rw [mul_assoc]
        rcases eq_or_ne j (k + m) with hj | hj
        · subst hj
          exact Submodule.mem_sup_right (Ideal.mul_mem_left _ c
            (zElt_mul_dPlusStarPow_zero_mem (k + m - i) i (by omega) hi1))
        · rw [mul_dPlusStarPow_zero_of_ne (zElt_mul_e j i) hj, mul_zero]; exact zero_mem _
    · rw [zero_mul]; exact zero_mem _
    · intro x y _ _ hx hy; rw [add_mul]; exact add_mem hx hy
    · intro c x _ hx; rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx
  · rw [mul_zero]; exact zero_mem _
  · intro x y _ _ hx hy; rw [mul_add]; exact add_mem hx hy
  · intro c x _ hx; rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx

/-- **`Ã𝟏_0` is spanned by the starred normal-form words modulo `𝓘`.** -/
theorem atildeE0_le_starNormalSup : atildeE0 K q u ≤ starNormalSup K q u := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨w, rfl⟩ := RingQuot.mkAlgHom_surjective K (Tilde.Rel K q u) x
  rw [rightE0_apply]
  change mk K q u w * e K q u 0 ∈ _
  have he0 : e K q u 0 ∈ starNormalSup K q u :=
    Submodule.mem_sup_left (dPlusStarPow_mem_starNormalSpan (u := u) 0)
  generalize e K q u 0 = y at he0 ⊢
  induction w using FreeAlgebra.induction generalizing y with
  | grade0 r =>
    rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    exact Submodule.smul_mem _ r he0
  | grade1 g =>
    cases g with
    | vertex l =>
      change e K q u l * y ∈ _
      exact levelAlg_mul_mem_starNormalSup (e_mem_levelAlg l) he0
    | up l =>
      change dPlus K q u l * y ∈ _
      exact dPlus_mul_mem_starNormalSup l he0
    | upStar l =>
      change dPlusStar K q u l * y ∈ _
      exact dPlusStar_mul_mem_starNormalSup h hbar l he0
    | down l =>
      change dMinus K q u l * y ∈ _
      exact levelAlg_mul_mem_starNormalSup (dMinus_mem_levelAlg l) he0
    | braid l i =>
      change Tg K q u l i * y ∈ _
      exact levelAlg_mul_mem_starNormalSup (Tg_mem_levelAlg l i) he0
  | mul a b ha hb => rw [map_mul, mul_assoc]; exact ha _ (hb _ he0)
  | add a b ha hb => rw [map_add, add_mul]; exact add_mem (ha _ he0) (hb _ he0)

end StarSwap

end HJO.Dyck.Tilde.Atilde

/-! ### Sorting the tail and removing zero tail exponents -/

namespace HJO.Dyck.Tilde.Atilde

variable {K : Type*} [CommRing K] {q u : K} [Invertible q] [Invertible (q - 1)]

/-- The tail `b_{k+1}, …, b_{k+m}` of an exponent function is weakly decreasing. -/
def TailSorted (k m : ℕ) (b : ℕ → ℕ) : Prop := ∀ j, k + 1 ≤ j → j + 1 ≤ k + m → b (j + 1) ≤ b j

/-- A weakly decreasing tail satisfies `b_{j'} ≤ b_j` for `k + 1 ≤ j ≤ j' ≤ k + m`. -/
theorem TailSorted.antitone {k m : ℕ} {b : ℕ → ℕ} (hs : TailSorted k m b) {j j' : ℕ}
    (h1 : k + 1 ≤ j) (h2 : j ≤ j') (h3 : j' ≤ k + m) : b j' ≤ b j := by
  induction j', h2 using Nat.le_induction with
  | base => exact le_rfl
  | succ j' hj ih => exact (hs j' (by omega) h3).trans (ih (by omega))

variable (K q u) in
/-- The span of the starred normal-form words with weakly decreasing tail. -/
noncomputable def sortedStarNormalSpan : Submodule K (Atilde K q u) :=
  Submodule.span K {x | ∃ k m b, TailSorted k m b ∧ x = starNormalWord K q u k m b}

/-- The lowering block and a span of lower-straightened corner monomials of weight less than `w`,
applied to the vacuum, lie in the span of the starred normal-form words of weight less than `w`. -/
theorem toTilde_dMinusPow_mul_lowerStraighten_mem {k m j w : ℕ} (hj0 : 1 ≤ j)
    (hj : j + 1 ≤ k + m) {x : Aq K q}
    (hx : x ∈ Submodule.span K (Aq.lowerStraightenSet K q (k + m) j w)) :
    HJO.Dyck.toTilde K q u (Aq.dMinusPow K q k m * x) * dPlusStarPow K q u 0 (k + m)
      ∈ Submodule.span K {y | ∃ b', Aq.yMonWt (k + m) b' < w ∧
          y = starNormalWord K q u k m b'} := by
  refine Submodule.span_induction
    (p := fun z _ => HJO.Dyck.toTilde K q u (Aq.dMinusPow K q k m * z) *
      dPlusStarPow K q u 0 (k + m) ∈ Submodule.span K {y | ∃ b', Aq.yMonWt (k + m) b' < w ∧
        y = starNormalWord K q u k m b'}) ?_ ?_ ?_ ?_ hx
  · rintro z ⟨b, hb, hz | hz⟩
    · rw [hz, ← mul_assoc, map_mul, mul_assoc, HJO.Dyck.toTilde_Tg,
        Tg_mul_dPlusStarPow_zero (by omega)]
      exact Submodule.subset_span ⟨b, hb, rfl⟩
    · rw [hz]; exact Submodule.subset_span ⟨b, hb, rfl⟩
  · rw [mul_zero, map_zero, zero_mul]; exact zero_mem _
  · intro x y _ _ hx hy; rw [mul_add, map_add, add_mul]; exact add_mem hx hy
  · intro c x _ hx; rw [mul_smul_comm, map_smul, smul_mul_assoc]; exact Submodule.smul_mem _ c hx

/-- A starred normal-form word with a tail ascent `b_j < b_{j+1}` is a combination of starred
normal-form words of strictly smaller weight. -/
theorem starNormalWord_mem_span_lower {k m j : ℕ} (hj1 : k + 1 ≤ j) (hj2 : j + 1 ≤ k + m)
    (b : ℕ → ℕ) (hlt : b j < b (j + 1)) :
    starNormalWord K q u k m b
      ∈ Submodule.span K {y | ∃ b', Aq.yMonWt (k + m) b' < Aq.yMonWt (k + m) b ∧
          y = starNormalWord K q u k m b'} := by
  have hTg : Aq.dMinusPow K q k m * Aq.Tg K q (k + m) (j - 1) = Aq.dMinusPow K q k m :=
    Aq.dMinusPow_mul_Tg (by omega) m (by omega)
  have hkey : starNormalWord K q u k m b
      = HJO.Dyck.toTilde K q u (Aq.dMinusPow K q k m *
          (Aq.Tg K q (k + m) (j - 1) * Aq.yMon K q (k + m) b)) *
        dPlusStarPow K q u 0 (k + m) := by
    rw [starNormalWord, ← mul_assoc, hTg]
  rw [hkey]
  exact toTilde_dMinusPow_mul_lowerStraighten_mem (j := j) (by omega) (by omega)
    (Aq.Tg_mul_yMon_mem_span_lowerStraightenSet (n := k + m) (i := j) (by omega) (by omega)
      (b j + b (j + 1)) b le_rfl hlt)

/-- **Every starred normal-form word is a combination of sorted ones**: an ascent in the tail is
exchanged inside `d₋^m(-)d₊^{*k+m}𝟏_0`, which absorbs the loop on both sides, for monomials of
strictly smaller weight `∑ s·b_s`. -/
theorem starNormalWord_mem_sorted (k m : ℕ) :
    ∀ (w : ℕ) (b : ℕ → ℕ), Aq.yMonWt (k + m) b ≤ w →
      starNormalWord K q u k m b ∈ sortedStarNormalSpan K q u := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro b hb
    by_cases hsorted : TailSorted k m b
    · exact Submodule.subset_span ⟨k, m, b, hsorted, rfl⟩
    · simp only [TailSorted, not_forall, not_le] at hsorted
      obtain ⟨j, hj1, hj2, hjlt⟩ := hsorted
      refine Submodule.span_le.2 ?_ (starNormalWord_mem_span_lower hj1 hj2 b hjlt)
      rintro y ⟨b', hb', rfl⟩
      exact ih (Aq.yMonWt (k + m) b') (lt_of_lt_of_le hb' hb) b' le_rfl

/-- The span of the starred normal-form words is contained in the span of the sorted ones. -/
theorem starNormalSpan_le_sorted : starNormalSpan K q u ≤ sortedStarNormalSpan K q u := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨k, m, b, rfl⟩
  exact starNormalWord_mem_sorted k m _ b le_rfl

variable (K q u) in
/-- The span of the starred normal-form words with weakly decreasing, positive tail. -/
noncomputable def posStarNormalSpan : Submodule K (Atilde K q u) :=
  Submodule.span K {x | ∃ k m b, TailSorted k m b ∧ (∀ j, k + 1 ≤ j → j ≤ k + m → 1 ≤ b j) ∧
    x = starNormalWord K q u k m b}

/-- **A zero last tail exponent is removed by the first family of `𝓘`**:
`d₋ y^b d₊^* d₊^{*n}𝟏_0 ≡ y^b d₊^{*n}𝟏_0`. -/
theorem starNormalWord_succ_sub_mem {k m : ℕ} {b : ℕ → ℕ} (hb : b (k + m + 1) = 0) :
    starNormalWord K q u k (m + 1) b - starNormalWord K q u k m b ∈ mellitKernel K q u := by
  have h : starNormalWord K q u k (m + 1) b - starNormalWord K q u k m b
      = HJO.Dyck.toTilde K q u (Aq.dMinusPow K q k m * Aq.yMon K q (k + m) b) *
        (dMinus K q u (k + m) * dPlusStarPow K q u 0 (k + m + 1)
          - dPlusStarPow K q u 0 (k + m)) := by
    rw [starNormalWord, starNormalWord, show k + (m + 1) = k + m + 1 from by omega,
      Aq.dMinusPow_succ, mul_assoc, Aq.dMinus_mul_yMon_of_eq_zero hb, ← mul_assoc, map_mul,
      HJO.Dyck.toTilde_dMinus, mul_sub, mul_assoc]
  rw [h]
  exact Ideal.mul_mem_left _ _ (dMinus_mul_dPlusStarPow_sub_mem _)

/-- A starred normal-form word with weakly decreasing tail lies in the span of those with weakly
decreasing positive tail, modulo `𝓘`. -/
theorem sorted_starNormalWord_mem (k : ℕ) :
    ∀ (m : ℕ) (b : ℕ → ℕ), TailSorted k m b →
      starNormalWord K q u k m b
        ∈ posStarNormalSpan K q u ⊔ (mellitKernel K q u).restrictScalars K := by
  intro m
  induction m with
  | zero =>
    intro b hs
    exact Submodule.mem_sup_left (Submodule.subset_span ⟨k, 0, b, hs, fun j h1 h2 => by omega,
      rfl⟩)
  | succ m ih =>
    intro b hs
    by_cases hb : b (k + m + 1) = 0
    · have hs' : TailSorted k m b := fun j h1 h2 => hs j h1 (by omega)
      rw [← sub_add_cancel (starNormalWord K q u k (m + 1) b) (starNormalWord K q u k m b)]
      exact add_mem (Submodule.mem_sup_right (starNormalWord_succ_sub_mem hb)) (ih b hs')
    · refine Submodule.mem_sup_left (Submodule.subset_span ⟨k, m + 1, b, hs, fun j h1 h2 => ?_,
        rfl⟩)
      have := hs.antitone (j := j) (j' := k + (m + 1)) h1 h2 le_rfl
      rw [show k + (m + 1) = k + m + 1 from by omega] at this
      omega

/-- **`Ã𝟏_0` is spanned modulo `𝓘` by the words with sorted positive tail.** -/
theorem atildeE0_le_posStarNormalSpan_sup {bar : K ≃+* K} {σ : Atilde K q u →+ Atilde K q u}
    (h : IsStarSwap q bar (e K q u) (dPlus K q u) (dPlusStar K q u) (dMinus K q u) (Tg K q u) σ)
    (hbar : bar q = ⅟q) :
    atildeE0 K q u ≤ posStarNormalSpan K q u ⊔ (mellitKernel K q u).restrictScalars K := by
  refine (atildeE0_le_starNormalSup h hbar).trans (sup_le ?_ le_sup_right)
  refine starNormalSpan_le_sorted.trans (Submodule.span_le.2 ?_)
  rintro _ ⟨k, m, b, hs, rfl⟩
  exact sorted_starNormalWord_mem k m b hs

end HJO.Dyck.Tilde.Atilde

namespace HJO.Sweep

open Dyck.Tilde

section Spanning

variable {L : Type*} [Field L] [Algebra ℚ L] (q u : L) [Invertible q] [Invertible (q - 1)]

omit [Algebra ℚ L] in
/-- A word with sorted positive tail is a displayed element `HJO.Sweep.structureWord`. -/
theorem starNormalWord_mem_range_structureWord {k m : ℕ} {b : ℕ → ℕ}
    (hs : Atilde.TailSorted k m b) (hpos : ∀ j, k + 1 ≤ j → j ≤ k + m → 1 ≤ b j) :
    Atilde.starNormalWord L q u k m b ∈ Set.range
      fun i : Σ k : ℕ, (Fin k →₀ ℕ) × {l : List ℕ // l.SortedGE} =>
        structureWord L q u i.1 i.2.1 i.2.2.1 := by
  set a : Fin k →₀ ℕ := Finsupp.equivFunOnFinite.symm fun j => b ((j : ℕ) + 1) with ha
  set l : List ℕ := (List.range m).map fun i => b (k + 1 + i) - 1 with hl
  have hlen : l.length = m := by rw [hl, List.length_map, List.length_range]
  have hsorted : l.SortedGE := by
    rw [List.sortedGE_iff_pairwise, hl, List.pairwise_map]
    refine (List.pairwise_lt_range (n := m)).imp_of_mem fun {i i'} hi hi' hlt => ?_
    rw [List.mem_range] at hi hi'
    have := hs.antitone (j := k + 1 + i) (j' := k + 1 + i') (by omega) (by omega) (by omega)
    omega
  refine ⟨⟨k, a, ⟨l, hsorted⟩⟩, ?_⟩
  change structureWord L q u k a l = _
  rw [structureWord, hlen, Atilde.starNormalWord]
  congr 3
  refine Dyck.Aq.yMon_congr fun s h1 h2 => ?_
  rw [structureExponent]
  split_ifs with hsk
  · rw [ha, Finsupp.coe_equivFunOnFinite_symm]
    change b (s - 1 + 1) = b s
    congr 1
    omega
  · rw [hl, List.getD_eq_getElem _ _ (by simp only [List.length_map, List.length_range]; omega),
      List.getElem_map, List.getElem_range, show k + 1 + (s - k - 1) = s from by omega]
    have := hpos s (by omega) h2
    omega

omit [Algebra ℚ L] in
/-- **The spanning half of `HJO.Standing.dpaStructure_param`**, under the hypotheses of
`HJO.Sym.paramInvLambda`: a ring involution of the base inverting `q` and `u`, which the paper's
`ℚ(q,u)` carries. -/
theorem structureSpanning [Invertible u] {bar : L ≃+* L} (hbar : bar q = ⅟q) (hbaru : bar u = ⅟u)
    (hbb : ∀ c : L, bar (bar c) = c) : StructureSpanning q u := by
  obtain ⟨σ, hσ⟩ := Atilde.exists_isStarSwap (K := L) (q := q) (u := u) hbar hbaru hbb
  refine (Atilde.atildeE0_le_posStarNormalSpan_sup hσ hbar).trans (sup_le_sup_right ?_ _)
  refine Submodule.span_le.2 ?_
  rintro _ ⟨k, m, b, hs, hpos, rfl⟩
  exact Submodule.subset_span (starNormalWord_mem_range_structureWord q u hs hpos)

/-- **Mellit, the structure of the double module**, over a field carrying the involution of
`HJO.Sym.paramInvLambda`; over `𝕜 = ℚ(q, u)` it is `HJO.Standing.dpaStructure_param`. The modified
pair `(ρ^♭, ρ^{♭*})` defines an action `ρ` of `Ã` on `V_*`; the kernel of
`φ : Ã𝟏_0 → V_*, x ↦ ρ(x)(1)` is `𝓘`; and the induced map `Ã𝟏_0/𝓘 → V_*` is a linear
isomorphism. -/
theorem dpaStructure (hq1 : q + 1 ≠ 0) [Invertible u] {bar : L ≃+* L} (hbar : bar q = ⅟q)
    (hbaru : bar u = ⅟u) (hbb : ∀ c : L, bar (bar c) = c) :
    ∃ ρ : Atilde L q u →ₐ[L] Module.End L (Vstar L),
      (∀ k : ℕ, ρ (Atilde.e L q u k) = pieceProj L k)
      ∧ (∀ k i : ℕ, ρ (Atilde.Tg L q u k i) = loopVstar (braidModPiece q) k i)
      ∧ (∀ k : ℕ, ρ (Atilde.dMinus L q u k) = lowerVstar (dminusModPiece q) k)
      ∧ (∀ k : ℕ, ρ (Atilde.dPlus L q u k) = raiseVstar (dplusModPiece q) k)
      ∧ (∀ k : ℕ, ρ (Atilde.dPlusStar L q u k) = raiseVstar (dplusStarPiece q u) k)
      ∧ LinearMap.ker ((evalOne ρ).domRestrict (Atilde.atildeE0 L q u))
          = ((Atilde.mellitKernel L q u).restrictScalars L).comap (Atilde.atildeE0 L q u).subtype
      ∧ ∃ e : (Atilde.atildeE0 L q u ⧸ ((Atilde.mellitKernel L q u).restrictScalars L).comap
            (Atilde.atildeE0 L q u).subtype) ≃ₗ[L] Vstar L,
          ∀ x : Atilde.atildeE0 L q u, e (Submodule.Quotient.mk x) = evalOne ρ x :=
  dpaStructure_of_spanning q u hq1 (structureSpanning q u hbar hbaru hbb)

end Spanning

end HJO.Sweep

end
