/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CMStructure.AtildeKernel
public import HJO.CarlssonMellit.ConjugationBottom
public import HJO.CarlssonMellit.StarSwapKernel
public meta import HJO.Attr

/-! # Transporting a star swap of `Ã` to a conjugation operator on `V_*`

`HJO.Sweep.exists_isConjugationOperator` asserts that a conjugation operator exists, and the proof
of it is a transport: a star swap `σ` of `Ã` carries `I` into `I` and fixes `e_0`, so it descends to
`Ãe_0/Ie_0`, and the isomorphism `Ãe_0/Ie_0 ≅ V_*` of
`HJO.Standing.exists_action_atilde_ker_eq_param` carries the descended map to an operator on `V_*`
satisfying every clause of `HJO.Sweep.IsConjugationOperator`.

This file runs that transport on `HJO.Sweep.evalOne`, the map `fe_0 ↦ f(1)` of
`HJO.Sweep.exists_quotient_linearMap_evalOne`, **without** forming the quotient: what the argument
needs of the isomorphism is only that `evalOne` restricted to `Ã𝟏_0` is surjective and that its
kernel there is no larger than `I𝟏_0`, and those two containments are exactly the two hypotheses
`HJO.Sweep.exists_isConjugationOperator_of_evalOne` carries. Everything else it uses is proved
elsewhere:

* the action of `Ã` on `V_*` (`HJO.Sweep.exists_action_atilde`), through the
  five clauses naming the images of `e_k`, the loops `T_i`, `d_-`, `d_+` and `d^*_+`;
* `I𝟏_0 ⊆ ker` (`HJO.Sweep.kernelIdealE0_le_ker`), which carries no hypothesis beyond the action's;
* a star swap of `Ã` (`HJO.Dyck.Tilde.Atilde.exists_isStarSwap`) and its stability of `I`
  (`HJO.Dyck.Tilde.Atilde.IsStarSwap.mem_kernelIdeal`).

## The two hypotheses, and where they are discharged

The two hypotheses are the two halves of
`HJO.Sweep.exists_quotient_linearMap_evalOne`/`HJO.Standing.atildeE0_inf_ker_evalOne_eq_param`:

* **surjectivity** of `Ã𝟏_0 → V_*`, and
* **`Ã𝟏_0 ∩ ker ⊆ I𝟏_0`**, the `⊆` half of `HJO.Standing.atildeE0_inf_ker_evalOne_eq_param`.

Both are proved, and the main result itself is closed, in `HJO/CMStructure/Thm73Closed.lean`:
`HJO.Sweep.exists_quotient_linearMap_evalOne` is `HJO.Sweep.exists_quotient_linearMap_evalOne`,
`HJO.Standing.atildeE0_inf_ker_evalOne_eq_param` is `HJO.Sweep.atildeE0_inf_ker_evalOne_eq`, and
`HJO.Sweep.exists_isConjugationOperator` is `HJO.Sweep.exists_isConjugationOperator`. This file is
the part of the argument that is not one of the two containments.

## What comes out of the construction

The summand clause of `HJO.Sweep.IsConjugationOperator`, `𝒩(V_k) ⊆ V_k`, is `σ(e_k) = e_k`. It is
also what makes the two intertwining clauses provable in the form `𝒩(d_-F) = d_-𝒩(F)`, where the
operator on the right is applied to `𝒩F`: the construction proves that `𝒩F` lies in a summand
(`hproj` inside the theorem) and spends it there as well.

The loop clause `𝒩(T_iF) = T̂_i𝒩(F)` is `σ(T_i) = T̂_i`, the clause `HJO.Dyck.IsStarSwap.map_T` of
the star swap, read through the image `T_i ↦ HJO.Sweep.loopVstar (HJO.Sweep.braidModPiece q) k i` of
the loops under the action.

## Main results

* `HJO.Dyck.Tilde.Atilde.IsStarSwap.mem_atildeE0` and `.mem_kernelIdealE0`: a star swap preserves
  `Ã𝟏_0` and `I𝟏_0`.
* `HJO.Sweep.evalOne_starSwap_congr`: the descent, i.e. two elements of `Ã𝟏_0` with the same value
  on `1` have swapped elements with the same value on `1`.
* `HJO.Sweep.exists_isConjugationOperator_of_evalOne`: the transport.
* `HJO.Sweep.exists_isConjugationOperator_of_exists_action`: the same with the star swap discharged,
  so that the one input left is an action of `Ã` on `V_*` surjective from `Ã𝟏_0` with kernel there
  inside `I𝟏_0`.

## References

The lemmas involved are `HJO.Sweep.exists_isConjugationOperator`,
`HJO.Standing.exists_action_atilde_ker_eq_param`, `HJO.Sweep.exists_action_atilde`,
`HJO.Standing.atildeE0_inf_ker_evalOne_eq_param`, `HJO.Dyck.Tilde.Atilde.exists_isStarSwap`,
`HJO.Dyck.Tilde.Atilde.IsStarSwap.mem_kernelIdeal`, with the definitions
`HJO.Sweep.IsConjugationOperator`, `HJO.Dyck.Tilde.Atilde.kernelIdeal`, `HJO.Dyck.IsStarSwap`.
-/

@[expose] public section

/-! ### `Ã𝟏_0` and `I𝟏_0` under a star swap -/

namespace HJO.Dyck.Tilde.Atilde

variable {K : Type*} [CommRing K] {q u : K} [Invertible q] [Invertible (q - 1)]

/-- **`Ã𝟏_0` is a left ideal in the only sense used here**: it absorbs left multiplication, by
associativity. It is defined as the range of right multiplication by `𝟏_0`, which is a submodule and
not an ideal, so this does not come from its `Submodule` structure. -/
theorem mul_mem_atildeE0 (x : Atilde K q u) {y : Atilde K q u} (hy : y ∈ atildeE0 K q u) :
    x * y ∈ atildeE0 K q u := by
  obtain ⟨z, hz⟩ := hy
  rw [rightE0_apply] at hz
  exact ⟨x * z, by rw [rightE0_apply, mul_assoc, hz]⟩

/-- `𝟏_0` itself lies in `Ã𝟏_0`, the idempotent being its own witness. -/
theorem e_zero_mem_atildeE0 : e K q u 0 ∈ atildeE0 K q u :=
  ⟨e K q u 0, by rw [rightE0_apply, e_mul_self]⟩

namespace IsStarSwap

variable {bar : K ≃+* K} {σ : Atilde K q u →+ Atilde K q u}
variable (h : IsStarSwap q bar (e K q u) (dPlus K q u) (dPlusStar K q u) (dMinus K q u)
  (Tg K q u) σ)

include h

/-- **A star swap preserves `Ã𝟏_0`**: it is multiplicative and fixes `𝟏_0`. -/
theorem mem_atildeE0 {x : Atilde K q u} (hx : x ∈ atildeE0 K q u) : σ x ∈ atildeE0 K q u := by
  obtain ⟨z, hz⟩ := hx
  rw [rightE0_apply] at hz
  exact ⟨σ z, by rw [rightE0_apply, ← h.map_e 0, ← h.map_mul, hz]⟩

/-- **A star swap preserves `I𝟏_0`**: it carries `I` into `I` by
`HJO.Dyck.Tilde.Atilde.IsStarSwap.mem_kernelIdeal` and fixes `𝟏_0`, so it carries `z𝟏_0` to
`σ(z)𝟏_0`. -/
theorem mem_kernelIdealE0 {x : Atilde K q u} (hx : x ∈ kernelIdealE0 K q u) :
    σ x ∈ kernelIdealE0 K q u := by
  obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hx
  refine Submodule.mem_map.2 ⟨σ z, mem_kernelIdeal h hz, ?_⟩
  rw [rightE0_apply, rightE0_apply, h.map_mul, h.map_e]

end IsStarSwap

end HJO.Dyck.Tilde.Atilde

/-! ### The transport -/

namespace HJO.Sweep

open HJO.Sym

section Transport

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L} [Invertible q] [Invertible (q - 1)]
  (ρ : Dyck.Tilde.Atilde L q u →ₐ[L] Module.End L (Vstar L)) {bar : L ≃+* L}
  {σA : Dyck.Tilde.Atilde L q u →+ Dyck.Tilde.Atilde L q u}

variable (hρe : ∀ k : ℕ, ρ (Dyck.Tilde.Atilde.e L q u k) = pieceProj L k)
  (hρup : ∀ k : ℕ, ρ (Dyck.Tilde.Atilde.dPlus L q u k) = raiseVstar (cmDPlusPiece q) k)
  (hρupStar : ∀ k : ℕ,
    ρ (Dyck.Tilde.Atilde.dPlusStar L q u k) = raiseVstar (dplusStarPiece q u) k)
  (h : Dyck.IsStarSwap q bar (Dyck.Tilde.Atilde.e L q u) (Dyck.Tilde.Atilde.dPlus L q u)
    (Dyck.Tilde.Atilde.dPlusStar L q u) (Dyck.Tilde.Atilde.dMinus L q u)
    (Dyck.Tilde.Atilde.Tg L q u) σA)
  (hker : Dyck.Tilde.Atilde.atildeE0 L q u ⊓ LinearMap.ker (evalOne ρ)
    ≤ Dyck.Tilde.Atilde.kernelIdealE0 L q u)

include hρe hρup hρupStar h hker

omit [Algebra ℚ L] in
/-- **The descent.** Two elements of `Ã𝟏_0` with the same value on `1` have swapped elements with
the same value on `1`.

This is the whole of "`σ` induces a map on `Ãe_0/Ie_0`", and the only place either kernel hypothesis
is spent: the difference lies in `Ã𝟏_0 ∩ ker`, hence in `I𝟏_0` by `hker`, hence its swap lies in
`I𝟏_0` by `HJO.Dyck.Tilde.Atilde.IsStarSwap.mem_kernelIdeal`, hence in `ker` by
`HJO.Sweep.kernelIdealE0_le_ker`. -/
theorem evalOne_starSwap_congr {x y : Dyck.Tilde.Atilde L q u}
    (hx : x ∈ Dyck.Tilde.Atilde.atildeE0 L q u) (hy : y ∈ Dyck.Tilde.Atilde.atildeE0 L q u)
    (hxy : evalOne ρ x = evalOne ρ y) : evalOne ρ (σA x) = evalOne ρ (σA y) := by
  have hmem : x - y ∈ Dyck.Tilde.Atilde.atildeE0 L q u ⊓ LinearMap.ker (evalOne ρ) :=
    Submodule.mem_inf.2 ⟨sub_mem hx hy,
      LinearMap.mem_ker.2 (by rw [map_sub, hxy, sub_self])⟩
  have hswap : σA x - σA y ∈ Dyck.Tilde.Atilde.kernelIdealE0 L q u := by
    rw [← map_sub]
    exact Dyck.Tilde.Atilde.IsStarSwap.mem_kernelIdealE0 h (hker hmem)
  have hzero := kernelIdealE0_le_ker ρ hρe hρup hρupStar hswap
  rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at hzero
  exact hzero

end Transport

section Exists

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L} [Invertible q] [Invertible (q - 1)]
  {bar : L ≃+* L}

/-- **`HJO.Sweep.exists_isConjugationOperator`, modulo the two halves of the kernel statement.**
Given

* an action `ρ` of `Ã` on `V_*` in which `e_k` acts as the projection onto `V_k`, the loops as the
  operators `T_i` of the summands, and `d_-`, `d_+` and `d^*_+` as the operators of
  `HJO.Sweep.dminusCM`, `HJO.Sweep.cmDPlus` and `HJO.Sweep.dplusStar`
  (`HJO.Sweep.exists_action_atilde`),
* a star swap `σ` of `Ã` (`HJO.Dyck.Tilde.Atilde.exists_isStarSwap`),
* **surjectivity** of `fe_0 ↦ f(1)` from `Ã𝟏_0` onto `V_*`, and
* **`Ã𝟏_0 ∩ ker ⊆ I𝟏_0`**,

a conjugation operator exists. The last two are the two halves of
`HJO.Sweep.exists_quotient_linearMap_evalOne` and `HJO.Standing.atildeE0_inf_ker_evalOne_eq_param`,
discharged in `HJO/CMStructure/Thm73Closed.lean`, where the statement itself is
`HJO.Sweep.exists_isConjugationOperator`.

The operator is `F ↦ σ(x_F)(1)` for any `x_F ∈ Ã𝟏_0` with `x_F(1) = F`, which is well defined by
`HJO.Sweep.evalOne_starSwap_congr`. Each clause is then one algebra identity of the star swap read
through `HJO.Sweep.evalOne_mul`: additivity and `𝒩(cF) = c̄𝒩(F)` from `σ` being additive and
conjugate-linear, `𝒩𝒩 = id` from `σσ = id`, `𝒩(1) = 1` from `σ(𝟏_0) = 𝟏_0`, and the two
intertwining clauses from `σ(d_-) = d_-` and `σ(d_+) = d^*_+`, the summand clause from
`σ(e_k) = e_k`, and the loop clause from `σ(T_i) = T̂_i`. The summand clause is needed first: it is
what licenses replacing `d_-` read at the vertex `k + 1` by `d_-` read on all of `V_*`, the shape
`HJO.Sweep.IsConjugationOperator` states. -/
theorem exists_isConjugationOperator_of_evalOne
    (ρ : Dyck.Tilde.Atilde L q u →ₐ[L] Module.End L (Vstar L))
    {σA : Dyck.Tilde.Atilde L q u →+ Dyck.Tilde.Atilde L q u}
    (hρe : ∀ k : ℕ, ρ (Dyck.Tilde.Atilde.e L q u k) = pieceProj L k)
    (hρT : ∀ k i : ℕ, ρ (Dyck.Tilde.Atilde.Tg L q u k i) = loopVstar (braidModPiece q) k i)
    (hρd : ∀ k : ℕ, ρ (Dyck.Tilde.Atilde.dMinus L q u k) = lowerVstar (dminusPiece q) k)
    (hρup : ∀ k : ℕ, ρ (Dyck.Tilde.Atilde.dPlus L q u k) = raiseVstar (cmDPlusPiece q) k)
    (hρupStar : ∀ k : ℕ,
      ρ (Dyck.Tilde.Atilde.dPlusStar L q u k) = raiseVstar (dplusStarPiece q u) k)
    (h : Dyck.IsStarSwap q bar (Dyck.Tilde.Atilde.e L q u) (Dyck.Tilde.Atilde.dPlus L q u)
      (Dyck.Tilde.Atilde.dPlusStar L q u) (Dyck.Tilde.Atilde.dMinus L q u)
      (Dyck.Tilde.Atilde.Tg L q u) σA)
    (hsurj : ∀ F : Vstar L, ∃ x ∈ Dyck.Tilde.Atilde.atildeE0 L q u, evalOne ρ x = F)
    (hker : Dyck.Tilde.Atilde.atildeE0 L q u ⊓ LinearMap.ker (evalOne ρ)
      ≤ Dyck.Tilde.Atilde.kernelIdealE0 L q u) :
    ∃ N : Vstar L →+ Vstar L, IsConjugationOperator q u bar N := by
  choose sec hsecmem hsecval using hsurj
  -- The value of the operator does not depend on the chosen preimage.
  have hrep : ∀ (F : Vstar L) (x : Dyck.Tilde.Atilde L q u),
      x ∈ Dyck.Tilde.Atilde.atildeE0 L q u → evalOne ρ x = F →
      evalOne ρ (σA (sec F)) = evalOne ρ (σA x) := fun F x hx hxval =>
    evalOne_starSwap_congr ρ hρe hρup hρupStar h hker (hsecmem F) hx
      (by rw [hsecval, hxval])
  -- Both intertwining clauses need the summands preserved first, and that is `σ(e_k) = e_k`.
  have hproj : ∀ (k : ℕ) (G : Vstar L), pieceProj L k G = G →
      evalOne ρ (σA (sec G)) = ofPiece L k (toPiece L k (evalOne ρ (σA (sec G)))) := by
    intro k G hG
    have hx : Dyck.Tilde.Atilde.e L q u k * sec G ∈ Dyck.Tilde.Atilde.atildeE0 L q u :=
      Dyck.Tilde.Atilde.mul_mem_atildeE0 _ (hsecmem G)
    have hval : evalOne ρ (Dyck.Tilde.Atilde.e L q u k * sec G) = G := by
      rw [evalOne_mul, hsecval, hρe, hG]
    have key : evalOne ρ (σA (sec G)) = pieceProj L k (evalOne ρ (σA (sec G))) :=
      calc evalOne ρ (σA (sec G))
          = evalOne ρ (σA (Dyck.Tilde.Atilde.e L q u k * sec G)) := hrep G _ hx hval
        _ = evalOne ρ (Dyck.Tilde.Atilde.e L q u k * σA (sec G)) := by rw [h.map_mul, h.map_e]
        _ = pieceProj L k (evalOne ρ (σA (sec G))) := by rw [evalOne_mul, hρe]
    rw [pieceProj_apply] at key
    exact key
  -- Additivity.
  have hadd : ∀ F G : Vstar L, evalOne ρ (σA (sec (F + G)))
      = evalOne ρ (σA (sec F)) + evalOne ρ (σA (sec G)) := by
    intro F G
    rw [hrep (F + G) (sec F + sec G) (add_mem (hsecmem F) (hsecmem G))
      (by rw [map_add, hsecval, hsecval]), map_add, map_add]
  refine ⟨AddMonoidHom.mk' (fun F => evalOne ρ (σA (sec F))) hadd, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `𝒩(cF) = c̄𝒩(F)`
    intro c F
    change evalOne ρ (σA (sec (c • F))) = bar c • evalOne ρ (σA (sec F))
    rw [hrep (c • F) (c • sec F) (Submodule.smul_mem _ c (hsecmem F))
      (by rw [map_smul, hsecval]), h.map_smul, map_smul]
  · -- `𝒩(𝒩(F)) = F`
    intro F
    change evalOne ρ (σA (sec (evalOne ρ (σA (sec F))))) = F
    rw [hrep (evalOne ρ (σA (sec F))) (σA (sec F))
      (Dyck.Tilde.Atilde.IsStarSwap.mem_atildeE0 h (hsecmem F)) rfl, h.involutive, hsecval]
  · -- `𝒩(1) = 1`
    change evalOne ρ (σA (sec (oneVstar L))) = oneVstar L
    rw [hrep (oneVstar L) (Dyck.Tilde.Atilde.e L q u 0) Dyck.Tilde.Atilde.e_zero_mem_atildeE0
      (evalOne_e_zero ρ hρe), h.map_e, evalOne_e_zero ρ hρe]
  · -- `𝒩(d_-F) = d_-𝒩(F)`
    intro k F
    have hx : Dyck.Tilde.Atilde.dMinus L q u k * sec (ofPiece L (k + 1) F)
        ∈ Dyck.Tilde.Atilde.atildeE0 L q u :=
      Dyck.Tilde.Atilde.mul_mem_atildeE0 _ (hsecmem _)
    have hval : evalOne ρ (Dyck.Tilde.Atilde.dMinus L q u k * sec (ofPiece L (k + 1) F))
        = dminusVstar q (ofPiece L (k + 1) F) := by
      rw [evalOne_mul, hsecval, hρd, lowerVstar_ofPiece, dminusVstar_ofPiece]
    have hNG := hproj (k + 1) (ofPiece L (k + 1) F) (pieceProj_ofPiece (k + 1) F)
    change evalOne ρ (σA (sec (dminusVstar q (ofPiece L (k + 1) F))))
      = dminusVstar q (evalOne ρ (σA (sec (ofPiece L (k + 1) F))))
    rw [hrep _ _ hx hval, h.map_mul, h.map_dMinus, evalOne_mul, hρd, hNG, lowerVstar_ofPiece,
      dminusVstar_ofPiece]
  · -- `𝒩(d_+F) = d_+^*𝒩(F)`
    intro k F
    have hx : Dyck.Tilde.Atilde.dPlus L q u k * sec (ofPiece L k F)
        ∈ Dyck.Tilde.Atilde.atildeE0 L q u :=
      Dyck.Tilde.Atilde.mul_mem_atildeE0 _ (hsecmem _)
    have hval : evalOne ρ (Dyck.Tilde.Atilde.dPlus L q u k * sec (ofPiece L k F))
        = cmDPlusVstar q (ofPiece L k F) := by
      rw [evalOne_mul, hsecval, hρup, raiseVstar_ofPiece, cmDPlusVstar_ofPiece]
    have hNG := hproj k (ofPiece L k F) (pieceProj_ofPiece k F)
    change evalOne ρ (σA (sec (cmDPlusVstar q (ofPiece L k F))))
      = dplusStarVstar q u (evalOne ρ (σA (sec (ofPiece L k F))))
    rw [hrep _ _ hx hval, h.map_mul, h.map_dPlus, evalOne_mul, hρupStar, hNG, raiseVstar_ofPiece,
      dplusStarVstar_ofPiece]
  · -- `𝒩(V_k) ⊆ V_k`
    intro k F
    exact ⟨_, hproj k (ofPiece L k F) (pieceProj_ofPiece k F)⟩
  · -- `𝒩(T_iF) = T̂_i𝒩(F)`, from `σ(T_i) = T̂_i`
    intro k i hik F
    have hx : Dyck.Tilde.Atilde.Tg L q u k i * sec F ∈ Dyck.Tilde.Atilde.atildeE0 L q u :=
      Dyck.Tilde.Atilde.mul_mem_atildeE0 _ (hsecmem _)
    have hval : evalOne ρ (Dyck.Tilde.Atilde.Tg L q u k i * sec F)
        = loopVstar (braidModPiece q) k i F := by
      rw [evalOne_mul, hsecval, hρT]
    change evalOne ρ (σA (sec (loopVstar (braidModPiece q) k i F)))
      = q⁻¹ • (loopVstar (braidModPiece q) k i (evalOne ρ (σA (sec F)))
        + (q - 1) • pieceProj L k (evalOne ρ (σA (sec F))))
    rw [hrep _ _ hx hval, h.map_mul, h.map_T hik, evalOne_mul, Dyck.tinvOf, map_smul, map_add,
      map_smul, hρT, hρe, invOf_eq_inv]
    rfl

/-- **`HJO.Sweep.exists_isConjugationOperator` with its one remaining input named.** A conjugation
operator exists as soon as there is an action of `Ã` on `V_*` of the shape
`HJO.Sweep.exists_action_atilde` supplies which is *surjective* from `Ã𝟏_0` and whose kernel there
is inside `I𝟏_0`.

The star swap is discharged here by `HJO.Dyck.Tilde.Atilde.exists_isStarSwap`, whose three
hypotheses on the bar are `HJO.Sym.paramInvLambda`'s own; `[Invertible u]` is `u ≠ 0`. The one input
left is `hact`: an action with the five clauses `HJO.Sweep.exists_action_atilde` supplies, and the
pair of containments that `HJO/CMStructure/Thm73Closed.lean` proves. -/
theorem exists_isConjugationOperator_of_exists_action [Invertible u] (hbar : bar q = ⅟q)
    (hbaru : bar u = ⅟u) (hbb : ∀ c : L, bar (bar c) = c)
    (hact : ∃ ρ : Dyck.Tilde.Atilde L q u →ₐ[L] Module.End L (Vstar L),
      (∀ k : ℕ, ρ (Dyck.Tilde.Atilde.e L q u k) = pieceProj L k)
      ∧ (∀ k i : ℕ, ρ (Dyck.Tilde.Atilde.Tg L q u k i) = loopVstar (braidModPiece q) k i)
      ∧ (∀ k : ℕ, ρ (Dyck.Tilde.Atilde.dMinus L q u k) = lowerVstar (dminusPiece q) k)
      ∧ (∀ k : ℕ, ρ (Dyck.Tilde.Atilde.dPlus L q u k) = raiseVstar (cmDPlusPiece q) k)
      ∧ (∀ k : ℕ, ρ (Dyck.Tilde.Atilde.dPlusStar L q u k) = raiseVstar (dplusStarPiece q u) k)
      ∧ (∀ F : Vstar L, ∃ x ∈ Dyck.Tilde.Atilde.atildeE0 L q u, evalOne ρ x = F)
      ∧ Dyck.Tilde.Atilde.atildeE0 L q u ⊓ LinearMap.ker (evalOne ρ)
          ≤ Dyck.Tilde.Atilde.kernelIdealE0 L q u) :
    ∃ N : Vstar L →+ Vstar L, IsConjugationOperator q u bar N := by
  obtain ⟨ρ, hρe, hρT, hρd, hρup, hρupStar, hsurj, hker⟩ := hact
  obtain ⟨σA, h⟩ := Dyck.Tilde.Atilde.exists_isStarSwap hbar hbaru hbb
  exact exists_isConjugationOperator_of_evalOne ρ hρe hρT hρd hρup hρupStar h hsurj hker

end Exists

end HJO.Sweep
