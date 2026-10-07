/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Ascent.Transport
public import HJO.Shuffle.MellitInductionBaseChange
public import HJO.Shuffle.SweepWitnessLhs
public import HJO.Shuffle.MellitRem41
public import HJO.Shuffle.MellitLhsSlopeMediant

/-! # Carrying the sweep operators along a coefficient homomorphism

The sweep operators act on `HJO.Sweep.Total L = Λ_L[y_1, y_2, …]`, and each of them is defined
uniformly in the coefficient field. A ring homomorphism of fields
`φ : L → K` therefore induces the coefficient map `HJO.Sweep.totalMap φ : Total L → Total K`,
applying `φ` on both layers, and this map intertwines each operator over `L` at the parameters
`(q, u)` with the same operator over `K` at `(φ q, φ u)`.

For the swaps, the divided differences, the Demazure--Lusztig operators and their trains, `d_-`,
`d_+`, `d^*_+` and `z_1` this is proved in `HJO.Shuffle.MellitInductionBaseChange`. Here it is
proved for the operators `z_i`, the slope operators `Ξ_{m,n}`, the letters `Ω(1; a, b)`,
`Ω(2; a, b)` and `Z^{(k+1)}_{a,b}`, the stages `G_{k+1,A}` and the stage word
`G_{ℓ,α_ℓ} ⋯ G_{1,α_1}(1)`, the run of lowering operators `d_-^ℓ`, and the constant coefficient,
which `totalMap φ` carries to `HJO.Ascent.lambdaMap φ`.

No hypothesis on the parameters is needed. Several operators divide by `1 - q`, `q` or `q u`; the
division is total and a homomorphism of fields commutes with inversion (`map_inv₀`), so at a
degenerate instance both sides are the same totalisation.

## Main results

* `HJO.Sweep.totalMap_zop`, `HJO.Sweep.totalMap_slopeOperator`: `z_i` and `Ξ_{m,n}` transport.
* `HJO.Mellit.totalMap_stageWordTotal`, `HJO.Mellit.totalMap_lowerRun`: the stage word and the
  lowering run transport.
* `HJO.Sweep.constantCoeff_totalMap`: the constant coefficient of the transport is the
  coefficient extension of the constant coefficient.

## Implementation notes

The coefficient map is the ring homomorphism `HJO.Sweep.totalMap`, stated for any ring
homomorphism of fields; a homomorphism of `ℚ`-algebras `φ` enters through its coercion, and then
`HJO.Sweep.constantCoeff_totalMap_eq_lambdaMap` and `HJO.Sweep.totalMap_C_eq_lambdaMap` compare it
with the coefficient extension `HJO.Ascent.lambdaMap φ` of the symmetric functions.
-/

@[expose] public section

namespace HJO.Sweep

open MvPolynomial

variable {L K : Type*} [Field L] [Field K] (φ : L →+* K)

/-- The constant coefficient of the transport is the transport of the constant coefficient. -/
theorem constantCoeff_totalMap (F : Total L) :
    constantCoeff (totalMap φ F) = MvPolynomial.map φ (constantCoeff F) :=
  MvPolynomial.constantCoeff_map _ F

/-- Left multiplication by an auxiliary variable transports. -/
theorem totalMap_mulLeft_auxVar (i : ℕ) (F : Total L) :
    totalMap φ (LinearMap.mulLeft L (auxVar i : Total L) F)
      = LinearMap.mulLeft K (auxVar i : Total K) (totalMap φ F) := by
  simp only [LinearMap.mulLeft_apply, map_mul, totalMap_auxVar]

/-- The power of an operator intertwined with its counterpart is intertwined with the power of the
counterpart. -/
theorem totalMap_pow_apply {f : Module.End L (Total L)} {g : Module.End K (Total K)}
    (h : ∀ F, totalMap φ (f F) = g (totalMap φ F)) (n : ℕ) (F : Total L) :
    totalMap φ ((f ^ n) F) = (g ^ n) (totalMap φ F) := by
  induction n generalizing F with
  | zero => rfl
  | succ n ih => rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]

section Newton

variable [Algebra ℚ L] [Algebra ℚ K]

/-- **The operators `z_i` transport.** -/
theorem totalMap_zop (q u : L) (k i : ℕ) (F : Total L) :
    totalMap φ (zop q u k i F) = zop (φ q) (φ u) k i (totalMap φ F) := by
  induction i using Nat.strong_induction_on generalizing F with
  | _ i ih =>
    match i, ih with
    | 0, _ => simp [zop]
    | 1, _ => exact totalMap_zopOneStar φ q u k F
    | i + 2, ih =>
      rw [zop_succ, zop_succ, LinearMap.smul_apply, LinearMap.smul_apply, totalMap_smul, map_inv₀,
        Module.End.mul_apply, Module.End.mul_apply, Module.End.mul_apply, Module.End.mul_apply,
        totalMap_braidEnd, ih (i + 1) (by omega), totalMap_braidEnd]

/-- **The slope operator `Ξ_{m,n}` transports.** -/
theorem totalMap_slopeOperator (q u : L) (k m n : ℕ) (F : Total L) :
    totalMap φ (slopeOperator q u k m n F) = slopeOperator (φ q) (φ u) k m n (totalMap φ F) := by
  refine totalMap_list_prod φ _ _ _ (fun l _ F => ?_) F
  cases l
  · simp only [LinearMap.neg_apply, map_neg, totalMap_mulLeft_auxVar]
  · simp only [LinearMap.smul_apply, totalMap_smul, map_inv₀, map_mul, totalMap_zop]

end Newton

end HJO.Sweep

namespace HJO.Mellit

open MvPolynomial HJO.Sweep

variable {L K : Type*} [Field L] [Field K] [Algebra ℚ L] [Algebra ℚ K] (φ : L →+* K)

/-- **`Ω(1; a, b)` at the witness transports.** -/
theorem totalMap_replOneTotal (q u : L) (a b k : ℕ) (F : Total L) :
    totalMap φ (replOneTotal q u a b k F) = replOneTotal (φ q) (φ u) a b k (totalMap φ F) := by
  simp only [replOneTotal, LinearMap.smul_apply, totalMap_smul, Module.End.mul_apply,
    LinearMap.neg_apply, map_neg, totalMap_slopeOperator, totalMap_mulLeft_auxVar,
    totalMap_dplusStar, map_pow, map_one]

/-- **`Ω(2; a, b)` at the witness transports.** -/
theorem totalMap_replTwoTotal (q u : L) (a b k : ℕ) (F : Total L) :
    totalMap φ (replTwoTotal q u a b k F) = replTwoTotal (φ q) (φ u) a b k (totalMap φ F) := by
  simp only [replTwoTotal, LinearMap.smul_apply, totalMap_smul, Module.End.mul_apply,
    LinearMap.neg_apply, map_neg, totalMap_slopeOperator, totalMap_mulLeft_auxVar,
    totalMap_zopOneStar, map_pow, map_one]

/-- **`Z^{(k+1)}_{a,b}` at the witness transports**, the factor `q^{-k}` going to `φ(q)^{-k}`. -/
theorem totalMap_replicatedTotal (q u : L) (a b k : ℕ) (F : Total L) :
    totalMap φ (replicatedTotal q u a b k F)
      = replicatedTotal (φ q) (φ u) a b k (totalMap φ F) := by
  simp only [replicatedTotal, LinearMap.smul_apply, totalMap_smul, Module.End.mul_apply,
    totalMap_trainDownEnd, totalMap_replTwoTotal, totalMap_trainUpEnd, map_zpow₀]

/-- **The stage `G_{k+1,A}` at the witness transports.** -/
theorem totalMap_stageTotal (q u : L) (a b k A : ℕ) (F : Total L) :
    totalMap φ (stageTotal q u a b k A F) = stageTotal (φ q) (φ u) a b k A (totalMap φ F) := by
  rw [stageTotal, stageTotal, Module.End.mul_apply, Module.End.mul_apply,
    totalMap_pow_apply φ (totalMap_replicatedTotal φ q u a b k), Module.End.mul_apply,
    Module.End.mul_apply, totalMap_trainDownEnd, totalMap_replOneTotal]

/-- **The stage word from any grading transports.** -/
theorem totalMap_stageFromTotal (q u : L) (a b : ℕ) (α : List ℕ) (k : ℕ) (F : Total L) :
    totalMap φ (stageFromTotal q u a b k F α)
      = stageFromTotal (φ q) (φ u) a b k (totalMap φ F) α := by
  induction α generalizing k F with
  | nil => rfl
  | cons A α ih => rw [stageFromTotal, stageFromTotal, ih, totalMap_stageTotal]

/-- **The stage word `G_{ℓ,α_ℓ} ⋯ G_{1,α_1}(1)` transports.** -/
theorem totalMap_stageWordTotal (q u : L) (a b : ℕ) (α : List ℕ) :
    totalMap φ (stageWordTotal q u a b α) = stageWordTotal (φ q) (φ u) a b α := by
  rw [stageWordTotal, stageWordTotal, totalMap_stageFromTotal, map_one]

/-- **The run `d_-^n` of lowering operators transports.** -/
theorem totalMap_lowerRun (q : L) (n : ℕ) (F : Total L) :
    totalMap φ (lowerRun q n F) = lowerRun (φ q) n (totalMap φ F) := by
  induction n generalizing F with
  | zero => rfl
  | succ n ih => rw [lowerRun, lowerRun, Module.End.mul_apply, Module.End.mul_apply, ih,
      totalMap_dminus]

omit [Algebra ℚ L] [Algebra ℚ K] in
/-- **The argument `y_1 d^*_+ C(f)` of the base case transports.** -/
theorem totalMap_slopeArg (q u : L) (f : Sym.Lambda L) :
    totalMap φ (slopeArg q u f) = slopeArg (φ q) (φ u) (MvPolynomial.map φ f) := by
  rw [slopeArg_def, slopeArg_def, map_mul, totalMap_auxVar, totalMap_dplusStar, totalMap_C]

end HJO.Mellit

namespace HJO.Sweep

open MvPolynomial HJO.Ascent

variable {K K' : Type*} [Field K] [Algebra ℚ K] [Field K'] [Algebra ℚ K']
variable (φ : K →ₐ[ℚ] K')

/-- Along a homomorphism of `ℚ`-algebras, the transport of a constant is the constant of the
coefficient extension. -/
theorem totalMap_C_eq_lambdaMap (f : Sym.Lambda K) :
    totalMap (φ : K →+* K') (C f) = C (lambdaMap φ f) :=
  totalMap_C _ f

/-- Along a homomorphism of `ℚ`-algebras, the constant coefficient of the transport is the
coefficient extension of the constant coefficient. -/
theorem constantCoeff_totalMap_eq_lambdaMap (F : Total K) :
    constantCoeff (totalMap (φ : K →+* K') F) = lambdaMap φ (constantCoeff F) :=
  constantCoeff_totalMap _ F

end HJO.Sweep

end
