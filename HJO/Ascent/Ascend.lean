/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Ascent.TransportShuffle
public meta import HJO.Attr

/-!
# The ascent

Let `K` be the fraction field of the parameter ring `ℚ[q, u]`, and let `L` be a field of
characteristic zero carrying an algebraically independent pair `x, y`. This file reads statements
about slope operators over `K`, at the standing parameters, as statements over `L` at `(x, y)`.

## Main definitions

* `HJO.Ascent.ascend`: the homomorphism of `ℚ`-algebras `K →ₐ[ℚ] L` sending the standing
  parameters to `x` and `y`.

## Main results

* `HJO.Ascent.lambdaMap_slopeHom`: a homomorphism of `ℚ`-algebras of coefficient fields
  intertwines two slope homomorphisms at an admissible instance.
* `HJO.Ascent.commute_qop_ascend`: if two slope operators commute at the standing parameters, they
  commute at `(x, y)`.
* `HJO.Ascent.slopeHom_ascend`: `ascend` intertwines a slope homomorphism over `K` with one over
  `L`.
-/

@[expose] public section

namespace HJO.Ascent

open HJO.Sym

section SlopeHom

variable {K K' : Type*} [Field K] [Algebra ℚ K] [Field K'] [Algebra ℚ K']
variable (φ : K →ₐ[ℚ] K')

/-- **The coefficient extension intertwines a pair of slope homomorphisms.** For an admissible
instance, a slope homomorphism at `(a, b)` over `K` and one over `K'`, the extension carries the
operator attached to a symmetric function to the operator attached to its extension. -/
@[hjo "lem_asc_slope_hom"]
theorem lambdaMap_slopeHom {a b : ℕ} {x y : K} (h : IsAdmissible x y)
    {Θ : Lambda K →ₐ[K] Module.End K (Lambda K)}
    {Θ' : Lambda K' →ₐ[K'] Module.End K' (Lambda K')}
    (hΘ : IsSlopeHom a b x y Θ) (hΘ' : IsSlopeHom a b (φ x) (φ y) Θ') (g f : Lambda K) :
    lambdaMap φ (Θ g f) = Θ' (lambdaMap φ g) (lambdaMap φ f) := by
  have hU : ∀ (k : ℕ) (f : Lambda K), 0 < k →
      lambdaMap φ (Θ (axisGen (x * y) k) f) =
        Θ' (lambdaMap φ (axisGen (x * y) k)) (lambdaMap φ f) := by
    intro k f hk
    rw [hΘ k hk, lambdaMap_axisGen, map_mul, hΘ' k hk, lambdaMap_qop]
  have hC : ∀ (c : K) (f : Lambda K),
      lambdaMap φ (Θ (MvPolynomial.C c) f) =
        Θ' (lambdaMap φ (MvPolynomial.C c)) (lambdaMap φ f) := by
    intro c f
    rw [lambdaMap_C, ← MvPolynomial.algebraMap_eq, ← MvPolynomial.algebraMap_eq,
      AlgHom.commutes, AlgHom.commutes, Module.algebraMap_end_apply,
      Module.algebraMap_end_apply, lambdaMap_smul]
  obtain ⟨p, hp⟩ := (axisSub_bijective_of_isAdmissible h).surjective g
  subst hp
  induction p using MvPolynomial.induction_on generalizing f with
  | C c =>
    rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, MvPolynomial.algebraMap_eq]
    exact hC c f
  | add p q hpq hqq =>
    rw [map_add, map_add, map_add, LinearMap.add_apply, map_add, hpq, hqq, map_add,
      LinearMap.add_apply]
  | mul_X p i hpq =>
    rw [map_mul, axisSub_X, map_mul, map_mul, lambdaMap_axisGen, Module.End.mul_apply, hpq,
      hU (i + 1) f (Nat.succ_pos i), lambdaMap_axisGen, map_mul, map_mul Θ',
      Module.End.mul_apply]

end SlopeHom

/-! ### The ascent -/

section Ascend

variable (K : Type*) [Field K] [Algebra ℚ K] [Algebra ParamRing K] [IsFractionRing ParamRing K]
variable {L : Type*} [Field L] [Algebra ℚ L] {x y : L}

/-- The embedding of `K` into `L` sending the standing parameters to `x` and `y`, as a
homomorphism of `ℚ`-algebras. -/
noncomputable def ascend (h : AlgebraicIndependent ℤ ![x, y]) : K →ₐ[ℚ] L :=
  toRatAlgHom (paramEmbedding K h)

/-- `ascend` sends the standing parameter `q` to `x`. -/
@[simp]
theorem ascend_paramQ (h : AlgebraicIndependent ℤ ![x, y]) : ascend K h (paramQ K) = x :=
  paramEmbedding_paramQ h

/-- `ascend` sends the standing parameter `u` to `y`. -/
@[simp]
theorem ascend_paramU (h : AlgebraicIndependent ℤ ![x, y]) : ascend K h (paramU K) = y :=
  paramEmbedding_paramU h

/-- **A commutation of slope operators ascends.** If two slope operators commute at the standing
parameters, then they commute at any algebraically independent pair `x, y` in `L`. -/
theorem commute_qop_ascend {m n m' n' : ℕ} (h : AlgebraicIndependent ℤ ![x, y])
    (hstd : Commute (Qop (paramQ K) (paramU K) m n) (Qop (paramQ K) (paramU K) m' n')) :
    Commute (Qop x y m n) (Qop x y m' n') := by
  have key := commute_qop_map (ascend K h) hstd
  rwa [ascend_paramQ, ascend_paramU] at key

/-- **A slope homomorphism ascends.** For slope homomorphisms at `(a, b)` over `K`, at the
standing parameters, and over `L`, at `(x, y)`, the map `ascend` carries the operator attached to a
symmetric function to the operator attached to its image. -/
theorem slopeHom_ascend {a b : ℕ} (h : AlgebraicIndependent ℤ ![x, y])
    {Θ : Lambda K →ₐ[K] Module.End K (Lambda K)}
    {Θ' : Lambda L →ₐ[L] Module.End L (Lambda L)}
    (hΘ : IsSlopeHom a b (paramQ K) (paramU K) Θ) (hΘ' : IsSlopeHom a b x y Θ')
    (g f : Lambda K) :
    lambdaMap (ascend K h) (Θ g f) =
      Θ' (lambdaMap (ascend K h) g) (lambdaMap (ascend K h) f) := by
  refine lambdaMap_slopeHom (ascend K h) (isAdmissible_standing K) hΘ ?_ g f
  rwa [ascend_paramQ, ascend_paramU]

end Ascend

end HJO.Ascent
