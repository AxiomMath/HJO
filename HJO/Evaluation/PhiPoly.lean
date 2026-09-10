/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Paths.ReturnPathSolves
public import HJO.Evaluation.AExponential
public meta import HJO.Attr

/-! # Reading the evaluation of a slope homomorphism off an integer polynomial

For a slope homomorphism at `(a, b)` the scalar obtained by sign extraction from the operator
attached to a creation seed, applied to `1`, is the value at the two parameters of a two-variable
integer polynomial: the generating polynomial of the below-diagonal paths with the prescribed
return composition by hook count and area. Substituting `1` for the second variable *of that
polynomial* is an honest operation on it, and what comes out is a one-variable integer series in
the first parameter. That series is the evaluation attached to the seed.

Two evaluations are computed. On the `N`-fold iterate of the creation operator of a single block
the witness polynomial is the one of the paths returning to the diagonal after every block, so the
substitution leaves their hook generating function, which is the finite series shifted by the
block hook count. On the elementary symmetric function `e_N` the witness polynomial is symmetric
in its two variables, so its value at `(q, 1)` is its value at `(1, q)`; that kills the hook count
and leaves the area, giving the area polynomial of all below-diagonal `(aN, bN)`-paths.

Both statements have two halves: a witness polynomial exists, and every witness polynomial yields
the same series. The second half needs the two parameters to be algebraically independent, which
is what makes the witness unique; the same hypothesis keeps the parameters away from the values at
which the slope operators degenerate.
-/

@[expose] public section

open Finset PowerSeries

namespace HJO.PhiPoly

open HJO.Sym HJO.Paths HJO.ThetaSymmetry

/-! ### Two arithmetic preliminaries -/

/-- A power of `-1` is its own inverse. -/
private theorem neg_one_pow_mul_self {R : Type*} [Monoid R] [HasDistribNeg R] (m : ℕ) :
    (-1 : R) ^ m * (-1 : R) ^ m = 1 := by
  rw [← pow_add]
  exact Even.neg_one_pow ⟨_, rfl⟩

/-- Algebraically independent parameters pin a two-variable integer polynomial down by its
value at them. -/
theorem eq_of_aeval_eq {L : Type*} [CommRing L] {q u : L} (hqu : AlgebraicIndependent ℤ ![q, u])
    {π π' : MvPolynomial (Fin 2) ℤ}
    (h : MvPolynomial.aeval ![q, u] π = MvPolynomial.aeval ![q, u] π') : π = π' :=
  algebraicIndependent_iff_injective_aeval.mp hqu h

/-- Exchanging the two arguments of an evaluation of a two-variable polynomial is renaming its
two variables. -/
theorem aeval_rename_swap {R : Type*} [CommRing R] [Algebra ℤ R] (x y : R)
    (π : MvPolynomial (Fin 2) ℤ) :
    MvPolynomial.aeval ![x, y] (MvPolynomial.rename ![1, 0] π) =
      MvPolynomial.aeval ![y, x] π := by
  have hcomp : (![x, y] ∘ ![(1 : Fin 2), 0]) = ![y, x] := by
    funext i
    fin_cases i <;> simp
  rw [MvPolynomial.aeval_rename, hcomp]

/-! ### The witness polynomial of a return composition -/

variable {a b N : ℕ}

/-- The generating polynomial of the below-diagonal `(aN, bN)`-paths with return composition `α`
by hook count and area, corrected by the sign `(-1) ^ (N (b + 1))`: the first variable carries the
hook count and the second the area. -/
noncomputable def signedReturnPoly (a b N : ℕ) (α : List ℕ) : MvPolynomial (Fin 2) ℤ :=
  (-1) ^ (N * (b + 1)) * ∑ y ∈ (univ : Finset (Heights a b N)) with HasReturns α y,
    (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℤ) ^ hookCount y * MvPolynomial.X 1 ^ area y

/-- Evaluating the witness polynomial of a return composition at a pair of ring elements gives
the generating function of those paths by hook count and area. -/
theorem aeval_signedReturnPoly {R : Type*} [CommRing R] [Algebra ℤ R] (a b N : ℕ) (α : List ℕ)
    (x y : R) :
    MvPolynomial.aeval ![x, y] (signedReturnPoly a b N α) =
      (-1) ^ (N * (b + 1)) * ∑ z ∈ (univ : Finset (Heights a b N)) with HasReturns α z,
        x ^ hookCount z * y ^ area z := by
  simp [signedReturnPoly]

/-- The scalar attached to a composite creation seed by a slope homomorphism at `(a, b)` is the
value at the two parameters of the witness polynomial of the return composition `α.reverse`, the
below-diagonal convention reading the blocks of the seed's composition from the other end. -/
theorem signExtract_copComp_eq_aeval {L : Type*} [Field L] [Algebra ℚ L] {q u : L}
    (shuffle : External.Shuffle L) (epsilonGessel : External.EpsilonGessel L)
    (hab : Nat.Coprime a b) (ha : 1 < a) (hb : a < b)
    (hqu : AlgebraicIndependent ℤ ![q, u])
    (ι : Lambda L →ₐ[L] AlphabetSeries L) (hι : IsRealisation ι)
    (Θ : Lambda L →ₐ[L] Module.End L (Lambda L)) (hΘ : IsSlopeHom a b q u Θ) (hN : 0 < N)
    (α : List ℕ) (hαpos : ∀ x ∈ α, 0 < x) (hα : α.sum = N) :
    signExtract L (Θ (CopComp q α 1) 1) =
      MvPolynomial.aeval ![q, u] (signedReturnPoly a b N α.reverse) := by
  have h := EpsilonSelection.signExtract_copComp_eq_sum_paths (shuffle a b hab ha hb q u hqu)
    epsilonGessel ι hι Θ hΘ (by omega) (by omega) hN α hαpos hα
  rw [aeval_signedReturnPoly, ← h, ← mul_assoc, neg_one_pow_mul_self, one_mul]

/-! ### The value read off a witness polynomial -/

/-- The value the evaluation map reads off a witness polynomial of a seed of degree `n`: the
variable is substituted for the first parameter and `1` for the second, and the result carries the
sign `(-1) ^ (n (b + 1))`. -/
noncomputable def phiValue (b n : ℕ) (π : MvPolynomial (Fin 2) ℤ) : ℤ⟦X⟧ :=
  (-1) ^ (n * (b + 1)) * MvPolynomial.aeval ![(X : ℤ⟦X⟧), 1] π

/-! ### The return evaluation -/

/-- The composite creation operator of the composition `(1ᴺ)` is the `N`-th power of the creation
operator of a single block. -/
theorem copComp_replicate {L : Type*} [Field L] [Algebra ℚ L] (q : L) (M : ℕ) :
    CopComp q (List.replicate M 1) = Cop q 1 ^ M := by
  rw [CopComp, List.map_replicate, List.prod_replicate]

/-- Membership in the running sums of the composition `(1ᴹ)`. -/
private theorem mem_scanl_replicate : ∀ (M c k : ℕ),
    k ∈ (List.replicate M 1).scanl (· + ·) c ↔ c ≤ k ∧ k ≤ c + M := by
  intro M
  induction M with
  | zero => intro c k; simp only [List.replicate_zero, List.scanl_nil, List.mem_singleton]; omega
  | succ M ih =>
    intro c k
    rw [List.replicate_succ, List.scanl_cons, List.mem_cons, ih (c + 1) k]
    omega

/-- A path has return composition `(1ᴺ)` exactly when it returns to the diagonal after every
block: the running sums of `(1ᴺ)` are all the ranks from `0` to `N`. -/
theorem hasReturns_replicate_iff (y : Heights a b N) :
    HasReturns (List.replicate N 1) y ↔ IsReturnPath y := by
  have hall : ∀ k ≤ N, k ∈ (List.replicate N 1).scanl (· + ·) 0 := fun k hk =>
    (mem_scanl_replicate N 0 k).2 ⟨Nat.zero_le k, by omega⟩
  constructor
  · rintro ⟨hbd, -, -, h⟩
    exact ⟨hbd, fun k hk => (h k hk).2 (hall k hk)⟩
  · rintro ⟨hbd, h⟩
    refine ⟨hbd, fun x hx => ?_, by simp, fun k hk => iff_of_true (h k hk) (hall k hk)⟩
    rw [List.eq_of_mem_replicate hx]
    omega

/-- Substituting the variable for the first parameter and `1` for the second in the witness
polynomial of the composition `(1ᴺ)` leaves the hook generating function of the paths returning to
the diagonal after every block, which is the finite series shifted by the block hook count. -/
theorem phiValue_signedReturnPoly_replicate (rankOne : External.RankOneDinv)
    (goodTraverse : External.GoodTraverse) (coercivity : HJO.Literature.HuangCoercivity)
    (hab : Nat.Coprime a b) (ha : 1 < a) (hb : a < b) :
    phiValue b N (signedReturnPoly a b N (List.replicate N 1)) =
      (X : ℤ⟦X⟧) ^ kappaShift a b N * Gaps.finiteSeries a b N := by
  have hfilter : {z ∈ (univ : Finset (Heights a b N)) | HasReturns (List.replicate N 1) z} =
      {z ∈ (univ : Finset (Heights a b N)) | IsReturnPath z} :=
    Finset.filter_congr fun z _ => hasReturns_replicate_iff z
  rw [phiValue, aeval_signedReturnPoly, ← mul_assoc, neg_one_pow_mul_self, one_mul,
    ReturnPathSolves.pow_kappaShift_mul_finiteSeries rankOne goodTraverse coercivity hab ha hb N]
  exact Finset.sum_congr hfilter fun z _ => by rw [one_pow, mul_one]

/-- For a slope homomorphism at `(a, b)` and every `N ≥ 1`, the scalar attached to the `N`-fold
iterate of the creation operator of a single block, applied to `1`, is the value at the two
parameters of a two-variable integer polynomial, and substituting the variable for the first
parameter and `1` for the second in any such polynomial gives the finite series shifted by the
block hook count. -/
@[hjo "prop_phi_return"]
theorem phiValue_cop_one_pow {L : Type*} [Field L] [Algebra ℚ L] {q u : L}
    (rankOne : External.RankOneDinv) (goodTraverse : External.GoodTraverse)
    (coercivity : HJO.Literature.HuangCoercivity) (shuffle : External.Shuffle L)
    (epsilonGessel : External.EpsilonGessel L) (hab : Nat.Coprime a b) (ha : 1 < a) (hb : a < b)
    (hqu : AlgebraicIndependent ℤ ![q, u]) (ι : Lambda L →ₐ[L] AlphabetSeries L)
    (hι : IsRealisation ι) (Θ : Lambda L →ₐ[L] Module.End L (Lambda L))
    (hΘ : IsSlopeHom a b q u Θ) (hN : 0 < N) :
    signExtract L (Θ ((Cop q 1 ^ N) 1) 1) =
        MvPolynomial.aeval ![q, u] (signedReturnPoly a b N (List.replicate N 1)) ∧
      ∀ π : MvPolynomial (Fin 2) ℤ,
        signExtract L (Θ ((Cop q 1 ^ N) 1) 1) = MvPolynomial.aeval ![q, u] π →
          phiValue b N π = (X : ℤ⟦X⟧) ^ kappaShift a b N * Gaps.finiteSeries a b N := by
  have hwit : signExtract L (Θ ((Cop q 1 ^ N) 1) 1) =
      MvPolynomial.aeval ![q, u] (signedReturnPoly a b N (List.replicate N 1)) := by
    rw [← copComp_replicate, signExtract_copComp_eq_aeval shuffle epsilonGessel hab ha hb hqu ι hι
      Θ hΘ hN _ (fun x hx => by rw [List.eq_of_mem_replicate hx]; omega) (by simp),
      List.reverse_replicate]
  refine ⟨hwit, fun π hπ => ?_⟩
  rw [← eq_of_aeval_eq hqu (hwit.symm.trans hπ)]
  exact phiValue_signedReturnPoly_replicate rankOne goodTraverse coercivity hab ha hb

/-! ### The all-path evaluation -/

/-- For a slope homomorphism at `(a, b)` and every `N ≥ 1`, the scalar attached to the elementary
symmetric function `e_N`, applied to `1`, is the value at the two parameters of a two-variable
integer polynomial, and substituting the variable for the first parameter and `1` for the second
in any such polynomial gives the area polynomial of all below-diagonal `(aN, bN)`-paths. -/
@[hjo "prop_phi_e"]
theorem phiValue_elemSymm {L : Type*} [Field L] [Algebra ℚ L] {q u : L}
    (shuffle : External.Shuffle L) (epsilonGessel : External.EpsilonGessel L)
    (creationExpansion : External.CreationExpansion L) (hab : Nat.Coprime a b) (ha : 1 < a)
    (hb : a < b) (hqu : AlgebraicIndependent ℤ ![q, u]) (ι : Lambda L →ₐ[L] AlphabetSeries L)
    (hι : IsRealisation ι) (Θ : Lambda L →ₐ[L] Module.End L (Lambda L))
    (hΘ : IsSlopeHom a b q u Θ) (hN : 0 < N) :
    signExtract L (Θ (elemSymm L N) 1) = MvPolynomial.aeval ![q, u] (signedPathPoly a b N) ∧
      ∀ π : MvPolynomial (Fin 2) ℤ,
        signExtract L (Θ (elemSymm L N) 1) = MvPolynomial.aeval ![q, u] π →
          phiValue b N π = areaPoly a b N := by
  obtain ⟨hval, hswap⟩ := signExtract_elemSymm_isPoly_and_swap (shuffle a b hab ha hb q u hqu)
    (shuffle a b hab ha hb u q (algebraicIndependent_swap hqu)) epsilonGessel ι hι Θ hΘ
    (by omega) (by omega) hN (creationExpansion q N hN) (creationExpansion u N hN)
  refine ⟨hval, fun π hπ => ?_⟩
  have hsym : signedPathPoly a b N = MvPolynomial.rename ![1, 0] (signedPathPoly a b N) :=
    eq_of_aeval_eq hqu (by rw [aeval_rename_swap]; exact hswap)
  have hone : MvPolynomial.aeval ![(1 : ℤ⟦X⟧), X] (signedPathPoly a b N) =
      (-1) ^ (N * (b + 1)) * areaPoly a b N := by
    simp [signedPathPoly, pathPoly, areaPoly]
  rw [← eq_of_aeval_eq hqu (hval.symm.trans hπ), phiValue, hsym, aeval_rename_swap, hone,
    ← mul_assoc, neg_one_pow_mul_self, one_mul]

end HJO.PhiPoly
