/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Analysis.Normed.Field.Lemmas
public import HJO.Determinant.Basic
public meta import HJO.Attr

/-! # Finiteness of the path set and uniqueness of the normalised solution

Two well-definedness facts. First, for each `N` there are only finitely many below-diagonal
`(aN, bN)`-paths, whether a path is recorded as an eventually-constant height function `ℕ → ℕ`
or as a height vector on a finite index type. Second, the `q`-difference equation
`G(qz;q) = 𝒜(-z;q) G(z;q)` together with the normalisation `G(0;q) = 1` has at most one
solution in `ℚ((q))⟦z⟧`: the coefficient of `z^N` is pinned by the earlier ones because
`q^N - 1` is invertible for `N ≥ 1`.
-/

@[expose] public section

open Finset PowerSeries

namespace HJO.Uniqueness

/-! ### The paths are finite in number -/

/-- A weakly increasing height function pinned to `bN` from `aN` onwards never exceeds `bN`
on the rectangle. -/
theorem le_of_monotone_of_pinned {a b N : ℕ} {y : ℕ → ℕ}
    (hpin : ∀ r, a * N ≤ r → y r = b * N) (hmono : Monotone y) {r : ℕ} (hr : r ≤ a * N) :
    y r ≤ b * N := by
  rw [← hpin (a * N) le_rfl]
  exact hmono hr

/-- For every `N` the below-diagonal `(aN, bN)`-paths form a finite set: such a path, recorded
as a height function `ℕ → ℕ` starting at `0`, weakly increasing, weakly below the diagonal and
pinned to `bN` from `aN` onwards, is determined by its `aN + 1` values on the rectangle, each
of which lies in `{0, …, bN}`. -/
@[hjo "lem_finite_dyck"]
theorem finite_setOf_belowDiagonal (a b N : ℕ) :
    {y : ℕ → ℕ | y 0 = 0 ∧ (∀ r, a * N ≤ r → y r = b * N) ∧ Monotone y ∧
      ∀ r, a * y r ≤ b * r}.Finite := by
  refine Set.Finite.of_finite_image (f := fun y : ℕ → ℕ => fun r : Fin (a * N + 1) =>
    (⟨min (y r) (b * N), by omega⟩ : Fin (b * N + 1))) (Set.toFinite _) ?_
  rintro y ⟨-, hpiny, hmonoy, -⟩ z ⟨-, hpinz, hmonoz, -⟩ hyz
  funext r
  rcases le_or_gt r (a * N) with hr | hr
  · have hy : y r ≤ b * N := le_of_monotone_of_pinned hpiny hmonoy hr
    have hz : z r ≤ b * N := le_of_monotone_of_pinned hpinz hmonoz hr
    have h := congrFun hyz (⟨r, by omega⟩ : Fin (a * N + 1))
    simp only [Fin.mk.injEq] at h
    omega
  · rw [hpiny r hr.le, hpinz r hr.le]

/-- The same finiteness on the height-vector encoding: the below-diagonal `(aN, bN)`-paths are
a set of vectors in a finite type. -/
theorem finite_setOf_isBelowDiagonal (a b N : ℕ) :
    {y : Paths.Heights a b N | Paths.IsBelowDiagonal y}.Finite :=
  Set.toFinite _

/-! ### Uniqueness of the normalised solution -/

open Determinant

/-- The `N`-th power of the variable `q` is the Hahn-series monomial supported at `N`. -/
theorem qVar_pow (N : ℕ) : qVar ^ N = HahnSeries.single (N : ℤ) (1 : ℚ) := by
  have hq : qVar = HahnSeries.ofPowerSeries ℤ ℚ PowerSeries.X := by simp [qVar, qOfInt]
  rw [hq, ← map_pow, HahnSeries.ofPowerSeries_X_pow]

/-- For `N ≥ 1` the element `q^N - 1` of `ℚ((q))` is nonzero, hence invertible. -/
theorem qVar_pow_sub_one_ne_zero {N : ℕ} (hN : N ≠ 0) : qVar ^ N - 1 ≠ 0 := by
  rw [sub_ne_zero, qVar_pow]
  intro h
  have h0 : (0 : ℚ) = (1 : LaurentSeries ℚ).coeff 0 := by
    rw [← h, HahnSeries.coeff_single_of_ne (Ne.symm (Nat.cast_ne_zero.mpr hN))]
  rw [HahnSeries.coeff_one] at h0
  simp at h0

/-- In a solution of the common equation the constant coefficient of `𝒜(-z;q)` is `1`, because
rescaling fixes constant coefficients and the solution is normalised by `G(0;q) = 1`. -/
theorem constantCoeff_rescale_genA {a b : ℕ} {G : ZSeries} (h : IsCommonSolution a b G) :
    constantCoeff (rescale (-1) (genA a b)) = 1 := by
  have e1 : constantCoeff (rescale qVar G) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_rescale, pow_zero, one_mul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, h.2]
  have e2 : constantCoeff (rescale (-1) (genA a b)) * constantCoeff G = 1 := by
    rw [← map_mul, ← h.1, e1]
  rw [h.2, mul_one] at e2
  exact e2

/-- Over `ℚ((q))⟦z⟧` at most one series satisfies the common equation. Comparing coefficients
of `z^N` turns the equation into `(q^N - 1) g_N = ∑_{k=1}^{N} (-1)^k A_k g_{N-k}`, so with
`q^N - 1` invertible and `g_0 = 1` fixed, every coefficient is fixed by the earlier ones. -/
@[hjo "lem_unique"]
theorem eq_of_isCommonSolution {a b : ℕ} {G₁ G₂ : ZSeries} (h₁ : IsCommonSolution a b G₁)
    (h₂ : IsCommonSolution a b G₂) : G₁ = G₂ := by
  set A : ZSeries := rescale (-1) (genA a b) with hA
  have hA0 : coeff 0 A = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hA]
    exact constantCoeff_rescale_genA h₁
  have hD : rescale qVar (G₁ - G₂) = A * (G₁ - G₂) := by
    rw [map_sub, h₁.1, h₂.1, mul_sub]
  suffices hall : ∀ N, coeff N (G₁ - G₂) = 0 from
    sub_eq_zero.mp (PowerSeries.ext fun N => by rw [hall N, map_zero])
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_sub, h₁.2, h₂.2, sub_self]
    have hsum : ∑ p ∈ antidiagonal N, coeff p.1 A * coeff p.2 (G₁ - G₂)
        = coeff N (G₁ - G₂) := by
      rw [Finset.sum_eq_single_of_mem (0, N) (Finset.HasAntidiagonal.mem_antidiagonal.2 (by simp))]
      · rw [hA0, one_mul]
      · rintro ⟨c₁, c₂⟩ hc hcne
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hc
        simp only [ne_eq, Prod.mk.injEq, not_and] at hcne
        rw [ih c₂ (by omega), mul_zero]
    have key : qVar ^ N * coeff N (G₁ - G₂) = coeff N (G₁ - G₂) :=
      calc qVar ^ N * coeff N (G₁ - G₂) = coeff N (rescale qVar (G₁ - G₂)) :=
            (coeff_rescale _ _ _).symm
        _ = coeff N (A * (G₁ - G₂)) := by rw [hD]
        _ = ∑ p ∈ antidiagonal N, coeff p.1 A * coeff p.2 (G₁ - G₂) :=
            PowerSeries.coeff_mul _ _ _
        _ = coeff N (G₁ - G₂) := hsum
    have hz : (qVar ^ N - 1) * coeff N (G₁ - G₂) = 0 := by rw [sub_mul, one_mul, key, sub_self]
    exact (mul_eq_zero.1 hz).resolve_left (qVar_pow_sub_one_ne_zero hN.ne')

end HJO.Uniqueness
