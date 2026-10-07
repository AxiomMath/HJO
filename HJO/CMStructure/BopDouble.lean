/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CMStructure.BpairSymmetric
public import HJO.CMStructure.BshiftCompose
public meta import HJO.Attr

/-! # A product of two Hall--Littlewood operators

`HJO.Sym.bop_bop`: for `f ∈ Λ`, an `N ≥ 0` with `φ_{a,b}(f) = 0` whenever `b < -N`, integers
`m, n` and an `R ≥ 0` with `R ≥ n + N`,

`B_mB_nf = ∑_{r=0}^{R} ϰ_r φ_{m+r, n-r}(f)`.

## Main results

* `HJO.Sym.bop_bop_eq_bicoeff` — `B_mB_nf` is the `(m,n)` bivariate coefficient of
  `Ψ_f ∑_{r ≥ 0} ϰ_r wʳz^{-r}`.
* `HJO.Sym.bicoeff_mul_bkernelSeriesZW` — the finite expansion of a bivariate coefficient of a
  product with the kernel series.
* `HJO.Sym.bop_bop`.

## Implementation notes

**The chain of the proof is a composite of named steps.** Every
named step exists: `HJO.Sym.bop_eq_coeff_plethShiftW`, `HJO.Sym.bshiftCoeff`
(a ring map, with `HJO.Sym.coeff_bshiftCoeff`),
`HJO.Sym.bshiftCoeff_ofLaurentPoly_plethShiftW` and
`HJO.Sym.bshiftCoeff_omegaSeries`. Composing them is
`HJO.Sym.bop_bop_eq_bicoeff`, and the only step there that is not a rewrite is the passage from
"multiply the inner series by `Ω(z)`" to "multiply the bivariate series by `Ω_z`", which is
`HahnSeries.coeff_mul_single_add` at `Ω_z = C(Ω(z))`.

**Truncating the kernel series, rather than summing over an antidiagonal.** The last
paragraph reads the coefficient of `wⁿ` in `Ψ_f ∑_{r≥0} ϰ_rwʳz^{-r}` term by term and observes that
the terms with `r > n+N` vanish. Doing that literally means a sum over
`Finset.antidiagonal` re-indexed by `Finset.range (R+1)`, which is where such proofs go wrong. What
is done instead: split the kernel series as `HJO.Sym.bkernelTrunc q R` — a *finite* sum of
bimonomials, over which multiplication distributes and each coefficient is one
`HahnSeries.coeff_mul_single_add` — plus a remainder whose `w`-support lies above `R`. The remainder
contributes nothing at `wⁿ` because the two supports cannot add to `n`: `Ψ_f` has no `w`-exponent
below `-N` and the remainder none at or below `R ≥ n+N`, so a contribution would need
`n = b_1 + b_2 > -N + R ≥ n`. That is `HahnSeries.coeff_mul` used once, on an antidiagonal shown to
be empty rather than re-indexed.

**`R` is a natural number and the `R ≥ 0` is that.** The statement as usually written quantifies
over an integer `R` with `R ≥ 0` and `R ≥ n+N`; here `R : ℕ` and the second bound is
`n + N ≤ (R : ℤ)`. The two readings are the same set of `R`, and `ϰ` is indexed by `ℕ`
(`HJO.Sym.bkernel`), so the sum is `Finset.range (R+1)` with no cast in the index. `N` stays an
integer, which is the shape `HJO.Sym.exists_bpairCoeff_eq_zero` produces its witness in — the
`BpairSymmetric` file records that it chose that shape for this use.

**`0 ≤ N` is redundant and is dropped.** The proof reads `N` only through `n + N ≤ R` and through
"`φ_{a,b}(f) = 0` for `b < -N`"; nowhere is the sign of `N` used. This
generalises the statement.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*,
Section 4.
-/

@[expose] public section

namespace HJO.Sym

section Double

variable {K : Type*} [CommRing K]

/-! ### Sums of bivariate coefficients -/

/-- A bivariate coefficient of a finite sum is the sum of the bivariate coefficients. -/
theorem bicoeff_sum (a b : ℤ) {ι : Type*} (s : Finset ι) (x : ι → LaurentZW K) :
    bicoeff a b (∑ r ∈ s, x r) = ∑ r ∈ s, bicoeff a b (x r) := by
  rw [bicoeff, HahnSeries.coeff_sum, HahnSeries.coeff_sum]
  rfl

/-- **A bivariate coefficient of a product with a bimonomial**: `z^iwʲ` shifts both indices.
Two applications of `HahnSeries.coeff_mul_single_add`, one in each variable. -/
theorem bicoeff_mul_monomialZW (Y : LaurentZW K) (i j a b : ℤ) (c : Lambda K) :
    bicoeff a b (Y * monomialZW i j c) = bicoeff (a - i) (b - j) Y * c := by
  have h1 : (Y * monomialZW i j c).coeff b
      = Y.coeff (b - j) * HahnSeries.single i c := by
    have h := HahnSeries.coeff_mul_single_add (x := Y) (a := b - j) (b := j)
      (r := HahnSeries.single i c)
    rwa [sub_add_cancel] at h
  have h2 : (Y.coeff (b - j) * HahnSeries.single i c).coeff a
      = (Y.coeff (b - j)).coeff (a - i) * c := by
    have h := HahnSeries.coeff_mul_single_add (x := Y.coeff (b - j)) (a := a - i) (b := i) (r := c)
    rwa [sub_add_cancel] at h
  rw [bicoeff, h1, h2, bicoeff]

/-! ### The kernel series, truncated -/

/-- **The kernel series `∑_{r ≥ 0} ϰ_rwʳz^{-r}` truncated at `wᴿ`**, a finite sum of bimonomials.
Multiplication distributes over it, which is what replaces the antidiagonal of
`HahnSeries.coeff_mul`. -/
noncomputable def bkernelTrunc (q : K) (R : ℕ) : LaurentZW K :=
  ∑ r ∈ Finset.range (R + 1), monomialZW (-(r : ℤ)) (r : ℤ) (MvPolynomial.C (bkernel q r))

/-- **The truncation agrees with the kernel series up to `wᴿ`.** Below `w⁰` both vanish, and at `wˢ`
with `s ≤ R` the sum has the single surviving term `r = s`. -/
theorem coeff_bkernelTrunc_of_le (q : K) (R : ℕ) {b : ℤ} (hb : b ≤ (R : ℤ)) :
    (bkernelTrunc q R).coeff b = (bkernelSeriesZW q).coeff b := by
  rcases lt_or_ge b 0 with hneg | hpos
  · rw [coeff_bkernelSeriesZW_of_neg q hneg, bkernelTrunc, HahnSeries.coeff_sum]
    refine Finset.sum_eq_zero fun r _ => ?_
    exact HahnSeries.coeff_single_of_ne (by omega)
  · lift b to ℕ using hpos with s
    rw [coeff_bkernelSeriesZW, bkernelTrunc, HahnSeries.coeff_sum,
      Finset.sum_eq_single_of_mem s (Finset.mem_range.2 (by omega)) ?_]
    · exact HahnSeries.coeff_single_same _ _
    · intro r _ hne
      exact HahnSeries.coeff_single_of_ne (by omega)

/-- **The remainder of the truncation has no `w`-exponent at or below `R`.** -/
theorem support_bkernelSeriesZW_sub_bkernelTrunc (q : K) (R : ℕ) :
    (bkernelSeriesZW q - bkernelTrunc q R).support ⊆ {b : ℤ | (R : ℤ) < b} := by
  intro b hb
  by_contra hcon
  rw [HahnSeries.mem_support] at hb
  exact hb (by
    rw [HahnSeries.coeff_sub, coeff_bkernelTrunc_of_le q R (not_lt.1 hcon), sub_self])

/-! ### The expansion of a bivariate coefficient of a product with the kernel series -/

/-- **The finite expansion.** If `Y` has no `w`-exponent below `-N` then for every `R` with
`n + N ≤ R`,
`[z^mwⁿ](Y ∑_{r≥0} ϰ_rwʳz^{-r}) = ∑_{r=0}^{R} ϰ_r [z^{m+r}w^{n-r}]Y`.

The truncation `HJO.Sym.bkernelTrunc q R` contributes the displayed sum, one
`HJO.Sym.bicoeff_mul_monomialZW` per term, and the remainder contributes nothing: its `w`-support
lies above `R`, that of `Y` at or above `-N`, and `n` is not a sum of one of each, since
`b_1 + b_2 > -N + R ≥ -N + (n + N) = n`. -/
theorem bicoeff_mul_bkernelSeriesZW (q : K) {Y : LaurentZW K} {N : ℤ}
    (hY : Y.support ⊆ {b : ℤ | -N ≤ b}) (m n : ℤ) {R : ℕ} (hR : n + N ≤ (R : ℤ)) :
    bicoeff m n (Y * bkernelSeriesZW q)
      = ∑ r ∈ Finset.range (R + 1),
          MvPolynomial.C (bkernel q r) * bicoeff (m + r) (n - r) Y := by
  have hzero : (Y * (bkernelSeriesZW q - bkernelTrunc q R)).coeff n = 0 := by
    rw [HahnSeries.coeff_mul]
    refine Finset.sum_eq_zero fun ij hij => ?_
    rw [Finset.mem_antidiagonal] at hij
    have h1 : -N ≤ ij.1 := hY hij.1
    have h2 : (R : ℤ) < ij.2 := support_bkernelSeriesZW_sub_bkernelTrunc q R hij.2.1
    exact absurd hij.2.2 (by omega)
  have hrest : bicoeff m n (Y * (bkernelSeriesZW q - bkernelTrunc q R)) = 0 := by
    rw [bicoeff, hzero, HahnSeries.coeff_zero]
  have hsplit : bkernelSeriesZW q
      = bkernelTrunc q R + (bkernelSeriesZW q - bkernelTrunc q R) := by ring
  rw [hsplit, mul_add, bicoeff_add, hrest, add_zero, bkernelTrunc, Finset.mul_sum, bicoeff_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [bicoeff_mul_monomialZW, show m - -(r : ℤ) = m + (r : ℤ) by ring, mul_comm]

end Double

/-! ### The main statement -/

section Node

variable {K : Type*} [CommRing K] [Algebra ℚ K]

/-- **`B_mB_nf` is a bivariate coefficient of `Ψ_f` against the kernel series**:
`B_mB_nf = [z^mwⁿ](Ψ_f ∑_{r ≥ 0} ϰ_rwʳz^{-r})`, which is the display of the module docstring,
assembled from `HJO.Sym.bop_eq_coeff_plethShiftW`, `HJO.Sym.bshiftCoeff`,
`HJO.Sym.bshiftCoeff_ofLaurentPoly_plethShiftW` and `HJO.Sym.bshiftCoeff_omegaSeries`. -/
theorem bop_bop_eq_bicoeff (q : K) (m n : ℤ) (f : Lambda K) :
    Bop q m (Bop q n f) = bicoeff m n (bpairSeries q f * bkernelSeriesZW q) := by
  set G : LaurentSeries (Lambda K) :=
    ofLaurentPoly (Lambda K) (plethShiftW q f) * omegaSeries K with hG
  set X : LaurentZW K := bshiftCoeff q G with hX
  -- the outer operator, read on the inner coefficient
  have houter : Bop q m (G.coeff n) = (X.coeff n * omegaSeries K).coeff m := by
    rw [hX, coeff_bshiftCoeff, coeff_polyToLaurentSeries_mul_omegaSeries]
    rfl
  -- multiplying the inner series by `Ω(z)` is multiplying the bivariate series by `Ω_z`
  have homegaZ : (X * omegaZ K).coeff n = X.coeff n * omegaSeries K := by
    have h := HahnSeries.coeff_mul_single_add (x := X) (a := n) (b := (0 : ℤ))
      (r := omegaSeries K)
    rwa [add_zero, ← HahnSeries.C_apply, ← omegaZ] at h
  -- the displacement of the two factors
  have hXval : X = laurentPolyLift (ofLaurentPoly (Lambda K)) (plethShiftTwo q f)
      * (omegaW K * bkernelSeriesZW q) := by
    rw [hX, hG, map_mul, bshiftCoeff_ofLaurentPoly_plethShiftW, bshiftCoeff_omegaSeries]
  have hprod : X * omegaZ K = bpairSeries q f * bkernelSeriesZW q := by
    rw [hXval, bpairSeries]
    ring
  rw [bop_eq_coeff_plethShiftW q n f, ← hG, houter, ← homegaZ, hprod, bicoeff]

/-- **A product of two Hall--Littlewood operators.** For `f ∈ Λ`, an integer
`N` with `φ_{a,b}(f) = 0` for every `a` and every `b < -N`, integers `m, n` and a natural number `R`
with `n + N ≤ R`,

`B_mB_nf = ∑_{r=0}^{R} ϰ_r φ_{m+r, n-r}(f)`.

`HJO.Sym.bop_bop_eq_bicoeff` is the display and
`HJO.Sym.bicoeff_mul_bkernelSeriesZW` is the extraction; the hypothesis is used only to bound the
`w`-support of `Ψ_f` from below, which is what makes the sum finite. The `N ≥ 0` is not
read anywhere and is dropped. -/
@[hjo "lem_cm_bop_double"]
theorem bop_bop (q : K) (f : Lambda K) {N : ℤ}
    (hN : ∀ a b : ℤ, b < -N → bpairCoeff q a b f = 0) (m n : ℤ) {R : ℕ}
    (hR : n + N ≤ (R : ℤ)) :
    Bop q m (Bop q n f)
      = ∑ r ∈ Finset.range (R + 1),
          MvPolynomial.C (bkernel q r) * bpairCoeff q (m + r) (n - r) f := by
  have hsupp : (bpairSeries q f).support ⊆ {b : ℤ | -N ≤ b} := by
    intro b hb
    by_contra hcon
    rw [HahnSeries.mem_support] at hb
    exact hb (HahnSeries.coeff_inj.1 (funext fun a => by
      rw [HahnSeries.coeff_zero]
      exact hN a b (not_le.1 hcon)))
  rw [bop_bop_eq_bicoeff, bicoeff_mul_bkernelSeriesZW q hsupp m n hR]
  rfl

end Node

end HJO.Sym
