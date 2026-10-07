/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.ZDeltaSums
public import HJO.CarlssonMellit.ZFirClosed
public meta import HJO.Attr

/-! # The swapping coefficients telescope

One result, `HJO.Sym.one_sub_C_scalarFrac_mul_summableSum_zSwapCoeff`: for `i ≥ 1`

`∑_{r ≥ 0}f_{i,r} = (1-q)^{-1}h_i[(1-q)(X + y_k)]`,

the sum being monomialwise finite, with `f_{i,r}` the iterated swapping coefficients of
`HJO.Sym.zSwapCoeff` whose closed form is `HJO.Sym.zSwapCoeff_succ_eq_mul_completeHomog`
(`HJO.CarlssonMellit.ZFirClosed`).

## The two halves

*Monomialwise finiteness.* By the closed form, `f_{i,r} = z_r·h_{i-1}[(1-q)X_{r-1} + z_r]` is
divisible by its own letter `z_r`, so a letter-monomial is reached only by the finitely many `r`
whose letter it contains, together with `r = 0`, whose letter is the constant `y_k`. That is
`HJO.Sym.isSummableFamily_zSwapCoeff`, and it is the only reason the sum is a sum at all.

*The value.* Summing the displayed form of `HJO.Sym.zSwapCoeff_succ_eq_mul_completeHomog`
telescopes: the partial sum to `t` is `(1-q)^{-1}h_i[(1-q)X_t]`, the bottom term cancelling because
`X_{-1} = 0` kills every `h_i` with `i ≥ 1`. What remains is the stabilisation "each monomial of
`h_i[(1-q)(X+y_k)]` involves finitely many of the `x_j` and so appears in `h_i[(1-q)X_R]` for all
large `R`", and that is the one step that needs an argument of its own.

## The truncation

The stabilisation is proved with `HJO.Sym.truncSeriesHom`: killing the letters `x_t, x_{t+1}, …` is
a *ring homomorphism* of `P°_{k+1}`, because the monomials supported below `t` form a saturated
submonoid — a factorisation of one has both factors supported below `t`, and a factorisation of
anything else has a factor that is not. Composed with the two alphabet homomorphisms it makes them
agree on the variables of `Λ` (the letters above the truncation contributing nothing to the power
sums), hence, both being ring homomorphisms with the same value on the scalars, on every element of
`Λ` — so in particular on `h_i`. Reading that off at a letter-monomial supported below `t` is
`HJO.Sym.coeff_completeHomog_eq_of_low`. No topology and no limit is involved.

## Main results

* `HJO.Sym.one_sub_C_scalarFrac_mul_summableSum_zSwapCoeff`, both halves.
* `HJO.Sym.isSummableFamily_zSwapCoeff`: the monomialwise finiteness on its own.
* `HJO.Sym.one_sub_C_scalarFrac_mul_sum_range_zSwapCoeff`: the telescoping of the partial sums.
* `HJO.Sym.coeff_completeHomog_eq_of_low`: the stabilisation of the truncated alphabets against the
  full one.
* `HJO.Sym.truncSeriesHom`, `HJO.Sym.truncSeries_mul`: the truncation as a ring homomorphism.
* `HJO.Sym.isSummableFamily_zLetterSeries_pow`,
  `HJO.Sym.truncSeries_summableSum_zLetterSeries_pow`: the power sums of the whole merged alphabet
  exist as monomialwise sums, and the truncation sees them as finite ones.
* `HJO.Sym.exists_ringHom_powerSum_eq_fullTwist`: the alphabet `(1-q)(X + y_k)` exists, so the
  statement is not vacuous.

## Implementation notes

*The division by `1-q` is not performed.* `1-q` is not a unit of `P°_{k+1}` for a general base, so
the identity is stated as `(1-q)·∑_{r≥0}f_{i,r} = h_i[(1-q)(X+y_k)]`. The
derivation factors `1-q` out of the numerator rather than inverting it, so this is the same
content; `HJO.CarlssonMellit.ZFirClosed` states `HJO.Sym.zSwapCoeff_succ_eq_mul_completeHomog` the
same way.

*The notion of sum is the monomialwise one.* `HJO.Sym.summableSum` of `HJO.PointwiseSum` is
`finsum` one monomial at a time, which is what "monomialwise finite" names;
`HJO.Sym.isZDelta_summableSum` of `HJO.CarlssonMellit.ZDeltaSums` is stated with the same notion, so
the two lemmas used in the lowering step speak the same language.

*The alphabets are hypotheses, not constructions*, as in `HJO.CarlssonMellit.ZFirClosed` and
`HJO.CarlssonMellit.DeltaUpow`: three families are quantified over — `Φ t` for `(1-q)X_{t-1} + z_t`,
`Ψ t` for `(1-q)X_{t-1}`, and `Λ` for `(1-q)(X + y_k)` — each named by its values on the power sums,
with the scalars of the last two pinned to the constants of `𝕂(y₁, …, y_k)` so that the
stabilisation's appeal to `MvPolynomial.ringHom_ext` has its `C`-clause. The existence statements
are separate.

*The bound is computed, not quantified over.* At a letter-monomial `x^α` the truncation index is
taken to be `sup α.support + 1`, which serves both purposes at once: above it `α` vanishes, so the
stabilisation applies, and no `f_{i,r}` with `r` beyond it reaches `x^α`, so the monomialwise sum
is the partial sum. That is why no "for all large `R`" appears in any statement.

## References

`HJO.Sym.one_sub_C_scalarFrac_mul_summableSum_zSwapCoeff` uses `HJO.Sym.completeHomog`,
`HJO.Sym.truncatedAlphabet`, `HJO.Sym.zSwapCoeff`, `HJO.Sym.zSwapCoeff_succ_eq_mul_completeHomog`
and `HJO.Sym.completeHomog_dilate_letter`; the summation notions are `HJO.Sym.IsSummableFamily` and
`HJO.Sym.summableSum`. Used by `HJO.Dyck.isLoweringSum`. E. Carlsson and A. Mellit, *A proof of
the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018) 661--697, Section 4, where the
interchange of the sum with the plethysm is not discussed.
-/

@[expose] public section

namespace HJO.Sym

/-! ### Killing the letters from an index on -/

section Trunc

variable {R : Type*} [CommSemiring R]

open scoped Classical in
/-- **The truncation that kills the letters `x_t, x_{t+1}, …`**: the series whose coefficient at a
letter-monomial involving only the letters below `t` is that of the argument, and `0` elsewhere.
It is a ring homomorphism (`HJO.Sym.truncSeriesHom`) because the monomials supported below `t` are
a *saturated* submonoid: a factorisation of such a monomial has both factors supported below `t`,
and a factorisation of any other has at least one factor that is not.

This is what makes the truncated alphabets of `HJO.Sym.truncatedAlphabet` stabilise against the full
alphabet: below `t` the two agree, so any identity between alphabet homomorphisms that holds after
truncating holds at every coefficient supported below `t`. -/
noncomputable def truncSeries (t : ℕ) (G : MvPowerSeries ℕ R) : MvPowerSeries ℕ R := fun α =>
  if ∀ j, t ≤ j → α j = 0 then MvPowerSeries.coeff α G else 0

open scoped Classical in
theorem coeff_truncSeries (t : ℕ) (G : MvPowerSeries ℕ R) (α : ℕ →₀ ℕ) :
    MvPowerSeries.coeff α (truncSeries t G)
      = if ∀ j, t ≤ j → α j = 0 then MvPowerSeries.coeff α G else 0 :=
  MvPowerSeries.coeff_apply _ _

/-- Below the truncation the coefficients are unchanged. -/
theorem coeff_truncSeries_of_low {t : ℕ} {α : ℕ →₀ ℕ} (h : ∀ j, t ≤ j → α j = 0)
    (G : MvPowerSeries ℕ R) :
    MvPowerSeries.coeff α (truncSeries t G) = MvPowerSeries.coeff α G := by
  classical
  rw [coeff_truncSeries, ite_eq_left h]

/-- At a letter-monomial reaching the truncation the coefficient is `0`. -/
theorem coeff_truncSeries_of_not_low {t : ℕ} {α : ℕ →₀ ℕ} (h : ¬ ∀ j, t ≤ j → α j = 0)
    (G : MvPowerSeries ℕ R) : MvPowerSeries.coeff α (truncSeries t G) = 0 := by
  classical
  rw [coeff_truncSeries, ite_eq_right h]

/-- Two series with the same coefficients below the truncation have the same truncation. -/
theorem truncSeries_congr {t : ℕ} {G H : MvPowerSeries ℕ R}
    (h : ∀ α : ℕ →₀ ℕ, (∀ j, t ≤ j → α j = 0) →
      MvPowerSeries.coeff α G = MvPowerSeries.coeff α H) :
    truncSeries t G = truncSeries t H := by
  refine MvPowerSeries.ext fun α => ?_
  by_cases hα : ∀ j, t ≤ j → α j = 0
  · rw [coeff_truncSeries_of_low hα, coeff_truncSeries_of_low hα, h α hα]
  · rw [coeff_truncSeries_of_not_low hα, coeff_truncSeries_of_not_low hα]

/-- **The truncation is a ring homomorphism.** Multiplicativity is the saturation of the monomials
supported below `t`: in a factorisation `β + γ` of such a monomial both factors are such, and in a
factorisation of any other monomial at least one factor reaches the truncation, so its coefficient
there is `0`. -/
noncomputable def truncSeriesHom (R : Type*) [CommSemiring R] (t : ℕ) :
    MvPowerSeries ℕ R →+* MvPowerSeries ℕ R where
  toFun := truncSeries t
  map_one' := by
    classical
    refine MvPowerSeries.ext fun α => ?_
    by_cases hα : ∀ j, t ≤ j → α j = 0
    · rw [coeff_truncSeries_of_low hα]
    · rw [coeff_truncSeries_of_not_low hα, MvPowerSeries.coeff_one,
        ite_eq_right fun h => hα fun j _ => by rw [h, Finsupp.coe_zero, Pi.zero_apply]]
  map_mul' G H := by
    classical
    refine MvPowerSeries.ext fun α => ?_
    by_cases hα : ∀ j, t ≤ j → α j = 0
    · rw [coeff_truncSeries_of_low hα, MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
      refine Finset.sum_congr rfl fun p hp => ?_
      have hsum : p.1 + p.2 = α := by simpa using hp
      have hle : ∀ j, p.1 j + p.2 j = α j := fun j => by
        have h := congrArg (fun f : ℕ →₀ ℕ => f j) hsum
        simpa only [Finsupp.add_apply] using h
      rw [coeff_truncSeries_of_low (fun j hj => by have := hle j; have := hα j hj; omega),
        coeff_truncSeries_of_low fun j hj => by have := hle j; have := hα j hj; omega]
    · rw [coeff_truncSeries_of_not_low hα, MvPowerSeries.coeff_mul]
      obtain ⟨j, hj, hjne⟩ : ∃ j, t ≤ j ∧ α j ≠ 0 := by
        by_contra hc
        exact hα fun j hj => by_contra fun h => hc ⟨j, hj, h⟩
      refine (Finset.sum_eq_zero fun p hp => ?_).symm
      have hsum : p.1 + p.2 = α := by simpa using hp
      have hle : p.1 j + p.2 j = α j := by
        have h := congrArg (fun f : ℕ →₀ ℕ => f j) hsum
        simpa only [Finsupp.add_apply] using h
      rcases eq_or_ne (p.1 j) 0 with h1 | h1
      · rw [coeff_truncSeries_of_not_low (α := p.2)
          (fun hlow => by have := hlow j hj; omega) H, mul_zero]
      · rw [coeff_truncSeries_of_not_low (α := p.1) (fun hlow => h1 (hlow j hj)) G, zero_mul]
  map_zero' := by
    classical
    refine MvPowerSeries.ext fun α => ?_
    by_cases hα : ∀ j, t ≤ j → α j = 0
    · rw [coeff_truncSeries_of_low hα]
    · rw [coeff_truncSeries_of_not_low hα, MvPowerSeries.coeff_zero]
  map_add' G H := by
    classical
    refine MvPowerSeries.ext fun α => ?_
    by_cases hα : ∀ j, t ≤ j → α j = 0
    · rw [coeff_truncSeries_of_low hα, map_add, map_add, coeff_truncSeries_of_low hα,
        coeff_truncSeries_of_low hα]
    · rw [coeff_truncSeries_of_not_low hα, map_add, coeff_truncSeries_of_not_low hα,
        coeff_truncSeries_of_not_low hα, add_zero]

@[simp]
theorem truncSeriesHom_apply (t : ℕ) (G : MvPowerSeries ℕ R) :
    truncSeriesHom R t G = truncSeries t G :=
  rfl

/-- The truncation is multiplicative, which is the content of `HJO.Sym.truncSeriesHom`. -/
theorem truncSeries_mul (t : ℕ) (G H : MvPowerSeries ℕ R) :
    truncSeries t (G * H) = truncSeries t G * truncSeries t H :=
  map_mul (truncSeriesHom R t) G H

end Trunc

/-! ### The letters of the merged alphabet, summed -/

variable {K : Type*} [CommRing K] [IsDomain K] {k : ℕ}

/-- A power of a letter of the merged alphabet at a positive offset has no coefficient at a
letter-monomial missing that letter. -/
theorem coeff_zLetterSeries_succ_pow_eq_zero {s j : ℕ} (hj : 0 < j) {α : ℕ →₀ ℕ} (hα : α s = 0) :
    MvPowerSeries.coeff α (zLetterSeries K k (s + 1) ^ j) = 0 := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  rw [zLetterSeries_succ, pow_succ']
  exact coeff_X_mul_eq_zero s _ hα

/-- **The letters of the merged alphabet, to any positive power, are a summable family**: a
letter-monomial is reached only by the letter it contains, and by the distinguished letter, which is
a constant. -/
theorem isSummableFamily_zLetterSeries_pow {j : ℕ} (hj : 0 < j) :
    IsSummableFamily fun s => zLetterSeries K k s ^ j := by
  classical
  refine pointwiseFinite_of_forall_exists_finset fun α => ?_
  refine ⟨insert 0 (α.support.image (· + 1)), fun s hs => ?_⟩
  cases s with
  | zero => exact Finset.mem_insert_self _ _
  | succ s =>
    refine Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨s, ?_, rfl⟩)
    refine Finsupp.mem_support_iff.2 fun h => hs ?_
    change MvPowerSeries.coeff α (zLetterSeries K k (s + 1) ^ j) = 0
    exact coeff_zLetterSeries_succ_pow_eq_zero hj h

/-- **The truncation sees the full merged alphabet as a truncated one**: above the truncation the
letters contribute nothing, so the monomialwise sum of the powers of all the letters truncates to
the finite sum of the powers of the letters at offsets at most `t`. -/
theorem truncSeries_summableSum_zLetterSeries_pow (t : ℕ) {j : ℕ} (hj : 0 < j) :
    truncSeries t (summableSum fun s => zLetterSeries K k s ^ j)
      = truncSeries t (∑ s ∈ Finset.range (t + 1), zLetterSeries K k s ^ j) := by
  classical
  refine truncSeries_congr fun α hα => ?_
  have hcov : ∀ s, MvPowerSeries.coeff α (zLetterSeries K k s ^ j) ≠ 0 →
      s ∈ Finset.range (t + 1) := by
    intro s hs
    refine Finset.mem_range.2 ?_
    by_contra hst
    cases s with
    | zero => omega
    | succ s =>
      exact hs (coeff_zLetterSeries_succ_pow_eq_zero hj (hα s (by omega)))
  rw [coeff_summableSum_eq_sum hcov, map_sum]

/-! ### The swapping coefficients are a summable family -/

variable {A : Type*} [CommRing A] [Algebra ℚ A]

/-- **The swapping coefficients are monomialwise finite.** By the closed form
`f_{i,t} = z_t·h_{i-1}[(1-q)X_{t-1} + z_t]` every one of them is divisible by its own letter `z_t`,
so a letter-monomial is reached only by the finitely many `t` whose letter it contains, together
with `t = 0`, whose letter is a constant. This is the monomialwise finiteness
`HJO.Sym.one_sub_C_scalarFrac_mul_summableSum_zSwapCoeff` asserts of its sum. -/
theorem isSummableFamily_zSwapCoeff {q : K}
    {Φ : ℕ → Lambda A →+* AuxAlphabetSeriesFrac K (k + 1)}
    (hΦC : ∀ a : A, Φ 0 (MvPolynomial.C a) ∈ zSymmSubring K k)
    (hΦp : ∀ (t j : ℕ), 0 < j → Φ t (powerSum A j)
      = (1 - MvPowerSeries.C (scalarFrac K q) ^ j)
          * (∑ s ∈ Finset.range t, zLetterSeries K k s ^ j) + zLetterSeries K k t ^ j)
    (n : ℕ) : IsSummableFamily fun r => zSwapCoeff K k q (n + 1) r := by
  classical
  refine pointwiseFinite_of_forall_exists_finset fun α => ?_
  refine ⟨insert 0 (α.support.image (· + 1)), fun r hr => ?_⟩
  cases r with
  | zero => exact Finset.mem_insert_self _ _
  | succ r =>
    refine Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨r, ?_, rfl⟩)
    refine Finsupp.mem_support_iff.2 fun h => hr ?_
    change MvPowerSeries.coeff α (zSwapCoeff K k q (n + 1) (r + 1)) = 0
    rw [zSwapCoeff_succ_eq_mul_completeHomog hΦC hΦp n (r + 1), zLetterSeries_succ]
    exact coeff_X_mul_eq_zero r _ h

/-! ### The telescoping -/

/-- **The partial sums telescope.** Summing the displayed form of
`HJO.Sym.zSwapCoeff_succ_eq_mul_completeHomog` over `t = 0, …, R` cancels everything but the top
alphabet, the bottom one being the empty alphabet `X_{-1} = 0`, which kills every `h_i` with
`i ≥ 1`. This is the "the partial sum to `r = R` telescopes to
`(h_i[(1-q)X_R] - h_i[(1-q)X_{-1}])/(1-q)`", with the division written as a product. -/
theorem one_sub_C_scalarFrac_mul_sum_range_zSwapCoeff {q : K}
    {Φ Ψ : ℕ → Lambda A →+* AuxAlphabetSeriesFrac K (k + 1)}
    (hΦC : ∀ a : A, Φ 0 (MvPolynomial.C a) ∈ zSymmSubring K k)
    (hΦp : ∀ (t j : ℕ), 0 < j → Φ t (powerSum A j)
      = (1 - MvPowerSeries.C (scalarFrac K q) ^ j)
          * (∑ s ∈ Finset.range t, zLetterSeries K k s ^ j) + zLetterSeries K k t ^ j)
    (hΨp : ∀ (t j : ℕ), 0 < j → Ψ t (powerSum A j)
      = (1 - MvPowerSeries.C (scalarFrac K q) ^ j)
          * ∑ s ∈ Finset.range t, zLetterSeries K k s ^ j)
    (n R : ℕ) :
    (1 - MvPowerSeries.C (scalarFrac K q))
        * ∑ r ∈ Finset.range (R + 1), zSwapCoeff K k q (n + 1) r
      = Ψ (R + 1) (completeHomog A (n + 1)) := by
  have hzero : Ψ 0 (completeHomog A (n + 1)) = 0 := by
    refine completeHomog_eq_zero_of_powerSum_eq_zero (Ψ 0) (fun j hj => ?_) (Nat.succ_pos n)
    rw [hΨp 0 j hj, Finset.range_zero, Finset.sum_empty, mul_zero]
  rw [Finset.mul_sum,
    Finset.sum_congr rfl fun r _ =>
      one_sub_C_scalarFrac_mul_zSwapCoeff hΦC hΦp hΨp n r,
    Finset.sum_range_sub (fun t => Ψ t (completeHomog A (n + 1))) (R + 1), hzero, sub_zero]

/-! ### The full alphabet stabilises the truncated ones -/

omit [Algebra ℚ A] in
/-- **The truncated alphabets stabilise against the full one.** Truncating at `t` makes the alphabet
`(1-q)X_t` and the alphabet `(1-q)(X + y_k)` agree on the variables of `Λ`, hence — both being ring
homomorphisms with the same value on the scalars — on every element of `Λ`. So at a
letter-monomial involving only the letters below `t` the two agree outright. This is the claim
"each monomial of `h_i[(1-q)(X+y_k)]` involves finitely many of the `x_j` and so appears in
`h_i[(1-q)X_R]` for all large `R`". -/
theorem coeff_completeHomog_eq_of_low {q : K} {base : A →+* AuxFrac K k}
    {Ψ : ℕ → Lambda A →+* AuxAlphabetSeriesFrac K (k + 1)}
    {Λ : Lambda A →+* AuxAlphabetSeriesFrac K (k + 1)}
    (hΨC : ∀ (t : ℕ) (a : A), Ψ t (MvPolynomial.C a)
      = MvPowerSeries.C (auxFracCastSucc K k (base a)))
    (hΨp : ∀ (t j : ℕ), 0 < j → Ψ t (powerSum A j)
      = (1 - MvPowerSeries.C (scalarFrac K q) ^ j)
          * ∑ s ∈ Finset.range t, zLetterSeries K k s ^ j)
    (hΛC : ∀ a : A, Λ (MvPolynomial.C a)
      = MvPowerSeries.C (auxFracCastSucc K k (base a)))
    (hΛp : ∀ j : ℕ, 0 < j → Λ (powerSum A j)
      = (1 - MvPowerSeries.C (scalarFrac K q) ^ j)
          * summableSum fun s => zLetterSeries K k s ^ j)
    (p : Lambda A) (t : ℕ) {α : ℕ →₀ ℕ} (hα : ∀ j, t ≤ j → α j = 0) :
    MvPowerSeries.coeff α (Λ p) = MvPowerSeries.coeff α (Ψ (t + 1) p) := by
  have hcomp : (truncSeriesHom (AuxFrac K (k + 1)) t).comp Λ
      = (truncSeriesHom (AuxFrac K (k + 1)) t).comp (Ψ (t + 1)) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) fun i => ?_
    · simp only [RingHom.comp_apply, truncSeriesHom_apply, hΛC a, hΨC (t + 1) a]
    · simp only [RingHom.comp_apply, truncSeriesHom_apply]
      rw [← CopPower.powerSum_succ, hΛp (i + 1) (Nat.succ_pos i),
        hΨp (t + 1) (i + 1) (Nat.succ_pos i), truncSeries_mul, truncSeries_mul,
        truncSeries_summableSum_zLetterSeries_pow t (Nat.succ_pos i)]
  have h := congrArg (fun f : Lambda A →+* AuxAlphabetSeriesFrac K (k + 1) => f p) hcomp
  simp only [RingHom.comp_apply, truncSeriesHom_apply] at h
  rw [← coeff_truncSeries_of_low hα (Λ p), ← coeff_truncSeries_of_low hα (Ψ (t + 1) p), h]

/-! ### The swapping coefficients telescope -/

/-- **The swapping coefficients telescope.** For every `i = n + 1 ≥ 1`

`(1-q)·∑_{r ≥ 0}f_{i,r} = h_i[(1-q)(X + y_k)]`,

the sum being monomialwise finite. This is
`HJO.Sym.one_sub_C_scalarFrac_mul_summableSum_zSwapCoeff`, with the closed form
`∑_{r≥0}f_{i,r} = (1-q)^{-1}h_i[(1-q)(X+y_k)]` written as a product: `1-q` is not a unit of
`P°_{k+1}` for a general base, and the derivation factors it out of the numerator
rather than inverting it.

Monomialwise finiteness is `HJO.Sym.isSummableFamily_zSwapCoeff`: by the closed form each `f_{i,r}`
is divisible by its own letter `z_r`. The identity is checked one letter-monomial at a time, and at
each of them the sum is a partial sum: taking `t` above every letter the monomial contains, the
terms beyond `t` do not reach it, the partial sum to `t` telescopes to `h_i[(1-q)X_t]`
(`HJO.Sym.one_sub_C_scalarFrac_mul_sum_range_zSwapCoeff`), and `h_i[(1-q)X_t]` has the same
coefficient there as `h_i[(1-q)(X+y_k)]` (`HJO.Sym.coeff_completeHomog_eq_of_low`). -/
@[hjo "lem_cm_fir_telescope"]
theorem one_sub_C_scalarFrac_mul_summableSum_zSwapCoeff {q : K} {base : A →+* AuxFrac K k}
    {Φ Ψ : ℕ → Lambda A →+* AuxAlphabetSeriesFrac K (k + 1)}
    {Λ : Lambda A →+* AuxAlphabetSeriesFrac K (k + 1)}
    (hΦC : ∀ a : A, Φ 0 (MvPolynomial.C a) ∈ zSymmSubring K k)
    (hΦp : ∀ (t j : ℕ), 0 < j → Φ t (powerSum A j)
      = (1 - MvPowerSeries.C (scalarFrac K q) ^ j)
          * (∑ s ∈ Finset.range t, zLetterSeries K k s ^ j) + zLetterSeries K k t ^ j)
    (hΨC : ∀ (t : ℕ) (a : A), Ψ t (MvPolynomial.C a)
      = MvPowerSeries.C (auxFracCastSucc K k (base a)))
    (hΨp : ∀ (t j : ℕ), 0 < j → Ψ t (powerSum A j)
      = (1 - MvPowerSeries.C (scalarFrac K q) ^ j)
          * ∑ s ∈ Finset.range t, zLetterSeries K k s ^ j)
    (hΛC : ∀ a : A, Λ (MvPolynomial.C a) = MvPowerSeries.C (auxFracCastSucc K k (base a)))
    (hΛp : ∀ j : ℕ, 0 < j → Λ (powerSum A j)
      = (1 - MvPowerSeries.C (scalarFrac K q) ^ j)
          * summableSum fun s => zLetterSeries K k s ^ j)
    (n : ℕ) :
    (IsSummableFamily fun r => zSwapCoeff K k q (n + 1) r) ∧
      (1 - MvPowerSeries.C (scalarFrac K q))
          * summableSum (fun r => zSwapCoeff K k q (n + 1) r)
        = Λ (completeHomog A (n + 1)) := by
  classical
  refine ⟨isSummableFamily_zSwapCoeff hΦC hΦp n, MvPowerSeries.ext fun α => ?_⟩
  set t : ℕ := α.support.sup id + 1 with htdef
  have hα : ∀ j, t ≤ j → α j = 0 := by
    intro j hj
    by_contra h
    have hle : j ≤ α.support.sup id := Finset.le_sup (f := id) (Finsupp.mem_support_iff.2 h)
    omega
  have hcov : ∀ r, MvPowerSeries.coeff α (zSwapCoeff K k q (n + 1) r) ≠ 0 →
      r ∈ Finset.range (t + 1) := by
    intro r hr
    refine Finset.mem_range.2 ?_
    by_contra hrt
    cases r with
    | zero => omega
    | succ r =>
      refine hr ?_
      rw [zSwapCoeff_succ_eq_mul_completeHomog hΦC hΦp n (r + 1), zLetterSeries_succ]
      exact coeff_X_mul_eq_zero r _ (hα r (by omega))
  have hC : (1 - MvPowerSeries.C (scalarFrac K q) : AuxAlphabetSeriesFrac K (k + 1))
      = MvPowerSeries.C (1 - scalarFrac K q) := by rw [map_sub, map_one]
  have hpart : MvPowerSeries.coeff α (summableSum fun r => zSwapCoeff K k q (n + 1) r)
      = MvPowerSeries.coeff α (∑ r ∈ Finset.range (t + 1), zSwapCoeff K k q (n + 1) r) := by
    rw [coeff_summableSum_eq_sum hcov, map_sum]
  rw [hC, MvPowerSeries.coeff_C_mul, hpart, ← MvPowerSeries.coeff_C_mul, ← hC,
    one_sub_C_scalarFrac_mul_sum_range_zSwapCoeff hΦC hΦp hΨp n t,
    coeff_completeHomog_eq_of_low hΨC hΨp hΛC hΛp (completeHomog A (n + 1)) t hα]

/-! ### The full twisted alphabet exists -/

omit [Algebra ℚ A] in
/-- **The alphabet `(1-q)(X + y_k)` exists.** The power sums of the whole merged alphabet are
monomialwise finite sums by `HJO.Sym.isSummableFamily_zLetterSeries_pow`, so the prescription makes
sense, and a homomorphism out of `Λ` is determined by prescribing the variables. -/
theorem exists_ringHom_powerSum_eq_fullTwist (q : K) (base : A →+* AuxFrac K k) :
    ∃ Λ : Lambda A →+* AuxAlphabetSeriesFrac K (k + 1),
      (∀ a : A, Λ (MvPolynomial.C a) = MvPowerSeries.C (auxFracCastSucc K k (base a))) ∧
        ∀ j : ℕ, 0 < j → Λ (powerSum A j)
          = (1 - MvPowerSeries.C (scalarFrac K q) ^ j)
            * summableSum fun s => zLetterSeries K k s ^ j := by
  refine ⟨MvPolynomial.eval₂Hom
      (((MvPowerSeries.C : AuxFrac K (k + 1) →+* AuxAlphabetSeriesFrac K (k + 1)).comp
        (auxFracCastSucc K k)).comp base)
      (fun i => (1 - MvPowerSeries.C (scalarFrac K q) ^ (i + 1))
        * summableSum fun s => zLetterSeries K k s ^ (i + 1)),
    fun a => MvPolynomial.eval₂Hom_C _ _ a, fun j hj => ?_⟩
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rw [CopPower.powerSum_succ, MvPolynomial.eval₂Hom_X']

end HJO.Sym
