/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import HJO.CMStructure.BopTwoVariable
public import HJO.CMStructure.BshiftEsymm
public meta import HJO.Attr

/-! # Composing the two displacements, and the kernel the composition produces

Inside the two-variable ring `𝒵 = Λ[[z]][z⁻¹][[w]][w⁻¹]` of `HJO.Sym.LaurentZW` the
Haglund--Morse--Zabrocki block applies the displacement `β` of the *inner* variable to every
coefficient of a series in the *outer* variable. That map is `HJO.Sym.bshiftCoeff`, written
`β̂`, and this file records the two identities the block needs about it.

The first is that `β̂` composed with the displacement `β'` of the outer variable is the double
displacement `β₂`: each displacement contributes `(1 - qᵏ)` times the inverse `k`-th power of its
own variable to `p_k`, and the two contributions do not interfere.

The second is that `β̂` does not fix the alternating elementary series `Ω(w)` but multiplies it by
an explicit kernel, `∑_{r ≥ 0} ϰ_r wʳ z^{-r}` with `ϰ` the kernel coefficients
`HJO.Sym.bkernel`. This is the identity that makes the two-variable generating function
`HJO.Sym.bpairSeries` symmetric in the two variables, and it is exactly the displacement of an
elementary symmetric function (`HJO.Sym.plethHallLittlewood_elemSymm`) read off coefficient by
coefficient in `w`.

## Main definitions

* `HJO.Sym.bkernelSeriesZW`: the kernel series `∑_{r ≥ 0} ϰ_r wʳ z^{-r}`, an element of `𝒵`.

## Main results

* `HJO.Sym.bshiftCoeff_ofLaurentPoly_plethShiftW`, that `β̂(β'(f)) = β₂(f)` for every `f ∈ Λ`.
* `HJO.Sym.bshiftCoeff_omegaSeries`, that
  `β̂(Ω(w)) = Ω(w) ∑_{r ≥ 0} ϰ_r wʳ z^{-r}`.

## Implementation notes

**Where the inclusions go.** `β̂` has domain `Λ[[w]][w⁻¹]` while `β'` of `HJO.Sym.plethShiftW`
lands in the Laurent *polynomials* `Λ[w, w⁻¹]`, so the composite reads
`β̂ (HJO.Sym.ofLaurentPoly _ (β' f))`; and `β₂` of `HJO.Sym.plethShiftTwo` lands in
`Λ[z, z⁻¹][w, w⁻¹]`, so it enters `𝒵` through `HJO.Sym.laurentPolyLift` taken with
`HJO.Sym.ofLaurentPoly` as its coefficient map. Both inclusions are the ones
`HJO.Sym.bpairSeries` already uses, and they are what the remark that `𝒵` contains
`Λ[[w]][w⁻¹]` and `Λ[z, z⁻¹, w, w⁻¹]` means. Since both sides are ring homomorphisms in `f`, the
identity is checked on the generators of `Λ` by `MvPolynomial.ringHom_ext`, as in
`HJO.Sym.ofLaurentPoly_plethShiftW`.

**`Ω(w)` wears two hats.** As the *argument* of `β̂` it is an element of `Λ[[w]][w⁻¹]`, namely
`HJO.Sym.omegaSeries`; as a *factor* on the right-hand side it is the element `HJO.Sym.omegaW` of
`𝒵`, which is `omegaSeries` with each coefficient viewed as a constant Laurent series in `z`. The
two are the same series read in the two rings, and the statement below names each in its own place.

**The kernel series is built from a power series in `w`.** Its coefficient at `wʳ` is
`ϰ_r z^{-r}` for `r ≥ 0` and `0` below, so its support lies in `Set.Ici 0`. Rather than exhibit
that partially well-ordered support by hand, `HJO.Sym.bkernelSeriesZW` is the image of an honest
power series under `HahnSeries.ofPowerSeries`, which supplies the support condition and, being a
ring homomorphism, also turns the product `Ω(w) ∑_r ϰ_r wʳ z^{-r}` into a single power-series
product whose coefficients are finite sums over `Finset.antidiagonal`.

**Truncated subtraction.** The sign bookkeeping `(-1)^m (-1)^r = (-1)^{m-r}` is done through
`m + r = 2r + (m - r)`, valid in `ℕ` for `r ≤ m`, which is the range of the sum; and the
reindexing `r ↦ m - r` is `Finset.sum_range_reflect`, whose two applications cancel because
`m - (m - r) = r` for `r ≤ m`. No claim below is stated outside that range, so no truncation is
silently used.

## References

The lemmas `HJO.Sym.bshiftCoeff_ofLaurentPoly_plethShiftW` and `HJO.Sym.bshiftCoeff_omegaSeries`, on
the Haglund--Morse--Zabrocki relations, using the definitions `HJO.Sym.plethHallLittlewood`,
`HJO.Sym.plethShiftW`, `HJO.Sym.bshiftCoeff`, `HJO.Sym.plethShiftTwo`, `HJO.Sym.bkernel`,
`HJO.Sym.elemSymmSeries` and `HJO.Sym.LaurentZW`.
-/

@[expose] public section

namespace HJO.Sym

/-! ### Coefficientwise maps of Laurent series -/

section Helpers

variable {R S : Type*} [CommRing R] [CommRing S]

/-- A coefficientwise ring homomorphism sends a monomial to the monomial of the same exponent with
the coefficient moved along. -/
private theorem mapLaurentSeries_single (φ : R →+* S) (b : ℤ) (c : R) :
    mapLaurentSeries φ (HahnSeries.single b c) = HahnSeries.single b (φ c) := by
  ext n
  rw [coeff_mapLaurentSeries]
  rcases eq_or_ne n b with rfl | h
  · rw [HahnSeries.coeff_single_same, HahnSeries.coeff_single_same]
  · rw [HahnSeries.coeff_single_of_ne h, HahnSeries.coeff_single_of_ne h, map_zero]

/-- A power series read as a two-sided Laurent series has no negative-exponent coefficient. -/
private theorem coeff_ofPowerSeries_of_neg (x : PowerSeries R) {n : ℤ} (hn : n < 0) :
    (HahnSeries.ofPowerSeries ℤ R x).coeff n = 0 := by
  rw [HahnSeries.ofPowerSeries_apply]
  refine HahnSeries.embDomain_of_notMem_range ?_
  rintro ⟨m, hm⟩
  simp only [Nat.castOrderEmbedding_apply] at hm
  omega

/-- Moving the coefficients of a power series along `φ` commutes with reading it as a two-sided
Laurent series. -/
private theorem mapLaurentSeries_ofPowerSeries (φ : R →+* S) (x : PowerSeries R) :
    mapLaurentSeries φ (HahnSeries.ofPowerSeries ℤ R x)
      = HahnSeries.ofPowerSeries ℤ S (PowerSeries.map φ x) := by
  ext n
  rw [coeff_mapLaurentSeries]
  rcases lt_or_ge n 0 with hn | hn
  · rw [coeff_ofPowerSeries_of_neg _ hn, coeff_ofPowerSeries_of_neg _ hn, map_zero]
  · lift n to ℕ using hn with m
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff,
      PowerSeries.coeff_map]

end Helpers

/-! ### Composing the two displacements -/

section Compose

variable {K : Type*} [CommRing K]

/-- `β̂` on a monomial of `Λ[[w]][w⁻¹]`: the exponent of `w` is untouched and the coefficient is
displaced. -/
private theorem bshiftCoeff_single (q : K) (b : ℤ) (c : Lambda K) :
    bshiftCoeff q (HahnSeries.single b c)
      = HahnSeries.single b (polyToLaurentSeries (Lambda K) (plethHallLittlewood q c)) := by
  rw [bshiftCoeff, mapLaurentSeries_single, RingHom.comp_apply, RingHom.coe_coe]

/-- **Composing the two displacements.** For every `f ∈ Λ`,
`β̂(β'(f)) = β₂(f)`.

The displacement `β'` of `HJO.Sym.plethShiftW` lands in the Laurent polynomials `Λ[w, w⁻¹]` and is
included into the Laurent series `Λ[[w]][w⁻¹]`, the domain of `β̂`, by `HJO.Sym.ofLaurentPoly`; the
double displacement `β₂` of `HJO.Sym.plethShiftTwo` lands in `Λ[z, z⁻¹][w, w⁻¹]` and is included
into `𝒵` coefficientwise, by `HJO.Sym.laurentPolyLift` taken with `HJO.Sym.ofLaurentPoly` as its
coefficient map — the same inclusion `HJO.Sym.bpairSeries` uses for `β₂`.

Both sides are ring homomorphisms in `f`, so the identity is checked on the generators of `Λ`:
`β'(p_k) = p_k + (1 - qᵏ)w⁻ᵏ` has the coefficient `p_k` at `w⁰` and the scalar `1 - qᵏ` at `w⁻ᵏ`,
and `β̂` displaces the first into `p_k + (1 - qᵏ)z⁻ᵏ` while fixing the second, which is
`β₂(p_k)`. -/
@[hjo "lem_cm_bshift_double_compose"]
theorem bshiftCoeff_ofLaurentPoly_plethShiftW (q : K) (f : Lambda K) :
    bshiftCoeff q (ofLaurentPoly (Lambda K) (plethShiftW q f))
      = laurentPolyLift (ofLaurentPoly (Lambda K)) (plethShiftTwo q f) := by
  have h : ((bshiftCoeff q).comp (ofLaurentPoly (Lambda K))).comp
        (plethShiftW q : Lambda K →+* LaurentPolynomial (Lambda K))
      = (laurentPolyLift (ofLaurentPoly (Lambda K))).comp
        (plethShiftTwo q : Lambda K →+* LaurentPolynomial (LaurentPolynomial (Lambda K))) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
    · simp only [RingHom.comp_apply, RingHom.coe_coe, plethShiftW_C, plethShiftTwo_C,
        ofLaurentPoly_C, laurentPolyLift_C, bshiftCoeff_C_C]
    · have hl : bshiftCoeff q (ofLaurentPoly (Lambda K) (plethShiftW q (MvPolynomial.X i)))
          = HahnSeries.single 0 (HahnSeries.single 0 (powerSum K (i + 1)))
            + HahnSeries.single 0
                (HahnSeries.single (-((i : ℤ) + 1)) (MvPolynomial.C (1 - q ^ (i + 1))))
            + HahnSeries.single (-((i : ℤ) + 1))
                (HahnSeries.single 0 (MvPolynomial.C (1 - q ^ (i + 1)) : Lambda K)) := by
        simp only [plethShiftW_X, map_add, map_mul, ofLaurentPoly_C, ofLaurentPoly_T,
          HahnSeries.C_apply, HahnSeries.single_mul_single, zero_add, mul_one, bshiftCoeff_single,
          plethHallLittlewood_powerSum q (k := i + 1) (by omega), plethHallLittlewood_C,
          polyToLaurentSeries_C, Polynomial.C_mul_X_pow_eq_monomial, polyToLaurentSeries_monomial,
          HahnSeries.single_add, Nat.cast_add, Nat.cast_one]
      have hr : laurentPolyLift (ofLaurentPoly (Lambda K)) (plethShiftTwo q (MvPolynomial.X i))
          = HahnSeries.single 0 (HahnSeries.single 0 (powerSum K (i + 1)))
            + (HahnSeries.single 0
                (HahnSeries.single (-((i : ℤ) + 1)) (MvPolynomial.C (1 - q ^ (i + 1))))
              + HahnSeries.single (-((i : ℤ) + 1))
                (HahnSeries.single 0 (MvPolynomial.C (1 - q ^ (i + 1)) : Lambda K))) := by
        simp only [plethShiftTwo_X, map_add, map_mul, mul_add, laurentPolyLift_C,
          laurentPolyLift_T, ofLaurentPoly_C, ofLaurentPoly_T, HahnSeries.C_apply,
          HahnSeries.single_mul_single, zero_add, mul_one]
      simp only [RingHom.comp_apply, RingHom.coe_coe]
      rw [hl, hr, add_assoc]
  exact congrArg (fun g : Lambda K →+* LaurentZW K => g f) h

end Compose

/-! ### The kernel produced by the displacement -/

section Kernel

variable {K : Type*} [CommRing K]

/-- **The kernel series** `∑_{r ≥ 0} ϰ_r wʳ z^{-r}`, an element of `𝒵`: its coefficient at `wʳ` is
the monomial `ϰ_r z^{-r}` for `r ≥ 0` and `0` for `r < 0`. This is the factor by which the
coefficientwise displacement `β̂` multiplies the alternating elementary series, and the `ϰ_r` are
the kernel coefficients `HJO.Sym.bkernel` of `HJO.Sym.bkernel`.

Because only non-negative powers of `w` occur, the series is the image of an honest power series in
`w` under `HahnSeries.ofPowerSeries`, which is where its partially well-ordered support comes
from. -/
noncomputable def bkernelSeriesZW (q : K) : LaurentZW K :=
  HahnSeries.ofPowerSeries ℤ (LaurentSeries (Lambda K))
    (PowerSeries.mk fun r => HahnSeries.single (-(r : ℤ)) (MvPolynomial.C (bkernel q r)))

/-- The coefficient of `wʳ` of the kernel series, for `r ≥ 0`, is the monomial `ϰ_r z^{-r}`. -/
theorem coeff_bkernelSeriesZW (q : K) (r : ℕ) :
    (bkernelSeriesZW q).coeff (r : ℤ)
      = HahnSeries.single (-(r : ℤ)) (MvPolynomial.C (bkernel q r)) := by
  rw [bkernelSeriesZW, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_mk]

/-- The kernel series has no negative power of `w`. -/
theorem coeff_bkernelSeriesZW_of_neg (q : K) {n : ℤ} (hn : n < 0) :
    (bkernelSeriesZW q).coeff n = 0 :=
  coeff_ofPowerSeries_of_neg _ hn

/-- The bivariate coefficients of the kernel series: `ϰ_r` at `z^{-r}wʳ` for `r ≥ 0` and `0`
elsewhere, which is the display `∑_{r ≥ 0} ϰ_r wʳ z^{-r}` read off entry by entry. -/
theorem bicoeff_bkernelSeriesZW (q : K) (a : ℤ) (r : ℕ) :
    bicoeff a (r : ℤ) (bkernelSeriesZW q)
      = if a = -(r : ℤ) then MvPolynomial.C (bkernel q r) else 0 := by
  rw [bicoeff, coeff_bkernelSeriesZW]
  split_ifs with h
  · rw [h, HahnSeries.coeff_single_same]
  · rw [HahnSeries.coeff_single_of_ne h]

variable [Algebra ℚ K]

/-- **The kernel produced by the displacement.**
`β̂(Ω(w)) = Ω(w) ∑_{r ≥ 0} ϰ_r wʳ z^{-r}`.

On the left `Ω(w)` is the element `HJO.Sym.omegaSeries` of `Λ[[w]][w⁻¹]`, the domain of `β̂`; on the
right it is the element `HJO.Sym.omegaW` of `𝒵`, the same series with each coefficient read as a
constant Laurent series in the inner variable `z`.

Both sides vanish at every negative power of `w`, since `Ω` has no such term and `β̂` does not move
the exponent of `w`. At `wⁿ` with `n ≥ 0` the left-hand side is `β((-1)ⁿeₙ)`, which
`HJO.Sym.plethHallLittlewood_elemSymm` expands as `∑_{r=0}^{n} ϰ_r z^{-r}(-1)^{n-r}e_{n-r}`, and
that is the coefficient of `wⁿ` in the product on the right. -/
@[hjo "lem_cm_bshift_omega_kernel"]
theorem bshiftCoeff_omegaSeries (q : K) :
    bshiftCoeff q (omegaSeries K) = omegaW K * bkernelSeriesZW q := by
  set P : PowerSeries (LaurentSeries (Lambda K)) :=
    PowerSeries.map (HahnSeries.C : Lambda K →+* LaurentSeries (Lambda K)) (elemSymmSeries K)
    with hP
  set Q : PowerSeries (LaurentSeries (Lambda K)) :=
    PowerSeries.mk fun r => HahnSeries.single (-(r : ℤ)) (MvPolynomial.C (bkernel q r)) with hQ
  have homega : omegaW K = HahnSeries.ofPowerSeries ℤ (LaurentSeries (Lambda K)) P := by
    rw [hP, omegaW, omegaSeries, mapLaurentSeries_ofPowerSeries]
  have hker : bkernelSeriesZW q = HahnSeries.ofPowerSeries ℤ (LaurentSeries (Lambda K)) Q := by
    rw [hQ, bkernelSeriesZW]
  rw [homega, hker, ← map_mul]
  refine HahnSeries.coeff_inj.1 (funext fun n => ?_)
  rcases lt_or_ge n 0 with hn | hn
  · rw [coeff_bshiftCoeff, coeff_omegaSeries, elemSymmAlt_of_neg hn, map_zero, map_zero,
      coeff_ofPowerSeries_of_neg _ hn]
  · lift n to ℕ using hn with m
    have hL : polyToLaurentSeries (Lambda K)
          (plethHallLittlewood q ((-1 : Lambda K) ^ m * elemSymm K m))
        = ∑ r ∈ Finset.range (m + 1), HahnSeries.single (-(r : ℤ))
            ((-1 : Lambda K) ^ (m - r) * elemSymm K (m - r) * MvPolynomial.C (bkernel q r)) := by
      rw [map_mul (plethHallLittlewood q), map_pow (plethHallLittlewood q), map_neg, map_one,
        plethHallLittlewood_elemSymm, map_mul (polyToLaurentSeries (Lambda K)),
        map_pow (polyToLaurentSeries (Lambda K)), map_neg, map_one,
        map_sum (polyToLaurentSeries (Lambda K)), Finset.mul_sum]
      refine Finset.sum_congr rfl fun r hr => ?_
      rw [Finset.mem_range, Nat.lt_succ_iff] at hr
      have hsign : (-1 : Lambda K) ^ m * (-1) ^ r = (-1) ^ (m - r) := by
        rw [← pow_add, show m + r = 2 * r + (m - r) by omega, pow_add, pow_mul, neg_one_sq,
          one_pow, one_mul]
      have hval : (-1 : Lambda K) ^ m *
            ((-1) ^ r * MvPolynomial.C (bkernel q r) * elemSymm K (m - r))
          = (-1 : Lambda K) ^ (m - r) * elemSymm K (m - r) * MvPolynomial.C (bkernel q r) := by
        linear_combination (MvPolynomial.C (bkernel q r) * elemSymm K (m - r)) * hsign
      rw [Polynomial.C_mul_X_pow_eq_monomial, polyToLaurentSeries_monomial,
        show ((-1 : LaurentSeries (Lambda K)) ^ m) = HahnSeries.C ((-1 : Lambda K) ^ m) by
          rw [map_pow, map_neg, map_one],
        HahnSeries.C_apply, HahnSeries.single_mul_single, zero_add, hval]
    have hreflect : ∀ F : ℕ → LaurentSeries (Lambda K),
        ∑ k ∈ Finset.range (m + 1), F (m - k) = ∑ k ∈ Finset.range (m + 1), F k := by
      intro F
      rw [← Finset.sum_range_reflect F (m + 1)]
      exact Finset.sum_congr rfl fun k _ => congrArg F (by omega)
    rw [coeff_bshiftCoeff, coeff_omegaSeries, elemSymmAlt_natCast,
      HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun a b => PowerSeries.coeff a P * PowerSeries.coeff b Q) m, hL]
    refine Eq.trans ?_
      (hreflect fun k => PowerSeries.coeff k P * PowerSeries.coeff (m - k) Q)
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range, Nat.lt_succ_iff] at hk
    rw [show m - (m - k) = k by omega, hP, hQ, PowerSeries.coeff_map, coeff_elemSymmSeries,
      PowerSeries.coeff_mk, HahnSeries.C_apply, HahnSeries.single_mul_single, zero_add]

end Kernel

end HJO.Sym
