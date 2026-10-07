/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.SignSumBlocks
public import HJO.CarlssonMellit.CharSeries
public meta import HJO.Attr

/-! # A weighted sum of super fundamentals is a sum over the super alphabet

The super expansion of the characteristic series is reached in two steps: the fundamental
quasisymmetric expansion `χ(R,n) = ∑_σ q^{inv(R,σ)}F_{n,Des(σ⁻¹)}` of
`HJO.Dyck.charSeries_eq_sum_gessel` becomes `∑_σ q^{inv(R,σ)}F̃_{n,Des(σ⁻¹)}` under the superization
formula, and that combination is then a single sum over `𝒜^n`. This file proves the second step,
which is independent of the superization formula and of every plethysm:

`∑_σ q^{inv(R,σ)}F̃_{n,Des(σ⁻¹)} = ∑_{v ∈ 𝒜^n}q^{inv^±(R,v)}z_v`.

Both halves are already available. `HJO.Sym.sum_superMonomial_superStdPerm` says each
`F̃_{n,Des(σ⁻¹)}` is the standardisation fibre of `σ`, so the fibres of `Std^±` regroup the
combination into one sum over all super words; and `HJO.Dyck.superInvSet_eq_invSet_superStd` says
the exponent of `q` carried by a word of that fibre is `inv^±(R,v)`, so the weight that was constant
on the fibre is the word's own super inversion number.

## Main results

* `HJO.Dyck.superInvNumber_eq_invNumber_of_superStdPerm_eq`: the weight is constant on a
  standardisation fibre, and equal there to the plain inversion number of the permutation.
* `HJO.Dyck.sum_pow_invNumber_smul_superFundamental`: the identity above.

## Implementation notes

*The sum over `𝒜^n` is `HJO.Sym.summableSum`, as in `HJO.CarlssonMellit.SignSumBlocks`, and the
identity is proved one coefficient at a time.* At a monomial `x^d` every super word that
contributes has its absolute values in the support of `d`, by
`HJO.Dyck.mem_piFinset_letterFinset_of_coeff_superMonomial_ne_zero`, so both sides are finite sums
over the same finite set of words; the regrouping is then `Finset.sum_fiberwise_of_maps_to` along
`HJO.Sym.superStdPerm`, and `HJO.Sym.sum_superMonomial_superStdPerm` — which is stated after
truncation to an arbitrary finite set of letters, exactly for this — evaluates each fibre.

*The hypothesis that the pairs of `R` increase is genuinely used*, by
`HJO.Dyck.superInvSet_eq_invSet_superStd`: without it the super inversion number of a word is not
the plain inversion number of its standardisation, the tie-breaks being chosen for increasing pairs.
The hypothesis `n ≥ 1` is not needed — at `n = 0` both sides are `1`.

## References

The lemmas `HJO.Sym.sum_superMonomial_superStdPerm`, `HJO.Dyck.superInvSet_eq_invSet_superStd` and
`HJO.ParkingFunctions.realisation_thetaLambda_of_eq_charSeries`; and E. Carlsson and A. Mellit, *A
proof of the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018) 661--697, Section 3: the
standardisation identities `Inv(π, w) = Inv(π, Std(w))` and
`∑_{Std(w) = σ} x_w = Q_{n,Des(σ⁻¹)}`, and their extension to the super alphabet.
-/

@[expose] public section

open Finset

namespace HJO.Dyck

open HJO.Sym

variable {n : ℕ} {K : Type*} [CommRing K]

/-- **The super inversion number is the plain inversion number of the standardisation**, read on the
permutation the word standardises to. This is `HJO.Dyck.superInvSet_eq_invSet_superStd` with the
standardisation replaced by the permutation it is, so that the weight is visibly constant on a fibre
of `HJO.Sym.superStdPerm`. -/
theorem superInvNumber_eq_invNumber_of_superStdPerm_eq {R : Finset (Fin n × Fin n)}
    (hR : ∀ p ∈ R, p.1 < p.2) {v : Fin n → SuperLetter} {σ : Equiv.Perm (Fin n)}
    (hv : superStdPerm v = σ) : superInvNumber R v = invNumber R fun i => σ i := by
  rw [superInvNumber, superInvSet_eq_invSet_superStd R hR v, invNumber]
  refine congrArg Finset.card (Finset.filter_congr fun p _ => ?_)
  rw [← hv, ← superStdPerm_apply v p.1, ← superStdPerm_apply v p.2]
  exact (Fin.lt_def (a := superStdPerm v p.2) (b := superStdPerm v p.1)).symm

/-- A super word whose monomial, restricted to admissible words, reaches `x^d` has every absolute
value in the support of `d`: the admissibility condition only ever replaces the monomial by `0`.
This is the finite index set both readings of the super fundamental's coefficient are taken over. -/
theorem mem_piFinset_letterFinset_of_coeff_ite_ne_zero (q : K) (S : Finset ℕ) {d : ℕ →₀ ℕ}
    {v : Fin n → SuperLetter}
    (hv : MvPowerSeries.coeff d
      (if IsSuperAscendingWord n S v then superMonomial K q v else 0) ≠ 0) :
    v ∈ Fintype.piFinset fun _ : Fin n => letterFinset d.support := by
  by_cases hadm : IsSuperAscendingWord n S v
  · rw [ite_eq_left hadm] at hv
    exact mem_piFinset_letterFinset_of_coeff_superMonomial_ne_zero q hv
  · exact absurd (by rw [ite_eq_right hadm, map_zero]) hv

/-- **The super fundamental's coefficient as a sum over the admissible words of bounded absolute
value.** The words that reach `x^d` all have their absolute values in the support of `d`, so the
defining sum may be cut down to those, and the admissibility condition becomes a filter. -/
theorem coeff_superFundamental_eq_coeff_sum (q : K) (S : Finset ℕ) (d : ℕ →₀ ℕ) :
    MvPowerSeries.coeff d (superFundamental K q n S)
      = MvPowerSeries.coeff d (∑ v ∈ {v ∈ Fintype.piFinset fun _ : Fin n =>
          letterFinset d.support | IsSuperAscendingWord n S v}, superMonomial K q v) := by
  rw [coeff_superFundamental_eq_sum q n S
      fun _ hv => mem_piFinset_letterFinset_of_coeff_ite_ne_zero q S hv,
    map_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases hadm : IsSuperAscendingWord n S v
  · rw [ite_eq_left hadm, ite_eq_left hadm]
  · rw [ite_eq_right hadm, ite_eq_right hadm, map_zero]

/-- **A `q`-weighted sum of super fundamentals is a sum over the whole super alphabet.**
`∑_σ q^{inv(R,σ)}F̃_{n,Des(σ⁻¹)} = ∑_{v ∈ 𝒜^n}q^{inv^±(R,v)}z_v`, for any set `R` of increasing
pairs of positions.

At a fixed monomial both sides are finite sums over the super words whose absolute values lie in its
support. The fibres of `HJO.Sym.superStdPerm` partition those words; on the fibre of `σ` the weight
is `q^{inv(R,σ)}` by `HJO.Dyck.superInvNumber_eq_invNumber_of_superStdPerm_eq`, and the fibre sums
to the truncated `F̃_{n,Des(σ⁻¹)}` by `HJO.Sym.sum_superMonomial_superStdPerm`. -/
theorem sum_pow_invNumber_smul_superFundamental (K : Type*) [CommRing K] (q : K) {n : ℕ}
    (R : Finset (Fin n × Fin n)) (hR : ∀ p ∈ R, p.1 < p.2) :
    ∑ σ : Equiv.Perm (Fin n),
        q ^ invNumber R (fun i => σ i) • superFundamental K q n (invDescentSet σ)
      = summableSum fun v : Fin n → SuperLetter =>
          q ^ superInvNumber R v • superMonomial K q v := by
  classical
  refine MvPowerSeries.ext fun d => ?_
  rw [coeff_summableSum_eq_sum (s := Fintype.piFinset fun _ : Fin n => letterFinset d.support)
      fun _ hv => mem_piFinset_letterFinset_of_coeff_ne_zero q R hv,
    ← Finset.sum_fiberwise_of_maps_to (g := superStdPerm)
      (t := (univ : Finset (Equiv.Perm (Fin n)))) (fun v _ => mem_univ _)
      fun v => MvPowerSeries.coeff d (q ^ superInvNumber R v • superMonomial K q v),
    map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [show MvPowerSeries.coeff d (q ^ invNumber R (fun i => σ i) • superFundamental K q n
        (invDescentSet σ))
      = q ^ invNumber R (fun i => σ i) *
        MvPowerSeries.coeff d (superFundamental K q n (invDescentSet σ)) from rfl,
    coeff_superFundamental_eq_coeff_sum q (invDescentSet σ) d,
    ← sum_superMonomial_superStdPerm K q σ (letterFinset d.support), map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [mem_filter] at hv
  rw [superInvNumber_eq_invNumber_of_superStdPerm_eq hR hv.2]
  rfl

end HJO.Dyck
