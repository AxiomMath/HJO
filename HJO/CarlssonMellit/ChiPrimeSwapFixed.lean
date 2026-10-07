/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.ChiPrimeSwap
public import HJO.CarlssonMellit.ChiPrimeZGraded
public import HJO.CarlssonMellit.LabelSumFull
public import HJO.CarlssonMellit.ZvarMerged
public meta import HJO.Attr

/-! # The characteristic series is fixed when neither label is special

`HJO.Dyck.zSwap_auxToFrac_unnormalisedCharSeries`: for a partial Dyck path `π ∈ 𝔻_{k+1,N}` and a
prescription `σ` no entry of which lies in `{m, m+1}`, the interchange `ŝ_m` of `HJO.Sym.zSwap`
fixes `χ'_σ(π)`. The index is `m = k + r`, the `m ≥ k`, so the two interchanged merged variables lie
at or above the level and `ŝ_m` is the operator of the merged alphabet rather than a renaming of the
free variables.

By `HJO.Dyck.equivalence_labelClass` the no-attack labellings fall into the classes
`K_m(π, σ, w)`, and by `HJO.Dyck.finsum_labelClass_full` each class sum is
`q^e g ∏_t (a_m(l_t,0) + a_m(l_t,1))`, every factor of which `ŝ_m` fixes: `q^e` is a scalar, each
factor of `g` is a merged variable off the two-letter support, hence neither `m` nor `m+1`, and each
remaining factor is fixed by `HJO.Sym.zSwap_runWeight_add_runWeight`. Since the fixed elements of
`Z^{(k+1)}` form a subring — `HJO.Sym.zSwapFixedSubring` — a finite sum of class sums is fixed too.

What this file has to supply beyond that is the passage from the classes to the series, and here it
cannot be the passage of `HJO.Dyck.auxToFrac_unnormalisedCharSeries_transposeTuple`: both
interchanged variables lie at or above the level, so the members of one class carry different
alphabet exponents and a class spans several monomials of `P_{k+1}`. Instead the sum is truncated:
`HJO.Dyck.charTrunc` sums only the labellings with letters in a finite set `s`, and as soon as `s`
contains `m` and `m+1` its index set is a union of
*whole* classes, grouped by `HJO.Dyck.labelClassKey`, so the truncation is fixed by `ŝ_m`. A merged
coefficient of `χ'_σ(π)` reads a single coefficient of the alphabet, so it agrees with the
truncation's as soon as `s` holds the finitely many letters that coefficient admits; choosing `s`
from the two merged exponents `ŝ_m` compares then settles that pair of merged coefficients, and
`HJO.Sym.eq_of_zCoeff_eq` settles the identity.

## Main definitions

* `HJO.Dyck.charTrunc`: the defining sum of `HJO.Dyck.unnormalisedCharSeries` truncated to the
  labellings with letters in a finite set.

## Main results

* `HJO.Dyck.auxToFrac_finsum_labelClass_mem_zSwapFixedSubring`: a class sum is fixed by `ŝ_m`.
* `HJO.Dyck.auxToFrac_charTrunc_mem_zSwapFixedSubring`: so is the truncated sum.
* `HJO.Dyck.zSwap_auxToFrac_unnormalisedCharSeries`: the main statement.

## Implementation notes

*The pairwise distinctness of `σ` is dropped*, as at `HJO.Dyck.finsum_labelClass_full`: neither
`HJO.Dyck.finsum_labelClass_full` nor `HJO.Dyck.finsum_labelClass_of_labelSupport_eq_empty` reads
it, and nothing else here does either. `N ≥ k` is carried by `HJO.Dyck.IsPartialDyck.le_length`, and
`m ≥ k` is the parametrisation `m = k + r`, so no truncated subtraction appears.

*Both cases of `HJO.Dyck.finsum_labelClass_full` are used.* At an empty two-letter support the class
is the singleton `{w}` and the run product is absent, which is
`HJO.Dyck.finsum_labelClass_of_labelSupport_eq_empty`; the factors of `g` are then all of
`z^{(k+1)}_w`, and none of its letters is `m` or `m+1`, so the same argument applies unchanged.

*The truncation is indexed by an arbitrary finite set of letters, not by a bound.* All that is asked
of `s` is that it contain `m` and `m+1`, which is what makes a class of a labelling with letters in
`s` lie wholly inside the index set; the sets actually used are unions of
`HJO.Dyck.zmonLetters`, so no arithmetic on the letters is needed.

## References

E. Carlsson and A. Mellit,
*A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018) 661--697, Section 4.
-/

@[expose] public section

open Finset

namespace HJO.Dyck

open HJO.Sym

variable {K : Type*} [CommRing K] {N k r : ℕ} {x : Fin N → ℕ} {w : Fin N → ℕ}

/-! ### The two spellings of a weighted labelling monomial -/

/-- The weight of a labelling written with the scalar as a constant series, which is the form the
class-sum layer uses, is the weight written as a scalar action, which is the form
`HJO.Dyck.unnormalisedCharSeries` uses. -/
private theorem smul_zmon_eq (q : K) (k n : ℕ) {N : ℕ} (v : Fin N → ℕ) :
    q ^ n • zmon K k v = scalarSeries K k q ^ n * zmon K k v := by
  rw [scalarSeries_pow_mul_zmon, zmon_eq_monomial]
  refine MvPowerSeries.ext fun d => ?_
  rw [show MvPowerSeries.coeff d (q ^ n • MvPowerSeries.monomial (zmonExponent k v)
        (zmonCoeff K k v))
      = q ^ n • MvPowerSeries.coeff d (MvPowerSeries.monomial (zmonExponent k v)
        (zmonCoeff K k v)) from rfl,
    MvPowerSeries.coeff_monomial, MvPowerSeries.coeff_monomial]
  split <;> simp

/-! ### The factors of a class sum are fixed by the interchange -/

variable [IsDomain K]

/-- The weight of a run at the two letters of the merged alphabet lies in `Z^{(k+1)}`, being a
product of powers of members of it. -/
private theorem runWeight_zLetterSeries_mem_zRing (q : K) (k r l : ℕ) (ε : Bool) :
    runWeight (MvPowerSeries.C (scalarFrac K q) : AuxAlphabetSeriesFrac K (k + 1))
        (zLetterSeries K k r) (zLetterSeries K k (r + 1)) l ε ∈ zRing K k := by
  have hq := (C_scalarFrac_mem_zSwapFixedSubring (K := K) (k := k) q r).1
  have hu := zLetterSeries_mem_zRing (K := K) (k := k) r
  have hv := zLetterSeries_mem_zRing (K := K) (k := k) (r + 1)
  cases ε <;> simp only [runWeight] <;>
    exact mul_mem_zRing (mul_mem_zRing (pow_mem_zRing hq _) (pow_mem_zRing hu _))
      (pow_mem_zRing hv _)

/-- **The two weights of a run sum to an element `ŝ_m` fixes**, which is
`HJO.Sym.zSwap_runWeight_add_runWeight` packaged as a membership in the fixed subring. -/
private theorem runWeight_add_mem_zSwapFixedSubring (q : K) (k r l : ℕ) :
    runWeight (MvPowerSeries.C (scalarFrac K q) : AuxAlphabetSeriesFrac K (k + 1))
          (zLetterSeries K k r) (zLetterSeries K k (r + 1)) l false
        + runWeight (MvPowerSeries.C (scalarFrac K q) : AuxAlphabetSeriesFrac K (k + 1))
          (zLetterSeries K k r) (zLetterSeries K k (r + 1)) l true
      ∈ zSwapFixedSubring K k r :=
  ⟨add_mem_zRing (runWeight_zLetterSeries_mem_zRing q k r l false)
      (runWeight_zLetterSeries_mem_zRing q k r l true),
    zSwap_runWeight_add_runWeight q r l⟩

/-- A merged variable other than the two the interchange moves is fixed by it. -/
private theorem auxToFrac_zvar_mem_zSwapFixedSubring {j : ℕ} (hj : j ≠ k + r)
    (hj' : j ≠ k + r + 1) :
    auxToFrac K (k + 1) (zvar K (k + 1) j) ∈ zSwapFixedSubring K k r :=
  ⟨auxToFrac_zvar_mem_zRing K k j, zSwap_auxToFrac_zvar_of_ne hj hj'⟩

variable {σ : Fin (k + 1) → ℕ}

/-- **A class sum is fixed by the interchange.** By `HJO.Dyck.finsum_labelClass_full` it is
`q^e g ∏_t (a_m(l_t,0) + a_m(l_t,1))`; the scalar `q^e` is fixed, each factor of `g` is a merged
variable at a position off the two-letter support, hence one carrying neither `m` nor `m + 1`, and
each remaining factor is fixed by `HJO.Sym.zSwap_runWeight_add_runWeight`. The fixed elements form a
subring, so the product is fixed. Both cases of `HJO.Dyck.finsum_labelClass_full` occur: at an empty
support the run product is absent and `g` is the whole labelling monomial. -/
theorem auxToFrac_finsum_labelClass_mem_zSwapFixedSubring (q : K)
    (hx : IsPartialDyck (k + 1) N x) (hw : w ∈ noAttackLabellings x σ)
    (hσ : ∀ j : Fin (k + 1), σ j ≠ k + r ∧ σ j ≠ k + r + 1) :
    auxToFrac K (k + 1) (∑ᶠ w' ∈ labelClass x σ (k + r) w,
        scalarSeries K (k + 1) q ^ invNumber (attackSet x) (wordOfFin w') * zmon K (k + 1) w')
      ∈ zSwapFixedSubring K k r := by
  have hg : ∀ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) ∉ labelSupport (k + r) w),
      auxToFrac K (k + 1) (zvar K (k + 1) (w i)) ∈ zSwapFixedSubring K k r := by
    intro i hi
    have h2 : ¬(w i = k + r ∨ w i = k + r + 1) := fun hc =>
      (Finset.mem_filter.1 hi).2 (mem_labelSupport_val.2 hc)
    exact auxToFrac_zvar_mem_zSwapFixedSubring (fun h => h2 (Or.inl h)) fun h => h2 (Or.inr h)
  by_cases hp : 1 ≤ #(labelSupport (k + r) w)
  · rw [finsum_labelClass_full q hx hw hσ hp, map_mul, map_mul, map_pow, map_prod, map_prod,
      auxToFrac_scalarSeries]
    refine Subring.mul_mem _ (Subring.mul_mem _
      (Subring.pow_mem _ (C_scalarFrac_mem_zSwapFixedSubring q r) _)
      (Subring.prod_mem _ hg)) (Subring.prod_mem _ fun t _ => ?_)
    rw [map_add, auxToFrac_runWeightZvar_level_add, auxToFrac_runWeightZvar_level_add]
    exact runWeight_add_mem_zSwapFixedSubring q k r _
  · rw [finsum_labelClass_of_labelSupport_eq_empty q hw
        (Finset.card_eq_zero.1 (by omega : #(labelSupport (k + r) w) = 0)),
      map_mul, map_pow, map_prod, auxToFrac_scalarSeries]
    exact Subring.mul_mem _ (Subring.pow_mem _ (C_scalarFrac_mem_zSwapFixedSubring q r) _)
      (Subring.prod_mem _ hg)

end HJO.Dyck

namespace HJO.Dyck

open HJO.Sym

variable {K : Type*} [CommRing K] {N k : ℕ} {x : Fin N → ℕ} {σ : Fin k → ℕ}

/-! ### The truncated characteristic sum -/

/-- **The defining sum of `HJO.Dyck.unnormalisedCharSeries` truncated to the letters in a finite set
`s`**: the finite sum of `q ^ inv(At(π), w) z^{(k)}_w` over the no-attack labellings with every
letter in `s`.

It agrees with `χ'_σ(π)` on every coefficient of the alphabet whose contributing labellings have
their letters in `s`, which is `HJO.Dyck.coeff_auxToFrac_unnormalisedCharSeries_eq`, and it is a
*finite* sum, so the grouping into classes that `HJO.Dyck.finsum_labelClass_full` evaluates takes
place inside it. -/
noncomputable def charTrunc (q : K) (k : ℕ) {N : ℕ} (x : Fin N → ℕ) (σ : Fin k → ℕ)
    (s : Finset ℕ) : AuxAlphabetSeries K k :=
  ∑ w ∈ {w ∈ Fintype.piFinset fun _ : Fin N => s | w ∈ noAttackLabellings x σ},
    q ^ #(invSet (finPairs N (attackSet x)) w) • zmon K k w

/-- Membership in the index set of the truncated sum: a no-attack labelling every letter of which
lies in `s`. -/
theorem mem_charTruncIndex {s : Finset ℕ} {w : Fin N → ℕ} :
    w ∈ {w ∈ Fintype.piFinset fun _ : Fin N => s | w ∈ noAttackLabellings x σ} ↔
      (∀ i, w i ∈ s) ∧ w ∈ noAttackLabellings x σ := by
  rw [Finset.mem_filter, Fintype.mem_piFinset]

/-- **The truncation has the coefficients of `χ'_σ(π)`** at every alphabet exponent whose
contributing labellings are covered by `s`, since those are the only labellings the coefficient
reads. -/
theorem coeff_auxToFrac_unnormalisedCharSeries_eq (q : K) {s : Finset ℕ} {e : ℕ →₀ ℕ}
    (hs : zmonLetters k e ⊆ s) :
    MvPowerSeries.coeff e (auxToFrac K k (unnormalisedCharSeries q k x σ))
      = MvPowerSeries.coeff e (auxToFrac K k (charTrunc q k x σ s)) := by
  rw [coeff_auxToFrac, coeff_auxToFrac, coeff_unnormalisedCharSeries_eq_coeff_sum hs, charTrunc,
    map_sum, map_sum]

end HJO.Dyck

namespace HJO.Dyck

open HJO.Sym

variable {K : Type*} [CommRing K] [IsDomain K] {N k r : ℕ} {x : Fin N → ℕ} {σ : Fin (k + 1) → ℕ}

/-! ### The truncation is a union of whole classes -/

/-- **A fibre of the grouping key inside the truncated index set is exactly a class**, as soon as
`s` contains both interchanged letters: the key determines the class by
`HJO.Dyck.labelClassKey_eq_iff`, and a member of the class again has its letters in `s`, being one
of `m`, `m + 1` on the two-letter support and a letter of the representative off it. Unlike
`HJO.Dyck.coe_filter_labelClassKey` this asks nothing of the alphabet exponent, so it holds with
both letters at or above the level. -/
theorem coe_filter_labelClassKey_charTruncIndex {s : Finset ℕ} {m : ℕ} (hm : m ∈ s)
    (hm' : m + 1 ∈ s) {w : Fin N → ℕ}
    (hw : w ∈ {v ∈ Fintype.piFinset fun _ : Fin N => s | v ∈ noAttackLabellings x σ}) :
    ↑{v ∈ {v ∈ Fintype.piFinset fun _ : Fin N => s | v ∈ noAttackLabellings x σ} |
        labelClassKey m v = labelClassKey m w} = labelClass x σ m w := by
  classical
  obtain ⟨hl, -⟩ := mem_charTruncIndex.1 hw
  refine Set.ext fun v => ?_
  simp only [Finset.coe_filter, Set.mem_ofPred_eq, mem_labelClass]
  constructor
  · rintro ⟨hv, hkey⟩
    exact ⟨(mem_charTruncIndex.1 hv).2, labelClassKey_eq_iff.1 hkey⟩
  · rintro ⟨hna, hS, hf⟩
    refine ⟨mem_charTruncIndex.2 ⟨fun i => ?_, hna⟩, labelClassKey_eq_iff.2 ⟨hS, hf⟩⟩
    by_cases hi : (i : ℕ) ∈ labelSupport m w
    · have hiv : (i : ℕ) ∈ labelSupport m v := by rw [hS]; exact hi
      rcases mem_labelSupport_val.1 hiv with h | h
      · rw [h]; exact hm
      · rw [h]; exact hm'
    · rw [hf i hi]
      exact hl i

/-- **The truncated sum is fixed by the interchange.** Its index set is a union of whole classes as
soon as `s` contains the two interchanged letters, grouping it by `HJO.Dyck.labelClassKey` writes it
as a finite sum of class sums, and each of those is fixed by
`HJO.Dyck.auxToFrac_finsum_labelClass_mem_zSwapFixedSubring`. -/
theorem auxToFrac_charTrunc_mem_zSwapFixedSubring (q : K) (hx : IsPartialDyck (k + 1) N x)
    (hσ : ∀ j : Fin (k + 1), σ j ≠ k + r ∧ σ j ≠ k + r + 1) {s : Finset ℕ} (hm : k + r ∈ s)
    (hm' : k + r + 1 ∈ s) :
    auxToFrac K (k + 1) (charTrunc q (k + 1) x σ s) ∈ zSwapFixedSubring K k r := by
  classical
  rw [charTrunc, ← Finset.sum_fiberwise_of_maps_to
      (t := ({v ∈ Fintype.piFinset fun _ : Fin N => s |
        v ∈ noAttackLabellings x σ}).image (labelClassKey (k + r)))
      (fun v hv => Finset.mem_image_of_mem _ hv)
      (fun v => q ^ #(invSet (finPairs N (attackSet x)) v) • zmon K (k + 1) v), map_sum]
  refine Subring.sum_mem _ fun c hc => ?_
  obtain ⟨w₀, hw₀, rfl⟩ := Finset.mem_image.1 hc
  have key : ∑ v ∈ {v ∈ {v ∈ Fintype.piFinset fun _ : Fin N => s |
          v ∈ noAttackLabellings x σ} | labelClassKey (k + r) v = labelClassKey (k + r) w₀},
        q ^ #(invSet (finPairs N (attackSet x)) v) • zmon K (k + 1) v
      = ∑ᶠ w' ∈ labelClass x σ (k + r) w₀,
        scalarSeries K (k + 1) q ^ invNumber (attackSet x) (wordOfFin w') * zmon K (k + 1) w' := by
    rw [← coe_filter_labelClassKey_charTruncIndex hm hm' hw₀, finsum_mem_coe_finset]
    exact Finset.sum_congr rfl fun v _ => by
      rw [smul_zmon_eq, card_invSet_finPairs_attackSet]
  rw [key]
  exact auxToFrac_finsum_labelClass_mem_zSwapFixedSubring q hx (mem_charTruncIndex.1 hw₀).2 hσ

/-! ### The main statement -/

/-- **The characteristic series is fixed when neither label is special**,
`HJO.Dyck.zSwap_auxToFrac_unnormalisedCharSeries`: for a partial Dyck path `π ∈ 𝔻_{k+1,N}` and a
prescription `σ` no entry of which is `m` or `m + 1`, the interchange `ŝ_m` of `HJO.Sym.zSwap` fixes
`χ'_σ(π)`. The index is `m = k + r`, the `m ≥ k`, so the interchange is the one of the merged
alphabet.

`χ'_σ(π)` lies in `Z^{(k+1)}` by `HJO.Dyck.auxToFrac_unnormalisedCharPart_mem_zGraded`, so it is
determined by its merged coefficients and `ŝ_m` reads them at the transposed merged exponents. Each
of the two merged coefficients being compared reads one coefficient of the alphabet, hence only the
labellings whose letters lie in a finite set; on the truncation of the defining sum to a finite set
of letters containing `m` and `m + 1` the whole classes of `HJO.Dyck.labelClass` are present, so it
is a finite sum of the class sums `HJO.Dyck.finsum_labelClass_full` evaluates and is fixed by `ŝ_m`.

The pairwise distinctness of `σ` is not used, as at `HJO.Dyck.finsum_labelClass_full`, and its
`N ≥ k` is `HJO.Dyck.IsPartialDyck.le_length`. -/
@[hjo "lem_cm_chiprime_swap_fixed"]
theorem zSwap_auxToFrac_unnormalisedCharSeries (q : K) (hx : IsPartialDyck (k + 1) N x)
    (hσ : ∀ j : Fin (k + 1), σ j ≠ k + r ∧ σ j ≠ k + r + 1) :
    zSwap K k r (auxToFrac K (k + 1) (unnormalisedCharSeries q (k + 1) x σ))
      = auxToFrac K (k + 1) (unnormalisedCharSeries q (k + 1) x σ) := by
  classical
  have hF : auxToFrac K (k + 1) (unnormalisedCharSeries q (k + 1) x σ) ∈ zRing K k :=
    auxToFrac_unnormalisedCharSeries_mem_zRing q k x σ
  refine eq_of_zCoeff_eq
    (fun α => coeff_mem_range_yFracEval_of_mem_zRing (zSwap_mem_zRing r hF) α)
    (fun α => coeff_mem_range_yFracEval_of_mem_zRing hF α) fun ν => ?_
  rw [zSwap_apply, zCoeff_zPerm _ hF]
  set s : Finset ℕ := zmonLetters (k + 1) ν.some ∪
    zmonLetters (k + 1) (Finsupp.equivMapDomain (zSwapEquiv r).symm ν).some ∪
      {k + r, k + r + 1} with hsdef
  have hm : k + r ∈ s := by rw [hsdef]; simp
  have hm' : k + r + 1 ∈ s := by rw [hsdef]; simp
  have hT := auxToFrac_charTrunc_mem_zSwapFixedSubring (r := r) q hx hσ hm hm'
  have hz : ∀ μ : Option ℕ →₀ ℕ, zmonLetters (k + 1) μ.some ⊆ s →
      zCoeff K k (auxToFrac K (k + 1) (unnormalisedCharSeries q (k + 1) x σ)) μ
        = zCoeff K k (auxToFrac K (k + 1) (charTrunc q (k + 1) x σ s)) μ := fun μ hμ => by
    rw [zCoeff, zCoeff, coeff_auxToFrac_unnormalisedCharSeries_eq q hμ]
  rw [hz _ (by rw [hsdef]; exact (Finset.subset_union_right).trans Finset.subset_union_left),
    hz ν (by rw [hsdef]; exact (Finset.subset_union_left).trans Finset.subset_union_left),
    ← zCoeff_zPerm (zSwapEquiv r) hT.1 ν, ← zSwap_apply, hT.2]

end HJO.Dyck
