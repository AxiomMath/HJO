/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.ChiPrime
public import HJO.CarlssonMellit.CornerInclusion
public import HJO.CarlssonMellit.SwapClass
public meta import HJO.Attr

/-! # The swapping proposition

`HJO.Dyck.auxToFrac_unnormalisedCharSeries_transposeTuple`: for a partial Dyck path `π ∈ 𝔻_{k,N}`
and a prescription `σ` putting `m` before `m + 1`, the swapping operator `Δ_m` carries `χ'_σ(π)` to
`χ'_{τ_m σ}(π)`.

`HJO.Dyck.pdelta_auxToFrac_finsum_labelClass` does this one class at a time, which is where the
mathematics is. This file is the passage from the classes to the series. `χ'_σ(π)` is defined one
coefficient at a time, each coefficient a finite sum over the labellings whose monomial has a
prescribed alphabet exponent; because `m + 1 < k` both letters lie below the level and contribute
nothing to that exponent, so each class lies wholly inside or wholly outside each of those finite
index sets. Grouping such a finite sum by `HJO.Dyck.labelClassKey` splits it into the class sums,
and `τ_m` matches the classes on the two sides.

## Main definitions

* `HJO.Dyck.labelClassKey`: the grouping key, `i ↦ if w i ∈ {m, m + 1} then m else w i`.
* `HJO.Dyck.chiIndex`: the finite index set of one coefficient of `χ'_σ(π)`.

## Main results

* `HJO.Dyck.card_invSet_finPairs_attackSet`: the two spellings of the inversion count agree.
* `HJO.Dyck.labelClassKey_eq_iff`: the key determines the class.
* `HJO.Dyck.coe_filter_labelClassKey`: a fibre of the key inside `chiIndex` *is* a class.
* `HJO.Dyck.finsum_labelClass_eq_monomial`: a class sum is a single monomial of the alphabet.
* `HJO.Dyck.auxToFrac_unnormalisedCharSeries_transposeTuple`: the swapping proposition.

## Implementation notes

*The key is `i ↦ if w i ∈ {m, m + 1} then m else w i`*, and it determines the class exactly: a
position lies in the two-letter support precisely where the key is `m`, since off the support the
letter is neither `m` nor `m + 1`. The relabelling `τ_m` leaves the key alone, so the fibres on the
two sides correspond under it and the two key sets coincide. This is the device
`HJO.Dyck.letterPerm_swap_sum_wordMonomial` already uses for the symmetry of `χ(R, n)`, there with
an `Option`-valued key.

*A class sum is one monomial of the alphabet.* Members of a class differ only inside the support,
where they carry `m` or `m + 1`, both below the level; so they all have the same
`HJO.Sym.zmonExponent`, and the class sum — a `∑ᶠ` over a `Set` — is
`MvPowerSeries.monomial e (finite sum of coefficients)`. That is what turns the per-class statement
about series into a statement about the single coefficient `e`, where the grouping happens, and
it is why no summability argument over the classes is needed: `HJO.Sym.pdelta_summableSum` is not
used.

*The inversion count has two spellings in this library*, `#(invSet (finPairs N (At π)) w)` on
the tuple `w : Fin N → ℕ` and `inv(At π, wordOfFin w)` on the word:
`HJO.Dyck.unnormalisedCharSeries` uses the first and the class-sum layer the second.
`HJO.Dyck.card_invSet_finPairs` reconciles them, its `HJO.Dyck.extendLabelling` being the same
function as `HJO.Dyck.wordOfFin`.

*The hypotheses are weaker than those of the statement as usually given*, exactly as for
`HJO.Dyck.pdelta_auxToFrac_finsum_labelClass`: `σ` is asked to be injective with `m` and `m + 1`
among its entries at positions `a < b`, not to list `{1, …, k}` without repetition. `k ≥ 2` and
`1 ≤ m ≤ k-1` are carried by the existence of `i j : Fin k` with `(i : ℕ) = m` and
`(j : ℕ) = m + 1`, and `N ≥ k` by `HJO.Dyck.IsPartialDyck.le_length`.

## References

E. Carlsson and A. Mellit,
*A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018) 661--697, Proposition 4.8.
-/

@[expose] public section

open Finset

namespace HJO.Dyck

open HJO.Sym

variable {N k m : ℕ} {x : Fin N → ℕ} {σ : Fin k → ℕ} {w w' : Fin N → ℕ} {e : ℕ →₀ ℕ}

/-! ### The two spellings of the inversion count -/

/-- **The inversion count of a labelling is the same read on the tuple and on the word.**
`HJO.Dyck.unnormalisedCharSeries` counts the inversions as pairs of positions of `Fin N`, the class
sums of `HJO.Dyck.finsum_labelClass` as cells of `ℕ × ℕ`; the attack set lies inside the square, so
the coercion `Fin.val` is a bijection between the two descriptions. -/
theorem card_invSet_finPairs_attackSet (x : Fin N → ℕ) (w : Fin N → ℕ) :
    #(invSet (finPairs N (attackSet x)) w) = invNumber (attackSet x) (wordOfFin w) :=
  card_invSet_finPairs (fun _ hc =>
    ⟨(fst_lt_snd_of_mem_attackSet hc).trans (snd_lt_of_mem_attackSet hc),
      snd_lt_of_mem_attackSet hc⟩) w

/-! ### Letters below the level leave no trace in the alphabet exponent -/

/-- A letter below the level contributes nothing to the alphabet exponent. -/
theorem zvarExponent_of_lt {j : ℕ} (h : j < k) : zvarExponent k j = 0 := by
  rw [zvarExponent, ite_eq_left h]

/-- A letter below the level is available to every coefficient. -/
theorem mem_zmonLetters_of_lt {j : ℕ} (h : j < k) : j ∈ zmonLetters k e :=
  Finset.mem_union_left _ (Finset.mem_range.2 h)

/-- **The relabelling does not move the alphabet exponent**, both letters lying below the level: at
each position the two letters either agree or lie in `{m, m + 1}`, and a letter below the level
contributes nothing. -/
theorem zmonExponent_transposeTuple (hmk : m + 1 < k) (w : Fin N → ℕ) :
    zmonExponent k (transposeTuple m w) = zmonExponent k w := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases eq_or_ne (w i) m with h | h
  · rw [transposeTuple_apply, h, Equiv.swap_apply_left,
      zvarExponent_of_lt (by omega : m + 1 < k), zvarExponent_of_lt (by omega : m < k)]
  rcases eq_or_ne (w i) (m + 1) with h' | h'
  · rw [transposeTuple_apply, h', Equiv.swap_apply_right,
      zvarExponent_of_lt (by omega : m < k), zvarExponent_of_lt (by omega : m + 1 < k)]
  · rw [transposeTuple_apply, swap_succ_of_ne h h']

/-! ### The grouping key -/

/-- **The grouping key of a class**: the labelling with every letter of the two-letter support
replaced by `m`. It determines the class of the labelling — a position lies in the support exactly
where the key is `m`, the letters off the support being neither `m` nor `m + 1` — and the
relabelling `τ_m` leaves it alone. -/
def labelClassKey (m : ℕ) {N : ℕ} (w : Fin N → ℕ) : Fin N → ℕ :=
  fun i => if w i = m ∨ w i = m + 1 then m else w i

/-- Membership in the two-letter support at a position of `Fin N`, read on the tuple. -/
theorem mem_labelSupport_val {i : Fin N} :
    (i : ℕ) ∈ labelSupport m w ↔ (w i = m ∨ w i = m + 1) := by
  rw [mem_labelSupport, wordOfFin_val]
  exact and_iff_right i.isLt

/-- **The key determines the class**: two labellings have the same key exactly when they have the
same two-letter support and agree outside it, which are the two conditions defining
`HJO.Dyck.labelClass`. -/
theorem labelClassKey_eq_iff :
    labelClassKey m w' = labelClassKey m w ↔ labelSupport m w' = labelSupport m w ∧
      ∀ i : Fin N, (i : ℕ) ∉ labelSupport m w → w' i = w i := by
  simp only [funext_iff, labelClassKey]
  constructor
  · intro h
    have hiff : ∀ i : Fin N, (w' i = m ∨ w' i = m + 1) ↔ (w i = m ∨ w i = m + 1) := by
      intro i
      have hi := h i
      by_cases h1 : w' i = m ∨ w' i = m + 1
      · refine iff_of_true h1 ?_
        by_contra h2
        rw [ite_eq_left h1, ite_eq_right h2] at hi
        exact h2 (Or.inl hi.symm)
      · refine iff_of_false h1 ?_
        by_contra h2
        rw [ite_eq_right h1, ite_eq_left h2] at hi
        exact h1 (Or.inl hi)
    refine ⟨Finset.ext fun p => ?_, fun i hi => ?_⟩
    · by_cases hpN : p < N
      · rw [show p = ((⟨p, hpN⟩ : Fin N) : ℕ) from rfl, mem_labelSupport_val,
          mem_labelSupport_val]
        exact hiff _
      · simp only [mem_labelSupport, hpN, false_and]
    · have hi' := h i
      rw [mem_labelSupport_val] at hi
      rwa [ite_eq_right (fun hc => hi ((hiff i).1 hc)), ite_eq_right hi] at hi'
  · rintro ⟨hS, hf⟩ i
    have hiff : (w' i = m ∨ w' i = m + 1) ↔ (w i = m ∨ w i = m + 1) := by
      rw [← mem_labelSupport_val, ← mem_labelSupport_val, hS]
    by_cases h1 : w i = m ∨ w i = m + 1
    · rw [ite_eq_left (hiff.2 h1), ite_eq_left h1]
    · rw [ite_eq_right (fun hc => h1 (hiff.1 hc)), ite_eq_right h1]
      exact hf i fun hc => h1 (mem_labelSupport_val.1 hc)

/-- **The relabelling leaves the key alone**: it moves neither the two-letter support nor the
letters outside it. -/
@[simp]
theorem labelClassKey_transposeTuple (m : ℕ) (w : Fin N → ℕ) :
    labelClassKey m (transposeTuple m w) = labelClassKey m w :=
  labelClassKey_eq_iff.2 ⟨labelSupport_transposeTuple m w,
    fun _ hi => transposeTuple_apply_of_notMem m w hi⟩

/-! ### The finite index set of one coefficient -/

/-- The labellings contributing to the coefficient of the monomial `x^e` in `χ'_σ(π)`: the no-attack
labellings whose monomial has alphabet exponent `e`, cut out of the tuples with letters in
`HJO.Dyck.zmonLetters`. This is the index set of the finite sum defining
`HJO.Dyck.unnormalisedCharSeries`, named so that the grouping into classes can be stated. -/
noncomputable def chiIndex (x : Fin N → ℕ) (σ : Fin k → ℕ) (e : ℕ →₀ ℕ) : Finset (Fin N → ℕ) :=
  {w ∈ Fintype.piFinset fun _ : Fin N => zmonLetters k e |
    w ∈ noAttackLabellings x σ ∧ zmonExponent k w = e}

theorem mem_chiIndex :
    w ∈ chiIndex x σ e ↔ (∀ i, w i ∈ zmonLetters k e) ∧
      w ∈ noAttackLabellings x σ ∧ zmonExponent k w = e := by
  rw [chiIndex, Finset.mem_filter, Fintype.mem_piFinset]

variable {K : Type*} [CommRing K]

/-- The coefficient of `x^e` in `χ'_σ(π)`, with its index set named. -/
theorem coeff_unnormalisedCharSeries_chiIndex (q : K) :
    MvPowerSeries.coeff e (unnormalisedCharSeries q k x σ) =
      ∑ v ∈ chiIndex x σ e, q ^ #(invSet (finPairs N (attackSet x)) v) • zmonCoeff K k v :=
  coeff_unnormalisedCharSeries

/-- **The relabelling matches the index sets of the two prescriptions.** Both letters lie below the
level, so they are available to every coefficient and leave the alphabet exponent alone, and the
no-attack condition is carried across by `HJO.Dyck.bijOn_transposeTuple`. -/
theorem transposeTuple_mem_chiIndex (hmk : m + 1 < k) (hw : w ∈ chiIndex x σ e) :
    transposeTuple m w ∈ chiIndex x (transposeTuple m σ) e := by
  obtain ⟨hl, hna, he⟩ := mem_chiIndex.1 hw
  refine mem_chiIndex.2 ⟨fun i => ?_, (bijOn_transposeTuple x σ m).mapsTo hna,
    by rw [zmonExponent_transposeTuple hmk, he]⟩
  rw [transposeTuple_apply]
  rcases eq_or_ne (w i) m with h | h
  · rw [h, Equiv.swap_apply_left]
    exact mem_zmonLetters_of_lt hmk
  rcases eq_or_ne (w i) (m + 1) with h' | h'
  · rw [h', Equiv.swap_apply_right]
    exact mem_zmonLetters_of_lt (by omega)
  · rw [swap_succ_of_ne h h']
    exact hl i

/-- **Members of one class have the same alphabet exponent**, both letters lying below the level:
inside the two-letter support each carries `m` or `m + 1`, which contribute nothing, and outside it
they agree. This is what makes a class lie wholly inside or wholly outside each index set. -/
theorem zmonExponent_eq_of_labelSupport_eq (hmk : m + 1 < k)
    (hS : labelSupport m w' = labelSupport m w)
    (hf : ∀ i : Fin N, (i : ℕ) ∉ labelSupport m w → w' i = w i) :
    zmonExponent k w' = zmonExponent k w := by
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : (i : ℕ) ∈ labelSupport m w
  · have hiv : (i : ℕ) ∈ labelSupport m w' := by rw [hS]; exact hi
    have h1 : w' i < k := by rcases mem_labelSupport_val.1 hiv with h | h <;> omega
    have h2 : w i < k := by rcases mem_labelSupport_val.1 hi with h | h <;> omega
    rw [zvarExponent_of_lt h1, zvarExponent_of_lt h2]
  · rw [hf i hi]

/-- **A fibre of the key inside the index set is exactly a class.** The key determines the class by
`HJO.Dyck.labelClassKey_eq_iff`, and conversely a member of the class is again in the index set: it
is a no-attack labelling, its letters are those of `w` off the support and `m` or `m + 1` on it, and
its alphabet exponent is unchanged. -/
theorem coe_filter_labelClassKey (hmk : m + 1 < k) (hw : w ∈ chiIndex x σ e) :
    ↑{v ∈ chiIndex x σ e | labelClassKey m v = labelClassKey m w} = labelClass x σ m w := by
  obtain ⟨hl, -, he⟩ := mem_chiIndex.1 hw
  refine Set.ext fun v => ?_
  simp only [Finset.coe_filter, Set.mem_ofPred_eq, mem_labelClass]
  constructor
  · rintro ⟨hv, hkey⟩
    exact ⟨(mem_chiIndex.1 hv).2.1, labelClassKey_eq_iff.1 hkey⟩
  · rintro ⟨hna, hS, hf⟩
    refine ⟨mem_chiIndex.2 ⟨fun i => ?_, hna, ?_⟩, labelClassKey_eq_iff.2 ⟨hS, hf⟩⟩
    · by_cases hi : (i : ℕ) ∈ labelSupport m w
      · have hiv : (i : ℕ) ∈ labelSupport m v := by rw [hS]; exact hi
        rcases mem_labelSupport_val.1 hiv with h | h
        · rw [h]
          exact mem_zmonLetters_of_lt (by omega)
        · rw [h]
          exact mem_zmonLetters_of_lt hmk
      · rw [hf i hi]
        exact hl i
    · rw [zmonExponent_eq_of_labelSupport_eq hmk hS hf, he]

/-! ### A class sum is one monomial of the alphabet -/

/-- A weighted labelling monomial is a monomial of `P_k`: the scalar weight is a constant series and
`HJO.Sym.zmon_eq_monomial` is the monomial. -/
theorem scalarSeries_pow_mul_zmon (q : K) (n : ℕ) (v : Fin N → ℕ) :
    scalarSeries K k q ^ n * zmon K k v =
      MvPowerSeries.monomial (zmonExponent k v) (q ^ n • zmonCoeff K k v) := by
  rw [zmon_eq_monomial, scalarSeries, ← map_pow, ← MvPowerSeries.monomial_zero_eq_C_apply,
    MvPowerSeries.monomial_mul_monomial, zero_add, MvPolynomial.smul_eq_C_mul, map_pow]

/-- **A class sum is a single monomial of the alphabet**, whose coefficient is the finite sum the
corresponding fibre of `HJO.Dyck.chiIndex` contributes to the coefficient of `x^e` in `χ'_σ(π)`.
Every member of the class has alphabet exponent `e`, so the whole class sum sits at that one
monomial; this is what turns the per-class identity `HJO.Dyck.finsum_labelClass` between *series*
into an identity between single coefficients, which is where the grouping happens. -/
theorem finsum_labelClass_eq_monomial (q : K) (hmk : m + 1 < k) (hw : w ∈ chiIndex x σ e) :
    (∑ᶠ w' ∈ labelClass x σ m w,
        scalarSeries K k q ^ invNumber (attackSet x) (wordOfFin w') * zmon K k w') =
      MvPowerSeries.monomial e
        (∑ v ∈ {v ∈ chiIndex x σ e | labelClassKey m v = labelClassKey m w},
          q ^ #(invSet (finPairs N (attackSet x)) v) • zmonCoeff K k v) := by
  rw [← coe_filter_labelClassKey hmk hw, finsum_mem_coe_finset, map_sum]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [← card_invSet_finPairs_attackSet, scalarSeries_pow_mul_zmon,
    (mem_chiIndex.1 (Finset.mem_filter.1 hv).1).2.2]

/-! ### The swapping proposition -/

variable [IsDomain K]

/-- **The per-class step, read at the one coefficient the class contributes to.** This is
`HJO.Dyck.pdelta_auxToFrac_finsum_labelClass` with both class sums replaced by their monomials and
the coefficient of `x^e` taken; the two sides are the contributions of the matching fibres of the
key to the coefficients of `χ'_σ(π)` and of `χ'_{τ_m σ}(π)`. -/
theorem pdeltaCoeff_algebraMap_sum_filter_labelClassKey (q : K) (hx : IsPartialDyck k N x)
    (hσ : Function.Injective σ) {i j : Fin k} (hmi : (i : ℕ) = m) (hmj : (j : ℕ) = m + 1)
    {a b : Fin k} (ha : σ a = m) (hb : σ b = m + 1) (hab : (a : ℕ) < (b : ℕ))
    (hw : w ∈ chiIndex x σ e) :
    pdeltaCoeff q i j (algebraMap (MvPolynomial (Fin k) K) (AuxFrac K k)
        (∑ v ∈ {v ∈ chiIndex x σ e | labelClassKey m v = labelClassKey m w},
          q ^ #(invSet (finPairs N (attackSet x)) v) • zmonCoeff K k v)) =
      algebraMap (MvPolynomial (Fin k) K) (AuxFrac K k)
        (∑ v ∈ {v ∈ chiIndex x (transposeTuple m σ) e | labelClassKey m v = labelClassKey m w},
          q ^ #(invSet (finPairs N (attackSet x)) v) • zmonCoeff K k v) := by
  have hmk : m + 1 < k := hmj ▸ j.isLt
  have h := pdelta_auxToFrac_finsum_labelClass q hx hσ hmi hmj ha hb hab
    (mem_chiIndex.1 hw).2.1 (K := K)
  rw [finsum_labelClass_eq_monomial q hmk hw,
    finsum_labelClass_eq_monomial q hmk (transposeTuple_mem_chiIndex hmk hw),
    labelClassKey_transposeTuple] at h
  have h2 := congrArg (MvPowerSeries.coeff e) h
  rwa [coeff_pdelta, coeff_auxToFrac, coeff_auxToFrac, MvPowerSeries.coeff_monomial_same,
    MvPowerSeries.coeff_monomial_same] at h2

/-- **The swapping proposition** `HJO.Dyck.auxToFrac_unnormalisedCharSeries_transposeTuple`: for a
partial Dyck path `π ∈ 𝔻_{k,N}` and a prescription `σ` with pairwise distinct entries among which
`m` occurs before `m + 1`,

`χ'_{τ_m σ}(π) = Δ_m(χ'_σ(π))`,

inside `P°_k`, where `Δ_m` lives.

Both series are given one coefficient at a time, and each coefficient is a finite sum over
`HJO.Dyck.chiIndex`. Since `m + 1 < k` both letters lie below the level, a class is wholly inside
or wholly outside each of those index sets; grouping the finite sum by `HJO.Dyck.labelClassKey`
therefore splits it into class sums, `HJO.Dyck.pdelta_auxToFrac_finsum_labelClass` carries each
fibre for `σ` to the matching fibre for `τ_m σ`, and the relabelling matches the two key sets by
`HJO.Dyck.bijOn_transposeTuple`. -/
@[hjo "prop_cm_swapping"]
theorem auxToFrac_unnormalisedCharSeries_transposeTuple (q : K) (hx : IsPartialDyck k N x)
    (hσ : Function.Injective σ) {i j : Fin k} (hmi : (i : ℕ) = m) (hmj : (j : ℕ) = m + 1)
    {a b : Fin k} (ha : σ a = m) (hb : σ b = m + 1) (hab : (a : ℕ) < (b : ℕ)) :
    auxToFrac K k (unnormalisedCharSeries q k x (transposeTuple m σ)) =
      pdelta q i j (auxToFrac K k (unnormalisedCharSeries q k x σ)) := by
  have hmk : m + 1 < k := hmj ▸ j.isLt
  refine MvPowerSeries.ext fun d => ?_
  rw [coeff_auxToFrac, coeff_pdelta, coeff_auxToFrac,
    coeff_unnormalisedCharSeries_chiIndex, coeff_unnormalisedCharSeries_chiIndex]
  have hmaps : ∀ v ∈ chiIndex x (transposeTuple m σ) d,
      labelClassKey m v ∈ (chiIndex x σ d).image (labelClassKey m) := by
    intro v hv
    refine Finset.mem_image.2 ⟨transposeTuple m v, ?_, labelClassKey_transposeTuple m v⟩
    have h := transposeTuple_mem_chiIndex hmk hv
    rwa [transposeTuple_transposeTuple] at h
  rw [← Finset.sum_fiberwise_of_maps_to (t := (chiIndex x σ d).image (labelClassKey m))
      (fun v hv => Finset.mem_image_of_mem _ hv)
      (fun v => q ^ #(invSet (finPairs N (attackSet x)) v) • zmonCoeff K k v),
    ← Finset.sum_fiberwise_of_maps_to hmaps
      (fun v => q ^ #(invSet (finPairs N (attackSet x)) v) • zmonCoeff K k v),
    map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun c hc => ?_
  obtain ⟨w₀, hw₀, rfl⟩ := Finset.mem_image.1 hc
  exact (pdeltaCoeff_algebraMap_sum_filter_labelClassKey q hx hσ hmi hmj ha hb hab hw₀).symm

end HJO.Dyck
