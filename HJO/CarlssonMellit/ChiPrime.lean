/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.NoAttack
public import HJO.CarlssonMellit.RunWeight
public import HJO.CarlssonMellit.TwoLetterChar
public import HJO.CarlssonMellit.ZTail
public meta import HJO.Attr

/-! # The unnormalised characteristic series of a partial Dyck path

One definition, `HJO.Dyck.unnormalisedCharSeries`: for a partial Dyck path `π ∈ 𝔻_{k,N}` and a
tuple `σ` of special values,

`χ'_σ(π) = ∑_{w ∈ U(π,σ)} q ^ inv(At(π), w) · z^{(k)}_w ∈ P_k`,

the sum over the no-attack labellings of `q` to the inversion number times the *full* labelling
monomial `HJO.Sym.zmon`. It differs from `HJO.Dyck.partialCharSeries`, the `ν_σ(π)`,
only in retaining the `k` factors contributed by the positions below the level; it is the series the
swapping proposition is stated at, because the swapping operator `Δ_m` acts on exactly those
factors.

As for `ν_σ(π)` the sum is infinite and its value is a power series, so it is built one coefficient
at a time. What makes that possible is that the labelling monomial is a *monomial* of `P_k`
(`HJO.Sym.zmon_eq_monomial`), with alphabet exponent `HJO.Sym.zmonExponent` and coefficient
`HJO.Sym.zmonCoeff` in `𝕜[y_1, …, y_k]`; a given monomial of the alphabet therefore receives
contributions only from the labellings with a given `zmonExponent`, and `HJO.Dyck.zmonLetters`
bounds their letters to a finite set.

## Main definitions

* `HJO.Sym.zmonExponent`, `HJO.Sym.zmonCoeff`: the two halves of the labelling monomial.
* `HJO.Dyck.zmonLetters`: the finite set of letters a labelling contributing to a given coefficient
  can carry.
* `HJO.Dyck.unnormalisedCharSeries`: `χ'_σ(π)`, the main definition.

## Main results

The definition is used through these, not by unfolding it.

* `HJO.Sym.coeff_zmon`: the coefficients of the labelling monomial.
* `HJO.Dyck.coeff_unnormalisedCharSeries`: the coefficient of a monomial, the defining property.
* `HJO.Dyck.coeff_unnormalisedCharSeries_of_subset`: the same with the letters bounded by any finite
  set containing `zmonLetters`.
* `HJO.Dyck.coeff_unnormalisedCharSeries_eq_coeff_sum`: `χ'_σ(π)` is the displayed sum of the
  monomials `HJO.Sym.zmon`, restricted to the no-attack labellings.

## Implementation notes

*`zmonLetters` needs neither `σ` nor the path.* Its counterpart `HJO.Dyck.nuLetters` for `ν_σ(π)`
carries the image of `σ`, because the free part `z^{(k)}_{w,♭}` skips the positions below the level
and those positions' letters leave no trace in the exponent; the full monomial `z^{(k)}_w` skips
nothing, so every letter of a contributing labelling is either below the level or recorded in the
exponent.

*The weight `q` lives in the base ring `K`* and acts on the coefficients through the `K`-algebra
structure of `MvPolynomial (Fin k) K`, as for `HJO.Dyck.partialCharSeries`.

*No hypothesis is imposed on `x`, on `σ` or on `k ≤ N`*, exactly as for
`HJO.Dyck.partialCharSeries`: the series reads `x` only through its attack set and `σ` only through
the prescription, so `π ∈ 𝔻_{k,N}` and the pairwise distinctness of `σ` are hypotheses of the
*lemmas* about `χ'_σ(π)`.

## References

E. Carlsson and
A. Mellit, *A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018) 661--697,
Section 4.
-/

@[expose] public section

open Finset

namespace HJO.Sym

/-! ### The labelling monomial as a monomial -/

/-- The exponent in the alphabet of the labelling monomial `z^{(k)}_w`: the sum over all positions
of the exponent each merged variable contributes, which is nothing for a letter below the level and
the letter shifted down by `k` for a letter at or above it. -/
noncomputable def zmonExponent (k : ℕ) {N : ℕ} (w : Fin N → ℕ) : ℕ →₀ ℕ :=
  ∑ i : Fin N, zvarExponent k (w i)

/-- The coefficient in `𝕜[y_1, …, y_k]` of the labelling monomial `z^{(k)}_w`: the product of the
auxiliary variables named by the letters of `w` that lie below the level. -/
noncomputable def zmonCoeff (K : Type*) [CommRing K] (k : ℕ) {N : ℕ} (w : Fin N → ℕ) :
    MvPolynomial (Fin k) K :=
  ∏ i : Fin N, zvarCoeff K k (w i)

/-- **The labelling monomial is a monomial of `P_k`**, with exponent `HJO.Sym.zmonExponent` in the
alphabet and coefficient `HJO.Sym.zmonCoeff` in the auxiliary variables. This is what makes the
sum `χ'_σ(π) = ∑_w q ^ inv(At(π), w) z^{(k)}_w` an element of `P_k` despite having
infinitely many terms. -/
theorem zmon_eq_monomial (K : Type*) [CommRing K] (k : ℕ) {N : ℕ} (w : Fin N → ℕ) :
    zmon K k w = MvPowerSeries.monomial (zmonExponent k w) (zmonCoeff K k w) := by
  rw [zmon, Finset.prod_congr rfl fun i _ => zvar_eq_monomial K k (w i),
    prod_monomial_eq_monomial, zmonExponent, zmonCoeff]

/-- The coefficients of `z^{(k)}_w`: the coefficient of the monomial with exponent `e` is
`zmonCoeff` when `e` is the exponent of `z^{(k)}_w` and `0` otherwise. -/
theorem coeff_zmon (K : Type*) [CommRing K] (k : ℕ) {N : ℕ} (w : Fin N → ℕ) (e : ℕ →₀ ℕ) :
    MvPowerSeries.coeff e (zmon K k w) =
      if e = zmonExponent k w then zmonCoeff K k w else 0 := by
  rw [zmon_eq_monomial, MvPowerSeries.coeff_monomial]

end HJO.Sym

namespace HJO.Dyck

open HJO.Sym

variable {K : Type*} [CommRing K] {N k : ℕ}

/-! ### The letters a contributing labelling can carry -/

/-- The letters available to a labelling that contributes to the coefficient of the monomial `x^e`
in `χ'_σ(π)`: the letters below the level `k`, which name auxiliary variables and so leave no trace
in `e`, and the letters `j + k` for `j` in the support of `e`, which name the letters of the
alphabet that `e` records.

This is a *finite* set, and `HJO.Dyck.mem_zmonLetters` shows every contributing labelling takes its
letters in it. That is what cuts a finite index set out of the infinite `U(π, σ)`, one coefficient
at a time. -/
def zmonLetters (k : ℕ) (e : ℕ →₀ ℕ) : Finset ℕ :=
  Finset.range k ∪ e.support.image (· + k)

/-- **Every labelling whose monomial has alphabet exponent `e` takes its letters in
`HJO.Dyck.zmonLetters`.** A letter below the level lies in `Finset.range k`; a letter at or above it
contributes the exponent `single (w_i - k) 1` to `zmonExponent k w = e`, so `w_i - k` lies in the
support of `e`. Unlike its counterpart for `ν_σ(π)` this reads neither the path nor `σ`. -/
theorem mem_zmonLetters {w : Fin N → ℕ} {e : ℕ →₀ ℕ} (he : zmonExponent k w = e) (i : Fin N) :
    w i ∈ zmonLetters k e := by
  by_cases hwi : w i < k
  · exact Finset.mem_union_left _ (Finset.mem_range.2 hwi)
  refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨w i - k, ?_, by omega⟩)
  have hval : (1 : ℕ) ≤ e (w i - k) := by
    rw [← he, zmonExponent, Finsupp.finsetSum_apply]
    refine le_trans ?_ (Finset.single_le_sum
      (f := fun l => zvarExponent k (w l) (w i - k)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i))
    simp only [zvarExponent, hwi, ↓reduceIte, Finsupp.single_eq_same, le_refl]
  exact Finsupp.mem_support_iff.2 (by omega)

/-! ### The unnormalised characteristic series -/

/-- **The unnormalised characteristic series `χ'_σ(π)` of a partial Dyck path**,

`χ'_σ(π) = ∑_{w ∈ U(π,σ)} q ^ inv(At(π), w) · z^{(k)}_w ∈ P_k`,

the sum over the no-attack labellings with the special values `σ` prescribed below the level, each
weighted by `q` to the number of attacking pairs it inverts and by its full labelling monomial.

The sum has infinitely many terms — `U(π, σ)` is infinite, the letters being unbounded — and is
nevertheless an element of `P_k`, so it is given one coefficient at a time, as
`HJO.Dyck.partialCharSeries` is. By `HJO.Sym.zmon_eq_monomial` the labelling monomial is a
*monomial* of `P_k`, with alphabet exponent `HJO.Sym.zmonExponent` and coefficient
`HJO.Sym.zmonCoeff`, so only the labellings with a prescribed `zmonExponent` contribute to a
prescribed monomial of the alphabet, and by `HJO.Dyck.mem_zmonLetters` there are finitely many of
those. That finite sum *is* the definition here, and
`HJO.Dyck.coeff_unnormalisedCharSeries_eq_coeff_sum` is the identification with the display. -/
@[hjo "def_cm_chiprime"]
noncomputable def unnormalisedCharSeries (q : K) (k : ℕ) {N : ℕ} (x : Fin N → ℕ) (σ : Fin k → ℕ) :
    AuxAlphabetSeries K k := fun e =>
  ∑ w ∈ {w ∈ Fintype.piFinset fun _ : Fin N => zmonLetters k e |
      w ∈ noAttackLabellings x σ ∧ zmonExponent k w = e},
    q ^ #(invSet (finPairs N (attackSet x)) w) • zmonCoeff K k w

variable {q : K} {x : Fin N → ℕ} {σ : Fin k → ℕ} {e : ℕ →₀ ℕ}

/-- **The defining property of `χ'_σ(π)`**: the coefficient of the monomial with alphabet exponent
`e` is the finite sum of `q ^ inv(At(π), w) · z^{(k)}_w` over the no-attack labellings `w` whose
monomial has that exponent, the `𝕜[y]`-part of that monomial being the summand's coefficient. -/
theorem coeff_unnormalisedCharSeries :
    MvPowerSeries.coeff e (unnormalisedCharSeries q k x σ) =
      ∑ w ∈ {w ∈ Fintype.piFinset fun _ : Fin N => zmonLetters k e |
          w ∈ noAttackLabellings x σ ∧ zmonExponent k w = e},
        q ^ #(invSet (finPairs N (attackSet x)) w) • zmonCoeff K k w :=
  MvPowerSeries.coeff_apply _ _

/-- The coefficient of `x^e` with the labellings summed over cut out of the tuples with letters in
any finite set containing `HJO.Dyck.zmonLetters`: the form in which a bound on the letters is chosen
freely. -/
theorem coeff_unnormalisedCharSeries_of_subset {s : Finset ℕ} (hs : zmonLetters k e ⊆ s) :
    MvPowerSeries.coeff e (unnormalisedCharSeries q k x σ) =
      ∑ w ∈ {w ∈ Fintype.piFinset fun _ : Fin N => s |
          w ∈ noAttackLabellings x σ ∧ zmonExponent k w = e},
        q ^ #(invSet (finPairs N (attackSet x)) w) • zmonCoeff K k w := by
  rw [coeff_unnormalisedCharSeries]
  refine Finset.sum_congr (Finset.ext fun w => ?_) fun _ _ => rfl
  simp only [Finset.mem_filter, Fintype.mem_piFinset]
  exact ⟨fun ⟨_, h⟩ => ⟨fun i => hs (mem_zmonLetters h.2 i), h⟩,
    fun ⟨_, h⟩ => ⟨fun i => mem_zmonLetters h.2 i, h⟩⟩

/-- **`χ'_σ(π)` is the sum** `∑_{w ∈ U(π,σ)} q ^ inv(At(π), w) z^{(k)}_w`: on the monomials with
alphabet exponent `e`, the series agrees with the honest *finite* sum of
`q ^ inv(At(π), w) · z^{(k)}_w` over the no-attack labellings with letters in any finite set
containing `HJO.Dyck.zmonLetters k e`. Every exponent is covered by some such set, so this
determines `χ'_σ(π)` and identifies it with the displayed series; the sum over *all* of `U(π, σ)`
cannot be formed in `P_k`, which is why the definition is coefficientwise. -/
theorem coeff_unnormalisedCharSeries_eq_coeff_sum {s : Finset ℕ} (hs : zmonLetters k e ⊆ s) :
    MvPowerSeries.coeff e (unnormalisedCharSeries q k x σ) =
      MvPowerSeries.coeff e (∑ w ∈ {w ∈ Fintype.piFinset fun _ : Fin N => s |
          w ∈ noAttackLabellings x σ},
        q ^ #(invSet (finPairs N (attackSet x)) w) • zmon K k w) := by
  rw [coeff_unnormalisedCharSeries_of_subset hs, map_sum]
  rw [show {w ∈ Fintype.piFinset fun _ : Fin N => s |
        w ∈ noAttackLabellings x σ ∧ zmonExponent k w = e}
      = {w ∈ {w ∈ Fintype.piFinset fun _ : Fin N => s | w ∈ noAttackLabellings x σ} |
        zmonExponent k w = e} from Finset.ext fun w => by
      simp only [Finset.mem_filter]; tauto, Finset.sum_filter]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [show MvPowerSeries.coeff e (q ^ #(invSet (finPairs N (attackSet x)) w) • zmon K k w)
      = q ^ #(invSet (finPairs N (attackSet x)) w) • MvPowerSeries.coeff e (zmon K k w) from rfl,
    coeff_zmon]
  by_cases hw : e = zmonExponent k w
  · simp [hw]
  · simp [hw, Ne.symm hw]

end HJO.Dyck
