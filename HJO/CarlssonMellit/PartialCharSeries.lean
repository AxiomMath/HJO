/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.NoAttack
public import HJO.CarlssonMellit.TwoLetterChar
public import HJO.CarlssonMellit.ZTail
public meta import HJO.Attr

/-! # The characteristic series of a partial Dyck path

The definition `HJO.Dyck.partialCharSeries`: for a partial Dyck path `π ∈ 𝔻_{k,N}` and a tuple `σ`
of special values,

`ν_σ(π) = ∑_{w ∈ U(π,σ)} q ^ inv(At(π), w) · z^{(k)}_{w,♭} ∈ P_k`,

the sum over the no-attack labellings of `HJO.Dyck.noAttackLabellings` of `q` to the inversion
number times the free part `HJO.Sym.ztail` of the labelling monomial. This is the object the
character recursion of Carlsson and Mellit's Section 4 is stated at, and the one every step of that
recursion computes.

The sum is infinite and its value is a power series, so — as for `HJO.Dyck.markedCharSeries` — it is
built one coefficient at a time. What makes that possible is that the free part of a labelling is a
*monomial* of `P_k` (`HJO.Sym.ztail_eq_monomial`): its exponent in the alphabet is
`HJO.Sym.ztailExponent` and its coefficient in `𝕜[y_1, …, y_k]` is `HJO.Sym.ztailCoeff`, so a given
monomial of the alphabet receives contributions only from the labellings with a given
`ztailExponent`, and `HJO.Dyck.nuLetters` bounds their letters to a finite set.

## Main definitions

* `HJO.Dyck.nuLetters`: the finite set of letters a labelling contributing to a given coefficient
  can carry.
* `HJO.Dyck.partialCharSeries`: `ν_σ(π)`.

## Main results

The definition is used through these, not by unfolding it.

* `HJO.Dyck.coeff_partialCharSeries`: the coefficient of a monomial, the defining property.
* `HJO.Dyck.coeff_partialCharSeries_of_subset`: the same with the letters bounded by any finite set
  containing `nuLetters`.
* `HJO.Dyck.coeff_partialCharSeries_eq_coeff_sum`: `ν_σ(π)` is the displayed sum of the
  monomials `HJO.Sym.ztail`, restricted to the no-attack labellings.
* `HJO.Dyck.partialCharSeries_of_isEmpty`: the empty path has `ν_σ(π) = 1`.

## Implementation notes

*The weight `q` lives in the base ring `K` and not in the coefficients.* The `q` is an
element of `𝕜` and `P_k = 𝕜[y_1, …, y_k]⟦x_1, x_2, …⟧`, so `q` acts on the coefficients by the
`K`-algebra structure of `MvPolynomial (Fin k) K`, which is what the scalar multiplication in the
definition is.

*Positions and letters are indexed from `0`*, so the positions `1, …, k` below the level
are the positions `i` of `Fin N` with `i < k`, and its `z^{(k)}_{w_i}` is `HJO.Sym.zvar K k (w i)`.

*No hypothesis on `x`, on `σ`, or on `k ≤ N`.* The series reads `x` only through `At(π)` and `σ`
only through the prescription at the positions below the level, so being a partial Dyck path and
having pairwise distinct special values are hypotheses of the lemmas, not of the definition. At
`N < k` the free part is the empty product and every labelling is prescribed, so the series
degenerates rather than being ill-formed.

*The inversion set is formed at pairs of `Fin N`*, through `HJO.Dyck.finPairs`, as it is for
`HJO.Dyck.markedCharSeries`: the labelling is a tuple and the attack set is a `Finset (ℕ × ℕ)`.

## References

The definition `HJO.Dyck.partialCharSeries`, using `HJO.Dyck.attackSet`, `HJO.Dyck.invNumber`,
`HJO.Sym.AuxAlphabetSeries`, `HJO.Dyck.IsPartialDyck`, `HJO.Sym.ztail` and
`HJO.Dyck.noAttackLabellings`. Transcribing E. Carlsson and A. Mellit, *A proof of the shuffle
conjecture*, J. Amer. Math. Soc. **31** (2018) 661--697, Section 4, where the series is `χ'_σ(π)`
with its special factors `y_1 ⋯ y_k` divided out. Consumed by `HJO.Dyck.IsSigmaCharacter`,
`HJO.Dyck.isSigmaCharacter_one_of_isEmpty`, `HJO.Dyck.isSigmaCharacter_cmDPlus` and
`HJO.Dyck.isSigmaCharacter_dminusCM'`.
-/

@[expose] public section

open Finset HJO.Sym

namespace HJO.Dyck

variable {K : Type*} [CommRing K] {N k : ℕ}

/-! ### The letters a contributing labelling can carry -/

/-- The letters available to a labelling that contributes to the coefficient of the monomial `x^e`
in `ν_σ(π)`: the letters below the level `k`, which name auxiliary variables and so leave no trace
in `e`; the letters `j + k` for `j` in the support of `e`, which name the letters of the alphabet
that `e` records; and the letters `σ` prescribes at the positions below the level.

This is a *finite* set, and `HJO.Dyck.mem_nuLetters_of_mem_noAttackLabellings` shows every
contributing labelling takes its letters in it. That is what cuts a finite index set out of the
infinite `U(π, σ)`, one coefficient at a time. -/
def nuLetters (k : ℕ) (e : ℕ →₀ ℕ) (σ : Fin k → ℕ) : Finset ℕ :=
  Finset.range k ∪ e.support.image (· + k) ∪ Finset.univ.image σ

/-- **Every labelling contributing to the coefficient of `x^e` takes its letters in
`HJO.Dyck.nuLetters`.** At a position below the level the letter is prescribed by `σ`. At a position
at or above the level the letter is either below the level, or else it contributes the exponent
`single (w_i - k) 1` to `ztailExponent k w = e`, so `w_i - k` lies in the support of `e`. -/
theorem mem_nuLetters_of_mem_noAttackLabellings {x : Fin N → ℕ} {σ : Fin k → ℕ} {w : Fin N → ℕ}
    {e : ℕ →₀ ℕ} (hw : w ∈ noAttackLabellings x σ) (he : ztailExponent k w = e) (i : Fin N) :
    w i ∈ nuLetters k e σ := by
  by_cases hik : (i : ℕ) < k
  · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨⟨(i : ℕ), hik⟩, Finset.mem_univ _,
      (eq_of_mem_noAttackLabellings hw (j := ⟨(i : ℕ), hik⟩) rfl).symm⟩)
  refine Finset.mem_union_left _ ?_
  by_cases hwi : w i < k
  · exact Finset.mem_union_left _ (Finset.mem_range.2 hwi)
  refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨w i - k, ?_, by omega⟩)
  have hiF : i ∈ ({l : Fin N | k ≤ (l : ℕ)} : Finset (Fin N)) := mem_filter_univ i |>.2 (by omega)
  have hval : (1 : ℕ) ≤ e (w i - k) := by
    rw [← he, ztailExponent, Finsupp.finsetSum_apply]
    refine le_trans ?_ (Finset.single_le_sum
      (f := fun l => zvarExponent k (w l) (w i - k)) (fun _ _ => Nat.zero_le _) hiF)
    simp only [zvarExponent, hwi, ↓reduceIte, Finsupp.single_eq_same, le_refl]
  exact Finsupp.mem_support_iff.2 (by omega)

/-! ### The characteristic series of a partial Dyck path -/

/-- **The characteristic series `ν_σ(π)` of a partial Dyck path**, namely

`ν_σ(π) = ∑_{w ∈ U(π,σ)} q ^ inv(At(π), w) · z^{(k)}_{w,♭} ∈ P_k`,

the sum over the no-attack labellings with the special values `σ` prescribed below the level, each
weighted by `q` to the number of attacking pairs it inverts and by the free part of its labelling
monomial.

The sum has infinitely many terms — `U(π, σ)` is infinite, the letters being unbounded — and is
nevertheless an element of `P_k`, so it is given one coefficient at a time, as
`HJO.Dyck.markedCharSeries` is. By `HJO.Sym.ztail_eq_monomial` the free part of a labelling is a
*monomial* of `P_k`, with alphabet exponent `HJO.Sym.ztailExponent` and coefficient
`HJO.Sym.ztailCoeff` in `𝕜[y_1, …, y_k]`, so only the labellings with a prescribed `ztailExponent`
contribute to a prescribed monomial of the alphabet, and by
`HJO.Dyck.mem_nuLetters_of_mem_noAttackLabellings` there are finitely many of those. That finite sum
*is* the definition here, and
`HJO.Dyck.coeff_partialCharSeries_eq_coeff_sum` is the identification with the display.

Carlsson and Mellit's `χ'_σ(π)` is this series with the first `k` factors
`z^{(k)}_{σ_1} ⋯ z^{(k)}_{σ_k}` retained; for a `σ` permuting `{1, …, k}` those are `y_1 ⋯ y_k` for
every labelling, so `χ'_σ(π) = y_1 ⋯ y_k · ν_σ(π)`, and dividing them out here avoids having to
prove a divisibility.

No hypothesis is imposed on `x`, on `σ` or on `k ≤ N`: the sum reads `x` only through its attack set
and `σ` only through the prescription, so that `π ∈ 𝔻_{k,N}` and the pairwise distinctness of `σ`
are hypotheses of the *lemmas* about `ν_σ(π)`, and `HJO.Dyck.noAttackLabellings` is likewise defined
without them. -/
@[hjo "def_cm_nu"]
noncomputable def partialCharSeries (q : K) (k : ℕ) {N : ℕ} (x : Fin N → ℕ) (σ : Fin k → ℕ) :
    AuxAlphabetSeries K k := fun e =>
  ∑ w ∈ {w ∈ Fintype.piFinset fun _ : Fin N => nuLetters k e σ |
      w ∈ noAttackLabellings x σ ∧ ztailExponent k w = e},
    q ^ #(invSet (finPairs N (attackSet x)) w) • ztailCoeff K k w

variable {q : K} {x : Fin N → ℕ} {σ : Fin k → ℕ} {e : ℕ →₀ ℕ}

/-- **The defining property of `ν_σ(π)`**: the coefficient of the monomial with alphabet exponent
`e` is the finite sum of `q ^ inv(At(π), w) · z^{(k)}_{w,♭}` over the no-attack labellings `w` whose
free part has that exponent, the `𝕜[y]`-part of the free part being the summand's coefficient. -/
theorem coeff_partialCharSeries :
    MvPowerSeries.coeff e (partialCharSeries q k x σ) =
      ∑ w ∈ {w ∈ Fintype.piFinset fun _ : Fin N => nuLetters k e σ |
          w ∈ noAttackLabellings x σ ∧ ztailExponent k w = e},
        q ^ #(invSet (finPairs N (attackSet x)) w) • ztailCoeff K k w :=
  MvPowerSeries.coeff_apply _ _

/-- The coefficient of `x^e` with the labellings summed over cut out of the tuples with letters in
any finite set containing `HJO.Dyck.nuLetters`: the form in which a bound on the letters is chosen
freely. -/
theorem coeff_partialCharSeries_of_subset {s : Finset ℕ} (hs : nuLetters k e σ ⊆ s) :
    MvPowerSeries.coeff e (partialCharSeries q k x σ) =
      ∑ w ∈ {w ∈ Fintype.piFinset fun _ : Fin N => s |
          w ∈ noAttackLabellings x σ ∧ ztailExponent k w = e},
        q ^ #(invSet (finPairs N (attackSet x)) w) • ztailCoeff K k w := by
  rw [coeff_partialCharSeries]
  refine Finset.sum_congr (Finset.ext fun w => ?_) fun _ _ => rfl
  simp only [Finset.mem_filter, Fintype.mem_piFinset]
  exact ⟨fun ⟨_, h⟩ => ⟨fun i => hs (mem_nuLetters_of_mem_noAttackLabellings h.1 h.2 i), h⟩,
    fun ⟨_, h⟩ => ⟨fun i => mem_nuLetters_of_mem_noAttackLabellings h.1 h.2 i, h⟩⟩

/-- **`ν_σ(π)` is the sum** `∑_{w ∈ U(π,σ)} q ^ inv(At(π), w) z^{(k)}_{w,♭}`: on the
monomials with alphabet exponent `e`, the series agrees with the honest *finite* sum of
`q ^ inv(At(π), w) · z^{(k)}_{w,♭}` over the no-attack labellings with letters in any finite set
containing `HJO.Dyck.nuLetters k e σ`. Every exponent is covered by some such set, so this
determines `ν_σ(π)` and identifies it with the displayed series; the sum over *all* of
`U(π, σ)` cannot be formed in `P_k`, which is why the definition is coefficientwise. -/
theorem coeff_partialCharSeries_eq_coeff_sum {s : Finset ℕ} (hs : nuLetters k e σ ⊆ s) :
    MvPowerSeries.coeff e (partialCharSeries q k x σ) =
      MvPowerSeries.coeff e (∑ w ∈ {w ∈ Fintype.piFinset fun _ : Fin N => s |
          w ∈ noAttackLabellings x σ},
        q ^ #(invSet (finPairs N (attackSet x)) w) • ztail K k w) := by
  rw [coeff_partialCharSeries_of_subset hs, map_sum]
  rw [show {w ∈ Fintype.piFinset fun _ : Fin N => s |
        w ∈ noAttackLabellings x σ ∧ ztailExponent k w = e}
      = {w ∈ {w ∈ Fintype.piFinset fun _ : Fin N => s | w ∈ noAttackLabellings x σ} |
        ztailExponent k w = e} from Finset.ext fun w => by
      simp only [Finset.mem_filter]; tauto, Finset.sum_filter]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [show MvPowerSeries.coeff e (q ^ #(invSet (finPairs N (attackSet x)) w) • ztail K k w)
      = q ^ #(invSet (finPairs N (attackSet x)) w) • MvPowerSeries.coeff e (ztail K k w) from rfl,
    coeff_ztail]
  by_cases hw : e = ztailExponent k w
  · simp [hw]
  · simp [hw, Ne.symm hw]

/-- **The empty path has characteristic series `1`.** At length `0` there is a single labelling, the
empty tuple; it inverts nothing, there being no attacking pairs, and its free part is the empty
product. So every coefficient of `ν_σ(π)` is the coefficient of `1`. This is the value
`HJO.Dyck.isSigmaCharacter_one_of_isEmpty` reads. -/
theorem partialCharSeries_of_isEmpty (q : K) (k : ℕ) (x : Fin 0 → ℕ) (σ : Fin k → ℕ) :
    partialCharSeries q k x σ = 1 := by
  refine MvPowerSeries.ext fun e => ?_
  rw [coeff_partialCharSeries]
  have hone : ∀ w : Fin 0 → ℕ,
      q ^ #(invSet (finPairs 0 (attackSet x)) w) • ztailCoeff K k w =
        (1 : MvPolynomial (Fin k) K) := by
    intro w
    have h1 : invSet (finPairs 0 (attackSet x)) w = ∅ := Finset.eq_empty_of_isEmpty _
    have h2 : ztailCoeff K k w = 1 := Finset.prod_eq_one fun i _ => absurd i.isLt (by omega)
    rw [h1, h2, Finset.card_empty, pow_zero, one_smul]
  by_cases he : e = 0
  · subst he
    rw [show {w ∈ Fintype.piFinset fun _ : Fin 0 => nuLetters k (0 : ℕ →₀ ℕ) σ |
          w ∈ noAttackLabellings x σ ∧ ztailExponent k w = 0}
        = {(fun i => isEmptyElim i : Fin 0 → ℕ)} from Finset.ext fun w => by
        simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_singleton]
        refine ⟨fun _ => funext fun i => absurd i.isLt (by omega), fun _ => ?_⟩
        refine ⟨fun i => absurd i.isLt (by omega), ⟨fun i j _ => absurd i.isLt (by omega),
          fun i j _ => absurd i.isLt (by omega)⟩, ?_⟩
        exact Finset.sum_eq_zero fun i _ => absurd i.isLt (by omega),
      Finset.sum_singleton, hone]
    simp [MvPowerSeries.coeff_one]
  · rw [show {w ∈ Fintype.piFinset fun _ : Fin 0 => nuLetters k e σ |
          w ∈ noAttackLabellings x σ ∧ ztailExponent k w = e} = ∅ from
        Finset.eq_empty_of_forall_notMem fun w hw => ?_, Finset.sum_empty]
    · rw [MvPowerSeries.coeff_one]
      simp only [he, ↓reduceIte]
    · refine he ?_
      rw [← (Finset.mem_filter.1 hw).2.2, ztailExponent]
      exact Finset.sum_eq_zero fun i _ => absurd i.isLt (by omega)

end HJO.Dyck
