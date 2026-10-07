/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import HJO.Symmetric.SymmetricFunctions
public import HJO.Symmetric.RealisationReverse
public import HJO.Macdonald.Inversion
public meta import HJO.Attr

/-! # The standard involution, the negation of the letters, and conjugation of descent sets

Three ingredients of the theory of `ω`: the classical involution `ω` of `Λ`, the substitution `ng`
negating every letter of the alphabet, and the injectivity of `S ↦ (\{1,…,n-1\} ∖ S)^{∨n}`.

## Main definitions

* `HJO.Sym.omegaStd`: `ω`, the `K`-algebra endomorphism of `Λ` with `ω(p_k) = (-1)^{k-1}p_k`.
* `HJO.Sym.letterNegate`: `ng`, the `K`-algebra endomorphism of `𝒫` with `ng(x_i) = -x_i`.

## Main statements

* `HJO.Sym.omegaStd_omegaStd`: `ω` is an involution.
* `HJO.ParkingFunctions.descentReverse_sdiff_injective`: the injectivity of
  `S ↦ (\{1,…,n-1\} ∖ S)^{∨n}`.

## Implementation notes

`ω` is *not* `HJO.Sym.signExtract`, which sends `p_k` to the scalar `(-1)^{k-1}`, and it is *not*
`HJO.Sym.plethNegate` (`ω₋`), which sends `p_k` to `-p_k`. The three are distinguished by their
values on `p_2`: `1`, `-p_2` and `p_2` respectively.

It *is* the untwisted case of `HJO.Sym.inversion`, Garsia--Haiman--Tesler's `↓`, which carries the
same sign on the power sums but twists the coefficients by a ring endomorphism `ι` and is therefore
only a `RingHom`. `omegaStd_coe_ringHom` records that identification, so the two are one map and no
second copy of the involution can drift: what `omegaStd` adds is the `K`-algebra structure `ω` is
stated with, available exactly because `ι` is the identity here.

`Λ = MvPolynomial ℕ K` is free on the power sums, so `ω` is `MvPolynomial.aeval`, with no
well-definedness to prove. The index shift is this library's convention: `powerSum K (i+1) = X i`,
so `ω(X i) = (-1)^i X i`.

`ng` is not free in the same way — `𝒫` is a power series ring and the values on the letters do not
determine an endomorphism, exactly as `HJO.Shuffle.LetterReversal` records for `tr_m` and
`rv_m`. The intended map is the substitution acting monomial-wise, which is
`MvPowerSeries.rescaleAlgHom` at the constant family `-1`; `coeff_letterNegate` is then the
usual description, "multiplies the coefficient of each monomial of total degree `d` by
`(-1)^d`", and `letterNegate_X` recovers the clause on the letters.

## References

This file concerns `HJO.Sym.omegaStd`, `HJO.Sym.letterNegate` and
`HJO.ParkingFunctions.descentReverse_sdiff_injective`.
-/

@[expose] public section

open Finset

namespace HJO.Sym

/-! ### The standard involution of `Λ` -/

/-- **The standard involution** `ω`, the `K`-algebra endomorphism of `Λ`
sending `p_k` to `(-1)^{k-1}p_k`. `Λ` is the polynomial ring on the power sums, so this is an
`aeval` and there is nothing to check. -/
@[hjo "def_omega_standard"]
noncomputable def omegaStd (K : Type*) [CommRing K] : Lambda K →ₐ[K] Lambda K :=
  MvPolynomial.aeval fun i => ((-1 : Lambda K) ^ i * MvPolynomial.X i)

/-- **The defining property of `ω`**: it multiplies `p_k` by `(-1)^{k-1}`. -/
@[hjo "def_omega_standard"]
theorem omegaStd_powerSum (K : Type*) [CommRing K] {k : ℕ} (hk : 0 < k) :
    omegaStd K (powerSum K k) = (-1) ^ (k - 1) * powerSum K k := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [powerSum, Nat.add_sub_cancel, omegaStd, MvPolynomial.aeval_X]

/-- **`ω` is the untwisted inversion.** `HJO.Sym.inversion` at `ι = id` is the same map, read as a
`RingHom`: `↓` is `ω` composed with the inversion of the parameters, and with no parameters left to
invert what remains is `ω`. -/
theorem omegaStd_coe_ringHom (K : Type*) [CommRing K] :
    ((omegaStd K : Lambda K →ₐ[K] Lambda K) : Lambda K →+* Lambda K)
      = inversion (RingHom.id K) := by
  refine MvPolynomial.ringHom_ext (fun a => ?_) fun i => ?_
  · simp [omegaStd]
  · simp [omegaStd]

/-- **`ω` is an involution**, as its name says: each `p_k` is multiplied
twice by the same sign. -/
theorem omegaStd_omegaStd (K : Type*) [CommRing K] (f : Lambda K) :
    omegaStd K (omegaStd K f) = f := by
  have : (omegaStd K).comp (omegaStd K) = AlgHom.id K (Lambda K) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    rw [AlgHom.comp_apply, omegaStd, MvPolynomial.aeval_X, map_mul, map_pow, map_neg, map_one,
      MvPolynomial.aeval_X, ← mul_assoc, ← mul_pow, neg_mul_neg, one_mul, one_pow, one_mul,
      AlgHom.id_apply]
  exact congrArg (fun φ => φ f) this

/-- `ω` is not sign extraction: `ε(p_2) = -1`, a scalar, while `ω(p_2) = -p_2`. The two are
confusable because both carry the sign `(-1)^{k-1}`, and this separates them. -/
theorem omegaStd_powerSum_two (K : Type*) [CommRing K] :
    omegaStd K (powerSum K 2) = -powerSum K 2 := by
  rw [omegaStd_powerSum K two_pos]
  norm_num

/-! ### Negating the letters of the alphabet -/

/-- **Negating the letters.** `ng` is the `K`-algebra endomorphism of `𝒫`
substituting `-x_i` for each `x_i`, i.e. rescaling every variable by `-1`. -/
@[hjo "def_letter_negation"]
noncomputable def letterNegate (K : Type*) [CommRing K] :
    AlphabetSeries K →ₐ[K] AlphabetSeries K :=
  MvPowerSeries.rescaleAlgHom fun _ => (-1 : K)

/-- **`ng` multiplies the coefficient of a monomial of total degree `d` by `(-1)^d`**, which is the
usual description of it. -/
@[hjo "def_letter_negation"]
theorem coeff_letterNegate {K : Type*} [CommRing K] (G : AlphabetSeries K) (d : ℕ →₀ ℕ) :
    MvPowerSeries.coeff d (letterNegate K G)
      = (-1) ^ (d.sum fun _ n => n) * MvPowerSeries.coeff d G := by
  rw [letterNegate, MvPowerSeries.rescaleAlgHom_apply, MvPowerSeries.coeff_rescale]
  congr 1
  rw [Finsupp.prod, Finsupp.sum, Finset.prod_pow_eq_pow_sum]

/-- **`ng(x_i) = -x_i`**, the clause defining it on the letters. -/
@[hjo "def_letter_negation"]
theorem letterNegate_X {K : Type*} [CommRing K] (i : ℕ) :
    letterNegate K (MvPowerSeries.X i) = -MvPowerSeries.X i := by
  refine MvPowerSeries.ext fun d => ?_
  rw [coeff_letterNegate, map_neg, MvPowerSeries.coeff_X]
  split_ifs with h
  · rw [h, Finsupp.sum_single_index rfl]
    norm_num
  · rw [mul_zero, neg_zero]

end HJO.Sym

namespace HJO.ParkingFunctions

/-- **Conjugating a descent set is injective.** Complementing
inside the window `\{1, …, n-1\}` and reflecting it are each involutions of the subsets of the
window, so their composite is too, and in particular injective. -/
@[hjo "lem_om_conjugate_descent_injective"]
theorem descentReverse_sdiff_injective {n : ℕ} {S S' : Finset ℕ} (hS : S ⊆ Ico 1 n)
    (hS' : S' ⊆ Ico 1 n)
    (h : descentReverse n (Ico 1 n \ S) = descentReverse n (Ico 1 n \ S')) : S = S' := by
  have hsub : ∀ T : Finset ℕ, Ico 1 n \ T ⊆ Iic n := fun T =>
    sdiff_subset.trans Ico_subset_Iic_self
  have hT : Ico 1 n \ S = Ico 1 n \ S' := by
    have h2 := congrArg (descentReverse n) h
    rwa [descentReverse_descentReverse (hsub S), descentReverse_descentReverse (hsub S')] at h2
  rw [← Finset.sdiff_sdiff_eq_self hS, ← Finset.sdiff_sdiff_eq_self hS', hT]

end HJO.ParkingFunctions
