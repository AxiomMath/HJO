/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.SignExtraction.Defs
public meta import HJO.Attr

/-! # The monomial of a word

The characteristic function of the Carlsson--Mellit recursion is a sum, over the words `w`
compatible with an attack set, of `q ^ inv(R, w)` times the monomial `x_w = x_{w_1} ⋯ x_{w_n}` of
the word. This file fixes that monomial and the four things the `χ` combinatorics reads off it: it
is the monomial at the word's exponent vector, so it sees the word only through the multiset of its
letters; it is multiplicative under concatenation; it is invariant under reindexing the positions;
and it factors over a set of positions and its complement.

## Main definitions

* `HJO.Sym.wordMonomial`: the monomial `x_w` of a word `w`, in the alphabet power series ring.

## Main results

* `HJO.Sym.wordMonomial_eq_monomial`, `HJO.Sym.coeff_wordMonomial`: `x_w = x ^ 𝐝(w)` with
  coefficient `1`, and the coefficients are the indicator of the exponent vector.
* `HJO.Sym.wordMonomial_eq_of_wordExponent_eq`, `HJO.Sym.wordExponent_eq_of_wordMonomial_eq`: the
  monomial and the exponent vector determine each other.
* `HJO.Sym.wordMonomial_comp_equiv`, `HJO.Sym.wordMonomial_append`,
  `HJO.Sym.wordMonomial_eq_prod_mul_prod_compl`: reindexing, concatenation and factoring.

## Implementation notes

The ambient ring is `HJO.Sym.AlphabetSeries K = K⟦x₀, x₁, …⟧`, the library's alphabet power
series ring, and not a polynomial ring: the power series ring is where the Gessel functions and the
characteristic functions both live, and `HJO.Dyck.charSeries_eq_sum_gessel` equates two elements of
it.

The alphabet is indexed from `0` and the positions are `0`-based, so Carlsson--Mellit's
`x_w = x_{w_1} ⋯ x_{w_n}` for `w ∈ ℤ_{>0}ⁿ` is the product over `k : Fin n` of `X (w k)`; no
positivity is imposed on a letter, matching `HJO.Sym.AlphabetSeries` and
`HJO.ParkingFunctions.gessel`, which likewise do not.

The definition is the product rather than `MvPowerSeries.monomial (wordExponent w) 1`, because the
product is what a consumer splitting a word into blocks manipulates;
`wordMonomial_eq_monomial` is the other reading and is proved by induction on the length.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, §2.3: "For any infinite set of
variables `X = {x₁, x₂, …}`, let `x_w = x_{w_1} ⋯ x_{w_n}`". Consumed by `HJO.Dyck.charSeries`,
`HJO.Dyck.letterPerm_swap_charSeries`, `HJO.Dyck.charSeries_eq_sum_gessel`,
`HJO.ParkingFunctions.coeff_wordExponent_minAscendingWord_gessel` and the negation and superalphabet
lemmas.
-/

@[expose] public section

open Finset

namespace HJO.Sym

/-- `x_w`, the monomial of the word `w`: the product `x_{w 0} ⋯ x_{w (n-1)}` of the letters `w`
names, taken with multiplicity, inside the formal power series `AlphabetSeries K = K⟦x₀, x₁, …⟧`
in the alphabet. The alphabet being indexed from `0` and the positions being `0`-based, this is
Carlsson--Mellit's `x_w = x_{w_1} ⋯ x_{w_n}` for `w ∈ ℤ_{>0}ⁿ`. It depends on `w` only through the
exponent vector `wordExponent w`, so it is a monomial with coefficient `1`, of total degree `n`,
and words that are rearrangements of one another have the same monomial. -/
@[hjo "def_dyck_monomial"]
noncomputable def wordMonomial (K : Type*) [CommRing K] {n : ℕ} (w : Fin n → ℕ) :
    AlphabetSeries K :=
  ∏ k, MvPowerSeries.X (w k)

variable {K : Type*} [CommRing K]

/-- **The monomial of a word is the monomial at its exponent vector**: `x_w = x ^ 𝐝(w)`, with
coefficient `1`. This is the description a reader uses in place of the product. -/
theorem wordMonomial_eq_monomial {n : ℕ} (w : Fin n → ℕ) :
    wordMonomial K w = MvPowerSeries.monomial (wordExponent w) 1 := by
  unfold wordMonomial wordExponent
  induction n with
  | zero => simp
  | succ N ih =>
    rw [Fin.prod_univ_succ, Fin.sum_univ_succ, ih, MvPowerSeries.X,
      MvPowerSeries.monomial_mul_monomial, one_mul]

/-- The coefficients of `x_w` are the indicator of its exponent vector: `[x^d] x_w` is `1` when
`d = 𝐝(w)` and `0` otherwise. -/
theorem coeff_wordMonomial {n : ℕ} (w : Fin n → ℕ) (d : ℕ →₀ ℕ) :
    MvPowerSeries.coeff d (wordMonomial K w) = if d = wordExponent w then 1 else 0 := by
  rw [wordMonomial_eq_monomial, MvPowerSeries.coeff_monomial]

/-- Words with the same multiset of letters have the same monomial: rearranging a word, or
padding two words of different lengths to the same letters, does not change `x_w`. -/
theorem wordMonomial_eq_of_wordExponent_eq {m n : ℕ} {v : Fin m → ℕ} {w : Fin n → ℕ}
    (h : wordExponent v = wordExponent w) : wordMonomial K v = wordMonomial K w := by
  rw [wordMonomial_eq_monomial, wordMonomial_eq_monomial, h]

/-- The monomial of a word determines the multiset of its letters, hence its length: two words,
of possibly different lengths, with the same monomial have the same exponent vector. This is why
a monomial of total degree `n` is `x_w` for only finitely many words `w`, the rearrangements of
one of them. -/
theorem wordExponent_eq_of_wordMonomial_eq [Nontrivial K] {m n : ℕ} {v : Fin m → ℕ}
    {w : Fin n → ℕ} (h : wordMonomial K v = wordMonomial K w) :
    wordExponent v = wordExponent w := by
  by_contra hne
  have h1 : MvPowerSeries.coeff (wordExponent v) (wordMonomial K v) = 1 := by
    simp [coeff_wordMonomial]
  have h2 : MvPowerSeries.coeff (wordExponent v) (wordMonomial K w) = 0 := by
    simp [coeff_wordMonomial, hne]
  rw [h, h2] at h1
  exact zero_ne_one h1

/-- **Reindexing the positions does not change the monomial**: `x_{w ∘ e} = x_w` for a bijection
`e` of the positions. This is the form in which `x_w` is read as `x_{a_1} ⋯ x_{a_n}` for
`a_r = w_{σ⁻¹ r}` when summing over the words standardising to a permutation `σ`, and in which
reversing a word is seen to fix its monomial, the two products having the same factors in the
reverse order. -/
theorem wordMonomial_comp_equiv {m n : ℕ} (e : Fin m ≃ Fin n) (w : Fin n → ℕ) :
    wordMonomial K (w ∘ e) = wordMonomial K w :=
  Fintype.prod_equiv e _ _ fun _ => rfl

/-- Concatenating words multiplies their monomials: `x_{vw} = x_v x_w`. -/
theorem wordMonomial_append {m n : ℕ} (v : Fin m → ℕ) (w : Fin n → ℕ) :
    wordMonomial K (Fin.append v w) = wordMonomial K v * wordMonomial K w := by
  rw [wordMonomial, wordMonomial, wordMonomial, Fin.prod_univ_add]
  simp

/-- `x_w` factors over any set of positions and its complement: the letters at the positions of
`s` and the letters at the remaining positions. This is the form in which the letters lying in a
two-element window are separated from the letters outside it. -/
theorem wordMonomial_eq_prod_mul_prod_compl {n : ℕ} (w : Fin n → ℕ) (s : Finset (Fin n)) :
    wordMonomial K w =
      (∏ k ∈ s, MvPowerSeries.X (w k)) * ∏ k ∈ sᶜ, MvPowerSeries.X (w k) :=
  (prod_mul_prod_compl s fun k => MvPowerSeries.X (w k)).symm

end HJO.Sym
