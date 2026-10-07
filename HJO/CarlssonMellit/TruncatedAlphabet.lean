/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.PSwap
public import HJO.PlethysticAlphabet
public meta import HJO.Attr

/-! # The truncated alphabet

The closed formula for the iterated swapping coefficients evaluates the complete homogeneous
functions at the plethystic multiple `(1 - q)` of a *finite* alphabet: the letter `y_k` together
with the first `r` free variables. This file fixes that alphabet.

## Main definitions

* `HJO.Sym.truncLetter`: the letters `y_k, x_1, x_2, …` of the merged alphabet, in order.
* `HJO.Sym.truncatedAlphabet`: `X_{t-1}`, the alphabet of the first `t` of those letters.
* `HJO.Sym.pTruncatedAlphabet`: the same alphabet inside `P°_{k+1}`, with `y_k` and the letters of
  the alphabet for its letters.

## Main results

* `HJO.Sym.truncatedAlphabet_powerSum`, `HJO.Sym.truncatedAlphabet_succ_powerSum`: the power sums of
  `X_{t-1}`, and the recursion `X_r = X_{r-1} + x_r`.
* `HJO.Sym.truncatedAlphabet_zero_powerSum`,
  `HJO.Sym.completeHomog_truncatedAlphabet_zero_eq_zero`: `X_{-1}` is the empty alphabet, and
  `h_i[X_{-1}] = 0` for `i ≥ 1` — the value the telescoping argument needs.
* `HJO.Sym.completeHomog_eq_zero_of_powerSum_eq_zero`: an alphabet with no letters kills every
  complete homogeneous function of positive degree. This is the statement that makes `X_{-1} = 0`
  useful, and it applies to the twisted alphabet `(1 - q)X_{-1}` as well as to `X_{-1}` itself.
* `HJO.Sym.pTruncatedAlphabet_succ_powerSum`: the power sums of
  `X_r = y_k + x_1 + ⋯ + x_r` in `P°_{k+1}`.

## Implementation notes

*An alphabet is a ring homomorphism out of `Λ`, as everywhere in this library.* What an alphabet
is used for is the plethystic evaluation `f ↦ f[A]`, and that evaluation is determined by the images
of the power sums: the alphabet with letters `a_1, …, a_m` is the homomorphism sending `p_j` to
`a_1^j + ⋯ + a_m^j`. That is the shape `HJO.Sym.completeHomog_add_alphabet`,
`HJO.Sym.completeHomog_single_letter` and `HJO.Sym.completeHomog_dilate_letter` are stated in, so
nothing about plethysm has to be rebuilt here; the definition below is exactly that homomorphism for
the truncations of the list `y_k, x_1, x_2, …`, and the letters are arbitrary elements of an
arbitrary `K`-algebra, since no statement about them uses more.
`HJO.Sym.pTruncatedAlphabet` is the specialisation used, in
`P°_{k+1} = 𝕂(y_1, …, y_{k+1})⟦x_1, x_2, …⟧`, the ring whose graded part carries the swapping
operator.

*The index is shifted by one, and that is what the telescoping argument forces.* Stating
the truncated alphabet as one formula over `r ≥ -1` is contradictory — the
general expression gives `X_{-1} = y_k`, while `h_i[(1-q)X_{-1}]` has to vanish — so it takes the
two cases `X_{-1} = 0` and `X_r = y_k + x_1 + ⋯ + x_r`. Both cases are *one* formula in the shifted
index: `truncatedAlphabet y x t` is the alphabet of the first `t` letters of the list
`y_k, x_1, x_2, …`, so `t = 0` is the empty alphabet `X_{-1}` and `t = r + 1` is `X_r`. That is the
shape `HJO.Sym.zSwapCoeff_succ_eq_mul_completeHomog` needs — its right-hand side pairs `X_r` with
`X_{r-1}` at every `r ≥ 0`, including `r = 0` — and the shape in which
`HJO.Sym.one_sub_C_scalarFrac_mul_summableSum_zSwapCoeff` telescopes, the partial sum to `R` being
the difference of the values at `t = R + 1` and `t = 0`. Keeping a separate constant `0` for
`X_{-1}` beside a family indexed by `r ≥ 0` would make both of those statements a case split at
`r = 0`, which is precisely the reading to avoid.

*The empty alphabet is not the zero homomorphism.* A ring homomorphism sends `1` to `1`, so
`truncatedAlphabet y x 0` is not `0`; what the convention `X_{-1} := 0` says is that the alphabet
has no letters, that is that every power sum is sent to `0`, and the consequence the telescoping
uses is `completeHomog_eq_zero_of_powerSum_eq_zero`. That consequence is
`HJO.Sym.completeHomog_single_letter` at the letter `0`.

## References

E. Carlsson and A. Mellit, *A proof of the
shuffle conjecture*, J. Amer. Math. Soc. **31** (2018) 661--697, Section 4.
-/

@[expose] public section

open Finset

namespace HJO.Sym

/-! ### The letters of the truncated alphabet -/

/-- The letters of the merged alphabet `y_k, x_1, x_2, …`, listed in the order in which the
truncations read them: the distinguished letter `y` first, then the free variables. The free
variables are indexed from `0`, so `truncLetter y x (s + 1)` is the letter `x_{s+1}`. -/
def truncLetter {R : Type*} (y : R) (x : ℕ → R) : ℕ → R
  | 0 => y
  | s + 1 => x s

@[simp]
theorem truncLetter_zero {R : Type*} (y : R) (x : ℕ → R) : truncLetter y x 0 = y := rfl

@[simp]
theorem truncLetter_succ {R : Type*} (y : R) (x : ℕ → R) (s : ℕ) :
    truncLetter y x (s + 1) = x s := rfl

/-! ### The truncated alphabet -/

/-- **The truncated alphabet** `X_{t-1}`: the alphabet whose letters
are the first `t` letters of the list `y_k, x_1, x_2, …`, that is the homomorphism out of `Λ`
sending the power sum `p_j` to the sum of the `j`-th powers of those letters.

The index is shifted by one, so that the two cases are one formula: `t = 0` is the
*empty* alphabet `X_{-1} = 0`, whose power sums all vanish, and `t = r + 1` is
`X_r = y_k + x_1 + ⋯ + x_r`, so that `X_0 = y_k`. A single formula over
`r ≥ -1` is contradictory, the general expression giving `X_{-1} = y_k` while the telescoping
argument needs `h_i[(1-q)X_{-1}] = 0`; the shift is that reading, and it is the one in which
`HJO.Sym.zSwapCoeff_succ_eq_mul_completeHomog` pairs `X_r` with `X_{r-1}` at every `r ≥ 0` without a
case split. -/
@[hjo "def_cm_truncated_alphabet"]
noncomputable def truncatedAlphabet (K : Type*) [CommRing K] {R : Type*} [CommRing R] [Algebra K R]
    (y : R) (x : ℕ → R) (t : ℕ) : Lambda K →ₐ[K] R :=
  MvPolynomial.aeval fun i => ∑ s ∈ range t, truncLetter y x s ^ (i + 1)

variable {K : Type*} [CommRing K] {R : Type*} [CommRing R] [Algebra K R] (y : R) (x : ℕ → R)

/-- **The power sums of the truncated alphabet**: `p_j[X_{t-1}]` is the sum of the `j`-th powers of
the first `t` letters, which is what makes the homomorphism *be* that alphabet. -/
@[hjo "def_cm_truncated_alphabet"]
theorem truncatedAlphabet_powerSum (t : ℕ) {j : ℕ} (hj : 0 < j) :
    truncatedAlphabet K y x t (powerSum K j) = ∑ s ∈ range t, truncLetter y x s ^ j := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rw [CopPower.powerSum_succ, truncatedAlphabet, MvPolynomial.aeval_X]

/-- **`X_{-1}` is the empty alphabet**: every power sum vanishes on it. This is the
definition `X_{-1} := 0`, and not the vanishing of the homomorphism, which sends `1` to `1`. -/
@[hjo "def_cm_truncated_alphabet"]
theorem truncatedAlphabet_zero_powerSum {j : ℕ} (hj : 0 < j) :
    truncatedAlphabet K y x 0 (powerSum K j) = 0 := by
  rw [truncatedAlphabet_powerSum y x 0 hj, Finset.range_zero, Finset.sum_empty]

/-- **`X_0 = y_k`**: the alphabet of the first letter alone is the one-letter alphabet `y_k`, the
letter present unconditionally. -/
@[hjo "def_cm_truncated_alphabet"]
theorem truncatedAlphabet_one_powerSum {j : ℕ} (hj : 0 < j) :
    truncatedAlphabet K y x 1 (powerSum K j) = y ^ j := by
  rw [truncatedAlphabet_powerSum y x 1 hj, Finset.sum_range_one, truncLetter_zero]

/-- **`X_r = X_{r-1} + x_r`**: adjoining the next letter to a truncation adds its powers to the
power sums, which is the recursion the closed form of the swapping coefficients runs on. -/
@[hjo "def_cm_truncated_alphabet"]
theorem truncatedAlphabet_succ_powerSum (t : ℕ) {j : ℕ} (hj : 0 < j) :
    truncatedAlphabet K y x (t + 1) (powerSum K j)
      = truncatedAlphabet K y x t (powerSum K j) + truncLetter y x t ^ j := by
  rw [truncatedAlphabet_powerSum y x (t + 1) hj, truncatedAlphabet_powerSum y x t hj,
    Finset.sum_range_succ]

/-- **The `X_r = y_k + x_1 + ⋯ + x_r`**, read on the power sums: at the shifted index
`r + 1` the truncated alphabet is the letter `y` together with the first `r` free variables. -/
@[hjo "def_cm_truncated_alphabet"]
theorem truncatedAlphabet_succ_powerSum_eq (r : ℕ) {j : ℕ} (hj : 0 < j) :
    truncatedAlphabet K y x (r + 1) (powerSum K j) = y ^ j + ∑ s ∈ range r, x s ^ j := by
  rw [truncatedAlphabet_powerSum y x (r + 1) hj, Finset.sum_range_succ' _ r, truncLetter_zero,
    add_comm]
  exact congrArg _ (Finset.sum_congr rfl fun s _ => by rw [truncLetter_succ])

/-! ### An alphabet with no letters -/

section Empty

variable {K' : Type*} [CommRing K'] [Algebra ℚ K']

/-- **An alphabet with no letters kills every complete homogeneous function of positive degree.**
This is `HJO.Sym.completeHomog_single_letter` at the letter `0`: a homomorphism sending every
positive power sum to `0` sends `h_n` to `0 ^ n`. It is the fact the `X_{-1} := 0` is
chosen for — the telescoping of the swapping coefficients needs `h_i[(1-q)X_{-1}] = 0` for `i ≥ 1` —
and it applies to the twisted alphabet `(1-q)X_{-1}` as well as to `X_{-1}`, both sending every
positive power sum to `0`. -/
theorem completeHomog_eq_zero_of_powerSum_eq_zero {R' : Type*} [CommRing R'] {F : Type*}
    [FunLike F (Lambda K') R'] [RingHomClass F (Lambda K') R'] (φ : F)
    (h : ∀ j : ℕ, 0 < j → φ (powerSum K' j) = 0) {n : ℕ} (hn : 0 < n) :
    φ (completeHomog K' n) = 0 := by
  rw [completeHomog_single_letter φ 0 (fun j hj => by rw [h j hj, zero_pow (by omega)]) n,
    zero_pow (by omega)]

/-- **`h_i[X_{-1}] = 0` for `i ≥ 1`**: the empty alphabet has no complete homogeneous functions
beyond `h_0 = 1`. -/
@[hjo "def_cm_truncated_alphabet"]
theorem completeHomog_truncatedAlphabet_zero_eq_zero {R' : Type*} [CommRing R'] [Algebra K' R']
    (y' : R') (x' : ℕ → R') {i : ℕ} (hi : 0 < i) :
    truncatedAlphabet K' y' x' 0 (completeHomog K' i) = 0 :=
  completeHomog_eq_zero_of_powerSum_eq_zero _
    (fun _ hj => truncatedAlphabet_zero_powerSum y' x' hj) hi

end Empty

/-! ### The truncated alphabet of the Carlsson--Mellit series ring -/

/-- **The truncated alphabet inside `P°_{k+1}`**: the alphabet `X_{t-1}`, whose letters are the
last auxiliary variable `y_{k+1}` — the letter called `y_k` above, at this level — and the letters
`x_1, x_2, …` of the alphabet. This is the specialisation of `HJO.Sym.truncatedAlphabet` the
proof uses, in the ring whose graded part `P^gr_{k+1,d}` carries the swapping operator. -/
@[hjo "def_cm_truncated_alphabet"]
noncomputable def pTruncatedAlphabet (K : Type*) [CommRing K] (k t : ℕ) :
    Lambda K →ₐ[K] AuxAlphabetSeriesFrac K (k + 1) :=
  truncatedAlphabet K (MvPowerSeries.C (yFrac K (Fin.last k)))
    (fun s => MvPowerSeries.X s) t

/-- **The power sums of the `X_r` in `P°_{k+1}`**: `y_k^j + x_1^j + ⋯ + x_r^j`. -/
@[hjo "def_cm_truncated_alphabet"]
theorem pTruncatedAlphabet_succ_powerSum (K : Type*) [CommRing K] (k r : ℕ) {j : ℕ} (hj : 0 < j) :
    pTruncatedAlphabet K k (r + 1) (powerSum K j)
      = (MvPowerSeries.C (yFrac K (Fin.last k)) : AuxAlphabetSeriesFrac K (k + 1)) ^ j
        + ∑ s ∈ range r, (MvPowerSeries.X s : AuxAlphabetSeriesFrac K (k + 1)) ^ j :=
  truncatedAlphabet_succ_powerSum_eq _ _ r hj

/-- **`X_{-1} = 0` in `P°_{k+1}`**: the empty alphabet, whose power sums vanish. -/
@[hjo "def_cm_truncated_alphabet"]
theorem pTruncatedAlphabet_zero_powerSum (K : Type*) [CommRing K] (k : ℕ) {j : ℕ} (hj : 0 < j) :
    pTruncatedAlphabet K k 0 (powerSum K j) = 0 :=
  truncatedAlphabet_zero_powerSum _ _ hj

end HJO.Sym
