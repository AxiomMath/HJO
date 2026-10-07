/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.TruncatedAlphabet
public import HJO.CarlssonMellit.PDelta
public meta import HJO.Attr

/-! # The iterated swapping coefficients

The lowering step of the Carlsson--Mellit analysis reaches the coefficients

`f_{i,r} = Δ_{x_{r-1},x_r} ⋯ Δ_{x_1,x_2} Δ_{y_k,x_1}(y_k^i)`,

the empty composite at `r = 0` giving `f_{i,0} = y_k^i`. This file defines them, as the iteration of
a family of operators along the merged alphabet `y_k, x_1, x_2, …`, and records the two clauses of
that definition together with the induction principle its closed form is proved by.

## Main definitions

* `HJO.Sym.swapCoeff`: `f_{i,r}`, the `r`-fold composite applied to the `i`-th power of the first
  letter of the merged alphabet.

## Main results

* `HJO.Sym.swapCoeff_zero`, `HJO.Sym.swapCoeff_succ`: the empty composite `f_{i,0} = y_k^i`, and the
  recursion `f_{i,r+1} = Δ_{x_r,x_{r+1}}(f_{i,r})` — the whole content of the definition.
* `HJO.Sym.swapCoeff_eq_of_zero_of_succ`: the two clauses determine `f_{i,r}`, which is the shape in
  which the closed form is proved: exhibit a family satisfying them.
* `HJO.Sym.sub_mul_swapCoeff_succ`: the recursion read through the defining equation of the swapping
  operator, so that `f_{i,r+1}` is pinned by a product rather than by a quotient.
* `HJO.Sym.sub_mul_pdelta`: the swapping operator on the auxiliary variables satisfies that same
  defining equation, which is what identifies the hypothesis of `HJO.Sym.sub_mul_swapCoeff_succ` as
  the formula of `HJO.Sym.pdelta`.

## Implementation notes

**`HJO.Sym.zSwapCoeff` is not defined here but in `HJO.CarlssonMellit.ZFir`.** What is
defined below is the *schema* of the composite, the iteration of an arbitrary family of operators
along the merged alphabet, and not the object: the operators composed are the `Δ_m` of
`HJO.Sym.IsZDelta`. `HJO.Sym.swapCoeff` alone is a three-line generic iteration in which no
swapping operator and no truncated alphabet occurs; the instance needs `HJO.Sym.IsZDelta` and
`HJO.Sym.zDeltaOn`. `HJO.Sym.zSwapCoeff` of `HJO.CarlssonMellit.ZFir` is `HJO.Sym.swapCoeff` at
the merged alphabet `HJO.Sym.zLetterSeries` and at the operators `HJO.Sym.zDeltaOn`, and
`HJO.Sym.isZDelta_zSwapCoeff` there is the hypothesis of
`HJO.Sym.sub_mul_swapCoeff_succ` discharged by `HJO.Sym.zDeltaOn`.

*The operator family is a parameter, and that is forced rather than chosen.* The
composite interchanges `y_k` with `x_1` at its first step and two free
variables afterwards, so its factors are the `Δ_m` of `HJO.Sym.IsZDelta` for `m ≥ k`, acting on the
alphabet-graded ring `Z^{(k)}`. The operator that is *not* it — `HJO.Sym.pdelta` — is
indexed by a pair `i j : Fin k` of
*auxiliary* variables and acts on the coefficient field `𝕂(y_1, …, y_k)` of `P°_k`, fixing every
letter (`HJO.Sym.pswap_X`). It therefore cannot be the first factor `Δ_{y_k,x_1}`, which moves a
letter, nor the later factors `Δ_{x_r,x_{r+1}}`, which move two. So `HJO.Sym.swapCoeff` takes the
family `D : ℕ → R → R` as an argument, exactly as `HJO.Sym.map_numerator_eq_zero` takes the
identification and the swap as arguments rather than naming a particular instance, and the
composite `f_{i,r}` is this at `D r = Δ_{k+r}`, which is `HJO.Sym.zSwapCoeff`. Nothing below
assumes anything about `D`; what makes the definition the right one is
`HJO.Sym.sub_mul_swapCoeff_succ`, whose hypothesis is the defining equation of `HJO.Sym.IsZDelta`
letter by letter, and `HJO.Sym.sub_mul_pdelta`, which exhibits that equation as the one
`HJO.Sym.pdelta` satisfies.

*The letters are indexed as in `HJO.Sym.truncLetter`, and the swap at `r` moves letters `r` and
`r + 1`.* The merged alphabet is the list `y_k, x_1, x_2, …`, so letter `0` is `y_k` and letter
`s + 1` is `x_{s+1}`; the factor `Δ_{y_k,x_1}` of `f_{i,r}` is the swap at `0` and its factor
`Δ_{x_r,x_{r+1}}` is the swap at `r`. The base of the recursion is accordingly the `i`-th power of
letter `0`, and the index `r` of `HJO.Sym.swapCoeff` is the `r` of `f_{i,r}`, counting the factors
of the composite.

*That index is the one the closed form needs.* `HJO.Sym.truncatedAlphabet` is shifted by one,
`t = 0` being the empty alphabet `X_{-1}` and `t = r + 1` being `X_r`, so
`HJO.Sym.zSwapCoeff_succ_eq_mul_completeHomog` reads, writing `A t` for `HJO.Sym.truncatedAlphabet`
at the index `t`,

`swapCoeff D z i r = (h_i[(1-q) A (r+1)] - h_i[(1-q) A r])/(1-q)`

at every `r ≥ 0` with no case split, and `HJO.Sym.one_sub_C_scalarFrac_mul_summableSum_zSwapCoeff`
sums it to the difference of the values at `t = R + 1` and `t = 0`. Keeping the `r - 1` would need
truncated subtraction on `ℕ`, which clips at `r = 0` to the same value as `r = 1` and so would make
the `r = 0` instance false rather than merely awkward.

*The ambient structure is a monoid.* The recursion needs a power of one letter and the iteration of
maps, and nothing else; the commutative ring reappears in
`HJO.Sym.sub_mul_swapCoeff_succ`, where a difference of letters multiplies.

## References

E. Carlsson and
A. Mellit, *A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018) 661--697,
Section 4.
-/

@[expose] public section

namespace HJO.Sym

/-! ### The iterated composite -/

/-- **The iterated swapping coefficients, `HJO.Sym.zSwapCoeff`'s composite as a schema**
`f_{i,r} = Δ_{x_{r-1},x_r} ⋯ Δ_{x_1,x_2} Δ_{y_k,x_1}(y_k^i)`: the `i`-th power of the first letter
of the merged alphabet `y_k, x_1, x_2, …`, hit by the swapping operators at the letter pairs
`(0,1), (1,2), …, (r-1,r)` in that order, the empty composite at `r = 0` giving `y_k^i`.

`z` is the merged alphabet, indexed as in `HJO.Sym.truncLetter`, so `z 0` is `y_k`; `D t` is the
swapping operator at the pair of letters `t` and `t + 1`, so `D 0` is `Δ_{y_k,x_1}` and `D r` is
`Δ_{x_r,x_{r+1}}`. Both are arguments: the operators composed are the `Δ_m` of
`HJO.Sym.IsZDelta`, which move letters and are not the `HJO.Sym.pdelta` of `HJO.Sym.pdelta`;
`HJO.Sym.sub_mul_swapCoeff_succ` is the statement that says which `D` is meant, and
`HJO.Sym.zSwapCoeff` of `HJO.CarlssonMellit.ZFir` is the instance at the real one. -/
def swapCoeff {R : Type*} [Monoid R] (D : ℕ → R → R) (z : ℕ → R) (i : ℕ) : ℕ → R
  | 0 => z 0 ^ i
  | r + 1 => D r (swapCoeff D z i r)

variable {R : Type*} [Monoid R] (D : ℕ → R → R) (z : ℕ → R) (i : ℕ)

/-- **The empty composite**: `f_{i,0} = y_k^i`, the `i`-th power of the first letter of the merged
alphabet, no swapping operator having been applied. -/
@[simp]
theorem swapCoeff_zero : swapCoeff D z i 0 = z 0 ^ i := rfl

/-- **The recursion**: `f_{i,r+1} = Δ_{x_r,x_{r+1}}(f_{i,r})`. The composite of `r + 1` operators is
the outermost one applied to the composite of the first `r`, the outermost being the swap at the
pair of letters `r` and `r + 1`. -/
theorem swapCoeff_succ (r : ℕ) : swapCoeff D z i (r + 1) = D r (swapCoeff D z i r) := rfl

/-- **The first coefficient**: `f_{i,1} = Δ_{y_k,x_1}(y_k^i)`, the one factor of the composite being
the swap of the distinguished letter with the first free variable. -/
theorem swapCoeff_one : swapCoeff D z i 1 = D 0 (z 0 ^ i) := rfl

/-- **The two clauses determine the coefficients.** A family `g` with `g 0 = y_k^i` and
`g (r+1) = Δ_{x_r,x_{r+1}}(g r)` is `f_{i,·}`. This is the shape the closed form is proved in: the
right-hand side of `HJO.Sym.zSwapCoeff_succ_eq_mul_completeHomog` is exhibited as such a family, by
the computation of its value at `r = 0` and the inductive step, and no further reference to the
composite is needed. -/
theorem swapCoeff_eq_of_zero_of_succ {g : ℕ → R} (h0 : g 0 = z 0 ^ i)
    (hs : ∀ r, g (r + 1) = D r (g r)) (r : ℕ) : swapCoeff D z i r = g r := by
  induction r with
  | zero => rw [swapCoeff_zero, h0]
  | succ r ih => rw [swapCoeff_succ, ih, hs r]

/-- The coefficients only depend on the operators actually composed: changing `D` above the index
`r` does not change `f_{i,r}`. -/
theorem swapCoeff_congr {D' : ℕ → R → R} (r : ℕ) (h : ∀ t < r, D t = D' t) :
    swapCoeff D z i r = swapCoeff D' z i r := by
  induction r with
  | zero => rw [swapCoeff_zero, swapCoeff_zero]
  | succ r ih =>
    rw [swapCoeff_succ, swapCoeff_succ, ih fun t ht => h t (ht.trans (Nat.lt_succ_self r)),
      h r (Nat.lt_succ_self r)]

/-! ### The recursion as the defining equation of the swapping operator -/

section CommRing

variable {R : Type*} [CommRing R] {q : R} {z : ℕ → R} {D s : ℕ → R → R}

/-- **The recursion, read as the defining equation of the swapping operator**: if each `D t` divides
the numerator of `HJO.Sym.IsZDelta` at the letters `t` and `t + 1` — that is, if

`(z_{t+1} - z_t) D_t(F) = (q-1) z_{t+1} F + (z_{t+1} - q z_t) ŝ_t(F)`

for every `F`, which is what `HJO.Sym.IsZDelta` asks of `Δ_t` and what `HJO.Sym.pdelta` writes as a
quotient — then `f_{i,r+1}` satisfies that equation with `f_{i,r}` on the right. Since the operators
divide by a letter difference that is not invertible, this product form is the only one
stated; the equation determines `f_{i,r+1}` because `P°_k` is a domain
(`HJO.Sym.eq_of_isZDelta`). -/
theorem sub_mul_swapCoeff_succ
    (hD : ∀ t F, (z (t + 1) - z t) * D t F
      = (q - 1) * z (t + 1) * F + (z (t + 1) - q * z t) * s t F) (i r : ℕ) :
    (z (r + 1) - z r) * swapCoeff D z i (r + 1)
      = (q - 1) * z (r + 1) * swapCoeff D z i r
        + (z (r + 1) - q * z r) * s r (swapCoeff D z i r) :=
  hD r (swapCoeff D z i r)

end CommRing

/-- **The swapping operator on the auxiliary variables satisfies that defining equation.** Clearing
the division in `HJO.Sym.pdelta` gives

`(y_j - y_i) Δ_i(F) = (q-1) y_j F + (y_j - q y_i) ŝ_i(F)`,

which is the hypothesis of `HJO.Sym.sub_mul_swapCoeff_succ` with the pair of auxiliary variables for
the pair of letters. It is recorded here to name the equation that hypothesis abstracts: the
predicate `HJO.Sym.IsZDelta` is the formula of `HJO.Sym.pdelta` with `y_m` and
`y_{m+1}` read as `z^{(k)}_m` and `z^{(k)}_{m+1}`, its quotient taken in the only sense
available. -/
theorem sub_mul_pdelta {K : Type*} [CommRing K] [IsDomain K] (q : K) {k : ℕ} {i j : Fin k}
    (hij : i ≠ j) (F : AuxAlphabetSeriesFrac K k) :
    (MvPowerSeries.C (yFrac K j) - MvPowerSeries.C (yFrac K i)) * pdelta q i j F
      = (MvPowerSeries.C (scalarFrac K q) - 1) * MvPowerSeries.C (yFrac K j) * F
        + (MvPowerSeries.C (yFrac K j) - MvPowerSeries.C (scalarFrac K q)
            * MvPowerSeries.C (yFrac K i)) * pswap K i j F := by
  have hne : yFrac K j - yFrac K i ≠ (0 : AuxFrac K k) := sub_yFrac_ne_zero hij
  have h : (MvPowerSeries.C (yFrac K j) - MvPowerSeries.C (yFrac K i) :
      AuxAlphabetSeriesFrac K k) * MvPowerSeries.C (yFrac K j - yFrac K i)⁻¹ = 1 := by
    rw [← map_sub, ← map_mul, mul_inv_cancel₀ hne, map_one]
  rw [pdelta, ← mul_assoc, h, one_mul]
  simp only [map_mul, map_sub, map_one]

/-! ### The merged alphabet -/

/-- **The empty composite on the merged alphabet**: `f_{i,0} = y_k^i`. The alphabet is
`HJO.Sym.truncLetter`, the list `y_k, x_1, x_2, …` whose first letter is the distinguished one, so
the base of the recursion is the power `y_k^i`, and the swap at `r` is
`Δ_{x_r,x_{r+1}}` at the letters of index `r` and `r + 1`. -/
theorem swapCoeff_truncLetter_zero {R' : Type*} [Monoid R'] (D : ℕ → R' → R') (y : R')
    (x : ℕ → R') (i : ℕ) :
    swapCoeff D (truncLetter y x) i 0 = y ^ i := rfl

end HJO.Sym
