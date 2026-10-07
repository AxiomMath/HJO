/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.Fir
public import HJO.CarlssonMellit.ZDeltaDefined
public meta import HJO.Attr

/-! # The iterated swapping coefficients, at the operators `Δ_m` of `IsZDelta`

`HJO.CarlssonMellit.Fir` provides the *schema* of the composite

`f_{i,r} = Δ_{x_{r-1},x_r} ⋯ Δ_{x_1,x_2} Δ_{y_k,x_1}(y_k^i)`,

the iteration of an arbitrary family of operators along the merged alphabet. The operators actually
composed are the `Δ_m` of `HJO.Sym.IsZDelta`, and a generic iteration shows no swapping operator and
no merged alphabet in it. This file forms the instance. The first factor `Δ_{y_k,x_1}` *moves a
letter* — it is the `Δ_m` of `HJO.Sym.IsZDelta` and not the `Δ_i` of `HJO.Sym.pdelta` — and that
operator is a partial one whose existence on a graded piece is provided by `HJO.Sym.zDeltaOn`, from
`HJO.CarlssonMellit.ZDeltaDefined`.

## Main definitions

* `HJO.Sym.zSwapCoeff`: `f_{i,r}`, the schema of
  `HJO.Sym.swapCoeff` instantiated at the merged alphabet `HJO.Sym.zLetterSeries` and at the
  swapping operators `HJO.Sym.zDeltaOn`.

## Main results

* `HJO.Sym.zSwapCoeff_zero`, `HJO.Sym.zSwapCoeff_succ`: the two clauses of the definition — the
  empty composite is `y_{k+1}^i` and each further step applies the operator at the next pair of
  letters.
* `HJO.Sym.isZDelta_zSwapCoeff`: **the operator composed at each step is the `Δ_m` of
  `HJO.Sym.IsZDelta`**, that is, `f_{i,r+1}` satisfies the defining equation with `f_{i,r}` on the
  right. This is exactly the statement the schema could not make.
* `HJO.Sym.zSwapCoeff_mem_zGraded`: every `f_{i,r}` lies in `Z^{(k+1)}_i`, which is why the
  iteration never leaves the domain of the operators.
* `HJO.Sym.eq_zSwapCoeff`: the two clauses determine the family, so nothing about the construction
  beyond the defining recursion is being asserted.
* `HJO.Sym.zSwapCoeff_eq_swapCoeff_truncLetter`: the alphabet iterated over is the merged
  alphabet `y_k, x_1, x_2, …` of `HJO.Sym.truncLetter`, the one `HJO.Sym.truncatedAlphabet` and
  `HJO.Sym.zSwapCoeff_succ_eq_mul_completeHomog` are stated with.

## Implementation notes

*The operator is the `Δ_m` of `HJO.Sym.IsZDelta`, not `HJO.Sym.pdelta`.* The `Δ_i` of
`HJO.Sym.pdelta` is indexed by a pair of *auxiliary* variables and fixes every letter
(`HJO.Sym.pswap_X`), so it cannot be the first factor `Δ_{y_k,x_1}` of the composite, which moves
`y_k` to `x_1`. The operator meant is `Δ_m` of `HJO.Sym.IsZDelta`.

*The index is `r`, counting the factors, and the letters are offsets.* `f_{i,0}` is
the `i`-th power of the first letter of the merged alphabet — `y_{k+1}` at the level `k + 1`, the
`y_k` of the formula above — and `f_{i,r+1}` is the operator at the pair of letters `r`, `r + 1`
applied to `f_{i,r}`, which is the factor `Δ_{x_r,x_{r+1}}` and, at `r = 0`, the factor
`Δ_{y_k,x_1}`. No `ℕ`-subtraction appears, for the reason recorded in `HJO.CarlssonMellit.Fir`.

*The operator is written as the total map `HJO.Sym.zDeltaOn` and not as `HJO.Sym.zDelta`.* The
recursion has to produce a value before it can produce a proof that the value lies in
`Z^{(k+1)}_i`, so a definition in terms of `HJO.Sym.zDelta` — which takes the membership as an
argument — would be a recursion on a dependent pair. `HJO.Sym.zDeltaOn` is the same construction
with the proof dropped; it lands in `Z^{(k+1)}_i` unconditionally, and
`HJO.Sym.isZDelta_zDeltaOn` is where the membership of the *argument* is spent. So the iteration is
an ordinary recursion and `HJO.Sym.isZDelta_zSwapCoeff` supplies the equation at each step.

*The degree is `i` at every step.* `y_{k+1}^i` has merged degree `i` and `Δ_m` preserves the merged
degree, so the whole composite lives in `Z^{(k+1)}_i` and one and the same instance of the operator
family serves every step. That is why `HJO.Sym.zSwapCoeff` can fix the degree argument of
`HJO.Sym.zDeltaOn` to `i`.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018)
661--697, Section 4. -/

@[expose] public section

namespace HJO.Sym

variable {K : Type*} [CommRing K] [IsDomain K] {k : ℕ}

/-! ### Powers and the merged alphabet -/

/-- A power of a member of a graded piece lies in the graded piece of the multiplied degree. -/
theorem pow_mem_zGraded {d n : ℕ} {G : AuxAlphabetSeriesFrac K (k + 1)} (hG : G ∈ zGraded K k d) :
    G ^ n ∈ zGraded K k (n * d) := by
  induction n with
  | zero =>
    rw [pow_zero, Nat.zero_mul]
    exact one_mem_zGraded
  | succ n ih =>
    rw [pow_succ, Nat.succ_mul]
    exact mul_mem_zGraded ih hG

/-- **The merged alphabet of this file is the list `y_k, x_1, x_2, …`**: the letters
`HJO.Sym.zLetterSeries` at the offsets from the level are the letters `HJO.Sym.truncLetter` that
`HJO.Sym.truncatedAlphabet` and `HJO.Sym.zSwapCoeff_succ_eq_mul_completeHomog` are stated with. -/
theorem zLetterSeries_eq_truncLetter (K : Type*) [CommRing K] [IsDomain K] (k : ℕ) :
    zLetterSeries K k
      = truncLetter (MvPowerSeries.C (yFrac K (Fin.last k)) : AuxAlphabetSeriesFrac K (k + 1))
        (fun r => MvPowerSeries.X r) := by
  funext r
  cases r with
  | zero => rw [zLetterSeries_zero, truncLetter_zero]
  | succ r => rw [zLetterSeries_succ, truncLetter_succ]

/-! ### The iterated swapping coefficients -/

/-- **The iterated swapping coefficients**
`f_{i,r} = Δ_{x_{r-1},x_r} ⋯ Δ_{x_1,x_2} Δ_{y_k,x_1}(y_k^i)`: the `i`-th power of the distinguished
letter of the merged alphabet, hit by the swapping operators at the letter pairs
`(0,1), (1,2), …, (r-1,r)` in that order, the empty composite at `r = 0` giving `y_{k+1}^i`.

This is `HJO.Sym.swapCoeff` — the schema of `HJO.CarlssonMellit.Fir` — at the merged alphabet
`HJO.Sym.zLetterSeries` and at the swapping operators `HJO.Sym.zDeltaOn` of `HJO.Sym.IsZDelta`.
Those are the operators composed, and not `HJO.Sym.pdelta`, whose `Δ_i`
fixes every letter and therefore cannot be the first factor `Δ_{y_k,x_1}`.
`HJO.Sym.isZDelta_zSwapCoeff` is the statement that each step satisfies the equation of
`HJO.Sym.IsZDelta`, and `HJO.Sym.eq_zSwapCoeff` that the two clauses determine the family. -/
@[hjo "def_cm_fir"]
noncomputable def zSwapCoeff (K : Type*) [CommRing K] [IsDomain K] (k : ℕ) (q : K) (i : ℕ) :
    ℕ → AuxAlphabetSeriesFrac K (k + 1) :=
  swapCoeff (fun t => zDeltaOn K k q i t) (zLetterSeries K k) i

/-- **The empty composite**: `f_{i,0} = y_{k+1}^i`, the `i`-th power of the distinguished letter of
the merged alphabet, which is the `y_k^i` at the level `k + 1`. -/
@[hjo "def_cm_fir"]
theorem zSwapCoeff_zero (q : K) (i : ℕ) :
    zSwapCoeff K k q i 0 = MvPowerSeries.C (yFrac K (Fin.last k)) ^ i := by
  rw [zSwapCoeff, swapCoeff_zero, zLetterSeries_zero]

/-- **The recursion**: `f_{i,r+1} = Δ_{x_r,x_{r+1}}(f_{i,r})`, the outermost factor of the composite
being the swapping operator at the pair of letters `r` and `r + 1`; at `r = 0` that is the
factor `Δ_{y_k,x_1}`. -/
@[hjo "def_cm_fir"]
theorem zSwapCoeff_succ (q : K) (i r : ℕ) :
    zSwapCoeff K k q i (r + 1) = zDeltaOn K k q i r (zSwapCoeff K k q i r) :=
  rfl

/-- **The composite never leaves the graded piece**: every `f_{i,r}` lies in `Z^{(k+1)}_i`. The base
`y_{k+1}^i` is a product of `i` letters, and `Δ_m` preserves the merged degree. This is what makes
the operators defined at every step. -/
theorem zSwapCoeff_mem_zGraded (q : K) (i r : ℕ) : zSwapCoeff K k q i r ∈ zGraded K k i := by
  cases r with
  | zero =>
    have h := pow_mem_zGraded (n := i) (zLetterSeries_mem_zGraded (K := K) (k := k) 0)
    rw [zLetterSeries_zero, Nat.mul_one] at h
    rw [zSwapCoeff_zero]
    exact h
  | succ r => exact zDeltaOn_mem_zGraded q i r _

/-- **The operator composed at each step is the `Δ_m` of `HJO.Sym.IsZDelta`**: `f_{i,r+1}` satisfies

`(z_{m+1} - z_m)f_{i,r+1} = (q-1)z_{m+1}f_{i,r} + (z_{m+1} - qz_m)ŝ_m(f_{i,r})`

at `m = k + 1 + r`, which is the defining equation of the swapping operator on the merged alphabet.
This is the content the schema of `HJO.CarlssonMellit.Fir` could not carry. Its hypothesis is
discharged by `HJO.Sym.zDeltaOn` through `HJO.Sym.zSwapCoeff_mem_zGraded`. -/
@[hjo "def_cm_fir"]
theorem isZDelta_zSwapCoeff (q : K) (i r : ℕ) :
    IsZDelta q r (zSwapCoeff K k q i r) (zSwapCoeff K k q i (r + 1)) :=
  isZDelta_zDeltaOn q r (zSwapCoeff_mem_zGraded q i r)

/-- **The two clauses determine the coefficients**: a family whose value at `0` is `y_{k+1}^i` and
each of whose steps satisfies the equation of `HJO.Sym.IsZDelta` is `f_{i,·}`. So the definition
asserts nothing about the construction beyond the defining recursion, uniqueness of the
solution being `HJO.Sym.eq_of_isZDelta`. -/
theorem eq_zSwapCoeff (q : K) (i : ℕ) {g : ℕ → AuxAlphabetSeriesFrac K (k + 1)}
    (h0 : g 0 = MvPowerSeries.C (yFrac K (Fin.last k)) ^ i)
    (hs : ∀ r, IsZDelta q r (g r) (g (r + 1))) (r : ℕ) : g r = zSwapCoeff K k q i r := by
  induction r with
  | zero => rw [zSwapCoeff_zero, h0]
  | succ r ih =>
    refine eq_of_isZDelta (hs r) ?_
    rw [ih]
    exact isZDelta_zSwapCoeff q i r

/-- **The alphabet iterated over is the truncated one**: `f_{i,·}` is the schema
`HJO.Sym.swapCoeff` at the letters `HJO.Sym.truncLetter`, the list `y_k, x_1, x_2, …` that
`HJO.Sym.truncatedAlphabet` builds the alphabets `X_r` from and that
`HJO.Sym.zSwapCoeff_succ_eq_mul_completeHomog` sums over. -/
theorem zSwapCoeff_eq_swapCoeff_truncLetter (q : K) (i : ℕ) :
    zSwapCoeff K k q i
      = swapCoeff (fun t => zDeltaOn K k q i t)
        (truncLetter (MvPowerSeries.C (yFrac K (Fin.last k)) : AuxAlphabetSeriesFrac K (k + 1))
          (fun r => MvPowerSeries.X r)) i := by
  rw [zSwapCoeff, zLetterSeries_eq_truncLetter]

end HJO.Sym
