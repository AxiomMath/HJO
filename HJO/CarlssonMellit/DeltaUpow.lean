/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.PDeltaGraded
public import HJO.PlethysticAlphabet
public meta import HJO.Attr

/-! # The swapping operator on a power of the left variable

The closed formula for the iterated swapping coefficients is proved by induction on the number of
free variables, and the inductive step evaluates the swapping operator in the free variables on a
power of the letter it moves. That evaluation is the identity of this file: for `j ≥ 1`,

`Δ_{x_r,x_{r+1}}(x_r^j) = x_{r+1} h_{j-1}[(1 - q)x_r + x_{r+1}]`.

The paper calls it straightforward to check and does not check it. What makes it a computation
rather than a division is that the left side is *defined* by a product: `HJO.Sym.xdelta` is the
unique solution of `(x_{r+1} - x_r)H = (q-1)x_{r+1}G + (x_{r+1} - qx_r)ŝ_{x_r,x_{r+1}}(G)`, so
exhibiting the value amounts to verifying one product identity and cancelling the factor
`x_{r+1} - x_r`, which is nonzero. On the right side the alphabet `(1 - q)x_r + x_{r+1}` has

`h_n[(1-q)x_r + x_{r+1}] = x_{r+1}^n + (1-q)∑_{s<n} x_r^{n-s}x_{r+1}^{s}`

by `HJO.Sym.completeHomog_add_alphabet` and `HJO.Sym.completeHomog_dilate_letter`, and the geometric
identity `(x_{r+1} - x_r)∑_{s<n}x_{r+1}^{s}x_r^{n-1-s} = x_{r+1}^n - x_r^n` turns the product into
the numerator.

## Main results

* `HJO.Sym.xdelta_X_pow_succ`, the value of `Δ_{x_r,x_{r+1}}` on `x_r^j`.
* `HJO.Sym.exists_ringHom_powerSum_eq_twist_add_letter`: the alphabet `(1 - q)x_r + x_{r+1}` is
  realized by a ring homomorphism out of `Λ`, so the hypothesis of the previous result is
  satisfiable and the statement is not vacuous.

## Implementation notes

*The alphabet is a hypothesis, not a construction.* An alphabet is a ring homomorphism out of
`Λ = HJO.Sym.Lambda A`, and `(1 - q)x_r + x_{r+1}` is named by the values it takes on the power
sums: `φ(p_j) = (1 - q^j)x_r^j + x_{r+1}^j` for `j ≥ 1`. The statement below is quantified over
every `φ` with those values rather than built on one chosen `φ`, which is the house style of
`HJO.Sym.completeHomog_dilate_letter` and of the rest of `HJO.PlethysticAlphabet`; the
existence statement is separate so that nothing has to be unfolded to use the identity. The
coefficient ring of `Λ` is left arbitrary — it is only a `ℚ`-algebra, needed for
`HJO.Sym.completeHomog` to be defined — and is unrelated to the base `K` of the series ring.

*No graded hypothesis appears.* The `Δ_{x_r,x_{r+1}}` exists only on the graded part,
and `HJO.Sym.existsUnique_mem_pGraded_xdeltaNum_eq` is what licenses it there; but
`HJO.Sym.xdeltaNum_eq_X_sub_X_mul_xdelta` holds for every series, graded or not, so the argument
here needs no membership hypothesis. The input `x_r^j` is of course homogeneous of degree `j`, and
`HJO.Sym.xdelta_mem_pGraded` records where the value lives.

*The `j ≥ 1` is written as `j = n + 1`*, so that `h_{j-1}` is `h_n` and no natural
subtraction occurs in the statement. The two auxiliary alphabets of the proof, the twisted letter
`(1 - q)x_r` and the plain letter `x_{r+1}`, are built on the same constant homomorphism
`φ ∘ MvPolynomial.C` as `φ` itself, so that the three alphabets agree on the scalars of `Λ`.

*The geometric sum is Mathlib's* `geom_sum₂_mul`, whose summand is `x^i * y^(n-1-i)`; the sum below
is written in that order for the rewrite to apply with no reindexing, and the final step is a
`linear_combination` against it, the exponents `n + 1` and `n + 2` being handled by `ring`.

## References

The lemma `HJO.Sym.xdelta_X_pow_succ`, using
`HJO.Sym.completeHomog`, `HJO.Sym.pdelta`, `HJO.Sym.pGraded`,
`HJO.Sym.existsUnique_mem_pGraded_xdeltaNum_eq` and `HJO.Sym.completeHomog_dilate_letter`; consumed
by `HJO.Sym.zSwapCoeff_succ_eq_mul_completeHomog`. E. Carlsson and A. Mellit, *A proof of the
shuffle conjecture*, J. Amer. Math. Soc. **31** (2018) 661--697, Section 4, where the identity is
asserted without proof.
-/

@[expose] public section

namespace HJO.Sym

variable {K : Type*} [CommRing K] {k : ℕ} {A : Type*} [CommRing A] [Algebra ℚ A]

/-! ### The alphabet `(1 - q)x_r + x_{r+1}` is realized -/

omit [Algebra ℚ A] in
/-- **The alphabet `(1 - q)x_r + x_{r+1}` exists**: for every homomorphism `base` of the scalars
into `P°_k` there is a homomorphism `Λ → P°_k` extending it and sending each power sum `p_j`,
`j ≥ 1`, to `(1 - q^j)x_r^j + x_{r+1}^j`. This is what makes the hypothesis of
`HJO.Sym.xdelta_X_pow_succ` satisfiable. -/
theorem exists_ringHom_powerSum_eq_twist_add_letter (q : K) (r : ℕ)
    (base : A →+* AuxAlphabetSeriesFrac K k) :
    ∃ φ : Lambda A →+* AuxAlphabetSeriesFrac K k, (∀ a : A, φ (MvPolynomial.C a) = base a) ∧
      ∀ j : ℕ, 0 < j → φ (powerSum A j)
        = (1 - MvPowerSeries.C (scalarFrac K q) ^ j) * MvPowerSeries.X r ^ j
          + MvPowerSeries.X (r + 1) ^ j := by
  refine ⟨MvPolynomial.eval₂Hom base fun i =>
      (1 - MvPowerSeries.C (scalarFrac K q) ^ (i + 1)) * MvPowerSeries.X r ^ (i + 1)
        + MvPowerSeries.X (r + 1) ^ (i + 1),
    fun a => MvPolynomial.eval₂Hom_C base _ a, fun j hj => ?_⟩
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rw [CopPower.powerSum_succ, MvPolynomial.eval₂Hom_X']

/-! ### The value of the swapping operator on a power of the left variable -/

/-- **The swapping operator on a power of the left variable.** Let `φ : Λ → P°_k` be the alphabet
`(1 - q)x_r + x_{r+1}`, that is, a ring homomorphism with
`φ(p_j) = (1 - q^j)x_r^j + x_{r+1}^j` for every `j ≥ 1`. Then for every `j = n + 1 ≥ 1`

`Δ_{x_r,x_{r+1}}(x_r^j) = x_{r+1} h_{j-1}[(1 - q)x_r + x_{r+1}]`.

The hypothesis is `j ≥ 1`, written here as `j = n + 1`; no membership in the graded part
is needed, since `HJO.Sym.xdeltaNum_eq_X_sub_X_mul_xdelta` holds for every series and the identity
is obtained by cancelling `x_{r+1} - x_r`, which is nonzero. Such a `φ` exists, by
`HJO.Sym.exists_ringHom_powerSum_eq_twist_add_letter`. -/
@[hjo "lem_cm_delta_upow"]
theorem xdelta_X_pow_succ [IsDomain K] {F : Type*}
    [FunLike F (Lambda A) (AuxAlphabetSeriesFrac K k)]
    [RingHomClass F (Lambda A) (AuxAlphabetSeriesFrac K k)] (φ : F) (q : K) (r n : ℕ)
    (hφ : ∀ j : ℕ, 0 < j → φ (powerSum A j)
      = (1 - MvPowerSeries.C (scalarFrac K q) ^ j) * MvPowerSeries.X r ^ j
        + MvPowerSeries.X (r + 1) ^ j) :
    xdelta q r (MvPowerSeries.X r ^ (n + 1) : AuxAlphabetSeriesFrac K k)
      = MvPowerSeries.X (r + 1) * φ (completeHomog A n) := by
  set base : A →+* AuxAlphabetSeriesFrac K k :=
    (φ : Lambda A →+* AuxAlphabetSeriesFrac K k).comp MvPolynomial.C with hbase
  -- the twisted letter `(1 - q)x_r`
  set ι : Lambda A →+* AuxAlphabetSeriesFrac K k := MvPolynomial.eval₂Hom base
    (fun i => (1 - MvPowerSeries.C (scalarFrac K q) ^ (i + 1)) * MvPowerSeries.X r ^ (i + 1))
    with hι
  have hιX : ∀ i : ℕ, ι (MvPolynomial.X i)
      = (1 - MvPowerSeries.C (scalarFrac K q) ^ (i + 1)) * MvPowerSeries.X r ^ (i + 1) :=
    fun i => by rw [hι, MvPolynomial.eval₂Hom_X']
  have hιp : ∀ j : ℕ, 0 < j → ι (powerSum A j)
      = (1 - MvPowerSeries.C (scalarFrac K q) ^ j) * MvPowerSeries.X r ^ j := by
    intro j hj
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [CopPower.powerSum_succ, hιX i]
  have hιh : ∀ b : ℕ, 0 < b → ι (completeHomog A b)
      = (1 - MvPowerSeries.C (scalarFrac K q)) * MvPowerSeries.X r ^ b :=
    fun b hb => completeHomog_dilate_letter ι _ _ hιp hb
  -- the plain letter `x_{r+1}`
  set ν : Lambda A →+* AuxAlphabetSeriesFrac K k :=
    MvPolynomial.eval₂Hom base (fun i => MvPowerSeries.X (r + 1) ^ (i + 1)) with hν
  have hνX : ∀ i : ℕ, ν (MvPolynomial.X i) = MvPowerSeries.X (r + 1) ^ (i + 1) :=
    fun i => by rw [hν, MvPolynomial.eval₂Hom_X']
  have hνp : ∀ j : ℕ, 0 < j → ν (powerSum A j) = MvPowerSeries.X (r + 1) ^ j := by
    intro j hj
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [CopPower.powerSum_succ, hνX i]
  have hνh : ∀ s : ℕ, ν (completeHomog A s) = MvPowerSeries.X (r + 1) ^ s :=
    completeHomog_single_letter ν _ hνp
  have hadd : ∀ j : ℕ, 0 < j → φ (powerSum A j) = ι (powerSum A j) + ν (powerSum A j) := by
    intro j hj
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [hφ _ hj, CopPower.powerSum_succ, hιX i, hνX i]
  -- the `h` of the sum of the two alphabets, with the top term `h_0[(1-q)x_r] = 1` peeled off
  have hsum : φ (completeHomog A n)
      = (∑ s ∈ Finset.range n, ι (completeHomog A (n - s)) * ν (completeHomog A s))
        + MvPowerSeries.X (r + 1) ^ n := by
    rw [completeHomog_add_alphabet ι ν φ hadd n, Finset.sum_range_succ, Nat.sub_self,
      CopPower.completeHomog_zero, map_one, one_mul, hνh n]
  have hT : (∑ s ∈ Finset.range n, ι (completeHomog A (n - s)) * ν (completeHomog A s))
      = (1 - MvPowerSeries.C (scalarFrac K q)) * MvPowerSeries.X r
        * ∑ s ∈ Finset.range n,
            (MvPowerSeries.X (r + 1) : AuxAlphabetSeriesFrac K k) ^ s
              * MvPowerSeries.X r ^ (n - 1 - s) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s hs => ?_
    have hs' : s < n := Finset.mem_range.mp hs
    rw [hιh (n - s) (by omega), hνh s, show n - s = n - 1 - s + 1 by omega, pow_succ]
    ring
  have hgeom : (∑ s ∈ Finset.range n,
        (MvPowerSeries.X (r + 1) : AuxAlphabetSeriesFrac K k) ^ s
          * MvPowerSeries.X r ^ (n - 1 - s))
        * (MvPowerSeries.X (r + 1) - MvPowerSeries.X r)
      = MvPowerSeries.X (r + 1) ^ n - MvPowerSeries.X r ^ n :=
    geom_sum₂_mul _ _ n
  refine mul_left_cancel₀ (X_sub_X_ne_zero (σ := ℕ) (A := AuxFrac K k) (i := r) (j := r + 1)
    (Nat.ne_of_lt (Nat.lt_succ_self r))) ?_
  rw [← xdeltaNum_eq_X_sub_X_mul_xdelta, xdeltaNum_apply, map_pow, xswap_X,
    Equiv.swap_apply_left, hsum, hT]
  linear_combination (-(1 - MvPowerSeries.C (scalarFrac K q)) * MvPowerSeries.X r
    * (MvPowerSeries.X (r + 1) : AuxAlphabetSeriesFrac K k)) * hgeom

end HJO.Sym
