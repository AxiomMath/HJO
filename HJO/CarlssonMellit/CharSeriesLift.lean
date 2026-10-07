/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.CharSeriesSymmetric
public import HJO.Symmetric.SwapInvariant
public meta import HJO.Attr

/-! # The characteristic series comes from a symmetric function

`HJO.Dyck.exists_iota_eq_pathCharSeries`: for a Dyck path `π` of length `n` and a realisation `ι`,
there is `f ∈ Λ` with `ι(f) = χ(π)`.

The two inputs are the symmetry of `χ` under each adjacent interchange of letters
(`HJO.Dyck.letterPerm_swap_charSeries`) and its homogeneity of degree `n`,
which is immediate because every labelling the series sums over has `n` letters. Together they put
`χ` in the span `W_n` of the monomial series
(`HJO.Sym.mem_msymmSpan_of_letterPerm_swap`), and that span is the image of the graded piece `Λ_n`
by `HJO.Sym.map_lambdaComp_eq_msymmSpan`.

## Main results

* `HJO.Dyck.coeff_charSeries_eq_zero_of_sum_ne`: `χ(R, n)` is homogeneous of degree `n`.
* `HJO.Dyck.charSeries_mem_msymmSpan`: `χ(R, n) ∈ W_n` for a transitive attack set `R`.
* `HJO.Dyck.exists_iota_eq_charSeries`, `HJO.Dyck.exists_iota_eq_pathCharSeries`: the
  characteristic series is realised by a symmetric function, at a transitive attack set and at a
  Dyck path.

## Implementation notes

*The group-theoretic step is discharged by `HJO.Sym.eq_of_map_range`, not by generating the finitary
permutations.* The argument as usually written is that the adjacent transpositions generate the
finitary permutations of the alphabet, so that the coefficient of `χ` at a monomial depends only on
the monomial's orbit. `HJO/Symmetric/SwapInvariant.lean` reaches the same conclusion by the window
induction, which never forms the permutation carrying one exponent vector to another: the sorting
relabelling `HJO.Sym.sortIndex` is not finitely supported, so the generation statement
`Equiv.Perm.mem_mclosure_swap_succ` does not by itself reach it. *The statement is given at a
transitive attack set as well as at a path*, the path version being `χ(π)` and the general one its
content: only `IsSquareDyck.mono` is read, through `HJO.Dyck.isTransitiveAttackSet_attackSet`. The
`n ≥ 0` is vacuous. `𝕜` is a field of characteristic zero here because
`HJO.Sym.map_lambdaComp_eq_msymmSpan` is — the monomial span is identified with `ι(Λ_n)` through a
basis whose diagonal coefficients are products of multiplicity factorials. *Uniqueness of `f` is not
stated.* The argument as usually written remarks that `f` is unique by
`HJO.Sym.realisation_injective`; the statement asks only for existence, and the uniqueness is
available from `HJO.Sym.realisation_injective` at any call site that wants it.

## References

The lemma `HJO.Dyck.exists_iota_eq_pathCharSeries`, on the involution on characteristic functions,
with `HJO.Dyck.letterPerm_swap_charSeries`, `HJO.Dyck.isTransitiveAttackSet_attackSet`,
`HJO.Sym.map_lambdaComp_eq_msymmSpan` and `HJO.Sym.realisation_injective`. E. Carlsson and A.
Mellit, *A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018) 661--697, §3.1.
-/

@[expose] public section

open Finset HJO.Sym

namespace HJO.Dyck

variable {K : Type*} [CommRing K] {q : K} {n : ℕ} {R : Finset (ℕ × ℕ)}

/-- **`χ(R, n)` is homogeneous of degree `n`**: only monomials whose exponents sum to `n` occur,
every labelling summed over having `n` letters. This is the marked series at the empty marking, so
it is `HJO.Dyck.coeff_markedCharSeries_eq_zero_of_sum_ne`. -/
theorem coeff_charSeries_eq_zero_of_sum_ne {d : ℕ →₀ ℕ} (h : (d.sum fun _ e => e) ≠ n) :
    MvPowerSeries.coeff d (charSeries q n R) = 0 :=
  coeff_markedCharSeries_eq_zero_of_sum_ne h

/-- **`χ(R, n)` lies in the span of the monomial series of the partitions of `n`**, given that it is
fixed by each adjacent interchange of letters. This is the homogeneity above fed to
`HJO.Sym.mem_msymmSpan_of_letterPerm_swap`; the symmetry hypothesis is
`HJO.Dyck.letterPerm_swap_charSeries`. -/
theorem charSeries_mem_msymmSpan_of_letterPerm_swap
    (hsym : ∀ m : ℕ, letterPerm K (Equiv.swap m (m + 1)) (charSeries q n R) = charSeries q n R) :
    charSeries q n R ∈ msymmSpan K n :=
  mem_msymmSpan_of_letterPerm_swap (fun _ h => coeff_charSeries_eq_zero_of_sum_ne h) hsym

/-- **`χ(R, n)` lies in `W_n` for a transitive attack set**, `HJO.Dyck.letterPerm_swap_charSeries`
supplying the symmetry. -/
theorem charSeries_mem_msymmSpan (q : K) (n : ℕ) {R : Finset (ℕ × ℕ)}
    (hR : IsTransitiveAttackSet n R) : charSeries q n R ∈ msymmSpan K n :=
  charSeries_mem_msymmSpan_of_letterPerm_swap fun m => letterPerm_swap_charSeries q hR m

/-- **`HJO.Dyck.exists_iota_eq_pathCharSeries` at a transitive attack set**: the characteristic
series of a transitive attack set on `{1, …, n}` is realised by a symmetric function. `χ(R, n)` lies
in the monomial span `W_n`, and `HJO.Sym.map_lambdaComp_eq_msymmSpan` identifies that span with the
image `ι(Λ_n)` of the graded piece. -/
theorem exists_iota_eq_charSeries {K : Type*} [Field K] [CharZero K]
    {ι : Lambda K →ₐ[K] AlphabetSeries K} (hι : IsRealisation ι) (q : K) (n : ℕ)
    {R : Finset (ℕ × ℕ)} (hR : IsTransitiveAttackSet n R) :
    ∃ f : Lambda K, ι f = charSeries q n R := by
  obtain ⟨f, -, hf⟩ := Submodule.mem_map.1
    (map_lambdaComp_eq_msymmSpan hι n ▸ charSeries_mem_msymmSpan q n hR)
  exact ⟨f, hf⟩

/-- **The characteristic series comes from a symmetric function.** For a Dyck
path `π` of length `n` and a realisation `ι` there is `f ∈ Λ` with `ι(f) = χ(π)`. Only
`IsSquareDyck.mono` is read, through `HJO.Dyck.isTransitiveAttackSet_attackSet`; the `n ≥ 0` is
vacuous. -/
@[hjo "lem_cm_chi_lift"]
theorem exists_iota_eq_pathCharSeries {K : Type*} [Field K] [CharZero K]
    {ι : Lambda K →ₐ[K] AlphabetSeries K} (hι : IsRealisation ι) (q : K) {n : ℕ}
    {x : Fin n → ℕ} (hx : IsSquareDyck n x) :
    ∃ f : Lambda K, ι f = pathCharSeries q x :=
  exists_iota_eq_charSeries hι q n (isTransitiveAttackSet_attackSet hx.mono)

end HJO.Dyck
