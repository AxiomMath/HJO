/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Collinear.ExpPairingSeparating
public meta import HJO.Attr

/-! # The kernel of the word map, length by length

The BGLX vanishing criterion says that a combination of words of length at most `m` in the basic
operators `Dop q u 0, Dop q u 1, …` acts by zero on the symmetric functions exactly when the
symmetrised symbol `Ξ` of each of its homogeneous parts vanishes. Its sufficiency half is
`HJO.Bglx.dopWordOperator_eq_zero_of_symbolSym` and its necessity half is
`HJO.Bglx.criterionNecessary`, whose one hypothesis on the parameters is supplied by their algebraic
independence (`HJO.Bglx.paramPleth_powerSum_ne_zero_of_algebraicIndependent`). This file draws the
two consequences of the criterion that the construction of the index shift consumes.

The first step is to put the criterion in the single-length form
`Ξ_c = 0 ↔ V c = 0` (`HJO.Bglx.symbolSym_eq_zero_iff_dopWordOperator_eq_zero`). Both statements
below are then immediate, because the condition on the right of the criterion is a condition on
each length separately and the symbol is a finer invariant of a coefficient family than the
operator it names:

* raising every index multiplies `Ξ` by the symmetric monomial `z₁z₂⋯z_k`
  (`HJO.Bglx.symbolSym_dopWordRaise_eq_zero_iff`), which is a nonzerodivisor, so the vanishing of
  `Ξ` — hence of the operator — survives the raise in both directions;
* a sum over distinct lengths vanishes only if each length does, because the criterion applied to
  the whole family and the criterion applied to the family supported at a single length test the
  same symmetrised symbols.

## Main results

* `HJO.Bglx.symbolSym_eq_zero_iff_dopWordOperator_eq_zero`: the criterion at one length.
* `HJO.Sym.dopWordOperator_dopWordRaise_eq_zero_iff`.
* `HJO.Sym.sum_dopWordOperator_eq_zero_iff`.

## Implementation notes

The set of lengths in the splitting statement is an arbitrary `Finset ℕ` rather than an initial
segment `Finset.range (m + 1)`; the criterion is stated on an initial segment, and the passage is
`Finset.sum_subset` across the extension of the family by zero, exactly as in
`HJO.Bglx.raiseStableKernel_of_criterionNecessary`, which ran both arguments inline before they
were available as statements.

The genericity hypothesis is `AlgebraicIndependent ℤ ![q, u]` on both statements, and it is not
decoration: at `q = u = 1` the plethystic displacement is trivial, `Dop 1 1 0` is the identity, and
`-1 + Dop 1 1 0` vanishes while neither summand does.

## References

F. Bergeron, A. M. Garsia, E. Leven and G. Xin, *Some remarkable new plethystic operators in the
theory of Macdonald polynomials*, arXiv:1405.0316v1, J. Comb. **7** (2016) 671--714, Theorems 2.1
and 2.2. -/

@[expose] public section

namespace HJO.Bglx

open HJO.Sym

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **The vanishing criterion at a single length.** At generic parameters the symmetrised symbol of
a coefficient family of words of one length vanishes exactly when the operator it names does. The
forward direction is the sufficiency half; the backward one is the necessity half, applied to the
family supported at the length `k` alone. -/
theorem symbolSym_eq_zero_iff_dopWordOperator_eq_zero (q u : L)
    (hqu : AlgebraicIndependent ℤ ![q, u]) (k : ℕ) (c : (Fin k → ℕ) →₀ L) :
    symbolSym q u k c = 0 ↔ dopWordOperator q u k c = 0 := by
  classical
  refine ⟨dopWordOperator_eq_zero_of_symbolSym q u k c, fun hc => ?_⟩
  set c' : ∀ j : ℕ, (Fin j → ℕ) →₀ L := fun j => if hj : j = k then hj ▸ c else 0 with hc'
  have hck : c' k = c := by rw [hc']; simp
  have hsum : ∑ j ∈ Finset.range (k + 1), dopWordOperator q u j (c' j) = 0 := by
    refine (Finset.sum_eq_single_of_mem k (Finset.mem_range.2 (Nat.lt_succ_self k))
      fun j _ hj => ?_).trans ?_
    · change dopWordOperator q u j (if hj : j = k then hj ▸ c else 0) = 0
      rw [dite_eq_right hj, map_zero]
    · rw [hck, hc]
  have hx := criterionNecessary q u
    (fun _j hj => paramPleth_powerSum_ne_zero_of_algebraicIndependent hqu hj) k c' hsum k le_rfl
  rwa [hck] at hx

end HJO.Bglx

namespace HJO.Sym

open HJO.Bglx

/-- **Raising every index preserves vanishing.** At generic parameters, for a finitely supported
family `c` of scalars indexed by the words `a : Fin k → ℕ` of length `k` in the basic operators,
the operator `V (c⁺) = ∑ a, c a • (Dop q u (aₖ+1) ∘ ⋯ ∘ Dop q u (a₁+1))` of the raised family
`c⁺` of `dopWordRaise` vanishes if and only if the operator
`V c = ∑ a, c a • (Dop q u aₖ ∘ ⋯ ∘ Dop q u a₁)` does. Equivalently, the submodule
`LinearMap.ker (dopWordOperator q u k)` of families acting by zero is stable under the raise and
the raise reflects membership in it; this is what makes the index shift
`Dop q u n ↦ Dop q u (n + 1)` well defined. -/
@[hjo "lem_bglx_raise_kernel"]
theorem dopWordOperator_dopWordRaise_eq_zero_iff {L : Type*} [Field L] [Algebra ℚ L] {q u : L}
    (hqu : AlgebraicIndependent ℤ ![q, u]) {k : ℕ} (c : (Fin k → ℕ) →₀ L) :
    dopWordOperator q u k (dopWordRaise L k c) = 0 ↔ dopWordOperator q u k c = 0 := by
  rw [← symbolSym_eq_zero_iff_dopWordOperator_eq_zero q u hqu k (dopWordRaise L k c),
    ← symbolSym_eq_zero_iff_dopWordOperator_eq_zero q u hqu k c]
  exact symbolSym_dopWordRaise_eq_zero_iff q u k c

/-- **Vanishing is decided one length at a time.** At generic parameters, for a family `c`
assigning to each word length `k` a finitely supported family `c k : (Fin k → ℕ) →₀ L` of
coefficients, and for a finite set `s` of lengths, the sum over `s` of the operators
`V (c k) = ∑ a, c k a • (Dop q u aₖ ∘ ⋯ ∘ Dop q u a₁)` vanishes if and only if each of them does.
Equivalently, the submodules `LinearMap.range (dopWordOperator q u k)` of `Module.End L (Lambda L)`
are independent: no cancellation between words of different lengths. -/
@[hjo "lem_bglx_length_split"]
theorem sum_dopWordOperator_eq_zero_iff {L : Type*} [Field L] [Algebra ℚ L] {q u : L}
    (hqu : AlgebraicIndependent ℤ ![q, u]) (s : Finset ℕ)
    (c : ∀ k : ℕ, ((Fin k → ℕ) →₀ L)) :
    ∑ k ∈ s, dopWordOperator q u k (c k) = 0 ↔
      ∀ k ∈ s, dopWordOperator q u k (c k) = 0 := by
  classical
  refine ⟨fun hsum k hk => ?_, fun h => Finset.sum_eq_zero h⟩
  set c' : ∀ j : ℕ, (Fin j → ℕ) →₀ L := fun j => if j ∈ s then c j else 0 with hc'
  have hsub : s ⊆ Finset.range (s.sup id + 1) := fun j hj => by
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hj)
  have hsum' : ∑ j ∈ Finset.range (s.sup id + 1), dopWordOperator q u j (c' j) = 0 := by
    rw [← Finset.sum_subset hsub (fun j _ hj => ?_), ← hsum]
    · refine Finset.sum_congr rfl fun j hj => ?_
      change dopWordOperator q u j (if j ∈ s then c j else 0) = dopWordOperator q u j (c j)
      rw [ite_eq_left hj]
    · change dopWordOperator q u j (if j ∈ s then c j else 0) = 0
      rw [ite_eq_right hj, map_zero]
  have hk' : symbolSym q u k (c k) = 0 := by
    have hx := criterionNecessary q u
      (fun _j hj => paramPleth_powerSum_ne_zero_of_algebraicIndependent hqu hj) _ c' hsum' k
      (Nat.lt_succ_iff.1 (Finset.mem_range.1 (hsub hk)))
    change symbolSym q u k (if k ∈ s then c k else 0) = 0 at hx
    rwa [ite_eq_left hk] at hx
  exact (symbolSym_eq_zero_iff_dopWordOperator_eq_zero q u hqu k (c k)).1 hk'

end HJO.Sym
