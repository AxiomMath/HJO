/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Order.Interval.Set.Defs
public meta import HJO.Attr

/-! # A triangular family is a basis

Let `W` be a module over a ring `R`, let `ι` be an index type carrying a linear order with no
infinite ascending chain, and let `b` be a basis of `W` indexed by `ι`. Call a family `v : ι → W`
*triangular* over `b` with diagonal `c : ι → R` when `v i - c i • b i` lies in the span of
`{b j : j > i}` for every `i`: the matrix of `v` in the basis `b` is then triangular with the
`c i` on its diagonal. If every `c i` is a unit, `v` is itself a basis of `W`.

The lemma is the mechanism that turns a triangularity statement between two families into a basis
statement. In this library it is applied to the elementary monomials against the power-sum
monomials, to the Schur functions against the monomial symmetric functions, and to Macdonald's
polynomials against the monomial symmetric functions, always with `ι` a finite set of partitions
under a total order chosen so that the correction terms lie above the index.

The two halves are the two directions of the triangular matrix. *Spanning* is a descending
induction: writing `U` for the span of the `v`, if `b j ∈ U` for every `j > i` then
`v i - c i • b i` lies in the span of those `b j`, hence in `U`, so `c i • b i ∈ U` and
`b i = c i⁻¹ • (c i • b i) ∈ U`; as `<` has no infinite ascending chain this induction is well
founded, and `U` then contains a basis, so `U = W`. *Linear independence* is the same
triangularity read at the smallest index: in a vanishing combination `∑ i, l i • v i = 0` let `i₀`
be the least index of the (finite) support; every `i` in the support has `i₀ ≤ i`, so the
correction `v i - c i • b i` contributes nothing to the `b i₀`-coordinate, and neither does
`c i • b i` unless `i = i₀`. Reading off that coordinate leaves `l i₀ * c i₀ = 0`, whence
`l i₀ = 0` because `c i₀` is a unit — contradicting `i₀` being in the support.

## Main results

* `Module.Basis.exists_basis_of_triangular`: a family triangular over a basis, with invertible
  diagonal coefficients, is a basis — and the basis it produces is that very family.

## Implementation notes

The `𝕂`-vector space is a module over a ring `R`, and its `c_s ≠ 0` is `IsUnit (c i)`.
Over a field the two agree (`isUnit_iff_ne_zero`), and invertibility rather than nonvanishing is
what the statement needs: over `R = ℤ` the family `v 0 = 2 • b 0` is triangular with diagonal
`2 ≠ 0` and spans `2ℤ`, not `ℤ`.

The finite totally ordered `S` is a `LinearOrder` with `WellFoundedGT` — no infinite
ascending chain — which a finite linear order satisfies by instance, so an application with finite
`S` supplies nothing extra. Some hypothesis of this kind is needed and not decoration: on `ι = ℕ`
the family `v i = b i - b (i + 1)` is triangular with all `c i = 1`, and `b 0` is not in its span.

"`v` is a basis" is stated as the existence of a bundled `Module.Basis ι R W` whose coercion to a
function is `v`, which is Mathlib's reading of the phrase; the equation `⇑b' = v` is what makes it
a statement about `v` and not about some unnamed basis. The `{w_t : t > s}` is
`⇑b '' Set.Ioi i`.

A proof over a field would close with a dimension count: a spanning family of `#S` vectors in a
space of dimension `#S` is a basis. That is unavailable here and not needed. The statement is over a
ring `R` with `ι` merely `WellFoundedGT`, where there is no dimension to count (and over a
noncommutative ring no determinant either), so linear independence is proved directly from the
triangularity, by the minimal-index argument above.

Both halves read a coordinate of the correction term through `Module.Basis.repr`, using that the
`i₀`-coordinate of an element of `span R (b '' s)` vanishes when `i₀ ∉ s`
(`Module.Basis.repr_support_subset_of_mem_span`). Scalars are kept on the left throughout —
`l i₀ * c i₀`, not `c i₀ * l i₀` — so that nothing here needs `R` commutative;
`IsUnit.mul_left_eq_zero` cancels the unit on the correct side.

## References

`Module.Basis.exists_basis_of_triangular` is used by
`HJO.Sym.exists_basis_lambdaComp_elemSymmMonomial`, `HJO.Sym.exists_basis_lambdaComp_prod_bop_one`,
`HJO.Sym.exists_basis_iota_pmonomial`, `HJO.Sym.exists_basis_schurSeries`,
`HJO.Sym.exists_basis_symmetricHomogeneousSubmodule_restrictAlphabet` and
`HJO.Mac.exists_basis_macPpoly`.
-/

@[expose] public section

namespace Module.Basis

section Triangular

variable {ι R W : Type*} [Ring R] [AddCommGroup W] [Module R W]

/-- A coordinate of an element of the span of part of a basis vanishes off that part. -/
private theorem repr_apply_eq_zero_of_mem_span_image (b : Basis ι R W) {s : Set ι} {x : W}
    (hx : x ∈ Submodule.span R (⇑b '' s)) {j : ι} (hj : j ∉ s) : b.repr x j = 0 := by
  by_contra h
  exact hj (b.repr_support_subset_of_mem_span s hx
    (Finset.mem_coe.mpr (Finsupp.mem_support_iff.mpr h)))

variable [LinearOrder ι] (b : Basis ι R W) {v : ι → W} {c : ι → R} (hc : ∀ i, IsUnit (c i))
  (htri : ∀ i, v i - c i • b i ∈ Submodule.span R (⇑b '' Set.Ioi i))

include hc htri in
/-- Every basis vector lies in the span of a triangular family with invertible diagonal: the
descending induction on the index. -/
private theorem mem_span_range_of_triangular [WellFoundedGT ι] (i : ι) :
    b i ∈ Submodule.span R (Set.range v) := by
  refine wellFounded_gt.induction (C := fun i => b i ∈ Submodule.span R (Set.range v)) i ?_
  intro i ih
  have h1 : Submodule.span R (⇑b '' Set.Ioi i) ≤ Submodule.span R (Set.range v) := by
    rw [Submodule.span_le]
    rintro x ⟨j, hj, rfl⟩
    exact ih j hj
  have h2 : c i • b i ∈ Submodule.span R (Set.range v) := by
    rw [show c i • b i = v i - (v i - c i • b i) from (sub_sub_cancel _ _).symm]
    exact sub_mem (Submodule.subset_span ⟨i, rfl⟩) (h1 (htri i))
  exact (Submodule.smul_mem_iff_of_isUnit _ (hc i)).mp h2

include hc htri in
/-- A triangular family with invertible diagonal is linearly independent: read the coordinate at
the least index of the support of a vanishing combination. -/
private theorem linearIndependent_of_triangular : LinearIndependent R v := by
  rw [linearIndependent_iff]
  intro l hl
  by_contra hne
  have hsupp : l.support.Nonempty := Finsupp.support_nonempty_iff.mpr hne
  set i₀ := l.support.min' hsupp with hi₀
  have hmem : i₀ ∈ l.support := Finset.min'_mem _ _
  set g : W →ₗ[R] R := (Finsupp.lapply i₀).comp (b.repr : W →ₗ[R] (ι →₀ R)) with hg
  have hgapp : ∀ x : W, g x = b.repr x i₀ := fun _ => rfl
  have hgv : ∀ i, i₀ ≤ i → g (v i) = if i = i₀ then c i₀ else 0 := by
    intro i hi
    have h0 : b.repr (v i - c i • b i) i₀ = 0 :=
      repr_apply_eq_zero_of_mem_span_image b (htri i) (by simpa using not_lt.mpr hi)
    have hsplit : b.repr (v i) i₀ = b.repr (v i - c i • b i) i₀ + b.repr (c i • b i) i₀ := by
      rw [← Finsupp.add_apply, ← map_add, sub_add_cancel]
    rw [hgapp, hsplit, h0, zero_add, map_smul, Finsupp.smul_apply, b.repr_self,
      Finsupp.single_apply]
    split_ifs with h
    · subst h; simp
    · simp
  have hself : g (v i₀) = c i₀ := by simpa using hgv i₀ le_rfl
  have hother : ∀ i, i₀ < i → g (v i) = 0 := fun i hi => by simp [hgv i hi.le, hi.ne']
  have key : g (Finsupp.linearCombination R v l) = l i₀ * c i₀ := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, Finset.sum_eq_single i₀]
    · rw [map_smul, hself, smul_eq_mul]
    · intro i hi hne'
      rw [map_smul, hother i (lt_of_le_of_ne (Finset.min'_le _ _ hi) (Ne.symm hne')), smul_zero]
    · intro h; exact absurd hmem h
  rw [hl, map_zero] at key
  exact (Finsupp.mem_support_iff.mp hmem) ((hc i₀).mul_left_eq_zero.mp key.symm)

end Triangular

variable {ι R W : Type*} [Ring R] [AddCommGroup W] [Module R W]

/-- **A triangular family with invertible diagonal is a basis.** If `b` is a basis of `W` indexed
by a linearly ordered `ι` with no infinite ascending chain, `c i` is a unit for every `i`, and
`v i - c i • b i` lies in the span of the `b j` with `j > i`, then `v` is a basis of `W`. -/
@[hjo "lem_cm_triangular_basis"]
theorem exists_basis_of_triangular [LinearOrder ι] [WellFoundedGT ι] (b : Basis ι R W)
    {v : ι → W} {c : ι → R} (hc : ∀ i, IsUnit (c i))
    (htri : ∀ i, v i - c i • b i ∈ Submodule.span R (⇑b '' Set.Ioi i)) :
    ∃ b' : Basis ι R W, ⇑b' = v :=
  ⟨Basis.mk (linearIndependent_of_triangular b hc htri) (by
    rw [← b.span_eq, Submodule.span_le]
    rintro x ⟨i, rfl⟩
    exact mem_span_range_of_triangular b hc htri i), Basis.coe_mk _ _⟩

end Module.Basis
