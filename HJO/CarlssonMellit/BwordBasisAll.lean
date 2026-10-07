/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.BwordBasis
public import HJO.Symmetric.AxisFree
public meta import HJO.Attr

/-! # The words of Hall--Littlewood operators are a basis of all of `Λ`

`HJO.Sym.exists_basis_prod_bop_one`: the family `B_{lam_1}(B_{lam_2}(⋯ B_{lam_m}(1)⋯))`, indexed by
ALL partitions, is a `𝕜`-basis of `Λ`.

The graded statement is already proved: `HJO.Sym.exists_basis_lambdaComp_prod_bop_one` gives, for
each `d`, a basis of `Λ_d` whose member at the partition `lam` of `d` is the word of `lam`. So what
is owed here is the passage from "a basis of each graded piece" to "a basis of the whole", and both
halves of it are off the shelf:

* `HJO.Sym.lambdaComp_isInternal` says `Λ` is the internal
  direct sum of its graded pieces;
* `DirectSum.IsInternal.collectedBasis` glues bases of the pieces into a basis of the whole, indexed
  by the sigma type `Σ d, Nat.Partition d`.

No reindexing is needed: `Σ d, Nat.Partition d` *is* the "all partitions", every
partition being a partition of exactly one `d` — the sum of its parts — and it is the same index
type that carries `HJO.Sym.linearIndependent_elemSymmMonomial`, the independence of the elementary
monomials of all degrees.

## Main results

* `HJO.Sym.exists_basis_prod_bop_one`.
* `HJO.Sym.sortedPartitionEquiv`: adding one to every entry, as a bijection from the weakly
  decreasing lists of naturals onto the partitions of all degrees. This is
  `HJO.Sym.shiftPartitionEquiv` in the shape the monomial basis of `V_*` consumes it —
  `HJO.Sym.shiftPartitionEquiv` lands in `YoungDiagram`, while the basis above is indexed by
  `Σ d, Nat.Partition d`, and Mathlib carries no bridge between the two readings of a partition.

## Implementation notes

"The family is a basis" is the existence of a bundled `Module.Basis` whose value at the index `lam`
is the word of `lam`; the equation is what makes the statement about *this* family rather than about
the dimension of `Λ`. The word is the `List.prod` of the operators of the parts in the ring
`Module.End 𝕜 Λ`, applied to `1`, with the parts read in nonincreasing order — the operators do not
commute, so the order is part of the statement and not a convention.

`HJO.Sym.sigma_partition_ext` is the only fiddly step: two partitions of possibly different degrees
with the same parts are equal *as elements of the sigma type*, the degrees agreeing because each is
the sum of the parts. Without it the right inverse of `HJO.Sym.sortedPartitionEquiv` is a dependent
rewrite.

## References

The lemma `HJO.Sym.exists_basis_prod_bop_one`, using `HJO.Sym.Lambda`, `HJO.Sym.Bop` and
`HJO.Sym.partitionEquivList`, proved from `HJO.Sym.exists_basis_lambdaComp_prod_bop_one` and
`HJO.Sym.lambdaComp_isInternal`, and consumed by `HJO.Sweep.exists_basis_vstar_prod_bop`; and the
lemma `HJO.Sym.shiftPartitionEquiv`. Following E. Carlsson and A. Mellit, *A proof of the shuffle
conjecture*, inside the proof of its Lemma 5.6, whose quotation of Hall--Littlewood theory is
replaced here by triangularity against the elementary monomials.
-/

@[expose] public section

namespace HJO.Sym

/-! ### All partitions, as one index type -/

/-- **Two partitions with the same parts are equal in the sigma type** `Σ d, Nat.Partition d`, even
when their degrees are not syntactically the same: the degree is the sum of the parts
(`Nat.Partition.parts_sum`), so it is determined. -/
theorem sigma_partition_ext {d₁ d₂ : ℕ} {p₁ : Nat.Partition d₁} {p₂ : Nat.Partition d₂}
    (h : p₁.parts = p₂.parts) : (⟨d₁, p₁⟩ : Σ d : ℕ, Nat.Partition d) = ⟨d₂, p₂⟩ := by
  have hd : d₁ = d₂ := by rw [← p₁.parts_sum, ← p₂.parts_sum, h]
  subst hd
  exact congrArg _ (Nat.Partition.ext h)

/-- **`HJO.Sym.shiftPartitionEquiv` at `Σ d, Nat.Partition d`: adding one to every entry is a
bijection from the weakly decreasing tuples of naturals onto the partitions.** The
tuples `a_1 ≥ … ≥ a_m ≥ 0`, over all `m ≥ 0`, are the weakly decreasing lists of naturals, the
condition `a_m ≥ 0` being vacuous; a partition is a multiset of POSITIVE parts, and the asymmetry
between the two positivity conditions is the whole content of the statement.

The inverse sorts the parts nonincreasingly and subtracts one, in `ℕ`, where subtraction is
truncated; nothing is truncated because the parts are positive. `HJO.Sym.shiftPartitionEquiv` is
the same bijection read into `YoungDiagram`; this reading is the one the basis of `Λ` is indexed
by. -/
noncomputable def sortedPartitionEquiv : {l : List ℕ // l.SortedGE} ≃ Σ d : ℕ, Nat.Partition d where
  toFun l :=
    ⟨((l.1.map (· + 1) : Multiset ℕ)).sum,
      { parts := (l.1.map (· + 1) : Multiset ℕ)
        parts_pos := by
          intro i hi
          obtain ⟨y, _, rfl⟩ := List.mem_map.1 (by simpa using hi)
          omega
        parts_sum := rfl }⟩
  invFun p := ⟨(p.2.parts.sort (· ≥ ·)).map (· - 1),
    sortedGE_map_sub_one (Multiset.pairwise_sort (r := (· ≥ ·)) p.2.parts).sortedGE⟩
  left_inv l := by
    refine Subtype.ext ?_
    change ((((l.1.map (· + 1) : Multiset ℕ)).sort (· ≥ ·)).map (· - 1)) = l.1
    rw [sort_coe_of_sortedGE (sortedGE_map_add_one l.2), List.map_map]
    simp [Function.comp_def]
  right_inv p := by
    refine sigma_partition_ext ?_
    have hmap : ((p.2.parts.sort (· ≥ ·)).map (· - 1)).map (· + 1) = p.2.parts.sort (· ≥ ·) := by
      rw [List.map_map]
      refine (List.map_congr_left ?_).trans (List.map_id' _)
      intro x hx
      have hpos := p.2.parts_pos (i := x)
        (by rw [← Multiset.sort_eq p.2.parts (· ≥ ·)]; exact hx)
      simp only [Function.comp_apply]
      omega
    change ((((p.2.parts.sort (· ≥ ·)).map (· - 1)).map (· + 1) : List ℕ) : Multiset ℕ)
      = p.2.parts
    rw [hmap]
    exact Multiset.sort_eq _ _

/-- **The parts of the shifted partition, in order, are the entries of the tuple raised by one.**
This is what identifies the word of `sortedPartitionEquiv l` as
`B_{a_1+1}(⋯ B_{a_m+1}(1)⋯)`. -/
theorem sort_parts_sortedPartitionEquiv (l : {l : List ℕ // l.SortedGE}) :
    (sortedPartitionEquiv l).2.parts.sort (· ≥ ·) = l.1.map (· + 1) := by
  change ((l.1.map (· + 1) : Multiset ℕ)).sort (· ≥ ·) = l.1.map (· + 1)
  exact sort_coe_of_sortedGE (sortedGE_map_add_one l.2)

/-! ### The basis -/

variable {K : Type*} [CommRing K] [Algebra ℚ K]

/-- **The words of Hall--Littlewood operators are a `𝕜`-basis of `Λ`.** For a
partition `lam`, read as its parts in nonincreasing order, the word
`B_{lam_1}(B_{lam_2}(⋯ B_{lam_m}(1)⋯))` is the product of the operators `HJO.Sym.Bop q lam_i` in
`Module.End 𝕜 Λ`, applied to `1`. Indexed by all partitions — the partitions of `d`, over all `d` —
these elements form a `𝕜`-basis of `Λ`, for every `q`.

`HJO.Sym.exists_basis_lambdaComp_prod_bop_one` is the same statement in each degree,
`HJO.Sym.lambdaComp_isInternal` says `Λ` is the direct sum of its graded pieces, and
`DirectSum.IsInternal.collectedBasis` glues. No hypothesis on `q` is needed: the triangularity
behind the graded statement has diagonal `(-1)^d`, a unit in every ring, and `q` enters only the
correction terms. -/
@[hjo "lem_cm_bword_basis"]
theorem exists_basis_prod_bop_one (q : K) :
    ∃ B : Module.Basis (Σ d : ℕ, Nat.Partition d) K (Lambda K),
      ∀ lam : Σ d : ℕ, Nat.Partition d,
        B lam = ((lam.2.parts.sort (· ≥ ·)).map fun r : ℕ => Bop q (r : ℤ)).prod 1 := by
  classical
  choose Bd hBd using fun d : ℕ => exists_basis_lambdaComp_prod_bop_one (K := K) q d
  refine ⟨(lambdaComp_isInternal (K := K)).collectedBasis Bd, fun lam => ?_⟩
  rw [DirectSum.IsInternal.collectedBasis_coe]
  exact hBd lam.1 lam.2

end HJO.Sym
