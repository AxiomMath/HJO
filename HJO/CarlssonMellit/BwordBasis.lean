/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.BwordTriangular
public import HJO.Classical.IotaMsymm
public meta import HJO.Attr

/-! # The words of Hall--Littlewood operators are a basis in each degree

`HJO.Sym.exists_basis_lambdaComp_prod_bop_one`: for every `d ≥ 0` the family
`B_{lam_1}(B_{lam_2}(⋯ B_{lam_m}(1)⋯))`, indexed by the partitions `lam` of `d`, is a `𝕜`-basis of
`Λ_d`.

## Main results

* `HJO.Sym.prod_map_bop_apply` — the word as a product of endomorphisms is the word as a fold.
* `HJO.Sym.foldr_bop_mem_lambdaComp` — a word along a partition of `d` is homogeneous of degree `d`.
* `HJO.Sym.exists_basis_lambdaComp_prod_bop_one`.

## Implementation notes

**Everything the proof asks for is proved earlier; what is new here is the transfer into the
submodule.** `HJO.Sym.exists_basis_lambdaComp_elemSymmMonomial` is the basis,
`HJO.Sym.foldr_bop_sub_smul_elemSymmMonomial_mem_span` is the triangularity, and
`Module.Basis.exists_basis_of_triangular` turns the two into a basis, taken through the
strict-total-order repackaging `HJO.Sym.exists_basis_of_triangular_of_sto` because
`HJO.Sym.partitionLt` carries no `LinearOrder` instance. That `HJO.Sym.partitionLex` orders the
partitions of `d` totally is the instance
`IsStrictTotalOrder (Nat.Partition d) HJO.Sym.partitionLt`, already available, so no order is
re-established here.

**Two spellings of the word, and the bridge between them.** The triangularity is stated as a
`List.foldr` of `HJO.Sym.Bop q`, because that is the shape its induction along the list of parts
produces; the main statement is a `List.prod` in `Module.End 𝕜 Λ` applied to `1`, because that is
the shape a word of operators has. `HJO.Sym.prod_map_bop_apply` identifies them by one induction,
and it is stated at a general argument rather than at `1` so that the induction has something to
step on.

**The degree of the word is read off the triangularity rather than proved separately.** A word along
a partition of `d` lies in `Λ_d` because it differs from `(-1)^de_lam` by an element of the span of
the `e_mu` with `mu` a partition of `d`, and every one of those is homogeneous of degree `d`
(`HJO.Sym.elemSymmMonomial_mem_lambdaComp` at `mu.parts.sum = d`). So
`HJO.Sym.bop_leading`'s degree bookkeeping is not repeated.

**The transfer.** The triangularity lives in `Λ`; the basis lives in the submodule `Λ_d`. The span
of the image of a basis under `Submodule.subtype` is the image of the span
(`Submodule.map_span`), and `Submodule.subtype` is injective, so membership downstairs is membership
upstairs — that is the whole of `htri` below, and it is the reason the statement is not a
one-liner off the three lemmas above.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, Section 4.
-/

@[expose] public section

namespace HJO.Sym

section Word

variable {K : Type*} [CommRing K] [Algebra ℚ K]

/-- **The word of Hall--Littlewood operators, as a product and as a fold.** `List.prod` in
`Module.End 𝕜 Λ` composes with the head outermost, which is `List.foldr` of the same letters. -/
theorem prod_map_bop_apply (q : K) (l : List ℕ) (f : Lambda K) :
    ((l.map fun r : ℕ => Bop q (r : ℤ)).prod) f
      = l.foldr (fun (a : ℕ) (g : Lambda K) => Bop q (a : ℤ) g) f := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, ih, List.foldr_cons]

/-- An elementary monomial indexed by a partition of `d` is homogeneous of degree `d`. -/
theorem elemSymmMonomial_parts_mem_lambdaComp {d : ℕ} (mu : Nat.Partition d) :
    elemSymmMonomial K mu.parts ∈ LambdaComp K d := by
  have h := elemSymmMonomial_mem_lambdaComp K mu.parts
  rwa [mu.parts_sum] at h

/-- The span `HJO.Sym.foldr_bop_sub_smul_elemSymmMonomial_mem_span` produces sits inside `Λ_d`. -/
theorem span_elemSymmMonomial_le_lambdaComp {d : ℕ} (lam : Nat.Partition d) :
    Submodule.span K ((fun mu : Nat.Partition d => elemSymmMonomial K mu.parts) ''
        {mu | partitionLt lam mu}) ≤ LambdaComp K d := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨mu, -, rfl⟩
  exact elemSymmMonomial_parts_mem_lambdaComp mu

/-- **A word along a partition of `d` is homogeneous of degree `d`**: by
`HJO.Sym.foldr_bop_sub_smul_elemSymmMonomial_mem_span` it differs from `(-1)^de_lam` by an element
of the span of the `e_mu` with `mu` a partition of `d`, and both of those lie in `Λ_d`. -/
theorem foldr_bop_mem_lambdaComp (q : K) {d : ℕ} (lam : Nat.Partition d) :
    (lam.parts.sort (· ≥ ·)).foldr (fun (a : ℕ) (f : Lambda K) => Bop q (a : ℤ) f) 1
      ∈ LambdaComp K d := by
  have h2 := span_elemSymmMonomial_le_lambdaComp lam
    (foldr_bop_sub_smul_elemSymmMonomial_mem_span q lam)
  have h3 : ((-1 : K) ^ d • elemSymmMonomial K lam.parts) ∈ LambdaComp K d :=
    Submodule.smul_mem _ _ (elemSymmMonomial_parts_mem_lambdaComp lam)
  simpa using add_mem h2 h3

/-- **The words of Hall--Littlewood operators are a basis of `Λ_d`.**
For every `d ≥ 0` the family `B_{lam_1}(B_{lam_2}(⋯ B_{lam_m}(1)⋯))`, indexed by the partitions
`lam` of `d` with the parts read in nonincreasing order and the outermost operator carrying the
largest part, is a `𝕜`-basis of `Λ_d`.

`HJO.Sym.exists_basis_lambdaComp_elemSymmMonomial` is the basis to compare against,
`HJO.Sym.foldr_bop_sub_smul_elemSymmMonomial_mem_span` is the triangularity, and
`Module.Basis.exists_basis_of_triangular` — through `HJO.Sym.exists_basis_of_triangular_of_sto`, the
partitions of `d` being finite and totally ordered by `HJO.Sym.partitionLt` — turns the two into a
basis. The diagonal coefficient is `(-1)^d`, a unit. -/
@[hjo "lem_cm_bword_basis_degree"]
theorem exists_basis_lambdaComp_prod_bop_one (q : K) (d : ℕ) :
    ∃ B : Module.Basis (Nat.Partition d) K (LambdaComp K d), ∀ lam : Nat.Partition d,
      (B lam : Lambda K)
        = ((lam.parts.sort (· ≥ ·)).map fun r : ℕ => Bop q (r : ℤ)).prod 1 := by
  obtain ⟨B, hB⟩ := exists_basis_lambdaComp_elemSymmMonomial K d
  set v : Nat.Partition d → LambdaComp K d := fun lam =>
    ⟨(lam.parts.sort (· ≥ ·)).foldr (fun (a : ℕ) (f : Lambda K) => Bop q (a : ℤ) f) 1,
      foldr_bop_mem_lambdaComp q lam⟩ with hv
  have hc : ∀ _ : Nat.Partition d, IsUnit ((-1 : K) ^ d) := fun _ =>
    IsUnit.pow d (isUnit_one.neg)
  have htri : ∀ lam : Nat.Partition d,
      v lam - ((-1 : K) ^ d) • B lam
        ∈ Submodule.span K (⇑B '' {mu : Nat.Partition d | partitionLt lam mu}) := by
    intro lam
    have hfun : (fun mu : Nat.Partition d => ((B mu : Lambda K)))
        = fun mu : Nat.Partition d => elemSymmMonomial K mu.parts := funext hB
    have himg : (Submodule.subtype (LambdaComp K d)) ''
          (⇑B '' {mu : Nat.Partition d | partitionLt lam mu})
        = (fun mu : Nat.Partition d => elemSymmMonomial K mu.parts) ''
          {mu : Nat.Partition d | partitionLt lam mu} := by
      rw [Set.image_image]
      exact congrArg (fun f : Nat.Partition d → Lambda K =>
        f '' {mu : Nat.Partition d | partitionLt lam mu}) hfun
    have hup : ((v lam - ((-1 : K) ^ d) • B lam : LambdaComp K d) : Lambda K)
        ∈ Submodule.span K ((Submodule.subtype (LambdaComp K d)) ''
          (⇑B '' {mu : Nat.Partition d | partitionLt lam mu})) := by
      rw [himg]
      have h := foldr_bop_sub_smul_elemSymmMonomial_mem_span q lam
      rwa [show ((v lam - ((-1 : K) ^ d) • B lam : LambdaComp K d) : Lambda K)
          = (lam.parts.sort (· ≥ ·)).foldr (fun (a : ℕ) (f : Lambda K) => Bop q (a : ℤ) f) 1
            - (-1 : K) ^ d • elemSymmMonomial K lam.parts from by
        rw [Submodule.coe_sub, Submodule.coe_smul, hB, hv]]
    rw [← Submodule.map_span] at hup
    obtain ⟨y, hy, hyeq⟩ := Submodule.mem_map.1 hup
    exact Subtype.ext hyeq ▸ hy
  obtain ⟨B', hB'⟩ := exists_basis_of_triangular_of_sto (partitionLt (d := d)) B hc htri
  refine ⟨B', fun lam => ?_⟩
  rw [hB', hv, prod_map_bop_apply]

end Word

end HJO.Sym
