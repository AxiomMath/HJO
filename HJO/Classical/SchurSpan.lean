/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Classical.RealisationInjective
public import HJO.Classical.SchurBasis
public meta import HJO.Attr

/-! # The Schur series span a graded piece

The lemma `HJO.Sym.exists_eq_sum_smul_schurSeries`: every `f ∈ Λ_n` is a `𝕜`-combination of elements
of `Λ` whose realisations are the Schur series of Young diagrams with `n` cells.

The three inputs are all in place. `HJO.Sym.map_lambdaComp_eq_msymmSpan` identifies `ι(Λ_n)` with
the span `W_n` of the monomial series; `HJO.Sym.exists_basis_schurSeries` makes the Schur series of
the diagrams `D_λ`, `λ` a partition of `n`, a `𝕜`-basis of that same `W_n`; and
`HJO.Sym.realisation_injective` turns an identity between the realisations into an identity in `Λ`.
So the proof is: expand `ι(f)` in the Schur basis of `W_n`, pull each basis vector back along `ι` —
possible because `W_n` is exactly the image of `Λ_n` — and cancel `ι`.

## Main statements

* `HJO.Sym.exists_eq_sum_smul_schurSeries`: the lemma with its index set named, the partitions of
  `n`, which is the one a consumer uses.
* `HJO.Sym.exists_finset_eq_sum_smul_schurSeries`: the statement in its original form, with the
  finite index set existentially quantified.

## Implementation notes

*The index set is the partitions of `n`.* The original statement asks only for *a* finite set `K`;
naming it is a strengthening, and it is the set its own proof uses. The existential form is derived
from it and is the faithful transcription, `Finset J` for an existentially quantified `J : Type`
being the "finite set `K`" with "one of each for `k ∈ K`".

*The hypothesis `n ≥ 1` of the original statement is dropped.* Nothing in the argument reads it, and
at `n = 0` the statement is true and not vacuous: the partitions of `0` are the single empty one,
whose diagram is empty, so `f ∈ Λ_0` — a scalar — is that scalar times an element realising the
empty Schur series `1`.

*The base ring is a field of characteristic zero.* `HJO.Sym.exists_basis_schurSeries` is proved over
an arbitrary commutative ring, but `HJO.Sym.map_lambdaComp_eq_msymmSpan` is not, and cannot be: it
rests on `Module.Basis.exists_basis_of_triangular` applied with the diagonal coefficients of the
expansion of `ι(p_λ)` in the `m_μ`, which must be *units*. Over `ℤ` the triangular family `2 • m_λ`
has nonzero diagonal and spans only the `2ℤ`-combinations. `HJO.Sym.realisation_injective` likewise
needs `CharZero` and no zero divisors.

## References

The lemma `HJO.Sym.exists_eq_sum_smul_schurSeries` is consumed by
`HJO.ParkingFunctions.realisation_thetaLambda_of_sum_smul_gessel`, which turns a fundamental
expansion of `ι(f)` into one of `ι(θ₀ f)` and reads this lemma for the Schur decomposition it
compares against.
-/

@[expose] public section

open Finset

namespace HJO.Sym

variable {K : Type*} [Field K] [CharZero K] {ι : Lambda K →ₐ[K] AlphabetSeries K}

/-- **The Schur series span a graded piece.** For `f ∈ Λ_n` there are scalars
`b_λ` and elements `g_λ ∈ Λ`, indexed by the partitions `λ` of `n`, with
`ι(g_λ) = sch(D_λ)` and `f = ∑_λ b_λ g_λ`. Each `D_λ` has `n` cells by
`HJO.Sym.card_partitionDiagram`.

The original statement leaves the finite index set existentially quantified;
`exists_finset_eq_sum_smul_schurSeries` is that reading, obtained from this one. -/
@[hjo "lem_cm_schur_span"]
theorem exists_eq_sum_smul_schurSeries (hι : IsRealisation ι) {n : ℕ} {f : Lambda K}
    (hf : f ∈ LambdaComp K n) :
    ∃ (b : Nat.Partition n → K) (g : Nat.Partition n → Lambda K),
      (∀ p : Nat.Partition n, ι (g p) = schurSeries K (partitionDiagram p)) ∧
        f = ∑ p, b p • g p := by
  classical
  have hmap : Submodule.map ι.toLinearMap (LambdaComp K n) = msymmSpan K n :=
    map_lambdaComp_eq_msymmSpan hι n
  have hlift : ∀ p : Nat.Partition n,
      ∃ y : Lambda K, ι y = schurSeries K (partitionDiagram p) := by
    intro p
    obtain ⟨y, -, hy⟩ := Submodule.mem_map.1 (hmap ▸ schurSeries_mem_msymmSpan K p)
    exact ⟨y, hy⟩
  choose g hg using hlift
  obtain ⟨b, hb⟩ := exists_basis_schurSeries K n
  have hfmem : ι f ∈ msymmSpan K n := hmap ▸ Submodule.mem_map_of_mem hf
  refine ⟨fun p => b.repr ⟨ι f, hfmem⟩ p, g, hg, realisation_injective hι ?_⟩
  have hrepr := b.sum_repr ⟨ι f, hfmem⟩
  rw [map_sum]
  calc ι f = ((∑ p, b.repr ⟨ι f, hfmem⟩ p • b p : msymmSpan K n) : AlphabetSeries K) := by
        rw [hrepr]
    _ = ∑ p, b.repr ⟨ι f, hfmem⟩ p • ι (g p) := by
        push_cast [Submodule.coe_sum]
        exact Finset.sum_congr rfl fun p _ => by rw [hb p, hg p]
    _ = ∑ p, ι (b.repr ⟨ι f, hfmem⟩ p • g p) :=
        Finset.sum_congr rfl fun p _ => (map_smul _ _ _).symm

/-- **`HJO.Sym.exists_eq_sum_smul_schurSeries` in its original form**: a finite set `K`, scalars
`b_k`, elements `g_k ∈ Λ` and Young diagrams `D_k` with `n` cells, one of each for `k ∈ K`, with
`ι(g_k) = sch(D_k)` and `f = ∑_{k ∈ K} b_k g_k`. -/
@[hjo "lem_cm_schur_span"]
theorem exists_finset_eq_sum_smul_schurSeries (hι : IsRealisation ι) {n : ℕ} {f : Lambda K}
    (hf : f ∈ LambdaComp K n) :
    ∃ (J : Type) (s : Finset J) (b : J → K) (g : J → Lambda K) (D : J → YoungDiagram),
      (∀ k ∈ s, (D k).card = n) ∧ (∀ k ∈ s, ι (g k) = schurSeries K (D k)) ∧
        f = ∑ k ∈ s, b k • g k := by
  obtain ⟨b, g, hg, hsum⟩ := exists_eq_sum_smul_schurSeries hι hf
  exact ⟨Nat.Partition n, Finset.univ, b, g, partitionDiagram,
    fun p _ => card_partitionDiagram p, fun p _ => hg p, hsum⟩

end HJO.Sym
