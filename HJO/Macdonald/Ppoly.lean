/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import HJO.Macdonald.Triangular
public meta import HJO.Attr

/-! # Macdonald's polynomial in a finite alphabet

`HJO.Mac.existsUnique_isMonicEigen` and `HJO.Mac.macPpoly`: for a partition `μ` of `d` with at most
`n` parts there is **exactly one** `f ∈ 𝒮_{n,d}` with `D^{(n)}_1 f = E_n(μ) f` and `f - m_μ[X_n]` in
the `𝕜`-span of the `m_ν[X_n]` with `\bar\nu <_lex \bar\mu`, and `P_μ[X_n]` is that element. **Both
halves are proved**: existence as well as uniqueness, from the one linear-algebra fact below.

## Main definitions

* `HJO.Mac.macPpoly`: `P_μ[X_n]`, the monic eigenfunction.

## Main results

* `Module.Basis.existsUnique_of_triangular`: an endomorphism triangular over a finite basis, with
  the diagonal entry at one index distinct from all the others, has exactly one eigenvector for
  that entry which is monic at that index and supported strictly below it.
* `HJO.Mac.existsUnique_isMonicEigen`: the monic eigenfunction of Macdonald's operator exists and
  is unique.
* `HJO.Mac.macOpComp_macPpoly`, `HJO.Mac.macPpoly_sub_msymm_mem_span`, `HJO.Mac.eq_macPpoly`: the
  two defining properties of `P_μ[X_n]` and the pinning they give.

## Genericity: exactly one nonvanishing is spent, and it cannot be dropped

This statement is **false** without genericity: over `ℚ` at `q = u = -1` in an alphabet of
two letters Macdonald's operator annihilates the whole of `𝒮_{2,2}` while `E_2((2)) = q²u + 1 = 0`,
so that every `f_c = m_{(2)} + c\,m_{(1,1)}` satisfies both conditions and uniqueness fails;
`q ≠ 0`, `u ≠ 0` and `M = (1-q)(1-u) ≠ 0` all hold at that point, so none of these side
conditions excludes it. *Existence* fails too, on the locus `qu = 1`: at
`(q, u) = (2, 1/2)` an admissible `f` on `𝒮_{2,2}` would need `c(q-1)(qu-1) = (q²-1)(u-1)`, which
reads `0 = -3/2` -- a genuine Jordan block.

So the statement carries `AlgebraicIndependent ℤ ![(q : K), u]`, this library's spelling of
`𝕜 = ℚ(q, u)`. It is spent in **exactly one place**: the pairwise distinctness of the
eigenvalues, `HJO.Sym.eq_of_macdonaldEigenvalue_eq`, through
`macdonaldEigenvalue_partDiagram_ne_of_ne` below. The triangularity this proof also consumes,
`macOpComp_msymm_sub_smul_mem_span_of_ne_zero`, spends only `u ≠ 0`; nothing else here consumes any
nonvanishing at all -- in particular `HJO.Sym.macdonaldEigenvalue_ne_zero` is *not* used, the linear
algebra never dividing by `E_n(μ)`.

The index range of the distinctness is the natural one: `μ.rowLen n = 0` for an alphabet of `n`
letters, which every `PartIdx σ d` satisfies for `n = #σ` (`rowLen_partDiagram_card`), so the
application needs nothing stronger.

## The linear algebra, and why existence comes for free

Order the index set `PartIdx σ d` by the lexicographic order on the exponent vectors `\bar\nu`,
which is a linear order because `partExp` is injective (`HJO.Mac.partExp_injective`). Then
`HJO.Mac.macOpComp_msymm_sub_smul_mem_span` says exactly that `D^{(n)}_1` is triangular over the
monomial symmetric basis with the eigenvalues `E_n(ν)` on the diagonal, the correction at `ν` lying
in the span of the basis vectors strictly *below* `ν`.

Write `V` for the span of the `b j` with `j < μ` and `S` for `D^{(n)}_1 - E_n(μ)`. Triangularity
makes `V` invariant under `D^{(n)}_1`, hence under `S`. Reading the coordinate of a vanishing
combination at the *largest* index of its support -- the mirror of the argument in
`HJO/Symmetric/TriangularBasis.lean`, which reads the smallest -- shows `S` is injective on
`V`, the only input being that `E_n(j) ≠ E_n(μ)` for `j < μ`. An admissible `f` is `b μ + v` with
`v ∈ V`, and the condition on it is `S v = -(S (b μ))` with `S (b μ) ∈ V`: uniqueness is the
injectivity just proved, and *existence* is the surjectivity that injectivity implies on the
finite-dimensional `V`. This is why one hypothesis buys both halves, and why no dimension count or
determinant appears.

`Module.Basis.existsUnique_of_triangular` is stated for a general field, a general finite index type
and a general endomorphism; it is the linear-algebra step performed inline in the proof -- its
"running through the finitely many indices below `μ` in decreasing order", the equation at each
determining one coefficient from those already determined. It is the companion of
`Module.Basis.exists_basis_of_triangular`.

## The attribution of the two conditions

`HJO.Mac.macPpoly` attributes its two conditions to Macdonald's Chapter VI, equations (4.15) and
(4.7), while (4.15) alone is elsewhere named as its defining property. Both conditions are needed
and neither is optional: the eigenvalue relation alone has a whole eigenspace of solutions once a
scalar is free, and the triangularity alone is satisfied by every monic member of the flag. The
mathematics here is stated as the conjunction, and the discrepancy is in the prose attribution
only.

## References

Lemma `HJO.Mac.existsUnique_isMonicEigen` and Definition
`HJO.Mac.macPpoly`, on `HJO.Sym.rowLenSeq`, `HJO.Sym.cells`,
`MvPolynomial.symmetricHomogeneousSubmodule`, `HJO.Mac.msymmMem`, `Finsupp.lex_lt_iff_isLeast`,
`HJO.Mac.macOp`, `HJO.Sym.macdonaldEigenvalue`, `Finsupp.isStrictTotalOrder_lex`,
`MvPolynomial.exists_basis_symmetricHomogeneousSubmodule_msymm`,
`HJO.Mac.exists_eq_macOp_algebraMap`, `HJO.Mac.macOpComp_msymm_sub_smul_mem_span`,
`HJO.Sym.eq_of_macdonaldEigenvalue_eq`, `HJO.Sym.finite_setOf_card_eq`.
`HJO.Sym.finite_setOf_card_eq` is the finiteness of the index set, which here is the `Fintype`
instance on `PartIdx σ d`.
-/

@[expose] public section

open Finset MvPolynomial MonomialOrder

/-! ### A triangular endomorphism has exactly one monic eigenvector -/

namespace Module.Basis

section Triangular

variable {ι K W : Type*} [Field K] [AddCommGroup W] [Module K W]

/-- A coordinate of an element of the span of part of a basis vanishes off that part. -/
private theorem repr_apply_eq_zero_of_notMem (b : Basis ι K W) {s : Set ι} {x : W}
    (hx : x ∈ Submodule.span K (⇑b '' s)) {j : ι} (hj : j ∉ s) : b.repr x j = 0 := by
  by_contra h
  exact hj (b.repr_support_subset_of_mem_span s hx
    (Finset.mem_coe.mpr (Finsupp.mem_support_iff.mpr h)))

variable [LinearOrder ι]

/-- **A triangular endomorphism is injective below a simple diagonal entry.** If `T` is triangular
over the basis `b` with diagonal `c`, and `c j ≠ c i` for every `j ≠ i`, then the only element of
the span of the `b j` with `j < i` that `T` scales by `c i` is `0`.

The coordinate is read at the *largest* index of the support: the correction term at an index `j`
of the support lives strictly below `j`, hence contributes nothing there. -/
theorem eq_zero_of_apply_eq_smul (b : Basis ι K W) {T : Module.End K W} {c : ι → K} {i : ι}
    (htri : ∀ j, T (b j) - c j • b j ∈ Submodule.span K (⇑b '' Set.Iio j))
    (hc : ∀ j, j ≠ i → c j ≠ c i) {x : W} (hx : x ∈ Submodule.span K (⇑b '' Set.Iio i))
    (hT : T x = c i • x) : x = 0 := by
  classical
  by_contra hne
  have hsupp : (b.repr x).support.Nonempty :=
    Finsupp.support_nonempty_iff.mpr fun h => hne (by simpa using congrArg b.repr.symm h)
  set j₀ := (b.repr x).support.max' hsupp with hj₀
  have hmem : j₀ ∈ (b.repr x).support := Finset.max'_mem _ _
  have hsub : ↑(b.repr x).support ⊆ Set.Iio i := b.repr_support_subset_of_mem_span _ hx
  have hj₀i : j₀ < i := hsub hmem
  set g : W →ₗ[K] K := (Finsupp.lapply j₀).comp (b.repr : W →ₗ[K] (ι →₀ K)) with hg
  have hgapp : ∀ y : W, g y = b.repr y j₀ := fun _ => rfl
  have hgb : ∀ j ∈ (b.repr x).support, g (T (b j)) = if j = j₀ then c j₀ else 0 := by
    intro j hj
    have hle : j ≤ j₀ := Finset.le_max' _ _ hj
    have h0 : b.repr (T (b j) - c j • b j) j₀ = 0 :=
      repr_apply_eq_zero_of_notMem b (htri j) (by simpa using not_lt.mpr hle)
    have hsplit : b.repr (T (b j)) j₀
        = b.repr (T (b j) - c j • b j) j₀ + b.repr (c j • b j) j₀ := by
      rw [← Finsupp.add_apply, ← map_add, sub_add_cancel]
    rw [hgapp, hsplit, h0, zero_add, map_smul, Finsupp.smul_apply, b.repr_self,
      Finsupp.single_apply]
    split_ifs with h
    · subst h; simp
    · simp
  have key : g (T x) = b.repr x j₀ * c j₀ := by
    conv_lhs => rw [← b.linearCombination_repr x]
    rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_sum, Finset.sum_eq_single j₀]
    · rw [map_smul, map_smul, hgb j₀ hmem, ite_eq_left rfl, smul_eq_mul]
    · intro j hj hjne
      rw [map_smul, map_smul, hgb j hj, ite_eq_right fun h => absurd h hjne, smul_zero]
    · intro h; exact absurd hmem h
  rw [hT, map_smul, hgapp, smul_eq_mul] at key
  have hzero : b.repr x j₀ * (c j₀ - c i) = 0 := by rw [mul_sub, ← key]; ring
  rcases mul_eq_zero.mp hzero with h | h
  · exact (Finsupp.mem_support_iff.mp hmem) h
  · exact hc j₀ (ne_of_lt hj₀i) (sub_eq_zero.mp h)

/-- **A triangular endomorphism has exactly one monic eigenvector at a simple diagonal entry.** Let
`b` be a basis of `W` indexed by a finite linearly ordered `ι`, let `T` be triangular over `b` with
diagonal `c` -- `T (b j) - c j • b j` in the span of the `b k` with `k < j` -- and let `i` be an
index with `c j ≠ c i` for every `j ≠ i`. Then there is exactly one `f` with `T f = c i • f` and
`f - b i` in the span of the `b j` with `j < i`.

Uniqueness is `eq_zero_of_apply_eq_smul` at the difference of two solutions; existence is the
surjectivity that the same injectivity gives on the finite-dimensional span. -/
theorem existsUnique_of_triangular [Finite ι] (b : Basis ι K W) {T : Module.End K W} {c : ι → K}
    (htri : ∀ j, T (b j) - c j • b j ∈ Submodule.span K (⇑b '' Set.Iio j)) {i : ι}
    (hc : ∀ j, j ≠ i → c j ≠ c i) :
    ∃! f : W, T f = c i • f ∧ f - b i ∈ Submodule.span K (⇑b '' Set.Iio i) := by
  classical
  set V := Submodule.span K (⇑b '' Set.Iio i) with hV
  have hfin : FiniteDimensional K V :=
    FiniteDimensional.span_of_finite K ((Set.toFinite (Set.Iio i)).image _)
  -- `V` is invariant under `T`: the correction at `j < i` lives below `j`, hence in `V`
  have hTV : V ≤ Submodule.comap (T : W →ₗ[K] W) V := by
    rw [hV, Submodule.span_le]
    rintro y ⟨j, hj, rfl⟩
    have h1 : Submodule.span K (⇑b '' Set.Iio j) ≤ V :=
      Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio (le_of_lt hj)))
    have h2 : T (b j) = c j • b j + (T (b j) - c j • b j) := by abel
    exact Submodule.mem_comap.mpr (h2 ▸ add_mem
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)) (h1 (htri j)))
  set S : Module.End K W := T - c i • (1 : Module.End K W) with hS
  have hSapp : ∀ y : W, S y = T y - c i • y := fun y => by simp [hS]
  have hSV : ∀ y ∈ V, S y ∈ V := fun y hy => by
    rw [hSapp]
    exact sub_mem (hTV hy) (Submodule.smul_mem _ _ hy)
  have hinj : Function.Injective (LinearMap.restrict (S : W →ₗ[K] W) hSV) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have h0 : S (y : W) = 0 := by
      have := congrArg Subtype.val hy
      simpa [LinearMap.restrict_apply] using this
    exact Subtype.ext (eq_zero_of_apply_eq_smul b htri hc y.2
      (sub_eq_zero.mp (by rw [← hSapp]; exact h0)))
  obtain ⟨v, hv⟩ := LinearMap.injective_iff_surjective.mp hinj
    ⟨-(T (b i) - c i • b i), neg_mem (htri i)⟩
  have hSv : T (v : W) - c i • (v : W) = -(T (b i) - c i • b i) := by
    rw [← hSapp]
    have := congrArg Subtype.val hv
    simpa [LinearMap.restrict_apply] using this
  have h1 : T (b i + (v : W)) = c i • (b i + (v : W)) := by
    rw [map_add, smul_add, ← sub_eq_zero,
      show T (b i) + T (v : W) - (c i • b i + c i • (v : W))
        = (T (b i) - c i • b i) + (T (v : W) - c i • (v : W)) by abel,
      hSv, add_neg_cancel]
  refine ⟨b i + (v : W), ⟨h1, by rw [add_sub_cancel_left]; exact v.2⟩, ?_⟩
  rintro y ⟨hy1, hy2⟩
  have hmem : y - (b i + (v : W)) ∈ V := by
    rw [show y - (b i + (v : W)) = (y - b i) - ((b i + (v : W)) - b i) by abel]
    exact sub_mem hy2 (by rw [add_sub_cancel_left]; exact v.2)
  refine sub_eq_zero.mp (eq_zero_of_apply_eq_smul b htri hc hmem ?_)
  rw [map_sub, hy1, h1, smul_sub]

end Triangular

end Module.Basis

namespace HJO.Mac

/-! ### The index set as an ordered index set, and the diagonal entries -/

section Index

variable {σ : Type*} [Fintype σ] [LinearOrder σ] {d : ℕ}

/-- The diagram of a partition indexing the monomial symmetric basis of `𝒮_{n,d}` has no row at
index `n`: this is the `μ_{n+1} = 0`, on `0`-indexed rows, and it is the hypothesis of
`HJO.Sym.eq_of_macdonaldEigenvalue_eq`. -/
theorem rowLen_partDiagram_card (μ : PartIdx σ d) :
    (partDiagram σ μ).rowLen (Fintype.card σ) = 0 := by
  rw [rowLen_partDiagram, rowLenSeqOf_of_le le_rfl]

/-- **Distinct indices have distinct diagrams**: the rows of the diagram of `μ` are the entries of
`\bar\mu`, and `partExp` is injective. -/
theorem partDiagram_injective :
    Function.Injective (partDiagram σ : PartIdx σ d → YoungDiagram) := by
  intro μ ν h
  refine partExp_injective (Finsupp.ext fun i => ?_)
  have hk := congrArg (fun D => YoungDiagram.rowLen D ((letterEquiv σ).symm i : ℕ)) h
  simp only [rowLen_partDiagram] at hk
  rw [rowLenSeqOf_of_lt (α := partExp σ μ) ((letterEquiv σ).symm i).2,
    rowLenSeqOf_of_lt (α := partExp σ ν) ((letterEquiv σ).symm i).2] at hk
  simpa using hk

/-- **The eigenvalues at distinct indices are distinct, at generic parameters.** This is
`HJO.Sym.eq_of_macdonaldEigenvalue_eq` read on `PartIdx σ d`, whose members all satisfy its index
condition (`rowLen_partDiagram_card`). **This is the one place genericity is spent** in the
construction of `P_μ[X_n]`. -/
theorem macdonaldEigenvalue_partDiagram_ne_of_ne {L : Type*} [CommRing L] {q u : L}
    (hqu : AlgebraicIndependent ℤ ![q, u]) {μ ν : PartIdx σ d} (hne : ν ≠ μ) :
    HJO.Sym.macdonaldEigenvalue q u (Fintype.card σ) (partDiagram σ ν)
      ≠ HJO.Sym.macdonaldEigenvalue q u (Fintype.card σ) (partDiagram σ μ) := fun h =>
  hne (partDiagram_injective (HJO.Sym.eq_of_macdonaldEigenvalue_eq hqu
    (rowLen_partDiagram_card ν) (rowLen_partDiagram_card μ) h))

/-- The index set of the monomial symmetric basis, ordered by the lexicographic order on the
exponent vectors: the order on the finite set `S` of partitions used in the construction, which is a
linear order because `partExp` is injective (`Finsupp.isStrictTotalOrder_lex` supplying the order on
the exponents).

This is the order for which `HJO.Mac.macOpComp_msymm_sub_smul_mem_span` is a triangularity, so
`Set.Iio μ` is the set of `ν` with `\bar\nu <_lex \bar\mu` -- by definition, not up to a lemma. -/
@[instance_reducible]
noncomputable def partIdxLexOrder (σ : Type*) [Fintype σ] [LinearOrder σ] (d : ℕ) :
    LinearOrder (PartIdx σ d) :=
  LinearOrder.lift' (fun μ => toLex (partExp σ μ))
    fun _ _ h => partExp_injective (toLex.injective h)

end Index

/-! ### Macdonald's polynomial in a finite alphabet -/

section Ppoly

variable {σ : Type*} [LinearOrder σ] [Fintype σ] {K : Type*} [Field K] {q : Kˣ} {u : K} {d : ℕ}

/-- Membership in the span of part of the monomial symmetric basis is the same question inside
`𝒮_{n,d}` and inside the polynomial ring: the basis vectors are the `m_ν[X_n]`, and the inclusion of
the submodule is injective. -/
private theorem coe_mem_span_iff
    {B : Module.Basis (PartIdx σ d) K (symmetricHomogeneousSubmodule σ K d)}
    (hB : ∀ ν, (B ν : MvPolynomial σ K) = msymm σ K ν.1) (S : Set (PartIdx σ d))
    (x : symmetricHomogeneousSubmodule σ K d) :
    (x : MvPolynomial σ K) ∈ Submodule.span K {p : MvPolynomial σ K | ∃ ν ∈ S, p = msymm σ K ν.1}
      ↔ x ∈ Submodule.span K (⇑B '' S) := by
  have himg : {p : MvPolynomial σ K | ∃ ν ∈ S, p = msymm σ K ν.1}
      = (symmetricHomogeneousSubmodule σ K d).subtype '' (⇑B '' S) := by
    ext p
    constructor
    · rintro ⟨ν, hν, rfl⟩
      exact ⟨B ν, ⟨ν, hν, rfl⟩, hB ν⟩
    · rintro ⟨y, ⟨ν, hν, rfl⟩, rfl⟩
      exact ⟨ν, hν, hB ν⟩
  rw [himg, ← Submodule.map_span]
  refine ⟨fun hx => ?_, fun hx => Submodule.mem_map_of_mem hx⟩
  obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp hx
  exact Subtype.coe_injective hyx ▸ hy

variable [Algebra ℚ K]

/-- The two conditions of `HJO.Mac.macPpoly` on an element of `𝒮_{n,d}`: it is an eigenvector of
`D^{(n)}_1` for the eigenvalue `E_n(μ)`, and it is `m_μ[X_n]` modulo the `m_ν[X_n]` with
`\bar\nu <_lex \bar\mu`. -/
def IsMonicEigen (q : Kˣ) (u : K) (μ : PartIdx σ d)
    (f : symmetricHomogeneousSubmodule σ K d) : Prop :=
  macOpComp q u d f
      = HJO.Sym.macdonaldEigenvalue (q : K) u (Fintype.card σ) (partDiagram σ μ) • f ∧
    (f : MvPolynomial σ K) - msymm σ K μ.1
      ∈ Submodule.span K {p : MvPolynomial σ K | ∃ ν : PartIdx σ d,
          toLex (partExp σ ν) < toLex (partExp σ μ) ∧ p = msymm σ K ν.1}

/-- **The monic eigenfunction of Macdonald's operator exists and is unique.** For `n ≥ 1` and a
partition `μ` of `d` with at most `n` parts there is exactly one `f ∈ 𝒮_{n,d}` with
`D^{(n)}_1 f = E_n(μ) f` and `f - m_μ[X_n]` in the `𝕜`-span of the `m_ν[X_n]` with
`\bar\nu <_lex \bar\mu`.

The statement asserts only that there is exactly one such `f`, which is what `∃!` says; both halves
are proved here. Genericity is spent only on the distinctness of the eigenvalues
(`macdonaldEigenvalue_partDiagram_ne_of_ne`), and it cannot be dropped: see the module docstring. -/
@[hjo "lem_mac_ppoly_unique"]
theorem existsUnique_isMonicEigen (hqu : AlgebraicIndependent ℤ ![(q : K), u])
    (μ : PartIdx σ d) : ∃! f : symmetricHomogeneousSubmodule σ K d, IsMonicEigen q u μ f := by
  classical
  obtain ⟨B, hB⟩ := exists_basis_symmetricHomogeneousSubmodule_msymm σ K d
  let _ : LinearOrder (PartIdx σ d) := partIdxLexOrder σ d
  have hBmem : ∀ ν : PartIdx σ d, B ν = msymmMem σ K ν := fun ν => Subtype.ext (hB ν)
  -- the triangularity of `D^{(n)}_1`, read in the basis `B` and the order just fixed
  have htri : ∀ ν : PartIdx σ d,
      macOpComp q u d (B ν)
          - HJO.Sym.macdonaldEigenvalue (q : K) u (Fintype.card σ) (partDiagram σ ν) • B ν
        ∈ Submodule.span K (⇑B '' Set.Iio ν) := by
    intro ν
    rw [← coe_mem_span_iff hB]
    rw [hBmem ν]
    exact macOpComp_msymm_sub_smul_mem_span_of_ne_zero (HJO.Standing.u_ne_zero hqu) ν
  have hmain := Module.Basis.existsUnique_of_triangular B htri (i := μ)
    fun ν hν => macdonaldEigenvalue_partDiagram_ne_of_ne hqu hν
  refine (existsUnique_congr fun f => ?_).mp hmain
  rw [IsMonicEigen, ← coe_mem_span_iff hB (Set.Iio μ) (f - B μ)]
  refine and_congr_right fun _ => ?_
  rw [show ((f - B μ : symmetricHomogeneousSubmodule σ K d) : MvPolynomial σ K)
    = (f : MvPolynomial σ K) - msymm σ K μ.1 by rw [Submodule.coe_sub, hB]]
  exact Iff.rfl

/-- **Macdonald's polynomial in a finite alphabet**, `P_μ[X_n]`: the one element of `𝒮_{n,|μ|}`
that `D^{(n)}_1` scales by `E_n(μ)` and that is `m_μ[X_n]` modulo the `m_ν[X_n]` with
`\bar\nu <_lex \bar\mu`. `existsUnique_isMonicEigen` is what makes this a definition rather than an
assumption.

The genericity hypothesis is an argument because without it there is nothing to define: at
`q = u = -1` the two conditions have a whole line of solutions in `𝒮_{2,2}`, and on `qu = 1` they
can have none. Being a proof of a proposition, it is irrelevant to the value.

The two theorems below state its defining properties: the
value of a `choose` says nothing by itself, so the three together are what the
definition asserts. -/
@[hjo "def_mac_ppoly"]
noncomputable def macPpoly (hqu : AlgebraicIndependent ℤ ![(q : K), u]) (μ : PartIdx σ d) :
    symmetricHomogeneousSubmodule σ K d :=
  (existsUnique_isMonicEigen hqu μ).exists.choose

/-- **`P_μ[X_n]` is an eigenvector of Macdonald's operator** with eigenvalue `E_n(μ)`: the first
condition of `HJO.Mac.macPpoly`, Macdonald's (4.15). -/
@[hjo "def_mac_ppoly"]
theorem macOpComp_macPpoly (hqu : AlgebraicIndependent ℤ ![(q : K), u]) (μ : PartIdx σ d) :
    macOpComp q u d (macPpoly hqu μ)
      = HJO.Sym.macdonaldEigenvalue (q : K) u (Fintype.card σ) (partDiagram σ μ)
          • macPpoly hqu μ :=
  (existsUnique_isMonicEigen hqu μ).exists.choose_spec.1

/-- **`P_μ[X_n]` is `m_μ[X_n]` modulo lower monomial symmetric polynomials**: the second condition
of `HJO.Mac.macPpoly`, the triangularity that normalises the eigenfunction. -/
@[hjo "def_mac_ppoly"]
theorem macPpoly_sub_msymm_mem_span (hqu : AlgebraicIndependent ℤ ![(q : K), u])
    (μ : PartIdx σ d) :
    (macPpoly hqu μ : MvPolynomial σ K) - msymm σ K μ.1
      ∈ Submodule.span K {p : MvPolynomial σ K | ∃ ν : PartIdx σ d,
          toLex (partExp σ ν) < toLex (partExp σ μ) ∧ p = msymm σ K ν.1} :=
  (existsUnique_isMonicEigen hqu μ).exists.choose_spec.2

/-- **The two conditions pin `P_μ[X_n]`**: anything satisfying them is it. This is how a consumer
identifies a polynomial it has built with Macdonald's. -/
theorem eq_macPpoly (hqu : AlgebraicIndependent ℤ ![(q : K), u]) {μ : PartIdx σ d}
    {f : symmetricHomogeneousSubmodule σ K d} (hf : IsMonicEigen q u μ f) :
    f = macPpoly hqu μ :=
  (existsUnique_isMonicEigen hqu μ).unique hf
    (existsUnique_isMonicEigen hqu μ).exists.choose_spec

end Ppoly

end HJO.Mac
