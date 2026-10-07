/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Macdonald.Conjugator
public import HJO.Macdonald.Inversion
public meta import HJO.Attr

/-! # From a Macdonald eigenbasis to a modified Macdonald family

`IsMacdonaldEigenbasis` has three clauses and `IsModifiedMacdonaldFamily` has four. This file is
the passage between them, and it is where the route to
`HJO.Standing.exists_isModifiedMacdonaldFamily_param'` becomes a finite amount of algebra on `Λ`
rather than the construction of Macdonald's polynomials.

The parameter inversion `ι` acts on the cell statistics (`ι B_μ = B*_μ`, `ι T_μ = T_μ⁻¹`,
`ι M = M̃`) and, through `↓`, conjugates `D_0` into `D*_0`. That turns eigenbasis clause `(b)`
together with clause `(c)` into family clause (iii), which is the content of
`HJO.Sym.dopStar_zero_smul_of_dop_zero`. Separately, a family which is a basis and satisfies clause
`(b)` is determined up to one nonzero scalar per index
(`HJO.Sym.exists_smul_of_dop_zero_eigenbasis`), because the cell sum determines the cells summed
over (`HJO.Sym.eq_of_sum_cellWeight_eq`); scalars do not move a span, so (iv) -- a statement about
spans -- transfers from any one such family to every other.

Clauses (i), (ii) and (iii) of `IsModifiedMacdonaldFamily` are established here from an
eigenbasis outright. Clause (iv) is established for *every* eigenbasis as soon as it holds for
*one* family that is a basis and satisfies clause `(b)`. So
`HJO.Standing.exists_isModifiedMacdonaldFamily_param'` reduces to exactly two inputs, both of which
concern the construction of Macdonald's polynomials:

* `HJO.Standing.hasUnnormalisedMacdonaldEigenbasis_param`: some family is a Macdonald eigenbasis;
* `HJO.Standing.elemSymm_one_mul_macHtilde_mem_span_param`: that family's `e₁`-products have
  covering support.

`exists_isModifiedMacdonaldFamily` below is `HJO.Standing.exists_isModifiedMacdonaldFamily_param'`
carrying precisely those two as hypotheses and nothing else, so the two remaining inputs are visible
in one signature.

## Main definitions

* `HJO.Sym.dopZeroEigenvalue`: the scalar `-(M B_μ - 1)` that eigenbasis clause `(b)` attaches to
  the index `μ`.
* `HJO.Sym.inversionW`: the inversion `↓` read in the variable `w = z⁻¹` the displacements are
  written in.

## Main results

* `Module.Basis.repr_apply_of_forall_apply_eq_smul`, `Module.Basis.exists_smul_of_apply_eq_smul`:
  an endomorphism diagonal in a basis multiplies the coordinate at an index by the eigenvalue
  there, and, its eigenvalues being pairwise distinct, its nonzero eigenvectors at the eigenvalue
  of `i` are the nonzero multiples of the basis member at `i`.
* `HJO.Sym.paramInv_cellWeight`, `paramInv_paramProduct`, `paramInv_cellSum`, `paramInv_cellProd`:
  the parameter inversion on the cell statistics.
* `HJO.Sym.paramProduct_ne_zero`: generic parameters have `M ≠ 0`.
* `HJO.Sym.eq_of_sum_cellWeight_eq`: at parameters generic over a nontrivial coefficient ring, the
  cell sum determines the finite set of cells it is summed over; `HJO.Sym.eq_of_cellSum_eq` is that
  for the cells of a partition.
* `HJO.Sym.eq_of_dopZeroEigenvalue_eq`: at generic parameters distinct partitions carry distinct
  eigenvalues, which is what lets clause `(b)` pin a family down.
* `HJO.Sym.inversion_elemSymm`: `↓ e_n = h_n`.
* `HJO.Sym.inversionW_plethShift`: `↓_w(δ(↓f)) = δ*(f)`.
* `HJO.Sym.dopStar_zero_eq`: `D*_0 f = ↓(D_0(↓f))`.
* `HJO.Sym.dopStar_zero_smul_of_dop_zero`: family clause (iii) from eigenbasis clauses `(b)`, `(c)`.
* `HJO.Sym.exists_smul_of_dop_zero_eigenbasis`: two such families agree up to one nonzero scalar.
* `HJO.Sym.elemSymm_one_mul_mem_of_dop_zero`: clause (iv) transported across that, carrying the
  constructed family's Pieri support as a hypothesis.
* `HJO.Sym.isModifiedMacdonaldFamily_of_isMacdonaldEigenbasis`,
  `HJO.Sym.exists_isModifiedMacdonaldFamily`,
  `HJO.Sym.exists_isMacdonaldConjugator_of_exists_isMacdonaldEigenbasis`: the reduction, carrying
  the same hypothesis.

## Implementation notes

Stated with no hypothesis on `q` and `u`, as it usually is,
`HJO.Sym.exists_smul_of_dop_zero_eigenbasis` is **false** over a general field. One hypothesis
repairs it: the genericity of the pair, `AlgebraicIndependent ℤ ![q, u]`, which is this library's
rendering of "`q` and `u` are indeterminates". It is spent twice over, and the two ways the lemma
fails without it are different.

Without `M ≠ 0` clause `(b)` says nothing at all: at `u = 1` the parameter product vanishes, every
eigenvalue `-(M B_μ - 1)` collapses to `1`, and `D_0` is the identity
(`HJO.DopRees.dop_eq_mulLeft`), so clause `(b)` holds for *every* family and cannot pin one up to
scalars. Without genericity the eigenvalue does not determine the index, through
`HJO.Sym.eq_of_sum_cellWeight_eq`, which, stated with no hypothesis, is also false over a
general field -- `B_μ` is a sum of monomials `q^{j-1}u^{i-1}` and only algebraic independence makes
the cells readable off it; the witness there is `q = u`, where `M = (1 - q)^2` is nonzero. So the
two failure modes are independent of one another.

`M ≠ 0` is nonetheless not a second hypothesis anywhere below: genericity *implies* it, by
`paramProduct_ne_zero`, since a parameter of an algebraically independent pair is transcendental
and so is not `1`. Carrying both would leave a reader unable to see that the two are not
independent, and would charge every call site with an obligation it already owns.

`exists_smul_of_dop_zero_eigenbasis` is one application of
`Module.Basis.exists_smul_of_apply_eq_smul`, which carries the whole of the coordinate comparison
and nothing about `Λ`, `D_0` or the cell sums: an endomorphism diagonal in a basis at pairwise
distinct eigenvalues has the coordinate lines of that basis for eigenspaces. That is stated for a
commutative ring without zero divisors, an arbitrary index type and no finiteness anywhere --
strictly less than this file assumes -- because cancelling one coordinate is all the argument asks
of the scalars. Genericity is spent only on the two hypotheses it takes: the eigenvalue clause, and
the injectivity of `μ ↦ -(M B_μ - 1)` through `eq_of_dopZeroEigenvalue_eq`. Those two ingredients
ask no more of the scalars than it does: the eigenvalue is a ring expression in the cell statistics
and its injectivity only cancels `M`, so both are stated over a commutative ring, without zero
divisors for the cancellation. The field is spent below where a comparison divides by the scalar
relating two families, and the inverted parameters of `ι` need it too.

`HJO.Sym.eq_of_sum_cellWeight_eq` is read here on an arbitrary finite set of cells rather than on a
partition. Its argument recovers a cell from the exponent pair of its monomial and never uses that
the cells of a partition form a lower set of `ℕ × ℕ`, so the diagram is not a hypothesis of it, and
the reading `eq_of_cellSum_eq` is one term away by `YoungDiagram.ext`. The extra
generality is not cosmetic: `{(1, 1)}` is a finite set of cells which is no partition's, so the set
form does not follow from the partition form. The coefficient ring of the genericity hypothesis is a
variable for the same reason: `AlgebraicIndependent ℤ ![q, u]` forces `ℤ` to inject into `L` and so
holds of no pair at all in positive characteristic, where the statement is nonetheless true and its
hypothesis is met by the indeterminates of `𝔽_p[Q, U]` over `R = 𝔽_p`. So the `ℤ` reading asserts
nothing over a whole class of bases, and the derivation runs only from the general form to it. What
the base ring must satisfy is `Nontrivial R`, spent on `(1 : R) ≠ 0` where a coefficient is read as
a membership: over the zero ring `L` is trivial too, all cell sums agree, and the statement fails.
Every consumer below supplies `R = ℤ`, inferred from the hypothesis, so none of them moves.

The coefficient inversion `ι` is a **parameter**, an arbitrary ring endomorphism of `L`, exactly as
in `HJO/Macdonald/Inversion.lean`; a second convention is not invented here. What holds
of the specific automorphism of `ℚ(q, u)` -- that it inverts `q` and `u`, fixes
`ℚ`, and is an involution -- is carried as three hypotheses `ι q = q⁻¹`, `ι u = u⁻¹`,
`ι ∘ ι = id` and `ι ∘ algebraMap ℚ L = algebraMap ℚ L`. Involutivity in particular cannot be proved
of an arbitrary endomorphism, and `HJO.Sym.paramQUInv_involutive` is exactly that hypothesis; it is
not restated as a theorem.

`↓_z` of `HJO.Sym.inversionZ` is realised in `Inversion.lean` on `LaurentSeries (Lambda K)`. The
displacements `δ` and `δ*` of this library land in `Polynomial (Lambda L)`, written in
`w = z⁻¹` (see `HJO/Collinear/Vocabulary.lean`), so the shift lemma is stated for the
corresponding operator on `Λ[w]`, `inversionW`, whose sign at `w^j = z^{-j}` is
`(-1)^{-j} = (-1)^j`. `inversionW` is the transcription of `HJO.Sym.inversionZ` into the variable
the operators are actually built in.

## References

The reference for the inversion chain is
A. M. Garsia, M. Haiman and G. Tesler, *Explicit plethystic formulas for Macdonald (q,t)-Kostka
coefficients*, Sém. Lothar. Combin. **42** (1999), B42m: their equation (1.13) is `↓`, their (1.14)
c) at `k = 0` is `dopStar_zero_eq`, and their Remark 1.1 -- that (1.11) b) follows from (1.11) a) --
is `dopStar_zero_smul_of_dop_zero`.
-/

@[expose] public section

open Finset MvPolynomial

namespace HJO.Sym

/-! ### The parameter inversion on the cell statistics -/

section ParamInv

variable {L : Type*} [Field L] {q u : L} (ι : L →+* L) (hq : ι q = q⁻¹) (hu : ι u = u⁻¹)

include hq hu

/-- **The parameter inversion inverts a cell weight.** `ι w(c) = w(c)⁻¹`: the weight is the
monomial `q^{j-1}u^{i-1}` and `ι` is multiplicative. -/
@[hjo "lem_ght2_param_inv_weight"]
theorem paramInv_cellWeight (c : ℕ × ℕ) : ι (cellWeight q u c) = (cellWeight q u c)⁻¹ := by
  rw [cellWeight, map_mul, map_pow, map_pow, hq, hu, mul_inv, inv_pow, inv_pow]

/-- **The parameter inversion carries the parameter product to its inverted form.**
`ι M = M̃`, that is `ι((1 - q)(1 - u)) = (1 - q⁻¹)(1 - u⁻¹)`. -/
@[hjo "lem_ght2_param_inv_M"]
theorem paramInv_paramProduct : ι (paramProduct q u) = paramProduct q⁻¹ u⁻¹ := by
  rw [paramProduct, paramProduct, map_mul, map_sub, map_sub, map_one, hq, hu]

/-- **The parameter inversion carries the cell sum to the inverted cell sum.** `ι B_μ = B*_μ`:
`B_μ` is a finite sum of cell weights and `ι` is additive. -/
@[hjo "lem_ght2_param_inv_bmu"]
theorem paramInv_cellSum (μ : YoungDiagram) : ι (cellSum q u μ) = cellSumInv q u μ := by
  rw [cellSum, cellSumInv, map_sum]
  exact Finset.sum_congr rfl fun c _ => paramInv_cellWeight ι hq hu c

/-- **The parameter inversion inverts the cell product.** `ι T_μ = T_μ⁻¹`: `T_μ` is a finite
product of cell weights and `ι` is multiplicative. -/
@[hjo "lem_ght2_param_inv_tmu"]
theorem paramInv_cellProd (μ : YoungDiagram) :
    ι (cellProd q u μ) = (cellProd q u μ)⁻¹ := by
  rw [cellProd, map_prod, ← Finset.prod_inv_distrib]
  exact Finset.prod_congr rfl fun c _ => paramInv_cellWeight ι hq hu c

end ParamInv

/-! ### Generic parameters -/

section Generic

variable {L : Type*} [CommRing L] [NoZeroDivisors L] {q u : L}

/-- **Generic parameters have nonvanishing parameter product**: `M = (1 - q)(1 - u) ≠ 0`.

A parameter of an algebraically independent pair is transcendental, hence not equal to `1`, and the
ring has no zero divisors. So `M ≠ 0` is a consequence of the genericity hypothesis and never a
second hypothesis beside it. -/
theorem paramProduct_ne_zero (hqu : AlgebraicIndependent ℤ ![q, u]) : paramProduct q u ≠ 0 :=
  have h : ∀ i, (1 : L) - ![q, u] i ≠ 0 := fun i hi =>
    hqu.transcendental i ((sub_eq_zero.mp hi).symm ▸ isAlgebraic_one)
  mul_ne_zero (h 0) (h 1)

end Generic

/-! ### The cell sum determines the set of cells -/

section BmuInjective

variable {L : Type*} [CommRing L] {q u : L}

/-- The exponent vector of the monomial attached to the cell `c`: the cell `(i, j)` contributes
`Q^j U^i`, the column index on `Q` and the row index on `U`. -/
private noncomputable def cellExp (c : ℕ × ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 c.2 + Finsupp.single 1 c.1

private theorem cellExp_apply_zero (c : ℕ × ℕ) : cellExp c 0 = c.2 := by simp [cellExp]

private theorem cellExp_apply_one (c : ℕ × ℕ) : cellExp c 1 = c.1 := by simp [cellExp]

/-- A cell is read off its exponent vector, so distinct cells carry distinct monomials. -/
private theorem cellExp_injective : Function.Injective cellExp := fun c d h =>
  Prod.ext (by rw [← cellExp_apply_one c, ← cellExp_apply_one d, h])
    (by rw [← cellExp_apply_zero c, ← cellExp_apply_zero d, h])

private theorem monomial_cellExp (R : Type*) [CommSemiring R] (c : ℕ × ℕ) :
    (monomial (cellExp c) 1 : MvPolynomial (Fin 2) R) = X 0 ^ c.2 * X 1 ^ c.1 := by
  rw [cellExp, X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, mul_one]

/-- The generating polynomial of a finite set of cells by column and row index:
`∑_{(i,j) ∈ s} Q^j U^i`, a sum of `|s|` pairwise distinct monomials each with coefficient `1`.
Evaluating at `(q, u)` returns the cell sum of `s`, which at `s = cells μ` is `B_μ`. -/
private noncomputable def cellPoly (R : Type*) [CommSemiring R] (s : Finset (ℕ × ℕ)) :
    MvPolynomial (Fin 2) R :=
  ∑ c ∈ s, X 0 ^ c.2 * X 1 ^ c.1

/-- The value of `cellPoly R s` at the parameters is the cell sum of `s`. -/
private theorem aeval_cellPoly (R : Type*) [CommSemiring R] [Algebra R L] (q u : L)
    (s : Finset (ℕ × ℕ)) :
    MvPolynomial.aeval ![q, u] (cellPoly R s) = ∑ c ∈ s, cellWeight q u c := by
  rw [cellPoly, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp [cellWeight]

/-- The coefficient of `cellPoly R s` at a cell's exponent vector reads membership in `s`. -/
private theorem coeff_cellExp_cellPoly (R : Type*) [CommSemiring R] (s : Finset (ℕ × ℕ))
    (c : ℕ × ℕ) : coeff (cellExp c) (cellPoly R s) = if c ∈ s then 1 else 0 := by
  have hd : ∀ d : ℕ × ℕ, coeff (cellExp c) (X 0 ^ d.2 * X 1 ^ d.1 : MvPolynomial (Fin 2) R) =
      if d = c then 1 else 0 := fun d => by
    rw [← monomial_cellExp, coeff_monomial]
    simp only [cellExp_injective.eq_iff]
  rw [cellPoly, coeff_sum, Finset.sum_congr rfl fun d _ => hd d, Finset.sum_ite_eq' s c]

/-- **The cell sum determines the set of cells, at generic parameters.**

The sum `∑_{(i,j) ∈ s} q^j u^i` is the value at `(q, u)` of `cellPoly R s`, whose coefficient at a
cell's exponent vector is `1` or `0` according as the cell lies in `s`; genericity is exactly the
injectivity of that evaluation, so the coefficients, and with them `s`, are recovered from the sum.
`Nontrivial R` is what separates the two coefficients.

The usual argument appeals to the `ℚ`-linear independence of distinct monomials in `ℚ[q, u]`,
which presumes `q` and `u` are indeterminates; over a general field the statement fails without
genericity. Nothing in the argument asks the set of cells to be a lower set of
`ℕ × ℕ`, which is strictly more than being finite -- `{(1, 1)}` is no partition's set of cells --
so the diagram is not a hypothesis here; `eq_of_cellSum_eq` is the reading. The
coefficient ring is a variable because the `ℤ` reading is empty in positive characteristic; see the
implementation notes. The bundled form is this statement,
`fun _ _ h => eq_of_sum_cellWeight_eq hqu h` proving
`Function.Injective fun s => ∑ c ∈ s, cellWeight q u c`. -/
@[hjo "lem_ght2_bmu_injective"]
theorem eq_of_sum_cellWeight_eq {R : Type*} [CommRing R] [Nontrivial R] [Algebra R L]
    (hqu : AlgebraicIndependent R ![q, u]) {s t : Finset (ℕ × ℕ)}
    (h : ∑ c ∈ s, cellWeight q u c = ∑ c ∈ t, cellWeight q u c) : s = t := by
  have hpoly : cellPoly R s = cellPoly R t :=
    hqu <| by rw [aeval_cellPoly, aeval_cellPoly, h]
  refine Finset.ext fun c => ?_
  have hc : (if c ∈ s then (1 : R) else 0) = if c ∈ t then 1 else 0 := by
    rw [← coeff_cellExp_cellPoly, ← coeff_cellExp_cellPoly, hpoly]
  by_cases hs : c ∈ s <;> by_cases ht : c ∈ t <;> simp_all

/-- **The cell sum determines the partition, at generic parameters**: a partition is its set of
cells, so this is `eq_of_sum_cellWeight_eq` at `s = cells μ`. It is the form usually stated and
the form the eigenvalue argument below cites. -/
theorem eq_of_cellSum_eq {R : Type*} [CommRing R] [Nontrivial R] [Algebra R L]
    (hqu : AlgebraicIndependent R ![q, u]) {μ ν : YoungDiagram}
    (h : cellSum q u μ = cellSum q u ν) : μ = ν :=
  YoungDiagram.ext (eq_of_sum_cellWeight_eq hqu h)

end BmuInjective

/-! ### The eigenvalue attached to a partition -/

section DopZeroEigenvalue

variable {L : Type*} [CommRing L]

/-- The eigenvalue clause `(b)` attaches to the index `μ`: the scalar `-(M B_μ - 1)`. -/
def dopZeroEigenvalue (q u : L) (μ : YoungDiagram) : L :=
  -(paramProduct q u * cellSum q u μ - 1)

/-- At generic parameters the eigenvalue clause `(b)` attaches distinct scalars to distinct indices.
This is what makes the clause pin a family down.

Genericity is spent twice: on cancelling `M`, which it supplies nonzero (`paramProduct_ne_zero`),
and on reading the index off the cell sum. The first is exactly what fails at `M = 0`, where every
scalar is `1`. Cancelling is all the scalars are asked for, so this holds over any domain and not
only over the field the eigenbasis comparison below is stated for. -/
theorem eq_of_dopZeroEigenvalue_eq [NoZeroDivisors L] {q u : L}
    (hqu : AlgebraicIndependent ℤ ![q, u]) {μ ν : YoungDiagram}
    (h : dopZeroEigenvalue q u μ = dopZeroEigenvalue q u ν) : μ = ν := by
  rw [dopZeroEigenvalue, dopZeroEigenvalue, neg_inj, sub_left_inj] at h
  exact eq_of_cellSum_eq hqu (mul_left_cancel₀ (paramProduct_ne_zero hqu) h)

end DopZeroEigenvalue

end HJO.Sym

/-! ### A diagonal endomorphism in a basis -/

namespace Module.Basis

/-- **An endomorphism diagonal in a basis is diagonal on coordinates.** If `f (b j) = E j • b j`
for every `j`, then `f` multiplies the `i`-th coordinate of every vector by `E i`.

The index type is arbitrary, so this is not the `LinearMap.toMatrix` reading of diagonality, which
asks it to be finite; `hasEigenvector_toLin_diagonal` is that reading. The Mathlib sibling
`LinearMap.IsSymmetric.eigenvectorBasis_apply_self_apply` records the same identity for a symmetric
operator on an inner-product space. -/
theorem repr_apply_of_forall_apply_eq_smul {ι R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (b : Module.Basis ι R M) {f : Module.End R M} {E : ι → R}
    (hf : ∀ j, f (b j) = E j • b j) (i : ι) (y : M) : b.repr (f y) i = E i * b.repr y i := by
  classical
  have hfg : (Finsupp.lapply i).comp ((b.repr : M →ₗ[R] (ι →₀ R)).comp f) =
      E i • ((Finsupp.lapply i).comp (b.repr : M →ₗ[R] (ι →₀ R))) := by
    refine b.ext fun j => ?_
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, Finsupp.lapply_apply,
      LinearEquiv.coe_coe, smul_eq_mul]
    rw [hf j, map_smul, Finsupp.smul_apply, b.repr_self, Finsupp.single_apply, smul_eq_mul]
    by_cases h : j = i
    · subst h; rfl
    · simp [h]
  exact congrArg (fun m : M →ₗ[R] R => m y) hfg

/-- **The eigenspaces of an endomorphism diagonal in a basis are the coordinate lines.** If
`f (b j) = E j • b j` for every `j` and the eigenvalues `E` are pairwise distinct, then a nonzero
`x` with `f x = E i • x` is a nonzero multiple of `b i`.

Comparing the `j`-th coordinate of `f x` computed two ways gives `E i c_j = E j c_j`, so a nonzero
coordinate forces `E j = E i` and hence `j = i`: the expansion of `x` has the single term `c_i b i`,
and `c_i ≠ 0` because `x ≠ 0`. Cancelling the coordinate is what asks the ring to have no zero
divisors; nothing asks the index type or the module to be finite. Distinct eigenvalues make the
eigenvectors independent (`Module.End.eigenvectors_linearIndependent'`), which is weaker: it does
not say that an eigenvector at `E i` is accounted for by `b i` alone. -/
theorem exists_smul_of_apply_eq_smul {ι R M : Type*} [CommRing R] [NoZeroDivisors R]
    [AddCommGroup M] [Module R M] (b : Module.Basis ι R M) {f : Module.End R M} {E : ι → R}
    (hf : ∀ j, f (b j) = E j • b j) (hE : Function.Injective E) {i : ι} {x : M} (hx : x ≠ 0)
    (hfx : f x = E i • x) : ∃ c : R, c ≠ 0 ∧ x = c • b i := by
  have hkey : ∀ j, E i * b.repr x j = E j * b.repr x j := fun j => by
    have h := b.repr_apply_of_forall_apply_eq_smul hf j x
    rwa [hfx, map_smul, Finsupp.smul_apply, smul_eq_mul] at h
  have hsupp : (b.repr x).support ⊆ {i} := fun j hj =>
    Finset.mem_singleton.mpr
      (hE (mul_right_cancel₀ (Finsupp.mem_support_iff.mp hj) (hkey j))).symm
  obtain ⟨c, hc⟩ : ∃ c : R, b.repr x = Finsupp.single i c :=
    ⟨b.repr x i, Finsupp.support_subset_singleton.mp hsupp⟩
  have hxc : x = c • b i := by
    rw [← b.linearCombination_repr x, hc, Finsupp.linearCombination_single]
  exact ⟨c, fun h0 => hx (by rw [hxc, h0, zero_smul]), hxc⟩

end Module.Basis

namespace HJO.Sym

/-! ### Two families with the same `D_0` eigenvalues agree up to one scalar per index -/

section Unique

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-- **Two eigenbases agree up to one scalar per index.**

If `(H̃_μ)` is a `𝕜`-basis of `Λ` and `(G_μ)` is `𝕜`-linearly independent, and both satisfy
`D_0 F_μ = -(M B_μ - 1) F_μ`, then `G_μ` is a nonzero scalar multiple of `H̃_μ` for every `μ`.

Genericity of `q` and `u` is genuinely needed: it
is spent both on `M ≠ 0`, without which every eigenvalue is `1` and `D_0` is the identity, and on
the injectivity of the cell sum, without which the eigenvalue does not determine the index. Those
two failure modes are independent -- at `q = u` the cell sum fails to separate the two partitions
of `2` while `M = (1 - q)^2` is nonzero. But `M ≠ 0` is not a second hypothesis: it follows
from genericity by `paramProduct_ne_zero`. Linear independence of `(G_μ)`, rather than its being a
basis, is all the proof uses, so that is what is asked here. -/
@[hjo "lem_ght2_eigenbasis_unique"]
theorem exists_smul_of_dop_zero_eigenbasis (hqu : AlgebraicIndependent ℤ ![q, u])
    {H G : YoungDiagram → Lambda L} (hH : LinearIndependent L H)
    (hHsp : Submodule.span L (Set.range H) = ⊤) (hG : LinearIndependent L G)
    (hHdop : ∀ μ, Dop q u 0 (H μ) = dopZeroEigenvalue q u μ • H μ)
    (hGdop : ∀ μ, Dop q u 0 (G μ) = dopZeroEigenvalue q u μ • G μ)
    (μ : YoungDiagram) : ∃ c : L, c ≠ 0 ∧ G μ = c • H μ := by
  simpa [Module.Basis.mk_apply] using (Module.Basis.mk hH hHsp.ge).exists_smul_of_apply_eq_smul
    (E := dopZeroEigenvalue q u) (by simpa [Module.Basis.mk_apply] using hHdop)
    (fun _ _ h => eq_of_dopZeroEigenvalue_eq hqu h) (hG.ne_zero μ) (hGdop μ)

/-- **The support of the one-cell Pieri expansion, transported.**

This is `HJO.Standing.elemSymm_one_mul_mem_span_of_dop_zero_param`: a family that is a `𝕜`-basis of
`Λ` and satisfies clause `(b)` has `e₁ H̃_ν` in the span of the `H̃_μ` with `μ` covering `ν`. It is
proved by comparing the given family with the constructed `H̃` of `HJO.Sym.macHtilde`,
whose Pieri support is `HJO.Standing.elemSymm_one_mul_macHtilde_mem_span_param`, using
`HJO.Sym.exists_smul_of_dop_zero_eigenbasis`; that comparison is what is proved here, with the
constructed family's Pieri support as the hypothesis `hGpieri`. So this is that
lemma with its one deep input named rather than assumed away: the property passes from
**any one** such family to **every** such family, because the two differ by one nonzero scalar per
index and a scalar does not move a span.

`hGpieri` is a hypothesis the statement of
`HJO.Standing.elemSymm_one_mul_mem_span_of_dop_zero_param` does not carry, so this declaration does
not state its full content; the missing input is
`HJO.Standing.elemSymm_one_mul_macHtilde_mem_span_param`, which instantiates `hGpieri` at the
constructed `H̃`. Contrast the genericity hypothesis `hqu`, which is a correction to a statement
false without it. -/
theorem elemSymm_one_mul_mem_of_dop_zero (hqu : AlgebraicIndependent ℤ ![q, u])
    {H G : YoungDiagram → Lambda L} (hG : LinearIndependent L G)
    (hGdop : ∀ μ, Dop q u 0 (G μ) = dopZeroEigenvalue q u μ • G μ)
    (hGpieri : ∀ ν, elemSymm L 1 * G ν ∈ Submodule.span L (G '' {μ : YoungDiagram | Covers μ ν}))
    (hH : LinearIndependent L H) (hHsp : Submodule.span L (Set.range H) = ⊤)
    (hHdop : ∀ μ, Dop q u 0 (H μ) = dopZeroEigenvalue q u μ • H μ) (ν : YoungDiagram) :
    elemSymm L 1 * H ν ∈ Submodule.span L (H '' {μ : YoungDiagram | Covers μ ν}) := by
  have hcl : ∀ μ, ∃ c : L, c ≠ 0 ∧ G μ = c • H μ := fun μ =>
    exists_smul_of_dop_zero_eigenbasis hqu hH hHsp hG hHdop hGdop μ
  -- each `G μ` is a scalar multiple of `H μ`, so the span of the covering `G`'s sits inside the
  -- span of the covering `H`'s
  have hspan : Submodule.span L (G '' {μ : YoungDiagram | Covers μ ν}) ≤
      Submodule.span L (H '' {μ : YoungDiagram | Covers μ ν}) := by
    rw [Submodule.span_le]
    rintro x ⟨μ, hμ, rfl⟩
    obtain ⟨c, -, hcμ⟩ := hcl μ
    rw [hcμ]
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨μ, hμ, rfl⟩)
  obtain ⟨c, hc0, hcν⟩ := hcl ν
  have hrw : elemSymm L 1 * H ν = c⁻¹ • (elemSymm L 1 * G ν) := by
    rw [hcν, mul_smul_comm, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  rw [hrw]
  exact Submodule.smul_mem _ _ (hspan (hGpieri ν))

end Unique

end HJO.Sym

/-! ### Substituting `-X` in a polynomial -/

namespace Polynomial

/-- Substituting `-X` multiplies the coefficient of `X^n` by `(-1)^n`. -/
theorem coeff_comp_neg_X {R : Type*} [CommRing R] (Q : Polynomial R) (n : ℕ) :
    (Q.comp (-Polynomial.X)).coeff n = (-1) ^ n * Q.coeff n := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [Polynomial.add_comp, Polynomial.coeff_add, hp, hq, Polynomial.coeff_add, mul_add]
  | monomial k a =>
      have hneg : ((-1 : Polynomial R)) ^ k = Polynomial.C ((-1 : R) ^ k) := by
        rw [Polynomial.C_pow]; norm_num
      rw [Polynomial.monomial_comp, neg_pow, Polynomial.X_pow_eq_monomial, hneg,
        ← mul_assoc, ← Polynomial.C_mul, Polynomial.C_mul_monomial, mul_one,
        Polynomial.coeff_monomial, Polynomial.coeff_monomial]
      by_cases h : k = n
      · subst h; simp [mul_comm]
      · simp [h]

end Polynomial

namespace HJO.Sym

/-! ### The inversion on the displacement variable -/

section InversionW

variable {K : Type*} [CommRing K]

/-- The inversion `↓_z` read in the variable `w = z⁻¹` the displacements are written in: apply `↓`
to each coefficient and send `w` to `-w`. Since `w^j = z^{-j}`, the sign attached to `w^j` is
`(-1)^{-j} = (-1)^j`, which is what `coeff_inversionW` records.

The inversion `↓_z` itself is `inversionZ` of
`HJO/Macdonald/Inversion.lean`, which realises `↓_z` on `LaurentSeries (Lambda K)`. This is its
transcription into `Λ[w]`, the ring `plethShift` and `plethShiftStar` actually land in. -/
noncomputable def inversionW (ι : K →+* K) : Polynomial (Lambda K) →+* Polynomial (Lambda K) :=
  (Polynomial.eval₂RingHom (Polynomial.C : Lambda K →+* Polynomial (Lambda K))
    (-Polynomial.X)).comp (Polynomial.mapRingHom (inversion ι))

theorem inversionW_apply (ι : K →+* K) (P : Polynomial (Lambda K)) :
    inversionW ι P = (P.map (inversion ι)).comp (-Polynomial.X) := rfl

@[simp]
theorem coeff_inversionW (ι : K →+* K) (P : Polynomial (Lambda K)) (n : ℕ) :
    (inversionW ι P).coeff n = (-1) ^ n * inversion ι (P.coeff n) := by
  rw [inversionW_apply, Polynomial.coeff_comp_neg_X, Polynomial.coeff_map]

@[simp]
theorem inversionW_C (ι : K →+* K) (g : Lambda K) :
    inversionW ι (Polynomial.C g) = Polynomial.C (inversion ι g) := by
  rw [inversionW_apply, Polynomial.map_C, Polynomial.C_comp]

@[simp]
theorem inversionW_X (ι : K →+* K) :
    inversionW ι (Polynomial.X : Polynomial (Lambda K)) = -Polynomial.X := by
  rw [inversionW_apply, Polynomial.map_X, Polynomial.X_comp]

end InversionW

/-! ### The inversion carries `e_n` to `h_n` -/

section InversionEsymm

variable {K : Type*} [CommRing K] [Algebra ℚ K]

/-- **The inversion carries the elementary to the complete symmetric functions.** `↓ e_n = h_n`.

Both are defined by Newton's identity, and `↓` fixes the rational scalars and the signs while
multiplying `p_k` by `(-1)^{k-1}`; that sign cancels against the `(-1)^{k-1}` of the elementary
recursion, turning it into the complete one.

The hypothesis `hQ` is that `ι` fixes `ℚ`, which the `ι` does by fiat. -/
@[hjo "lem_ght2_inversion_esymm"]
theorem inversion_elemSymm (ι : K →+* K)
    (hQ : ∀ r : ℚ, ι (algebraMap ℚ K r) = algebraMap ℚ K r) :
    ∀ n : ℕ, inversion ι (elemSymm K n) = completeHomog K n
  | 0 => by rw [elemSymm, completeHomog, map_one]
  | n + 1 => by
      rw [elemSymm, completeHomog, map_mul, inversion_C, hQ, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      have hp : inversion ι (powerSum K (k + 1)) = (-1) ^ k * powerSum K (k + 1) := by
        rw [powerSum, Nat.add_sub_cancel, inversion_X]
      rw [map_mul, map_mul, map_pow, map_neg, map_one, hp,
        inversion_elemSymm ι hQ (n - k), ← mul_assoc]
      rw [show ((-1 : Lambda K)) ^ k * (-1) ^ k = 1 by
        rw [← pow_add, show k + k = 2 * k by ring, pow_mul]; norm_num, one_mul]

end InversionEsymm

/-! ### The inversion conjugates `D_0` into `D*_0`, and clause (iii) -/

section Clause3

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

omit [Algebra ℚ L] in
theorem coeffPairing_apply (c : ℕ → Lambda L) (P : Polynomial (Lambda L)) :
    coeffPairing c P = P.sum fun j A => A * c j := rfl

omit [Algebra ℚ L] in
/-- **The inversion carries the displacement to its starred form.** `↓_w(δ(↓f)) = δ*(f)`.

Both sides are ring homomorphisms `Λ → Λ[w]`, so it is enough to compare them on the coefficients
and on each `p_k`. On a coefficient `c` the left side is `ι(ι c) = c`, which is where involutivity
is used; on `p_k` the two signs `(-1)^{k-1}` -- one from `↓` on `p_k`, one from `↓_w` -- multiply to
`1` on the `p_k` term and to `-1` on the `z^{-k}` term, which is exactly the sign flip taking `δ`
to `δ*`, while `ι` inverts the two parameters in the scalar. -/
@[hjo "lem_ght2_inversion_shift"]
theorem inversionW_plethShift (ι : L →+* L) (hq : ι q = q⁻¹) (hu : ι u = u⁻¹)
    (hιι : ∀ c : L, ι (ι c) = c) (f : Lambda L) :
    inversionW ι (plethShift q u (inversion ι f)) = plethShiftStar q u f := by
  -- the value at each generator `p_{i+1}`: the two signs cancel on `p_{i+1}` and compose to `-1`
  -- on the `w^{i+1}` term, which is the flip taking `δ` to `δ*`
  have hX : ∀ i : ℕ, inversionW ι (plethShift q u (inversion ι (MvPolynomial.X i))) =
      plethShiftStar q u (MvPolynomial.X i) := by
    intro i
    have hpow : inversion ι (powerSum L (i + 1)) = (-1) ^ i * powerSum L (i + 1) := by
      rw [powerSum, Nat.add_sub_cancel, inversion_X]
    have hscal : inversion ι (MvPolynomial.C ((1 - q ^ (i + 1)) * (1 - u ^ (i + 1)))) =
        MvPolynomial.C ((1 - (q ^ (i + 1))⁻¹) * (1 - (u ^ (i + 1))⁻¹)) := by
      rw [inversion_C, map_mul, map_sub, map_sub, map_one, map_pow, map_pow, hq, hu, inv_pow,
        inv_pow]
    have hCneg : Polynomial.C ((-1 : Lambda L) ^ i) = (-1 : Polynomial (Lambda L)) ^ i := by
      rw [Polynomial.C_pow]; norm_num
    have hsq : ((-1 : Polynomial (Lambda L))) ^ i * (-1) ^ i = 1 := by
      rw [← pow_add, show i + i = 2 * i by ring, pow_mul]; norm_num
    have h1 : plethShift q u (inversion ι (MvPolynomial.X i)) =
        (-1 : Polynomial (Lambda L)) ^ i * (Polynomial.C (powerSum L (i + 1)) +
          Polynomial.C (MvPolynomial.C ((1 - q ^ (i + 1)) * (1 - u ^ (i + 1)))) *
            Polynomial.X ^ (i + 1)) := by
      rw [inversion_X, map_mul, map_pow, map_neg, map_one, plethShift, MvPolynomial.aeval_X]
    have hnegX : ((-Polynomial.X : Polynomial (Lambda L))) ^ (i + 1)
        = (-1) ^ i * (-1) * Polynomial.X ^ (i + 1) := by
      rw [← neg_one_mul (Polynomial.X : Polynomial (Lambda L)), mul_pow,
        pow_succ (-1 : Polynomial (Lambda L)) i]
    have key : ∀ s A B : Polynomial (Lambda L), s * s = 1 →
        s * (s * A + B * (s * (-1) * Polynomial.X ^ (i + 1))) = A - B * Polynomial.X ^ (i + 1) := by
      intro s A B hs
      have h : s * (s * A + B * (s * (-1) * Polynomial.X ^ (i + 1)))
          = (s * s) * A + (s * s) * (-(B * Polynomial.X ^ (i + 1))) := by ring
      rw [h, hs, one_mul, one_mul, sub_eq_add_neg]
    rw [h1, plethShiftStar_X, map_mul, map_pow, map_neg, map_one, map_add, map_mul, map_pow,
      inversionW_C, inversionW_C, inversionW_X, hpow, hscal, Polynomial.C_mul, hCneg, hnegX]
    exact key _ _ _ hsq
  induction f using MvPolynomial.induction_on with
  | C c =>
      rw [inversion_C]
      rw [show (MvPolynomial.C (ι c) : Lambda L) = algebraMap L (Lambda L) (ι c) from rfl,
        AlgHom.commutes, IsScalarTower.algebraMap_apply L (Lambda L) (Polynomial (Lambda L)),
        Polynomial.algebraMap_eq, inversionW_C,
        show (algebraMap L (Lambda L)) (ι c) = MvPolynomial.C (ι c) from rfl, inversion_C, hιι,
        show (MvPolynomial.C c : Lambda L) = algebraMap L (Lambda L) c from rfl, AlgHom.commutes,
        IsScalarTower.algebraMap_apply L (Lambda L) (Polynomial (Lambda L)),
        Polynomial.algebraMap_eq]
  | add p r hp hr => rw [map_add, map_add, map_add, hp, hr, map_add]
  | mul_X p i hp => rw [map_mul, map_mul, map_mul, hp, hX i, map_mul]

/-- **The inversion conjugates the degree-zero operator into its starred form.**
`D*_0 f = ↓(D_0(↓f))`.

This is Garsia--Haiman--Tesler's equation (1.14) c) at `k = 0`. `D_0` extracts the `z^0`
coefficient of `δ(g) · ∑_r (-z)^r e_r`; applying `↓` inverts the parameters in the displacement
(`inversionW_plethShift`) and turns each `(-1)^r e_r` into `h_r` (`inversion_elemSymm`, the two
signs cancelling), which is exactly what `D*_0` extracts. -/
@[hjo "lem_ght2_inversion_dop"]
theorem dopStar_zero_eq (ι : L →+* L) (hq : ι q = q⁻¹) (hu : ι u = u⁻¹)
    (hιι : ∀ c : L, ι (ι c) = c) (hQ : ∀ r : ℚ, ι (algebraMap ℚ L r) = algebraMap ℚ L r)
    (f : Lambda L) : DopStar q u 0 f = inversion ι (Dop q u 0 (inversion ι f)) := by
  classical
  set Q : Polynomial (Lambda L) := plethShift q u (inversion ι f) with hQdef
  have hP : plethShiftStar q u f = inversionW ι Q :=
    (inversionW_plethShift ι hq hu hιι f).symm
  have hsub : (inversionW ι Q).support ⊆ Q.support := by
    intro j hj
    rw [Polynomial.mem_support_iff] at hj ⊢
    intro h0
    exact hj (by rw [coeff_inversionW, h0, map_zero, mul_zero])
  rw [dopStar_apply, hP, coeffPairing_apply, Polynomial.sum_def,
    Finset.sum_subset hsub fun j _ hj => by
      rw [Polynomial.notMem_support_iff.mp hj, zero_mul]]
  rw [dop_apply, ← hQdef, coeffPairing_apply, Polynomial.sum_def, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coeff_inversionW, map_mul, map_mul, map_pow, map_neg, map_one,
    inversion_elemSymm ι hQ (0 + j), zero_add]
  ring

/-- **The starred eigenvalue relation from the unstarred one**: family clause (iii) from eigenbasis
clauses `(b)` and `(c)`.

Given `D_0 H̃_μ = -(M B_μ - 1) H̃_μ` and `↓H̃_μ = T_μ⁻¹ H̃_μ`, conjugating by `↓` gives
`D*_0 H̃_μ = -(M̃ B*_μ - 1) H̃_μ`. This is Garsia--Haiman--Tesler's Remark 1.1: their equation
(1.11) b) is not a second quoted fact but a consequence of (1.11) a).

The cell product `T_μ` must be invertible for the statement of clause `(c)` to be usable, which is
why `q ≠ 0` and `u ≠ 0` appear: over a general field the one-row two-cell partition has
`T_μ = q` exactly (`HJO.Sym.cellProd_ne_zero`). -/
@[hjo "lem_ght2_eigen_dop_star"]
theorem dopStar_zero_smul_of_dop_zero (hq0 : q ≠ 0) (hu0 : u ≠ 0) (ι : L →+* L) (hq : ι q = q⁻¹)
    (hu : ι u = u⁻¹) (hιι : ∀ c : L, ι (ι c) = c)
    (hQ : ∀ r : ℚ, ι (algebraMap ℚ L r) = algebraMap ℚ L r) {H : YoungDiagram → Lambda L}
    (hdop : ∀ μ, Dop q u 0 (H μ) = -(paramProduct q u * cellSum q u μ - 1) • H μ)
    (hinv : ∀ μ, inversion ι (H μ) = (cellProd q u μ)⁻¹ • H μ) (μ : YoungDiagram) :
    DopStar q u 0 (H μ) = -(paramProduct q⁻¹ u⁻¹ * cellSumInv q u μ - 1) • H μ := by
  have hT : cellProd q u μ ≠ 0 := cellProd_ne_zero hq0 hu0 μ
  rw [dopStar_zero_eq ι hq hu hιι hQ, hinv μ, map_smul, hdop μ]
  -- `↓` is not `𝕜`-linear: it applies `ι` to the scalar
  rw [inversion_smul, inversion_smul, hinv μ]
  rw [map_neg, map_sub, map_one, map_mul, paramInv_paramProduct ι hq hu,
    paramInv_cellSum ι hq hu, map_inv₀, paramInv_cellProd ι hq hu, inv_inv]
  rw [smul_smul, smul_smul]
  congr 1
  field_simp

end Clause3

/-! ### The reduction: an eigenbasis with Pieri support is a modified Macdonald family

Each declaration in this section has a hypothesis that the corresponding statement does not,
standing in for an input proved elsewhere.

`HJO.Standing.elemSymm_one_mul_mem_span_of_dop_zero_param` says that *every* family which is a
basis with clause `(b)` has the covering Pieri support; its proof gets that from the constructed
`H̃` of `HJO.Sym.macHtilde`, whose support is
`HJO.Standing.elemSymm_one_mul_macHtilde_mem_span_param`, resting on the construction of
Macdonald's polynomials. `elemSymm_one_mul_mem_of_dop_zero` above is the *transport* half of that
argument and is complete, but it takes the constructed family's support as the hypothesis
`hGpieri`.

Likewise `HJO.Standing.exists_isModifiedMacdonaldFamily_param'` asserts existence outright, while
`exists_isModifiedMacdonaldFamily` below asserts it *given* an eigenbasis with Pieri support. What
it does is make the remaining inputs exactly two, visible in one signature.
-/

section Reduction

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-- A Macdonald eigenbasis is a modified Macdonald family, once some family that is a basis with
clause `(b)` is known to have the covering Pieri support.

Clauses (i) and (ii) of `IsModifiedMacdonaldFamily` are clauses `(a)` and `(b)` of
`IsMacdonaldEigenbasis` verbatim. Clause (iii) is derived from `(b)` and `(c)` by
`dopStar_zero_smul_of_dop_zero`. Clause (iv) is transported from the witness `G` by
`elemSymm_one_mul_mem_of_dop_zero`.

`hGpieri` is a hypothesis `HJO.Standing.elemSymm_one_mul_mem_span_of_dop_zero_param` does not
carry, so this is not that statement. -/
theorem isModifiedMacdonaldFamily_of_isMacdonaldEigenbasis (hq0 : q ≠ 0) (hu0 : u ≠ 0)
    (hqu : AlgebraicIndependent ℤ ![q, u]) (ι : L →+* L) (hq : ι q = q⁻¹) (hu : ι u = u⁻¹)
    (hιι : ∀ c : L, ι (ι c) = c)
    (hQ : ∀ r : ℚ, ι (algebraMap ℚ L r) = algebraMap ℚ L r) {G : YoungDiagram → Lambda L}
    (hG : LinearIndependent L G)
    (hGdop : ∀ μ, Dop q u 0 (G μ) = dopZeroEigenvalue q u μ • G μ)
    (hGpieri : ∀ ν, elemSymm L 1 * G ν ∈ Submodule.span L (G '' {μ : YoungDiagram | Covers μ ν}))
    {H : YoungDiagram → Lambda L} (hH : IsMacdonaldEigenbasis ι q u H) :
    IsModifiedMacdonaldFamily q u H where
  linearIndependent := hH.linearIndependent
  span_eq_top := hH.span_eq_top
  dop_zero := hH.dop_zero
  dopStar_zero :=
    dopStar_zero_smul_of_dop_zero hq0 hu0 ι hq hu hιι hQ hH.dop_zero hH.inversion_apply
  elemSymm_one_mul_mem :=
    elemSymm_one_mul_mem_of_dop_zero hqu hG hGdop hGpieri hH.linearIndependent hH.span_eq_top
      fun μ => hH.dop_zero μ

/-- **`HJO.Standing.exists_isModifiedMacdonaldFamily_param'` modulo exactly two inputs.**

A modified Macdonald family exists, given a Macdonald eigenbasis whose `e₁`-products have covering
support. The two hypotheses are `HJO.Standing.hasUnnormalisedMacdonaldEigenbasis_param` and
`HJO.Standing.elemSymm_one_mul_macHtilde_mem_span_param`; everything else the statement needs --
clause (iii) from the parameter inversion, clause (iv) from the uniqueness of the eigenvalue
decomposition -- is proved above.

The genericity hypothesis is a correction, not a weakening:
`HJO.Sym.exists_smul_of_dop_zero_eigenbasis`, which clause (iv) passes through, is false at `M = 0`
and false at non-generic `(q, u)`. It covers the first of those by itself, through
`paramProduct_ne_zero`, so `M ≠ 0` is not asked for separately.

`hex` is a substantive hypothesis that `HJO.Standing.exists_isModifiedMacdonaldFamily_param'` does
not carry. -/
theorem exists_isModifiedMacdonaldFamily (hq0 : q ≠ 0) (hu0 : u ≠ 0)
    (hqu : AlgebraicIndependent ℤ ![q, u]) (ι : L →+* L) (hq : ι q = q⁻¹) (hu : ι u = u⁻¹)
    (hιι : ∀ c : L, ι (ι c) = c)
    (hQ : ∀ r : ℚ, ι (algebraMap ℚ L r) = algebraMap ℚ L r)
    (hex : ∃ H : YoungDiagram → Lambda L, IsMacdonaldEigenbasis ι q u H ∧
      ∀ ν, elemSymm L 1 * H ν ∈ Submodule.span L (H '' {μ : YoungDiagram | Covers μ ν})) :
    ∃ H : YoungDiagram → Lambda L, IsModifiedMacdonaldFamily q u H := by
  obtain ⟨H, hH, hpieri⟩ := hex
  exact ⟨H, isModifiedMacdonaldFamily_of_isMacdonaldEigenbasis hq0 hu0 hqu ι hq hu hιι hQ
    hH.linearIndependent (fun μ => hH.dop_zero μ) hpieri hH⟩

/-- The whole of the collinear side, assembled here: a Macdonald conjugator exists, given a
Macdonald eigenbasis with covering Pieri support.

This composes `exists_isModifiedMacdonaldFamily` with `exists_isMacdonaldConjugator`
(`HJO/Macdonald/Conjugator.lean`), whose only substantive hypothesis is the existence of a
modified Macdonald family. It is recorded here so that what an unconditional Macdonald conjugator
needs beyond this file is one hypothesis in one signature. -/
theorem exists_isMacdonaldConjugator_of_exists_isMacdonaldEigenbasis (hq0 : q ≠ 0) (hu0 : u ≠ 0)
    (hqu : AlgebraicIndependent ℤ ![q, u]) (ι : L →+* L) (hq : ι q = q⁻¹) (hu : ι u = u⁻¹)
    (hιι : ∀ c : L, ι (ι c) = c)
    (hQ : ∀ r : ℚ, ι (algebraMap ℚ L r) = algebraMap ℚ L r)
    (hex : ∃ H : YoungDiagram → Lambda L, IsMacdonaldEigenbasis ι q u H ∧
      ∀ ν, elemSymm L 1 * H ν ∈ Submodule.span L (H '' {μ : YoungDiagram | Covers μ ν})) :
    ∃ nabla : Module.End L (Lambda L), IsMacdonaldConjugator q u nabla :=
  exists_isMacdonaldConjugator hq0 hu0 (paramProduct_ne_zero hqu)
    (exists_isModifiedMacdonaldFamily hq0 hu0 hqu ι hq hu hιι hQ hex)

end Reduction

end HJO.Sym
