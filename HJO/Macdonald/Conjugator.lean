/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Collinear.Commutation
public import HJO.Macdonald.Family
public meta import HJO.Attr

/-! # From a modified Macdonald family to a Macdonald conjugator

The eigenoperator `∇` of a modified Macdonald family is a Macdonald conjugator. This file proves
the four properties that says -- `∇` is bijective, it commutes with `D_0`, it carries
multiplication by `e₁` to `-D_1`, and it carries `D*_1` to multiplication by `e₁` -- and assembles
them into the existence statement.

The assembly takes the *existence of a modified Macdonald family as a hypothesis*. That family is
built from Macdonald polynomial theory, which is a separate part of the library, so the
only input of `exists_isMacdonaldConjugator` below beyond what is proved here is that one
existence statement.

## Main results

* `HJO.Sym.sub_cellSum_of_cells_eq_insert`, `HJO.Sym.cellProd_of_cells_eq_insert`: the weight of a
  single added cell is both the increment of the cell sums and the ratio of the cell products.
* `HJO.Sym.sub_cellSum_mul_of_covers`, `HJO.Sym.sub_cellSum_one_one`: that increment is
  multiplicative in the parameter pair and is `1` at the trivial pair, so at a pair inverting the
  first it reads `(B_μ - B_ν)(B*_μ - B*_ν) = 1`.
* `HJO.Sym.cellProd_of_covers`: adding one cell to a partition multiplies the cell product by the
  increment of the cell sums.
* `HJO.Sym.cellProd_mul_sub_cellSum_of_mul_eq_one`: the same with the second parameter pair carried
  as data, `T_μ (B_μ(q', u') - B_ν(q', u')) = T_ν` whenever `q q' = 1` and `u u' = 1`.
* `HJO.Sym.cellProd_of_covers_cellSumInv`, `HJO.Sym.cellProd_mul_sub_cellSumInv_of_ne`: the same
  for the inverted cell sums, whose increment divides the cell product instead of multiplying it.
* `HJO.Sym.bijective_of_isEigenoperator`: `∇` is bijective.
* `HJO.Sym.nabla_dop_zero`: `∇(D_0 f) = D_0(∇ f)`.
* `HJO.Sym.nabla_elemSymm_one_mul`: `∇(e₁ f) = -D_1(∇ f)`.
* `HJO.Sym.nabla_dopStar_one`: `∇(D*_1 f) = e₁ · ∇ f`.
* `HJO.Sym.exists_isMacdonaldConjugator`: a Macdonald conjugator exists, given a modified
  Macdonald family.

## Implementation notes

The relations proved here are Garsia--Haiman--Tesler's and Bergeron--Garsia--Leven--Xin's,
`∇ e₁ ∇⁻¹ = -D_1` and `∇ D*_1 ∇⁻¹ = e₁`, which is what `IsMacdonaldConjugator` asks for.
Carlsson--Mellit assert the negative of this pair on *both* clauses; the two conventions differ by
the grading sign `f ↦ (-1)^(deg f) f` and are not interchangeable. Nothing here switches between
them.

Both cover-ratio identities rest on one fact about a single cell: if the cells of `μ` are those of
`ν` with `c` inserted, then `w(c)` is at once the increment `B_μ - B_ν` of the cell sums and the
ratio `T_μ / T_ν` of the cell products. It is stated here of the cell *decomposition* rather than
as an existential over a cover, because the consumers read it at several parameter pairs *at the
same cell*: `cellProd_of_covers_cellSumInv` needs the product ratio at `(q, u)` and the sum
increment at `(q⁻¹, u⁻¹)`, and `sub_cellSum_mul_of_covers` needs the sum increment at `(q, u)`,
`(q', u')` and `(q q', u u')`. An existential packaging would hand each of those a fresh cell.
Splitting it in two also keeps each half at its own class: the product ratio is a `CommMonoid`
statement, and only the increment, being a difference, needs a `CommRing`.

Over a general field the appeals to "`x` is a nonzero element of `𝕜 = ℚ(q, u)`" become
explicit hypotheses:

* `cellProd q u μ = ∏_c q^j u^i` is nonzero as soon as `q ≠ 0` and `u ≠ 0`, so `hq` and `hu` are
  carried by `cellProd_ne_zero` and by `bijective_of_isEigenoperator`. The converse fails for small
  `μ`: the empty diagram and the single cell both give the value `1` whatever `q` and `u` are. The
  starred cover-ratio identity needs no hypothesis at all, and no field either: with the inverting
  pair carried as data it is `cellProd_mul_sub_cellSum_of_mul_eq_one`, over any commutative ring.
  What costs a side condition is the spelling `B*_μ = ∑_c w(c)⁻¹`, for at `q = 0` a cell outside
  column zero has weight zero and increment `0⁻¹ = 0`; so `cellProd_of_covers_cellSumInv` inverts
  the increment instead, and the arrangement, `cellProd_mul_sub_cellSumInv_of_ne`,
  asks exactly that it be nonzero -- a condition on the added cell alone, which `hq` and `hu`
  reach through `cellProd_mul_sub_cellSumInv`.
* `M = (1 - q)(1 - u)` is cancelled in `nabla_elemSymm_one_mul`, so `hM` appears there. The same
  hypothesis is used in `HJO/Collinear/Commutation.lean`.
* `M̃ = (1 - q⁻¹)(1 - u⁻¹)` is cancelled in `nabla_dopStar_one`. It needs no hypothesis of its own:
  `paramProduct_inv_ne_zero` derives `M̃ ≠ 0` from `M ≠ 0` alone, since `M ≠ 0` gives `q ≠ 1` and
  `q⁻¹ = 1` forces `q = 1` even where `0⁻¹ = 0`.

## References

This file formalises Lemmas `HJO.Sym.bijective_of_isEigenoperator`, `HJO.Sym.nabla_dop_zero`,
`HJO.Sym.nabla_elemSymm_one_mul`, `HJO.Sym.nabla_dopStar_one` and
`HJO.Sym.exists_isMacdonaldConjugator`. The steps they are built from are proved below as
`cellProd_of_covers`, `cellProd_of_covers_cellSumInv`, `dopStar_elemSymm_one_mul` (stated for every
`k`), `nabla_commutator` and `nabla_commutator_star`; the starred cover ratio is stated three times,
its reading over a general commutative ring being `cellProd_mul_sub_cellSum_of_mul_eq_one` and the
field arrangement `cellProd_mul_sub_cellSumInv_of_ne`. The unstarred companion
`HJO.Sym.dop_elemSymm_one_mul` is *not* reproved: it is proved in
`HJO/Collinear/Commutation.lean`, stated for every `k`, and is used from there.

The relations are Proposition 1.5, equations (1.30) b) and b*), and Proposition 1.4, equation
(1.28), of A. M. Garsia, M. Haiman and G. Tesler, *Explicit plethystic formulas for Macdonald
(q,t)-Kostka coefficients*, Sém. Lothar. Combin. **42** (1999), B42m, and clauses (iii) and (iii)*
of Proposition 1.1 of F. Bergeron, A. M. Garsia, E. Leven and G. Xin, *Some remarkable new
plethystic operators in the theory of Macdonald polynomials*, arXiv:1405.0316, J. Comb. **7**
(2016) 671--714.
-/

@[expose] public section

namespace HJO.Sym

/-! ### Adding a cell to a partition -/

section Cover

variable {K : Type*}

/-- A partition covering another has exactly one cell more, so its cells are the cells of the
smaller one with a single further cell inserted. -/
theorem exists_cell_of_covers {μ ν : YoungDiagram} (h : Covers μ ν) :
    ∃ c ∉ cells ν, cells μ = insert c (cells ν) := by
  obtain ⟨hle, hcard⟩ := h
  obtain ⟨c, hc, hins⟩ :=
    Finset.exists_eq_insert_iff.2 ⟨YoungDiagram.cells_subset_iff.mpr hle, hcard.symm⟩
  exact ⟨c, hc, hins.symm⟩

/-- The cell product over a diagram whose cells are those of another with one further cell
inserted: the added cell contributes its weight as a factor, `T_μ = w(c) T_ν`. -/
theorem cellProd_of_cells_eq_insert [CommMonoid K] (q u : K) {μ ν : YoungDiagram} {c : ℕ × ℕ}
    (hc : c ∉ cells ν) (hins : cells μ = insert c (cells ν)) :
    cellProd q u μ = cellWeight q u c * cellProd q u ν := by
  simp only [cellProd, hins, Finset.prod_insert hc]

/-- **The one-cell increment of the cell sum is the added cell's weight.** If the cells of `μ` are
those of `ν` with one further cell `c` inserted then `B_μ - B_ν = w(c)`.

Together with `cellProd_of_cells_eq_insert` this is the justification Garsia--Haiman--Tesler give
for their equation (1.33) `B_μ - B_ν = T_μ / T_ν`: that monomial is precisely the weight of the
cell one must add to `ν` to get `μ`. -/
theorem sub_cellSum_of_cells_eq_insert [CommRing K] (q u : K) {μ ν : YoungDiagram} {c : ℕ × ℕ}
    (hc : c ∉ cells ν) (hins : cells μ = insert c (cells ν)) :
    cellSum q u μ - cellSum q u ν = cellWeight q u c := by
  simp only [cellSum, hins, Finset.sum_insert hc, add_sub_cancel_right]

/-- **The one-cell increment of the cell sum is multiplicative in the parameter pair.** If `μ`
covers `ν` then
`B_μ(q q', u u') - B_ν(q q', u u') = (B_μ(q, u) - B_ν(q, u)) (B_μ(q', u') - B_ν(q', u'))`: the
increment is a single cell weight, and a cell weight is multiplicative in its parameters
(`cellWeight_mul`).

At a second pair inverting the first this reads `(B_μ - B_ν)(B*_μ - B*_ν) = 1`, the cancellation
the starred cover-ratio identity turns on; `cellWeight_mul` alone does not reach it, saying nothing
about a cover. -/
theorem sub_cellSum_mul_of_covers [CommRing K] (q u q' u' : K) {μ ν : YoungDiagram}
    (h : Covers μ ν) :
    cellSum (q * q') (u * u') μ - cellSum (q * q') (u * u') ν
      = (cellSum q u μ - cellSum q u ν) * (cellSum q' u' μ - cellSum q' u' ν) := by
  obtain ⟨c, hc, hins⟩ := exists_cell_of_covers h
  rw [sub_cellSum_of_cells_eq_insert (q * q') (u * u') hc hins,
    sub_cellSum_of_cells_eq_insert q u hc hins, sub_cellSum_of_cells_eq_insert q' u' hc hins,
    cellWeight_mul]

/-- **The one-cell increment of the cell sum is `1` at the trivial parameter pair.** If `μ` covers
`ν` then `B_μ(1, 1) - B_ν(1, 1) = 1`: the increment is the added cell's weight, and every cell
weighs `1` there.

Read against `sub_cellSum_mul_of_covers` this is the cancellation the starred cover-ratio identity
turns on, the product of the increments at an inverting pair being the increment at `(1, 1)`. -/
theorem sub_cellSum_one_one [CommRing K] {μ ν : YoungDiagram} (h : Covers μ ν) :
    cellSum (1 : K) 1 μ - cellSum (1 : K) 1 ν = 1 := by
  obtain ⟨c, hc, hins⟩ := exists_cell_of_covers h
  simp only [sub_cellSum_of_cells_eq_insert (1 : K) 1 hc hins, cellWeight, one_pow, one_mul]

/-- **Adding a cell multiplies the cell product by the difference of the cell sums.**
If `μ` covers `ν` then `T_μ = (B_μ - B_ν) T_ν`: the single extra cell `c` contributes `w(c)` to the
cell sum and multiplies the cell product by `w(c)`. This is Garsia--Haiman--Tesler's equation
(1.33), cleared of the division. -/
@[hjo "lem_ght_cover_ratio"]
theorem cellProd_of_covers [CommRing K] (q u : K) {μ ν : YoungDiagram} (h : Covers μ ν) :
    cellProd q u μ = (cellSum q u μ - cellSum q u ν) * cellProd q u ν := by
  obtain ⟨c, hc, hins⟩ := exists_cell_of_covers h
  rw [sub_cellSum_of_cells_eq_insert q u hc hins, cellProd_of_cells_eq_insert q u hc hins]

/-- **Adding a cell, against the cell sums at an inverting pair.** If `q q' = 1` and `u u' = 1` and
`μ` covers `ν` then `T_μ (B_μ(q', u') - B_ν(q', u')) = T_ν`. This is
the starred cover-ratio identity in its displayed arrangement, with the inverting
parameters carried as data; so read, it asks nothing of the ring beyond commutativity, nothing of
the cover and nothing of the added cell, where the field readings below need `q` and `u` invertible
to write `B*` at all.

The mechanism is that the added cell's weight and its weight at the inverting pair multiply to `1`
-- `sub_cellSum_mul_of_covers` evaluated by `sub_cellSum_one_one` -- so both hypotheses are spent,
and only through that cancelled factor: over `ℚ` at `q = 2`, `u = u' = 1`, `q' = 1` the row of two
covers the row of one by a cell of weight `2` and the display reads `2 = 1`, while at `q = q' = 1`,
`u = 2`, `u' = 1` the column of two does the same over the single cell. The second witness has to
add a cell off row zero, `u` not occurring in the weight of a cell there. -/
@[hjo "lem_ght_cover_ratio_star"]
theorem cellProd_mul_sub_cellSum_of_mul_eq_one [CommRing K] {q u q' u' : K}
    (hq : q * q' = 1) (hu : u * u' = 1) {μ ν : YoungDiagram} (h : Covers μ ν) :
    cellProd q u μ * (cellSum q' u' μ - cellSum q' u' ν) = cellProd q u ν := by
  rw [cellProd_of_covers q u h, mul_right_comm, ← sub_cellSum_mul_of_covers q u q' u' h,
    hq, hu, sub_cellSum_one_one h, one_mul]

/-- **Adding a cell and the inverted cell sums.** If `μ` covers `ν` then
`T_μ = (B*_μ - B*_ν)⁻¹ T_ν`: the extra cell `c` contributes `w(c)` to the cell product and `w(c)⁻¹`
to the inverted cell sum, and inverting the second returns the first. This is
`HJO.Sym.cellProd_mul_sub_cellSum_of_mul_eq_one` in the field spelling of `B*`, reoriented into the
arrangement of the unstarred `cellProd_of_covers` above -- the cell product alone on the left, the
one-cell increment as a factor on the right.

So arranged it needs no hypothesis on `q`, `u` or `μ`: where the added cell has weight zero both
sides vanish, `(0⁻¹)⁻¹` being `0`. The other arrangement,
`T_μ (B*_μ - B*_ν) = T_ν`, is false at such a cell and is
`cellProd_mul_sub_cellSumInv_of_ne` below. -/
@[hjo "lem_ght_cover_ratio_star"]
theorem cellProd_of_covers_cellSumInv [Field K] (q u : K) {μ ν : YoungDiagram} (h : Covers μ ν) :
    cellProd q u μ = (cellSumInv q u μ - cellSumInv q u ν)⁻¹ * cellProd q u ν := by
  obtain ⟨c, hc, hins⟩ := exists_cell_of_covers h
  rw [cellSumInv_eq_cellSum_inv, cellSumInv_eq_cellSum_inv,
    sub_cellSum_of_cells_eq_insert q⁻¹ u⁻¹ hc hins, ← cellWeight_inv, inv_inv,
    cellProd_of_cells_eq_insert q u hc hins]

/-- **Adding a cell and the inverted cell sums, the arrangement.** If `μ` covers `ν`
and the inverted cell sums differ then `T_μ (B*_μ - B*_ν) = T_ν`: the identity above with the
one-cell increment cancelled rather than inverted.

The hypothesis is exactly what that cancellation spends, and it is a condition on the added cell
alone -- the increment is the inverse of that cell's weight, so it is nonzero precisely where the
weight is. It cannot be dropped: at a cell of weight zero the left side vanishes and `T_ν` need
not.

Nor is this `cellProd_mul_sub_cellSum_of_mul_eq_one` read at `q' = q⁻¹`, `u' = u⁻¹`, which would
ask `q ≠ 0` and `u ≠ 0`: those are strictly stronger than `hne`, which holds for the single cell
over the empty diagram at `q = 0`, where the added cell `(0, 0)` still weighs `1` and no inverting
pair exists. Stated with the inverting pair carried as data, which is that general reading, the
equation needs no hypothesis beyond the cover; the side condition is the price of the spelling
`B*_μ = ∑_c w(c)⁻¹`, and over `𝕜 = ℚ(q, u)` there is no cell of weight zero to meet. -/
@[hjo "lem_ght_cover_ratio_star"]
theorem cellProd_mul_sub_cellSumInv_of_ne [Field K] {q u : K} {μ ν : YoungDiagram}
    (h : Covers μ ν) (hne : cellSumInv q u μ ≠ cellSumInv q u ν) :
    cellProd q u μ * (cellSumInv q u μ - cellSumInv q u ν) = cellProd q u ν := by
  rw [cellProd_of_covers_cellSumInv q u h, mul_right_comm,
    inv_mul_cancel₀ (sub_ne_zero_of_ne hne), one_mul]

/-- The arrangement above under `T_μ ≠ 0`, which `cellProd_ne_zero` supplies from `q ≠ 0` and
`u ≠ 0`: a cell product that does not vanish has no cell of weight zero, the added one included.
This is the reading the eigenoperator computations below use, carrying `hq` and `hu` as they do.
The hypothesis is strictly stronger than the increment's -- it constrains every cell of `μ` where
the increment constrains one -- and the extra strength buys nothing: on the instances it discards
both sides vanish, `T_μ = 0` with a nonzero increment forcing `T_ν = 0`. -/
theorem cellProd_mul_sub_cellSumInv [Field K] {q u : K} {μ ν : YoungDiagram} (h : Covers μ ν)
    (hμ : cellProd q u μ ≠ 0) :
    cellProd q u μ * (cellSumInv q u μ - cellSumInv q u ν) = cellProd q u ν :=
  cellProd_mul_sub_cellSumInv_of_ne h fun h0 =>
    hμ (by rw [cellProd_of_covers_cellSumInv q u h, h0, sub_self, inv_zero, zero_mul])

/-- The cell product of a partition is nonzero as soon as both parameters are: it is a product of
cell weights `q ^ j * u ^ i`. -/
theorem cellProd_ne_zero [Field K] {q u : K} (hq : q ≠ 0) (hu : u ≠ 0) (μ : YoungDiagram) :
    cellProd q u μ ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun _ _ => mul_ne_zero (pow_ne_zero _ hq) (pow_ne_zero _ hu)

/-- `M̃ = (1 - q⁻¹)(1 - u⁻¹)` is nonzero as soon as `M = (1 - q)(1 - u)` is. No hypothesis on `q`
and `u` themselves is needed: `M ≠ 0` gives `q ≠ 1`, and `q⁻¹ = 1` forces `q = 1` even in a field
where `0⁻¹ = 0`. -/
theorem paramProduct_inv_ne_zero [Field K] {q u : K}
    (hM : paramProduct q u ≠ 0) : paramProduct q⁻¹ u⁻¹ ≠ 0 := by
  have key : ∀ x : K, (1 : K) - x ≠ 0 → (1 : K) - x⁻¹ ≠ 0 := fun x hx =>
    sub_ne_zero.2 fun h => sub_ne_zero.1 hx (inv_eq_one.1 h.symm).symm
  exact mul_ne_zero (key q fun h => hM (by rw [paramProduct, h, zero_mul]))
    (key u fun h => hM (by rw [paramProduct, h, mul_zero]))

end Cover

/-! ### The starred operators against multiplication by `e₁` -/

section DopStarE1

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **The starred displacement of the first elementary symmetric function.**
`e₁[X - M̃/z] = e₁ - M̃ z⁻¹`. The minus sign of the starred alphabet is not squared, so the scalar
is `M̃ = (1 - q⁻¹)(1 - u⁻¹)` itself — that is `HJO.Sym.paramProductInv`, which is
`paramProduct q⁻¹ u⁻¹` and so the expression below.

No hypothesis on `q` or `u` is needed: this is the defining formula of `HJO.Sym.plethShiftStar` at
`k = 1`, read through `e₁ = p₁`. The closed form at general `n`,
`HJO.Sym.plethShiftStar_elemSymm`, does need `q, u ≠ 0` and `q u ≠ 1`, since it
divides by `1 - q u`; the two agree at `n = 1`. -/
@[hjo "lem_shift_star_e1"]
theorem plethShiftStar_elemSymm_one (q u : L) :
    plethShiftStar q u (elemSymm L 1) =
      Polynomial.C (elemSymm L 1) -
        Polynomial.C (MvPolynomial.C (paramProduct q⁻¹ u⁻¹)) * Polynomial.X := by
  rw [elemSymm_one_eq_X, plethShiftStar, MvPolynomial.aeval_X]
  simp only [powerSum, zero_add, tsub_self, pow_one, map_mul, map_sub, map_one, paramProduct]

/-- **The starred operators against multiplication by `e₁`.** For every `k ≥ 0` and every `f ∈ Λ`,
`D*_k(e₁ f) = e₁ D*_k f - M̃ D*_{k+1} f`. The starred displacement is an algebra map, so it turns
the product into `(e₁ - M̃ z⁻¹) f[X - M̃/z]`; the first summand contributes `e₁ D*_k f`, and the
single power of `z⁻¹` in the second shifts the extracted coefficient from `zᵏ` to `z^{k+1}`.

Its `k = 0` case is Proposition 1.4, equation (1.28) b), of Garsia--Haiman--Tesler. No hypothesis on
`q` or `u` is needed: `HJO.Sym.plethShiftStar_elemSymm_one` carries none, and the pairing identities
are algebra. -/
@[hjo "lem_dopstar_e1"]
theorem dopStar_elemSymm_one_mul (q u : L) (k : ℕ) (f : Lambda L) :
    DopStar q u k (elemSymm L 1 * f) =
      elemSymm L 1 * DopStar q u k f - paramProduct q⁻¹ u⁻¹ • DopStar q u (k + 1) f := by
  have hfam : (fun j => completeHomog L (k + (j + 1))) =
      fun j => completeHomog L (k + 1 + j) := by
    funext j
    rw [show k + (j + 1) = k + 1 + j by omega]
  rw [dopStar_apply, dopStar_apply, dopStar_apply, map_mul, plethShiftStar_elemSymm_one, sub_mul,
    map_sub, mul_assoc, coeffPairing_C_mul, coeffPairing_C_mul, coeffPairing_X_mul, hfam,
    MvPolynomial.smul_eq_C_mul]

attribute [hjo "lem_ght_dopstar_zero_e1"] dopStar_elemSymm_one_mul

end DopStarE1

/-! ### The eigenoperator of a modified Macdonald family -/

section Conjugator

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L} {H : YoungDiagram → Lambda L}
  {nabla : Module.End L (Lambda L)}

/-- Multiplication by `e₁`, as an endomorphism of `Λ`. -/
private noncomputable def mulE1 (L : Type*) [Field L] [Algebra ℚ L] :
    Module.End L (Lambda L) :=
  LinearMap.mulLeft L (elemSymm L 1)

@[simp]
private theorem mulE1_apply (f : Lambda L) : mulE1 L f = elemSymm L 1 * f := rfl

/-- **The eigenoperator is bijective.** Prescribing `H̃_μ ↦ T_μ⁻¹ H̃_μ` on the basis gives a
two-sided inverse, since every cell product `T_μ` is a nonzero scalar.

Over `ℚ(q, u)` the nonvanishing of `T_μ` is read off the fact that a cell weight is a monomial in
`ℚ(q, u)`; over a general field it is exactly `q ≠ 0` and `u ≠ 0`. -/
@[hjo "lem_ght_scaling_bijective"]
theorem bijective_of_isEigenoperator (hq : q ≠ 0) (hu : u ≠ 0)
    (h : IsModifiedMacdonaldFamily q u H) (hn : IsEigenoperator q u H nabla) :
    Function.Bijective nabla := by
  set Psi : Module.End L (Lambda L) := h.basis.constr L fun μ => (cellProd q u μ)⁻¹ • H μ
    with hPsidef
  have hPsi : ∀ μ, Psi (H μ) = (cellProd q u μ)⁻¹ • H μ := fun μ => by
    rw [hPsidef, ← h.basis_apply μ, Module.Basis.constr_basis, h.basis_apply]
  have h1 : Psi ∘ₗ nabla = LinearMap.id := h.basis.ext fun μ => by
    simp only [LinearMap.comp_apply, h.basis_apply, hn μ, map_smul, hPsi, LinearMap.id_apply,
      smul_smul, mul_inv_cancel₀ (cellProd_ne_zero hq hu μ), one_smul]
  have h2 : nabla ∘ₗ Psi = LinearMap.id := h.basis.ext fun μ => by
    simp only [LinearMap.comp_apply, h.basis_apply, hPsi, map_smul, hn μ, LinearMap.id_apply,
      smul_smul, inv_mul_cancel₀ (cellProd_ne_zero hq hu μ), one_smul]
  exact Function.bijective_iff_has_inverse.2 ⟨Psi,
    fun x => by simpa using DFunLike.congr_fun h1 x,
    fun x => by simpa using DFunLike.congr_fun h2 x⟩

/-- **The eigenoperator commutes with the degree-zero operator.** Both sides are linear in `f`, so
it is enough to check the identity at `f = H̃_μ`, where `D_0` acts by the scalar `-(M B_μ - 1)`
(clause (ii) of the family) and `∇` by the scalar `T_μ`; two scalars commute.

This is where the diagonality of `D_0` on the modified Macdonald basis is used. -/
@[hjo "lem_ght_nabla_dop_zero"]
theorem nabla_dop_zero (h : IsModifiedMacdonaldFamily q u H)
    (hn : IsEigenoperator q u H nabla) (f : Lambda L) :
    nabla (Dop q u 0 f) = Dop q u 0 (nabla f) := by
  have key : nabla ∘ₗ Dop q u 0 = Dop q u 0 ∘ₗ nabla := h.basis.ext fun μ => by
    simp only [LinearMap.comp_apply, h.basis_apply]
    rw [h.dop_zero μ, map_smul, hn μ, map_smul, h.dop_zero μ]
    module
  simpa using DFunLike.congr_fun key f

/-- The commutator computation of `nabla_commutator`, carried out on the span in which clause (iv)
of the family places `e₁ H̃_ν`. On a generator `H̃_μ` with `μ` covering `ν` the two scalar clauses
collapse the left-hand side to `-M (B_μ - B_ν) T_ν H̃_μ`, which the cover-ratio identity turns into
`-M T_μ H̃_μ`; the right-hand side is that by the eigenoperator property. -/
private theorem commutator_key (h : IsModifiedMacdonaldFamily q u H)
    (hn : IsEigenoperator q u H nabla) (ν : YoungDiagram) {g : Lambda L}
    (hg : g ∈ Submodule.span L (H '' {μ : YoungDiagram | Covers μ ν})) :
    cellProd q u ν • (Dop q u 0 g + (paramProduct q u * cellSum q u ν - 1) • g)
      = -paramProduct q u • nabla g := by
  set Phi : Module.End L (Lambda L) :=
    cellProd q u ν • (Dop q u 0 + (paramProduct q u * cellSum q u ν - 1) • LinearMap.id) +
      paramProduct q u • nabla with hPhi
  have hker : Submodule.span L (H '' {μ : YoungDiagram | Covers μ ν}) ≤ LinearMap.ker Phi := by
    rw [Submodule.span_le]
    rintro x ⟨μ, hμ, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, hPhi, LinearMap.add_apply,
      LinearMap.smul_apply, LinearMap.id_apply, h.dop_zero μ, hn μ]
    rw [cellProd_of_covers q u hμ]
    match_scalars
    ring
  have hzero : Phi g = 0 := LinearMap.mem_ker.1 (hker hg)
  simp only [hPhi, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply] at hzero
  rw [neg_smul, eq_neg_iff_add_eq_zero]
  exact hzero

/-- **The commutator of `D_0` with `e₁`, against the eigenoperator.** For every `f ∈ Λ`,
`D_0(e₁ ∇f) - e₁ D_0(∇f) = -M ∇(e₁ f)`.

This is Proposition 1.5, equation (1.30) b), of Garsia--Haiman--Tesler with both sides composed with
`∇` on the right so that no inverse appears. -/
@[hjo "lem_ght_nabla_commutator"]
theorem nabla_commutator (h : IsModifiedMacdonaldFamily q u H)
    (hn : IsEigenoperator q u H nabla) (f : Lambda L) :
    Dop q u 0 (elemSymm L 1 * nabla f) - elemSymm L 1 * Dop q u 0 (nabla f)
      = -paramProduct q u • nabla (elemSymm L 1 * f) := by
  have main : Dop q u 0 ∘ₗ mulE1 L ∘ₗ nabla - mulE1 L ∘ₗ Dop q u 0 ∘ₗ nabla
      = (-paramProduct q u) • (nabla ∘ₗ mulE1 L) := by
    refine h.basis.ext fun ν => ?_
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, h.basis_apply,
      mulE1_apply]
    rw [hn ν, mul_smul_comm, map_smul, map_smul, mul_smul_comm, h.dop_zero ν, mul_smul_comm,
      ← commutator_key h hn ν (h.elemSymm_one_mul_mem ν)]
    module
  simpa using DFunLike.congr_fun main f

/-- The starred commutator computation, carried out on the span in which clause (iv) of the family
places `e₁ H̃_ν`. On a generator `H̃_μ` with `μ` covering `ν` clause (iii) collapses the bracket to
`-M̃ (B*_μ - B*_ν) H̃_μ`, and applying `∇` multiplies it by `T_μ`; the starred cover-ratio identity
turns `T_μ(B*_μ - B*_ν)` into `T_ν`. -/
private theorem commutator_star_key (hq : q ≠ 0) (hu : u ≠ 0)
    (h : IsModifiedMacdonaldFamily q u H) (hn : IsEigenoperator q u H nabla) (ν : YoungDiagram)
    {g : Lambda L} (hg : g ∈ Submodule.span L (H '' {μ : YoungDiagram | Covers μ ν})) :
    nabla (DopStar q u 0 g + (paramProduct q⁻¹ u⁻¹ * cellSumInv q u ν - 1) • g)
      = -paramProduct q⁻¹ u⁻¹ • (cellProd q u ν • g) := by
  set Phi : Module.End L (Lambda L) :=
    nabla ∘ₗ (DopStar q u 0 + (paramProduct q⁻¹ u⁻¹ * cellSumInv q u ν - 1) • LinearMap.id) +
      (paramProduct q⁻¹ u⁻¹ * cellProd q u ν) • LinearMap.id with hPhi
  have hker : Submodule.span L (H '' {μ : YoungDiagram | Covers μ ν}) ≤ LinearMap.ker Phi := by
    rw [Submodule.span_le]
    rintro x ⟨μ, hμ, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, hPhi, LinearMap.add_apply,
      LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply, h.dopStar_zero μ]
    rw [← add_smul, map_smul, hn μ, ← cellProd_mul_sub_cellSumInv hμ (cellProd_ne_zero hq hu μ)]
    match_scalars
    ring
  have hzero : Phi g = 0 := LinearMap.mem_ker.1 (hker hg)
  simp only [hPhi, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.id_apply] at hzero
  rw [neg_smul, smul_smul, eq_neg_iff_add_eq_zero]
  exact hzero

/-- **The starred commutator against the eigenoperator.** For every `f ∈ Λ`,
`∇(D*_0(e₁ f) - e₁ D*_0 f) = -M̃ e₁ ∇f`.

This is Proposition 1.5, equation (1.30) b*), of Garsia--Haiman--Tesler composed with `∇` on the
left so that no inverse appears. -/
@[hjo "lem_ght_nabla_commutator_star"]
theorem nabla_commutator_star (hq : q ≠ 0) (hu : u ≠ 0)
    (h : IsModifiedMacdonaldFamily q u H) (hn : IsEigenoperator q u H nabla) (f : Lambda L) :
    nabla (DopStar q u 0 (elemSymm L 1 * f) - elemSymm L 1 * DopStar q u 0 f)
      = -paramProduct q⁻¹ u⁻¹ • (elemSymm L 1 * nabla f) := by
  have main : nabla ∘ₗ (DopStar q u 0 ∘ₗ mulE1 L - mulE1 L ∘ₗ DopStar q u 0)
      = (-paramProduct q⁻¹ u⁻¹) • (mulE1 L ∘ₗ nabla) := by
    refine h.basis.ext fun ν => ?_
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, h.basis_apply,
      mulE1_apply]
    rw [h.dopStar_zero ν, hn ν, mul_smul_comm, mul_smul_comm, neg_smul, sub_neg_eq_add,
      commutator_star_key hq hu h hn ν (h.elemSymm_one_mul_mem ν)]
  simpa using DFunLike.congr_fun main f

/-- **The eigenoperator carries multiplication by `e₁` to `-D_1`.** For every `f ∈ Λ`,
`∇(e₁ f) = -D_1(∇ f)`.

Combine `dop_elemSymm_one_mul` at `k = 0` applied to `∇f`, which says the commutator of `D_0` with
`e₁` on `∇f` is `M D_1(∇f)`, with `nabla_commutator`, which says that same commutator is
`-M ∇(e₁ f)`; then cancel `M`.

This is clause (iii) of Bergeron--Garsia--Leven--Xin's Proposition 1.1,
`∇ e₁ ∇⁻¹ = -D_1`, in the form `IsMacdonaldConjugator` asks for. Carlsson--Mellit's convention is
the negative of this; the two are not interchanged here. -/
@[hjo "lem_ght_nabla_e1"]
theorem nabla_elemSymm_one_mul (hM : paramProduct q u ≠ 0)
    (h : IsModifiedMacdonaldFamily q u H) (hn : IsEigenoperator q u H nabla) (f : Lambda L) :
    nabla (elemSymm L 1 * f) = -Dop q u 1 (nabla f) := by
  have hcomm := nabla_commutator h hn f
  rw [dop_elemSymm_one_mul q u 0 (nabla f), zero_add, add_sub_cancel_left] at hcomm
  -- `hcomm : M • D_1 (∇ f) = -M • ∇ (e₁ f)`
  have hcancel := congrArg (fun z : Lambda L => (paramProduct q u)⁻¹ • z) hcomm
  simp only [smul_smul, neg_smul, inv_mul_cancel₀ hM, one_smul, smul_neg] at hcancel
  rw [hcancel, neg_neg]

/-- **The eigenoperator carries `D*_1` to multiplication by `e₁`.** For every `f ∈ Λ`,
`∇(D*_1 f) = e₁ · ∇ f`.

Combine `dopStar_elemSymm_one_mul` at `k = 0`, which says the starred commutator of `D*_0` with
`e₁` on `f` is `-M̃ D*_1 f`, with `nabla_commutator_star`, which says `∇` of that commutator is
`-M̃ e₁ ∇f`; then cancel `M̃`.

This is clause (iii)* of Bergeron--Garsia--Leven--Xin's Proposition 1.1, `∇ D*_1 ∇⁻¹ = e₁`, in the
form `IsMacdonaldConjugator` asks for. -/
@[hjo "lem_ght_nabla_dopstar_one"]
theorem nabla_dopStar_one (hq : q ≠ 0) (hu : u ≠ 0) (hM : paramProduct q u ≠ 0)
    (h : IsModifiedMacdonaldFamily q u H) (hn : IsEigenoperator q u H nabla) (f : Lambda L) :
    nabla (DopStar q u 1 f) = elemSymm L 1 * nabla f := by
  have hMt : (-paramProduct q⁻¹ u⁻¹) ≠ 0 := neg_ne_zero.2 (paramProduct_inv_ne_zero hM)
  have hcomm := nabla_commutator_star hq hu h hn f
  rw [dopStar_elemSymm_one_mul q u 0 f, zero_add, sub_sub_cancel_left, ← neg_smul,
    map_smul] at hcomm
  -- `hcomm : (-M̃) • ∇ (D*_1 f) = (-M̃) • (e₁ * ∇ f)`
  have hcancel := congrArg (fun z : Lambda L => (-paramProduct q⁻¹ u⁻¹)⁻¹ • z) hcomm
  simpa only [smul_smul, inv_mul_cancel₀ hMt, one_smul] using hcancel

/-- **Garsia--Haiman--Tesler, the Macdonald conjugator.** Given a modified Macdonald family, its
eigenoperator `∇` -- the unique linear map with `∇ H̃_μ = T_μ H̃_μ` -- is a Macdonald conjugator:
bijective by `bijective_of_isEigenoperator`, commuting with `D_0` by `nabla_dop_zero`, carrying
`e₁` to `-D_1` by `nabla_elemSymm_one_mul` and `D*_1` to `e₁` by `nabla_dopStar_one`.

The existence of the family is a hypothesis, not a claim: it is
`HJO.Standing.exists_isModifiedMacdonaldFamily_param'`, which rests on Macdonald polynomial theory
and is proved elsewhere. So the only input of this statement is that one existence statement. -/
@[hjo "lem_conjugator_exists"]
theorem exists_isMacdonaldConjugator (hq : q ≠ 0) (hu : u ≠ 0) (hM : paramProduct q u ≠ 0)
    (hfam : ∃ H : YoungDiagram → Lambda L, IsModifiedMacdonaldFamily q u H) :
    ∃ nabla : Module.End L (Lambda L), IsMacdonaldConjugator q u nabla := by
  obtain ⟨H, h⟩ := hfam
  have hn := isEigenoperator_nablaOf h
  exact ⟨nablaOf h,
    { bijective := bijective_of_isEigenoperator hq hu h hn
      map_dop_zero := nabla_dop_zero h hn
      map_elemSymm_one_mul := nabla_elemSymm_one_mul hM h hn
      map_dopStar_one := nabla_dopStar_one hq hu hM h hn }⟩

end Conjugator

end HJO.Sym
