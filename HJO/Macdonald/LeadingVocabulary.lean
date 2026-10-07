/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Data.Finsupp.NeLocus
public import HJO.Macdonald.CutAlphabet
public import HJO.Macdonald.DopCommute
public meta import HJO.Attr

/-! # The leading-exponent vocabulary, arms and legs, and the normalisation of `H̃_μ`

Two groups of facts from the section on Macdonald's polynomials.

The first is the vocabulary of symmetric polynomials in a finite alphabet: the subalgebra `𝒮_n` of
symmetric polynomials, the lexicographic order `<_lex` on exponent vectors, the leading exponent
`ld(f)` of a nonzero polynomial, the leading coefficient of a product, and the map `cut_n` erasing
the last variable. Each of these is Mathlib's, and what is recorded here is that Mathlib's object
is the intended one: a characterisation of each in its own words.

The second is the arm-and-leg calculus of a partition and what it buys. Summing over the cells of
`μ`, the arms total the column offsets, the legs total the row offset sum `n(μ)` (the leg of a cell
is the arm of the transposed cell in the transposed diagram), and so the cell product is
`T_μ = q^{∑ a_μ} u^{∑ l_μ}`. That identity is what turns the eigenvalue of the inversion `↓` on
`H̃_μ` into `T_μ^{-1}`: cell by cell, `1 - q^{-a} u^{l+1} = -q^{-a} u^{l+1}(1 - q^a u^{-l-1})`, so
the two parameter inversions change Macdonald's normalising product `γ_μ` by the factor
`(-1)^{|μ|} q^{-∑ a_μ} u^{n(μ) + |μ|}`.

## Main results

* `Finsupp.lex_lt_iff_isLeast`: `α <_lex β` if and only if `α ≠ β` and `α_i < β_i` at the least
  index where they differ.
* `MonomialOrder.lex_degree_isGreatest`: the lexicographic leading exponent of a nonzero
  polynomial occurs in it and dominates every exponent occurring in it.
* `MvPolynomial.eq_killCompl_castSucc_iff`: `cut_n` is the algebra homomorphism fixing
  `x_1, …, x_n` and killing `x_{n+1}`.
* `HJO.Sym.sum_cells_fst`, `HJO.Sym.sum_cellArm`, `HJO.Sym.sum_cellLeg`: the total row offset is
  `n(μ)`, the total arm is the total column offset, the total leg is `n(μ)`.
* `HJO.Sym.cellProd_eq_pow_sum_cellArm_mul_pow_sum_cellLeg`: `T_μ = q^{∑ a_μ} u^{∑ l_μ}`.
* `HJO.Sym.inversion_macHtilde`, `HJO.Standing.inversion_macHtilde_param`:
  `↓H̃_μ = T_μ^{-1} H̃_μ`, for any commuting pair of parameter inversions and at the standing
  field.

## Implementation notes

The `𝒮_n`, `ld`, the leading coefficient of a product and `cut_n` are Mathlib's
`MvPolynomial.symmetricSubalgebra`, `MonomialOrder.degree` at `MonomialOrder.lex`,
`MonomialOrder.coeff_mul_of_degree_add` and `MvPolynomial.killCompl` at `Fin.castSucc`; the
order `<_lex` is `Finsupp.Lex (· < ·) (· < ·)`. The lemma on the leading coefficient of a
product holds for every monomial order and with no hypothesis that the factors are nonzero, both
sides vanishing otherwise. Cells are `0`-indexed, so the `i - 1` and `j - 1` are the
coordinates `c.1` and `c.2` of a cell.

The normalisation is proved first for an arbitrary field with generic parameters and an arbitrary
pair `ι, υ` of commuting inversions, `ι` an involution inverting both parameters and `υ` inverting
the second and fixing the first; the standing field supplies such a pair.

## References

I. G. Macdonald, *Symmetric functions and Hall
polynomials*, Chapter VI, and A. M. Garsia, M. Haiman and G. Tesler, *Explicit plethystic formulas
for Macdonald (q,t)-Kostka coefficients*, Sém. Lothar. Combin. **42** (1999), B42m.
-/

@[expose] public section

open Finset

/-! ### Symmetric polynomials, the lexicographic order and the leading exponent -/

/- The `𝒮_n` is Mathlib's subalgebra of symmetric polynomials, whose members are the
`p` with `rename w p = p` for every permutation `w` of the variables. -/
attribute [hjo "def_mac_symm"] MvPolynomial.symmetricSubalgebra

/- The `ld(f)` is Mathlib's leading exponent for the lexicographic monomial order. -/
attribute [hjo "def_mac_lead"] MonomialOrder.degree

/- The leading coefficient of a product is the product of the leading coefficients, for any
monomial order; `MonomialOrder.leadingCoeff f` is the coefficient of `x^{ld(f)}` in `f`. -/
attribute [hjo "lem_mac_lead_coeff"] MonomialOrder.coeff_mul_of_degree_add

/- The `cut_n` is `MvPolynomial.killCompl (Fin.castSucc_injective n)`. -/
attribute [hjo "def_mac_cut"] MvPolynomial.killCompl

/-- **The lexicographic order on exponents**, in the words: `α <_lex β` holds exactly
when `α ≠ β` and `α_i < β_i` at the least index `i` at which `α` and `β` differ. Here `<_lex` is
`Finsupp.Lex (· < ·) (· < ·)`, the relation the lexicographic monomial order and
`Finsupp.isStrictTotalOrder_lex` are stated for, on any linearly ordered alphabet and any linearly
ordered coefficients. -/
@[hjo "def_mac_lex"]
theorem Finsupp.lex_lt_iff_isLeast {σ N : Type*} [LinearOrder σ] [Zero N] [LinearOrder N]
    {α β : σ →₀ N} :
    Finsupp.Lex (· < ·) (· < ·) α β ↔
      α ≠ β ∧ ∀ i, IsLeast {j | α j ≠ β j} i → α i < β i := by
  classical
  rw [Finsupp.lex_def]
  constructor
  · rintro ⟨j, hj, hlt⟩
    refine ⟨fun h => (ne_of_lt hlt) (by rw [h]), fun i hi => ?_⟩
    have hij : i ≤ j := hi.2 (ne_of_lt hlt)
    have hji : j ≤ i := not_lt.mp fun h => hi.1 (hj i h)
    rwa [le_antisymm hij hji]
  · rintro ⟨hne, h⟩
    have hnon : (α.neLocus β).Nonempty := Finsupp.nonempty_neLocus_iff.mpr hne
    set i := (α.neLocus β).min' hnon
    have hleast : IsLeast {j | α j ≠ β j} i :=
      ⟨Finsupp.mem_neLocus.mp ((α.neLocus β).min'_mem hnon),
        fun j hj => (α.neLocus β).min'_le j (Finsupp.mem_neLocus.mpr hj)⟩
    exact ⟨i, fun d hd => not_ne_iff.mp fun hd' => not_lt_of_ge (hleast.2 hd') hd, h i hleast⟩

/-- **The leading exponent**, in the words: for a nonzero `f`, `ld(f)` is an exponent
whose monomial occurs in `f`, and every exponent `α` whose monomial occurs in `f` is `ld(f)` or
lexicographically smaller. Here `ld` is `MonomialOrder.degree` for the lexicographic monomial
order `MonomialOrder.lex`. -/
@[hjo "def_mac_lead"]
theorem MonomialOrder.lex_degree_isGreatest {σ R : Type*} [LinearOrder σ] [WellFoundedGT σ]
    [CommSemiring R] {f : MvPolynomial σ R} (hf : f ≠ 0) :
    MonomialOrder.lex.degree f ∈ f.support ∧
      ∀ α ∈ f.support, α = MonomialOrder.lex.degree f ∨
        Finsupp.Lex (· < ·) (· < ·) α (MonomialOrder.lex.degree f) := by
  refine ⟨MonomialOrder.degree_mem_support hf, fun α hα => ?_⟩
  rcases (MonomialOrder.le_degree (m := MonomialOrder.lex) hα).lt_or_eq with h | h
  · exact Or.inr (MonomialOrder.lex_lt_iff.mp h)
  · exact Or.inl (MonomialOrder.lex.toSyn.injective h)

/-- **Erasing the last variable**, in the words: an `R`-algebra homomorphism
`R[x_1, …, x_{n+1}] → R[x_1, …, x_n]` is
`cut_n = MvPolynomial.killCompl (Fin.castSucc_injective n)` exactly when it fixes `x_1, …, x_n` and
sends `x_{n+1}` to `0`. -/
@[hjo "def_mac_cut"]
theorem MvPolynomial.eq_killCompl_castSucc_iff {R : Type*} [CommSemiring R] {n : ℕ}
    (φ : MvPolynomial (Fin (n + 1)) R →ₐ[R] MvPolynomial (Fin n) R) :
    φ = MvPolynomial.killCompl (Fin.castSucc_injective n) ↔
      (∀ i : Fin n, φ (MvPolynomial.X i.castSucc) = MvPolynomial.X i) ∧
        φ (MvPolynomial.X (Fin.last n)) = 0 := by
  constructor
  · rintro rfl
    exact ⟨fun i => MvPolynomial.killCompl_X _ i,
      MvPolynomial.killCompl_X_eq_zero _ fun ⟨i, hi⟩ => (Fin.castSucc_lt_last i).ne hi⟩
  · rintro ⟨hX, hlast⟩
    refine MvPolynomial.algHom_ext fun i => ?_
    induction i using Fin.lastCases with
    | last =>
      rw [hlast, MvPolynomial.killCompl_X_eq_zero _ fun ⟨j, hj⟩ => (Fin.castSucc_lt_last j).ne hj]
    | cast i => rw [hX, MvPolynomial.killCompl_X]

namespace HJO.Sym

/-- **The total row offset is the row offset sum**: `∑_{(i,j) ∈ μ} (i - 1) = n(μ)`, read on the
`0`-indexed cells, where the `i - 1` of the formula is the row index `c.1`. -/
@[hjo "lem_mac_row_offset_sum"]
theorem sum_cells_fst (μ : YoungDiagram) : ∑ c ∈ cells μ, c.1 = rowOffsetSum μ := by
  classical
  have hmaps : ∀ c ∈ cells μ, c.1 ∈ range μ.card := by
    intro c hc
    rw [mem_range]
    by_contra h
    have h0 := HJO.Mac.rowLen_eq_zero_of_card_le (D := μ) (not_lt.mp h)
    have := YoungDiagram.mem_iff_lt_rowLen.mp ((YoungDiagram.mem_cells _).mp hc)
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, rowOffsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => i) (fun c hc => (Finset.mem_filter.mp hc).2),
    Finset.sum_const, smul_eq_mul, mul_comm, YoungDiagram.rowLen_eq_card]
  rfl

/-- **The total arm is the total column offset**: `∑_{c ∈ μ} a_μ(c) = ∑_{(i,j) ∈ μ} (j - 1)`, read
on the `0`-indexed cells, where the `j - 1` of the formula is the column index `c.2`. Reflecting
each row, `(i, j) ↦ (i, μ_i - 1 - j)`, is an involution of the cells carrying the column index to
the arm. -/
@[hjo "lem_mac_arm_sum"]
theorem sum_cellArm (μ : YoungDiagram) : ∑ c ∈ cells μ, cellArm μ c = ∑ c ∈ cells μ, c.2 := by
  have hmem : ∀ c ∈ cells μ, (c.1, cellArm μ c) ∈ cells μ := by
    intro c hc
    have h := YoungDiagram.mem_iff_lt_rowLen.mp ((YoungDiagram.mem_cells _).mp hc)
    refine (YoungDiagram.mem_cells _).mpr (YoungDiagram.mem_iff_lt_rowLen.mpr ?_)
    simp only [cellArm]
    omega
  have hinv : ∀ c ∈ cells μ, (c.1, cellArm μ (c.1, cellArm μ c)) = c := by
    intro c hc
    have h := YoungDiagram.mem_iff_lt_rowLen.mp ((YoungDiagram.mem_cells _).mp hc)
    simp only [cellArm]
    ext
    · rfl
    · simp only
      omega
  exact Finset.sum_nbij' (fun c => (c.1, cellArm μ c)) (fun c => (c.1, cellArm μ c)) hmem hmem
    hinv hinv (fun c _ => rfl)

/-- The leg of a cell is the arm of the transposed cell in the transposed diagram. -/
theorem cellLeg_eq_cellArm_transpose (μ : YoungDiagram) (c : ℕ × ℕ) :
    cellLeg μ c = cellArm μ.transpose c.swap := by
  simp [cellLeg, cellArm, YoungDiagram.rowLen_transpose]

/-- Summing over the cells of the transposed diagram is summing over the transposed cells. -/
theorem sum_cells_transpose {M : Type*} [AddCommMonoid M] (μ : YoungDiagram) (f : ℕ × ℕ → M) :
    ∑ c ∈ cells μ.transpose, f c = ∑ c ∈ cells μ, f c.swap := by
  refine (Finset.sum_nbij' Prod.swap Prod.swap (fun c hc => ?_) (fun c hc => ?_)
    (fun c _ => Prod.swap_swap c) (fun c _ => Prod.swap_swap c) (fun c _ => rfl)).symm
  · exact (YoungDiagram.mem_cells _).mpr
      (YoungDiagram.mem_transpose.mpr (by simpa using (YoungDiagram.mem_cells _).mp hc))
  · exact (YoungDiagram.mem_cells _).mpr
      (YoungDiagram.mem_transpose.mp ((YoungDiagram.mem_cells _).mp hc))

/-- **The total leg is the row offset sum**: `∑_{c ∈ μ} l_μ(c) = n(μ)`. The leg of a cell is the
arm of the transposed cell in the transposed diagram, so the total leg of `μ` is the total arm of
`μ'`, which is the total column offset of `μ'`, which is the total row offset of `μ`. -/
@[hjo "lem_mac_leg_sum"]
theorem sum_cellLeg (μ : YoungDiagram) : ∑ c ∈ cells μ, cellLeg μ c = rowOffsetSum μ := by
  rw [← sum_cells_fst]
  simp only [cellLeg_eq_cellArm_transpose]
  rw [← sum_cells_transpose μ (cellArm μ.transpose), sum_cellArm, sum_cells_transpose]
  rfl

/-- **The cell product in terms of arms and legs**:
`T_μ = q^{∑_{c ∈ μ} a_μ(c)} u^{∑_{c ∈ μ} l_μ(c)}`, in any commutative monoid. -/
@[hjo "lem_mac_tmu_hook"]
theorem cellProd_eq_pow_sum_cellArm_mul_pow_sum_cellLeg {M : Type*} [CommMonoid M] (q u : M)
    (μ : YoungDiagram) :
    cellProd q u μ = q ^ (∑ c ∈ cells μ, cellArm μ c) * u ^ (∑ c ∈ cells μ, cellLeg μ c) := by
  rw [sum_cellArm, sum_cellLeg, ← sum_cells_fst, cellProd, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum]

/-! ### The normalisation of the modified Macdonald polynomials -/

section Normalisation

open HJO.Mac

variable {K : Type*} [Field K] [Algebra ℚ K] {q : Kˣ} {u : K}

omit [Algebra ℚ K] in
/-- **The two parameter inversions on Macdonald's normalising product.** If `ι` inverts both
parameters and `υ` inverts the second only, then `ιυ(γ_μ)` is `υ(γ_μ)` times
`(-1)^{|μ|} q^{-∑ a_μ} u^{∑ l_μ + |μ|}`: cell by cell,
`1 - q^{-a} u^{l+1} = -q^{-a} u^{l+1} (1 - q^a u^{-l-1})`. -/
theorem map_map_normalisingProduct {ι υ : K →+* K} (hq0 : (q : K) ≠ 0) (hu0 : u ≠ 0)
    (hιq : ι q = (q : K)⁻¹) (hιu : ι u = u⁻¹) (hυq : υ q = q) (hυu : υ u = u⁻¹)
    (μ : YoungDiagram) :
    ι (υ (normalisingProduct (q : K) u μ))
      = (-1) ^ μ.card * ((q : K)⁻¹ ^ (∑ c ∈ cells μ, cellArm μ c)
          * u ^ (∑ c ∈ cells μ, cellLeg μ c) * u ^ μ.card)
        * υ (normalisingProduct (q : K) u μ) := by
  have hιu' : ι u⁻¹ = u := by rw [map_inv₀, hιu, inv_inv]
  have hcell : ∀ c ∈ cells μ,
      ι (υ (1 - (q : K) ^ cellArm μ c * u ^ (cellLeg μ c + 1)))
        = (-1) * ((q : K)⁻¹ ^ cellArm μ c * u ^ cellLeg μ c * u)
          * υ (1 - (q : K) ^ cellArm μ c * u ^ (cellLeg μ c + 1)) := by
    intro c _
    simp only [map_sub, map_one, map_mul, map_pow, hυq, hυu, hιq, hιu']
    have hQ : (q : K) ^ cellArm μ c * (q : K)⁻¹ ^ cellArm μ c = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hq0, one_pow]
    have hU : u ^ cellLeg μ c * u⁻¹ ^ cellLeg μ c = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hu0, one_pow]
    linear_combination (-(u * u⁻¹ * (u ^ cellLeg μ c * u⁻¹ ^ cellLeg μ c))) * hQ
      - (u ^ cellLeg μ c * u⁻¹ ^ cellLeg μ c) * mul_inv_cancel₀ hu0 - hU
  have hcard : ((-1 : K) ^ μ.card) = ∏ _c ∈ cells μ, (-1 : K) := by
    rw [Finset.prod_const]
  have hucard : u ^ μ.card = ∏ _c ∈ cells μ, u := by
    rw [Finset.prod_const]
  rw [normalisingProduct, map_prod, map_prod, Finset.prod_congr rfl hcell,
    Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, hcard, hucard]

/-- **The modified Macdonald polynomials are normalised**, for any pair of parameter inversions:
if `ι` is an involution inverting both parameters, `υ` inverts the second parameter and fixes the
first, and the two commute, then `↓H̃_μ = T_μ^{-1} H̃_μ`. -/
theorem inversion_macHtilde {ι υ : K →+* K} (hqu : AlgebraicIndependent ℤ ![(q : K), u])
    (hιι : ∀ c : K, ι (ι c) = c) (hιq : ι q = (q : K)⁻¹) (hιu : ι u = u⁻¹) (hυq : υ q = q)
    (hυu : υ u = u⁻¹) (hcomm : ∀ c : K, ι (υ c) = υ (ι c)) (μ : YoungDiagram) :
    inversion ι (macHtilde υ hqu μ) = (cellProd (q : K) u μ)⁻¹ • macHtilde υ hqu μ := by
  have hu0 : u ≠ 0 := HJO.Standing.u_ne_zero hqu
  have hιu' : ι u⁻¹ = u := by rw [map_inv₀, hιu, inv_inv]
  have hPι : coeffSubst ι (macPfun hqu μ) = macPfun hqu μ :=
    coeffSubst_macPfun hqu hιι (by rw [hιq, Units.val_inv_eq_inv_val])
      (by rw [hιu, inv_mul_cancel₀ hu0]) μ
  have hG := inversion_plethDivide_coeffSubst hu0 hιu' hcomm (macPfun_mem hqu μ) hPι
  rw [macHtilde_eq_smul, inversion_smul, hG, smul_smul, smul_smul]
  congr 1
  rw [map_mul, map_map_normalisingProduct q.ne_zero hu0 hιq hιu hυq hυu,
    cellProd_eq_pow_sum_cellArm_mul_pow_sum_cellLeg, sum_cellLeg, map_pow, hιu]
  have hV := normalisingProduct_ne_zero hqu μ
  generalize υ (normalisingProduct (q : K) u μ) = V
  generalize ∑ c ∈ cells μ, cellArm μ c = A
  generalize rowOffsetSum μ = n
  generalize μ.card = d
  have hsq : ((-1 : K) ^ d) * (-1) ^ d = 1 := by rw [← mul_pow]; simp
  have hD : u ^ d * u⁻¹ ^ d = 1 := by rw [← mul_pow, mul_inv_cancel₀ hu0, one_pow]
  rw [neg_pow, mul_inv, ← inv_pow, ← inv_pow]
  linear_combination ((q : K)⁻¹ ^ A * V * (u⁻¹ ^ n * u ^ n) * (u ^ d * u⁻¹ ^ d)) * hsq
    + ((q : K)⁻¹ ^ A * V * (u⁻¹ ^ n * u ^ n)) * hD

end Normalisation

end HJO.Sym

namespace HJO.Standing

open HJO.Ascent HJO.Sym

variable (K : Type*) [Field K] [Algebra ParamRing K] [IsFractionRing ParamRing K] [Algebra ℚ K]

/-- **The modified Macdonald polynomials are normalised**: at the standing field `𝕜 = ℚ(q, u)`,
with `↓` the inversion built on `ι : q ↦ q^{-1}, u ↦ u^{-1}` and `H̃_μ` built with
`υ : u ↦ u^{-1}`, every `H̃_μ` satisfies `↓H̃_μ = T_μ^{-1} H̃_μ`. -/
@[hjo "lem_mac_htilde_inversion"]
theorem inversion_macHtilde_param (μ : YoungDiagram) :
    inversion (paramQUInvHom K)
        (macHtilde (paramUInvHom K) (algebraicIndependent_paramQUnit K) μ)
      = (cellProd (paramQ K) (paramU K) μ)⁻¹ •
          macHtilde (paramUInvHom K) (algebraicIndependent_paramQUnit K) μ :=
  inversion_macHtilde (algebraicIndependent_paramQUnit K) (paramQUInvHom_involutive K)
    (paramQUInvHom_paramQ K) (paramQUInvHom_paramU K) (paramUInvHom_paramQ K)
    (paramUInvHom_paramU K) (paramQUInvHom_paramUInvHom_comm K) μ

end HJO.Standing
