/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Combinatorics.Enumerative.Composition
public import HJO.CreationSeeds.LogDeriv
public import HJO.CreationSeeds.Bernstein
public meta import HJO.Attr

/-! # The elementary function as a sum of creation seeds

The `N`-th elementary symmetric function is the sum of the creation seeds `C_α 1` over the
compositions `α` of `N`. This is the expansion the compositional rational shuffle identity is
applied through, and it is proved here rather than quoted.

The route is as follows. The creation displacement `δ'` of `Sym.plethCreate`
differs from the Bernstein displacement `δ₀` of `Sym.plethBernstein` by the single letter
`1/(qz)`, so the letter-by-letter recursions of `HJO.CreationSeeds.LogDeriv` compute
`e_n[X - (1 - q⁻¹)/z]` in closed form, and pairing that against the complete homogeneous series
computes `C_r(e_n)`. Summing over `r` telescopes: the scalars collapse by a finite geometric sum
and what is left is the Cauchy relation, so `∑_{r=1}^{N} C_r(e_{N-r}) = e_N`. A strong induction
on `N` then finishes, the inductive step being the bijection between the compositions of `N` and
the pairs `(r, β)` with `1 ≤ r ≤ N` and `β` a composition of `N - r`.

Everything is written in the variable `w = z⁻¹` of `Sym.plethCreate`: only non-negative powers of
`w` occur in a displaced symmetric function, so the target is the polynomial ring `Λ[w]` and the
coefficient of `zʳ` in the product with `∑ₘ h_m zᵐ` is the finite pairing `Sym.coeffPairing`
against `h_{r+j}`.

Compositions are `Mathlib`'s `Composition N`; the split of the inductive step is run on the
`Finset (List ℕ)` of their block lists, which is what makes the head-of-list bijection a plain
`Finset.biUnion`.
-/

@[expose] public section

open Finset

namespace HJO.CreationSeeds

/-! ### Two reindexings of a `Finset.Icc` -/

section Reindex

variable {M : Type*} [AddCommMonoid M]

/-- Reindexing `Icc 1 n` as `range n`. -/
theorem sum_Icc_one_eq_sum_range (f : ℕ → M) (n : ℕ) :
    ∑ r ∈ Icc 1 n, f r = ∑ i ∈ range n, f (i + 1) := by
  refine Finset.sum_nbij' (fun r => r - 1) (fun i => i + 1) ?_ ?_ ?_ ?_ ?_
  · intro r hr; simp only [Finset.mem_Icc] at hr; simp only [Finset.mem_range]; omega
  · intro i hi; simp only [Finset.mem_range] at hi; simp only [Finset.mem_Icc]; omega
  · intro r hr; simp only [Finset.mem_Icc] at hr; omega
  · intro i _; omega
  · intro r hr; simp only [Finset.mem_Icc] at hr; rw [show r - 1 + 1 = r by omega]

/-- Substituting the total degree `m = r + j` for the shift `j`. -/
theorem sum_Icc_shift (g : ℕ → M) (r N : ℕ) :
    ∑ j ∈ Icc 1 (N - r), g (r + j) = ∑ m ∈ Icc (r + 1) N, g m := by
  refine Finset.sum_nbij' (fun j => r + j) (fun m => m - r) ?_ ?_ ?_ ?_ (fun _ _ => rfl)
  · intro j hj; simp only [Finset.mem_Icc] at hj ⊢; omega
  · intro m hm; simp only [Finset.mem_Icc] at hm ⊢; omega
  · intro j hj; simp only [Finset.mem_Icc] at hj; omega
  · intro m hm; simp only [Finset.mem_Icc] at hm; omega

end Reindex

/-! ### The creation displacement is the Bernstein displacement plus one letter -/

section Displacement

variable {L : Type*} [Field L] [Algebra ℚ L]

omit [Algebra ℚ L] in
/-- The creation displacement on the generator `i` of `Lambda L`, which stands for `p_{i+1}`. -/
theorem plethCreate_X (q : L) (i : ℕ) :
    Sym.plethCreate q (MvPolynomial.X i)
      = Polynomial.C (Sym.powerSum L (i + 1))
        - Polynomial.C (MvPolynomial.C (1 - (q ^ (i + 1))⁻¹)) * Polynomial.X ^ (i + 1) := by
  rw [Sym.plethCreate, MvPolynomial.aeval_X]

omit [Algebra ℚ L] in
/-- The creation displacement on a generator, expanded around the Bernstein displacement. -/
theorem plethCreate_X_eq_plethBernstein_add (q : L) (i : ℕ) :
    Sym.plethCreate q (MvPolynomial.X i)
      = Sym.plethBernstein L (MvPolynomial.X i)
        + (Polynomial.C (MvPolynomial.C q⁻¹) * Polynomial.X) ^ (i + 1) := by
  rw [plethCreate_X, Sym.plethBernstein_X]
  have hp : ((Polynomial.C (MvPolynomial.C q⁻¹) : Polynomial (Sym.Lambda L))
        * Polynomial.X) ^ (i + 1)
      = Polynomial.C (MvPolynomial.C ((q ^ (i + 1))⁻¹)) * Polynomial.X ^ (i + 1) := by
    rw [mul_pow, ← map_pow, ← map_pow, inv_pow]
  have hc : (Polynomial.C (MvPolynomial.C (1 - (q ^ (i + 1))⁻¹)) : Polynomial (Sym.Lambda L))
      = 1 - Polynomial.C (MvPolynomial.C ((q ^ (i + 1))⁻¹)) := by
    rw [map_sub, map_sub, map_one, map_one]
  rw [hp, hc]
  ring

omit [Algebra ℚ L] in
/-- **The creation displacement adds the single letter `1/(qz)` to the Bernstein
displacement**: `δ'(p_k) = δ₀(p_k) + (q⁻¹z⁻¹)ᵏ` for every `k ≥ 1`. -/
@[hjo "lem_pleth_create_letter"]
theorem plethCreate_powerSum (q : L) {k : ℕ} (hk : 0 < k) :
    Sym.plethCreate q (Sym.powerSum L k)
      = Sym.plethBernstein L (Sym.powerSum L k)
        + (Polynomial.C (MvPolynomial.C q⁻¹) * Polynomial.X) ^ k := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [CopPower.powerSum_succ, plethCreate_X_eq_plethBernstein_add]

/-- **The Bernstein displacement of an elementary symmetric function**: removing the single
letter `z⁻¹` from the alphabet gives `∑_{j=0}ⁿ (-1)ʲ e_{n-j} z⁻ʲ`. -/
theorem plethBernstein_elemSymm (n : ℕ) :
    Sym.plethBernstein L (Sym.elemSymm L n)
      = ∑ j ∈ range (n + 1), (-1 : Polynomial (Sym.Lambda L)) ^ j
          * Polynomial.C (Sym.elemSymm L (n - j)) * Polynomial.X ^ j := by
  rw [elemSymm_sub_letter (Polynomial.C : Sym.Lambda L →+* Polynomial (Sym.Lambda L))
    (Sym.plethBernstein L) Polynomial.X (fun _ hk => Sym.plethBernstein_powerSum hk) n]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [neg_pow]
  ring

/-- **The creation displacement of an elementary symmetric function**:
`e_n[X - (1 - q⁻¹)/z] = e_n + (1 - q⁻¹) ∑_{j=1}ⁿ (-1)ʲ e_{n-j} z⁻ʲ`. -/
@[hjo "lem_pleth_create_esymm"]
theorem plethCreate_elemSymm (q : L) (n : ℕ) :
    Sym.plethCreate q (Sym.elemSymm L n)
      = Polynomial.C (Sym.elemSymm L n)
        + Polynomial.C (MvPolynomial.C (1 - q⁻¹))
          * ∑ j ∈ Icc 1 n, (-1 : Polynomial (Sym.Lambda L)) ^ j
              * Polynomial.C (Sym.elemSymm L (n - j)) * Polynomial.X ^ j := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [elemSymm_zero, map_one]
    simp
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [elemSymm_add_letter (Sym.plethBernstein L) (Sym.plethCreate q)
      (Polynomial.C (MvPolynomial.C q⁻¹) * Polynomial.X)
      (fun _ hk => plethCreate_powerSum q hk) (n := m + 1) (by omega),
    Nat.add_sub_cancel, plethBernstein_elemSymm, plethBernstein_elemSymm]
  have hL1 : (∑ j ∈ range (m + 1 + 1), (-1 : Polynomial (Sym.Lambda L)) ^ j
        * Polynomial.C (Sym.elemSymm L (m + 1 - j)) * Polynomial.X ^ j)
      = (∑ j ∈ range (m + 1), (-1 : Polynomial (Sym.Lambda L)) ^ (j + 1)
          * Polynomial.C (Sym.elemSymm L (m - j)) * Polynomial.X ^ (j + 1))
        + Polynomial.C (Sym.elemSymm L (m + 1)) := by
    rw [Finset.sum_range_succ']
    simp only [pow_zero, one_mul, mul_one, Nat.sub_zero]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show m + 1 - (j + 1) = m - j by omega]
  have hR1 : (∑ j ∈ Icc 1 (m + 1), (-1 : Polynomial (Sym.Lambda L)) ^ j
        * Polynomial.C (Sym.elemSymm L (m + 1 - j)) * Polynomial.X ^ j)
      = ∑ j ∈ range (m + 1), (-1 : Polynomial (Sym.Lambda L)) ^ (j + 1)
          * Polynomial.C (Sym.elemSymm L (m - j)) * Polynomial.X ^ (j + 1) := by
    rw [sum_Icc_one_eq_sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show m + 1 - (j + 1) = m - j by omega]
  have hstep : ∀ j ∈ range (m + 1),
      (-1 : Polynomial (Sym.Lambda L)) ^ (j + 1) * Polynomial.C (Sym.elemSymm L (m - j))
          * Polynomial.X ^ (j + 1)
        + Polynomial.C (MvPolynomial.C q⁻¹) * Polynomial.X
          * ((-1 : Polynomial (Sym.Lambda L)) ^ j * Polynomial.C (Sym.elemSymm L (m - j))
            * Polynomial.X ^ j)
      = Polynomial.C (MvPolynomial.C (1 - q⁻¹))
        * ((-1 : Polynomial (Sym.Lambda L)) ^ (j + 1) * Polynomial.C (Sym.elemSymm L (m - j))
          * Polynomial.X ^ (j + 1)) := by
    intro j _
    rw [show (Polynomial.C (MvPolynomial.C (1 - q⁻¹)) : Polynomial (Sym.Lambda L))
      = 1 - Polynomial.C (MvPolynomial.C q⁻¹) by rw [map_sub, map_sub, map_one, map_one],
      pow_succ]
    ring
  rw [hL1, hR1, Finset.mul_sum, Finset.mul_sum, add_right_comm, ← Finset.sum_add_distrib,
    Finset.sum_congr rfl hstep]
  exact add_comm _ _

/-- The creation displacement of an elementary symmetric function, written as a sum of monomials
in `w = z⁻¹`, the shape `Sym.coeffPairing` consumes. -/
theorem plethCreate_elemSymm_monomial (q : L) (n : ℕ) :
    Sym.plethCreate q (Sym.elemSymm L n)
      = Polynomial.monomial 0 (Sym.elemSymm L n)
        + ∑ j ∈ Icc 1 n, Polynomial.monomial j
            (MvPolynomial.C (1 - q⁻¹) * ((-1) ^ j * Sym.elemSymm L (n - j))) := by
  rw [plethCreate_elemSymm, Finset.mul_sum, Polynomial.monomial_zero_left]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.C_mul, Polynomial.C_mul, map_pow,
    map_neg, map_one]
  ring

end Displacement

/-! ### The creation operators on the elementary symmetric functions -/

section Creation

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **The `r`-th creation operator on an elementary symmetric function**:
`C_r(e_n) = (-q)^{1-r}(e_n h_r + (1 - q⁻¹) ∑_{j=1}ⁿ (-1)ʲ e_{n-j} h_{r+j})`. -/
@[hjo "lem_cop_esymm"]
theorem cop_elemSymm (q : L) (r n : ℕ) :
    Sym.Cop q r (Sym.elemSymm L n)
      = MvPolynomial.C ((-q) ^ (1 - (r : ℤ)))
        * (Sym.elemSymm L n * Sym.completeHomog L r
          + MvPolynomial.C (1 - q⁻¹)
            * ∑ j ∈ Icc 1 n, (-1) ^ j * Sym.elemSymm L (n - j)
                * Sym.completeHomog L (r + j)) := by
  rw [Sym.Cop]
  simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply]
  rw [plethCreate_elemSymm_monomial, map_add, map_sum]
  simp only [CopPower.coeffPairing_monomial, Nat.add_zero]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · ring
  · exact Finset.sum_congr rfl fun j _ => by ring

omit [Algebra ℚ L] in
/-- **The scalar sum**: for every `m ≥ 1`,
`(-q)^{1-m} + (1 - q⁻¹) ∑_{r=1}^{m-1} (-1)^{m-r}(-q)^{1-r} = (-1)^{m-1}`. -/
@[hjo "lem_cop_scalar_sum"]
theorem sum_zpow_scalar (q : L) {m : ℕ} (hm : 0 < m) :
    (-q) ^ (1 - (m : ℤ))
        + (1 - q⁻¹) * ∑ r ∈ Icc 1 (m - 1), (-1) ^ (m - r) * (-q) ^ (1 - (r : ℤ))
      = (-1) ^ (m - 1) := by
  have key : ∀ r : ℕ, 0 < r → (-q) ^ (1 - (r : ℤ)) = (-q⁻¹) ^ (r - 1) := by
    intro r hr
    obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    push_cast
    rw [show (1 : ℤ) - ((s : ℤ) + 1) = -(s : ℤ) by ring, zpow_neg, zpow_natCast, ← inv_pow,
      inv_neg]
  have hsum : ∑ r ∈ Icc 1 (m - 1), (-1 : L) ^ (m - r) * (-q) ^ (1 - (r : ℤ))
      = (-1) ^ (m - 1) * ∑ i ∈ range (m - 1), q⁻¹ ^ i := by
    rw [sum_Icc_one_eq_sum_range, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_range] at hi
    rw [key (i + 1) i.succ_pos, Nat.add_sub_cancel, neg_pow q⁻¹ i, ← mul_assoc, ← pow_add,
      show m - (i + 1) + i = m - 1 by omega]
  rw [key m hm, hsum, neg_pow q⁻¹ (m - 1)]
  linear_combination ((-1 : L) ^ (m - 1)) * mul_neg_geom_sum q⁻¹ (m - 1)

omit [Algebra ℚ L] in
/-- The scalar sum, transported into `Lambda L` along `MvPolynomial.C`. -/
theorem sum_zpow_scalar_C (q : L) {m : ℕ} (hm : 0 < m) :
    MvPolynomial.C ((-q) ^ (1 - (m : ℤ)))
        + MvPolynomial.C (1 - q⁻¹)
          * ∑ r ∈ Icc 1 (m - 1), (-1 : Sym.Lambda L) ^ (m - r)
              * MvPolynomial.C ((-q) ^ (1 - (r : ℤ)))
      = (-1) ^ (m - 1) := by
  have h := congrArg (fun x : L => (MvPolynomial.C x : Sym.Lambda L)) (sum_zpow_scalar q hm)
  simp only [map_add, map_mul, map_sum, map_pow, map_neg, map_one] at h
  exact h

/-- The `r`-th creation operator on `e_{N-r}`, with the inner sum reindexed by the total degree
`m = r + j`. -/
theorem cop_elemSymm_reindexed (q : L) (r N : ℕ) :
    Sym.Cop q r (Sym.elemSymm L (N - r))
      = MvPolynomial.C ((-q) ^ (1 - (r : ℤ)))
          * (Sym.elemSymm L (N - r) * Sym.completeHomog L r)
        + ∑ m ∈ Icc (r + 1) N, MvPolynomial.C (1 - q⁻¹)
            * ((-1 : Sym.Lambda L) ^ (m - r) * MvPolynomial.C ((-q) ^ (1 - (r : ℤ))))
            * (Sym.elemSymm L (N - m) * Sym.completeHomog L m) := by
  rw [cop_elemSymm, mul_add, Finset.mul_sum, Finset.mul_sum,
    ← sum_Icc_shift (fun m => MvPolynomial.C (1 - q⁻¹)
      * ((-1 : Sym.Lambda L) ^ (m - r) * MvPolynomial.C ((-q) ^ (1 - (r : ℤ))))
      * (Sym.elemSymm L (N - m) * Sym.completeHomog L m)) r N]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show r + j - r = j by omega, show N - (r + j) = N - r - j by omega]
  ring

/-- **The creation operators recover the elementary symmetric functions**: for every `N ≥ 1`,
`∑_{r=1}^{N} C_r(e_{N-r}) = e_N`. -/
@[hjo "lem_cop_esymm_sum"]
theorem sum_cop_elemSymm (q : L) {N : ℕ} (hN : 0 < N) :
    ∑ r ∈ Icc 1 N, Sym.Cop q r (Sym.elemSymm L (N - r)) = Sym.elemSymm L N := by
  have h1 : ∑ r ∈ Icc 1 N, Sym.Cop q r (Sym.elemSymm L (N - r))
      = (∑ r ∈ Icc 1 N, MvPolynomial.C ((-q) ^ (1 - (r : ℤ)))
            * (Sym.elemSymm L (N - r) * Sym.completeHomog L r))
        + ∑ r ∈ Icc 1 N, ∑ m ∈ Icc (r + 1) N, MvPolynomial.C (1 - q⁻¹)
            * ((-1 : Sym.Lambda L) ^ (m - r) * MvPolynomial.C ((-q) ^ (1 - (r : ℤ))))
            * (Sym.elemSymm L (N - m) * Sym.completeHomog L m) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun r _ => cop_elemSymm_reindexed q r N
  have h2 : ∑ r ∈ Icc 1 N, ∑ m ∈ Icc (r + 1) N, MvPolynomial.C (1 - q⁻¹)
        * ((-1 : Sym.Lambda L) ^ (m - r) * MvPolynomial.C ((-q) ^ (1 - (r : ℤ))))
        * (Sym.elemSymm L (N - m) * Sym.completeHomog L m)
      = ∑ m ∈ Icc 1 N, ∑ r ∈ Icc 1 (m - 1), MvPolynomial.C (1 - q⁻¹)
          * ((-1 : Sym.Lambda L) ^ (m - r) * MvPolynomial.C ((-q) ^ (1 - (r : ℤ))))
          * (Sym.elemSymm L (N - m) * Sym.completeHomog L m) :=
    Finset.sum_comm' (by intro r m; simp only [Finset.mem_Icc]; omega)
  have h3 : ∀ m ∈ Icc 1 N,
      MvPolynomial.C ((-q) ^ (1 - (m : ℤ)))
          * (Sym.elemSymm L (N - m) * Sym.completeHomog L m)
        + ∑ r ∈ Icc 1 (m - 1), MvPolynomial.C (1 - q⁻¹)
            * ((-1 : Sym.Lambda L) ^ (m - r) * MvPolynomial.C ((-q) ^ (1 - (r : ℤ))))
            * (Sym.elemSymm L (N - m) * Sym.completeHomog L m)
      = (-1 : Sym.Lambda L) ^ (m - 1) * Sym.elemSymm L (N - m) * Sym.completeHomog L m := by
    intro m hm
    simp only [Finset.mem_Icc] at hm
    rw [← Finset.sum_mul, ← Finset.mul_sum, ← add_mul, sum_zpow_scalar_C q (by omega)]
    ring
  have hc := sum_alternating_elemSymm_mul_completeHomog (K := L) hN
  rw [Finset.sum_range_succ'] at hc
  simp only [pow_zero, one_mul, Nat.sub_zero, CopPower.completeHomog_zero, mul_one] at hc
  have hterm : ∀ i ∈ range N,
      (-1 : Sym.Lambda L) ^ (i + 1 - 1) * Sym.elemSymm L (N - (i + 1))
          * Sym.completeHomog L (i + 1)
        = -((-1 : Sym.Lambda L) ^ (i + 1) * Sym.elemSymm L (N - (i + 1))
            * Sym.completeHomog L (i + 1)) := by
    intro i _
    rw [Nat.add_sub_cancel, pow_succ]
    ring
  rw [h1, h2, ← Finset.sum_add_distrib, Finset.sum_congr rfl h3, sum_Icc_one_eq_sum_range,
    Finset.sum_congr rfl hterm, Finset.sum_neg_distrib]
  linear_combination -hc

end Creation

/-! ### The composites of the creation operators and the creation seeds -/

section Seeds

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **A composite creation operator peels off its first part**: `C_{(r,β)} = C_r ∘ C_β`. -/
@[hjo "lem_cop_comp_cons"]
theorem copComp_cons (q : L) (r : ℕ) (β : List ℕ) :
    Sym.CopComp q (r :: β) = Sym.Cop q r * Sym.CopComp q β := by
  simp only [Sym.CopComp, List.map_cons, List.prod_cons]

/-- The block lists of the compositions of `N`, as a finite set of lists. -/
def compBlocks (N : ℕ) : Finset (List ℕ) :=
  Finset.univ.image (Composition.blocks : Composition N → List ℕ)

/-- A list is the block list of a composition of `N` exactly when its entries are positive and
it sums to `N`. -/
theorem mem_compBlocks {N : ℕ} {l : List ℕ} :
    l ∈ compBlocks N ↔ (∀ i ∈ l, 0 < i) ∧ l.sum = N := by
  simp only [compBlocks, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨fun _ hi => c.blocks_pos hi, c.blocks_sum⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨l, fun hi => h1 _ hi, h2⟩, rfl⟩

/-- Summing over the compositions of `N` is summing over their block lists. -/
theorem sum_compBlocks {M : Type*} [AddCommMonoid M] (N : ℕ) (F : List ℕ → M) :
    ∑ l ∈ compBlocks N, F l = ∑ c : Composition N, F c.blocks := by
  rw [compBlocks, Finset.sum_image fun _ _ _ _ h => Composition.ext h]

/-- The only composition of `0` is the empty one. -/
theorem compBlocks_zero : compBlocks 0 = {([] : List ℕ)} := by
  ext l
  simp only [mem_compBlocks, Finset.mem_singleton]
  constructor
  · rintro ⟨hpos, hsum⟩
    match l with
    | [] => rfl
    | a :: t =>
      rw [List.sum_cons] at hsum
      have := hpos a (by simp)
      omega
  · rintro rfl
    simp
/-- **Splitting a composition at its first part.** For `N ≥ 1` every composition of `N` is a
first part `1 ≤ r ≤ N` followed by a composition of `N - r`, and the assignment is a
bijection. -/
theorem compBlocks_eq_biUnion {N : ℕ} (hN : 0 < N) :
    compBlocks N = (Icc 1 N).biUnion fun r => (compBlocks (N - r)).image (r :: ·) := by
  ext l
  simp only [mem_compBlocks, Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_image]
  constructor
  · rintro ⟨hpos, hsum⟩
    match l with
    | [] => rw [List.sum_nil] at hsum; omega
    | r :: t =>
      rw [List.sum_cons] at hsum
      have hr : 0 < r := hpos r (by simp)
      exact ⟨r, ⟨hr, by omega⟩, t,
        ⟨fun i hi => hpos i (List.mem_cons_of_mem _ hi), by omega⟩, rfl⟩
  · rintro ⟨r, ⟨hr1, hrN⟩, t, ⟨hpos, hsum⟩, rfl⟩
    refine ⟨fun i hi => ?_, by rw [List.sum_cons, hsum]; omega⟩
    rcases List.mem_cons.mp hi with rfl | hi
    · omega
    · exact hpos i hi

/-- The split of `compBlocks_eq_biUnion`, as an identity between sums. -/
theorem sum_compBlocks_split {M : Type*} [AddCommMonoid M] {N : ℕ} (hN : 0 < N)
    (F : List ℕ → M) :
    ∑ l ∈ compBlocks N, F l = ∑ r ∈ Icc 1 N, ∑ l ∈ compBlocks (N - r), F (r :: l) := by
  rw [compBlocks_eq_biUnion hN, Finset.sum_biUnion]
  · exact Finset.sum_congr rfl fun r _ =>
      Finset.sum_image fun a _ b _ h => by simpa using h
  · intro r _ r' _ hne
    simp only [Function.onFun, Finset.disjoint_left, Finset.mem_image]
    rintro l ⟨t, -, rfl⟩ ⟨t', -, h⟩
    simp only [List.cons.injEq] at h
    exact hne h.1.symm

/-- **The creation seeds of `N` split at the first part**: the sum over the compositions of `N` is
`∑_{r=1}^{N} C_r` applied to the sum over the compositions of `N - r`. -/
@[hjo "lem_creation_seed_split"]
theorem sum_copComp_split (q : L) {N : ℕ} (hN : 0 < N) :
    ∑ c : Composition N, Sym.CopComp q c.blocks 1
      = ∑ r ∈ Icc 1 N, Sym.Cop q r (∑ c : Composition (N - r), Sym.CopComp q c.blocks 1) := by
  rw [← sum_compBlocks N fun l => Sym.CopComp q l 1, sum_compBlocks_split hN]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [map_sum, ← sum_compBlocks (N - r) fun l => Sym.Cop q r (Sym.CopComp q l 1)]
  exact Finset.sum_congr rfl fun l _ => by rw [copComp_cons, Module.End.mul_apply]

/-- **The elementary symmetric function is the sum of the creation seeds**: for every `N`,
`∑_{α ⊨ N} C_α 1 = e_N`. -/
@[hjo "lem_creation_seed_esymm"]
theorem sum_copComp_eq_elemSymm (q : L) (N : ℕ) :
    ∑ c : Composition N, Sym.CopComp q c.blocks 1 = Sym.elemSymm L N := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · rw [← sum_compBlocks 0 fun l => Sym.CopComp q l 1, compBlocks_zero,
        Finset.sum_singleton]
      simp [Sym.CopComp, elemSymm_zero]
    · have hstep : ∀ r ∈ Icc 1 N,
          Sym.Cop q r (∑ c : Composition (N - r), Sym.CopComp q c.blocks 1)
            = Sym.Cop q r (Sym.elemSymm L (N - r)) := by
        intro r hr
        simp only [Finset.mem_Icc] at hr
        rw [ih (N - r) (by omega)]
      rw [sum_copComp_split q hN, Finset.sum_congr rfl hstep]
      exact sum_cop_elemSymm q hN

end Seeds

end HJO.CreationSeeds
