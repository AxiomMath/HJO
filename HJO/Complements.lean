/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Evaluation.CrossCount
public import HJO.Evaluation.PrimitiveRankData
public import HJO.Determinant.CycleWeight
public import HJO.CarlssonMellit.MixedIdeal
public import Mathlib.RingTheory.Congruence.Hom
public import HJO.Collinear.KernelFactorClear
public import HJO.Collinear.SymbolSym
public import HJO.Collinear.PlethShiftMulti
public meta import HJO.Attr

/-! # Rank bijections, the cycle expansion, the two-step presentation of `Ã`, and the
Stanton--Stembridge trick

Four independent results, each the formal content of a lemma whose vocabulary is already in
place.

**The rank bijections.** For coprime `a, b` and an order filter `F` of the gap set of `⟨a, b⟩`, the
north ranks `ρ_F(i) = b min{r : y_r ≥ i} - ai`, `1 ≤ i ≤ b`, of the primitive path `P_F` are
exactly the integers `j` of the flag set `F̂` with `j - b ∉ F̂`, each once; and the east ranks
`σ_F(r) = rb - a y_r`, `0 ≤ r ≤ a - 1`, are exactly those with `j - a ∉ F̂`. Both rest on the
reading `rb - ai ∈ F̂ ⟺ i ≤ y_r` of the flag set through the heights of `P_F`, together with the
unique residue `r` with `rb ≡ j` modulo `a`.

**The cycle expansion.** For `a, b ≥ 1` the Leibniz expansion of `det(I - L_H)` runs over the
permutations of the vertices of the rank graph `G_H`; a permutation contributes only if it moves
every vertex of its support along an edge, its cycles then form a collection of vertex-disjoint
simple cycles, and its sign together with the `ℓ` minus signs of a cycle of length `ℓ` leaves
`(-1)^k` for a collection of `k` cycles. So `det(I - L_H) = ∑_C (-1)^{|C|} wt(C)`.

**The two-step presentation.** The extended Dyck path algebra `Ã` is the two-sided algebra `𝔹`
modulo the mixed ideal `J`: the relations of `𝔹` are among those of `Ã`, and the three mixed
relations of `Ã` are the generators of `J`, so the two quotient maps factor through each other.

**The Stanton--Stembridge trick and the clearing of the denominator.** The Laurent monomials
`z^α` are linearly independent in `K(z₁, …, z_k)`, so a Laurent polynomial is determined by its
monomial sum there. Each relabelling `z_i ↦ z_{σ(i)}` permutes the monomials, so `Sym_k` of a
Laurent polynomial is the Laurent polynomial whose coefficients are the averages over the
relabelled coefficient families; its constant coefficient is the constant coefficient of the
original. In the module `M_k` of formal sums, multiplying the symmetrised symbol `Ξ_c` by the
symmetric Laurent polynomial `Θ_k` commutes with every relabelling, and on each summand it clears
the kernel expansion `Ω̂_k` to the Laurent polynomial `L`; so `Θ_k Ξ_c = Sym_k(Π_c L)`, and if
`Ξ_c = 0` then `Sym_k(Π_c Ω_k) = 0` in `𝕜(z₁, …, z_k)`, `Θ_k` being symmetric and nonzero there.

## Main definitions

* `HJO.Dyck.TwoSided.Bq.quotientMixedIdealEquiv`: the isomorphism `𝔹/J ≃ Ã`.
* `HJO.Bglx.zMonomial`, `HJO.Bglx.laurentEval`: the Laurent monomial `z^α` and the reading of a
  Laurent polynomial in the rational function field.
* `HJO.Bglx.kernelDenomLaurent`, `HJO.Bglx.kernelClearLaurent`: `Θ_k` and the clearing product
  `L = ∏_{i<j}(1 - z_i/z_j)(1 - qu z_i/z_j)(1 - q z_j/z_i)(1 - u z_j/z_i)` as Laurent polynomials.
* `HJO.Bglx.laurentMulFamily`: the product of a Laurent polynomial with an arbitrary formal sum.

## Main results

* `HJO.MultiplicativeEvaluation.bijOn_northRank`: the north ranks are the flag set stepped by `b`.
* `HJO.MultiplicativeEvaluation.bijOn_eastRank`: the east ranks are the flag set stepped by `a`.
* `HJO.Determinant.det_one_sub_edgeWeight_eq_sum_collectionWeight`: the truncated determinant
  expands over cycle collections.
* `HJO.Dyck.TwoSided.Bq.exists_algEquiv_quotient_mixedIdeal`: `Ã` is `𝔹/J`, generator by generator.
* `HJO.Bglx.linearIndependent_zMonomial`: the Laurent monomials are linearly independent.
* `HJO.Bglx.exists_mvRatFuncSymmetrization_eq`,
  `HJO.Bglx.coeff_zero_eq_of_mvRatFuncSymmetrization_eq`: the Stanton--Stembridge trick.
* `HJO.Bglx.laurentMulFamily_kernelDenomLaurent_symbolSym`: `Θ_k Ξ_c = Sym_k(Π_c L)`.
* `HJO.Bglx.mvRatFuncSymmetrization_eq_zero_of_symbolSym_eq_zero`: `Ξ_c = 0` forces
  `Sym_k(Π_c Ω_k) = 0`.

## Implementation notes

The transfer matrix `L_H` is written as `Matrix.of fun r r' => edgeWeight a b s q r r'` on the
vertex type `Fin (H + 1)`, an edge between two vertices of `{0, …, H}` being automatically an edge
of `G_H`. A collection of cycles is a finite set of cyclic permutations of the vertices, pairwise
disjoint, each moving every vertex of its support along an edge of `rankGraph a b H`; this is the
presentation `HJO.Determinant.collectionWeight` is defined on. The sum over `k ≥ 0`, with the
`k`-collections in the `k`-th term, is written as one sum over all collections
with the sign `(-1)^{|C|}`; only finitely many collections exist, so the two are the same sum
regrouped.

The quotient `𝔹/J` is the quotient by the ring congruence of the two-sided ideal `J`, a
`K`-algebra.

A Laurent polynomial whose image in `𝕜(z₁, …, z_k)` is named by a symmetrisation enters a
statement through a representative `G` with `laurentEval G` equal to that image; the representative
exists by `exists_mvRatFuncSymmetrization_eq` and is unique by `linearIndependent_zMonomial`. The
kernel denominator `Θ_k` is used in the Laurent form `kernelDenomLaurent`, which is the cone ring
element `HJO.Bglx.kernelDenom` of every ordering (`laurentToCone_kernelDenomLaurent`) and has
finite support, so its product with an arbitrary formal sum is defined coefficientwise by a finite
sum. The coefficient field of the last two results is any field containing `ℚ`, its characteristic
zero being supplied from the `ℚ`-algebra structure.

## References

This file proves the lemmas `HJO.MultiplicativeEvaluation.bijOn_northRank`,
`HJO.MultiplicativeEvaluation.bijOn_eastRank`,
`HJO.Determinant.det_one_sub_edgeWeight_eq_sum_collectionWeight`,
`HJO.Dyck.TwoSided.Bq.exists_algEquiv_quotient_mixedIdeal`,
`HJO.Bglx.exists_mvRatFuncSymmetrization_eq`,
`HJO.Bglx.laurentMulFamily_kernelDenomLaurent_symbolSym` and
`HJO.Bglx.mvRatFuncSymmetrization_eq_zero_of_symbolSym_eq_zero`. References: F. Bergeron, A. M.
Garsia, E. Leven and G. Xin, *Some remarkable new plethystic operators in the theory of Macdonald
polynomials*, arXiv:1405.0316, equations (2.6) and (2.7); E. Carlsson and A. Mellit, *A proof of the
shuffle conjecture*, J. Amer. Math. Soc. **31** (2018), Section 3.
-/

@[expose] public section

open Finset NumericalSemigroup

namespace HJO.MultiplicativeEvaluation

open HJO.Primitive

variable {a b : ℕ} {F : Finset ℕ}

/-! ### The rank bijections -/

/-- A natural combination of the generators lies in the flag set. -/
theorem mem_flagSet_of_combination (hco : a.Coprime b) {j : ℤ} {u v : ℕ}
    (hj : j = (u : ℤ) * a + v * b) : j ∈ flagSet a b F := by
  rw [mem_flagSet_iff, flag_eq_one_iff]
  refine ⟨by rw [hj]; positivity, Or.inr ?_⟩
  have htn : j.toNat = u * a + v * b := by rw [hj]; omega
  rw [htn]
  by_contra h
  exact (Gaps.mem_gaps_iff_not_exists a b hco _).mp (((finspan {a, b}).mem_gaps_iff).mpr h)
    ⟨u, v, rfl⟩

/-- The flag set read through the heights of the primitive path, in the form of a membership. -/
theorem mem_flagSet_iff_le_ht (hco : a.Coprime b) (ha : 0 < a) (hF : Gaps.IsOrderFilter a b F)
    {r i : ℕ} (hr : r ≤ a) :
    (r : ℤ) * b - a * i ∈ flagSet a b F ↔ i ≤ Paths.ht (primitivePath a b F) r :=
  flag_eq_one_iff_le_ht hco ha hF hr

/-- There is a residue `0 ≤ r < a` with `rb ≡ j` modulo `a`. -/
theorem exists_residue (hco : a.Coprime b) (ha : 0 < a) (j : ℤ) :
    ∃ r : ℕ, r < a ∧ (a : ℤ) ∣ (r : ℤ) * b - j := by
  obtain ⟨x, y, hxy⟩ : IsCoprime (a : ℤ) (b : ℤ) := Nat.isCoprime_iff_coprime.mpr hco
  have ha' : (0 : ℤ) < a := by exact_mod_cast ha
  refine ⟨((j * y) % a).toNat, ?_, ?_⟩
  · have := Int.emod_lt_of_pos (j * y) ha'
    have := Int.emod_nonneg (j * y) ha'.ne'
    omega
  · have h0 := Int.emod_nonneg (j * y) ha'.ne'
    rw [Int.toNat_of_nonneg h0]
    have hdiv : (j * y) % a = j * y - a * ((j * y) / a) := by
      rw [Int.emod_def]
    refine ⟨-(j * x) - (j * y) / a * b, ?_⟩
    rw [hdiv]
    linear_combination j * hxy

/-- Two residues `r, r'` in a window of length `a` with `rb ≡ r'b` modulo `a` coincide. -/
theorem eq_of_mul_dvd (hco : a.Coprime b) {r r' : ℕ} {c : ℤ} (hr : r < a) (hr' : r' < a)
    (h : (r : ℤ) * b - r' * b = a * c) : r = r' := by
  have hacop : IsCoprime (a : ℤ) (b : ℤ) := Nat.isCoprime_iff_coprime.mpr hco
  have hdvd : (a : ℤ) ∣ ((r : ℤ) - r') := hacop.dvd_of_dvd_mul_right ⟨c, by linarith⟩
  have hrr : (r : ℤ) - r' = 0 := by
    refine Int.eq_zero_of_abs_lt_dvd hdvd ?_
    rw [abs_lt]
    have h1 : (r : ℤ) < a := by exact_mod_cast hr
    have h2 : (r' : ℤ) < a := by exact_mod_cast hr'
    exact ⟨by linarith, by linarith⟩
  omega

/-- **The north ranks are the flag set stepped by `b`.** For an order filter `F` of the gap set,
`i ↦ ρ_F(i)` is a bijection from `{1, …, b}` onto the set of integers `j ∈ F̂` with
`j - b ∉ F̂`. -/
@[hjo "lem_ret_north_flag"]
theorem bijOn_northRank (hco : a.Coprime b) (ha : 0 < a) (hF : Gaps.IsOrderFilter a b F) :
    Set.BijOn (northRank a b F) (Set.Icc 1 b)
      {j | j ∈ flagSet a b F ∧ j - b ∉ flagSet a b F} := by
  have hya : Paths.ht (primitivePath a b F) (a * 1) = b := by
    rw [Nat.mul_one]; exact ht_primitivePath_self a b F
  have hmono := (ReturnPath.isBelowDiagonal_primitivePath hco ha hF).ht_mono
  -- the first column reaching `i ≤ b` lies in `[1, a]`
  have hA : ∀ i, 1 ≤ i → i ≤ b →
      1 ≤ Paths.firstReach (primitivePath a b F) i ∧
        Paths.firstReach (primitivePath a b F) i ≤ a ∧
        i ≤ Paths.ht (primitivePath a b F) (Paths.firstReach (primitivePath a b F) i) ∧
        Paths.ht (primitivePath a b F) (Paths.firstReach (primitivePath a b F) i - 1) < i := by
    intro i hi1 hib
    have hle : Paths.firstReach (primitivePath a b F) i ≤ a := by
      have := ReturnPath.firstReach_le (primitivePath a b F) (i := i) (r := a * 1) le_rfl
        (by rw [hya]; exact hib)
      omega
    have hreach := ReturnPath.le_ht_firstReach (primitivePath a b F) (i := i)
      (by rw [hya]; exact hib)
    have hpos : 1 ≤ Paths.firstReach (primitivePath a b F) i := by
      by_contra h0
      have h00 : Paths.firstReach (primitivePath a b F) i = 0 := by omega
      rw [h00, ht_primitivePath_zero F ha] at hreach
      omega
    exact ⟨hpos, hle, hreach,
      ReturnPath.ht_lt_of_lt_firstReach (primitivePath a b F) (by omega)⟩
  refine ⟨?_, ?_, ?_⟩
  · -- the map lands in the asserted set
    rintro i ⟨hi1, hib⟩
    obtain ⟨h1, h2, h3, h4⟩ := hA i hi1 hib
    refine ⟨?_, ?_⟩
    · rw [northRank, show (b : ℤ) * (Paths.firstReach (primitivePath a b F) i : ℕ) - a * i
        = ((Paths.firstReach (primitivePath a b F) i : ℕ) : ℤ) * b - a * i by ring]
      exact (mem_flagSet_iff_le_ht hco ha hF h2).mpr h3
    · rw [northRank, show (b : ℤ) * (Paths.firstReach (primitivePath a b F) i : ℕ) - a * i - b
        = ((Paths.firstReach (primitivePath a b F) i - 1 : ℕ) : ℤ) * b - a * i by
          push_cast [Nat.cast_sub h1]; ring]
      rw [mem_flagSet_iff_le_ht hco ha hF (by omega)]
      omega
  · -- injectivity
    rintro i ⟨hi1, hib⟩ i' ⟨hi1', hib'⟩ h
    obtain ⟨h1, h2, -, -⟩ := hA i hi1 hib
    obtain ⟨h1', h2', -, -⟩ := hA i' hi1' hib'
    simp only [northRank] at h
    have hr := eq_of_mul_dvd (r := Paths.firstReach (primitivePath a b F) i - 1)
      (r' := Paths.firstReach (primitivePath a b F) i' - 1)
      (c := (i : ℤ) - i') hco (by omega) (by omega)
      (by push_cast [Nat.cast_sub h1, Nat.cast_sub h1']; linarith)
    have hrr : (Paths.firstReach (primitivePath a b F) i : ℤ) =
        Paths.firstReach (primitivePath a b F) i' := by omega
    rw [hrr] at h
    have ha' : (0 : ℤ) < a := by exact_mod_cast ha
    have : (a : ℤ) * i = a * i' := by linarith
    exact_mod_cast mul_left_cancel₀ ha'.ne' this
  · -- surjectivity
    rintro j ⟨hj, hjb⟩
    obtain ⟨r0, hr0, k, hk⟩ := exists_residue hco ha (j - b)
    set r := r0 + 1 with hr
    have hra : r ≤ a := by omega
    -- `j = rb - ak`
    have hjk : j = (r : ℤ) * b - a * k := by rw [hr]; push_cast; linarith
    -- `k ≥ 1`
    have hk1 : 1 ≤ k := by
      by_contra hk0
      exact hjb (mem_flagSet_of_combination hco (u := (-k).toNat) (v := r0)
        (by rw [hjk, hr]; push_cast; rw [Int.toNat_of_nonneg (by omega)]; ring))
    set i := k.toNat with hi
    have hik : (i : ℤ) = k := by rw [hi]; omega
    rw [← hik] at hjk
    have hle : i ≤ Paths.ht (primitivePath a b F) r :=
      (mem_flagSet_iff_le_ht hco ha hF hra).mp (hjk ▸ hj)
    have hlt : Paths.ht (primitivePath a b F) r0 < i := by
      have hjb' : (r0 : ℤ) * b - a * i ∉ flagSet a b F := by
        rw [show (r0 : ℤ) * b - a * i = j - b by rw [hjk, hr]; push_cast; ring]
        exact hjb
      rw [mem_flagSet_iff_le_ht hco ha hF (by omega)] at hjb'
      omega
    have hfr : Paths.firstReach (primitivePath a b F) i = r := by
      refine ReturnPath.firstReach_eq (primitivePath a b F) (by omega) hle fun j' hj' hcon => ?_
      have := hmono (show j' ≤ r0 by omega)
      omega
    have hib : i ≤ b := by
      have := hmono (show r ≤ a * 1 by omega)
      rw [hya] at this
      omega
    refine ⟨i, ⟨by omega, hib⟩, ?_⟩
    rw [northRank, hfr, hjk]
    ring

/-- **The east ranks are the flag set stepped by `a`.** For an order filter `F` of the gap set,
`r ↦ σ_F(r)` is a bijection from `{0, …, a - 1}` onto the set of integers `j ∈ F̂` with
`j - a ∉ F̂`. -/
@[hjo "lem_ret_east_flag"]
theorem bijOn_eastRank (hco : a.Coprime b) (ha : 0 < a) (hF : Gaps.IsOrderFilter a b F) :
    Set.BijOn (eastRank a b F) (Set.Iio a)
      {j | j ∈ flagSet a b F ∧ j - a ∉ flagSet a b F} := by
  refine ⟨?_, ?_, ?_⟩
  · rintro r (hr : r < a)
    refine ⟨(mem_flagSet_iff_le_ht hco ha hF hr.le).mpr le_rfl, ?_⟩
    rw [eastRank, show (r : ℤ) * b - a * (Paths.ht (primitivePath a b F) r : ℕ) - a
      = (r : ℤ) * b - a * ((Paths.ht (primitivePath a b F) r + 1 : ℕ) : ℤ) by push_cast; ring,
      mem_flagSet_iff_le_ht hco ha hF hr.le]
    omega
  · rintro r (hr : r < a) r' (hr' : r' < a) h
    simp only [eastRank] at h
    exact eq_of_mul_dvd (c := (Paths.ht (primitivePath a b F) r : ℤ) -
      Paths.ht (primitivePath a b F) r') hco hr hr' (by linarith)
  · rintro j ⟨hj, hja⟩
    obtain ⟨r, hr, k, hk⟩ := exists_residue hco ha j
    have hjk : j = (r : ℤ) * b - a * k := by linarith
    have hk0 : 0 ≤ k := by
      by_contra hk0
      exact hja (mem_flagSet_of_combination hco (u := (-k - 1).toNat) (v := r)
        (by rw [hjk, Int.toNat_of_nonneg (by omega)]; ring))
    set i := k.toNat with hi
    have hik : (i : ℤ) = k := by rw [hi]; omega
    rw [← hik] at hjk
    have hle : i ≤ Paths.ht (primitivePath a b F) r :=
      (mem_flagSet_iff_le_ht hco ha hF hr.le).mp (hjk ▸ hj)
    have hlt : Paths.ht (primitivePath a b F) r < i + 1 := by
      have hja' : (r : ℤ) * b - a * ((i + 1 : ℕ) : ℤ) ∉ flagSet a b F := by
        rw [show (r : ℤ) * b - a * ((i + 1 : ℕ) : ℤ) = j - a by rw [hjk]; push_cast; ring]
        exact hja
      rw [mem_flagSet_iff_le_ht hco ha hF hr.le] at hja'
      omega
    refine ⟨r, hr, ?_⟩
    rw [eastRank, hjk, show Paths.ht (primitivePath a b F) r = i by omega]

end HJO.MultiplicativeEvaluation

namespace HJO.Determinant

open Equiv

variable {R : Type*} [CommRing R] {a b H : ℕ}

/-- The Leibniz term of a permutation `σ` in `det(I - L_H)`, read along the steps `i → σ i`, is
`(-1)^k` times the weight of the collection of the `k` cycles of `σ`. -/
theorem sign_smul_prod_one_sub_edgeWeight (ha : 0 < a) (hb : 0 < b) (s q : R)
    (σ : Perm (Fin (H + 1))) :
    Perm.sign σ • ∏ i, (1 - (Matrix.of fun r r' : Fin (H + 1) =>
        edgeWeight a b s q (r : ℕ) (r' : ℕ) : Matrix (Fin (H + 1)) (Fin (H + 1)) R)) i (σ i)
      = (-1) ^ σ.cycleFactorsFinset.card * collectionWeight a b s q σ.cycleFactorsFinset := by
  rw [collectionWeight_cycleFactorsFinset, permWeight]
  have hprod : ∏ i, (1 - (Matrix.of fun r r' : Fin (H + 1) =>
        edgeWeight a b s q (r : ℕ) (r' : ℕ) : Matrix (Fin (H + 1)) (Fin (H + 1)) R)) i (σ i)
      = ∏ i ∈ σ.support, -edgeWeight a b s q (i : ℕ) (σ i : ℕ) := by
    rw [← Finset.prod_subset (Finset.subset_univ σ.support)]
    · refine Finset.prod_congr rfl fun i hi => ?_
      have hne : i ≠ σ i := fun h => (Perm.mem_support.mp hi) h.symm
      rw [Matrix.sub_apply, Matrix.one_apply_ne hne, Matrix.of_apply, zero_sub]
    · intro i _ hi
      have hσi : σ i = i := by simpa [Perm.mem_support] using hi
      rw [hσi, Matrix.sub_apply, Matrix.one_apply_eq, Matrix.of_apply, edgeWeight,
        ite_eq_right_iff.mpr (fun _ => by omega),
        ite_eq_right_iff.mpr (fun _ => by omega), sub_zero]
  rw [hprod, Finset.prod_neg, Units.smul_def, zsmul_eq_mul, Perm.sign_of_cycleType,
    Perm.sum_cycleType]
  have hcard : Multiset.card σ.cycleType = σ.cycleFactorsFinset.card := by
    rw [Perm.cycleType_def, Multiset.card_map]
    rfl
  rw [hcard]
  push_cast
  have h1 : ((-1 : R) ^ σ.support.card) * (-1) ^ σ.support.card = 1 := by
    rw [← pow_add, Even.neg_one_pow ⟨_, rfl⟩]
  generalize ∏ x ∈ σ.support, edgeWeight a b s q (x : ℕ) (σ x : ℕ) = w
  linear_combination ((-1 : R) ^ σ.cycleFactorsFinset.card * w) * h1

open Classical in
/-- **The truncated determinant expands over cycle collections.** For `a, b ≥ 1`, the
determinant `det(I - L_H)` of one minus the transfer matrix of the rank graph `G_H` is the sum,
over the collections `C` of pairwise vertex-disjoint simple directed cycles of `G_H`, of
`(-1)^k wt(C)`, where `k` is the number of cycles of `C` and `wt(C)` its weight. The cycles are
presented as cyclic permutations of the vertices `0, …, H` moving each vertex of their support
along an edge of `G_H`. -/
@[hjo "lem_det_cycle_expansion"]
theorem det_one_sub_edgeWeight_eq_sum_collectionWeight (ha : 0 < a) (hb : 0 < b) (s q : R) :
    (1 - (Matrix.of fun r r' : Fin (H + 1) => edgeWeight a b s q (r : ℕ) (r' : ℕ) :
        Matrix (Fin (H + 1)) (Fin (H + 1)) R)).det =
      ∑ C ∈ (Finset.univ : Finset (Finset (Perm (Fin (H + 1))))).filter
          (fun C : Finset (Perm (Fin (H + 1))) =>
          (∀ c ∈ C, c.IsCycle ∧ ∀ i ∈ c.support, (rankGraph a b H).Adj (i : ℕ) (c i : ℕ)) ∧
            (C : Set (Perm (Fin (H + 1)))).Pairwise Perm.Disjoint),
        (-1) ^ C.card * collectionWeight a b s q C := by
  rw [← Matrix.det_transpose, Matrix.det_apply]
  simp only [Matrix.transpose_apply]
  simp_rw [sign_smul_prod_one_sub_edgeWeight ha hb s q]
  refine Finset.sum_bij_ne_zero (fun σ _ _ => σ.cycleFactorsFinset) ?_ ?_ ?_ (fun _ _ _ => rfl)
  · intro σ _ hσ
    rw [collectionWeight_cycleFactorsFinset, permWeight] at hσ
    have hedge : ∀ i ∈ σ.support, ((σ i : ℕ) = (i : ℕ) + b ∨ (i : ℕ) = (σ i : ℕ) + a) := by
      intro i hi
      by_contra hcon
      push Not at hcon
      exact (right_ne_zero_of_mul hσ) (Finset.prod_eq_zero hi (edgeWeight_eq_zero hcon.1 hcon.2))
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun c hc => ⟨(Perm.mem_cycleFactorsFinset_iff.mp hc).1, fun i hi => ?_⟩,
      Perm.cycleFactorsFinset_pairwise_disjoint σ⟩
    rw [(Perm.mem_cycleFactorsFinset_iff.mp hc).2 i hi]
    exact rankGraph_adj.mpr ⟨hedge i (Perm.mem_cycleFactorsFinset_support_le hc hi),
      Nat.lt_succ_iff.mp i.isLt, Nat.lt_succ_iff.mp (σ i).isLt⟩
  · intro σ _ _ τ _ _ h
    exact Perm.cycleFactorsFinset_injective h
  · intro C hC hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hC
    obtain ⟨hcyc, hdisj⟩ := hC
    set σ := C.noncommProd id (hdisj.mono' fun _ _ => Perm.Disjoint.commute) with hσdef
    have hfac : σ.cycleFactorsFinset = C :=
      Perm.cycleFactorsFinset_eq_finset.2 ⟨fun c hc => (hcyc c hc).1, hdisj, hσdef.symm⟩
    exact ⟨σ, Finset.mem_univ _, by rw [hfac]; exact hg, hfac⟩

end HJO.Determinant

namespace HJO.Dyck.TwoSided.Bq

open Tilde

variable {K : Type*} [CommRing K] {q u : K} [Invertible q] [Invertible (q - 1)]

/-- The corner element `y_i` of the free algebra goes to the corner element `y_i` of `𝔹`. -/
@[simp] theorem mk_freeY (k i : ℕ) : mk K q (freeY K q k i) = yElt K q k i :=
  map_cornerOf _ q ⅟q ⅟(q - 1) mk_freeE mk_freeUp mk_freeDown mk_freeT k i

/-- The corner element `z_i` of the free algebra goes to the corner element `z_i` of `𝔹`. -/
@[simp] theorem mk_freeZ (k i : ℕ) : mk K q (freeZ K q k i) = zElt K q k i :=
  map_cornerOf _ (⅟q) q (-(q * ⅟(q - 1))) mk_freeE mk_freeUpStar mk_freeDown mk_freeTinv k i

variable (K q u) in
/-- The homomorphism `𝔹 → Ã` carrying each generator to the generator of the same name: every
relation of `𝔹` is a relation of `Ã`. -/
noncomputable def toAtilde : Bq K q →ₐ[K] Atilde K q u :=
  RingQuot.liftAlgHom K ⟨Atilde.mk K q u, fun x y h => by
    refine Atilde.mk_rel ?_
    cases h with
    | vertex_mul_self k => exact Tilde.Rel.vertex_mul_self k
    | vertex_mul_vertex h => exact Tilde.Rel.vertex_mul_vertex h
    | vertex_mul_down k => exact Tilde.Rel.vertex_mul_down k
    | down_mul_vertex k => exact Tilde.Rel.down_mul_vertex k
    | vertex_mul_braid k i => exact Tilde.Rel.vertex_mul_braid k i
    | braid_mul_vertex k i => exact Tilde.Rel.braid_mul_vertex k i
    | braid_eq_zero h => exact Tilde.Rel.braid_eq_zero h
    | source h => exact Tilde.Rel.source h
    | sourceStar h => exact Tilde.Rel.sourceStar h⟩

/-- `𝔹 → Ã` sends the class in `𝔹` of a free-algebra element to its class in `Ã`. -/
@[simp] theorem toAtilde_mk (x : FreeAlgebra K Tilde.Gen) :
    toAtilde K q u (mk K q x) = Atilde.mk K q u x := by
  rw [toAtilde, mk, RingQuot.liftAlgHom_mkAlgHom_apply]

/-- `𝔹 → Ã` sends the idempotent `e_k` of `𝔹` to `e_k` in `Ã`. -/
@[simp] theorem toAtilde_e (k : ℕ) : toAtilde K q u (e K q k) = Atilde.e K q u k :=
  toAtilde_mk _

/-- `𝔹 → Ã` sends `d₊` on `V_k` to `d₊` on `V_k`. -/
@[simp] theorem toAtilde_dPlus (k : ℕ) : toAtilde K q u (dPlus K q k) = Atilde.dPlus K q u k :=
  toAtilde_mk _

/-- `𝔹 → Ã` sends `d₊^*` on `V_k` to `d₊^*` on `V_k`. -/
@[simp] theorem toAtilde_dPlusStar (k : ℕ) :
    toAtilde K q u (dPlusStar K q k) = Atilde.dPlusStar K q u k :=
  toAtilde_mk _

/-- `𝔹 → Ã` sends `d₋` on `V_k` to `d₋` on `V_k`. -/
@[simp] theorem toAtilde_dMinus (k : ℕ) : toAtilde K q u (dMinus K q k) = Atilde.dMinus K q u k :=
  toAtilde_mk _

/-- `𝔹 → Ã` sends the Hecke generator `T_i` on `V_k` to `T_i` on `V_k`. -/
@[simp] theorem toAtilde_Tg (k i : ℕ) : toAtilde K q u (Tg K q k i) = Atilde.Tg K q u k i :=
  toAtilde_mk _

/-- `𝔹 → Ã` sends `y_i` on `V_k` to `y_i` on `V_k`. -/
@[simp] theorem toAtilde_yElt (k i : ℕ) :
    toAtilde K q u (yElt K q k i) = Atilde.yElt K q u k i := by
  rw [← mk_freeY, toAtilde_mk, Atilde.mk_freeY]

/-- `𝔹 → Ã` sends `z_i` on `V_k` to `z_i` on `V_k`. -/
@[simp] theorem toAtilde_zElt (k i : ℕ) :
    toAtilde K q u (zElt K q k i) = Atilde.zElt K q u k i := by
  rw [← mk_freeZ, toAtilde_mk, Atilde.mk_freeZ]

/-- The mixed ideal lies in the kernel of `𝔹 → Ã`: its three families of generators are the three
mixed relations of `Ã`. -/
theorem mixedIdeal_le_ker_toAtilde :
    mixedIdeal K q u ≤ TwoSidedIdeal.ker (toAtilde K q u) := by
  refine TwoSidedIdeal.span_le.mpr ?_
  rintro x ((⟨k, i, h1, h2, rfl⟩ | ⟨k, i, h1, h2, rfl⟩) | ⟨k, rfl⟩) <;>
    simp only [SetLike.mem_coe, TwoSidedIdeal.mem_ker, map_sub, map_add, map_mul, map_smul,
      toAtilde_yElt, toAtilde_zElt, toAtilde_dPlus, toAtilde_dPlusStar, sub_eq_zero]
  · have := Atilde.mk_rel (Tilde.Rel.mixed_z (K := K) (q := q) (u := u) h1 h2)
    simpa using this
  · have := Atilde.mk_rel (Tilde.Rel.mixed_y (K := K) (q := q) (u := u) h1 h2)
    simpa using this
  · have := Atilde.mk_rel (Tilde.Rel.mixed_top (K := K) (q := q) (u := u) k)
    simp only [map_mul, map_smul, Atilde.mk_freeY, Atilde.mk_freeZ, Atilde.mk_freeUp,
      Atilde.mk_freeUpStar] at this
    rw [this, neg_smul, neg_add_cancel]

variable (K q u) in
/-- The homomorphism `𝔹/J → Ã` induced by `𝔹 → Ã`, which kills the mixed ideal. -/
noncomputable def quotientToAtilde : (mixedIdeal K q u).ringCon.Quotient →ₐ[K] Atilde K q u :=
  RingCon.liftₐ _ (toAtilde K q u) fun x y h => by
    rw [TwoSidedIdeal.rel_iff] at h
    have h' := mixedIdeal_le_ker_toAtilde h
    rw [TwoSidedIdeal.mem_ker, map_sub, sub_eq_zero] at h'
    exact h'

/-- `𝔹/J → Ã` sends the class of `x ∈ 𝔹` to the image of `x` under `𝔹 → Ã`. -/
@[simp] theorem quotientToAtilde_mkₐ (x : Bq K q) :
    quotientToAtilde K q u (RingCon.mkₐ K (mixedIdeal K q u).ringCon x) = toAtilde K q u x :=
  rfl

/-- Two elements of `𝔹` whose difference lies in `J` have the same class in `𝔹/J`. -/
theorem mkₐ_eq_of_sub_mem {x y : Bq K q} (h : x - y ∈ mixedIdeal K q u) :
    RingCon.mkₐ K (mixedIdeal K q u).ringCon x = RingCon.mkₐ K (mixedIdeal K q u).ringCon y :=
  (RingCon.eq _).mpr ((TwoSidedIdeal.rel_iff _ _ _).mpr h)

variable (K q u) in
/-- The homomorphism `Ã → 𝔹/J` carrying each generator to the class of the generator of the same
name: the relations of `𝔹` hold in `𝔹`, and the three mixed relations hold modulo `J`. -/
noncomputable def atildeToQuotient : Atilde K q u →ₐ[K] (mixedIdeal K q u).ringCon.Quotient :=
  RingQuot.liftAlgHom K ⟨(RingCon.mkₐ K (mixedIdeal K q u).ringCon).comp (mk K q), fun x y h => by
    have hB : ∀ {x y : FreeAlgebra K Tilde.Gen}, Rel K q x y →
        ((RingCon.mkₐ K (mixedIdeal K q u).ringCon).comp (mk K q)) x =
          ((RingCon.mkₐ K (mixedIdeal K q u).ringCon).comp (mk K q)) y :=
      fun h => by rw [AlgHom.comp_apply, AlgHom.comp_apply, mk_rel h]
    cases h with
    | vertex_mul_self k => exact hB (Rel.vertex_mul_self k)
    | vertex_mul_vertex h => exact hB (Rel.vertex_mul_vertex h)
    | vertex_mul_down k => exact hB (Rel.vertex_mul_down k)
    | down_mul_vertex k => exact hB (Rel.down_mul_vertex k)
    | vertex_mul_braid k i => exact hB (Rel.vertex_mul_braid k i)
    | braid_mul_vertex k i => exact hB (Rel.braid_mul_vertex k i)
    | braid_eq_zero h => exact hB (Rel.braid_eq_zero h)
    | source h => exact hB (Rel.source h)
    | sourceStar h => exact hB (Rel.sourceStar h)
    | mixed_z h1 h2 =>
      simp only [AlgHom.comp_apply, map_mul, mk_freeZ, mk_freeUp]
      exact mkₐ_eq_of_sub_mem (mixedGenZ_subset_mixedIdeal ⟨_, _, h1, h2, rfl⟩)
    | mixed_y h1 h2 =>
      simp only [AlgHom.comp_apply, map_mul, mk_freeY, mk_freeUpStar]
      exact mkₐ_eq_of_sub_mem (mixedGenY_subset_mixedIdeal ⟨_, _, h1, h2, rfl⟩)
    | mixed_top k =>
      simp only [AlgHom.comp_apply, map_mul, map_smul, mk_freeY, mk_freeZ, mk_freeUp,
        mk_freeUpStar]
      refine mkₐ_eq_of_sub_mem ?_
      simp only [neg_smul, sub_neg_eq_add]
      exact mixedGenTop_subset_mixedIdeal ⟨k, rfl⟩⟩

/-- `Ã → 𝔹/J` sends the class in `Ã` of a free-algebra element to the class in `𝔹/J` of its
class in `𝔹`. -/
@[simp] theorem atildeToQuotient_mk (x : FreeAlgebra K Tilde.Gen) :
    atildeToQuotient K q u (Atilde.mk K q u x) =
      RingCon.mkₐ K (mixedIdeal K q u).ringCon (mk K q x) := by
  rw [atildeToQuotient, Atilde.mk, RingQuot.liftAlgHom_mkAlgHom_apply, AlgHom.comp_apply]

variable (K q u) in
/-- **The extended algebra is the two-sided algebra modulo the mixed ideal**: `𝔹/J ≃ Ã`, the
class of each generator going to the generator of the same name. -/
noncomputable def quotientMixedIdealEquiv :
    (mixedIdeal K q u).ringCon.Quotient ≃ₐ[K] Atilde K q u :=
  AlgEquiv.ofAlgHom (quotientToAtilde K q u) (atildeToQuotient K q u)
    (RingQuot.ringQuot_ext' K _ _ (FreeAlgebra.hom_ext (funext fun x => by
      simp only [Function.comp_apply, AlgHom.comp_apply, AlgHom.id_apply]
      rw [show RingQuot.mkAlgHom K (Tilde.Rel K q u) (FreeAlgebra.ι K x) =
        Atilde.mk K q u (FreeAlgebra.ι K x) from rfl, atildeToQuotient_mk, quotientToAtilde_mkₐ,
        toAtilde_mk])))
    (RingCon.Quotient.hom_extₐ (RingQuot.ringQuot_ext' K _ _ (FreeAlgebra.hom_ext
      (funext fun x => by
        simp only [Function.comp_apply, AlgHom.comp_apply, AlgHom.id_apply]
        rw [quotientToAtilde_mkₐ, show RingQuot.mkAlgHom K (Rel K q) (FreeAlgebra.ι K x) =
          mk K q (FreeAlgebra.ι K x) from rfl, toAtilde_mk, atildeToQuotient_mk]))))

/-- The isomorphism `𝔹/J ≃ Ã` sends the class of `x ∈ 𝔹` to the image of `x` under `𝔹 → Ã`. -/
@[simp] theorem quotientMixedIdealEquiv_mkₐ (x : Bq K q) :
    quotientMixedIdealEquiv K q u (RingCon.mkₐ K (mixedIdeal K q u).ringCon x) =
      toAtilde K q u x := by
  rw [quotientMixedIdealEquiv, AlgEquiv.ofAlgHom_apply, quotientToAtilde_mkₐ]

/-- **`HJO.Dyck.TwoSided.Bq.exists_algEquiv_quotient_mixedIdeal`.** There is an isomorphism from
`𝔹/J` to `Ã` carrying the class of each generator `e_k`, `d₊`, `d₊^*`, `d₋`, `T_i` of `𝔹` to the
generator of `Ã` of the same name. -/
@[hjo "lem_cm_dpa_tilde_two_step"]
theorem exists_algEquiv_quotient_mixedIdeal :
    ∃ φ : (mixedIdeal K q u).ringCon.Quotient ≃ₐ[K] Atilde K q u,
      (∀ k, φ (RingCon.mkₐ K _ (e K q k)) = Atilde.e K q u k) ∧
      (∀ k, φ (RingCon.mkₐ K _ (dPlus K q k)) = Atilde.dPlus K q u k) ∧
      (∀ k, φ (RingCon.mkₐ K _ (dPlusStar K q k)) = Atilde.dPlusStar K q u k) ∧
      (∀ k, φ (RingCon.mkₐ K _ (dMinus K q k)) = Atilde.dMinus K q u k) ∧
      (∀ k i, φ (RingCon.mkₐ K _ (Tg K q k i)) = Atilde.Tg K q u k i) :=
  ⟨quotientMixedIdealEquiv K q u,
    fun _ => by rw [quotientMixedIdealEquiv_mkₐ, toAtilde_e],
    fun _ => by rw [quotientMixedIdealEquiv_mkₐ, toAtilde_dPlus],
    fun _ => by rw [quotientMixedIdealEquiv_mkₐ, toAtilde_dPlusStar],
    fun _ => by rw [quotientMixedIdealEquiv_mkₐ, toAtilde_dMinus],
    fun _ _ => by rw [quotientMixedIdealEquiv_mkₐ, toAtilde_Tg]⟩

end HJO.Dyck.TwoSided.Bq

namespace HJO.Bglx

open HJO.Sym

/-! ### Laurent monomials in the rational function field -/

section Monomial

variable (K : Type*) [CommRing K] [IsDomain K] {k : ℕ}

/-- The Laurent monomial `z^α = z₁^{α₁} ⋯ z_k^{α_k}` in the rational function field
`K(z₁, …, z_k)`. -/
noncomputable def zMonomial (α : Fin k →₀ ℤ) : FractionRing (MvPolynomial (Fin k) K) :=
  ∏ i, zVar K i ^ α i

variable {K}

/-- The Laurent monomial with zero exponent is `1`. -/
@[simp] theorem zMonomial_zero : zMonomial K (0 : Fin k →₀ ℤ) = 1 := by
  simp [zMonomial]

/-- `z^{α + β} = z^α z^β`. -/
theorem zMonomial_add (α β : Fin k →₀ ℤ) :
    zMonomial K (α + β) = zMonomial K α * zMonomial K β := by
  rw [zMonomial, zMonomial, zMonomial, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => by rw [Finsupp.add_apply, zpow_add₀ (zVar_ne_zero i)]

/-- A Laurent monomial with nonnegative exponents is the image of a monomial of the polynomial
ring. -/
theorem zMonomial_eq_algebraMap_monomial {α : Fin k →₀ ℤ} {m : Fin k →₀ ℕ}
    (h : ∀ i, α i = m i) :
    zMonomial K α =
      algebraMap (MvPolynomial (Fin k) K) _ (MvPolynomial.monomial m (1 : K)) := by
  rw [MvPolynomial.monomial_eq, map_one, one_mul,
    Finsupp.prod_fintype _ _ fun _ => pow_zero _, map_prod, zMonomial]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [h i, zpow_natCast, map_pow]
  rfl

/-- **The Laurent monomials are linearly independent** in `K(z₁, …, z_k)`: a relation among
finitely many of them, multiplied by a monomial clearing every negative exponent, is a relation
among distinct monomials of the polynomial ring. -/
theorem linearIndependent_zMonomial {K : Type*} [Field K] :
    LinearIndependent K (zMonomial K (k := k)) := by
  rw [linearIndependent_iff']
  intro s g hg α hα
  set N : ℕ := ∑ β ∈ s, ∑ i, (β i).natAbs
  have hN : ∀ β ∈ s, ∀ i, ((β i).natAbs : ℤ) ≤ N := by
    intro β hβ i
    have h1 : (β i).natAbs ≤ ∑ j, (β j).natAbs :=
      Finset.single_le_sum (f := fun j => (β j).natAbs) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)
    have h2 : ∑ j, (β j).natAbs ≤ N :=
      Finset.single_le_sum (f := fun β : Fin k →₀ ℤ => ∑ j, (β j).natAbs)
        (fun _ _ => Nat.zero_le _) hβ
    exact_mod_cast h1.trans h2
  set sh : Fin k →₀ ℤ := Finsupp.equivFunOnFinite.symm fun _ => (N : ℤ)
  let e : (Fin k →₀ ℤ) → (Fin k →₀ ℕ) := fun β =>
    Finsupp.equivFunOnFinite.symm fun i => (β i + N).toNat
  have hnn : ∀ β ∈ s, ∀ i, 0 ≤ β i + N := fun β hβ i => by
    have := hN β hβ i
    omega
  have he : ∀ β ∈ s, ∀ i, (β + sh) i = (e β i : ℤ) := fun β hβ i => by
    simp only [Finsupp.add_apply, sh, e, Finsupp.coe_equivFunOnFinite_symm]
    exact (Int.toNat_of_nonneg (hnn β hβ i)).symm
  have heinj : ∀ β ∈ s, e β = e α → β = α := fun β hβ h => by
    ext i
    have h₁ := he β hβ i
    have h₂ := he α hα i
    rw [h, Finsupp.add_apply] at h₁
    rw [Finsupp.add_apply] at h₂
    omega
  have hpoly : algebraMap (MvPolynomial (Fin k) K) (FractionRing (MvPolynomial (Fin k) K))
      (∑ β ∈ s, MvPolynomial.monomial (e β) (g β)) = 0 := by
    have : (∑ β ∈ s, g β • zMonomial K β) * zMonomial K sh = 0 := by rw [hg, zero_mul]
    rw [Finset.sum_mul] at this
    rw [map_sum, ← this]
    refine Finset.sum_congr rfl fun β hβ => ?_
    rw [smul_mul_assoc, ← zMonomial_add, zMonomial_eq_algebraMap_monomial (he β hβ),
      Algebra.smul_def, ← algebraMap_mvPolynomial_C, ← map_mul, MvPolynomial.C_mul_monomial,
      mul_one]
  have hP := (IsFractionRing.injective (MvPolynomial (Fin k) K) _) (hpoly.trans (map_zero _).symm)
  have hcoeff := congrArg (MvPolynomial.coeff (e α)) hP
  rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_zero,
    Finset.sum_eq_single α (fun β hβ hne => by
      rw [MvPolynomial.coeff_monomial]
      split_ifs with h
      · exact absurd (heinj β hβ h) hne
      · rfl)
      (fun h => absurd hα h)] at hcoeff
  simpa [MvPolynomial.coeff_monomial] using hcoeff

end Monomial

section Symmetrisation

variable {K : Type*} [Field K] [CharZero K] {k : ℕ}

omit [CharZero K] in
/-- The monomial sum `∑_α f_α z^α`, written as a sum over exponents, is the linear combination of
the Laurent monomials. -/
theorem sum_algebraMap_mul_prod_zVar (f : (Fin k →₀ ℤ) →₀ K) :
    (f.sum fun α c =>
        algebraMap K (FractionRing (MvPolynomial (Fin k) K)) c * ∏ i, zVar K i ^ α i) =
      Finsupp.linearCombination K (zMonomial K) f := by
  rw [Finsupp.linearCombination_apply]
  exact Finsupp.sum_congr fun α _ => (Algebra.smul_def _ _).symm

omit [CharZero K] in
/-- The relabelling `z_i ↦ z_{σ(i)}` of the rational function field carries `z^α` to
`z^{σ_* α}`, where `(σ_* α)_{σ(i)} = α_i`. -/
theorem fieldEquivOfAlgEquiv_renameEquiv_zMonomial (σ : Equiv.Perm (Fin k))
    (α : Fin k →₀ ℤ) :
    IsFractionRing.fieldEquivOfAlgEquiv K (FractionRing (MvPolynomial (Fin k) K))
        (FractionRing (MvPolynomial (Fin k) K)) (MvPolynomial.renameEquiv K σ) (zMonomial K α) =
      zMonomial K (Finsupp.domCongr σ α) := by
  rw [zMonomial, map_prod, zMonomial]
  refine Fintype.prod_equiv σ _ _ fun i => ?_
  rw [map_zpow₀, zVar, IsFractionRing.fieldEquivOfAlgEquiv_algebraMap,
    MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X, Finsupp.domCongr_apply,
    Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply]
  rfl

/-- Symmetrisation of a monomial sum is the monomial sum of the averaged coefficient family. -/
theorem mvRatFuncSymmetrization_linearCombination (f : (Fin k →₀ ℤ) →₀ K) :
    mvRatFuncSymmetrization K k (Finsupp.linearCombination K (zMonomial K) f) =
      Finsupp.linearCombination K (zMonomial K)
        ((Nat.factorial k : K)⁻¹ • ∑ σ : Equiv.Perm (Fin k),
          Finsupp.mapDomain (Finsupp.domCongr σ) f) := by
  rw [map_smul, map_sum, mvRatFuncSymmetrization, LinearMap.smul_apply, LinearMap.sum_apply]
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [AlgEquiv.toLinearMap_apply, Finsupp.linearCombination_mapDomain]
  rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply, map_finsuppSum]
  refine Finsupp.sum_congr fun α _ => ?_
  rw [Algebra.smul_def, map_mul, AlgEquiv.commutes, ← Algebra.smul_def,
    fieldEquivOfAlgEquiv_renameEquiv_zMonomial]
  rfl

/-- The symmetrisation of a Laurent polynomial is a Laurent polynomial: the monomial sum of `F`
is carried by `Sym_k` to the monomial sum of the average of the `k!` relabellings of `F`. This is
what makes the coefficient of `z₁⁰z₂⁰ ⋯ z_k⁰` in `Sym_k F` meaningful; the representative is
unique by `linearIndependent_zMonomial`. -/
@[hjo "lem_bglx_sss"]
theorem exists_mvRatFuncSymmetrization_eq (F : AddMonoidAlgebra K (Fin k →₀ ℤ)) :
    ∃ G : AddMonoidAlgebra K (Fin k →₀ ℤ), mvRatFuncSymmetrization K k
        (F.coeff.sum fun α c =>
          algebraMap K (FractionRing (MvPolynomial (Fin k) K)) c * ∏ i, zVar K i ^ α i)
      = G.coeff.sum fun α c =>
          algebraMap K (FractionRing (MvPolynomial (Fin k) K)) c * ∏ i, zVar K i ^ α i := by
  refine ⟨AddMonoidAlgebra.ofCoeff ((Nat.factorial k : K)⁻¹ • ∑ σ : Equiv.Perm (Fin k),
    Finsupp.mapDomain (Finsupp.domCongr σ) F.coeff), ?_⟩
  rw [sum_algebraMap_mul_prod_zVar, sum_algebraMap_mul_prod_zVar,
    mvRatFuncSymmetrization_linearCombination]

/-- **The Stanton--Stembridge symmetrisation trick.** Let `F` be a Laurent polynomial in
`z₁, …, z_k` over `K` and let `G` be a Laurent polynomial representing `Sym_k F`, that is, one
whose monomial sum `∑_α g_α z₁^{α₁} ⋯ z_k^{α_k}` in `K(z₁, …, z_k)` is the symmetrisation of the
monomial sum of `F`. Then the coefficient of `z₁⁰z₂⁰ ⋯ z_k⁰` in `G` equals that in `F`. -/
@[hjo "lem_bglx_sss"]
theorem coeff_zero_eq_of_mvRatFuncSymmetrization_eq
    {F G : AddMonoidAlgebra K (Fin k →₀ ℤ)}
    (hFG : mvRatFuncSymmetrization K k
        (F.coeff.sum fun α c =>
          algebraMap K (FractionRing (MvPolynomial (Fin k) K)) c * ∏ i, zVar K i ^ α i)
      = G.coeff.sum fun α c =>
          algebraMap K (FractionRing (MvPolynomial (Fin k) K)) c * ∏ i, zVar K i ^ α i) :
    G.coeff 0 = F.coeff 0 := by
  rw [sum_algebraMap_mul_prod_zVar, sum_algebraMap_mul_prod_zVar,
    mvRatFuncSymmetrization_linearCombination] at hFG
  have hG := linearIndependent_zMonomial (K := K) (k := k) hFG
  rw [← hG, Finsupp.smul_apply, Finsupp.finsetSum_apply]
  have h0 : ∀ σ : Equiv.Perm (Fin k),
      Finsupp.mapDomain (Finsupp.domCongr σ) F.coeff 0 = F.coeff 0 := fun σ => by
    conv_lhs => rw [← map_zero (Finsupp.domCongr (M := ℤ) σ)]
    exact Finsupp.mapDomain_apply (Finsupp.domCongr σ).injective _ _
  simp only [h0, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul, smul_eq_mul]
  rw [inv_mul_cancel_left₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k))]

end Symmetrisation

/-! ### Laurent polynomials read in the rational function field -/

section Eval

variable (K : Type*) [Field K] (k : ℕ)

/-- `α ↦ z^α`, as a monoid homomorphism from the exponent lattice. -/
noncomputable def zMonomialHom :
    Multiplicative (Fin k →₀ ℤ) →* FractionRing (MvPolynomial (Fin k) K) where
  toFun α := zMonomial K α.toAdd
  map_one' := by rw [toAdd_one, zMonomial_zero]
  map_mul' α β := by rw [toAdd_mul, zMonomial_add]

/-- A Laurent polynomial `∑_α f_α z^α` read in the rational function field `K(z₁, …, z_k)`, as a
`K`-algebra homomorphism. It is injective, by `linearIndependent_zMonomial`. -/
noncomputable def laurentEval :
    AddMonoidAlgebra K (Fin k →₀ ℤ) →ₐ[K] FractionRing (MvPolynomial (Fin k) K) :=
  AddMonoidAlgebra.lift K _ (Fin k →₀ ℤ) (zMonomialHom K k)

variable {K k}

/-- The evaluation of `F = ∑_α f_α z^α` is the linear combination `∑_α f_α z^α` in
`K(z₁, …, z_k)`. -/
theorem laurentEval_apply (F : AddMonoidAlgebra K (Fin k →₀ ℤ)) :
    laurentEval K k F = Finsupp.linearCombination K (zMonomial K) F.coeff := by
  rw [laurentEval, AddMonoidAlgebra.lift_apply', Finsupp.linearCombination_apply]
  exact Finsupp.sum_congr fun α _ => (Algebra.smul_def _ _).symm

/-- The evaluation of the single term `c z^β` is `c z^β`. -/
theorem laurentEval_single (β : Fin k →₀ ℤ) (c : K) :
    laurentEval K k (AddMonoidAlgebra.single β c) = algebraMap K _ c * zMonomial K β := by
  rw [laurentEval, AddMonoidAlgebra.lift_single, Algebra.smul_def]
  rfl

/-- The Laurent monomial with exponent `n` at `i` and zero elsewhere is `z_i ^ n`. -/
theorem zMonomial_single (i : Fin k) (n : ℤ) :
    zMonomial K (Finsupp.single i n) = zVar K i ^ n := by
  rw [zMonomial, Finset.prod_eq_single i (fun j _ hj => by
    rw [Finsupp.single_eq_of_ne hj, zpow_zero]) (fun h => absurd (Finset.mem_univ i) h),
    Finsupp.single_eq_same]

theorem zMonomial_single_sub_single (i j : Fin k) :
    zMonomial K (Finsupp.single i (1 : ℤ) - Finsupp.single j 1) = zVar K i / zVar K j := by
  rw [sub_eq_add_neg, zMonomial_add, ← Finsupp.single_neg, zMonomial_single, zMonomial_single,
    zpow_one, zpow_neg_one, div_eq_mul_inv]

/-- The relabelling `z_i ↦ z_{σ(i)}` of the rational function field on a variable. -/
theorem fieldEquivOfAlgEquiv_renameEquiv_zVar (σ : Equiv.Perm (Fin k)) (i : Fin k) :
    IsFractionRing.fieldEquivOfAlgEquiv K (FractionRing (MvPolynomial (Fin k) K))
        (FractionRing (MvPolynomial (Fin k) K)) (MvPolynomial.renameEquiv K σ) (zVar K i) =
      zVar K (σ i) := by
  rw [zVar, IsFractionRing.fieldEquivOfAlgEquiv_algebraMap, MvPolynomial.renameEquiv_apply,
    MvPolynomial.rename_X]
  rfl

end Eval

/-! ### Clearing the denominator on the symmetrised symbol -/

section Clear

variable {L : Type*} [Field L] [Algebra ℚ L] {k : ℕ}

/-- A field containing `ℚ` has characteristic zero. -/
local instance : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective

omit [Algebra ℚ L] in
/-- The Laurent polynomial `z^β` with coefficients in `Λ`, read in a cone ring, is the monomial. -/
theorem laurentToCone_single_one (τ : Equiv.Perm (Fin k)) (β : Fin k →₀ ℤ) :
    laurentToCone τ (AddMonoidAlgebra.single β (1 : Lambda L)) = monoElem τ β :=
  ConeRing.ext (funext fun α => by
    rw [coeff_laurentToCone, coeff_monoElem, AddMonoidAlgebra.coeff_single]
    simp [Finsupp.single_apply, eq_comm])

omit [Algebra ℚ L] in
/-- A constant Laurent polynomial, read in a cone ring, is the constant. -/
theorem laurentToCone_laurentConst (τ : Equiv.Perm (Fin k)) (a : L) :
    laurentToCone τ (laurentConst L k a) = scalarElem τ a :=
  ConeRing.ext (funext fun α => by
    rw [coeff_laurentToCone, coeff_scalarElem, laurentConst_apply, AddMonoidAlgebra.coeff_single]
    simp [Finsupp.single_apply, eq_comm])

variable (L) in
/-- The coefficientwise inclusion of the Laurent polynomials over `𝕜` into those over `Λ`. -/
noncomputable abbrev laurentLambdaMap (k : ℕ) :
    AddMonoidAlgebra L (Fin k →₀ ℤ) →+* LaurentLambda L k :=
  AddMonoidAlgebra.mapRingHom (Fin k →₀ ℤ) (algebraMap L (Lambda L))

/-- The kernel denominator `Θ_k = ∏_{i ≠ j} (1 - q z_i/z_j)(1 - u z_i/z_j)` as a Laurent
polynomial with coefficients in `Λ`. -/
noncomputable def kernelDenomLaurent (q u : L) (k : ℕ) : LaurentLambda L k :=
  ∏ p ∈ Finset.univ.offDiag,
    ((1 - laurentConst L k q *
        AddMonoidAlgebra.single (Finsupp.single p.1 (1 : ℤ) - Finsupp.single p.2 1) 1) *
      (1 - laurentConst L k u *
        AddMonoidAlgebra.single (Finsupp.single p.1 (1 : ℤ) - Finsupp.single p.2 1) 1))

omit [Algebra ℚ L] in
/-- In every cone ring the Laurent kernel denominator is the kernel denominator. -/
theorem laurentToCone_kernelDenomLaurent (q u : L) (τ : Equiv.Perm (Fin k)) :
    laurentToCone τ (kernelDenomLaurent q u k) = kernelDenom q u k τ := by
  simp only [kernelDenomLaurent, kernelDenom, map_prod, map_mul, map_sub, map_one,
    laurentToCone_single_one, laurentToCone_laurentConst]

omit [Algebra ℚ L] in
/-- `Θ_k` is symmetric: its coefficients are invariant under relabelling the exponents. -/
theorem coeff_kernelDenomLaurent_relabelExp (q u : L) (τ : Equiv.Perm (Fin k))
    (β : Fin k →₀ ℤ) :
    (kernelDenomLaurent q u k).coeff (relabelExp τ β) = (kernelDenomLaurent q u k).coeff β := by
  have hsingle : ∀ a b : Fin k, relabelExp τ (Finsupp.single a (1 : ℤ) - Finsupp.single b 1) =
      Finsupp.single (τ a) 1 - Finsupp.single (τ b) 1 := fun a b => by
    rw [map_sub, relabelExp, Finsupp.domCongr_apply, Finsupp.domCongr_apply,
      Finsupp.equivMapDomain_single, Finsupp.equivMapDomain_single]
  have h : AddMonoidAlgebra.mapDomainRingHom (Lambda L) (relabelExp τ).toAddMonoidHom
      (kernelDenomLaurent q u k) = kernelDenomLaurent q u k := by
    rw [kernelDenomLaurent, map_prod]
    simp only [map_mul, map_sub, map_one, laurentConst_apply,
      AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single,
      AddEquiv.coe_toAddMonoidHom, map_zero, hsingle]
    refine Finset.prod_equiv (Equiv.prodCongr τ τ) (fun p => ?_) fun _ _ => rfl
    simp [Finset.mem_offDiag]
  conv_lhs => rw [← h]
  rw [AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.coeff_mapDomain]
  exact Finsupp.mapDomain_apply (M := Lambda L) (relabelExp τ).injective
    (kernelDenomLaurent q u k).coeff β

/-- The product of a Laurent polynomial with an arbitrary formal sum: each coefficient is the
finite sum `(x f)_α = ∑_β x_β f_{α - β}` over the support of `x`. -/
noncomputable def laurentMulFamily (x : LaurentLambda L k) (f : Family k (Lambda L)) :
    Family k (Lambda L) :=
  fun α => ∑ β ∈ x.coeff.support, x.coeff β * f (α - β)

omit [Algebra ℚ L] in
/-- On a cone-bounded formal sum the product is the product of the cone ring. -/
theorem laurentMulFamily_coeff (τ : Equiv.Perm (Fin k)) (x : LaurentLambda L k)
    (y : ConeRing k τ (Lambda L)) :
    laurentMulFamily x y.coeff = (laurentToCone τ x * y).coeff := by
  funext α
  rw [ConeRing.coeff_mul_of_subset _ _ α x.coeff.support fun α' hα' =>
    Finset.mem_coe.2 (Finsupp.mem_support_iff.2 hα'.1)]
  rfl

omit [Algebra ℚ L] in
/-- Multiplication by a Laurent polynomial commutes with scalar multiplication of the family. -/
theorem laurentMulFamily_smul (x : LaurentLambda L k) (a : L) (f : Family k (Lambda L)) :
    laurentMulFamily x (a • f) = a • laurentMulFamily x f := by
  funext α
  simp only [laurentMulFamily, Pi.smul_apply, Finset.smul_sum, mul_smul_comm]

omit [Algebra ℚ L] in
/-- Multiplication by a Laurent polynomial distributes over finite sums of families. -/
theorem laurentMulFamily_sum {ι : Type*} (s : Finset ι) (x : LaurentLambda L k)
    (f : ι → Family k (Lambda L)) :
    laurentMulFamily x (∑ i ∈ s, f i) = ∑ i ∈ s, laurentMulFamily x (f i) := by
  funext α
  simp only [laurentMulFamily, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

omit [Algebra ℚ L] in
/-- The product of a Laurent polynomial with the zero family is zero. -/
@[simp] theorem laurentMulFamily_zero (x : LaurentLambda L k) :
    laurentMulFamily x (0 : Family k (Lambda L)) = 0 := by
  funext α
  simp [laurentMulFamily]

omit [Algebra ℚ L] in
/-- Multiplication by the symmetric `Θ_k` commutes with relabelling. -/
theorem laurentMulFamily_kernelDenomLaurent_relabel (q u : L) (τ : Equiv.Perm (Fin k))
    (f : Family k (Lambda L)) :
    laurentMulFamily (kernelDenomLaurent q u k) (relabel τ f) =
      relabel τ (laurentMulFamily (kernelDenomLaurent q u k) f) := by
  funext α
  simp only [laurentMulFamily, relabel_apply]
  have hinv : ∀ β, (kernelDenomLaurent q u k).coeff ((relabelExp τ).symm β) =
      (kernelDenomLaurent q u k).coeff β := fun β => by
    conv_rhs => rw [← AddEquiv.apply_symm_apply (relabelExp τ) β]
    rw [coeff_kernelDenomLaurent_relabelExp]
  refine Finset.sum_nbij' (relabelExp τ).symm (relabelExp τ) (fun β hβ => ?_) (fun β hβ => ?_)
    (fun β _ => AddEquiv.apply_symm_apply _ _) (fun β _ => AddEquiv.symm_apply_apply _ _)
    fun β _ => ?_
  · rw [Finsupp.mem_support_iff, hinv]
    exact Finsupp.mem_support_iff.1 hβ
  · rw [Finsupp.mem_support_iff, coeff_kernelDenomLaurent_relabelExp]
    exact Finsupp.mem_support_iff.1 hβ
  · rw [hinv, map_sub]

/-- The clearing product `L = ∏_{i<j}(1 - z_i/z_j)(1 - qu z_i/z_j)(1 - q z_j/z_i)(1 - u z_j/z_i)`,
a Laurent polynomial over `𝕜`. -/
noncomputable def kernelClearLaurent (q u : L) (k : ℕ) : AddMonoidAlgebra L (Fin k →₀ ℤ) :=
  ∏ i : Fin k, ∏ j ∈ Finset.Ioi i,
    ((1 - AddMonoidAlgebra.single (Finsupp.single i (1 : ℤ) - Finsupp.single j 1) 1) *
        (1 - AddMonoidAlgebra.single 0 (q * u) *
          AddMonoidAlgebra.single (Finsupp.single i (1 : ℤ) - Finsupp.single j 1) 1) *
      ((1 - AddMonoidAlgebra.single 0 q *
          AddMonoidAlgebra.single (Finsupp.single j (1 : ℤ) - Finsupp.single i 1) 1) *
        (1 - AddMonoidAlgebra.single 0 u *
          AddMonoidAlgebra.single (Finsupp.single j (1 : ℤ) - Finsupp.single i 1) 1)))

omit [Algebra ℚ L] in
/-- The coefficientwise map into `Λ` sends the single term `a z^β` to `a z^β` with `a` read in
`Λ`. -/
theorem laurentLambdaMap_single (β : Fin k →₀ ℤ) (a : L) :
    laurentLambdaMap L k (AddMonoidAlgebra.single β a) =
      AddMonoidAlgebra.single β (algebraMap L (Lambda L) a) :=
  AddMonoidAlgebra.ext (by
    ext α
    rw [AddMonoidAlgebra.coeff_mapRingHom, AddMonoidAlgebra.coeff_single,
      AddMonoidAlgebra.coeff_single, Finsupp.single_apply, Finsupp.single_apply]
    split_ifs <;> simp)

omit [Algebra ℚ L] in
/-- In the cone ring of the identity ordering, the clearing product is the right-hand side of
`HJO.Bglx.kernelDenom_mul_kernelExpansion`. -/
theorem laurentToCone_kernelClearLaurent (q u : L) :
    laurentToCone 1 (laurentLambdaMap L k (kernelClearLaurent q u k)) =
      ∏ i : Fin k, ∏ j ∈ Finset.Ioi i,
          ((1 - monoElem 1 (Finsupp.single i (1 : ℤ) - Finsupp.single j 1)) *
              (1 - scalarElem 1 (q * u) *
                monoElem 1 (Finsupp.single i (1 : ℤ) - Finsupp.single j 1)) *
            ((1 - scalarElem 1 q * monoElem 1 (Finsupp.single j (1 : ℤ) - Finsupp.single i 1)) *
              (1 - scalarElem 1 u *
                monoElem 1 (Finsupp.single j (1 : ℤ) - Finsupp.single i 1)))) := by
  have hc : ∀ a : L, AddMonoidAlgebra.single (0 : Fin k →₀ ℤ) (algebraMap L (Lambda L) a) =
      laurentConst L k a := fun a => by rw [laurentConst_apply, MvPolynomial.algebraMap_eq]
  simp only [kernelClearLaurent, map_prod, map_mul (laurentToCone (1 : Equiv.Perm (Fin k))),
    map_mul (laurentLambdaMap L k), map_sub, map_one, laurentLambdaMap_single, hc,
    laurentToCone_laurentConst, laurentToCone_single_one]

omit [Algebra ℚ L] in
/-- The symbol, read in a cone ring, is the image of the Laurent polynomial `Π_c`. -/
theorem symbolElem_eq_laurentToCone (τ : Equiv.Perm (Fin k)) (c : (Fin k → ℕ) →₀ L) :
    symbolElem τ c = laurentToCone τ (laurentLambdaMap L k (dopWordSymbol L k c)) :=
  ConeRing.ext (funext fun α => by
    rw [coeff_symbolElem, coeff_laurentToCone, AddMonoidAlgebra.coeff_mapRingHom]
    rfl)

omit [Algebra ℚ L] in
/-- Relabelling the formal sum of a Laurent polynomial relabels its exponents. -/
theorem relabel_algebraMap_coeff (τ : Equiv.Perm (Fin k)) (X : AddMonoidAlgebra L (Fin k →₀ ℤ)) :
    relabel τ (fun α => algebraMap L (Lambda L) (X.coeff α)) =
      fun α => algebraMap L (Lambda L) (Finsupp.mapDomain (Finsupp.domCongr τ) X.coeff α) := by
  funext α
  rw [relabel_apply]
  congr 1
  conv_rhs => rw [← AddEquiv.apply_symm_apply (relabelExp τ) α]
  exact (Finsupp.mapDomain_apply (Finsupp.domCongr τ).injective _ _).symm

/-- **Clearing the denominator on the symmetrised symbol**: `Θ_k Ξ_c = Sym_k(Π_c L)` in `M_k`, the
right-hand side being the Laurent polynomial `G` representing `Sym_k(Π_c L)`, read as a family. -/
@[hjo "lem_bglx_symbol_sym_clear"]
theorem laurentMulFamily_kernelDenomLaurent_symbolSym (q u : L) (c : (Fin k → ℕ) →₀ L)
    {G : AddMonoidAlgebra L (Fin k →₀ ℤ)}
    (hG : mvRatFuncSymmetrization L k
        (laurentEval L k (dopWordSymbol L k c * kernelClearLaurent q u k)) = laurentEval L k G) :
    laurentMulFamily (kernelDenomLaurent q u k) (symbolSym q u k c) =
      fun α => algebraMap L (Lambda L) (G.coeff α) := by
  set X := dopWordSymbol L k c * kernelClearLaurent q u k with hX
  rw [laurentEval_apply, laurentEval_apply, mvRatFuncSymmetrization_linearCombination] at hG
  have hGc := linearIndependent_zMonomial (K := L) (k := k) hG
  have hP : laurentMulFamily (kernelDenomLaurent q u k)
      (symbolElem 1 c * kernelExpansion q u k).coeff =
        fun α => algebraMap L (Lambda L) (X.coeff α) := by
    rw [laurentMulFamily_coeff 1, laurentToCone_kernelDenomLaurent, mul_left_comm,
      kernelDenom_mul_kernelExpansion, ← laurentToCone_kernelClearLaurent,
      symbolElem_eq_laurentToCone, ← map_mul, ← map_mul, hX]
    funext α
    rw [coeff_laurentToCone, AddMonoidAlgebra.coeff_mapRingHom]
  rw [symbolSym, laurentMulFamily_smul, laurentMulFamily_sum]
  simp only [laurentMulFamily_kernelDenomLaurent_relabel, hP, relabel_algebraMap_coeff]
  funext α
  rw [← hGc, Finsupp.smul_apply, Finsupp.finsetSum_apply, Pi.smul_apply, Finset.sum_apply,
    smul_eq_mul, map_mul, map_sum, Algebra.smul_def]

omit [Algebra ℚ L] in
/-- The kernel denominator, read as a rational function, is fixed by every relabelling. -/
theorem fieldEquivOfAlgEquiv_renameEquiv_kernelDenomRat (q u : L) (σ : Equiv.Perm (Fin k)) :
    IsFractionRing.fieldEquivOfAlgEquiv L (FractionRing (MvPolynomial (Fin k) L))
        (FractionRing (MvPolynomial (Fin k) L)) (MvPolynomial.renameEquiv L σ)
        (kernelDenomRat q u k) = kernelDenomRat q u k := by
  rw [kernelDenomRat, map_prod]
  simp only [map_mul, map_sub, map_one, AlgEquiv.commutes, map_div₀,
    fieldEquivOfAlgEquiv_renameEquiv_zVar]
  refine Finset.prod_equiv (Equiv.prodCongr σ σ) (fun p => ?_) fun _ _ => rfl
  simp [Finset.mem_offDiag]

/-- Symmetrisation is linear over the rational functions fixed by every relabelling. -/
theorem mvRatFuncSymmetrization_mul_of_forall_eq {θ : FractionRing (MvPolynomial (Fin k) L)}
    (hθ : ∀ σ : Equiv.Perm (Fin k), IsFractionRing.fieldEquivOfAlgEquiv L
        (FractionRing (MvPolynomial (Fin k) L)) (FractionRing (MvPolynomial (Fin k) L))
        (MvPolynomial.renameEquiv L σ) θ = θ)
    (x : FractionRing (MvPolynomial (Fin k) L)) :
    mvRatFuncSymmetrization L k (θ * x) = θ * mvRatFuncSymmetrization L k x := by
  simp only [mvRatFuncSymmetrization, LinearMap.smul_apply, LinearMap.sum_apply,
    AlgEquiv.toLinearMap_apply, map_mul, hθ, ← Finset.mul_sum, mul_smul_comm]

omit [Algebra ℚ L] in
/-- The kernel denominator is a nonzero rational function. -/
theorem kernelDenomRat_ne_zero (q u : L) : kernelDenomRat q u k ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ hp =>
    mul_ne_zero (one_sub_C_mul_div_ne_zero q (Finset.mem_offDiag.1 hp).2.2)
      (one_sub_C_mul_div_ne_zero u (Finset.mem_offDiag.1 hp).2.2)

omit [Algebra ℚ L] in
/-- The clearing product, read as a rational function, is `Θ_k Ω_k`. -/
theorem laurentEval_kernelClearLaurent (q u : L) :
    laurentEval L k (kernelClearLaurent q u k) = kernelDenomRat q u k * dopKernelFactor q u k := by
  rw [kernelDenomRat_mul_dopKernelFactor]
  simp only [kernelClearLaurent, map_prod, map_mul, map_sub, map_one, laurentEval_single,
    map_one, one_mul, zMonomial_zero, mul_one, zMonomial_single_sub_single]

/-- **From the expansion to the rational kernel factor**: if the symmetrised symbol `Ξ_c`
vanishes, then `Sym_k(Π_c Ω_k) = 0` in `𝕜(z₁, …, z_k)`. -/
@[hjo "lem_bglx_sym_formal_to_rational"]
theorem mvRatFuncSymmetrization_eq_zero_of_symbolSym_eq_zero (q u : L)
    {c : (Fin k → ℕ) →₀ L} (h : symbolSym q u k c = 0) :
    mvRatFuncSymmetrization L k
      (laurentEval L k (dopWordSymbol L k c) * dopKernelFactor q u k) = 0 := by
  set X := dopWordSymbol L k c * kernelClearLaurent q u k
  set A := (Nat.factorial k : L)⁻¹ • ∑ σ : Equiv.Perm (Fin k),
    Finsupp.mapDomain (Finsupp.domCongr σ) X.coeff
  have hSym : mvRatFuncSymmetrization L k (laurentEval L k X) =
      laurentEval L k (AddMonoidAlgebra.ofCoeff A) := by
    rw [laurentEval_apply, laurentEval_apply, mvRatFuncSymmetrization_linearCombination]
  have hfam := laurentMulFamily_kernelDenomLaurent_symbolSym q u c hSym
  rw [h, laurentMulFamily_zero] at hfam
  have hA : A = 0 := by
    refine Finsupp.ext fun α => ?_
    rw [Finsupp.zero_apply]
    have := congrFun hfam α
    rw [Pi.zero_apply] at this
    exact (algebraMap L (Lambda L)).injective (by rw [map_zero]; exact this.symm)
  have hX0 : mvRatFuncSymmetrization L k (laurentEval L k X) = 0 := by
    rw [hSym, laurentEval_apply, show (AddMonoidAlgebra.ofCoeff A).coeff = A from rfl, hA,
      map_zero]
  rw [map_mul, laurentEval_kernelClearLaurent, mul_left_comm,
    mvRatFuncSymmetrization_mul_of_forall_eq
      (fieldEquivOfAlgEquiv_renameEquiv_kernelDenomRat q u)] at hX0
  exact (mul_eq_zero.mp hX0).resolve_left (kernelDenomRat_ne_zero q u)

end Clear

end HJO.Bglx
