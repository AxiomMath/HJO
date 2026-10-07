/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.ZDeltaDefined
public import HJO.PointwiseSum
public meta import HJO.Attr

/-! # The swapping operator on the merged alphabet respects monomialwise sums

The lemma `HJO.Sym.isZDelta_summableSum`, in full generality: for an *arbitrary* index set `I` and a
family `(F_l)_{l ∈ I}` in `Z^{(k+1)}_d` such that every monomial of the merged alphabet has a
nonzero coefficient in only finitely many `F_l`,

`Δ_m(∑_{l ∈ I}F_l) = ∑_{l ∈ I}Δ_m(F_l)`,

both sums being monomialwise finite. The notion of sum is `HJO.Sym.summableSum` of
`HJO.PointwiseSum`, Mathlib's `finsum` applied one monomial at a time; the `Finset`-indexed
case is `HJO.Sym.isZDelta_sum` of `HJO.CarlssonMellit.ZDeltaDefined`, and it is genuinely
weaker.

## The route

The obstruction the finite case does not meet is the *support transfer*: the right-hand sum has to
be monomialwise finite too, and `Δ_m` is not given by a formula on `P°_{k+1}` — it is the solution
of an equation. What makes the transfer possible is that the solution `HJO.Sym.zDeltaOn` is built
from three operations each of which reads one coefficient of its output off *finitely many*
coefficients of its input: multiplication by a fixed series, a renaming of the letters, and the
division `HJO.Sym.diffQuot`, whose coefficient is by definition a `Finset` sum of coefficients of
the numerator. `HJO.Sym.isSummableFamily_of_coeff_eq_sum` and `HJO.Sym.summableSum_of_coeff_eq_sum`
are that observation made once, and every step below is an instance of it.

So the proof is not the usual one — which decomposes into the two-variable blocks of
`MvPowerSeries.IsHomogeneous.existsUnique_eq_monomialwiseFinsum_monomial_mul` and divides inside
each — but it establishes the same statement, and it needs no block family. The two routes agree
because the solution of the equation is unique (`HJO.Sym.eq_of_isZDelta`).

## Main results

* `HJO.Sym.isSummableFamily_zDeltaOn`, `HJO.Sym.zDeltaOn_summableSum`:
  `HJO.Sym.isZDelta_summableSum` at the written-down solution `HJO.Sym.zDeltaOn` — the images are a
  summable family and their sum is the operator's value at the sum.
* `HJO.Sym.isZDelta_summableSum` as a statement about the relation
  `HJO.Sym.IsZDelta`, which is how `Δ_m` is defined: if each `H_l` solves the equation
  for `F_l`, then `∑_l H_l` solves it for `∑_l F_l`, and the family `(H_l)` is summable.
* `HJO.Sym.summableSum_mem_zGraded`: the sum of a summable family in `Z^{(k+1)}_d` is in
  `Z^{(k+1)}_d`.
* `HJO.Sym.isSummableFamily_of_zSeries`: the hypothesis is about monomials of the
  *merged* alphabet, and on a graded family that is the same condition as monomialwise finiteness
  in the free alphabet, each coefficient there being a single power of `y_{k+1}` times one merged
  coefficient.

## General tools proved here

* `HJO.Sym.isSummableFamily_mul_left`, `HJO.Sym.mul_summableSum`: multiplication by a fixed series.
* `HJO.Sym.isSummableFamily_add`, `HJO.Sym.summableSum_add`.
* `HJO.Sym.isSummableFamily_rename_perm`, `HJO.Sym.rename_perm_summableSum`: relabelling the
  letters along a permutation.
* `HJO.Sym.isSummableFamily_diffQuot`, `HJO.Sym.diffQuot_summableSum`: the division of
  `HJO.CarlssonMellit.DiffDivides`.

## Implementation notes

*The hypothesis is stated at the merged coefficients.* The natural hypothesis is that "for every
monomial in `y_k, x_1, x_2, …` only finitely many `F_l` have a nonzero coefficient at it", which is
`IsSummableFamily fun l => zSeries K k (F l)`. On a family in `Z^{(k+1)}_d` that is equivalent to
`IsSummableFamily F`, the coefficient of a member at a letter-monomial `x^α` being `c y_{k+1}^{b}`
with `b + |α| = d` and `c` one merged coefficient; `HJO.Sym.isSummableFamily_of_zSeries` is the
direction used and `HJO.Sym.isSummableFamily_zSeries` the other. Both forms of the conclusion are
supplied, so no user of the lemma has to redo that translation.

*`Δ_m` is applied as the total map `HJO.Sym.zDeltaOn`, and the relational statement is derived.*
`HJO.Sym.zDeltaOn` is the construction with the graded hypothesis dropped, which is what lets the
support transfer be a statement about a composite of operations rather than about a solution set;
`HJO.Sym.isZDelta_summableSum` then identifies the given solutions `H_l` with its values by
`HJO.Sym.eq_of_isZDelta` and transports the conclusion. Nothing about the construction leaks into
the statement.

*The general tools are stated for `MvPowerSeries σ R` and not for the ring `P°_{k+1}` of this file.*
Each is an identity between coefficients with no grading and no merged alphabet in it, so stating
them at that ring would be stating them at less than their content;
`HJO.Sym.isSummableFamily_of_coeff_eq_sum` and `HJO.Sym.summableSum_of_coeff_eq_sum` are the shape
they all share — an operator each of whose output coefficients is a `Finset`-indexed sum of input
coefficients — and `diffQuot` is the instance that matters, its coefficient being by definition
`HJO.Sym.diffQuotSum`.

*What does not appear: a bound on the merged degrees of the family.* The members all lie in the
*same* `Z^{(k+1)}_d`, as the statement asks, so no such bound is needed; the sum lands in that same
piece by `HJO.Sym.summableSum_mem_zGraded`, whose proof is that `𝕂(y₁,…,y_k)y_{k+1}^b` is an
additive subgroup.

## References

The lemma `HJO.Sym.isZDelta_summableSum`, with `HJO.Sym.zvar`, `HJO.Sym.zGraded`,
`HJO.Sym.IsZDelta`, `MvPowerSeries.IsHomogeneous.existsUnique_eq_monomialwiseFinsum_monomial_mul`
and `HJO.Sym.zDeltaOn`; the summation notions are `HJO.Sym.IsSummableFamily` and
`HJO.Sym.summableSum`. E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, J. Amer.
Math. Soc. **31** (2018) 661--697, Section 4, where the operator is a fraction and the interchange
with an infinite sum is not discussed.
-/

@[expose] public section

namespace HJO.Sym

/-! ### Summable families: a common criterion -/

section General

variable {I σ R : Type*} [CommSemiring R] {f g : I → MvPowerSeries σ R}

/-- A summable family has, for any *finite* set of monomials, one finite set of indices carrying
every member with a nonzero coefficient at any of them. -/
theorem IsSummableFamily.exists_finset_finset (hf : IsSummableFamily f) (s : Finset (σ →₀ ℕ)) :
    ∃ t : Finset I, ∀ e ∈ s, ∀ l, MvPowerSeries.coeff e (f l) ≠ 0 → l ∈ t := by
  classical
  choose t ht using fun e => hf.exists_finset e
  exact ⟨s.biUnion t, fun e he l hl => Finset.mem_biUnion.2 ⟨e, he, ht e l hl⟩⟩

/-- **An operator each of whose output coefficients is a `Finset`-indexed linear combination of
input coefficients carries a summable family to a summable family.** The indices reaching a
monomial after the operator are among those reaching one of the finitely many monomials the
combination runs over.
This is the shape shared by multiplication by a fixed series, a relabelling of the letters and the
division `HJO.Sym.diffQuot`. -/
theorem isSummableFamily_of_coeff_eq_sum {ι : Type*} {Φ : MvPowerSeries σ R → MvPowerSeries σ R}
    {idx : (σ →₀ ℕ) → Finset ι} {mon : (σ →₀ ℕ) → ι → σ →₀ ℕ} {c : (σ →₀ ℕ) → ι → R}
    (hΦ : ∀ (G : MvPowerSeries σ R) (e : σ →₀ ℕ), MvPowerSeries.coeff e (Φ G)
      = ∑ p ∈ idx e, c e p * MvPowerSeries.coeff (mon e p) G)
    (hf : IsSummableFamily f) : IsSummableFamily fun l => Φ (f l) := by
  classical
  refine pointwiseFinite_of_forall_exists_finset fun e => ?_
  obtain ⟨t, ht⟩ := hf.exists_finset_finset ((idx e).image (mon e))
  refine ⟨t, fun l hl => ?_⟩
  by_contra hlt
  refine hl ?_
  change MvPowerSeries.coeff e (Φ (f l)) = 0
  rw [hΦ]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hz : MvPowerSeries.coeff (mon e p) (f l) = 0 := by
    by_contra hne
    exact hlt (ht (mon e p) (Finset.mem_image.2 ⟨p, hp, rfl⟩) l hne)
  rw [hz, mul_zero]

/-- **Such an operator commutes with the sum of a summable family.** Both sides are, at each
monomial, the same double `Finset` sum — over the monomials the operator reads and over the indices
that reach them. -/
theorem summableSum_of_coeff_eq_sum {ι : Type*} {Φ : MvPowerSeries σ R → MvPowerSeries σ R}
    {idx : (σ →₀ ℕ) → Finset ι} {mon : (σ →₀ ℕ) → ι → σ →₀ ℕ} {c : (σ →₀ ℕ) → ι → R}
    (hΦ : ∀ (G : MvPowerSeries σ R) (e : σ →₀ ℕ), MvPowerSeries.coeff e (Φ G)
      = ∑ p ∈ idx e, c e p * MvPowerSeries.coeff (mon e p) G)
    (hf : IsSummableFamily f) : Φ (summableSum f) = summableSum fun l => Φ (f l) := by
  classical
  refine MvPowerSeries.ext fun e => ?_
  obtain ⟨t, ht⟩ := hf.exists_finset_finset ((idx e).image (mon e))
  have hmon : ∀ p ∈ idx e, c e p * MvPowerSeries.coeff (mon e p) (summableSum f)
      = ∑ l ∈ t, c e p * MvPowerSeries.coeff (mon e p) (f l) := by
    intro p hp
    rw [coeff_summableSum_eq_sum
      (fun l hl => ht (mon e p) (Finset.mem_image.2 ⟨p, hp, rfl⟩) l hl), Finset.mul_sum]
  have hΦt : ∀ l, MvPowerSeries.coeff e (Φ (f l)) ≠ 0 → l ∈ t := by
    intro l hl
    by_contra hlt
    refine hl ?_
    rw [hΦ]
    refine Finset.sum_eq_zero fun p hp => ?_
    have hz : MvPowerSeries.coeff (mon e p) (f l) = 0 := by
      by_contra hne
      exact hlt (ht (mon e p) (Finset.mem_image.2 ⟨p, hp, rfl⟩) l hne)
    rw [hz, mul_zero]
  rw [hΦ, Finset.sum_congr rfl hmon, coeff_summableSum_eq_sum hΦt, Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => (hΦ (f l) e).symm

/-! ### Addition -/

/-- The termwise sum of two summable families is summable. -/
theorem isSummableFamily_add (hf : IsSummableFamily f) (hg : IsSummableFamily g) :
    IsSummableFamily fun l => f l + g l := by
  classical
  refine pointwiseFinite_of_forall_exists_finset fun e => ?_
  obtain ⟨t, ht⟩ := hf.exists_finset e
  obtain ⟨t', ht'⟩ := hg.exists_finset e
  refine ⟨t ∪ t', fun l hl => ?_⟩
  by_cases hfl : MvPowerSeries.coeff e (f l) = 0
  · refine Finset.mem_union_right _ (ht' l fun hgl => hl ?_)
    change MvPowerSeries.coeff e (f l + g l) = 0
    rw [map_add, hfl, hgl, add_zero]
  · exact Finset.mem_union_left _ (ht l hfl)

/-- The sums of two summable families add termwise. -/
theorem summableSum_add (hf : IsSummableFamily f) (hg : IsSummableFamily g) :
    summableSum f + summableSum g = summableSum fun l => f l + g l := by
  classical
  refine MvPowerSeries.ext fun e => ?_
  obtain ⟨t, ht⟩ := hf.exists_finset e
  obtain ⟨t', ht'⟩ := hg.exists_finset e
  have h1 : ∀ l, MvPowerSeries.coeff e (f l) ≠ 0 → l ∈ t ∪ t' :=
    fun l hl => Finset.mem_union_left _ (ht l hl)
  have h2 : ∀ l, MvPowerSeries.coeff e (g l) ≠ 0 → l ∈ t ∪ t' :=
    fun l hl => Finset.mem_union_right _ (ht' l hl)
  have h3 : ∀ l, MvPowerSeries.coeff e (f l + g l) ≠ 0 → l ∈ t ∪ t' := by
    intro l hl
    by_cases hfl : MvPowerSeries.coeff e (f l) = 0
    · exact h2 l fun hgl => hl (by rw [map_add, hfl, hgl, add_zero])
    · exact h1 l hfl
  rw [map_add, coeff_summableSum_eq_sum h1, coeff_summableSum_eq_sum h2,
    coeff_summableSum_eq_sum h3, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun l _ => (map_add (MvPowerSeries.coeff e) (f l) (g l)).symm

/-! ### Multiplication by a fixed series -/

/-- The coefficient of a product, in the shape `HJO.Sym.isSummableFamily_of_coeff_eq_sum` asks for:
a `Finset`-indexed linear combination of the coefficients of the right-hand factor. -/
theorem coeff_mul_eq_sum [DecidableEq σ] (p G : MvPowerSeries σ R) (e : σ →₀ ℕ) :
    MvPowerSeries.coeff e (p * G)
      = ∑ x ∈ Finset.antidiagonal e,
          MvPowerSeries.coeff x.1 p * MvPowerSeries.coeff x.2 G :=
  MvPowerSeries.coeff_mul e p G

/-- Multiplying every member of a summable family by one fixed series leaves it summable: the
coefficient of a product at a monomial is a `Finset` combination of the factor's coefficients over
the finitely many factorisations of that monomial. -/
theorem isSummableFamily_mul_left (hf : IsSummableFamily f) (p : MvPowerSeries σ R) :
    IsSummableFamily fun l => p * f l := by
  classical
  exact isSummableFamily_of_coeff_eq_sum (idx := fun e => Finset.antidiagonal e)
    (mon := fun _ x => x.2) (c := fun _ x => MvPowerSeries.coeff x.1 p)
    (Φ := fun G => p * G) (coeff_mul_eq_sum p) hf

/-- Multiplication by a fixed series commutes with the sum of a summable family. -/
theorem mul_summableSum (hf : IsSummableFamily f) (p : MvPowerSeries σ R) :
    p * summableSum f = summableSum fun l => p * f l := by
  classical
  exact summableSum_of_coeff_eq_sum (idx := fun e => Finset.antidiagonal e)
    (mon := fun _ x => x.2) (c := fun _ x => MvPowerSeries.coeff x.1 p)
    (Φ := fun G => p * G) (coeff_mul_eq_sum p) hf

/-! ### Relabelling the letters -/

/-- The coefficient of a relabelled series, in the shape the criterion asks for. -/
theorem coeff_rename_perm_eq_sum (ρ : Equiv.Perm σ) (G : MvPowerSeries σ R) (e : σ →₀ ℕ) :
    MvPowerSeries.coeff e (MvPowerSeries.rename (ρ : σ → σ) G)
      = ∑ _p ∈ ({()} : Finset Unit),
          (1 : R) * MvPowerSeries.coeff (Finsupp.equivMapDomain ρ.symm e) G := by
  rw [Finset.sum_singleton, one_mul, coeff_rename_perm ρ G e]

/-- Relabelling the letters along a permutation leaves a summable family summable: it reads one
coefficient off one coefficient. -/
theorem isSummableFamily_rename_perm (hf : IsSummableFamily f) (ρ : Equiv.Perm σ) :
    IsSummableFamily fun l => MvPowerSeries.rename (ρ : σ → σ) (f l) :=
  isSummableFamily_of_coeff_eq_sum (idx := fun _ => ({()} : Finset Unit))
    (mon := fun e _ => Finsupp.equivMapDomain ρ.symm e) (c := fun _ _ => (1 : R))
    (Φ := fun G => MvPowerSeries.rename (ρ : σ → σ) G) (coeff_rename_perm_eq_sum ρ) hf

/-- Relabelling the letters along a permutation commutes with the sum of a summable family. -/
theorem rename_perm_summableSum (hf : IsSummableFamily f) (ρ : Equiv.Perm σ) :
    MvPowerSeries.rename (ρ : σ → σ) (summableSum f)
      = summableSum fun l => MvPowerSeries.rename (ρ : σ → σ) (f l) :=
  summableSum_of_coeff_eq_sum (idx := fun _ => ({()} : Finset Unit))
    (mon := fun e _ => Finsupp.equivMapDomain ρ.symm e) (c := fun _ _ => (1 : R))
    (Φ := fun G => MvPowerSeries.rename (ρ : σ → σ) G) (coeff_rename_perm_eq_sum ρ) hf

/-! ### The division by a difference of two letters -/

section Diff

variable {A : Type*} [CommRing A] {fA : I → MvPowerSeries σ A}

/-- The coefficients of `HJO.Sym.diffQuot`, as the `Finset` sum of coefficients of the numerator
that they are by definition, in the shape the criterion asks for. -/
theorem coeff_diffQuot_eq_sum (i j : σ) (G : MvPowerSeries σ A) (e : σ →₀ ℕ) :
    MvPowerSeries.coeff e (diffQuot i j G)
      = ∑ p ∈ Finset.antidiagonal (e i), (1 : A) * MvPowerSeries.coeff
          (eraseTwo i j e + Finsupp.single i p.1 + Finsupp.single j (e j + 1 + p.2)) G := by
  rw [show MvPowerSeries.coeff e (diffQuot i j G)
    = diffQuotSum i j G (eraseTwo i j e) (e i) (e j + 1) from rfl, diffQuotSum_apply]
  exact Finset.sum_congr rfl fun p _ => (one_mul _).symm

/-- The division by a difference of two letters leaves a summable family summable. -/
theorem isSummableFamily_diffQuot (hf : IsSummableFamily fA) (i j : σ) :
    IsSummableFamily fun l => diffQuot i j (fA l) :=
  isSummableFamily_of_coeff_eq_sum (idx := fun e => Finset.antidiagonal (e i))
    (mon := fun e p => eraseTwo i j e + Finsupp.single i p.1 + Finsupp.single j (e j + 1 + p.2))
    (c := fun _ _ => (1 : A)) (Φ := fun G => diffQuot i j G) (coeff_diffQuot_eq_sum i j) hf

/-- The division by a difference of two letters commutes with the sum of a summable family. This is
the step reached by dividing inside each two-variable block. -/
theorem diffQuot_summableSum (hf : IsSummableFamily fA) (i j : σ) :
    diffQuot i j (summableSum fA) = summableSum fun l => diffQuot i j (fA l) :=
  summableSum_of_coeff_eq_sum (idx := fun e => Finset.antidiagonal (e i))
    (mon := fun e p => eraseTwo i j e + Finsupp.single i p.1 + Finsupp.single j (e j + 1 + p.2))
    (c := fun _ _ => (1 : A)) (Φ := fun G => diffQuot i j G) (coeff_diffQuot_eq_sum i j) hf

end Diff

end General

/-! ### Summable families in a graded piece -/

variable {K : Type*} [CommRing K] [IsDomain K] {k d : ℕ} {I : Type*}
  {F : I → AuxAlphabetSeriesFrac K (k + 1)}

/-- **The sum of a summable family in `Z^{(k+1)}_d` lies in `Z^{(k+1)}_d`**: each coefficient of the
sum is a finite sum of multiples of one and the same power of `y_{k+1}`, and
`HJO.Sym.auxFracYPow` is an additive subgroup; above the degree every summand vanishes. This is the
statement that a monomialwise finite sum lies in `Z^{(k)}_d` by `HJO.Sym.zGraded`. -/
theorem summableSum_mem_zGraded (hF : ∀ l, F l ∈ zGraded K k d) (hsum : IsSummableFamily F) :
    summableSum F ∈ zGraded K k d := by
  classical
  refine ⟨fun α b hb => ?_, fun α hα => ?_⟩
  · obtain ⟨t, ht⟩ := hsum.exists_finset α
    rw [← mem_auxFracYPow, coeff_summableSum_eq_sum ht]
    exact sum_mem fun l _ => mem_auxFracYPow.2 (exists_coeff_eq_of_mem_zGraded (hF l) α hb)
  · rw [coeff_summableSum_eq_sum (s := (∅ : Finset I))
      fun l hl => absurd (coeff_eq_zero_of_mem_zGraded (hF l) hα) hl, Finset.sum_empty]

/-- Monomialwise finiteness in the merged alphabet follows from monomialwise finiteness in the free
alphabet, with no hypothesis: a merged coefficient is read off the coefficient at the corresponding
letter-monomial, and `HJO.Sym.yFracCoeff` kills `0`. -/
theorem isSummableFamily_zSeries (hsum : IsSummableFamily F) :
    IsSummableFamily fun l => zSeries K k (F l) := by
  classical
  refine pointwiseFinite_of_forall_exists_finset fun ν => ?_
  obtain ⟨t, ht⟩ := hsum.exists_finset ν.some
  refine ⟨t, fun l hl => ht l fun h => hl ?_⟩
  change MvPowerSeries.coeff ν (zSeries K k (F l)) = 0
  rw [coeff_zSeries, zCoeff, h, yFracCoeff_zero]

/-- **The hypothesis implies monomialwise finiteness in the free alphabet**, on a family
in a graded piece: the coefficient of a member at the letter-monomial `x^α` is
`c y_{k+1}^{b}` for the `b` with `b + |α| = d` and `c` the merged coefficient at
`y_{k+1}^{b}x^α`, so it vanishes as soon as that merged coefficient does. Above the degree the
coefficient vanishes outright. -/
theorem isSummableFamily_of_zSeries (hF : ∀ l, F l ∈ zGraded K k d)
    (hsum : IsSummableFamily fun l => zSeries K k (F l)) : IsSummableFamily F := by
  classical
  refine pointwiseFinite_of_forall_exists_finset fun α => ?_
  rcases lt_or_ge d (Finsupp.degree α) with hα | hα
  · exact ⟨∅, fun l hl => absurd (coeff_eq_zero_of_mem_zGraded (hF l) hα) hl⟩
  · obtain ⟨t, ht⟩ := hsum.exists_finset (α.optionElim (d - Finsupp.degree α))
    refine ⟨t, fun l hl => ht l fun h => hl ?_⟩
    change MvPowerSeries.coeff α (F l) = 0
    obtain ⟨c, hc⟩ := exists_coeff_eq_of_mem_zGraded (hF l) α
      (b := d - Finsupp.degree α) (by omega)
    have hcz : c = 0 := by
      have h' : zCoeff K k (F l) (α.optionElim (d - Finsupp.degree α)) = 0 := h
      rw [zCoeff, Finsupp.some_optionElim, Finsupp.optionElim_apply_none, hc,
        yFracCoeff_mul_yFrac_pow, ite_eq_left rfl] at h'
      exact h'
    rw [hc, hcz, map_zero, zero_mul]

/-! ### The merged coefficients of a monomialwise sum -/

/-- **The merged coefficients of a monomialwise sum are the sums of the merged coefficients**, on a
family in a graded piece. The extraction `HJO.Sym.yFracCoeff` is additive on the coefficients that
are polynomial in `y_{k+1}`, which every coefficient of a member of `Z^{(k+1)}_d` is. -/
theorem zSeries_summableSum (hF : ∀ l, F l ∈ zGraded K k d) (hsum : IsSummableFamily F) :
    zSeries K k (summableSum F) = summableSum fun l => zSeries K k (F l) := by
  classical
  refine MvPowerSeries.ext fun ν => ?_
  obtain ⟨t, ht⟩ := hsum.exists_finset ν.some
  have hzt : ∀ l, MvPowerSeries.coeff ν (zSeries K k (F l)) ≠ 0 → l ∈ t := by
    intro l hl
    refine ht l fun h => hl ?_
    rw [coeff_zSeries, zCoeff, h, yFracCoeff_zero]
  rw [coeff_zSeries, zCoeff, coeff_summableSum_eq_sum ht, coeff_summableSum_eq_sum hzt,
    yFracCoeff_sum_of_mem_range
      fun l _ => coeff_mem_range_yFracEval_of_mem_zGraded (hF l) ν.some]
  exact Finset.sum_congr rfl fun l _ => rfl

/-! ### The prescribed-coefficient construction respects monomialwise sums -/

/-- Prescribing the merged coefficients carries a summable family to a summable family: a
coefficient of `HJO.Sym.zOfSeries` is one prescribed coefficient, scaled. -/
theorem isSummableFamily_zOfSeries {Q : I → MvPowerSeries (Option ℕ) (AuxFrac K k)}
    (hQ : IsSummableFamily Q) : IsSummableFamily fun l => zOfSeries K k d (Q l) := by
  classical
  refine pointwiseFinite_of_forall_exists_finset fun α => ?_
  by_cases hα : Finsupp.degree α ≤ d
  · obtain ⟨t, ht⟩ := hQ.exists_finset (α.optionElim (d - Finsupp.degree α))
    refine ⟨t, fun l hl => ht l fun h => hl ?_⟩
    change MvPowerSeries.coeff α (zOfSeries K k d (Q l)) = 0
    rw [coeff_zOfSeries, ite_eq_left hα, h, map_zero, zero_mul]
  · refine ⟨∅, fun l hl => absurd ?_ hl⟩
    change MvPowerSeries.coeff α (zOfSeries K k d (Q l)) = 0
    rw [coeff_zOfSeries, ite_eq_right hα]

/-- Prescribing the merged coefficients commutes with monomialwise sums. -/
theorem zOfSeries_summableSum {Q : I → MvPowerSeries (Option ℕ) (AuxFrac K k)}
    (hQ : IsSummableFamily Q) :
    zOfSeries K k d (summableSum Q) = summableSum fun l => zOfSeries K k d (Q l) := by
  classical
  refine MvPowerSeries.ext fun α => ?_
  by_cases hα : Finsupp.degree α ≤ d
  · obtain ⟨t, ht⟩ := hQ.exists_finset (α.optionElim (d - Finsupp.degree α))
    have hzt : ∀ l, MvPowerSeries.coeff α (zOfSeries K k d (Q l)) ≠ 0 → l ∈ t := by
      intro l hl
      refine ht l fun h => hl ?_
      rw [coeff_zOfSeries, ite_eq_left hα, h, map_zero, zero_mul]
    rw [coeff_zOfSeries, ite_eq_left hα, coeff_summableSum_eq_sum ht,
      coeff_summableSum_eq_sum hzt, map_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun l _ => by rw [coeff_zOfSeries, ite_eq_left hα]
  · have hz : ∀ l, MvPowerSeries.coeff α (zOfSeries K k d (Q l)) = 0 := fun l => by
      rw [coeff_zOfSeries, ite_eq_right hα]
    rw [coeff_zOfSeries, ite_eq_right hα,
      coeff_summableSum_eq_sum (s := (∅ : Finset I)) fun l hl => absurd (hz l) hl,
      Finset.sum_empty]

/-! ### The numerator at the merged coefficients -/

/-- **The numerator of `HJO.Sym.IsZDelta`, read at the merged coefficients**: the expression
`HJO.Sym.zSeries_zdeltaNum` computes, with the two moved letters as power-series variables and `ŝ_m`
as a relabelling. Naming it is what lets the three commutations below be applied to it one at a
time. -/
noncomputable def zdeltaNumSeries (q : K) (r : ℕ) (Q : MvPowerSeries (Option ℕ) (AuxFrac K k)) :
    MvPowerSeries (Option ℕ) (AuxFrac K k) :=
  (MvPowerSeries.C (scalarFrac K q) - 1) * MvPowerSeries.X (zLetter (r + 1)) * Q
    + (MvPowerSeries.X (zLetter (r + 1))
        - MvPowerSeries.C (scalarFrac K q) * MvPowerSeries.X (zLetter r))
      * MvPowerSeries.rename (zSwapEquiv r : Option ℕ → Option ℕ) Q

/-- `HJO.Sym.zSeries_zdeltaNum` in the named form. -/
theorem zSeries_zdeltaNum_eq {G : AuxAlphabetSeriesFrac K (k + 1)} (q : K) (r : ℕ)
    (hG : G ∈ zRing K k) :
    zSeries K k (zdeltaNum q r G) = zdeltaNumSeries q r (zSeries K k G) :=
  zSeries_zdeltaNum q r hG

variable {Q : I → MvPowerSeries (Option ℕ) (AuxFrac K k)}

omit [IsDomain K] in
/-- The numerator carries a summable family to a summable family: it is two multiplications by fixed
series, one relabelling and one addition. -/
theorem isSummableFamily_zdeltaNumSeries (hQ : IsSummableFamily Q) (q : K) (r : ℕ) :
    IsSummableFamily fun l => zdeltaNumSeries q r (Q l) :=
  isSummableFamily_add (isSummableFamily_mul_left hQ _)
    (isSummableFamily_mul_left (isSummableFamily_rename_perm hQ (zSwapEquiv r)) _)

omit [IsDomain K] in
/-- The numerator commutes with monomialwise sums. -/
theorem zdeltaNumSeries_summableSum (hQ : IsSummableFamily Q) (q : K) (r : ℕ) :
    zdeltaNumSeries q r (summableSum Q) = summableSum fun l => zdeltaNumSeries q r (Q l) := by
  rw [zdeltaNumSeries, mul_summableSum hQ, rename_perm_summableSum hQ,
    mul_summableSum (isSummableFamily_rename_perm hQ (zSwapEquiv r)),
    summableSum_add (isSummableFamily_mul_left hQ _)
      (isSummableFamily_mul_left (isSummableFamily_rename_perm hQ (zSwapEquiv r)) _)]
  rfl

/-! ### The swapping operator respects monomialwise sums -/

variable {q : K} {r : ℕ} {H : I → AuxAlphabetSeriesFrac K (k + 1)}

/-- The merged coefficients of the numerators of a graded family form a summable family. -/
theorem isSummableFamily_zSeries_zdeltaNum (hF : ∀ l, F l ∈ zGraded K k d)
    (hsum : IsSummableFamily fun l => zSeries K k (F l)) (q : K) (r : ℕ) :
    IsSummableFamily fun l => zSeries K k (zdeltaNum q r (F l)) := by
  have hfam : (fun l => zSeries K k (zdeltaNum q r (F l)))
      = fun l => zdeltaNumSeries q r (zSeries K k (F l)) :=
    funext fun l => zSeries_zdeltaNum_eq q r (zGraded_subset_zRing K k d (hF l))
  rw [hfam]
  exact isSummableFamily_zdeltaNumSeries hsum q r

/-- **The images under `Δ_m` of a summable family in `Z^{(k+1)}_d` are a summable family.** This is
the half of `HJO.Sym.isZDelta_summableSum` the `Finset` case cannot see: `Δ_m` is built from
multiplication by fixed series, a relabelling of the letters and the division `HJO.Sym.diffQuot`,
each of which reads one output coefficient off finitely many input coefficients, so the indices
reaching a monomial afterwards are among those reaching finitely many monomials before. -/
theorem isSummableFamily_zDeltaOn (hF : ∀ l, F l ∈ zGraded K k d)
    (hsum : IsSummableFamily fun l => zSeries K k (F l)) (q : K) (r : ℕ) :
    IsSummableFamily fun l => zDeltaOn K k q d r (F l) :=
  isSummableFamily_zOfSeries
    (isSummableFamily_diffQuot (isSummableFamily_zSeries_zdeltaNum hF hsum q r)
      (zLetter r) (zLetter (r + 1)))

/-- **`Δ_m` of a monomialwise sum is the monomialwise sum of the `Δ_m`**, at the written-down
solution `HJO.Sym.zDeltaOn`. Each of the three operations the solution is built from commutes with a
monomialwise sum, by `HJO.Sym.summableSum_of_coeff_eq_sum`. -/
theorem zDeltaOn_summableSum (hF : ∀ l, F l ∈ zGraded K k d)
    (hsum : IsSummableFamily fun l => zSeries K k (F l)) (q : K) (r : ℕ) :
    zDeltaOn K k q d r (summableSum F) = summableSum fun l => zDeltaOn K k q d r (F l) := by
  have hFsum : IsSummableFamily F := isSummableFamily_of_zSeries hF hsum
  have hmem : summableSum F ∈ zGraded K k d := summableSum_mem_zGraded hF hFsum
  have hnum : IsSummableFamily fun l => zSeries K k (zdeltaNum q r (F l)) :=
    isSummableFamily_zSeries_zdeltaNum hF hsum q r
  have hfam : (fun l => zdeltaNumSeries q r (zSeries K k (F l)))
      = fun l => zSeries K k (zdeltaNum q r (F l)) :=
    funext fun l => (zSeries_zdeltaNum_eq q r (zGraded_subset_zRing K k d (hF l))).symm
  have h1 : zSeries K k (zdeltaNum q r (summableSum F))
      = summableSum fun l => zSeries K k (zdeltaNum q r (F l)) := by
    rw [zSeries_zdeltaNum_eq q r (zGraded_subset_zRing K k d hmem),
      zSeries_summableSum hF hFsum, zdeltaNumSeries_summableSum hsum q r, hfam]
  rw [zDeltaOn, h1, diffQuot_summableSum hnum (zLetter r) (zLetter (r + 1)),
    zOfSeries_summableSum
      (isSummableFamily_diffQuot hnum (zLetter r) (zLetter (r + 1)))]
  rfl

/-- **The swapping operator on the merged alphabet respects monomialwise sums**, in the generality
`HJO.Sym.isZDelta_summableSum` states it: for a family `(F_l)_{l ∈ I}` in `Z^{(k+1)}_d` indexed by
an arbitrary set, with only finitely many members having a nonzero coefficient at any given monomial
of the merged alphabet, and solutions `H_l` of the equation of `HJO.Sym.IsZDelta` for each `F_l`,
the family `(H_l)` is monomialwise finite too and `∑_l H_l` solves the equation for `∑_l F_l`.

Together with `HJO.Sym.eq_of_isZDelta` that is the identity `Δ_m(∑_l F_l) = ∑_l Δ_m(F_l)`, and
`HJO.Sym.zDeltaOn_summableSum` is the same identity written at values. The `Finset`-indexed case is
`HJO.Sym.isZDelta_sum`. -/
@[hjo "lem_cm_zdelta_sums"]
theorem isZDelta_summableSum (hF : ∀ l, F l ∈ zGraded K k d)
    (hsum : IsSummableFamily fun l => zSeries K k (F l))
    (h : ∀ l, IsZDelta q r (F l) (H l)) :
    IsSummableFamily H ∧ (IsSummableFamily fun l => zSeries K k (H l))
      ∧ IsZDelta q r (summableSum F) (summableSum H) := by
  have hH : H = fun l => zDeltaOn K k q d r (F l) :=
    funext fun l => eq_of_isZDelta (h l) (isZDelta_zDeltaOn q r (hF l))
  subst hH
  refine ⟨isSummableFamily_zDeltaOn hF hsum q r,
    isSummableFamily_zSeries (isSummableFamily_zDeltaOn hF hsum q r), ?_⟩
  rw [← zDeltaOn_summableSum hF hsum q r]
  exact isZDelta_zDeltaOn q r (summableSum_mem_zGraded hF (isSummableFamily_of_zSeries hF hsum))

/-- **The monomialwise sum of the images lies in `Z^{(k+1)}_d`**, so that the right-hand side of
`HJO.Sym.isZDelta_summableSum` lies where the operators `Δ_m` are defined and the identity can
be iterated without leaving the graded piece. -/
@[hjo "lem_cm_zdelta_sums"]
theorem summableSum_zDeltaOn_mem_zGraded (hF : ∀ l, F l ∈ zGraded K k d)
    (hsum : IsSummableFamily fun l => zSeries K k (F l)) (q : K) (r : ℕ) :
    (summableSum fun l => zDeltaOn K k q d r (F l)) ∈ zGraded K k d :=
  summableSum_mem_zGraded (fun l => zDeltaOn_mem_zGraded q d r (F l))
    (isSummableFamily_zDeltaOn hF hsum q r)

end HJO.Sym
