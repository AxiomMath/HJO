/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Classical.MonomialBasis
public import HJO.Classical.PartitionDominance
public meta import HJO.Attr

/-! # The realised power-sum monomials are triangular, hence independent

The independence half of `HJO.Sym.exists_basis_iota_pmonomial`: for a realisation `ι` and `d ≥ 0`
the family `(ι(p_λ))`, indexed by the partitions `λ` of `d`, is `𝕜`-linearly independent.

## Main definitions

* `HJO.Sym.powerSumSeries`, `HJO.Sym.tupleCount`: the `ℕ`-valued avatars of `ι(p_r)` and of
  `ι(p_λ)`, whose coefficients literally count the tuples of letters producing a monomial.
* `HJO.Sym.letterExp`: the exponent vector of a letter assignment.
* `HJO.Sym.degHom`: the total degree of an exponent vector, as an additive homomorphism.

## Main statements

* `HJO.Sym.coeff_letterExp_tupleCount_ne_zero` and
  `HJO.Sym.exists_letterExp_of_coeff_tupleCount_ne_zero`: a coefficient of `ι(p_λ)` is nonzero
  exactly at the exponent vectors of a letter assignment.
* `HJO.Sym.coeff_partitionExponent_iota_pmonomial_ne_zero`: the diagonal coefficient, `R_λ ≠ 0`.
* `HJO.Sym.dominates_of_coeff_iota_pmonomial_ne_zero`: the triangularity, `μ ⪰ λ`.
* `HJO.Sym.degHom_of_coeff_iota_pmonomial_ne_zero`: `ι(p_λ)` lives in total degree `d`.
* `HJO.Sym.linearIndependent_iota_pmonomial`: the independence half of
  `HJO.Sym.exists_basis_iota_pmonomial`.

## Implementation notes

**The counting is done over `ℕ` and transported, and that is not decoration.** The coefficient of
`x^α` in `ι(p_λ)` is the *number* of tuples `(i_1, …, i_m)` of letters with
`α_i = ∑_{j : i_j = i}λ_j`, and the argument that it is nonzero is "a sum of nonnegative terms is at
least one of them" — which is false in an arbitrary commutative ring, where the terms could cancel.
So `tupleCount` is the same product formed in `MvPowerSeries ℕ ℕ`, `map_tupleCount` identifies its
image under `ℕ → K` with `ι(p_λ)`, and the positivity happens over `ℕ`. `CharZero K` is then what
carries it across; it holds for the base field `𝕜 = ℚ(q,u)`, and some such hypothesis is necessary,
since a multiplicity factorial can vanish in positive characteristic.

**The triangularity is `HJO.Sym.dominates_of_blockSums` applied to the letter assignment.** A letter
assignment `g` on the positions of the parts of `λ` has, by construction, nonempty fibres over
exactly the letters it uses, which for `α = x^μ` are exactly `0, …, #μ.parts - 1`; that is why
`HJO.Sym.dominates_of_blockSums`'s labelling presentation applies directly with `r = #μ.parts`, and
why no relabelling of blocks is needed.

Nothing here needs the symmetry of `ι(p_λ)` in the letters. The route to
`HJO.Sym.exists_basis_iota_pmonomial` goes through `HJO.Sym.exists_triangular_msymm`, whose
expansion into the `m_μ` does need it; the *independence*, which is what
`HJO.Sym.algebraicIndependent_realisation_powerSum` and `HJO.Sym.realisation_injective` use,
needs only the two coefficient facts above read at the lexicographically least index of a vanishing
combination.

## References

This file formalises the independence half of `HJO.Sym.exists_basis_iota_pmonomial`; the
spanning half goes through `HJO.Sym.exists_triangular_msymm`.
-/

@[expose] public section

open Finset

namespace HJO.Sym

/-! ### The total degree of an exponent vector -/

/-- The total degree of an exponent vector, as an additive homomorphism so that it passes through
sums without ceremony. -/
noncomputable def degHom : (ℕ →₀ ℕ) →+ ℕ :=
  Finsupp.liftAddHom fun _ => AddMonoidHom.id ℕ

@[simp]
theorem degHom_single (i r : ℕ) : degHom (Finsupp.single i r) = r := by
  rw [degHom, Finsupp.liftAddHom_apply_single]
  rfl

/-! ### The `ℕ`-valued avatar of a realised power sum -/

/-- **The `ℕ`-valued power-sum series** `∑_i x_i^r`: the coefficient is `1` at each `x_i^r` and `0`
elsewhere, which is what `HJO.Sym.IsRealisation` prescribes for `ι(p_r)`. -/
noncomputable def powerSumSeries (r : ℕ) : MvPowerSeries ℕ ℕ :=
  Set.indicator {α : ℕ →₀ ℕ | ∃ i, α = Finsupp.single i r} 1

theorem coeff_powerSumSeries_of_mem {r : ℕ} {α : ℕ →₀ ℕ} (h : ∃ i, α = Finsupp.single i r) :
    MvPowerSeries.coeff α (powerSumSeries r) = 1 :=
  Set.indicator_of_mem h 1

theorem coeff_powerSumSeries_of_notMem {r : ℕ} {α : ℕ →₀ ℕ}
    (h : ¬∃ i, α = Finsupp.single i r) : MvPowerSeries.coeff α (powerSumSeries r) = 0 :=
  Set.indicator_of_notMem h 1

/-- **The tuple-counting series of a list of parts**: the `ℕ`-valued product `∏_j(∑_i x_i^{L_j})`,
whose coefficient at `x^α` is the number of letter assignments producing `x^α`. -/
noncomputable def tupleCount (L : List ℕ) : MvPowerSeries ℕ ℕ :=
  (L.map powerSumSeries).prod

@[simp]
theorem tupleCount_nil : tupleCount [] = 1 := rfl

theorem tupleCount_cons (r : ℕ) (L : List ℕ) :
    tupleCount (r :: L) = powerSumSeries r * tupleCount L := by
  simp only [tupleCount, List.map_cons, List.prod_cons]

/-! ### Letter assignments and their exponent vectors -/

/-- **The exponent vector of a letter assignment**: the assignment `g` sends the position `j`, which
carries the part `L_j`, to the letter `g j`, and the resulting monomial is `∏_j x_{g j}^{L_j}`. -/
noncomputable def letterExp (L : List ℕ) (g : ℕ → ℕ) : ℕ →₀ ℕ :=
  ∑ j ∈ range L.length, Finsupp.single (g j) (L.getD j 0)

@[simp]
theorem letterExp_nil (g : ℕ → ℕ) : letterExp [] g = 0 := by simp [letterExp]

theorem letterExp_cons (r : ℕ) (L : List ℕ) (g : ℕ → ℕ) :
    letterExp (r :: L) g = Finsupp.single (g 0) r + letterExp L fun j => g (j + 1) := by
  rw [letterExp, letterExp, List.length_cons, Finset.sum_range_succ']
  simp only [List.getD_cons_succ, List.getD_cons_zero]
  rw [add_comm]

theorem letterExp_apply (L : List ℕ) (g : ℕ → ℕ) (i : ℕ) :
    letterExp L g i = ∑ j ∈ range L.length with g j = i, L.getD j 0 := by
  classical
  rw [letterExp, Finset.sum_apply', Finset.sum_filter]
  exact sum_congr rfl fun j _ => Finsupp.single_apply

/-- The total degree of the monomial of a letter assignment is the sum of the parts. -/
theorem degHom_letterExp (L : List ℕ) (g : ℕ → ℕ) : degHom (letterExp L g) = L.sum := by
  rw [letterExp, map_sum, sum_congr rfl fun j _ => degHom_single (g j) (L.getD j 0),
    ← List.sum_take_eq_sum_range_getD, List.take_of_length_le le_rfl]

/-! ### The coefficients of the tuple-counting series -/

/-- **Every letter assignment contributes.** The coefficient of `tupleCount L` at the monomial of an
assignment is nonzero: over `ℕ` a sum of terms is at least any one of them, and the term indexed by
the assignment itself is `1`. -/
theorem coeff_letterExp_tupleCount_ne_zero :
    ∀ (L : List ℕ) (g : ℕ → ℕ), MvPowerSeries.coeff (letterExp L g) (tupleCount L) ≠ 0 := by
  intro L
  induction L with
  | nil => intro g; simp
  | cons r L ih =>
    intro g hzero
    rw [letterExp_cons, tupleCount_cons, MvPowerSeries.coeff_mul] at hzero
    have hmem : (Finsupp.single (g 0) r, letterExp L fun j => g (j + 1))
        ∈ Finset.antidiagonal (Finsupp.single (g 0) r + letterExp L fun j => g (j + 1)) :=
      Finset.HasAntidiagonal.mem_antidiagonal.2 rfl
    have hle := Finset.single_le_sum
      (f := fun p : (ℕ →₀ ℕ) × (ℕ →₀ ℕ) => MvPowerSeries.coeff p.1 (powerSumSeries r)
        * MvPowerSeries.coeff p.2 (tupleCount L))
      (fun _ _ => Nat.zero_le _) hmem
    rw [coeff_powerSumSeries_of_mem ⟨g 0, rfl⟩, one_mul, hzero] at hle
    exact ih (fun j => g (j + 1)) (Nat.le_zero.1 hle)

/-- **Only letter assignments contribute.** A nonzero coefficient of `tupleCount L` is at the
monomial of some assignment: a nonzero sum has a nonzero term, and a nonzero coefficient of
`powerSumSeries r` pins one letter. -/
theorem exists_letterExp_of_coeff_tupleCount_ne_zero :
    ∀ (L : List ℕ) (α : ℕ →₀ ℕ), MvPowerSeries.coeff α (tupleCount L) ≠ 0 →
      ∃ g : ℕ → ℕ, α = letterExp L g := by
  intro L
  induction L with
  | nil =>
    intro α hα
    refine ⟨fun _ => 0, ?_⟩
    rw [letterExp_nil]
    by_contra hne
    rw [tupleCount_nil, MvPowerSeries.coeff_one, ite_eq_right hne] at hα
    exact hα rfl
  | cons r L ih =>
    intro α hα
    rw [tupleCount_cons, MvPowerSeries.coeff_mul] at hα
    obtain ⟨⟨x, y⟩, hmem, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hα
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hmem
    obtain ⟨i, rfl⟩ : ∃ i, x = Finsupp.single i r := by
      by_contra hcon
      rw [coeff_powerSumSeries_of_notMem hcon, zero_mul] at hne
      exact hne rfl
    obtain ⟨g, hg⟩ := ih y fun h => hne (by rw [h, mul_zero])
    refine ⟨fun j => if j = 0 then i else g (j - 1), ?_⟩
    rw [letterExp_cons, ite_eq_left rfl, ← hmem, hg]
    congr 1

/-! ### The realised power-sum monomial as a transported count -/

variable {K : Type*} [CommRing K] {ι : Lambda K →ₐ[K] AlphabetSeries K}

/-- `ι(p_r)` is the transport of the `ℕ`-valued power-sum series along `ℕ → K`, for `r ≥ 1`: both
have coefficient `1` at each `x_i^r` and `0` elsewhere, which is `HJO.Sym.IsRealisation`. -/
theorem map_powerSumSeries (hι : IsRealisation ι) {r : ℕ} (hr : 0 < r) :
    MvPowerSeries.map (Nat.castRingHom K) (powerSumSeries r) = ι (powerSum K r) := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  refine MvPowerSeries.ext fun α => ?_
  rw [MvPowerSeries.coeff_map]
  by_cases h : ∃ i, α = Finsupp.single i (k + 1)
  · obtain ⟨i, rfl⟩ := h
    rw [coeff_powerSumSeries_of_mem ⟨i, rfl⟩, hι.coeff_pow k i]
    exact map_one _
  · rw [coeff_powerSumSeries_of_notMem h, hι.coeff_of_ne k α fun i hcon => h ⟨i, hcon⟩]
    exact map_zero _

/-- The product over a list of parts transports the same way. -/
theorem map_tupleCount (hι : IsRealisation ι) :
    ∀ L : List ℕ, (∀ r ∈ L, 0 < r) →
      MvPowerSeries.map (Nat.castRingHom K) (tupleCount L)
        = (L.map fun r => ι (powerSum K r)).prod := by
  intro L
  induction L with
  | nil => intro _; rw [tupleCount_nil, List.map_nil, List.prod_nil]; exact map_one _
  | cons r L ih =>
    intro hL
    rw [tupleCount_cons, map_mul, map_powerSumSeries hι (hL r List.mem_cons_self),
      ih fun s hs => hL s (List.mem_cons_of_mem r hs), List.map_cons, List.prod_cons]

/-- **`ι(p_λ)` is the transported tuple count** of the nonincreasing listing of the parts of `λ`. -/
theorem iota_pmonomial_eq_map_tupleCount (hι : IsRealisation ι) {d : ℕ} (p : Nat.Partition d) :
    ι (pmonomial K p)
      = MvPowerSeries.map (Nat.castRingHom K) (tupleCount (p.parts.sort (· ≥ ·))) := by
  rw [map_tupleCount hι _ fun r hr => pos_of_mem_sort p hr, pmonomial, map_multiset_prod,
    Multiset.map_map]
  conv_lhs => rw [← Multiset.sort_eq p.parts (· ≥ ·)]
  rw [Multiset.map_coe, Multiset.prod_coe]
  rfl

/-- **The coefficients of `ι(p_λ)` are the transported tuple counts.** -/
theorem coeff_iota_pmonomial (hι : IsRealisation ι) {d : ℕ} (p : Nat.Partition d) (α : ℕ →₀ ℕ) :
    MvPowerSeries.coeff α (ι (pmonomial K p))
      = ((MvPowerSeries.coeff α (tupleCount (p.parts.sort (· ≥ ·))) : ℕ) : K) := by
  rw [iota_pmonomial_eq_map_tupleCount hι, MvPowerSeries.coeff_map]
  rfl

/-! ### The two coefficient facts -/

/-- **The diagonal coefficient is nonzero**: `R_λ ≠ 0`. The identity assignment, which
sends the `j`-th position to the `j`-th letter, produces `x^λ`, so the count is at least one; and a
positive natural number is nonzero in characteristic zero. -/
theorem coeff_partitionExponent_iota_pmonomial_ne_zero [CharZero K] (hι : IsRealisation ι) {d : ℕ}
    (p : Nat.Partition d) :
    MvPowerSeries.coeff (partitionExponent p) (ι (pmonomial K p)) ≠ 0 := by
  have hid : partitionExponent p = letterExp (p.parts.sort (· ≥ ·)) fun j => j := by
    refine Finsupp.ext fun i => ?_
    rw [partitionExponent_apply, letterExp_apply]
    by_cases hi : i < (p.parts.sort (· ≥ ·)).length
    · rw [Finset.filter_eq' (range _) i, ite_eq_left (mem_range.2 hi), sum_singleton]
    · rw [List.getD_eq_default _ 0 (by omega), Finset.sum_eq_zero]
      intro j hj
      rw [mem_filter, mem_range] at hj
      exact absurd (hj.2 ▸ hj.1) hi
  rw [hid, coeff_iota_pmonomial hι, Nat.cast_ne_zero]
  exact coeff_letterExp_tupleCount_ne_zero _ _

/-- **`ι(p_λ)` lives in total degree `d`**: a nonzero coefficient sits at the monomial of a letter
assignment, whose degree is the sum of the parts. -/
theorem degHom_of_coeff_iota_pmonomial_ne_zero (hι : IsRealisation ι) {d : ℕ}
    (p : Nat.Partition d) {α : ℕ →₀ ℕ}
    (h : MvPowerSeries.coeff α (ι (pmonomial K p)) ≠ 0) : degHom α = d := by
  have h' : MvPowerSeries.coeff α (tupleCount (p.parts.sort (· ≥ ·))) ≠ 0 := fun hn => h (by
    rw [coeff_iota_pmonomial hι, hn, Nat.cast_zero])
  obtain ⟨g, rfl⟩ := exists_letterExp_of_coeff_tupleCount_ne_zero _ α h'
  rw [degHom_letterExp, ← Multiset.sum_coe, Multiset.sort_eq, p.parts_sum]

/-- **The triangularity**: a nonzero coefficient of `ι(p_λ)` at `x^μ` forces `μ ⪰ λ`. The letter
assignment behind the coefficient merges the parts of `λ` into blocks whose sums are the parts of
`μ`, and merging dominates (`HJO.Sym.dominates_of_blockSums`). -/
theorem dominates_of_coeff_iota_pmonomial_ne_zero (hι : IsRealisation ι) {d : ℕ}
    (p q : Nat.Partition d)
    (h : MvPowerSeries.coeff (partitionExponent q) (ι (pmonomial K p)) ≠ 0) :
    Dominates q p := by
  classical
  have h' : MvPowerSeries.coeff (partitionExponent q)
      (tupleCount (p.parts.sort (· ≥ ·))) ≠ 0 := fun hn => h (by
    rw [coeff_iota_pmonomial hι, hn, Nat.cast_zero])
  obtain ⟨g, hgq⟩ := exists_letterExp_of_coeff_tupleCount_ne_zero _ _ h'
  set L := p.parts.sort (· ≥ ·) with hL
  have hlen : Multiset.card p.parts = L.length := by rw [hL, Multiset.length_sort]
  -- the block sum at the letter `t` is the `t`-th part of `q`
  have hblock : ∀ t : ℕ, (∑ j ∈ range L.length with g j = t, L.getD j 0)
      = partitionExponent q t := fun t => by rw [hgq, letterExp_apply]
  have hmapq : (Multiset.range (Multiset.card q.parts)).map (partitionExponent q) = q.parts := by
    have hq := map_partitionExponent q
    rwa [support_partitionExponent] at hq
  refine dominates_of_blockSums (r := Multiset.card q.parts) p q hlen g (fun j hj => ?_) ?_
  · -- a used letter lies in the support of `x^μ`, which is the index range of the parts of `q`
    have hpos : 0 < partitionExponent q (g j) := by
      rw [← hblock (g j)]
      refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun k => L.getD k 0)
        (fun _ _ => Nat.zero_le _) (mem_filter.2 ⟨mem_range.2 hj, rfl⟩))
      rw [List.getD_eq_getElem _ 0 hj]
      exact pos_of_mem_sort p (List.getElem_mem hj)
    rw [← mem_range, ← support_partitionExponent q]
    exact Finsupp.mem_support_iff.2 (by omega)
  · conv_lhs => rw [← hmapq]
    exact Multiset.map_congr rfl fun t _ => (hblock t).symm

/-! ### Independence -/

/-- **`HJO.Sym.exists_basis_iota_pmonomial`, the independence half: the realised power-sum monomials
of the partitions of `d` are linearly independent.**

Read a vanishing combination at the monomial `x^{λ₀}` of the lexicographically least `λ₀` whose
scalar is nonzero. A term `ι(p_λ)` contributing there has `λ₀ ⪰ λ`, hence `λ₀ > λ`
(`HJO.Sym.partitionLex_of_dominates`) unless `λ = λ₀`; minimality excludes that, so only the `λ₀`
term survives, and its coefficient `R_{λ₀}` is nonzero. -/
theorem linearIndependent_iota_pmonomial [CharZero K] [NoZeroDivisors K] (hι : IsRealisation ι)
    (d : ℕ) :
    LinearIndependent K fun p : Nat.Partition d => ι (pmonomial K p) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  by_contra hex
  rw [not_forall] at hex
  obtain ⟨p₁, hp₁⟩ := hex
  set R : Nat.Partition d → Nat.Partition d → Prop :=
    fun a b => partitionLex (partitionDiagram a) (partitionDiagram b) with hR
  have : IsTrans (Nat.Partition d) R := ⟨fun _ _ _ => partitionLex_trans⟩
  have : Std.Irrefl R := ⟨fun a => not_partitionLex_self (partitionDiagram a)⟩
  obtain ⟨p₀, hp₀mem, hp₀min⟩ :=
    (Finite.wellFounded_of_trans_of_irrefl R).has_min {a | g a ≠ 0} ⟨p₁, hp₁⟩
  have hcoeff := congrArg (MvPowerSeries.coeff (partitionExponent p₀)) hg
  rw [map_sum, map_zero] at hcoeff
  rw [Finset.sum_eq_single p₀ (fun a _ hne => ?_) (fun h => absurd (mem_univ p₀) h),
    MvPowerSeries.coeff_smul] at hcoeff
  · exact hp₀mem (by
      rcases mul_eq_zero.1 hcoeff with h | h
      · exact h
      · exact absurd h (coeff_partitionExponent_iota_pmonomial_ne_zero hι p₀))
  · rw [MvPowerSeries.coeff_smul]
    by_cases hga : g a = 0
    · rw [hga, zero_mul]
    · refine mul_eq_zero_of_right _ (by_contra fun hne' => ?_)
      exact hp₀min a hga
        (partitionLex_of_dominates (dominates_of_coeff_iota_pmonomial_ne_zero hι a p₀ hne') hne)

end HJO.Sym
