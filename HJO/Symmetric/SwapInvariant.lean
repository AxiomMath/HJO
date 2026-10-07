/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Classical.SchurBasis
public import HJO.Shuffle.LetterReversal
public meta import HJO.Attr

/-! # A homogeneous series fixed by the adjacent relabellings is a monomial combination

Let `G ∈ 𝒫 = K⟦x₀, x₁, …⟧` be homogeneous of degree `n` — every monomial occurring in it has total
degree `n` — and let `G` be fixed by the relabelling `x_i ↔ x_{i+1}` for every `i`. Then `G` is a
`K`-combination of the monomial series `m_μ` over the partitions `μ` of `n`, with the coefficient of
`m_μ` the coefficient of `G` at `x^μ`.

This is the step that turns a symmetry statement about a series into membership of `W_n`, the span
of the `m_μ`, and hence — through `HJO.Sym.map_lambdaComp_eq_msymmSpan` — into the existence of a
symmetric function realising it. It is applied in `HJO.Dyck.exists_iota_eq_pathCharSeries`,
whose input is exactly `HJO.Dyck.letterPerm_swap_charSeries`: the characteristic series is fixed by
each adjacent interchange, and is homogeneous because every labelling it sums over has `n` letters.

## Main definitions

* `HJO.Sym.exponentStab F`: the submonoid of permutations of the alphabet that a function `F` of
  exponent vectors does not notice.

## Main results

* `HJO.Sym.eq_of_map_range`: if `F` is fixed by every adjacent interchange, then `F α = F β`
  whenever `α` and `β` agree above a window and have the same multiset of entries inside it.
* `HJO.Sym.eq_partitionExponent`: hence `F α = F (x^{μ_α})`, the value of `F` at an exponent vector
  depending only on the partition formed by its nonzero entries.
* `HJO.Sym.eq_sum_msymmSeries_of_letterPerm_swap`, `HJO.Sym.mem_msymmSpan_of_letterPerm_swap`: the
  expansion `G = ∑_μ [x^μ]G · m_μ` and the membership `G ∈ W_n`.

## Implementation notes

*The route is the window induction, not the construction of a sorting permutation.* The sorting
relabelling `HJO.Sym.sortIndex` of `HJO/Classical/SortExponent.lean` carries `x^α` to `x^{μ_α}`
but is **not** finitely supported — it shifts the whole complement of the support — so it is not a
product of adjacent interchanges and the hypothesis here does not reach it. `letterPerm_realisation`
can use it because a realised symmetric function is fixed by *every* permutation of the alphabet;
here only the adjacent ones are given. `eq_of_map_range` therefore moves one entry at a time into
position `k` by a single transposition and recurses on the shorter window, which needs no
permutation of `ℕ` beyond the transpositions themselves.

*This generalises the Kostka-number version.* `HJO.Sym.kostkaStab`,
`HJO.Sym.kostka_eq_of_map_range` and `HJO.Sym.kostka_comp` of
`HJO/Classical/BenderKnuth.lean` are the same three statements with `F = kostka μ`, proved
there from the Bender--Knuth involution.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018)
661--697, §3.1.
-/

@[expose] public section

open Finset

namespace HJO.Sym

/-! ### The relabellings a function of exponent vectors does not notice -/

variable {M : Type*}

/-- **The relabellings of the letters that `F` does not notice.** A permutation `σ` of the alphabet
belongs to it when `F` takes the same value at `α` and at `α` reindexed along `σ`. -/
def exponentStab (F : (ℕ →₀ ℕ) → M) : Submonoid (Equiv.Perm ℕ) where
  carrier := {σ | ∀ α : ℕ →₀ ℕ, F (Finsupp.equivMapDomain σ α) = F α}
  mul_mem' {σ τ} hσ hτ := fun α => by
    have h : Finsupp.equivMapDomain (σ * τ) α
        = Finsupp.equivMapDomain σ (Finsupp.equivMapDomain τ α) := by
      rw [← Finsupp.equivMapDomain_trans]
      rfl
    rw [h, hσ, hτ]
  one_mem' := fun α => by rw [Equiv.Perm.one_def, Finsupp.equivMapDomain_refl]

theorem mem_exponentStab {F : (ℕ →₀ ℕ) → M} {σ : Equiv.Perm ℕ} :
    σ ∈ exponentStab F ↔ ∀ α : ℕ →₀ ℕ, F (Finsupp.equivMapDomain σ α) = F α := Iff.rfl

variable {F : (ℕ →₀ ℕ) → M} (hF : ∀ i : ℕ, Equiv.swap i (i + 1) ∈ exponentStab F)

include hF

/-- Every interchange of two letters at distance `k` is a composite of adjacent ones. -/
theorem swap_add_mem_exponentStab (a k : ℕ) : Equiv.swap a (a + k) ∈ exponentStab F := by
  induction k with
  | zero => rw [Nat.add_zero, Equiv.swap_self, ← Equiv.Perm.one_def]; exact one_mem _
  | succ k ih => exact SubmonoidClass.swap_mem_trans _ ih (hF (a + k))

/-- **Every interchange of two letters is unnoticed** as soon as the adjacent ones are. -/
theorem swap_mem_exponentStab (a b : ℕ) : Equiv.swap a b ∈ exponentStab F := by
  rcases le_total a b with h | h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    exact swap_add_mem_exponentStab hF a k
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [Equiv.swap_comm]
    exact swap_add_mem_exponentStab hF b k

/-- **`F` depends only on the multiset of entries below the window in which two exponent vectors
differ.** The induction moves the correct entry into position `k` by a single transposition, which
`swap_mem_exponentStab` shows `F` does not notice, and then recurses on the shorter window. -/
theorem eq_of_map_range : ∀ (k : ℕ) (α β : ℕ →₀ ℕ),
    (∀ a, k ≤ a → α a = β a) →
      Multiset.map α (range k).val = Multiset.map β (range k).val → F α = F β := by
  intro k
  induction k with
  | zero => exact fun α β hag _ => by rw [Finsupp.ext fun a => hag a (Nat.zero_le a)]
  | succ k ih =>
    intro α β hag hmap
    have hmem : β k ∈ Multiset.map α (range (k + 1)).val := by
      rw [hmap]
      exact Multiset.mem_map.2 ⟨k, by rw [← Finset.mem_def, mem_range]; omega, rfl⟩
    obtain ⟨a, ha, hav⟩ := Multiset.mem_map.1 hmem
    rw [← Finset.mem_def, mem_range] at ha
    set α' := Finsupp.equivMapDomain (Equiv.swap a k) α with hα'
    have hval : ∀ b : ℕ, α' b = α (Equiv.swap a k b) := fun b => by
      rw [hα', Finsupp.equivMapDomain_apply, Equiv.symm_swap]
    have hk : α' k = β k := by rw [hval, Equiv.swap_apply_right, hav]
    have hag' : ∀ b, k ≤ b → α' b = β b := by
      intro b hb
      rcases eq_or_lt_of_le hb with rfl | hlt
      · exact hk
      · rw [hval, Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)]
        exact hag b (by omega)
    have hswap : Multiset.map (Equiv.swap a k) (range (k + 1)).val = (range (k + 1)).val := by
      have hfin : Finset.map (Equiv.swap a k).toEmbedding (range (k + 1)) = range (k + 1) := by
        refine Finset.eq_of_subset_of_card_le (fun x hx => ?_) (by rw [Finset.card_map])
        obtain ⟨j, hj, rfl⟩ := Finset.mem_map.1 hx
        rw [mem_range] at hj ⊢
        rw [Equiv.coe_toEmbedding]
        rcases eq_or_ne j a with rfl | hja
        · rw [Equiv.swap_apply_left]; omega
        rcases eq_or_ne j k with rfl | hjk
        · rw [Equiv.swap_apply_right]; omega
        · rw [Equiv.swap_apply_of_ne_of_ne hja hjk]; omega
      rw [← Equiv.coe_toEmbedding (f := Equiv.swap a k), ← Finset.map_val, hfin]
    have hmap' : Multiset.map α' (range k).val = Multiset.map β (range k).val := by
      have h1 : Multiset.map α' (range (k + 1)).val = Multiset.map α (range (k + 1)).val := by
        rw [show (α' : ℕ → ℕ) = (α : ℕ → ℕ) ∘ (Equiv.swap a k : ℕ → ℕ) from funext hval,
          ← Multiset.map_map, hswap]
      have hrange : ∀ γ : ℕ →₀ ℕ, Multiset.map γ (range (k + 1)).val
          = γ k ::ₘ Multiset.map γ (range k).val := fun γ => by
        rw [Finset.range_val, Finset.range_val, Multiset.range_succ, Multiset.map_cons]
      have h2 : α' k ::ₘ Multiset.map α' (range k).val
          = β k ::ₘ Multiset.map β (range k).val := by
        rw [← hrange α', ← hrange β, h1, hmap]
      rw [hk] at h2
      exact (Multiset.cons_inj_right (β k)).1 h2
    exact ((swap_mem_exponentStab hF a k) α).symm.trans (ih α' β hag' hmap')

/-- **`F` is read at a partition**: its value at `α` is its value at the exponent vector `x^{μ_α}`
of the partition formed by the nonzero entries of `α`. The two vectors agree above a window
containing both supports and have the same multiset of entries inside it. -/
theorem eq_partitionExponent {d : ℕ} {α : ℕ →₀ ℕ} (h : degHom α = d) :
    F α = F (partitionExponent (partitionOfValues h)) := by
  classical
  set β := partitionExponent (partitionOfValues h) with hβ
  have hvals : β.support.val.map β = α.support.val.map α := by
    rw [hβ, map_partitionExponent, parts_partitionOfValues]
  have hcard : #β.support = #α.support := by
    have h1 : Multiset.card (Multiset.map β β.support.val) = #β.support := Multiset.card_map _ _
    have h2 : Multiset.card (Multiset.map α α.support.val) = #α.support := Multiset.card_map _ _
    rw [← h1, ← h2, hvals]
  obtain ⟨M₁, hM₁⟩ := Finset.exists_nat_subset_range α.support
  obtain ⟨M₂, hM₂⟩ := Finset.exists_nat_subset_range β.support
  have hα : α.support ⊆ range (max M₁ M₂) :=
    hM₁.trans (Finset.range_subset_range.2 (le_max_left _ _))
  have hβ' : β.support ⊆ range (max M₁ M₂) :=
    hM₂.trans (Finset.range_subset_range.2 (le_max_right _ _))
  refine eq_of_map_range hF (max M₁ M₂) α β (fun a ha => ?_) ?_
  · rw [Finsupp.notMem_support_iff.1 fun hc => absurd (mem_range.1 (hα hc)) (by omega),
      Finsupp.notMem_support_iff.1 fun hc => absurd (mem_range.1 (hβ' hc)) (by omega)]
  · rw [map_range_val α hα, map_range_val β hβ', hcard, hvals]

omit hF

/-! ### A homogeneous series fixed by the adjacent interchanges -/

variable {K : Type*} [CommRing K] {n : ℕ} {G : AlphabetSeries K}

/-- The adjacent interchanges a series is fixed by, read as relabellings its coefficients do not
notice. `letterPerm K ρ` reindexes a coefficient along `ρ⁻¹`, and an interchange is its own
inverse. -/
theorem swap_mem_exponentStab_coeff
    (hsym : ∀ m : ℕ, letterPerm K (Equiv.swap m (m + 1)) G = G) (i : ℕ) :
    Equiv.swap i (i + 1) ∈ exponentStab fun α => MvPowerSeries.coeff α G := fun α => by
  have h := coeff_letterPerm (Equiv.swap i (i + 1)) G α
  rw [hsym i, Equiv.symm_swap] at h
  exact h.symm

/-- **A homogeneous series fixed by the adjacent interchanges is the combination of the monomial
series with its own coefficients.** A monomial of total degree other than `n` occurs in neither
side; and at one of total degree `n` the right side is the single contribution of `m_{μ_α}`, whose
coefficient is that of `G` at `x^{μ_α}` — which is that of `G` at `x^α` by
`eq_partitionExponent`. -/
theorem eq_sum_msymmSeries_of_letterPerm_swap
    (hhom : ∀ α : ℕ →₀ ℕ, (α.sum fun _ e => e) ≠ n → MvPowerSeries.coeff α G = 0)
    (hsym : ∀ m : ℕ, letterPerm K (Equiv.swap m (m + 1)) G = G) :
    G = ∑ μ : Nat.Partition n, MvPowerSeries.coeff (partitionExponent μ) G • msymmSeries K μ := by
  classical
  have hstab := swap_mem_exponentStab_coeff hsym
  refine MvPowerSeries.ext fun α => ?_
  rw [map_sum]
  simp only [MvPowerSeries.coeff_smul]
  by_cases hd : degHom α = n
  · rw [Finset.sum_eq_single (partitionOfValues hd) (fun p _ hne => ?_)
      (fun hc => absurd (mem_univ _) hc)]
    · rw [coeff_msymmSeries, ite_eq_left (parts_partitionOfValues hd).symm, mul_one]
      exact eq_partitionExponent hstab hd
    · rw [coeff_msymmSeries, ite_eq_right fun hp => hne (Nat.Partition.ext
        (hp.symm.trans (parts_partitionOfValues hd).symm)), mul_zero]
  · rw [hhom α fun hc => hd ((degHom_apply α).trans hc)]
    refine (Finset.sum_eq_zero fun p _ => ?_).symm
    refine mul_eq_zero_of_right _ (coeff_msymmSeries_eq_zero_of_sum_ne K p ?_)
    exact fun hc => hd ((degHom_apply α).trans hc)

/-- **A homogeneous series fixed by the adjacent interchanges lies in `W_n`**, the span of the
monomial series of the partitions of `n`. -/
theorem mem_msymmSpan_of_letterPerm_swap
    (hhom : ∀ α : ℕ →₀ ℕ, (α.sum fun _ e => e) ≠ n → MvPowerSeries.coeff α G = 0)
    (hsym : ∀ m : ℕ, letterPerm K (Equiv.swap m (m + 1)) G = G) :
    G ∈ msymmSpan K n := by
  rw [eq_sum_msymmSeries_of_letterPerm_swap hhom hsym]
  exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (msymmSeries_mem_msymmSpan K p)

end HJO.Sym
