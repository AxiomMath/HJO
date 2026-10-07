/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Classical.HsymmComposition
public import HJO.Symmetric.AxisFree
public meta import HJO.Attr

/-! # The complete homogeneous products span a graded piece

Two lemmas. Newton's identity, read backwards, writes `p_n` in the `h`'s; and a graded
piece of `Λ` is spanned by the products of power sums, so it is spanned by the products `h_α` over
the compositions `α` of its degree.

## Main definitions

* `HJO.Sym.completeHomogCompSpan`: the `K`-span of the `h_α` with `α` a composition of `n`.

## Main statements

* `HJO.Sym.powerSum_mem_completeHomogCompSpan`.
* `HJO.Sym.lambdaComp_le_completeHomogCompSpan`.

## Implementation notes

The "`f` is a `𝕜`-linear combination of finitely many `h_α`" is membership in a
`Submodule.span`, which is what such a combination is; `Submodule.mem_span_finset` is the
translation back to the phrasing if a consumer wants it.

The span is closed under multiplication with the degrees adding
(`HJO.Sym.completeHomogCompSpan_mul_le`), because concatenating two compositions concatenates the
two products — that single fact is what carries both lemmas, `p_k h_{n-k}` in the first and the
product of powers of power sums in the second.

*The `n ≥ 1` is needed in the first lemma and not in the second.* `p_n` for `n = 0` is
`p_1` by the truncated subtraction of `HJO.Sym.powerSum`, and `Λ_0` is spanned by `1 = h_{()}`, so
the spanning statement is true at `n = 0` while the power-sum statement is not. That is a
generalisation of the second lemma.

## References

This file formalises `HJO.Sym.powerSum_mem_completeHomogCompSpan` and
`HJO.Sym.lambdaComp_le_completeHomogCompSpan`.
-/

@[expose] public section

open Finset

namespace HJO.Sym

section Span

variable (K : Type*) [CommRing K] [Algebra ℚ K]

/-- Concatenating compositions multiplies the complete homogeneous products:
`h_{αβ} = h_α h_β`. -/
theorem completeHomogComp_append (α β : List ℕ) :
    completeHomogComp K (α ++ β) = completeHomogComp K α * completeHomogComp K β := by
  rw [completeHomogComp, completeHomogComp, completeHomogComp, List.map_append, List.prod_append]

/-- `h_α` of a one-part composition is the complete homogeneous function of that part. -/
@[simp]
theorem completeHomogComp_singleton (a : ℕ) :
    completeHomogComp K [a] = completeHomog K a := by
  rw [completeHomogComp_cons, completeHomogComp_nil, mul_one]

/-- The `K`-span of the complete homogeneous products `h_α` over the compositions `α` of `n`: the
set of `K`-linear combinations of finitely many of them, which is the conclusion both
lemmas below state. A composition is a list of positive parts summing to `n`. -/
noncomputable def completeHomogCompSpan (n : ℕ) : Submodule K (Lambda K) :=
  Submodule.span K
    {f : Lambda K | ∃ α : List ℕ, (∀ a ∈ α, 0 < a) ∧ α.sum = n ∧ f = completeHomogComp K α}

/-- `h_α` lies in the span of its own degree. -/
theorem completeHomogComp_mem_completeHomogCompSpan {α : List ℕ} (hα : ∀ a ∈ α, 0 < a) :
    completeHomogComp K α ∈ completeHomogCompSpan K α.sum :=
  Submodule.subset_span ⟨α, hα, rfl, rfl⟩

/-- `h_a` lies in the span of degree `a`, for `a ≥ 1`: it is `h_α` at the one-part composition. -/
theorem completeHomog_mem_completeHomogCompSpan {a : ℕ} (ha : 0 < a) :
    completeHomog K a ∈ completeHomogCompSpan K a := by
  have h := completeHomogComp_mem_completeHomogCompSpan K (α := [a]) (by simpa using ha)
  rwa [completeHomogComp_singleton, List.sum_singleton] at h

/-- `1` lies in the span of degree `0`: it is `h_α` at the empty composition. -/
theorem one_mem_completeHomogCompSpan : (1 : Lambda K) ∈ completeHomogCompSpan K 0 := by
  have h := completeHomogComp_mem_completeHomogCompSpan K (α := ([] : List ℕ)) (by simp)
  rwa [completeHomogComp_nil, List.sum_nil] at h

/-- **The spans multiply, the degrees adding**: concatenating the two compositions concatenates the
two products, so the product of a composition of `a` and one of `b` is one of `a + b`. -/
theorem completeHomogCompSpan_mul_le (a b : ℕ) :
    completeHomogCompSpan K a * completeHomogCompSpan K b ≤ completeHomogCompSpan K (a + b) := by
  rw [completeHomogCompSpan, completeHomogCompSpan, Submodule.span_mul_span]
  refine Submodule.span_le.2 (Set.mul_subset_iff.2 ?_)
  rintro x ⟨α, hα, hαs, rfl⟩ y ⟨β, hβ, hβs, rfl⟩
  refine Submodule.subset_span ⟨α ++ β, ?_, ?_, (completeHomogComp_append K α β).symm⟩
  · intro c hc
    rcases List.mem_append.1 hc with h | h
    · exact hα c h
    · exact hβ c h
  · rw [List.sum_append, hαs, hβs]

/-- The product of two members of the spans lies in the span of the sum of the degrees. -/
theorem mul_mem_completeHomogCompSpan {a b : ℕ} {f g : Lambda K}
    (hf : f ∈ completeHomogCompSpan K a) (hg : g ∈ completeHomogCompSpan K b) :
    f * g ∈ completeHomogCompSpan K (a + b) :=
  completeHomogCompSpan_mul_le K a b (Submodule.mul_mem_mul hf hg)

/-- A power of a member of the span lies in the span of the multiplied degree. -/
theorem pow_mem_completeHomogCompSpan {a : ℕ} {f : Lambda K}
    (hf : f ∈ completeHomogCompSpan K a) (k : ℕ) :
    f ^ k ∈ completeHomogCompSpan K (a * k) := by
  induction k with
  | zero => rw [pow_zero, Nat.mul_zero]; exact one_mem_completeHomogCompSpan K
  | succ k ih =>
    rw [pow_succ, show a * (k + 1) = a * k + a from by ring]
    exact mul_mem_completeHomogCompSpan K ih hf

/-- A finite product of members of the spans lies in the span of the sum of the degrees. -/
theorem prod_mem_completeHomogCompSpan {ι : Type*} {s : Finset ι} {f : ι → Lambda K} {d : ι → ℕ}
    (h : ∀ i ∈ s, f i ∈ completeHomogCompSpan K (d i)) :
    ∏ i ∈ s, f i ∈ completeHomogCompSpan K (∑ i ∈ s, d i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => rw [Finset.prod_empty, Finset.sum_empty]; exact one_mem_completeHomogCompSpan K
  | cons i s hi ih =>
    rw [Finset.prod_cons, Finset.sum_cons]
    exact mul_mem_completeHomogCompSpan K (h i (Finset.mem_cons_self i s))
      (ih fun j hj => h j (Finset.mem_cons_of_mem hj))

/-- **A power sum in the complete homogeneous functions.** For `n ≥ 1`,
`p_n` is a `K`-linear combination of the `h_α` with `α` a composition of `n`.

Newton's identity, `n h_n = ∑_{k=1}^{n} p_k h_{n-k}`, has `p_n h_0 = p_n` as its last term, so
`p_n = n h_n - ∑_{k=1}^{n-1}p_k h_{n-k}`. The first term is a scalar multiple of `h_{(n)}`; in each
other term the strong inductive hypothesis writes `p_k` in the `h_β` with `β` a composition of
`k ≤ n - 1`, and appending the part `n - k ≥ 1` makes a composition of `n`.

Equivalently, for `n ≥ 1`, `p_n`
lies in the `𝕜`-span of the products `h_{μ_1} ⋯ h_{μ_m}` with every `μ_i ≥ 1` summing to `n`, which
is this span — a composition of `n` is such a tuple of parts. -/
@[hjo "lem_ght_psum_hproduct"]
theorem powerSum_mem_completeHomogCompSpan :
    ∀ {n : ℕ}, 0 < n → powerSum K n ∈ completeHomogCompSpan K n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    match n with
    | 0 => exact absurd hn (lt_irrefl 0)
    | m + 1 =>
      have hnewton := CopPower.natCast_mul_completeHomog (K := K) m
      rw [Finset.sum_range_succ, Nat.sub_self, CopPower.completeHomog_zero, mul_one] at hnewton
      have hsplit : powerSum K (m + 1)
          = ((m : K) + 1) • completeHomog K (m + 1)
            - ∑ k ∈ range m, powerSum K (k + 1) * completeHomog K (m - k) := by
        rw [MvPolynomial.smul_eq_C_mul, map_add, MvPolynomial.C_1, map_natCast]
        linear_combination -hnewton
      rw [hsplit]
      refine Submodule.sub_mem _ (Submodule.smul_mem _ _ ?_) (Submodule.sum_mem _ fun k hk => ?_)
      · exact completeHomog_mem_completeHomogCompSpan K m.succ_pos
      · have hkm : k < m := Finset.mem_range.1 hk
        have hmem := mul_mem_completeHomogCompSpan K
          (ih (k + 1) (by omega) k.succ_pos)
          (completeHomog_mem_completeHomogCompSpan K (a := m - k) (by omega))
        rwa [show k + 1 + (m - k) = m + 1 from by omega] at hmem

attribute [hjo "lem_om_psymm_hsymm_span"] powerSum_mem_completeHomogCompSpan

/-- **The complete homogeneous products span a graded piece.** Every
`f ∈ Λ_n` is a `K`-linear combination of the `h_α` with `α` a composition of `n`.

`Λ_n` is spanned by the products of power sums of total degree `n`; each factor `p_{i+1}` is a
combination of the `h_β` with `β` a composition of `i + 1`, and the degrees add along the product.
The `n ≥ 1` is not used: at `n = 0` the only generator is the empty product `1`, which
is `h_{()}`. -/
@[hjo "lem_om_hsymm_span"]
theorem lambdaComp_le_completeHomogCompSpan (n : ℕ) :
    LambdaComp K n ≤ completeHomogCompSpan K n := by
  rw [lambdaComp_eq_span]
  refine Submodule.span_le.2 ?_
  rintro f ⟨e, he, rfl⟩
  have hdeg : ∑ i ∈ e.support, (i + 1) * e i = n := by
    rw [← he, Finsupp.weight_apply, Finsupp.sum]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_eq_mul, Nat.mul_comm]
  have hprod := prod_mem_completeHomogCompSpan K (s := e.support)
    (f := fun i => powerSum K (i + 1) ^ e i) (d := fun i => (i + 1) * e i)
    fun i _ => pow_mem_completeHomogCompSpan K
      (powerSum_mem_completeHomogCompSpan K i.succ_pos) (e i)
  rwa [hdeg] at hprod

end Span

end HJO.Sym
