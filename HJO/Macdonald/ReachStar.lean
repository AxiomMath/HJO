/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Classical.HsymmSpan
public import HJO.Collinear.DopStarDegree
public import HJO.Macdonald.Conjugator
public import HJO.Shuffle.Grading
public meta import HJO.Attr

/-! # One starred step, and reachability from the unit

Garsia--Haiman--Tesler's Theorem 2.1 in its starred form, and the reachability statement
Carlsson--Mellit quote from it: the only `𝕜`-subspace of `Λ` containing `1` and closed under both
multiplication by `e₁` and `D*_1` is `Λ` itself.

The route is as follows. `G_k = {D*_1A + e₁B : A, B ∈ Λ_{k-1}}` is a subspace, being the sum of
the image of a graded piece under a linear map and the image under multiplication by `e₁`. Every
`D*_a g` with `g ∈ Λ_{k-a}` lies in it, by induction on `a` from the commutation
`D*_a(e₁g) = e₁D*_ag - M̃D*_{a+1}g`. Every `h_b h` with `h ∈ Λ_{k-b}` lies in it, by induction on
`k - b` from the expansion `D*_bh = ∑_r h*_{[r]}h_{r+b}`, whose `r = 0` term is `h h_b`. Those
products span `Λ_k`, so `Λ_k ⊆ G_k`; and an induction on the degree then reaches every graded
piece from the unit.

## Main definitions

* `HJO.Sym.reachStarSubmodule`: `G_k` as a submodule -- the sum `D*_1(Λ_{k-1}) + e₁Λ_{k-1}`.

## Main results

* `HJO.Sym.lambdaComp_eq_completeHomogCompSpan`.
* `HJO.Sym.coe_reachStarSubmodule`.
* `HJO.Sym.dopStar_mem_reachStar`.
* `HJO.Sym.completeHomog_mul_mem_reachStar`.
* `HJO.Sym.exists_mem_reachStar`.
* `HJO.Sym.eq_top_of_one_mem_of_closed`.

## Implementation notes

**The side condition, and where it comes from.** From `HJO.Sym.dopStar_mem_reachStar` onwards every
statement here carries `M = (1 - q)(1 - u) ≠ 0`, written `HJO.Sym.paramProduct q u ≠ 0`. The proof
of `HJO.Sym.dopStar_mem_reachStar` divides the relation `M̃ D*_ag = e₁D*_{a-1}g - D*_{a-1}(e₁g)` by
`M̃ = (1 - q⁻¹)(1 - u⁻¹)` and justifies that by "`M̃` is a nonzero element of the field
`𝕜 = ℚ(q, u)`". Over a general field that is a hypothesis, and `M ≠ 0` is the form the rest of this
library carries it in; `HJO.Sym.paramProduct_inv_ne_zero` turns it into `M̃ ≠ 0`. It is free at
the consumer, which instantiates at `AlgebraicIndependent ℤ ![q, u]`
(`HJO.Sym.paramProduct_ne_zero`).

*The condition is not an artefact.* At `q = 1` one has `M̃ = 0`, the relation above degenerates to
`e₁D*_{a-1}g = D*_{a-1}(e₁g)`, and nothing forces `D*_ag` into `G_k`; the route has no content
there. `HJO.Sym.exists_bound_plethShiftStar`, `HJO.Sym.dopStar_eq_sum_range`,
`HJO.Sym.isLinearMap_dopStar`, `HJO.Sym.shiftStarCoeff_zero`, `HJO.Sym.dopStar_mem_lambdaComp`,
`HJO.Sym.dopStar_elemSymm_one_mul` and `HJO.Sym.lambdaComp_eq_completeHomogCompSpan` carry no
condition at all.

**Truncated subtraction.** The inductions are on `a` upward from `1` and on `k - b`
downward, both against a subtraction. Every statement below is therefore *also* given in the
shifted form the induction actually runs in -- `a = b + 1` and `k = b + 1 + c` for
`HJO.Sym.dopStar_succ_mem_reachStar`, `b = e + 1` and `k = e + 1 + c` for
`HJO.Sym.completeHomog_mul_mem_reachStar_add`, `k = m + 1` for `HJO.Sym.exists_mem_reachStar` --
so that no hypothesis is stated at an index where `ℕ` truncation would make it vacuous, and the
unshifted phrasing is derived from the shifted one.

## References

Reachability from the unit: the lemmas `HJO.Sym.lambdaComp_eq_completeHomogCompSpan`,
`HJO.Sym.coe_reachStarSubmodule`, `HJO.Sym.dopStar_mem_reachStar`,
`HJO.Sym.completeHomog_mul_mem_reachStar`, `HJO.Sym.exists_mem_reachStar` and
`HJO.Sym.eq_top_of_one_mem_of_closed`, and the definition `HJO.Sym.reachStar`.
-/

@[expose] public section

open Finset

namespace HJO.Sym

/-! ### The complete homogeneous products span a graded piece -/

section HproductSpan

variable (K : Type*) [CommRing K] [Algebra ℚ K]

/-- `h_α` is homogeneous of degree `α.sum`: each factor `h_a` lies in `Λ_a` and the grading is
multiplicative. No positivity of the parts is needed, `h_0 = 1` lying in `Λ_0`. -/
theorem completeHomogComp_mem_lambdaComp (α : List ℕ) :
    completeHomogComp K α ∈ LambdaComp K α.sum := by
  induction α with
  | nil => rw [completeHomogComp_nil, List.sum_nil]; exact one_mem_lambdaComp K
  | cons a α ih =>
    rw [completeHomogComp_cons, List.sum_cons]
    exact mul_mem_lambdaComp (completeHomog_mem_lambdaComp K a) ih

/-- The span of the `h_α` over the compositions of `d` sits inside `Λ_d`: each `h_α` does. -/
theorem completeHomogCompSpan_le_lambdaComp (d : ℕ) :
    completeHomogCompSpan K d ≤ LambdaComp K d := by
  rw [completeHomogCompSpan]
  refine Submodule.span_le.2 ?_
  rintro x ⟨α, -, hαs, rfl⟩
  rw [SetLike.mem_coe, ← hαs]
  exact completeHomogComp_mem_lambdaComp K α

/-- **The products of complete homogeneous functions span each graded
piece.** For every `d ≥ 0` the space `Λ_d` *is* the `𝕜`-linear span of the products
`h_{μ_1} ⋯ h_{μ_m}` with `m ≥ 0`, every `μ_i ≥ 1` and `μ_1 + ⋯ + μ_m = d` -- a composition of `d`
being exactly such a tuple of parts.

Both inclusions are already available: `Λ_d ⊆ S_d` is
`HJO.Sym.lambdaComp_le_completeHomogCompSpan`, which runs through
`HJO.Sym.powerSum_mem_completeHomogCompSpan`, and `S_d ⊆ Λ_d` is the multiplicativity of the
grading. -/
@[hjo "lem_ght_hproduct_span"]
theorem lambdaComp_eq_completeHomogCompSpan (d : ℕ) :
    LambdaComp K d = completeHomogCompSpan K d :=
  le_antisymm (lambdaComp_le_completeHomogCompSpan K d) (completeHomogCompSpan_le_lambdaComp K d)

end HproductSpan

/-! ### One starred step is a subspace -/

section ReachStarSubspace

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **`G_k` as a submodule**: the sum of the image of `Λ_{k-1}` under `D*_1` and the image of
`Λ_{k-1}` under multiplication by `e₁`. Both summands are submodules, `D*_1` and multiplication by
`e₁` being `𝕜`-linear, and the sum of two submodules consists of the sums of one element of each --
which is what `HJO.Sym.reachStar` describes. -/
noncomputable def reachStarSubmodule (q u : L) (k : ℕ) : Submodule L (Lambda L) :=
  (LambdaComp L (k - 1)).map (DopStar q u 1) ⊔
    (LambdaComp L (k - 1)).map (LinearMap.mulLeft L (elemSymm L 1))

/-- Membership in the submodule is membership in `G_k`. -/
theorem mem_reachStarSubmodule_iff {q u : L} {k : ℕ} {f : Lambda L} :
    f ∈ reachStarSubmodule q u k ↔ f ∈ reachStar q u k := by
  rw [reachStarSubmodule, Submodule.mem_sup, mem_reachStar]
  constructor
  · rintro ⟨y, ⟨A, hA, rfl⟩, z, ⟨B, hB, rfl⟩, rfl⟩
    exact ⟨A, hA, B, hB, rfl⟩
  · rintro ⟨A, hA, B, hB, rfl⟩
    exact ⟨DopStar q u 1 A, ⟨A, hA, rfl⟩, elemSymm L 1 * B, ⟨B, hB, rfl⟩, rfl⟩

/-- **One starred step spans a subspace.** The set `G_k` is a
`𝕜`-subspace of `Λ`: it is the carrier of `HJO.Sym.reachStarSubmodule`. -/
@[hjo "lem_ght_reach_star_subspace"]
theorem coe_reachStarSubmodule (q u : L) (k : ℕ) :
    (reachStarSubmodule q u k : Set (Lambda L)) = reachStar q u k :=
  Set.ext fun _ => mem_reachStarSubmodule_iff

/-- `HJO.Sym.coe_reachStarSubmodule` in its usual phrasing: there is a `𝕜`-subspace of `Λ`
whose elements are exactly the elements of `G_k`. -/
@[hjo "lem_ght_reach_star_subspace"]
theorem exists_submodule_coe_eq_reachStar (q u : L) (k : ℕ) :
    ∃ W : Submodule L (Lambda L), (W : Set (Lambda L)) = reachStar q u k :=
  ⟨reachStarSubmodule q u k, coe_reachStarSubmodule q u k⟩

end ReachStarSubspace

/-! ### A starred operator of any index is one starred step -/

section DopStarReach

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-- **`HJO.Sym.dopStar_mem_reachStar` in the form its induction runs in.** For `g ∈ Λ_c`,
`D*_{b+1}g ∈ G_{b+1+c}`. The conditions `1 ≤ a ≤ k` and `g ∈ Λ_{k-a}` are `a = b + 1` and
`k = a + c`, which is what keeps the statement free of truncated subtraction.

Induction on `b`. At `b = 0` the element is `D*_1g + e₁·0` with `g ∈ Λ_c = Λ_{(1+c)-1}`. At `b+1`,
`HJO.Sym.dopStar_elemSymm_one_mul` at index `b+1` gives
`M̃ D*_{b+2}g = e₁D*_{b+1}g - D*_{b+1}(e₁g)`; the second term is in `G` by the inductive hypothesis
applied to `e₁g ∈ Λ_{1+c}`, the first because `D*_{b+1}g ∈ Λ_{c+(b+1)}` by
`HJO.Sym.dopStar_mem_lambdaComp`, and `M̃ ≠ 0` divides out. -/
theorem dopStar_succ_mem_reachStar (hM : paramProduct q u ≠ 0) :
    ∀ (b c : ℕ) (g : Lambda L), g ∈ LambdaComp L c →
      DopStar q u (b + 1) g ∈ reachStar q u (b + 1 + c) := by
  intro b
  induction b with
  | zero =>
    intro c g hg
    refine ⟨g, ?_, 0, Submodule.zero_mem _, by rw [mul_zero, add_zero]⟩
    rwa [show 0 + 1 + c - 1 = c from by omega]
  | succ b ih =>
    intro c g hg
    have hMt : paramProduct q⁻¹ u⁻¹ ≠ 0 := paramProduct_inv_ne_zero hM
    have hg1 : elemSymm L 1 * g ∈ LambdaComp L (1 + c) :=
      mul_mem_lambdaComp (elemSymm_mem_lambdaComp L 1) hg
    have h1 : DopStar q u (b + 1) (elemSymm L 1 * g)
        ∈ reachStarSubmodule q u (b + 1 + 1 + c) := by
      have h := ih (1 + c) _ hg1
      rw [show b + 1 + (1 + c) = b + 1 + 1 + c from by omega] at h
      exact mem_reachStarSubmodule_iff.2 h
    have h2 : elemSymm L 1 * DopStar q u (b + 1) g
        ∈ reachStarSubmodule q u (b + 1 + 1 + c) := by
      refine mem_reachStarSubmodule_iff.2 ⟨0, Submodule.zero_mem _, DopStar q u (b + 1) g, ?_, ?_⟩
      · have h := dopStar_mem_lambdaComp q u (b + 1) hg
        rwa [show c + (b + 1) = b + 1 + 1 + c - 1 from by omega] at h
      · rw [map_zero, zero_add]
    have hsub := Submodule.sub_mem _ h2 h1
    rw [dopStar_elemSymm_one_mul q u (b + 1) g, sub_sub_cancel] at hsub
    have := Submodule.smul_mem _ (paramProduct q⁻¹ u⁻¹)⁻¹ hsub
    rw [inv_smul_smul₀ hMt] at this
    exact mem_reachStarSubmodule_iff.1 this

/-- **A starred operator of any index is one starred step.** For `k ≥ 1`,
`1 ≤ a ≤ k` and `g ∈ Λ_{k-a}`, the element `D*_ag` lies in `G_k`.

This is `HJO.Sym.dopStar_succ_mem_reachStar` read at `a = b + 1` and `k = a + (k - a)`; the
hypothesis `1 ≤ a` is what makes that reading possible and `a ≤ k` is what makes the truncated
`k - a` the true difference. The side condition `M ≠ 0` is discussed in the module docstring. -/
@[hjo "lem_ght_dopstar_reach"]
theorem dopStar_mem_reachStar (hM : paramProduct q u ≠ 0) {k a : ℕ} (ha : 1 ≤ a) (hak : a ≤ k)
    {g : Lambda L} (hg : g ∈ LambdaComp L (k - a)) : DopStar q u a g ∈ reachStar q u k := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  have h := dopStar_succ_mem_reachStar hM b (k - (b + 1)) g hg
  rwa [show b + 1 + (k - (b + 1)) = k from by omega] at h

end DopStarReach

/-! ### A complete homogeneous multiple is one starred step -/

section HsymmReach

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-- **`HJO.Sym.completeHomog_mul_mem_reachStar` in the form its induction runs in.** For `g ∈ Λ_c`,
`h_{e+1} g ∈ G_{e+1+c}`. The conditions `1 ≤ b ≤ k` and `h ∈ Λ_{k-b}` are `b = e + 1` and
`k = b + c`.

Strong induction on `c`, the induction on `k - b`. The expansion
`D*_{e+1}g = ∑_{r=0}^{c}g*_{[r]}h_{r+e+1}` has `g h_{e+1}` as its `r = 0` term by
`HJO.Sym.shiftStarCoeff_zero`, so `h_{e+1}g = D*_{e+1}g - ∑_{r=1}^{c}g*_{[r]}h_{r+e+1}`. The first
term is in `G` by `HJO.Sym.dopStar_mem_reachStar`; in the `r`-th remaining term `g*_{[r]} ∈ Λ_{c-r}`
with `c - r < c`, so the inductive hypothesis applies at the larger index `r + e + 1`. -/
theorem completeHomog_mul_mem_reachStar_add (hM : paramProduct q u ≠ 0) :
    ∀ (c e : ℕ) (g : Lambda L), g ∈ LambdaComp L c →
      completeHomog L (e + 1) * g ∈ reachStar q u (e + 1 + c) := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro e g hg
    have hexp := dopStar_eq_sum_range q u (e + 1) g (N := c + 1)
      fun r hr => shiftStarCoeff_eq_zero_of_lt q u hg (by omega)
    rw [Finset.sum_range_succ', shiftStarCoeff_zero] at hexp
    have hD : DopStar q u (e + 1) g ∈ reachStarSubmodule q u (e + 1 + c) :=
      mem_reachStarSubmodule_iff.2 (dopStar_succ_mem_reachStar hM e c g hg)
    have hrest : ∀ r ∈ range c,
        shiftStarCoeff q u g (r + 1) * completeHomog L (r + 1 + (e + 1))
          ∈ reachStarSubmodule q u (e + 1 + c) := by
      intro r hr
      have hrc : r + 1 ≤ c := by
        have := Finset.mem_range.1 hr
        omega
      have hcoeff : shiftStarCoeff q u g (r + 1) ∈ LambdaComp L (c - (r + 1)) :=
        shiftStarCoeff_mem_lambdaComp q u hg hrc
      have h := ih (c - (r + 1)) (by omega) (r + 1 + e) _ hcoeff
      rw [show r + 1 + e + 1 + (c - (r + 1)) = e + 1 + c from by omega] at h
      have hcomm : completeHomog L (r + 1 + e + 1) * shiftStarCoeff q u g (r + 1)
          = shiftStarCoeff q u g (r + 1) * completeHomog L (r + 1 + (e + 1)) := by
        rw [mul_comm, show r + 1 + e + 1 = r + 1 + (e + 1) from by omega]
      rw [hcomm] at h
      exact mem_reachStarSubmodule_iff.2 h
    have hsum : (∑ r ∈ range c,
        shiftStarCoeff q u g (r + 1) * completeHomog L (r + 1 + (e + 1)))
          ∈ reachStarSubmodule q u (e + 1 + c) := Submodule.sum_mem _ hrest
    have hmem : g * completeHomog L (0 + (e + 1)) ∈ reachStarSubmodule q u (e + 1 + c) := by
      have h := Submodule.sub_mem _ hD hsum
      rwa [hexp, add_sub_cancel_left] at h
    rw [Nat.zero_add, mul_comm] at hmem
    exact mem_reachStarSubmodule_iff.1 hmem

/-- **A complete homogeneous multiple is one starred step.** For `k ≥ 1`,
`1 ≤ b ≤ k` and `h ∈ Λ_{k-b}`, the element `h_b h` lies in `G_k`. -/
@[hjo "lem_ght_hsymm_reach"]
theorem completeHomog_mul_mem_reachStar (hM : paramProduct q u ≠ 0) {k b : ℕ} (hb : 1 ≤ b)
    (hbk : b ≤ k) {h : Lambda L} (hh : h ∈ LambdaComp L (k - b)) :
    completeHomog L b * h ∈ reachStar q u k := by
  obtain ⟨e, rfl⟩ : ∃ e, b = e + 1 := ⟨b - 1, by omega⟩
  have hmem := completeHomog_mul_mem_reachStar_add hM (k - (e + 1)) e h hh
  rwa [show e + 1 + (k - (e + 1)) = k from by omega] at hmem

end HsymmReach

/-! ### One starred step reaches every degree, and reachability from the unit -/

section Reachable

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-- **`HJO.Sym.exists_mem_reachStar` as an inclusion of submodules**, stated at `k = m + 1` so that
the piece `Λ_{k-1}` is `Λ_m` with nothing truncated.

`Λ_{m+1}` is the span of the `h_α` over the compositions `α` of `m+1` by
`HJO.Sym.lambdaComp_eq_completeHomogCompSpan`, and such an `α` is nonempty, so it is `(e+1) :: β`;
then `h_α = h_{e+1}h_β` with `h_β ∈ Λ_{β.sum}` and `e + 1 + β.sum = m + 1`, so
`HJO.Sym.completeHomog_mul_mem_reachStar` puts it in `G_{m+1}`. -/
theorem lambdaComp_le_reachStarSubmodule (hM : paramProduct q u ≠ 0) (m : ℕ) :
    LambdaComp L (m + 1) ≤ reachStarSubmodule q u (m + 1) := by
  rw [lambdaComp_eq_completeHomogCompSpan, completeHomogCompSpan]
  refine Submodule.span_le.2 ?_
  rintro x ⟨α, hα, hαs, rfl⟩
  match α with
  | [] => exact absurd hαs (by rw [List.sum_nil]; omega)
  | a :: β =>
    obtain ⟨e, rfl⟩ : ∃ e, a = e + 1 := ⟨a - 1, by
      have := hα a (List.mem_cons_self ..)
      omega⟩
    rw [List.sum_cons] at hαs
    rw [SetLike.mem_coe, completeHomogComp_cons]
    refine mem_reachStarSubmodule_iff.2 ?_
    have h := completeHomog_mul_mem_reachStar_add hM β.sum e _
      (completeHomogComp_mem_lambdaComp L β)
    rwa [hαs] at h

/-- **Garsia--Haiman--Tesler, one starred step reaches every degree.** For
`k ≥ 1` and `f ∈ Λ_k` there are `A, B ∈ Λ_{k-1}` with `f = D*_1A + e₁B`.

Stated at `k = m + 1`: `Λ_{k-1}` is then `Λ_m`, and no hypothesis sits at an index where `ℕ`
truncation would empty it. -/
@[hjo "lem_ght_thm21_star"]
theorem exists_mem_reachStar (hM : paramProduct q u ≠ 0) {m : ℕ} {f : Lambda L}
    (hf : f ∈ LambdaComp L (m + 1)) :
    ∃ A ∈ LambdaComp L m, ∃ B ∈ LambdaComp L m, f = DopStar q u 1 A + elemSymm L 1 * B := by
  have h := mem_reachStarSubmodule_iff.1 (lambdaComp_le_reachStarSubmodule hM m hf)
  rwa [mem_reachStar, Nat.add_sub_cancel] at h

/-- **Garsia--Haiman--Tesler, reachability from the unit.** The only
`𝕜`-subspace of `Λ` that contains `1`, is closed under multiplication by `e₁` and is closed under
`D*_1` is `Λ` itself.

Induction on the degree: `Λ_0` is the `𝕜`-multiples of `1` by `HJO.Sym.lambdaComp_zero`, and
at `d = m + 1` every `f ∈ Λ_d` is `D*_1A + e₁B` with `A, B ∈ Λ_m ⊆ W` by
`HJO.Sym.exists_mem_reachStar`, so the two closure hypotheses put `f` in `W`. Every element of `Λ`
is a finite sum of monomials, each homogeneous of its own weighted degree, so `W` is everything. -/
@[hjo "lem_cm_reachable"]
theorem eq_top_of_one_mem_of_closed (hM : paramProduct q u ≠ 0) {W : Submodule L (Lambda L)}
    (hone : (1 : Lambda L) ∈ W) (helem : ∀ f ∈ W, elemSymm L 1 * f ∈ W)
    (hdop : ∀ f ∈ W, DopStar q u 1 f ∈ W) : W = ⊤ := by
  have key : ∀ d : ℕ, LambdaComp L d ≤ W := by
    intro d
    induction d with
    | zero =>
      rw [lambdaComp_zero]
      refine Submodule.span_le.2 ?_
      rintro x hx
      rw [Set.mem_singleton_iff] at hx
      exact hx ▸ hone
    | succ m ih =>
      intro f hf
      obtain ⟨A, hA, B, hB, rfl⟩ := exists_mem_reachStar hM hf
      exact Submodule.add_mem _ (hdop A (ih hA)) (helem B (ih hB))
  refine top_unique fun f _ => ?_
  rw [f.as_sum]
  refine Submodule.sum_mem _ fun e _ => ?_
  exact key _ (mem_lambdaComp.2
    (MvPolynomial.isWeightedHomogeneous_monomial _ e (MvPolynomial.coeff e f) rfl))

end Reachable

end HJO.Sym
