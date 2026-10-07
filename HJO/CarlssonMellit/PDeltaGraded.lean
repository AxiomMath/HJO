/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.DiffDivides
public import HJO.CarlssonMellit.PDelta
public meta import HJO.Attr

/-! # The swapping operator is defined on the graded part

The swapping operator `Δ_i` of `HJO.Sym.pdelta` divides by `y_{i+1} - y_i`, which is invertible in
the coefficient field `𝕂(y₁, …, y_k)`; the lowering step of the Carlsson--Mellit analysis needs the
*same formula read in the free variables*, dividing by `x_{r+1} - x_r`, and there the divisor is not
invertible. That division is legitimate on the graded part `P^gr_{k,d}`, and that is what is proved
here: the numerator

`(q - 1)x_{r+1}G + (x_{r+1} - qx_r)ŝ_{x_r,x_{r+1}}(G)`

vanishes on identifying `x_r` with `x_{r+1}`, so by
`HJO.Sym.existsUnique_mem_pGraded_eq_X_sub_X_mul` it is `x_{r+1} - x_r` times a unique element of
`P^gr_{k,d}`, and that element is the value of the operator.

## Main definitions

* `HJO.Sym.xswap`: the interchange `ŝ_{x_r,x_s}` of two free variables, an algebra automorphism of
  `P°_k` over the coefficient field. Unlike the interchange of two *auxiliary* variables, this one
  is a genuine renaming of the power-series variables.
* `HJO.Sym.xdeltaNum`: the numerator of the swapping operator read in the free variables.

## Main results

* `HJO.Sym.rename_collapseVar_xdeltaNum`: the numerator vanishes on the diagonal. This is the
  computation of `HJO.Sym.map_numerator_eq_zero` with `x_r` and `x_{r+1}` in place of `y_i` and
  `y_{i+1}`, which uses nothing about the two variables beyond their being interchanged.
* `HJO.Sym.existsUnique_mem_pGraded_xdeltaNum_eq`, the well-definedness of
  `Δ_{x_r,x_{r+1}}` on `P^gr_{k,d}`.
* `HJO.Sym.xdelta`: the operator itself, the element the previous result produces.

## Implementation notes

*Three natural hypotheses are dead and are dropped.* One would state this under `k ≥ 2`, `r ≥ 1` and
`d ≥ 1`. Nothing here reads the level, so `k ≥ 2` — which belongs to the *auxiliary* operator, where
there must be a variable `y_{i+1}` — is not needed; the free variables are indexed from `0`, so the
`r ≥ 1` is every `r : ℕ`; and `d ≥ 1` is dead because what
`HJO.Sym.existsUnique_mem_pGraded_eq_X_sub_X_mul` is applied at is the numerator's degree `d + 1`,
which is at least `1` for every `d`. Dropping redundant hypotheses only generalises the statement.

*`Δ_{x_r,x_{r+1}}` is given a definition of its own here.* `HJO.Sym.pdelta` defines `Δ_i` for
`1 ≤ i ≤ k-1` in the *auxiliary* variables only, and `Δ_{x_r,x_{r+1}}` is "the formula of
`HJO.Sym.pdelta` read in the free variables". The two operators are not the same declaration and
cannot be: `pdelta` divides by an invertible element of the coefficient field and is defined on all
of `P°_k`, while this one divides by a non-unit and is defined only on the graded part, its very
existence being the content of this lemma. So `HJO.Sym.xdelta` is a separate declaration:
identifying it with `HJO.Sym.pdelta` would put two different operators under one name.

*The interchange of two free variables is `MvPowerSeries.rename` along a transposition*, hence an
algebra automorphism over the coefficient field, where the interchange of two auxiliary variables
(`HJO.Sym.pswap`) acts on the coefficients instead. The composite of the collapse with the
transposition is the collapse again, which is why the numerator's two summands cancel.

*The numerator is written with `C q - 1` and not with `C (q - 1)`.* Both are the same series; the
first form lets `ring` finish the vanishing computation without unfolding `MvPowerSeries.C`.

*Membership in `HJO.Sym.pGraded` is a `Pi` type behind a reducible definition, and closing a goal
with `exact` on a hypothesis of exactly that type fails.* `pGraded K k d` has carrier
`{G | MvPowerSeries.IsHomogeneous G d}`, and `IsHomogeneous` unfolds to
`∀ ⦃α⦄, coeff α G ≠ 0 → weight 1 α = d`; when `exact h` whnfs the two sides it inserts that
strict-implicit argument into `h` and then cannot match. `assumption`, which uses plain
`isDefEq`, closes the same goal. The `have`s below therefore carry explicit types and the last
step is `assumption`.

## References

The lemma `HJO.Sym.existsUnique_mem_pGraded_xdeltaNum_eq`, using `HJO.Sym.pdelta`,
`HJO.Sym.pGraded`, `HJO.Sym.map_numerator_eq_zero` and
`HJO.Sym.existsUnique_mem_pGraded_eq_X_sub_X_mul`; this is the statement that lets the lowering
step be decomposed. E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, J.
Amer. Math. Soc. **31** (2018) 661--697, Section 4.
-/

@[expose] public section

namespace HJO.Sym

variable {K : Type*} [CommRing K] {k d : ℕ}

/-! ### Homogeneity of the building blocks -/

/-- A constant series is homogeneous of degree `0`. -/
theorem C_mem_pGraded (a : AuxFrac K k) :
    (MvPowerSeries.C a : AuxAlphabetSeriesFrac K k) ∈ pGraded K k 0 := by
  classical
  refine mem_pGraded_iff.2 fun α hα => ?_
  rcases eq_or_ne α 0 with rfl | h
  · exact map_zero Finsupp.degree
  · exact absurd (by rw [MvPowerSeries.coeff_C, ite_eq_right h]) hα

/-- A free variable is homogeneous of degree `1`. -/
theorem X_mem_pGraded (K : Type*) [CommRing K] (k l : ℕ) :
    (MvPowerSeries.X l : AuxAlphabetSeriesFrac K k) ∈ pGraded K k 1 := by
  classical
  refine mem_pGraded_iff.2 fun α hα => ?_
  rcases eq_or_ne α (Finsupp.single l 1) with rfl | h
  · exact Finsupp.degree_single l 1
  · exact absurd (by rw [MvPowerSeries.coeff_X, ite_eq_right h]) hα

/-- The product of two graded series is graded, elementwise: the `≤` form
`HJO.Sym.pGraded_mul_pGraded_le` read at a pair of elements. -/
theorem mul_mem_pGraded {a b : AuxAlphabetSeriesFrac K k} {m n : ℕ} (ha : a ∈ pGraded K k m)
    (hb : b ∈ pGraded K k n) : a * b ∈ pGraded K k (m + n) :=
  pGraded_mul_pGraded_le K k m n (Submodule.mul_mem_mul ha hb)

/-- The difference of two series of one free-variable degree has that degree. -/
theorem sub_mem_pGraded {a b : AuxAlphabetSeriesFrac K k} {m : ℕ} (ha : a ∈ pGraded K k m)
    (hb : b ∈ pGraded K k m) : a - b ∈ pGraded K k m :=
  Submodule.sub_mem (pGraded K k m) ha hb

/-- Renaming the free variables preserves the free-variable degree: a monomial and its relabelling
have the same letters counted with multiplicity. -/
theorem rename_mem_pGraded {f : ℕ → ℕ} [Filter.TendstoCofinite f]
    {G : AuxAlphabetSeriesFrac K k} (hG : G ∈ pGraded K k d) :
    MvPowerSeries.rename f G ∈ pGraded K k d := by
  classical
  refine isHomogeneous_of_coeff_eq_zero fun α hα => ?_
  rw [MvPowerSeries.coeff_rename]
  refine Finset.sum_eq_zero fun y hy => coeff_eq_zero_of_mem_pGraded hG ?_
  rw [Set.Finite.mem_toFinset] at hy
  have hy' : Finsupp.mapDomain f y = α := hy
  rw [← hy', Finsupp.degree_mapDomain] at hα
  exact hα

/-! ### Interchanging two free variables -/

/-- **The interchange of two free variables** `ŝ_{x_r,x_s}`: the algebra automorphism of `P°_k`
renaming the power-series variables along the transposition of `r` and `s`. Where the interchange
`HJO.Sym.pswap` of two *auxiliary* variables acts on the coefficients, this one acts on the
variables, and it is an automorphism over the coefficient field. -/
noncomputable def xswap (K : Type*) [CommRing K] (k r s : ℕ) :
    AuxAlphabetSeriesFrac K k →ₐ[AuxFrac K k] AuxAlphabetSeriesFrac K k :=
  MvPowerSeries.rename (Equiv.swap r s)

theorem xswap_apply (r s : ℕ) (G : AuxAlphabetSeriesFrac K k) :
    xswap K k r s G = MvPowerSeries.rename (Equiv.swap r s) G :=
  rfl

@[simp]
theorem xswap_X (r s l : ℕ) :
    xswap K k r s (MvPowerSeries.X l) = MvPowerSeries.X (Equiv.swap r s l) :=
  MvPowerSeries.rename_X _ _

@[simp]
theorem xswap_C (r s : ℕ) (a : AuxFrac K k) :
    xswap K k r s (MvPowerSeries.C a : AuxAlphabetSeriesFrac K k) = MvPowerSeries.C a :=
  MvPowerSeries.rename_C _ _

/-- The interchange preserves the free-variable grading. -/
theorem xswap_mem_pGraded (r s : ℕ) {G : AuxAlphabetSeriesFrac K k} (hG : G ∈ pGraded K k d) :
    xswap K k r s G ∈ pGraded K k d :=
  rename_mem_pGraded hG

/-- **Substituting `x_{r+1}` for `x_r` absorbs the interchange of `x_r` and `x_{r+1}`**: both
variables end up as `x_{r+1}` either way. This is what makes the numerator's two summands cancel. -/
theorem collapseVar_comp_swap (r : ℕ) :
    collapseVar r (r + 1) ∘ (Equiv.swap r (r + 1) : ℕ → ℕ) = collapseVar r (r + 1) := by
  funext l
  by_cases h1 : l = r
  · subst h1
    rw [Function.comp_apply, Equiv.swap_apply_left, collapseVar_right, collapseVar_self]
  by_cases h2 : l = r + 1
  · subst h2
    rw [Function.comp_apply, Equiv.swap_apply_right, collapseVar_self, collapseVar_right]
  · rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h1 h2]

/-- Substituting `x_{r+1}` for `x_r` after the interchange is substituting `x_{r+1}` for `x_r`. -/
theorem rename_collapseVar_xswap (r : ℕ) (G : AuxAlphabetSeriesFrac K k) :
    MvPowerSeries.rename (collapseVar r (r + 1)) (xswap K k r (r + 1) G)
      = MvPowerSeries.rename (collapseVar r (r + 1)) G := by
  rw [xswap_apply, MvPowerSeries.rename_rename]
  simp only [collapseVar_comp_swap]

/-! ### The numerator of the swapping operator in the free variables -/

/-- **The numerator of the swapping operator read in the free variables**:
`(q - 1)x_{r+1}G + (x_{r+1} - qx_r)ŝ_{x_r,x_{r+1}}(G)`, the formula of `HJO.Sym.pdelta` with the
two letters `x_r`, `x_{r+1}` in place of the two auxiliary variables. -/
noncomputable def xdeltaNum (q : K) (r : ℕ) (G : AuxAlphabetSeriesFrac K k) :
    AuxAlphabetSeriesFrac K k :=
  (MvPowerSeries.C (scalarFrac K q) - 1) * MvPowerSeries.X (r + 1) * G
    + (MvPowerSeries.X (r + 1) - MvPowerSeries.C (scalarFrac K q) * MvPowerSeries.X r)
      * xswap K k r (r + 1) G

theorem xdeltaNum_apply (q : K) (r : ℕ) (G : AuxAlphabetSeriesFrac K k) :
    xdeltaNum q r G = (MvPowerSeries.C (scalarFrac K q) - 1) * MvPowerSeries.X (r + 1) * G
      + (MvPowerSeries.X (r + 1) - MvPowerSeries.C (scalarFrac K q) * MvPowerSeries.X r)
        * xswap K k r (r + 1) G :=
  rfl

/-- **The numerator is homogeneous one degree higher**: it is a sum of products of `G` with one
letter. -/
theorem xdeltaNum_mem_pGraded (q : K) (r : ℕ) {G : AuxAlphabetSeriesFrac K k}
    (hG : G ∈ pGraded K k d) : xdeltaNum q r G ∈ pGraded K k (d + 1) := by
  have h0 : (MvPowerSeries.C (scalarFrac K q) - 1 : AuxAlphabetSeriesFrac K k) ∈ pGraded K k 0 :=
    sub_mem_pGraded (C_mem_pGraded (scalarFrac K q)) (one_mem_pGraded K k)
  have hCX : (MvPowerSeries.C (scalarFrac K q) * MvPowerSeries.X r :
      AuxAlphabetSeriesFrac K k) ∈ pGraded K k 1 :=
    mul_mem_pGraded (C_mem_pGraded (scalarFrac K q)) (X_mem_pGraded K k r)
  have hfac : (MvPowerSeries.X (r + 1) - MvPowerSeries.C (scalarFrac K q) * MvPowerSeries.X r :
      AuxAlphabetSeriesFrac K k) ∈ pGraded K k 1 :=
    sub_mem_pGraded (X_mem_pGraded K k (r + 1)) hCX
  have ht1 : (MvPowerSeries.C (scalarFrac K q) - 1) * MvPowerSeries.X (r + 1) * G
      ∈ pGraded K k (d + 1) := by
    have h : (MvPowerSeries.C (scalarFrac K q) - 1) * MvPowerSeries.X (r + 1) * G
        ∈ pGraded K k (0 + 1 + d) :=
      mul_mem_pGraded (mul_mem_pGraded h0 (X_mem_pGraded K k (r + 1))) hG
    rwa [show 0 + 1 + d = d + 1 from by omega] at h
  have ht2 : (MvPowerSeries.X (r + 1) - MvPowerSeries.C (scalarFrac K q) * MvPowerSeries.X r)
      * xswap K k r (r + 1) G ∈ pGraded K k (d + 1) := by
    have h : (MvPowerSeries.X (r + 1) - MvPowerSeries.C (scalarFrac K q) * MvPowerSeries.X r)
        * xswap K k r (r + 1) G ∈ pGraded K k (1 + d) :=
      mul_mem_pGraded hfac (xswap_mem_pGraded r (r + 1) hG)
    rwa [show 1 + d = d + 1 from by omega] at h
  have hsum : (MvPowerSeries.C (scalarFrac K q) - 1) * MvPowerSeries.X (r + 1) * G
      + (MvPowerSeries.X (r + 1) - MvPowerSeries.C (scalarFrac K q) * MvPowerSeries.X r)
        * xswap K k r (r + 1) G ∈ pGraded K k (d + 1) :=
    Submodule.add_mem (pGraded K k (d + 1)) ht1 ht2
  rw [xdeltaNum_apply]
  assumption

/-- **The numerator vanishes on the diagonal**: substituting `x_{r+1}` for `x_r` carries the
interchange to the identity, so the numerator becomes `(q-1)x_{r+1}\bar G - (q-1)x_{r+1}\bar G = 0`.
This is the computation of `HJO.Sym.map_numerator_eq_zero`, which uses nothing about the two
variables beyond their being interchanged by the swap. -/
theorem rename_collapseVar_xdeltaNum (q : K) (r : ℕ) (G : AuxAlphabetSeriesFrac K k) :
    MvPowerSeries.rename (collapseVar r (r + 1)) (xdeltaNum q r G) = 0 := by
  rw [xdeltaNum_apply]
  simp only [map_add, map_mul, map_sub, map_one, MvPowerSeries.rename_C, MvPowerSeries.rename_X,
    rename_collapseVar_xswap, collapseVar_self, collapseVar_right]
  ring

/-! ### The swapping operator is defined on the graded part -/

/-- **The swapping operator is defined on the graded part.** For `G` in the graded part
`P^gr_{k,d}` of `P°_k` there is exactly one `H ∈ P^gr_{k,d}` with
`(q-1)x_{r+1}G + (x_{r+1} - qx_r)ŝ_{x_r,x_{r+1}}(G) = (x_{r+1} - x_r)H`; that `H` is
`Δ_{x_r,x_{r+1}}(G)`.

The division is legitimate not because the divisor is invertible — it is not — but because the
numerator vanishes on the diagonal, which is `HJO.Sym.rename_collapseVar_xdeltaNum`. The natural
hypotheses `k ≥ 2`, `r ≥ 1` and `d ≥ 1` are all dead: nothing reads the level, the free variables
are indexed from `0`, and what `HJO.Sym.existsUnique_mem_pGraded_eq_X_sub_X_mul` is applied at is
the numerator's degree `d + 1`, which is at least `1` for every `d`. -/
@[hjo "lem_cm_pdelta_graded"]
theorem existsUnique_mem_pGraded_xdeltaNum_eq [IsDomain K] (q : K) (r : ℕ)
    {G : AuxAlphabetSeriesFrac K k}
    (hG : G ∈ pGraded K k d) :
    ∃! H : AuxAlphabetSeriesFrac K k, H ∈ pGraded K k d ∧
      xdeltaNum q r G = (MvPowerSeries.X (r + 1) - MvPowerSeries.X r) * H :=
  existsUnique_mem_pGraded_eq_X_sub_X_mul (xdeltaNum_mem_pGraded q r hG)
    (Nat.ne_of_lt (Nat.lt_succ_self r)) (rename_collapseVar_xdeltaNum q r G)

/-- **The swapping operator `Δ_{x_r,x_{r+1}}` on the graded part**: the quotient that
`HJO.Sym.existsUnique_mem_pGraded_xdeltaNum_eq` produces, which is
`HJO.Sym.diffQuot r (r+1) (xdeltaNum q r G)`. It is not `HJO.Sym.pdelta`: the operator is introduced
in `HJO.Sym.existsUnique_mem_pGraded_xdeltaNum_eq` as the formula of `HJO.Sym.pdelta` read in the
free variables, but `HJO.Sym.pdelta` is the operator in the *auxiliary* variables and is a different
declaration — that one divides by a unit of the coefficient field and is total on `P°_k`, this one
divides by a non-unit and exists only on the graded part. -/
noncomputable def xdelta (q : K) (r : ℕ) (G : AuxAlphabetSeriesFrac K k) :
    AuxAlphabetSeriesFrac K k :=
  diffQuot r (r + 1) (xdeltaNum q r G)

/-- The operator lands in the graded part it came from. -/
theorem xdelta_mem_pGraded (q : K) (r : ℕ) {G : AuxAlphabetSeriesFrac K k}
    (hG : G ∈ pGraded K k d) : xdelta q r G ∈ pGraded K k d :=
  isHomogeneous_diffQuot (Nat.ne_of_lt (Nat.lt_succ_self r)) (xdeltaNum_mem_pGraded q r hG)

/-- The operator solves the equation that defines it. -/
theorem xdeltaNum_eq_X_sub_X_mul_xdelta (q : K) (r : ℕ) (G : AuxAlphabetSeriesFrac K k) :
    xdeltaNum q r G = (MvPowerSeries.X (r + 1) - MvPowerSeries.X r) * xdelta q r G :=
  (MvPowerSeries.ext fun α =>
    coeff_X_sub_X_mul_diffQuot (Nat.ne_of_lt (Nat.lt_succ_self r))
      (rename_collapseVar_xdeltaNum q r G) α).symm

end HJO.Sym
