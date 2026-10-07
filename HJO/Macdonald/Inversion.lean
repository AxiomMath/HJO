/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.RingTheory.LaurentSeries
public import HJO.Macdonald.Vocabulary
public import HJO.Symmetric.SymmetricFunctions
public meta import HJO.Attr

/-! # The inversion of the symmetric functions, and a Macdonald eigenbasis

Garsia--Haiman--Tesler's operator `↓`, written `↓F[X;q,u] = ω F[X;1/q,1/u]`: the ring endomorphism
of `Λ` whose restriction to the coefficients is the parameter inversion `ι` and which sends `p_k`
to `(-1)^{k-1} p_k`, the sign being their `ω`. It is **not** `𝕜`-linear -- a ring endomorphism
restricting to `ι` on `𝕜` satisfies `↓(c f) = ι(c) ↓f` instead (`inversion_smul`) -- which is why
it is a `RingHom` and not a `Module.End`.

Its companion `↓_z` acts on the series in the extraction variable: `Λ[z⁻¹][[z]]`, the formal series
`F = ∑_{n ≥ -N} F_n z^n` with `N ≥ 0` and every `F_n ∈ Λ`, which is Mathlib's
`LaurentSeries (Lambda K)` -- a `HahnSeries ℤ`, whose support condition on `ℤ` is exactly
"bounded below". On such an `F`, `↓_z` applies `↓` to each coefficient and sends `z` to `-z`.

Finally a **Macdonald eigenbasis**: the three properties of Garsia--Haiman--Tesler's
`H̃_μ` that the conjugator argument consumes, with the inversion clause `↓H̃_μ = T_μ⁻¹ H̃_μ` in
place of the starred eigenvalue relation. It is a different predicate from
`IsModifiedMacdonaldFamily`, with three clauses rather than four, and the starred relation is
derived from it rather than assumed.

## Main definitions

* `HJO.Sym.inversion`: the operator `↓`.
* `HJO.Sym.inversionZ`: the operator `↓_z` on `Λ[z⁻¹][[z]]`.
* `HJO.Sym.IsMacdonaldEigenbasis`: the three clauses `(a)`, `(b)`, `(c)`.

## Implementation notes

The coefficient inversion `ι` is a **parameter**, an arbitrary ring endomorphism of the coefficient
ring, rather than the specific automorphism of `ℚ(q, u)`. Instantiating it at the automorphism
`HJO.Sym.paramQUInv` recovers the inversion `↓` of `q` and `u` verbatim; taking it as a
parameter is a generalisation, and it is what lets `↓` be defined without the field-of-fractions
machinery `HJO.Sym.paramQUInv` is built from.

`↓` sends the generator `i`, which stands for `p_{i+1}`, to `(-1)^i p_{i+1}`, matching
`(-1)^{k-1} p_k` at `k = i + 1`.

The sign of `↓_z` is written with `Int.negOnePow`, whose additivity (`Int.negOnePow_add`) is exactly
what makes `↓_z` multiplicative: the sign attached to `z^n` splits along `n = i + j` over the
antidiagonal of the Hahn-series product.

## References

Definitions `HJO.Sym.inversion`, `HJO.Sym.inversionZ` and
`HJO.Sym.IsMacdonaldEigenbasis`. The reference is A. M. Garsia, M. Haiman and G. Tesler, *Explicit
plethystic formulas for Macdonald (q,t)-Kostka coefficients*, Sém. Lothar. Combin. **42** (1999),
B42m, whose equation (1.13) introduces `↓`, whose equation (1.11) a) is clause `(b)` of a Macdonald
eigenbasis and whose equation (1.16) is clause `(c)`. The sources' `t` is written `u` here.
-/

@[expose] public section

namespace HJO.Sym

/-! ### The inversion of the symmetric functions -/

section Inversion

variable {K : Type*} [CommRing K]

/-- **The inversion `↓` of the symmetric functions**: the ring endomorphism of `Λ` whose
restriction to the coefficients is `ι` and which sends `p_k` to `(-1)^{k-1} p_k` for every
`k ≥ 1`.

This is Garsia--Haiman--Tesler's `↓F[X;q,u] = ω F[X;1/q,1/u]`: the parameter inversion contributes
`ι` and their `ω` contributes the sign. It is a ring endomorphism and **not** `𝕜`-linear; see
`inversion_smul`. Since `Λ` is a polynomial ring over the coefficients on the `p_k`, prescribing
the values on the coefficients and on the generators determines it uniquely. -/
@[hjo "def_ght2_inversion"]
noncomputable def inversion (ι : K →+* K) : Lambda K →+* Lambda K :=
  MvPolynomial.eval₂Hom ((MvPolynomial.C : K →+* Lambda K).comp ι)
    fun i => (-1 : Lambda K) ^ i * MvPolynomial.X i

@[simp]
theorem inversion_C (ι : K →+* K) (c : K) :
    inversion ι (MvPolynomial.C c) = MvPolynomial.C (ι c) := by
  rw [inversion, MvPolynomial.eval₂Hom_C, RingHom.coe_comp, Function.comp_apply]

@[simp]
theorem inversion_X (ι : K →+* K) (i : ℕ) :
    inversion ι (MvPolynomial.X i) = (-1 : Lambda K) ^ i * MvPolynomial.X i := by
  rw [inversion, MvPolynomial.eval₂Hom_X']

/-- The value of `↓` on the power sum `p_k`, for `k ≥ 1`: the sign `(-1)^{k-1}`. -/
theorem inversion_powerSum (ι : K →+* K) {k : ℕ} (hk : 0 < k) :
    inversion ι (powerSum K k) = (-1 : Lambda K) ^ (k - 1) * powerSum K k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h : powerSum K (j + 1) = MvPolynomial.X j := rfl
  rw [h, inversion_X, Nat.add_sub_cancel]

/-- `↓` is not `𝕜`-linear: a ring endomorphism restricting to `ι` on the coefficients satisfies
`↓(c f) = ι(c) ↓f`. -/
theorem inversion_smul (ι : K →+* K) (c : K) (f : Lambda K) :
    inversion ι (c • f) = ι c • inversion ι f := by
  rw [← MvPolynomial.C_mul', ← MvPolynomial.C_mul', map_mul, inversion_C]

end Inversion

/-! ### The inversion on series in the extraction variable -/

section InversionZ

variable {K : Type*} [CommRing K]

theorem negOnePow_cast_add (m n : ℤ) :
    ((Int.negOnePow (m + n) : ℤ) : Lambda K) =
      ((Int.negOnePow m : ℤ) : Lambda K) * ((Int.negOnePow n : ℤ) : Lambda K) := by
  rw [Int.negOnePow_add, Units.val_mul, Int.cast_mul]

/-- The coefficient of `z^n` in a Hahn-series product, read over the antidiagonal of any pair of
partially well-ordered sets containing the two supports. Mathlib relaxes one factor at a time
(`HahnSeries.coeff_mul_left'`, `HahnSeries.coeff_mul_right'`); this relaxes both at once, which is
what puts two such products over one index set. -/
theorem coeff_mul_of_subset {R : Type*} [CommRing R] {s t : Set ℤ}
    (hs : s.IsPWO) (ht : t.IsPWO) {x y : HahnSeries ℤ R} (hxs : x.support ⊆ s)
    (hyt : y.support ⊆ t) (a : ℤ) :
    (x * y).coeff a = ∑ ij ∈ Finset.antidiagonal hs ht a, x.coeff ij.1 * y.coeff ij.2 := by
  rw [HahnSeries.coeff_mul_left' hs hxs]
  refine Finset.sum_subset (Finset.antidiagonal_mono_right hyt) fun gh hgh hz => ?_
  have hy : y.coeff gh.2 = 0 := by
    by_contra h
    exact hz (Finset.mem_antidiagonal.2 ⟨(Finset.mem_antidiagonal.1 hgh).1,
      (HahnSeries.mem_support y gh.2).2 h, (Finset.mem_antidiagonal.1 hgh).2.2⟩)
  rw [hy, mul_zero]

theorem support_coeff_subset (ι : K →+* K) (F : LaurentSeries (Lambda K)) :
    (Function.support fun n => ((Int.negOnePow n : ℤ) : Lambda K) * inversion ι (F.coeff n)) ⊆
      F.support := by
  intro n hn
  simp only [Function.mem_support, ne_eq] at hn
  simp only [HahnSeries.mem_support, ne_eq]
  intro h
  rw [h, map_zero, mul_zero] at hn
  exact hn rfl

/-- The underlying map of `↓_z`: apply `↓` to each coefficient and send `z` to `-z`. The support
can only shrink, so the Hahn-series condition is inherited. -/
noncomputable def inversionZAux (ι : K →+* K) (F : LaurentSeries (Lambda K)) :
    LaurentSeries (Lambda K) where
  coeff n := ((Int.negOnePow n : ℤ) : Lambda K) * inversion ι (F.coeff n)
  isPWO_support' := F.isPWO_support.mono (support_coeff_subset ι F)

@[simp]
theorem coeff_inversionZAux (ι : K →+* K) (F : LaurentSeries (Lambda K)) (n : ℤ) :
    (inversionZAux ι F).coeff n =
      ((Int.negOnePow n : ℤ) : Lambda K) * inversion ι (F.coeff n) := rfl

theorem support_inversionZAux_subset (ι : K →+* K) (F : LaurentSeries (Lambda K)) :
    (inversionZAux ι F).support ⊆ F.support := support_coeff_subset ι F

/-- **The inversion `↓_z` on the series in the extraction variable**: the ring endomorphism of
`Λ[z⁻¹][[z]]` sending `F = ∑_{n ≥ -N} F_n z^n` to `∑_{n ≥ -N} (-1)^n (↓F_n) z^n`.

That is: apply `↓` to each coefficient and send `z` to `-z`. Its restriction to `Λ`, the series
with `F_n = 0` for `n ≠ 0`, is `↓`. -/
@[hjo "def_ght2_inversion_z"]
noncomputable def inversionZ (ι : K →+* K) :
    LaurentSeries (Lambda K) →+* LaurentSeries (Lambda K) where
  toFun := inversionZAux ι
  map_zero' := by
    refine HahnSeries.ext (funext fun n => ?_)
    simp
  map_one' := by
    refine HahnSeries.ext (funext fun n => ?_)
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp [HahnSeries.coeff_one, hn]
  map_add' F G := by
    refine HahnSeries.ext (funext fun n => ?_)
    simp [HahnSeries.coeff_add, mul_add]
  map_mul' F G := by
    refine HahnSeries.ext (funext fun n => ?_)
    rw [coeff_mul_of_subset F.isPWO_support G.isPWO_support
        (support_inversionZAux_subset ι F) (support_inversionZAux_subset ι G) n,
      coeff_inversionZAux, HahnSeries.coeff_mul, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ij hij => ?_
    have hn : ij.1 + ij.2 = n := (Finset.mem_antidiagonal.1 hij).2.2
    rw [coeff_inversionZAux, coeff_inversionZAux, map_mul, ← hn, negOnePow_cast_add]
    ring

@[simp]
theorem coeff_inversionZ (ι : K →+* K) (F : LaurentSeries (Lambda K)) (n : ℤ) :
    (inversionZ ι F).coeff n =
      ((Int.negOnePow n : ℤ) : Lambda K) * inversion ι (F.coeff n) := rfl

/-- The restriction of `↓_z` to `Λ` -- the series with `F_n = 0` for `n ≠ 0` -- is `↓`. -/
@[simp]
theorem inversionZ_C (ι : K →+* K) (f : Lambda K) :
    inversionZ ι (HahnSeries.C f) = HahnSeries.C (inversion ι f) := by
  refine HahnSeries.ext (funext fun n => ?_)
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simp [HahnSeries.C_apply, hn]

end InversionZ

/-! ### A Macdonald eigenbasis -/

section Eigenbasis

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- A **Macdonald eigenbasis** `(H̃_μ)`, indexed by the partitions: a `𝕜`-basis of `Λ`
(clause (a), the two fields `linearIndependent` and `span_eq_top`) which is an eigenbasis of the
basic operator `D_0` with eigenvalue `-(M B_μ - 1)` (clause (b)) and of the inversion `↓` with
eigenvalue `T_μ⁻¹` (clause (c)).

These are the three properties of Garsia--Haiman--Tesler's `H̃_μ` that the conjugator argument
consumes. Clause (c) has the role of a normalisation rather than of a further property: clauses
(a) and (b) leave one nonzero scalar per index free, and clause (c) is the clause that is not
invariant under such a rescaling.

This is a predicate on families, not a construction: nothing here asserts that such a family
exists. -/
@[hjo "def_ght2_eigenbasis"]
structure IsMacdonaldEigenbasis (ι : L →+* L) (q u : L) (H : YoungDiagram → Lambda L) : Prop where
  /-- Clause (a), first half: the family is `𝕜`-linearly independent. -/
  linearIndependent : LinearIndependent L H
  /-- Clause (a), second half: the family spans `Λ` over `𝕜`. -/
  span_eq_top : Submodule.span L (Set.range H) = ⊤
  /-- Clause (b): `D_0 H̃_μ = -(M B_μ - 1) H̃_μ`. -/
  dop_zero : ∀ μ : YoungDiagram,
    Dop q u 0 (H μ) = -(paramProduct q u * cellSum q u μ - 1) • H μ
  /-- Clause (c): `↓H̃_μ = T_μ⁻¹ H̃_μ`. -/
  inversion_apply : ∀ μ : YoungDiagram,
    inversion ι (H μ) = (cellProd q u μ)⁻¹ • H μ

/-- Clause (a) as the basis it is. -/
noncomputable def IsMacdonaldEigenbasis.basis {ι : L →+* L} {q u : L}
    {H : YoungDiagram → Lambda L} (h : IsMacdonaldEigenbasis ι q u H) :
    Module.Basis YoungDiagram L (Lambda L) :=
  Module.Basis.mk h.linearIndependent h.span_eq_top.ge

@[simp]
theorem IsMacdonaldEigenbasis.basis_apply {ι : L →+* L} {q u : L} {H : YoungDiagram → Lambda L}
    (h : IsMacdonaldEigenbasis ι q u H) (μ : YoungDiagram) : h.basis μ = H μ :=
  Module.Basis.mk_apply _ _ _

end Eigenbasis

end HJO.Sym
