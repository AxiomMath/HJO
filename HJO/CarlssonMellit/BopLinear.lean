/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.Bop
public import HJO.Collinear.DopStarPair
public import HJO.Shuffle.Grading
public meta import HJO.Attr

/-! # The Hall--Littlewood operators are linear, and their leading term

Two facts about the family `B_r` of `HJO.Sym.Bop` that the triangularity of a word of them rests
on: that each `B_r` is `𝕜`-linear, and that on the homogeneous component `Λ_n` the value `B_r f`
is `(-1)^r e_r f` plus a combination of the `e_s` with `s > r` whose cofactors sit in strictly
lower components.

## Main results

* `HJO.Sym.isLinearMap_bop`: `f ↦ B_r f` is `𝕜`-linear.
* `HJO.Sym.coeff_zero_plethHallLittlewood`: the displacement fixes an element modulo its own
  variable, `[w⁰] f[X - (q-1)/z] = f`.
* `HJO.Sym.bop_leading`: the leading term of `B_r` on `Λ_n`.

## Implementation notes

Linearity is not a computation here. `HJO.Sym.Bop q r` is built as a bundled
`Module.End K (Lambda K)` — the composite of the displacement `β`, which is a `K`-algebra
homomorphism, with the pairing `HJO.Sym.coeffPairing`, which is `K`-linear — so the
three linear factors are each discharged where the operator is defined, and the linearity
assertion is the unbundling `isLinearMap_bop`.

The leading-term lemma is the grading of the displacement, which the tree already has as
`HJO.Sym.plethShift_mem_polyComp`: for `f ∈ Λ_n` the coefficient of `wʲ` in `β f` lies in
`Λ_{n-j}`, read at an integer index so that the vanishing above `j = n` is the same statement
rather than a side condition. The cofactors `g_s` of the statement are those coefficients at
`j = s - r`, and the index set is `Finset.Icc (r+1) (r+n)`, on which `n + r - s` is an honest
subtraction; stating the membership as a `∀ s` over all of `ℕ` would read the truncated value
outside that window and say something different there.

## References

This file formalises the lemmas `HJO.Sym.isLinearMap_bop` and `HJO.Sym.bop_leading`.
-/

@[expose] public section

namespace HJO.Sym

variable {K : Type*} [CommRing K]

/-! ### The displacement fixes an element modulo its own variable -/

/-- **The constant coefficient of a displaced element is the element**: `[w⁰] f[X - (q-1)/z] = f`.
The displacement sends the generator `p_k` to `p_k` plus a multiple of `wᵏ` with `k ≥ 1`, so
composing it with evaluation at `w = 0` gives a ring endomorphism of `Λ` fixing every generator and
every scalar. -/
theorem coeff_zero_plethHallLittlewood (q : K) (f : Lambda K) :
    (plethHallLittlewood q f).coeff 0 = f := by
  have h : (Polynomial.evalRingHom (0 : Lambda K)).comp
      (plethHallLittlewood q : Lambda K →+* Polynomial (Lambda K)) = RingHom.id (Lambda K) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
    · simp
    · simp [powerSum]
  rw [Polynomial.coeff_zero_eq_eval_zero]
  exact congrArg (fun g : Lambda K →+* Lambda K => g f) h

/-- The coefficient of `wʲ` in a displaced homogeneous element: for `f ∈ Λ_n` it lies in
`Λ_{n-j}`, read at an integer index, so it vanishes for `j > n`. This is
`HJO.Sym.plethShift_mem_polyComp` at `u = 0`. -/
theorem coeff_plethHallLittlewood_mem (q : K) {n : ℕ} {f : Lambda K} (hf : f ∈ LambdaComp K n)
    (j : ℕ) : (plethHallLittlewood q f).coeff j ∈ LambdaCompInt K ((n : ℤ) - j) := by
  rw [plethHallLittlewood_eq_plethShift]
  exact plethShift_mem_polyComp q 0 hf j

/-- The coefficient of `wʲ` in a displaced element of `Λ_n` vanishes for `j > n`: the target
component `Λ_{n-j}` is the zero subspace there. -/
theorem coeff_plethHallLittlewood_eq_zero (q : K) {n : ℕ} {f : Lambda K} (hf : f ∈ LambdaComp K n)
    {j : ℕ} (hj : n < j) : (plethHallLittlewood q f).coeff j = 0 :=
  eq_zero_of_mem_lambdaCompInt (by omega) (coeff_plethHallLittlewood_mem q hf j)

/-! ### Linearity -/

variable [Algebra ℚ K]

/-- **The Hall--Littlewood operators are linear.** `HJO.Sym.isLinearMap_bop`: for every
`r ∈ ℤ` the map `f ↦ B_r f` from `Λ` to `Λ` is `𝕜`-linear. Its three factors — the displacement
`β`, multiplication by the fixed series `∑_{n ≥ 0} (-z)ⁿ eₙ` and extraction of the coefficient of
`zʳ`, the last two taken together as `HJO.Sym.coeffPairing` — are each linear where they are
defined, so `HJO.Sym.Bop q r` is a bundled `Module.End K (Lambda K)`, and this is that bundling
read as an unbundled statement. -/
@[hjo "lem_cm_bop_linear"]
theorem isLinearMap_bop (q : K) (r : ℤ) : IsLinearMap K fun f : Lambda K => Bop q r f :=
  ⟨fun f g => map_add (Bop q r) f g, fun c f => map_smul (Bop q r) c f⟩

/-! ### The leading term -/

/-- **The leading term of a Hall--Littlewood operator.** `HJO.Sym.bop_leading`: for
`n, r ≥ 0` and `f ∈ Λ_n` there are `g_{r+1}, …, g_{r+n}` in `Λ` with `g_s ∈ Λ_{n+r-s}` and
`B_r f = (-1)^r e_r f + ∑_{s=r+1}^{r+n} (-1)^s e_s g_s`.

The cofactor `g_s` is the coefficient of `w^{s-r}` in `f[X - (q-1)/z]`, which lies in
`Λ_{n-(s-r)} = Λ_{n+r-s}` by `HJO.Sym.coeff_plethHallLittlewood_mem`; the term `s = r` of the
pairing is the constant coefficient, and that is `f` itself by
`HJO.Sym.coeff_zero_plethHallLittlewood`. -/
@[hjo "lem_cm_bop_leading"]
theorem bop_leading (q : K) (n r : ℕ) {f : Lambda K} (hf : f ∈ LambdaComp K n) :
    ∃ g : ℕ → Lambda K, (∀ s ∈ Finset.Icc (r + 1) (r + n), g s ∈ LambdaComp K (n + r - s)) ∧
      Bop q (r : ℤ) f = (-1) ^ r * elemSymm K r * f +
        ∑ s ∈ Finset.Icc (r + 1) (r + n), (-1) ^ s * elemSymm K s * g s := by
  have hsum : Bop q (r : ℤ) f
      = ∑ j ∈ Finset.range (n + 1),
          (plethHallLittlewood q f).coeff j * elemSymmAlt K ((r : ℤ) + j) :=
    coeffPairing_eq_sum_range _ _ fun j hj => coeff_plethHallLittlewood_eq_zero q hf (by omega)
  refine ⟨fun s => (plethHallLittlewood q f).coeff (s - r), fun s hs => ?_, ?_⟩
  · rw [Finset.mem_Icc] at hs
    have h := coeff_plethHallLittlewood_mem q hf (s - r)
    rw [show ((n : ℤ) - ((s - r : ℕ) : ℤ)) = ((n + r - s : ℕ) : ℤ) by
        rw [Nat.cast_sub (by omega : r ≤ s), Nat.cast_sub (by omega : s ≤ n + r)]; push_cast; ring,
      lambdaCompInt_natCast] at h
    exact h
  · have h1 : (plethHallLittlewood q f).coeff 0 * elemSymmAlt K ((r : ℤ) + ((0 : ℕ) : ℤ))
        = (-1) ^ r * elemSymm K r * f := by
      rw [coeff_zero_plethHallLittlewood, Nat.cast_zero, add_zero, elemSymmAlt_natCast]
      ring
    have h2 : ∑ j ∈ Finset.range n,
          (plethHallLittlewood q f).coeff (j + 1) * elemSymmAlt K ((r : ℤ) + ((j + 1 : ℕ) : ℤ))
        = ∑ s ∈ Finset.Icc (r + 1) (r + n),
            (-1) ^ s * elemSymm K s * (plethHallLittlewood q f).coeff (s - r) := by
      have hIcc : Finset.Icc (r + 1) (r + n) = Finset.Ico (r + 1) (r + n + 1) := by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_Ico]
        omega
      rw [hIcc, Finset.sum_Ico_eq_sum_range, show r + n + 1 - (r + 1) = n by omega]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show ((r : ℤ) + ((j + 1 : ℕ) : ℤ)) = ((r + 1 + j : ℕ) : ℤ) by push_cast; ring,
        elemSymmAlt_natCast, show r + 1 + j - r = j + 1 by omega]
      ring
    rw [hsum, Finset.sum_range_succ', h1, h2]
    exact add_comm _ _

end HJO.Sym
