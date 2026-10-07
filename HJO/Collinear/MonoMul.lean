/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Collinear.ConeRing
public meta import HJO.Attr

/-! # Multiplication by a monomial on the formal sums in `k` variables

The BGLX vanishing criterion is stated with the *symmetrised symbol*
`Ξ_c = (1/k!) ∑_τ τ_*(Π_c Ω̂_k)`, whose `k!` summands lie in the `k!` different cone rings
`R^τ_k` of `HJO/Collinear/ConeRing.lean` and whose sum therefore lies in none of them: it is
recorded in the module `M_k = HJO.Bglx.Family k Λ` of *all* families, where addition needs no
support condition. Raising every index of every word divides the symbol by `z₁z₂⋯z_k`, so the step
that carries the criterion to the index shift has to multiply an element of `M_k` by a monomial,
and to know that this operation is additive, injective, and compatible with relabelling the
variables.

That operation is what this file supplies. `HJO.Bglx.monoMul β` is multiplication by `z ^ β` on
all of `M_k` — on coefficients, the shift `α ↦ α - β` — and `HJO.Bglx.coeff_monoElem_mul`
identifies it, on the cone-bounded families, with the ring multiplication of `ConeRing` by the
monomial `z ^ β`. The lemma the criterion needs is
`HJO.Bglx.relabel_monoMul_allOnes`: relabelling the variables passes the symmetric monomial
`z₁z₂⋯z_k`.

## Main definitions

* `HJO.Bglx.monoMul`: multiplication by the monomial `z ^ β` on `M_k`, as the exponent shift
  `α ↦ α - β` on coefficients.
* `HJO.Bglx.monoElem`: the monomial `z ^ β` as an element of the cone ring `R^τ_k`.
* `HJO.Bglx.allOnes`: the exponent `(1, …, 1)`, so that `monoMul (allOnes k)` is multiplication
  by `z₁z₂⋯z_k`.

## Main statements

* `HJO.Bglx.coeff_monoElem_mul`: on the cone-bounded families, `monoMul β` *is* multiplication by
  the monomial `z ^ β` in `R^τ_k`. This is what makes `monoMul` the operation the statements name
  and not merely a shift of indices that happens to be additive.
* `HJO.Bglx.monoMul_injective`: multiplication by a monomial is injective on `M_k`, the step that
  lets the criterion cancel `z₁⋯z_k`.
* `HJO.Bglx.relabel_monoMul_allOnes`: `τ_*(z₁z₂⋯z_k · f) = z₁z₂⋯z_k · τ_* f`.
* `HJO.Bglx.ct_relabel`: constant-term extraction is invariant under relabelling.

## Implementation notes

**Why `monoMul` has to exist as a definition of its own.** The usual argument writes
`z₁z₂⋯z_k f` for `f ∈ M_k` and justifies it by the remark that multiplying a
family by a monomial shifts exponents, but the product of `HJO.Bglx.ConeRing` is defined only
*inside* one cone ring `R^τ_k`, and a general `f ∈ M_k` is not cone-bounded — the whole reason
`Ξ_c` is recorded in `M_k` is that its summands live in different rings. So no existing
definition provides the operation the statements use, and multiplication by a monomial on all of
`M_k` had to be introduced here. `Family k R` is a `Pi` type, so it carries Mathlib's *pointwise*
multiplication, which is a different and wrong operation; `monoMul` is a named function precisely
so that `*` is never written on `Family`.

`coeff_monoElem_mul` is the faithfulness tie. Without it `monoMul` would be an unmotivated shift;
with it, the two readings of `z ^ β · f` — the convolution of `ConeRing` where both are defined,
and the shift on all of `M_k` — agree, so the lemmas below really are the statements
about multiplying by a monomial.

`allOnes k` is `(1, …, 1) ∈ ℤ^k` spelled through `Finsupp.equivFunOnFinite`, and
`relabelExp_allOnes` is the one fact about it the argument uses: a constant exponent is fixed by
every permutation of the variables, which is exactly why `z₁⋯z_k` may be moved across `τ_*`
while a general monomial may not. The index base follows `ConeRing`: exponents are
`Fin k →₀ ℤ` and zero-based, so `allOnes k i = 1` for every `i : Fin k` is the usual
`𝟏 = (1, …, 1)` with its coordinates numbered from `1`.

Generic in the coefficients. `monoMul`, `monoMul_injective` and `relabel_monoMul` need only
`AddCommMonoid`/`Semiring` on `R`, `monoElem` needs `Zero` and `One`, and `coeff_monoElem_mul`
needs `CommRing` because that is what `ConeRing` carries a ring structure over. The
`Λ` over `𝕜 = ℚ(q, u)` is the instance `R = Lambda L`; nothing here mentions `q`, `u` or any
parameter condition, the operation being one on exponents.

`monoMul` is `noncomputable` only because subtraction on `Finsupp` is.

Faithfulness to Lemma "Relabelling passes the product of the variables"
(`HJO.Bglx.relabel_monoMul_allOnes`): (1) No hypothesis is dead: `k` is the number of variables, `τ`
the permutation moved across, `f` the arbitrary member of `M_k` the statement quantifies over, and
`Semiring R` is what makes `relabel` a linear equivalence — there is no hypothesis on `k`, on `τ`,
or on the support of `f`, matching a statement made for all of `M_k`.
(2) The scalars and the base are those of the statement: `f` has coefficients in the same ring
`R` the relabelling is linear over, and the monomial moved across is the one with coefficient `1`.
(3) The claim is pinned, not characterised up to something: both sides are the
displayed families, with the monomial `z₁z₂⋯z_k` and not another monomial — `relabel_monoMul`
records what happens for a general `z ^ β`, namely that the exponent is itself relabelled, so the
specialisation is visibly the case where that has no effect.
(4) The instantiation is not degenerate: `relabel_monoMul` shows the general monomial does *not*
pass unchanged (its exponent is moved by `relabelExp τ`), so the lemma is a statement about
`(1, …, 1)` and not an instance of a triviality; and `monoMul_injective` shows multiplication by
`z₁⋯z_k` is not the zero map for any `k`.

## References

F. Bergeron, A. M. Garsia, E. Leven and G. Xin, *Some remarkable new plethystic
operators in the theory of Macdonald polynomials*, arXiv:1405.0316v1, J. Comb. **7** (2016)
671--714, whose proof of Theorem 2.2 divides the symbol by `z₁z₂⋯z_k`.
-/

@[expose] public section

namespace HJO.Bglx

variable {k : ℕ} {R : Type*} {τ : Equiv.Perm (Fin k)}

/-- Multiplication of a formal sum by the monomial `z ^ β`: the shift `α ↦ α - β` of exponents.
Defined on all of `M_k`, where the ring multiplication of `ConeRing` is unavailable because a
general family is not cone-bounded. -/
noncomputable def monoMul (β : Fin k →₀ ℤ) (f : Family k R) : Family k R := fun α => f (α - β)

@[simp] lemma monoMul_apply (β : Fin k →₀ ℤ) (f : Family k R) (α : Fin k →₀ ℤ) :
    monoMul β f α = f (α - β) := rfl

@[simp] lemma monoMul_zero_exp (f : Family k R) : monoMul 0 f = f := by
  funext α; simp

lemma monoMul_monoMul (β γ : Fin k →₀ ℤ) (f : Family k R) :
    monoMul β (monoMul γ f) = monoMul (β + γ) f := by
  funext α; simp [sub_sub]

/-- Multiplication by a monomial is injective on `M_k`: it shifts every exponent, so it carries a
nonzero family to a nonzero family. -/
lemma monoMul_injective (β : Fin k →₀ ℤ) : Function.Injective (monoMul β (R := R)) := by
  intro f g h
  funext α
  simpa using congrFun h (α + β)

@[simp] lemma monoMul_eq_zero_iff [Zero R] (β : Fin k →₀ ℤ) (f : Family k R) :
    monoMul β f = 0 ↔ f = 0 := by
  refine ⟨fun h => monoMul_injective β (h.trans ?_), fun h => ?_⟩
  · funext α; simp
  · rw [h]; funext α; simp

section Mono

variable [Zero R] [One R]

lemma support_mono_subset (β : Fin k →₀ ℤ) :
    Function.support (mono β : Family k R) ⊆ {β} := by
  intro α hα
  rw [Function.mem_support, mono, Pi.single_apply, ne_eq, ite_eq_right_iff, not_forall] at hα
  exact hα.1

lemma isConeBounded_mono (τ : Equiv.Perm (Fin k)) (β : Fin k →₀ ℤ) :
    IsConeBounded τ (mono β : Family k R) :=
  isConeBounded_of_finite (Set.Finite.subset (Set.finite_singleton β) (support_mono_subset β))

/-- The monomial `z ^ β` as an element of the cone ring `R^τ_k`; its support is the single
exponent `β`, hence cone-bounded for every ordering. -/
noncomputable def monoElem (τ : Equiv.Perm (Fin k)) (β : Fin k →₀ ℤ) : ConeRing k τ R where
  coeff := mono β
  isConeBounded := isConeBounded_mono τ β

@[simp] lemma coeff_monoElem (τ : Equiv.Perm (Fin k)) (β α : Fin k →₀ ℤ) :
    (monoElem τ β : ConeRing k τ R).coeff α = if α = β then 1 else 0 :=
  Pi.single_apply _ _ _

end Mono

/-- **`monoMul` is multiplication by a monomial.** On the cone-bounded families the shift
`monoMul β` agrees with the ring multiplication of `R^τ_k` by the monomial `z ^ β`: only the pair
`(β, α - β)` contributes to the convolution at `α`. -/
lemma coeff_monoElem_mul [CommRing R] (β : Fin k →₀ ℤ) (x : ConeRing k τ R) :
    ((monoElem τ β : ConeRing k τ R) * x).coeff = monoMul β x.coeff := by
  funext α
  have hsub : ConeRing.convSupport (monoElem τ β : ConeRing k τ R) x α
      ⊆ (({β} : Finset (Fin k →₀ ℤ)) : Set _) := by
    intro α' hα'
    have h1 := hα'.1
    rw [coeff_monoElem] at h1
    by_contra h
    exact h1 (ite_eq_right (by simpa using h))
  rw [ConeRing.coeff_mul_of_subset _ _ _ _ hsub]
  simp

/-- The exponent `𝟏 = (1, …, 1) ∈ ℤ^k`, so that `monoMul (allOnes k)` is multiplication by the
symmetric monomial `z₁z₂⋯z_k`. -/
noncomputable def allOnes (k : ℕ) : Fin k →₀ ℤ := Finsupp.equivFunOnFinite.symm fun _ => 1

@[simp] lemma allOnes_apply (i : Fin k) : allOnes k i = 1 := by simp [allOnes]

/-- A constant exponent is fixed by every permutation of the variables: this is the whole reason
`z₁z₂⋯z_k` passes across a relabelling. -/
@[simp] lemma relabelExp_allOnes (τ : Equiv.Perm (Fin k)) :
    relabelExp τ (allOnes k) = allOnes k := by
  refine Finsupp.ext fun i => ?_
  rw [← τ.apply_symm_apply i, relabelExp_apply_perm]
  simp

/-- Relabelling a monomial multiple: the monomial's exponent is itself relabelled. -/
lemma relabel_monoMul [Semiring R] (τ : Equiv.Perm (Fin k)) (β : Fin k →₀ ℤ) (f : Family k R) :
    relabel τ (monoMul β f) = monoMul (relabelExp τ β) (relabel τ f) := by
  funext α
  simp only [relabel_apply, monoMul_apply, map_sub, AddEquiv.symm_apply_apply]

/-- **Relabelling passes the product of the variables.** For every `f ∈ M_k` and every permutation
`τ` of the `k` variables, `τ_*(z₁z₂⋯z_k · f) = z₁z₂⋯z_k · τ_* f`: the exponent `(1, …, 1)` is fixed
by `τ`, so the symmetric monomial commutes with the relabelling, and the symmetrised symbol of a
raised family may be compared with that of the family itself. -/
@[hjo "lem_bglx_sym_raise"]
theorem relabel_monoMul_allOnes [Semiring R] (τ : Equiv.Perm (Fin k)) (f : Family k R) :
    relabel τ (monoMul (allOnes k) f) = monoMul (allOnes k) (relabel τ f) := by
  rw [relabel_monoMul, relabelExp_allOnes]

/-- Constant-term extraction is invariant under relabelling: `τ⁻¹ 0 = 0`. -/
@[simp] lemma ct_relabel [Semiring R] (τ : Equiv.Perm (Fin k)) (f : Family k R) :
    ct k R (relabel τ f) = ct k R f := by
  rw [ct_apply, ct_apply, relabel_apply, map_zero]

end HJO.Bglx
