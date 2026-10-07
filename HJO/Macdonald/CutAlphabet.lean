/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.GroupTheory.Perm.ViaEmbedding
public import HJO.Macdonald.FiniteAlphabet
public meta import HJO.Attr

/-! # Erasing variables is graded

Macdonald's polynomials in a finite alphabet are compared across alphabets by the map
`cut_n : 𝕜[x_1, …, x_{n+1}] → 𝕜[x_1, …, x_n]` that fixes `x_1, …, x_n` and sends `x_{n+1}` to `0`.
This file records that this map respects the grading of the symmetric polynomials: a symmetric
polynomial in `n + 1` variables all of whose monomials have total degree `d` is carried to a
symmetric polynomial in `n` variables all of whose monomials have total degree `d`.

## Main results

* `MvPolynomial.rename_killCompl`: the commutation that carries the symmetry — renaming along a
  permutation `w` of the small alphabet and then erasing agrees with erasing and then renaming
  along the extension `w.viaEmbedding` of `w` to the large alphabet.
* `MvPolynomial.IsSymmetric.killCompl`, `MvPolynomial.IsHomogeneous.killCompl`: the two halves.
* `MvPolynomial.killCompl_mem_symmetricHomogeneousSubmodule`: for an injective `f : σ → τ`, the
  algebra map `MvPolynomial.killCompl` sends `𝒮_{τ,d}` into `𝒮_{σ,d}`; at `σ = Fin n`,
  `τ = Fin (n + 1)` and `f = Fin.castSucc` this is the statement about `cut_n`.

## Implementation notes

The map `cut_n` is `MvPolynomial.killCompl (Fin.castSucc_injective n)`: `killCompl hf` is
the algebra homomorphism sending `X (f a)` to `X a` and every variable outside the range of `f` to
`0`, and the complement of the range of `Fin.castSucc : Fin n → Fin (n + 1)` is exactly
`{Fin.last n}`, the erased variable. Nothing in the argument uses that the erased variable is the
*last* one, nor that the two alphabets differ by *one* variable, so everything is stated for an
arbitrary injective `f : σ → τ` between arbitrary alphabets over an arbitrary commutative
semiring `R`; the hypotheses `n ≥ 1` and `d ≥ 0` are therefore absent, and `σ` may even be empty.
That generality is what the library needs: the construction erases several variables in
succession, and a composite of `killCompl`s of injections is again the `killCompl` of an injection.

Both halves are proved from `MvPolynomial.coeff_killCompl`, which says that the coefficient of
`killCompl hf p` at `s` is the coefficient of `p` at `Finsupp.mapDomain f s`. Homogeneity is then
`Finsupp.degree_mapDomain`: pushing an exponent vector forward along *any* map leaves its total
degree alone, which is the statement "every monomial of `cut_n f` is a monomial of `f`".

Symmetry is the commutation `cut_n ∘ w = w ∘ cut_n`, and Mathlib has none such, so
`rename_comp_killCompl` builds it: the extension of `w` to the large alphabet fixing everything off
the range of `f` is `Equiv.Perm.viaEmbedding w ⟨f, hf⟩`, and the two algebra maps
`MvPolynomial τ R →ₐ[R] MvPolynomial σ R` are compared on the variables by `algHom_ext`. On
`X (f a)` both sides give `X (w a)`, because `viaEmbedding` sends `f a` to `f (w a)`; on an `X b`
with `b` off the range both sides give `0`, because `viaEmbedding` fixes `b`.

## References

The main lemma is `MvPolynomial.killCompl_mem_symmetricHomogeneousSubmodule`, resting on
`MvPolynomial.symmetricSubalgebra`, `MvPolynomial.symmetricHomogeneousSubmodule` and
`MvPolynomial.eq_killCompl_castSucc_iff`; it is used by `MvPolynomial.killComplComp_bijective`,
`HJO.Mac.exists_basis_macPpoly` and `HJO.Mac.killComplComp_macOpComp`.
-/

@[expose] public section

namespace MvPolynomial

variable {σ τ R : Type*} [CommSemiring R] {f : σ → τ}

/-- `killCompl hf` is a left inverse of `f` on the variables: it sends `X (f a)` back to `X a`. -/
theorem killCompl_X (hf : Function.Injective f) (a : σ) :
    killCompl (R := R) hf (X (f a)) = X a := by
  rw [← rename_X (f := f), killCompl_rename_app]

/-- `killCompl hf` kills every variable outside the range of `f`. -/
theorem killCompl_X_eq_zero (hf : Function.Injective f) {b : τ} (hb : b ∉ Set.range f) :
    killCompl (R := R) hf (X b) = 0 := by
  simp [killCompl, hb]

/-- Erasing the variables off the range of `f` commutes with permuting the surviving ones: a
permutation `w` of the small alphabet `σ` is the restriction of the permutation
`w.viaEmbedding ⟨f, hf⟩` of the large alphabet `τ`, which fixes every erased variable. This is
`cut_n ∘ w = w ∘ cut_n`, and both sides are algebra maps agreeing on the variables. -/
theorem rename_comp_killCompl (hf : Function.Injective f) (w : Equiv.Perm σ) :
    (rename (w : σ → σ)).comp (killCompl (R := R) hf) =
      (killCompl hf).comp (rename (w.viaEmbedding ⟨f, hf⟩)) := by
  apply algHom_ext
  intro b
  by_cases hb : b ∈ Set.range f
  · obtain ⟨a, rfl⟩ := hb
    have h : (w.viaEmbedding ⟨f, hf⟩) (f a) = f (w a) := w.viaEmbedding_apply (ι := ⟨f, hf⟩) a
    simp only [AlgHom.comp_apply, rename_X, h, killCompl_X]
  · have h : (w.viaEmbedding ⟨f, hf⟩) b = b :=
      w.viaEmbedding_apply_of_notMem (ι := ⟨f, hf⟩) b (by simpa using hb)
    simp only [AlgHom.comp_apply, rename_X, h, killCompl_X_eq_zero hf hb, map_zero]

/-- The pointwise form of `MvPolynomial.rename_comp_killCompl`. -/
theorem rename_killCompl (hf : Function.Injective f) (w : Equiv.Perm σ) (p : MvPolynomial τ R) :
    rename (w : σ → σ) (killCompl hf p) = killCompl hf (rename (w.viaEmbedding ⟨f, hf⟩) p) :=
  AlgHom.congr_fun (rename_comp_killCompl hf w) p

/-- Erasing the variables off the range of an injection preserves symmetry: a permutation of the
small alphabet is pulled through `killCompl` into a permutation of the large one, which `p`
absorbs. -/
theorem IsSymmetric.killCompl (hf : Function.Injective f) {p : MvPolynomial τ R}
    (hp : p.IsSymmetric) : (killCompl hf p).IsSymmetric := fun w => by
  rw [rename_killCompl hf w p, hp]

/-- Erasing the variables off the range of an injection preserves homogeneity: the coefficient of
`killCompl hf p` at `s` is the coefficient of `p` at `Finsupp.mapDomain f s`, and pushing an
exponent vector forward along `f` does not change its total degree. -/
theorem IsHomogeneous.killCompl (hf : Function.Injective f) {d : ℕ} {p : MvPolynomial τ R}
    (hp : p.IsHomogeneous d) : (killCompl hf p).IsHomogeneous d := by
  intro s hs
  rw [coeff_killCompl] at hs
  by_contra hne
  refine hs (hp.coeff_eq_zero ?_)
  rw [Finsupp.degree_mapDomain, Finsupp.degree_eq_weight_one]
  exact hne

/-- Erasing variables is graded: if `f : σ → τ` is injective and `p` is a symmetric polynomial in
the alphabet `τ` all of whose monomials have total degree `d`, then `killCompl hf p` — the
polynomial in the alphabet `σ` obtained by setting every variable outside the range of `f` to
zero — is symmetric in `σ` and again has all its monomials of total degree `d`. At `σ = Fin n`,
`τ = Fin (n + 1)` and `f = Fin.castSucc` this is the inclusion `cut_n (𝒮_{n+1,d}) ⊆ 𝒮_{n,d}`. -/
@[hjo "lem_mac_cut_component"]
theorem killCompl_mem_symmetricHomogeneousSubmodule (hf : Function.Injective f) {d : ℕ}
    {p : MvPolynomial τ R} (hp : p ∈ symmetricHomogeneousSubmodule τ R d) :
    killCompl hf p ∈ symmetricHomogeneousSubmodule σ R d :=
  mem_symmetricHomogeneousSubmodule.2
    ⟨IsSymmetric.killCompl hf (mem_symmetricHomogeneousSubmodule.1 hp).1,
      IsHomogeneous.killCompl hf (mem_symmetricHomogeneousSubmodule.1 hp).2⟩

/-- The submodule form: `killCompl hf` maps `𝒮_{τ,d}` into `𝒮_{σ,d}`. -/
theorem symmetricHomogeneousSubmodule_map_killCompl_le (hf : Function.Injective f) (d : ℕ) :
    Submodule.map (killCompl (R := R) hf).toLinearMap (symmetricHomogeneousSubmodule τ R d) ≤
      symmetricHomogeneousSubmodule σ R d :=
  Submodule.map_le_iff_le_comap.2 fun _ hp =>
    killCompl_mem_symmetricHomogeneousSubmodule hf hp

end MvPolynomial
