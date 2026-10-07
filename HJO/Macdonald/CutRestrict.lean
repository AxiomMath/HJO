/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Macdonald.CutAlphabet
public import HJO.Macdonald.RestrictBasis
public meta import HJO.Attr

/-! # Erasing variables after restricting, and the bijectivity that follows

Two lemmas of the alphabet descent: `HJO.Sym.killCompl_restrictAlphabet` and
`MvPolynomial.killComplComp_bijective`.

`HJO.Sym.killCompl_restrictAlphabet`: erasing a variable after restricting to the larger alphabet is
restricting to the smaller one, `cut_n ∘ res_{n+1} = res_n`. Both sides are `𝕜`-algebra
homomorphisms out of `Λ = 𝕜[p₁, p₂, …]`, so `HJO.Sym.eq_restrictAlphabet` reduces the claim to the
power sums, where it says that erasing a variable from `x_1^k + ⋯ + x_{n+1}^k` leaves
`x_1^k + ⋯ + x_n^k` --- true because `k ≥ 1`, the constant term being the one thing erasure would
keep.

`MvPolynomial.killComplComp_bijective`: for `d ≤ n` the map `cut_n` carries `𝒮_{n+1,d}` bijectively
onto `𝒮_{n,d}`.

## The route, and the lemma it avoids

One can prove the bijectivity by transporting the monomial symmetric basis: `cut_n` carries
`m_ν[X_{n+1}]` to `m_ν[X_n]` for `ν_{n+1} = 0` and to `0` otherwise
(`MvPolynomial.killCompl_msymm`), and for `d ≤ n` the two index sets coincide, so a basis goes to a
basis. Here the bijectivity is instead read off `HJO.Sym.killCompl_restrictAlphabet` and the
bijectivity of the restrictions themselves: for `d ≤ n` both `res_n` and `res_{n+1}` are bijections
from `Λ_d` onto their targets (`HJO.Sym.restrictAlphabetComp_bijective`), and the triangle
`cut_n ∘ res_{n+1} = res_n` then exhibits `cut_n` on `𝒮_{n+1,d}` as `res_n ∘ res_{n+1}^{-1}`, a
composite of two bijections.

**So `MvPolynomial.killCompl_msymm` is not on THIS route** -- the bijectivity above is read off the
triangle rather than by transporting the monomial symmetric basis, so nothing here needs it.

`MvPolynomial.killCompl_msymm` is also the natural route to `HJO.Mac.killComplComp_macPpoly`,
which avoids it as well, by going through the converse of
`HJO.Mac.sub_msymm_mem_span_lowerMsymmSet` (`HJO/Macdonald/PieriColumn.lean`) instead of
transporting the basis. The lemma itself is proved in `HJO/Macdonald/MsymmCut.lean`.

## Generality, and the hypotheses that are dropped

Everything is stated for an arbitrary injection `f : σ → τ` of finite alphabets, as in
`HJO/Macdonald/CutAlphabet.lean`: the `cut_n` is
`MvPolynomial.killCompl (Fin.castSucc_injective n)`, and nothing in either argument uses that the
erased variable is the last one or that there is only one of it. In particular the descent through
several variables at once is the same statement, and the `n ≥ 1` is absent. The
hypothesis of the bijectivity is `d ≤ #σ` alone: `d ≤ #τ` follows, an injection not decreasing the
cardinality.

No genericity and no field: a commutative ring that is a `ℚ`-algebra suffices, as in
`HJO/Macdonald/RestrictBasis.lean`, and the parameters `q` and `u` do not occur.

## Main definitions

* `MvPolynomial.killComplComp`: `killCompl hf` restricted to a graded piece, a `K`-linear map
  `𝒮_{τ,d} →ₗ 𝒮_{σ,d}`; the containment is
  `MvPolynomial.killCompl_mem_symmetricHomogeneousSubmodule`.

## Main results

* `HJO.Sym.killCompl_restrictAlphabet`.
* `MvPolynomial.killComplComp_bijective`, and its bundled form
  `MvPolynomial.killComplEquiv` (`MvPolynomial.killComplComp_bijective`).

## References

This file proves `HJO.Sym.killCompl_restrictAlphabet` and `MvPolynomial.killComplComp_bijective`
from `HJO.Sym.Lambda`, `HJO.Sym.cells`, `MvPolynomial.symmetricHomogeneousSubmodule`,
`HJO.Sym.restrictAlphabet`, `MvPolynomial.eq_killCompl_castSucc_iff`,
`MvPolynomial.killCompl_mem_symmetricHomogeneousSubmodule`,
`MvPolynomial.exists_basis_symmetricHomogeneousSubmodule_msymm` and
`HJO.Sym.restrictAlphabetComp_bijective`; `HJO.Mac.killComplComp_macPpoly` and
`HJO.Mac.restrictAlphabet_macPfun_partDiagram` use them.
-/

@[expose] public section

open Finset MvPolynomial

namespace HJO.Sym

/-! ### Erasing variables in a power sum -/

variable {σ τ : Type*} [Fintype σ] [Fintype τ] {K : Type*} [CommRing K] {f : σ → τ}

/-- **Erasing the variables off the range of an injection in a power sum of positive degree leaves
the power sum of the smaller alphabet.** The surviving variables contribute `x_a^{k+1}`, the erased
ones `0` --- which is where `k + 1 ≥ 1` is spent, a power sum of degree `0` being the cardinality of
the alphabet and not stable under erasure. -/
theorem killCompl_psum (hf : Function.Injective f) (k : ℕ) :
    killCompl (R := K) hf (psum τ K (k + 1)) = psum σ K (k + 1) := by
  classical
  rw [psum, map_sum, psum]
  have hzero : ∀ i ∈ (univ : Finset τ), i ∉ univ.image f →
      killCompl (R := K) hf (X i ^ (k + 1)) = 0 := by
    intro i _ hi
    rw [map_pow, killCompl_X_eq_zero hf fun ⟨a, ha⟩ => hi (mem_image.mpr ⟨a, mem_univ a, ha⟩),
      zero_pow (Nat.succ_ne_zero k)]
  rw [← Finset.sum_subset (Finset.subset_univ (univ.image f)) hzero,
    Finset.sum_image fun a _ b _ hab => hf hab]
  exact Finset.sum_congr rfl fun a _ => by rw [map_pow, killCompl_X hf]

/-- **Restriction commutes with erasing variables.** For an injection
`f : σ → τ` of finite alphabets, `killCompl hf ∘ res_τ = res_σ`; at `σ = Fin n`, `τ = Fin (n + 1)`
and `f = Fin.castSucc` this is the `cut_n(res_{n+1}(g)) = res_n(g)`.

Both sides are `K`-algebra homomorphisms `Λ → 𝕜[x_i : i ∈ σ]`, and `HJO.Sym.eq_restrictAlphabet`
says that the values on the power-sum symbols pin such a map; those values agree by
`killCompl_psum`. -/
@[hjo "lem_mac_res_cut"]
theorem killCompl_restrictAlphabet [Algebra ℚ K] (hf : Function.Injective f) (g : Lambda K) :
    killCompl (R := K) hf (restrictAlphabet τ K g) = restrictAlphabet σ K g :=
  AlgHom.congr_fun
    (eq_restrictAlphabet ((killCompl hf).comp (restrictAlphabet τ K)) fun k => by
      rw [AlgHom.comp_apply, restrictAlphabet_powerSum, killCompl_psum hf]) g

end HJO.Sym

/-! ### Erasing variables is bijective on a graded piece -/

namespace MvPolynomial

open HJO.Sym

variable {σ τ : Type*} {K : Type*} [CommRing K] {f : σ → τ}

/-- `killCompl hf` restricted to the symmetric polynomials homogeneous of degree `d`: the
map `cut_n` read as a map `𝒮_{n+1,d} → 𝒮_{n,d}`. The containment is
`MvPolynomial.killCompl_mem_symmetricHomogeneousSubmodule`. -/
noncomputable def killComplComp (hf : Function.Injective f) (K : Type*) [CommRing K] (d : ℕ) :
    symmetricHomogeneousSubmodule τ K d →ₗ[K] symmetricHomogeneousSubmodule σ K d :=
  (killCompl (R := K) hf).toLinearMap.restrict
    fun _ hp => killCompl_mem_symmetricHomogeneousSubmodule hf hp

@[simp]
theorem coe_killComplComp (hf : Function.Injective f) {d : ℕ}
    (p : symmetricHomogeneousSubmodule τ K d) :
    (killComplComp hf K d p : MvPolynomial σ K) = killCompl hf (p : MvPolynomial τ K) := rfl

/-- Erasing variables after restricting is restricting, read on the graded pieces: the triangle
`killComplComp ∘ restrictAlphabetComp τ = restrictAlphabetComp σ` of
`HJO.Sym.killCompl_restrictAlphabet`. -/
theorem killComplComp_comp_restrictAlphabetComp [Fintype σ] [Fintype τ] [Algebra ℚ K]
    (hf : Function.Injective f) (d : ℕ) :
    (killComplComp hf K d).comp (restrictAlphabetComp τ K d) = restrictAlphabetComp σ K d :=
  LinearMap.ext fun g => Subtype.ext (killCompl_restrictAlphabet hf (g : Lambda K))

/-- **Erasing variables is bijective above the degree.** For `d ≤ #σ` and
an injection `f : σ → τ`, `killCompl hf` carries `𝒮_{τ,d}` bijectively onto `𝒮_{σ,d}`.

The two restrictions `res_σ` and `res_τ` are bijections from `Λ_d` onto their targets
(`HJO.Sym.restrictAlphabetComp_bijective`; the hypothesis `d ≤ #τ` follows from `d ≤ #σ`, an
injection not decreasing the cardinality), and `HJO.Sym.killCompl_restrictAlphabet` factors `res_σ`
through `killCompl hf`, so `killCompl hf` on `𝒮_{τ,d}` is `res_σ` composed with the inverse of
`res_τ`. -/
@[hjo "lem_mac_cut_bijective"]
theorem killComplComp_bijective [Fintype σ] [Finite τ] [Algebra ℚ K] (hf : Function.Injective f)
    {d : ℕ} (hd : d ≤ Fintype.card σ) : Function.Bijective (killComplComp hf K d) := by
  let _ : Fintype τ := Fintype.ofFinite τ
  have hdτ : d ≤ Fintype.card τ := hd.trans (Fintype.card_le_of_injective f hf)
  have hσ := restrictAlphabetComp_bijective σ K hd
  have hτ := restrictAlphabetComp_bijective τ K hdτ
  have hcomp : Function.Bijective
      ((killComplComp hf K d).comp (restrictAlphabetComp τ K d) : LambdaComp K d → _) := by
    rw [killComplComp_comp_restrictAlphabetComp]
    exact hσ
  refine ⟨fun x y hxy => ?_, fun z => ?_⟩
  · obtain ⟨a, rfl⟩ := hτ.surjective x
    obtain ⟨b, rfl⟩ := hτ.surjective y
    exact congrArg _ (hcomp.injective hxy)
  · obtain ⟨a, ha⟩ := hcomp.surjective z
    exact ⟨restrictAlphabetComp τ K d a, ha⟩

/-- The bijection of `MvPolynomial.killComplComp_bijective`, bundled as a `K`-linear equivalence
`𝒮_{τ,d} ≃ₗ 𝒮_{σ,d}`. This is the form a descent through the alphabets uses: it names the inverse,
which is what identifies an element of the larger alphabet from its image. -/
noncomputable def killComplEquiv [Fintype σ] [Finite τ] [Algebra ℚ K]
    (hf : Function.Injective f) {d : ℕ} (hd : d ≤ Fintype.card σ) :
    symmetricHomogeneousSubmodule τ K d ≃ₗ[K] symmetricHomogeneousSubmodule σ K d :=
  LinearEquiv.ofBijective _ (killComplComp_bijective hf hd)

@[simp]
theorem coe_killComplEquiv [Fintype σ] [Finite τ] [Algebra ℚ K] (hf : Function.Injective f)
    {d : ℕ} (hd : d ≤ Fintype.card σ) (p : symmetricHomogeneousSubmodule τ K d) :
    (killComplEquiv hf hd p : MvPolynomial σ K) = killCompl hf (p : MvPolynomial τ K) := rfl

/-- **Erasing variables is injective above the degree**, the half a descent spends: two symmetric
polynomials of degree `d ≤ #σ` in the larger alphabet with the same image under `killCompl hf` are
equal. -/
theorem eq_of_killCompl_eq [Fintype σ] [Finite τ] [Algebra ℚ K] (hf : Function.Injective f)
    {d : ℕ} (hd : d ≤ Fintype.card σ) {p g : MvPolynomial τ K}
    (hp : p ∈ symmetricHomogeneousSubmodule τ K d) (hg : g ∈ symmetricHomogeneousSubmodule τ K d)
    (h : killCompl (R := K) hf p = killCompl hf g) : p = g :=
  Subtype.ext_iff.mp ((killComplComp_bijective hf hd (K := K) (d := d)).injective
    (a₁ := ⟨p, hp⟩) (a₂ := ⟨g, hg⟩) (Subtype.ext h))

end MvPolynomial
