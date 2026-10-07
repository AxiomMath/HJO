/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Ascent.Transport
public import HJO.Macdonald.Htilde
public import HJO.Macdonald.ParamInversion
public import HJO.Macdonald.StandingFacts
public meta import HJO.Attr

/-! # The duality vocabulary: the three semilinear endomorphisms of `Λ`

Three of the parameter operations on symmetric functions, and the parameter
automorphisms of `𝕜` they restrict to. All three are ring endomorphisms of `Λ` that are NOT
`𝕜`-linear: each acts on the coefficients through an automorphism of `𝕜` and on the power sums by a
rule of its own.

* `HJO.Ascent.dualitySwap` -- `Θ`, restricting to the exchange `τ` of the two parameters and fixing
  every `p_k`. `Θ(F)` is commonly written `F[X; u, q]`.
* `HJO.Ascent.paramUInvLambda` -- `ȷ`, restricting to the inversion `υ` of the second parameter and
  fixing every `p_k`. `ȷ(F)` is commonly written `F[X; q, 1/u]`.
* `HJO.Ascent.dualityOmega` -- `Ω`, restricting to `ι ∘ τ` (so `q ↦ u⁻¹` and `u ↦ q⁻¹`) and sending
  `p_k` to `-q^k (1 - u^k)/(1 - q^k) · p_k`.

## The substrate, and why none of these is built by hand

`Λ` is `MvPolynomial ℕ K` (`HJO.Sym.Lambda`), a polynomial ring over `K` on the power sums, so an
endomorphism "determined by its restriction to `𝕜` and its values on the `p_k`" is a
`MvPolynomial.eval₂Hom` and nothing more. Two of the three need no new construction at all:
`HJO.Sym.coeffSubst φ` is `MvPolynomial.map φ`, which is exactly "act on coefficients by `φ`, fix
every generator", so `Θ` and `ȷ` ARE `coeffSubst` at the right automorphism of `𝕜`. Only `Ω`, which
scales the generators, needs `eval₂Hom`.

The parameter automorphisms come from `HJO.Ascent.paramEmbedding`, which turns an algebraically
independent pair into a homomorphism out of `𝕜` sending the two indeterminates to that pair. So
each automorphism of `𝕜` below is named by exhibiting the pair it should send `(q, u)` to, and the
independence of that pair is the whole content. `υ` and `ι` were already built this way
(`HJO.Ascent.paramUInvHom`, `HJO.Ascent.paramQUInvHom`); `τ` and `ι ∘ τ` are added here.

## Indexing: `p_k` is `X (k - 1)`

`HJO.Sym.powerSum K k` is `MvPolynomial.X (k - 1)`, with truncated natural subtraction, so the
generator `X i` is `p_{i+1}`. This is not a detail to be rediscovered: it is what makes `Ω`
well defined. The scaling rule is stated for `k ≥ 1`, and the scalar genuinely fails at
`k = 0` -- its denominator `1 - q^0` is zero. Defining `Ω` on the generator `X i` with the scalar
belonging to `p_{i+1}` means the index is at least one by construction, with no side condition to
carry and no junk value at `k = 0`.

## Where the nonvanishing comes from

`1 - q^k` and `1 - u^k` must be nonzero for `k ≥ 1` or `Ω`'s scalar is not defined. This holds
because `q` and `u` are distinct indeterminates of `𝕜 = ℚ(q, u)`; here it is
`HJO.Standing.paramQ_pow_succ_ne_one` and `HJO.Standing.paramU_pow_succ_ne_one`, which prove exactly
that from the algebraic independence of the two indeterminates. The two lemmas below only restate
them as nonvanishing of a difference.

Every statement below is at a field merely PRESENTED as a field of fractions of the parameter ring,
rather than at one particular construction of `𝕜`.
-/

@[expose] public section

namespace HJO.Ascent

open HJO.Sym

variable (K : Type*) [Field K] [Algebra ℚ K] [Algebra ParamRing K] [IsFractionRing ParamRing K]

/-! ### The two remaining parameter automorphisms of `𝕜` -/

omit [Algebra ℚ K] in
/-- **`(u, q)` is algebraically independent over `ℤ`.** Exchanging the two entries is composing the
family with the reindexing `![1, 0]` of `Fin 2`, which is injective, so this is
`AlgebraicIndependent.comp`. It is what makes the exchange of the parameters reachable through
`HJO.Ascent.paramEmbedding`. -/
theorem algebraicIndependent_param_swap :
    AlgebraicIndependent ℤ ![paramU K, paramQ K] := by
  have h : ![paramU K, paramQ K] = ![paramQ K, paramU K] ∘ ![1, 0] := by
    funext i; fin_cases i <;> rfl
  rw [h]
  exact (algebraicIndependent_param K).comp _ (by decide)

omit [Algebra ℚ K] in
/-- **`(u⁻¹, q⁻¹)` is algebraically independent over `ℤ`.** The composite `ι ∘ τ` of the exchange
with the inversion of both parameters sends `q` to `u⁻¹` and `u` to `q⁻¹`, so this is the pair that
makes it reachable through `HJO.Ascent.paramEmbedding`. -/
theorem algebraicIndependent_param_swapInv :
    AlgebraicIndependent ℤ ![(paramU K)⁻¹, (paramQ K)⁻¹] := by
  have h : ![(paramU K)⁻¹, (paramQ K)⁻¹] = ![(paramQ K)⁻¹, (paramU K)⁻¹] ∘ ![1, 0] := by
    funext i; fin_cases i <;> rfl
  rw [h]
  exact (algebraicIndependent_param_invQU K).comp _ (by decide)

/-- The exchange `τ` of the two parameters, as a ring endomorphism of `𝕜`: the embedding of `𝕜`
into itself carrying `q` to `u` and `u` to `q`. -/
noncomputable def paramSwapHom : K →+* K := paramEmbedding K (algebraicIndependent_param_swap K)

/-- The composite `ι ∘ τ` of the exchange with the inversion of both parameters, as a ring
endomorphism of `𝕜`: it carries `q` to `u⁻¹` and `u` to `q⁻¹`. -/
noncomputable def paramSwapInvHom : K →+* K :=
  paramEmbedding K (algebraicIndependent_param_swapInv K)

@[simp]
theorem paramSwapHom_paramQ : paramSwapHom K (paramQ K) = paramU K :=
  paramEmbedding_paramQ (algebraicIndependent_param_swap K)

@[simp]
theorem paramSwapHom_paramU : paramSwapHom K (paramU K) = paramQ K :=
  paramEmbedding_paramU (algebraicIndependent_param_swap K)

@[simp]
theorem paramSwapInvHom_paramQ : paramSwapInvHom K (paramQ K) = (paramU K)⁻¹ :=
  paramEmbedding_paramQ (algebraicIndependent_param_swapInv K)

@[simp]
theorem paramSwapInvHom_paramU : paramSwapInvHom K (paramU K) = (paramQ K)⁻¹ :=
  paramEmbedding_paramU (algebraicIndependent_param_swapInv K)

/-! ### `Θ` and `ȷ`: the two that fix every power sum -/

/-- **The exchange of the two parameters on the symmetric functions.** `Θ`, the ring
endomorphism of `Λ` restricting to `τ` on `𝕜` and fixing every `p_k`; `Θ(F)` is commonly written
`F[X; u, q]`.

This is `HJO.Sym.coeffSubst` at `τ`, which is `MvPolynomial.map τ` -- acting on the coefficients and
fixing every generator is precisely what that map does, so the uniqueness appealed to
needs no separate argument here. It is not `𝕜`-linear but satisfies `Θ(cF) = τ(c)Θ(F)`, which is
`HJO.Sym.coeffSubst_smul`. -/
@[hjo "def_dua_swap"]
noncomputable def dualitySwap : Lambda K →+* Lambda K := coeffSubst (paramSwapHom K)

/-- **The second-parameter inversion of the symmetric functions.** `ȷ`, the ring
endomorphism of `Λ` restricting to `υ` on `𝕜` and fixing every `p_k`; `ȷ(F)` is commonly written
`F[X; q, 1/u]`.

As with `Θ`, this is `HJO.Sym.coeffSubst` at the relevant automorphism of `𝕜`, here
`HJO.Ascent.paramUInvHom`, and `ȷ(cF) = υ(c)ȷ(F)` is `HJO.Sym.coeffSubst_smul`. -/
@[hjo "def_mac_uinv"]
noncomputable def paramUInvLambda : Lambda K →+* Lambda K := coeffSubst (paramUInvHom K)

@[simp]
theorem dualitySwap_powerSum (k : ℕ) : dualitySwap K (powerSum K k) = powerSum K k :=
  coeffSubst_powerSum _ k

@[simp]
theorem paramUInvLambda_powerSum (k : ℕ) : paramUInvLambda K (powerSum K k) = powerSum K k :=
  coeffSubst_powerSum _ k

@[simp]
theorem dualitySwap_C (c : K) :
    dualitySwap K (MvPolynomial.C c) = MvPolynomial.C (paramSwapHom K c) :=
  coeffSubst_C _ c

@[simp]
theorem paramUInvLambda_C (c : K) :
    paramUInvLambda K (MvPolynomial.C c) = MvPolynomial.C (paramUInvHom K c) :=
  coeffSubst_C _ c

/-! ### `Ω`: the one that scales the power sums -/

omit [Algebra ℚ K] in
/-- `1 - q^k ≠ 0` for `k ≥ 1`, which is what makes `Ω`'s scalar a legitimate element of `𝕜`. This
is `HJO.Standing.paramQ_pow_succ_ne_one` read as a nonvanishing rather than as an inequality of
powers -- the fact itself is already proved there, at the standing field, from the algebraic
independence of the two indeterminates. -/
theorem one_sub_paramQ_pow_ne_zero (k : ℕ) : 1 - paramQ K ^ (k + 1) ≠ 0 :=
  sub_ne_zero_of_ne (Standing.paramQ_pow_succ_ne_one K k).symm

omit [Algebra ℚ K] in
/-- `1 - u^k ≠ 0` for `k ≥ 1`, the companion of `HJO.Ascent.one_sub_paramQ_pow_ne_zero`; it is
`HJO.Standing.paramU_pow_succ_ne_one`. -/
theorem one_sub_paramU_pow_ne_zero (k : ℕ) : 1 - paramU K ^ (k + 1) ≠ 0 :=
  sub_ne_zero_of_ne (Standing.paramU_pow_succ_ne_one K k).symm

/-- The scalar `Ω` multiplies the generator `X i = p_{i+1}` by: `-q^k (1 - u^k)/(1 - q^k)` at
`k = i + 1`.

The index is `i + 1` rather than `i` because `HJO.Sym.powerSum K k` is `MvPolynomial.X (k - 1)`, so
the generator `X i` is `p_{i+1}`. That shift is what makes the scalar total: the rule is
stated for `k ≥ 1`, and at `k = 0` its denominator `1 - q^0` really is zero, so a definition indexed
by `k` directly would carry a side condition or a junk value. -/
noncomputable def omegaScalar (i : ℕ) : K :=
  -paramQ K ^ (i + 1) * (1 - paramU K ^ (i + 1)) / (1 - paramQ K ^ (i + 1))

omit [Algebra ℚ K] in
/-- The scalar of `Ω` is nonzero: the numerator is a product of nonzero factors and the denominator
is nonzero, all four facts being standing facts about the two indeterminates rather than
hypotheses. -/
theorem omegaScalar_ne_zero (i : ℕ) : omegaScalar K i ≠ 0 :=
  div_ne_zero
    (mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ (Standing.paramQ_ne_zero K)))
      (one_sub_paramU_pow_ne_zero K i))
    (one_sub_paramQ_pow_ne_zero K i)

/-- **The duality map.** `Ω`, the ring endomorphism of `Λ` restricting to `ι ∘ τ`
on `𝕜` -- so `q ↦ u⁻¹` and `u ↦ q⁻¹` -- and sending `p_k` to `-q^k (1 - u^k)/(1 - q^k) · p_k` for
every `k ≥ 1`.

`Λ` being a polynomial ring over `𝕜` on the power sums, such an endomorphism exists and is unique,
and `MvPolynomial.eval₂Hom` is that existence: it takes the action on coefficients and the images of
the generators and returns the ring homomorphism. `Ω(cF) = ι(τ(c))Ω(F)` holds because the
coefficient action is a ring homomorphism, and `ι ∘ τ` is an automorphism of `𝕜` as a composite of
two. -/
@[hjo "def_dua_omega"]
noncomputable def dualityOmega : Lambda K →+* Lambda K :=
  MvPolynomial.eval₂Hom ((MvPolynomial.C : K →+* Lambda K).comp (paramSwapInvHom K))
    fun i => MvPolynomial.C (omegaScalar K i) * MvPolynomial.X i

@[simp]
theorem dualityOmega_C (c : K) :
    dualityOmega K (MvPolynomial.C c) = MvPolynomial.C (paramSwapInvHom K c) := by
  simp [dualityOmega]

/-- `Ω` scales the power sum `p_{k+1}` by its scalar. Stated at `p_{k+1}` rather than `p_k` because
that is where the rule lives: `p_0` is not a generator the rule speaks about, and
`HJO.Sym.powerSum K 0` is the same generator as `p_1` by the truncated subtraction. -/
@[simp]
theorem dualityOmega_powerSum (k : ℕ) :
    dualityOmega K (powerSum K (k + 1))
      = MvPolynomial.C (omegaScalar K k) * powerSum K (k + 1) := by
  simp [dualityOmega, powerSum]

/-- **The exchange fixes the elementary symmetric functions.**
`Θ(e_r) = e_r` for every `r ≥ 0` (the `r ≥ 0` includes `e_0 = 1`).

Nothing about the exchange in particular is used: `e_r` is a combination of products of power sums
with RATIONAL coefficients -- the scalars of Newton's identity are `(-1)^k / n` -- and every
parameter automorphism of `𝕜` here is a `ℚ`-algebra map, so it fixes those scalars while
`coeffSubst` fixes the power sums. That is exactly `HJO.Ascent.lambdaMap_elemSymm`, read at the
exchange rather than at an ascent embedding, which is available because `Θ` and the coefficient
extension are the same construction: both are `MvPolynomial.map` on the coefficients. -/
@[hjo "lem_dua_swap_esymm"]
theorem dualitySwap_elemSymm (r : ℕ) : dualitySwap K (elemSymm K r) = elemSymm K r := by
  have h := lambdaMap_elemSymm (φ := toRatAlgHom (paramSwapHom K)) r
  rwa [lambdaMap_apply] at h

end HJO.Ascent
