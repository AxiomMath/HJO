/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.Parameters
public import HJO.PlethysticAlphabet
public meta import HJO.Attr

/-! # Negating the alphabet exchanges the two families

`HJO.Sym.plethNegate_completeHomog`: `ω₋(h_n) = (-1)ⁿ eₙ` for every `n ≥ 0`, where `ω₋` is the
substitution `f ↦ f[-X]` of `HJO.Sym.plethNegate`.

## The proof is one instance of a general principle

`HJO.Sym.completeHomog_neg_scale_alphabet` already says that a homomorphism `ψ`
with `ψ(p_j) = -(cʲ φ(p_j))` on every positive `p_j` satisfies `ψ(hₙ) = (-1)ⁿ cⁿ φ(eₙ)`. The
map `ω₋` is that principle at `φ = id` and `c = 1`, since `ω₋(p_j) = -p_j`; so the induction
on Newton's identity is already done, once, in
`HJO.PlethysticAlphabet`, and is not repeated here.

The textbook proof runs the induction again and divides by `n`, which is why it needs
`𝕜 ⊇ ℚ`. That hypothesis is still present here — it is what defines `hₙ` and `eₙ` at all
(`HJO.Sym.completeHomog` and `HJO.Sym.elemSymm` are given by Newton's identities) — but it is spent
inside the general principle rather than here.

## The scalar is `-1` at every degree, and not `(-1)ᵏ`

`HJO.Sym.plethNegate` sends `p_k` to `-p_k`, the power sums being additive in the alphabet; the
scaling `HJO.Sym.plethScale (-1)` instead multiplies `p_k` by `(-1)ᵏ`, and the two maps differ at
every even `k` as soon as `2 ≠ 0`. That separation is recorded on `plethNegate` itself, and
`HJO.Sym.plethNegate_eq_plethScale_omegaStd` is the bridge between them. Under the wrong reading
this lemma would say `ω₋(hₙ) = eₙ`, with no sign.

## Main results

* `HJO.Sym.plethNegate_completeHomog`: `ω₋(hₙ) = (-1)ⁿ eₙ`.

## References

The file formalises the lemma `HJO.Sym.plethNegate_completeHomog` and the definition
`HJO.Sym.plethNegate`.
-/

@[expose] public section

namespace HJO.Sym

/-- **Negating the alphabet exchanges the two families.**
`ω₋(hₙ) = (-1)ⁿ eₙ` for every `n ≥ 0`.

This is `HJO.Sym.completeHomog_neg_scale_alphabet` at `φ = id` and `c = 1`: `ω₋(p_j) = -p_j` is
`-(1ʲ · id(p_j))`, so the general principle gives `ω₋(hₙ) = (-1)ⁿ 1ⁿ eₙ`. -/
@[hjo "lem_negate_hsymm"]
theorem plethNegate_completeHomog (K : Type*) [CommRing K] [Algebra ℚ K] (n : ℕ) :
    plethNegate K (completeHomog K n) = (-1) ^ n * elemSymm K n := by
  have h : ∀ j : ℕ, 0 < j →
      plethNegate K (powerSum K j)
        = -((1 : Lambda K) ^ j * (AlgHom.id K (Lambda K)) (powerSum K j)) := by
    intro j _
    rw [one_pow, one_mul, AlgHom.id_apply, plethNegate_powerSum]
  have := completeHomog_neg_scale_alphabet (K := K) (AlgHom.id K (Lambda K)) (plethNegate K)
    (1 : Lambda K) h n
  rwa [one_pow, mul_one, AlgHom.id_apply] at this

end HJO.Sym
