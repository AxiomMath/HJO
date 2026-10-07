/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.CharP.Algebra
public import HJO.Evaluation.PhiPoly
public import HJO.Symmetric.AxisFree
public meta import HJO.Attr

/-! # The collinear commutation input, with the slope homomorphism removed

`HJO.External.CollinearCommutation` is a conjunction of two clauses: the collinear slope operators
`Q_{ka, kb}`, `k ≥ 1`, pairwise commute, and a slope homomorphism at `(a, b)` exists. Only the
first clause is quoted from the literature. The second follows from it: commuting operators
prescribe an algebra homomorphism on the power sums, and composing with the inverse of the axis
substitution turns that into a slope homomorphism, which is `HJO.Sym.exists_isSlopeHom`.

This file states the commutation clause on its own and proves that the two-clause assumption
follows from it, so that the redundancy of the second clause is a compiled fact rather than a
claim. It is additive: `HJO.External.CollinearCommutation` is left as it is, and a consumer that
still takes it can be supplied from the narrowed form by `collinearCommutation`.

The two genericity facts `exists_isSlopeHom` needs -- that `v = q u` is nonzero and not a root of
unity -- come from the algebraic independence the quoted statement is already stated at, by the
same argument as `HJO.Assembly.generic_of_algebraicIndependent` but for arbitrary parameters
rather than for a parameter extended from a coefficient field.
-/

@[expose] public section

namespace HJO.CollinearNarrowed

/-! ### Consequences of algebraic independence -/

variable {L : Type*} [CommRing L] {q u : L}

/-- The product of two algebraically independent parameters is nonzero: otherwise the product of
the two variables would be the zero polynomial, which it is not at `(1, 1)`. -/
@[hjo "lem_generic_v_ne_zero"]
theorem mul_ne_zero_of_algebraicIndependent (hqu : AlgebraicIndependent ℤ ![q, u]) :
    q * u ≠ 0 := fun h => by
  have h0 : (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) ℤ) = 0 :=
    PhiPoly.eq_of_aeval_eq hqu (by simp [h])
  have h1 := congrArg (MvPolynomial.aeval ![(1 : ℤ), 1]) h0
  simp at h1

/-- The product of two algebraically independent parameters is not a root of unity: otherwise a
positive power of the product of the two variables would be `1`, which it is not at `(0, 0)`. -/
@[hjo "lem_generic_v_not_root_of_unity"]
theorem pow_succ_ne_one_of_algebraicIndependent (hqu : AlgebraicIndependent ℤ ![q, u]) (j : ℕ) :
    (q * u) ^ (j + 1) ≠ 1 := fun h => by
  have h0 : (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) ℤ) ^ (j + 1) = 1 :=
    PhiPoly.eq_of_aeval_eq hqu (by simp [h])
  have h1 := congrArg (MvPolynomial.aeval ![(0 : ℤ), 0]) h0
  simp at h1

/-! ### The narrowed input -/

/-- **Bergeron–Garsia–Leven–Xin, `Compositional (km,kn)-shuffle conjectures`, Theorem 5.1**: the
collinear slope operators `Q_{ka, kb}`, `k ≥ 1`, pairwise commute. This is the whole of what that
theorem supplies, and it is `HJO.External.CollinearCommutation` without its second conjunct: the
genericity hypothesis is kept because Bergeron–Garsia–Leven–Xin work at generic parameters, but the
existence of a slope homomorphism is not asked for. -/
@[hjo "lem_collinear_commute"]
def CollinearCommute (L : Type*) [Field L] [Algebra ℚ L] : Prop :=
  ∀ a b : ℕ, Nat.Coprime a b → 1 < a → a < b →
    ∀ q u : L, AlgebraicIndependent ℤ ![q, u] →
      ∀ k l : ℕ, 0 < k → 0 < l →
        Commute (Sym.Qop q u (a * k) (b * k)) (Sym.Qop q u (a * l) (b * l))

/-- **The second clause of the collinear input is redundant.** The two-clause assumption
`HJO.External.CollinearCommutation` follows from the commutation clause alone: the slope
homomorphism it also asks for is produced from the commuting operators by
`HJO.Sym.exists_isSlopeHom`, whose two genericity hypotheses are supplied by the algebraic
independence the clause is already stated at, and whose characteristic-zero hypothesis by the
rational algebra structure. -/
theorem collinearCommutation {L : Type*} [Field L] [Algebra ℚ L] (h : CollinearCommute L) :
    HJO.External.CollinearCommutation L := by
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  intro a b hab ha hb q u hqu
  exact ⟨h a b hab ha hb q u hqu, Sym.exists_isSlopeHom
    (mul_ne_zero_of_algebraicIndependent hqu) (pow_succ_ne_one_of_algebraicIndependent hqu)
    (h a b hab ha hb q u hqu)⟩

end HJO.CollinearNarrowed
