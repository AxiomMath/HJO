/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.BopModified
public import HJO.CMStructure.StarConjRel1
public import HJO.CMStructure.StarEasy
public import HJO.CMStructure.EvalReduction
public import HJO.Shuffle.SweepWitness
public meta import HJO.Attr

/-! # `z_1` on a general element of `V_1 = Λ[y_1]`

`HJO.Sweep.zopOneStar_one_auxVar_sq` (`HJO/Shuffle/MellitLhsSlopeBase.lean`) evaluates
`z_1` at `k = 1` on `y_1^2`, a monomial with *trivial* `Λ`-coefficient, which is all the slope word
`β_{2,3} = yzy` ever asks for. From `(3, 4)` on, whose word is `β_{3,4} = yzyzy`, the second `z`
letter meets an element with a nontrivial `Λ`-coefficient, and that case needs a separate
evaluation. This file supplies it, for every `C(A)y_1^m` and then for a general element of `V_1`.

## The shape of the answer

At `k = 1` the train of `HJO.Sweep.zop` is empty (`HJO.Braid.trainUp_self`), so

`z_1 = q/(1-q)·(d^*_+{}^{(0)}d_-^{(1)} - d_-^{(2)}d^*_+{}^{(1)})`  on `V_1`,

and each half is a computation already in the library once one fact about `d^*_+` is recorded.

**The first half is the Hall--Littlewood operator followed by the one-letter displacement.**
`d_-^{(1)}(y_1^mC(A)) = C(B_mA)` is `HJO.Sweep.dminus_auxVar_pow_mul_C`
(`HJO.Sweep.dminus_auxVar_pow_mul` on a bare symmetric function), and `d^*_+{}^{(0)}` then adds the
virtual alphabet `(q-1)uy_1` (`HJO.Sweep.dplusStar_C_eq_starGamma`).

**The second half is `B_m` applied coefficientwise in `y_1` after the same displacement.** This is
naturally described as a *two-letter* displacement of `A`, by `(q-1)uy_1 - (q-1)y_2`, followed by
extraction in `y_2` — and it is exactly what `HJO.Sweep.dminus_auxVar_pow_mul` already says, once
the input is put in the form `y_2^m·F` with `F ∈ V_1`. That reshaping is
`HJO.Sweep.dplusStar_one_auxVar_pow_mul_C` below: `d^*_+{}^{(1)}` carries `y_1` to `y_2`
(`HJO.Sweep.dplusStar_auxVar_mul`) and, *on the constants, does not read its level*
(`HJO.Sweep.dplusStar_C_eq_starGamma`), so

`d^*_+{}^{(1)}(y_1^mC(A)) = y_2^m·d^*_+{}^{(0)}(C(A))`,

whose `d_-^{(2)}` is `B_m` on each `y_1`-coefficient, i.e. `HJO.Sweep.bopExt`. The extraction in
`y_2` is therefore not performed by hand here: the second letter `-(q-1)y_2` of the displacement is
the substitution `τ^-_{2,2}` that `HJO.Sweep.dminus_auxVar_pow_mul_C` already integrates against
`HJO.Sym.plethHallLittlewood`, and `y_1` rides through as a spectator because `d_-^{(2)}` is linear
over it.

In particular `HJO.Bglx.plethShiftMulti` is a different displacement — its letter is
`(1-q^j)(1-u^j)z^{-j}`, the alphabet `M/z`, not `(q^j-1)u^jy_1^j - (q^j-1)y_2^j` — and nothing here
reads it. `HJO.Sweep.lowerCoeff_monomial'` is used, but one level down, inside the proof of
`HJO.Sweep.dminus_auxVar_pow_mul_C`. The remaining ingredient, the level-independence of `d^*_+` on
constants, is `HJO.Sweep.dplusStar_C_eq_starGamma`.

## Genericity

**Nothing here needs a hypothesis on `q` or `u`.** The scalar `q^k/(1-q)` of `HJO.Sweep.zop` is
carried symbolically on both sides, exactly as in `HJO.Sweep.zopOneStar_one_auxVar_sq`, so at
`q = 1` the statement reads `0 = 0` and at `q = 0` or `u ∈ {0, 1}` it is the unconditional identity
of two polynomial expressions. The degenerate-parameter conditions of the base case of
`HJO.Mellit.lhsRewrite_sweepWitness` — `q ∉ {0, 1}` and `u ∉ {0, 1}`, the last of these false on a
whole curve by `HJO.Mellit.not_lhsBase_two_three_of_u_eq_one` — enter in the statements that use
this evaluation, from the `(qu)^{-1}` of `HJO.Sweep.slopeOperator` and the `((1-q)(1-u))^{-1}` of
`HJO.Sym.Qop`, not from this evaluation.

## Main results

* `HJO.Sweep.dplusStar_C_level` — `d^*_+` does not read its level on the constants.
* `HJO.Sweep.dplusStar_one_auxVar_pow_mul_C` — `d^*_+{}^{(1)}(y_1^mC(A)) = y_2^md^*_+{}^{(0)}(C A)`.
* `HJO.Sweep.zopOneStar_one_auxVar_pow_mul_C` — `z_1` on `C(A)y_1^m`.
* `HJO.Sweep.zopOneStar_one_auxVar_sq'` — the cross-check: the `(2,3)` evaluation
  `HJO.Sweep.zopOneStar_one_auxVar_sq`, reproved from the general formula.
* `HJO.Sweep.zopOneStar_one_of_mem_piece` — `z_1` on a general element of `V_1`.

## What the induction step still needs

With `P := y_1d^*_+{}^{(0)}d_-^{(1)}` and `N := d_-^{(2)}d^*_+{}^{(1)}` on `V_1`, the results below
say `y_1z_1 = q/(1-q)·(P - y_1N)`, so the slope side's letter pair `YZ` of
`HJO.Mellit.slopeEval_mediant` is `-(qu)^{-1}q/(1-q)·(P - y_1N)` and `N` is now computable. The
mediant step of the gluing identity then reduces to an identity of the shape

`M^{-1}(Ξ_2PΞ_1 - Ξ_1PΞ_2) = ±(u(1-q))^{-1}·Ξ_2(P - y_1N)Ξ_1`,   `M = (1-q)(1-u)`,

read after `d_-` on the image of `y_1d^*_+C`. **This does not follow from the mediant factorisation
alone**: `HJO.Mellit.slopeEval_mediant` and `HJO.Mellit.slopeEval_mediant_rev` give
`Ξ_2YZΞ_1 = Ξ_1ZYΞ_2`, i.e. the slope side has *one* value where `HJO.Sym.Qop` has an antisymmetric
commutator, and the scalars `M^{-1}` and `(u(1-q))^{-1}` do not agree — their difference is
`(2u-1)/((1-q)u(1-u))`. So the asymmetry has to be carried by the `N` term, which is a theorem about
`z_1` and not bookkeeping; it is the general form of the `field_simp; ring` that closed `(2,3)` in
`HJO/Shuffle/MellitLhsSlopeBase.lean`. It is a finite computation at `(3,4)`.

## Implementation notes

`HJO.Sweep.zop` is the definition of `z_1`, not of any evaluation of it; the general-slope gluing
identity these evaluations serve is discussed in `HJO/Shuffle/MellitLhsSlopeBase.lean`'s module
docstring.
-/

@[expose] public section

namespace HJO.Sweep

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-! ### `d^*_+` on the constants does not read its level -/

/-- **`d^*_+` is the same substitution on `Λ` at every level.**
`HJO.Sweep.dplusStar_C_eq_starGamma` computes `d^*_+{}^{(k)}(C f)` as the shift by the virtual
alphabet `quy_1 - uy_1` *with no `k` in the answer*; so any two levels agree there. The levels do
**not** agree off the constants: `d^*_+{}^{(k)}` sends `y_i` to `y_{i+1}` only for `i ≤ k`. -/
theorem dplusStar_C_level (q u : L) (j k : ℕ) (f : Sym.Lambda L) :
    dplusStar q u j (MvPolynomial.C f) = dplusStar q u k (MvPolynomial.C f) := by
  rw [dplusStar_C_eq_starGamma, dplusStar_C_eq_starGamma]

/-- **`d^*_+{}^{(1)}(y_1^m C(A)) = y_2^m · d^*_+{}^{(0)}(C A)`.**

Two known facts: `d^*_+{}^{(1)}` raises the index of the multiplier `y_1`
(`HJO.Sweep.dplusStar_auxVar_mul` at `i = k = 1`, iterated by
`HJO.Sweep.map_auxVar_pow_mul_of_map_auxVar_mul`), and on the constant `C A` it is the level-`0`
operator (`HJO.Sweep.dplusStar_C_level`). The point of putting the answer at level `0` is that
`d^*_+{}^{(0)}(C A) ∈ V_1`, which is the hypothesis `HJO.Sweep.dminus_auxVar_pow_mul` spends. -/
theorem dplusStar_one_auxVar_pow_mul_C (q u : L) (m : ℕ) (A : Sym.Lambda L) :
    dplusStar q u 1 ((auxVar 1 : Total L) ^ m * MvPolynomial.C A)
      = (auxVar 2 : Total L) ^ m * dplusStar q u 0 (MvPolynomial.C A) := by
  rw [map_auxVar_pow_mul_of_map_auxVar_mul (Φ := (dplusStar q u 1 : Total L →ₗ[L] Total L))
    (S := (auxVar 2 : Total L)) (dplusStar_auxVar_mul q u le_rfl le_rfl) m (MvPolynomial.C A),
    dplusStar_C_level q u 1 0]

omit [Algebra ℚ L] in
/-- `C A` lies in `V_0`, the constants of the total space being the image of the base `Λ`. -/
theorem C_mem_piece_zero (A : Sym.Lambda L) : (MvPolynomial.C A : Total L) ∈ piece L 0 :=
  Subalgebra.algebraMap_mem _ A

omit [Algebra ℚ L] in
/-- **`d^*_+{}^{(0)}(C A) ∈ V_1`**: the displacement `(q-1)uy_1` introduces `y_1` and nothing
further. -/
theorem dplusStar_zero_C_mem_piece_one (q u : L) (A : Sym.Lambda L) :
    dplusStar q u 0 (MvPolynomial.C A : Total L) ∈ piece L 1 :=
  dplusStar_mem_piece q u (C_mem_piece_zero A)

/-! ### The two halves of `z_1` on `C(A)y_1^m` -/

/-- **The `d_-^{(1)}` half:** `d_-^{(1)}(y_1^mC(A)) = C(B_mA)`, which is
`HJO.Sweep.dminus_auxVar_pow_mul_C` at `k = 0`. -/
theorem dminus_one_auxVar_pow_mul_C (q : L) (m : ℕ) (A : Sym.Lambda L) :
    dminus q 1 ((auxVar 1 : Total L) ^ m * MvPolynomial.C A)
      = MvPolynomial.C (Sym.Bop q (m : ℤ) A) := by
  simpa using dminus_auxVar_pow_mul_C q 0 m A

/-- **The `d_-^{(2)}d^*_+{}^{(1)}` half:** `B_m` applied to each `y_1`-coefficient of the displaced
`A`. This is the two-letter displacement described in the module docstring — the first letter
`(q-1)uy_1` is `d^*_+{}^{(0)}`, the second `-(q-1)y_2` is the `τ^-_{2,2}` inside `d_-^{(2)}` — with
the extraction in `y_2` performed by `HJO.Sweep.dminus_auxVar_pow_mul`, whose hypothesis `F ∈ V_1`
is exactly `HJO.Sweep.dplusStar_zero_C_mem_piece_one`. -/
theorem dminus_two_dplusStar_one_auxVar_pow_mul_C (q u : L) (m : ℕ) (A : Sym.Lambda L) :
    dminus q 2 (dplusStar q u 1 ((auxVar 1 : Total L) ^ m * MvPolynomial.C A))
      = bopExt q (m : ℤ) (dplusStar q u 0 (MvPolynomial.C A : Total L)) := by
  rw [dplusStar_one_auxVar_pow_mul_C]
  simpa using dminus_auxVar_pow_mul q 1 m (dplusStar_zero_C_mem_piece_one q u A)

/-! ### `z_1` on `C(A)y_1^m`, and on a general element of `V_1` -/

/-- **`z_1(C(A)y_1^m) = q/(1-q)·(d^*_+(C(B_mA)) - B_m(d^*_+(C A)))` on `V_1`**, the evaluation the
general-slope base case needs.

`HJO.Sweep.zop` at `k = 1` is `q/(1-q)(d^*_+d_- - d_-d^*_+)T^*_{1↘1}` with an empty train
(`HJO.Braid.trainUp_self`); the two halves are
`HJO.Sweep.dminus_one_auxVar_pow_mul_C` and
`HJO.Sweep.dminus_two_dplusStar_one_auxVar_pow_mul_C`. Both `B_m` on the right are the *same*
Hall--Littlewood operator `HJO.Sym.Bop`, applied to `A` before the displacement in the first
summand and after it — coefficientwise in `y_1`, via `HJO.Sweep.bopExt` — in the second. So `z_1`
on `V_1` measures exactly the failure of `B_m` to commute with the one-letter displacement
`(q-1)uy_1`, which is why it vanishes on the constants and is nonzero already on `y_1^2`.

No hypothesis on `q` or `u`: the scalar `q/(1-q)` is carried symbolically on both sides. -/
theorem zopOneStar_one_auxVar_pow_mul_C (q u : L) (m : ℕ) (A : Sym.Lambda L) :
    zopOneStar q u 1 ((auxVar 1 : Total L) ^ m * MvPolynomial.C A)
      = (q / (1 - q)) • (dplusStar q u 0 (MvPolynomial.C (Sym.Bop q (m : ℤ) A))
          - bopExt q (m : ℤ) (dplusStar q u 0 (MvPolynomial.C A : Total L))) := by
  rw [zopOneStar, show trainUpEnd q 1 1 = 1 from Braid.trainUp_self _ _ 1, mul_one]
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.mul_apply, pow_one,
    Nat.sub_self]
  rw [dminus_one_auxVar_pow_mul_C, show (1 : ℕ) + 1 = 2 from rfl,
    dminus_two_dplusStar_one_auxVar_pow_mul_C]

/-- **Cross-check: the general evaluation reproves `HJO.Sweep.zopOneStar_one_auxVar_sq`.**

At `A = 1` and `m = 2` the two `B_2` of the general formula are both `B_2(1) = e_2`
(`HJO.Sym.bop_one`), and `d^*_+{}^{(0)}` fixes the unit, so the answer collapses to the `(2,3)`
evaluation. The two routes are different above the level of `HJO.Sweep.lowerCoeff`, where they meet:
`HJO.Sweep.zopOneStar_one_auxVar_sq` evaluates `d_-` and `d^*_+` directly on the monomial `y_1^2`
(`HJO.Sweep.dminus_auxVar_pow`, `HJO.Sweep.dplusStar_auxVar_pow`), the one above goes through the
Hall--Littlewood operator and its coefficientwise extension and never names `y_2^2`. So this is the
check that the general formula's `B_m`-shaped answer specialises correctly, not merely that it is
well typed. -/
theorem zopOneStar_one_auxVar_sq' (q u : L) :
    zopOneStar q u 1 ((auxVar 1 : Total L) ^ 2)
      = (q / (1 - q)) • (dplusStar q u 0 (MvPolynomial.C (Sym.elemSymm L 2))
          - MvPolynomial.C (Sym.elemSymm L 2)) := by
  have hb : Sym.Bop q ((2 : ℕ) : ℤ) (1 : Sym.Lambda L) = Sym.elemSymm L 2 := by
    rw [Sym.bop_one, Sym.elemSymmAlt_natCast]
    norm_num
  have h1 : dplusStar q u 0 (1 : Total L) = 1 := by rw [dplusStar_apply, map_one, map_one]
  rw [show ((auxVar 1 : Total L) ^ 2) = (auxVar 1 : Total L) ^ 2 * MvPolynomial.C 1 from by
      rw [MvPolynomial.C_1, mul_one],
    zopOneStar_one_auxVar_pow_mul_C, hb, MvPolynomial.C_1, h1, ← MvPolynomial.C_1, bopExt_C, hb]

omit [Algebra ℚ L] in
/-- Every monomial of an element of `V_1` is a power of `y_1`. -/
theorem exists_single_zero_of_mem_piece_one {G : Total L} (hG : G ∈ piece L 1) {d : ℕ →₀ ℕ}
    (hd : d ∈ G.support) : ∃ m : ℕ, d = Finsupp.single 0 m := by
  rw [piece, MvPolynomial.mem_supported] at hG
  refine ⟨d 0, Finsupp.ext fun n => ?_⟩
  rcases eq_or_ne n 0 with rfl | hn
  · rw [Finsupp.single_eq_same]
  · have hzero : (Finsupp.single 0 (d 0) : ℕ →₀ ℕ) n = 0 := by
      simp [Ne.symm hn]
    rw [hzero]
    by_contra h
    have hmem : n ∈ G.vars := MvPolynomial.mem_vars_iff_mem_support n |>.2
      ⟨d, hd, Finsupp.mem_support_iff.2 h⟩
    exact hn (Nat.lt_one_iff.1 (hG hmem))

/-- **`z_1` on a general element of `V_1`.** Each `y_1`-monomial of `G` is handled by
`HJO.Sweep.zopOneStar_one_auxVar_pow_mul_C`, and the sum over `G.support` is the
expansion `G = ∑_m G_m y_1^m` with `G_m = MvPolynomial.coeff (single 0 m) G` the `Λ`-coefficients.

`G ∈ V_1` is not decoration: on a monomial carrying `y_2` the second half's `d_-^{(2)}` meets a
further power of the variable it extracts in, and `HJO.Sweep.dminus_auxVar_pow_mul` fails there. -/
theorem zopOneStar_one_of_mem_piece (q u : L) {G : Total L} (hG : G ∈ piece L 1) :
    zopOneStar q u 1 G
      = (q / (1 - q)) • ∑ d ∈ G.support,
          (dplusStar q u 0 (MvPolynomial.C (Sym.Bop q ((d 0 : ℕ) : ℤ) (MvPolynomial.coeff d G)))
            - bopExt q ((d 0 : ℕ) : ℤ)
              (dplusStar q u 0 (MvPolynomial.C (MvPolynomial.coeff d G) : Total L))) := by
  conv_lhs => rw [G.as_sum]
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  obtain ⟨m, rfl⟩ := exists_single_zero_of_mem_piece_one hG hd
  have hmon : ∀ a : Sym.Lambda L, (auxVar 1 : Total L) ^ m * MvPolynomial.C a
      = MvPolynomial.monomial (Finsupp.single 0 m) a := by
    intro a
    rw [auxVar, Nat.sub_self, MvPolynomial.X_pow_eq_monomial, mul_comm,
      MvPolynomial.C_mul_monomial, mul_one]
  rw [Finsupp.single_eq_same, ← hmon, zopOneStar_one_auxVar_pow_mul_C]

end HJO.Sweep
