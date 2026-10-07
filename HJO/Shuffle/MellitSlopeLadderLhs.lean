/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.MellitSlopeLadder
public import HJO.Shuffle.MellitLhsCompNoInduction
public import HJO.Shuffle.Completion
public import HJO.Shuffle.MellitShiftAlgebra
public meta import HJO.Attr

/-! # What the `(2,3)` ladder does to the creation side, and what it does not do

`HJO.Sym.qop_ladder` makes the family `Q_{2N+1,3N+2}` the orbit of `D_2` under one fixed map, and
`HJO.Sym.qop_ladder_apply_one_binomial` evaluates it at the vacuum in a closed form whose only
`Λ`-valued inputs are the powers `Q_{2,3}^m(1)`. The question this file settles is whether that
closes the creation side of `HJO.Mellit.LhsWord` at `(a,b) = (2,3)`.

**It does not.** Two things are proved, and they point opposite ways.

## The positive half: at `(2,3)` a slope homomorphism has a two-generator image

`HJO.Sym.split_two_three` — `Split 2 3 = (1,1)`, so `Q_{2,3}` is itself a normalised bracket of the
base cases: `HJO.Sym.qop_two_three_eq_bracket_dop` gives `Q_{2,3} = M⁻¹(D_2D_1 - D_1D_2)`. That
makes the collinear bracket of `HJO.Mellit.qop_two_three_collinear_bracket` valid at `k = 1` as
well, so the whole axis prescription collapses to a single formula with no case split
(`HJO.Sym.qop_two_three_axis_eq_ladder`):

  `Θ(U_k) = Q_{2k,3k} = M⁻¹( L_{k-1}D_1 - D_1L_{k-1} )`,  `L_j = (ad_{2,3})^j(D_2)`,  `k ≥ 1`.

Since `ad_{2,3}` is itself a bracket against `Q_{2,3}`, every `L_j` and hence every `Θ(U_k)` is a
word in the two fixed operators `D_1` and `D_2`, and because the axis generators generate `Λ`
(`HJO.Sym.adjoin_axisGen_eq_top`) so is *every* value of `Θ`:

  `HJO.Sym.theta_mem_dopTwoAlgebra`: `Θ f ∈ L[D_1, D_2]` for every `f ∈ Λ`.

This is a real gain over the obstruction recorded in
`HJO/Shuffle/MellitLhsCompNoInduction.lean` — that the clause at total degree `N` reads
`Q_{2N,3N}`, an operator of unbounded index that no lower-degree clause mentions. After the ladder,
no index moves with `N` at all: only the *length* of the word in `D_1, D_2` does. The obstruction as
stated there is removed.

## The negative half: the removal is a rewriting, and the orbit is not what remains

Two separate reasons, in increasing sharpness.

**The substitution is a no-op.** `HJO.Sym.ladderSlopeHom_iff_isSlopeHom` — the ladder description of
`Θ` is *equivalent* to `HJO.Sym.IsSlopeHom 2 3 q u Θ`, being one rewrite by an unconditional
identity in each direction. So `HJO.Mellit.lhsWord_two_three_iff_lhsWordLadder`: the clause with the
ladder substituted into its hypothesis on `Θ` is the same proposition as the clause. Nothing is
transported. This is the same pattern as `HJO.Mellit.lhsWord_iff_lhsVecAppendStep` — a
reformulation whose datum is already a theorem carries no content.

**The orbit `Q_{2,3}^m(1)` is not the remaining input.** `Θ(U_k)` is a *bracket*, so its value at
the vacuum is `M⁻¹( L_{k-1}(D_1(1)) - D_1(L_{k-1}(1)) )`, and the first branch asks the rung for its
value at `D_1(1) = -e_1`, not at the vacuum. Concretely, at the smallest composition beyond the
singleton case (`HJO.Sym.qop_four_six_apply_one_eq_ladder_at_elemSymm_one`, and with `Θ` in
`HJO.Mellit.theta_copComp_one_one_two_three_apply_one`):

  `Q_{4,6}(1) = M⁻¹( -Q_{3,5}(e_1) - D_1(Q_{3,5}(1)) )`.

The orbit lies in degrees `0, 3, 6, …` (`HJO.Sym.qop_pow_apply_one_mem_lambdaComp`, from
`HJO.Sym.qop_shiftsDegree`) and `e_1` lies in `Λ_1`, so `Q_{3,5}(e_1)` is not a value the closed
form names. `HJO.Sym.collinearBracket_apply_one_not_determined_by_orbit` makes that sharp in the
strongest available sense: two operators agreeing on the **whole** orbit whose brackets with `D_1`
differ at the vacuum — the zero map, and the degree-one graded component `HJO.Sym.lambdaComponent`.
So no handle on the orbit alone, however complete, determines the creation side.

This is the exact analogue, one level up, of `HJO.Sym.ladderTwoThree_apply_one_not_determined`, and
it is *not* implied by it: that theorem separates operators agreeing at the vacuum alone, and the
orbit is strictly more data than the vacuum. What the creation side actually needs is the family of
words in `D_1, D_2` applied to the vacuum, whose length grows with the total degree — a strictly
larger object than one operator's orbit.

## What is *not* claimed

Nothing here refutes `hlhs`, and nothing here says the two-generator description is useless. It is
the best available description of `Θ` at `(2,3)` and it does delete the growing-index obstruction.
What is settled is that it is not a proof and does not reduce the clause: the clause equates the
creation side to the sweep side, and no statement about the creation side alone — however closed —
touches that equation. The two routes that would have consumed such a statement are independently
closed: the opposite-ends induction in all three data
(`HJO.Mellit.lhsWord_iff_lhsVecAppendStep`, `HJO.Mellit.lhsWord_iff_lhsOpAppendStep`) and the
value-carrying step at `(2,3)` (`HJO.Sweep.not_exists_factorization_two_three`). The ladder touches
neither.

## Genericity

`HJO.Sym.split_two_three`, `HJO.Sym.qop_two_three_eq_bracket_dop`,
`HJO.Sym.qop_two_three_axis_eq_ladder`, `HJO.Sym.ladderSlopeHom_iff_isSlopeHom`, the four
`dopTwoAlgebra` membership lemmas, `HJO.Sym.qop_pow_shiftsDegree`,
`HJO.Sym.qop_pow_apply_one_mem_lambdaComp`,
`HJO.Sym.qop_four_six_apply_one_eq_ladder_at_elemSymm_one` and
`HJO.Mellit.lhsWord_two_three_iff_lhsWordLadder`: **none**. Every `M⁻¹` is `HJO.Sym.Qop`'s own and
is carried in the statement rather than cancelled, so at `M = 0` these read `0 = 0` — the
totalisation of `HJO.Sym.Qop`, true and empty, not a false clause.

`HJO.Sym.theta_mem_dopTwoAlgebra`: `CharZero L`, `qu ≠ 0` and `(qu)^{j+1} ≠ 1` for every `j` —
verbatim `HJO.Sym.adjoin_axisGen_eq_top`'s, i.e. the free generation of `Λ` by the axis generators,
without which `Θ f` is not determined at all. Algebraic independence of `q, u` supplies them.

`HJO.Sym.collinearBracket_apply_one_not_determined_by_orbit`: `M ≠ 0`, and nothing else. At `M = 0`
the bracket is the zero map on both sides and there is nothing to separate; `M ≠ 0` holds at
algebraically independent `q, u`. The hypothesis is explicit and not inside a definition, so no
letter here silently becomes the zero map.

`HJO.Mellit.theta_copComp_one_one_two_three_apply_one`: `qu ≠ 0` and `qu ≠ 1`, verbatim
`HJO.Mellit.theta_copComp_one_one`'s, which are `HJO.Sym.axisGen_one`'s.

## References

This file concerns `HJO.Sym.Split`, `HJO.Sym.DopInt`, `HJO.Sym.Qop`, `HJO.Sym.IsSlopeHom`,
`HJO.Sym.axisGen`, `HJO.Sym.Cop`, `HJO.Mellit.lhsRewrite_sweepWitness`.
-/

@[expose] public section

namespace HJO.Sym

variable {L : Type*} [Field L] [Algebra ℚ L]

/-! ### The base rung is itself a bracket of the two basic operators -/

/-- `Split 2 3 = (1,1)`: the bounded search of `HJO.Sym.Split` at `(2,3)` returns `(1,1)`, the only
pair with `1 ≤ r < 2`, `1 ≤ s < 3` and `2s + 1 = 3r`. -/
theorem split_two_three : Split 2 3 = (1, 1) := by decide

/-- **`Q_{2,3}` is itself a normalised bracket of `D_2` and `D_1`.** `HJO.Sym.Qop`'s primitive
recursion at the coprime slope `(2,3)` peels the split `(1,1)`, and both halves are base cases:
`Q_{1,2} = D_2` and `Q_{1,1} = D_1`. Unconditional in `q` and `u`. -/
theorem qop_two_three_eq_bracket_dop (q u : L) : Qop q u 2 3
    = ((1 - q) * (1 - u))⁻¹ • (Dop q u 2 * Dop q u 1 - Dop q u 1 * Dop q u 2) := by
  have h := qop_of_coprime q u (m := 2) (n := 3) (by norm_num) (by decide)
  rw [split_two_three] at h
  norm_num only at h
  rw [h, qop_one, qop_one]

/-! ### Every axis value of a `(2,3)` slope homomorphism, uniformly -/

/-- **The whole axis prescription at `(2,3)`, in one formula valid at every `k ≥ 1`.**

  `Q_{2k,3k} = M⁻¹ ( L_{k-1} D_1 - D_1 L_{k-1} )`,  `L_j = (ad_{2,3})^j (D_2)`.

At `k = 1` this is `HJO.Sym.qop_two_three_eq_bracket_dop`, with `L_0 = D_2`; at `k ≥ 2` it is
`HJO.Mellit.qop_two_three_collinear_bracket` composed with
`HJO.Sym.qop_two_three_complement_eq_ladder`. So the two indexings agree at the boundary and no
case split survives into the statement.

Unconditional in `q` and `u`; at `M = 0` both sides are the zero map, which is `HJO.Sym.Qop`'s
totalisation and not a property of the slope operators. -/
theorem qop_two_three_axis_eq_ladder (q u : L) {k : ℕ} (hk : 1 ≤ k) :
    Qop q u (2 * k) (3 * k) = ((1 - q) * (1 - u))⁻¹ •
      ((ladderTwoThree q u)^[k - 1] (Dop q u 2) * Dop q u 1 -
        Dop q u 1 * (ladderTwoThree q u)^[k - 1] (Dop q u 2)) := by
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · obtain rfl : k = 1 := by omega
    rw [show 2 * 1 = 2 from rfl, show 3 * 1 = 3 from rfl, show 1 - 1 = 0 from rfl,
      Function.iterate_zero_apply]
    exact qop_two_three_eq_bracket_dop q u
  · rw [Mellit.qop_two_three_collinear_bracket q u hk2,
      qop_two_three_complement_eq_ladder q u hk, qop_one]

/-! ### The image of a `(2,3)` slope homomorphism sits in a two-generator subalgebra -/

/-- The subalgebra of operators generated by the two basic operators `D_1` and `D_2`. -/
noncomputable def dopTwoAlgebra (q u : L) : Subalgebra L (Module.End L (Lambda L)) :=
  Algebra.adjoin L {Dop q u 1, Dop q u 2}

theorem dop_one_mem_dopTwoAlgebra (q u : L) : Dop q u 1 ∈ dopTwoAlgebra q u :=
  Algebra.subset_adjoin (by simp)

theorem dop_two_mem_dopTwoAlgebra (q u : L) : Dop q u 2 ∈ dopTwoAlgebra q u :=
  Algebra.subset_adjoin (by simp)

theorem qop_two_three_mem_dopTwoAlgebra (q u : L) : Qop q u 2 3 ∈ dopTwoAlgebra q u := by
  rw [qop_two_three_eq_bracket_dop]
  exact Subalgebra.smul_mem _ (sub_mem
    (mul_mem (dop_two_mem_dopTwoAlgebra q u) (dop_one_mem_dopTwoAlgebra q u))
    (mul_mem (dop_one_mem_dopTwoAlgebra q u) (dop_two_mem_dopTwoAlgebra q u))) _

/-- One rung of the ladder stays in the two-generator subalgebra: the step is a normalised
commutator against `Q_{2,3}`, which is there by `HJO.Sym.qop_two_three_mem_dopTwoAlgebra`. -/
theorem ladderTwoThree_mem_dopTwoAlgebra (q u : L) {A : Module.End L (Lambda L)}
    (hA : A ∈ dopTwoAlgebra q u) : ladderTwoThree q u A ∈ dopTwoAlgebra q u := by
  rw [ladderTwoThree]
  exact Subalgebra.smul_mem _ (sub_mem (mul_mem hA (qop_two_three_mem_dopTwoAlgebra q u))
    (mul_mem (qop_two_three_mem_dopTwoAlgebra q u) hA)) _

/-- Every rung of the ladder is a word in `D_1` and `D_2`. -/
theorem iterate_ladderTwoThree_mem_dopTwoAlgebra (q u : L) (j : ℕ) :
    (ladderTwoThree q u)^[j] (Dop q u 2) ∈ dopTwoAlgebra q u := by
  induction j with
  | zero => rw [Function.iterate_zero_apply]; exact dop_two_mem_dopTwoAlgebra q u
  | succ j ih => rw [Function.iterate_succ_apply']; exact ladderTwoThree_mem_dopTwoAlgebra q u ih

/-- **Every axis value of a `(2,3)` slope homomorphism is a word in `D_1` and `D_2`.** -/
theorem qop_two_three_axis_mem_dopTwoAlgebra (q u : L) {k : ℕ} (hk : 1 ≤ k) :
    Qop q u (2 * k) (3 * k) ∈ dopTwoAlgebra q u := by
  rw [qop_two_three_axis_eq_ladder q u hk]
  exact Subalgebra.smul_mem _ (sub_mem
    (mul_mem (iterate_ladderTwoThree_mem_dopTwoAlgebra q u _) (dop_one_mem_dopTwoAlgebra q u))
    (mul_mem (dop_one_mem_dopTwoAlgebra q u)
      (iterate_ladderTwoThree_mem_dopTwoAlgebra q u _))) _

/-- **The whole image of a `(2,3)` slope homomorphism lies in the two-generator subalgebra.**

The axis generators generate `Λ` (`HJO.Sym.adjoin_axisGen_eq_top`), the preimage of a subalgebra
under an algebra homomorphism is a subalgebra, and every axis generator is sent into
`HJO.Sym.dopTwoAlgebra` by `HJO.Sym.qop_two_three_axis_mem_dopTwoAlgebra`. So *no* operator in the
image of `Θ` has an index moving with anything.

Genericity: `qu ≠ 0` and `(qu)^{j+1} ≠ 1` for every `j` — verbatim the hypotheses of
`HJO.Sym.adjoin_axisGen_eq_top`, without which `Θ` is not determined at all — and `CharZero L`,
which is the same lemma's. All three hold at algebraically independent `q, u`. Nothing is spent on
`M`: this is a membership statement, true (and empty) at `M = 0` where both `Q`s are zero. -/
theorem theta_mem_dopTwoAlgebra [CharZero L] {q u : L} (hv0 : q * u ≠ 0)
    (hv1 : ∀ j : ℕ, (q * u) ^ (j + 1) ≠ 1)
    {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)} (hΘ : IsSlopeHom 2 3 q u Θ) (f : Lambda L) :
    Θ f ∈ dopTwoAlgebra q u := by
  have hle : Algebra.adjoin L (axisGen (q * u) '' Set.Ici 1)
      ≤ (dopTwoAlgebra q u).comap Θ := by
    rw [Algebra.adjoin_le_iff]
    rintro g ⟨k, hk, rfl⟩
    have hk1 : 1 ≤ k := Set.mem_Ici.mp hk
    rw [SetLike.mem_coe, Subalgebra.mem_comap, hΘ k hk1]
    exact qop_two_three_axis_mem_dopTwoAlgebra q u hk1
  rw [adjoin_axisGen_eq_top hv0 hv1] at hle
  exact (Subalgebra.mem_comap _ _ _).1 (hle (Algebra.mem_top (R := L) (x := f)))

/-! ### The ladder description of `Θ` is equivalent to being a slope homomorphism -/

/-- **The ladder description of a `(2,3)` slope homomorphism**: the prescription of
`HJO.Sym.IsSlopeHom` at `(a,b) = (2,3)` with the right-hand side rewritten through the ladder, so
that the only operators named are `D_1` and `D_2`. -/
def LadderSlopeHom (q u : L) (Θ : Lambda L →ₐ[L] Module.End L (Lambda L)) : Prop :=
  ∀ k : ℕ, 0 < k → Θ (axisGen (q * u) k) = ((1 - q) * (1 - u))⁻¹ •
    ((ladderTwoThree q u)^[k - 1] (Dop q u 2) * Dop q u 1 -
      Dop q u 1 * (ladderTwoThree q u)^[k - 1] (Dop q u 2))

/-- **The ladder description is `HJO.Sym.IsSlopeHom` at `(2,3)`, not a strengthening or a
weakening of it.** Both directions are one rewrite by `HJO.Sym.qop_two_three_axis_eq_ladder`, which
is an unconditional identity. Unconditional in `q` and `u`. -/
theorem ladderSlopeHom_iff_isSlopeHom (q u : L)
    (Θ : Lambda L →ₐ[L] Module.End L (Lambda L)) :
    LadderSlopeHom q u Θ ↔ IsSlopeHom 2 3 q u Θ := by
  rw [LadderSlopeHom, IsSlopeHom]
  refine forall_congr' fun k => imp_congr_right fun hk => ?_
  rw [qop_two_three_axis_eq_ladder q u hk]

/-! ### The orbit of the vacuum lives in degrees divisible by three -/

/-- A power of a slope operator shifts degree by its second index times the exponent. -/
theorem qop_pow_shiftsDegree (q u : L) (m n j : ℕ) :
    ShiftsDegree ((n * j : ℕ) : ℤ) (Qop q u m n ^ j) := by
  induction j with
  | zero => rw [pow_zero, Nat.mul_zero, Nat.cast_zero]; exact shiftsDegree_one
  | succ j ih =>
    have h := (qop_shiftsDegree q u m n).comp ih
    rw [← pow_succ'] at h
    rwa [show (n : ℤ) + ((n * j : ℕ) : ℤ) = ((n * (j + 1) : ℕ) : ℤ) by push_cast; ring] at h

/-- **The `Q_{2,3}`-orbit of the vacuum sits in degrees `0, 3, 6, …`.** `Q_{m,n}` shifts `Λ`-degree
by `n` (`HJO.Sym.qop_shiftsDegree`) and the vacuum is in degree `0`. Unconditional. -/
theorem qop_pow_apply_one_mem_lambdaComp (q u : L) (m n j : ℕ) :
    (Qop q u m n ^ j) (1 : Lambda L) ∈ LambdaComp L (n * j) := by
  have h := (qop_pow_shiftsDegree q u m n j).apply_mem_lambdaComp (one_mem_lambdaComp L)
  rwa [Nat.zero_add] at h

/-! ### The orbit is not enough: the bracket reads `D_1` of the vacuum, which is in degree one -/

/-- **`D_1` of the vacuum is not in the span of the `Q_{2,3}`-orbit of the vacuum.**
`D_1(1) = -e_1` lies in `Λ_1`, and every `Q_{2,3}^m(1)` lies in `Λ_{3m}`; the degree-one graded
component separates them. Stated as the failure of the orbit to determine a linear functional:
`HJO.Sym.lambdaComponent L 1` kills the whole orbit and not `D_1(1)`. Unconditional. -/
theorem lambdaComponent_one_qop_two_three_pow_apply_one (q u : L) (m : ℕ) :
    lambdaComponent L 1 ((Qop q u 2 3 ^ m) (1 : Lambda L)) = 0 := by
  rw [lambdaComponent_of_mem (qop_pow_apply_one_mem_lambdaComp q u 2 3 m)]
  exact ite_eq_right_iff.2 fun h => absurd h (by omega)

theorem lambdaComponent_one_dop_one_apply_one (q u : L) :
    lambdaComponent L 1 (Dop q u 1 (1 : Lambda L)) = -elemSymm L 1 := by
  rw [dop_one_apply_one, map_neg, lambdaComponent_of_mem (elemSymm_mem_lambdaComp L 1)]
  simp

theorem elemSymm_one_ne_zero : elemSymm L 1 ≠ 0 := by
  rw [elemSymm_one]
  exact MvPolynomial.X_ne_zero _

omit [Algebra ℚ L] in
theorem lambdaComponent_one_apply_one : lambdaComponent L 1 (1 : Lambda L) = 0 := by
  rw [lambdaComponent_of_mem (one_mem_lambdaComp L)]
  exact ite_eq_right_iff.2 fun h => absurd h (by omega)

/-- **The collinear bracket at the vacuum is not a function of the previous operator's values on
the `Q_{2,3}`-orbit of the vacuum.**

`HJO.Sym.qop_two_three_axis_eq_ladder` writes `Θ(U_k)` as `M⁻¹(L_{k-1} D_1 - D_1 L_{k-1})`, so its
value at the vacuum is `M⁻¹ ( L_{k-1}(D_1 1) - D_1(L_{k-1} 1) )`: the first branch asks the rung
`L_{k-1}` for its value at `D_1(1) = -e_1`, which is in degree one and therefore outside the span of
the orbit `{Q_{2,3}^m(1)}` (degrees `0, 3, 6, …`). Two operators agreeing on the *whole* orbit whose
brackets with `D_1` differ at the vacuum: the zero map, and the degree-one graded component
`HJO.Sym.lambdaComponent L 1`.

This is the precise refutation of the hope that a handle on the single orbit `Q_{2,3}^m(1)` is all
the creation side at `(2,3)` still needs. It is the exact analogue, one level up, of
`HJO.Sym.ladderTwoThree_apply_one_not_determined`, and it is *not* implied by it: that theorem
separates two operators agreeing at the vacuum alone, and the orbit is strictly more data.

Spends `M ≠ 0`, which is `HJO.Sym.Qop`'s own normalisation and holds at algebraically independent
`q, u`; at `M = 0` the bracket is the zero map on both sides and there is nothing to separate. -/
theorem collinearBracket_apply_one_not_determined_by_orbit {q u : L}
    (hM : (1 - q) * (1 - u) ≠ 0) :
    ∃ A A' : Module.End L (Lambda L),
      (∀ m : ℕ, A ((Qop q u 2 3 ^ m) (1 : Lambda L))
          = A' ((Qop q u 2 3 ^ m) (1 : Lambda L))) ∧
        ((1 - q) * (1 - u))⁻¹ • (A * Dop q u 1 - Dop q u 1 * A) (1 : Lambda L)
          ≠ ((1 - q) * (1 - u))⁻¹ • (A' * Dop q u 1 - Dop q u 1 * A') (1 : Lambda L) := by
  refine ⟨0, lambdaComponent L 1, fun m => ?_, ?_⟩
  · rw [LinearMap.zero_apply, lambdaComponent_one_qop_two_three_pow_apply_one]
  · have hA' : ((1 - q) * (1 - u))⁻¹ •
        (lambdaComponent L 1 * Dop q u 1 - Dop q u 1 * lambdaComponent L 1) (1 : Lambda L)
        = ((1 - q) * (1 - u))⁻¹ • (-elemSymm L 1) := by
      simp only [LinearMap.sub_apply, Module.End.mul_apply,
        lambdaComponent_one_dop_one_apply_one, lambdaComponent_one_apply_one,
        map_zero, sub_zero]
    rw [hA']
    simp only [zero_mul, mul_zero, sub_zero, smul_zero, LinearMap.zero_apply]
    intro h
    rcases smul_eq_zero.mp h.symm with h1 | h1
    · exact inv_ne_zero hM h1
    · exact elemSymm_one_ne_zero (neg_eq_zero.mp h1)

/-! ### The smallest instance: the clause at the two-part composition reads `Q_{3,5}` at `e_1` -/

/-- **`Q_{4,6}(1)` is not a value of the `(2,3)` ladder at the vacuum.** The doubled slope that the
clause at the two-part composition reads is, by `HJO.Sym.qop_two_three_axis_eq_ladder` at `k = 2`,

  `Q_{4,6}(1) = M⁻¹ ( -Q_{3,5}(e_1) - D_1(Q_{3,5}(1)) )`,

because `D_1(1) = -e_1` (`HJO.Sym.dop_one_apply_one`). The first summand is the *first rung* of the
ladder evaluated at `e_1`, which lies in `Λ_1`; the `Q_{2,3}`-orbit of the vacuum lies in
`Λ_0, Λ_3, Λ_6, …` (`HJO.Sym.qop_pow_apply_one_mem_lambdaComp`). So the closed form of
`HJO.Sym.qop_ladder_apply_one_binomial`, which names only the orbit, does not reach this value.

Unconditional in `q` and `u`. -/
theorem qop_four_six_apply_one_eq_ladder_at_elemSymm_one (q u : L) :
    Qop q u 4 6 (1 : Lambda L)
      = ((1 - q) * (1 - u))⁻¹ • (-Qop q u 3 5 (elemSymm L 1)
          - Dop q u 1 (Qop q u 3 5 (1 : Lambda L))) := by
  have hk := qop_two_three_axis_eq_ladder q u (k := 2) (by omega)
  rw [show 2 * 2 = 4 from rfl, show 3 * 2 = 6 from rfl, show 2 - 1 = 1 from rfl,
    Function.iterate_one, ← qop_three_five_eq_ladder q u] at hk
  rw [hk]
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.mul_apply, dop_one_apply_one,
    map_neg]

end HJO.Sym

namespace HJO.Mellit

open _root_.HJO.Sym

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-- **The creation side of the clause at the two-part composition, at `(2,3)`, in the ladder's
vocabulary.** Substituting `HJO.Sym.qop_four_six_apply_one_eq_ladder_at_elemSymm_one` into
`HJO.Mellit.theta_copComp_one_one` at `(a,b) = (2,3)`:

  `(qu+1)·Θ(C_1C_1(1))(1)`
    `= (u+1)·Q_{2,3}(Q_{2,3}(1)) + u(q-1)M⁻¹( -Q_{3,5}(e_1) - D_1(Q_{3,5}(1)) )`.

Every operator named is `Q_{2,3}`, `Q_{3,5} = ad_{2,3}(D_2)` or `D_1`, so the ladder has indeed
removed every growing index from the creation side — but of the four `Λ`-valued inputs only
`Q_{2,3}(Q_{2,3}(1))` and `Q_{3,5}(1)` are values at the vacuum. `Q_{3,5}(e_1)` is the first ladder
rung at a degree-one argument, and `D_1(Q_{3,5}(1))` applies a second operator to the rung's value.
Neither is named by `HJO.Sym.qop_ladder_apply_one_binomial`, and this is already the *smallest*
composition the clause's singleton case does not cover.

Genericity: `qu ≠ 0` and `qu ≠ 1`, verbatim `HJO.Mellit.theta_copComp_one_one`'s, which are
`HJO.Sym.axisGen_one`'s. The `M⁻¹` is `HJO.Sym.Qop`'s own and is carried, not cancelled, so nothing
here becomes the zero map by inadvertence; at `M = 0` the identity is the true and empty `0 = 0` in
the doubled-slope term. -/
theorem theta_copComp_one_one_two_three_apply_one (hv0 : q * u ≠ 0) (hv1 : q * u ≠ 1)
    {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)} (hΘ : IsSlopeHom 2 3 q u Θ) :
    (q * u + 1) • Θ (CopComp q [1, 1] (1 : Lambda L)) (1 : Lambda L)
      = (u + 1) • Qop q u 2 3 (Qop q u 2 3 (1 : Lambda L))
        + (u * (q - 1)) • (((1 - q) * (1 - u))⁻¹ • (-Qop q u 3 5 (elemSymm L 1)
            - Dop q u 1 (Qop q u 3 5 (1 : Lambda L)))) := by
  have h := congrArg (fun T : Module.End L (Lambda L) => T (1 : Lambda L))
    (theta_copComp_one_one hv0 hv1 hΘ)
  simp only [LinearMap.smul_apply, LinearMap.add_apply, Module.End.mul_apply] at h
  rw [show (2 * 2 : ℕ) = 4 from by norm_num, show (3 * 2 : ℕ) = 6 from by norm_num,
    qop_four_six_apply_one_eq_ladder_at_elemSymm_one] at h
  exact h

/-- **`HJO.Mellit.LhsWord` at `(2,3)` with the ladder substituted into the hypothesis on `Θ`.**
Every operator named in the prescription is `D_1` or `D_2`; no index moves with `k`. -/
def LhsWordLadder (q u : L) : Prop :=
  ∀ Θ : Lambda L →ₐ[L] Module.End L (Lambda L), LadderSlopeHom q u Θ →
    ∀ N : ℕ, 0 < N → ∀ α : List ℕ, (∀ x ∈ α, 0 < x) → α.sum = N →
      (-1 : L) ^ (N * (3 + 1)) • Θ (CopComp q α 1) 1
        = ((-1 : L) ^ ((2 - 1) * N) * q ^ ((α.length : ℤ) - (N : ℤ))) •
            MvPolynomial.constantCoeff (lowerRun q α.length (stageWordTotal q u 2 3 α))

/-- **The ladder substitution transports nothing.** The clause at `(2,3)` with the ladder
description of `Θ` in place of `HJO.Sym.IsSlopeHom` is the *same* proposition, because
`HJO.Sym.ladderSlopeHom_iff_isSlopeHom` is an equivalence. Unconditional in `q` and `u`.

This is the answer to whether the ladder makes `HJO.Mellit.LhsWord q u 2 3` provable: it rewrites
one side of the clause by an identity, and a rewriting by an identity is a bijection on proofs. It
is the same phenomenon as `HJO.Mellit.lhsWord_iff_lhsVecAppendStep` — a reformulation whose datum
is already a theorem carries no content. -/
theorem lhsWord_two_three_iff_lhsWordLadder (q u : L) :
    LhsWord q u 2 3 ↔ LhsWordLadder q u := by
  rw [LhsWord, LhsWordLadder]
  exact forall_congr' fun Θ => imp_congr_left (ladderSlopeHom_iff_isSlopeHom q u Θ).symm

end HJO.Mellit
