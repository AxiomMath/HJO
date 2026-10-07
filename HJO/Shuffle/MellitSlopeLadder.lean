/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Collinear.SplitSteps
public import HJO.Shuffle.MellitLhsSlopeBase
public meta import HJO.Attr

/-! # The `(2,3)` ladder: the family `Q_{2N-1,3N-1}` is a single ad-orbit of `Q_{2,3}`

`HJO.Mellit.qop_two_three_collinear_bracket` reduces the collinear slope operator `Q_{2N,3N}` that
the two-part clause at `(a,b) = (2,3)` names to the coprime slope operator `Q_{2N-1,3N-1}`, whose
first index is unbounded in `N`. That leaves the whole family

  `Q_{3,5}, Q_{5,8}, Q_{7,11}, …`

to be understood *uniformly in `N`*, and each member is individually reachable by
`HJO.Sym.qop_of_coprime` only because `gcd(2N-1, 3N-1) = 1`; that gives `N` unrelated
computations, not a handle on the family.

This file supplies the handle. The observation is about the split, not about `Λ`:

* `HJO.Sym.split_ladder` — `Split (2N+3) (3N+5) = (2,3)` for **every** `N`, because
  `(2N+3)·3 + 1 = (3N+5)·2` exhibits a solution of the split equation and
  `HJO.Sym.split_unique` makes the solution unique. The split of this family **does not move
  with `N`**.

So the primitive recursion of `HJO.Sym.Qop` peels the *same* fixed coprime slope `(2,3)` off every
member, and the complement is the previous member: `(2N+3) - 2 = 2N+1` and `(3N+5) - 3 = 3N+2`.
That is `HJO.Sym.qop_ladder_step`,

  `Q_{2N+3,3N+5} = M⁻¹ (Q_{2N+1,3N+2} Q_{2,3} - Q_{2,3} Q_{2N+1,3N+2})`,

one normalised commutator against a **fixed** second operand. Iterating it from the base
`Q_{1,2} = D_2` gives `HJO.Sym.qop_ladder`:

  `Q_{2N+1,3N+2} = (ad_{2,3})^N (D_2)`,   `ad_{2,3}(A) = M⁻¹ (A Q_{2,3} - Q_{2,3} A)`,

and `HJO.Sym.qop_ladder_binomial` expands the iterate, the two multiplications by `Q_{2,3}` on
the left and on the right commuting:

  `Q_{2N+1,3N+2} = M^{-N} ∑_{m ≤ N} (-1)^{N-m} \binom{N}{m} Q_{2,3}^{N-m} D_2 Q_{2,3}^{m}`.

At the vacuum (`HJO.Sym.qop_ladder_apply_one_binomial`) this is a closed form in `N` whose only
`Λ`-valued inputs are the orbit `Q_{2,3}^m(1)` of the vacuum under one fixed operator: `N` enters
only as a binomial coefficient, a power of `M⁻¹` and an iteration count.

## What is spent

Nothing. `HJO.Sym.qop_of_coprime` is unconditional, so every statement here holds at every `q, u`,
including the degenerate loci. The identities are *content-bearing* exactly where `M ≠ 0`: at
`M = 0` the inverse totalises to `0`, so `HJO.Sym.Qop` makes every `Q_{m,n}` with `m > 1` the zero
map and the ladder reads `0 = 0`. On the range that matters -- algebraically independent `q, u` --
`M` is a unit and no such collapse occurs. The statements that do spend hypotheses are the three at
the end -- `HJO.Sym.sepThree_qop_two_three_apply_one`,
`HJO.Sym.qop_two_three_apply_one_not_smul_one` and
`HJO.Sym.ladderTwoThree_apply_one_not_determined` -- which quote
`HJO.Sym.qop_two_three_apply_one` and therefore carry its `M ≠ 0`, and additionally spend
`q + u ≠ 1` to make the separating functional nonzero. Both hold at algebraically independent
`q, u`; neither is hidden inside a definition, so no letter here can silently become the zero
map.

## What this does not do

The ladder is an identity between **operators**. Evaluating it at the vacuum does *not* produce a
recursion in the values `Q_{2N-1,3N-1}(1)` alone: the first branch of the commutator asks for
`Q_{2N+1,3N+2}` at `Q_{2,3}(1)`, which is not the vacuum -- `HJO.Sym.qop_two_three_apply_one` makes
it `-e_1e_2 + (1-q-u)e_3`. Two theorems make that sharp:
`HJO.Sym.qop_two_three_apply_one_not_smul_one`, that `Q_{2,3}(1)` is not a scalar multiple of the
vacuum, and `HJO.Sym.ladderTwoThree_apply_one_not_determined`, that the step's value at the vacuum
is therefore not a function of the previous operator's value there. Neither rules out a value
recursion obtained some other way; what they rule out is reading one off the step. The binomial form
is the positive replacement -- the extra data the step consumes is exactly the `Q_{2,3}`-orbit of
the vacuum, and the closed form names it.
-/

@[expose] public section

namespace HJO.Sym

/-! ### The split of the `(2,3)` ladder does not move with `N` -/

/-- The ladder slopes are coprime: `2(3N+5) - 3(2N+3) = 1`, so any common divisor divides `1`.
This is the same Bezout certificate that `HJO.Sym.split_ladder` uses, at the other pairing. -/
@[hjo "lem_qop_two_three_ladder"]
theorem coprime_ladder (N : ℕ) : Nat.Coprime (2 * N + 3) (3 * N + 5) := by
  have ha : Nat.gcd (2 * N + 3) (3 * N + 5) ∣ 3 * (2 * N + 3) :=
    Dvd.dvd.mul_left (Nat.gcd_dvd_left _ _) 3
  have hb : Nat.gcd (2 * N + 3) (3 * N + 5) ∣ 2 * (3 * N + 5) :=
    Dvd.dvd.mul_left (Nat.gcd_dvd_right _ _) 2
  have hsub := Nat.dvd_sub hb ha
  rw [show 2 * (3 * N + 5) - 3 * (2 * N + 3) = 1 from by omega] at hsub
  exact Nat.dvd_one.mp hsub

/-- **The split of the ladder slope is `(2,3)` at every `N`.** The pair `(r,s) = (2,3)` solves the
split equation `(2N+3)·3 + 1 = (3N+5)·2` and lies in the search range for every `N ≥ 0`
(`2 < 2N+3` and `3 < 3N+5`), so `HJO.Sym.split_eq_of_spec` -- uniqueness of the solution --
pins the bounded search to it. Nothing here grows with `N`: this is what makes the family a
ladder rather than `N` unrelated recursions. -/
@[hjo "lem_qop_two_three_ladder"]
theorem split_ladder (N : ℕ) : Split (2 * N + 3) (3 * N + 5) = (2, 3) :=
  split_eq_of_spec (by omega) (coprime_ladder N) (by omega) (by omega) (by omega) (by omega)
    (by omega)

/-! ### The ladder step -/

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **One rung of the ladder.** `HJO.Sym.Qop`'s primitive recursion at the coprime slope
`(2N+3,3N+5)` peels off the split `(2,3)` -- fixed, by `HJO.Sym.split_ladder` -- and leaves the
complement `(2N+3-2, 3N+5-3) = (2N+1, 3N+2)`, the previous rung. Unconditional in `q` and `u`. -/
theorem qop_ladder_step (q u : L) (N : ℕ) :
    Qop q u (2 * N + 3) (3 * N + 5) = ((1 - q) * (1 - u))⁻¹ •
      (Qop q u (2 * N + 1) (3 * N + 2) * Qop q u 2 3 -
        Qop q u 2 3 * Qop q u (2 * N + 1) (3 * N + 2)) := by
  have h := qop_of_coprime q u (m := 2 * N + 3) (n := 3 * N + 5) (by omega) (coprime_ladder N)
  rw [split_ladder N] at h
  rw [h, show 2 * N + 3 - ((2 : ℕ), (3 : ℕ)).1 = 2 * N + 1 from by omega,
    show 3 * N + 5 - ((2 : ℕ), (3 : ℕ)).2 = 3 * N + 2 from by omega]

/-- The normalised adjoint action of the fixed slope operator `Q_{2,3}`: the map
`A ↦ M⁻¹(A Q_{2,3} - Q_{2,3} A)` on the operators of `Λ`. `HJO.Sym.qop_ladder_step` says that one
application of this map climbs the `(2,3)` ladder by one rung, so the whole family is its orbit. -/
noncomputable def ladderTwoThree (q u : L) (A : Module.End L (Lambda L)) :
    Module.End L (Lambda L) :=
  ((1 - q) * (1 - u))⁻¹ • (A * Qop q u 2 3 - Qop q u 2 3 * A)

theorem ladderTwoThree_apply (q u : L) (A : Module.End L (Lambda L)) :
    ladderTwoThree q u A =
      ((1 - q) * (1 - u))⁻¹ • (A * Qop q u 2 3 - Qop q u 2 3 * A) := rfl

/-- **The ladder, closed.** Every member of the `(2,3)` slope family is an iterate of one fixed
map applied to one fixed operator:

  `Q_{2N+1,3N+2} = (A ↦ M⁻¹(A Q_{2,3} - Q_{2,3} A))^N (D_2)`.

The base rung is `Q_{1,2} = D_2` (`HJO.Sym.qop_one`) and the step is
`HJO.Sym.qop_ladder_step`. Unconditional in `q` and `u`; at `M = 0` both sides are the zero map for
`N ≥ 1`, which is an artefact of the totalisation of `HJO.Sym.Qop` and not a property of the
slope operators. -/
@[hjo "lem_qop_two_three_ladder"]
theorem qop_ladder (q u : L) (N : ℕ) :
    Qop q u (2 * N + 1) (3 * N + 2) = (ladderTwoThree q u)^[N] (Dop q u 2) := by
  induction N with
  | zero =>
    rw [Function.iterate_zero_apply, show 2 * 0 + 1 = 1 from rfl, show 3 * 0 + 2 = 2 from rfl,
      qop_one]
  | succ N ih =>
    rw [Function.iterate_succ_apply', ← ih, ladderTwoThree_apply,
      show 2 * (N + 1) + 1 = 2 * N + 3 from by ring, show 3 * (N + 1) + 2 = 3 * N + 5 from by ring]
    exact qop_ladder_step q u N

/-- The ladder in the indexing the two-part clause at `(2,3)` produces: the complement of the
collinear slope `(2N,3N)` is the `(N-1)`-st rung. Valid from `N = 1` on, where it is the base
rung `Q_{1,2} = D_2`. -/
@[hjo "lem_qop_two_three_ladder"]
theorem qop_two_three_complement_eq_ladder (q u : L) {N : ℕ} (hN : 1 ≤ N) :
    Qop q u (2 * N - 1) (3 * N - 1) = (ladderTwoThree q u)^[N - 1] (Dop q u 2) := by
  obtain ⟨j, rfl⟩ : ∃ j, N = j + 1 := ⟨N - 1, by omega⟩
  rw [show 2 * (j + 1) - 1 = 2 * j + 1 from by omega,
    show 3 * (j + 1) - 1 = 3 * j + 2 from by omega, show j + 1 - 1 = j from rfl]
  exact qop_ladder q u j

/-- The ladder at the vacuum, which is where the creation side reads it. -/
theorem qop_ladder_apply_one (q u : L) (N : ℕ) :
    Qop q u (2 * N + 1) (3 * N + 2) (1 : Lambda L)
      = ((ladderTwoThree q u)^[N] (Dop q u 2)) (1 : Lambda L) := by
  rw [qop_ladder]

/-! ### Pins against the independently computed low rungs

`HJO.Sym.qop_three_five_apply_one` (`HJO/Shuffle/MellitTwoPartTwoThreeClause.lean`) computes
`Q_{3,5}(1)` in the `e`-basis from scratch, by `decide`-ing `Split 3 5 = (2,3)` and grinding the
commutator. These two pins say the general ladder lands on the same expression there, and name the
next rung `(5,8)` -- whose value is computed nowhere else in the library -- in the same shape.
-/

/-- The first rung: `Q_{3,5}` is one ladder step off `D_2`. This is `HJO.Sym.qop_ladder` at `N = 1`,
and it is the bracket `HJO.Sym.qop_three_five_apply_one` is proved from. -/
theorem qop_three_five_eq_ladder (q u : L) :
    Qop q u 3 5 = ladderTwoThree q u (Dop q u 2) := by
  have h := qop_ladder q u 1
  norm_num only at h
  exact h

/-- The second rung: `Q_{5,8}` is two ladder steps off `D_2`. No other lemma of the library
evaluates this slope; the ladder reaches it with no new computation. -/
theorem qop_five_eight_eq_ladder (q u : L) :
    Qop q u 5 8 = ladderTwoThree q u (ladderTwoThree q u (Dop q u 2)) := by
  have h := qop_ladder q u 2
  norm_num only at h
  exact h

/-- `Q_{3,5}(1)` as the normalised bracket at the vacuum -- the exact expression
`HJO.Sym.qop_three_five_apply_one` evaluates. Unconditional. -/
theorem qop_three_five_apply_one_eq_bracket (q u : L) :
    Qop q u 3 5 (1 : Lambda L)
      = ((1 - q) * (1 - u))⁻¹ • (Dop q u 2 (Qop q u 2 3 (1 : Lambda L))
          - Qop q u 2 3 (Dop q u 2 (1 : Lambda L))) := by
  rw [qop_three_five_eq_ladder, ladderTwoThree]
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.mul_apply]

/-! ### The iterate expanded: a closed form in `N`

The ladder step is `M⁻¹` times the difference of right and left multiplication by `Q_{2,3}`, and
those two commute -- `(A Q_{2,3}) Q_{2,3} = Q_{2,3} (A Q_{2,3})` is associativity, nothing more.
So the `N`-th iterate is a binomial sum, and `N` leaves the operator indices entirely: it survives
only as a binomial coefficient and an exponent.
-/

/-- The ladder step as a single endomorphism of the operator algebra: `M⁻¹(R - L)`, with `R` and
`L` right and left multiplication by `Q_{2,3}`. This is `HJO.Sym.ladderTwoThree` packaged so that
its iterates are powers in a ring, which is what makes the binomial theorem available. -/
noncomputable def ladderMap (q u : L) : Module.End L (Module.End L (Lambda L)) :=
  ((1 - q) * (1 - u))⁻¹ •
    (LinearMap.mulRight L (Qop q u 2 3) - LinearMap.mulLeft L (Qop q u 2 3))

theorem ladderMap_apply (q u : L) (A : Module.End L (Lambda L)) :
    ladderMap q u A = ladderTwoThree q u A := by
  rw [ladderMap, ladderTwoThree]
  simp [sub_eq_add_neg]

/-- Iterating the ladder step is taking powers of `HJO.Sym.ladderMap`. -/
theorem iterate_ladderTwoThree (q u : L) (N : ℕ) (A : Module.End L (Lambda L)) :
    (ladderTwoThree q u)^[N] A = (ladderMap q u ^ N) A := by
  rw [Module.End.pow_apply]
  congr 1

/-- **The ladder in closed form.** Left and right multiplication by `Q_{2,3}` commute, so the
binomial theorem for commuting elements (`Commute.add_pow`) expands the `N`-th iterate:

  `Q_{2N+1,3N+2} = M^{-N} ∑_{m ≤ N} (-1)^{N-m} \binom{N}{m} Q_{2,3}^{N-m} D_2 Q_{2,3}^{m}`.

`N` appears only as a binomial coefficient, a power of `M⁻¹` and an exponent of the single fixed
operator `Q_{2,3}`; no index of any operator on the right grows with `N` except those exponents.
Unconditional in `q` and `u`. -/
@[hjo "lem_qop_two_three_ladder"]
theorem qop_ladder_binomial (q u : L) (N : ℕ) :
    Qop q u (2 * N + 1) (3 * N + 2)
      = (((1 - q) * (1 - u))⁻¹) ^ N •
        ∑ m ∈ Finset.range (N + 1), ((-1 : L) ^ (N - m) * (N.choose m : L)) •
          (Qop q u 2 3 ^ (N - m) * Dop q u 2 * Qop q u 2 3 ^ m) := by
  rw [qop_ladder, iterate_ladderTwoThree]
  set B := Qop q u 2 3 with hB
  set X : Module.End L (Module.End L (Lambda L)) := LinearMap.mulRight L B with hX
  set Y : Module.End L (Module.End L (Lambda L)) := (-1 : L) • LinearMap.mulLeft L B with hY
  have hc : Commute X Y := by
    rw [hX, hY, Commute, SemiconjBy]
    apply LinearMap.ext
    intro Z
    simp [Module.End.mul_apply, mul_assoc]
  have hsplit : LinearMap.mulRight L B - LinearMap.mulLeft L B = X + Y := by
    rw [hX, hY]; apply LinearMap.ext; intro Z; simp [sub_eq_add_neg]
  rw [ladderMap, smul_pow, hsplit, hc.add_pow]
  simp only [hX, hY, LinearMap.smul_apply, LinearMap.sum_apply, Module.End.mul_apply,
    smul_pow, LinearMap.pow_mulLeft, LinearMap.pow_mulRight, LinearMap.mulLeft_apply,
    LinearMap.mulRight_apply, Module.End.natCast_apply]
  congr 1
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, ← Nat.cast_smul_eq_nsmul L (N.choose d), smul_mul_assoc,
    smul_smul]

/-- **The family at the vacuum, in closed form.** The only `Λ`-valued inputs are the orbit of the
vacuum under the single fixed operator `Q_{2,3}`:

  `Q_{2N+1,3N+2}(1) = M^{-N} ∑_{m ≤ N} (-1)^{N-m} \binom{N}{m} Q_{2,3}^{N-m}(D_2(Q_{2,3}^m(1)))`.

This is the uniform handle the creation side asks for: one formula, valid at every `N`, naming no
operator whose slope moves with `N`. -/
theorem qop_ladder_apply_one_binomial (q u : L) (N : ℕ) :
    Qop q u (2 * N + 1) (3 * N + 2) (1 : Lambda L)
      = (((1 - q) * (1 - u))⁻¹) ^ N •
        ∑ m ∈ Finset.range (N + 1), ((-1 : L) ^ (N - m) * (N.choose m : L)) •
          (Qop q u 2 3 ^ (N - m)) (Dop q u 2 ((Qop q u 2 3 ^ m) (1 : Lambda L))) := by
  rw [qop_ladder_binomial]
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, Module.End.mul_apply]

/-! ### Why the orbit is needed: the step is not a function of the previous value

The ladder is an identity between operators, and the creation side would prefer a recursion in the
*values* `Q_{2N-1,3N-1}(1)`. It does not get one from here, and the reason is sharp: the first
branch of the commutator asks the previous rung for its value at `Q_{2,3}(1)`, and that element is
not a scalar multiple of the vacuum. Two statements below, in increasing strength of what they
rule out.

The separating functional is the difference of two evaluations of `Λ`, both algebra maps:
`HJO.Sym.evalThree` (`p_3 ↦ 1`, every other `p_k ↦ 0`) and the evaluation killing every
power sum. Their difference kills the vacuum, and on `Q_{2,3}(1) = -e_1e_2 + (1-q-u)e_3` it
returns `(1-q-u)/3`.
-/

/-- The evaluation of `Λ` killing every power sum. `HJO.Sym.Lambda` is the *free* polynomial
algebra on the power-sum symbols, so no verification is owed. -/
noncomputable def evalZero (L : Type*) [Field L] [Algebra ℚ L] : Lambda L →ₐ[L] L :=
  MvPolynomial.aeval fun _ => (0 : L)

/-- Every `e_k` with `k ≥ 1` has zero constant term: Newton's identity writes it as a sum each of
whose summands carries a factor `p_{k+1}`. -/
theorem evalZero_elemSymm_succ (n : ℕ) : evalZero L (elemSymm L (n + 1)) = 0 := by
  rw [elemSymm, map_mul, map_sum]
  simp [powerSum, evalZero]

/-- The functional separating `Q_{2,3}(1)` from the vacuum: `evalThree - evalZero`. It is not an
algebra map -- it is a difference of two -- and that is the point: it kills `1`. -/
noncomputable def sepThree (L : Type*) [Field L] [Algebra ℚ L] : Lambda L →ₗ[L] L :=
  (evalThree L).toLinearMap - (evalZero L).toLinearMap

theorem sepThree_one : sepThree L (1 : Lambda L) = 0 := by
  simp [sepThree]

/-- **`sepThree(Q_{2,3}(1)) = (1-q-u)/3`.** `evalThree` kills `e_1` hence the product `e_1e_2`, and
sends `e_3` to `1/3`; `evalZero` kills both degree-`3` monomials. Spends the `M ≠ 0` of
`HJO.Sym.qop_two_three_apply_one` and nothing else. -/
theorem sepThree_qop_two_three_apply_one {q u : L} (hM : (1 - q) * (1 - u) ≠ 0) :
    sepThree L (Qop q u 2 3 (1 : Lambda L))
      = (1 - q - u) * algebraMap ℚ L ((2 + 1 : ℚ))⁻¹ := by
  have h1 : evalZero L (elemSymm L 1) = 0 := evalZero_elemSymm_succ (L := L) 0
  have h3 : evalZero L (elemSymm L 3) = 0 := evalZero_elemSymm_succ (L := L) 2
  rw [qop_two_three_apply_one hM, sepThree]
  simp only [LinearMap.sub_apply, AlgHom.toLinearMap_apply, map_add, map_neg, map_mul,
    MvPolynomial.smul_eq_C_mul, MvPolynomial.algHom_C, evalThree_elemSymm_one,
    evalThree_elemSymm_three, h1, h3, Algebra.algebraMap_self, RingHom.id_apply]
  ring

/-- `1/3 ≠ 0` in a `ℚ`-algebra that is a field: the structure map of a field extension of `ℚ` is
injective. This is the only place characteristic zero is used. -/
theorem algebraMap_three_inv_ne_zero : algebraMap ℚ L ((2 + 1 : ℚ))⁻¹ ≠ 0 := by
  simpa using (map_ne_zero_iff _ (algebraMap ℚ L).injective).mpr
    (by norm_num : ((2 + 1 : ℚ))⁻¹ ≠ 0)

/-- **The element the ladder feeds back is not a multiple of the vacuum.** `Q_{2,3}(1)` is not in
the line `L·1`, so the first branch `Q_{2N+1,3N+2}(Q_{2,3}(1))` of the ladder step genuinely asks
the previous rung for a value the vacuum does not supply. This is the precise reason the operator
ladder does not descend to a recursion in the values at the vacuum alone.

Spends `M ≠ 0` (through `HJO.Sym.qop_two_three_apply_one`) and `q + u ≠ 1`, both of which hold at
algebraically independent `q, u`. At `q + u = 1` the value is `-e_1e_2`, still not a multiple of the
vacuum -- this functional simply does not see it, and a different one is needed there. -/
theorem qop_two_three_apply_one_not_smul_one {q u : L} (hM : (1 - q) * (1 - u) ≠ 0)
    (hqu : q + u ≠ 1) (c : L) : Qop q u 2 3 (1 : Lambda L) ≠ c • (1 : Lambda L) := by
  have hne : (1 : L) - q - u ≠ 0 := fun h0 => hqu (by linear_combination -h0)
  intro h
  have h1 : sepThree L (Qop q u 2 3 (1 : Lambda L)) = 0 := by
    rw [h, map_smul, sepThree_one, smul_zero]
  rw [sepThree_qop_two_three_apply_one hM] at h1
  exact (mul_ne_zero hne algebraMap_three_inv_ne_zero) h1

/-- **The ladder step is not a function of the previous value at the vacuum.** Two operators
agreeing at the vacuum whose ladder steps do not: the zero operator, and `f ↦ sepThree(f)·1`,
which kills the vacuum but not `Q_{2,3}(1)`.

This says that no recursion in the values `Q_{2N-1,3N-1}(1)` can be *read off the ladder step*; it
does not say the family satisfies no value recursion for some other reason. The positive replacement
is `HJO.Sym.qop_ladder_apply_one_binomial`, which names exactly the extra data the step consumes:
the `Q_{2,3}`-orbit of the vacuum. -/
theorem ladderTwoThree_apply_one_not_determined {q u : L} (hM : (1 - q) * (1 - u) ≠ 0)
    (hqu : q + u ≠ 1) :
    ∃ A A' : Module.End L (Lambda L), A (1 : Lambda L) = A' (1 : Lambda L) ∧
      ladderTwoThree q u A (1 : Lambda L) ≠ ladderTwoThree q u A' (1 : Lambda L) := by
  have hne : (1 : L) - q - u ≠ 0 := fun h0 => hqu (by linear_combination -h0)
  have hscal : (((1 - q) * (1 - u))⁻¹ * ((1 - q - u) * algebraMap ℚ L ((2 + 1 : ℚ))⁻¹)) ≠ 0 :=
    mul_ne_zero (inv_ne_zero hM) (mul_ne_zero hne algebraMap_three_inv_ne_zero)
  refine ⟨0, (sepThree L).smulRight (1 : Lambda L), by simp [sepThree_one], ?_⟩
  have hA' : ladderTwoThree q u ((sepThree L).smulRight (1 : Lambda L)) (1 : Lambda L)
      = (((1 - q) * (1 - u))⁻¹ * ((1 - q - u) * algebraMap ℚ L ((2 + 1 : ℚ))⁻¹)) •
        (1 : Lambda L) := by
    rw [ladderTwoThree]
    simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.mul_apply,
      LinearMap.smulRight_apply, sepThree_one, zero_smul, map_zero, sub_zero,
      sepThree_qop_two_three_apply_one hM, smul_smul]
  rw [hA', ladderTwoThree]
  simp only [zero_mul, mul_zero, sub_zero, smul_zero, LinearMap.zero_apply]
  intro h
  rcases smul_eq_zero.mp h.symm with h1 | h1
  · exact hscal h1
  · exact one_ne_zero h1

end HJO.Sym
