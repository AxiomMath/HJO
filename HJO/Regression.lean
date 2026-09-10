/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Symmetric.Multiplication
public import HJO.Symmetric.EpsilonSelection

/-! # Identities pinning down the conventions of the definitions

Several of this development's definitions are fixed by a convention — a choice of split, a sign,
a virtual rather than a monomial substitution — that a variant of the definition would change
without changing any type: the variant elaborates, every consumer of it elaborates, and it names
a different mathematical object. This file computes the values those conventions force, inside
the build, so that such a variant is a build error rather than a silently different theorem.
Each declaration says in its docstring which competing value it excludes, and why the naive
reading it excludes is degenerate.

These are pins on the *library's own* definitions rather than steps of the argument, so nothing
else in the library depends on them.

The five conventions pinned, in the order they appear:

* **The split.** `Sym.Split` is a bounded search with a totalising default `(1, 0)`, and the
  default is reached at inputs where the source's split is something else. `primitiveSplit`
  makes both boundary values explicit: the raw search is wrong at first coordinate `1` and
  second coordinate at least `2`, but its fallback is correct at second coordinate `1`.
  `slopeSplit` splits the *primitive* pair rather than the multiplied one. Section 1 pins the
  boundary values and `Split 4 6 = (1, 0)` — a true fact about `Split` and the reason `Qop` must
  not call it at a noncoprime slope.
* **The recursion at a noncoprime slope.** Section 2 evaluates the bracket that `Qop` unfolds to
  at the first three noncoprime slopes and at the base case, in a general field.
* **The axis plethysm.** `Sym.axisGen` substitutes a *virtual* alphabet, so the scalar attached
  to `p_k` is `v ^ (-k) - 1` and not `((1 - v) / v) ^ k`. Section 3 pins the linear coefficient
  at a numeric parameter, and pins the root of unity at which it vanishes.
* **The collapse at `u = 1`.** Section 4 pins the vanishing of every slope operator of first
  slope at least two at `u = 1`, which is what makes a specialisation read inside the base field
  vacuous rather than merely degenerate.
* **The rank perturbation.** Section 5 pins the sign convention of `ParkingFunctions.pointRank`
  and the tie its perturbation breaks.
-/

@[expose] public section

open Finset

namespace HJO.Regression

open MvPolynomial

/-! ### 1. The split of a slope and its explicit boundary values -/

/-- The interior of the coprime domain, where the bounded search of `Sym.Split` does succeed:
`(2, 3)` splits as `(1, 1)`, the unique pair with `1 ≤ r < 2`, `1 ≤ s < 3` and
`2 * s + 1 = 3 * r`. This is the value `Sym.slopeSplit` reads off for every slope of the form
`(2k, 3k)`, so if it moves, every one of those slopes recurses on the wrong pair of halves. -/
theorem primitiveSplit_two_three : Sym.primitiveSplit 2 3 = (1, 1) := by decide

/-- **The BGLX (2.9) boundary at a COPRIME pair, which the raw search gets wrong.** At `a = 1`
the search of `Sym.Split 1 b` filters on `1 ≤ p.1` with `p.1 ∈ List.range 1 = [0]`, so it finds
nothing and falls through to its default `(1, 0)` — even though `(1, 3)` is coprime and the
source's split there is `(1, b - 1) = (1, 2)`. `Sym.primitiveSplit` writes this value out
in its `a = 1` branch. If this breaks, `Sym.Qop q u 2 6` silently recurses on `(1, 6)` and `(1, 0)`
instead of `(1, 4)` and `(1, 2)`, which is a different operator. -/
theorem primitiveSplit_one_three : Sym.primitiveSplit 1 3 = (1, 2) := by decide

/-- The other written-out boundary: at `b = 1 < a` the source's split is `(1, 0)`, the pair
naming the boundary operator `Q_{1,0} = D_0`. Here `Sym.primitiveSplit` and the raw search agree,
but they agree for different reasons — the former *asserts* `(1, 0)` and the search *defaults* to
it — so the pin is on `Sym.primitiveSplit`. -/
theorem primitiveSplit_two_one : Sym.primitiveSplit 2 1 = (1, 0) := by decide

/-- `Sym.slopeSplit` splits the primitive pair: `(4, 6)` has multiplicity `2` and primitive pair
`(2, 3)`, so its split is `Sym.primitiveSplit 2 3 = (1, 1)`. This is the value that makes the
complement `(4 - 1, 6 - 1) = (3, 5)`, and `(3, 5)` is coprime — which is what keeps the
noncoprime branch of `Sym.Qop` from being re-entered. -/
theorem slopeSplit_four_six : Sym.slopeSplit 4 6 = (1, 1) := by decide

/-- **Why `Sym.Qop` may not call the raw search at a noncoprime slope.** The Bezout equation
`4 * s + 1 = 6 * r` has odd left side and even right side, so it has no solution at all and
`Sym.Split 4 6` falls through to its default `(1, 0)`. That is a correct fact about `Split`,
which is totalised on purpose; it is a *wrong* split of `(4, 6)`, and taking it would make
`Sym.Qop q u 4 6` the bracket `[Q_{3,6}, Q_{1,0}]` rather than the source's
`[Q_{3,5}, Q_{1,1}]`. This is the identity that must keep holding for `slopeSplit` to be
necessary: if `Split 4 6` ever starts returning `(1, 1)` by itself, the reader will conclude
`slopeSplit` is redundant and delete it, and the boundary case `primitiveSplit 1 3` above will
break with it. -/
theorem split_four_six : Sym.Split 4 6 = (1, 0) := by decide

/-! ### 2. The source's recursion at the first noncoprime slopes -/

section Qop

variable {L : Type*} [Field L] [Algebra ℚ L] (q u : L)

/-- **The first noncoprime slope.** `Sym.Qop q u 4 6 = M⁻¹ • [Q_{3,5}, Q_{1,1}]` with
`M = (1 - q) * (1 - u)`. The multiplicity is `2` and the primitive pair `(2, 3)` splits as
`(1, 1)`, so the halves are `(1, 1)` and `(4 - 1, 6 - 1) = (3, 5)`.

The value this pins *against* is `M⁻¹ • [Q_{3,6}, Q_{1,0}]`, which is what the definition
produced while it split `(m, n)` with the raw search instead of splitting the primitive pair:
`Sym.Split 4 6 = (1, 0)` (see `split_four_six`), giving halves `(1, 0)` and `(3, 6)`. Both
brackets typecheck and both are `Module.End L (Lambda L)`; nothing but this identity
distinguishes them. -/
theorem qop_four_six :
    Sym.Qop q u 4 6 = ((1 - q) * (1 - u))⁻¹ •
      (Sym.Qop q u 3 5 * Sym.Qop q u 1 1 - Sym.Qop q u 1 1 * Sym.Qop q u 3 5) := by
  have h := Sym.qop_eq_bracket q u (m := 4) (n := 6) (by norm_num) (by norm_num) (by decide)
  simpa [show Sym.slopeSplit 4 6 = (1, 1) from by decide] using h

/-- Multiplicity `3` over the same primitive pair `(2, 3)`: the split is still `(1, 1)`, so the
halves of `(6, 9)` are `(1, 1)` and `(5, 8)`. The point of a second multiplicity is that the split
does *not* scale with it — the complement `((k - 1) a + r, (k - 1) b + s)` absorbs the whole
multiplicity. A definition that split the primitive pair and then multiplied the split back up
would give `(3, 3)` and `(3, 6)` here, and *both* of those are noncoprime, so the recursion would
re-enter the noncoprime branch of `Sym.Qop` — exactly what the coprimality half of
`Sym.slopeSplit_spec` rules out, and what makes the fuel bound of `Sym.QopPrim` sufficient. With
the correct split, `(1, 1)` and `(5, 8)` are both coprime. -/
theorem qop_six_nine :
    Sym.Qop q u 6 9 = ((1 - q) * (1 - u))⁻¹ •
      (Sym.Qop q u 5 8 * Sym.Qop q u 1 1 - Sym.Qop q u 1 1 * Sym.Qop q u 5 8) := by
  have h := Sym.qop_eq_bracket q u (m := 6) (n := 9) (by norm_num) (by norm_num) (by decide)
  simpa [show Sym.slopeSplit 6 9 = (1, 1) from by decide] using h

/-- **The noncoprime slope whose primitive pair has width one**, where the boundary value
`Sym.primitiveSplit 1 3 = (1, 2)` is what is being used: `(2, 6)` has multiplicity `2` and
primitive pair `(1, 3)`, so the halves are `(1, 2)` and `(2 - 1, 6 - 2) = (1, 4)`. Under the
raw search's default `(1, 0)` the halves would instead be `(1, 0)` and `(1, 6)`, i.e.
`[D_6, D_0]` in place of `[D_4, D_2]` — two different operators, both well-typed. This is the
witness that `primitiveSplit`'s `a = 1` branch is load-bearing and not decoration. -/
theorem qop_two_six :
    Sym.Qop q u 2 6 = ((1 - q) * (1 - u))⁻¹ •
      (Sym.Qop q u 1 4 * Sym.Qop q u 1 2 - Sym.Qop q u 1 2 * Sym.Qop q u 1 4) := by
  have h := Sym.qop_eq_bracket q u (m := 2) (n := 6) (by norm_num) (by norm_num) (by decide)
  simpa [show Sym.slopeSplit 2 6 = (1, 2) from by decide] using h

/-- The base case the whole recursion bottoms out in, `Q_{1,n} = D_n`, including the boundary
operator `Q_{1,0} = D_0` at `n = 0` — the value that gives the pair `(1, 0)` returned by
`Sym.primitiveSplit 2 1` its meaning. Every bracket in this section is ultimately a nested
commutator of `Dop`s only because this holds; if the `m ≤ 1` branch of `Sym.Qop` were ever
changed to guard against `n = 0`, the boundary operator would disappear and the split
`(1, 0)` would name nothing. -/
theorem qop_one_eq_dop (n : ℕ) : Sym.Qop q u 1 n = Sym.Dop q u n := Sym.qop_one q u n

end Qop

/-! ### 3. The linear coefficient of an axis generator -/

/-- **The paper's value for the linear coefficient of `U_2` at `v = 6`, over `ℚ`.** The axis
generator substitutes the *virtual* alphabet `(1 - v) / v * X`, whose power sums are the
difference `p_k[v⁻¹ X] - p_k[X] = (v ^ (-k) - 1) * p_k`. So the coefficient of `p_2` in `U_2` is
`v / (v - 1) * ((v ^ (-2)) - 1) / 2`, which at `v = 6` is `6/5 * (1/36 - 1) / 2 = -7/12`.

The body this pins against is the *monomial* reading, in which the alphabet is scaled by the
scalar `(1 - v) / v` and the scalar at `p_k` is `((1 - v) / v) ^ k`. At `v = 6` and `k = 2` that
gives `6/5 * (25/36) / 2 = +5/12`. Both are rational numbers of the same shape; only the sign
distinguishes them here, which is why a numeric pin and not a shape check is needed. -/
theorem coeff_single_axisGen_six_two :
    coeff (Finsupp.single 1 1) (Sym.axisGen (6 : ℚ) 2) = -(7 / 12) := by
  rw [UkRegular.coeff_single_axisGen]
  norm_num

/-- **The root of unity that falsifies the `v ≠ 0, 1` contract.** At `v = -1` the linear
coefficient of `U_2` is `-1 / (-2) * ((-1) ^ (-2) - 1) / 2 = 0`, so `U_2` involves no `p_2` at
all and the axis generators fail to generate — even though `-1` is neither `0` nor `1`. This is
the counterexample behind the hypothesis `∀ j, v ^ (j + 1) ≠ 1` of
`UkRegular.coeff_single_axisGen_ne_zero`: any attempt to weaken that hypothesis to `v ≠ 0` and
`v ≠ 1` must contradict this identity, so it is the guard against a "simplification" of the
triangularity lemma. -/
theorem coeff_single_axisGen_neg_one_two :
    coeff (Finsupp.single 1 1) (Sym.axisGen (-1 : ℚ) 2) = 0 := by
  rw [UkRegular.coeff_single_axisGen]
  norm_num

/-! ### 4. The collapse of every slope operator at `u = 1` -/

/-- **The collapse at `u = 1`.** The slope recursion divides by `M = (1 - q) * (1 - u)`, so at
`u = 1` the normalisation `M⁻¹` is `0` (in a field, `(0 : L)⁻¹ = 0`) and every slope operator of
first slope at least two is the zero operator.

Consequently "specialise at `u = 1`" must not be read as an equation inside the base field: that
reading makes the hypotheses of the multiplication and homomorphism statements inconsistent rather
than merely degenerate, so they hold vacuously. The specialisation is instead carried on the
subring of elements regular at `u = 1` (`HJO.ReesRegular`), a local ring where evaluation has
nonzero kernel. Any rendering of the specialisation that can be instantiated with `u = 1` in the
field proves nothing. -/
theorem qop_eq_zero_at_one {L : Type*} [Field L] [Algebra ℚ L] (q : L) {m : ℕ} (hm : 2 ≤ m)
    (n : ℕ) : Sym.Qop q 1 m n = 0 :=
  Multiplication.qop_eq_zero q rfl hm n

/-! ### 5. The sign and the perturbation of the parking-function rank -/

/-- **The sign convention of `ParkingFunctions.pointRank`.** The rank is
`(aN + 1) * (a * y - b * x) + x`, and it *increases* up a column — which is what makes the
rank-ordered labelling of a path a legal parking labelling.

The competing convention `b * x - a * y` follows the paper's hook-count display rather than the
paper's own assertion that the rank increases up a column; the two are incompatible. Under
`b * x - a * y` the rank-ordered labelling of a path is no longer a parking labelling, and at
`(a, b, N) = (2, 3, 1)` no parking function then has full `ides`, so the sign-extracted sum over
the selected parking functions is `0` instead of `q + u`. A concrete pin is worth more than the
general monotonicity lemma here, because flipping the sign of the definition *and* the direction
of the general lemma together would leave the library consistent and wrong. -/
theorem pointRank_lt_up_column : ParkingFunctions.pointRank 2 3 1 0 0 <
    ParkingFunctions.pointRank 2 3 1 0 1 := by
  norm_num [ParkingFunctions.pointRank]

/-- The general statement of the same convention, over an arbitrary column of an arbitrary
rectangle: strictly monotone in the height. Pinned alongside the numeric value so that the two
must be flipped together, and pinned here rather than only in `EpsilonSelection` so that a
reader who breaks the numeric value finds the lemma it generalises. -/
theorem pointRank_strictMono_up_column {a b N : ℕ} (ha : 0 < a) (x : ℕ) {s t : ℕ} (hst : s < t) :
    ParkingFunctions.pointRank a b N x s < ParkingFunctions.pointRank a b N x t :=
  EpsilonSelection.pointRank_lt_pointRank_of_lt ha x hst

/-- **What the `+ x` perturbation buys.** The lattice points `(0, 0)` and `(2, 3)` of the
`2 × 3` rectangle have the *same* integral rank `a * y - b * x = 0`, so without the perturbation
their ranks tie and the rank order fails to be a total order on the north steps. With it they
are separated, by their horizontal positions, in the direction the source's perturbation
`x / (aN + 1)` points. Deleting the `+ x` — the obvious "simplification", since the integral
part carries all the geometry — would make this false and reinstate the tie. -/
theorem pointRank_perturbation_breaks_tie :
    (2 * 0 - 3 * 0 : ℤ) = (2 * 3 - 3 * 2 : ℤ) ∧
      ParkingFunctions.pointRank 2 3 1 0 0 < ParkingFunctions.pointRank 2 3 1 2 3 := by
  refine ⟨by norm_num, ?_⟩
  norm_num [ParkingFunctions.pointRank]

end HJO.Regression
