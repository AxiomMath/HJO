/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.MellitStraightMonomial
public meta import HJO.Attr

/-! # The vertex step `T` at a general `Λ`-coefficient, and the `(a,1)` column at `f = e_1`

`HJO/Shuffle/MellitStraightMonomial.lean` reduces the whole `HJO.Mellit.LhsSlope` family to one
operator iterated: `Y^aZ^b(Φf) = (-1)^ay_1^{a+1}T^b(d^*_+{}^{(0)}(Cf))`
(`HJO.Sweep.straightMonomial_slopeArg`), with `T = z_1 + d^*_+{}^{(0)}d_-^{(1)}`
(`HJO.Sweep.vertexStep`). It evaluates `T^b` only at `f = 1`, where `T(1) = 1` makes the answer
independent of `b`. **This file evaluates `T` at a general `Λ`-coefficient, and carries the `(a,1)`
column to the first coefficient the vacuum cannot see, `f = e_1`, at every `a`.**

## `T` in closed form

The vertex relation `HJO.Sweep.dplusStar_C_bop_sub` says, in generating functions with
`B(t) = ∑B_it^i` and `y = uy_1`, that `(1-yt)d^*_+B(t) = (1-qyt)B(t)d^*_+` on the constants. Fed
into the two-term `HJO.Sweep.vertexStep_auxVar_pow_mul_C` the factor `(1-q)^{-1}` **cancels
exactly**, leaving a recursion in the `y_1`-degree with no scalar at all:

`T(y_1^{m+1}CA) = uy_1·T(y_1^mCA) + B_{m+1}(d^*_+{}^{(0)}(CA))`
  (`HJO.Sweep.vertexStep_auxVar_pow_succ_mul_C`).

Since `B_m(d^*_+(CA)) = d_-^{(2)}d^*_+{}^{(1)}(y_1^mCA)`
(`HJO.Sweep.dminus_two_dplusStar_one_auxVar_pow_mul_C`), on monomials this *is* the operator
identity
`T∘(y_1·) = u(y_1·)∘T + N∘(y_1·)` for the second half `N` of `HJO.Sweep.zop` — the `P - N` of the
vertex relation resolved into a rule for moving one `y_1` past `T`.

Telescoping it (`HJO.Sweep.vertexStep_auxVar_pow_mul_C_eq_sum`, at `J = m`
`HJO.Sweep.vertexStep_auxVar_pow_mul_C_closed`):

`T(y_1^mCA) = ∑_{j<m}(uy_1)^jB_{m-j}(d^*_+(CA)) + (uy_1)^mT(CA)`.

So **`T` is one Jing generating function `(1-uy_1t)^{-1}B(t)` composed with the plethystic shift
`d^*_+`, read at `t^m` where `m` is the `y_1`-degree of its argument**, plus its value on the
constants — and that last value, `T(CA) = (1-q)^{-1}(d^*_+(C(B_0A)) - qB_0(d^*_+(CA)))`, is the only
irreducible datum left. On the `y_1`-axis it is `T(1) = 1` and the sum is fully explicit:

`T(y_1^m) = ∑_{i≤m}(-1)^ie_i(uy_1)^{m-i}`   (`HJO.Sweep.vertexStep_auxVar_pow`),

the first evaluation of `T` away from the vacuum that needs no coefficient data at all.

## Why `T^b` does not close at a general `f`: the obstruction

**The truncation is the obstruction, and it is not removable.** Writing `d^*_+(CA) = ∑_ny_1^nCA_n`,
the closed form reads `T(y_1^mCA) = ∑_{j,n}u^jy_1^{j+n}C(B_{m-j}A_n)`: the index the sum is cut off
at, `j ≥ 0`, is the `y_1`-degree `m` of the argument, while the surviving `y_1`-degrees are `j+n` —
and the `n` come from `d^*_+`, which *raises* the `y_1`-degree of every coefficient
(`HJO.Sweep.dplusStar_C_elemSymm`). So the degree the next `T` truncates at is not the degree the
previous one produced, the truncation indices of the `b` factors are coupled, and `T^b` is a
`b`-fold sum of words alternating `B`'s with plethystic shifts. **Two truncated Jing evaluations do
not compose into one truncated Jing evaluation**; that, and not any failure of the vertex relation,
is what stops the closed form at `b = 1`. Dropping the truncation is not available either:
`∑_iB_i(g)t^i` is unbounded above in `i`, so the untruncated sum has unboundedly negative powers of
`y_1`.

Two escapes that fail.

* **`T∘d^*_+ ≠ d^*_+∘X` for any `X` on `Λ`**, so the `f`-side and the `b`-side cannot be separated
  into `T^b(d^*_+(Cf)) = d^*_+(C(X^bf))`. At `A = e_1`
  `HJO.Sweep.vertexStep_pow_dplusStar_C_elemSymm_one` at `b = 1` gives
  `T(d^*_+(Ce_1)) = (q+u-qu)Ce_1 + (q-1)u^2y_1`, while `d^*_+(C(ce_1)) = c(Ce_1 + (q-1)uy_1)`; both
  are degree one, so matching forces `c = q+u-qu` and `(q-1)u^2 = c(q-1)u`, i.e. `q(1-u) = 0`. For
  `q ≠ 0` that is `u = 1`. (Arithmetic off that value; not formalised as a `≠`.)
* **`f = 1` says nothing**: `T^b(1) = 1` at every `b` (`HJO.Sweep.vertexStep_pow_one`).

## The `(a,1)` column at `f = e_1`, at every `a`

What *does* close is the whole column at a fixed low-degree `f`, because `T` preserves the total
degree of `V_1` and the degree-one part is two-dimensional. On `span(Ce_1, y_1)`:

* `T(Ce_1) = qCe_1`   (`HJO.Sweep.vertexStep_C_elemSymm_one`);
* `T(y_1) = -Ce_1 + uy_1`   (`HJO.Sweep.vertexStep_auxVar`, the `m = 1` case of the `y_1`-axis
form).

So `T` is triangular there with eigenvalues `q` and `u`, and
`T^b(d^*_+(Ce_1)) = α_bCe_1 + (q-1)u^{b+1}y_1` where `α_0 = 1`, `α_{b+1} = qα_b + (1-q)u^{b+1}`
(`HJO.Sym.colAlpha`, `HJO.Sweep.vertexStep_pow_dplusStar_C_elemSymm_one`); in closed form
`α_b = (q^{b+1}(1-u) - u^{b+1}(1-q))/(q-u)`, which is where the two eigenvalues show. Applying
`π = d_-^{(1)}` to `y_1·` that — the only `Λ`-values read being `B_1(e_1) = -e_1^2 + (1-q)e_2` and
`B_2(1) = e_2` — gives the sweep side of the column
(`HJO.Sweep.dminus_straightMonomial_slopeArg_elemSymm_one`):

`πZ^bΦ(e_1) = -α_be_1^2 + (1-q)(α_b - u^{b+1})e_2`.

The `Λ` side matches it at every `b`. `Q_{b+1,1} = M^{-1}(Q_{b,1}D_0 - D_0Q_{b,1})`
(`HJO.Sym.qop_of_coprime` with `HJO.Sym.split_snd_one`) closes on `span(e_1^2, e_2)` because
`D_0(e_1) = (1-M)e_1` is a *scalar* multiple of `e_1` (`HJO.Sym.dop_zero_elemSymm_one`) and `D_0` on
the two degree-two monomials is known (`HJO.Sym.dop_zero_elemSymm_two`) or Pieri
(`HJO.Sym.dop_zero_elemSymm_one_sq`, off `HJO.Sym.dop_elemSymm_mul`). That is
`HJO.Sym.qop_succ_one_elemSymm_one`, and the two sides agree:

**`HJO.Sweep.lhsSlopeAt_succ_one_elemSymm_one`: `HJO.Mellit.LhsSlopeAt q u (b+1) 1 e_1` for every
`b`.**

This is the `(a,1)` column of `HJO.Mellit.lhsRewrite_sweepWitness` — the column
`HJO/Shuffle/MellitLhsSlopeMediant.lean` cannot reach, its Stern–Brocot parents being `(a-1,1)`
and `(1,0)` — at a coefficient the vacuum cannot see, uniformly in `a`. It is not a reduction: no
hypothesis is discharged, both sides are evaluated and compared.

## The value depends on `a`, so the vacuum was hiding the content

`HJO.Sweep.dminus_straightMonomial_slopeArg_elemSymm_one_ne`: at `f = e_1` the `(2,1)` and `(1,1)`
values **differ**, `α_1 - α_0 = -M`, the defect being `M(e_1^2 + ce_2) ≠ 0` by
`HJO.Sym.elemSymm_one_sq_add_smul_elemSymm_two_ne_zero`. At the vacuum they are equal — both `-e_1`
at every `a`, by `HJO.Sweep.dminus_straightMonomial_slopeArg_one` and
`HJO.Sym.qop_apply_one_of_snd_one`. So `f = e_1` is the smallest coefficient at which this column
has any content, and it is a real test of the slope rather than of the bookkeeping: it passes at
every `a`.

## Genericity

* The recursion, its telescoping, `T(y_1^m)` and `T(y_1)`: **`q ≠ 1` and nothing else**, no
  condition on `u`. The exclusion is real: at `q = 1` the scalar `q/(1-q)` of `HJO.Sweep.zop` is `0`
  under the field convention `x/0 = 0`, so `z_1 = 0` and `T = d^*_+d_-`, whence
  `T(y_1) = d^*_+(C(B_1 1)) = -Ce_1` — the `uy_1` of `HJO.Sweep.vertexStep_auxVar` is missing, and
  the recursion at `m = 0`, `A = 1` fails, unless `u = 0`. (Not formalised here; the `q = 1`
  degeneration of the *letter* is `HJO.Sweep.zLetter_eq_zero_of_q_eq_one`.)
* `HJO.Sweep.vertexStep_C_elemSymm_one`: `q ≠ 1` is **inherited and unnecessary** — at `q = 1` both
  sides are `Ce_1`, since `B_0(e_1) = qe_1` and `d^*_+(Ce_1) = Ce_1` there. It is carried only
  because the two-term formula it is proved from carries it.
* The column theorems: `q ≠ 0`, `u ≠ 0`, `q ≠ 1`, `M = (1-q)(1-u) ≠ 0`. The first three are **real**
  for the reason recorded in `MellitStraightMonomial.lean` — the letter `Z = (qu)^{-1}z_1` is the
  zero map at each (`HJO.Sweep.zLetter_eq_zero_of_mul_eq_zero`,
  `HJO.Sweep.zLetter_eq_zero_of_q_eq_one`) — and here the refutation is *sharper* than at the
  vacuum, because the `Λ` side is visibly nonzero: at `u = 0` the recursion gives `α_b = q^b`, so
  `Q_{b+1,1}(e_1) = -q^be_1^2 + (1-q)q^be_2`, while the sweep side is `0` for `b ≥ 1`; at `q = 0`,
  `α_b = u^b` for `b ≥ 1` and the same happens. `M ≠ 0` is `HJO.Sym.Qop`'s normalisation. **No
  condition on `u - 1` anywhere.**

## What this file does not prove

`HJO.Mellit.lhsRewrite_sweepWitness` states its `(a,1)` column for a *general* `f`; this file
proves it only at `f = e_1`.
-/

@[expose] public section

namespace HJO.Sweep

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-- The cleared form of `HJO.Sweep.vertexStep_auxVar_pow_mul_C`. -/
theorem scal_sub_mul_vertexStep_auxVar_pow_mul_C (hq1 : q ≠ 1) (m : ℕ) (A : Sym.Lambda L) :
    (1 - scal q : Total L) * vertexStep q u ((auxVar 1 : Total L) ^ m * MvPolynomial.C A)
      = dplusStar q u 0 (MvPolynomial.C (Sym.Bop q (m : ℤ) A))
        - scal q * bopExt q (m : ℤ) (dplusStar q u 0 (MvPolynomial.C A : Total L)) := by
  have h1q : (1 : L) - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq1)
  have hs : (1 - scal q : Total L) = scal (1 - q) := by rw [scal_sub, scal_one]
  rw [vertexStep_auxVar_pow_mul_C hq1 m A, hs]
  simp only [smul_eq_scal_mul]
  rw [← mul_assoc, ← scal_mul, mul_inv_cancel₀ h1q, scal_one, one_mul]

/-- **The `y_1`-degree recursion for `T`:**
`T(y_1^{m+1}CA) = uy_1T(y_1^mCA) + B_{m+1}(d^*_+(CA))`. -/
@[hjo "lem_mellit_vertex_degree_recursion"]
theorem vertexStep_auxVar_pow_succ_mul_C (hq1 : q ≠ 1) (m : ℕ) (A : Sym.Lambda L) :
    vertexStep q u ((auxVar 1 : Total L) ^ (m + 1) * MvPolynomial.C A)
      = starLetter u * vertexStep q u ((auxVar 1 : Total L) ^ m * MvPolynomial.C A)
        + bopExt q ((m : ℤ) + 1) (dplusStar q u 0 (MvPolynomial.C A : Total L)) := by
  have h1q : (1 : L) - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq1)
  have hv := dplusStar_C_bop_sub q u ((m : ℤ) + 1) A
  rw [show (m : ℤ) + 1 - 1 = (m : ℤ) from by ring] at hv
  have h2 := scal_sub_mul_vertexStep_auxVar_pow_mul_C (q := q) (u := u) hq1 m A
  have h1 := scal_sub_mul_vertexStep_auxVar_pow_mul_C (q := q) (u := u) hq1 (m + 1) A
  rw [show ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 from by push_cast; ring] at h1
  have key : (1 - scal q : Total L)
        * vertexStep q u ((auxVar 1 : Total L) ^ (m + 1) * MvPolynomial.C A)
      = (1 - scal q : Total L)
        * (starLetter u * vertexStep q u ((auxVar 1 : Total L) ^ m * MvPolynomial.C A)
          + bopExt q ((m : ℤ) + 1) (dplusStar q u 0 (MvPolynomial.C A : Total L))) :=
    by linear_combination h1 - starLetter u * h2 + hv
  have hne : (1 - scal q : Total L) ≠ 0 := by
    rw [show (1 - scal q : Total L) = scal (1 - q) from by rw [scal_sub, scal_one]]
    simp only [scal, ne_eq, MvPolynomial.C_eq_zero, sub_eq_zero]
    exact fun h => hq1 h.symm
  exact mul_left_cancel₀ hne key

end HJO.Sweep

namespace HJO.Sym

variable {L : Type*} [Field L] [Algebra ℚ L]

theorem elemSymmAlt_zero : elemSymmAlt L (0 : ℤ) = 1 := by
  rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, elemSymmAlt_natCast]
  simp [elemSymm_zero L]

/-- `B_0(e_1) = qe_1`, from `HJO.Sym.bop_powerSum` at `r = 0`, `k = 1`: `e_1 - (1-q)e_1`. -/
theorem bop_zero_elemSymm_one (q : L) :
    Bop q (0 : ℤ) (elemSymm L 1) = MvPolynomial.C q * elemSymm L 1 := by
  rw [elemSymm_one L, bop_powerSum q 0 (k := 1) Nat.one_pos, elemSymmAlt_zero,
    show ((0 : ℤ) + ((1 : ℕ) : ℤ)) = ((1 : ℕ) : ℤ) from by norm_num, elemSymmAlt_natCast,
    ← elemSymm_one L]
  simp only [map_sub, map_one, pow_one]
  ring

/-- `B_1(e_1) = -e_1^2 + (1-q)e_2`, from `HJO.Sym.bop_powerSum` at `r = 1`, `k = 1`. -/
theorem bop_one_elemSymm_one (q : L) :
    Bop q (1 : ℤ) (elemSymm L 1)
      = -(elemSymm L 1 * elemSymm L 1) + MvPolynomial.C (1 - q) * elemSymm L 2 := by
  rw [elemSymm_one L, bop_powerSum q 1 (k := 1) Nat.one_pos,
    show ((1 : ℤ)) = ((1 : ℕ) : ℤ) from by norm_num, elemSymmAlt_natCast,
    show (((1 : ℕ) : ℤ) + ((1 : ℕ) : ℤ)) = ((2 : ℕ) : ℤ) from by norm_num,
    elemSymmAlt_natCast, ← elemSymm_one L]
  simp only [map_sub, map_one, pow_one]
  ring

end HJO.Sym

namespace HJO.Sweep

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

omit [Algebra ℚ L] in
theorem C_C_mul (c : L) (f : Sym.Lambda L) :
    (MvPolynomial.C (MvPolynomial.C c * f) : Total L) = c • MvPolynomial.C f := by
  rw [map_mul, smul_eq_scal_mul]
  rfl

omit [Algebra ℚ L] in
theorem starLetter_eq_smul (u : L) : (starLetter u : Total L) = u • (auxVar 1 : Total L) := by
  rw [starLetter, smul_eq_scal_mul]

/-- `B_r` on a monomial of `V_1`: it acts on the `Λ`-coefficient only. -/
theorem bopExt_auxVar_pow_mul_C (q : L) (r : ℤ) (m : ℕ) (A : Sym.Lambda L) :
    bopExt q r ((auxVar 1 : Total L) ^ m * MvPolynomial.C A)
      = (auxVar 1 : Total L) ^ m * MvPolynomial.C (Sym.Bop q r A) := by
  have hav : ((auxVar 1 : Total L)) ^ m = MvPolynomial.monomial (Finsupp.single 0 m) 1 := by
    rw [auxVar, Nat.sub_self]
    exact MvPolynomial.X_pow_eq_monomial
  rw [hav, bopExt_monomial_mul, bopExt_C]

/-! ### The telescoped form of the recursion -/

/-- **`T` on a monomial of `V_1`, telescoped `J` steps down:** for every `J ≤ m`,

`T(y_1^mCA) = ∑_{j<J}(uy_1)^jB_{m-j}(d^*_+(CA)) + (uy_1)^JT(y_1^{m-J}CA)`.

Iterating `HJO.Sweep.vertexStep_auxVar_pow_succ_mul_C`. The sum is the whole of `T` except for the
remainder, which is `T` on a *lower* power of `y_1`; so the only irreducible datum is `T` on the
constants, `J = m` (`HJO.Sweep.vertexStep_auxVar_pow_mul_C_closed`). Read in `t`, the identity says
that `T` at `y_1`-degree `m` is the coefficient of `t^m` in `(1-uy_1t)^{-1}B(t)d^*_+`, truncated at
`t^{m-J}`: **`T` is one Jing generating function against the plethystic shift, cut off at the
`y_1`-degree of its argument.** The cut-off is why iterating does not collapse — see the module
docstring. -/
theorem vertexStep_auxVar_pow_mul_C_eq_sum (hq1 : q ≠ 1) (m : ℕ) (A : Sym.Lambda L) :
    ∀ J ≤ m, vertexStep q u ((auxVar 1 : Total L) ^ m * MvPolynomial.C A)
      = (∑ j ∈ Finset.range J, starLetter u ^ j
            * bopExt q ((m : ℤ) - j) (dplusStar q u 0 (MvPolynomial.C A : Total L)))
        + starLetter u ^ J
            * vertexStep q u ((auxVar 1 : Total L) ^ (m - J) * MvPolynomial.C A) := by
  intro J
  induction J with
  | zero => intro _; simp
  | succ c ih =>
      intro hc
      have hstep := vertexStep_auxVar_pow_succ_mul_C (u := u) hq1 (m - (c + 1)) A
      rw [show m - (c + 1) + 1 = m - c from by omega,
        show ((m - (c + 1) : ℕ) : ℤ) + 1 = (m : ℤ) - c from by omega] at hstep
      rw [ih (by omega), Finset.sum_range_succ, hstep]
      ring

/-- **`T` on a monomial of `V_1`, in closed form:**

`T(y_1^mCA) = ∑_{j<m}(uy_1)^jB_{m-j}(d^*_+(CA)) + (uy_1)^mT(CA)`.

`HJO.Sweep.vertexStep_auxVar_pow_mul_C_eq_sum` at `J = m`: every `y_1` of the argument is spent, and
what is left is `T` on the constant `CA`, which is the two-term
`HJO.Sweep.vertexStep_auxVar_pow_mul_C` at `m = 0`. -/
@[hjo "lem_mellit_vertex_degree_recursion"]
theorem vertexStep_auxVar_pow_mul_C_closed (hq1 : q ≠ 1) (m : ℕ) (A : Sym.Lambda L) :
    vertexStep q u ((auxVar 1 : Total L) ^ m * MvPolynomial.C A)
      = (∑ j ∈ Finset.range m, starLetter u ^ j
            * bopExt q ((m : ℤ) - j) (dplusStar q u 0 (MvPolynomial.C A : Total L)))
        + starLetter u ^ m * vertexStep q u (MvPolynomial.C A : Total L) := by
  have h := vertexStep_auxVar_pow_mul_C_eq_sum (u := u) hq1 m A m le_rfl
  rwa [Nat.sub_self, pow_zero, one_mul] at h

/-- **`T` on the `y_1`-axis, in closed form, at every `m`:**
`T(y_1^m) = ∑_{i≤m}(-1)^ie_i(uy_1)^{m-i}`.

`HJO.Sweep.vertexStep_auxVar_pow_succ_mul_C` at `A = 1`, where `d^*_+(C1) = 1` and
`B_i(1) = (-1)^ie_i` (`HJO.Sym.bop_one`). The `m = 0` case is `HJO.Sweep.vertexStep_one`,
`T(1) = 1`;
the `b`-independence of `πY^aZ^bΦ(1)` is the statement that *only* that case is ever read at the
vacuum. -/
@[hjo "lem_mellit_vertex_degree_recursion"]
theorem vertexStep_auxVar_pow (hq1 : q ≠ 1) (m : ℕ) :
    vertexStep q u ((auxVar 1 : Total L) ^ m)
      = ∑ i ∈ Finset.range (m + 1),
          MvPolynomial.C (Sym.elemSymmAlt L (i : ℤ)) * starLetter u ^ (m - i) := by
  induction m with
  | zero =>
      rw [pow_zero, vertexStep_one, Finset.sum_range_one]
      simp [Sym.elemSymmAlt_zero]
  | succ c ih =>
      have h := vertexStep_auxVar_pow_succ_mul_C (u := u) hq1 c (1 : Sym.Lambda L)
      rw [MvPolynomial.C_1, mul_one, mul_one, dplusStar_one,
        ← MvPolynomial.C_1 (σ := ℕ) (R := Sym.Lambda L), bopExt_C, Sym.bop_one] at h
      rw [h, ih, Finset.mul_sum]
      conv_rhs => rw [Finset.sum_range_succ]
      rw [show ((c : ℤ) + 1) = ((c + 1 : ℕ) : ℤ) from by push_cast; ring, Nat.sub_self,
        pow_zero, mul_one]
      refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun i hi => ?_) rfl
      rw [Finset.mem_range] at hi
      rw [show c + 1 - i = (c - i) + 1 from by omega, pow_succ]
      ring

/-! ### `T` on the two degree-one vectors of `V_1` -/

/-- **`T(y_1) = -e_1 + uy_1`.** -/
theorem vertexStep_auxVar (hq1 : q ≠ 1) :
    vertexStep q u (auxVar 1 : Total L)
      = -(MvPolynomial.C (Sym.elemSymm L 1) : Total L) + u • (auxVar 1 : Total L) := by
  have h := vertexStep_auxVar_pow_succ_mul_C (q := q) (u := u) hq1 0 (1 : Sym.Lambda L)
  rw [pow_zero, pow_one, MvPolynomial.C_1, mul_one, one_mul, vertexStep_one, mul_one,
    dplusStar_one, ← MvPolynomial.C_1 (σ := ℕ) (R := Sym.Lambda L), bopExt_C, Sym.bop_one,
    Nat.cast_zero, zero_add, show ((1 : ℤ)) = ((1 : ℕ) : ℤ) from by norm_num,
    Sym.elemSymmAlt_natCast] at h
  rw [h, starLetter_eq_smul]
  simp only [pow_one, neg_mul, one_mul, map_neg]
  ring

/-- **`T(Ce_1) = qCe_1`**: the constant term is an eigenvector of `T` with eigenvalue `q`. -/
theorem vertexStep_C_elemSymm_one (hq1 : q ≠ 1) :
    vertexStep q u (MvPolynomial.C (Sym.elemSymm L 1) : Total L)
      = q • (MvPolynomial.C (Sym.elemSymm L 1) : Total L) := by
  have h1q : (1 : L) - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq1)
  have hd : dplusStar q u 0 (MvPolynomial.C (Sym.elemSymm L 1) : Total L)
      = (MvPolynomial.C (Sym.elemSymm L 1) : Total L) + ((q - 1) * u) • (auxVar 1 : Total L) := by
    rw [dplusStar_C_elemSymm_one, starLetter_eq_smul, smul_eq_scal_mul, smul_eq_scal_mul,
      ← mul_assoc, ← scal_mul]
  have hb : bopExt q (0 : ℤ) (dplusStar q u 0 (MvPolynomial.C (Sym.elemSymm L 1) : Total L))
      = q • (MvPolynomial.C (Sym.elemSymm L 1) : Total L)
        + ((q - 1) * u) • (auxVar 1 : Total L) := by
    rw [hd, map_add, map_smul]
    rw [show (MvPolynomial.C (Sym.elemSymm L 1) : Total L)
        = (auxVar 1 : Total L) ^ 0 * MvPolynomial.C (Sym.elemSymm L 1) from by rw [pow_zero,
          one_mul]]
    rw [bopExt_auxVar_pow_mul_C, Sym.bop_zero_elemSymm_one, C_C_mul, pow_zero, one_mul]
    rw [show (auxVar 1 : Total L)
        = (auxVar 1 : Total L) ^ 1 * MvPolynomial.C (1 : Sym.Lambda L) from by
      rw [pow_one, MvPolynomial.C_1, mul_one]]
    rw [bopExt_auxVar_pow_mul_C, Sym.bop_one, Sym.elemSymmAlt_zero, MvPolynomial.C_1, mul_one,
      pow_one, one_mul]
  have hs : dplusStar q u 0 (MvPolynomial.C (Sym.Bop q ((0 : ℕ) : ℤ) (Sym.elemSymm L 1)))
      = q • ((MvPolynomial.C (Sym.elemSymm L 1) : Total L)
        + ((q - 1) * u) • (auxVar 1 : Total L)) := by
    rw [Nat.cast_zero, Sym.bop_zero_elemSymm_one, C_C_mul, map_smul, hd]
  have h := vertexStep_auxVar_pow_mul_C (q := q) (u := u) hq1 0 (Sym.elemSymm L 1)
  rw [pow_zero, one_mul, hs] at h
  rw [show ((0 : ℕ) : ℤ) = (0 : ℤ) from Nat.cast_zero] at h
  rw [h, hb]
  match_scalars <;> (field_simp; try ring)

end HJO.Sweep

namespace HJO.Sym

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-- **`D_0(e_1^2) = (1-2M)e_1^2 + M^2e_2`**, the Pieri rule `HJO.Sym.dop_elemSymm_mul` at
`k = 0`, `n = 1`, `f = e_1`. -/
theorem dop_zero_elemSymm_one_sq (q u : L) :
    Dop q u 0 (elemSymm L 1 * elemSymm L 1)
      = (1 - 2 * ((1 - q) * (1 - u))) • (elemSymm L 1 * elemSymm L 1)
        + ((1 - q) * (1 - u)) ^ 2 • elemSymm L 2 := by
  rw [dop_elemSymm_mul q u 0 1 (elemSymm L 1), Finset.sum_range_succ, Finset.sum_range_one,
    Bglx.paramPleth_elemSymm_zero, Bglx.paramPleth_elemSymm_one_eq, Nat.sub_self, Nat.sub_zero,
    show (0 : ℕ) + 0 = 0 from rfl, show (0 : ℕ) + 1 = 1 from rfl, dop_zero_elemSymm_one,
    dop_one_elemSymm_one, elemSymm_zero L]
  simp only [MvPolynomial.smul_eq_C_mul, map_sub, map_mul, map_one, map_pow, map_ofNat]
  ring

/-- The scalar of the `(a,1)` column at `f = e_1`: `α_0 = 1`, `α_{b+1} = qα_b + (1-q)u^{b+1}`. -/
noncomputable def colAlpha (q u : L) : ℕ → L
  | 0 => 1
  | b + 1 => q * colAlpha q u b + (1 - q) * u ^ (b + 1)

omit [Algebra ℚ L] in
theorem colAlpha_zero (q u : L) : colAlpha q u 0 = 1 := rfl

omit [Algebra ℚ L] in
theorem colAlpha_succ (q u : L) (b : ℕ) :
    colAlpha q u (b + 1) = q * colAlpha q u b + (1 - q) * u ^ (b + 1) := rfl

/-- **The `Λ` side of the `(a,1)` column at `f = e_1`, for every `a`:**
`Q_{b+1,1}(e_1) = -α_be_1^2 + (1-q)(α_b - u^{b+1})e_2`. -/
theorem qop_succ_one_elemSymm_one (hM : (1 - q) * (1 - u) ≠ 0) (b : ℕ) :
    Qop q u (b + 1) 1 (elemSymm L 1)
      = (-colAlpha q u b) • (elemSymm L 1 * elemSymm L 1)
        + ((1 - q) * (colAlpha q u b - u ^ (b + 1))) • elemSymm L 2 := by
  induction b with
  | zero =>
      rw [qop_one, dop_one_elemSymm_one, colAlpha_zero]
      simp only [MvPolynomial.smul_eq_C_mul, map_sub, map_mul, map_one, map_neg]
      ring_nf
  | succ c ih =>
      have hlt : 1 < c + 1 + 1 := by omega
      have hcop : Nat.Coprime (c + 1 + 1) 1 := Nat.coprime_one_right _
      rw [qop_of_coprime q u hlt hcop, split_snd_one]
      simp only [Nat.add_sub_cancel, Nat.sub_zero]
      rw [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
        qop_of_le_one q u 0 (le_refl 1), dop_zero_elemSymm_one, map_smul, ih, map_add, map_smul,
        map_smul, dop_zero_elemSymm_one_sq, dop_zero_elemSymm_two, colAlpha_succ]
      rw [inv_smul_eq_iff₀ hM]
      simp only [MvPolynomial.smul_eq_C_mul, map_sub, map_add, map_mul, map_one, map_neg, map_pow,
        map_ofNat]
      ring

omit [Algebra ℚ L] in
/-- `α_1 = q + u - qu ≠ 1 = α_0` whenever `M = (1-q)(1-u) ≠ 0`: the column scalar is not
constant in `b`, the difference being exactly `-M`. -/
theorem colAlpha_one_ne_colAlpha_zero (hM : (1 - q) * (1 - u) ≠ 0) :
    colAlpha q u 1 ≠ colAlpha q u 0 := by
  rw [colAlpha_succ, colAlpha_zero]
  intro h
  exact hM (by linear_combination -h)

/-- **Two `(a,1)` values at `f = e_1` with different `α` are different.** The `e_1^2`
coefficient of `Q_{b+1,1}(e_1)` is `-α_b`, and `e_1^2` and `e_2` are linearly independent
over the scalars (`HJO.Sym.elemSymm_one_sq_add_smul_elemSymm_two_ne_zero`). -/
theorem qop_succ_one_elemSymm_one_ne_of_ne (hM : (1 - q) * (1 - u) ≠ 0) {b c : ℕ}
    (hbc : colAlpha q u b ≠ colAlpha q u c) :
    Qop q u (b + 1) 1 (elemSymm L 1) ≠ Qop q u (c + 1) 1 (elemSymm L 1) := by
  intro h
  rw [qop_succ_one_elemSymm_one hM b, qop_succ_one_elemSymm_one hM c] at h
  have hs : colAlpha q u c - colAlpha q u b ≠ 0 := sub_ne_zero.mpr (Ne.symm hbc)
  have hCs : (MvPolynomial.C (colAlpha q u c - colAlpha q u b) : Lambda L) ≠ 0 := by
    simp only [ne_eq, MvPolynomial.C_eq_zero]
    exact hs
  set D : L := (1 - q) * (colAlpha q u b - u ^ (b + 1)) with hD
  set D' : L := (1 - q) * (colAlpha q u c - u ^ (c + 1)) with hD'
  refine elemSymm_one_sq_add_smul_elemSymm_two_ne_zero
    ((colAlpha q u c - colAlpha q u b)⁻¹ * (D - D')) ?_
  have hcancel : (MvPolynomial.C (colAlpha q u c - colAlpha q u b) : Lambda L)
      * MvPolynomial.C ((colAlpha q u c - colAlpha q u b)⁻¹ * (D - D'))
      = MvPolynomial.C (D - D') := by
    rw [← map_mul, ← mul_assoc, mul_inv_cancel₀ hs, one_mul]
  have key : (MvPolynomial.C (colAlpha q u c - colAlpha q u b) : Lambda L)
      * (elemSymm L 1 * elemSymm L 1
          + ((colAlpha q u c - colAlpha q u b)⁻¹ * (D - D')) • elemSymm L 2) = 0 := by
    simp only [MvPolynomial.smul_eq_C_mul, map_sub, map_neg] at h hcancel ⊢
    linear_combination h + elemSymm L 2 * hcancel
  rcases mul_eq_zero.mp key with h1 | h2
  · exact absurd h1 hCs
  · exact h2

end HJO.Sym

namespace HJO.Sweep

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

omit [Algebra ℚ L] in
theorem C_smul (c : L) (f : Sym.Lambda L) :
    (MvPolynomial.C (c • f) : Total L) = c • (MvPolynomial.C f : Total L) := by
  rw [MvPolynomial.smul_eq_C_mul, C_C_mul]

theorem dplusStar_C_elemSymm_one_smul (q u : L) (k : ℕ) :
    dplusStar q u k (MvPolynomial.C (Sym.elemSymm L 1) : Total L)
      = (MvPolynomial.C (Sym.elemSymm L 1) : Total L) + ((q - 1) * u) • (auxVar 1 : Total L) := by
  rw [dplusStar_C_elemSymm_one, starLetter_eq_smul, smul_eq_scal_mul, smul_eq_scal_mul,
    ← mul_assoc, ← scal_mul]

/-- **`T^b` on `d^*_+(Ce_1)`, for every `b`:**
`T^b(d^*_+(Ce_1)) = α_bCe_1 + (q-1)u^{b+1}y_1`, with `α` the recursion `HJO.Sym.colAlpha`.

This is the evaluation of the iterated vertex step at a **general** degree-one `Λ`-coefficient: the
two-dimensional space spanned by `Ce_1` and `y_1` is `T`-stable, `Ce_1` is an eigenvector with
eigenvalue `q` (`HJO.Sweep.vertexStep_C_elemSymm_one`) and `y_1` has `T(y_1) = -Ce_1 + uy_1`
(`HJO.Sweep.vertexStep_auxVar`), so `T` is triangular there with eigenvalues `q` and `u`. -/
theorem vertexStep_pow_dplusStar_C_elemSymm_one (hq1 : q ≠ 1) (b : ℕ) :
    (vertexStep q u ^ b) (dplusStar q u 0 (MvPolynomial.C (Sym.elemSymm L 1) : Total L))
      = (Sym.colAlpha q u b) • (MvPolynomial.C (Sym.elemSymm L 1) : Total L)
        + ((q - 1) * u ^ (b + 1)) • (auxVar 1 : Total L) := by
  induction b with
  | zero =>
      rw [pow_zero, Module.End.one_apply, dplusStar_C_elemSymm_one_smul, Sym.colAlpha_zero,
        pow_one, one_smul]
  | succ c ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_add, map_smul, map_smul,
        vertexStep_C_elemSymm_one hq1, vertexStep_auxVar hq1, Sym.colAlpha_succ]
      match_scalars <;> ring

/-- **The sweep side of the `(a,1)` column at `f = e_1`, for every `a`:**
`πZ^bΦ(e_1) = -α_be_1^2 + (1-q)(α_b - u^{b+1})e_2`. -/
theorem dminus_straightMonomial_slopeArg_elemSymm_one (hq0 : q ≠ 0) (hu0 : u ≠ 0)
    (hq1 : q ≠ 1) (b : ℕ) :
    dminus q 1 (straightMonomial q u 0 b (Mellit.slopeArg q u (Sym.elemSymm L 1)))
      = (-Sym.colAlpha q u b)
            • (MvPolynomial.C (Sym.elemSymm L 1 * Sym.elemSymm L 1) : Total L)
          + ((1 - q) * (Sym.colAlpha q u b - u ^ (b + 1)))
            • (MvPolynomial.C (Sym.elemSymm L 2) : Total L) := by
  rw [straightMonomial_slopeArg hq0 hu0 hq1 0 b, vertexStep_pow_dplusStar_C_elemSymm_one hq1 b,
    pow_zero, one_smul, zero_add, pow_one, mul_add, mul_smul_comm, mul_smul_comm, map_add,
    map_smul, map_smul,
    show (auxVar 1 : Total L) * MvPolynomial.C (Sym.elemSymm L 1)
      = (auxVar 1 : Total L) ^ 1 * MvPolynomial.C (Sym.elemSymm L 1) from by rw [pow_one],
    dminus_one_auxVar_pow_mul_C, Nat.cast_one, Sym.bop_one_elemSymm_one,
    show (auxVar 1 : Total L) * auxVar 1 = (auxVar (0 + 1) : Total L) ^ 2 from by
      norm_num; ring,
    dminus_auxVar_pow q 0 2]
  simp only [map_add, map_neg, map_mul]
  rw [show ((-1 : Total L) ^ 2) = 1 from by norm_num, one_mul,
    show (MvPolynomial.C (MvPolynomial.C (1 - q)) : Total L) = scal (1 - q) from rfl,
    ← smul_eq_scal_mul]
  match_scalars <;> ring

/-- `Ξ_{b+1,1} = Z^b` is the straight monomial with no `Y`: `HJO.Mellit.slopeEval_one_right` read
against `HJO.Sweep.straightMonomial`. -/
theorem slopeOperator_one_succ_one (q u : L) (b : ℕ) :
    slopeOperator q u 1 (b + 1) 1 = straightMonomial q u 0 b := by
  rw [slopeOperator_eq_slopeEval, Mellit.slopeEval_one_right _ _ (by omega), straightMonomial,
    pow_zero, one_mul, Nat.add_sub_cancel]

/-- **The clause `HJO.Mellit.lhsRewrite_sweepWitness` at the slope `(b+1,1)` and `f = e_1`, for
every `b`.**

The two sides are `HJO.Sym.qop_succ_one_elemSymm_one` and
`HJO.Sweep.dminus_straightMonomial_slopeArg_elemSymm_one`, and they agree. -/
theorem lhsSlopeAt_succ_one_elemSymm_one (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1)
    (hM : (1 - q) * (1 - u) ≠ 0) (b : ℕ) :
    Mellit.LhsSlopeAt q u (b + 1) 1 (Sym.elemSymm L 1) := by
  rw [Mellit.LhsSlopeAt, slopeOperator_one_succ_one,
    dminus_straightMonomial_slopeArg_elemSymm_one hq0 hu0 hq1 b,
    Sym.qop_succ_one_elemSymm_one hM b, map_add, C_smul, C_smul]
  norm_num

/-- The clause identifies the sweep side of the `(b+1,1)` column at `f = e_1` with
`C(Q_{b+1,1}e_1)`, the sign `(-1)^{1+1}` being trivial on this column. -/
theorem dminus_straightMonomial_slopeArg_elemSymm_one_eq_C (hq0 : q ≠ 0) (hu0 : u ≠ 0)
    (hq1 : q ≠ 1) (hM : (1 - q) * (1 - u) ≠ 0) (b : ℕ) :
    dminus q 1 (straightMonomial q u 0 b (Mellit.slopeArg q u (Sym.elemSymm L 1)))
      = MvPolynomial.C (Sym.Qop q u (b + 1) 1 (Sym.elemSymm L 1)) := by
  have h := lhsSlopeAt_succ_one_elemSymm_one hq0 hu0 hq1 hM b
  rw [Mellit.LhsSlopeAt, slopeOperator_one_succ_one] at h
  rw [h]
  norm_num

/-- **The `(a,1)` column at `f = e_1` is NOT independent of `a`** — in sharp contrast with the
vacuum, where `HJO.Sweep.dminus_straightMonomial_slopeArg_one` gives the same `-e_1` at every `b`.
Already `b = 0` and `b = 1` differ, by `HJO.Sym.colAlpha_one_ne_colAlpha_zero`: the defect is
`M(e_1^2 + ce_2)` for a scalar `c`, nonzero because the elementary symmetric functions freely
generate `Λ`.

So the degree-one coefficient `f = e_1` is the smallest place where the column has content, and the
`b`-independence at the vacuum is a property of the vacuum and not of the family. -/
theorem dminus_straightMonomial_slopeArg_elemSymm_one_ne (hq0 : q ≠ 0) (hu0 : u ≠ 0)
    (hq1 : q ≠ 1) (hM : (1 - q) * (1 - u) ≠ 0) :
    dminus q 1 (straightMonomial q u 0 1 (Mellit.slopeArg q u (Sym.elemSymm L 1)))
      ≠ dminus q 1 (straightMonomial q u 0 0 (Mellit.slopeArg q u (Sym.elemSymm L 1))) := by
  rw [dminus_straightMonomial_slopeArg_elemSymm_one_eq_C hq0 hu0 hq1 hM 1,
    dminus_straightMonomial_slopeArg_elemSymm_one_eq_C hq0 hu0 hq1 hM 0]
  intro h
  exact Sym.qop_succ_one_elemSymm_one_ne_of_ne hM (Sym.colAlpha_one_ne_colAlpha_zero hM)
    (MvPolynomial.C_injective _ _ h)

end HJO.Sweep
