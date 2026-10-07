/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.LhsSingletonAxisResidual
public import HJO.Shuffle.CopCompHExpansion

/-! # The creation side of the `hlhs` clause at EVERY composition

`HJO.Mellit.LhsComputes` (`HJO/Shuffle/SweepWitnessLhs.lean`) is one of the two binders left in
`HJO.Mellit.shuffle_of_lhs_and_induction`, and it is decided at exactly three compositions — `[1]`,
`[2]` and `[1,1]`. Its left-hand side is `Θ(C_α 1)(1)` for an arbitrary slope homomorphism `Θ`. This
file evaluates that side at **every** composition `α`, in two vocabularies, and reads off what the
binder over `α` still needs.

## What is proved

* `HJO.Mellit.theta_copComp` — **the creation side at every `α`, in the `h`-operators.** For every
  algebra homomorphism `Θ` and every composition,

    `Θ(C_α 1) = (Θ ∘ hSub)(copCompH q α 1)`,

  i.e. the creation side is the *explicit* polynomial `HJO.CreationSeeds.copCompH q α 1` with the
  variable standing for `h_n` replaced by the **operator** `Θ(h_n)`. Unconditional in `q` and `u`,
  and it does not even ask `Θ` to be a slope homomorphism. This is
  `HJO.CreationSeeds.copComp_apply_one_eq_hSub` pushed along `Θ`, and it is cited as an
  *expansion*: `HJO.Sym.hSub` is not proved injective, so nothing here says the preimage is unique
  — the content is that this particular explicit preimage works.

* `HJO.Mellit.theta_copComp_axis` — **the same, in the slope operators.** With `v = qu` neither zero
  nor a root of unity,

    `Θ(C_α 1) = (Θ ∘ axisSub v)(hUSub v (copCompH q α 1))`,   `(Θ ∘ axisSub v)(p_k) = Q_{ak,bk}`,

  `HJO.Mellit.theta_axisSub_powerSum` being the second half. So the creation side at every `α` is an
  explicit polynomial in the collinear slope operators `Q_{ak,bk}`, applied to the vacuum.

* `HJO.Mellit.theta_copComp_congr` and `HJO.Mellit.lhsAt_congr_of_isSlopeHom` — **the `∀ Θ`
  binder of the clause is free at every `α`.** Two slope homomorphisms take the same value on
  every creation seed, so the clause at `α` for one is the clause at `α` for the other, and
  `HJO.Mellit.lhsWord_iff_forall_lhsAt` removes the quantifier outright once any one slope
  homomorphism is in hand (`HJO.Sym.exists_isSlopeHom` supplies one). This is strictly cheaper than
  `HJO.Sym.isSlopeHom_unique`: that needs `HJO.Sym.axisSub_surjective` and hence `CharZero L`, while
  the creation seeds are in the image of `HJO.Sym.axisSub` *by construction*
  (`HJO.CreationSeeds.copComp_apply_one_eq_axisSub`), so no surjectivity and no `CharZero` is spent.

* `HJO.Mellit.theta_copComp_pair` and `HJO.Mellit.theta_copComp_pair_apply_one` — **the two-part
  creation side at a general pair `(A,B)`**, the first genuinely general case beyond the one-part
  family:

    `Θ(C_{(A,B)}1)(1) = (-q)^{1-A}(-q)^{1-B} ∑_{j≤B} c_j · Θ(h_{B-j})(Θ(h_{A+j})(1))`,

  with `c_j = HJO.CreationSeeds.dispCoeff q j`. Unconditional in `q` and `u`. Note the shape: the
  *outer* operator `Θ(h_{B-j})` is applied to a **non-vacuum** argument. That is the quantifier the
  one-part clause family does not reach; see "What remains" below.

* `HJO.Mellit.theta_completeHomog_one_eq_neg_qop` and
  `HJO.Mellit.theta_completeHomog_two_smul_gen` — `Θ(h_1) = -Q_{a,b}` and
  `(1+qu)Θ(h_2) = qu(Q_{a,b}^2 - Q_{2a,2b})` at **every** slope `(a,b)`,
  the second being `HJO.Mellit.theta_completeHomog_two_smul` with `(2,3)` released.

* `HJO.Mellit.theta_copComp_one_one_of_pair` and
  `HJO.Mellit.lhsAt_two_three_one_one_of_pair` — **a consistency check.** The decided instance
  `[1,1]` is re-derived *through* the general two-part formula: specialising it at `A = B = 1`
  and clearing `1 + qu` reproduces `HJO.Mellit.theta_copComp_one_one` on the nose, and feeding
  that into `HJO.Mellit.qop_double_apply_one_two_three` re-proves
  `HJO.Mellit.lhsAt_two_three_one_one`. The two routes to that operator identity share nothing: the
  earlier one expands `C_1C_1(1)` in the axis generators through
  `HJO.Sym.elemSymm_two_eq_axisGen`, this one expands it in the `h`-basis through
  `HJO.CreationSeeds.cop_completeHomog` and `HJO.CreationSeeds.dispCoeff`. An off-by-one in the
  `j`-sum, a sign in `dispCoeff`, or the second index `A+j` read as `A-j` all separate them.

* `HJO.Mellit.lhsAt_two_three_pair_iff` — **the clause at `(2,3)` and a general two-part
  composition, with every scalar cleared.** The two-part analogue of the one-part
  `HJO.Mellit.lhsAt_two_three_singleton_iff`: for every `A` and `B`,

    `LhsAt q u 2 3 Θ [A,B]  ↔  ∑_{j≤B} c_j Θ(h_{B-j})(Θ(h_{A+j})(1)) = ct(d_-^2 G_{2,B}G_{1,A}(1))`,

  an **equivalence** on `q ≠ 0` alone — the displacement scalars of the creation side cancel the
  clause's own normalisation exactly (`HJO.Mellit.pair_scalar_eq`), and at `(2,3)` the residual sign
  `(-1)^{(A+B)(a+b+1)}` is `+1`, so no constant survives.
  `HJO.Mellit.sum_dispCoeff_two_three_one_one` runs it forward at `A = B = 1` onto the decided
  instance, which is a check on that bookkeeping.

## What remains open, and the quantifier

The binder over `α` is **not** discharged, and the missing datum is now exactly nameable.
`HJO.Mellit.theta_copComp` reduces the creation side at every `α` to the one-part family
`{Θ(h_n)}` — but as *operators*. The clause at a one-part composition
(`HJO.Mellit.lhsAt_two_three_singleton_iff_bop`) is a statement about `Θ(h_A)(1)`, the value at the
**vacuum** only. At `α` of length `ℓ ≥ 2` the formula nests: `Θ(h_{B-j})` is applied to
`Θ(h_{A+j})(1)`, an element of `Λ` of positive degree. So:

**open, with the quantifier named:** the clause at every composition of length `≥ 2` needs the value
of `Θ(h_m)` at the `Λ`-elements `Θ(h_n)(1)` — that is, `∀ m n, Θ(h_m)(Θ(h_n)(1))` — and the whole
one-part family of clauses constrains only the diagonal-free part `∀ n, Θ(h_n)(1)`. Nothing in this
file, and nothing elsewhere in the library, closes that gap; the operator recursion
`HJO.Mellit.theta_completeHomog_smul_eq_sum_qop` reduces it to `∀ s g, Q_{2s,3s}(g)` at general
arguments `g`, which is where `HJO.Sym.dop_mul_mulLeft_elemSymm` (the straightening rule) is the
available tool and where no explicit evaluation past `D`-words of length two exists.

Equally open: the **sweep** side at every `α`. `HJO.Mellit.lhsAt_append_iff` gives its recursion and
`HJO.Sweep.constantCoeff_dminus_one_of_mem_piece` evaluates `ct ∘ d_-` at length one only, so
nothing here compares the two recursions at length `≥ 2` beyond the single decided `[1,1]`.

## Genericity

`HJO.Mellit.theta_copComp`, `HJO.Mellit.theta_copComp_pair`,
`HJO.Mellit.theta_copComp_pair_apply_one`: **none**. Both sides are totalisations at `q = 0`, the
displacement coefficient being `HJO.CreationSeeds.dispCoeff`'s unconditional spelling
`c_j = q^{-j} - q^{-(j-1)}` rather than the algebraically equal `(1-q)q^{-j}`, which is false at
`q = 0`.

`HJO.Mellit.theta_copComp_axis`, `HJO.Mellit.theta_copComp_congr`,
`HJO.Mellit.lhsAt_congr_of_isSlopeHom`, `HJO.Mellit.lhsWord_iff_forall_lhsAt`: `v = qu ≠ 0` and
`v^{j+1} ≠ 1` for every `j`, verbatim `HJO.Sym.adjoin_axisGen_eq_top`'s and so
`HJO.CreationSeeds.copComp_apply_one_eq_axisSub`'s. These are the difference between true and false,
not between stated and vacuous: `HJO.Sym.axisGen` carries the scalar `v/(v-1)`, and in a field
`0⁻¹ = 0`, so at `v ∈ {0,1}` every `U_k` is the zero element (`HJO.Sym.axisGen_eq_zero`) and the
prescription pins nothing.

`HJO.Mellit.theta_completeHomog_one_eq_neg_qop`, `HJO.Mellit.theta_completeHomog_two_smul_gen`:
`qu ≠ 0` and `qu ≠ 1`, `HJO.Sym.axisGen_one`'s. The scalar `1 + qu` is carried on the left and never
inverted, so nothing here excludes `qu = -1`.

`HJO.Mellit.theta_copComp_one_one_of_pair`: `q ≠ 0` in addition — the check multiplies
`c_1 = q^{-1} - 1` by `qu`, and `(q^{-1}-1)qu = u - qu` needs it. This is the one place a letter
would become the zero map: at `q = 0`, `c_1 = -1` while `(1-q)q^{-1} = 0`, so the hypothesis belongs
to the *route*, and the statement it proves is the earlier `HJO.Mellit.theta_copComp_one_one`, which
does not carry it.

`HJO.Mellit.lhsAt_two_three_one_one_of_pair` and `HJO.Mellit.sum_dispCoeff_two_three_one_one`:
verbatim `HJO.Mellit.lhsAt_two_three_one_one`'s — `q ≠ 0`, `u ≠ 0`, `q ≠ 1`, `u ≠ 1`, `qu ≠ 1`,
`qu + 1 ≠ 0`.

`HJO.Mellit.pair_scalar_eq` and `HJO.Mellit.lhsAt_two_three_pair_iff`: `q ≠ 0` and nothing else, not
even positivity of the parts. It is needed to add the two negative exponents `1-A` and `1-B`; at
`q = 0` both scalars are `0` and the equivalence would read `0 = 0 ↔ ...`, i.e. would be false
rather than vacuous in the backward direction.

## Relation to the `hlhs` clause

These are values of `HJO.Sym.IsSlopeHom` on `HJO.Sym.CopComp`, while
`HJO.Mellit.lhsRewrite_sweepWitness` asserts the *equation* between this side and the sweep side,
not this side's value; `HJO.Mellit.lhsAt_two_three_one_one_of_pair` re-proves an instance proved
elsewhere by a second route.

## References

The file evaluates `HJO.Sym.Cop` and `HJO.Sym.CopComp` through `HJO.Sym.completeHomog`,
`HJO.Sym.axisGen`, `HJO.Sym.axisSub`, `HJO.Sym.IsSlopeHom`, `HJO.Sym.Qop` and
`HJO.Sym.sum_alternating_pow_completeHomog_mul_elemSymm`, towards
`HJO.Mellit.lhsRewrite_sweepWitness`.
-/

@[expose] public section

namespace HJO.Mellit

open Finset HJO.Sym HJO.CreationSeeds

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L} {a b : ℕ}

/-! ### The creation side at every composition, in the `h`-operators -/

/-- **The creation side of the `hlhs` clause at every composition, in the `h`-operators.**

`Θ(C_α 1) = (Θ ∘ hSub)(copCompH q α 1)`: the explicit polynomial
`HJO.CreationSeeds.copCompH q α 1` on the `h`-variables, with the variable standing for `h_n`
replaced by the operator `Θ(h_n)` (`HJO.Mellit.theta_hSub_X`).

`HJO.CreationSeeds.copComp_apply_one_eq_hSub` pushed along `Θ`, so this is an **expansion** and not
a characterisation: `HJO.Sym.hSub` is not proved injective, and being surjective under the standing
genericity it has many preimages. The content is that *this* explicit one is a preimage.

Unconditional in `q` and `u`, at every composition, and `Θ` is not asked to be a slope
homomorphism. -/
theorem theta_copComp (Θ : Lambda L →ₐ[L] Module.End L (Lambda L)) (q : L) (α : List ℕ) :
    Θ (CopComp q α (1 : Lambda L)) = (Θ.comp (hSub L)) (copCompH q α (1 : Lambda L)) := by
  rw [copComp_apply_one_eq_hSub, AlgHom.comp_apply]

/-- The substitution of `HJO.Mellit.theta_copComp` on the variable standing for `h_{i+1}`: it is the
operator `Θ(h_{i+1})`. So the creation side at every composition is determined by the one-part
family of **operators** `{Θ(h_n)}`. -/
theorem theta_hSub_X (Θ : Lambda L →ₐ[L] Module.End L (Lambda L)) (i : ℕ) :
    (Θ.comp (hSub L)) (MvPolynomial.X i) = Θ (completeHomog L (i + 1)) := by
  rw [AlgHom.comp_apply, hSub_X]

/-! ### The creation side at every composition, in the slope operators -/

/-- **The creation side at every composition, in the slope operators.**

`Θ(C_α 1) = (Θ ∘ axisSub v)(hUSub v (copCompH q α 1))` with `v = qu`, from
`HJO.CreationSeeds.copComp_apply_one_eq_axisSub`. Together with
`HJO.Mellit.theta_axisSub_powerSum` — which says the substitution sends `p_k` to `Q_{ak,bk}` — this
writes the creation side at every composition as an explicit polynomial in the collinear slope
operators.

Genericity: `v ≠ 0` and `v^{j+1} ≠ 1` for every `j`, which at `v = qu` read `q ≠ 0`, `u ≠ 0` and
`(qu)^k ≠ 1` for `k ≥ 1`; they are `HJO.Sym.axisSub_hU`'s, and at `v ∈ {0,1}` every axis generator
is the zero element so the statement would be false rather than vacuous. Nothing is asked of `Θ`
here — the prescription enters only through `HJO.Mellit.theta_axisSub_powerSum`. -/
theorem theta_copComp_axis (Θ : Lambda L →ₐ[L] Module.End L (Lambda L)) (q : L) {v : L}
    (hv0 : v ≠ 0) (hv1 : ∀ j : ℕ, v ^ (j + 1) ≠ 1) (α : List ℕ) :
    Θ (CopComp q α (1 : Lambda L))
      = (Θ.comp (axisSub v)) (hUSub v (copCompH q α (1 : Lambda L))) := by
  rw [copComp_apply_one_eq_axisSub q hv0 hv1, AlgHom.comp_apply]

/-- **The substitution of `HJO.Mellit.theta_copComp_axis` is the slope prescription**: it sends the
power sum `p_k`, `k ≥ 1`, to `Q_{ak,bk}`. This is `HJO.Sym.IsSlopeHom` and
`HJO.Sym.axisSub_powerSum`, with no hypothesis on `q` or `u` — the prescription is read, not
evaluated. -/
theorem theta_axisSub_powerSum {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)}
    (hΘ : IsSlopeHom a b q u Θ) {k : ℕ} (hk : 0 < k) :
    (Θ.comp (axisSub (q * u))) (powerSum L k) = Qop q u (a * k) (b * k) := by
  rw [AlgHom.comp_apply, axisSub_powerSum (q * u) hk, hΘ k hk]

/-! ### The `∀ Θ` binder of the clause is free, at every composition -/

/-- **Any two slope homomorphisms agree on every creation seed.**

The composite `Θ ∘ axisSub (qu)` is pinned on every generator by the prescription alone
(`HJO.Mellit.theta_axisSub_powerSum`), and `HJO.Mellit.theta_copComp_axis` puts every creation seed
in the image of `axisSub (qu)` *explicitly*. So no surjectivity of the axis substitution is needed
and, unlike `HJO.Sym.isSlopeHom_unique`, no `CharZero L`: this is the part of uniqueness the clause
actually consumes.

Genericity: `qu ≠ 0` and `(qu)^{j+1} ≠ 1` for every `j`. -/
theorem theta_copComp_congr (hv0 : q * u ≠ 0) (hv1 : ∀ j : ℕ, (q * u) ^ (j + 1) ≠ 1)
    {Θ Θ' : Lambda L →ₐ[L] Module.End L (Lambda L)} (hΘ : IsSlopeHom a b q u Θ)
    (hΘ' : IsSlopeHom a b q u Θ') (α : List ℕ) :
    Θ (CopComp q α (1 : Lambda L)) = Θ' (CopComp q α (1 : Lambda L)) := by
  have key : Θ.comp (axisSub (q * u)) = Θ'.comp (axisSub (q * u)) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    have h : ∀ Ψ : Lambda L →ₐ[L] Module.End L (Lambda L), IsSlopeHom a b q u Ψ →
        (Ψ.comp (axisSub (q * u))) (MvPolynomial.X i)
          = Qop q u (a * (i + 1)) (b * (i + 1)) := by
      intro Ψ hΨ
      rw [AlgHom.comp_apply, axisSub_X, hΨ (i + 1) (Nat.succ_pos i)]
    rw [h Θ hΘ, h Θ' hΘ']
  rw [theta_copComp_axis Θ q hv0 hv1, theta_copComp_axis Θ' q hv0 hv1,
    AlgHom.congr_fun key (hUSub (q * u) (copCompH q α (1 : Lambda L)))]

/-- **The clause at a composition does not depend on which slope homomorphism it is read at.**
`HJO.Mellit.LhsAt` mentions `Θ` only through `Θ(C_α 1)`, which
`HJO.Mellit.theta_copComp_congr` pins. Genericity: `qu ≠ 0` and `(qu)^{j+1} ≠ 1`. -/
theorem lhsAt_congr_of_isSlopeHom (hv0 : q * u ≠ 0) (hv1 : ∀ j : ℕ, (q * u) ^ (j + 1) ≠ 1)
    {Θ Θ' : Lambda L →ₐ[L] Module.End L (Lambda L)} (hΘ : IsSlopeHom a b q u Θ)
    (hΘ' : IsSlopeHom a b q u Θ') (α : List ℕ) :
    LhsAt q u a b Θ α ↔ LhsAt q u a b Θ' α := by
  rw [LhsAt, LhsAt, theta_copComp_congr hv0 hv1 hΘ hΘ' α]

/-- **The `∀ Θ` binder of `HJO.Mellit.LhsWord` is removable.** Given one slope homomorphism `Θ₀` —
`HJO.Sym.exists_isSlopeHom` constructs one at generic parameters — the `Λ`-level clause over every
slope homomorphism and every composition is *equivalent* to the clause at `Θ₀` alone.

Read left to right this is instantiation; read right to left it is
`HJO.Mellit.lhsAt_congr_of_isSlopeHom`. So the quantifier costs nothing, and this is a change of
vocabulary and not of difficulty: what remains after it is the same equation at each `α`.

Genericity: `qu ≠ 0` and `(qu)^{j+1} ≠ 1`. -/
theorem lhsWord_iff_forall_lhsAt (hv0 : q * u ≠ 0) (hv1 : ∀ j : ℕ, (q * u) ^ (j + 1) ≠ 1)
    {Θ₀ : Lambda L →ₐ[L] Module.End L (Lambda L)} (hΘ₀ : IsSlopeHom a b q u Θ₀) :
    LhsWord q u a b ↔ ∀ α : List ℕ, (∀ x ∈ α, 0 < x) → 0 < α.sum → LhsAt q u a b Θ₀ α := by
  constructor
  · intro h α hpos hsum
    exact h Θ₀ hΘ₀ α.sum hsum α hpos rfl
  · intro h Θ hΘ N hN α hpos hsum
    subst hsum
    exact (lhsAt_congr_of_isSlopeHom hv0 hv1 hΘ₀ hΘ α).1 (h α hpos hN)

/-! ### The two-part creation side at a general pair -/

/-- **The two-part creation side at a general pair, as an operator.**

`Θ(C_{(A,B)}1) = (-q)^{1-A}(-q)^{1-B} ∑_{j≤B} c_j · Θ(h_{B-j})Θ(h_{A+j})`, with
`c_j = HJO.CreationSeeds.dispCoeff q j`. This is `HJO.Mellit.copComp_pair_apply_one` pushed along
the multiplicative `Θ`, so the *product* `h_{B-j}h_{A+j}` becomes the **composite** of two
operators — and the `j`-sum runs to the inner part `B`, so the second index never drops below `A`.

Unconditional in `q` and `u`: `HJO.CreationSeeds.dispCoeff`'s spelling
`c_j = q^{-j} - q^{-(j-1)}` is a totalisation at `q = 0` on both sides. -/
theorem theta_copComp_pair (Θ : Lambda L →ₐ[L] Module.End L (Lambda L)) (q : L) (A B : ℕ) :
    Θ (CopComp q [A, B] (1 : Lambda L))
      = ((-q) ^ (1 - (A : ℤ)) * (-q) ^ (1 - (B : ℤ))) •
          ∑ j ∈ range (B + 1), dispCoeff q j •
            (Θ (completeHomog L (B - j)) * Θ (completeHomog L (A + j))) := by
  rw [copComp_pair_apply_one, ← MvPolynomial.smul_eq_C_mul, map_smul, map_sum]
  refine congrArg _ (Finset.sum_congr rfl fun j _ => ?_)
  rw [mul_assoc, ← MvPolynomial.smul_eq_C_mul, map_smul, map_mul]

/-- **The two-part creation side at a general pair, at the vacuum** — the shape the clause reads:

`Θ(C_{(A,B)}1)(1) = (-q)^{1-A}(-q)^{1-B} ∑_{j≤B} c_j · Θ(h_{B-j})(Θ(h_{A+j})(1))`.

The outer operator is applied to `Θ(h_{A+j})(1)`, an element of `Λ` of degree `3(A+j)` at `(2,3)`
and **not** the vacuum. That is the precise datum the one-part clause family
(`HJO.Mellit.lhsAt_two_three_singleton_iff_bop`, a statement about `Θ(h_A)(1)` only) does not
supply, and it is why the clause at length `≥ 2` is not a consequence of the clause at length `1`.

Unconditional in `q` and `u`. -/
theorem theta_copComp_pair_apply_one (Θ : Lambda L →ₐ[L] Module.End L (Lambda L)) (q : L)
    (A B : ℕ) :
    Θ (CopComp q [A, B] (1 : Lambda L)) 1
      = ((-q) ^ (1 - (A : ℤ)) * (-q) ^ (1 - (B : ℤ))) •
          ∑ j ∈ range (B + 1), dispCoeff q j •
            Θ (completeHomog L (B - j)) (Θ (completeHomog L (A + j)) 1) := by
  have h := congrArg (fun T : Module.End L (Lambda L) => T (1 : Lambda L))
    (theta_copComp_pair Θ q A B)
  simpa only [LinearMap.smul_apply, LinearMap.sum_apply, Module.End.mul_apply] using h

/-! ### The one-part operators at degrees one and two, at every slope -/

/-- **`Θ(h_1) = -Q_{a,b}` at every slope.** `h_1 = e_1 = -U_1` (`HJO.Sym.axisGen_one`), and
`HJO.Sym.IsSlopeHom` sends `U_1` to `Q_{a,b}`. Genericity: `qu ≠ 0`, `qu ≠ 1`. -/
theorem theta_completeHomog_one_eq_neg_qop (hv0 : q * u ≠ 0) (hv1 : q * u ≠ 1)
    {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)} (hΘ : IsSlopeHom a b q u Θ) :
    Θ (completeHomog L 1) = -Qop q u a b := by
  have h1 : completeHomog L 1 = CopComp q [1] (1 : Lambda L) := by
    rw [copComp_one_apply_one, CopPower.completeHomog_one, elemSymm_one]
  rw [h1, theta_copComp_one hv0 hv1 hΘ]

/-- **`(1 + qu)Θ(h_2) = qu(Q_{a,b}^2 - Q_{2a,2b})` at every slope**, which is
`HJO.Mellit.theta_completeHomog_two_smul` with the restriction to `(2,3)` released.

`HJO.Sym.completeHomog_two_smul_eq_axisGen` pushed along `Θ`: `U_1^2` becomes the composite of
`Q_{a,b}` with itself, and `U_2` the operator at the **doubled** slope `Q_{2a,2b}` — the operator
the clause at a one-part composition of size `1` never mentions.

The scalar `1 + qu` is not inverted, so `qu = -1` is not excluded; there the statement reads
`0 = 0`, and that is exactly where `U_1, U_2` fail to span `h_2`. Genericity: `qu ≠ 0`, `qu ≠ 1`. -/
theorem theta_completeHomog_two_smul_gen (hv0 : q * u ≠ 0) (hv1 : q * u ≠ 1)
    {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)} (hΘ : IsSlopeHom a b q u Θ) :
    (q * u + 1) • Θ (completeHomog L 2)
      = (q * u) • (Qop q u a b * Qop q u a b - Qop q u (a * 2) (b * 2)) := by
  have h := congrArg Θ (completeHomog_two_smul_eq_axisGen (L := L) hv0 hv1)
  rw [map_smul, map_smul, map_sub, map_pow, hΘ 1 one_pos, hΘ 2 two_pos, mul_one, mul_one] at h
  rw [h]
  norm_num [sq]

/-! ### Consistency check: the decided `[1,1]` instance, through the general two-part formula -/

/-- **The general two-part formula reproduces `HJO.Mellit.theta_copComp_one_one`.**

At `A = B = 1` the scalars `(-q)^{1-A}` are `1`, the `j`-sum has the two terms `c_0 = 1` and
`c_1 = q^{-1}-1`, and `h_0 = 1` makes the second term `Θ(h_2)(1)`. Substituting
`HJO.Mellit.theta_completeHomog_one_eq_neg_qop` and `HJO.Mellit.theta_completeHomog_two_smul_gen`
and clearing `1 + qu` gives

`(1+qu)Θ(C_1C_1(1)) = (u+1)Q_{a,b}^2 + u(q-1)Q_{2a,2b}`,

which is the earlier `HJO.Mellit.theta_copComp_one_one`, statement for statement — and
`HJO.Mellit.theta_copComp_one_one_of_pair_eq` checks that by `rfl`, which can only typecheck if the
two propositions are literally the same. The two routes share nothing: the earlier one expands
`C_1C_1(1)` in the axis generators via `HJO.Sym.elemSymm_two_eq_axisGen`, this one in the `h`-basis
via `HJO.CreationSeeds.cop_completeHomog`. So this is the check on the `j`-range, on the sign of
`HJO.CreationSeeds.dispCoeff` and on the index `A+j` of the second factor.

Genericity: `qu ≠ 0`, `qu ≠ 1`, and `q ≠ 0` — the latter belongs to the route, being what turns
`(q^{-1}-1)qu` into `u - qu`; the statement proved does not carry it. -/
theorem theta_copComp_one_one_of_pair (hq0 : q ≠ 0) (hv0 : q * u ≠ 0) (hv1 : q * u ≠ 1)
    {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)} (hΘ : IsSlopeHom a b q u Θ) :
    (q * u + 1) • Θ (CopComp q [1, 1] (1 : Lambda L))
      = (u + 1) • (Qop q u a b * Qop q u a b)
        + (u * (q - 1)) • Qop q u (a * 2) (b * 2) := by
  have hcoef : (q⁻¹ - 1) * (q * u) = u - q * u := by
    have hinv : q⁻¹ * q = 1 := inv_mul_cancel₀ hq0
    linear_combination u * hinv
  have hpair := theta_copComp_pair Θ q 1 1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.cast_one, sub_self,
    zpow_zero, mul_one, one_smul, dispCoeff_zero, dispCoeff_one, Nat.sub_zero, Nat.add_zero,
    Nat.sub_self, show (1 : ℕ) + 1 = 2 from rfl, CopPower.completeHomog_zero, map_one, one_mul,
    theta_completeHomog_one_eq_neg_qop hv0 hv1 hΘ, neg_mul_neg] at hpair
  -- `hpair : Θ(C_1C_1 1) = Q·Q + (q⁻¹ - 1) • Θ(h_2)`.
  rw [hpair, smul_add, smul_comm (q * u + 1) (q⁻¹ - 1),
    theta_completeHomog_two_smul_gen hv0 hv1 hΘ, smul_smul, hcoef]
  module

/-- **The two routes to `(1+qu)Θ(C_1C_1(1))` state the same proposition.** `rfl` between the two
proofs typechecks only if the statements are identical, which is a stronger check than comparing
printed coefficients: it rules out a transposed index, a re-associated product or a sign absorbed
into a scalar. Both sides are `HJO.Mellit.theta_copComp_one_one`'s statement — the earlier one
proved from the axis expansion of `e_2`, `HJO.Mellit.theta_copComp_one_one_of_pair` from the
`h`-basis expansion at a general pair. -/
theorem theta_copComp_one_one_of_pair_eq (hq0 : q ≠ 0) (hv0 : q * u ≠ 0) (hv1 : q * u ≠ 1)
    {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)} (hΘ : IsSlopeHom a b q u Θ) :
    theta_copComp_one_one_of_pair hq0 hv0 hv1 hΘ = theta_copComp_one_one hv0 hv1 hΘ := rfl

/-- `HJO.Mellit.theta_copComp_one_one_of_pair` at the vacuum, the shape the clause reads. -/
theorem theta_copComp_one_one_apply_one_of_pair (hq0 : q ≠ 0) (hv0 : q * u ≠ 0) (hv1 : q * u ≠ 1)
    {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)} (hΘ : IsSlopeHom a b q u Θ) :
    (q * u + 1) • Θ (CopComp q [1, 1] (1 : Lambda L)) 1
      = (u + 1) • Qop q u a b (Qop q u a b (1 : Lambda L))
        + (u * (q - 1)) • Qop q u (a * 2) (b * 2) (1 : Lambda L) := by
  have h := congrArg (fun T : Module.End L (Lambda L) => T (1 : Lambda L))
    (theta_copComp_one_one_of_pair hq0 hv0 hv1 hΘ)
  simpa only [LinearMap.smul_apply, LinearMap.add_apply, Module.End.mul_apply] using h

/-- **The decided `[1,1]` instance of the `hlhs` clause, re-derived through the general two-part
formula.** Word for word `HJO.Mellit.lhsAt_two_three_one_one`, with
`HJO.Mellit.theta_copComp_one_one_of_pair` in place of `HJO.Mellit.theta_copComp_one_one` — so the
creation side comes from the `h`-basis expansion at general `(A,B)` rather than from the degree-two
axis expansion, and the sweep side is `HJO.Mellit.qop_double_apply_one_two_three`.

This is the consistency check the general formula has to pass: it lands on an already-decided value,
and a sign or an index off by one anywhere in `HJO.Mellit.theta_copComp_pair_apply_one` would leave
it unprovable.

Genericity: verbatim `HJO.Mellit.lhsAt_two_three_one_one`'s — `q ≠ 0`, `u ≠ 0`, `q ≠ 1`, `u ≠ 1`,
`qu ≠ 1`, `qu + 1 ≠ 0`. -/
theorem lhsAt_two_three_one_one_of_pair (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) (hu1 : u ≠ 1)
    (hv1 : q * u ≠ 1) (hvm : q * u + 1 ≠ 0)
    {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)} (hΘ : IsSlopeHom 2 3 q u Θ) :
    LhsAt q u 2 3 Θ [1, 1] := by
  have hM : (1 - q) * (1 - u) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr (Ne.symm hq1)) (sub_ne_zero.mpr (Ne.symm hu1))
  have hv0 : q * u ≠ 0 := mul_ne_zero hq0 hu0
  have h := theta_copComp_one_one_apply_one_of_pair hq0 hv0 hv1 hΘ
  rw [show (2 * 2 : ℕ) = 4 from rfl, show (3 * 2 : ℕ) = 6 from rfl,
    qop_double_apply_one_two_three hM hq0 hu0 hq1] at h
  have hcore : Θ (CopComp q [1, 1] (1 : Lambda L)) 1
      = MvPolynomial.constantCoeff (lowerRun q 2 (stageWordTotal q u 2 3 [1, 1])) :=
    smul_right_injective (Lambda L) hvm h
  rw [LhsAt]
  norm_num
  exact hcore

/-! ### The two-part clause at a general pair, normalised -/

omit [Algebra ℚ L] in
/-- **The two scalars of the clause at a two-part composition are the same scalar.**
`(-q)^{1-A}(-q)^{1-B} = (-1)^{A+B}q^{2-(A+B)}`: the creation side's displacement scalars and the
clause's own normalisation agree at length two, which is what makes
`HJO.Mellit.lhsAt_two_three_pair_iff` carry no leftover constant.

Genericity: `q ≠ 0`, needed to add the two negative exponents at all. -/
private theorem pair_scalar_eq (hq0 : q ≠ 0) (A B : ℕ) :
    (-q) ^ (1 - (A : ℤ)) * (-q) ^ (1 - (B : ℤ))
      = (-1 : L) ^ (A + B) * q ^ ((2 : ℤ) - ((A + B : ℕ) : ℤ)) := by
  have hn : (-1 : L) ≠ 0 := by norm_num
  have hnq : (-q : L) ≠ 0 := neg_ne_zero.mpr hq0
  have hsq : ∀ n : ℕ, ((-1 : L) ^ n)⁻¹ = (-1) ^ n := fun n =>
    inv_eq_of_mul_eq_one_right (by
      rw [← pow_add, show n + n = 2 * n from by ring, pow_mul]; norm_num)
  have hsum : (1 - (A : ℤ)) + (1 - (B : ℤ)) = (2 : ℤ) - ((A + B : ℕ) : ℤ) := by push_cast; ring
  rw [← zpow_add₀ hnq, hsum, show (-q : L) = (-1) * q from by ring, mul_zpow]
  congr 1
  rw [zpow_sub₀ hn, zpow_natCast, div_eq_mul_inv, hsq]
  norm_num

/-- **The `hlhs` clause at `(2,3)` and a general two-part composition, with every scalar cleared:**

`∑_{j≤B} c_j Θ(h_{B-j})(Θ(h_{A+j})(1)) = ct(d_-^2(G_{2,B}G_{1,A}(1)))`,  `c_j = dispCoeff q j`.

This is the two-part analogue of `HJO.Mellit.lhsAt_two_three_singleton_iff`, and it is an
**equivalence** — nothing is weakened in either direction. Both scalars of `HJO.Mellit.LhsAt` cancel
against the displacement scalars of `HJO.Mellit.theta_copComp_pair_apply_one`
(`HJO.Mellit.pair_scalar_eq`), and at `(2,3)` the sign `(-1)^{(A+B)(a+b+1)}` is `+1`, so no constant
survives at all.

So the clause at every two-part composition is: the creation side's `B+1`-term sum of **nested**
values of the operators `Θ(h_·)` equals the sweep side's double lowering of the stage word. Neither
side is evaluated here. What the statement isolates is that the creation side reads
`Θ(h_m)(Θ(h_n)(1))` and nothing else, the nesting being the content the one-part family misses.

Genericity: `q ≠ 0` only — `HJO.Mellit.pair_scalar_eq`'s, and needed for the cancellation to be a
cancellation rather than `0 = 0`. Nothing is asked of `u`, of `Θ` beyond being an algebra
homomorphism, or of `A` and `B`; in particular the parts need not be positive. -/
theorem lhsAt_two_three_pair_iff (hq0 : q ≠ 0) (A B : ℕ)
    (Θ : Lambda L →ₐ[L] Module.End L (Lambda L)) :
    LhsAt q u 2 3 Θ [A, B] ↔
      ∑ j ∈ range (B + 1), dispCoeff q j •
          Θ (completeHomog L (B - j)) (Θ (completeHomog L (A + j)) 1)
        = MvPolynomial.constantCoeff (lowerRun q 2 (stageWordTotal q u 2 3 [A, B])) := by
  have hc : ((-q) ^ (1 - (A : ℤ)) * (-q) ^ (1 - (B : ℤ)) : L) ≠ 0 :=
    mul_ne_zero (zpow_ne_zero _ (neg_ne_zero.mpr hq0)) (zpow_ne_zero _ (neg_ne_zero.mpr hq0))
  rw [LhsAt, theta_copComp_pair_apply_one]
  simp only [List.sum_cons, List.sum_nil, List.length_cons, List.length_nil, Nat.add_zero,
    Nat.zero_add, show (1 + 1 : ℕ) = 2 from rfl, Nat.cast_ofNat]
  rw [show ((-1 : L) ^ ((A + B) * (3 + 1))) = 1 from by
        rw [show (A + B) * (3 + 1) = 4 * (A + B) from by ring, pow_mul]; norm_num,
    one_smul, show (2 - 1 : ℕ) = 1 from rfl, one_mul, ← pair_scalar_eq hq0 A B]
  exact ⟨fun h => smul_right_injective (Lambda L) hc h, fun h => by rw [h]⟩

/-- **The normalised two-part clause at `A = B = 1` is the decided instance**, which is the second
consistency check: it runs `HJO.Mellit.lhsAt_two_three_pair_iff` — hence
`HJO.Mellit.pair_scalar_eq`, the whole sign-and-exponent bookkeeping of the normalisation — forward
on `HJO.Mellit.lhsAt_two_three_one_one_of_pair` and lands on a value of the sweep side.

Genericity: `HJO.Mellit.lhsAt_two_three_one_one_of_pair`'s. -/
theorem sum_dispCoeff_two_three_one_one (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) (hu1 : u ≠ 1)
    (hv1 : q * u ≠ 1) (hvm : q * u + 1 ≠ 0)
    {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)} (hΘ : IsSlopeHom 2 3 q u Θ) :
    Θ (completeHomog L 1) (Θ (completeHomog L 1) 1)
        + (q⁻¹ - 1) • Θ (completeHomog L 2) (1 : Lambda L)
      = MvPolynomial.constantCoeff (lowerRun q 2 (stageWordTotal q u 2 3 [1, 1])) := by
  have h := (lhsAt_two_three_pair_iff hq0 1 1 Θ).1
    (lhsAt_two_three_one_one_of_pair hq0 hu0 hq1 hu1 hv1 hvm hΘ)
  simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, dispCoeff_zero,
    dispCoeff_one, one_smul, Nat.sub_zero, Nat.add_zero, Nat.sub_self,
    show (1 : ℕ) + 1 = 2 from rfl, CopPower.completeHomog_zero, map_one,
    Module.End.one_apply] using h

end HJO.Mellit

end
