/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.MellitStraightening
public import HJO.Shuffle.ThetaCreationSeedGeneral
public import HJO.Shuffle.ThetaCompleteHomogAxisTwoThree

/-! # `D`-words of EVERY length at EVERY `e`-monomial, and `Θ(h_m)(Θ(h_n)(1))` for `m ≤ 2`

`HJO.Mellit.theta_copComp_pair_apply_one` (`HJO/Shuffle/ThetaCreationSeedGeneral.lean`)
computes the creation side of the `hlhs` clause at every two-part composition,

  `Θ(C_{(A,B)}1)(1) = (-q)^{1-A}(-q)^{1-B} ∑_{j≤B} c_j · Θ(h_{B-j})(Θ(h_{A+j})(1))`,

and leaves exactly one datum undetermined: the nested value `Θ(h_m)(Θ(h_n)(1))`, one `h`-operator at
the **non-vacuum** element `Θ(h_n)(1)`. This file **evaluates** it for `m ≤ 2` at every `n`, and
builds the machinery that evaluation needs: the expansion of a `D`-word of **arbitrary length**
at an **arbitrary** `e`-monomial. It states no new equivalence.

## What is proved

### The `ℓ`-fold straightening sum

* `HJO.Sym.dopShiftSum` and `HJO.Sym.dop_apply_elemSymmComp_of_linear` — **one basic operator at an
  `e`-monomial, under any linear map.** Iterating `HJO.Sym.dop_elemSymm_mul` over the factors of a
  monomial: each factor `e_{n_i}` donates `s_i ≤ n_i` to the operator's index and keeps
  `e_{n_i-s_i}`.
  The ambient linear map is carried because the induction consumes one factor at a time and the
  leftover has to be pushed through whatever acts outside.

* `HJO.Sym.dopPushMono` and `HJO.Sym.dopList_reverse_apply_elemSymmComp` — **every `D`-word at every
  `e`-monomial, fully expanded:**

    `D_{k_ℓ}(⋯D_{k_1}(e_l)⋯) = dopPushMono q u [k_1,…,k_ℓ] l`,

  the word listed in application order. Each letter is one round of the shift sum, so a word of
  length `ℓ` at a monomial of `p` factors produces monomials of `p + ℓ` factors. This is the
  `ℓ`-fold sum indexed by lists of bounded sum; otherwise explicit expansion is available for words
  of length **two** only (`HJO.Sym.dop_dop_elemSymm_mul`), and the span statement
  `HJO.Sym.dopList_mul_mulLeft_mem_straightSpanLen` bounds the length without naming a coefficient.
  `HJO.Sym.dopList_reverse_apply_one` is the vacuum case.

* `HJO.Sym.dop_dop_apply_one_of_pushMono` — **the first consistency check.** The general expansion
  reproduces `HJO.Sym.dop_dop_apply_one` at **every** pair `(a,b)`, and
  `HJO.Sym.dop_dop_apply_one_of_pushMono_eq` checks by `rfl` that the two propositions are literally
  the same. The proof of `HJO.Sym.dop_dop_apply_one` is one Pieri rule on `HJO.Sym.DopInt` at the
  vacuum and shares no step with this one, so the check pins the sign `(-1)^{a+b+r}`, the direction
  of the shift and the order of the two letters.

### The slope operators at an arbitrary argument

* `HJO.Sym.qop_two_three_apply_elemSymmComp` — `Q_{2,3}` at every `e`-monomial, from the bracket
  `M⁻¹(D_2D_1 - D_1D_2)` and two words of length two.

* `HJO.Sym.qop_two_three_apply_elemSymm_one_of_pushMono` — **the second consistency check, off the
  vacuum.** Word for word `HJO.Sym.qop_two_three_apply_elemSymm_pin`, which three other routes
  already agree on; `HJO.Sym.qop_two_three_apply_elemSymm_one_of_pushMono_eq` checks it by
  `rfl`. All four coefficients agree, including the `e_4` one.

* `HJO.Sym.qop_two_three_sq_apply_elemSymmComp` and `HJO.Sym.qop_four_six_apply_elemSymmComp` —
  `Q_{2,3}^2` and the **doubled-slope** operator `Q_{4,6}` at every `e`-monomial: four and six
  `D`-words of length **four**. For `Q_{4,6}` the ladder
  `HJO.Sym.qop_two_three_axis_eq_ladder` at `k = 2` unwinds to

    `M^3 Q_{4,6} = D_2D_2D_1D_1 - 2 D_2D_1D_2D_1 + 2 D_1D_2D_1D_2 - D_1D_1D_2D_2`,

  the two `D_1D_2D_2D_1` terms cancelling outright. Nothing in them is specific to the length.

### The two-index family

* `HJO.Mellit.theta_completeHomog_mul_apply_one` — **`Θ(h_m)(Θ(h_n)(1)) = Θ(h_m h_n)(1)`**, with no
  hypothesis at all: `Θ` is multiplicative, so the nesting is only apparent and the two-index family
  is the value of `Θ` on the `h`-monomial basis, at the vacuum.
  `HJO.Mellit.theta_completeHomog_apply_one_comm` is the resulting symmetry in `m` and `n`.

* `HJO.Mellit.theta_completeHomog_one_apply_theta_apply_one` and
  `HJO.Mellit.theta_completeHomog_two_smul_apply_theta_apply_one` — **the family at `m ≤ 2`, for
  every `n`:**

    `Θ(h_1)(Θ(h_n)(1)) = -Q_{2,3}(Θ(h_n)(1))`,
    `(1+qu) Θ(h_2)(Θ(h_n)(1)) = qu (Q_{2,3}^2 - Q_{4,6})(Θ(h_n)(1))`,

  and by the symmetry also for every `m` with `n ≤ 2`. Both right-hand sides are explicit at an
  arbitrary argument by the section above, so this row of the family is reduced to the **one-part**
  values `Θ(h_n)(1)` — the family the singleton clause already constrains — with no new datum.
  `HJO.Mellit.theta_completeHomog_one_apply_elemSymmComp` and
  `HJO.Mellit.theta_completeHomog_two_smul_apply_elemSymmComp` are the fully written-out forms at an
  `e`-monomial, and `HJO.Mellit.theta_completeHomog_one_apply_sum_elemSymmComp` the form that reads
  an arbitrary expansion.

### The creation side at two infinite families of compositions

* `HJO.Mellit.theta_copComp_pair_one_apply_one_qop` — at every `[A, 1]`:

    `Θ(C_{[A,1]}1)(1) = (-q)^{1-A} ( -Q_{2,3}(Θ(h_A)(1)) + (q^{-1}-1) Θ(h_{A+1})(1) )`.

* `HJO.Mellit.theta_copComp_pair_two_apply_one_qop` — at every `[A, 2]`, with `1 + qu` cleared onto
  the left.

  So the creation side is now evaluated at every two-part composition whose **inner** part is at
  most `2`, in terms of the one-part values alone. Beyond the four compositions decided elsewhere
  (`[1]`, `[2]`, `[1,1]`, and the singleton family's equivalence) these are two infinite
  families.

* `HJO.Mellit.theta_copComp_one_one_apply_one_of_pair_one` — **the third and strongest consistency
  check.** The general `[A,1]` formula at `A = 1`, with both operator values substituted and
  `1 + qu` cleared, is `HJO.Mellit.theta_copComp_one_one_apply_one_of_pair` statement for statement,
  and `HJO.Mellit.theta_copComp_one_one_apply_one_of_pair_one_eq` checks that by `rfl`. That
  statement re-proves `HJO.Mellit.lhsAt_two_three_one_one` through
  `HJO.Mellit.lhsAt_two_three_one_one_of_pair`, so the decided clause is reached **through** this
  file's general formula.

## What remains open, and the quantifier

* **`Θ(h_m)(Θ(h_n)(1))` for `m ≥ 3` and `n ≥ 3`** is not evaluated. What is missing is not machinery
  but the expansion of `h_m` on the axis generators for `m ≥ 3`:
  `HJO.Mellit.theta_completeHomog_smul_eq_sum_qop` gives it as a recursion whose terms are
  `Θ(h_{m-s})Q_{2s,3s}`, and each `Q_{2s,3s}` is `M⁻¹(L_{s-1}D_1 - D_1L_{s-1})` — a combination of
  `D`-words of length `2s`, which `HJO.Sym.dopPushMono` evaluates. So every instance is computable;
  what is **not** proved here is a single statement covering all `m` at once, and there is no closed
  form to be had, the `h_m`-to-axis expansion having one monomial per partition of `m`.

* **The number of terms** in `HJO.Sym.dopPushMono q u w l` is not part of any statement. It is
  `∏` over the rounds of one factor per surviving elementary factor, hand arithmetic, not a theorem.

* **The `e`-monomials span `Λ`**, so `HJO.Mellit.theta_completeHomog_one_apply_sum_elemSymmComp`
  applies to every argument — but the bridge is not formalized here.
  `HJO.Sym.mem_span_elemSymmMonomial_rowLens` is the spanning statement, indexed by
  **multisets** of row lengths of a partition, and connecting it to this file's **list**-indexed
  `HJO.Sym.elemSymmComp` (plus the homogeneity of `Θ(h_n)(1)`) is not done. So "at every element of
  `Λ`" is proved here only in the form "given an expansion in `e`-monomials".

* **The sweep side** at length `≥ 2` is untouched. Nothing here compares the two recursions, and the
  clause at `[A,1]` or `[A,2]` is therefore not decided — only its creation side is computed.

## Genericity

`HJO.Sym.dopShiftSum`, `HJO.Sym.dopPushMono` and every statement about them:
**no hypothesis on `q` or `u`.** `HJO.Bglx.paramPleth` is a polynomial in `q, u` and the signs are
integers, so nothing is inverted and nothing degenerates.

The `Q`-statements (`HJO.Sym.qop_two_three_apply_elemSymmComp`,
`HJO.Sym.qop_two_three_sq_apply_elemSymmComp`, `HJO.Sym.qop_four_six_apply_elemSymmComp`): also
**unconditional**, because `HJO.Sym.Qop`'s own `M⁻¹ = ((1-q)(1-u))⁻¹` is *carried in the statement*
rather than cleared. At `M = 0` both sides are the zero element — the totalisation, not a claim.
Only
`HJO.Sym.qop_two_three_apply_elemSymm_one_of_pushMono`, which solves for the value, spends `M ≠ 0`,
and it spends it exactly once, on `M⁻¹M = 1`; so it also carries `q ≠ 1` and `u ≠ 1`.

`HJO.Mellit.theta_completeHomog_mul_apply_one`, `HJO.Mellit.theta_completeHomog_apply_one_comm`,
`HJO.Mellit.theta_copComp_pair_one_apply_one`, `HJO.Mellit.theta_copComp_pair_two_apply_one`:
**no hypothesis at all**, and `Θ` is not asked to be a slope homomorphism.
`HJO.CreationSeeds.dispCoeff`'s spelling `c_j = q^{-j} - q^{-(j-1)}` is a totalisation at `q = 0` on
both sides; the algebraically equal `(1-q)q^{-j}` would be **false** there, not vacuous.

Every statement mentioning a slope homomorphism carries `qu ≠ 0` and `qu ≠ 1`, which are
`HJO.Sym.axisGen_one`'s: `HJO.Sym.axisGen` normalises by `v/(v-1)` with `v = qu`, and in a field
`0⁻¹ = 0`, so at `v ∈ {0,1}` every `U_k` is the zero element (`HJO.Sym.axisGen_eq_zero`) and the
prescription pins nothing — there the statements would be false, not vacuous. `qu ≠ 0` gives `q ≠ 0`
and `u ≠ 0`.

The scalar `1 + qu` is carried on the left in every `h_2` statement and never inverted, so `qu = -1`
is **not** excluded; there those statements read `0 = 0`, which is exactly where `U_1, U_2` fail to
span `h_2`. `q ≠ 0` appears in one place only, the consistency check
`HJO.Mellit.theta_copComp_one_one_apply_one_of_pair_one`, for `q^{-1}q = 1`; it belongs to the route
and the statement it proves does not carry it.

## References

The objects involved are `HJO.Sym.DopInt`, `HJO.Sym.Qop`, `HJO.Sym.elemSymm`, `HJO.Sym.axisGen`,
`HJO.Sym.IsSlopeHom`, `HJO.Sym.completeHomog`,
`HJO.Sym.CopComp`, `HJO.Sym.dop_elemSymm_one_mul`, `HJO.Sym.coprime_ladder`,
`HJO.Mellit.lhsRewrite_sweepWitness`.
-/

@[expose] public section

namespace HJO.Sym

open HJO.Bglx Finset

variable {L : Type*} [Field L] [Algebra ℚ L]

/-! ### `D`-words as lists -/

/-- Concatenating index lists composes the `D`-words. -/
theorem dopList_append (q u : L) (l₁ l₂ : List ℕ) :
    dopList q u (l₁ ++ l₂) = dopList q u l₁ * dopList q u l₂ := by
  rw [dopList, dopList, dopList, List.map_append, List.prod_append]

/-- A one-letter word is the basic operator. -/
theorem dopList_singleton (q u : L) (k : ℕ) : dopList q u [k] = Dop q u k := by
  rw [dopList_cons, dopList_nil, mul_one]

/-- A two-letter word, leftmost letter applied last. -/
theorem dopList_pair (q u : L) (a b : ℕ) :
    dopList q u [a, b] = Dop q u a * Dop q u b := by
  rw [dopList_cons, dopList_singleton]

/-- Reversing a cons peels the letter off on the **right**, i.e. off the end that acts first. -/
theorem dopList_reverse_cons (q u : L) (k : ℕ) (w : List ℕ) :
    dopList q u (k :: w).reverse = dopList q u w.reverse * Dop q u k := by
  rw [List.reverse_cons, dopList_append, dopList_singleton]

/-! ### The shift sum of one basic operator past an `e`-monomial -/

/-- **The shift sum.** `dopShiftSum q u cont l j` is the sum over shift vectors `s` of the
`e`-monomial `l = (n_1, …, n_p)` — one `s_i ≤ n_i` per factor, taken in turn — of
`(∏_i κ(e_{s_i})) • cont (n_1 - s_1, …, n_p - s_p) (j + ∑_i s_i)`.

It is the bookkeeping of `HJO.Sym.dop_elemSymm_mul` iterated over the factors of a monomial: each
factor `e_{n_i}` donates `s_i` to the index of the basic operator and keeps `e_{n_i - s_i}`. The
continuation receives the shortened monomial and the accumulated index, which is what lets the
result be used both to expand a single basic operator (`HJO.Sym.dop_apply_elemSymmComp`) and to
carry a whole word (`HJO.Sym.dopPushMono`).

Unconditional in `q` and `u`; `κ = HJO.Bglx.paramPleth`. -/
noncomputable def dopShiftSum (q u : L) (cont : List ℕ → ℕ → Lambda L) :
    List ℕ → ℕ → Lambda L
  | [], j => cont [] j
  | n :: l, j => ∑ s ∈ range (n + 1), paramPleth q u (elemSymm L s) •
      dopShiftSum q u (fun m i => cont ((n - s) :: m) i) l (j + s)

/-- The shift sum at the empty monomial is the continuation. -/
theorem dopShiftSum_nil (q u : L) (cont : List ℕ → ℕ → Lambda L) (j : ℕ) :
    dopShiftSum q u cont [] j = cont [] j := rfl

/-- The shift sum peels the first factor of the monomial. -/
theorem dopShiftSum_cons (q u : L) (cont : List ℕ → ℕ → Lambda L) (n : ℕ) (l : List ℕ) (j : ℕ) :
    dopShiftSum q u cont (n :: l) j
      = ∑ s ∈ range (n + 1), paramPleth q u (elemSymm L s) •
          dopShiftSum q u (fun m i => cont ((n - s) :: m) i) l (j + s) := rfl

/-- **One basic operator at an `e`-monomial, under any linear map, expanded.**

For every `T : End_L(Λ)`, every `e`-monomial `e_l` and every `j`,

  `T (D_j (e_l)) = ∑_s (∏ κ(e_{s_i})) • (-1)^{j+∑s} • T (e_{l - s} e_{j + ∑ s})`,

the sum being `HJO.Sym.dopShiftSum`'s. The `T` is carried because the induction on the factors of
the monomial consumes them one at a time: after peeling `e_{n_1}` the leftover `e_{n_1-s_1}` has to
be pushed *through* whatever acts on the outside, and `T ↦ T ∘ (e_{n_1-s_1} ·)` is exactly that.
Taking `T = 1` gives `HJO.Sym.dop_apply_elemSymmComp`; taking `T` a `D`-word gives
`HJO.Sym.dopList_reverse_apply_elemSymmComp`.

Unconditional in `q` and `u`, at every `j` and every monomial. -/
theorem dop_apply_elemSymmComp_of_linear (q u : L) (T : Module.End L (Lambda L)) :
    ∀ (l : List ℕ) (j : ℕ), T (Dop q u j (elemSymmComp L l))
      = dopShiftSum q u (fun m i => ((-1 : L) ^ i) • T (elemSymmComp L (m ++ [i]))) l j := by
  intro l
  induction l generalizing T with
  | nil =>
    intro j
    rw [dopShiftSum_nil, elemSymmComp_nil, dop_apply_one_smul, map_smul]
    simp only [List.nil_append, elemSymmComp_cons, elemSymmComp_nil, mul_one]
  | cons n l ih =>
    intro j
    rw [elemSymmComp_cons, dop_elemSymm_mul, map_sum, dopShiftSum_cons]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [map_smul]
    congr 1
    have key := ih (T * LinearMap.mulLeft L (elemSymm L (n - s))) (j + s)
    simp only [Module.End.mul_apply, LinearMap.mulLeft_apply] at key
    rw [key]
    congr 1

/-- **One basic operator at every `e`-monomial, expanded**:
`HJO.Sym.dop_apply_elemSymmComp_of_linear` at `T = 1`. Unconditional in `q` and `u`, at every index
and every monomial; the previous explicit expansion (`HJO.Sym.dop_elemSymm_mul`) covered a
**single** elementary factor times an opaque `f`. -/
theorem dop_apply_elemSymmComp (q u : L) (l : List ℕ) (j : ℕ) :
    Dop q u j (elemSymmComp L l)
      = dopShiftSum q u (fun m i => ((-1 : L) ^ i) • elemSymmComp L (m ++ [i])) l j := by
  have h := dop_apply_elemSymmComp_of_linear q u (1 : Module.End L (Lambda L)) l j
  simpa only [Module.End.one_apply] using h

/-! ### `D`-words of every length at every `e`-monomial -/

/-- **The expansion of a `D`-word at an `e`-monomial.** `dopPushMono q u w l` is the value of the
word `w = (k_1, …, k_ℓ)` — **read in application order**, `D_{k_1}` acting first — at the
`e`-monomial `e_l`, written out as a combination of `e`-monomials.

Each letter contributes one round of `HJO.Sym.dopShiftSum`: it shifts every surviving elementary
factor down, collects the donated indices into its own, and appends the resulting `e_{k+∑s}` to the
monomial. So a word of length `ℓ` at a monomial of `p` factors produces monomials of `p + ℓ`
factors, and the sum has `∏` (one factor per (letter, elementary factor) pair) terms — the
`ℓ`-fold sum, indexed by lists of bounded sum.

Unconditional in `q` and `u`, at every length. -/
noncomputable def dopPushMono (q u : L) : List ℕ → List ℕ → Lambda L
  | [], l => elemSymmComp L l
  | k :: w, l =>
      dopShiftSum q u (fun m i => ((-1 : L) ^ i) • dopPushMono q u w (m ++ [i])) l k

/-- The empty word is the identity. -/
theorem dopPushMono_nil (q u : L) (l : List ℕ) :
    dopPushMono q u [] l = elemSymmComp L l := rfl

/-- One more letter acts by one round of the shift sum. -/
theorem dopPushMono_cons (q u : L) (k : ℕ) (w l : List ℕ) :
    dopPushMono q u (k :: w) l
      = dopShiftSum q u (fun m i => ((-1 : L) ^ i) • dopPushMono q u w (m ++ [i])) l k := rfl

/-- **Every `D`-word at every `e`-monomial, explicitly.**

`D_{k_ℓ}(⋯ D_{k_1}(e_l) ⋯) = dopPushMono q u [k_1, …, k_ℓ] l`, the word being listed in application
order on the right and outermost-first on the left (`HJO.Sym.dopList` puts the leftmost letter
outermost, so the two orders differ by a reversal and nothing else).

This is the `ℓ`-fold straightening sum. Without it, explicit expansion is available for `D`-words
of length **two** only, and only at a single elementary factor; here the length and the number of
elementary factors are both arbitrary, and the right-hand side is a closed recursive expression in
`κ`, signs and elementary symmetric functions with nothing left to evaluate.

Unconditional in `q` and `u`. -/
theorem dopList_reverse_apply_elemSymmComp (q u : L) :
    ∀ (w l : List ℕ), dopList q u w.reverse (elemSymmComp L l) = dopPushMono q u w l := by
  intro w
  induction w with
  | nil => intro l; rw [List.reverse_nil, dopList_nil, dopPushMono_nil, Module.End.one_apply]
  | cons k w ih =>
    intro l
    rw [dopList_reverse_cons, Module.End.mul_apply, dop_apply_elemSymmComp_of_linear,
      dopPushMono_cons]
    congr 1
    funext m i
    rw [ih]

/-- **Every `D`-word at the vacuum, explicitly** — `HJO.Sym.dopList_reverse_apply_elemSymmComp` at
the empty monomial, `e_∅ = 1`. Unconditional in `q` and `u`, at every length. -/
theorem dopList_reverse_apply_one (q u : L) (w : List ℕ) :
    dopList q u w.reverse (1 : Lambda L) = dopPushMono q u w [] := by
  rw [← dopList_reverse_apply_elemSymmComp q u w [], elemSymmComp_nil]

/-! ### Consistency check: the two-letter vacuum values, through the general expansion -/

/-- **The general expansion reproduces `HJO.Sym.dop_dop_apply_one`** at every pair `(a, b)`:

`D_aD_b(1) = ∑_{r≤b} (-1)^{a+b+r} κ(e_r) · e_{b-r}e_{a+r}`.

Run through `HJO.Sym.dopList_reverse_apply_one` at the word `[b, a]` — application order, so `D_b`
first — the two rounds of the shift sum give the `b`-indexed sum, the sign `(-1)^{a+b+r}` as the
product of the two rounds' signs, and the second factor's index as `a + r`. That statement is
proved from one Pieri rule on `HJO.Sym.DopInt` at the vacuum and shares no step with this route, so
the agreement pins the sign convention, the direction of the shift and the order of the two letters.

`HJO.Sym.dop_dop_apply_one_of_pushMono_eq` checks by `rfl` that the two propositions are literally
the same. Unconditional in `q` and `u`. -/
theorem dop_dop_apply_one_of_pushMono (q u : L) (a b : ℕ) :
    Dop q u a (Dop q u b 1)
      = ∑ r ∈ range (b + 1), ((-1 : L) ^ (a + b + r) * paramPleth q u (elemSymm L r)) •
          (elemSymm L (b - r) * elemSymm L (a + r)) := by
  have h := dopList_reverse_apply_one q u [b, a]
  rw [show ([b, a] : List ℕ).reverse = [a, b] from rfl, dopList_pair, Module.End.mul_apply] at h
  rw [h, dopPushMono_cons, dopShiftSum_nil]
  simp only [List.nil_append, dopPushMono_cons, dopShiftSum_cons, dopShiftSum_nil,
    dopPushMono_nil, List.cons_append, elemSymmComp_cons, elemSymmComp_nil, mul_one,
    Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun r _ => ?_
  congr 1
  rw [show a + b + r = b + (a + r) from by omega, pow_add]
  ring

/-- **The two routes to `D_aD_b(1)` state the same proposition.** `rfl` between the proofs
typechecks only if the statements are identical, which rules out an absorbed sign, a transposed
index or a re-associated product. -/
theorem dop_dop_apply_one_of_pushMono_eq (q u : L) (a b : ℕ) :
    dop_dop_apply_one_of_pushMono q u a b = dop_dop_apply_one (L := L) q u a b := rfl

/-- A four-letter word, leftmost letter applied last. -/
theorem dopList_quad (q u : L) (a b c d : ℕ) :
    dopList q u [a, b, c, d] = Dop q u a * (Dop q u b * (Dop q u c * Dop q u d)) := by
  rw [dopList_cons, dopList_cons, dopList_pair]

/-- A three-letter word, leftmost letter applied last. -/
theorem dopList_triple (q u : L) (a b c : ℕ) :
    dopList q u [a, b, c] = Dop q u a * (Dop q u b * Dop q u c) := by
  rw [dopList_cons, dopList_pair]

/-- `HJO.Sym.dopList_reverse_apply_elemSymmComp` with the word in `HJO.Sym.dopList`'s own order:
the expansion is indexed by the **reversed** list, since `dopList` puts the leftmost letter
outermost while `HJO.Sym.dopPushMono` consumes letters in application order. -/
theorem dopList_apply_elemSymmComp (q u : L) (w l : List ℕ) :
    dopList q u w (elemSymmComp L l) = dopPushMono q u w.reverse l := by
  rw [← dopList_reverse_apply_elemSymmComp q u w.reverse l, List.reverse_reverse]

/-! ### `Q_{2,3}` at every `e`-monomial -/

/-- **`Q_{2,3}` at every `e`-monomial, explicitly.**

`HJO.Sym.Qop` at the coprime slope `(2,3)` is the normalised bracket `M⁻¹(D_2D_1 - D_1D_2)`
(`HJO.Sym.qop_two_three_eq_bracket_dop`), and each half is a two-letter `D`-word, so
`HJO.Sym.dopList_reverse_apply_elemSymmComp` evaluates both at every `e`-monomial. The two words are
listed in application order, which is why they read `[1,2]` and `[2,1]` rather than `[2,1]` and
`[1,2]`.

Unconditional in `q` and `u`: `HJO.Sym.Qop`'s own `M⁻¹` is carried in the statement, so at `M = 0`
both sides are zero and nothing is claimed. -/
theorem qop_two_three_apply_elemSymmComp (q u : L) (l : List ℕ) :
    Qop q u 2 3 (elemSymmComp L l)
      = ((1 - q) * (1 - u))⁻¹ • (dopPushMono q u [1, 2] l - dopPushMono q u [2, 1] l) := by
  have h1 : (Dop q u 2 * Dop q u 1) (elemSymmComp L l) = dopPushMono q u [1, 2] l := by
    rw [← dopList_pair, show ([2, 1] : List ℕ) = ([1, 2] : List ℕ).reverse from rfl,
      dopList_reverse_apply_elemSymmComp]
  have h2 : (Dop q u 1 * Dop q u 2) (elemSymmComp L l) = dopPushMono q u [2, 1] l := by
    rw [← dopList_pair, show ([1, 2] : List ℕ) = ([2, 1] : List ℕ).reverse from rfl,
      dopList_reverse_apply_elemSymmComp]
  rw [qop_two_three_eq_bracket_dop]
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, h1, h2]

/-- **Consistency check off the vacuum: the general expansion reproduces `Q_{2,3}(e_1)`.**

Word for word the right-hand side of `HJO.Sym.qop_two_three_apply_elemSymm_pin`, which three other
routes already agree on (the direct commutator grind of `HJO.Sym.qop_two_three_apply_elemSymm_one`,
the shift step of `HJO.Sym.qop_two_three_apply_elemSymm_one_pin`, and the two-letter
straightening of `HJO.Sym.qop_two_three_apply_elemSymm`), obtained here from
`HJO.Sym.qop_two_three_apply_elemSymmComp` — i.e. from the general `ℓ`-fold expansion at a word of
length two and a monomial of one factor. All four coefficients agree, including the `e_4` one, so
the check pins the sign, both index shifts and the order of the bracket.

`M ≠ 0` is spent exactly once, on `M⁻¹M = 1`, as in `HJO.Sym.qop_two_three_apply_elemSymm_pin`. -/
theorem qop_two_three_apply_elemSymm_one_of_pushMono (q u : L) (hM : (1 - q) * (1 - u) ≠ 0) :
    Qop q u 2 3 (elemSymm L 1)
      = -(elemSymm L 1 * elemSymm L 1 * elemSymm L 2)
        + ((1 - q) * (1 - u)) • (elemSymm L 2 * elemSymm L 2)
        + (1 - q - u + (q + u) * ((1 - q) * (1 - u))) • (elemSymm L 1 * elemSymm L 3)
        + ((q ^ 2 + q * u + u ^ 2 - 1) * ((1 - q) * (1 - u))) • elemSymm L 4 := by
  have hl : elemSymmComp L [1] = elemSymm L 1 := by
    rw [elemSymmComp_cons, elemSymmComp_nil, mul_one]
  have h := qop_two_three_apply_elemSymmComp q u (L := L) [1]
  rw [hl] at h
  rw [h]
  refine (inv_smul_eq_iff₀ hM).2 ?_
  norm_num only [dopPushMono_cons, dopShiftSum_cons, dopShiftSum_nil, dopPushMono_nil,
    List.cons_append, List.nil_append, elemSymmComp_cons, elemSymmComp_nil, mul_one,
    Finset.sum_range_succ, Finset.sum_range_zero, zero_add, paramPleth_elemSymm_zero,
    paramPleth_elemSymm_one_eq, paramPleth_elemSymm_two_eq, paramPleth_elemSymm_three_eq,
    elemSymm_zero, one_smul, one_mul]
  simp only [MvPolynomial.smul_eq_C_mul, map_sub, map_add, map_mul, map_neg, map_one, map_pow]
  ring

/-- **The two routes to `Q_{2,3}(e_1)` state the same proposition**, checked by `rfl` between the
proofs rather than by comparing printed coefficients. -/
theorem qop_two_three_apply_elemSymm_one_of_pushMono_eq (q u : L)
    (hM : (1 - q) * (1 - u) ≠ 0) :
    qop_two_three_apply_elemSymm_one_of_pushMono (L := L) q u hM
      = qop_two_three_apply_elemSymm_pin q u hM := rfl

/-! ### The doubled slope: `Q_{2,3}^2` and `Q_{4,6}` at every `e`-monomial -/

/-- **`Q_{2,3}^2` at every `e`-monomial, explicitly.** Squaring the bracket
`Q_{2,3} = M⁻¹(D_2D_1 - D_1D_2)` gives four `D`-words of length **four**, and
`HJO.Sym.dopList_reverse_apply_elemSymmComp` evaluates each at every `e`-monomial. This is where the
general `ℓ`-fold expansion pays: nothing here is specific to the length.

Unconditional in `q` and `u`, the two factors of `M⁻¹` being carried. -/
theorem qop_two_three_sq_apply_elemSymmComp (q u : L) (l : List ℕ) :
    Qop q u 2 3 (Qop q u 2 3 (elemSymmComp L l))
      = (((1 - q) * (1 - u))⁻¹ * ((1 - q) * (1 - u))⁻¹) •
          (dopPushMono q u [1, 2, 1, 2] l - dopPushMono q u [2, 1, 1, 2] l
            - dopPushMono q u [1, 2, 2, 1] l + dopPushMono q u [2, 1, 2, 1] l) := by
  have hop : Qop q u 2 3 * Qop q u 2 3
      = (((1 - q) * (1 - u))⁻¹ * ((1 - q) * (1 - u))⁻¹) •
          (dopList q u [2, 1, 2, 1] - dopList q u [2, 1, 1, 2]
            - dopList q u [1, 2, 2, 1] + dopList q u [1, 2, 1, 2]) := by
    rw [qop_two_three_eq_bracket_dop, smul_mul_assoc, mul_smul_comm, smul_smul]
    congr 1
    simp only [dopList_quad]
    noncomm_ring
  have h := congrArg (fun T : Module.End L (Lambda L) => T (elemSymmComp L l)) hop
  simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.add_apply,
    dopList_apply_elemSymmComp] at h
  rw [h]
  norm_num only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]

/-- **`Q_{4,6}` at every `e`-monomial, explicitly** — the operator at the **doubled** slope, which
is what `h_2` reads and the clause at a one-part composition of size one never mentions.

`HJO.Sym.qop_two_three_axis_eq_ladder` at `k = 2` gives `Q_{4,6} = M⁻¹(L_1D_1 - D_1L_1)` with
`L_1 = M⁻¹(D_2Q_{2,3} - Q_{2,3}D_2)`, so unwinding both brackets gives `M⁻³` times a combination of
`D`-words of length four, in which the two `D_1D_2D_2D_1` terms cancel outright and only four words
survive:

  `M^3 Q_{4,6} = D_2D_2D_1D_1 - 2 D_2D_1D_2D_1 + 2 D_1D_2D_1D_2 - D_1D_1D_2D_2`.

Unconditional in `q` and `u`: the three factors of `M⁻¹` are carried on the right and never cleared,
so at `M = 0` both sides are zero. -/
theorem qop_four_six_apply_elemSymmComp (q u : L) (l : List ℕ) :
    Qop q u 4 6 (elemSymmComp L l)
      = (((1 - q) * (1 - u))⁻¹ * ((1 - q) * (1 - u))⁻¹ * ((1 - q) * (1 - u))⁻¹) •
          (dopPushMono q u [1, 1, 2, 2] l
            - dopPushMono q u [1, 2, 1, 2] l - dopPushMono q u [1, 2, 1, 2] l
            + dopPushMono q u [2, 1, 2, 1] l + dopPushMono q u [2, 1, 2, 1] l
            - dopPushMono q u [2, 2, 1, 1] l) := by
  have hL : ladderTwoThree q u (Dop q u 2)
      = (((1 - q) * (1 - u))⁻¹ * ((1 - q) * (1 - u))⁻¹) •
          (dopList q u [2, 2, 1] - dopList q u [2, 1, 2] - dopList q u [2, 1, 2]
            + dopList q u [1, 2, 2]) := by
    rw [ladderTwoThree_apply, qop_two_three_eq_bracket_dop, mul_smul_comm, smul_mul_assoc,
      ← smul_sub, smul_smul]
    congr 1
    simp only [dopList_triple]
    noncomm_ring
  have hcore : (dopList q u [2, 2, 1] - dopList q u [2, 1, 2] - dopList q u [2, 1, 2]
        + dopList q u [1, 2, 2]) * Dop q u 1
      - Dop q u 1 * (dopList q u [2, 2, 1] - dopList q u [2, 1, 2] - dopList q u [2, 1, 2]
        + dopList q u [1, 2, 2])
      = dopList q u [2, 2, 1, 1] - dopList q u [2, 1, 2, 1] - dopList q u [2, 1, 2, 1]
        + dopList q u [1, 2, 1, 2] + dopList q u [1, 2, 1, 2] - dopList q u [1, 1, 2, 2] := by
    simp only [dopList_triple, dopList_quad]
    noncomm_ring
  have hword : ((1 - q) * (1 - u))⁻¹ •
      (ladderTwoThree q u (Dop q u 2) * Dop q u 1 -
        Dop q u 1 * ladderTwoThree q u (Dop q u 2))
      = (((1 - q) * (1 - u))⁻¹ * ((1 - q) * (1 - u))⁻¹ * ((1 - q) * (1 - u))⁻¹) •
          (dopList q u [2, 2, 1, 1] - dopList q u [2, 1, 2, 1] - dopList q u [2, 1, 2, 1]
            + dopList q u [1, 2, 1, 2] + dopList q u [1, 2, 1, 2]
            - dopList q u [1, 1, 2, 2]) := by
    rw [hL, smul_mul_assoc, mul_smul_comm, ← smul_sub, smul_smul,
      show ((1 - q) * (1 - u))⁻¹ * (((1 - q) * (1 - u))⁻¹ * ((1 - q) * (1 - u))⁻¹)
        = ((1 - q) * (1 - u))⁻¹ * ((1 - q) * (1 - u))⁻¹ * ((1 - q) * (1 - u))⁻¹ from
        (mul_assoc _ _ _).symm, hcore]
  have hop : Qop q u 4 6
      = (((1 - q) * (1 - u))⁻¹ * ((1 - q) * (1 - u))⁻¹ * ((1 - q) * (1 - u))⁻¹) •
          (dopList q u [2, 2, 1, 1] - dopList q u [2, 1, 2, 1] - dopList q u [2, 1, 2, 1]
            + dopList q u [1, 2, 1, 2] + dopList q u [1, 2, 1, 2]
            - dopList q u [1, 1, 2, 2]) := by
    refine Eq.trans ?_ hword
    have h := qop_two_three_axis_eq_ladder q u (k := 2) (by omega)
    rw [show 2 * 2 = 4 from rfl, show 3 * 2 = 6 from rfl, show 2 - 1 = 1 from rfl,
      Function.iterate_one] at h
    exact h
  have h := congrArg (fun T : Module.End L (Lambda L) => T (elemSymmComp L l)) hop
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.add_apply,
    dopList_apply_elemSymmComp, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append] at h
  exact h

end HJO.Sym

namespace HJO.Mellit

open HJO.Sym HJO.Bglx HJO.CreationSeeds Finset

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-! ### The two-index family is a one-index family -/

/-- **`Θ(h_m)(Θ(h_n)(1)) = Θ(h_m h_n)(1)`.**

The datum blocking the creation side of the `hlhs` clause at length `≥ 2`
(`HJO.Mellit.theta_copComp_pair_apply_one`) is the nested value `Θ(h_m)(Θ(h_n)(1))`, one
`h`-operator at the **non-vacuum** element `Θ(h_n)(1)`. Because `Θ` is an algebra homomorphism into
the endomorphisms, the composite of the two operators is the operator of the product, so the nesting
is only apparent: the two-index family is the value of `Θ` at the `h`-monomial `h_mh_n`, at the
vacuum.

**No hypothesis at all** — not on `q`, not on `u`, and `Θ` is not asked to be a slope
homomorphism. -/
theorem theta_completeHomog_mul_apply_one (Θ : Lambda L →ₐ[L] Module.End L (Lambda L)) (m n : ℕ) :
    Θ (completeHomog L m) (Θ (completeHomog L n) 1)
      = Θ (completeHomog L m * completeHomog L n) 1 := by
  rw [map_mul, Module.End.mul_apply]

/-- **The two-index family is symmetric**: `Θ(h_m)(Θ(h_n)(1)) = Θ(h_n)(Θ(h_m)(1))`, because `Λ` is
commutative and `Θ` is multiplicative. So half the family is redundant, and in
`HJO.Mellit.theta_copComp_pair_apply_one` the outer index `B - j` and the inner index `A + j` may be
exchanged term by term. No hypothesis. -/
theorem theta_completeHomog_apply_one_comm (Θ : Lambda L →ₐ[L] Module.End L (Lambda L)) (m n : ℕ) :
    Θ (completeHomog L m) (Θ (completeHomog L n) 1)
      = Θ (completeHomog L n) (Θ (completeHomog L m) 1) := by
  rw [theta_completeHomog_mul_apply_one, theta_completeHomog_mul_apply_one, mul_comm]

/-- **The `m = 1` row of the two-index family, at every `n`.**
`Θ(h_1)(Θ(h_n)(1)) = -Q_{2,3}(Θ(h_n)(1))` for every `n`: the outer operator of the nested value is
the single explicit operator `Q_{2,3}`, which
`HJO.Mellit.theta_completeHomog_one_apply_sum_elemSymmComp` evaluates at an arbitrary argument. So
this row of the family costs nothing beyond the one-part values. Genericity: `qu ≠ 0`, `qu ≠ 1`. -/
theorem theta_completeHomog_one_apply_theta_apply_one (hv0 : q * u ≠ 0) (hv1 : q * u ≠ 1)
    {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)} (hΘ : IsSlopeHom 2 3 q u Θ) (n : ℕ) :
    Θ (completeHomog L 1) (Θ (completeHomog L n) 1)
      = -Qop q u 2 3 (Θ (completeHomog L n) 1) := by
  rw [theta_completeHomog_one hΘ hv0 hv1, LinearMap.neg_apply]

/-- **The `m = 2` row of the two-index family, at every `n`.**

`(1+qu) Θ(h_2)(Θ(h_n)(1)) = qu (Q_{2,3}^2 - Q_{4,6})(Θ(h_n)(1))` for every `n`, both operators being
evaluated at an arbitrary `e`-monomial by `HJO.Sym.qop_two_three_sq_apply_elemSymmComp` and
`HJO.Sym.qop_four_six_apply_elemSymmComp`.

With the previous lemma this is the two-index family `Θ(h_m)(Θ(h_n)(1))` for **`m ≤ 2` and every
`n`** — and by `HJO.Mellit.theta_completeHomog_apply_one_comm` also for every `m` with `n ≤ 2`. The
scalar `1 + qu` is carried on the left. Genericity: `qu ≠ 0`, `qu ≠ 1`. -/
theorem theta_completeHomog_two_smul_apply_theta_apply_one (hv0 : q * u ≠ 0) (hv1 : q * u ≠ 1)
    {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)} (hΘ : IsSlopeHom 2 3 q u Θ) (n : ℕ) :
    (q * u + 1) • Θ (completeHomog L 2) (Θ (completeHomog L n) 1)
      = (q * u) • (Qop q u 2 3 (Qop q u 2 3 (Θ (completeHomog L n) 1))
          - Qop q u 4 6 (Θ (completeHomog L n) 1)) := by
  have h := congrArg (fun T : Module.End L (Lambda L) => T (Θ (completeHomog L n) 1))
    (theta_completeHomog_two_smul hΘ hv0 hv1)
  simpa only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.mul_apply] using h

/-! ### `Θ(h_1)` at every `e`-monomial, and hence at every element of `Λ` -/

/-- **`Θ(h_1)` at every `e`-monomial, explicitly.** `Θ(h_1) = -Q_{2,3}`
(`HJO.Mellit.theta_completeHomog_one`), and `HJO.Sym.qop_two_three_apply_elemSymmComp` evaluates
`Q_{2,3}` at every `e`-monomial. Genericity: `qu ≠ 0` and `qu ≠ 1`, `HJO.Sym.axisGen_one`'s — at
`qu ∈ {0,1}` every axis generator is the zero element and the prescription pins nothing. `M⁻¹` is
carried, not inverted, so `M = 0` is not excluded. -/
theorem theta_completeHomog_one_apply_elemSymmComp (hv0 : q * u ≠ 0) (hv1 : q * u ≠ 1)
    {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)} (hΘ : IsSlopeHom 2 3 q u Θ) (l : List ℕ) :
    Θ (completeHomog L 1) (elemSymmComp L l)
      = -(((1 - q) * (1 - u))⁻¹ • (dopPushMono q u [1, 2] l - dopPushMono q u [2, 1] l)) := by
  rw [theta_completeHomog_one hΘ hv0 hv1, LinearMap.neg_apply, qop_two_three_apply_elemSymmComp]

/-- **`Θ(h_1)` at every element of `Λ`, explicitly**, the `e`-monomials being a spanning set: given
any expansion `x = ∑ c_i e_{μ_i}`, the value is the matching combination of the explicit expansions.
This is the form the two-index family needs, since `Θ(h_n)(1)` is produced by
`HJO.Mellit.theta_completeHomog_apply_one_smul_eq_sum_qop` as such a combination and never as a
single monomial. Genericity: `qu ≠ 0`, `qu ≠ 1`. -/
theorem theta_completeHomog_one_apply_sum_elemSymmComp (hv0 : q * u ≠ 0) (hv1 : q * u ≠ 1)
    {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)} (hΘ : IsSlopeHom 2 3 q u Θ) {ι : Type*}
    (s : Finset ι) (c : ι → L) (μ : ι → List ℕ) :
    Θ (completeHomog L 1) (∑ i ∈ s, c i • elemSymmComp L (μ i))
      = ∑ i ∈ s, c i • -(((1 - q) * (1 - u))⁻¹ •
          (dopPushMono q u [1, 2] (μ i) - dopPushMono q u [2, 1] (μ i))) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [map_smul, theta_completeHomog_one_apply_elemSymmComp hv0 hv1 hΘ]

/-! ### The creation side at every two-part composition with inner part one -/

/-- **The creation side of the `hlhs` clause at every composition `[A, 1]`.**

`HJO.Mellit.theta_copComp_pair_apply_one` at `B = 1` has two terms, and `h_0 = 1` makes the second
one a **vacuum** value:

  `Θ(C_{[A,1]}1)(1) = (-q)^{1-A} ( Θ(h_1)(Θ(h_A)(1)) + c_1 · Θ(h_{A+1})(1) )`,  `c_1 = q^{-1}-1`.

So the whole creation side at this infinite family is the one-part family `{Θ(h_n)(1)}` plus the
single nested value `Θ(h_1)(Θ(h_A)(1))` — and that one is `-Q_{2,3}` at `Θ(h_A)(1)`, evaluated by
`HJO.Mellit.theta_completeHomog_one_apply_sum_elemSymmComp`.

**No hypothesis at all**, `HJO.CreationSeeds.dispCoeff`'s spelling `c_j = q^{-j} - q^{-(j-1)}` being
a totalisation at `q = 0` on both sides; the algebraically equal `(1-q)q^{-j}` would be false
there. -/
theorem theta_copComp_pair_one_apply_one (Θ : Lambda L →ₐ[L] Module.End L (Lambda L)) (q : L)
    (A : ℕ) :
    Θ (CopComp q [A, 1] (1 : Lambda L)) 1
      = ((-q) ^ (1 - (A : ℤ))) •
          (Θ (completeHomog L 1) (Θ (completeHomog L A) 1)
            + dispCoeff q 1 • Θ (completeHomog L (A + 1)) 1) := by
  rw [theta_copComp_pair_apply_one Θ q A 1]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.cast_one, sub_self,
    zpow_zero, mul_one, dispCoeff_zero, one_smul, Nat.sub_zero, Nat.add_zero, Nat.sub_self,
    CopPower.completeHomog_zero, map_one, Module.End.one_apply]

/-- **The creation side at every `[A, 1]`, in the slope operator.**
`HJO.Mellit.theta_copComp_pair_one_apply_one` with `Θ(h_1) = -Q_{2,3}` substituted:

  `Θ(C_{[A,1]}1)(1) = (-q)^{1-A} ( -Q_{2,3}(Θ(h_A)(1)) + (q^{-1}-1) Θ(h_{A+1})(1) )`.

Every ingredient is now explicit: `Θ(h_A)(1)` and `Θ(h_{A+1})(1)` are the one-part values the
singleton clause family already constrains, and `Q_{2,3}` at an arbitrary argument is
`HJO.Sym.qop_two_three_apply_elemSymmComp`. So the two-part clause at inner part one is **determined
by the one-part family**, at every `A` — an infinite family, beyond the four compositions decided
elsewhere.

Genericity: `qu ≠ 0` and `qu ≠ 1`, entering only through `HJO.Mellit.theta_completeHomog_one`;
`M⁻¹` and `q^{-1}` are carried, not cleared. -/
theorem theta_copComp_pair_one_apply_one_qop (hv0 : q * u ≠ 0) (hv1 : q * u ≠ 1)
    {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)} (hΘ : IsSlopeHom 2 3 q u Θ) (A : ℕ) :
    Θ (CopComp q [A, 1] (1 : Lambda L)) 1
      = ((-q) ^ (1 - (A : ℤ))) •
          (-(Qop q u 2 3 (Θ (completeHomog L A) 1))
            + dispCoeff q 1 • Θ (completeHomog L (A + 1)) 1) := by
  rw [theta_copComp_pair_one_apply_one Θ q A, theta_completeHomog_one hΘ hv0 hv1,
    LinearMap.neg_apply]

/-- **Consistency check: the general `[A, 1]` formula run forward onto the decided `[1, 1]`
instance.**

Specialising `HJO.Mellit.theta_copComp_pair_one_apply_one_qop` at `A = 1`, substituting
`Θ(h_1)(1) = -Q_{2,3}(1)` for the inner value and `(1+qu)Θ(h_2)(1) = qu(Q_{2,3}^2 - Q_{4,6})(1)` for
the outer one, and clearing `1 + qu`, gives

  `(1+qu) Θ(C_1C_1(1))(1) = (u+1) Q_{2,3}(Q_{2,3}1) + u(q-1) Q_{4,6}(1)`,

which is `HJO.Mellit.theta_copComp_one_one_apply_one_of_pair` statement for statement —
`HJO.Mellit.theta_copComp_one_one_apply_one_of_pair_one_eq` checks that by `rfl`. The scalar
arithmetic the check exercises is `(q^{-1}-1)qu = u - qu`, which is where `q ≠ 0` is spent and the
only place; an off-by-one in the `j`-range, a sign in `HJO.CreationSeeds.dispCoeff` or the two
operators exchanged would all separate the two sides.

Genericity: `q ≠ 0` (the route's, for `q^{-1}q = 1`), `qu ≠ 0`, `qu ≠ 1`. -/
theorem theta_copComp_one_one_apply_one_of_pair_one (hq0 : q ≠ 0) (hv0 : q * u ≠ 0)
    (hv1 : q * u ≠ 1) {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)}
    (hΘ : IsSlopeHom 2 3 q u Θ) :
    (q * u + 1) • Θ (CopComp q [1, 1] (1 : Lambda L)) 1
      = (u + 1) • Qop q u 2 3 (Qop q u 2 3 (1 : Lambda L))
        + (u * (q - 1)) • Qop q u (2 * 2) (3 * 2) (1 : Lambda L) := by
  have hcoef : (q⁻¹ - 1) * (q * u) = u - q * u := by
    have hinv : q⁻¹ * q = 1 := inv_mul_cancel₀ hq0
    linear_combination u * hinv
  have h2 := congrArg (fun T : Module.End L (Lambda L) => T (1 : Lambda L))
    (theta_completeHomog_two_smul hΘ hv0 hv1)
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.mul_apply] at h2
  have h1 : Θ (completeHomog L 1) (1 : Lambda L) = -Qop q u 2 3 (1 : Lambda L) := by
    rw [theta_completeHomog_one hΘ hv0 hv1, LinearMap.neg_apply]
  have h := theta_copComp_pair_one_apply_one_qop hv0 hv1 hΘ 1
  rw [h1, map_neg, neg_neg, show (1 : ℕ) + 1 = 2 from rfl, Nat.cast_one, sub_self, zpow_zero,
    one_smul, dispCoeff_one] at h
  rw [show (2 : ℕ) * 2 = 4 from rfl, show (3 : ℕ) * 2 = 6 from rfl, h, smul_add,
    smul_comm (q * u + 1) (q⁻¹ - 1), h2, smul_smul, hcoef]
  module

/-- **The two routes to `(1+qu)Θ(C_1C_1(1))(1)` state the same proposition.** `rfl` between the
proofs typechecks only if the statements are identical; the left-hand route is this file's general
two-part formula at inner part one, the right-hand one the `h`-basis derivation of
`HJO.Mellit.theta_copComp_one_one_apply_one_of_pair`, which in turn re-proves
`HJO.Mellit.lhsAt_two_three_one_one` through `HJO.Mellit.lhsAt_two_three_one_one_of_pair`. -/
theorem theta_copComp_one_one_apply_one_of_pair_one_eq (hq0 : q ≠ 0) (hv0 : q * u ≠ 0)
    (hv1 : q * u ≠ 1) {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)}
    (hΘ : IsSlopeHom 2 3 q u Θ) :
    theta_copComp_one_one_apply_one_of_pair_one hq0 hv0 hv1 hΘ
      = theta_copComp_one_one_apply_one_of_pair hq0 hv0 hv1 hΘ := rfl

/-! ### `Θ(h_2)` at every `e`-monomial, and the creation side at every `[A, 2]` -/

/-- **`(1 + qu)Θ(h_2)` at every `e`-monomial, explicitly.**
`HJO.Mellit.theta_completeHomog_two_smul` says `(1+qu)Θ(h_2) = qu(Q_{2,3}^2 - Q_{4,6})`, and both
operators are now evaluated at every `e`-monomial by `HJO.Sym.qop_two_three_sq_apply_elemSymmComp`
and `HJO.Sym.qop_four_six_apply_elemSymmComp` — six `D`-words of length four in all.

The scalar `1 + qu` is carried on the left and never inverted, so `qu = -1` is not excluded; there
the statement reads `0 = 0`, which is exactly where `U_1, U_2` fail to span `h_2`.
Genericity: `qu ≠ 0`, `qu ≠ 1`. -/
theorem theta_completeHomog_two_smul_apply_elemSymmComp (hv0 : q * u ≠ 0) (hv1 : q * u ≠ 1)
    {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)} (hΘ : IsSlopeHom 2 3 q u Θ) (l : List ℕ) :
    (q * u + 1) • Θ (completeHomog L 2) (elemSymmComp L l)
      = (q * u) • ((((1 - q) * (1 - u))⁻¹ * ((1 - q) * (1 - u))⁻¹) •
            (dopPushMono q u [1, 2, 1, 2] l - dopPushMono q u [2, 1, 1, 2] l
              - dopPushMono q u [1, 2, 2, 1] l + dopPushMono q u [2, 1, 2, 1] l)
          - (((1 - q) * (1 - u))⁻¹ * ((1 - q) * (1 - u))⁻¹ * ((1 - q) * (1 - u))⁻¹) •
            (dopPushMono q u [1, 1, 2, 2] l
              - dopPushMono q u [1, 2, 1, 2] l - dopPushMono q u [1, 2, 1, 2] l
              + dopPushMono q u [2, 1, 2, 1] l + dopPushMono q u [2, 1, 2, 1] l
              - dopPushMono q u [2, 2, 1, 1] l)) := by
  have h := congrArg (fun T : Module.End L (Lambda L) => T (elemSymmComp L l))
    (theta_completeHomog_two_smul hΘ hv0 hv1)
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.mul_apply] at h
  rw [h, qop_two_three_sq_apply_elemSymmComp, qop_four_six_apply_elemSymmComp]

/-- **The creation side of the `hlhs` clause at every composition `[A, 2]`.**

`HJO.Mellit.theta_copComp_pair_apply_one` at `B = 2` has three terms, and `h_0 = 1` makes the last
one a vacuum value:

  `Θ(C_{[A,2]}1)(1) = (-q)^{1-A}(-q)^{-1}
      ( Θ(h_2)(Θ(h_A)(1)) + c_1 Θ(h_1)(Θ(h_{A+1})(1)) + c_2 Θ(h_{A+2})(1) )`.

So the outer operators are `Θ(h_2)`, `Θ(h_1)` and the identity — all three evaluated at arbitrary
arguments by this file. **No hypothesis at all.** -/
theorem theta_copComp_pair_two_apply_one (Θ : Lambda L →ₐ[L] Module.End L (Lambda L)) (q : L)
    (A : ℕ) :
    Θ (CopComp q [A, 2] (1 : Lambda L)) 1
      = ((-q) ^ (1 - (A : ℤ)) * (-q) ^ (1 - ((2 : ℕ) : ℤ))) •
          (Θ (completeHomog L 2) (Θ (completeHomog L A) 1)
            + dispCoeff q 1 • Θ (completeHomog L 1) (Θ (completeHomog L (A + 1)) 1)
            + dispCoeff q 2 • Θ (completeHomog L (A + 2)) 1) := by
  rw [theta_copComp_pair_apply_one Θ q A 2]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, dispCoeff_zero, one_smul,
    Nat.sub_zero, Nat.add_zero, Nat.sub_self, CopPower.completeHomog_zero, map_one,
    Module.End.one_apply, show (2 : ℕ) - 1 = 1 from rfl]

/-- **The creation side at every `[A, 2]`, in the slope operators.**

`HJO.Mellit.theta_copComp_pair_two_apply_one` with `Θ(h_1) = -Q_{2,3}` and
`(1+qu)Θ(h_2) = qu(Q_{2,3}^2 - Q_{4,6})` substituted, the scalar `1 + qu` cleared onto the left:

  `(1+qu) Θ(C_{[A,2]}1)(1) = (-q)^{1-A}(-q)^{-1} (
      qu (Q_{2,3}^2 - Q_{4,6})(Θ(h_A)(1))
      - (1+qu) c_1 Q_{2,3}(Θ(h_{A+1})(1)) + (1+qu) c_2 Θ(h_{A+2})(1) )`.

Together with `HJO.Mellit.theta_copComp_pair_one_apply_one_qop` this evaluates the creation side at
**every** two-part composition whose inner part is at most `2`, in terms of the one-part values
`Θ(h_n)(1)` alone and of operators this file evaluates at every argument. Two infinite families,
beyond the four compositions decided elsewhere.

Genericity: `qu ≠ 0`, `qu ≠ 1`; `1 + qu` is carried on the left, so `qu = -1` is not excluded, and
`M⁻¹`, `q^{-1}` are carried inside the explicit operators. -/
theorem theta_copComp_pair_two_apply_one_qop (hv0 : q * u ≠ 0) (hv1 : q * u ≠ 1)
    {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)} (hΘ : IsSlopeHom 2 3 q u Θ) (A : ℕ) :
    (q * u + 1) • Θ (CopComp q [A, 2] (1 : Lambda L)) 1
      = ((-q) ^ (1 - (A : ℤ)) * (-q) ^ (1 - ((2 : ℕ) : ℤ))) •
          ((q * u) • (Qop q u 2 3 (Qop q u 2 3 (Θ (completeHomog L A) 1))
              - Qop q u 4 6 (Θ (completeHomog L A) 1))
            - (q * u + 1) • dispCoeff q 1 • Qop q u 2 3 (Θ (completeHomog L (A + 1)) 1)
            + (q * u + 1) • dispCoeff q 2 • Θ (completeHomog L (A + 2)) 1) := by
  have h2 := congrArg (fun T : Module.End L (Lambda L) => T (Θ (completeHomog L A) 1))
    (theta_completeHomog_two_smul hΘ hv0 hv1)
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.mul_apply] at h2
  rw [theta_copComp_pair_two_apply_one Θ q A, theta_completeHomog_one hΘ hv0 hv1,
    LinearMap.neg_apply,
    smul_comm (q * u + 1) ((-q) ^ (1 - (A : ℤ)) * (-q) ^ (1 - ((2 : ℕ) : ℤ)))]
  simp only [smul_add]
  rw [h2]
  module

end HJO.Mellit
