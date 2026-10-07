/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.MellitCollinearSplit

/-! # The induction on the composition carries nothing, whatever its datum

`HJO.Mellit.lhsWord_iff_lhsAppendStep` (`HJO/Shuffle/MellitLhsCompInduction.lean`) says the
clause of `HJO.Mellit.lhsRewrite_sweepWitness` *is* its own append step, so the whole content of
`hlhs` sits in the step that peels the last part of the composition. Three choices of inductive
datum suggest themselves — the constant term, the accumulated vector, the accumulated creation
operator. This file settles all three.

## The value-carrying datum is refuted; the other two are empty

With the **constant term** as datum the step needs
`ct ∘ d_-^ℓ ∘ (d_-^{(ℓ+1)}G_{ℓ+1,A})` to factor through `ct ∘ d_-^ℓ`, and
`HJO.Sweep.not_exists_factorization_two_three`
(`HJO/Shuffle/MellitLevelRaiseTwoThree.lean`) refutes that **in range**, at `(2,3)`.

With the accumulated **vector** as datum there is nothing to refute, and nothing to use.
`HJO.Mellit.stageWordTotal_append` is already a theorem with **no hypothesis at all**: the
accumulated vector at `β ++ [A]` *is* `G_{ℓ+1,A}` of the accumulated vector at `β`. So the vector
datum is available at every composition, at every `(a,b)`, for free — and a step that may assume it
is a step that may assume nothing. `HJO.Mellit.lhsWord_iff_lhsVecAppendStep` is that, exactly: the
append step whose hypothesis is the vector and its transport law, *with the clause at `β` dropped*,
is **equivalent to the whole of `HJO.Mellit.LhsWord`**. Replacing the constant term by the vector
does not weaken the factorization the value-carrying step needed; it deletes the factorization, and
with it the step.

The same applies to the accumulated creation **operator** `Ψ : f ↦ Θ(C_β(f))1`, the third
datum: its transport law is `HJO.Mellit.copComp_append_apply`, also unconditional, and
`HJO.Mellit.lhsWord_iff_lhsOpAppendStep` is the same equivalence. Whichever of the three is carried,
the step is either refuted or vacuous.

## Why neither datum can help: the creation side reads a new slope at every total degree

Appending a part changes the creation word's **seed**, not its letters
(`HJO.Mellit.lhsAt_append_iff`): the creation side at `β ++ [A]` is `Θ(C_β(C_A 1))1`, the *same*
word at a *different* argument, while the clause at `β` constrains only its value at `1`. So no
datum accumulated on the sweep side touches it. What the creation side needs instead is measured
here, at every total degree and not just at two.

`HJO.Sym.IsSlopeHom` is the *only* information a slope homomorphism carries: `Θ(U_k) = Q_{ak,bk}`
for `k ≥ 1`. So evaluating `Θ` on the creation seed of a composition of total degree `N` means
writing that seed as a polynomial in the axis generators, and

`HJO.Sym.completeHomog_not_mem_adjoin_axisGen`: `h_N ∉ L[U_1, …, U_{N-1}]`

for every `N ≥ 1` and every `v`, unconditionally. The single-part composition `[N]` has seed
`C_N(1) = (-q)^{1-N}h_N` (`HJO.Mellit.copComp_singleton_apply_one`), so
`HJO.Mellit.copComp_singleton_not_mem_adjoin_axisGen`: **the clause at total degree `N` reads
`Q_{Na,Nb}`, an operator no clause of total degree `< N` mentions.** At `N = 2` this is the earlier
`HJO.Mellit.theta_copComp_one_one`, whose `Q_{2a,2b}`-coefficient `u(q-1)` is nonzero at every
parameter the clause is not vacuous at; the theorem here is the same phenomenon at every `N`.

`HJO.Mellit.copComp_one_mem_supported` is the bounding half, at every composition and not just the
one-part ones: total degree `N` reads nothing *above* `p_N`. So each total degree contributes
exactly one new slope operator, and never none.

The proof is one variable: `Λ` is the polynomial algebra on the `p_j`, `h_k` and `U_k` both live in
`p_1, …, p_k` (`HJO.Sym.completeHomog_mem_supported`, `HJO.Sym.axisGen_mem_supported` —
`HJO.Sym.axisGen` is a *diagonal* substitution applied to `h_k`, so it moves no variable), and `h_N`
genuinely uses `p_N`: the two evaluations `p_N ↦ 1` and `p_N ↦ 0`, all other `p_j ↦ 0`, agree on
everything supported below `p_N` and differ on `h_N`, by `1/N`.

## How big the new slope is

`HJO.Mellit.qop_two_three_collinear_bracket` reads the consequence at the slope `(2,3)`, the
smallest in range. `Q_{2N,3N}` is collinear and not coprime, and `primitiveSplit(2,3) = (1,1)`, so
`HJO.Sym.qop_collinear_eq_bracket` gives

`Q_{2N,3N} = M^{-1}(Q_{2N-1,3N-1}Q_{1,1} - Q_{1,1}Q_{2N-1,3N-1})`,  `M = (1-q)(1-u)`,

with `Q_{2N-1,3N-1}` coprime. Its first index is `2N - 1`, **unbounded in `N`**, and for `N ≥ 2` it
lies in neither family proved earlier: not the `(a,1)` column of `HJO.Mellit.lhsSlope_succ_one`
(`3N - 1 > 1`) and not the `(2,b)` row of `HJO.Mellit.lhsSlope_two_odd` (`2N - 1 > 2`). `N = 2` is
`Q_{3,5}`, which the two-part rung evaluates by hand;
`N = 3, 4, …` are `Q_{5,8}, Q_{7,11}, …`.

So the step of the induction on the composition is **not a fixed finite identity**: its content
grows with the total degree, one new coprime slope operator per degree, each outside the families
proved earlier. That is the obstruction, and it is independent of the datum.

## Why there is no seed slot on the sweep side

`HJO.Mellit.theta_copComp_mem_lambdaComp`: the creation side at seed degree `d` is homogeneous of
degree `b(β.sum + d)` — `HJO.Sym.IsSlopeHom` scales every degree by `b`. The only slot for a seed on
the sweep side is the innermost one, `V_0`, and that carries the `Λ`-degree *additively*, giving
`b·β.sum + d`. The two agree only when `(b-1)d = 0`, so at `b ≥ 2` — which is all of `hlhs`, since
`1 < a < b` — no clause generalised in the seed can hold. The additivity of the sweep seed is a
degree count that is not formalised here; the factor `b` on the creation side is.

## What is *not* claimed

Nothing here refutes `hlhs`, which is proved by a different route
(`HJO.Mellit.lhsRewrite_sweepWitness`); what is closed is the *route* —
an induction on the composition, in any of the three data. Nor is the growing family impossible to
evaluate: each `Q_{2N-1,3N-1}(1)` is a finite computation through `HJO.Sym.qop_of_coprime`. There
are infinitely many of them, and the one at `N = 2` already needed degree-eleven coefficients.

## Genericity

`HJO.Sym.completeHomog_mem_supported`, `HJO.Sym.axisGen_mem_supported`,
`HJO.Sym.completeHomog_not_mem_adjoin_axisGen` and
`HJO.Sym.mem_supported_of_mem_lambdaComp`, `HJO.Mellit.copComp_one_mem_supported`,
`HJO.Mellit.copComp_append_apply`, `HJO.Mellit.lhsWord_iff_lhsVecAppendStep` and
`HJO.Mellit.lhsWord_iff_lhsOpAppendStep`: **none**.
`HJO.Mellit.theta_copComp_mem_lambdaComp`: `0 < b`, `qu ≠ 0` and `(qu)^j ≠ 1` for every `j ≥ 1` —
`HJO.Sym.axisSub_surjective`'s, i.e. the free generation of `Λ` by the axis generators, without
which `Θ f` is not determined at all. Algebraic independence of `q, u` supplies them.
`HJO.Mellit.copComp_singleton_not_mem_adjoin_axisGen`: `q ≠ 0`, which is `HJO.Sym.Cop`'s own
`(-q)^{1-r}` and is not removable — at `q = 0` that scalar is `0` and the seed is `0`, which lies
in every subalgebra. `HJO.Mellit.qop_two_three_collinear_bracket`: none beyond `2 ≤ N`; the
`M^{-1}` is `HJO.Sym.Qop`'s and the statement is its own definition unfolded, so `M = 0` is not
excluded.

## Implementation notes

These are structural facts about `HJO.Sym.Lambda`, `HJO.Sym.axisGen` and `HJO.Sym.Cop`, and
negative facts about a proof route.

## References

The file is about the clause `HJO.Mellit.lhsRewrite_sweepWitness`, read through
`HJO.Sym.Lambda`, `HJO.Sym.completeHomog`, `HJO.Sym.axisGen`, `HJO.Sym.Cop`, `HJO.Sym.IsSlopeHom`
and `HJO.Sym.Qop`.
-/

@[expose] public section

namespace HJO.Sym

open MvPolynomial

variable {L : Type*} [Field L] [Algebra ℚ L]

/-! ### `Λ` is a polynomial algebra, and `h_k` and `U_k` use only its first `k` variables -/

omit [Algebra ℚ L] in
/-- A variable of `HJO.Sym.Lambda` lies in the subalgebra supported on any set containing its index.
`MvPolynomial.X_mem_supported` asks for `Nontrivial`; this route does not. -/
theorem X_mem_supported_of_mem (s : Set ℕ) {i : ℕ} (hi : i ∈ s) :
    (MvPolynomial.X i : Lambda L) ∈ MvPolynomial.supported L s := by
  rw [MvPolynomial.supported_eq_adjoin_X]
  exact Algebra.subset_adjoin ⟨i, hi, rfl⟩

/-- **`h_n` uses only `p_1, …, p_n`.** Newton's identity of `HJO.Sym.completeHomog` reaches back at
most `n` steps, and the generator it multiplies in at step `k` is `p_{k+1}` with `k < n`.
Unconditional. -/
theorem completeHomog_mem_supported (n : ℕ) :
    completeHomog L n ∈ MvPolynomial.supported L (Set.Iio n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rw [HJO.CopPower.completeHomog_zero]; exact Subalgebra.one_mem _
    | (m + 1) =>
      rw [completeHomog]
      refine Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
        (Subalgebra.sum_mem _ fun k hk => ?_)
      rw [Finset.mem_range] at hk
      refine Subalgebra.mul_mem _ ?_
        (MvPolynomial.supported_mono (Set.Iio_subset_Iio (by omega)) (ih (m - k) (by omega)))
      rw [powerSum]
      simp only [Nat.add_sub_cancel]
      exact X_mem_supported_of_mem _ (by simp only [Set.mem_Iio]; omega)

omit [Algebra ℚ L] in
/-- **A diagonal substitution moves no variable.** `HJO.Sym.diagScale` scales each generator, so it
preserves every subalgebra supported on a set of indices. Unconditional. -/
theorem diagScale_mem_supported {c : ℕ → L} {s : Set ℕ} {f : Lambda L}
    (hf : f ∈ MvPolynomial.supported L s) : diagScale c f ∈ MvPolynomial.supported L s := by
  have h : MvPolynomial.supported L s
      ≤ Subalgebra.comap (diagScale c) (MvPolynomial.supported L s) := by
    rw [MvPolynomial.supported_eq_adjoin_X]
    refine Algebra.adjoin_le ?_
    rintro _ ⟨i, hi, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_comap, diagScale_X,
      ← MvPolynomial.supported_eq_adjoin_X]
    exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (X_mem_supported_of_mem _ hi)
  exact h hf

/-- **The axis generator `U_k` uses only `p_1, …, p_k`.** `HJO.Sym.axisGen` is a scalar times a
diagonal substitution of `h_k`, and neither moves a variable. Unconditional — in particular the
degenerate values of `HJO.Sym.axisGen` at `v = 0, 1` are covered. -/
theorem axisGen_mem_supported (v : L) (k : ℕ) :
    axisGen v k ∈ MvPolynomial.supported L (Set.Iio k) := by
  rw [axisGen, plethAxis_eq_diagScale]
  exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
    (diagScale_mem_supported (completeHomog_mem_supported k))

/-! ### `h_N` genuinely uses `p_N` -/

/-- The evaluation of `HJO.Sym.Lambda` sending `p_N` to `c` and every other power sum to `0`. -/
noncomputable def evalAtPowerSum (L : Type*) [Field L] (N : ℕ) (c : L) : Lambda L →ₐ[L] L :=
  MvPolynomial.aeval fun i => if i = N - 1 then c else 0

omit [Algebra ℚ L] in
theorem evalAtPowerSum_powerSum_self (N : ℕ) (c : L) :
    evalAtPowerSum L N c (powerSum L N) = c := by
  rw [powerSum, evalAtPowerSum, MvPolynomial.aeval_X]
  simp

omit [Algebra ℚ L] in
theorem evalAtPowerSum_powerSum_of_ne (N : ℕ) (c : L) (hN : 0 < N) {j : ℕ} (hj : 0 < j)
    (hjN : j ≠ N) : evalAtPowerSum L N c (powerSum L j) = 0 := by
  rw [powerSum, evalAtPowerSum, MvPolynomial.aeval_X]
  simp only [show j - 1 ≠ N - 1 from by omega, ite_false]

/-- Every `h_m` with `1 ≤ m < N` dies: `HJO.Sym.completeHomog` writes it through `p_1, …, p_m`, all
sent to `0`. -/
theorem evalAtPowerSum_completeHomog_of_lt (N : ℕ) (c : L) :
    ∀ m : ℕ, 0 < m → m < N → evalAtPowerSum L N c (completeHomog L m) = 0 := by
  intro m hm hmN
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  rw [completeHomog, map_mul, map_sum]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun k hk => ?_)
  rw [Finset.mem_range] at hk
  rw [map_mul, evalAtPowerSum_powerSum_of_ne N c (by omega) (by omega) (by omega), zero_mul]

/-- **`h_N` reads `p_N` with coefficient `1/N`.** Exactly one term of Newton's identity survives the
evaluation, the one carrying `p_N` itself against `h_0 = 1`. -/
theorem evalAtPowerSum_completeHomog_self (N : ℕ) (c : L) (hN : 0 < N) :
    evalAtPowerSum L N c (completeHomog L N) = algebraMap ℚ L ((N : ℚ)⁻¹) * c := by
  obtain ⟨j, rfl⟩ : ∃ j, N = j + 1 := ⟨N - 1, by omega⟩
  rw [completeHomog, map_mul, map_sum, evalAtPowerSum, MvPolynomial.aeval_C, ← evalAtPowerSum]
  have hc : (algebraMap ℚ L) ((j : ℚ) + 1)⁻¹ = (algebraMap ℚ L) (((j + 1 : ℕ) : ℚ))⁻¹ := by
    push_cast; ring_nf
  rw [hc]
  congr 1
  rw [Finset.sum_eq_single j]
  · rw [map_mul, evalAtPowerSum_powerSum_self, Nat.sub_self,
      HJO.CopPower.completeHomog_zero, map_one, mul_one]
  · intro k hk hkj
    rw [Finset.mem_range] at hk
    rw [map_mul, evalAtPowerSum_powerSum_of_ne _ c (by omega) (by omega) (by omega), zero_mul]
  · intro h; exact absurd (Finset.self_mem_range_succ j) h

omit [Algebra ℚ L] in
/-- Two of these evaluations that differ only at `p_N` agree on everything supported below it. -/
theorem evalAtPowerSum_eq_of_mem_supported (N : ℕ) (c c' : L) {f : Lambda L}
    (hf : f ∈ MvPolynomial.supported L (Set.Iio (N - 1))) :
    evalAtPowerSum L N c f = evalAtPowerSum L N c' f := by
  have h : MvPolynomial.supported L (Set.Iio (N - 1))
      ≤ AlgHom.equalizer (evalAtPowerSum L N c) (evalAtPowerSum L N c') := by
    rw [MvPolynomial.supported_eq_adjoin_X]
    refine Algebra.adjoin_le ?_
    rintro _ ⟨i, hi, rfl⟩
    simp only [Set.mem_Iio] at hi
    rw [SetLike.mem_coe, AlgHom.mem_equalizer, evalAtPowerSum, evalAtPowerSum,
      MvPolynomial.aeval_X, MvPolynomial.aeval_X]
    simp only [show i ≠ N - 1 from by omega, ite_false]
  exact h hf

/-- **`h_N` is not supported on `p_1, …, p_{N-1}`.** Unconditional for `N ≥ 1`. -/
theorem completeHomog_not_mem_supported (N : ℕ) (hN : 0 < N) :
    completeHomog L N ∉ MvPolynomial.supported L (Set.Iio (N - 1)) := by
  intro h
  have h1 := evalAtPowerSum_eq_of_mem_supported N (1 : L) 0 h
  rw [evalAtPowerSum_completeHomog_self N 1 hN, evalAtPowerSum_completeHomog_self N 0 hN,
    mul_one, mul_zero] at h1
  have h2 : ((N : ℚ))⁻¹ = 0 := (algebraMap ℚ L).injective (by rw [h1, map_zero])
  rw [inv_eq_zero, Nat.cast_eq_zero] at h2
  omega

/-- **`h_N` IS NOT A POLYNOMIAL IN THE LOWER AXIS GENERATORS**, at every `N ≥ 1` and every `v`,
unconditionally.

`HJO.Sym.axisGen` at index `k` uses only `p_1, …, p_k` (`HJO.Sym.axisGen_mem_supported`), so the
subalgebra generated by `U_1, …, U_{N-1}` is supported below `p_N`, and
`HJO.Sym.completeHomog_not_mem_supported` says `h_N` is not.

**The consequence for `HJO.Mellit.lhsRewrite_sweepWitness`.** `HJO.Sym.IsSlopeHom` pins a slope
homomorphism on the axis generators and on nothing else, so `Θ(h_N)` is not determined by
`Q_{a,b}, …, Q_{(N-1)a,(N-1)b}`: the creation seed at total degree `N` reads `Q_{Na,Nb}`, which no
composition of smaller total degree mentions. At `N = 2` this is
`HJO.Mellit.theta_copComp_one_one`. -/
@[hjo "lem_slope_one_new_per_degree"]
theorem completeHomog_not_mem_adjoin_axisGen (v : L) (N : ℕ) (hN : 0 < N) :
    completeHomog L N ∉ Algebra.adjoin L (axisGen v '' {k : ℕ | 0 < k ∧ k < N}) := by
  have hle : Algebra.adjoin L (axisGen v '' {k : ℕ | 0 < k ∧ k < N})
      ≤ MvPolynomial.supported L (Set.Iio (N - 1)) := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨k, ⟨hk0, hkN⟩, rfl⟩
    exact MvPolynomial.supported_mono (Set.Iio_subset_Iio (by omega)) (axisGen_mem_supported v k)
  exact fun h => completeHomog_not_mem_supported N hN (hle h)

omit [Algebra ℚ L] in
/-- **A homogeneous element of degree `N` uses only `p_1, …, p_N`.** Every monomial of it has
weighted degree `N`, so a generator occurring in one has weight at most `N`. Unconditional. -/
@[hjo "lem_slope_one_new_per_degree"]
theorem mem_supported_of_mem_lambdaComp {N : ℕ} {f : Lambda L} (hf : f ∈ LambdaComp L N) :
    f ∈ MvPolynomial.supported L (Set.Iio N) := by
  rw [MvPolynomial.mem_supported]
  intro i hi
  rw [Finset.mem_coe, MvPolynomial.mem_vars_iff_mem_support] at hi
  obtain ⟨d, hd, hid⟩ := hi
  have hw := mem_lambdaComp.1 hf (MvPolynomial.mem_support_iff.1 hd)
  have h2 : (fun j : ℕ => j + 1) i ≤ Finsupp.weight (fun j : ℕ => j + 1) d :=
    Finsupp.le_weight_of_ne_zero' _ (Finsupp.mem_support_iff.1 hid)
  rw [hw] at h2
  have h3 : i + 1 ≤ N := h2
  simp only [Set.mem_Iio]
  omega

end HJO.Sym

namespace HJO.Mellit

open HJO.Sym

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L} {a b : ℕ}

/-! ### The creation seed at total degree `N` reads the slope at total degree `N` -/

/-- **The creation seed of a composition of total degree `N` uses only `p_1, …, p_N`.** The bounding
half: `HJO.Sym.copComp_one_mem_lambdaComp` makes it homogeneous of degree `N`, and
`HJO.Sym.mem_supported_of_mem_lambdaComp` reads that as a bound on the variables. Unconditional.

Together with `HJO.Mellit.copComp_singleton_not_mem_adjoin_axisGen` this says the clause at total
degree `N` reads `p_N` — hence `U_N`, hence `Q_{Na,Nb}` — and **nothing above it**: each total
degree contributes exactly one new slope operator, and the contribution is never empty. -/
theorem copComp_one_mem_supported (q : L) {α : List ℕ} {N : ℕ} (hα : α.sum = N) :
    CopComp q α (1 : Lambda L) ∈ MvPolynomial.supported L (Set.Iio N) :=
  mem_supported_of_mem_lambdaComp (copComp_one_mem_lambdaComp q hα)

/-- **The creation seed of the one-part composition `[N]` is not a polynomial in the axis generators
of index `< N`.** `HJO.Mellit.copComp_singleton_apply_one` makes it `(-q)^{1-N}h_N`, a unit times
`h_N`, and `HJO.Sym.completeHomog_not_mem_adjoin_axisGen` does the rest.

So the clause of `HJO.Mellit.lhsRewrite_sweepWitness` at `α = [N]` — one part, length one, total
degree `N` — already reads `Q_{Na,Nb}`. An induction on the composition therefore faces a *new*
slope operator at every total degree, whatever it carries from one step to the next: the datum
accumulates on the sweep side and this is on the creation side.

`q ≠ 0` is `HJO.Sym.Cop`'s own `(-q)^{1-r}` and is not removable: at `q = 0` the seed is `0`, which
lies in every subalgebra. -/
@[hjo "lem_slope_one_new_per_degree"]
theorem copComp_singleton_not_mem_adjoin_axisGen (q v : L) (hq0 : q ≠ 0) (N : ℕ) (hN : 0 < N) :
    CopComp q [N] (1 : Lambda L) ∉ Algebra.adjoin L (axisGen v '' {k : ℕ | 0 < k ∧ k < N}) := by
  rw [copComp_singleton_apply_one]
  intro h
  refine completeHomog_not_mem_adjoin_axisGen v N hN ?_
  have hs : ((-q) ^ (1 - (N : ℤ)) : L) ≠ 0 := zpow_ne_zero _ (neg_ne_zero.2 hq0)
  have := Subalgebra.mul_mem _
    (Subalgebra.algebraMap_mem (Algebra.adjoin L (axisGen v '' {k : ℕ | 0 < k ∧ k < N}))
      (((-q) ^ (1 - (N : ℤ)))⁻¹)) h
  rwa [MvPolynomial.algebraMap_eq, ← mul_assoc, ← MvPolynomial.C_mul,
    inv_mul_cancel₀ hs, MvPolynomial.C_1, one_mul] at this

/-- **At `(a,b) = (2,3)` the new slope of total degree `N` is `Q_{2N-1,3N-1}`, and it is coprime.**

`primitiveSplit(2,3) = (1,1)`, so `HJO.Sym.qop_collinear_eq_bracket` at multiplicity `N` reads the
collinear slope `Q_{2N,3N}` off the coprime pair `(2N-1, 3N-1)` and `(1,1)`. The first index is
`2N - 1`, unbounded in `N`: for `N ≥ 2` it exceeds `2`, so the slope lies outside the `(2,b)` row of
`HJO.Mellit.lhsSlope_two_odd`, and its second index `3N - 1` exceeds `1`, so it lies outside the
`(a,1)` column of `HJO.Mellit.lhsSlope_succ_one`. `N = 2` is `Q_{3,5}`, the one the two-part
rung evaluates by hand.

No genericity: this is `HJO.Sym.Qop`'s own non-coprime branch with the split identified. -/
theorem qop_two_three_collinear_bracket (q u : L) {N : ℕ} (hN : 2 ≤ N) :
    Qop q u (2 * N) (3 * N) = ((1 - q) * (1 - u))⁻¹ •
      (Qop q u (2 * N - 1) (3 * N - 1) * Qop q u 1 1 -
        Qop q u 1 1 * Qop q u (2 * N - 1) (3 * N - 1)) := by
  have h := qop_collinear_eq_bracket (L := L) q u (a := 2) (b := 3) (k := N)
    (by norm_num) (by norm_num) (by decide) hN
  rwa [show primitiveSplit 2 3 = ((1 : ℕ), (1 : ℕ)) from by decide] at h

/-! ### The append step whose datum is the accumulated vector -/

/-- **The append step of the opposite-ends induction, with the accumulated VECTOR as its datum.**

What is available at `β` is the accumulated vector `W = G_{ℓ,β_ℓ}⋯G_{1,β_1}(1) ∈ V_ℓ` together with
its transport law — the clause at `β` is deliberately **not** assumed, since carrying the vector is
supposed to replace carrying the value. -/
def LhsVecAppendStep (q u : L) (a b : ℕ) : Prop :=
  ∀ Θ : Lambda L →ₐ[L] Module.End L (Lambda L), IsSlopeHom a b q u Θ →
    ∀ β : List ℕ, (∀ x ∈ β, 0 < x) → ∀ A : ℕ, 0 < A →
      ∀ W : Sweep.Total L, W = stageWordTotal q u a b β →
        stageWordTotal q u a b (β ++ [A]) = stageTotal q u a b β.length A W →
          LhsAt q u a b Θ (β ++ [A])

/-- **The vector-carrying step is the whole clause.** Read left to right this says the step is
forced, as `HJO.Mellit.lhsWord_iff_lhsAppendStep` does for the value-carrying one; read right to
left it says the step **transports nothing**, because both of its hypotheses are theorems —
`rfl` and `HJO.Mellit.stageWordTotal_append`, the latter with no hypothesis on `q`, `u`, `a`, `b`,
`β` or `A`.

This is the precise sense in which replacing the constant term by the accumulated vector does not
get past `HJO.Sweep.not_exists_factorization_two_three`: the refuted factorization was what made the
value-carrying step a *step*, and dropping it leaves an implication whose antecedent is empty. A
proof of `HJO.Mellit.LhsVecAppendStep` is a proof of the clause at every non-empty composition, with
no use made of the clause at any shorter one.

Unconditional. -/
theorem lhsWord_iff_lhsVecAppendStep : LhsWord q u a b ↔ LhsVecAppendStep q u a b := by
  rw [lhsWord_iff_lhsAppendStep]
  constructor
  · intro h Θ hΘ β hβ A hA _ _ _
    exact h Θ hΘ β hβ A hA (lhsAt_of_lhsAppendStep h Θ hΘ β hβ)
  · intro h Θ hΘ β hβ A hA _
    exact h Θ hΘ β hβ A hA (stageWordTotal q u a b β) rfl
      (stageWordTotal_append q u a b β A)

/-! ### The accumulated creation operator as datum, and why it has no counterpart -/

/-- **Appending a part changes the creation word's seed.** The mirror of
`HJO.Mellit.stageWordTotal_append` on the creation side, at every seed rather than only at the
vacuum: `HJO.Sym.CopComp` is a product of operators, and the appended part is the innermost factor.
Unconditional. -/
theorem copComp_append_apply (q : L) (β : List ℕ) (A : ℕ) (f : Lambda L) :
    CopComp q (β ++ [A]) f = CopComp q β (Cop q A f) := by
  rw [CopComp, CopComp, List.map_append, List.prod_append]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    Module.End.mul_apply]

/-- **The append step whose datum is the accumulated creation OPERATOR** — the linear map
`Ψ : f ↦ Θ(C_β(f))1` on all of `Λ`, not merely its value at the vacuum — together with its
transport law. -/
def LhsOpAppendStep (q u : L) (a b : ℕ) : Prop :=
  ∀ Θ : Lambda L →ₐ[L] Module.End L (Lambda L), IsSlopeHom a b q u Θ →
    ∀ β : List ℕ, (∀ x ∈ β, 0 < x) → ∀ A : ℕ, 0 < A →
      ∀ Ψ : Lambda L → Lambda L, (∀ f, Ψ f = Θ (CopComp q β f) 1) →
        (∀ f, Ψ (Cop q A f) = Θ (CopComp q (β ++ [A]) f) 1) →
          LhsAt q u a b Θ (β ++ [A])

/-- **The operator-carrying step is also the whole clause.** Exactly as for
`HJO.Mellit.lhsWord_iff_lhsVecAppendStep`, and for the same reason: both hypotheses are theorems,
the second being `HJO.Mellit.copComp_append_apply`, which is unconditional. So carrying the whole
accumulated creation operator instead of its value at the vacuum transports nothing either.

Unconditional. -/
theorem lhsWord_iff_lhsOpAppendStep : LhsWord q u a b ↔ LhsOpAppendStep q u a b := by
  rw [lhsWord_iff_lhsAppendStep]
  constructor
  · intro h Θ hΘ β hβ A hA _ _ _
    exact h Θ hΘ β hβ A hA (lhsAt_of_lhsAppendStep h Θ hΘ β hβ)
  · intro h Θ hΘ β hβ A hA _
    exact h Θ hΘ β hβ A hA (fun f => Θ (CopComp q β f) 1) (fun _ => rfl)
      fun f => by rw [copComp_append_apply]

/-- **The creation side multiplies the seed's degree by `b`.** For a seed `f` homogeneous of degree
`d`, the creation-side value `Θ(C_β(f))1` is homogeneous of degree `b(β.sum + d)`:
`HJO.Sym.copComp_shiftsDegree` adds `β.sum` to `d`, and `HJO.Sym.isSlopeHom_shiftsDegree` then
scales by `b`, because `HJO.Sym.IsSlopeHom` sends the generator of degree `k` to an operator
shifting degree by `bk`.

**This is why the seed slot has no counterpart on the sweep side.** The clause itself is the case
`d = 0`, where the two sides agree at degree `b·β.sum`. A generalisation carrying the seed would
have to insert `f` somewhere in the sweep word, and the only slot there is the innermost one, `V_0`,
which carries the `Λ`-degree *additively* — giving `b·β.sum + d` against the `b(β.sum + d)` proved
here. So such a generalisation can hold only when `(b-1)d = 0`, i.e. never for `b ≥ 2` and a seed of
positive degree, and `hlhs` ranges over `1 < a < b`. The additivity of the sweep seed is a degree
count that is *not* formalised here; what is formalised is the factor `b` on the creation side.

Genericity: `qu ≠ 0` and `(qu)^j ≠ 1` for every `j ≥ 1`, which are `HJO.Sym.axisSub_surjective`'s —
the free generation of `Λ` by the axis generators is what makes `Θ f` known at all. Algebraic
independence of `q, u` supplies both. -/
theorem theta_copComp_mem_lambdaComp [CharZero L] (hb : 0 < b) (hv0 : q * u ≠ 0)
    (hv1 : ∀ j : ℕ, (q * u) ^ (j + 1) ≠ 1)
    {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)} (hΘ : IsSlopeHom a b q u Θ) (β : List ℕ) {d : ℕ}
    {f : Lambda L} (hf : f ∈ LambdaComp L d) :
    Θ (CopComp q β f) 1 ∈ LambdaComp L (b * (β.sum + d)) := by
  have h1 : CopComp q β f ∈ LambdaComp L (d + β.sum) :=
    (copComp_shiftsDegree q (α := β) rfl).apply_mem_lambdaComp hf
  have h2 := isSlopeHom_shiftsDegree hb hv0 hv1 hΘ h1
  rw [show ((b : ℤ) * ((d + β.sum : ℕ) : ℤ)) = ((b * (β.sum + d) : ℕ) : ℤ) by push_cast; ring] at h2
  have h3 : (1 : Lambda L) ∈ LambdaComp L 0 := by
    rw [mem_lambdaComp]; exact MvPolynomial.isWeightedHomogeneous_one L _
  simpa using h2.apply_mem_lambdaComp h3

end HJO.Mellit

end
