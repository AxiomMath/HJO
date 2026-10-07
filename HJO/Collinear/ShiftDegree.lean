/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Symmetric.SymmetricFunctions
public meta import HJO.Attr

/-! # The displacement moves weighted degree into the variable

The BGLX step "displacement in the last variable" needs to know that the plethystic displacement
`δ = plethShift q u`, which sends `f` to `f[X + M/z]`, does not create degree out of nothing: each
power `z^{-n}` it produces is paid for by `n` units of weighted degree taken out of the symmetric
function. Concretely, if every monomial of `f` has weighted degree at most `N` — the generator
`p_{i+1}` weighing `i + 1` — then the coefficient of `w ^ n` in `δ f` (where `w = z⁻¹`, so this is
the coefficient of `z ^ (-n)`) has weighted degree at most `N - n`, and vanishes outright once
`n > N`.

This file supplies the two filtrations that make that statement sayable and the transfer between
them. `HJO.Bglx.LambdaLE K N` is the submodule of symmetric functions of weighted degree at most
`N`, a *filtration* rather than the grading `HJO.Sym.LambdaComp`: the displacement is not
homogeneous — it sends `p_k` to `p_k + (1 - q ^ k)(1 - u ^ k) w ^ k`, whose two terms have
different symmetric-function degrees — so the statement has to be about degree *bounds*, and the
graded submodules cannot carry it. `HJO.Bglx.ShiftLE K N` is the matching filtration on the target
`Polynomial (Lambda K)`: the polynomials in `w` whose `w ^ n`-coefficient has degree at most
`N - n` and which stop at `w ^ N`. The main theorem is that `δ` maps the first into the second.

## Main definitions

* `HJO.Bglx.LambdaLE`: the symmetric functions all of whose monomials have weighted degree at
  most `N`.
* `HJO.Bglx.ShiftLE`: the polynomials in `w = z⁻¹` over `Lambda K` whose coefficient of `w ^ n`
  lies in `LambdaLE K (N - n)` and which vanish above `w ^ N`.

## Main statements

* `HJO.Bglx.plethShift_mem_shiftLE`: the displacement carries `LambdaLE K N` into `ShiftLE K N` —
  degree moves from the symmetric function into the variable, one for one.
* `HJO.Bglx.coeff_plethShift_mem_lambdaLE` and `HJO.Bglx.coeff_plethShift_eq_zero`: the same fact
  read off coefficient by coefficient, which is the form the word estimates use.
* `HJO.Bglx.mul_mem_lambdaLE` and `HJO.Bglx.mul_mem_shiftLE`: both filtrations are multiplicative,
  the degrees adding.
* `HJO.Bglx.elemSymm_mem_lambdaLE`: the elementary symmetric function `e_n` has weighted degree at
  most `n`, so the pairing of `δ f` against the `e`-series respects the filtration.

## Implementation notes

`LambdaLE` is defined by a condition on the support rather than as
`⨆ d ≤ N, HJO.Sym.LambdaComp K d` or through `MvPolynomial.weightedTotalDegree`: the support form
is what every proof here actually uses, it needs no `Decidable` or nontriviality side conditions,
and membership is definitionally the bound (`mem_lambdaLE_iff` is `Iff.rfl`), so the filtration
never has to be unfolded by hand.

The main theorem is proved by reducing to a single monomial with `MvPolynomial.as_sum` and
`MvPolynomial.monomial_eq`, since `plethShift` is an algebra map: a monomial `p^e` becomes a
product of powers of `δ p_{i+1}`, each of which lies in `ShiftLE K (i + 1)` by direct computation,
and the multiplicativity of `ShiftLE` then adds the exponents to exactly the weight of `e`.

## References

* [F. Bergeron, A. Garsia, E. Leven, G. Xin, *Compositional (km, kn)-shuffle conjectures*]
-/

@[expose] public section

open Finset

namespace HJO.Bglx

open HJO.Sym

variable {K : Type*} [CommRing K]

/-! ### The weighted-degree filtration on symmetric functions -/

/-- The symmetric functions of weighted degree at most `N`: those all of whose monomials `e` have
`Finsupp.weight (fun i => i + 1) e ≤ N`, the generator `p_{i+1}` weighing `i + 1`. -/
def LambdaLE (K : Type*) [CommRing K] (N : ℕ) : Submodule K (Lambda K) where
  carrier := {f | ∀ e ∈ f.support, Finsupp.weight (fun i => i + 1) e ≤ N}
  add_mem' hf hg e he := by
    rcases Finset.mem_union.1 (MvPolynomial.support_add he) with h | h
    · exact hf e h
    · exact hg e h
  zero_mem' e he := by simp at he
  smul_mem' a _ hf e he := hf e (MvPolynomial.support_smul he)

/-- Membership in `LambdaLE K N` is the bound on the weight of every monomial. -/
theorem mem_lambdaLE_iff {N : ℕ} {f : Lambda K} :
    f ∈ LambdaLE K N ↔ ∀ e ∈ f.support, Finsupp.weight (fun i => i + 1) e ≤ N := Iff.rfl

/-- The filtration is increasing. -/
theorem lambdaLE_mono {N M : ℕ} (h : N ≤ M) : LambdaLE K N ≤ LambdaLE K M :=
  fun _ hf e he => (hf e he).trans h

/-- A scalar has weighted degree `0`, hence degree at most any `N`. -/
theorem C_mem_lambdaLE (a : K) (N : ℕ) : (MvPolynomial.C a : Lambda K) ∈ LambdaLE K N := by
  refine mem_lambdaLE_iff.2 fun e he => ?_
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C] at he
  rcases eq_or_ne (0 : ℕ →₀ ℕ) e with h | h
  · rw [← h, map_zero]
    exact Nat.zero_le _
  · simp [h] at he

/-- The unit has weighted degree `0`, hence degree at most any `N`. -/
theorem one_mem_lambdaLE (N : ℕ) : (1 : Lambda K) ∈ LambdaLE K N := by
  rw [← MvPolynomial.C_1]
  exact C_mem_lambdaLE 1 N

/-- The filtration is multiplicative: the degrees add. -/
theorem mul_mem_lambdaLE {N M : ℕ} {f g : Lambda K} (hf : f ∈ LambdaLE K N)
    (hg : g ∈ LambdaLE K M) : f * g ∈ LambdaLE K (N + M) := by
  refine mem_lambdaLE_iff.2 fun e he => ?_
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_mul] at he
  obtain ⟨p, hp, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero he
  rw [Finset.mem_antidiagonal] at hp
  have h1 : MvPolynomial.coeff p.1 f ≠ 0 := fun h => hne (by rw [h, zero_mul])
  have h2 : MvPolynomial.coeff p.2 g ≠ 0 := fun h => hne (by rw [h, mul_zero])
  have hw : Finsupp.weight (fun i => i + 1) (p.1 + p.2)
      = Finsupp.weight (fun i => i + 1) p.1 + Finsupp.weight (fun i => i + 1) p.2 :=
    map_add _ _ _
  rw [← hp, hw]
  exact add_le_add (mem_lambdaLE_iff.1 hf _ (MvPolynomial.mem_support_iff.mpr h1))
    (mem_lambdaLE_iff.1 hg _ (MvPolynomial.mem_support_iff.mpr h2))

/-- Multiplicativity against a slack bound, the form in which the arithmetic is usually
discharged. -/
theorem mul_mem_lambdaLE_of_le {N M P : ℕ} {f g : Lambda K} (hf : f ∈ LambdaLE K N)
    (hg : g ∈ LambdaLE K M) (h : N + M ≤ P) : f * g ∈ LambdaLE K P :=
  lambdaLE_mono h (mul_mem_lambdaLE hf hg)

/-- The power sum `p_j` has weighted degree `j`, for `j ≥ 1`. -/
theorem powerSum_mem_lambdaLE {j : ℕ} (hj : 1 ≤ j) : powerSum K j ∈ LambdaLE K j := by
  refine mem_lambdaLE_iff.2 fun e he => ?_
  rw [powerSum, MvPolynomial.mem_support_iff, MvPolynomial.coeff_X] at he
  rcases eq_or_ne (Finsupp.single (j - 1) 1) e with h | h
  · rw [← h, Finsupp.weight_single, one_smul]
    omega
  · simp [h] at he

/-- The elementary symmetric function `e_n` has weighted degree at most `n`. The Newton recursion
`n eₙ = ∑_{k<n} (-1)^k p_{k+1} e_{n-1-k}` adds `k + 1` to a degree bound of `n - 1 - k`. -/
theorem elemSymm_mem_lambdaLE [Algebra ℚ K] (n : ℕ) : elemSymm K n ∈ LambdaLE K n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 =>
      rw [elemSymm]
      exact one_mem_lambdaLE 0
    | m + 1 =>
      rw [elemSymm]
      refine mul_mem_lambdaLE_of_le (C_mem_lambdaLE _ 0)
        (Submodule.sum_mem _ fun k hk => ?_) (Nat.zero_add _).le
      rw [Finset.mem_range] at hk
      have hsign : ((-1 : Lambda K)) ^ k = MvPolynomial.C ((-1 : K) ^ k) := by
        rw [map_pow, map_neg, map_one]
      rw [hsign]
      exact mul_mem_lambdaLE_of_le
        (mul_mem_lambdaLE_of_le (C_mem_lambdaLE _ 0) (powerSum_mem_lambdaLE (Nat.le_add_left 1 k))
          (Nat.zero_add _).le)
        (ih (m - k) (by omega)) (by omega)

/-! ### The matching filtration on the displaced polynomials -/

/-- The displaced elements of degree at most `N`: the coefficient of `w ^ n` has degree at most
`N - n`, and vanishes for `n > N`. Here `w = z⁻¹`, so the coefficient of `w ^ n` is the
coefficient of `z ^ (-n)`. -/
def ShiftLE (K : Type*) [CommRing K] (N : ℕ) : Submodule K (Polynomial (Lambda K)) where
  carrier := {P | (∀ n, P.coeff n ∈ LambdaLE K (N - n)) ∧ ∀ n, N < n → P.coeff n = 0}
  add_mem' hP hQ :=
    ⟨fun n => by rw [Polynomial.coeff_add]; exact add_mem (hP.1 n) (hQ.1 n),
     fun n hn => by rw [Polynomial.coeff_add, hP.2 n hn, hQ.2 n hn, add_zero]⟩
  zero_mem' :=
    ⟨fun n => by rw [Polynomial.coeff_zero]; exact zero_mem _,
     fun n _ => Polynomial.coeff_zero n⟩
  smul_mem' a _ hP :=
    ⟨fun n => by rw [Polynomial.coeff_smul]; exact Submodule.smul_mem _ a (hP.1 n),
     fun n hn => by rw [Polynomial.coeff_smul, hP.2 n hn, smul_zero]⟩

/-- Membership in `ShiftLE K N` is the coefficientwise degree bound together with the vanishing
above `w ^ N`. -/
theorem mem_shiftLE_iff {N : ℕ} {P : Polynomial (Lambda K)} :
    P ∈ ShiftLE K N ↔ (∀ n, P.coeff n ∈ LambdaLE K (N - n)) ∧ ∀ n, N < n → P.coeff n = 0 :=
  Iff.rfl

/-- The filtration on the displaced polynomials is increasing. -/
theorem shiftLE_mono {N M : ℕ} (h : N ≤ M) : ShiftLE K N ≤ ShiftLE K M := fun _ hP =>
  ⟨fun n => lambdaLE_mono (by omega) (hP.1 n), fun n hn => hP.2 n (by omega)⟩

/-- The filtration on the displaced polynomials is multiplicative: the degrees add. On the
`w ^ n`-coefficient of a product the summand indexed by `a + b = n` lies in
`LambdaLE K ((N - a) + (M - b))`, and `(N - a) + (M - b) ≤ N + M - n`. -/
theorem mul_mem_shiftLE {N M : ℕ} {P Q : Polynomial (Lambda K)} (hP : P ∈ ShiftLE K N)
    (hQ : Q ∈ ShiftLE K M) : P * Q ∈ ShiftLE K (N + M) := by
  refine mem_shiftLE_iff.2 ⟨fun n => ?_, fun n hn => ?_⟩
  · rw [Polynomial.coeff_mul]
    refine Submodule.sum_mem _ fun p hp => ?_
    rw [Finset.mem_antidiagonal] at hp
    by_cases h1 : N < p.1
    · rw [hP.2 p.1 h1, zero_mul]
      exact zero_mem _
    by_cases h2 : M < p.2
    · rw [hQ.2 p.2 h2, mul_zero]
      exact zero_mem _
    exact mul_mem_lambdaLE_of_le (hP.1 p.1) (hQ.1 p.2) (by omega)
  · rw [Polynomial.coeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [Finset.mem_antidiagonal] at hp
    by_cases h1 : N < p.1
    · rw [hP.2 p.1 h1, zero_mul]
    · rw [hQ.2 p.2 (by omega), mul_zero]

/-- A monomial `a w ^ n` with `a` of degree at most `N` lies in `ShiftLE K (N + n)`: the variable
`w` carries one unit of degree per power. -/
theorem monomial_mem_shiftLE {N : ℕ} (n : ℕ) {a : Lambda K} (ha : a ∈ LambdaLE K N) :
    (Polynomial.monomial n a : Polynomial (Lambda K)) ∈ ShiftLE K (N + n) := by
  refine mem_shiftLE_iff.2 ⟨fun m => ?_, fun m hm => ?_⟩
  · rw [Polynomial.coeff_monomial]
    split_ifs with h
    · subst h
      exact lambdaLE_mono (by omega) ha
    · exact zero_mem _
  · rw [Polynomial.coeff_monomial]
    split_ifs with h
    · exact absurd h (by omega)
    · rfl

/-- A constant of degree at most `N` lies in `ShiftLE K N`. -/
theorem C_mem_shiftLE {N : ℕ} {a : Lambda K} (ha : a ∈ LambdaLE K N) :
    (Polynomial.C a : Polynomial (Lambda K)) ∈ ShiftLE K N := by
  have h := monomial_mem_shiftLE 0 ha
  rwa [Polynomial.monomial_zero_left, Nat.add_zero] at h

/-- The unit lies in every `ShiftLE K N`. -/
theorem one_mem_shiftLE (N : ℕ) : (1 : Polynomial (Lambda K)) ∈ ShiftLE K N := by
  rw [← Polynomial.C_1]
  exact C_mem_shiftLE (one_mem_lambdaLE N)

/-- Powers multiply the degree bound. -/
theorem pow_mem_shiftLE {N : ℕ} {P : Polynomial (Lambda K)} (hP : P ∈ ShiftLE K N) (k : ℕ) :
    P ^ k ∈ ShiftLE K (N * k) := by
  induction k with
  | zero =>
    rw [pow_zero, Nat.mul_zero]
    exact one_mem_shiftLE 0
  | succ k ih =>
    rw [pow_succ]
    have h := mul_mem_shiftLE ih hP
    rwa [show N * k + N = N * (k + 1) from by ring] at h

/-- A finite product adds the degree bounds. -/
theorem prod_mem_shiftLE {ι : Type*} {P : ι → Polynomial (Lambda K)} {N : ι → ℕ}
    (h : ∀ i, P i ∈ ShiftLE K (N i)) (s : Finset ι) :
    (∏ i ∈ s, P i) ∈ ShiftLE K (∑ i ∈ s, N i) := by
  induction s using Finset.cons_induction with
  | empty => simpa using one_mem_shiftLE (K := K) 0
  | cons a s _ ih =>
    rw [Finset.prod_cons, Finset.sum_cons]
    exact mul_mem_shiftLE (h a) ih

/-! ### The displacement respects the filtrations -/

/-- The displacement of the generator of index `i`, which stands for `p_{i+1}`, lies in
`ShiftLE K (i + 1)`: its `w ^ 0`-coefficient is `p_{i+1}`, of degree `i + 1`, and its
`w ^ (i+1)`-coefficient is a scalar, of degree `0`. -/
theorem plethShift_X_mem_shiftLE (q u : K) (i : ℕ) :
    plethShift q u (MvPolynomial.X i) ∈ ShiftLE K (i + 1) := by
  rw [plethShift, MvPolynomial.aeval_X]
  refine add_mem (C_mem_shiftLE (powerSum_mem_lambdaLE (Nat.le_add_left 1 i))) ?_
  rw [Polynomial.C_mul_X_pow_eq_monomial]
  have h := monomial_mem_shiftLE (K := K) (i + 1)
    (C_mem_lambdaLE ((1 - q ^ (i + 1)) * (1 - u ^ (i + 1))) 0)
  rwa [Nat.zero_add] at h

/-- The displacement of a scalar lies in `ShiftLE K 0`: an algebra map fixes the scalars. -/
theorem plethShift_C_mem_shiftLE (q u : K) (a : K) :
    plethShift q u (MvPolynomial.C a) ∈ ShiftLE K 0 := by
  rw [plethShift, MvPolynomial.aeval_C, Algebra.algebraMap_eq_smul_one]
  exact Submodule.smul_mem _ a (one_mem_shiftLE 0)

/-- The displacement of a monomial `a p^e` lies in `ShiftLE K (weight e)`: the monomial is a
product of powers of the generators, each factor contributing `(i + 1) * e i`. -/
theorem plethShift_monomial_mem_shiftLE (q u : K) (e : ℕ →₀ ℕ) (a : K) :
    plethShift q u (MvPolynomial.monomial e a) ∈
      ShiftLE K (Finsupp.weight (fun i => i + 1) e) := by
  have hwt : Finsupp.weight (fun i => i + 1) e = ∑ i ∈ e.support, (i + 1) * e i := by
    rw [Finsupp.weight_apply, Finsupp.sum]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_eq_mul, mul_comm]
  rw [MvPolynomial.monomial_eq, map_mul, Finsupp.prod, map_prod, hwt]
  have hprod : (∏ i ∈ e.support, plethShift q u (MvPolynomial.X i ^ e i)) ∈
      ShiftLE K (∑ i ∈ e.support, (i + 1) * e i) := by
    refine prod_mem_shiftLE (fun i => ?_) e.support
    rw [map_pow]
    exact pow_mem_shiftLE (plethShift_X_mem_shiftLE q u i) (e i)
  have h := mul_mem_shiftLE (plethShift_C_mem_shiftLE q u a) hprod
  rwa [Nat.zero_add] at h

/-- **The displacement moves degree into the variable.** If every monomial of `f` has weighted
degree at most `N`, then `f[X + M/z]` lies in `ShiftLE K N`: its coefficient of `z ^ (-n)` has
weighted degree at most `N - n`, and there is no `z ^ (-n)` at all for `n > N`. -/
theorem plethShift_mem_shiftLE (q u : K) {N : ℕ} {f : Lambda K} (hf : f ∈ LambdaLE K N) :
    plethShift q u f ∈ ShiftLE K N := by
  rw [MvPolynomial.as_sum f, map_sum]
  refine Submodule.sum_mem _ fun e he => ?_
  exact shiftLE_mono (mem_lambdaLE_iff.1 hf e he) (plethShift_monomial_mem_shiftLE q u e _)

/-- The coefficient of `z ^ (-n)` in `f[X + M/z]` has weighted degree at most `N - n`. -/
theorem coeff_plethShift_mem_lambdaLE (q u : K) {N : ℕ} {f : Lambda K} (hf : f ∈ LambdaLE K N)
    (n : ℕ) : (plethShift q u f).coeff n ∈ LambdaLE K (N - n) :=
  (mem_shiftLE_iff.1 (plethShift_mem_shiftLE q u hf)).1 n

/-- There is no `z ^ (-n)` in `f[X + M/z]` beyond the weighted degree of `f`. -/
theorem coeff_plethShift_eq_zero (q u : K) {N : ℕ} {f : Lambda K} (hf : f ∈ LambdaLE K N)
    {n : ℕ} (hn : N < n) : (plethShift q u f).coeff n = 0 :=
  (mem_shiftLE_iff.1 (plethShift_mem_shiftLE q u hf)).2 n hn

end HJO.Bglx
