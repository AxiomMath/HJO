/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Collinear.ShiftDegree
public import HJO.Collinear.MonoMul
public meta import HJO.Attr

/-! # Degree control and the displacement in a new last variable

BGLX build the displacement `δ^{(k)}` one variable at a time: given a formal sum in `z_1, …, z_k`
they apply the plethystic displacement `δ = plethShift q u` to each *coefficient* and read the
powers of `z_{k+1}` it produces as a new last exponent. That operation does not preserve
cone-boundedness for an arbitrary element of `M_k`: it lowers the last exponent by as much as the
weighted degree of the coefficient, and that degree is unbounded over the support. What controls
it is a correlation present in every sum occurring in BGLX's argument — the degree of the
coefficient at `α` grows no faster than `α_1 + ⋯ + α_k`. This file isolates that condition,
`G_k`, shows it cuts out a subalgebra of the cone ring, and builds the displacement in the new
variable on it.

The degree bookkeeping is done with an *integer* bound: `HJO.Bglx.DegLEZ N x` says every monomial
of `x` has weighted degree at most `N` for `N : ℤ`, which at a negative `N` forces `x = 0`. That
is what the condition "lies in the sum of the `Λ_d` with `d ≤ N + α_1 + ⋯ + α_k`" says, the
right-hand side being an integer that may well be negative, and the `ℕ`-valued filtration
`HJO.Bglx.LambdaLE` of `HJO/Collinear/ShiftDegree.lean` cannot state it.

## Main definitions

* `HJO.Bglx.snocExp`, `HJO.Bglx.initExp`, `HJO.Bglx.lastExp`: the splitting of an exponent in
  `k + 1` variables into its first `k` coordinates and its last, and `HJO.Bglx.coordSum` for the
  sum of all coordinates.
* `HJO.Bglx.DegLEZ`: the weighted-degree bound with an integer bound.
* `HJO.Bglx.IsDegreeControlled`: the condition `G_k`, that the coefficient at `α` has weighted
  degree at most `N + α_1 + ⋯ + α_k` for one `N` serving every `α`.
* `HJO.Bglx.padFamily`: the padding of a formal sum with a last variable, the coefficient at
  `(α, n)` being `f α` for `n = 0` and `0` otherwise.
* `HJO.Bglx.shiftExtend`: the displacement in the last variable, the coefficient at `(α, n)` being
  the coefficient of `z_{k+1} ^ n` in `δ (f α)`; `HJO.Bglx.shiftExtendElem` is the same map with
  its target recorded as an element of the cone ring.

## Main statements

* `HJO.Bglx.isDegreeControlled_zero`, `HJO.Bglx.isDegreeControlled_add`,
  `HJO.Bglx.isDegreeControlled_smul`, `HJO.Bglx.isDegreeControlled_one` and
  `HJO.Bglx.isDegreeControlled_mul`: the degree-controlled cone-bounded sums are a subalgebra.
* `HJO.Bglx.isConeBounded_padFamily` and `HJO.Bglx.isDegreeControlled_padFamily`: the padding
  preserves both conditions.
* `HJO.Bglx.isConeBounded_shiftExtend` and `HJO.Bglx.isDegreeControlled_shiftExtend`: the
  displacement in the last variable preserves both conditions. This is where degree control is
  used: without it the new last exponent is unbounded below.
* `HJO.Bglx.shiftExtendElem_mul`: the displacement in the last variable is multiplicative.

## Implementation notes

**The exponent splitting is `snocExp`/`initExp`/`lastExp`, not `Fin.snoc` on the nose.** Exponents
are `Fin k →₀ ℤ` (see `HJO/Collinear/ConeRing.lean`), so `Fin.snoc` has to be wrapped in
`Finsupp.equivFunOnFinite.symm`; the three wrappers and their `simp` lemmas let every later proof
work with `snocExp α n` and never unfold the `Finsupp`.

**The bound in `DegLEZ` is an integer and the bound in `LambdaLE` is a natural number.** The two
are bridged by `DegLEZ_of_mem_lambdaLE`, `mem_lambdaLE_of_DegLEZ` and
`eq_zero_of_DegLEZ_neg`: a degree-controlled family at an `α` with `N + coordSum α < 0` has a zero
coefficient there, and that case has to be split off before the `ℕ`-valued statements of
`ShiftDegree` can be applied. `DegLEZ_coeff_plethShift` and
`coeff_plethShift_eq_zero_of_DegLEZ` package the two `ShiftDegree` theorems with that case split
done once and for all, and they are the whole mathematical content of
`isConeBounded_shiftExtend`: one unit of weighted degree pays for one power of `z_{k+1}^{-1}`.

**The exponent `γ₀` bounding the support of a displacement is built through the partial-sum
bijection.** The proof asks for the vector with prescribed partial sums `P^id_j(β)` for
`j ≤ k` and `-N` at `j = k+1`; `snocPsumExp` is that vector, defined as the inverse image of the
prescribed tuple under `psumEquiv 1`, and `psum_snocPsumExp_of_le` and `psum_snocPsumExp_last` are
its two defining properties. Nothing about it is canonical — only that it exists.

**Multiplicativity is a double interchange of finite sums.** `ConeRing.coeff_mul_of_subset` lets
both sides be written as sums over finsets *chosen by the situation*: on the left the convolution
finset `s` of the coefficient at `α` and the antidiagonal of `m = -n`, on the right the image of
`s ×ˢ range (m+1)` under `snocExp`. The injectivity of `snocExp` matches them termwise, so no
reindexing lemma about the product is needed.

**How the definitions match BGLX's.** (1) `IsDegreeControlled`, `padFamily` and `shiftExtend` are
the `G_k`, padding and `δ̃_k` on the nose, with `shiftExtend_snocExp` pinning the coefficient at
`(α, n)` to the coefficient of `w ^ (-n)` in `δ (f α)` — that is of `z_{k+1} ^ n`, the polynomial
variable being `w = z⁻¹`. (2) Nothing is weakened: the degree bound in `isDegreeControlled_mul`
really is the sum `N + N'` of the two bounds, and the same `N` really works for `shiftExtend`, as
BGLX's proof asserts. (3) `shiftExtend_eq_padFamily` is the remark that on scalar coefficients the
displacement *is* the padding, so the two constructions are tied and `shiftExtend` is not some
unrelated map that happens to land in the ring. (4) The condition is not vacuous and not everything:
a finitely supported family is degree-controlled, while the coefficients of a degree-controlled
family at exponents with `coordSum α` very negative must vanish (`eq_zero_of_DegLEZ_neg`).

## References

This file follows F. Bergeron,
A. M. Garsia, E. Leven and G. Xin, *Some remarkable new plethystic operators in the theory of
Macdonald polynomials*, arXiv:1405.0316v1, J. Comb. **7** (2016) 671--714, whose proof of
Theorem 2.1 applies the displacement one variable at a time; the condition `G_k` making that
legitimate inside the cone ring is added here.
-/

@[expose] public section

namespace HJO.Bglx

open HJO.Sym

variable {k : ℕ} {R : Type*}

/-! ### Splitting an exponent into its first coordinates and its last -/

/-- The exponent in `k+1` variables with first `k` coordinates `α` and last coordinate `n`. -/
noncomputable def snocExp (α : Fin k →₀ ℤ) (n : ℤ) : Fin (k + 1) →₀ ℤ :=
  Finsupp.equivFunOnFinite.symm (Fin.snoc (fun i => α i) n)

/-- The first `k` coordinates of an exponent in `k+1` variables. -/
noncomputable def initExp (γ : Fin (k + 1) →₀ ℤ) : Fin k →₀ ℤ :=
  Finsupp.equivFunOnFinite.symm fun i => γ i.castSucc

/-- The last coordinate of an exponent in `k+1` variables. -/
def lastExp (γ : Fin (k + 1) →₀ ℤ) : ℤ := γ (Fin.last k)

@[simp] lemma initExp_apply (γ : Fin (k + 1) →₀ ℤ) (i : Fin k) : initExp γ i = γ i.castSucc := by
  simp [initExp]

@[simp] lemma snocExp_castSucc (α : Fin k →₀ ℤ) (n : ℤ) (i : Fin k) :
    snocExp α n i.castSucc = α i := by
  simp [snocExp]

@[simp] lemma snocExp_last (α : Fin k →₀ ℤ) (n : ℤ) : snocExp α n (Fin.last k) = n := by
  simp [snocExp]

@[simp] lemma initExp_snocExp (α : Fin k →₀ ℤ) (n : ℤ) : initExp (snocExp α n) = α :=
  Finsupp.ext fun i => by simp

@[simp] lemma lastExp_snocExp (α : Fin k →₀ ℤ) (n : ℤ) : lastExp (snocExp α n) = n := by
  simp [lastExp]

/-- An exponent in `k+1` variables is the join of its first `k` coordinates and its last. -/
lemma snocExp_initExp (γ : Fin (k + 1) →₀ ℤ) : snocExp (initExp γ) (lastExp γ) = γ := by
  refine Finsupp.ext fun i => ?_
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · simp
  · simp [lastExp]

/-- The splitting is additive. -/
lemma snocExp_add (α β : Fin k →₀ ℤ) (m n : ℤ) :
    snocExp (α + β) (m + n) = snocExp α m + snocExp β n := by
  refine Finsupp.ext fun i => ?_
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl <;> simp

@[simp] lemma initExp_sub (γ δ : Fin (k + 1) →₀ ℤ) : initExp (γ - δ) = initExp γ - initExp δ :=
  Finsupp.ext fun i => by simp

@[simp] lemma lastExp_sub (γ δ : Fin (k + 1) →₀ ℤ) : lastExp (γ - δ) = lastExp γ - lastExp δ := by
  simp [lastExp]

/-- The sum of the coordinates of an exponent. -/
def coordSum (α : Fin k →₀ ℤ) : ℤ := ∑ i : Fin k, α i

@[simp] lemma coordSum_zero : coordSum (0 : Fin k →₀ ℤ) = 0 := by simp [coordSum]

/-- The sum of the coordinates is additive. -/
lemma coordSum_add (α β : Fin k →₀ ℤ) : coordSum (α + β) = coordSum α + coordSum β := by
  simp [coordSum, Finset.sum_add_distrib]

/-- The sum of the coordinates commutes with subtraction. -/
lemma coordSum_sub (α β : Fin k →₀ ℤ) : coordSum (α - β) = coordSum α - coordSum β := by
  simp [coordSum, Finset.sum_sub_distrib]

/-- Adjoining a last coordinate adds it to the sum of the coordinates. -/
lemma coordSum_snocExp (α : Fin k →₀ ℤ) (n : ℤ) : coordSum (snocExp α n) = coordSum α + n := by
  rw [coordSum, Fin.sum_univ_castSucc, snocExp_last, coordSum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => snocExp_castSucc α n i

/-- The sum of the coordinates of an exponent in `k+1` variables splits as the sum of the first
`k` coordinates plus the last. -/
lemma coordSum_eq_coordSum_initExp_add_lastExp (γ : Fin (k + 1) →₀ ℤ) :
    coordSum γ = coordSum (initExp γ) + lastExp γ := by
  rw [← snocExp_initExp γ, coordSum_snocExp, initExp_snocExp, lastExp_snocExp]

/-- The `k`-th partial sum along the identity ordering is the sum of all coordinates. -/
lemma psum_one_eq_coordSum (α : Fin k →₀ ℤ) : psum 1 α k = coordSum α := by
  rw [psum, coordSum, ← Fin.sum_univ_eq_sum_range (fun m => letter 1 α m)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [letter_eq_of_lt i.isLt]
  rfl

/-- The partial sums of an exponent in `k+1` variables agree with those of its first `k`
coordinates, up to the last index. -/
lemma psum_one_initExp (γ : Fin (k + 1) →₀ ℤ) {j : ℕ} (hj : j ≤ k) :
    psum 1 γ j = psum 1 (initExp γ) j := by
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmk : m < k := by
    rw [Finset.mem_range] at hm; omega
  rw [letter_eq_of_lt (by omega : m < k + 1), letter_eq_of_lt hmk]
  change γ _ = initExp γ _
  rw [initExp_apply]
  rfl

/-- An exponent in `k+1` variables with prescribed partial sums along the identity ordering: the
first `k` are those of `β`, the last is `c`. It exists because `psumEquiv 1` is a bijection of the
exponent lattice. -/
noncomputable def snocPsumExp (β : Fin k →₀ ℤ) (c : ℤ) : Fin (k + 1) →₀ ℤ :=
  (psumEquiv 1).symm (Finsupp.equivFunOnFinite.symm
    fun j : Fin (k + 1) => if (j : ℕ) < k then psum 1 β ((j : ℕ) + 1) else c)

/-- The partial sums of `snocPsumExp β c`, read off index by index. -/
lemma psum_snocPsumExp (β : Fin k →₀ ℤ) (c : ℤ) (j : Fin (k + 1)) :
    psum 1 (snocPsumExp β c) ((j : ℕ) + 1)
      = if (j : ℕ) < k then psum 1 β ((j : ℕ) + 1) else c := by
  rw [← psumEquiv_apply (τ := (1 : Equiv.Perm (Fin (k + 1)))) (α := snocPsumExp β c) j,
    snocPsumExp, AddEquiv.apply_symm_apply]
  simp

/-- Up to index `k` the partial sums of `snocPsumExp β c` are those of `β`. -/
lemma psum_snocPsumExp_of_le (β : Fin k →₀ ℤ) (c : ℤ) {j : ℕ} (hj : j ≤ k) :
    psum 1 (snocPsumExp β c) j = psum 1 β j := by
  match j with
  | 0 => simp
  | (l + 1) =>
    have hl : l < k := by omega
    have h := psum_snocPsumExp β c ⟨l, by omega⟩
    simpa [hl] using h

/-- The last partial sum of `snocPsumExp β c` is `c`. -/
lemma psum_snocPsumExp_last (β : Fin k →₀ ℤ) (c : ℤ) :
    psum 1 (snocPsumExp β c) (k + 1) = c := by
  simpa using psum_snocPsumExp β c ⟨k, Nat.lt_succ_self k⟩

/-! ### The weighted-degree bound with an integer bound -/

variable {K : Type*} [CommRing K]

/-- A symmetric function all of whose monomials have weighted degree at most `N`, with `N` an
INTEGER: at a negative bound this forces the element to be `0`, which is what the "lies
in the sum of the `Λ_d` with `d ≤ N`" says. -/
def DegLEZ (N : ℤ) (x : Lambda K) : Prop :=
  ∀ e ∈ x.support, ((Finsupp.weight (fun i => i + 1) e : ℕ) : ℤ) ≤ N

/-- The zero symmetric function satisfies every degree bound. -/
lemma DegLEZ_zero {N : ℤ} : DegLEZ N (0 : Lambda K) := by
  intro e he
  simp at he

/-- The bound in `DegLEZ` may be enlarged. -/
lemma DegLEZ_mono {N M : ℤ} (h : N ≤ M) {x : Lambda K} (hx : DegLEZ N x) : DegLEZ M x :=
  fun e he => (hx e he).trans h

/-- A sum of two symmetric functions obeys a common degree bound. -/
lemma DegLEZ_add {N : ℤ} {x y : Lambda K} (hx : DegLEZ N x) (hy : DegLEZ N y) :
    DegLEZ N (x + y) := by
  intro e he
  rcases Finset.mem_union.1 (MvPolynomial.support_add he) with h | h
  · exact hx e h
  · exact hy e h

/-- Scaling does not raise the degree. -/
lemma DegLEZ_smul {N : ℤ} (a : K) {x : Lambda K} (hx : DegLEZ N x) : DegLEZ N (a • x) :=
  fun e he => hx e (MvPolynomial.support_smul he)

/-- A finite sum obeys a common degree bound. -/
lemma DegLEZ_sum {N : ℤ} {ι : Type*} {s : Finset ι} {g : ι → Lambda K}
    (h : ∀ i ∈ s, DegLEZ N (g i)) : DegLEZ N (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simpa using DegLEZ_zero
  | cons a s _ ih =>
    rw [Finset.sum_cons]
    exact DegLEZ_add (h a (by simp)) (ih fun i hi => h i (by simp [hi]))

/-- The degree bounds add under multiplication. -/
lemma DegLEZ_mul {N M : ℤ} {x y : Lambda K} (hx : DegLEZ N x) (hy : DegLEZ M y) :
    DegLEZ (N + M) (x * y) := by
  intro e he
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_mul] at he
  obtain ⟨p, hp, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero he
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  have h1 : MvPolynomial.coeff p.1 x ≠ 0 := fun h => hne (by rw [h, zero_mul])
  have h2 : MvPolynomial.coeff p.2 y ≠ 0 := fun h => hne (by rw [h, mul_zero])
  have hw : Finsupp.weight (fun i => i + 1) (p.1 + p.2)
      = Finsupp.weight (fun i => i + 1) p.1 + Finsupp.weight (fun i => i + 1) p.2 :=
    map_add _ _ _
  have e1 := hx p.1 (MvPolynomial.mem_support_iff.2 h1)
  have e2 := hy p.2 (MvPolynomial.mem_support_iff.2 h2)
  rw [← hp, hw]
  push_cast
  omega

/-- A nonnegative bound in `DegLEZ` is a bound in the `ℕ`-valued filtration `LambdaLE`. -/
lemma DegLEZ_of_mem_lambdaLE {N : ℕ} {x : Lambda K} (h : x ∈ LambdaLE K N) :
    DegLEZ (N : ℤ) x := fun e he => by exact_mod_cast mem_lambdaLE_iff.1 h e he

/-- Conversely, a bound in the `ℕ`-valued filtration is a bound in `DegLEZ`. -/
lemma mem_lambdaLE_of_DegLEZ {N : ℕ} {x : Lambda K} (h : DegLEZ (N : ℤ) x) :
    x ∈ LambdaLE K N := mem_lambdaLE_iff.2 fun e he => by exact_mod_cast h e he

/-- A negative degree bound forces the element to vanish: every monomial has weighted degree at
least `0`. -/
lemma eq_zero_of_DegLEZ_neg {N : ℤ} (hN : N < 0) {x : Lambda K} (h : DegLEZ N x) : x = 0 := by
  by_contra hx
  obtain ⟨e, he⟩ :=
    Finset.nonempty_iff_ne_empty.2 fun hs => hx (MvPolynomial.support_eq_empty.1 hs)
  have := h e he
  omega

/-- The unit has weighted degree `0`. -/
lemma DegLEZ_one : DegLEZ 0 (1 : Lambda K) := by
  have h := DegLEZ_of_mem_lambdaLE (one_mem_lambdaLE (K := K) 0)
  rwa [Nat.cast_zero] at h

/-- The coefficient of `w ^ m` of a scalar's displacement: `δ` fixes the scalars. -/
lemma coeff_plethShift_C (q u : K) (a : K) (m : ℕ) :
    Polynomial.coeff (plethShift q u (MvPolynomial.C a : Lambda K)) m
      = if m = 0 then MvPolynomial.C a else 0 := by
  rw [plethShift, MvPolynomial.aeval_C, Algebra.algebraMap_eq_smul_one, Polynomial.coeff_smul,
    Polynomial.coeff_one]
  split_ifs with h
  · rw [Algebra.smul_def, mul_one, MvPolynomial.algebraMap_eq]
  · rw [smul_zero]

/-- **The displacement moves degree into the variable, with an integer bound.** The
`w ^ m`-coefficient of `δ x` has weighted degree at most `N - m` when `x` has weighted degree at
most `N`. -/
lemma DegLEZ_coeff_plethShift (q u : K) {N : ℤ} {x : Lambda K} (hx : DegLEZ N x) (m : ℕ) :
    DegLEZ (N - m) (Polynomial.coeff (plethShift q u x) m) := by
  rcases lt_or_ge N 0 with hN | hN
  · rw [eq_zero_of_DegLEZ_neg hN hx, map_zero, Polynomial.coeff_zero]
    exact DegLEZ_zero
  have hx' : x ∈ LambdaLE K N.toNat := mem_lambdaLE_of_DegLEZ (by rwa [Int.toNat_of_nonneg hN])
  rcases Nat.lt_or_ge N.toNat m with hm | hm
  · rw [coeff_plethShift_eq_zero q u hx' hm]
    exact DegLEZ_zero
  · have h := DegLEZ_of_mem_lambdaLE (coeff_plethShift_mem_lambdaLE q u hx' m)
    refine DegLEZ_mono (le_of_eq ?_) h
    omega

/-- Beyond the weighted degree of `x` the displacement `δ x` has no `w ^ m` at all. -/
lemma coeff_plethShift_eq_zero_of_DegLEZ (q u : K) {N : ℤ} {x : Lambda K} (hx : DegLEZ N x)
    {m : ℕ} (hm : N < m) : Polynomial.coeff (plethShift q u x) m = 0 := by
  rcases lt_or_ge N 0 with hN | hN
  · rw [eq_zero_of_DegLEZ_neg hN hx, map_zero, Polynomial.coeff_zero]
  · have hx' : x ∈ LambdaLE K N.toNat := mem_lambdaLE_of_DegLEZ (by rwa [Int.toNat_of_nonneg hN])
    exact coeff_plethShift_eq_zero q u hx' (by omega)

/-! ### Degree-controlled formal sums -/

/-- **Degree-controlled formal sums** `G_k`: the coefficient at `α` has weighted degree at most
`N + α_1 + ⋯ + α_k`, for one `N` serving all `α`. -/
@[hjo "def_bglx_cone_graded"]
def IsDegreeControlled (f : Family k (Lambda K)) : Prop :=
  ∃ N : ℤ, ∀ α : Fin k →₀ ℤ, DegLEZ (N + coordSum α) (f α)

/-- The zero formal sum is degree-controlled. -/
theorem isDegreeControlled_zero : IsDegreeControlled (0 : Family k (Lambda K)) :=
  ⟨0, fun _ => DegLEZ_zero⟩

/-- Degree control is closed under addition: the bounds are taken to be the larger of the two. -/
@[hjo "lem_bglx_cone_graded_subring"]
theorem isDegreeControlled_add {f g : Family k (Lambda K)} (hf : IsDegreeControlled f)
    (hg : IsDegreeControlled g) : IsDegreeControlled (f + g) := by
  obtain ⟨N, hN⟩ := hf
  obtain ⟨M, hM⟩ := hg
  refine ⟨max N M, fun α => DegLEZ_add ?_ ?_⟩
  · exact DegLEZ_mono (by omega) (hN α)
  · exact DegLEZ_mono (by omega) (hM α)

/-- Degree control is closed under scaling. -/
@[hjo "lem_bglx_cone_graded_subring"]
theorem isDegreeControlled_smul (a : K) {f : Family k (Lambda K)} (hf : IsDegreeControlled f) :
    IsDegreeControlled (a • f) := by
  obtain ⟨N, hN⟩ := hf
  exact ⟨N, fun α => DegLEZ_smul a (hN α)⟩

/-- The unit of the cone ring is degree-controlled, with bound `0`. -/
@[hjo "lem_bglx_cone_graded_subring"]
theorem isDegreeControlled_one (τ : Equiv.Perm (Fin k)) :
    IsDegreeControlled (1 : ConeRing k τ (Lambda K)).coeff := by
  refine ⟨0, fun α => ?_⟩
  rw [ConeRing.coeff_one]
  split_ifs with h
  · subst h
    simpa using DegLEZ_one (K := K)
  · exact DegLEZ_zero

/-- Degree control is closed under the product of the cone ring: the bounds add. Each summand of
the convolution at `α` is bounded by `(N + coordSum α') + (N' + coordSum (α - α'))`, which is
`N + N' + coordSum α`. -/
@[hjo "lem_bglx_cone_graded_subring"]
theorem isDegreeControlled_mul {τ : Equiv.Perm (Fin k)} {x y : ConeRing k τ (Lambda K)}
    (hx : IsDegreeControlled x.coeff) (hy : IsDegreeControlled y.coeff) :
    IsDegreeControlled (x * y).coeff := by
  classical
  obtain ⟨N, hN⟩ := hx
  obtain ⟨M, hM⟩ := hy
  refine ⟨N + M, fun α => ?_⟩
  have hs : ConeRing.convSupport x y α ⊆ ↑(ConeRing.finite_convSupport x y α).toFinset := by
    rw [Set.Finite.coe_toFinset]
  rw [ConeRing.coeff_mul_of_subset x y α _ hs]
  refine DegLEZ_sum fun α' _ => ?_
  refine DegLEZ_mono (le_of_eq ?_) (DegLEZ_mul (hN α') (hM (α - α')))
  rw [coordSum_sub]
  ring

/-! ### Padding a formal sum with a last variable -/

/-- **Padding a formal sum with a last variable**: the coefficient at `(α, n)` is `f α` when
`n = 0` and `0` otherwise. -/
@[hjo "def_bglx_pad"]
noncomputable def padFamily [Zero R] (f : Family k R) : Family (k + 1) R :=
  fun γ => if lastExp γ = 0 then f (initExp γ) else 0

@[simp] lemma padFamily_snocExp_zero [Zero R] (f : Family k R) (α : Fin k →₀ ℤ) :
    padFamily f (snocExp α 0) = f α := by
  simp [padFamily]

@[simp] lemma padFamily_snocExp_of_ne [Zero R] (f : Family k R) (α : Fin k →₀ ℤ) {n : ℤ}
    (hn : n ≠ 0) : padFamily f (snocExp α n) = 0 := by
  simp [padFamily, hn]

/-- Padding is injective: the padded family remembers `f` on the hyperplane `n = 0`. -/
lemma padFamily_injective [Zero R] : Function.Injective (padFamily (k := k) (R := R)) := by
  intro f g h
  funext α
  rw [← padFamily_snocExp_zero f α, ← padFamily_snocExp_zero g α, h]

@[simp] lemma padFamily_zero [Zero R] : padFamily (0 : Family k R) = 0 := by
  funext γ
  simp [padFamily]

/-- Padding is additive. -/
lemma padFamily_add [AddZeroClass R] (f g : Family k R) :
    padFamily (f + g) = padFamily f + padFamily g := by
  funext γ
  simp only [padFamily, Pi.add_apply]
  split_ifs
  · rfl
  · rw [add_zero]

/-- Padding commutes with scaling, so it is `Λ`-linear. -/
lemma padFamily_smul {S : Type*} [Zero R] [SMulZeroClass S R] (a : S) (f : Family k R) :
    padFamily (a • f) = a • padFamily f := by
  funext γ
  simp only [padFamily, Pi.smul_apply]
  split_ifs
  · rfl
  · rw [smul_zero]

/-- Padding preserves cone-boundedness: a support inside `β + C^id_k` becomes a support inside
`snocExp β 0 + C^id_{k+1}`, the partial sums being unchanged up to index `k` and the last one
equal to the `k`-th. -/
theorem isConeBounded_padFamily {f : Family k (Lambda K)} (hf : IsConeBounded 1 f) :
    IsConeBounded 1 (padFamily f) := by
  rw [isConeBounded_iff] at hf ⊢
  obtain ⟨β, hβ⟩ := hf
  refine ⟨snocExp β 0, fun γ hγ j => ?_⟩
  have hlast : lastExp γ = 0 := by
    by_contra hc
    rw [padFamily, ite_eq_right hc] at hγ
    exact hγ rfl
  have hf0 : f (initExp γ) ≠ 0 := by
    rw [padFamily, ite_eq_left hlast] at hγ
    exact hγ
  by_cases hj : j ≤ k
  · rw [psum_one_initExp _ hj, psum_one_initExp _ hj, initExp_snocExp]
    exact hβ _ hf0 j
  · rw [psum_eq_psum_of_le (by omega : k + 1 ≤ j), psum_eq_psum_of_le (by omega : k + 1 ≤ j),
      psum_one_eq_coordSum, psum_one_eq_coordSum, coordSum_snocExp, add_zero,
      coordSum_eq_coordSum_initExp_add_lastExp γ, hlast, add_zero, ← psum_one_eq_coordSum,
      ← psum_one_eq_coordSum]
    exact hβ _ hf0 k

/-- Padding preserves degree control, the sum of the coordinates being unchanged. -/
theorem isDegreeControlled_padFamily {f : Family k (Lambda K)} (hf : IsDegreeControlled f) :
    IsDegreeControlled (padFamily f) := by
  obtain ⟨N, hN⟩ := hf
  refine ⟨N, fun γ => ?_⟩
  rw [padFamily]
  split_ifs with h
  · rw [coordSum_eq_coordSum_initExp_add_lastExp γ, h, add_zero]
    exact hN (initExp γ)
  · exact DegLEZ_zero

/-! ### The displacement in the last variable -/

/-- **The displacement in the last variable**: the coefficient at `(α, n)` is the coefficient of
`z_{k+1}^n` in `δ(f α)`, that is the coefficient of `w^(-n)` in `plethShift q u (f α)`; only `n ≤ 0`
occurs. -/
@[hjo "def_bglx_shift_extend"]
noncomputable def shiftExtend (q u : K) (f : Family k (Lambda K)) : Family (k + 1) (Lambda K) :=
  fun γ => if lastExp γ ≤ 0 then
      Polynomial.coeff (plethShift q u (f (initExp γ))) (-(lastExp γ)).toNat else 0

/-- The displacement in the last variable, on an exponent with nonpositive last coordinate. -/
lemma shiftExtend_apply_of_nonpos (q u : K) (f : Family k (Lambda K)) {γ : Fin (k + 1) →₀ ℤ}
    (hγ : lastExp γ ≤ 0) : shiftExtend q u f γ
      = Polynomial.coeff (plethShift q u (f (initExp γ))) (-(lastExp γ)).toNat := by
  rw [shiftExtend, ite_eq_left hγ]

/-- The displacement in the last variable vanishes at a positive last coordinate. -/
lemma shiftExtend_eq_zero_of_pos (q u : K) (f : Family k (Lambda K)) {γ : Fin (k + 1) →₀ ℤ}
    (hγ : 0 < lastExp γ) : shiftExtend q u f γ = 0 := by
  rw [shiftExtend, ite_eq_right (by omega)]

/-- The coefficient of the displacement at `(α, n)` for `n ≤ 0`. -/
theorem shiftExtend_snocExp (q u : K) (f : Family k (Lambda K)) (α : Fin k →₀ ℤ) {n : ℤ}
    (hn : n ≤ 0) : shiftExtend q u f (snocExp α n)
      = Polynomial.coeff (plethShift q u (f α)) (-n).toNat := by
  rw [shiftExtend_apply_of_nonpos q u f (by rwa [lastExp_snocExp]), initExp_snocExp,
    lastExp_snocExp]

/-- No positive power of the new variable occurs. -/
theorem shiftExtend_snocExp_of_pos (q u : K) (f : Family k (Lambda K)) (α : Fin k →₀ ℤ) {n : ℤ}
    (hn : 0 < n) : shiftExtend q u f (snocExp α n) = 0 :=
  shiftExtend_eq_zero_of_pos q u f (by rwa [lastExp_snocExp])

/-- On a family whose coefficients are scalars the displacement is the padding, `δ` fixing `𝕜`. -/
theorem shiftExtend_eq_padFamily (q u : K) (f : Family k (Lambda K))
    (hf : ∀ α, ∃ a : K, f α = MvPolynomial.C a) : shiftExtend q u f = padFamily f := by
  funext γ
  obtain ⟨a, ha⟩ := hf (initExp γ)
  rcases lt_trichotomy (lastExp γ) 0 with h | h | h
  · rw [shiftExtend_apply_of_nonpos q u f h.le, ha, coeff_plethShift_C,
      ite_eq_right (by omega : ¬ (-(lastExp γ)).toNat = 0), padFamily, ite_eq_right (by omega)]
  · rw [shiftExtend_apply_of_nonpos q u f h.le, ha, coeff_plethShift_C,
      ite_eq_left (by omega : (-(lastExp γ)).toNat = 0), padFamily, ite_eq_left h, ha]
  · rw [shiftExtend_eq_zero_of_pos q u f h, padFamily, ite_eq_right (by omega)]

/-- **The displacement in the last variable stays in the ring.** The new last exponent `n` at an
`α` in the support of `f` is bounded below by `-(N + coordSum α)`, because a nonzero coefficient
of `w^(-n)` in `δ (f α)` forces `-n` to be at most the degree bound of `f α`; so the partial sums
of `(α, n)` are bounded below by those of `snocPsumExp β (-N)`. -/
@[hjo "lem_bglx_shift_extend_target"]
theorem isConeBounded_shiftExtend (q u : K) {f : Family k (Lambda K)} (hcb : IsConeBounded 1 f)
    (hdc : IsDegreeControlled f) : IsConeBounded 1 (shiftExtend q u f) := by
  rw [isConeBounded_iff] at hcb ⊢
  obtain ⟨β, hβ⟩ := hcb
  obtain ⟨N, hN⟩ := hdc
  refine ⟨snocPsumExp β (-N), fun γ hγ j => ?_⟩
  have hlast : lastExp γ ≤ 0 := by
    by_contra hc
    exact hγ (shiftExtend_eq_zero_of_pos q u f (by omega))
  rw [shiftExtend_apply_of_nonpos q u f hlast] at hγ
  have hf0 : f (initExp γ) ≠ 0 := by
    intro h
    rw [h, map_zero, Polynomial.coeff_zero] at hγ
    exact hγ rfl
  have hm : (((-(lastExp γ)).toNat : ℕ) : ℤ) ≤ N + coordSum (initExp γ) := by
    by_contra hc
    exact hγ (coeff_plethShift_eq_zero_of_DegLEZ q u (hN (initExp γ)) (by omega))
  by_cases hj : j ≤ k
  · rw [psum_snocPsumExp_of_le β (-N) hj, psum_one_initExp _ hj]
    exact hβ _ hf0 j
  · have h1 : psum 1 γ j = coordSum γ := by
      rw [psum_eq_psum_of_le (show k + 1 ≤ j by omega), psum_one_eq_coordSum]
    have h2 : psum 1 (snocPsumExp β (-N)) j = -N := by
      rw [psum_eq_psum_of_le (show k + 1 ≤ j by omega), psum_snocPsumExp_last]
    rw [h1, h2, coordSum_eq_coordSum_initExp_add_lastExp γ]
    have hmn : (((-(lastExp γ)).toNat : ℕ) : ℤ) = -(lastExp γ) := Int.toNat_of_nonneg (by omega)
    omega

/-- The displacement in the last variable preserves degree control with the same bound: the
coefficient at `(α, n)` has degree at most `(N + coordSum α) + n = N + coordSum (α, n)`. -/
@[hjo "lem_bglx_shift_extend_target"]
theorem isDegreeControlled_shiftExtend (q u : K) {f : Family k (Lambda K)}
    (hdc : IsDegreeControlled f) : IsDegreeControlled (shiftExtend q u f) := by
  obtain ⟨N, hN⟩ := hdc
  refine ⟨N, fun γ => ?_⟩
  by_cases hlast : lastExp γ ≤ 0
  · rw [shiftExtend_apply_of_nonpos q u f hlast]
    refine DegLEZ_mono (le_of_eq ?_)
      (DegLEZ_coeff_plethShift q u (hN (initExp γ)) (-(lastExp γ)).toNat)
    rw [coordSum_eq_coordSum_initExp_add_lastExp γ]
    have hmn : (((-(lastExp γ)).toNat : ℕ) : ℤ) = -(lastExp γ) := Int.toNat_of_nonneg (by omega)
    omega
  · rw [shiftExtend_eq_zero_of_pos q u f (by omega)]
    exact DegLEZ_zero

/-! ### Multiplicativity of the displacement in the last variable -/

/-- The displacement in the last variable, as an element of the cone ring. -/
noncomputable def shiftExtendElem (q u : K) (x : ConeRing k 1 (Lambda K))
    (h : IsDegreeControlled x.coeff) : ConeRing (k + 1) 1 (Lambda K) where
  coeff := shiftExtend q u x.coeff
  isConeBounded := isConeBounded_shiftExtend q u x.isConeBounded h

@[simp] lemma coeff_shiftExtendElem (q u : K) (x : ConeRing k 1 (Lambda K))
    (h : IsDegreeControlled x.coeff) :
    (shiftExtendElem q u x h).coeff = shiftExtend q u x.coeff := rfl

/-- **The displacement in the last variable multiplies.** At `(α, n)` with `n ≤ 0` both sides are
the double sum over `α' + α'' = α` and `n' + n'' = n` of the product of the coefficients of
`w^(-n')` in `δ(x_{α'})` and of `w^(-n'')` in `δ(y_{α''})`: on the left by the multiplicativity of
`δ` and `Polynomial.coeff_mul`, on the right by the convolution of the cone ring over the image of
`s ×ˢ range (m+1)` under `snocExp`. -/
@[hjo "lem_bglx_shift_extend_mult"]
theorem shiftExtendElem_mul (q u : K) (x y : ConeRing k 1 (Lambda K))
    (hx : IsDegreeControlled x.coeff) (hy : IsDegreeControlled y.coeff) :
    shiftExtendElem q u (x * y) (isDegreeControlled_mul hx hy)
      = shiftExtendElem q u x hx * shiftExtendElem q u y hy := by
  classical
  refine ConeRing.ext (funext fun γ => ?_)
  by_cases hn : lastExp γ ≤ 0
  · -- the interesting case: the double sums match termwise
    have hsub : ConeRing.convSupport x y (initExp γ)
        ⊆ ↑(ConeRing.finite_convSupport x y (initExp γ)).toFinset := by
      rw [Set.Finite.coe_toFinset]
    have hL : (shiftExtendElem q u (x * y) (isDegreeControlled_mul hx hy)).coeff γ
        = ∑ α' ∈ (ConeRing.finite_convSupport x y (initExp γ)).toFinset,
            ∑ b ∈ Finset.range ((-(lastExp γ)).toNat + 1),
              Polynomial.coeff (plethShift q u (x.coeff α')) b *
                Polynomial.coeff (plethShift q u (y.coeff (initExp γ - α')))
                  ((-(lastExp γ)).toNat - b) := by
      simp only [coeff_shiftExtendElem]
      rw [shiftExtend_apply_of_nonpos q u _ hn,
        ConeRing.coeff_mul_of_subset x y (initExp γ) _ hsub, map_sum,
        Polynomial.finsetSum_coeff]
      refine Finset.sum_congr rfl fun α' _ => ?_
      rw [map_mul, Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    have hinj : ∀ p ∈ (ConeRing.finite_convSupport x y (initExp γ)).toFinset ×ˢ
          Finset.range ((-(lastExp γ)).toNat + 1),
        ∀ p' ∈ (ConeRing.finite_convSupport x y (initExp γ)).toFinset ×ˢ
          Finset.range ((-(lastExp γ)).toNat + 1),
        snocExp p.1 (-(p.2 : ℤ)) = snocExp p'.1 (-(p'.2 : ℤ)) → p = p' := by
      intro p _ p' _ h
      have h1 : p.1 = p'.1 := by
        have h' := congrArg initExp h
        rwa [initExp_snocExp, initExp_snocExp] at h'
      have h2 : p.2 = p'.2 := by
        have h' := congrArg lastExp h
        rw [lastExp_snocExp, lastExp_snocExp] at h'
        omega
      exact Prod.ext h1 h2
    have hS : ConeRing.convSupport (shiftExtendElem q u x hx) (shiftExtendElem q u y hy) γ
        ⊆ ↑(((ConeRing.finite_convSupport x y (initExp γ)).toFinset ×ˢ
            Finset.range ((-(lastExp γ)).toNat + 1)).image
              fun p => snocExp p.1 (-(p.2 : ℤ))) := by
      rintro γ' ⟨h1, h2⟩
      simp only [coeff_shiftExtendElem] at h1 h2
      have hl1 : lastExp γ' ≤ 0 := by
        by_contra hc
        exact h1 (shiftExtend_eq_zero_of_pos q u _ (by omega))
      have hl2 : lastExp (γ - γ') ≤ 0 := by
        by_contra hc
        exact h2 (shiftExtend_eq_zero_of_pos q u _ (by omega))
      rw [shiftExtend_apply_of_nonpos q u _ hl1] at h1
      rw [shiftExtend_apply_of_nonpos q u _ hl2, initExp_sub] at h2
      have hx0 : x.coeff (initExp γ') ≠ 0 := by
        intro h
        rw [h, map_zero, Polynomial.coeff_zero] at h1
        exact h1 rfl
      have hy0 : y.coeff (initExp γ - initExp γ') ≠ 0 := by
        intro h
        rw [h, map_zero, Polynomial.coeff_zero] at h2
        exact h2 rfl
      rw [lastExp_sub] at hl2
      refine Finset.mem_coe.2 (Finset.mem_image.2
        ⟨(initExp γ', (-(lastExp γ')).toNat), Finset.mem_product.2 ⟨?_, ?_⟩, ?_⟩)
      · exact Set.Finite.mem_toFinset _ |>.2 ⟨hx0, hy0⟩
      · exact Finset.mem_range.2 (by omega)
      · rw [Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ -lastExp γ'), neg_neg, snocExp_initExp]
    have hR : (shiftExtendElem q u x hx * shiftExtendElem q u y hy).coeff γ
        = ∑ α' ∈ (ConeRing.finite_convSupport x y (initExp γ)).toFinset,
            ∑ b ∈ Finset.range ((-(lastExp γ)).toNat + 1),
              Polynomial.coeff (plethShift q u (x.coeff α')) b *
                Polynomial.coeff (plethShift q u (y.coeff (initExp γ - α')))
                  ((-(lastExp γ)).toNat - b) := by
      rw [ConeRing.coeff_mul_of_subset _ _ _ _ hS, Finset.sum_image hinj, Finset.sum_product]
      refine Finset.sum_congr rfl fun α' _ => Finset.sum_congr rfl fun b hb => ?_
      rw [Finset.mem_range] at hb
      simp only [coeff_shiftExtendElem]
      have hsnd : γ - snocExp α' (-(b : ℤ)) = snocExp (initExp γ - α') (lastExp γ + b) := by
        rw [← snocExp_initExp (γ - snocExp α' (-(b : ℤ))), initExp_sub, lastExp_sub,
          initExp_snocExp, lastExp_snocExp, sub_neg_eq_add]
      rw [shiftExtend_snocExp q u x.coeff α' (by omega : -(b : ℤ) ≤ 0), hsnd,
        shiftExtend_snocExp q u y.coeff _ (by omega : lastExp γ + b ≤ 0),
        show (-(-(b : ℤ))).toNat = b from by omega,
        show (-(lastExp γ + b)).toNat = (-(lastExp γ)).toNat - b from by omega]
    rw [hL, hR]
  · -- no positive power of the new variable occurs on either side
    have hsub : ConeRing.convSupport (shiftExtendElem q u x hx) (shiftExtendElem q u y hy) γ
        ⊆ ↑(ConeRing.finite_convSupport (shiftExtendElem q u x hx)
            (shiftExtendElem q u y hy) γ).toFinset := by
      rw [Set.Finite.coe_toFinset]
    rw [ConeRing.coeff_mul_of_subset _ _ _ _ hsub]
    simp only [coeff_shiftExtendElem]
    rw [shiftExtend_eq_zero_of_pos q u _ (by omega : 0 < lastExp γ)]
    refine (Finset.sum_eq_zero fun γ' _ => ?_).symm
    by_cases hl : lastExp γ' ≤ 0
    · rw [shiftExtend_eq_zero_of_pos q u y.coeff
        (by rw [lastExp_sub]; omega : 0 < lastExp (γ - γ')), mul_zero]
    · rw [shiftExtend_eq_zero_of_pos q u x.coeff (by omega), zero_mul]

end HJO.Bglx
