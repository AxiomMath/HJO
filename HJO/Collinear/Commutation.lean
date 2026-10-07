/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Evaluation.CollinearNarrowed
public import HJO.Collinear.SplitSteps
public import HJO.Collinear.Vocabulary
public meta import HJO.Attr

/-! # The slope operators under the two Euclidean steps, and the collinear commutation

The recursion of `Sym.Qop` is naturally stated uniformly, on the split of the primitive pair
of `(m, n)`, and the two branches of the Lean definition -- the coprime one, which runs the
bounded search on `(m, n)` itself, and the noncoprime one, which runs it on the primitive pair --
agree there. `Sym.qop_rec` is that uniform recursion, and every induction in this file is an
induction along it.

Two of those inductions need no analytic input at all. Every slope operator lies in the algebra
`𝖠` the basic operators generate, because the recursion only ever forms `L`-linear combinations
and products of operators of smaller first index; and an index shift, being an `L`-algebra
endomorphism of `𝖠`, carries `Q_{m,n}` to `Q_{m,n+m}`, because the split of `(m, n + m)` is the
split of `(m, n)` under the second Euclidean step.

The other step of the lattice, `(m, n) ↦ (m + n, n)`, is realised by conjugation with a Macdonald
conjugator, and that does need one identity about the basic operators: the commutator of `D_k`
with multiplication by `e₁` is `M D_{k+1}`. It is proved here from the displacement being an
algebra homomorphism, and it is the only analytic input below. Since the conjugation induction
divides by `M = (1 - q)(1 - u)`, every statement on that side carries the hypothesis `M ≠ 0`,
which is invisible at generic parameters -- at `u = 1` the slope
operators above width one all vanish, so the hypothesis cannot be dropped.

The file ends with the Euclidean descent that the two steps drive: collinear slope operators
commute, given a conjugator, an index shift, and the diagonal base case `Q_{k,k}` against
`Q_{l,l}`. All three are hypotheses: the two existence statements are separate chains, and the
diagonal case rests on identifying `Q_{k,k}` with a conjugate of multiplication by the axis
generator, which is done in `HJO.Sym.qop_diag_commute`.
-/

@[expose] public section

namespace HJO.Sym

variable {L : Type*} [Field L] [Algebra ℚ L]

/-! ### The recursion of `Qop`, uniformly on both branches -/

/-- **The recursion for `Qop`, on both branches at once.** For `m ≥ 2` and `n ≥ 1`,
writing `(r, s)` for the split `slopeSplit m n` of the primitive pair of `(m, n)`,

  `Q_{m,n} = M⁻¹ (Q_{m-r,n-s} Q_{r,s} - Q_{r,s} Q_{m-r,n-s})`,   `M = (1 - q)(1 - u)`.

On the noncoprime branch this is the definition; on the coprime branch the primitive pair is
`(m, n)` itself and its primitive split is the bounded search, which is what that branch runs. -/
@[hjo "lem_qop_rec"]
theorem qop_rec (q u : L) {m n : ℕ} (hm : 1 < m) (hn : 0 < n) :
    Qop q u m n = ((1 - q) * (1 - u))⁻¹ •
      (Qop q u (m - (slopeSplit m n).1) (n - (slopeSplit m n).2) *
          Qop q u (slopeSplit m n).1 (slopeSplit m n).2 -
        Qop q u (slopeSplit m n).1 (slopeSplit m n).2 *
          Qop q u (m - (slopeSplit m n).1) (n - (slopeSplit m n).2)) := by
  by_cases h : Nat.Coprime m n
  · rw [slopeSplit_eq_split hm h]
    exact qop_of_coprime q u hm h
  · exact qop_eq_bracket q u hm hn h

/-! ### The slope operators lie in the operator algebra -/

/-- **The slope operators lie in the operator algebra.** For `m ≥ 1` and `n ≥ 0` with `n ≥ 1` or
`m = 1`, the slope operator `Q_{m,n}` lies in `𝖠`. The base case `Q_{1,n} = D_n` is a generator,
and the recursive case is a scalar multiple of a difference of products of two slope operators of
smaller first index, both of which stay inside the domain: the complementary pair `(m - r, n - s)`
has `n - s ≥ 1`, and the split pair `(r, s)` has `s ≥ 1` unless `s = 0`, in which case `r = 1`. -/
@[hjo "lem_qop_in_algebra"]
theorem qop_mem_dopAlgebra (q u : L) : ∀ m : ℕ, 0 < m → ∀ n : ℕ, (0 < n ∨ m = 1) →
    Qop q u m n ∈ DopAlgebra q u := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm n hn
    rcases Nat.lt_or_ge m 2 with h1 | h1
    · rw [qop_of_le_one q u n (by omega)]
      exact dop_mem_dopAlgebra q u n
    · have hm1 : 1 < m := by omega
      have hn1 : 0 < n := by omega
      obtain ⟨hr1, hrm⟩ := one_le_slopeSplit_fst_lt hm1 hn1
      have he := one_le_sub_slopeSplit_snd hm1 hn1
      have hmem2 : Qop q u (slopeSplit m n).1 (slopeSplit m n).2 ∈ DopAlgebra q u := by
        refine ih _ hrm hr1 _ ?_
        rcases Nat.eq_zero_or_pos (slopeSplit m n).2 with hs | hs
        · exact Or.inr (slopeSplit_fst_eq_one hm1 hn1 hs)
        · exact Or.inl hs
      have hmem1 : Qop q u (m - (slopeSplit m n).1) (n - (slopeSplit m n).2) ∈ DopAlgebra q u :=
        ih _ (by omega) (by omega) _ (Or.inl (by omega))
      rw [qop_rec q u hm1 hn1]
      exact Subalgebra.smul_mem _ (Subalgebra.sub_mem _ (Subalgebra.mul_mem _ hmem1 hmem2)
        (Subalgebra.mul_mem _ hmem2 hmem1)) _

/-! ### The index shift realises the second Euclidean step -/

/-- The engine of `qop_shift_right`: stated for an arbitrary element of `𝖠` representing
`Q_{m,n}`, which is the form the induction consumes, the coercion being injective. -/
theorem qop_shift_right_aux {q u : L} {S : DopAlgebra q u →ₐ[L] DopAlgebra q u}
    (hS : IsIndexShift q u S) :
    ∀ m : ℕ, 0 < m → ∀ n : ℕ, (0 < n ∨ m = 1) → ∀ x : DopAlgebra q u,
      (x : Module.End L (Lambda L)) = Qop q u m n →
        (S x : Module.End L (Lambda L)) = Qop q u m (n + m) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm n hn x hx
    rcases Nat.lt_or_ge m 2 with h1 | h1
    · -- width one: the shift sends the generator `D_n` to `D_{n+1}`
      have hm1 : m = 1 := by omega
      subst hm1
      have hxd : x = dopGen q u n := Subtype.ext (by rw [hx, dopGen_coe, qop_one])
      rw [hxd, hS n, dopGen_coe, qop_one]
    · have hm1 : 1 < m := by omega
      have hn1 : 0 < n := by omega
      obtain ⟨hr1, hrm⟩ := one_le_slopeSplit_fst_lt hm1 hn1
      have he := one_le_sub_slopeSplit_snd hm1 hn1
      have hsn : (slopeSplit m n).2 < n := by omega
      -- the two halves of the split, as elements of the algebra
      have hmem2 : Qop q u (slopeSplit m n).1 (slopeSplit m n).2 ∈ DopAlgebra q u := by
        refine qop_mem_dopAlgebra q u _ hr1 _ ?_
        rcases Nat.eq_zero_or_pos (slopeSplit m n).2 with hs | hs
        · exact Or.inr (slopeSplit_fst_eq_one hm1 hn1 hs)
        · exact Or.inl hs
      have hmem1 : Qop q u (m - (slopeSplit m n).1) (n - (slopeSplit m n).2) ∈ DopAlgebra q u :=
        qop_mem_dopAlgebra q u _ (by omega) _ (Or.inl (by omega))
      set y : DopAlgebra q u := ⟨_, hmem1⟩ with hy
      set z : DopAlgebra q u := ⟨_, hmem2⟩ with hz
      -- the shift on each half, by the inductive hypothesis
      have hSy : (S y : Module.End L (Lambda L)) =
          Qop q u (m - (slopeSplit m n).1)
            (n - (slopeSplit m n).2 + (m - (slopeSplit m n).1)) :=
        ih _ (by omega) (by omega) _ (Or.inl (by omega)) y rfl
      have hSz : (S z : Module.End L (Lambda L)) =
          Qop q u (slopeSplit m n).1 ((slopeSplit m n).2 + (slopeSplit m n).1) := by
        refine ih _ hrm hr1 _ ?_ z rfl
        rcases Nat.eq_zero_or_pos (slopeSplit m n).2 with hs | hs
        · exact Or.inr (slopeSplit_fst_eq_one hm1 hn1 hs)
        · exact Or.inl hs
      -- `x` is the normalised commutator of the two halves
      have hxeq : x = ((1 - q) * (1 - u))⁻¹ • (y * z - z * y) :=
        Subtype.ext (by rw [hx, qop_rec q u hm1 hn1]; rfl)
      -- the recursion at the stepped slope: its split is `(r, r + s)`
      have hidx : n + m - ((slopeSplit m n).1 + (slopeSplit m n).2) =
          n - (slopeSplit m n).2 + (m - (slopeSplit m n).1) := by omega
      have hcomm : (slopeSplit m n).1 + (slopeSplit m n).2 =
          (slopeSplit m n).2 + (slopeSplit m n).1 := Nat.add_comm _ _
      have key : S (y * z - z * y) = S y * S z - S z * S y := by
        have h := map_sub S (y * z) (z * y)
        rw [map_mul, map_mul] at h
        exact h
      rw [hxeq, map_smul, key, qop_rec q u hm1 (show 0 < n + m by omega),
        slopeSplit_right (by omega) hn1]
      dsimp only
      rw [hidx, hcomm]
      simp only [SetLike.val_smul, AddSubgroupClass.coe_sub, MulMemClass.coe_mul, hSy, hSz]

/-- **The index shift realises the second step.** An index shift `𝖲` sends `Q_{m,n}` to
`Q_{m,n+m}`, for `m ≥ 1` and `n ≥ 0` with `n ≥ 1` or `m = 1`. At width one this is the defining
property of the shift, `D_n ↦ D_{n+1}`; in the recursive case the split of `(m, n + m)` is
`(r, r + s)` by `slopeSplit_right`, the complementary pair is `(m - r, (n - s) + (m - r))`, and the
shift, being an `L`-algebra endomorphism, commutes with the normalised commutator. -/
@[hjo "lem_qop_shift_right"]
theorem qop_shift_right {q u : L} {S : DopAlgebra q u →ₐ[L] DopAlgebra q u}
    (hS : IsIndexShift q u S) {m : ℕ} (hm : 0 < m) {n : ℕ} (hn : 0 < n ∨ m = 1) :
    (S ⟨Qop q u m n, qop_mem_dopAlgebra q u m hm n hn⟩ : Module.End L (Lambda L)) =
      Qop q u m (n + m) :=
  qop_shift_right_aux hS m hm n hn _ rfl

/-! ### The pairing against a displaced product -/

section Pairing

variable {K : Type*} [CommRing K]

/-- Pairing a monomial in `w = z⁻¹` against a family of symmetric functions picks out the member
matching its degree. -/
theorem coeffPairing_monomial (c : ℕ → Lambda K) (k : ℕ) (b : Lambda K) :
    coeffPairing c (Polynomial.monomial k b) = b * c k := by
  change (Polynomial.monomial k b).sum (fun j A => A * c j) = b * c k
  exact Polynomial.sum_monomial_index b _ (by simp)

/-- A symmetric function not involving `w` factors out of the pairing. -/
theorem coeffPairing_C_mul (c : ℕ → Lambda K) (g : Lambda K) (P : Polynomial (Lambda K)) :
    coeffPairing c (Polynomial.C g * P) = g * coeffPairing c P := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => rw [mul_add, map_add, map_add, hP, hQ, mul_add]
  | monomial k b =>
    rw [Polynomial.C_mul_monomial, coeffPairing_monomial, coeffPairing_monomial, mul_assoc]

/-- **One power of `w` shifts the family by one.** Extracting the coefficient of `zᵏ` from
`z⁻¹ g` is extracting the coefficient of `z^{k+1}` from `g`. -/
theorem coeffPairing_X_mul (c : ℕ → Lambda K) (P : Polynomial (Lambda K)) :
    coeffPairing c (Polynomial.X * P) = coeffPairing (fun j => c (j + 1)) P := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => rw [mul_add, map_add, map_add, hP, hQ]
  | monomial k b => rw [Polynomial.X_mul_monomial, coeffPairing_monomial, coeffPairing_monomial]

end Pairing

/-! ### The basic operators against multiplication by `e₁` -/

-- `elemSymm_one_eq_X` is the content of `HJO.Sym.elemSymm_one`, and `elemSymm_zero_eq_one` is
-- immediate from the definition. Both are reproved here rather than imported: the existing copies
-- `HJO.DopCommutator.elemSymm_zero` and `HJO.DopCommutator.elemSymm_one` sit behind the
-- differential-order and multiplication machinery this file does not depend on.
-- `coeffPairing_monomial` above likewise repeats `HJO.CopPower.coeffPairing_monomial`, which sits
-- behind the creation-operator machinery; when either moves into
-- `HJO.Symmetric.SymmetricFunctions`, next to the definitions they are about, these copies should
-- go.

/-- The elementary symmetric function of degree zero is `1`. -/
theorem elemSymm_zero_eq_one : elemSymm L 0 = 1 := by rw [elemSymm]

/-- The elementary symmetric function of degree one is the first power sum, the generator of
index zero. -/
theorem elemSymm_one_eq_X : elemSymm L 1 = MvPolynomial.X 0 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, elemSymm]
  simp [powerSum, elemSymm_zero_eq_one]

/-- The basic operator as the pairing it is, evaluated at an element. -/
theorem dop_apply (q u : L) (k : ℕ) (f : Lambda L) :
    Dop q u k f =
      coeffPairing (fun j => (-1) ^ (k + j) * elemSymm L (k + j)) (plethShift q u f) := rfl

/-- **The displacement of the first elementary symmetric function.**
`e₁[X + M/z] = e₁ + M z⁻¹`. The minus sign of the alphabet is not squared, so the scalar is
`M = (1 - q)(1 - u)` itself. -/
@[hjo "lem_shift_e1"]
theorem plethShift_elemSymm_one (q u : L) :
    plethShift q u (elemSymm L 1) =
      Polynomial.C (elemSymm L 1) +
        Polynomial.C (MvPolynomial.C ((1 - q) * (1 - u))) * Polynomial.X := by
  rw [elemSymm_one_eq_X, plethShift, MvPolynomial.aeval_X]
  simp [powerSum]

/-- **The basic operators against multiplication by `e₁`.** For every `k ≥ 0` and every
`f ∈ Λ`, `D_k(e₁ f) = e₁ D_k f + M D_{k+1} f`. The displacement is an algebra map, so it turns the
product into `(e₁ + M z⁻¹) f[X + M/z]`; the first summand contributes `e₁ D_k f`, and the single
power of `z⁻¹` in the second shifts the extracted coefficient from `zᵏ` to `z^{k+1}`. -/
@[hjo "lem_dop_e1"]
theorem dop_elemSymm_one_mul (q u : L) (k : ℕ) (f : Lambda L) :
    Dop q u k (elemSymm L 1 * f) =
      elemSymm L 1 * Dop q u k f + ((1 - q) * (1 - u)) • Dop q u (k + 1) f := by
  have hfam : (fun j => (-1 : Lambda L) ^ (k + (j + 1)) * elemSymm L (k + (j + 1))) =
      fun j => (-1 : Lambda L) ^ (k + 1 + j) * elemSymm L (k + 1 + j) := by
    funext j
    rw [show k + (j + 1) = k + 1 + j by omega]
  rw [dop_apply, dop_apply, dop_apply, map_mul, plethShift_elemSymm_one, add_mul, map_add,
    mul_assoc, coeffPairing_C_mul, coeffPairing_C_mul, coeffPairing_X_mul, hfam,
    MvPolynomial.smul_eq_C_mul]

attribute [hjo "lem_ght_dop_zero_e1"] dop_elemSymm_one_mul

/-! ### The recursion on the ray below the diagonal -/

/-- **The recursion on the ray below the diagonal.** For `k ≥ 1`,
`Q_{k+1,k} = M⁻¹ (D_1 Q_{k,k-1} - Q_{k,k-1} D_1)`. The pair `(k + 1, k)` is coprime with split
`(k, k - 1)`, so its complementary pair is `(1, 1)` and `Q_{1,1} = D_1`. -/
@[hjo "lem_qop_upper_rec"]
theorem qop_upper_rec (q u : L) {k : ℕ} (hk : 1 ≤ k) :
    Qop q u (k + 1) k = ((1 - q) * (1 - u))⁻¹ •
      (Dop q u 1 * Qop q u k (k - 1) - Qop q u k (k - 1) * Dop q u 1) := by
  have h1 : k + 1 - k = 1 := by omega
  have h2 : k - (k - 1) = 1 := by omega
  rw [qop_rec q u (by omega) (by omega), slopeSplit_succ_self hk]
  dsimp only
  rw [h1, h2, qop_one]

/-! ### Conjugation by a Macdonald conjugator -/

section Conjugator

variable {q u : L} {nabla : Module.End L (Lambda L)}

/-- The conjugator read backwards on the second of its three equations: `D_1(∇ f) = -∇(e₁ f)`. -/
theorem IsMacdonaldConjugator.dop_one_apply (h : IsMacdonaldConjugator q u nabla) (f : Lambda L) :
    Dop q u 1 (nabla f) = -nabla (elemSymm L 1 * f) := by
  rw [h.map_elemSymm_one_mul f, neg_neg]

/-- **The ray below the diagonal is a conjugate, inverse-free form.** For every `k ≥ 0` and every
`f ∈ Λ`, `Q_{k+1,k}(∇ f) = ∇(D_k f)`. Induction on `k`: at `k = 0` this is the conjugator's
commutation with `D_0`, and the step feeds the commutator identity
`D_k(e₁ f) = e₁ D_k f + M D_{k+1} f` of `HJO.Sym.dop_elemSymm_one_mul` through the recursion
`Q_{k+2,k+1} = M⁻¹(D_1 Q_{k+1,k} - Q_{k+1,k} D_1)`, the conjugator turning multiplication by `e₁`
into `-D_1`. Dividing by `M` is where the hypothesis `M ≠ 0` enters. -/
theorem qop_succ_apply_nabla (h : IsMacdonaldConjugator q u nabla)
    (hM : (1 - q) * (1 - u) ≠ 0) :
    ∀ (k : ℕ) (f : Lambda L), Qop q u (k + 1) k (nabla f) = nabla (Dop q u k f) := by
  have hcancel : ∀ X Y : Lambda L, -X - -(X + Y) = Y := fun X Y => by abel
  intro k
  induction k with
  | zero =>
    intro f
    rw [qop_one]
    exact (h.map_dop_zero f).symm
  | succ k ih =>
    intro f
    have hsucc : k + 1 - 1 = k := by omega
    have hq := LinearMap.congr_fun (qop_upper_rec q u (show 1 ≤ k + 1 by omega)) (nabla f)
    rw [hsucc] at hq
    simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.mul_apply] at hq
    rw [hq, ih f, h.dop_one_apply (Dop q u k f), h.dop_one_apply f, map_neg,
      ih (elemSymm L 1 * f), dop_elemSymm_one_mul q u k f, map_add, map_smul, hcancel,
      smul_smul, inv_mul_cancel₀ hM, one_smul]

/-- **The ray below the diagonal is a conjugate.** For a Macdonald conjugator `∇` with `M ≠ 0`,
every `k ≥ 0` and every `f ∈ Λ`, `Q_{k+1,k} f = ∇(D_k(∇⁻¹ f))`. -/
@[hjo "lem_conj_phi"]
theorem conj_phi (h : IsMacdonaldConjugator q u nabla) (hM : (1 - q) * (1 - u) ≠ 0) (k : ℕ)
    (f : Lambda L) :
    Qop q u (k + 1) k f =
      nabla (Dop q u k ((LinearEquiv.ofBijective nabla h.bijective).symm f)) := by
  have hf : nabla ((LinearEquiv.ofBijective nabla h.bijective).symm f) = f :=
    (LinearEquiv.ofBijective nabla h.bijective).apply_symm_apply f
  have hk := qop_succ_apply_nabla h hM k ((LinearEquiv.ofBijective nabla h.bijective).symm f)
  rwa [hf] at hk

/-- **Conjugation realises the first step, inverse-free form.** For all `m ≥ 1`, `n ≥ 1` and every
`f ∈ Λ`, `Q_{m+n,n}(∇ f) = ∇(Q_{m,n} f)`. Strong induction on `m`: at `m = 1` this is
`qop_succ_apply_nabla` at `k = n`, and in the recursive case the split of `(m + n, n)` is
`(r + s, s)` by `slopeSplit_up`, its complementary pair is `((m - r) + (n - s), n - s)`, and the
inductive hypothesis applies to both halves -- to `(r, s)` at `s = 0` through the conjugator's
commutation with `D_0`, since then `r = 1` and both slope operators are `D_0`. -/
theorem qop_add_apply_nabla (h : IsMacdonaldConjugator q u nabla) (hM : (1 - q) * (1 - u) ≠ 0) :
    ∀ m : ℕ, 0 < m → ∀ n : ℕ, 0 < n → ∀ f : Lambda L,
      Qop q u (m + n) n (nabla f) = nabla (Qop q u m n f) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm n hn f
    rcases Nat.lt_or_ge m 2 with h1 | h1
    · have hm1 : m = 1 := by omega
      subst hm1
      rw [qop_one, Nat.add_comm 1 n]
      exact qop_succ_apply_nabla h hM n f
    · have hm1 : 1 < m := by omega
      obtain ⟨hr1, hrm⟩ := one_le_slopeSplit_fst_lt hm1 hn
      have he := one_le_sub_slopeSplit_snd hm1 hn
      have hsn : (slopeSplit m n).2 < n := by omega
      -- the inductive hypothesis on the complementary pair
      have hc : ∀ g : Lambda L,
          Qop q u (m - (slopeSplit m n).1 + (n - (slopeSplit m n).2))
              (n - (slopeSplit m n).2) (nabla g) =
            nabla (Qop q u (m - (slopeSplit m n).1) (n - (slopeSplit m n).2) g) :=
        ih _ (by omega) (by omega) _ (by omega)
      -- and on the split pair, the boundary `s = 0` being the conjugator's commutation with `D_0`
      have hr : ∀ g : Lambda L,
          Qop q u ((slopeSplit m n).1 + (slopeSplit m n).2) (slopeSplit m n).2 (nabla g) =
            nabla (Qop q u (slopeSplit m n).1 (slopeSplit m n).2 g) := by
        rcases Nat.eq_zero_or_pos (slopeSplit m n).2 with hs | hs
        · intro g
          rw [hs, slopeSplit_fst_eq_one hm1 hn hs, Nat.add_zero, qop_one]
          exact (h.map_dop_zero g).symm
        · exact ih _ hrm hr1 _ hs
      have hidx : m + n - ((slopeSplit m n).1 + (slopeSplit m n).2) =
          m - (slopeSplit m n).1 + (n - (slopeSplit m n).2) := by omega
      have hq := LinearMap.congr_fun
        (qop_rec q u (show 1 < m + n by omega) hn) (nabla f)
      rw [slopeSplit_up (by omega) hn] at hq
      dsimp only at hq
      rw [hidx] at hq
      simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.mul_apply] at hq
      have hf := LinearMap.congr_fun (qop_rec q u hm1 hn) f
      simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.mul_apply] at hf
      rw [hq, hr f, hc f, hc _, hr _, hf, map_smul, map_sub]

/-- **Conjugation realises the first step.** For a Macdonald conjugator `∇` with `M ≠ 0`, all
`m ≥ 1` and `n ≥ 1` and every `f ∈ Λ`, `Q_{m+n,n} f = ∇(Q_{m,n}(∇⁻¹ f))`. -/
@[hjo "lem_qop_conj_up"]
theorem qop_conj_up (h : IsMacdonaldConjugator q u nabla) (hM : (1 - q) * (1 - u) ≠ 0)
    {m : ℕ} (hm : 0 < m) {n : ℕ} (hn : 0 < n) (f : Lambda L) :
    Qop q u (m + n) n f =
      nabla (Qop q u m n ((LinearEquiv.ofBijective nabla h.bijective).symm f)) := by
  have hf : nabla ((LinearEquiv.ofBijective nabla h.bijective).symm f) = f :=
    (LinearEquiv.ofBijective nabla h.bijective).apply_symm_apply f
  have hk := qop_add_apply_nabla h hM m hm n hn
    ((LinearEquiv.ofBijective nabla h.bijective).symm f)
  rwa [hf] at hk

end Conjugator

/-! ### The collinear commutation

The Euclidean descent of the argument. What it needs, beyond the two structural data,
is the diagonal base case: the descent subtracts the smaller coordinate from the larger, so a
coprime pair reaches `(1, 1)`, and there neither Euclidean step applies. The diagonal case is
`HJO.Sym.qop_diag_commute`, whose proof identifies `Q_{k,k}` with a conjugate of
multiplication by the axis generator `U_k`; that identification is
taken here as a hypothesis, exactly like the existence of the two structural data.
-/

section Collinear

variable {q u : L}

/-- **The collinear slope operators commute**, given a Macdonald conjugator, an index shift and
the diagonal base case. Strong induction on `a + b`: at `a = b` coprimality forces `a = b = 1` and
the claim is the diagonal hypothesis; at `a > b` the pair `(a - b, b)` is coprime with smaller sum
and `Q_{ka,kb}` is the `∇`-conjugate of `Q_{k(a-b),kb}` by `qop_add_apply_nabla`, so conjugating
the inductive commutation by the bijective `∇` gives the claim; at `a < b` the pair `(a, b - a)` is
coprime with smaller sum and `𝖲` carries `Q_{ka,k(b-a)}` to `Q_{ka,kb}` by `qop_shift_right`, so
applying the multiplicative `𝖲` to the inductive commutation inside `𝖠` gives the claim.

Only the two forward steps are used, and `∇⁻¹` occurs only through the conjugation: nothing here
needs an action of `SL₂(ℤ)`. -/
theorem collinear_commute_of_diag (hM : (1 - q) * (1 - u) ≠ 0)
    (hconj : ∃ nabla : Module.End L (Lambda L), IsMacdonaldConjugator q u nabla)
    (hshift : ∃ S : DopAlgebra q u →ₐ[L] DopAlgebra q u, IsIndexShift q u S)
    (hdiag : ∀ k l : ℕ, 0 < k → 0 < l → Commute (Qop q u k k) (Qop q u l l)) :
    ∀ a b : ℕ, Nat.Coprime a b → 0 < a → 0 < b → ∀ k l : ℕ, 0 < k → 0 < l →
      Commute (Qop q u (k * a) (k * b)) (Qop q u (l * a) (l * b)) := by
  obtain ⟨nabla, h⟩ := hconj
  obtain ⟨S, hS⟩ := hshift
  suffices H : ∀ N a b : ℕ, a + b ≤ N → Nat.Coprime a b → 0 < a → 0 < b →
      ∀ k l : ℕ, 0 < k → 0 < l →
        Commute (Qop q u (k * a) (k * b)) (Qop q u (l * a) (l * b)) from
    fun a b hab ha hb k l hk hl => H (a + b) a b le_rfl hab ha hb k l hk hl
  intro N
  induction N with
  | zero =>
    intro a b hN _ ha hb
    omega
  | succ N ih =>
    intro a b hN hab ha hb k l hk hl
    rcases lt_trichotomy a b with hlt | heq | hgt
    · -- `a < b`: the index shift sends `(a, b - a)` to `(a, b)`
      have hba : a ≤ b := le_of_lt hlt
      have hb' : 0 < b - a := by omega
      have hcop : Nat.Coprime a (b - a) := by
        refine Nat.coprime_add_self_right.mp ?_
        rwa [Nat.sub_add_cancel hba]
      have hIH := ih a (b - a) (by omega) hcop ha hb' k l hk hl
      have hk' : k * (b - a) + k * a = k * b := by
        rw [← Nat.mul_add, Nat.sub_add_cancel hba]
      have hl' : l * (b - a) + l * a = l * b := by
        rw [← Nat.mul_add, Nat.sub_add_cancel hba]
      have hmx : Qop q u (k * a) (k * (b - a)) ∈ DopAlgebra q u :=
        qop_mem_dopAlgebra q u _ (Nat.mul_pos hk ha) _ (Or.inl (Nat.mul_pos hk hb'))
      have hmy : Qop q u (l * a) (l * (b - a)) ∈ DopAlgebra q u :=
        qop_mem_dopAlgebra q u _ (Nat.mul_pos hl ha) _ (Or.inl (Nat.mul_pos hl hb'))
      have hSx : (S ⟨_, hmx⟩ : Module.End L (Lambda L)) = Qop q u (k * a) (k * b) := by
        have hx := qop_shift_right_aux hS (k * a) (Nat.mul_pos hk ha) (k * (b - a))
          (Or.inl (Nat.mul_pos hk hb')) ⟨_, hmx⟩ rfl
        rwa [hk'] at hx
      have hSy : (S ⟨_, hmy⟩ : Module.End L (Lambda L)) = Qop q u (l * a) (l * b) := by
        have hy := qop_shift_right_aux hS (l * a) (Nat.mul_pos hl ha) (l * (b - a))
          (Or.inl (Nat.mul_pos hl hb')) ⟨_, hmy⟩ rfl
        rwa [hl'] at hy
      have hxy : (⟨_, hmx⟩ : DopAlgebra q u) * ⟨_, hmy⟩ = ⟨_, hmy⟩ * ⟨_, hmx⟩ :=
        Subtype.ext hIH
      have hSxy := congrArg S hxy
      rw [map_mul, map_mul] at hSxy
      have hcoe := congrArg (Subtype.val (p := fun x => x ∈ DopAlgebra q u)) hSxy
      rw [MulMemClass.coe_mul, MulMemClass.coe_mul, hSx, hSy] at hcoe
      exact hcoe
    · -- `a = b`: coprimality forces `(1, 1)`, and the claim is the diagonal hypothesis
      subst heq
      have ha1 : a = 1 := by
        have hg := Nat.gcd_self a
        have : Nat.gcd a a = 1 := hab
        omega
      subst ha1
      simpa using hdiag k l hk hl
    · -- `b < a`: conjugation by `∇` sends `(a - b, b)` to `(a, b)`
      have hba : b ≤ a := le_of_lt hgt
      have ha' : 0 < a - b := by omega
      have hcop : Nat.Coprime (a - b) b := by
        refine Nat.coprime_add_self_left.mp ?_
        rwa [Nat.sub_add_cancel hba]
      have hIH := ih (a - b) b (by omega) hcop ha' hb k l hk hl
      have hk' : k * (a - b) + k * b = k * a := by
        rw [← Nat.mul_add, Nat.sub_add_cancel hba]
      have hl' : l * (a - b) + l * b = l * a := by
        rw [← Nat.mul_add, Nat.sub_add_cancel hba]
      have hA := qop_add_apply_nabla h hM (k * (a - b)) (Nat.mul_pos hk ha') (k * b)
        (Nat.mul_pos hk hb)
      have hB := qop_add_apply_nabla h hM (l * (a - b)) (Nat.mul_pos hl ha') (l * b)
        (Nat.mul_pos hl hb)
      rw [hk'] at hA
      rw [hl'] at hB
      refine LinearMap.ext fun x => ?_
      obtain ⟨g, rfl⟩ := h.bijective.surjective x
      have hcomm := LinearMap.congr_fun hIH g
      simp only [Module.End.mul_apply] at hcomm ⊢
      rw [hB g, hA (Qop q u (l * (a - b)) (l * b) g), hA g,
        hB (Qop q u (k * (a - b)) (k * b) g), hcomm]

end Collinear

end HJO.Sym

/-! ### The bridge to the narrowed collinear input

`HJO.CollinearNarrowed.CollinearCommute` is the commutation clause as the rest of the library
uses it, and `HJO.CollinearNarrowed.collinearCommutation` already takes it to the two-clause
`HJO.External.CollinearCommutation`. So the collinear side is complete once the three hypotheses
below are discharged: the existence of a Macdonald conjugator, the existence of an index shift, and
the diagonal base case. The genericity the narrowed clause carries supplies `M ≠ 0` for free.
-/

namespace HJO.CollinearNarrowed

open HJO.Sym

/-- Neither `1 - q` nor `1 - u` vanishes at algebraically independent parameters: otherwise the
polynomial `(1 - X₀)(1 - X₁)` would be zero, which it is not at `(0, 0)`. -/
@[hjo "lem_generic_M_ne_zero"]
theorem one_sub_mul_one_sub_ne_zero_of_algebraicIndependent {L : Type*} [CommRing L] {q u : L}
    (hqu : AlgebraicIndependent ℤ ![q, u]) : (1 - q) * (1 - u) ≠ 0 := fun hz => by
  have h0 : ((1 - MvPolynomial.X 0) * (1 - MvPolynomial.X 1) : MvPolynomial (Fin 2) ℤ) = 0 :=
    PhiPoly.eq_of_aeval_eq hqu (by simp [hz])
  have h1 := congrArg (MvPolynomial.aeval ![(0 : ℤ), 0]) h0
  simp at h1

/-- **The narrowed collinear input, from the two structural data and the diagonal base case.**
Composing with `collinearCommutation` this supplies `HJO.External.CollinearCommutation`, so the
collinear commutation holds modulo exactly these three hypotheses. -/
theorem collinearCommute_of_diag {L : Type*} [Field L] [Algebra ℚ L]
    (hconj : ∀ q u : L, AlgebraicIndependent ℤ ![q, u] →
      ∃ nabla : Module.End L (Lambda L), IsMacdonaldConjugator q u nabla)
    (hshift : ∀ q u : L, AlgebraicIndependent ℤ ![q, u] →
      ∃ S : DopAlgebra q u →ₐ[L] DopAlgebra q u, IsIndexShift q u S)
    (hdiag : ∀ q u : L, AlgebraicIndependent ℤ ![q, u] → ∀ k l : ℕ, 0 < k → 0 < l →
      Commute (Qop q u k k) (Qop q u l l)) :
    CollinearCommute L := by
  intro a b hab ha hb q u hqu k l hk hl
  have hcomm := collinear_commute_of_diag
    (one_sub_mul_one_sub_ne_zero_of_algebraicIndependent hqu)
    (hconj q u hqu) (hshift q u hqu) (hdiag q u hqu) a b hab (by omega) (by omega) k l hk hl
  rwa [Nat.mul_comm k a, Nat.mul_comm k b, Nat.mul_comm l a, Nat.mul_comm l b] at hcomm

end HJO.CollinearNarrowed
