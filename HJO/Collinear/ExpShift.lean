/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Collinear.ScalarFamily
public import HJO.Collinear.ShiftIterate
public import HJO.Collinear.ShiftEsymm
public meta import HJO.Attr

/-! # Displacing the exponential factor produces the kernel

The displacement in a new last variable, `δ̃_k` of `HJO/Collinear/ConeGraded.lean`, applies the
plethystic displacement `δ = plethShift q u` to every coefficient and reads the powers of `w = z⁻¹`
it produces as the new last exponent. This file computes it on the exponential factor: in
`k + 1` variables,
`δ̃_k(E_k) = E_k · ∏_{i ≤ k} ∑_{s ≥ 0} (-1)^s κ(e_s) z^{s(e_i - e_{k+1})}`, the factor `E_k` on the
right being its padding — *the kernel is produced by displacing the exponential factor*, which is
the step that turns BGLX's product of four factors in `k` variables into the product of four
factors in `k + 1` variables.

Two things make this computable. First, `δ̃_k` is defined only on the degree-controlled part `G_k`,
and `E_k` lies there with the bound `N = 0`: its coefficient at `r ∈ ℕ^k` is `± e_{r_1} ⋯ e_{r_k}`,
of weighted degree `r_1 + ⋯ + r_k = coordSum r`. Second, `δ̃_k` is multiplicative, so it may be
applied factor by factor to the product `E_k = ∏_i ∑_{r ≥ 0} (-z_i)^r e_r` of
`HJO/Collinear/ExpAlphabetProd.lean`, and the whole computation reduces to *one* variable's
factor, `δ̃_k(∑_{r ≥ 0} (-z_i)^r e_r)` being
`(∑_{r ≥ 0} (-z_i)^r e_r) · ∑_{s ≥ 0} (-1)^s κ(e_s) z^{s(e_i - e_{k+1})}`,
which is the expansion `δ(e_r) = ∑_{s ≤ r} e_{r-s} κ(e_s) w^s` of
`HJO/Collinear/ShiftEsymm.lean` read off exponent by exponent.

## Main statements

* `HJO.Bglx.isDegreeControlled_expRay` and `HJO.Bglx.isDegreeControlled_expAlphabet`: one
  variable's factor and the whole exponential factor are degree-controlled, so the displacement in
  the last variable applies to them.
* `HJO.Bglx.shiftExtendElem_expRay`: **displacing one variable's factor produces that variable's
  factor of the kernel**, the heart of the file.
* `HJO.Bglx.shiftExtendElem_prod`: the displacement in the last variable is applied to a finite
  product factor by factor.
* `HJO.Bglx.shiftExtendElem_expAlphabet`: **displacing the exponential factor produces the
  kernel.**

## Implementation notes

**The one-variable computation is a comparison of coefficients at `snocExp α n`.** For `n > 0` both
sides vanish: the left by `shiftExtend_snocExp_of_pos`, the right because every pair contributing
to the convolution has last coordinates `0` and `-s`, so their sum is nonpositive
(`mem_convSupport_expRay_kernelRay` packages that analysis, the support of the ray of `e_i` giving
the first exponent and the support of the ray of `e_i - e_{k+1}` the second). For `n = -m ≤ 0`
*exactly one* pair contributes, namely `α' = (α - m e_i, 0)`, so
`ConeRing.coeff_mul_of_subset` over a singleton turns the right-hand side into the single product
`((-1)^{r-m} e_{r-m}) · ((-1)^m κ(e_m))` with `r` the `i`-th coordinate of `α`; the two signs
multiply to `(-1)^r`, which is exactly the sign the left-hand side carries out of
`coeff_plethShift_elemSymm`. The case `m > r` gives `0` on both sides — on the left because the
expansion of `δ(e_r)` stops at `w^r`, on the right because `e_{r-m}` sits at a negative exponent of
the ray.

**Degree control is proved for one factor and multiplied up.** `isDegreeControlled_expRay` is the
only computation — a coefficient of one variable's factor is `± e_c` at the exponent `c e_i`, which
lies in `LambdaLE K c` by `elemSymm_mem_lambdaLE`, and `coordSum (c e_i) = c` — and
`isDegreeControlled_prod`, an induction using `isDegreeControlled_mul`, carries it to the product.
The bounds add to `0`, which is the `N = 0`.

**The degree-control argument of `shiftExtendElem` is a proof of a `Prop` and is irrelevant.**
`ConeRing.ext` reduces any equation between two displacements to their coefficient families, which
are literally `shiftExtend q u …` and mention no proof; that is why
`coeff_shiftExtendElem_prod` — the coefficient-level form of `shiftExtendElem_prod` — can be proved
by induction without carrying a hypothesis whose type changes at every step.

## References

The reference is F. Bergeron, A. M. Garsia, E. Leven and G. Xin, *Some remarkable new plethystic
operators in the theory of Macdonald polynomials*, arXiv:1405.0316v1, J. Comb. **7** (2016)
671--714, whose proof of Theorem 2.1 displaces one variable at a time and reads off the kernel
factor the displacement creates.
-/

@[expose] public section

namespace HJO.Bglx

open HJO.Sym

variable {K : Type*} [CommRing K] [Algebra ℚ K] {k : ℕ}

/-! ### Small facts about exponents supported at one variable -/

/-- The `s`-th point of the ray of `e_i - e_{k+1}`, read through the splitting of an exponent in
`k+1` variables: its first `k` coordinates are `s e_i` and its last is `-s`. -/
lemma nsmul_kernelBase (i : Fin k) (s : ℕ) :
    s • (Finsupp.single i.castSucc (1 : ℤ) - Finsupp.single (Fin.last k) 1)
      = snocExp (Finsupp.single i (s : ℤ)) (-(s : ℤ)) := by
  refine Finsupp.ext fun j => ?_
  rcases Fin.eq_castSucc_or_eq_last j with ⟨l, rfl⟩ | rfl
  · rw [snocExp_castSucc, Finsupp.smul_apply, Finsupp.sub_apply,
      Finsupp.single_eq_of_ne (Fin.castSucc_lt_last l).ne, sub_zero, Finsupp.single_apply,
      Finsupp.single_apply, smul_ite, smul_zero, nsmul_eq_mul, mul_one]
    exact if_congr Fin.castSucc_inj rfl rfl
  · rw [snocExp_last, Finsupp.smul_apply, Finsupp.sub_apply,
      Finsupp.single_eq_of_ne (Fin.castSucc_lt_last i).ne', Finsupp.single_eq_same, zero_sub,
      smul_neg, nsmul_eq_mul, mul_one]

/-! ### The exponential factor is degree-controlled -/

/-- A coefficient `(-1)^n e_n` of the exponential series has weighted degree at most `n`, the sign
being a scalar. -/
lemma neg_one_pow_mul_elemSymm_mem_lambdaLE (n : ℕ) :
    (-1 : Lambda K) ^ n * elemSymm K n ∈ LambdaLE K n := by
  refine mul_mem_lambdaLE_of_le (N := 0) ?_ (elemSymm_mem_lambdaLE n) (by omega)
  rw [show ((-1 : Lambda K)) ^ n = MvPolynomial.C ((-1 : K) ^ n) from by
    rw [map_pow, map_neg, map_one]]
  exact C_mem_lambdaLE _ 0

/-- **One variable's factor of the exponential factor is degree-controlled**, with bound `N = 0`:
its coefficient at `c e_i` is `± e_c`, of weighted degree at most `c = coordSum (c e_i)`, and it
vanishes off the ray of `e_i`. -/
theorem isDegreeControlled_expRay (i : Fin k) :
    IsDegreeControlled (expRay K 1 i).coeff := by
  refine ⟨0, fun α => ?_⟩
  rw [zero_add]
  by_cases hex : ∃ c : ℤ, α = Finsupp.single i c
  · obtain ⟨c, rfl⟩ := hex
    rw [coeff_expRay, coordSum_single]
    split_ifs with hc
    · exact DegLEZ_mono (le_of_eq (Int.toNat_of_nonneg hc))
        (DegLEZ_of_mem_lambdaLE (neg_one_pow_mul_elemSymm_mem_lambdaLE c.toNat))
    · exact DegLEZ_zero
  · rw [expRay, coeff_rayHom_of_forall_ne _ _ _ fun n hn =>
      hex ⟨(n : ℤ), by rw [hn, nsmul_single_one]⟩]
    exact DegLEZ_zero

omit [Algebra ℚ K] in
/-- Degree control is closed under a finite product of the cone ring, the bounds adding. -/
theorem isDegreeControlled_prod {ι : Type*} (f : ι → ConeRing k 1 (Lambda K))
    (hf : ∀ i, IsDegreeControlled (f i).coeff) (s : Finset ι) :
    IsDegreeControlled (∏ i ∈ s, f i).coeff := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.prod_empty]; exact isDegreeControlled_one 1
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact isDegreeControlled_mul (hf a) ih

/-- **The exponential factor is degree-controlled**: its coefficient at `r ∈ ℕ^k` is
`± e_{r_1} ⋯ e_{r_k}`, of weighted degree `r_1 + ⋯ + r_k`, so the bound `N = 0` works. Multiplying
the one-variable bounds `0` of `isDegreeControlled_expRay` along
`expAlphabet_eq_prod` is that statement. -/
theorem isDegreeControlled_expAlphabet (K : Type*) [CommRing K] [Algebra ℚ K] (k : ℕ) :
    IsDegreeControlled (expAlphabet K k 1).coeff := by
  rw [expAlphabet_eq_prod]
  exact isDegreeControlled_prod _ (fun i => isDegreeControlled_expRay i) _

/-- The splitting of an exponent commutes with subtraction. -/
lemma snocExp_sub (α β : Fin k →₀ ℤ) (m n : ℤ) :
    snocExp (α - β) (m - n) = snocExp α m - snocExp β n := by
  refine Finsupp.ext fun j => ?_
  rcases Fin.eq_castSucc_or_eq_last j with ⟨l, rfl⟩ | rfl <;> simp

/-! ### Displacing one variable's factor -/

/-- The coefficient of one variable's factor at a nonnegative multiple of `e_i`. -/
lemma coeff_expRay_natCast (τ : Equiv.Perm (Fin k)) (i : Fin k) (r : ℕ) :
    (expRay K τ i).coeff (Finsupp.single i (r : ℤ)) = (-1) ^ r * elemSymm K r := by
  rw [coeff_expRay, Int.toNat_natCast, ite_eq_left (Int.natCast_nonneg r)]

/-- The coefficient of one factor of the kernel expansion along its own ray. -/
lemma coeff_kernelRay_nsmul (q u : K) {i j : Fin k} (hij : i < j) (s : ℕ) :
    (kernelRay q u hij).coeff (s • (Finsupp.single i (1 : ℤ) - Finsupp.single j 1))
      = MvPolynomial.C ((-1) ^ s * paramPleth q u (elemSymm K s)) := by
  rw [kernelRay, coeff_rayHom_nsmul, coeff_kernelSeries]

/-- An exponent carrying a nonzero coefficient of a factor of the kernel expansion is a
nonnegative multiple of `e_i - e_j`. -/
lemma exists_nsmul_of_coeff_kernelRay_ne_zero (q u : K) {i j : Fin k} (hij : i < j)
    {α : Fin k →₀ ℤ} (hα : (kernelRay q u hij).coeff α ≠ 0) :
    ∃ s : ℕ, α = s • (Finsupp.single i (1 : ℤ) - Finsupp.single j 1) := by
  by_contra hex
  rw [kernelRay] at hα
  exact hα (coeff_rayHom_of_forall_ne _ _ _ (not_exists.1 hex))

/-- **The pairs contributing to the product of one variable's factor with its factor of the
kernel.** The first exponent is a nonnegative multiple `a e_i` of `e_i`, hence has last coordinate
`0`, and the second is a nonnegative multiple `s(e_i - e_{k+1})`, hence has last coordinate `-s`; so
the exponent they contribute to is `((a+s) e_i, -s)`. Both the vanishing branches and the single
contributing pair of `shiftExtendElem_expRay` are read off this. -/
lemma mem_convSupport_expRay_kernelRay (q u : K) (i : Fin k) {γ γ' : Fin (k + 1) →₀ ℤ}
    (hγ' : γ' ∈ ConeRing.convSupport (expRay K 1 i.castSucc)
      (kernelRay q u (Fin.castSucc_lt_last i)) γ) :
    ∃ a s : ℕ, γ' = Finsupp.single i.castSucc (a : ℤ) ∧
      γ = snocExp (Finsupp.single i ((a : ℤ) + s)) (-(s : ℤ)) := by
  obtain ⟨h1, h2⟩ := hγ'
  obtain ⟨a, ha⟩ := exists_natCast_of_coeff_expRay_ne_zero _ h1
  obtain ⟨s, hs⟩ := exists_nsmul_of_coeff_kernelRay_ne_zero q u _ h2
  refine ⟨a, s, ha, ?_⟩
  rw [nsmul_kernelBase] at hs
  have hsum : γ' + (γ - γ') = snocExp (Finsupp.single i ((a : ℤ) + s)) (-(s : ℤ)) := by
    rw [hs, ha, ← snocExp_single i (a : ℤ), ← snocExp_add, ← Finsupp.single_add, zero_add]
  rw [← hsum]
  abel

/-- **Displacing one variable's factor of the exponential factor** produces that variable's factor
of the kernel, times the factor itself in one more variable. -/
theorem shiftExtendElem_expRay (q u : K) (i : Fin k)
    (h : IsDegreeControlled (expRay K 1 i).coeff) :
    shiftExtendElem q u (expRay K 1 i) h
      = expRay K 1 i.castSucc * kernelRay q u (Fin.castSucc_lt_last i) := by
  classical
  refine ConeRing.ext (funext fun γ => ?_)
  obtain ⟨α, n, rfl⟩ : ∃ α n, γ = snocExp α n := ⟨initExp γ, lastExp γ, (snocExp_initExp γ).symm⟩
  rw [coeff_shiftExtendElem]
  rcases lt_or_ge 0 n with hn | hn
  · rw [shiftExtend_snocExp_of_pos q u _ α hn]
    refine ((ConeRing.coeff_mul_of_subset _ _ _ (∅ : Finset (Fin (k + 1) →₀ ℤ)) ?_).trans
      Finset.sum_empty).symm
    intro γ' hγ'
    obtain ⟨a, s, -, heq⟩ := mem_convSupport_expRay_kernelRay q u i hγ'
    have hlast := congrArg lastExp heq
    rw [lastExp_snocExp, lastExp_snocExp] at hlast
    omega
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = -(m : ℤ) := ⟨(-n).toNat, by omega⟩
    rw [shiftExtend_snocExp q u _ α (by omega : -(m : ℤ) ≤ 0),
      show (-(-(m : ℤ))).toNat = m from by omega]
    by_cases hex : ∃ r : ℕ, α = Finsupp.single i (r : ℤ)
    · obtain ⟨r, rfl⟩ := hex
      have hdiff : snocExp (Finsupp.single i (r : ℤ)) (-(m : ℤ))
            - snocExp (Finsupp.single i ((r : ℤ) - (m : ℤ))) 0
          = m • (Finsupp.single i.castSucc (1 : ℤ) - Finsupp.single (Fin.last k) 1) := by
        rw [nsmul_kernelBase, ← snocExp_sub, ← Finsupp.single_sub, sub_sub_cancel, sub_zero]
      have hsub : ConeRing.convSupport (expRay K 1 i.castSucc)
            (kernelRay q u (Fin.castSucc_lt_last i))
            (snocExp (Finsupp.single i (r : ℤ)) (-(m : ℤ)))
          ⊆ ↑({snocExp (Finsupp.single i ((r : ℤ) - (m : ℤ))) 0} :
              Finset (Fin (k + 1) →₀ ℤ)) := by
        intro γ' hγ'
        obtain ⟨a, s, ha, heq⟩ := mem_convSupport_expRay_kernelRay q u i hγ'
        have hlast := congrArg lastExp heq
        rw [lastExp_snocExp, lastExp_snocExp] at hlast
        have hinit := congrArg initExp heq
        rw [initExp_snocExp, initExp_snocExp] at hinit
        have hi := congrArg (fun β : Fin k →₀ ℤ => β i) hinit
        simp only [Finsupp.single_eq_same] at hi
        rw [Finset.mem_coe, Finset.mem_singleton, ha, snocExp_single,
          show (r : ℤ) - (m : ℤ) = (a : ℤ) from by omega]
      have hps : plethShift q u ((-1 : Lambda K) ^ r * elemSymm K r)
          = Polynomial.C ((-1 : Lambda K) ^ r) * plethShift q u (elemSymm K r) := by
        simp only [map_mul, map_pow, map_neg, map_one]
      have hC : (MvPolynomial.C ((-1 : K) ^ m * paramPleth q u (elemSymm K m)) : Lambda K)
          = (-1 : Lambda K) ^ m * MvPolynomial.C (paramPleth q u (elemSymm K m)) := by
        rw [map_mul, map_pow, map_neg, map_one]
      rw [coeff_expRay_natCast, hps, Polynomial.coeff_C_mul, coeff_plethShift_elemSymm,
        ConeRing.coeff_mul_of_subset _ _ _ _ hsub, Finset.sum_singleton, hdiff,
        coeff_kernelRay_nsmul, snocExp_single, coeff_expRay, hC]
      by_cases hmr : m ≤ r
      · rw [ite_eq_left hmr, ite_eq_left (by omega : (0 : ℤ) ≤ (r : ℤ) - (m : ℤ)),
          show ((r : ℤ) - (m : ℤ)).toNat = r - m from by omega,
          show (-1 : Lambda K) ^ (r - m) * elemSymm K (r - m) *
              ((-1 : Lambda K) ^ m * MvPolynomial.C (paramPleth q u (elemSymm K m)))
            = (-1 : Lambda K) ^ (r - m) * (-1 : Lambda K) ^ m *
              (elemSymm K (r - m) * MvPolynomial.C (paramPleth q u (elemSymm K m))) from by ring,
          ← pow_add, Nat.sub_add_cancel hmr]
      · rw [ite_eq_right hmr, ite_eq_right (by omega : ¬ (0 : ℤ) ≤ (r : ℤ) - (m : ℤ)), mul_zero,
          zero_mul]
    · have hzero : (expRay K 1 i).coeff α = 0 := by
        rw [expRay]
        exact coeff_rayHom_of_forall_ne _ _ _ fun t ht => hex ⟨t, by rw [ht, nsmul_single_one]⟩
      rw [hzero, map_zero, Polynomial.coeff_zero]
      refine ((ConeRing.coeff_mul_of_subset _ _ _ (∅ : Finset (Fin (k + 1) →₀ ℤ)) ?_).trans
        Finset.sum_empty).symm
      intro γ' hγ'
      obtain ⟨a, s, -, heq⟩ := mem_convSupport_expRay_kernelRay q u i hγ'
      have hinit := congrArg initExp heq
      rw [initExp_snocExp, initExp_snocExp] at hinit
      exact absurd ⟨a + s, by rw [hinit, Nat.cast_add]⟩ hex

/-! ### Displacing the exponential factor -/

omit [Algebra ℚ K] in
/-- The displacement in the last variable fixes the unit: its coefficients are scalars, on which
the displacement is the padding. -/
theorem shiftExtend_coeff_one (q u : K) :
    shiftExtend q u (1 : ConeRing k 1 (Lambda K)).coeff
      = (1 : ConeRing (k + 1) 1 (Lambda K)).coeff := by
  rw [shiftExtend_eq_padFamily q u _ fun α => ⟨if α = 0 then 1 else 0, by
    rw [ConeRing.coeff_one]; split_ifs <;> simp⟩]
  exact congrArg ConeRing.coeff (padElem_one (K := K) (k := k))

omit [Algebra ℚ K] in
/-- **The displacement in the last variable is applied to a finite product factor by factor**, read
as an identity between coefficient families so that no degree-control hypothesis has to be carried
through the induction. -/
theorem coeff_shiftExtendElem_prod (q u : K) {ι : Type*} (f : ι → ConeRing k 1 (Lambda K))
    (hf : ∀ i, IsDegreeControlled (f i).coeff) (s : Finset ι) :
    shiftExtend q u (∏ i ∈ s, f i).coeff
      = (∏ i ∈ s, shiftExtendElem q u (f i) (hf i)).coeff := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.prod_empty, Finset.prod_empty]; exact shiftExtend_coeff_one q u
  | insert a s ha ih =>
    have hy : IsDegreeControlled (∏ i ∈ s, f i).coeff := isDegreeControlled_prod f hf s
    have hB : shiftExtendElem q u (∏ i ∈ s, f i) hy
        = ∏ i ∈ s, shiftExtendElem q u (f i) (hf i) := ConeRing.ext ih
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      ← coeff_shiftExtendElem q u _ (isDegreeControlled_mul (hf a) hy),
      shiftExtendElem_mul q u _ _ (hf a) hy, hB]

omit [Algebra ℚ K] in
/-- **The displacement in the last variable is applied to a finite product factor by factor.** The
degree-control argument is a proof of a `Prop`, so the element does not depend on which proof is
supplied. -/
theorem shiftExtendElem_prod (q u : K) {ι : Type*} (s : Finset ι)
    (f : ι → ConeRing k 1 (Lambda K)) (hf : ∀ i, IsDegreeControlled (f i).coeff)
    (h : IsDegreeControlled (∏ i ∈ s, f i).coeff) :
    shiftExtendElem q u (∏ i ∈ s, f i) h = ∏ i ∈ s, shiftExtendElem q u (f i) (hf i) :=
  ConeRing.ext (coeff_shiftExtendElem_prod q u f hf s)

/-- **Displacing the exponential factor produces the kernel.** The displacement of `E_k` is the
padding of `E_k` times the `k` factors of the kernel expansion involving the new last variable. -/
@[hjo "lem_bglx_exp_shift"]
theorem shiftExtendElem_expAlphabet (q u : K) (k : ℕ) :
    shiftExtendElem q u (expAlphabet K k 1) (isDegreeControlled_expAlphabet K k)
      = padElem (expAlphabet K k 1) * ∏ i : Fin k, kernelRay q u (Fin.castSucc_lt_last i) := by
  have key : (∏ i : Fin k, shiftExtendElem q u (expRay K 1 i) (isDegreeControlled_expRay i))
      = padElem (∏ i : Fin k, expRay K 1 i)
        * ∏ i : Fin k, kernelRay q u (Fin.castSucc_lt_last i) := by
    rw [padElem_prod, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by rw [shiftExtendElem_expRay, padElem_expRay]
  refine ConeRing.ext ?_
  rw [coeff_shiftExtendElem, expAlphabet_eq_prod,
    coeff_shiftExtendElem_prod q u _ fun i => isDegreeControlled_expRay i, key]

end HJO.Bglx
