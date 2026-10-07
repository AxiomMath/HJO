/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Collinear.EsymmAlphabet
public import HJO.Collinear.RaySeries
public import Mathlib.Tactic.LinearCombination
public meta import HJO.Attr

/-! # The exponential factor, the expansion of the kernel factor, and its denominator

BGLX's Theorem 2.1 writes a composite `D_{a_k} ⋯ D_{a_1}` as the constant term of a product of four
formal sums in `z_1, …, z_k`. Two of the four are built here, both inside the cone ring `R^τ_k` of
`HJO/Collinear/ConeRing.lean`:

* the **exponential factor** `E_k = ∑_{r ∈ ℕ^k} (-1)^{r_1+⋯+r_k} e_{r_1}⋯e_{r_k} z^r`, the
  written-out form of `∏_i Exp[-z_i X]`, whose one-variable factor is the series already used in the
  definition of the basic operators;
* the **expansion of the kernel factor** `Ω̂_k = ∏_{i<j} ∑_{s ≥ 0} (-1)^s κ(e_s) z^{s(e_i - e_j)}`,
  the expansion, in the cone of the identity ordering, of the rational function
  `Ω_k = ∏_{i<j} Exp[-M z_i/z_j]` of `HJO.Sym.dopKernelFactor`.

Those two are *different objects* — one a formal sum, one a rational function — and the relation
between them is denominator clearing: the **kernel denominator**
`Θ_k = ∏_{i ≠ j} (1 - q z_i/z_j)(1 - u z_i/z_j)`, of finite support, has
`Θ_k Ω̂_k = ∏_{i<j}(1 - z_i/z_j)(1 - qu z_i/z_j)(1 - q z_j/z_i)(1 - u z_j/z_i)`, which is the same
Laurent polynomial as `Θ_k Ω_k` on the rational side.

## Main definitions

* `HJO.Bglx.expSeries`: the one-variable series `∑_{r ≥ 0} (-v)^r e_r`.
* `HJO.Bglx.kernelSeries`: the one-variable series `∑_{s ≥ 0} (-1)^s κ(e_s) v^s`, the expansion of
  `Exp[-vM]` in powers of `v`.
* `HJO.Bglx.expAlphabet`: the exponential factor `E_k`, defined by its coefficients.
* `HJO.Bglx.kernelRay`: one factor `∑_{s ≥ 0} (-1)^s κ(e_s) z^{s(e_i - e_j)}` of the expansion.
* `HJO.Bglx.kernelExpansion`: the expansion `Ω̂_k` of the kernel factor.
* `HJO.Bglx.kernelDenom`: the kernel denominator `Θ_k`.

## Main statements

* `HJO.Bglx.coeff_expAlphabet_of_nonneg`: the coefficients of `E_k` in the displayed form.
* `HJO.Bglx.expAlphabet_eq_prod`: `E_k` is the product over the variables of the one-variable
  factors — the form the displacement in the last variable uses, a ring homomorphism being
  applicable factor by factor.
* `HJO.Bglx.relabel_coeff_expAlphabet`: `E_k` is symmetric in the variables.
* `HJO.Bglx.kernelSeries_clear`: the one-variable clearing identity
  `(1 - qv)(1 - uv) ∑_s (-1)^s κ(e_s) v^s = (1 - v)(1 - qu v)`.
* `HJO.Bglx.kernelDenom_mul_kernelExpansion`: clearing the denominator on the expansion.

## Implementation notes

**`E_k` is defined by its coefficients and the product decomposition is a theorem.** `E_k` is
the displayed sum over `ℕ^k`, so that is the definition here, written as a product
over the variables of a per-coordinate factor that vanishes at a negative coordinate — which makes
"supported in `ℕ^k`" a one-line consequence and the displayed form
(`coeff_expAlphabet_of_nonneg`) another. `expAlphabet_eq_prod` then recovers the product
`∏_i ∑_r (-z_i)^r e_r` of BGLX's Proposition 1.2.

**`Ω̂_k` is defined as the displayed product**, its factors being *ray series*: each is
the image of `kernelSeries` under the ray homomorphism of `HJO/Collinear/RaySeries.lean` at the
exponent `e_i - e_j`, which lies in the cone of the identity ordering exactly because `i < j`. That
the factors are ray images is what makes the clearing lemma a consequence of a one-variable
power-series identity: `kernelSeries_clear` is proved from the recursion
`HJO.Bglx.paramPleth_elemSymm_zero` over the coefficient field, and the ray homomorphism — being a
ring homomorphism — carries it into the cone ring.

The factor of the expansion indexed by a pair is only cone-bounded for the identity ordering when
`i < j`, so `kernelRay` carries that hypothesis and `kernelRayIf` is the totalisation by `1` used to
write the product over `j ∈ Ioi i`; no factor of `kernelExpansion` is the junk value.

`Θ_k` is recorded as a member of the cone ring rather than of the Laurent polynomial ring: it has
finite support, so it lies in `R^τ_k` for every ordering, and the clearing statement is an identity
*there*, which is where it is stated. Its factors are monomial multiples of scalars, and
`HJO.Bglx.scalarElem` is the scalar of the base ring read as a constant formal sum.

The coefficient ring is `Lambda K` for `K` a commutative `ℚ`-algebra; the standing field
`𝕜 = ℚ(q, u)` is the instance `K = L`. Nothing here needs a hypothesis on `q` or `u`: the expansion
exists as a formal sum whatever the parameters, and it is only the *rational* kernel factor that
needs its denominators to be nonzero.

## References

The reference is F. Bergeron, A. M. Garsia, E. Leven and G. Xin,
*Some remarkable new plethystic operators in the theory of Macdonald polynomials*,
arXiv:1405.0316v1, J. Comb. **7** (2016) 671--714, whose Proposition 1.2 is the composite formula
these factors occur in and whose Theorem 2.1 is the vanishing criterion.
-/

@[expose] public section

namespace HJO.Bglx

open HJO.Sym

variable {K : Type*} [CommRing K] [Algebra ℚ K] {k : ℕ} {τ : Equiv.Perm (Fin k)}

/-! ### Two products over the pairs of variables -/

/-- The product over the ordered pairs of distinct indices, grouped into the unordered pairs: the
factor at `i < j` is the one at `(i, j)` times the one at `(j, i)`. This is the first step of the
proof of `HJO.Bglx.kernelDenom_mul_kernelExpansion`. -/
theorem prod_offDiag_pair {M : Type*} [CommMonoid M] (f : Fin k → Fin k → M) :
    ∏ p ∈ Finset.univ.offDiag, f p.1 p.2
      = ∏ i : Fin k, ∏ j ∈ Finset.Ioi i, (f i j * f j i) := by
  classical
  have hlt : ∀ g : Fin k → Fin k → M,
      ∏ p ∈ Finset.univ.filter (fun p : Fin k × Fin k => p.1 < p.2), g p.1 p.2
        = ∏ i : Fin k, ∏ j ∈ Finset.Ioi i, g i j := by
    intro g
    rw [Finset.prod_sigma']
    refine Finset.prod_nbij' (fun p => (⟨p.1, p.2⟩ : (_ : Fin k) × Fin k))
      (fun q => (q.1, q.2)) ?_ ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      simp [Finset.mem_sigma, Finset.mem_Ioi, hp]
    · intro q hq
      simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_Ioi, true_and] at hq
      simp [hq]
    · intro p _; rfl
    · intro q _; rfl
    · intro p _; rfl
  have hsplit : (Finset.univ : Finset (Fin k)).offDiag
      = (Finset.univ.filter fun p : Fin k × Fin k => p.1 < p.2)
        ∪ (Finset.univ.filter fun p : Fin k × Fin k => p.2 < p.1) := by
    ext p
    simp only [Finset.mem_offDiag, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact ⟨fun h => (lt_or_gt_of_ne h).imp id id,
      fun h => h.elim ne_of_lt fun h' => (ne_of_lt h').symm⟩
  have hdisj : Disjoint (Finset.univ.filter fun p : Fin k × Fin k => p.1 < p.2)
      (Finset.univ.filter fun p : Fin k × Fin k => p.2 < p.1) :=
    Finset.disjoint_left.2 fun p hp hp' => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hp'
      exact absurd hp' (asymm hp)
  have hswap : ∏ p ∈ Finset.univ.filter (fun p : Fin k × Fin k => p.2 < p.1), f p.1 p.2
      = ∏ p ∈ Finset.univ.filter (fun p : Fin k × Fin k => p.1 < p.2), f p.2 p.1 := by
    refine Finset.prod_nbij' (fun p => (p.2, p.1)) (fun p => (p.2, p.1)) ?_ ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      exact hp
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      exact hp
    · intro p _; rfl
    · intro p _; rfl
    · intro p _; rfl
  rw [hsplit, Finset.prod_union hdisj, hlt, hswap, hlt (fun a b => f b a),
    ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => Finset.prod_mul_distrib.symm

/-! ### Scalars and monomials in the cone ring -/

/-- A scalar of the base ring as a constant formal sum. -/
noncomputable def scalarElem (τ : Equiv.Perm (Fin k)) (a : K) : ConeRing k τ (Lambda K) :=
  ConeRing.const (MvPolynomial.C a)

omit [Algebra ℚ K] in
@[simp] lemma coeff_scalarElem (a : K) (α : Fin k →₀ ℤ) :
    (scalarElem τ a).coeff α = if α = 0 then MvPolynomial.C a else 0 :=
  ConeRing.coeff_const _ _

/-- The exponent `e_i - e_j` of the variable ratio `z_i / z_j` is nonzero when `i ≠ j`. -/
theorem sub_single_ne_zero {i j : Fin k} (h : i ≠ j) :
    Finsupp.single i (1 : ℤ) - Finsupp.single j 1 ≠ 0 := by
  have h1 : (Finsupp.single i (1 : ℤ) - Finsupp.single j 1 : Fin k →₀ ℤ) i = 1 := by
    simp [Ne.symm h]
  intro hc
  rw [hc] at h1
  exact absurd h1 (by norm_num)

/-- The exponent `e_i - e_j` lies in the cone of the identity ordering when `i < j`: its partial
sums are `1` between the two indices and `0` outside. -/
theorem sub_single_mem_cone {i j : Fin k} (h : i < j) :
    Finsupp.single i (1 : ℤ) - Finsupp.single j 1 ∈ cone (1 : Equiv.Perm (Fin k)) := by
  have hlt : (((1 : Equiv.Perm (Fin k)).symm) i).val < (((1 : Equiv.Perm (Fin k)).symm) j).val := h
  have hone := mem_cone_nsmul_sub_single (τ := (1 : Equiv.Perm (Fin k))) hlt 1
  rwa [one_nsmul] at hone

/-! ### The two one-variable series -/

/-- The one-variable exponential series `∑_{r ≥ 0} (-v)^r e_r`, the series the basic operators are
built from. -/
noncomputable def expSeries (K : Type*) [CommRing K] [Algebra ℚ K] : PowerSeries (Lambda K) :=
  PowerSeries.mk fun r => (-1) ^ r * elemSymm K r

@[simp] lemma coeff_expSeries (r : ℕ) :
    PowerSeries.coeff r (expSeries K) = (-1) ^ r * elemSymm K r :=
  PowerSeries.coeff_mk _ _

/-- The one-variable kernel series over the coefficient field: `∑_{s ≥ 0} (-1)^s κ(e_s) v^s`, the
expansion of `Exp[-vM]` in powers of `v`, whose coefficient of `v^s` is
`h_s[-M]`. -/
noncomputable def kernelSeriesBase (q u : K) : PowerSeries K :=
  PowerSeries.mk fun s => (-1) ^ s * paramPleth q u (elemSymm K s)

@[simp] lemma coeff_kernelSeriesBase (q u : K) (s : ℕ) :
    PowerSeries.coeff s (kernelSeriesBase q u) = (-1) ^ s * paramPleth q u (elemSymm K s) :=
  PowerSeries.coeff_mk _ _

/-- The one-variable kernel series, read with coefficients in `Λ`. -/
noncomputable def kernelSeries (q u : K) : PowerSeries (Lambda K) :=
  PowerSeries.map (algebraMap K (Lambda K)) (kernelSeriesBase q u)

@[simp] lemma coeff_kernelSeries (q u : K) (s : ℕ) :
    PowerSeries.coeff s (kernelSeries q u)
      = MvPolynomial.C ((-1) ^ s * paramPleth q u (elemSymm K s)) := by
  rw [kernelSeries, PowerSeries.coeff_map, coeff_kernelSeriesBase, MvPolynomial.algebraMap_eq]

/-- The coefficient of `v^n` in `(1 - rv) f`. -/
theorem coeff_one_sub_C_mul_X_mul {R : Type*} [CommRing R] (r : R) (f : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n ((1 - PowerSeries.C r * PowerSeries.X) * f)
      = PowerSeries.coeff n f - r * (if n = 0 then 0 else PowerSeries.coeff (n - 1) f) := by
  rw [sub_mul, one_mul, map_sub, mul_assoc, PowerSeries.coeff_C_mul]
  cases n with
  | zero => simp
  | succ m => simp [PowerSeries.coeff_succ_X_mul]

/-- The coefficient of `v^n` in the linear factor `1 - rv`. -/
theorem coeff_one_sub_C_mul_X {R : Type*} [CommRing R] (r : R) (n : ℕ) :
    PowerSeries.coeff n (1 - PowerSeries.C r * PowerSeries.X)
      = if n = 0 then 1 else if n = 1 then -r else 0 := by
  rw [map_sub, PowerSeries.coeff_one, PowerSeries.coeff_C_mul, PowerSeries.coeff_X]
  obtain _ | _ | m := n <;> simp

/-- The coefficient of `v^n` in `(1 - v) f`. -/
theorem coeff_one_sub_X_mul {R : Type*} [CommRing R] (f : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n ((1 - PowerSeries.X) * f)
      = PowerSeries.coeff n f - (if n = 0 then 0 else PowerSeries.coeff (n - 1) f) := by
  rw [show (1 : PowerSeries R) - PowerSeries.X = 1 - PowerSeries.C 1 * PowerSeries.X by
    rw [map_one, one_mul], coeff_one_sub_C_mul_X_mul, one_mul]

/-- **The kernel series clears its denominator.** The rational form of `Exp[-vM]` is
`(1-v)(1-quv)/((1-qv)(1-uv))`, and this is that identity between power series in `v`: read off
coefficient by coefficient it is exactly the recursion `HJO.Bglx.paramPleth_elemSymm_zero`. -/
theorem kernelSeriesBase_clear (q u : K) :
    (1 - PowerSeries.C q * PowerSeries.X) *
        ((1 - PowerSeries.C u * PowerSeries.X) * kernelSeriesBase q u)
      = (1 - PowerSeries.X) * (1 - PowerSeries.C (q * u) * PowerSeries.X) := by
  ext n
  simp only [coeff_one_sub_X_mul, coeff_one_sub_C_mul_X_mul, coeff_one_sub_C_mul_X,
    coeff_kernelSeriesBase]
  obtain _ | _ | m := n
  · norm_num [paramPleth_elemSymm_zero]
  · have h := paramPleth_elemSymm_one (K := K) q u
    norm_num
    linear_combination -h
  · have h := paramPleth_elemSymm_add_two (K := K) q u m
    obtain _ | l := m
    · norm_num at h ⊢
      linear_combination h
    · norm_num at h ⊢
      rw [show l + 1 + 2 = l + 1 + 1 + 1 from rfl] at h
      linear_combination (-((-1 : K) ^ l)) * h

/-- The clearing identity with coefficients in `Λ`. -/
theorem kernelSeries_clear (q u : K) :
    (1 - PowerSeries.C (MvPolynomial.C q) * PowerSeries.X) *
        ((1 - PowerSeries.C (MvPolynomial.C u) * PowerSeries.X) * kernelSeries q u)
      = (1 - PowerSeries.X) *
        (1 - PowerSeries.C (MvPolynomial.C (q * u)) * PowerSeries.X) := by
  have h := congrArg (PowerSeries.map (algebraMap K (Lambda K))) (kernelSeriesBase_clear q u)
  simpa [kernelSeries, PowerSeries.map_C, PowerSeries.map_X, MvPolynomial.algebraMap_eq] using h

/-! ### The exponential factor -/

/-- The coefficient family of the exponential factor: the product over the variables of
`(-1)^{α_i} e_{α_i}`, read as `0` at a negative coordinate — so the family is supported in `ℕ^k` and
its value there is the `(-1)^{r_1+⋯+r_k} e_{r_1}⋯e_{r_k}`. -/
noncomputable def expAlphabetCoeff (K : Type*) [CommRing K] [Algebra ℚ K] (k : ℕ) :
    Family k (Lambda K) :=
  fun α => ∏ i : Fin k, if 0 ≤ α i then (-1) ^ (α i).toNat * elemSymm K (α i).toNat else 0

lemma expAlphabetCoeff_eq_zero_of_not_nonneg {α : Fin k →₀ ℤ} (h : ¬ 0 ≤ α) :
    expAlphabetCoeff K k α = 0 := by
  rw [Finsupp.le_def, not_forall] at h
  obtain ⟨i, hi⟩ := h
  exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right (by simpa using hi))

/-- **The exponential factor** `E_k = ∑_{r ∈ ℕ^k} (-1)^{r_1+⋯+r_k} e_{r_1}⋯e_{r_k} z^r`, an element
of the cone ring of *every* ordering: its support lies in `ℕ^k`, which is contained in every cone.
At `k = 0` it is `z^0 = 1`. -/
@[hjo "def_bglx_exp_alphabet"]
noncomputable def expAlphabet (K : Type*) [CommRing K] [Algebra ℚ K] (k : ℕ)
    (τ : Equiv.Perm (Fin k)) : ConeRing k τ (Lambda K) where
  coeff := expAlphabetCoeff K k
  isConeBounded := by
    refine ⟨0, fun α hα => mem_vadd_cone_iff.2 ?_⟩
    rw [sub_zero]
    refine mem_cone_of_nonneg ?_
    by_contra h
    exact hα (expAlphabetCoeff_eq_zero_of_not_nonneg h)

@[simp] lemma coeff_expAlphabet (α : Fin k →₀ ℤ) :
    (expAlphabet K k τ).coeff α
      = ∏ i : Fin k, if 0 ≤ α i then (-1) ^ (α i).toNat * elemSymm K (α i).toNat else 0 :=
  rfl

/-- The coefficient of `E_k` at an exponent with a negative coordinate vanishes. -/
theorem coeff_expAlphabet_of_not_nonneg {α : Fin k →₀ ℤ} (h : ¬ 0 ≤ α) :
    (expAlphabet K k τ).coeff α = 0 :=
  expAlphabetCoeff_eq_zero_of_not_nonneg h

/-- **The coefficients of the exponential factor**, in the displayed form: at an exponent
`r ∈ ℕ^k` it is `(-1)^{r_1+⋯+r_k} e_{r_1}⋯e_{r_k}`. -/
@[hjo "def_bglx_exp_alphabet"]
theorem coeff_expAlphabet_of_nonneg {α : Fin k →₀ ℤ} (h : 0 ≤ α) :
    (expAlphabet K k τ).coeff α
      = (-1) ^ (∑ i : Fin k, (α i).toNat) * ∏ i : Fin k, elemSymm K (α i).toNat := by
  rw [coeff_expAlphabet, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => ite_eq_left (by simpa using Finsupp.le_def.1 h i)

/-- Relabelling the exponents reads the coordinate at the relabelled index. -/
theorem relabelExp_symm_apply (σ : Equiv.Perm (Fin k)) (α : Fin k →₀ ℤ) (i : Fin k) :
    ((relabelExp σ).symm α) i = α (σ i) := by
  have h := relabelExp_apply_perm (τ := σ) (α := (relabelExp σ).symm α) i
  rw [AddEquiv.apply_symm_apply] at h
  exact h.symm

/-- **The exponential factor is symmetric in the variables.** Its coefficient at an exponent depends
only on the multiset of coordinates, so relabelling the variables fixes it. -/
theorem relabel_coeff_expAlphabet (σ : Equiv.Perm (Fin k)) :
    relabel σ (expAlphabet K k τ).coeff = (expAlphabet K k τ).coeff := by
  funext α
  rw [relabel_apply, coeff_expAlphabet, coeff_expAlphabet]
  refine Fintype.prod_equiv σ _ _ fun i => ?_
  rw [relabelExp_symm_apply]

/-! ### The expansion of the kernel factor -/

/-- The ray homomorphism sends the variable to the monomial. -/
theorem rayHom_X {R : Type*} [CommRing R] {b : Fin k →₀ ℤ} (hb : b ∈ cone τ) (hb0 : b ≠ 0) :
    rayHom τ b hb hb0 (PowerSeries.X : PowerSeries R) = monoElem τ b :=
  ConeRing.ext (coeff_rayHom_X hb hb0)

/-- The ray homomorphism sends a constant to the constant formal sum. -/
theorem rayHom_C {R : Type*} [CommRing R] {b : Fin k →₀ ℤ} (hb : b ∈ cone τ) (hb0 : b ≠ 0)
    (r : R) : rayHom τ b hb hb0 (PowerSeries.C r) = ConeRing.const r :=
  ConeRing.ext (coeff_rayHom_C hb hb0 r)

/-- **One factor of the expansion of the kernel factor**: the ray
`∑_{s ≥ 0} (-1)^s κ(e_s) z^{s(e_i - e_j)}`, supported on the nonnegative multiples of `e_i - e_j`,
which lie in the cone of the identity ordering because `i < j`. -/
noncomputable def kernelRay (q u : K) {i j : Fin k} (h : i < j) : ConeRing k 1 (Lambda K) :=
  rayHom 1 (Finsupp.single i 1 - Finsupp.single j 1) (sub_single_mem_cone h)
    (sub_single_ne_zero (ne_of_lt h)) (kernelSeries q u)

/-- The factor of the expansion at an arbitrary pair of indices, taken to be `1` off the pairs
`i < j` the product runs over; no factor of `kernelExpansion` is that junk value. -/
noncomputable def kernelRayIf (q u : K) (i j : Fin k) : ConeRing k 1 (Lambda K) :=
  if h : i < j then kernelRay q u h else 1

lemma kernelRayIf_of_lt (q u : K) {i j : Fin k} (h : i < j) :
    kernelRayIf q u i j = kernelRay q u h := dite_eq_left h

/-- **The expansion of the kernel factor**
`Ω̂_k = ∏_{i<j} ∑_{s ≥ 0} (-1)^s κ(e_s) z^{s(e_i - e_j)}`, the product formed in the cone ring of
the identity ordering. For `k ≤ 1` the product is empty, hence `z^0 = 1`. -/
@[hjo "def_bglx_kernel_expansion"]
noncomputable def kernelExpansion (q u : K) (k : ℕ) : ConeRing k 1 (Lambda K) :=
  ∏ i : Fin k, ∏ j ∈ Finset.Ioi i, kernelRayIf q u i j

/-- **The kernel denominator** `Θ_k = ∏_{i ≠ j} (1 - q z_i/z_j)(1 - u z_i/z_j)`, the product over
the ordered pairs of distinct indices. It has finite support, so it lies in the cone ring of every
ordering; for `k ≤ 1` the product is empty, hence `1`. -/
@[hjo "def_bglx_kernel_denominator"]
noncomputable def kernelDenom (q u : K) (k : ℕ) (τ : Equiv.Perm (Fin k)) :
    ConeRing k τ (Lambda K) :=
  ∏ p ∈ Finset.univ.offDiag,
    ((1 - scalarElem τ q * monoElem τ (Finsupp.single p.1 1 - Finsupp.single p.2 1)) *
      (1 - scalarElem τ u * monoElem τ (Finsupp.single p.1 1 - Finsupp.single p.2 1)))

/-- The ray homomorphism on a linear factor. -/
theorem rayHom_one_sub_C_mul_X {R : Type*} [CommRing R] {b : Fin k →₀ ℤ} (hb : b ∈ cone τ)
    (hb0 : b ≠ 0) (a : R) :
    rayHom τ b hb hb0 (1 - PowerSeries.C a * PowerSeries.X)
      = 1 - ConeRing.const a * monoElem τ b := by
  rw [map_sub, map_one, map_mul, rayHom_X, rayHom_C]

/-- The ray homomorphism on a linear factor with unit coefficient. -/
theorem rayHom_one_sub_X {R : Type*} [CommRing R] {b : Fin k →₀ ℤ} (hb : b ∈ cone τ)
    (hb0 : b ≠ 0) : rayHom τ b hb hb0 (1 - PowerSeries.X : PowerSeries R) = 1 - monoElem τ b := by
  rw [map_sub, map_one, rayHom_X]

/-- **Clearing the denominator on one factor of the expansion.** -/
theorem kernelDenom_factor_mul_kernelRay (q u : K) {i j : Fin k} (h : i < j) :
    (1 - scalarElem 1 q * monoElem 1 (Finsupp.single i (1 : ℤ) - Finsupp.single j 1)) *
        ((1 - scalarElem 1 u * monoElem 1 (Finsupp.single i (1 : ℤ) - Finsupp.single j 1)) *
          kernelRay q u h)
      = (1 - monoElem 1 (Finsupp.single i (1 : ℤ) - Finsupp.single j 1)) *
        (1 - scalarElem 1 (q * u) *
          monoElem 1 (Finsupp.single i (1 : ℤ) - Finsupp.single j 1)) := by
  have hmap := congrArg (rayHom (1 : Equiv.Perm (Fin k))
    (Finsupp.single i (1 : ℤ) - Finsupp.single j 1) (sub_single_mem_cone h)
    (sub_single_ne_zero (ne_of_lt h))) (kernelSeries_clear q u)
  rw [map_mul, map_mul, map_mul, rayHom_one_sub_C_mul_X, rayHom_one_sub_C_mul_X,
    rayHom_one_sub_X, rayHom_one_sub_C_mul_X] at hmap
  exact hmap

/-- **Clearing the denominator on the expansion.** -/
@[hjo "lem_bglx_kernel_expansion_clear"]
theorem kernelDenom_mul_kernelExpansion (q u : K) (k : ℕ) :
    kernelDenom q u k 1 * kernelExpansion q u k
      = ∏ i : Fin k, ∏ j ∈ Finset.Ioi i,
          ((1 - monoElem 1 (Finsupp.single i (1 : ℤ) - Finsupp.single j 1)) *
              (1 - scalarElem 1 (q * u) *
                monoElem 1 (Finsupp.single i (1 : ℤ) - Finsupp.single j 1)) *
            ((1 - scalarElem 1 q * monoElem 1 (Finsupp.single j (1 : ℤ) - Finsupp.single i 1)) *
              (1 - scalarElem 1 u *
                monoElem 1 (Finsupp.single j (1 : ℤ) - Finsupp.single i 1)))) := by
  rw [kernelDenom, prod_offDiag_pair (fun a b =>
      (1 - scalarElem 1 q * monoElem 1 (Finsupp.single a (1 : ℤ) - Finsupp.single b 1)) *
        (1 - scalarElem 1 u * monoElem 1 (Finsupp.single a (1 : ℤ) - Finsupp.single b 1))),
    kernelExpansion, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j hj => ?_
  have hij : i < j := Finset.mem_Ioi.1 hj
  rw [kernelRayIf_of_lt q u hij]
  rw [show ∀ A A' B G : ConeRing k 1 (Lambda K), A * A' * B * G = A * (A' * G) * B from
    fun A A' B G => by ring, kernelDenom_factor_mul_kernelRay q u hij]

end HJO.Bglx
