/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Collinear.MonoMul
public import Mathlib.RingTheory.HahnSeries.PowerSeries
public meta import HJO.Attr

/-! # Power series read along a ray of the exponent cone

The BGLX kernel `Ω̂_k` is a product of factors each of which is a *one-variable* power series
evaluated at a monomial: `∑_{r ≥ 0} (-z_i)ʳ e_r` is a power series in `z_i`, and the expansion of
`Exp[-M z_i / z_j]` is a power series in `z_i / z_j`. Each factor therefore has its support on the
nonnegative multiples `{n b : n ≥ 0}` of a single exponent `b` — a *ray* of the exponent cone
`C^τ_k` of `HJO/Collinear/ConeRing.lean` — and expanding the kernel means multiplying such
factors together inside `R^τ_k`.

This file supplies the ring homomorphism that produces those factors. `HJO.Bglx.rayHom τ b hb hb0`
reads a `PowerSeries R` as the element of `R^τ_k` whose coefficient at `n • b` is the `n`-th
coefficient of the series and whose coefficient off the ray is `0`; it is a ring homomorphism, so a
product of one-variable power series read along (possibly different) rays is computed factor by
factor, and `HJO.Bglx.relabel_coeff_rayHom` says that relabelling the variables moves a ray to the
relabelled ray, which is the step the symmetrisation of the kernel needs.

## Main definitions

* `HJO.Bglx.nsmulHom`: the ray `n ↦ n • c` of exponents as an additive homomorphism `ℕ →+ ℤ^k`,
  with `HJO.Bglx.rayEmb` the order embedding it becomes when `c` is nonnegative and nonzero.
* `HJO.Bglx.ConeRing.hahnRingEquiv`: the reindexing bijection `ConeRing.hahnEquiv` upgraded to a
  ring isomorphism, which is what a composite of ring homomorphisms can end in.
* `HJO.Bglx.rayHom`: a power series `∑_n a_n Xⁿ` read as the formal sum `∑_n a_n z ^ (n b)`
  supported on the ray of a nonzero exponent `b` of the cone.

## Main statements

* `HJO.Bglx.ConeRing.coeff_mul_congr`: a product in a cone ring depends only on the two
  coefficient families, not on the ordering whose ring the product is taken in. The `k!` cone rings
  share the module `M_k` of all families, and this is what lets a computation begun in `R^τ_k` be
  read in `R^ρ_k`.
* `HJO.Bglx.coeff_rayHom_nsmul` and `HJO.Bglx.coeff_rayHom_of_forall_ne`: the two halves of the
  coefficient description of `rayHom`, on and off the ray.
* `HJO.Bglx.relabel_coeff_rayHom`: `σ_*` carries the ray of `b` in `R^τ_k` to the ray of
  `relabelExp σ b` in `R^{στ}_k`.
* `HJO.Bglx.coeff_rayHom_X` and `HJO.Bglx.coeff_rayHom_C`: the two values that pin `rayHom` down,
  `X ↦ z ^ b` and `C r ↦ r`.

## Implementation notes

**The ray is an order embedding because the cone is pointed along it.** `HahnSeries` supports
reindexing by an order embedding (`HahnSeries.embDomainRingHom`), and that is the whole content of
`rayHom`: the composite

  `PowerSeries R ≃+* R⟦ℕ⟧ →+* R⟦ℤ^k⟧ ≃+* R^τ_k`

whose middle map is `embDomain` along `n ↦ n • c`, where `c = psumEquiv τ b` is the exponent `b`
in the partial-sum coordinates in which `ConeRing` is a Hahn series ring. For `n ↦ n • c` to be an
order embedding one needs `n • c ≤ m • c ↔ n ≤ m`, and that is exactly where the two hypotheses on
`b` are used: `hb : b ∈ cone τ` gives `0 ≤ c`, which makes the ray monotone, and `hb0 : b ≠ 0`
gives a coordinate `i` with `0 < c i`, which makes it *strictly* monotone — without it the ray
collapses to a point and the reindexing is not injective. So `nsmulHom_le_iff` is not a technical
lemma but the reason the hypotheses are there.

**Why `hahnRingEquiv` is needed and `hahnEquiv` is not enough.** `ConeRing.instCommRing` is
Mathlib's ring structure transported along the bijection `ConeRing.hahnEquiv`, so `hahnEquiv` is a
ring isomorphism *by construction* — `ConeRing.mul_def` and `ConeRing.add_def` say so. But it is
recorded as an `Equiv`, and `rayHom` has to be a `RingHom` in order to be used on a product of
power series, so the bijection has to be packaged with its two `map_` fields. `hahnRingEquiv` is
that packaging and nothing more; `rayHom_eq` is the `rfl` that says composing through it is the
same as composing through `hahnEquiv`, and every coefficient computation below goes through
`ConeRing.coeff_hahnEquiv_symm`.

**An auxiliary construction.** Nothing here is a main result: the kernel factors are
`Exp`-expansions with named coefficients, and this file is the ambient statement that a
one-variable series may be read along a ray at all. It is used by the files that expand the
kernel, and `coeff_rayHom_X` and `coeff_rayHom_C` pin the homomorphism to the intended one — `X`
goes to the monomial `z ^ b` of `HJO.Bglx.monoElem` and a constant to the constant formal sum of
`ConeRing.const`, so `rayHom` is not some other ring map onto the same ray.

Generic in the coefficient ring: `nsmulHom`, `rayEmb` and the facts about them concern only
exponents, and everything with a `PowerSeries` in it needs `CommRing R`, which is what `ConeRing`
carries a ring structure over. `rayHom` is `noncomputable` because `psumEquiv` and `HahnSeries`
multiplication are.

## References

The reference for Definition `HJO.Bglx.ConeRing` (the ring the ray lands in) and for the kernel
expansion it is used for is F. Bergeron, A. M. Garsia, E. Leven and G. Xin, *Some remarkable new
plethystic operators in the theory of Macdonald polynomials*, arXiv:1405.0316v1, J. Comb. **7**
(2016) 671--714, whose Theorem 2.1 expands each factor of `Ω̂_k` as a power series in one monomial.
-/

@[expose] public section

namespace HJO.Bglx

variable {k : ℕ} {R : Type*} {τ : Equiv.Perm (Fin k)}

/-! ### Products depend only on the coefficient families -/

/-- **A product in a cone ring depends only on the two coefficient families.** The same two
families, multiplied in the cone ring of another ordering, have the same coefficients: the
convolution of `ConeRing.coeff_mul` mentions the ordering nowhere. -/
theorem ConeRing.coeff_mul_congr [CommRing R] {τ' : Equiv.Perm (Fin k)}
    (x y : ConeRing k τ R) (x' y' : ConeRing k τ' R)
    (hx : x.coeff = x'.coeff) (hy : y.coeff = y'.coeff) :
    (x * y).coeff = (x' * y').coeff := by
  funext α
  simp only [ConeRing.coeff_mul, hx, hy]

/-! ### The reindexing bijection as a ring isomorphism -/

/-- The reindexing bijection `ConeRing.hahnEquiv` as a ring isomorphism. The ring structure on
`ConeRing` is transported along it, so the two `map_` fields are `ConeRing.mul_def` and
`ConeRing.add_def` followed by `Equiv.apply_symm_apply`. -/
noncomputable def ConeRing.hahnRingEquiv (k : ℕ) (τ : Equiv.Perm (Fin k)) (R : Type*)
    [CommRing R] : ConeRing k τ R ≃+* HahnSeries (Fin k →₀ ℤ) R where
  toEquiv := hahnEquiv k τ R
  map_mul' x y := by rw [mul_def]; exact (hahnEquiv k τ R).apply_symm_apply _
  map_add' x y := by rw [add_def]; exact (hahnEquiv k τ R).apply_symm_apply _

/-- The ring isomorphism `ConeRing.hahnRingEquiv` is the bijection `ConeRing.hahnEquiv`. -/
lemma ConeRing.hahnRingEquiv_symm_apply [CommRing R] (x : HahnSeries (Fin k →₀ ℤ) R) :
    (hahnRingEquiv k τ R).symm x = (hahnEquiv k τ R).symm x := rfl

/-! ### The ray of an exponent -/

/-- The ray `n ↦ n • c` of the exponent `c`, as an additive homomorphism of the exponent
lattice. -/
noncomputable def nsmulHom (c : Fin k →₀ ℤ) : ℕ →+ (Fin k →₀ ℤ) where
  toFun n := n • c
  map_zero' := zero_nsmul c
  map_add' m n := add_nsmul c m n

@[simp] lemma nsmulHom_apply (c : Fin k →₀ ℤ) (n : ℕ) : nsmulHom c n = n • c := rfl

/-- A nonnegative nonzero exponent is strictly positive in some coordinate. -/
lemma exists_pos_coord {c : Fin k →₀ ℤ} (hc : 0 ≤ c) (hc0 : c ≠ 0) : ∃ i, 0 < c i := by
  by_contra h
  simp only [not_exists, not_lt] at h
  exact hc0 (Finsupp.ext fun i => le_antisymm (h i) (by simpa using Finsupp.le_def.1 hc i))

/-- **The ray of a nonnegative nonzero exponent is order-reflecting.** Monotonicity is the
nonnegativity of `c`; the converse needs a coordinate in which `c` is strictly positive, which is
where `c ≠ 0` enters. -/
lemma nsmulHom_le_iff {c : Fin k →₀ ℤ} (hc : 0 ≤ c) (hc0 : c ≠ 0) (n m : ℕ) :
    nsmulHom c n ≤ nsmulHom c m ↔ n ≤ m := by
  obtain ⟨i, hi⟩ := exists_pos_coord hc hc0
  refine ⟨fun h => ?_, fun h => nsmul_le_nsmul_left hc h⟩
  have h1 := Finsupp.le_def.1 h i
  simp only [nsmulHom_apply, Finsupp.smul_apply, nsmul_eq_mul] at h1
  exact Nat.cast_le.1 (le_of_mul_le_mul_right h1 hi)

/-- The ray of a nonnegative nonzero exponent is injective. -/
lemma nsmulHom_injective {c : Fin k →₀ ℤ} (hc : 0 ≤ c) (hc0 : c ≠ 0) :
    Function.Injective (nsmulHom c) := fun n m h =>
  le_antisymm ((nsmulHom_le_iff hc hc0 n m).1 h.le) ((nsmulHom_le_iff hc hc0 m n).1 h.ge)

/-- The ray `n ↦ n • c` of a nonnegative nonzero exponent, as an order embedding of `ℕ` into the
exponent lattice. This is the reindexing along which a power series becomes a Hahn series. -/
noncomputable def rayEmb {c : Fin k →₀ ℤ} (hc : 0 ≤ c) (hc0 : c ≠ 0) : ℕ ↪o (Fin k →₀ ℤ) :=
  ⟨⟨nsmulHom c, nsmulHom_injective hc hc0⟩, nsmulHom_le_iff hc hc0 _ _⟩

@[simp] lemma rayEmb_apply {c : Fin k →₀ ℤ} (hc : 0 ≤ c) (hc0 : c ≠ 0) (n : ℕ) :
    rayEmb hc hc0 n = n • c := rfl

/-- The partial sums of a nonzero exponent are nonzero, `psumEquiv` being a bijection. -/
lemma psumEquiv_ne_zero {b : Fin k →₀ ℤ} (hb0 : b ≠ 0) : psumEquiv τ b ≠ 0 :=
  fun h => hb0 ((psumEquiv τ).map_eq_zero_iff.1 h)

/-- The ray of a nonzero exponent of the cone is injective on exponents. -/
lemma nsmul_injective_of_mem_cone {b : Fin k →₀ ℤ} (hb : b ∈ cone τ) (hb0 : b ≠ 0) :
    Function.Injective fun n : ℕ => n • b := by
  intro n m h
  refine nsmulHom_injective (mem_cone_iff_le.1 hb) (psumEquiv_ne_zero (τ := τ) hb0) ?_
  simp only [nsmulHom_apply, ← map_nsmul (psumEquiv τ)]
  exact congrArg (psumEquiv τ) h

/-! ### A power series read along a ray -/

/-- **A power series read along a ray of the exponent cone.** The series `∑_n a_n Xⁿ` becomes the
formal sum `∑_n a_n z ^ (n b)`, supported on the nonnegative multiples of the nonzero cone exponent
`b`. It is the composite of the isomorphism `PowerSeries R ≃+* R⟦ℕ⟧`, the reindexing of Hahn series
along the ray `rayEmb`, and the reindexing bijection `ConeRing.hahnRingEquiv`, so it is a ring
homomorphism. -/
noncomputable def rayHom [CommRing R] (τ : Equiv.Perm (Fin k)) (b : Fin k →₀ ℤ)
    (hb : b ∈ cone τ) (hb0 : b ≠ 0) : PowerSeries R →+* ConeRing k τ R :=
  (ConeRing.hahnRingEquiv k τ R).symm.toRingHom.comp
    ((HahnSeries.embDomainRingHom (nsmulHom (psumEquiv τ b))
        (nsmulHom_injective (mem_cone_iff_le.1 hb) (psumEquiv_ne_zero hb0))
        (nsmulHom_le_iff (mem_cone_iff_le.1 hb) (psumEquiv_ne_zero hb0))).comp
      HahnSeries.toPowerSeries.symm.toRingHom)

/-- `rayHom` unfolded: the reindexing `HahnSeries.embDomain` along the ray, read back through
`ConeRing.hahnEquiv`. -/
private lemma rayHom_eq [CommRing R] {b : Fin k →₀ ℤ} (hb : b ∈ cone τ) (hb0 : b ≠ 0)
    (s : PowerSeries R) :
    rayHom τ b hb hb0 s = (ConeRing.hahnEquiv k τ R).symm
      (HahnSeries.embDomain (rayEmb (mem_cone_iff_le.1 hb) (psumEquiv_ne_zero (τ := τ) hb0))
        (HahnSeries.toPowerSeries.symm s)) := rfl

/-- **On the ray, `rayHom` has the coefficients of the series.** -/
@[simp] theorem coeff_rayHom_nsmul [CommRing R] {b : Fin k →₀ ℤ} (hb : b ∈ cone τ) (hb0 : b ≠ 0)
    (s : PowerSeries R) (n : ℕ) :
    (rayHom τ b hb hb0 s).coeff (n • b) = PowerSeries.coeff n s := by
  rw [rayHom_eq hb hb0, ConeRing.coeff_hahnEquiv_symm, map_nsmul,
    ← rayEmb_apply (mem_cone_iff_le.1 hb) (psumEquiv_ne_zero (τ := τ) hb0) n,
    HahnSeries.embDomain_coeff, HahnSeries.coeff_toPowerSeries_symm]

/-- **Off the ray, `rayHom` vanishes.** -/
theorem coeff_rayHom_of_forall_ne [CommRing R] {b : Fin k →₀ ℤ} (hb : b ∈ cone τ) (hb0 : b ≠ 0)
    (s : PowerSeries R) {α : Fin k →₀ ℤ} (h : ∀ n : ℕ, α ≠ n • b) :
    (rayHom τ b hb hb0 s).coeff α = 0 := by
  rw [rayHom_eq hb hb0, ConeRing.coeff_hahnEquiv_symm]
  refine HahnSeries.embDomain_of_notMem_range ?_
  rintro ⟨n, hn⟩
  rw [rayEmb_apply] at hn
  refine h n ((psumEquiv τ).injective ?_)
  rw [map_nsmul, hn]

/-! ### Relabelling the variables -/

/-- **Relabelling moves a ray to the relabelled ray.** The ray of `b` in `R^τ_k` is carried by
`σ_*` to the ray of `relabelExp σ b` in `R^{στ}_k`, with the same series along it. -/
theorem relabel_coeff_rayHom [CommRing R] (σ : Equiv.Perm (Fin k)) {b : Fin k →₀ ℤ}
    (hb : b ∈ cone τ) (hb0 : b ≠ 0) (s : PowerSeries R) :
    relabel σ (rayHom τ b hb hb0 s).coeff
      = (rayHom (σ * τ) (relabelExp σ b) ((mem_cone_relabelExp σ τ).2 hb)
          (fun h => hb0 ((relabelExp σ).map_eq_zero_iff.1 h)) s).coeff := by
  funext α
  by_cases hex : ∃ n : ℕ, α = n • relabelExp σ b
  · obtain ⟨n, rfl⟩ := hex
    rw [coeff_rayHom_nsmul, relabel_apply,
      show (relabelExp σ).symm (n • relabelExp σ b) = n • b from by
        rw [← map_nsmul, AddEquiv.symm_apply_apply],
      coeff_rayHom_nsmul]
  · rw [coeff_rayHom_of_forall_ne _ _ s (not_exists.1 hex), relabel_apply]
    refine coeff_rayHom_of_forall_ne hb hb0 s fun n hn => ?_
    have h2 : relabelExp σ ((relabelExp σ).symm α) = relabelExp σ (n • b) := by rw [hn]
    rw [AddEquiv.apply_symm_apply, map_nsmul] at h2
    exact (not_exists.1 hex) n h2

/-! ### The two values that pin the ray homomorphism down -/

/-- **`rayHom` sends the variable to the monomial `z ^ b`.** -/
theorem coeff_rayHom_X [CommRing R] {b : Fin k →₀ ℤ} (hb : b ∈ cone τ) (hb0 : b ≠ 0) :
    (rayHom τ b hb hb0 (PowerSeries.X : PowerSeries R)).coeff
      = (monoElem τ b : ConeRing k τ R).coeff := by
  funext α
  by_cases hex : ∃ n : ℕ, α = n • b
  · obtain ⟨n, rfl⟩ := hex
    have h1 : (n • b = b) ↔ n = 1 := by
      refine ⟨fun h => nsmul_injective_of_mem_cone hb hb0 ?_, fun h => by rw [h, one_nsmul]⟩
      simpa using h
    rw [coeff_rayHom_nsmul, coeff_monoElem, PowerSeries.coeff_X]
    simp only [h1]
  · rw [coeff_rayHom_of_forall_ne hb hb0 _ (not_exists.1 hex), coeff_monoElem,
      ite_eq_right fun h => (not_exists.1 hex) 1 (by rw [one_nsmul]; exact h)]

/-- **`rayHom` sends a constant to the constant formal sum.** -/
theorem coeff_rayHom_C [CommRing R] {b : Fin k →₀ ℤ} (hb : b ∈ cone τ) (hb0 : b ≠ 0) (r : R) :
    (rayHom τ b hb hb0 (PowerSeries.C r)).coeff = (ConeRing.const r : ConeRing k τ R).coeff := by
  funext α
  by_cases hex : ∃ n : ℕ, α = n • b
  · obtain ⟨n, rfl⟩ := hex
    have h1 : (n • b = 0) ↔ n = 0 := by
      refine ⟨fun h => nsmul_injective_of_mem_cone hb hb0 ?_, fun h => by rw [h, zero_nsmul]⟩
      simpa using h
    rw [coeff_rayHom_nsmul, ConeRing.coeff_const, PowerSeries.coeff_C]
    simp only [h1]
  · rw [coeff_rayHom_of_forall_ne hb hb0 _ (not_exists.1 hex), ConeRing.coeff_const,
      ite_eq_right fun h => (not_exists.1 hex) 0 (by rw [zero_nsmul]; exact h)]

end HJO.Bglx
