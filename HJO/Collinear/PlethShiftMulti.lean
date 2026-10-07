/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Collinear.KernelExpansion
public import Mathlib.Algebra.MonoidAlgebra.Basic
public meta import HJO.Attr

/-! # The plethystic displacement in `k` variables

BGLX's Theorem 2.1 applies the plethystic displacement `f ↦ f[X + M/z]` of
`HJO.Sym.plethShift` once for each of the `k` variables at a time. The composite is the
`𝕜`-algebra homomorphism `δ^{(k)}` of this file: it sends the power sum `p_j` to
`p_j + (1-q^j)(1-u^j)(z_1^{-j} + ⋯ + z_k^{-j})`, so its image lies in the Laurent polynomials in
`z_1, …, z_k` over `Λ` — in fact in the polynomials in the `z_i^{-1}`.

Two facts about `δ^{(k)}` are what the identity needs, and both are here. Its image has *finite*
support, hence lies in the cone ring `R^τ_k` of `HJO/Collinear/ConeRing.lean` for **every**
ordering `τ`; and it is *symmetric* in the variables, the sum over the variables it adds to each
power sum being so.

## Main definitions

* `HJO.Bglx.LaurentLambda`: the Laurent polynomials `Λ[z_1^{±1}, …, z_k^{±1}]`, as the additive
  monoid algebra of the exponent lattice `ℤ^k` over `Λ`.
* `HJO.Bglx.laurentConst`: a scalar as a constant Laurent polynomial.
* `HJO.Bglx.laurentToCone`: a Laurent polynomial read as a member of the cone ring, a ring
  homomorphism.
* `HJO.Bglx.plethShiftMulti`: the displacement `δ^{(k)}`.

## Main statements

* `HJO.Bglx.plethShiftMulti_powerSum`: the value of `δ^{(k)}` on a power sum, which is the
  defining formula.
* `HJO.Bglx.plethShiftMulti_zero_vars`: at `k = 0` the displacement is the identity of `Λ`.
* `HJO.Bglx.domCongr_plethShiftMulti` and `HJO.Bglx.relabel_coeff_plethShiftMulti`: the
  displacement is symmetric in the variables, stated once inside the Laurent polynomial ring and
  once as the statement about coefficient families that the symmetrisation argument uses.

## Implementation notes

**The target is `AddMonoidAlgebra (Lambda K) (Fin k →₀ ℤ)`, not the cone ring.** The map
`δ^{(k)}` lands in a polynomial ring, and that is what makes its image finitely
supported and so a member of `R^τ_k` for every `τ` at once; were it defined into one cone ring, the
statement that it lies in the others would have to be proved again for each. `laurentToCone` is the
bridge, a ring homomorphism because a Laurent polynomial's finite support makes the cone ring's
convolution the finite convolution of Laurent polynomials — `coeff_laurentToCone` pins it to the
identity on coefficient families, so no reindexing is hidden in it.

**The exponent lattice is spelled `Fin k →₀ ℤ`**, the same spelling as in `ConeRing`, so that
`laurentToCone` is the identity on coefficients and `relabelExp` serves as the relabelling on both
sides: `AddMonoidAlgebra.domCongr` along `relabelExp σ` and `HJO.Bglx.relabel σ` are the same
substitution, which is what `relabel_coeff_plethShiftMulti` records.

**`δ^{(k)}` is defined by `MvPolynomial.eval₂Hom` on the generators.** `Lambda K` is the polynomial
ring `MvPolynomial ℕ K` on the power sums, with `MvPolynomial.X i` the generator `p_{i+1}`, so
prescribing the images of the generators defines the homomorphism and nothing has to be checked;
`plethShiftMulti_powerSum` is then the displayed formula, with the index shift
`p_j = X (j-1)` undone. Symmetry is proved through the generators: both
`domCongr ∘ δ^{(k)}` and `δ^{(k)}` are ring homomorphisms out of a polynomial ring, so
`MvPolynomial.ringHom_ext` reduces the claim to the generators, where relabelling merely reindexes
the sum over the variables.

Nothing here needs a hypothesis on `q` or `u`: the displacement exists for every choice of
parameters, only the *rational* kernel factor needing its denominators nonzero.

## References

The reference is F. Bergeron, A. M. Garsia, E. Leven
and G. Xin, *Some remarkable new plethystic operators in the theory of Macdonald polynomials*,
arXiv:1405.0316v1, J. Comb. **7** (2016) 671--714, whose alphabet `X + ∑_i M/z_i` this is the
substitution into.
-/

@[expose] public section

namespace HJO.Bglx

open HJO.Sym

variable {K : Type*} [CommRing K] {k : ℕ} {τ : Equiv.Perm (Fin k)}

/-! ### Laurent polynomials over `Λ` -/

/-- The Laurent polynomials `Λ[z_1^{±1}, …, z_k^{±1}]` in the variables, with coefficients in `Λ`:
the additive monoid algebra of the exponent lattice `ℤ^k` over `Λ`, whose exponents are spelled the
way `HJO.Bglx.ConeRing` spells them. -/
abbrev LaurentLambda (K : Type*) [CommRing K] (k : ℕ) :=
  AddMonoidAlgebra (Lambda K) (Fin k →₀ ℤ)

/-- A scalar of the base ring as a constant Laurent polynomial, the structure map `𝕜 → Λ[z^{±1}]`
of the displacement: it is `MvPolynomial.C` into `Λ` followed by the exponent-`0` monomial. -/
noncomputable def laurentConst (K : Type*) [CommRing K] (k : ℕ) : K →+* LaurentLambda K k :=
  (AddMonoidAlgebra.singleZeroRingHom).comp (MvPolynomial.C (σ := ℕ))

@[simp] lemma laurentConst_apply (a : K) :
    laurentConst K k a = AddMonoidAlgebra.single 0 (MvPolynomial.C a) := rfl

/-- A coefficient of a product of Laurent polynomials, as the convolution over the support of the
left factor: the exponents outside that support contribute nothing. -/
theorem coeff_mul_laurent (x y : LaurentLambda K k) (α : Fin k →₀ ℤ) :
    (x * y).coeff α = ∑ α' ∈ x.coeff.support, x.coeff α' * y.coeff (α - α') := by
  classical
  rw [AddMonoidAlgebra.coeff_mul, Finsupp.sum]
  refine Finset.sum_congr rfl fun α' _ => ?_
  have hcond : ∀ α₂ : Fin k →₀ ℤ, (α' + α₂ = α) = (α₂ = α - α') :=
    fun α₂ => by rw [eq_iff_iff, eq_sub_iff_add_eq, add_comm]
  rw [Finsupp.sum]
  simp only [hcond]
  rw [Finset.sum_ite_eq' y.coeff.support (α - α') fun α₂ => x.coeff α' * y.coeff α₂]
  split_ifs with h
  · rfl
  · rw [Finsupp.notMem_support_iff.1 h, mul_zero]

/-- **A Laurent polynomial read as a cone-bounded formal sum**, as a ring homomorphism: it has
finite support, so it lies in the cone ring of *every* ordering, and the convolution defining the
product of the cone ring is the product of the Laurent polynomials. -/
noncomputable def laurentToCone (τ : Equiv.Perm (Fin k)) :
    LaurentLambda K k →+* ConeRing k τ (Lambda K) where
  toFun x := ⟨fun α => x.coeff α, isConeBounded_of_finite
    (by rw [Finsupp.fun_support_eq]; exact x.coeff.support.finite_toSet)⟩
  map_one' := by
    refine ConeRing.ext (funext fun α => ?_)
    rw [ConeRing.coeff_one]
    change (1 : LaurentLambda K k).coeff α = _
    rw [AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    exact if_congr eq_comm rfl rfl
  map_mul' x y := by
    refine ConeRing.ext (funext fun α => ?_)
    change (x * y).coeff α = _
    rw [coeff_mul_laurent, ConeRing.coeff_mul_of_subset _ _ _ x.coeff.support fun α' hα' =>
      Finset.mem_coe.2 (Finsupp.mem_support_iff.2 hα'.1)]
  map_zero' := ConeRing.ext (funext fun α => by simp)
  map_add' x y := ConeRing.ext (funext fun α => by simp)

@[simp] theorem coeff_laurentToCone (x : LaurentLambda K k) (α : Fin k →₀ ℤ) :
    (laurentToCone τ x).coeff α = x.coeff α := rfl

/-! ### The displacement -/

/-- **The plethystic displacement in `k` variables**, the `𝕜`-algebra homomorphism `δ^{(k)}` from
`Λ` to the Laurent polynomials in `z_1, …, z_k` sending the power sum `p_j` to
`p_j + (1-q^j)(1-u^j)(z_1^{-j} + ⋯ + z_k^{-j})`. Prescribing the images of the generators
`MvPolynomial.X i = p_{i+1}` of the polynomial ring `Λ` defines it; at `k = 0` it is the identity of
`Λ`. -/
@[hjo "def_bglx_pleth_shift_multi"]
noncomputable def plethShiftMulti (q u : K) (k : ℕ) : Lambda K →+* LaurentLambda K k :=
  MvPolynomial.eval₂Hom (laurentConst K k) fun i =>
    AddMonoidAlgebra.single 0 (powerSum K (i + 1))
      + ∑ l : Fin k, AddMonoidAlgebra.single (Finsupp.single l (-((i : ℤ) + 1)))
          (MvPolynomial.C ((1 - q ^ (i + 1)) * (1 - u ^ (i + 1))))

/-- The value of `δ^{(k)}` on a constant: constants are untouched. -/
@[simp] theorem plethShiftMulti_C (q u : K) (k : ℕ) (a : K) :
    plethShiftMulti q u k (MvPolynomial.C a) = AddMonoidAlgebra.single 0 (MvPolynomial.C a) := by
  rw [plethShiftMulti, MvPolynomial.eval₂Hom_C, laurentConst_apply]

/-- The value of `δ^{(k)}` on a power sum: this pins the definition to the displayed formula. -/
theorem plethShiftMulti_powerSum (q u : K) (k : ℕ) {j : ℕ} (hj : 1 ≤ j) :
    plethShiftMulti q u k (powerSum K j)
      = AddMonoidAlgebra.single 0 (powerSum K j)
        + ∑ l : Fin k, AddMonoidAlgebra.single (Finsupp.single l (-(j : ℤ)))
            (MvPolynomial.C ((1 - q ^ j) * (1 - u ^ j))) := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  rw [powerSum, Nat.add_sub_cancel, plethShiftMulti, MvPolynomial.eval₂Hom_X']
  push_cast
  rfl

/-- At `k = 0` the displacement is the identity of `Λ`. -/
theorem plethShiftMulti_zero_vars (q u : K) (F : Lambda K) :
    (plethShiftMulti q u 0 F).coeff 0 = F := by
  have key : ((ConeRing.zeroVarsAlgEquiv (1 : Equiv.Perm (Fin 0))).toRingEquiv.toRingHom.comp
      ((laurentToCone (1 : Equiv.Perm (Fin 0))).comp (plethShiftMulti q u 0)))
      = RingHom.id (Lambda K) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) fun i => ?_
    · simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply,
        RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv]
      change (laurentToCone (1 : Equiv.Perm (Fin 0))
        (plethShiftMulti q u 0 (MvPolynomial.C a))).coeff 0 = _
      rw [plethShiftMulti_C, coeff_laurentToCone, AddMonoidAlgebra.coeff_single,
        Finsupp.single_eq_same]
    · simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply,
        RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv]
      change (laurentToCone (1 : Equiv.Perm (Fin 0))
        (plethShiftMulti q u 0 (MvPolynomial.X i))).coeff 0 = _
      rw [show MvPolynomial.X i = powerSum K (i + 1) by rw [powerSum, Nat.add_sub_cancel],
        plethShiftMulti_powerSum q u 0 (Nat.succ_le_succ (Nat.zero_le i)), coeff_laurentToCone]
      simp
  have h2 := RingHom.congr_fun key F
  simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv] at h2
  exact h2

/-! ### Symmetry in the variables -/

/-- Relabelling the exponents carries a monomial exponent to the relabelled one. -/
@[simp] theorem relabelExp_single (σ : Equiv.Perm (Fin k)) (l : Fin k) (c : ℤ) :
    relabelExp σ (Finsupp.single l c) = Finsupp.single (σ l) c := by
  rw [relabelExp]
  exact Finsupp.equivMapDomain_single σ l c

/-- **The displacement in `k` variables is symmetric in the variables**: relabelling them fixes
it, since the sum over the variables is. -/
theorem domCongr_plethShiftMulti (q u : K) (k : ℕ) (σ : Equiv.Perm (Fin k)) (F : Lambda K) :
    AddMonoidAlgebra.domCongr (Lambda K) (Lambda K) (relabelExp σ) (plethShiftMulti q u k F)
      = plethShiftMulti q u k F := by
  have key : ((AddMonoidAlgebra.domCongr (Lambda K) (Lambda K)
      (relabelExp σ)).toRingEquiv.toRingHom.comp (plethShiftMulti q u k))
      = plethShiftMulti q u k := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) fun i => ?_
    · simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv]
      rw [plethShiftMulti_C, AddMonoidAlgebra.domCongr_single, map_zero]
    · simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv]
      rw [show MvPolynomial.X i = powerSum K (i + 1) by rw [powerSum, Nat.add_sub_cancel],
        plethShiftMulti_powerSum q u k (Nat.succ_le_succ (Nat.zero_le i)), map_add, map_sum,
        AddMonoidAlgebra.domCongr_single, map_zero]
      refine congrArg _ (Fintype.sum_equiv σ _ _ fun l => ?_)
      rw [AddMonoidAlgebra.domCongr_single, relabelExp_single]
  have := RingHom.congr_fun key F
  simpa only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv] using this

/-- The same, as the statement about coefficient families that the symmetrisation argument uses. -/
theorem relabel_coeff_plethShiftMulti (q u : K) (k : ℕ) (σ : Equiv.Perm (Fin k)) (F : Lambda K) :
    relabel σ (fun α => (plethShiftMulti q u k F).coeff α)
      = fun α => (plethShiftMulti q u k F).coeff α := by
  funext α
  rw [relabel_apply]
  conv_rhs => rw [← domCongr_plethShiftMulti q u k σ F]
  rw [AddMonoidAlgebra.coeff_domCongr]

end HJO.Bglx
