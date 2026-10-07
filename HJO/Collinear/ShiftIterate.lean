/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Collinear.PadStructure
public import HJO.Collinear.PlethShiftMulti
public meta import HJO.Attr

/-! # The displacement in `k+1` variables is built one variable at a time

BGLX apply the plethystic displacement `δ = plethShift q u` once for each variable, and the
composite `δ^{(k)}` of `HJO/Collinear/PlethShiftMulti.lean` is what their alphabet
`X + ∑_{i ≤ k} M/z_i` substitutes. The induction driving their Theorem 2.1 needs to know that the
composite in `k+1` variables really is the composite in `k` variables followed by one more
displacement, the new variable being read as a new last exponent by the operator `δ̃_{k+1}` of
`HJO/Collinear/ConeGraded.lean`. That is what is proved here.

The first thing needed is that `δ̃_{k+1}` may be applied at all: its domain is the
*degree-controlled* part `G_k` of the cone ring, and the image of `δ^{(k)}` is a Laurent
polynomial, hence a family with finite support. Finitely many coefficients, each a polynomial of
some finite weighted degree, admit a common bound, so every such family is degree-controlled.

## Main statements

* `HJO.Bglx.isDegreeControlled_of_finite_support`: a formal sum with finite support is
  degree-controlled.
* `HJO.Bglx.isDegreeControlled_laurentToCone`: a Laurent polynomial is degree-controlled.
* `HJO.Bglx.shiftExtendLaurent`: the displacement in the last variable applied to a Laurent
  polynomial, as a ring homomorphism `Λ[z^{±1}]_k → R^{id}_{k+1}`.
* `HJO.Bglx.shiftExtendElem_plethShiftMulti`: the displacement in `k+1` variables is the
  displacement in `k` variables followed by the displacement in the last variable.

## Implementation notes

**The comparison is made between ring homomorphisms.** `Λ` is the polynomial ring
`MvPolynomial ℕ K` on the power sums, so `MvPolynomial.ringHom_ext` reduces the identity to the
constants and the generators `p_j`. The left-hand side is a ring homomorphism because
`shiftExtendLaurent` is one: `laurentToCone` is a ring homomorphism whose image is always
degree-controlled, so the multiplicativity `shiftExtendElem_mul` of `δ̃_{k+1}` applies to it with
no side condition. This is the route the proof takes, and it is why the degree-control
hypothesis never has to be carried around: it is discharged once, by
`isDegreeControlled_laurentToCone`.

**The proof-irrelevance of the degree-control argument is used silently.** `shiftExtendElem` takes
a proof that its argument is degree-controlled, and two such proofs of the same statement are
definitionally equal, so `coeff_shiftExtendElem` may be applied before anything else and every
later rewrite happens in a term with no dependent argument left in it. Rewriting the *argument* of
`shiftExtendElem` first would not typecheck.

**On the generators the computation splits along the three exponents involved.** Every exponent of
`k+1` variables is `snocExp α n`, and `snocExp_eq_snocExp_iff` turns each of the three monomials
occurring — the constant exponent `0`, the ray `-j e_{k+1}` produced by the new displacement, and
the rays `-j e_i` inherited from `δ^{(k)}` — into a condition on the pair `(α, n)`. The inherited
rays have *scalar* coefficients, so on them `δ̃_{k+1}` is the padding
(`shiftExtend_eq_padFamily`), which is `shiftExtendLaurent_single_C`; the coefficient `p_j` at the
exponent `0` is the only one the displacement acts on nontrivially, and
`shiftExtendLaurent_single_zero` is that computation, whose whole content is
`coeff_plethShift_powerSum`.

## References

F. Bergeron,
A. M. Garsia, E. Leven and G. Xin, *Some remarkable new plethystic operators in the theory of
Macdonald polynomials*, arXiv:1405.0316v1, J. Comb. **7** (2016) 671--714, whose proof of
Theorem 2.1 applies the displacement one variable at a time.
-/

@[expose] public section

namespace HJO.Bglx

open HJO.Sym

variable {K : Type*} [CommRing K] {k : ℕ}

/-! ### Degree control from finite support -/

/-- A formal sum with finite support is degree-controlled: finitely many coefficients each of finite
degree admit a common bound. -/
theorem isDegreeControlled_of_finite_support {f : Family k (Lambda K)}
    (hf : (Function.support f).Finite) : IsDegreeControlled f := by
  classical
  obtain ⟨d, hd⟩ : ∃ d : (Fin k →₀ ℤ) → ℤ, ∀ α, DegLEZ (d α) (f α) := by
    refine ⟨fun α => (((f α).support.sup fun e => Finsupp.weight (fun i => i + 1) e : ℕ) : ℤ),
      fun α e he => ?_⟩
    change ((Finsupp.weight (fun i => i + 1) e : ℕ) : ℤ)
      ≤ (((f α).support.sup fun e => Finsupp.weight (fun i => i + 1) e : ℕ) : ℤ)
    exact_mod_cast Finset.le_sup (f := fun e => Finsupp.weight (fun i => i + 1) e) he
  refine ⟨((hf.toFinset.sup fun α => (d α - coordSum α).toNat : ℕ) : ℤ), fun α => ?_⟩
  by_cases hα : α ∈ hf.toFinset
  · refine DegLEZ_mono ?_ (hd α)
    have h2 : (d α - coordSum α).toNat ≤ hf.toFinset.sup fun α => (d α - coordSum α).toNat :=
      Finset.le_sup (f := fun α => (d α - coordSum α).toNat) hα
    omega
  · rw [Set.Finite.mem_toFinset] at hα
    have h0 : f α = 0 := by simpa using hα
    rw [h0]
    exact DegLEZ_zero

/-- A Laurent polynomial is degree-controlled. -/
theorem isDegreeControlled_laurentToCone (x : LaurentLambda K k) :
    IsDegreeControlled (laurentToCone (1 : Equiv.Perm (Fin k)) x).coeff := by
  refine isDegreeControlled_of_finite_support
    (Set.Finite.subset x.coeff.support.finite_toSet fun α hα => ?_)
  exact Finset.mem_coe.2 (Finsupp.mem_support_iff.2 hα)

/-! ### Exponents of the last variable -/

/-- The zero exponent of `k+1` variables is the zero exponent of `k` variables with last
coordinate `0`. -/
@[simp] lemma snocExp_zero : snocExp (0 : Fin k →₀ ℤ) 0 = 0 := by
  refine Finsupp.ext fun i => ?_
  rcases Fin.eq_castSucc_or_eq_last i with ⟨l, rfl⟩ | rfl <;> simp

/-- The splitting of an exponent determines it: two exponents of `k+1` variables agree exactly
when their first `k` coordinates and their last do. -/
lemma snocExp_eq_snocExp_iff {α β : Fin k →₀ ℤ} {m n : ℤ} :
    snocExp α m = snocExp β n ↔ α = β ∧ m = n := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => by rw [h.1, h.2]⟩
  · simpa using congrArg initExp h
  · simpa using congrArg lastExp h

/-- The exponent `c e_i` of `k` variables pads to the exponent `c e_i` of `k+1` variables. -/
lemma snocExp_single (i : Fin k) (c : ℤ) :
    snocExp (Finsupp.single i c) 0 = Finsupp.single i.castSucc c := by
  refine Finsupp.ext fun m => ?_
  rcases Fin.eq_castSucc_or_eq_last m with ⟨l, rfl⟩ | rfl
  · rw [snocExp_castSucc, Finsupp.single_apply, Finsupp.single_apply]
    exact if_congr ⟨fun h => by rw [h], fun h => Fin.castSucc_inj.1 h⟩ rfl rfl
  · rw [snocExp_last, Finsupp.single_apply, ite_eq_right]
    intro h
    exact absurd h (Fin.castSucc_lt_last i).ne

/-- The exponent `c e_{k+1}` in the last variable alone is the zero exponent with last
coordinate `c`. -/
lemma snocExp_zero_last (c : ℤ) :
    snocExp (0 : Fin k →₀ ℤ) c = Finsupp.single (Fin.last k) c := by
  refine Finsupp.ext fun m => ?_
  rcases Fin.eq_castSucc_or_eq_last m with ⟨l, rfl⟩ | rfl
  · rw [snocExp_castSucc, Finsupp.coe_zero, Pi.zero_apply,
      Finsupp.single_eq_of_ne (Fin.ne_of_lt (Fin.castSucc_lt_last l))]
  · rw [snocExp_last, Finsupp.single_eq_same]

/-- When the zero exponent is a splitting: both parts vanish. -/
lemma zero_eq_snocExp_iff {α : Fin k →₀ ℤ} {n : ℤ} :
    (0 : Fin (k + 1) →₀ ℤ) = snocExp α n ↔ α = 0 ∧ n = 0 := by
  rw [← snocExp_zero (k := k), snocExp_eq_snocExp_iff]
  exact and_congr eq_comm eq_comm

/-- When a ray in the last variable is a splitting: the first `k` coordinates vanish and the last
is the exponent of the ray. -/
lemma single_last_eq_snocExp_iff {c : ℤ} {α : Fin k →₀ ℤ} {n : ℤ} :
    Finsupp.single (Fin.last k) c = snocExp α n ↔ α = 0 ∧ n = c := by
  rw [← snocExp_zero_last (k := k) c, snocExp_eq_snocExp_iff]
  exact and_congr eq_comm eq_comm

/-! ### The displacement in the last variable is additive -/

/-- The displacement in the last variable kills the zero family. -/
lemma shiftExtend_zero (q u : K) : shiftExtend q u (0 : Family k (Lambda K)) = 0 := by
  funext γ
  by_cases hγ : lastExp γ ≤ 0
  · rw [shiftExtend_apply_of_nonpos q u _ hγ, Pi.zero_apply, map_zero, Polynomial.coeff_zero,
      Pi.zero_apply]
  · rw [shiftExtend_eq_zero_of_pos q u _ (by omega), Pi.zero_apply]

/-- The displacement in the last variable is additive, `δ` and `Polynomial.coeff` both being so. -/
lemma shiftExtend_add (q u : K) (f g : Family k (Lambda K)) :
    shiftExtend q u (f + g) = shiftExtend q u f + shiftExtend q u g := by
  funext γ
  by_cases hγ : lastExp γ ≤ 0
  · rw [shiftExtend_apply_of_nonpos q u (f + g) hγ, Pi.add_apply, map_add, Polynomial.coeff_add,
      Pi.add_apply, shiftExtend_apply_of_nonpos q u f hγ, shiftExtend_apply_of_nonpos q u g hγ]
  · rw [shiftExtend_eq_zero_of_pos q u (f + g) (by omega), Pi.add_apply,
      shiftExtend_eq_zero_of_pos q u f (by omega), shiftExtend_eq_zero_of_pos q u g (by omega),
      add_zero]

/-- The coefficient family of a padding, as a function. -/
lemma coeff_padElem' (x : ConeRing k 1 (Lambda K)) : (padElem x).coeff = padFamily x.coeff := rfl

/-- **The displacement in the last variable fixes the unit.** All coefficients of `1` are scalars,
so the displacement is the padding there, and padding fixes the unit. -/
theorem shiftExtend_one (q u : K) :
    shiftExtend q u (1 : ConeRing k 1 (Lambda K)).coeff
      = (1 : ConeRing (k + 1) 1 (Lambda K)).coeff := by
  have hconst : ∀ α : Fin k →₀ ℤ, ∃ a : K,
      (1 : ConeRing k 1 (Lambda K)).coeff α = MvPolynomial.C a := by
    intro α
    rw [ConeRing.coeff_one]
    split_ifs
    · exact ⟨1, by rw [map_one]⟩
    · exact ⟨0, by rw [map_zero]⟩
  rw [shiftExtend_eq_padFamily q u _ hconst, ← coeff_padElem', padElem_one]

/-! ### The displacement in the last variable of a Laurent polynomial -/

/-- **The displacement in the last variable of a Laurent polynomial**, as a ring homomorphism: a
Laurent polynomial is degree-controlled, so no side condition is left. -/
noncomputable def shiftExtendLaurent (q u : K) (k : ℕ) :
    LaurentLambda K k →+* ConeRing (k + 1) 1 (Lambda K) where
  toFun x := shiftExtendElem q u (laurentToCone 1 x) (isDegreeControlled_laurentToCone x)
  map_one' := by
    refine ConeRing.ext ?_
    rw [coeff_shiftExtendElem, map_one, shiftExtend_one]
  map_mul' x y := by
    refine ConeRing.ext ?_
    rw [coeff_shiftExtendElem, map_mul]
    exact congrArg ConeRing.coeff (shiftExtendElem_mul q u (laurentToCone 1 x) (laurentToCone 1 y)
      (isDegreeControlled_laurentToCone x) (isDegreeControlled_laurentToCone y))
  map_zero' := by
    refine ConeRing.ext (funext fun γ => ?_)
    rw [coeff_shiftExtendElem, map_zero]
    have h0 : (0 : ConeRing k 1 (Lambda K)).coeff = 0 :=
      funext fun α => ConeRing.coeff_zero α
    rw [h0, shiftExtend_zero, Pi.zero_apply, ConeRing.coeff_zero]
  map_add' x y := by
    refine ConeRing.ext (funext fun γ => ?_)
    rw [coeff_shiftExtendElem, map_add]
    have h0 : (laurentToCone (1 : Equiv.Perm (Fin k)) x + laurentToCone 1 y).coeff
        = (laurentToCone (1 : Equiv.Perm (Fin k)) x).coeff + (laurentToCone 1 y).coeff :=
      funext fun α => ConeRing.coeff_add _ _ α
    rw [h0, shiftExtend_add, Pi.add_apply, ConeRing.coeff_add]
    rfl

@[simp] lemma shiftExtendLaurent_apply (q u : K) (k : ℕ) (x : LaurentLambda K k) :
    shiftExtendLaurent q u k x
      = shiftExtendElem q u (laurentToCone 1 x) (isDegreeControlled_laurentToCone x) := rfl

@[simp] lemma coeff_shiftExtendLaurent (q u : K) (k : ℕ) (x : LaurentLambda K k) :
    (shiftExtendLaurent q u k x).coeff = shiftExtend q u (laurentToCone 1 x).coeff := rfl

/-- The padding of a Laurent monomial is the Laurent monomial at the padded exponent. -/
theorem padElem_laurentToCone_single (α₀ : Fin k →₀ ℤ) (x : Lambda K) :
    padElem (laurentToCone (1 : Equiv.Perm (Fin k)) (AddMonoidAlgebra.single α₀ x))
      = laurentToCone (1 : Equiv.Perm (Fin (k + 1)))
        (AddMonoidAlgebra.single (snocExp α₀ 0) x) := by
  refine ConeRing.ext (funext fun γ => ?_)
  rw [coeff_padElem, coeff_laurentToCone, coeff_laurentToCone, AddMonoidAlgebra.coeff_single,
    AddMonoidAlgebra.coeff_single, Finsupp.single_apply, Finsupp.single_apply]
  by_cases hγ : lastExp γ = 0
  · rw [ite_eq_left hγ]
    refine if_congr ⟨fun h => ?_, fun h => ?_⟩ rfl rfl
    · rw [h, ← hγ, snocExp_initExp]
    · rw [← h, initExp_snocExp]
  · rw [ite_eq_right hγ, ite_eq_right]
    intro h
    rw [← h, lastExp_snocExp] at hγ
    exact absurd rfl hγ

/-- **On a Laurent monomial with a scalar coefficient the displacement is the padding.** -/
theorem shiftExtendLaurent_single_C (q u : K) (k : ℕ) (α₀ : Fin k →₀ ℤ) (a : K) :
    shiftExtendLaurent q u k (AddMonoidAlgebra.single α₀ (MvPolynomial.C a))
      = laurentToCone 1 (AddMonoidAlgebra.single (snocExp α₀ 0) (MvPolynomial.C a)) := by
  have hconst : ∀ α : Fin k →₀ ℤ, ∃ b : K, (laurentToCone (1 : Equiv.Perm (Fin k))
      (AddMonoidAlgebra.single α₀ (MvPolynomial.C a : Lambda K))).coeff α = MvPolynomial.C b := by
    intro α
    rw [coeff_laurentToCone, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    split_ifs
    · exact ⟨a, rfl⟩
    · exact ⟨0, by rw [map_zero]⟩
  refine ConeRing.ext ?_
  rw [coeff_shiftExtendLaurent, shiftExtend_eq_padFamily q u _ hconst, ← coeff_padElem',
    padElem_laurentToCone_single]

/-- The displacement of a power sum, coefficient by coefficient: only `w^0` and `w^j` occur. -/
theorem coeff_plethShift_powerSum (q u : K) {j : ℕ} (hj : 1 ≤ j) (m : ℕ) :
    Polynomial.coeff (plethShift q u (powerSum K j)) m
      = if m = 0 then powerSum K j
        else if m = j then MvPolynomial.C ((1 - q ^ j) * (1 - u ^ j)) else 0 := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hp : powerSum K (i + 1) = (MvPolynomial.X i : Lambda K) := by
    rw [powerSum, Nat.add_sub_cancel]
  have key : plethShift q u (MvPolynomial.X i : Lambda K)
      = Polynomial.C (powerSum K (i + 1))
        + Polynomial.C (MvPolynomial.C ((1 - q ^ (i + 1)) * (1 - u ^ (i + 1))))
          * Polynomial.X ^ (i + 1) := by
    rw [plethShift, MvPolynomial.aeval_X]
  rw [hp, key, ← hp, Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow]
  rcases eq_or_ne m 0 with rfl | hm0
  · rw [ite_eq_left rfl, ite_eq_left rfl, ite_eq_right (by omega : ¬(0 = i + 1)), mul_zero,
      add_zero]
  · rw [ite_eq_right hm0, ite_eq_right hm0, zero_add]
    rcases eq_or_ne m (i + 1) with rfl | hmi
    · rw [ite_eq_left rfl, ite_eq_left rfl, mul_one]
    · rw [ite_eq_right hmi, ite_eq_right hmi, mul_zero]

/-- **The displacement in the last variable of a power sum sitting at the exponent `0`**: it
produces the power sum at the exponent `0` and the kernel scalar on the ray `-j e_{k+1}` of the new
variable. -/
theorem shiftExtendLaurent_single_zero (q u : K) (k : ℕ) {j : ℕ} (hj : 1 ≤ j) :
    shiftExtendLaurent q u k (AddMonoidAlgebra.single 0 (powerSum K j))
      = laurentToCone 1 (AddMonoidAlgebra.single 0 (powerSum K j)
          + AddMonoidAlgebra.single (Finsupp.single (Fin.last k) (-(j : ℤ)))
              (MvPolynomial.C ((1 - q ^ j) * (1 - u ^ j)))) := by
  refine ConeRing.ext (funext fun γ => ?_)
  obtain ⟨α, n, rfl⟩ : ∃ α n, γ = snocExp α n :=
    ⟨initExp γ, lastExp γ, (snocExp_initExp γ).symm⟩
  rw [coeff_shiftExtendLaurent, coeff_laurentToCone, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    AddMonoidAlgebra.coeff_single, AddMonoidAlgebra.coeff_single, Finsupp.single_apply,
    Finsupp.single_apply]
  simp only [zero_eq_snocExp_iff, single_last_eq_snocExp_iff]
  by_cases hα : α = 0
  · subst hα
    simp only [true_and]
    by_cases hn : n ≤ 0
    · rw [shiftExtend_snocExp q u _ 0 hn, coeff_laurentToCone, AddMonoidAlgebra.coeff_single,
        Finsupp.single_eq_same, coeff_plethShift_powerSum q u hj]
      rcases eq_or_ne n 0 with rfl | hn0
      · rw [ite_eq_left rfl, ite_eq_right (by omega : ¬((0 : ℤ) = -(j : ℤ))), add_zero,
          ite_eq_left (by omega : (-(0 : ℤ)).toNat = 0)]
      · rw [ite_eq_right hn0]
        rcases eq_or_ne n (-(j : ℤ)) with rfl | hnj
        · rw [ite_eq_left rfl, zero_add, ite_eq_right (by omega : ¬((-(-(j : ℤ))).toNat = 0)),
            ite_eq_left (by omega : (-(-(j : ℤ))).toNat = j)]
        · rw [ite_eq_right hnj, add_zero, ite_eq_right (by omega : ¬((-n).toNat = 0)),
            ite_eq_right (by omega : ¬((-n).toNat = j))]
    · rw [shiftExtend_snocExp_of_pos q u _ 0 (by omega), ite_eq_right (by omega : ¬(n = 0)),
        ite_eq_right (by omega : ¬(n = -(j : ℤ))), add_zero]
  · rw [ite_eq_right fun h : α = 0 ∧ n = 0 => hα h.1,
      ite_eq_right fun h : α = 0 ∧ n = -(j : ℤ) => hα h.1, add_zero]
    by_cases hn : n ≤ 0
    · rw [shiftExtend_snocExp q u _ α hn, coeff_laurentToCone, AddMonoidAlgebra.coeff_single,
        Finsupp.single_eq_of_ne hα, map_zero, Polynomial.coeff_zero]
    · exact shiftExtend_snocExp_of_pos q u _ α (by omega)

/-! ### The displacement is built one variable at a time -/

/-- **The displacement in `k+1` variables is built one variable at a time.** -/
@[hjo "lem_bglx_shift_multi_iterate"]
theorem shiftExtendElem_plethShiftMulti (q u : K) (k : ℕ) (F : Lambda K) :
    shiftExtendElem q u (laurentToCone 1 (plethShiftMulti q u k F))
        (isDegreeControlled_laurentToCone _)
      = laurentToCone 1 (plethShiftMulti q u (k + 1) F) := by
  have key : (shiftExtendLaurent q u k).comp (plethShiftMulti q u k)
      = (laurentToCone 1).comp (plethShiftMulti q u (k + 1)) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) fun i => ?_
    · simp only [RingHom.coe_comp, Function.comp_apply]
      rw [plethShiftMulti_C, plethShiftMulti_C, shiftExtendLaurent_single_C, snocExp_zero]
    · simp only [RingHom.coe_comp, Function.comp_apply]
      have hj : 1 ≤ i + 1 := Nat.succ_le_succ (Nat.zero_le i)
      have hp : (MvPolynomial.X i : Lambda K) = powerSum K (i + 1) := by
        rw [powerSum, Nat.add_sub_cancel]
      rw [hp, plethShiftMulti_powerSum q u k hj, plethShiftMulti_powerSum q u (k + 1) hj,
        map_add, map_add, map_sum, map_sum, shiftExtendLaurent_single_zero q u k hj,
        Fin.sum_univ_castSucc]
      simp only [shiftExtendLaurent_single_C, snocExp_single]
      rw [map_add]
      abel
  have h := RingHom.congr_fun key F
  simp only [RingHom.coe_comp, Function.comp_apply, shiftExtendLaurent_apply] at h
  exact h

end HJO.Bglx
