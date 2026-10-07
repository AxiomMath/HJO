/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import HJO.CarlssonMellit.AddLetter
public import HJO.CarlssonMellit.PartialCharacter
public meta import HJO.Attr

/-! # Insertion realises the addition of a letter

The raising recursion reads the new auxiliary variable `y_{k+1}` as the *first letter* of the
alphabet: the insertion `Φ_k` of `HJO.Sym.insertFront` substitutes `y_{k+1}` for `x_1` and pushes
every later letter down one place. This file proves the compatibility that makes that reading
usable, `HJO.Dyck.insertFront_realisation`: realising `G ∈ V_k` in the alphabet and then inserting
is the same as adding the genuine letter `y_{k+1}` to `G` and then realising at the level `k+1`.

## Main results

* `HJO.Dyck.insertFront_realisation`,
  `Φ_k(ι_k(G)) = ι_{k+1}(ρ_{k+1}(G))` for every `G ∈ V_k`.

## Implementation notes

**`Φ_k` is not a ring homomorphism, so the proof cannot be transcribed.** The standard argument is
that both sides are `𝕜`-algebra homomorphisms `V_k → P_{k+1}`, compared on the generators
`y_1, …, y_k, p_1, p_2, …`. But `HJO.Sym.insertFront` is not a map `P_k → P_{k+1}` at all, and
`HJO.Sym.insertFront` is the total extension by `0` at the letter-monomials where the defining sum
is infinite. That extension is not additive and not multiplicative, so there is no homomorphism on
the left to compare, and `HJO.Sym.not_injective_insertFront` shows the failure is real and not an
artefact.

*No boundedness hypothesis is needed in the statement.* The natural repair — give
`Φ_k` the domain it has, the series of bounded `x_1`-degree at each letter-monomial — is carried out
here not as a subring but as a **factorisation of the arguments**. Every series the layer inserts is
assembled from a *polynomial* in the first letter, so this file introduces

* `HJO.Sym.splitFirst`: the algebra isomorphism `P_k ≃ₐ P_k⟦x_1⟧` splitting off the first letter,
  obtained from `MvPowerSeries.optionEquivLeft` along the relabelling `HJO.Sym.natOptionEquiv`;
* `HJO.Sym.assembleFirst`: the algebra homomorphism `P_k[T] →ₐ P_k` reading a polynomial in `T` as a
  series whose `x_1`-degree is bounded, `T ↦ x_1`;
* `HJO.Sym.insertPoly`: the algebra homomorphism `P_k[T] →ₐ P_{k+1}` substituting `T ↦ y_{k+1}`;
* `HJO.Dyck.polyRealise`: the realisation of `V_k` in `P_k[T]`, sending `p_r` to
  `T^r + ∑_i x_i^r` — the power sum with its first letter split off.

`HJO.Sym.insertFront_assembleFirst` is then the one place where the coefficient formula of
`HJO.Sym.insertFront` is read: on an assembled polynomial the defining sum has finite support, and
insertion agrees with the substitution `T ↦ y_{k+1}`, which *is* a homomorphism. The
generator comparison survives on both sides of that identity —
`HJO.Dyck.assembleFirst_comp_polyRealise` and `HJO.Dyck.insertPoly_polyRealise` are exactly the two
comparisons it makes, each between genuine algebra homomorphisms — and the statement of
`HJO.Dyck.insertFront_realisation` needs no side condition, because `ι_k(G)` is assembled for every
`G ∈ V_k` by the first of them.

*The realisation is a predicate, as in `HJO.Dyck.IsAuxRealisation`.* Both `ι_k` and `ι_{k+1}` enter
as arbitrary maps satisfying `HJO.Dyck.IsAuxRealisation`, which pins them on `V_k` by
`HJO.Dyck.eq_of_isAuxRealisation`; nothing below reads their values at the auxiliary variables above
the level, where the predicate says nothing.

## References

This file proves `HJO.Dyck.insertFront_realisation`, with the definitions `HJO.Sym.Lambda`,
`HJO.Sweep.piece`, `HJO.Dyck.IsAuxRealisation`, `HJO.Sweep.addLetter` and `HJO.Sym.insertFront`, and
the refutation recorded at `HJO.Sym.insertFront` and `HJO.Sym.injOn_insertFront`. Consumed by
`HJO.Dyck.isSigmaCharacter_cmDPlus`. E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*,
J. Amer. Math. Soc. **31** (2018) 661--697, Section 4.
-/

@[expose] public section

namespace HJO.PhiMul

/-- **The power sum of the alphabet is defined over any base**: a change of coefficients carries it
to the power sum, its coefficients being `0` and `1`. -/
theorem map_alphabetPowerSum {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) (r : ℕ) :
    MvPowerSeries.map φ (alphabetPowerSum A r) = alphabetPowerSum B r := by
  refine MvPowerSeries.ext fun d => ?_
  rw [MvPowerSeries.coeff_map]
  by_cases hd : ∃ i, d = Finsupp.single i r
  · obtain ⟨i, rfl⟩ := hd
    rw [coeff_alphabetPowerSum_single, coeff_alphabetPowerSum_single, map_one]
  · simp only [not_exists] at hd
    rw [coeff_alphabetPowerSum_of_ne _ _ _ hd, coeff_alphabetPowerSum_of_ne _ _ _ hd, map_zero]

end HJO.PhiMul

namespace HJO.Sym

/-! ### Reading the first letter as a separate variable -/

/-- The relabelling `ℕ ≃ Option ℕ` of the alphabet that reads the first letter `x_1` as `none` and
the letter `x_{n+2}` as `some n`: the index bookkeeping behind `HJO.Sym.splitFirst`. -/
def natOptionEquiv : ℕ ≃ Option ℕ where
  toFun n := match n with
    | 0 => none
    | (m + 1) => some m
  invFun o := match o with
    | none => 0
    | some m => m + 1
  left_inv n := by cases n <;> rfl
  right_inv o := by cases o <;> rfl

@[simp] theorem natOptionEquiv_zero : natOptionEquiv 0 = none := rfl

@[simp] theorem natOptionEquiv_succ (n : ℕ) : natOptionEquiv (n + 1) = some n := rfl

@[simp] theorem natOptionEquiv_symm_none : natOptionEquiv.symm none = 0 := rfl

@[simp] theorem natOptionEquiv_symm_some (n : ℕ) : natOptionEquiv.symm (some n) = n + 1 := rfl

/-- The letter-monomial `x_1^a` times `e` pushed up one letter, relabelled along
`HJO.Sym.natOptionEquiv`: it is `e` with the value `a` attached at `none`. This is the index
identity that `HJO.Sym.coeff_coeff_splitFirst` runs on. -/
theorem equivMapDomain_natOptionEquiv (a : ℕ) (e : ℕ →₀ ℕ) :
    Finsupp.equivMapDomain natOptionEquiv (Finsupp.single 0 a + e.mapDomain Nat.succ)
      = e.optionElim a := by
  refine Finsupp.ext fun o => ?_
  rw [Finsupp.equivMapDomain_apply]
  cases o with
  | none =>
    rw [natOptionEquiv_symm_none, Finsupp.optionElim_apply_none, Finsupp.add_apply,
      Finsupp.single_eq_same, Finsupp.mapDomain_of_notMem_range e 0 (by simp), add_zero]
  | some n =>
    rw [natOptionEquiv_symm_some, Finsupp.optionElim_apply_some, Finsupp.add_apply,
      Finsupp.single_eq_of_ne (by omega), Finsupp.mapDomain_apply Nat.succ_injective, zero_add]

variable {K : Type*} [CommRing K]

/-- **Splitting off the first letter**: the algebra isomorphism from `P_k` to the power series
in one variable over `P_k` that reads a series in the alphabet as a series in `x_1` whose
coefficients are series in the remaining letters, relabelled back to the whole alphabet. It is
`MvPowerSeries.optionEquivLeft` along the relabelling `HJO.Sym.natOptionEquiv`. -/
noncomputable def splitFirst (K : Type*) [CommRing K] (k : ℕ) :
    AuxAlphabetSeries K k ≃ₐ[MvPolynomial (Fin k) K] PowerSeries (AuxAlphabetSeries K k) :=
  (MvPowerSeries.renameEquiv (MvPolynomial (Fin k) K) natOptionEquiv).trans
    (MvPowerSeries.optionEquivLeft ℕ (MvPolynomial (Fin k) K))

/-- The coefficients of `HJO.Sym.splitFirst`: the coefficient of `e` in the `a`-th coefficient
is the coefficient of `F` at `x_1^a` times `e` pushed up one letter — which is exactly the index the
defining sum of `HJO.Sym.insertFront` runs over. -/
theorem coeff_coeff_splitFirst (k : ℕ) (F : AuxAlphabetSeries K k) (a : ℕ) (e : ℕ →₀ ℕ) :
    MvPowerSeries.coeff e (PowerSeries.coeff a (splitFirst K k F))
      = MvPowerSeries.coeff (Finsupp.single 0 a + e.mapDomain Nat.succ) F := by
  have h : Finsupp.embDomain natOptionEquiv.toEmbedding
      (Finsupp.single 0 a + e.mapDomain Nat.succ) = e.optionElim a := by
    rw [Finsupp.embDomain_eq_mapDomain, Equiv.coe_toEmbedding,
      ← Finsupp.equivMapDomain_eq_mapDomain, equivMapDomain_natOptionEquiv]
  suffices hsuff : MvPowerSeries.coeff e (PowerSeries.coeff a
      (MvPowerSeries.optionEquivLeft ℕ (MvPolynomial (Fin k) K)
        (MvPowerSeries.rename (⇑natOptionEquiv) F)))
      = MvPowerSeries.coeff (Finsupp.single 0 a + e.mapDomain Nat.succ) F by
    simpa [splitFirst] using hsuff
  simp_rw [← Equiv.coe_toEmbedding, MvPowerSeries.coeff_coeff_optionEquivLeft, ← h,
    MvPowerSeries.coeff_embDomain_rename]

/-- `HJO.Sym.splitFirst` reads the first letter as the new variable. -/
theorem splitFirst_X_zero (k : ℕ) :
    splitFirst K k (MvPowerSeries.X 0) = PowerSeries.X := by
  simp [splitFirst]

/-- **Pushing every letter up one place**: the algebra endomorphism of `P_k` obtained by including
`P_k` in `P_k⟦x_1⟧` as the coefficient of `x_1^0` and reading the result back through
`HJO.Sym.splitFirst`. Its coefficients are `HJO.Sym.coeff_shiftLetters`: the image involves the
letter `x_1` to the degree `0` only, and its coefficient at `x_2^{a_1}x_3^{a_2}⋯` is the coefficient
of the argument at `x_1^{a_1}x_2^{a_2}⋯`. -/
noncomputable def shiftLetters (K : Type*) [CommRing K] (k : ℕ) :
    AuxAlphabetSeries K k →ₐ[K] AuxAlphabetSeries K k :=
  ((splitFirst K k).symm.toAlgHom.restrictScalars K).comp
    (IsScalarTower.toAlgHom K (AuxAlphabetSeries K k) (PowerSeries (AuxAlphabetSeries K k)))

theorem splitFirst_shiftLetters (k : ℕ) (F : AuxAlphabetSeries K k) :
    splitFirst K k (shiftLetters K k F) = PowerSeries.C F := by
  rw [shiftLetters, AlgHom.comp_apply, AlgHom.restrictScalars_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.apply_symm_apply]
  rfl

/-! ### Series of bounded degree in the first letter -/

/-- **Assembling a series from a polynomial in the first letter**: the algebra homomorphism
`P_k[T] → P_k` substituting the first letter `x_1` for `T`. It lands in the series whose
`x_1`-degree is bounded — the domain the remark on `HJO.Sym.insertFront` asks that `Φ_k` be
given — and every series this layer inserts is in its image, by
`HJO.Dyck.assembleFirst_comp_polyRealise`. -/
noncomputable def assembleFirst (K : Type*) [CommRing K] (k : ℕ) :
    Polynomial (AuxAlphabetSeries K k) →ₐ[K] AuxAlphabetSeries K k :=
  Polynomial.aevalTower (shiftLetters K k) (MvPowerSeries.X 0)

theorem assembleFirst_C (k : ℕ) (F : AuxAlphabetSeries K k) :
    assembleFirst K k (Polynomial.C F) = shiftLetters K k F :=
  Polynomial.aevalTower_C _ _ _

theorem assembleFirst_X (k : ℕ) :
    assembleFirst K k Polynomial.X = MvPowerSeries.X 0 :=
  Polynomial.aevalTower_X _ _

/-- **`HJO.Sym.assembleFirst` is the inverse of `HJO.Sym.splitFirst` on polynomials**: splitting off
the first letter of an assembled series returns the polynomial it was assembled from. Both sides are
ring homomorphisms, so the induction on the polynomial is the whole proof. -/
theorem splitFirst_assembleFirst (k : ℕ) (p : Polynomial (AuxAlphabetSeries K k)) :
    splitFirst K k (assembleFirst K k p) = ↑p := by
  induction p using Polynomial.induction_on with
  | C a => rw [assembleFirst_C, splitFirst_shiftLetters, Polynomial.coe_C]
  | add p q hp hq => rw [map_add, map_add, Polynomial.coe_add, hp, hq]
  | monomial n a h =>
    rw [pow_succ, ← mul_assoc, map_mul, map_mul, Polynomial.coe_mul, h, assembleFirst_X,
      splitFirst_X_zero, Polynomial.coe_X]

/-- The coefficient of an assembled series at `x_1^a` times `e` pushed up one letter: it is the
coefficient of `e` in the `a`-th coefficient of the polynomial. -/
theorem coeff_index_assembleFirst (k : ℕ) (p : Polynomial (AuxAlphabetSeries K k)) (a : ℕ)
    (e : ℕ →₀ ℕ) :
    MvPowerSeries.coeff (Finsupp.single 0 a + e.mapDomain Nat.succ) (assembleFirst K k p)
      = MvPowerSeries.coeff e (p.coeff a) := by
  rw [← coeff_coeff_splitFirst, splitFirst_assembleFirst, Polynomial.coeff_coe]

/-- The letter-monomial `d` with its first letter deleted: the exponent of `x_{r+1}` in
`dropFirst d` is the exponent of `x_{r+2}` in `d`. -/
noncomputable def dropFirst (d : ℕ →₀ ℕ) : ℕ →₀ ℕ :=
  Finsupp.comapDomain Nat.succ d Nat.succ_injective.injOn

@[simp] theorem dropFirst_apply (d : ℕ →₀ ℕ) (n : ℕ) : dropFirst d n = d (n + 1) :=
  Finsupp.comapDomain_apply _ _ _ _

/-- Every letter-monomial is `x_1^{d_1}` times its own tail pushed up one letter. -/
theorem single_add_mapDomain_dropFirst (d : ℕ →₀ ℕ) :
    Finsupp.single 0 (d 0) + (dropFirst d).mapDomain Nat.succ = d := by
  refine Finsupp.ext fun n => ?_
  cases n with
  | zero =>
    rw [Finsupp.add_apply, Finsupp.single_eq_same,
      Finsupp.mapDomain_of_notMem_range _ 0 (by simp), add_zero]
  | succ m =>
    rw [Finsupp.add_apply, Finsupp.single_eq_of_ne (by omega),
      Finsupp.mapDomain_apply Nat.succ_injective, zero_add, dropFirst_apply]

/-- The coefficients of an assembled series, at an arbitrary letter-monomial. -/
theorem coeff_assembleFirst (k : ℕ) (p : Polynomial (AuxAlphabetSeries K k)) (d : ℕ →₀ ℕ) :
    MvPowerSeries.coeff d (assembleFirst K k p)
      = MvPowerSeries.coeff (dropFirst d) (p.coeff (d 0)) := by
  conv_lhs => rw [← single_add_mapDomain_dropFirst d]
  rw [coeff_index_assembleFirst]

/-- `x_1` occurs to the degree `0` in a series pushed up one letter: the assembled series of a
constant polynomial is a series in the letters `x_2, x_3, …` alone. -/
theorem coeff_shiftLetters (k : ℕ) (F : AuxAlphabetSeries K k) (d : ℕ →₀ ℕ) :
    MvPowerSeries.coeff d (shiftLetters K k F)
      = if d 0 = 0 then MvPowerSeries.coeff (dropFirst d) F else 0 := by
  rw [← assembleFirst_C, coeff_assembleFirst, Polynomial.coeff_C]
  split_ifs with h
  · rfl
  · rw [MvPowerSeries.coeff_zero]

/-- Pushing the letters up fixes a constant: a constant of `P_k` involves no letter at all. -/
theorem shiftLetters_C (k : ℕ) (c : MvPolynomial (Fin k) K) :
    shiftLetters K k (MvPowerSeries.C c) = MvPowerSeries.C c := by
  refine MvPowerSeries.ext fun d => ?_
  rw [coeff_shiftLetters]
  by_cases hd : d = 0
  · have h0 : dropFirst (0 : ℕ →₀ ℕ) = 0 := Finsupp.ext fun n => rfl
    subst hd
    simp [h0]
  · rw [MvPowerSeries.coeff_C_of_ne_zero hd]
    split_ifs with h0
    · refine MvPowerSeries.coeff_C_of_ne_zero (fun hcon => hd ?_) c
      rw [← single_add_mapDomain_dropFirst d, h0, hcon]
      simp
    · rfl

/-! ### Insertion on an assembled series -/

/-- **Inserting the new auxiliary variable**: the algebra homomorphism `P_k[T] → P_{k+1}`
substituting `y_{k+1}` for `T` and renaming the old auxiliary variables into the first `k` of the
new ones. This is the `Φ_k` on the series of bounded `x_1`-degree, and it *is* a
homomorphism, which `HJO.Sym.insertFront` is not. -/
noncomputable def insertPoly (K : Type*) [CommRing K] (k : ℕ) :
    Polynomial (AuxAlphabetSeries K k) →ₐ[K] AuxAlphabetSeries K (k + 1) :=
  Polynomial.aevalTower (MvPowerSeries.mapAlgHom (MvPolynomial.rename Fin.castSucc))
    (MvPowerSeries.C (MvPolynomial.X (Fin.last k)))

theorem insertPoly_C (k : ℕ) (F : AuxAlphabetSeries K k) :
    insertPoly K k (Polynomial.C F)
      = MvPowerSeries.mapAlgHom (MvPolynomial.rename Fin.castSucc) F :=
  Polynomial.aevalTower_C _ _ _

theorem insertPoly_X (k : ℕ) :
    insertPoly K k Polynomial.X = MvPowerSeries.C (MvPolynomial.X (Fin.last k)) :=
  Polynomial.aevalTower_X _ _

/-- **Insertion on an assembled series is the substitution `T ↦ y_{k+1}`.** This is the one
place the defining sum of `HJO.Sym.insertFront` is read: on `assembleFirst p` the coefficient of `F`
at `x_1^a` is the `a`-th coefficient of `p`, so the sum has finite support and evaluates to the
polynomial `p` at `y_{k+1}`. Everything the `Φ_k` is used for in this layer happens
inside this identity, whose right-hand side is a genuine algebra homomorphism. -/
theorem insertFront_assembleFirst (k : ℕ) (p : Polynomial (AuxAlphabetSeries K k)) :
    insertFront K k (assembleFirst K k p) = insertPoly K k p := by
  have hins : insertPoly K k p = ∑ a ∈ p.support,
      MvPowerSeries.C (MvPolynomial.X (Fin.last k) ^ a) *
        MvPowerSeries.mapAlgHom (MvPolynomial.rename Fin.castSucc) (p.coeff a) := by
    conv_lhs => rw [Polynomial.as_sum_support p]
    rw [map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, insertPoly_C, insertPoly_X,
      ← map_pow]
    ring
  refine MvPowerSeries.ext fun e => ?_
  rw [coeff_insertFront, hins, map_sum]
  have hsub : (Function.support fun a : ℕ => MvPolynomial.X (Fin.last k) ^ a *
      MvPolynomial.rename Fin.castSucc
        (MvPowerSeries.coeff (Finsupp.single 0 a + e.mapDomain Nat.succ)
          (assembleFirst K k p))) ⊆ ↑p.support := by
    intro a ha
    simp only [Function.mem_support, ne_eq] at ha
    by_contra hmem
    rw [Finset.mem_coe, Polynomial.notMem_support_iff] at hmem
    rw [coeff_index_assembleFirst, hmem, MvPowerSeries.coeff_zero, map_zero, mul_zero] at ha
    exact ha rfl
  rw [finsum_eq_sum_of_support_subset _ hsub]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [coeff_index_assembleFirst, MvPowerSeries.coeff_C_mul, MvPowerSeries.mapAlgHom_apply,
    MvPowerSeries.coeff_map]
  rfl

end HJO.Sym

namespace HJO.Dyck

variable {K : Type*} [CommRing K]

/-! ### The realisation with the first letter split off -/

/-- **The realisation of `V_k` with the first letter split off**: the `𝕜`-algebra homomorphism from
the total space of the sweep to `P_k[T]` sending the power sum `p_r` to `T^r + ∑_i x_i^r` and each
auxiliary variable below the level to itself. Composed with `HJO.Sym.assembleFirst` it is the
realisation `ι_k` of `HJO.Dyck.IsAuxRealisation` (`HJO.Dyck.assembleFirst_comp_polyRealise`), and
composed with `HJO.Sym.insertPoly` it is `ι_{k+1} ∘ ρ_{k+1}` (`HJO.Dyck.insertPoly_polyRealise`):
the two comparisons the proof of `HJO.Dyck.insertFront_realisation` makes. -/
noncomputable def polyRealise (K : Type*) [CommRing K] (k : ℕ) :
    Sweep.Total K →ₐ[K] Polynomial (Sym.AuxAlphabetSeries K k) :=
  MvPolynomial.aevalTower
    (MvPolynomial.aeval fun i : ℕ => Polynomial.X ^ (i + 1) +
      Polynomial.C (PhiMul.alphabetPowerSum (MvPolynomial (Fin k) K) (i + 1)))
    fun j : ℕ => if h : j < k then Polynomial.C (MvPowerSeries.C (MvPolynomial.X ⟨j, h⟩)) else 0

theorem polyRealise_powerSum (k r : ℕ) :
    polyRealise K k (MvPolynomial.C (Sym.powerSum K (r + 1)))
      = Polynomial.X ^ (r + 1) +
        Polynomial.C (PhiMul.alphabetPowerSum (MvPolynomial (Fin k) K) (r + 1)) := by
  rw [polyRealise, MvPolynomial.aevalTower_C, Sym.powerSum, Nat.add_sub_cancel,
    MvPolynomial.aeval_X]

theorem polyRealise_X (k j : ℕ) :
    polyRealise K k (MvPolynomial.X j) =
      if h : j < k then Polynomial.C (MvPowerSeries.C (MvPolynomial.X ⟨j, h⟩)) else 0 := by
  rw [polyRealise, MvPolynomial.aevalTower_X]

theorem auxRealise_powerSum (k r : ℕ) :
    auxRealise K k (MvPolynomial.C (Sym.powerSum K (r + 1)))
      = PhiMul.alphabetPowerSum (MvPolynomial (Fin k) K) (r + 1) := by
  rw [auxRealise, MvPolynomial.aevalTower_C, Sym.powerSum, Nat.add_sub_cancel,
    MvPolynomial.aeval_X]

/-- **The power sum, assembled from its first letter.** `∑_i x_i^r` is `x_1^r` plus the same power
sum in the letters `x_2, x_3, …`, which is the value of `HJO.Dyck.polyRealise` on `p_r` read through
`HJO.Sym.assembleFirst`. -/
theorem assembleFirst_polyRealise_powerSum (k r : ℕ) :
    Sym.assembleFirst K k (Polynomial.X ^ (r + 1) +
        Polynomial.C (PhiMul.alphabetPowerSum (MvPolynomial (Fin k) K) (r + 1)))
      = PhiMul.alphabetPowerSum (MvPolynomial (Fin k) K) (r + 1) := by
  refine MvPowerSeries.ext fun d => ?_
  rw [Sym.coeff_assembleFirst, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C]
  by_cases h1 : d 0 = r + 1
  · have h0 : ¬ (d 0 = 0) := by omega
    rw [ite_eq_left h1, ite_eq_right h0, add_zero]
    by_cases he : Sym.dropFirst d = 0
    · have hd : d = Finsupp.single 0 (r + 1) := by
        rw [← Sym.single_add_mapDomain_dropFirst d, he, h1]
        simp
      rw [he, hd, MvPowerSeries.coeff_zero_one, PhiMul.coeff_alphabetPowerSum_single]
    · rw [MvPowerSeries.coeff_one, ite_eq_right he]
      refine (PhiMul.coeff_alphabetPowerSum_of_ne (MvPolynomial (Fin k) K) (r + 1) d
        fun i hi => he ?_).symm
      have hi0 : i = 0 := by
        by_contra hne
        rw [hi, Finsupp.single_apply, ite_eq_right (by omega)] at h1
        omega
      refine Finsupp.ext fun n => ?_
      rw [Sym.dropFirst_apply, hi, hi0, Finsupp.single_apply, ite_eq_right (by omega)]
      rfl
  · by_cases h0 : d 0 = 0
    · rw [ite_eq_right h1, ite_eq_left h0, zero_add]
      have hd : d = (Sym.dropFirst d).mapDomain Nat.succ := by
        conv_lhs => rw [← Sym.single_add_mapDomain_dropFirst d]
        rw [h0, Finsupp.single_zero, zero_add]
      by_cases he : ∃ i, Sym.dropFirst d = Finsupp.single i (r + 1)
      · obtain ⟨i, hi⟩ := he
        have hd' : d = Finsupp.single (i + 1) (r + 1) := by
          rw [hd, hi, Finsupp.mapDomain_single]
        rw [hi, hd', PhiMul.coeff_alphabetPowerSum_single, PhiMul.coeff_alphabetPowerSum_single]
      · simp only [not_exists] at he
        rw [PhiMul.coeff_alphabetPowerSum_of_ne _ _ _ he]
        refine (PhiMul.coeff_alphabetPowerSum_of_ne _ _ _ fun i hi => ?_).symm
        have hi0 : i ≠ 0 := by
          intro hcon
          rw [hi, hcon, Finsupp.single_eq_same] at h0
          omega
        obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
        refine he m (Finsupp.ext fun n => ?_)
        rw [Sym.dropFirst_apply, hi, Finsupp.single_apply, Finsupp.single_apply]
        simp only [Nat.succ_inj]
    · rw [ite_eq_right h1, ite_eq_right h0, add_zero, MvPowerSeries.coeff_zero]
      refine (PhiMul.coeff_alphabetPowerSum_of_ne _ _ _ fun i hi => ?_).symm
      rw [hi] at h0 h1
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · rw [Finsupp.single_eq_same] at h1
        exact h1 rfl
      · rw [Finsupp.single_apply, ite_eq_right (by omega)] at h0
        exact h0 rfl

/-- **`HJO.Sym.assembleFirst ∘ HJO.Dyck.polyRealise` is the realisation `ι_k`.** Both are
`𝕜`-algebra homomorphisms from the total space to `P_k`, so they are compared on the generators: on
`p_r` by `HJO.Dyck.assembleFirst_polyRealise_powerSum`, and on the auxiliary variables because
pushing the letters up fixes a constant. -/
theorem assembleFirst_comp_polyRealise (K : Type*) [CommRing K] (k : ℕ) :
    (Sym.assembleFirst K k).comp (polyRealise K k) = auxRealise K k := by
  refine MvPolynomial.algHom_ext' ?_ fun j => ?_
  · refine MvPolynomial.algHom_ext fun r => ?_
    have hC : (algebraMap (Sym.Lambda K) (Sweep.Total K)) (MvPolynomial.X r)
        = MvPolynomial.C (Sym.powerSum K (r + 1)) := by
      simp [Sym.powerSum]
    simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', hC]
    rw [polyRealise_powerSum, assembleFirst_polyRealise_powerSum, auxRealise_powerSum]
  · rw [AlgHom.comp_apply, polyRealise_X, auxRealise, MvPolynomial.aevalTower_X]
    split_ifs with h
    · rw [Sym.assembleFirst_C, Sym.shiftLetters_C]
    · rw [map_zero]

/-! ### The two realisations of `V_k` are matched by the insertion -/

/-- Two `𝕜`-algebra homomorphisms out of the total space that agree on the symmetric functions and
on the auxiliary variables below the level agree on `V_k`. This is the induction
`HJO.Dyck.eq_of_isAuxRealisation` runs, with the hypotheses it actually uses: the values above the
level are never read. -/
theorem eq_on_piece {B : Type*} [CommRing B] [Algebra K B] {k : ℕ}
    {f g : Sweep.Total K →ₐ[K] B}
    (hC : ∀ a : Sym.Lambda K, f (MvPolynomial.C a) = g (MvPolynomial.C a))
    (hX : ∀ j < k, f (MvPolynomial.X j) = g (MvPolynomial.X j))
    {G : Sweep.Total K} (hG : G ∈ Sweep.piece K k) : f G = g G := by
  rw [Sweep.piece, MvPolynomial.supported_eq_adjoin_X] at hG
  induction hG using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨j, hj, rfl⟩ := hy
    exact hX j hj
  | algebraMap r => exact hC r
  | add y z _ _ hy hz => rw [map_add, map_add, hy, hz]
  | mul y z _ _ hy hz => rw [map_mul, map_mul, hy, hz]

/-- **`HJO.Sym.insertPoly ∘ HJO.Dyck.polyRealise` is `ι_{k+1} ∘ ρ_{k+1}` on `V_k`.** Both are
`𝕜`-algebra homomorphisms, so they are compared on the generators: on `p_r` both
give `y_{k+1}^r + ∑_i x_i^r`, the left because `T ↦ y_{k+1}` and the right because
`ρ_{k+1}(p_r) = p_r + y_{k+1}^r`; and on `y_j` with `j ≤ k` both give `y_j`. -/
theorem insertPoly_polyRealise {k : ℕ}
    {ι : Sweep.Total K →ₐ[K] Sym.AuxAlphabetSeries K (k + 1)} (h : IsAuxRealisation (k + 1) ι)
    {G : Sweep.Total K} (hG : G ∈ Sweep.piece K k) :
    Sym.insertPoly K k (polyRealise K k G) = ι (Sweep.addLetter K (k + 1) G) := by
  have hlast : ι (Sweep.auxVar (k + 1)) = MvPowerSeries.C (MvPolynomial.X (Fin.last k)) := by
    have := h.map_auxVar (Fin.last k)
    rwa [Fin.val_last] at this
  refine eq_on_piece (f := (Sym.insertPoly K k).comp (polyRealise K k))
    (g := ι.comp (Sweep.addLetter K (k + 1))) (fun a => ?_) (fun j hj => ?_) hG
  · have key : ((Sym.insertPoly K k).comp (polyRealise K k)).comp
          (IsScalarTower.toAlgHom K (Sym.Lambda K) (Sweep.Total K))
        = (ι.comp (Sweep.addLetter K (k + 1))).comp
          (IsScalarTower.toAlgHom K (Sym.Lambda K) (Sweep.Total K)) := by
      refine MvPolynomial.algHom_ext fun r => ?_
      have hC : (algebraMap (Sym.Lambda K) (Sweep.Total K)) (MvPolynomial.X r)
          = MvPolynomial.C (Sym.powerSum K (r + 1)) := by
        simp [Sym.powerSum]
      have hiota : ι (MvPolynomial.C (Sym.powerSum K (r + 1)))
          = PhiMul.alphabetPowerSum (MvPolynomial (Fin (k + 1)) K) (r + 1) := by
        rw [apply_C_eq_of_isAuxRealisation h (isAuxRealisation_auxRealise K (k + 1)),
          auxRealise_powerSum]
      simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', hC]
      rw [polyRealise_powerSum, map_add, map_pow, Sym.insertPoly_X, Sym.insertPoly_C,
        MvPowerSeries.mapAlgHom_apply, PhiMul.map_alphabetPowerSum, Sweep.addLetter_powerSum,
        map_add, map_pow, hiota, hlast, ← map_pow]
      exact add_comm _ _
    exact AlgHom.congr_fun key a
  · have hj' : j < k + 1 := by omega
    have hX : (MvPolynomial.X j : Sweep.Total K)
        = Sweep.auxVar ((⟨j, hj'⟩ : Fin (k + 1)) + 1) := by
      rw [Sweep.auxVar]
      simp
    rw [AlgHom.comp_apply, AlgHom.comp_apply, polyRealise_X, dite_eq_left hj,
      Sweep.addLetter_auxVar, Sym.insertPoly_C, MvPowerSeries.mapAlgHom_apply,
      MvPowerSeries.map_C, hX, h.map_auxVar ⟨j, hj'⟩]
    simp

/-! ### Insertion realises the addition of a letter -/

/-- **Insertion realises the addition of a letter.**
`Φ_k(ι_k(G)) = ι_{k+1}(ρ_{k+1}(G))` for every `G ∈ V_k`: substituting the new auxiliary variable
`y_{k+1}` for the first letter of the realisation of `G` is the same as adding the genuine letter
`y_{k+1}` to `G` and realising at the level `k + 1`.

No boundedness hypothesis appears, although `HJO.Sym.insertFront` is the extension by `0` of the
defining prescription and not the map: `ι_k(G)` is *assembled* from a polynomial in
the first letter for every `G ∈ V_k` — that is `HJO.Dyck.assembleFirst_comp_polyRealise` — and on an
assembled series the insertion is the substitution `T ↦ y_{k+1}`, by
`HJO.Sym.insertFront_assembleFirst`. So the value read here is the intended one, and the two
generator comparisons the proof makes are
`HJO.Dyck.assembleFirst_comp_polyRealise` and `HJO.Dyck.insertPoly_polyRealise`. -/
@[hjo "lem_cm_insert_realisation"]
theorem insertFront_realisation {k : ℕ}
    {ι : Sweep.Total K →ₐ[K] Sym.AuxAlphabetSeries K k} (h : IsAuxRealisation k ι)
    {ι' : Sweep.Total K →ₐ[K] Sym.AuxAlphabetSeries K (k + 1)} (h' : IsAuxRealisation (k + 1) ι')
    {G : Sweep.Total K} (hG : G ∈ Sweep.piece K k) :
    Sym.insertFront K k (ι G) = ι' (Sweep.addLetter K (k + 1) G) := by
  have hassemble : ι G = Sym.assembleFirst K k (polyRealise K k G) := by
    rw [eq_of_isAuxRealisation h (isAuxRealisation_auxRealise K k) hG,
      ← assembleFirst_comp_polyRealise K k, AlgHom.comp_apply]
  rw [hassemble, Sym.insertFront_assembleFirst, insertPoly_polyRealise h' hG]

end HJO.Dyck
