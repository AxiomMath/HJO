/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.AddLetter
public import HJO.CarlssonMellit.PartialCharacter
public import HJO.CarlssonMellit.ZDeltaDefined
public meta import HJO.Attr

/-! # The expansion coefficients are symmetric in the full alphabet

The raising recursion expands `χ'_{Id_k}(π)` in powers of the distinguished letter and reads the
coefficients as `g_j(π)[X + y_k]` with `g_j(π) ∈ V_{k-1}`. This file proves that every such
`g[X + y_k]` is fixed by every relabelling `ŝ_ρ` of the merged alphabet — it is symmetric in
`y_k, x_1, x_2, …` and not merely in the free variables — which is
`HJO.Dyck.realiseAddLetter_mem_zSymmSubring` and is the symmetry the lowering step uses to move
`Δ_{y_k,x_1}` past the coefficients.

The argument is as follows. The elements fixed by every `ŝ_ρ` form a subring of `Z^{(k+1)}`,
because `ŝ_ρ` is a ring homomorphism there (`HJO.Sym.zPermEquiv`); `V_{k-1}` is generated as a
`𝕂`-algebra by the auxiliary variables `y_1, …, y_{k-1}` and the power sums `p_1, p_2, …`; and the
images of those generators lie in that subring. The auxiliary variables go to scalars of the lower
coefficient field, which every relabelling fixes. A power sum `p_r` goes to
`y_{k+1}^r + ∑_{l}x_l^r`, the `r`-th power sum of the *whole* merged alphabet, whose merged
coefficients are `1` at every merged monomial `z_a^r` and `0` elsewhere — a family the relabelling
permutes.

## Main definitions

* `HJO.Sym.zSymmSubring`: the members of `Z^{(k+1)}` fixed by every relabelling of the merged
  alphabet, as a subring of `P°_{k+1}`. This is the "symmetric in `y_k, x_1, x_2, …`" of the
  statement.

## Main results

* `HJO.Sym.mem_zSymmSubring_of_coeff`: a series whose coefficients are those of a power sum of the
  merged alphabet is symmetric. This is where the whole content sits.
* `HJO.Dyck.realiseAddLetter_mem_zSymmSubring`: `g[X + y_k]`, realised in `P°_{k+1}`, lies in
  `Z^{(k+1)}` and is fixed by every `ŝ_ρ`.
* `HJO.Dyck.zPerm_realiseAddLetter`: the same read as an invariance
  under every `ŝ_ρ`.

## Implementation notes

*The finitarity hypothesis on `ρ` is dead and is dropped.* One would restrict to the permutations of
the letters fixing all but finitely many, as is needed at
`HJO.Sym.zPerm_eq_self_of_forall_zSwap_eq_self`, where the proof factors a permutation into adjacent
interchanges. Here nothing of the kind happens: the merged coefficients of a power sum of the merged
alphabet are the indicator of the set `{z_a^r : a a letter}`, and *every* permutation of the letters
permutes that set. So the statement is proved for an arbitrary `ρ : Equiv.Perm (Option ℕ)`, and the
finitary case is an instance.

*The realisation is a hypothesis, not a construction.* `HJO.Dyck.IsAuxRealisation` is the
realisation `ι_k` stated as a property — the values on the power sums pinned coefficientwise and the
auxiliary variables fixed — and that is all this proof reads. So the statement is for an arbitrary
`ι` with that property, exactly as `HJO.Dyck.isSigmaCharacter_one_of_isEmpty` of
`HJO.CarlssonMellit.PartialCharacter` is.

*The level is `k + 1` and the added letter is `y_{k+1}`.* The `g ∈ V_{k-1}` with the
letter `y_k` adjoined reads here as `G ∈ HJO.Sweep.piece K k` with `HJO.Sweep.addLetter K (k + 1)`
applied, realised at the level `k + 1`; the lower coefficient field `𝕂(y_1, …, y_{k-1})` is
`HJO.Sym.AuxFrac K k` entering by `HJO.Sym.auxFracCastSucc`, and the distinguished letter is
`HJO.Sym.yFrac K (Fin.last k)`. No subtraction appears on any index.

*The symmetric elements are a `Subring` and not a `Subalgebra`.* As everywhere in this layer, a
subalgebra over the lower coefficient field would need an `Algebra (AuxFrac K k) (P°_{k+1})`
instance, which is the diamond `HJO.CarlssonMellit.SeriesGrading` was set up to avoid. The
workaround used throughout — a ring-theoretic package plus a pointwise-fixed-base lemma — applies:
the subring carries the constants of the lower field through `HJO.Sym.zPerm_C`, and that together
with multiplicativity *is* base-linearity.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018)
661--697, Section 4, where the symmetry is used without comment.
-/

@[expose] public section

namespace HJO.Sym

variable {K : Type*} [CommRing K] [IsDomain K] {k : ℕ}

/-! ### The symmetric members of the alphabet-graded ring -/

/-- A relabelling of the merged alphabet is additive on differences of members of `Z^{(k+1)}`. -/
theorem zPerm_neg_of_mem_zRing (ρ : Equiv.Perm (Option ℕ))
    {F : AuxAlphabetSeriesFrac K (k + 1)} (hF : F ∈ zRing K k) :
    zPerm K k ρ (-F) = -zPerm K k ρ F := by
  have h := zPerm_add_of_mem_zRing ρ hF (neg_mem_zRing hF)
  rw [add_neg_cancel, zPerm_zero] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

/-- A relabelling fixes the unit series. -/
@[simp]
theorem zPerm_one_series (ρ : Equiv.Perm (Option ℕ)) :
    zPerm K k ρ (1 : AuxAlphabetSeriesFrac K (k + 1)) = 1 := by
  have h : (1 : AuxAlphabetSeriesFrac K (k + 1)) = MvPowerSeries.C (auxFracCastSucc K k 1) := by
    rw [map_one, map_one]
  rw [h, zPerm_C]

/-- **The symmetric members of `Z^{(k+1)}`**: those fixed by every relabelling `ŝ_ρ` of the merged
alphabet `y_{k+1}, x₁, x₂, …`. This is the "symmetric in `y_k, x_1, x_2, …`", and it is
a subring because `ŝ_ρ` is a ring homomorphism of `Z^{(k+1)}` (`HJO.Sym.zPermEquiv`). -/
noncomputable def zSymmSubring (K : Type*) [CommRing K] [IsDomain K] (k : ℕ) :
    Subring (AuxAlphabetSeriesFrac K (k + 1)) where
  carrier := {F | F ∈ zRing K k ∧ ∀ ρ : Equiv.Perm (Option ℕ), zPerm K k ρ F = F}
  one_mem' := ⟨one_mem_zRing, fun ρ => zPerm_one_series ρ⟩
  mul_mem' hF hH :=
    ⟨mul_mem_zRing hF.1 hH.1, fun ρ => by
      rw [zPerm_mul_of_mem_zRing ρ hF.1 hH.1, hF.2 ρ, hH.2 ρ]⟩
  zero_mem' := ⟨zero_mem_zRing, fun ρ => zPerm_zero ρ⟩
  add_mem' hF hH :=
    ⟨add_mem_zRing hF.1 hH.1, fun ρ => by
      rw [zPerm_add_of_mem_zRing ρ hF.1 hH.1, hF.2 ρ, hH.2 ρ]⟩
  neg_mem' hF := ⟨neg_mem_zRing hF.1, fun ρ => by rw [zPerm_neg_of_mem_zRing ρ hF.1, hF.2 ρ]⟩

theorem mem_zSymmSubring {F : AuxAlphabetSeriesFrac K (k + 1)} :
    F ∈ zSymmSubring K k ↔ F ∈ zRing K k ∧ ∀ ρ : Equiv.Perm (Option ℕ), zPerm K k ρ F = F :=
  Iff.rfl

/-- The constants of the lower coefficient field are symmetric: every relabelling fixes them, which
is `HJO.Sym.zPerm_C`. With multiplicativity this is the base-linearity required of
`ŝ_ρ`. -/
theorem C_auxFracCastSucc_mem_zSymmSubring (c : AuxFrac K k) :
    (MvPowerSeries.C (auxFracCastSucc K k c) : AuxAlphabetSeriesFrac K (k + 1))
      ∈ zSymmSubring K k :=
  ⟨C_auxFracCastSucc_mem_zRing c, fun ρ => zPerm_C ρ c⟩

/-- The constants of the base are symmetric. -/
theorem C_scalarFrac_mem_zSymmSubring (a : K) :
    (MvPowerSeries.C (scalarFrac K a) : AuxAlphabetSeriesFrac K (k + 1)) ∈ zSymmSubring K k := by
  rw [← auxFracCastSucc_scalarFrac (K := K) (k := k) a]
  exact C_auxFracCastSucc_mem_zSymmSubring _

/-! ### A power sum of the merged alphabet is symmetric -/

/-- Two merged exponent vectors agreeing on the letters and on the distinguished letter are
equal. -/
private theorem eq_of_some_eq_of_none_eq {ν μ : Option ℕ →₀ ℕ} (hs : ν.some = μ.some)
    (hn : ν none = μ none) : ν = μ := by
  refine Finsupp.ext fun a => ?_
  cases a with
  | none => exact hn
  | some i => rw [← Finsupp.some_apply, ← Finsupp.some_apply, hs]

/-- The merged exponent vectors of the monomials of a power sum: `z_a^{r+1}` for a letter `a`. -/
private def IsMergedPow (r : ℕ) (ν : Option ℕ →₀ ℕ) : Prop :=
  ∃ a : Option ℕ, ν = Finsupp.single a (r + 1)

private theorem isMergedPow_equivMapDomain_iff (ρ : Equiv.Perm (Option ℕ)) (r : ℕ)
    (ν : Option ℕ →₀ ℕ) :
    IsMergedPow r (Finsupp.equivMapDomain ρ.symm ν) ↔ IsMergedPow r ν := by
  refine ⟨fun ⟨a, ha⟩ => ⟨ρ a, ?_⟩, fun ⟨a, ha⟩ => ⟨ρ.symm a, ?_⟩⟩
  · rw [← equivMapDomain_equivMapDomain_symm ρ ν, ha, Finsupp.equivMapDomain_single]
  · rw [ha, Finsupp.equivMapDomain_single]

private theorem isMergedPow_iff_of_some_eq_zero (r : ℕ) {ν : Option ℕ →₀ ℕ} (hs : ν.some = 0) :
    IsMergedPow r ν ↔ ν none = r + 1 := by
  refine ⟨fun ⟨a, ha⟩ => ?_, fun h => ⟨none, eq_of_some_eq_of_none_eq ?_ ?_⟩⟩
  · cases a with
    | none => rw [ha, Finsupp.single_eq_same]
    | some i =>
      have h1 : ν.some = Finsupp.single i (r + 1) := by rw [ha, Finsupp.some_single_some]
      rw [hs] at h1
      exact absurd h1.symm (Finsupp.single_ne_zero.2 (Nat.succ_ne_zero r))
  · rw [hs, Finsupp.some_single_none]
  · rw [h, Finsupp.single_eq_same]

private theorem isMergedPow_iff_of_some_eq_single (r : ℕ) {ν : Option ℕ →₀ ℕ} {i : ℕ}
    (hs : ν.some = Finsupp.single i (r + 1)) : IsMergedPow r ν ↔ ν none = 0 := by
  refine ⟨fun ⟨a, ha⟩ => ?_, fun h => ⟨some i, eq_of_some_eq_of_none_eq ?_ ?_⟩⟩
  · cases a with
    | none =>
      have h1 : ν.some = 0 := by rw [ha, Finsupp.some_single_none]
      rw [hs] at h1
      exact absurd h1 (Finsupp.single_ne_zero.2 (Nat.succ_ne_zero r))
    | some j =>
      have h2 : ν.some = Finsupp.single j (r + 1) := by rw [ha, Finsupp.some_single_some]
      have hji : j = i :=
        Finsupp.single_left_injective (Nat.succ_ne_zero r) (h2.symm.trans hs)
      rw [ha, hji, Finsupp.single_eq_of_ne (by simp)]
  · rw [hs, Finsupp.some_single_some]
  · rw [h, Finsupp.single_eq_of_ne (by simp)]

private theorem not_isMergedPow (r : ℕ) {ν : Option ℕ →₀ ℕ} (hs0 : ν.some ≠ 0)
    (hsi : ∀ i : ℕ, ν.some ≠ Finsupp.single i (r + 1)) : ¬ IsMergedPow r ν := by
  rintro ⟨a, ha⟩
  cases a with
  | none => exact hs0 (by rw [ha, Finsupp.some_single_none])
  | some i => exact hsi i (by rw [ha, Finsupp.some_single_some])

/-- **A series whose coefficients are those of a power sum of the merged alphabet is symmetric.**
The hypotheses say that the coefficient is `y_{k+1}^{r+1}` at the empty letter-monomial, `1` at each
`x_i^{r+1}` and `0` elsewhere — that is, that the series is
`y_{k+1}^{r+1} + ∑_{i}x_i^{r+1}`, the `(r+1)`-st power sum of the merged alphabet. Its merged
coefficients are then the indicator of the merged monomials `z_a^{r+1}`, a family that every
relabelling of the letters permutes, so every `ŝ_ρ` fixes it. -/
theorem mem_zSymmSubring_of_coeff {F : AuxAlphabetSeriesFrac K (k + 1)} {r : ℕ}
    (h0 : MvPowerSeries.coeff 0 F = yFrac K (Fin.last k) ^ (r + 1))
    (h1 : ∀ i : ℕ, MvPowerSeries.coeff (Finsupp.single i (r + 1)) F = 1)
    (hz : ∀ α : ℕ →₀ ℕ, α ≠ 0 → (∀ i : ℕ, α ≠ Finsupp.single i (r + 1)) →
      MvPowerSeries.coeff α F = 0) :
    F ∈ zSymmSubring K k := by
  classical
  have hone : (1 : AuxFrac K (k + 1))
      = auxFracCastSucc K k 1 * yFrac K (Fin.last k) ^ 0 := by rw [map_one, pow_zero, mul_one]
  have hy : yFrac K (Fin.last k) ^ (r + 1)
      = auxFracCastSucc K k 1 * yFrac K (Fin.last k) ^ (r + 1) := by rw [map_one, one_mul]
  have hzero : (0 : AuxFrac K (k + 1))
      = auxFracCastSucc K k 0 * yFrac K (Fin.last k) ^ 0 := by rw [map_zero, zero_mul]
  -- the series lies in the graded piece of merged degree `r + 1`
  have hgr : F ∈ zGraded K k (r + 1) := by
    refine ⟨fun α b hb => ?_, fun α hα => ?_⟩
    · rcases eq_or_ne α 0 with rfl | hα0
      · rw [h0, show b = r + 1 from by simpa using hb]
        exact ⟨1, hy⟩
      by_cases hαi : ∃ i : ℕ, α = Finsupp.single i (r + 1)
      · obtain ⟨i, rfl⟩ := hαi
        rw [h1 i, show b = 0 from by rw [Finsupp.degree_single] at hb; omega]
        exact ⟨1, hone⟩
      · rw [hz α hα0 fun i hi => hαi ⟨i, hi⟩]
        exact ⟨0, by rw [map_zero, zero_mul]⟩
    · refine hz α (fun h => ?_) fun i hi => ?_
      · rw [h, map_zero] at hα; omega
      · rw [hi, Finsupp.degree_single] at hα; omega
  -- the merged coefficients are the indicator of the merged monomials `z_a^{r+1}`
  have hcoeff : ∀ ν : Option ℕ →₀ ℕ,
      zCoeff K k F ν = if IsMergedPow r ν then 1 else 0 := by
    intro ν
    rw [zCoeff]
    rcases eq_or_ne ν.some 0 with hs | hs
    · rw [hs, h0, hy, yFracCoeff_mul_yFrac_pow, ite_congr
        (propext (isMergedPow_iff_of_some_eq_zero r hs)) (fun _ => rfl) fun _ => rfl]
    by_cases hsi : ∃ i : ℕ, ν.some = Finsupp.single i (r + 1)
    · obtain ⟨i, hi⟩ := hsi
      rw [hi, h1 i, hone, yFracCoeff_mul_yFrac_pow, ite_congr
        (propext (isMergedPow_iff_of_some_eq_single r hi)) (fun _ => rfl) fun _ => rfl]
    · simp only [not_exists] at hsi
      rw [hz ν.some hs hsi, yFracCoeff_zero, ite_eq_right (not_isMergedPow r hs hsi)]
  refine ⟨zGraded_subset_zRing K k (r + 1) hgr, fun ρ => ?_⟩
  refine eq_of_zCoeff_eq
    (coeff_mem_range_yFracEval_of_mem_zRing
      (zPerm_mem_zRing ρ (zGraded_subset_zRing K k (r + 1) hgr)))
    (coeff_mem_range_yFracEval_of_mem_zRing (zGraded_subset_zRing K k (r + 1) hgr)) fun ν => ?_
  rw [zCoeff_zPerm ρ (zGraded_subset_zRing K k (r + 1) hgr), hcoeff, hcoeff,
    show (if IsMergedPow r (Finsupp.equivMapDomain ρ.symm ν) then (1 : AuxFrac K k) else 0)
      = if IsMergedPow r ν then 1 else 0 from by
        rw [ite_congr (propext (isMergedPow_equivMapDomain_iff ρ r ν)) (fun _ => rfl)
          fun _ => rfl]]

end HJO.Sym


namespace HJO.Dyck

open HJO.Sweep

variable {K : Type*} [CommRing K] [IsDomain K] {k : ℕ}
  {ι : Sweep.Total K →ₐ[K] Sym.AuxAlphabetSeries K (k + 1)}

/-! ### The coefficientwise inclusion on a constant -/

omit [IsDomain K] in
/-- The inclusion `P_m ⊆ P°_m` on a constant series: the coefficient is included. -/
theorem auxToFrac_C (m : ℕ) (p : MvPolynomial (Fin m) K) :
    Sym.auxToFrac K m (MvPowerSeries.C p)
      = MvPowerSeries.C (algebraMap (MvPolynomial (Fin m) K) (Sym.AuxFrac K m) p) := by
  classical
  refine MvPowerSeries.ext fun α => ?_
  rw [Sym.coeff_auxToFrac, MvPowerSeries.coeff_C, MvPowerSeries.coeff_C]
  rcases eq_or_ne α 0 with rfl | h
  · rw [ite_eq_left rfl, ite_eq_left rfl]
  · rw [ite_eq_right h, ite_eq_right h, map_zero]

/-! ### The realisation of the enlarged alphabet -/

/-- **`g ↦ g[X + y_{k+1}]`, realised in `P°_{k+1}`**: the `ρ_k` followed by a
realisation with auxiliary variables and by the coefficientwise inclusion `P_{k+1} ⊆ P°_{k+1}`. A
ring homomorphism, which is all the symmetry argument uses. -/
noncomputable def realiseAddLetter (K : Type*) [CommRing K] [IsDomain K] (k : ℕ)
    (ι : Sweep.Total K →ₐ[K] Sym.AuxAlphabetSeries K (k + 1)) :
    Sweep.Total K →+* Sym.AuxAlphabetSeriesFrac K (k + 1) :=
  ((Sym.auxToFrac K (k + 1)).toRingHom.comp ι.toRingHom).comp (addLetter K (k + 1)).toRingHom

theorem realiseAddLetter_apply (G : Sweep.Total K) :
    realiseAddLetter K k ι G
      = Sym.auxToFrac K (k + 1) (ι (addLetter K (k + 1) G)) :=
  rfl

/-! ### The images of the generators -/

/-- **The image of an auxiliary variable below the level is a constant of the lower coefficient
field.** `ρ_{k+1}` fixes `y_{j+1}`, the realisation carries it to the scalar `y_{j+1}`, and for
`j < k` that scalar comes from `𝕂(y_1, …, y_k)`; every relabelling of the merged alphabet fixes it,
by `HJO.Sym.zPerm_C`. -/
theorem realiseAddLetter_X_mem (hι : IsAuxRealisation (k + 1) ι) {j : ℕ} (hj : j < k) :
    realiseAddLetter K k ι (MvPolynomial.X j) ∈ Sym.zSymmSubring K k := by
  have hj' : j < k + 1 := by omega
  have haux : (MvPolynomial.X j : Sweep.Total K) = auxVar (((⟨j, hj'⟩ : Fin (k + 1)) : ℕ) + 1) := by
    rw [auxVar, Nat.add_sub_cancel]
  have hcast : (⟨j, hj'⟩ : Fin (k + 1)) = Fin.castSucc ⟨j, hj⟩ := rfl
  rw [realiseAddLetter_apply, addLetter_auxVar, haux, hι.map_auxVar ⟨j, hj'⟩, auxToFrac_C,
    show algebraMap (MvPolynomial (Fin (k + 1)) K) (Sym.AuxFrac K (k + 1))
        (MvPolynomial.X (⟨j, hj'⟩ : Fin (k + 1))) = Sym.yFrac K (⟨j, hj'⟩ : Fin (k + 1)) from rfl,
    hcast, ← Sym.auxFracCastSucc_yFrac]
  exact Sym.C_auxFracCastSucc_mem_zSymmSubring _

/-- **The image of a power sum is a power sum of the merged alphabet**, hence symmetric.
`ρ_{k+1}(p_{r+1}) = p_{r+1} + y_{k+1}^{r+1}`, whose realisation has coefficient `1` at each
`x_i^{r+1}`, `y_{k+1}^{r+1}` at the empty letter-monomial, and `0` elsewhere — the merged alphabet's
own `(r+1)`-st power sum. -/
theorem realiseAddLetter_powerSum_mem (hι : IsAuxRealisation (k + 1) ι) (r : ℕ) :
    realiseAddLetter K k ι (MvPolynomial.C (Sym.powerSum K (r + 1))) ∈ Sym.zSymmSubring K k := by
  classical
  have hlast : ((Fin.last k : Fin (k + 1)) : ℕ) + 1 = k + 1 := by simp
  have hy : ι (auxVar (k + 1) : Sweep.Total K)
      = MvPowerSeries.C (MvPolynomial.X (Fin.last k)) := by
    have h := hι.map_auxVar (Fin.last k)
    rwa [Fin.val_last] at h
  have hyF : Sym.auxToFrac K (k + 1) (MvPowerSeries.C (MvPolynomial.X (Fin.last k)))
      = MvPowerSeries.C (Sym.yFrac K (Fin.last k)) := auxToFrac_C _ _
  have hsplit : realiseAddLetter K k ι (MvPolynomial.C (Sym.powerSum K (r + 1)))
      = Sym.auxToFrac K (k + 1) (ι (MvPolynomial.C (Sym.powerSum K (r + 1))))
        + MvPowerSeries.C (Sym.yFrac K (Fin.last k) ^ (r + 1)) := by
    rw [realiseAddLetter_apply, addLetter_powerSum, map_add, map_add, map_pow, map_pow, hy, hyF,
      map_pow]
  have hne : ∀ i : ℕ, (0 : ℕ →₀ ℕ) ≠ Finsupp.single i (r + 1) := fun i h =>
    absurd h.symm (Finsupp.single_ne_zero.2 (Nat.succ_ne_zero r))
  rw [hsplit]
  refine Sym.mem_zSymmSubring_of_coeff (r := r) ?_ (fun i => ?_) fun α hα0 hαi => ?_
  · rw [map_add, Sym.coeff_auxToFrac, hι.coeff_of_ne r 0 hne, MvPowerSeries.coeff_C,
      ite_eq_left rfl, map_zero, zero_add]
  · rw [map_add, Sym.coeff_auxToFrac, hι.coeff_pow r i, MvPowerSeries.coeff_C,
      ite_eq_right (Ne.symm (hne i)), map_one, add_zero]
  · rw [map_add, Sym.coeff_auxToFrac, hι.coeff_of_ne r α hαi, MvPowerSeries.coeff_C,
      ite_eq_right hα0, map_zero, add_zero]

/-- The image of a symmetric function, with no auxiliary variable: a member of the symmetric
subring. The power sums generate `Λ` as a `𝕂`-algebra, and the scalars go to constants of the
base. -/
theorem realiseAddLetter_C_mem (hι : IsAuxRealisation (k + 1) ι) (c : Sym.Lambda K) :
    realiseAddLetter K k ι (MvPolynomial.C c) ∈ Sym.zSymmSubring K k := by
  induction c using MvPolynomial.induction_on with
  | C a =>
    have h1 : (MvPolynomial.C (MvPolynomial.C a : Sym.Lambda K) : Sweep.Total K)
        = algebraMap K (Sweep.Total K) a := rfl
    have h2 : (algebraMap K (Sym.AuxAlphabetSeries K (k + 1)) a)
        = MvPowerSeries.C (MvPolynomial.C a) := by
      rw [MvPowerSeries.algebraMap_apply, MvPolynomial.algebraMap_eq]
    rw [realiseAddLetter_apply, h1, AlgHom.commutes, AlgHom.commutes, h2, auxToFrac_C,
      show algebraMap (MvPolynomial (Fin (k + 1)) K) (Sym.AuxFrac K (k + 1)) (MvPolynomial.C a)
        = Sym.scalarFrac K a from rfl]
    exact Sym.C_scalarFrac_mem_zSymmSubring a
  | add p q hp hq =>
    rw [map_add, map_add]
    exact add_mem hp hq
  | mul_X p n hp =>
    rw [map_mul, map_mul,
      show (MvPolynomial.X n : Sym.Lambda K) = Sym.powerSum K (n + 1) from by
        rw [Sym.powerSum, Nat.add_sub_cancel]]
    exact mul_mem hp (realiseAddLetter_powerSum_mem hι n)

/-! ### The expansion coefficients are symmetric -/

/-- **The expansion coefficients are symmetric in the full alphabet.** For `g ∈ V_{k-1}` the element
`g[X + y_k]`, realised in `P°_{k+1}`, lies in `Z^{(k+1)}` and is fixed by every relabelling `ŝ_ρ` of
the merged alphabet `y_k, x_1, x_2, …`.

`V_{k-1}` is generated as a `𝕂`-algebra by the auxiliary variables `y_1, …, y_{k-1}` and the power
sums; the symmetric elements form a subring, because `ŝ_ρ` is a ring homomorphism of `Z^{(k+1)}`
(`HJO.Sym.zPermEquiv`); and the two families of generators go respectively to constants of the lower
coefficient field and to power sums of the merged alphabet, both of which every `ŝ_ρ` fixes.

One may restrict `ρ` to the permutations moving finitely many letters. Nothing here needs
that, so nothing carries it. -/
@[hjo "lem_cm_chiprime_coeff_symmetric"]
theorem realiseAddLetter_mem_zSymmSubring (hι : IsAuxRealisation (k + 1) ι) {G : Sweep.Total K}
    (hG : G ∈ piece K k) : realiseAddLetter K k ι G ∈ Sym.zSymmSubring K k := by
  rw [piece, MvPolynomial.supported_eq_adjoin_X] at hG
  induction hG using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨j, hj, rfl⟩ := hy
    exact realiseAddLetter_X_mem hι hj
  | algebraMap c =>
    rw [show algebraMap (Sym.Lambda K) (Sweep.Total K) c = MvPolynomial.C c from rfl]
    exact realiseAddLetter_C_mem hι c
  | add x y _ _ hx hy =>
    rw [map_add]
    exact add_mem hx hy
  | mul x y _ _ hx hy =>
    rw [map_mul]
    exact mul_mem hx hy

/-- **The expansion coefficients are symmetric**, as an invariance:
`ŝ_ρ(g[X + y_k]) = g[X + y_k]` for every permutation `ρ` of the letters of the merged alphabet. -/
@[hjo "lem_cm_chiprime_coeff_symmetric"]
theorem zPerm_realiseAddLetter (hι : IsAuxRealisation (k + 1) ι) {G : Sweep.Total K}
    (hG : G ∈ piece K k) (ρ : Equiv.Perm (Option ℕ)) :
    Sym.zPerm K k ρ (realiseAddLetter K k ι G) = realiseAddLetter K k ι G :=
  (realiseAddLetter_mem_zSymmSubring hι hG).2 ρ

end HJO.Dyck
