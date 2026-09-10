/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.RingTheory.MvPowerSeries.LinearTopology
public import QSeriesLib.NumberTheory.HJO.OfPosDef
public import QSeriesLib.NumberTheory.QTheory.StrongNonarchimedean
public import QSeriesLib.Order.Filter.Unbounded.PosDefInt
public import HJO.Series.Summable
public import HJO.Series.GapPoset
public import HJO.Series.ProductExponents
public import HJO.Defs

/-! # Coefficientwise limits of the two sides

Three passages to the limit in `ℤ⟦X⟧`, whose topology is the coefficientwise one: convergence
of a sequence of power series means that each coefficient is eventually constant.

* The finite polynomials `F_N` converge to `HJO.zNat`, the power series presentation of the
  HJO series. Only the cone points with `Q 𝐧 ≤ j` reach the coefficient of `q^j`, and by
  coercivity there are finitely many of them, each with `n_f` bounded in terms of `j`; the
  ratio `(q)_N / (q)_{N - n_f}` is then a product of factors `1 - q^i` with `i > j`, so it
  does not disturb that coefficient.
* The bounded cylindric series `C_{𝐜,≤N}` converge to `C_𝐜`, because a cylinder of volume at
  most `j` has all of its entries at most `j`; together with `(q)_N → (q)_∞` this gives the
  convergence of the products.
* The two convergent infinite products `∏_m (1 - q^m)^{e_m}` with integer exponents, one
  assembled from the Foda--Welsh factors and one from the exponents `-ρ(m)`, agree, because
  their exponent sequences do. The integer powers are taken in the unit group of `ℤ⟦X⟧`,
  a negative power being the power series inverse.
-/

@[expose] public section

open Finset Filter NumericalSemigroup PowerSeries
open scoped QTheory Topology PowerSeries.DiscreteTopology

namespace HJO.Limits

open Gaps GapPoset HJO.Cylindric ProductExponents

/-! ### The truncated `q`-Pochhammer ratio -/

/-- `(q)_N` written out as `∏_{i < N} (1 - q^{i+1})`. -/
theorem selfQPochhammer_eq_prod (N : ℕ) :
    ((X; X)_N : ℤ⟦X⟧) = ∏ i ∈ range N, (1 - X ^ (i + 1)) := by
  simp [qPochhammer, pow_succ']

/-- `(q)_N` has constant coefficient `1`, so it is a unit of `ℤ⟦X⟧`. -/
theorem constantCoeff_selfQPochhammer (N : ℕ) :
    constantCoeff ((X; X)_N : ℤ⟦X⟧) = 1 := by
  rw [selfQPochhammer_eq_prod]
  simp

/-- The ratio `(q)_N / (q)_M` for `M ≤ N` is the product of the `N - M` factors `1 - q^{i+1}`
with `M ≤ i < N`, the division being multiplication by the power series inverse. -/
theorem selfQPochhammer_mul_invOfUnit {M N : ℕ} (h : M ≤ N) :
    ((X; X)_N : ℤ⟦X⟧) * invOfUnit ((X; X)_M : ℤ⟦X⟧) 1 = ∏ i ∈ Ico M N, (1 - X ^ (i + 1)) := by
  rw [selfQPochhammer_eq_prod N, ← Finset.prod_range_mul_prod_Ico _ h,
    ← selfQPochhammer_eq_prod M, mul_comm ((X; X)_M : ℤ⟦X⟧) _, mul_assoc,
    mul_invOfUnit _ 1 (by simpa using constantCoeff_selfQPochhammer M), mul_one]

/-- Every factor of `∏_{M ≤ i < N} (1 - q^{i+1})` is congruent to `1` modulo `q^{M+1}`, hence so
is the product. -/
theorem X_pow_dvd_prod_Ico_sub_one (M N : ℕ) :
    (X : ℤ⟦X⟧) ^ (M + 1) ∣ (∏ i ∈ Ico M N, (1 - X ^ (i + 1))) - 1 := by
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem,
    map_sub, map_one, map_prod, sub_eq_zero]
  refine Finset.prod_eq_one fun i hi => ?_
  rw [mem_Ico] at hi
  rw [map_sub, map_one, Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.mem_span_singleton.mpr (pow_dvd_pow (X : ℤ⟦X⟧) (by omega))), sub_zero]

/-- Multiplying by a series congruent to `1` modulo `q^{j+1}` leaves the coefficient of `q^j`
unchanged. -/
theorem coeff_eq_of_X_pow_dvd_sub_one {j : ℕ} {g : ℤ⟦X⟧} (hg : (X : ℤ⟦X⟧) ^ (j + 1) ∣ g - 1)
    (h : ℤ⟦X⟧) : coeff j (g * h) = coeff j h := by
  have h2 : (X : ℤ⟦X⟧) ^ (j + 1) ∣ g * h - h := by
    rw [show g * h - h = (g - 1) * h by ring]
    exact hg.mul_right h
  have h3 := PowerSeries.X_pow_dvd_iff.mp h2 j (by omega)
  rw [map_sub] at h3
  omega

/-- The ratio `(q)_N / (q)_M` is invisible to the coefficient of `q^j` once `j ≤ M ≤ N`. -/
theorem coeff_selfQPochhammer_ratio_mul {j M N : ℕ} (hMN : M ≤ N) (hjM : j ≤ M) (h : ℤ⟦X⟧) :
    coeff j (((X; X)_N : ℤ⟦X⟧) * invOfUnit ((X; X)_M : ℤ⟦X⟧) 1 * h) = coeff j h := by
  refine coeff_eq_of_X_pow_dvd_sub_one ?_ h
  rw [selfQPochhammer_mul_invOfUnit hMN]
  exact dvd_trans (pow_dvd_pow (X : ℤ⟦X⟧) (by omega)) (X_pow_dvd_prod_Ico_sub_one M N)

/-- An unbounded natural-valued family takes each value bound on a finite set of indices. -/
theorem finite_le_of_unbounded {α : Type*} {n : α → ℕ} (hn : Filter.Unbounded n) (d : ℕ) :
    {x | n x ≤ d}.Finite :=
  (Filter.eventually_cofinite.mp
      (Filter.tendsto_atTop.mp (Filter.Unbounded.nat_def.mp hn) (d + 1))).subset
    fun _ (hx : n _ ≤ d) => (show ¬ d + 1 ≤ n _ by omega)

/-! ### The HJO series as the limit of the finite polynomials -/

/-- The gap set of `⟨a, b⟩` is nonempty for coprime `1 < a < b`: it contains the Frobenius gap. -/
theorem card_gaps_pos {a b : ℕ} (hco : a.Coprime b) (ha : 1 < a) (hab : a < b) :
    0 < (finspan {a, b}).gaps.card :=
  Finset.card_pos.mpr ⟨_, frobeniusGap_mem a b hco ha (ha.trans hab)⟩

/-- Coercivity makes the quadratic form positive definite on the monotonicity cone: a nonzero
cone point has some nonzero coordinate, whose square bounds `|G| * Q 𝐧` from below. -/
theorem posDefOn_Q (huang : HJO.Literature.HuangCoercivity) {a b : ℕ} (hco : a.Coprime b)
    (ha : 1 < a) (hab : a < b) : (HJO.Q a b).PosDefOn (HJO.cone a b) := by
  intro n hn hne
  obtain ⟨i, hi⟩ : ∃ i, n i ≠ 0 := by
    by_contra hc
    exact hne (funext fun i => not_not.mp fun h => hc ⟨i, h⟩)
  have h1 := huang a b hco ha hab n hn i
  have h2 : 0 < n i ^ 2 := pow_pos (abs_pos.mpr hi) 2 |>.trans_le (le_of_eq (sq_abs _))
  have h3 : (0 : ℤ) < (finspan {a, b}).gaps.card := by
    exact_mod_cast card_gaps_pos hco ha hab
  nlinarith

/-- On the monotonicity cone the value at the Frobenius gap is bounded by `|G| * j` as soon as
`Q 𝐧 ≤ j`, since coercivity bounds its square by `|G| * Q 𝐧`. -/
theorem extend_frobeniusGap_le (huang : HJO.Literature.HuangCoercivity) {a b : ℕ}
    (hco : a.Coprime b) (ha : 1 < a) (hab : a < b) {n : (finspan {a, b}).gaps → ℤ}
    (hn : n ∈ HJO.cone a b) {j : ℕ} (hj : HJO.Q a b n ≤ (j : ℤ)) :
    (HJO.extend n (frobeniusGap a b)).toNat ≤ (finspan {a, b}).gaps.card * j := by
  have hcard : (0 : ℤ) ≤ (finspan {a, b}).gaps.card := by positivity
  have hsq := coercivity_frobeniusGap huang a b hco ha hab n hn
  have hf := frobeniusGap_mem a b hco ha (ha.trans hab)
  have ht0 : 0 ≤ HJO.extend n (frobeniusGap a b) := by
    rw [GapPoset.extend_of_mem n hf]
    exact hn.1 _
  set t := HJO.extend n (frobeniusGap a b) with hts
  have hC : t ^ 2 ≤ ((finspan {a, b}).gaps.card : ℤ) * (j : ℤ) := by nlinarith
  have ht : t ≤ ((finspan {a, b}).gaps.card : ℤ) * (j : ℤ) := by
    rcases eq_or_lt_of_le ht0 with h | h1
    · rw [← h]; positivity
    · have h2 : t * 1 ≤ t * t := mul_le_mul_of_nonneg_left h1 ht0
      nlinarith
  omega

/-- The power series presentation of the HJO series is the sum over the monotonicity cone: off
the cone every gap product vanishes. -/
theorem zNat_eq_tsum_cone (a b : ℕ) :
    HJO.zNat a b = ∑' n : HJO.cone a b,
      (∏ g : (finspan {a, b}).gaps, HJO.multiplicand _ a b (n : _) g) *
        X ^ (HJO.Q a b n).toNat := by
  have hsupp : Function.support (fun n : (finspan {a, b}).gaps → ℤ =>
      (∏ g : (finspan {a, b}).gaps, HJO.multiplicand _ a b n g) *
        (X : ℤ⟦X⟧) ^ (HJO.Q a b n).toNat) ⊆ HJO.cone a b := by
    refine fun n hn => HJO.iInter_support_multiplicand_subset_cone _ a b rfl
      (Set.mem_iInter.mpr fun i hi => Function.mem_support.mp hn ?_)
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hi]
    simp
  rw [HJO.zNat, HJO.zNat']
  exact (tsum_subtype_eq_of_support_subset hsupp).symm

/-- On the monotonicity cone the exponents `Q 𝐧` are unbounded, which is what makes the sum
defining the HJO series a genuine sum. -/
theorem unbounded_Q_toNat (huang : HJO.Literature.HuangCoercivity) {a b : ℕ}
    (hco : a.Coprime b) (ha : 1 < a) (hab : a < b) :
    Filter.Unbounded fun n : HJO.cone a b => (HJO.Q a b n).toNat :=
  Filter.Unbounded.toNat_of_posDefOn_int (posDefOn_Q huang hco ha hab)
    (HJO.coneFun (finspan {a, b}).gaps a b)
    (HJO.polyhedralCone_coneFun_eq_cone (finspan {a, b}).gaps a b).symm

/-- Deleting the factor `(q)_N / (q)_{N - n_f}` from the generalised Gaussian multinomial does
not change the coefficient of `q^j`, provided `n_f + j ≤ N`. -/
theorem coeff_multinomial_mul {a b : ℕ} {j N k : ℕ} (hkj : k + j ≤ N)
    (n : (finspan {a, b}).gaps → ℤ) (hn : HJO.extend n (frobeniusGap a b) = (k : ℤ))
    (h : ℤ⟦X⟧) :
    coeff j (multinomial a b N n * h)
      = coeff j ((∏ g : (finspan {a, b}).gaps, HJO.multiplicand _ a b n g) * h) := by
  have hNk : ((N : ℤ) - (k : ℤ)).toNat = N - k := by omega
  rw [multinomial, hn, HJO.extendedSelfQPochhammerInv,
    ite_eq_left (show (0 : ℤ) ≤ (N : ℤ) - (k : ℤ) by omega), hNk,
    show ((X; X)_N : ℤ⟦X⟧) * invOfUnit ((X; X)_(N - k) : ℤ⟦X⟧) 1 *
        (∏ g : (finspan {a, b}).gaps, HJO.multiplicand _ a b n g) * h
      = ((X; X)_N : ℤ⟦X⟧) * invOfUnit ((X; X)_(N - k) : ℤ⟦X⟧) 1 *
        ((∏ g : (finspan {a, b}).gaps, HJO.multiplicand _ a b n g) * h) from by ring,
    coeff_selfQPochhammer_ratio_mul (by omega) (by omega)]

/-- Each coefficient of the finite HJO polynomial is eventually constant in `N`, with value the
corresponding coefficient of the HJO series: for `|G| * j + j ≤ N` the two agree in degree `j`. -/
theorem coeff_finiteSeries_eq_coeff_zNat (huang : HJO.Literature.HuangCoercivity) {a b : ℕ}
    (hco : a.Coprime b) (ha : 1 < a) (hab : a < b) (j N : ℕ)
    (hN : (finspan {a, b}).gaps.card * j + j ≤ N) :
    coeff j (finiteSeries a b N) = coeff j (HJO.zNat a b) := by
  classical
  have hq := posDefOn_Q huang hco ha hab
  have hunb := unbounded_Q_toNat huang hco ha hab
  set Sj : Finset (HJO.cone a b) := (finite_le_of_unbounded hunb j).toFinset with hSj
  set Cj : Finset ((finspan {a, b}).gaps → ℤ) := Sj.image Subtype.val with hCj
  have hmemCj : ∀ n : (finspan {a, b}).gaps → ℤ,
      n ∈ Cj ↔ ∃ h : n ∈ HJO.cone a b, (HJO.Q a b n).toNat ≤ j := by
    intro n
    simp only [hCj, hSj, Finset.mem_image, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨m.2, hm⟩
    · rintro ⟨h, hle⟩
      exact ⟨⟨n, h⟩, hle, rfl⟩
  have hf := frobeniusGap_mem a b hco ha (ha.trans hab)
  have hz : coeff j (HJO.zNat a b) = ∑ n ∈ Cj, coeff j
      ((∏ g : (finspan {a, b}).gaps, HJO.multiplicand _ a b n g) *
        X ^ (HJO.Q a b n).toNat) := by
    rw [zNat_eq_tsum_cone,
      hunb.coeff_tsum_eq_sum _ j Sj (fun n hn => by
        simpa [hSj] using hn), hCj,
      Finset.sum_image (fun x _ y _ h => Subtype.ext h)]
  have hfin := finite_cone_frobeniusGap_le a b N hco ha hab
  have hFs : finiteSeries a b N = ∑ n ∈ hfin.toFinset,
      multinomial a b N n * X ^ (HJO.Q a b n).toNat :=
    finsum_mem_eq_finite_toFinset_sum _ hfin
  have hsub : Cj ⊆ hfin.toFinset := by
    intro n hn
    obtain ⟨hcone, hle⟩ := (hmemCj n).mp hn
    have hQ0 := hq.nonneg hcone
    have hQle : HJO.Q a b n ≤ (j : ℤ) := by omega
    have hb1 := extend_frobeniusGap_le huang hco ha hab hcone hQle
    have ht0 : 0 ≤ HJO.extend n (frobeniusGap a b) := by
      rw [GapPoset.extend_of_mem n hf]
      exact hcone.1 _
    rw [Set.Finite.mem_toFinset]
    exact ⟨hcone, by omega⟩
  have hzero : ∀ n ∈ hfin.toFinset, n ∉ Cj →
      coeff j (multinomial a b N n * X ^ (HJO.Q a b n).toNat) = 0 := by
    intro n hn hnc
    rw [Set.Finite.mem_toFinset] at hn
    have hgt : ¬ (HJO.Q a b n).toNat ≤ j := fun h => hnc ((hmemCj n).mpr ⟨hn.1, h⟩)
    exact PowerSeries.DiscreteTopology.coeff_mul_pow_eq_zero (by omega)
  rw [hFs, map_sum, ← Finset.sum_subset hsub hzero, hz]
  refine Finset.sum_congr rfl fun n hn => ?_
  obtain ⟨hcone, hle⟩ := (hmemCj n).mp hn
  have hQ0 := hq.nonneg hcone
  have hQle : HJO.Q a b n ≤ (j : ℤ) := by omega
  have hb1 := extend_frobeniusGap_le huang hco ha hab hcone hQle
  have ht0 : 0 ≤ HJO.extend n (frobeniusGap a b) := by
    rw [GapPoset.extend_of_mem n hf]
    exact hcone.1 _
  exact coeff_multinomial_mul (k := (HJO.extend n (frobeniusGap a b)).toNat)
    (by omega) n (Int.toNat_of_nonneg ht0).symm _

/-- The finite HJO polynomials converge to the HJO series: every coefficient is eventually
constant in `N`. -/
theorem tendsto_finiteSeries (huang : HJO.Literature.HuangCoercivity) {a b : ℕ}
    (hco : a.Coprime b) (ha : 1 < a) (hab : a < b) :
    Filter.Tendsto (finiteSeries a b) atTop (𝓝 (HJO.zNat a b)) := by
  rw [PowerSeries.DiscreteTopology.tendsto_iff_coeff_eventually_const]
  exact fun d => eventually_atTop.mpr
    ⟨(finspan {a, b}).gaps.card * d + d,
      fun N hN => coeff_finiteSeries_eq_coeff_zNat huang hco ha hab d N hN⟩

/-! ### The cylindric series as the limit of the bounded ones -/

/-- The volumes of the cylindric partitions of a fixed profile are unbounded. -/
theorem unbounded_cylVolume (a b : ℕ) (ha : 0 < a) :
    Filter.Unbounded (fun l : {l : ℕ → ℕ → ℕ // IsCylindric a (profile a b) l} =>
      cylVolume a l.val) :=
  Filter.Unbounded.comp_subtypeVal_iff.mpr fun y =>
    (Summable.finite_setOf_cylVolume_lt a y y (profile a b) ha).subset fun _ hl =>
      ⟨⟨hl.1, Summable.boundedBy_of_cylVolume_lt ha hl.1 (not_le.mp hl.2)⟩, not_le.mp hl.2⟩

open scoped Classical in
/-- The bounded cylindric series read as a sum over all cylindric partitions of the profile, the
ones with an entry above `N` contributing zero. -/
theorem boundedGF_eq_tsum (a b N : ℕ) :
    boundedGF a b N = ∑' l : {l : ℕ → ℕ → ℕ // IsCylindric a (profile a b) l},
      (if BoundedBy N l.val then (1 : ℤ⟦X⟧) else 0) * X ^ cylVolume a l.val := by
  set F : {l : ℕ → ℕ → ℕ // IsCylindric a (profile a b) l} → ℤ⟦X⟧ := fun l =>
    (if BoundedBy N l.val then (1 : ℤ⟦X⟧) else 0) * X ^ cylVolume a l.val with hF
  set g : {l : ℕ → ℕ → ℕ // IsCylindric a (profile a b) l ∧ BoundedBy N l} →
      {l : ℕ → ℕ → ℕ // IsCylindric a (profile a b) l} := fun l => ⟨l.1, l.2.1⟩ with hg
  have hinj : Function.Injective g := by
    intro x y h
    simp only [hg, Subtype.mk.injEq] at h
    exact Subtype.ext h
  have hsupp : Function.support F ⊆ Set.range g := by
    intro l hl
    by_cases hb : BoundedBy N l.val
    · exact ⟨⟨l.1, l.2, hb⟩, rfl⟩
    · exact absurd (show F l = 0 by rw [hF]; simp [hb]) hl
  rw [boundedGF, ← hinj.tsum_eq hsupp]
  exact tsum_congr fun l => by rw [hF, hg]; simp [l.2.2]

/-- Each coefficient of the bounded cylindric series is eventually constant in the bound: for
`j ≤ N` the coefficient of `q^j` already agrees with that of the unbounded series, because a
cylinder of volume at most `j` has every entry at most `j`. -/
theorem coeff_boundedGF_eq_coeff_unboundedGF (a b N j : ℕ) (ha : 0 < a) (hjN : j ≤ N) :
    coeff j (boundedGF a b N) = coeff j (unboundedGF a b) := by
  classical
  have hn := unbounded_cylVolume a b ha
  set S := (finite_le_of_unbounded hn j).toFinset with hS
  have hSmem : ∀ l ∉ S, j < cylVolume a l.val := by
    intro l hl
    simpa [hS] using hl
  rw [boundedGF_eq_tsum, unboundedGF, hn.coeff_tsum_eq_sum _ j S hSmem,
    show (∑' l : {l : ℕ → ℕ → ℕ // IsCylindric a (profile a b) l},
        (X : ℤ⟦X⟧) ^ cylVolume a l.val)
      = ∑' l : {l : ℕ → ℕ → ℕ // IsCylindric a (profile a b) l},
        (1 : ℤ⟦X⟧) * X ^ cylVolume a l.val from tsum_congr fun l => (one_mul _).symm,
    hn.coeff_tsum_eq_sum _ j S hSmem]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hvol : cylVolume a l.val ≤ j := by simpa [hS] using hl
  have hb : BoundedBy N l.val := fun i k =>
    (Summable.le_cylVolume ha l.2 i k).trans (hvol.trans hjN)
  rw [ite_eq_left hb]

/-- The bounded cylindric series converge to the cylindric series. -/
theorem tendsto_boundedGF (a b : ℕ) (ha : 0 < a) :
    Filter.Tendsto (boundedGF a b) atTop (𝓝 (unboundedGF a b)) := by
  rw [PowerSeries.DiscreteTopology.tendsto_iff_coeff_eventually_const]
  exact fun d => eventually_atTop.mpr
    ⟨d, fun N hN => coeff_boundedGF_eq_coeff_unboundedGF a b N d ha hN⟩

/-- The finite `q`-Pochhammer symbols converge to the infinite one. -/
theorem tendsto_selfQPochhammer :
    Filter.Tendsto (fun N => ((X; X)_N : ℤ⟦X⟧)) atTop (𝓝 ((X; X)_∞)) :=
  tendsto_qPochhammer_qPochhammerInf PowerSeries.DiscreteTopology.isTopologicallyNilpotent_X

/-- `(q)_N C_{𝐜,≤N} → (q)_∞ C_𝐜` coefficientwise. -/
theorem tendsto_selfQPochhammer_mul_boundedGF (a b : ℕ) (ha : 0 < a) :
    Filter.Tendsto (fun N => ((X; X)_N : ℤ⟦X⟧) * boundedGF a b N) atTop
      (𝓝 ((X; X)_∞ * unboundedGF a b)) :=
  tendsto_selfQPochhammer.mul (tendsto_boundedGF a b ha)

/-! ### Integer powers of `1 - q^m` -/

/-- `1 - q^{m+1}` as a unit of `ℤ⟦X⟧`; its inverse is the power series inverse. -/
noncomputable def oneSubUnit (m : ℕ) : ℤ⟦X⟧ˣ where
  val := 1 - X ^ (m + 1)
  inv := invOfUnit (1 - X ^ (m + 1) : ℤ⟦X⟧) 1
  val_inv := mul_invOfUnit _ 1 (by simp)
  inv_val := by rw [mul_comm]; exact mul_invOfUnit _ 1 (by simp)

/-- The unit `oneSubUnit m` has value `1 - q^{m+1}`. -/
@[simp] theorem oneSubUnit_val (m : ℕ) : (oneSubUnit m : ℤ⟦X⟧) = 1 - X ^ (m + 1) := rfl

/-- `(1 - q^{m+1})^k` for an integer exponent `k`, a negative power being the power series
inverse raised to the corresponding positive power. -/
noncomputable def zpowOneSub (m : ℕ) (k : ℤ) : ℤ⟦X⟧ := ((oneSubUnit m ^ k : ℤ⟦X⟧ˣ) : ℤ⟦X⟧)

/-- The zeroth power is `1`. -/
@[simp] theorem zpowOneSub_zero (m : ℕ) : zpowOneSub m 0 = 1 := by simp [zpowOneSub]

/-- Integer exponents add. -/
theorem zpowOneSub_add (m : ℕ) (k l : ℤ) :
    zpowOneSub m (k + l) = zpowOneSub m k * zpowOneSub m l := by
  simp [zpowOneSub, zpow_add]

/-- The first power is `1 - q^{m+1}` itself. -/
theorem zpowOneSub_one (m : ℕ) : zpowOneSub m 1 = (1 - X ^ (m + 1) : ℤ⟦X⟧) := by
  simp [zpowOneSub]

/-- A negative integer power is a power of the power series inverse. -/
theorem zpowOneSub_neg_natCast (m n : ℕ) :
    zpowOneSub m (-(n : ℤ)) = invOfUnit (1 - X ^ (m + 1) : ℤ⟦X⟧) 1 ^ n := by
  simp [zpowOneSub, zpow_neg, zpow_natCast, oneSubUnit]

/-- Raising an integer power to a natural power multiplies the exponents. -/
theorem zpowOneSub_pow (m : ℕ) (k : ℤ) (n : ℕ) :
    zpowOneSub m k ^ n = zpowOneSub m ((n : ℤ) * k) := by
  rw [zpowOneSub, zpowOneSub, ← Units.val_pow_eq_pow_val,
    ← zpow_natCast (oneSubUnit m ^ k) n, ← zpow_mul, mul_comm]

/-- Every integer power of `1 - q^{m+1}` is congruent to `1` modulo `q^{m+1}`: the reduction of
`oneSubUnit m` in the quotient by `q^{m+1}` is the trivial unit. -/
theorem X_pow_dvd_zpowOneSub_sub_one (m : ℕ) (k : ℤ) :
    (X : ℤ⟦X⟧) ^ (m + 1) ∣ zpowOneSub m k - 1 := by
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, sub_eq_zero]
  set red := Ideal.Quotient.mk (Ideal.span {(X : ℤ⟦X⟧) ^ (m + 1)}) with hred
  have h1 : Units.map red.toMonoidHom (oneSubUnit m) = 1 := by
    refine Units.ext ?_
    change red (1 - X ^ (m + 1)) = 1
    rw [map_sub, map_one, hred, Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_span_singleton.mpr dvd_rfl), sub_zero]
  calc red (zpowOneSub m k) = ((Units.map red.toMonoidHom (oneSubUnit m ^ k) : _) : _) := rfl
    _ = ((Units.map red.toMonoidHom (oneSubUnit m) ^ k : _) : _) := by rw [map_zpow]
    _ = 1 := by rw [h1, one_zpow, Units.val_one]

/-- Below degree `m + 1` every integer power of `1 - q^{m+1}` looks like `1`. -/
theorem coeff_zpowOneSub {m d : ℕ} (hd : d ≤ m) (k : ℤ) :
    coeff d (zpowOneSub m k) = coeff d (1 : ℤ⟦X⟧) := by
  have h := PowerSeries.X_pow_dvd_iff.mp (X_pow_dvd_zpowOneSub_sub_one m k) d (by omega)
  rw [map_sub] at h
  omega

/-- For any exponent sequence the family `(1 - q^{m+1})^{e_m}` is multipliable: its terms tend
to `1` coefficientwise. -/
theorem multipliable_zpowOneSub (e : ℕ → ℤ) :
    Multipliable fun m => zpowOneSub m (e m) := by
  refine multipliable_of_tendsto_one ?_
  rw [PowerSeries.DiscreteTopology.tendsto_iff_coeff_eventually_const]
  exact fun d => eventually_atTop.mpr ⟨d, fun m hm => coeff_zpowOneSub hm (e m)⟩

/-- Multiplying two such products adds the exponent sequences. -/
theorem tprod_zpowOneSub_mul (e f : ℕ → ℤ) :
    (∏' m, zpowOneSub m (e m)) * (∏' m, zpowOneSub m (f m))
      = ∏' m, zpowOneSub m (e m + f m) :=
  ((multipliable_zpowOneSub e).tprod_mul (multipliable_zpowOneSub f)).symm.trans
    (tprod_congr fun m => (zpowOneSub_add m (e m) (f m)).symm)

/-- Raising such a product to a natural power scales the exponent sequence. -/
theorem tprod_zpowOneSub_pow (e : ℕ → ℤ) (n : ℕ) :
    (∏' m, zpowOneSub m (e m)) ^ n = ∏' m, zpowOneSub m ((n : ℤ) * e m) :=
  ((multipliable_zpowOneSub e).tprod_pow n).symm.trans
    (tprod_congr fun m => zpowOneSub_pow m (e m) n)

/-- A finite product of such products sums the exponent sequences. -/
theorem tprod_zpowOneSub_finsetProd {ι : Type*} (S : Finset ι) (e : ι → ℕ → ℤ) :
    (∏ s ∈ S, ∏' m, zpowOneSub m (e s m)) = ∏' m, zpowOneSub m (∑ s ∈ S, e s m) := by
  classical
  refine (Multipliable.tprod_finsetProd (fun s _ => multipliable_zpowOneSub (e s))).symm.trans ?_
  refine tprod_congr fun m => ?_
  induction S using Finset.induction with
  | empty => simp
  | insert s S hs ih => rw [Finset.prod_insert hs, Finset.sum_insert hs, zpowOneSub_add, ih]

/-! ### The infinite products -/

/-- `(q^J; q^d)_∞` as a product over all `m` of integer powers of `1 - q^m`: the factor at `m`
occurs exactly once when `m` lies in the class of `J` modulo `d`, and not at all otherwise. -/
theorem qPochhammerInf_eq_tprod_zpowOneSub {J d : ℕ} (hJ : 0 < J) (hd : 0 < d) :
    ((X ^ J; X ^ d)_∞ : ℤ⟦X⟧)
      = ∏' m, zpowOneSub m (if J ≤ m + 1 ∧ d ∣ (m + 1) - J then 1 else 0) := by
  classical
  have hqd : IsTopologicallyNilpotent ((X : ℤ⟦X⟧) ^ d) :=
    (PowerSeries.DiscreteTopology.isTopologicallyNilpotent_X_pow d).mpr (by omega)
  set g : ℕ → ℤ⟦X⟧ :=
    fun m => zpowOneSub m (if J ≤ m + 1 ∧ d ∣ (m + 1) - J then 1 else 0) with hg
  have hcond : ∀ i : ℕ, J ≤ J + d * i - 1 + 1 ∧ d ∣ J + d * i - 1 + 1 - J := by
    intro i
    refine ⟨by omega, ?_⟩
    rw [show J + d * i - 1 + 1 - J = d * i by omega]
    exact Dvd.intro i rfl
  have hψinj : Function.Injective fun i : ℕ => J + d * i - 1 := by
    intro i j h
    simp only at h
    exact Nat.eq_of_mul_eq_mul_left hd (by omega)
  have hsupp : Function.mulSupport g ⊆ Set.range fun i : ℕ => J + d * i - 1 := by
    intro m hm
    by_cases hc : J ≤ m + 1 ∧ d ∣ m + 1 - J
    · obtain ⟨i, hi⟩ := hc.2
      refine ⟨i, ?_⟩
      change J + d * i - 1 = m
      omega
    · exact absurd (show g m = 1 by rw [hg]; simp [hc]) hm
  rw [qPochhammerInf_eq_tprod hqd]
  refine Eq.trans (tprod_congr fun i => ?_) (hψinj.tprod_eq hsupp)
  simp only [ite_eq_left (hcond i), zpowOneSub_one, ← pow_mul, ← pow_add]
  congr 2
  omega

/-- `(q)_∞ = ∏_{m ≥ 1} (1 - q^m)`, in the indexing used here. -/
theorem qPochhammerInf_self_eq_tprod : ((X; X)_∞ : ℤ⟦X⟧) = ∏' m, zpowOneSub m 1 := by
  have h := qPochhammerInf_eq_tprod_zpowOneSub (J := 1) (d := 1) one_pos one_pos
  rw [pow_one] at h
  refine h.trans (tprod_congr fun m => ?_)
  rw [ite_eq_left ⟨by omega, one_dvd _⟩]

/-- `(q)_∞` has constant coefficient `1`, being the coefficientwise limit of the `(q)_N`. -/
theorem constantCoeff_qPochhammerInf_self : constantCoeff ((X; X)_∞ : ℤ⟦X⟧) = 1 := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((PowerSeries.DiscreteTopology.tendsto_iff_coeff_eventually_const
      (fun N => ((X; X)_N : ℤ⟦X⟧)) atTop ((X; X)_∞)).mp tendsto_selfQPochhammer 0)
  have h1 := hN N le_rfl
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, ← h1,
    PowerSeries.coeff_zero_eq_constantCoeff, qPochhammer]
  simp

/-- The power series inverse of `(q)_∞` is the product of the inverses of the `1 - q^m`. -/
theorem invOfUnit_qPochhammerInf_self :
    invOfUnit ((X; X)_∞ : ℤ⟦X⟧) 1 = ∏' m, zpowOneSub m (-1) := by
  have hmul : ((X; X)_∞ : ℤ⟦X⟧) * (∏' m, zpowOneSub m (-1)) = 1 := by
    rw [qPochhammerInf_self_eq_tprod, tprod_zpowOneSub_mul]
    simp
  calc invOfUnit ((X; X)_∞ : ℤ⟦X⟧) 1
      = invOfUnit ((X; X)_∞ : ℤ⟦X⟧) 1 * (((X; X)_∞ : ℤ⟦X⟧) * ∏' m, zpowOneSub m (-1)) := by
        rw [hmul, mul_one]
    _ = (((X; X)_∞ : ℤ⟦X⟧) * invOfUnit ((X; X)_∞ : ℤ⟦X⟧) 1) * ∏' m, zpowOneSub m (-1) := by ring
    _ = ∏' m, zpowOneSub m (-1) := by
        rw [mul_invOfUnit _ 1 (by simpa using constantCoeff_qPochhammerInf_self), one_mul]

/-- The HJO product as a product of integer powers of `1 - q^m`, the exponent at `m` being
`-ρ(m)`. -/
theorem charge_eq_tprod_zpowOneSub (a b : ℕ) :
    HJO.charge a b = ∏' m, zpowOneSub m (-(HJO.negR a b (m + 1) : ℤ)) := by
  set f : ℕ → ℤ⟦X⟧ := fun n => invOfUnit (1 - X ^ n : ℤ⟦X⟧) 1 ^ HJO.negR a b n with hf
  have hψinj : Function.Injective fun m : ℕ => m + 1 := fun i j h => by
    have h' : i + 1 = j + 1 := h
    omega
  have hsupp : Function.mulSupport f ⊆ Set.range fun m : ℕ => m + 1 := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · exact absurd (show f 0 = 1 by rw [hf]; simp [HJO.negR_zero]) hn
    · refine ⟨n - 1, ?_⟩
      change n - 1 + 1 = n
      omega
  rw [HJO.charge, ← hψinj.tprod_eq hsupp]
  exact tprod_congr fun m => (zpowOneSub_neg_natCast m (HJO.negR a b (m + 1))).symm

/-- The Foda--Welsh product is the HJO product: both are convergent products of integer powers
of the `1 - q^m`, and their exponent sequences agree at every `m`. -/
theorem fodaWelsh_eq_charge {a b : ℕ} (hco : a.Coprime b) (ha : 1 < a) (hab : a < b) :
    ((X ^ (a + b); X ^ (a + b))_∞ : ℤ⟦X⟧) ^ (a - 1) * invOfUnit ((X; X)_∞ : ℤ⟦X⟧) 1 ^ (a - 1) *
        ∏ s ∈ Icc 1 (a - 1), ∏ v ∈ range a, ((X ^ jSum a b v s; X ^ (a + b))_∞ : ℤ⟦X⟧)
      = HJO.charge a b := by
  classical
  have hd : 0 < a + b := by omega
  have h1 : ((X ^ (a + b); X ^ (a + b))_∞ : ℤ⟦X⟧) ^ (a - 1)
      = ∏' m, zpowOneSub m (((a - 1 : ℕ) : ℤ) *
          (if a + b ≤ m + 1 ∧ a + b ∣ (m + 1) - (a + b) then 1 else 0)) := by
    rw [qPochhammerInf_eq_tprod_zpowOneSub hd hd, tprod_zpowOneSub_pow]
  have h2 : invOfUnit ((X; X)_∞ : ℤ⟦X⟧) 1 ^ (a - 1)
      = ∏' m, zpowOneSub m (((a - 1 : ℕ) : ℤ) * (-1)) := by
    rw [invOfUnit_qPochhammerInf_self, tprod_zpowOneSub_pow]
  have h3 : (∏ s ∈ Icc 1 (a - 1), ∏ v ∈ range a, ((X ^ jSum a b v s; X ^ (a + b))_∞ : ℤ⟦X⟧))
      = ∏' m, zpowOneSub m (∑ s ∈ Icc 1 (a - 1), ∑ v ∈ range a,
          (if jSum a b v s ≤ m + 1 ∧ a + b ∣ (m + 1) - jSum a b v s then (1 : ℤ) else 0)) := by
    rw [← tprod_zpowOneSub_finsetProd (Icc 1 (a - 1)) fun s m => ∑ v ∈ range a,
      (if jSum a b v s ≤ m + 1 ∧ a + b ∣ (m + 1) - jSum a b v s then (1 : ℤ) else 0)]
    refine Finset.prod_congr rfl fun s hs => ?_
    rw [mem_Icc] at hs
    rw [← tprod_zpowOneSub_finsetProd (range a) fun v m =>
      (if jSum a b v s ≤ m + 1 ∧ a + b ∣ (m + 1) - jSum a b v s then (1 : ℤ) else 0)]
    exact Finset.prod_congr rfl fun v _ =>
      qPochhammerInf_eq_tprod_zpowOneSub (jSum_pos_lt ha hab v (by omega) (by omega)).1 hd
  rw [h1, h2, h3, tprod_zpowOneSub_mul, tprod_zpowOneSub_mul, charge_eq_tprod_zpowOneSub]
  refine tprod_congr fun m => ?_
  congr 1
  have hte := total_exponent_eq ha hab hco (m + 1)
  have hcast : ((a - 1 : ℕ) : ℤ) = (a : ℤ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ a), Nat.cast_one]
  have hiff : (a + b ≤ m + 1 ∧ a + b ∣ (m + 1) - (a + b)) ↔ a + b ∣ m + 1 := by
    constructor
    · rintro ⟨hle, k, hk⟩
      exact ⟨k + 1, by rw [Nat.mul_succ]; omega⟩
    · rintro ⟨k, hk⟩
      rcases Nat.eq_zero_or_pos k with rfl | hk1
      · simp at hk
      have hle : a + b ≤ (a + b) * k := Nat.le_mul_of_pos_right _ hk1
      refine ⟨by omega, k - 1, ?_⟩
      have hsplit : (a + b) * k = (a + b) * (k - 1) + (a + b) := by
        rw [← Nat.mul_succ]
        congr 1
        omega
      omega
  have hIcc : Finset.Icc 1 (a - 1) = Finset.Ico 1 a := by
    ext s
    simp only [mem_Icc, mem_Ico]
    omega
  rw [hcast, if_congr hiff rfl rfl, hIcc, Finset.sum_comm]
  push_cast at hte ⊢
  linarith [hte]

/-- `(q)_∞ C_𝐜 = P_{a,b}`: the cylindric product identifies the left side with the Foda--Welsh
product, whose exponents are those of the HJO product. -/
theorem qPochhammerInf_mul_unboundedGF_eq_charge (cyl : HJO.Literature.CylindricProduct)
    {a b : ℕ} (hco : a.Coprime b) (ha : 1 < a) (hab : a < b) :
    ((X; X)_∞ : ℤ⟦X⟧) * unboundedGF a b = HJO.charge a b := by
  rw [cyl a b hco ha hab]
  exact fodaWelsh_eq_charge hco ha hab

/-! ### Passing to the limit in the finite identity -/

/-- Taking the coefficientwise limit of `F_N = (q)_N C_{𝐜,≤N}` gives `Z = (q)_∞ C_𝐜`. -/
theorem zNat_eq_qPochhammerInf_mul_unboundedGF (huang : HJO.Literature.HuangCoercivity) {a b : ℕ}
    (hco : a.Coprime b) (ha : 1 < a) (hab : a < b)
    (hfinite : ∀ N : ℕ, finiteSeries a b N = ((X; X)_N : ℤ⟦X⟧) * boundedGF a b N) :
    HJO.zNat a b = ((X; X)_∞ : ℤ⟦X⟧) * unboundedGF a b :=
  tendsto_nhds_unique (tendsto_finiteSeries huang hco ha hab)
    ((tendsto_selfQPochhammer_mul_boundedGF a b (by omega)).congr fun N => (hfinite N).symm)

end HJO.Limits
