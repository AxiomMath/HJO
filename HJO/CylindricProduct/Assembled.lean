/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Finset.Prod
public import Mathlib.Order.Interval.Finset.Nat
public import HJO.Series.GapForms
public import HJO.Series.Limits
public import HJO.CylindricProduct.TransferTrace
public meta import HJO.Attr

/-! # Counting the pairs of slots at a prescribed cyclic difference

At the heart of the assembled-exponent identity is a count: for each residue `M` the number of
ordered pairs `(s, s')` with `s` a lowering slot, `s'` a raising slot and `s - s' ≡ M` modulo
`d = a + b` is the cylindric weight `w_{a,b}(M) = min {a, b, dist(aM, dℤ)}`.

The count is carried out in three moves.

* For each raising slot `s'` there is exactly one `s` in `[0, d)` with `s - s' ≡ M`, namely
  `(s' + M) \bmod d`, so the pairs are indexed by the raising slots `s'` at which that partner is
  lowering.
* Multiplication by `a` is a bijection of `[0, d)`, because `a` is coprime to `d`, and by the
  definition of `IsRaising` it carries the raising slots onto `[b, d)` and the lowering slots onto
  `[0, b)`.
  So the count becomes the number of `u \in [b, d)` whose translate by `μ = aM \bmod d` lands in
  `[0, b)`.
* That set is the interval `[max(b, d - μ), min(d, d + b - μ))`, whose length is
  `min {a, μ, d - μ}`; since `a < b` and the distance to `dℤ` never exceeds `d/2 < b`, this is
  `w_{a,b}(M)`.

The third move is where the hypothesis `a < b` is used: it makes `min a b = a` and puts the
raising block `[b, d)` and its translate far enough apart that the intersection is an interval.
-/

@[expose] public section

open Finset PowerSeries
open scoped QTheory Topology PowerSeries.DiscreteTopology

namespace HJO.CylindricProduct

/-! ### The pairs at a prescribed cyclic difference -/

/-- The ordered pairs of a lowering slot and a raising slot of the step word shifted by `c`, the
lowering slot first. Shifting is what `transferKernel` does to put a lowering slot last, and none of
the counts below depend on the shift. -/
noncomputable def slotPairs (a b c : ℕ) : Finset (ℕ × ℕ) :=
  ((range (a + b)).filter fun t => ¬ IsRaising a b ((t + c) % (a + b))) ×ˢ
    ((range (a + b)).filter fun t => IsRaising a b ((t + c) % (a + b)))

/-- The ordered pairs `(s, s')` of a lowering slot and a raising slot whose cyclic difference
`s - s'` is congruent to `M` modulo `d = a + b`. -/
noncomputable def diffPairs (a b c M : ℕ) : Finset (ℕ × ℕ) :=
  (slotPairs a b c).filter fun p => M % (a + b) = (p.1 + (a + b) - p.2) % (a + b)

/-- **The partner of a slot at a prescribed difference is unique.** For `s` and `s'` below `d`,
the cyclic difference `s - s'` is `M` exactly when `s` is the reduction of `s' + M`. -/
theorem mod_diff_iff {d s s' M : ℕ} (hs : s < d) (hs' : s' < d) :
    M % d = (s + d - s') % d ↔ s = (s' + M) % d := by
  have hkey : s + d - s' + s' = s + d := by omega
  constructor
  · intro h
    have h1 : (M + s') % d = (s + d - s' + s') % d := Nat.ModEq.add_right s' h
    rw [hkey, Nat.add_mod_right, Nat.mod_eq_of_lt hs] at h1
    rw [Nat.add_comm s' M, h1]
  · intro h
    have h1 : (s + d - s' + s') % d = (M + s') % d := by
      rw [hkey, Nat.add_mod_right, Nat.mod_eq_of_lt hs, Nat.add_comm M s', ← h]
    exact (Nat.ModEq.add_right_cancel' s' h1).symm

/-- **The pairs are indexed by their raising slot.** -/
theorem diffPairs_eq_image (a b c M : ℕ) :
    diffPairs a b c M
      = ((range (a + b)).filter fun s' =>
          IsRaising a b ((s' + c) % (a + b)) ∧
            ¬ IsRaising a b (((s' + M) % (a + b) + c) % (a + b))).image
        fun s' => ((s' + M) % (a + b), s') := by
  classical
  refine Finset.ext fun p => ?_
  simp only [diffPairs, slotPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
    Finset.mem_image]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩
    have hp : p.1 = (p.2 + M) % (a + b) := (mod_diff_iff h1 h3).mp h5
    exact ⟨p.2, ⟨h3, h4, by rwa [← hp]⟩, by rw [← hp]⟩
  · rintro ⟨s', ⟨h1, h2, h3⟩, rfl⟩
    have hd : 0 < a + b := by
      by_contra hcon
      exact absurd h1 (by omega)
    refine ⟨⟨⟨Nat.mod_lt _ hd, h3⟩, h1, h2⟩, ?_⟩
    exact (mod_diff_iff (Nat.mod_lt _ hd) h1).mpr rfl

/-- The count of pairs is the count of raising slots whose partner is lowering. -/
theorem card_diffPairs_eq (a b c M : ℕ) :
    (diffPairs a b c M).card
      = ((range (a + b)).filter fun s' =>
          IsRaising a b ((s' + c) % (a + b)) ∧
            ¬ IsRaising a b (((s' + M) % (a + b) + c) % (a + b))).card := by
  classical
  rw [diffPairs_eq_image]
  refine Finset.card_image_of_injective _ fun s t h => ?_
  exact (Prod.mk.injEq _ _ _ _).mp h |>.2

/-! ### Multiplication by `a` reindexes the slots -/

/-- Multiplication by `a` modulo `d` is injective on `[0, d)`, `a` being coprime to `d`. -/
theorem injOn_mul_mod {d a : ℕ} (hco : Nat.Coprime d a) :
    Set.InjOn (fun t => t * a % d) (range d) := by
  intro t ht t' ht' h
  simp only [Finset.coe_range, Set.mem_Iio] at ht ht'
  have hgen : ∀ u v : ℕ, u ≤ v → v < d → u * a % d = v * a % d → u = v := by
    intro u v huv hv h'
    have h2 : d ∣ v * a - u * a :=
      (Nat.modEq_iff_dvd' (Nat.mul_le_mul_right a huv)).mp h'
    have h3 : d ∣ (v - u) * a := by rwa [Nat.sub_mul]
    rcases Nat.eq_zero_or_pos (v - u) with h4 | h4
    · omega
    · exact absurd (Nat.le_of_dvd h4 (hco.dvd_of_dvd_mul_right h3)) (by omega)
  rcases le_total t t' with hle | hle
  · exact hgen t t' hle ht' h
  · exact (hgen t' t hle ht h.symm).symm

/-- Multiplication by `a` modulo `d` is onto `[0, d)`. -/
theorem image_mul_mod {d a : ℕ} (hd : 0 < d) (hco : Nat.Coprime d a) :
    (range d).image (fun t => t * a % d) = range d := by
  refine Finset.eq_of_subset_of_card_le (fun u hu => ?_) ?_
  · obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hu
    exact Finset.mem_range.mpr (Nat.mod_lt _ hd)
  · rw [Finset.card_range, Finset.card_image_of_injOn (injOn_mul_mod hco), Finset.card_range]

/-- **Reindexing a count along a bijection of the slots.** -/
theorem card_filter_comp {d : ℕ} {f : ℕ → ℕ} (himg : (range d).image f = range d)
    (hinj : Set.InjOn f (range d)) (Q : ℕ → Prop) [DecidablePred Q] :
    ((range d).filter fun t => Q (f t)).card = ((range d).filter Q).card := by
  classical
  calc ((range d).filter fun t => Q (f t)).card
      = (((range d).filter fun t => Q (f t)).image f).card :=
        (Finset.card_image_of_injOn
          (hinj.mono (by exact_mod_cast Finset.filter_subset _ _))).symm
    _ = (((range d).image f).filter Q).card := by rw [Finset.filter_image]
    _ = ((range d).filter Q).card := by rw [himg]

/-- Translation by `c` modulo `d` is injective on `[0, d)`. -/
theorem injOn_add_mod {d c : ℕ} : Set.InjOn (fun t => (t + c) % d) (range d) := by
  intro t ht t' ht' h
  simp only [Finset.coe_range, Set.mem_Iio] at ht ht'
  have hgen : ∀ u v : ℕ, u ≤ v → v < d → (u + c) % d = (v + c) % d → u = v := by
    intro u v huv hv h'
    have h2 : d ∣ v + c - (u + c) := (Nat.modEq_iff_dvd' (by omega)).mp h'
    rw [show v + c - (u + c) = v - u by omega] at h2
    rcases Nat.eq_zero_or_pos (v - u) with h4 | h4
    · omega
    · exact absurd (Nat.le_of_dvd h4 h2) (by omega)
  rcases le_total t t' with hle | hle
  · exact hgen t t' hle ht' h
  · exact (hgen t' t hle ht h.symm).symm

/-- Translation by `c` modulo `d` is onto `[0, d)`. -/
theorem image_add_mod {d c : ℕ} (hd : 0 < d) :
    (range d).image (fun t => (t + c) % d) = range d := by
  refine Finset.eq_of_subset_of_card_le (fun u hu => ?_) ?_
  · obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hu
    exact Finset.mem_range.mpr (Nat.mod_lt _ hd)
  · rw [Finset.card_range, Finset.card_image_of_injOn injOn_add_mod, Finset.card_range]

/-! ### The slot conditions in the reindexed variable -/

/-- The raising condition at the reduction of `t + M` reads, in the variable `u = ta \bmod d`,
as the translate of `u` by `μ = Ma \bmod d`. -/
theorem isRaising_mod_add {a b t M : ℕ} :
    IsRaising a b ((t + M) % (a + b))
      ↔ b ≤ (t * a % (a + b) + M * a % (a + b)) % (a + b) := by
  have h1 : (t + M) % (a + b) * a % (a + b) = (t + M) * a % (a + b) :=
    Nat.ModEq.mul_right a (Nat.mod_modEq _ _)
  rw [IsRaising, h1, Nat.add_mul, Nat.add_mod]

/-! ### The interval that the count reduces to -/

/-- The reindexed count is the length of an interval. -/
theorem filter_translate_eq_Ico {d b mu : ℕ} (hd : 0 < d) (hmu : mu < d) :
    ((range d).filter fun u => b ≤ u ∧ ¬ b ≤ (u + mu) % d)
      = Finset.Ico (max b (d - mu)) (min d (d + b - mu)) := by
  refine Finset.ext fun u => ?_
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, not_le]
  constructor
  · rintro ⟨hu, hb, hlt⟩
    by_cases hcase : u + mu < d
    · rw [Nat.mod_eq_of_lt hcase] at hlt; omega
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hlt
      omega
  · rintro ⟨h1, h2⟩
    have hcase : ¬ u + mu < d := by omega
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

/-! ### The count is the cylindric weight -/

/-- The cylindric weight in natural numbers: `min {a, b, min (aM \bmod d, d - aM \bmod d)}`. -/
theorem cylWeight_eq_nat {a b M : ℕ} (hd : 0 < a + b) :
    HJO.Defs.cylWeight a b M
      = min (min a b) (min (a * M % (a + b)) ((a + b) - a * M % (a + b))) := by
  have h := HJO.Defs.cylWeight_eq a b M
  have hmod : (a : ℤ) * M % ((a : ℤ) + b) = ((a * M % (a + b) : ℕ) : ℤ) := by
    push_cast [Int.natCast_mod]
    ring_nf
  rw [hmod] at h
  have hlt : a * M % (a + b) < a + b := Nat.mod_lt _ hd
  omega

/-- **The pairs at cyclic difference `M` number `w_{a,b}(M)`.** This is the arithmetic core of the
assembled-exponent identity: the raising slots are the image of an interval of length `a` under
multiplication by `a` modulo `d`, so counting pairs at a prescribed cyclic difference intersects
two blocks of lengths `a` and `b`. -/
theorem card_diffPairs {a b : ℕ} (hco : Nat.Coprime a b) (ha : 0 < a) (hab : a < b) (c M : ℕ) :
    (diffPairs a b c M).card = HJO.Defs.cylWeight a b M := by
  classical
  have hd : 0 < a + b := by omega
  have hcod : Nat.Coprime (a + b) a := by
    rw [Nat.coprime_comm]
    simpa using (Nat.coprime_add_self_right (m := a) (n := b)).mpr hco
  have hmu : a * M % (a + b) < a + b := Nat.mod_lt _ hd
  have hmu' : M * a % (a + b) = a * M % (a + b) := by rw [Nat.mul_comm]
  rw [card_diffPairs_eq]
  have hshift : ∀ t, (IsRaising a b ((t + c) % (a + b)) ∧
        ¬ IsRaising a b (((t + M) % (a + b) + c) % (a + b)))
      ↔ (fun u => IsRaising a b u ∧ ¬ IsRaising a b ((u + M) % (a + b))) ((t + c) % (a + b)) := by
    intro t
    have hkey : ((t + M) % (a + b) + c) % (a + b) = ((t + c) % (a + b) + M) % (a + b) := by
      rw [Nat.mod_add_mod, Nat.mod_add_mod, Nat.add_right_comm]
    rw [hkey]
  rw [Finset.filter_congr fun t _ => (by rw [hshift t] : _ ↔ _),
    card_filter_comp (image_add_mod hd) injOn_add_mod
      (fun u => IsRaising a b u ∧ ¬ IsRaising a b ((u + M) % (a + b)))]
  have hpred : ∀ t, (IsRaising a b t ∧ ¬ IsRaising a b ((t + M) % (a + b)))
      ↔ (b ≤ t * a % (a + b) ∧ ¬ b ≤ (t * a % (a + b) + a * M % (a + b)) % (a + b)) := by
    intro t
    rw [IsRaising, isRaising_mod_add, hmu']
  rw [Finset.filter_congr fun t _ => (by rw [hpred t] : _ ↔ _),
    card_filter_comp (image_mul_mod hd hcod) (injOn_mul_mod hcod)
      (fun u => b ≤ u ∧ ¬ b ≤ (u + a * M % (a + b)) % (a + b)),
    filter_translate_eq_Ico hd hmu, Nat.card_Ico, cylWeight_eq_nat hd]
  omega

/-! ### The exponents contributed by one pair -/

/-- **One pair contributes each positive integer in its residue class exactly once.** At the pair
`(s, s')` the winding family supplies the exponents `d + s - s' + dn` for `n ≥ 0` and the crossing
factor, present exactly when `s' < s`, supplies the one remaining positive representative
`s - s'`. -/
theorem exponent_indicator {d s s' M : ℕ} (hd : 0 < d) (hs : s < d) (hs' : s' < d)
    (hM : 1 ≤ M) :
    (if d + s - s' ≤ M ∧ d ∣ M - (d + s - s') then (1 : ℤ) else 0)
        + (if s' < s ∧ M = s - s' then (1 : ℤ) else 0)
      = if M % d = (s + d - s') % d then (1 : ℤ) else 0 := by
  have hJ : (d + s - s') % d = (s + d - s') % d := by rw [Nat.add_comm d s]
  have hiff : ∀ _ : d + s - s' ≤ M, (d ∣ M - (d + s - s') ↔ M % d = (s + d - s') % d) := by
    intro hle
    rw [← Nat.modEq_iff_dvd' hle, Nat.ModEq, hJ]
    exact eq_comm
  have hmodle := Nat.mod_le M d
  by_cases hle : s' ≤ s
  · have hdelta : (s + d - s') % d = s - s' := by
      rw [show s + d - s' = (s - s') + d by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    by_cases hres : M % d = s - s'
    · by_cases hsmall : M = s - s'
      · rw [ite_eq_right (by rintro ⟨h1, -⟩; omega), ite_eq_left ⟨by omega, hsmall⟩,
          ite_eq_left (hres.trans hdelta.symm)]
        norm_num
      · have hdvd : d ∣ M - (s - s') :=
          (Nat.modEq_iff_dvd' (by omega : s - s' ≤ M)).mp
            (by rw [Nat.ModEq, Nat.mod_eq_of_lt (show s - s' < d by omega), hres])
        have hbig : d ≤ M - (s - s') := Nat.le_of_dvd (by omega) hdvd
        have hlemma : d + s - s' ≤ M := by omega
        rw [ite_eq_left ⟨hlemma, (hiff hlemma).mpr (hres.trans hdelta.symm)⟩,
          ite_eq_right (fun h => hsmall h.2), ite_eq_left (hres.trans hdelta.symm)]
        norm_num
    · rw [ite_eq_right (fun h => hres (((hiff h.1).mp h.2).trans hdelta)),
        ite_eq_right (fun h => hres (by rw [h.2, Nat.mod_eq_of_lt (by omega)])),
        ite_eq_right (fun h => hres (h.trans hdelta))]
      norm_num
  · have hlt : s + d - s' < d := by omega
    have hdelta : (s + d - s') % d = s + d - s' := Nat.mod_eq_of_lt hlt
    have hmodlt : M % d < d := Nat.mod_lt _ hd
    by_cases hres : M % d = s + d - s'
    · have hge : d + s - s' ≤ M := by omega
      rw [ite_eq_left ⟨hge, (hiff hge).mpr (hres.trans hdelta.symm)⟩,
        ite_eq_right (by rintro ⟨h1, -⟩; omega), ite_eq_left (hres.trans hdelta.symm)]
      norm_num
    · rw [ite_eq_right (fun h => hres (((hiff h.1).mp h.2).trans hdelta)),
        ite_eq_right (by rintro ⟨h1, -⟩; omega), ite_eq_right (fun h => hres (h.trans hdelta))]
      norm_num

/-! ### The assembled product -/

/-- The exponent of `1 - q^{m+1}` contributed by the winding family at the pair `p`: one if
`m + 1` is one of the exponents `d + s - s' + dn` with `n ≥ 0`, and zero otherwise. -/
def windExp (d : ℕ) (p : ℕ × ℕ) (m : ℕ) : ℤ :=
  if d + p.1 - p.2 ≤ m + 1 ∧ d ∣ (m + 1) - (d + p.1 - p.2) then 1 else 0

/-- The exponent of `1 - q^{m+1}` contributed by the crossing factor at the pair `p`: one if
`s' < s` and `m + 1 = s - s'`, and zero otherwise. -/
def crossExp (p : ℕ × ℕ) (m : ℕ) : ℤ :=
  if p.2 < p.1 ∧ m + 1 = p.1 - p.2 then 1 else 0

/-- A single factor `1 - q^k` as a product of integer powers of the `1 - q^m`. -/
theorem oneSub_X_pow_eq_tprod {k : ℕ} (hk : 1 ≤ k) :
    (1 - X ^ k : ℤ⟦X⟧) = ∏' m, Limits.zpowOneSub m (if m + 1 = k then (1 : ℤ) else 0) := by
  rw [tprod_eq_mulSingle (k - 1)
    (fun m hm => by rw [ite_eq_right (by omega), Limits.zpowOneSub_zero]),
    ite_eq_left (by omega : k - 1 + 1 = k), Limits.zpowOneSub_one,
    show k - 1 + 1 = k from by omega]

/-- **The assembled exponents.** The winding families over all pairs of a lowering and a raising
slot, together with the crossing factors at the pairs with `s' < s`, assemble into the single
product `∏_{m ≥ 1} (1 - q^m)^{w_{a,b}(m)}`. Both sides are inverted relative to the more familiar
arrangement, in which the left side is the product of the inverses of these factors and the right
side is `∏_{m ≥ 1}(1 - q^m)^{-w_{a,b}(m)}`; the form below avoids any power series inverse.

The arguments are those of `transferKernel`: at a lowering slot `s` and a raising slot `s'`
the pair argument is `x_{s'} y_s = q^{d + s - s'}`, so the winding family at that pair is
`(q^{d+s-s'}; q^d)_∞` and the crossing factor is `1 - q^{s-s'}`. The statement holds for the step
word shifted by any `c`, in particular for the rotated word of `transferKernel`. -/
@[hjo "lem_assembled_exponents"]
theorem assembled_exponents {a b : ℕ} (hco : Nat.Coprime a b) (ha : 0 < a) (hab : a < b)
    (c : ℕ) :
    (∏ p ∈ slotPairs a b c, ((X ^ (a + b + p.1 - p.2); X ^ (a + b))_∞ : ℤ⟦X⟧)) *
        ∏ p ∈ (slotPairs a b c).filter fun p => p.2 < p.1, (1 - X ^ (p.1 - p.2) : ℤ⟦X⟧)
      = ∏' m, Limits.zpowOneSub m (HJO.Defs.cylWeight a b (m + 1) : ℤ) := by
  classical
  have hd : 0 < a + b := by omega
  have hmem : ∀ p ∈ slotPairs a b c, p.1 < a + b ∧ p.2 < a + b := by
    intro p hp
    simp only [slotPairs, Finset.mem_product, Finset.mem_filter, Finset.mem_range] at hp
    exact ⟨hp.1.1, hp.2.1⟩
  have hfac1 : ∀ p ∈ slotPairs a b c,
      ((X ^ (a + b + p.1 - p.2); X ^ (a + b))_∞ : ℤ⟦X⟧)
        = ∏' m, Limits.zpowOneSub m (windExp (a + b) p m) := fun p hp =>
    Limits.qPochhammerInf_eq_tprod_zpowOneSub (by have := (hmem p hp).2; omega) hd
  have hfac2 : ∀ p ∈ (slotPairs a b c).filter fun p => p.2 < p.1,
      (1 - X ^ (p.1 - p.2) : ℤ⟦X⟧)
        = ∏' m, Limits.zpowOneSub m (if m + 1 = p.1 - p.2 then (1 : ℤ) else 0) := by
    intro p hp
    have hlt : p.2 < p.1 := (Finset.mem_filter.mp hp).2
    exact oneSub_X_pow_eq_tprod (by omega)
  rw [Finset.prod_congr rfl hfac1, Finset.prod_congr rfl hfac2,
    Limits.tprod_zpowOneSub_finsetProd, Limits.tprod_zpowOneSub_finsetProd,
    Limits.tprod_zpowOneSub_mul]
  refine tprod_congr fun m => ?_
  congr 1
  have hsplit : (∑ p ∈ (slotPairs a b c).filter fun p => p.2 < p.1,
      if m + 1 = p.1 - p.2 then (1 : ℤ) else 0) = ∑ p ∈ slotPairs a b c, crossExp p m := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun p _ => by simp only [crossExp, ite_and]
  have hterm : ∀ p ∈ slotPairs a b c, windExp (a + b) p m + crossExp p m
      = if (m + 1) % (a + b) = (p.1 + (a + b) - p.2) % (a + b) then (1 : ℤ) else 0 := by
    intro p hp
    rw [windExp, crossExp]
    exact exponent_indicator hd (hmem p hp).1 (hmem p hp).2 (by omega)
  rw [hsplit, ← Finset.sum_add_distrib, Finset.sum_congr rfl hterm, Finset.sum_boole,
    ← diffPairs, card_diffPairs hco ha hab c (m + 1)]

/-! ### The rotated step word of the transfer kernel -/

/-- The rotation of `transferKernel` is a shift: slot `t` of the rotated word is slot
`(t + c) mod d` of the original, with `c = d - r mod d` for the rotation offset `r`. -/
theorem rotSlot_eq_add_mod {a b : ℕ} (hd : 0 < a + b) (t : ℕ) :
    rotSlot a b t = (t + ((a + b) - rotOffset a b % (a + b))) % (a + b) := by
  have hr : rotOffset a b % (a + b) < a + b := Nat.mod_lt _ hd
  rw [rotSlot, show t + (a + b) - rotOffset a b % (a + b)
    = t + ((a + b) - rotOffset a b % (a + b)) from by omega]

/-- **The assembled exponents at the rotated word of `transferKernel`.** The specialisation of
`assembled_exponents` to the slots the transfer kernel actually uses. -/
@[hjo "lem_assembled_exponents"]
theorem assembled_exponents_rotSlot {a b : ℕ} (hco : Nat.Coprime a b) (ha : 0 < a)
    (hab : a < b) :
    (∏ p ∈ ((range (a + b)).filter fun t => ¬ IsRaising a b (rotSlot a b t)) ×ˢ
        ((range (a + b)).filter fun t => IsRaising a b (rotSlot a b t)),
          ((X ^ (a + b + p.1 - p.2); X ^ (a + b))_∞ : ℤ⟦X⟧)) *
        ∏ p ∈ (((range (a + b)).filter fun t => ¬ IsRaising a b (rotSlot a b t)) ×ˢ
            ((range (a + b)).filter fun t => IsRaising a b (rotSlot a b t))).filter
          fun p => p.2 < p.1, (1 - X ^ (p.1 - p.2) : ℤ⟦X⟧)
      = ∏' m, Limits.zpowOneSub m (HJO.Defs.cylWeight a b (m + 1) : ℤ) := by
  classical
  have hd : 0 < a + b := by omega
  have hset : ((range (a + b)).filter fun t => ¬ IsRaising a b (rotSlot a b t)) ×ˢ
      ((range (a + b)).filter fun t => IsRaising a b (rotSlot a b t))
      = slotPairs a b ((a + b) - rotOffset a b % (a + b)) := by
    simp only [slotPairs, rotSlot_eq_add_mod hd]
  rw [hset]
  exact assembled_exponents hco ha hab _

end HJO.CylindricProduct
