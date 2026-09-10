/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import QSeriesLib.NumberTheory.QTheory.Defs
public import QSeriesLib.RingTheory.PowerSeries.DiscreteTopology
public import HJO.Defs
public import HJO.Series.Gaps
public meta import HJO.Attr

/-! # The exponents of the explicit cylindric product

For coprime `1 < a < b` and `d = a + b`, the explicit product
`(q^d; q^d)_∞^{a-1} / (q; q)_∞^{a-1} ∏_{s=1}^{a-1} ∏_{v=0}^{a-1} (q^{J_{v,s}}; q^d)_∞`
and the product `∏_{m ≥ 1} (1 - q^m)^{-ρ m}` have the same exponent at every factor
`1 - q^m`: this is `total_exponent_eq`, proved by counting the pairs `(v, s)` whose shift
sum `J_{v,s}` lies in the residue class of `m` modulo `d`.
-/

@[expose] public section

open Finset

namespace HJO.ProductExponents

open HJO.Cylindric

/-! ### Arithmetic of the cylindric shift sums -/

/-- Coprimality of `a` and `b` passes to `a` and `d = a + b`. -/
theorem coprime_add {a b : ℕ} (hab : a.Coprime b) : a.Coprime (a + b) := by
  rw [Nat.add_comm, Nat.coprime_add_self_right]
  exact hab

/-- A sum of two residues below `a` contributes a quotient of `1` or `0` according as it
reaches `a` or not. -/
theorem div_eq_ite_of_lt {a x y : ℕ} (hx : x < a) (hy : y < a) :
    (x + y) / a = if a ≤ x + y then 1 else 0 := by
  split_ifs with h
  · have h1 : (x + y - a) / a = 0 := Nat.div_eq_of_lt (by omega)
    have h2 : (x + y) / a = (x + y - a) / a + 1 := by
      conv_lhs => rw [show x + y = x + y - a + a by omega]
      rw [Nat.add_div_right _ (by omega)]
    omega
  · exact Nat.div_eq_of_lt (by omega)

/-- Adding a residue `x < a` before dividing by `a` shifts the quotient by at most one. -/
theorem add_div_eq_of_lt {a x y : ℕ} (ha : 0 < a) (hx : x < a) :
    (x + y) / a = y / a + if a ≤ x + y % a then 1 else 0 := by
  conv_lhs => rw [← Nat.div_add_mod y a]
  rw [show x + (a * (y / a) + y % a) = a * (y / a) + (x + y % a) by ring, Nat.mul_add_div ha,
    div_eq_ite_of_lt hx (Nat.mod_lt _ ha)]

/-- The shift sums telescope: `J_{v,s} + ⌊vd/a⌋ = ⌊(v+s)d/a⌋`. -/
theorem jSum_add_div (a b v s : ℕ) :
    jSum a b v s + v * (a + b) / a = (v + s) * (a + b) / a := by
  induction s with
  | zero => simp [jSum]
  | succ s ih =>
    have h1 : jSum a b v (s + 1) = jSum a b v s + jShift a b (v + s) := by
      simp [jSum, Finset.sum_range_succ]
    have h2 : jShift a b (v + s) = (v + s + 1) * (a + b) / a - (v + s) * (a + b) / a := rfl
    have h3 : (v + (s + 1)) * (a + b) / a = (v + s + 1) * (a + b) / a := by
      rw [show v + (s + 1) = v + s + 1 from (Nat.add_assoc v s 1).symm]
    have hle : (v + s) * (a + b) / a ≤ (v + s + 1) * (a + b) / a :=
      Nat.div_le_div_right (Nat.mul_le_mul (by omega) (le_refl (a + b)))
    rw [h1, h2, h3]
    omega

/-- The shift sum in closed form: `J_{v,s}` is `⌊sd/a⌋`, plus one exactly when the residues
of `vd` and of `sd` modulo `a` overflow. -/
theorem jSum_eq {a : ℕ} (ha : 0 < a) (b v s : ℕ) :
    jSum a b v s
      = s * (a + b) / a + if a ≤ v * (a + b) % a + s * (a + b) % a then 1 else 0 := by
  have h1 := jSum_add_div a b v s
  have h2 : (v + s) * (a + b) / a
      = v * (a + b) / a
        + (s * (a + b) / a + if a ≤ v * (a + b) % a + s * (a + b) % a then 1 else 0) := by
    rw [Nat.add_mul]
    conv_lhs => rw [← Nat.div_add_mod (v * (a + b)) a]
    rw [show a * (v * (a + b) / a) + v * (a + b) % a + s * (a + b)
        = a * (v * (a + b) / a) + (v * (a + b) % a + s * (a + b)) by ring,
      Nat.mul_add_div ha, add_div_eq_of_lt ha (Nat.mod_lt _ ha)]
  refine Nat.add_right_cancel (m := v * (a + b) / a) ?_
  rw [h1, h2]
  exact Nat.add_comm _ _

/-- For `1 ≤ s < a` the shift sum is a nonzero residue modulo `d`: `0 < J_{v,s} < d`. -/
theorem jSum_pos_lt {a b : ℕ} (ha : 1 < a) (hb : a < b) (v : ℕ) {s : ℕ} (hs : 0 < s)
    (hsa : s < a) : 0 < jSum a b v s ∧ jSum a b v s < a + b := by
  have ha' : 0 < a := by omega
  have h1 : 1 ≤ s * (a + b) / a := by
    rw [Nat.le_div_iff_mul_le ha']
    calc 1 * a ≤ 1 * (a + b) := Nat.mul_le_mul (le_refl 1) (by omega)
      _ ≤ s * (a + b) := Nat.mul_le_mul hs (le_refl (a + b))
  have hxa : a + b ≤ a * (a + b) := Nat.le_mul_of_pos_left _ ha'
  have h4 : (a - 1) * (a + b) < (a + b - 1) * a := by
    rw [Nat.sub_mul, Nat.sub_mul, Nat.one_mul, Nat.one_mul, Nat.mul_comm (a + b) a]
    omega
  have h5 : s * (a + b) / a < a + b - 1 := by
    rw [Nat.div_lt_iff_lt_mul ha']
    exact lt_of_le_of_lt (Nat.mul_le_mul (by omega : s ≤ a - 1) (le_refl (a + b))) h4
  rw [jSum_eq ha']
  split_ifs <;> omega

/-! ### Counting the shift sums in one period -/

/-- The number of `v` in one period with `J_{v,s} = i`: it is `a - (sd mod a)` at
`i = ⌊sd/a⌋`, it is `sd mod a` at `i = ⌊sd/a⌋ + 1`, and it vanishes elsewhere. -/
def periodCount (a b s i : ℕ) : ℕ :=
  if i = s * (a + b) / a then a - s * (a + b) % a
  else if i = s * (a + b) / a + 1 then s * (a + b) % a else 0

/-- Multiplying by `d` permutes the residues modulo `a` when `a` and `d` are coprime, so
exactly `c` of the residues of `v * d` with `v < a` are below `c ≤ a`. -/
theorem card_filter_mul_mod_lt {a d : ℕ} (ha : 0 < a) (h : a.Coprime d) {c : ℕ} (hc : c ≤ a) :
    #{v ∈ range a | v * d % a < c} = c := by
  have hinj : Set.InjOn (fun v => v * d % a) (range a) := by
    intro x hx y hy hxy
    simp only [Finset.mem_coe, mem_range] at hx hy
    have h1 : x ≡ y [MOD a] := Nat.ModEq.cancel_right_of_coprime h hxy
    rw [Nat.ModEq, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at h1
    exact h1
  have himg : (range a).image (fun v => v * d % a) = range a := by
    refine Finset.eq_of_subset_of_card_le (fun y hy => ?_) ?_
    · simp only [mem_image] at hy
      obtain ⟨v, _, rfl⟩ := hy
      exact mem_range.mpr (Nat.mod_lt _ ha)
    · rw [Finset.card_image_of_injOn hinj]
  have hfl : (range a).filter (fun y => y < c) = range c := by
    ext x
    simp only [mem_filter, mem_range]
    omega
  calc #{v ∈ range a | v * d % a < c}
      = #(((range a).filter (fun v => v * d % a < c)).image (fun v => v * d % a)) :=
        (Finset.card_image_of_injOn
          (hinj.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _)))).symm
    _ = #(((range a).image (fun v => v * d % a)).filter (fun y => y < c)) := by
        rw [Finset.filter_image]
    _ = c := by rw [himg, hfl, card_range]

/-- In one period of `v` the shift sum `J_{v,s}` takes only the two values `⌊sd/a⌋` and
`⌊sd/a⌋ + 1`, with the multiplicities recorded by `periodCount`. -/
theorem card_filter_jSum {a b : ℕ} (ha : 0 < a) (hab : a.Coprime (a + b)) (s i : ℕ) :
    #{v ∈ range a | jSum a b v s = i} = periodCount a b s i := by
  have hw : s * (a + b) % a < a := Nat.mod_lt _ ha
  have hlow : {v ∈ range a | jSum a b v s = s * (a + b) / a}
      = {v ∈ range a | v * (a + b) % a < a - s * (a + b) % a} := by
    refine Finset.filter_congr fun v _ => ?_
    have hr : v * (a + b) % a < a := Nat.mod_lt _ ha
    rw [jSum_eq ha]
    split_ifs with hc <;> omega
  have hhigh : {v ∈ range a | jSum a b v s = s * (a + b) / a + 1}
      = {v ∈ range a | ¬ v * (a + b) % a < a - s * (a + b) % a} := by
    refine Finset.filter_congr fun v _ => ?_
    have hr : v * (a + b) % a < a := Nat.mod_lt _ ha
    rw [jSum_eq ha]
    split_ifs with hc <;> omega
  have hcompl : #{v ∈ range a | ¬ v * (a + b) % a < a - s * (a + b) % a} = s * (a + b) % a := by
    have h := Finset.card_filter_add_card_filter_not (s := range a)
      (fun v => v * (a + b) % a < a - s * (a + b) % a)
    rw [card_filter_mul_mod_lt ha hab (by omega), card_range] at h
    omega
  rw [periodCount]
  split_ifs with h1 h2
  · rw [h1, hlow, card_filter_mul_mod_lt ha hab (by omega)]
  · rw [h2, hhigh, hcompl]
  · refine Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun v _ => ?_)
    rw [jSum_eq ha]
    split_ifs with hc <;> omega

/-- The values `⌊sd/a⌋` are spaced at least two apart, because `d > 2a`. -/
theorem div_add_two_le {a b : ℕ} (ha : 0 < a) (hb : a < b) {s t : ℕ} (hst : s < t) :
    s * (a + b) / a + 2 ≤ t * (a + b) / a := by
  induction t with
  | zero => omega
  | succ t ih =>
    rcases Nat.lt_or_ge s t with h | h
    · exact (ih h).trans
        (Nat.div_le_div_right (Nat.mul_le_mul (by omega) (le_refl (a + b))))
    · have hst' : s = t := by omega
      subst hst'
      rw [Nat.le_div_iff_mul_le ha]
      calc (s * (a + b) / a + 2) * a = s * (a + b) / a * a + 2 * a := by ring
        _ ≤ s * (a + b) + (a + b) := by
            have := Nat.div_mul_le_self (s * (a + b)) a
            omega
        _ = (s + 1) * (a + b) := by ring

/-- Because the pairs `{⌊sd/a⌋, ⌊sd/a⌋ + 1}` are disjoint for different `s`, at most one
summand of `∑ s, periodCount a b s i` is nonzero. -/
theorem sum_periodCount_eq_single {a b : ℕ} (ha : 0 < a) (hb : a < b) {s₀ i : ℕ}
    (hs₀ : s₀ ∈ Ico 1 a) (hi : i = s₀ * (a + b) / a ∨ i = s₀ * (a + b) / a + 1) :
    ∑ s ∈ Ico 1 a, periodCount a b s i = periodCount a b s₀ i := by
  refine Finset.sum_eq_single_of_mem s₀ hs₀ fun s _ hne => ?_
  have h : i ≠ s * (a + b) / a ∧ i ≠ s * (a + b) / a + 1 := by
    rcases Nat.lt_or_ge s s₀ with hlt | hge
    · have := div_add_two_le ha hb hlt
      omega
    · have := div_add_two_le ha hb (show s₀ < s by omega)
      omega
  rw [periodCount, ite_eq_right h.1, ite_eq_right h.2]

/-- The residue count, summed over `s`: for `0 < i < d` the total is
`a - min a (dist (a * i, dℤ))`, the distance being `min (ai mod d) (d - ai mod d)`. -/
theorem sum_periodCount {a b i : ℕ} (ha : 1 < a) (hb : a < b) (hab : a.Coprime b)
    (hi : 0 < i) (hid : i < a + b) :
    ∑ s ∈ Ico 1 a, periodCount a b s i
      = a - min a (min (a * i % (a + b)) (a + b - a * i % (a + b))) := by
  have ha' : 0 < a := by omega
  have hd : 0 < a + b := by omega
  have hcop : a.Coprime (a + b) := coprime_add hab
  have hr : a * i % (a + b) < a + b := Nat.mod_lt _ hd
  have hai : a ≤ a * i := Nat.le_mul_of_pos_right a hi
  have haid : a * i < a * (a + b) := Nat.mul_lt_mul_of_pos_left hid ha'
  have hr0 : a * i % (a + b) ≠ 0 := by
    intro h0
    have h2 : (a + b) ∣ i := hcop.symm.dvd_of_dvd_mul_left (Nat.dvd_of_mod_eq_zero h0)
    have := Nat.le_of_dvd hi h2
    omega
  rcases Nat.lt_or_ge (a * i % (a + b)) a with hcase | hcase
  · -- `i = ⌊sd/a⌋ + 1` for `s = ⌊ai/d⌋`
    obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    have hdm : (a + b) * (a * (i' + 1) / (a + b)) + a * (i' + 1) % (a + b) = a * (i' + 1) :=
      Nat.div_add_mod _ _
    have hprod : a * (i' + 1) = a * i' + a := by ring
    have hs1 : 1 ≤ a * (i' + 1) / (a + b) := by
      rcases Nat.eq_zero_or_pos (a * (i' + 1) / (a + b)) with h0 | h0
      · rw [h0, Nat.mul_zero, Nat.zero_add] at hdm
        omega
      · exact h0
    have hsa : a * (i' + 1) / (a + b) < a := by
      by_contra hcon
      have h1 : (a + b) * a ≤ (a + b) * (a * (i' + 1) / (a + b)) :=
        Nat.mul_le_mul (le_refl (a + b)) (by omega)
      have hcomm : a * (a + b) = (a + b) * a := Nat.mul_comm _ _
      omega
    have hmul : a * (i' + 1) / (a + b) * (a + b) = a * i' + (a - a * (i' + 1) % (a + b)) := by
      rw [Nat.mul_comm (a * (i' + 1) / (a + b)) (a + b)]
      omega
    have hu : a * (i' + 1) / (a + b) * (a + b) / a = i' := by
      rw [hmul, Nat.mul_add_div ha', Nat.div_eq_of_lt (by omega), Nat.add_zero]
    have hwt : a * (i' + 1) / (a + b) * (a + b) % a = a - a * (i' + 1) % (a + b) := by
      rw [hmul, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
    rw [sum_periodCount_eq_single (s₀ := a * (i' + 1) / (a + b)) ha' hb
      (mem_Ico.mpr ⟨hs1, hsa⟩) (Or.inr (by rw [hu])), periodCount, hu, hwt,
      ite_eq_right (by omega), ite_eq_left rfl]
    omega
  · rcases Nat.lt_or_ge (a + b - a * i % (a + b)) a with hcase' | hcase'
    · -- `i = ⌊sd/a⌋` for `s = ⌊ai/d⌋ + 1`
      have hdm : (a + b) * (a * i / (a + b)) + a * i % (a + b) = a * i := Nat.div_add_mod _ _
      have hmul : (a * i / (a + b) + 1) * (a + b) = a * i + (a + b - a * i % (a + b)) := by
        rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (a * i / (a + b)) (a + b)]
        omega
      have hsa : a * i / (a + b) + 1 < a := by
        by_contra hcon
        have h1 : a * (a + b) ≤ (a * i / (a + b) + 1) * (a + b) :=
          Nat.mul_le_mul (by omega) (le_refl (a + b))
        have h2 : a * (i + 1) ≤ a * (a + b) := Nat.mul_le_mul (le_refl a) (by omega)
        have h3 : a * (i + 1) = a * i + a := by ring
        omega
      have hu : (a * i / (a + b) + 1) * (a + b) / a = i := by
        rw [hmul, Nat.mul_add_div ha', Nat.div_eq_of_lt (by omega), Nat.add_zero]
      have hwt : (a * i / (a + b) + 1) * (a + b) % a = a + b - a * i % (a + b) := by
        rw [hmul, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
      rw [sum_periodCount_eq_single (s₀ := a * i / (a + b) + 1) ha' hb
        (mem_Ico.mpr ⟨Nat.le_add_left 1 _, hsa⟩) (Or.inl (by rw [hu])), periodCount, hu, hwt,
        ite_eq_left rfl]
      omega
    · -- the distance is at least `a`, and no pair contributes
      have hzero : ∀ s ∈ Ico 1 a, periodCount a b s i = 0 := by
        intro s hs
        rw [mem_Ico] at hs
        obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
        have hw : (s' + 1) * (a + b) % a < a := Nat.mod_lt _ ha'
        have hw0 : (s' + 1) * (a + b) % a ≠ 0 := by
          intro h0
          have h2 : a ∣ s' + 1 :=
            hcop.dvd_of_dvd_mul_right (Nat.dvd_of_mod_eq_zero h0)
          have := Nat.le_of_dvd (by omega) h2
          omega
        have hdm : a * ((s' + 1) * (a + b) / a) + (s' + 1) * (a + b) % a = (s' + 1) * (a + b) :=
          Nat.div_add_mod _ _
        have hsplit : (s' + 1) * (a + b) = (a + b) * s' + (a + b) := by ring
        have hne1 : i ≠ (s' + 1) * (a + b) / a := by
          intro heq
          have h1 : a * i + (s' + 1) * (a + b) % a = (a + b) * s' + (a + b) := by
            rw [heq]
            omega
          have h2 : a * i = (a + b) * s' + (a + b - (s' + 1) * (a + b) % a) := by omega
          have h3 : a * i % (a + b) = a + b - (s' + 1) * (a + b) % a := by
            rw [h2, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
          omega
        have hne2 : i ≠ (s' + 1) * (a + b) / a + 1 := by
          intro heq
          have h1 : a * i = a * ((s' + 1) * (a + b) / a) + a := by rw [heq]; ring
          have h2 : a * i = (a + b) * s' + (a + b) + (a - (s' + 1) * (a + b) % a) := by
            rw [h1]; omega
          have h3 : a * i = (a + b) * (s' + 1) + (a - (s' + 1) * (a + b) % a) := by
            rw [h2]; ring
          have h4 : a * i % (a + b) = a - (s' + 1) * (a + b) % a := by
            rw [h3, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
          omega
        rw [periodCount, ite_eq_right hne1, ite_eq_right hne2]
      rw [Finset.sum_eq_zero hzero]
      omega

/-! ### The exponent identity -/

/-- The factor `1 - q^m` occurs in `(q^J; q^d)_∞` exactly when `m` lies in the class of `J`
modulo `d`, for a residue `0 < J < d`. -/
theorem le_and_dvd_sub_iff {d J m : ℕ} (hJd : J < d) :
    (J ≤ m ∧ d ∣ m - J) ↔ J = m % d := by
  constructor
  · rintro ⟨h1, k, hk⟩
    have hm : m = J + d * k := by omega
    rw [hm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hJd]
  · intro h
    refine ⟨by rw [h]; exact Nat.mod_le m d, ?_⟩
    rw [h]
    exact Nat.dvd_sub_mod m

/-- The two products agree factor by factor: for every `m`, the multiplicity of `1 - q^m` in
`(q^d; q^d)_∞^{a-1} / (q; q)_∞^{a-1} ∏_{s=1}^{a-1} ∏_{v=0}^{a-1} (q^{J_{v,s}}; q^d)_∞` is
`-ρ m`, where `d = a + b` and `ρ = HJO.negR a b` is the exponent of `1 - q^m` in the HJO
product. The three summands on the left are the contributions of `(q^d; q^d)_∞^{a-1}`, of
`(q; q)_∞^{-(a-1)}`, and of the pairs `(v, s)` with `m ∈ J_{v,s} + dℕ`. -/
@[hjo "lem_product_exponents"]
theorem total_exponent_eq {a b : ℕ} (ha : 1 < a) (hb : a < b) (hab : a.Coprime b) (m : ℕ) :
    ((a : ℤ) - 1) * (if a + b ∣ m then 1 else 0) - ((a : ℤ) - 1)
        + (∑ v ∈ range a, ∑ s ∈ Ico 1 a,
            if jSum a b v s ≤ m ∧ a + b ∣ m - jSum a b v s then 1 else 0 : ℕ)
      = -(HJO.negR a b m : ℤ) := by
  have ha' : 0 < a := by omega
  have hd : 0 < a + b := by omega
  have hcop : a.Coprime (a + b) := coprime_add hab
  have hcount : (∑ v ∈ range a, ∑ s ∈ Ico 1 a,
        if jSum a b v s ≤ m ∧ a + b ∣ m - jSum a b v s then 1 else 0)
      = ∑ s ∈ Ico 1 a, periodCount a b s (m % (a + b)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [mem_Ico] at hs
    rw [← card_filter_jSum ha' hcop s (m % (a + b)), Finset.card_filter]
    refine Finset.sum_congr rfl fun v _ => ?_
    exact if_congr (le_and_dvd_sub_iff (jSum_pos_lt ha hb v hs.1 hs.2).2) rfl rfl
  have hzc : ((a : ℤ) * m % ((a : ℤ) + b)) = ((a * m % (a + b) : ℕ) : ℤ) := by push_cast; ring
  have hrn : a * m % (a + b) < a + b := Nat.mod_lt _ hd
  rw [hcount, Gaps.negR_eq a b m hab, hzc]
  by_cases hdvd : (a + b) ∣ m
  · have hm0 : m % (a + b) = 0 := Nat.mod_eq_zero_of_dvd hdvd
    have hr0 : a * m % (a + b) = 0 := Nat.mod_eq_zero_of_dvd (Dvd.dvd.mul_left hdvd a)
    have hsum : ∑ s ∈ Ico 1 a, periodCount a b s (m % (a + b)) = 0 := by
      refine Finset.sum_eq_zero fun s hs => ?_
      rw [mem_Ico] at hs
      have h1 : 1 ≤ s * (a + b) / a := by
        rw [Nat.le_div_iff_mul_le ha']
        calc 1 * a ≤ 1 * (a + b) := Nat.mul_le_mul (le_refl 1) (by omega)
          _ ≤ s * (a + b) := Nat.mul_le_mul hs.1 (le_refl (a + b))
      rw [periodCount, ite_eq_right (by omega), ite_eq_right (by omega)]
    rw [hsum, hr0, ite_eq_left hdvd]
    push_cast
    have hab' : (a : ℤ) ≤ b := by exact_mod_cast hb.le
    have ha0 : (0 : ℤ) ≤ a := by positivity
    omega
  · have hi : 0 < m % (a + b) := Nat.pos_of_ne_zero fun h => hdvd (Nat.dvd_of_mod_eq_zero h)
    have hid : m % (a + b) < a + b := Nat.mod_lt _ hd
    have hmod : a * (m % (a + b)) % (a + b) = a * m % (a + b) :=
      (Nat.mod_modEq m (a + b)).mul_left a
    have hmin : min a (min (a * m % (a + b)) (a + b - a * m % (a + b))) ≤ a := min_le_left _ _
    rw [sum_periodCount ha hb hab hi hid, hmod, ite_eq_right hdvd, Nat.cast_sub hmin]
    push_cast [Nat.cast_sub hrn.le]
    have hab' : (a : ℤ) ≤ b := by exact_mod_cast hb.le
    omega

end HJO.ProductExponents
