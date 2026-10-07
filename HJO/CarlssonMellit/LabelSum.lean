/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.LabelWeight
public import HJO.CarlssonMellit.RunWeight
public meta import HJO.Attr

/-! # The class sum factorises over the runs

Fix a partial Dyck path `π` of level `k`, a no-attack labelling `w` of it with prescription `σ`, and
two consecutive letters `m`, `m + 1` one of which occurs among the entries of `σ`. Summing
`q^{inv(At(π), w')} z^{(k)}_{w'}` over the class `K_m(π, σ, w)` gives

`q^e · g · a_m(l_1, ε_1) · ∏_{t=2}^{r} (a_m(l_t, 0) + a_m(l_t, 1))`,

Carlsson and Mellit's factorisation of a class sum over the runs of the two-letter support. Three
things go into it. The class is a cube, by `HJO.Dyck.bijOn_runBit`: a member is determined by one
bit per run, and the bit of the first run is forced. The weight of a member is `q^e g` times the
product of the runs' weights: the inversion count is `HJO.Dyck.invNumber_eq_of_mem_labelClass`, and
the monomial factorises because the positions off the support carry the letters of `w` whatever the
member, while along a run the letters alternate, so the number of positions of the run carrying each
of the two letters is fixed by the run's length and its bit. Summing a product over a cube then
factorises it —
`Finset.prod_univ_sum`, with the forced coordinate read as a one-element factor.

## Main results

* `HJO.Dyck.card_filter_Icc_run`, `HJO.Dyck.card_filter_Icc_run_succ`: along an initial stretch of a
  run, how many indices carry each of the two letters.
* `HJO.Dyck.zmon_eq_prod_runs`: the monomial of a member of the class, broken into the positions off
  the support and the runs.
* `HJO.Dyck.pow_mul_prod_run_eq_runWeight`: one run contributes exactly its weight `a_m(l_t, ε_t)`.
* `HJO.Dyck.weight_eq_prod_runWeight`: the weight of a member of the class.
* `HJO.Dyck.finsum_labelClass`: the class sum.

## Implementation notes

*The class sum is a `finsum`.* `HJO.Dyck.labelClass` is a `Set`, being carved out of the infinite
`U(π, σ)`, and the cube bijection is what makes it finite; rather than replace it by a `Finset` —
which would need a chosen enumeration and a theorem identifying it with the class — the sum is
written with Mathlib's `∑ᶠ`, the convention `HJO.PointwiseSum` already follows for its
summability statements. The finiteness is derived inside the proof from
`HJO.Dyck.bijOn_runBit`, and the sum is transported to the face of the cube by `Finset.sum_bij`
along the *forward* map `w' ↦ ε(w')`, so no inverse has to be named.

*The runs are indexed by `Fin r` on the cube and by `1, …, r` everywhere else*, with the `j`-th bit
belonging to the run `j + 1`; `HJO.Dyck.prod_Icc_one_eq_prod_fin` and
`HJO.Dyck.sum_Icc_one_eq_sum_fin` move between the two. The `∏_{t=2}^r` is the product
over `Finset.univ.erase 0`.

*The hypotheses are weaker than Carlsson and Mellit's*, exactly as for the two lemmas below this
one: `σ` is not assumed to have pairwise distinct entries and `m ≥ 1` is not assumed (letters are
`0`-based here). What is needed is a `j₀` with `σ j₀ ∈ {m, m + 1}`.

*A fourth substantial part of the argument lives here and not in the two lemmas it uses.*
`HJO.Dyck.bijOn_runBit` and `HJO.Dyck.invNumber_eq_of_mem_labelClass` give the cube and the
inversion count; the factorisation of the *monomial* `z^{(k)}_{w'}` over the runs, and the
conversion of the three letter-counts into the exponents of `a_m(l_t, ε_t)`, are neither of those
and are proved here (`HJO.Dyck.zmon_eq_prod_runs` and `HJO.Dyck.pow_mul_prod_run_eq_runWeight`). So
the class sum is not obtained from those two lemmas by `Finset.prod_univ_sum` alone.

## References

The lemma `HJO.Dyck.finsum_labelClass`, on swapping operators; E. Carlsson and A. Mellit, *A proof
of the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018) 661--697, Section 4.
-/

@[expose] public section

open Finset

namespace HJO.Sym

/-! ### Counting by parity along an interval -/

/-- The indices of `{0, …, n-1}` whose shift by `e` is even number `⌈n/2⌉` when `e` is even and
`⌊n/2⌋` when it is odd. -/
theorem card_filter_range_add_even (n e : ℕ) :
    #{d ∈ range n | (d + e) % 2 = 0} = if e % 2 = 0 then (n + 1) / 2 else n / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [range_add_one, Finset.filter_insert]
    split
    · rename_i hn
      rw [Finset.card_insert_of_notMem (by simp), ih]
      split_ifs with he <;> omega
    · rename_i hn
      rw [ih]
      split_ifs with he <;> omega

/-- The complementary count, the same table read the other way. -/
theorem card_filter_range_add_not_even (n e : ℕ) :
    #{d ∈ range n | ¬((d + e) % 2 = 0)} = if e % 2 = 0 then n / 2 else (n + 1) / 2 := by
  have h := Finset.card_filter_add_card_filter_not (s := range n) (fun d => (d + e) % 2 = 0)
  rw [card_filter_range_add_even, Finset.card_range] at h
  split_ifs at h ⊢ <;> omega

/-- Counting along `{a, …, a + n - 1}` by a condition on the distance from `a` is counting along
`{0, …, n-1}`. The hypothesis `1 ≤ a` is what makes the interval empty at `n = 0`. -/
theorem card_filter_Icc_sub (a n : ℕ) (ha : 1 ≤ a) (Q : ℕ → Prop) [DecidablePred Q] :
    #{c ∈ Icc a (a + n - 1) | Q (c - a)} = #{d ∈ range n | Q d} := by
  refine Finset.card_bij' (fun c _ => c - a) (fun d _ => a + d) ?_ ?_ ?_ ?_
  · intro c hc
    have hcQ := (mem_filter.1 hc).2
    have hc' := mem_Icc.1 (mem_filter.1 hc).1
    exact mem_filter.2 ⟨mem_range.2 (by omega), hcQ⟩
  · intro d hd
    obtain ⟨hdr, hdQ⟩ := mem_filter.1 hd
    have hdn := mem_range.1 hdr
    refine mem_filter.2 ⟨mem_Icc.2 ⟨by omega, by omega⟩, ?_⟩
    rwa [show a + d - a = d from by omega]
  · intro c hc
    have := mem_Icc.1 (mem_filter.1 hc).1
    omega
  · intro d _
    omega

end HJO.Sym

namespace HJO.Dyck

open HJO.Sym

variable {N k : ℕ} {x : Fin N → ℕ} {σ : Fin k → ℕ} {m : ℕ} {w w' : Fin N → ℕ}

/-! ### Reindexing the runs -/

/-- The runs `1, …, r` reindexed by `Fin r`, for a product. -/
theorem prod_Icc_one_eq_prod_fin {M : Type*} [CommMonoid M] (r : ℕ) (f : ℕ → M) :
    ∏ t ∈ Icc 1 r, f t = ∏ j : Fin r, f ((j : ℕ) + 1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range,
    Fin.prod_univ_eq_prod_range (fun i => f (i + 1)) r]
  exact Finset.prod_congr (by simp) fun i _ => by rw [Nat.add_comm]

/-- The runs `2, …, r` reindexed by `Fin r` with the first run removed:
`∏_{t=2}^{r}` as a product over `Finset.univ.erase 0`. Stated with the run count of a labelling so
that no dependent type enters a consumer's rewriting. -/
theorem prod_Icc_two_eq_prod_erase_zero {M : Type*} [CommMonoid M] (x : Fin N → ℕ) (m : ℕ)
    (w : Fin N → ℕ) (h : ℕ → M) :
    ∏ t ∈ Icc 2 (labelRunCount x m w), h t
      = ∏ j ∈ (Finset.univ : Finset (Fin (labelRunCount x m w))).erase 0, h ((j : ℕ) + 1) := by
  refine Finset.prod_bij (fun t ht => (⟨t - 1, by have := mem_Icc.1 ht; omega⟩ :
    Fin (labelRunCount x m w))) ?_ ?_ ?_ ?_
  · intro t ht
    have h2 := mem_Icc.1 ht
    refine Finset.mem_erase.2 ⟨fun hc => ?_, mem_univ _⟩
    have := congrArg Fin.val hc
    simp only [Fin.val_zero] at this
    omega
  · intro t₁ h₁ t₂ h₂ heq
    have e₁ := mem_Icc.1 h₁
    have e₂ := mem_Icc.1 h₂
    have := congrArg Fin.val heq
    simp only at this
    omega
  · intro j hj
    have hj0 : (j : ℕ) ≠ 0 := fun hc => (Finset.mem_erase.1 hj).1 (Fin.ext (by simpa using hc))
    have hjr : (j : ℕ) < labelRunCount x m w := j.isLt
    refine ⟨(j : ℕ) + 1, mem_Icc.2 ⟨by omega, by omega⟩, Fin.ext ?_⟩
    simp only
    omega
  · intro t ht
    have h2 := mem_Icc.1 ht
    simp only
    rw [show t - 1 + 1 = t from by omega]

/-- The runs `1, …, r` reindexed by `Fin r`, for a sum. -/
theorem sum_Icc_one_eq_sum_fin (r : ℕ) (f : ℕ → ℕ) :
    ∑ t ∈ Icc 1 r, f t = ∑ j : Fin r, f ((j : ℕ) + 1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range,
    Fin.sum_univ_eq_sum_range (fun i => f (i + 1)) r]
  exact Finset.sum_congr (by simp) fun i _ => by rw [Nat.add_comm]

/-! ### The letters of a member of the class along a run -/

/-- The letter at a distance `D` from a reference letter of `{m, m+1}`, given the shift `e` that
records which of the two the reference letter is. -/
private theorem parity_iff {m u u₁ D e : ℕ} (hu : u = m ∨ u = m + 1)
    (hu₁ : u₁ = m ∨ u₁ = m + 1) (he : u₁ = m + 1 → e = 1) (he' : u₁ = m → e = 0)
    (huiff : u = u₁ ↔ D % 2 = 0) : u = m ↔ (D + e) % 2 = 0 := by
  rcases hu₁ with h1 | h1
  · rw [he' h1, Nat.add_zero, ← huiff, h1]
  · rw [he h1]
    rcases hu with h | h
    · rw [h]
      have hne : u ≠ u₁ := by rw [h, h1]; omega
      have hpar : ¬ (D % 2 = 0) := fun hh => hne (huiff.2 hh)
      constructor <;> intro hh <;> omega
    · rw [h]
      have heq : u = u₁ := by rw [h, h1]
      have hpar : D % 2 = 0 := huiff.1 heq
      constructor <;> intro hh <;> omega

/-- **The letter of a member of the class at an index of a run** is `m` exactly when the distance
from the run's first index, shifted by the run's bit, is even. -/
theorem wordOfFin_sortNth_eq_iff_parity (hw' : w' ∈ labelClass x σ m w) {c t : ℕ}
    (hne : (labelRun x m w t).Nonempty) (hct : c ∈ labelRun x m w t) :
    wordOfFin w' (sortNth (labelSupport m w) c) = m ↔
      (c - cutBlockMin #(labelSupport m w) (labelCutSet x m w) t +
        (if runBit x m w w' t then 1 else 0)) % 2 = 0 := by
  have hamem := cutBlockMin_mem hne
  have hale := cutBlockMin_le hct
  have hmemaS : sortNth (labelSupport m w)
      (cutBlockMin #(labelSupport m w) (labelCutSet x m w) t) ∈ labelSupport m w :=
    sortNth_mem (one_le_cutBlockMin hne) (cutBlockMin_le_card hne)
  have hmemcS : sortNth (labelSupport m w) c ∈ labelSupport m w :=
    sortNth_mem (mem_cutBlock.1 hct).1.1 (mem_cutBlock.1 hct).1.2
  refine parity_iff (wordOfFin_mem_pair_of_mem_labelClass hw' hmemcS)
    (wordOfFin_mem_pair_of_mem_labelClass hw' hmemaS) (fun h => ?_) (fun h => ?_)
    (wordOfFin_sortNth_eq_iff_even_of_mem_labelClass hw' hale hamem hct)
  · rw [runBit, h]; simp
  · rw [runBit, h]; simp

/-- The letter at an index of a run is `m + 1` exactly when it is not `m`. -/
theorem wordOfFin_sortNth_eq_succ_iff_parity (hw' : w' ∈ labelClass x σ m w) {c t : ℕ}
    (hne : (labelRun x m w t).Nonempty) (hct : c ∈ labelRun x m w t) :
    wordOfFin w' (sortNth (labelSupport m w) c) = m + 1 ↔
      ¬((c - cutBlockMin #(labelSupport m w) (labelCutSet x m w) t +
        (if runBit x m w w' t then 1 else 0)) % 2 = 0) := by
  rw [← wordOfFin_sortNth_eq_iff_parity hw' hne hct]
  have hmemcS : sortNth (labelSupport m w) c ∈ labelSupport m w :=
    sortNth_mem (mem_cutBlock.1 hct).1.1 (mem_cutBlock.1 hct).1.2
  rcases wordOfFin_mem_pair_of_mem_labelClass hw' hmemcS with h | h <;> rw [h] <;> simp

/-- **The indices of an initial stretch of a run at which a member of the class carries `m`**: a
count depending only on the stretch's length and the run's bit. -/
theorem card_filter_Icc_run (hw' : w' ∈ labelClass x σ m w) {t n : ℕ}
    (hne : (labelRun x m w t).Nonempty)
    (hsub : Icc (cutBlockMin #(labelSupport m w) (labelCutSet x m w) t)
      (cutBlockMin #(labelSupport m w) (labelCutSet x m w) t + n - 1) ⊆ labelRun x m w t) :
    #{c ∈ Icc (cutBlockMin #(labelSupport m w) (labelCutSet x m w) t)
        (cutBlockMin #(labelSupport m w) (labelCutSet x m w) t + n - 1) |
        wordOfFin w' (sortNth (labelSupport m w) c) = m} =
      if runBit x m w w' t then n / 2 else (n + 1) / 2 := by
  rw [Finset.filter_congr (fun c hc => wordOfFin_sortNth_eq_iff_parity hw' hne (hsub hc)),
    card_filter_Icc_sub _ n (one_le_cutBlockMin hne)
      (fun d => (d + (if runBit x m w w' t then 1 else 0)) % 2 = 0),
    card_filter_range_add_even]
  cases h : runBit x m w w' t <;> simp

/-- The same count for the letter `m + 1`. -/
theorem card_filter_Icc_run_succ (hw' : w' ∈ labelClass x σ m w) {t n : ℕ}
    (hne : (labelRun x m w t).Nonempty)
    (hsub : Icc (cutBlockMin #(labelSupport m w) (labelCutSet x m w) t)
      (cutBlockMin #(labelSupport m w) (labelCutSet x m w) t + n - 1) ⊆ labelRun x m w t) :
    #{c ∈ Icc (cutBlockMin #(labelSupport m w) (labelCutSet x m w) t)
        (cutBlockMin #(labelSupport m w) (labelCutSet x m w) t + n - 1) |
        wordOfFin w' (sortNth (labelSupport m w) c) = m + 1} =
      if runBit x m w w' t then (n + 1) / 2 else n / 2 := by
  rw [Finset.filter_congr (fun c hc => wordOfFin_sortNth_eq_succ_iff_parity hw' hne (hsub hc)),
    card_filter_Icc_sub _ n (one_le_cutBlockMin hne)
      (fun d => ¬((d + (if runBit x m w w' t then 1 else 0)) % 2 = 0)),
    card_filter_range_add_not_even]
  cases h : runBit x m w w' t <;> simp


/-! ### The monomial of a member of the class -/

/-- The product over the positions of the two-letter support, reindexed by the increasing
listing `s_1 < ⋯ < s_p`. -/
theorem prod_labelSupport_eq_prod_Icc {M : Type*} [CommMonoid M] (f : ℕ → M) (v : Fin N → ℕ) :
    ∏ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) ∈ labelSupport m w), f (v i) =
      ∏ c ∈ Icc 1 #(labelSupport m w), f (wordOfFin v (sortNth (labelSupport m w) c)) := by
  refine Finset.prod_bij (fun i _ => sortIdx (labelSupport m w) (i : ℕ)) ?_ ?_ ?_ ?_
  · intro i hi
    exact mem_Icc.2 ⟨one_le_sortIdx _ _, sortIdx_le_card (mem_filter.1 hi).2⟩
  · intro i₁ h₁ i₂ h₂ heq
    have hc := congrArg (sortNth (labelSupport m w)) heq
    rw [sortNth_sortIdx (mem_filter.1 h₁).2, sortNth_sortIdx (mem_filter.1 h₂).2] at hc
    exact Fin.ext hc
  · intro c hc
    obtain ⟨hc1, hcp⟩ := mem_Icc.1 hc
    have hmem : sortNth (labelSupport m w) c ∈ labelSupport m w := sortNth_mem hc1 hcp
    have hlt : sortNth (labelSupport m w) c < N := mem_range.1 (labelSupport_subset_range w hmem)
    exact ⟨⟨sortNth (labelSupport m w) c, hlt⟩, mem_filter.2 ⟨mem_univ _, hmem⟩,
      sortIdx_sortNth hc1 hcp⟩
  · intro i hi
    rw [sortNth_sortIdx (mem_filter.1 hi).2, wordOfFin_val]

/-- The index range of the listing, broken into the runs. -/
theorem prod_Icc_eq_prod_runs {M : Type*} [CommMonoid M] (F : ℕ → M) :
    ∏ c ∈ Icc 1 #(labelSupport m w), F c =
      ∏ t ∈ Icc 1 (labelRunCount x m w), ∏ c ∈ labelRun x m w t, F c := by
  rw [← Finset.prod_fiberwise_of_maps_to
    (g := cutBlockIdx (labelCutSet x m w)) (t := Icc 1 (labelRunCount x m w))
    (fun c _ => mem_Icc.2 ⟨one_le_cutBlockIdx _ _, cutBlockIdx_le _ _⟩) F]
  refine Finset.prod_congr rfl fun t _ =>
    Finset.prod_congr (Finset.ext fun c => ⟨fun h => ?_, fun h => ?_⟩) fun _ _ => rfl
  · obtain ⟨hcIcc, hcidx⟩ := mem_filter.1 h
    obtain ⟨h1, h2⟩ := mem_Icc.1 hcIcc
    exact mem_cutBlock.2 ⟨⟨h1, h2⟩, hcidx⟩
  · obtain ⟨⟨h1, h2⟩, hidx⟩ := mem_cutBlock.1 h
    exact mem_filter.2 ⟨mem_Icc.2 ⟨h1, h2⟩, hidx⟩

variable {K : Type*} [CommRing K]

/-- **Along a run the monomial is a power of `z^{(k)}_m` times a power of `z^{(k)}_{m+1}`**, the two
exponents counting the indices of the run carrying each of the two letters. -/
theorem prod_run_zvar (hw' : w' ∈ labelClass x σ m w) (t : ℕ) :
    ∏ c ∈ labelRun x m w t, zvar K k (wordOfFin w' (sortNth (labelSupport m w) c)) =
      zvar K k m ^ #{c ∈ labelRun x m w t | wordOfFin w' (sortNth (labelSupport m w) c) = m} *
        zvar K k (m + 1) ^
          #{c ∈ labelRun x m w t | wordOfFin w' (sortNth (labelSupport m w) c) = m + 1} := by
  have hset : {c ∈ labelRun x m w t | ¬(wordOfFin w' (sortNth (labelSupport m w) c) = m)} =
      {c ∈ labelRun x m w t | wordOfFin w' (sortNth (labelSupport m w) c) = m + 1} := by
    refine Finset.filter_congr fun c hc => ?_
    have hmem : sortNth (labelSupport m w) c ∈ labelSupport m w :=
      sortNth_mem (mem_cutBlock.1 hc).1.1 (mem_cutBlock.1 hc).1.2
    rcases wordOfFin_mem_pair_of_mem_labelClass hw' hmem with h | h <;> rw [h] <;> simp
  rw [← Finset.prod_filter_mul_prod_filter_not (labelRun x m w t)
    (fun c => wordOfFin w' (sortNth (labelSupport m w) c) = m)
    (fun c => zvar K k (wordOfFin w' (sortNth (labelSupport m w) c)))]
  congr 1
  · rw [← Finset.prod_const]
    exact Finset.prod_congr rfl fun c hc => by rw [(mem_filter.1 hc).2]
  · rw [hset, ← Finset.prod_const]
    exact Finset.prod_congr rfl fun c hc => by rw [(mem_filter.1 hc).2]

/-- **The monomial of a member of the class factorises over the runs**: the positions off the
two-letter support contribute the factor `g` of the class sum, which no member moves, and the
positions on it are grouped run by run. -/
theorem zmon_eq_prod_runs (hw' : w' ∈ labelClass x σ m w) :
    zmon K k w' =
      (∏ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) ∉ labelSupport m w), zvar K k (w i)) *
        ∏ t ∈ Icc 1 (labelRunCount x m w),
          ∏ c ∈ labelRun x m w t, zvar K k (wordOfFin w' (sortNth (labelSupport m w) c)) := by
  rw [zmon, ← Finset.prod_filter_mul_prod_filter_not (univ : Finset (Fin N))
    (fun i : Fin N => (i : ℕ) ∈ labelSupport m w) (fun i => zvar K k (w' i)),
    prod_labelSupport_eq_prod_Icc (m := m) (w := w) (fun a => zvar K k a) w',
    prod_Icc_eq_prod_runs (x := x) (m := m) (w := w)
      (fun c => zvar K k (wordOfFin w' (sortNth (labelSupport m w) c))), mul_comm]
  congr 1
  exact Finset.prod_congr rfl fun i hi => by rw [hw'.2.2 i (mem_filter.1 hi).2]


/-! ### The weight of a member of the class, run by run -/

/-- **The contribution of one run to the weight of a member of the class is that run's weight**
`a_m(l_t, ε_t)`: the power of `q` counts the inversions internal to the run, and the two exponents
of the merged variables count the indices of the run carrying each of the two letters. -/
theorem pow_mul_prod_run_eq_runWeight (q : K) (hw' : w' ∈ labelClass x σ m w) {t : ℕ}
    (hne : (labelRun x m w t).Nonempty) :
    scalarSeries K k q ^ #{c ∈ Icc (cutBlockMin #(labelSupport m w) (labelCutSet x m w) t)
        (cutBlockMin #(labelSupport m w) (labelCutSet x m w) t + #(labelRun x m w t) - 2) |
        wordOfFin w' (sortNth (labelSupport m w) c) = m + 1} *
      (∏ c ∈ labelRun x m w t, zvar K k (wordOfFin w' (sortNth (labelSupport m w) c)))
    = runWeightZvar q k m (#(labelRun x m w t)) (runBit x m w w' t) := by
  obtain ⟨l, hl⟩ : ∃ l, #(labelRun x m w t) = l := ⟨_, rfl⟩
  have hl1 : 1 ≤ l := hl ▸ one_le_card_cutBlock hne
  have hIcc : labelRun x m w t =
      Icc (cutBlockMin #(labelSupport m w) (labelCutSet x m w) t)
        (cutBlockMin #(labelSupport m w) (labelCutSet x m w) t + l - 1) := by
    rw [← hl]; exact cutBlock_eq_Icc hne
  have hsub1 : Icc (cutBlockMin #(labelSupport m w) (labelCutSet x m w) t)
      (cutBlockMin #(labelSupport m w) (labelCutSet x m w) t + l - 1) ⊆ labelRun x m w t := by
    rw [hIcc]
  have hsub2 : Icc (cutBlockMin #(labelSupport m w) (labelCutSet x m w) t)
      (cutBlockMin #(labelSupport m w) (labelCutSet x m w) t + (l - 1) - 1) ⊆
        labelRun x m w t := by
    rw [hIcc]
    exact fun c hc => mem_Icc.2 ⟨(mem_Icc.1 hc).1, by have := (mem_Icc.1 hc).2; omega⟩
  have hA := card_filter_Icc_run hw' hne hsub1
  have hB := card_filter_Icc_run_succ hw' hne hsub1
  have hn := card_filter_Icc_run_succ hw' hne hsub2
  rw [← hIcc] at hA hB
  rw [prod_run_zvar hw' t, hl, hA, hB,
    show cutBlockMin #(labelSupport m w) (labelCutSet x m w) t + l - 2
      = cutBlockMin #(labelSupport m w) (labelCutSet x m w) t + (l - 1) - 1 from by omega, hn]
  cases hb : runBit x m w w' t
  · simp only [Bool.false_eq_true, ite_false, runWeightZvar, runWeight]
    ring
  · simp only [ite_true, runWeightZvar, runWeight, show l - 1 + 1 = l from by omega]
    ring


/-- **The weight of a member of the class**: `q^e` and the monomial `g` of the positions off the
two-letter support, which no member moves, times the product of the runs' weights. -/
theorem weight_eq_prod_runWeight (q : K) (hx : IsPartialDyck k N x)
    (hw : w ∈ noAttackLabellings x σ) {j₀ : Fin k} (hj₀ : σ j₀ = m ∨ σ j₀ = m + 1)
    (hw' : w' ∈ labelClass x σ m w) :
    scalarSeries K k q ^ invNumber (attackSet x) (wordOfFin w') * zmon K k w' =
      scalarSeries K k q ^ #{p ∈ invSet (attackSet x) (wordOfFin w) |
            ¬(p.1 ∈ labelSupport m w ∧ p.2 ∈ labelSupport m w)} *
          (∏ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) ∉ labelSupport m w),
            zvar K k (w i)) *
          ∏ t ∈ Icc 1 (labelRunCount x m w),
            runWeightZvar q k m (#(labelRun x m w t)) (runBit x m w w' t) := by
  have hp : 1 ≤ #(labelSupport m w) := one_le_card_labelSupport hx hw hj₀
  have hCsub : labelCutSet x m w ⊆ Ico 1 #(labelSupport m w) := cutSet_subset_Ico _ _
  have hprod : (∏ t ∈ Icc 1 (labelRunCount x m w),
        scalarSeries K k q ^ #{c ∈ Icc (cutBlockMin #(labelSupport m w) (labelCutSet x m w) t)
          (cutBlockMin #(labelSupport m w) (labelCutSet x m w) t + #(labelRun x m w t) - 2) |
          wordOfFin w' (sortNth (labelSupport m w) c) = m + 1}) *
      (∏ t ∈ Icc 1 (labelRunCount x m w),
        ∏ c ∈ labelRun x m w t, zvar K k (wordOfFin w' (sortNth (labelSupport m w) c)))
      = ∏ t ∈ Icc 1 (labelRunCount x m w),
        runWeightZvar q k m (#(labelRun x m w t)) (runBit x m w w' t) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun t ht => pow_mul_prod_run_eq_runWeight q hw'
      (cutBlock_nonempty hp hCsub (mem_Icc.1 ht).1 (mem_Icc.1 ht).2)
  rw [invNumber_eq_of_mem_labelClass hx hw hj₀ hw', pow_add, zmon_eq_prod_runs hw',
    ← Finset.prod_pow_eq_pow_sum, ← hprod]
  ring

/-! ### The class sum -/

/-- **The class sum factorises over the runs.** Summing `q^{inv} z^{(k)}_{w'}` over the class
`K_m(π, σ, w)` gives `q^e g` times the weight of the first run at its forced bit times, for each
later run, the sum of that run's two weights. The class is the cube of `HJO.Dyck.bijOn_runBit`, the
weight of a member is the product of the runs' weights by `HJO.Dyck.invNumber_eq_of_mem_labelClass`,
and summing a product over a cube factorises it — `Finset.prod_univ_sum`. -/
@[hjo "lem_cm_class_sum"]
theorem finsum_labelClass (q : K) (hx : IsPartialDyck k N x)
    (hw : w ∈ noAttackLabellings x σ) {j₀ : Fin k} (hj₀ : σ j₀ = m ∨ σ j₀ = m + 1) :
    ∑ᶠ w' ∈ labelClass x σ m w,
        scalarSeries K k q ^ invNumber (attackSet x) (wordOfFin w') * zmon K k w'
      = scalarSeries K k q ^ #{p ∈ invSet (attackSet x) (wordOfFin w) |
            ¬(p.1 ∈ labelSupport m w ∧ p.2 ∈ labelSupport m w)} *
          (∏ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) ∉ labelSupport m w),
            zvar K k (w i)) *
          (runWeightZvar q k m (#(labelRun x m w 1))
              (decide (wordOfFin w (sortNth (labelSupport m w) 1) = m + 1)) *
            ∏ t ∈ Icc 2 (labelRunCount x m w),
              (runWeightZvar q k m (#(labelRun x m w t)) false +
                runWeightZvar q k m (#(labelRun x m w t)) true)) := by
  classical
  rw [prod_Icc_two_eq_prod_erase_zero x m w
    (fun t => runWeightZvar q k m (#(labelRun x m w t)) false +
      runWeightZvar q k m (#(labelRun x m w t)) true)]
  have hbij := bijOn_runBit hx hw hj₀
  have hfin : (labelClass x σ m w).Finite := by
    refine Set.Finite.of_finite_image ?_ hbij.injOn
    rw [hbij.image_eq]
    exact Set.toFinite _
  -- the sum over the class is the sum over the forced face of the cube
  have hstep : ∑ w' ∈ hfin.toFinset,
        (scalarSeries K k q ^ invNumber (attackSet x) (wordOfFin w') * zmon K k w')
      = ∑ ε ∈ {ε ∈ (Finset.univ : Finset (Fin (labelRunCount x m w) → Bool)) |
          ε 0 = decide (wordOfFin w (sortNth (labelSupport m w) 1) = m + 1)},
        (scalarSeries K k q ^ #{p ∈ invSet (attackSet x) (wordOfFin w) |
              ¬(p.1 ∈ labelSupport m w ∧ p.2 ∈ labelSupport m w)} *
            (∏ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) ∉ labelSupport m w),
              zvar K k (w i)) *
            ∏ j : Fin (labelRunCount x m w),
              runWeightZvar q k m (#(labelRun x m w ((j : ℕ) + 1))) (ε j)) := by
    refine Finset.sum_bij
      (fun w' _ (j : Fin (labelRunCount x m w)) => runBit x m w w' ((j : ℕ) + 1)) ?_ ?_ ?_ ?_
    · intro v hv
      exact mem_filter.2 ⟨mem_univ _, hbij.mapsTo (hfin.mem_toFinset.1 hv)⟩
    · intro v₁ h₁ v₂ h₂ heq
      exact hbij.injOn (hfin.mem_toFinset.1 h₁) (hfin.mem_toFinset.1 h₂) heq
    · intro ε hε
      obtain ⟨v, hv, hveq⟩ := hbij.surjOn (mem_filter.1 hε).2
      exact ⟨v, hfin.mem_toFinset.2 hv, hveq⟩
    · intro v hv
      rw [weight_eq_prod_runWeight q hx hw hj₀ (hfin.mem_toFinset.1 hv),
        prod_Icc_one_eq_prod_fin (labelRunCount x m w)
          (fun t => runWeightZvar q k m (#(labelRun x m w t)) (runBit x m w v t))]
  -- the face is a product of one-element and full factors, and the sum over it factorises
  have hpi : {ε ∈ (Finset.univ : Finset (Fin (labelRunCount x m w) → Bool)) |
        ε 0 = decide (wordOfFin w (sortNth (labelSupport m w) 1) = m + 1)}
      = Fintype.piFinset (fun j : Fin (labelRunCount x m w) =>
          if j = 0 then {decide (wordOfFin w (sortNth (labelSupport m w) 1) = m + 1)}
          else Finset.univ) := by
    refine Finset.ext fun ε => ?_
    rw [mem_filter, Fintype.mem_piFinset]
    refine ⟨fun h j => ?_, fun h => ⟨mem_univ _, ?_⟩⟩
    · by_cases hj : j = 0
      · subst hj
        simpa using h.2
      · simp [hj]
    · simpa using h 0
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, hstep, hpi, ← Finset.mul_sum,
    ← Finset.prod_univ_sum]
  congr 1
  rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin (labelRunCount x m w))) _ (mem_univ 0)]
  congr 1
  · rw [show (if (0 : Fin (labelRunCount x m w)) = 0 then
        ({decide (wordOfFin w (sortNth (labelSupport m w) 1) = m + 1)} : Finset Bool)
      else Finset.univ) = {decide (wordOfFin w (sortNth (labelSupport m w) 1) = m + 1)}
      from by simp, Finset.sum_singleton, Fin.val_zero]
  · refine Finset.prod_congr rfl fun j hj => ?_
    have hj0 : j ≠ 0 := Finset.ne_of_mem_erase hj
    rw [show (if j = 0 then ({decide (wordOfFin w (sortNth (labelSupport m w) 1) = m + 1)} :
        Finset Bool) else Finset.univ) = Finset.univ from by simp [hj0], Fintype.sum_bool]
    ring
end HJO.Dyck
