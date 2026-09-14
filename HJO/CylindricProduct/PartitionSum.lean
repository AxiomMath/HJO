/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CylindricProduct.Commutation
public import HJO.CylindricProduct.Exponents
public meta import HJO.Attr

/-! # Euler's identity for the partition generating function

The trace of a grading kernel against raising kernels collapses to `∑_λ q^{d|λ|}`, and this file
supplies the classical evaluation of that sum:

`(q^d; q^d)_∞ ∑_λ q^{d|λ|} = 1`,

which is Euler's identity `∑_λ q^{|λ|} = ∏_{k ≥ 1}(1 - q^k)^{-1}` at `q^d`, written without an
inverse.

The proof is the elementary induction on the number of rows rather than a reduction to Mathlib's
multiset partitions, which would need a bridge between the antitone sequences used here and the
multisets used there, and a substitution `q ↦ q^d` on top of it.

Write `rowGF d N` for the sum restricted to the partitions with at most `N` rows. Removing the
`N`-th row from such a partition, that is subtracting `λ_N` from every part, is a bijection

`{λ : at most N + 1 rows} ≃ ℕ × {μ : at most N rows}`,  `λ ↦ (λ_N, λ - λ_N)`,

which multiplies the weight by `q^{d(N+1)λ_N}`; summing the geometric series in `q^{d(N+1)}` gives
`(1 - q^{d(N+1)}) rowGF d (N+1) = rowGF d N`, and hence
`(∏_{j < N}(1 - q^{d(j+1)})) rowGF d N = 1` by induction, the base case being that the only
partition with no rows is the empty one.

Two truncation estimates then pass to the limit. A partition with more than `N` rows has size more
than `N`, so `rowGF d N` agrees with the full sum modulo `q^{d(N+1)}`; and `(q^d; q^d)_∞` splits as
its own `N`-th partial product times a tail congruent to `1` modulo `q^{d(N+1)}`. So the product of
`(q^d; q^d)_∞` with the full sum is congruent to `1` modulo `q^{d(N+1)}` for every `N`, and
therefore equal to it.
-/

@[expose] public section

open Finset Filter PowerSeries
open scoped QTheory Topology PowerSeries.DiscreteTopology

namespace HJO.CylindricProduct

/-! ### Partitions with a bounded number of rows -/

/-- `λ` has **at most `N` rows**: its parts vanish from index `N` on. -/
def RowBdd (N : ℕ) (l : Part) : Prop := ∀ i, N ≤ i → l.parts i = 0

/-- The size of a partition with at most `N` rows is the total of its first `N` parts. -/
theorem RowBdd.size_eq {N : ℕ} {l : Part} (h : RowBdd N l) :
    l.size = ∑ i ∈ range N, l.parts i :=
  Part.size_eq_sum_range l h

/-- A partition with more than `N` rows has size more than `N`: its first `N + 1` parts are all
positive. -/
theorem lt_size_of_not_rowBdd {N : ℕ} {l : Part} (h : ¬ RowBdd N l) : N < l.size := by
  simp only [RowBdd, not_forall] at h
  obtain ⟨i, hi, hne⟩ := h
  have hpos : ∀ j ∈ range (N + 1), 1 ≤ l.parts j := fun j hj =>
    le_trans (Nat.one_le_iff_ne_zero.mpr hne) (l.antitone (by simp only [mem_range] at hj; omega))
  obtain ⟨B, hB⟩ := l.vanish
  have hle : ∑ j ∈ range (N + 1), l.parts j ≤ l.size := by
    rw [Part.size_eq_sum_range l (B := max B (N + 1))
      fun j hj => hB j (le_trans (le_max_left _ _) hj)]
    exact Finset.sum_le_sum_of_subset fun x hx => by simp only [mem_range] at hx ⊢; omega
  have hcard : (N + 1) * 1 ≤ ∑ j ∈ range (N + 1), l.parts j := by
    simpa using Finset.card_nsmul_le_sum (range (N + 1)) l.parts 1 hpos
  omega

/-- **Removing the `N`-th row**: subtract `λ_N` from every part. -/
noncomputable def rowTrim (N : ℕ) (l : Part) : Part where
  parts := fun i => l.parts i - l.parts N
  antitone' := fun _ _ hij => Nat.sub_le_sub_right (l.antitone hij) _
  vanish' := ⟨N, fun i hi => by have := l.antitone hi; omega⟩

@[simp] theorem rowTrim_parts (N : ℕ) (l : Part) (i : ℕ) :
    (rowTrim N l).parts i = l.parts i - l.parts N := rfl

theorem rowBdd_rowTrim (N : ℕ) (l : Part) : RowBdd N (rowTrim N l) :=
  fun i hi => by have := l.antitone hi; simp only [rowTrim_parts]; omega

/-- **Restoring the `N`-th row**: add `k` to each of the first `N + 1` parts. -/
noncomputable def rowGrow (N k : ℕ) (l : Part) : Part where
  parts := fun i => if i < N + 1 then l.parts i + k else 0
  antitone' := antitone_nat_of_succ_le fun i => by
    by_cases h1 : i + 1 < N + 1
    · rw [ite_eq_left h1, ite_eq_left (by omega : i < N + 1)]
      exact Nat.add_le_add_right (l.antitone (Nat.le_succ i)) k
    · rw [ite_eq_right h1]
      exact Nat.zero_le _
  vanish' := ⟨N + 1, fun _ hi => ite_eq_right (by omega)⟩

theorem rowGrow_parts_of_le {N k : ℕ} {l : Part} {i : ℕ} (hi : i ≤ N) :
    (rowGrow N k l).parts i = l.parts i + k := ite_eq_left (by omega)

theorem rowGrow_parts_of_lt {N k : ℕ} {l : Part} {i : ℕ} (hi : N < i) :
    (rowGrow N k l).parts i = 0 := ite_eq_right (by omega)

theorem rowBdd_rowGrow (N k : ℕ) (l : Part) : RowBdd (N + 1) (rowGrow N k l) :=
  fun _ hi => rowGrow_parts_of_lt (by omega)

/-- Restoring a row adds `(N + 1) k` to the size. -/
theorem size_rowGrow {N k : ℕ} {l : Part} (h : RowBdd N l) :
    (rowGrow N k l).size = l.size + (N + 1) * k := by
  rw [(rowBdd_rowGrow N k l).size_eq, h.size_eq,
    Finset.sum_congr rfl fun i hi =>
      rowGrow_parts_of_le (by simp only [mem_range] at hi; omega : i ≤ N),
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    Finset.sum_range_succ, h N le_rfl, Nat.add_zero]
  ring

/-- The forward half of `rowEquiv`: read off the `N`-th part and subtract it from every part. -/
noncomputable def rowSplit (N : ℕ) (l : {l : Part // RowBdd (N + 1) l}) :
    ℕ × {l : Part // RowBdd N l} :=
  (l.1.parts N, ⟨rowTrim N l.1, rowBdd_rowTrim N l.1⟩)

/-- The backward half of `rowEquiv`: add `k` to each of the first `N + 1` parts. -/
noncomputable def rowJoin (N : ℕ) (p : ℕ × {l : Part // RowBdd N l}) :
    {l : Part // RowBdd (N + 1) l} :=
  ⟨rowGrow N p.1 p.2.1, rowBdd_rowGrow N p.1 p.2.1⟩

theorem rowJoin_rowSplit (N : ℕ) (l : {l : Part // RowBdd (N + 1) l}) :
    rowJoin N (rowSplit N l) = l := by
  refine Subtype.ext (Part.ext (funext fun i => ?_))
  by_cases hi : i ≤ N
  · have := l.1.antitone hi
    rw [show (rowJoin N (rowSplit N l)).1 = rowGrow N (l.1.parts N) (rowTrim N l.1) from rfl,
      rowGrow_parts_of_le hi, rowTrim_parts]
    omega
  · rw [show (rowJoin N (rowSplit N l)).1 = rowGrow N (l.1.parts N) (rowTrim N l.1) from rfl,
      rowGrow_parts_of_lt (by omega), l.2 i (by omega)]

theorem rowSplit_rowJoin (N : ℕ) (p : ℕ × {l : Part // RowBdd N l}) :
    rowSplit N (rowJoin N p) = p := by
  have hN : (rowGrow N p.1 p.2.1).parts N = p.1 := by
    rw [rowGrow_parts_of_le le_rfl, p.2.2 N le_rfl, Nat.zero_add]
  refine Prod.ext hN (Subtype.ext (Part.ext (funext fun i => ?_)))
  rw [show (rowSplit N (rowJoin N p)).2.1 = rowTrim N (rowGrow N p.1 p.2.1) from rfl,
    rowTrim_parts, hN]
  by_cases hi : i ≤ N
  · rw [rowGrow_parts_of_le hi, Nat.add_sub_cancel]
  · rw [rowGrow_parts_of_lt (by omega), p.2.2 i (by omega), Nat.zero_sub]

/-- **The rows split off one at a time.** A partition with at most `N + 1` rows is exactly its
`N`-th part together with the partition of at most `N` rows left after that part is subtracted from
all the others. -/
noncomputable def rowEquiv (N : ℕ) :
    {l : Part // RowBdd (N + 1) l} ≃ ℕ × {l : Part // RowBdd N l} where
  toFun := rowSplit N
  invFun := rowJoin N
  left_inv := rowJoin_rowSplit N
  right_inv := rowSplit_rowJoin N

/-! ### The generating function of the partitions with at most `N` rows -/

/-- `∑_{λ : at most N rows} q^{d|λ|}`, the partition generating function truncated to `N` rows. -/
noncomputable def rowGF (d N : ℕ) : ℤ⟦X⟧ := ∑' l : {l : Part // RowBdd N l}, X ^ (d * l.1.size)

/-- The only partition with no rows is the empty one. -/
theorem rowGF_zero (d : ℕ) : rowGF d 0 = 1 := by
  refine (tsum_eq_single ⟨Part.zero, fun _ _ => rfl⟩ fun l hl => ?_).trans ?_
  · exact absurd (Subtype.ext (Part.eq_zero_of_parts_eq_zero fun i => l.2 i (Nat.zero_le i))) hl
  · simp

/-- Only finitely many partitions with at most `N` rows reach a given degree. -/
theorem finite_rowBdd {d : ℕ} (hd : 0 < d) (N n : ℕ) :
    {l : {l : Part // RowBdd N l} | d * l.1.size ≤ n}.Finite := by
  refine Set.Finite.of_finite_image ?_ (Subtype.val_injective (p := RowBdd N)).injOn
  refine (finite_size_le n).subset ?_
  rintro l ⟨l', hl', rfl⟩
  simp only [Set.mem_ofPred_eq] at hl' ⊢
  have : l'.1.size ≤ d * l'.1.size := Nat.le_mul_of_pos_left _ hd
  omega

/-- The family summed over the partitions of at most `N` rows is summable. -/
theorem summable_rowBdd {d : ℕ} (hd : 0 < d) (N : ℕ) :
    Summable fun l : {l : Part // RowBdd N l} => (X : ℤ⟦X⟧) ^ (d * l.1.size) :=
  summable_of_dvd_of_finite (g := fun l : {l : Part // RowBdd N l} => d * l.1.size)
    (fun _ => dvd_rfl) (finite_rowBdd hd N)

/-- Only finitely many pairs of a multiplicity and a partition of at most `N` rows reach a given
degree. -/
theorem finite_rowPair {d : ℕ} (hd : 0 < d) (N n : ℕ) :
    {p : ℕ × {l : Part // RowBdd N l} | d * (p.2.1.size + (N + 1) * p.1) ≤ n}.Finite := by
  have hinj : Function.Injective fun p : ℕ × {l : Part // RowBdd N l} => (p.1, p.2.1) := by
    rintro ⟨k, l⟩ ⟨k', l'⟩ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1 (Subtype.ext h.2)
  refine Set.Finite.of_finite_image ?_ hinj.injOn
  refine ((Set.finite_Iic n).prod (finite_size_le n)).subset ?_
  rintro q ⟨p, hp, rfl⟩
  simp only [Set.mem_ofPred_eq] at hp
  have hA : p.2.1.size + (N + 1) * p.1 ≤ d * (p.2.1.size + (N + 1) * p.1) :=
    Nat.le_mul_of_pos_left _ hd
  have hB : p.1 ≤ (N + 1) * p.1 := Nat.le_mul_of_pos_left _ (Nat.succ_pos N)
  refine Set.mk_mem_prod (Set.mem_Iic.mpr (by omega)) ?_
  simp only [Set.mem_ofPred_eq]
  omega

/-- The family summed over a multiplicity and a partition of at most `N` rows is summable. -/
theorem summable_rowPair {d : ℕ} (hd : 0 < d) (N : ℕ) :
    Summable fun p : ℕ × {l : Part // RowBdd N l} =>
      ((X : ℤ⟦X⟧) ^ (d * (N + 1))) ^ p.1 * X ^ (d * p.2.1.size) :=
  summable_of_dvd_of_finite (g := fun p => d * (p.2.1.size + (N + 1) * p.1))
    (fun p => by rw [← pow_mul, ← pow_add]; exact pow_dvd_pow _ (by ring_nf; omega))
    (finite_rowPair hd N)

/-- **One row at a time.** Splitting off the `N`-th row multiplies the truncated generating
function by the geometric series in `q^{d(N+1)}`, which `1 - q^{d(N+1)}` inverts. -/
theorem oneSub_mul_rowGF_succ {d : ℕ} (hd : 0 < d) (N : ℕ) :
    (1 - X ^ (d * (N + 1)) : ℤ⟦X⟧) * rowGF d (N + 1) = rowGF d N := by
  have hcc : constantCoeff ((X : ℤ⟦X⟧) ^ (d * (N + 1))) = 0 := by
    rw [map_pow, constantCoeff_X]
    exact zero_pow (by positivity)
  have key : rowGF d (N + 1) = (∑' k : ℕ, ((X : ℤ⟦X⟧) ^ (d * (N + 1))) ^ k) * rowGF d N := by
    calc rowGF d (N + 1)
        = ∑' p : ℕ × {l : Part // RowBdd N l}, (X : ℤ⟦X⟧) ^ (d * (rowJoin N p).1.size) :=
          ((rowEquiv N).symm.tsum_eq
            fun l : {l : Part // RowBdd (N + 1) l} => (X : ℤ⟦X⟧) ^ (d * l.1.size)).symm
      _ = ∑' p : ℕ × {l : Part // RowBdd N l},
            ((X : ℤ⟦X⟧) ^ (d * (N + 1))) ^ p.1 * X ^ (d * p.2.1.size) :=
          tsum_congr fun p => by
            rw [show (rowJoin N p).1 = rowGrow N p.1 p.2.1 from rfl, size_rowGrow p.2.2,
              ← pow_mul, ← pow_add]
            congr 1
            ring
      _ = ∑' k : ℕ, ∑' l : {l : Part // RowBdd N l},
            ((X : ℤ⟦X⟧) ^ (d * (N + 1))) ^ k * X ^ (d * l.1.size) :=
          (summable_rowPair hd N).tsum_prod
      _ = ∑' k : ℕ, ((X : ℤ⟦X⟧) ^ (d * (N + 1))) ^ k * rowGF d N :=
          tsum_congr fun k => (summable_rowBdd hd N).tsum_mul_left _
      _ = (∑' k : ℕ, ((X : ℤ⟦X⟧) ^ (d * (N + 1))) ^ k) * rowGF d N :=
          (summable_pow_of_constantCoeff_eq_zero hcc).tsum_mul_right _
  rw [key, ← mul_assoc, one_sub_mul_tsum_pow hcc, one_mul]

/-- **The truncated identity.** The partial product of the `1 - q^{dk}` inverts the generating
function of the partitions with at most `N` rows. -/
theorem prod_mul_rowGF {d : ℕ} (hd : 0 < d) (N : ℕ) :
    (∏ j ∈ range N, (1 - X ^ (d * (j + 1)) : ℤ⟦X⟧)) * rowGF d N = 1 := by
  induction N with
  | zero => simp [rowGF_zero]
  | succ N ih =>
    rw [Finset.prod_range_succ, mul_assoc, oneSub_mul_rowGF_succ hd N, ih]

/-! ### The full partition sum -/

/-- `∑_λ q^{d|λ|}`, the sum over all partitions. -/
noncomputable def partGF (d : ℕ) : ℤ⟦X⟧ := ∑' l : Part, X ^ (d * l.size)

theorem summable_partGF {d : ℕ} (hd : 0 < d) :
    Summable fun l : Part => (X : ℤ⟦X⟧) ^ (d * l.size) :=
  summable_of_dvd_of_finite (g := fun l : Part => d * l.size) (fun _ => dvd_rfl) fun n =>
    (finite_size_le n).subset fun l hl => by
      simp only [Set.mem_ofPred_eq] at hl ⊢
      have : l.size ≤ d * l.size := Nat.le_mul_of_pos_left _ hd
      omega

/-- **The truncation is harmless.** A partition with more than `N` rows has size more than `N`, so
the truncated generating function agrees with the full sum modulo `q^{d(N+1)}`. -/
theorem X_pow_dvd_partGF_sub_rowGF {d : ℕ} (hd : 0 < d) (N : ℕ) :
    (X : ℤ⟦X⟧) ^ (d * (N + 1)) ∣ partGF d - rowGF d N := by
  have hs := summable_partGF hd
  have hsplit := Summable.tsum_add_tsum_compl (f := fun l : Part => (X : ℤ⟦X⟧) ^ (d * l.size))
    (s := {l : Part | RowBdd N l}) (hs.subtype _) (hs.subtype _)
  have hrow : (∑' l : ↥{l : Part | RowBdd N l}, (X : ℤ⟦X⟧) ^ (d * l.1.size)) = rowGF d N := rfl
  rw [partGF, ← hsplit, hrow, add_sub_cancel_left]
  refine X_pow_dvd_tsum (hs.subtype _) fun l => pow_dvd_pow _ ?_
  have := lt_size_of_not_rowBdd (N := N) (l := l.1) l.2
  exact Nat.mul_le_mul_left d (by omega)

/-! ### The tail of the self-Pochhammer symbol -/

/-- **A Pochhammer symbol is trivial to its own order.** `(q^J; q^d)_∞` is congruent to `1` modulo
`q^J`, every one of its factors being. -/
theorem X_pow_dvd_qPochhammerInf_sub_one {J d : ℕ} (hJ : 0 < J) (hd : 0 < d) :
    (X : ℤ⟦X⟧) ^ J ∣ ((X ^ J; X ^ d)_∞ : ℤ⟦X⟧) - 1 := by
  rw [Limits.qPochhammerInf_eq_tprod_zpowOneSub hJ hd]
  refine PowerSeries.X_pow_dvd_iff.mpr fun j hj => ?_
  have htriv : ∀ m ∈ range j,
      Limits.zpowOneSub m (if J ≤ m + 1 ∧ d ∣ (m + 1) - J then (1 : ℤ) else 0) = 1 := by
    intro m hm
    rw [mem_range] at hm
    rw [ite_eq_right fun h => absurd h.1 (by omega), Limits.zpowOneSub_zero]
  rw [map_sub, coeff_tprod_zpowOneSub, Finset.prod_congr rfl htriv, Finset.prod_const_one,
    sub_self]

/-- The `N`-th partial product of `(q^d; q^d)_∞`, written with the exponents `d(j+1)`. -/
theorem selfQPochhammer_pow_eq_prod (d N : ℕ) :
    ((X ^ d; X ^ d)_N : ℤ⟦X⟧) = ∏ j ∈ range N, (1 - X ^ (d * (j + 1)) : ℤ⟦X⟧) := by
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← pow_mul, ← pow_add]
  congr 2
  ring

/-- **The self-Pochhammer symbol agrees with its partial product to the order of its tail.** -/
theorem X_pow_dvd_selfQPochhammerInf_sub_prod {d : ℕ} (hd : 0 < d) (N : ℕ) :
    (X : ℤ⟦X⟧) ^ (d * (N + 1)) ∣
      ((X ^ d; X ^ d)_∞ : ℤ⟦X⟧) - ∏ j ∈ range N, (1 - X ^ (d * (j + 1)) : ℤ⟦X⟧) := by
  have hnil : IsTopologicallyNilpotent ((X : ℤ⟦X⟧) ^ d) :=
    (PowerSeries.DiscreteTopology.isTopologicallyNilpotent_X_pow d).mpr (by omega)
  have harg : (X : ℤ⟦X⟧) ^ d * ((X : ℤ⟦X⟧) ^ d) ^ N = X ^ (d * (N + 1)) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    ring
  obtain ⟨c, hc⟩ := X_pow_dvd_qPochhammerInf_sub_one (J := d * (N + 1)) (by positivity) hd
  have hkey : ((X ^ (d * (N + 1)); X ^ d)_∞ : ℤ⟦X⟧) = 1 + X ^ (d * (N + 1)) * c := by
    rw [← hc]; ring
  rw [qPochhammerInf_eq_qPochhammer_mul_qPochhammerInf (a := (X : ℤ⟦X⟧) ^ d)
    (q := (X : ℤ⟦X⟧) ^ d) N hnil, harg, selfQPochhammer_pow_eq_prod, hkey]
  exact ⟨(∏ j ∈ range N, (1 - X ^ (d * (j + 1)) : ℤ⟦X⟧)) * c, by ring⟩

/-! ### Euler's identity -/

/-- **Euler's identity at `q^d`.** `(q^d; q^d)_∞ ∑_λ q^{d|λ|} = 1`: the sum over all partitions of
`q^d` raised to the size is the reciprocal of the self-Pochhammer symbol. -/
theorem selfQPochhammerInf_mul_partGF {d : ℕ} (hd : 0 < d) :
    ((X ^ d; X ^ d)_∞ : ℤ⟦X⟧) * partGF d = 1 := by
  have hdvd : ∀ n : ℕ, (X : ℤ⟦X⟧) ^ (n + 1) ∣ ((X ^ d; X ^ d)_∞ : ℤ⟦X⟧) * partGF d - 1 := by
    intro n
    refine dvd_trans (pow_dvd_pow _ (Nat.le_mul_of_pos_left (n + 1) hd)) ?_
    obtain ⟨c1, hc1⟩ := X_pow_dvd_selfQPochhammerInf_sub_prod hd n
    obtain ⟨c2, hc2⟩ := X_pow_dvd_partGF_sub_rowGF hd n
    set A := ∏ j ∈ range n, (1 - X ^ (d * (j + 1)) : ℤ⟦X⟧) with hA
    have e1 : ((X ^ d; X ^ d)_∞ : ℤ⟦X⟧) = A + X ^ (d * (n + 1)) * c1 := by rw [← hc1]; ring
    have e2 : partGF d = rowGF d n + X ^ (d * (n + 1)) * c2 := by rw [← hc2]; ring
    have e3 : A * rowGF d n = 1 := prod_mul_rowGF hd n
    refine ⟨c1 * partGF d + A * c2, ?_⟩
    calc ((X ^ d; X ^ d)_∞ : ℤ⟦X⟧) * partGF d - 1
        = (A + X ^ (d * (n + 1)) * c1) * (rowGF d n + X ^ (d * (n + 1)) * c2) - 1 := by
          rw [← e1, ← e2]
      _ = (A * rowGF d n - 1)
            + X ^ (d * (n + 1)) * (c1 * (rowGF d n + X ^ (d * (n + 1)) * c2) + A * c2) := by
          ring
      _ = X ^ (d * (n + 1)) * (c1 * partGF d + A * c2) := by
          rw [e3, sub_self, zero_add, ← e2]
  refine sub_eq_zero.mp (PowerSeries.ext fun n => ?_)
  simpa using PowerSeries.X_pow_dvd_iff.mp (hdvd n) n (by omega)

end HJO.CylindricProduct
