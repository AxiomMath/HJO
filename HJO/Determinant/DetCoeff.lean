/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import QSeriesLib.NumberTheory.QTheory.Defs
public import QSeriesLib.RingTheory.PowerSeries.DiscreteTopology
public import HJO.Defs
public import HJO.Determinant.Basic

/-! # Vertex-disjoint cycles, their occupied set and their staircase partitions

In the graph on `ℕ` whose edges are `v → v + b` (of weight `q^{⌊v/a⌋}`) and `v → v - a` (of
weight `1`), a finite collection of vertex-disjoint cycles is recorded by its set of occupied
vertices together with the successor map along the cycles. This file establishes the
combinatorial anatomy of such a collection.

* Each residue class modulo `d = a + b` carries the same number `N` of occupied vertices, so the
  occupied set has `dN` elements, and the successor map takes the `i`-th smallest occupied
  vertex of one class to the `i`-th smallest of the next: the collection is determined by its
  occupied set.
* Listing the levels `⌊v/d⌋` of the occupied vertices of one class in increasing order,
  subtracting the staircase `(0, 1, …, N-1)` and reversing produces a partition with at most `N`
  parts, hence a conjugate all of whose parts are at most `N`. Consecutive classes differ by a
  vertical strip in one direction or the other, according to whether the residues of the class
  are below `a`, so their conjugates differ by a horizontal strip.
* The weight `∑ ⌊v/a⌋` over the vertices leaving along an up-edge equals the sum `∑ ⌊v/d⌋` of
  the levels of all occupied vertices, hence the rank shift `γ_N = d\binom{N}{2}` plus the total
  size of the `d` staircase partitions. The proof is a telescoping of the potential
  `ψ(v) = ∑_{j ≤ v/a} ⌊(v - ja)/d⌋` around the cycles.

Conjugation of partitions is handled through the adjunction `conjPart l i ≤ j ↔ l j ≤ i`, which
is all that the strip statements need.

The rest of the file sets up the diagonal reading and proves it a weight-preserving bijection
onto the cylindric partitions of the balanced profile with entries at most `N`. The mediating
object is a *diagonal function*: a function `W` of a single position `w` with
`W (w + a) ≤ W w` and `W (w + b) ≤ W w`, bounded by `N` and eventually zero. Both sides of the
bijection are equivalent to such a function.

* The entry of row `i` and column `j` of an array sits at the diagonal position
  `ib mod a + aj`; the two graph edges become the two coordinate directions, so the outgoing
  inequality of a cylindric partition is the step by `b` and the row inequality the step by `a`.
  Since `i ↦ ib mod a` permutes the residues modulo `a`, this is a bijection between positions
  and entries, whence `cylOfDiag` and `diagOfCyl` are mutually inverse and the volume of the
  array is the total of the diagonal function.
* From a collection, the value at a position `w` is the `⌊w/d⌋`-th part of the conjugate of the
  staircase partition of the class of `w`. The two directions of the strip statements are exactly
  the two steps, so this is a diagonal function; summing it over the positions recovers the total
  size of the `d` staircase partitions, so the volume of the array is that total and the weight is
  `γ_N` plus the volume.
* Conversely a diagonal function is cut into its `d` diagonal slices, each conjugated and the
  staircase added back, which returns the levels of a collection. The comparison of consecutive
  slices forces every step of its successor map to be a graph edge, so it is a collection, and its
  diagonal reading is the function one started from.
-/

@[expose] public section

open Finset

namespace HJO.DetCoeff

/-! ### Partitions and conjugation -/

/-- A partition with at most `N` parts, written as a weakly decreasing sequence of naturals
vanishing from index `N` on. -/
structure IsPartitionUpTo (N : ℕ) (l : ℕ → ℕ) : Prop where
  /-- The parts weakly decrease. -/
  antitone : Antitone l
  /-- There are at most `N` parts. -/
  vanish : ∀ j, N ≤ j → l j = 0

/-- The conjugate of a partition: `conjPart l i` is the number of parts of `l` exceeding `i`,
computed as the least index at which `l` has dropped to `i` or below. -/
noncomputable def conjPart (l : ℕ → ℕ) (i : ℕ) : ℕ := sInf {j | l j ≤ i}

/-- The adjunction defining conjugation: `conjPart l i ≤ j` exactly when `l j ≤ i`. -/
lemma conjPart_le_iff {N : ℕ} {l : ℕ → ℕ} (hl : IsPartitionUpTo N l) (i j : ℕ) :
    conjPart l i ≤ j ↔ l j ≤ i := by
  refine ⟨fun h => ?_, fun h => Nat.sInf_le h⟩
  have hne : {j | l j ≤ i}.Nonempty := ⟨N, by simp [hl.vanish N le_rfl]⟩
  have hmem : l (conjPart l i) ≤ i := Nat.sInf_mem hne
  exact le_trans (hl.antitone h) hmem

/-- At the conjugate index the partition has already dropped to `i`. -/
lemma apply_conjPart_le {N : ℕ} {l : ℕ → ℕ} (hl : IsPartitionUpTo N l) (i : ℕ) :
    l (conjPart l i) ≤ i := (conjPart_le_iff hl i _).1 le_rfl

/-- Every part of the conjugate of a partition with at most `N` parts is at most `N`. -/
lemma conjPart_le {N : ℕ} {l : ℕ → ℕ} (hl : IsPartitionUpTo N l) (i : ℕ) : conjPart l i ≤ N :=
  (conjPart_le_iff hl i N).2 (by rw [hl.vanish N le_rfl]; exact Nat.zero_le i)

/-- The conjugate of a partition with at most `N` parts is a partition with at most `l 0` parts;
by `conjPart_le` all of its parts are at most `N`. -/
lemma isPartitionUpTo_conjPart {N : ℕ} {l : ℕ → ℕ} (hl : IsPartitionUpTo N l) :
    IsPartitionUpTo (l 0) (conjPart l) where
  antitone := fun _ i' hii => (conjPart_le_iff hl i' _).2 (le_trans (apply_conjPart_le hl _) hii)
  vanish := fun i hi => Nat.le_zero.1 ((conjPart_le_iff hl i 0).2 hi)

/-- Conjugation exchanges vertical and horizontal strips: from `m ≤ l ≤ m + 1` pointwise, the
conjugate of `m` is contained in that of `l` and the difference is a horizontal strip. -/
lemma conjPart_horizontal {N : ℕ} {l m : ℕ → ℕ} (hl : IsPartitionUpTo N l)
    (hm : IsPartitionUpTo N m) (h1 : ∀ j, m j ≤ l j) (h2 : ∀ j, l j ≤ m j + 1) (i : ℕ) :
    conjPart m i ≤ conjPart l i ∧ conjPart l (i + 1) ≤ conjPart m i := by
  refine ⟨(conjPart_le_iff hm i _).2 (le_trans (h1 _) (apply_conjPart_le hl i)), ?_⟩
  exact (conjPart_le_iff hl (i + 1) _).2
    (le_trans (h2 _) (Nat.succ_le_succ (apply_conjPart_le hm i)))

/-! ### The staircase subtraction -/

/-- A strictly monotone map out of `Fin N` grows at least as fast as the index. -/
lemma add_le_of_strictMono {N : ℕ} {f : Fin N → ℕ} (hf : StrictMono f) :
    ∀ (k : ℕ) (i j : Fin N), (j : ℕ) = (i : ℕ) + k → f i + k ≤ f j := by
  intro k
  induction k with
  | zero =>
    intro i j hij
    have hij' : i = j := Fin.val_injective (by omega)
    simp [hij']
  | succ k ih =>
    intro i j hij
    have hj := j.isLt
    have hlt : (j : ℕ) - 1 < N := by omega
    have h1 := ih i ⟨(j : ℕ) - 1, hlt⟩ (by change (j : ℕ) - 1 = (i : ℕ) + k; omega)
    have h2 : f ⟨(j : ℕ) - 1, hlt⟩ < f j := hf (by
      rw [Fin.lt_def]; change (j : ℕ) - 1 < (j : ℕ); omega)
    omega

/-- The staircase subtraction: from a strictly increasing sequence `f 0 < ⋯ < f (N-1)`,
`stair f` is the reversed sequence with the staircase `(0, 1, …, N-1)` removed. -/
def stair {N : ℕ} (f : Fin N → ℕ) (j : ℕ) : ℕ :=
  if h : j < N then f ⟨N - 1 - j, by omega⟩ - (N - 1 - j) else 0

/-- The parts of `stair f` in the relevant range. -/
lemma stair_of_lt {N : ℕ} (f : Fin N → ℕ) {j : ℕ} (h : j < N) (h' : N - 1 - j < N) :
    stair f j = f ⟨N - 1 - j, h'⟩ - (N - 1 - j) := dite_eq_left h

/-- `stair f` vanishes from index `N` on. -/
lemma stair_of_le {N : ℕ} (f : Fin N → ℕ) {j : ℕ} (h : N ≤ j) : stair f j = 0 :=
  dite_eq_right (by omega)

/-- The staircase subtraction of a strictly increasing sequence of length `N` is a partition
with at most `N` parts. -/
lemma isPartitionUpTo_stair {N : ℕ} {f : Fin N → ℕ} (hf : StrictMono f) :
    IsPartitionUpTo N (stair f) where
  antitone := by
    intro x y hxy
    by_cases hy : y < N
    · have hx : x < N := lt_of_le_of_lt hxy hy
      rw [stair_of_lt f hx (by omega), stair_of_lt f hy (by omega)]
      have key := add_le_of_strictMono hf ((N - 1 - x) - (N - 1 - y))
        ⟨N - 1 - y, by omega⟩ ⟨N - 1 - x, by omega⟩
        (by change N - 1 - x = (N - 1 - y) + ((N - 1 - x) - (N - 1 - y)); omega)
      omega
    · rw [stair_of_le f (by omega)]
      exact Nat.zero_le _
  vanish := fun _ hj => stair_of_le f hj

/-- Pointwise domination is inherited by the staircase subtraction. -/
lemma stair_le_stair {N : ℕ} {f g : Fin N → ℕ} (h : ∀ i, f i ≤ g i) (j : ℕ) :
    stair f j ≤ stair g j := by
  by_cases hj : j < N
  · rw [stair_of_lt f hj (by omega), stair_of_lt g hj (by omega)]
    have := h ⟨N - 1 - j, by omega⟩
    omega
  · rw [stair_of_le f (by omega), stair_of_le g (by omega)]

/-- A pointwise gap of one is inherited by the staircase subtraction. -/
lemma stair_le_stair_succ {N : ℕ} {f g : Fin N → ℕ} (h : ∀ i, g i ≤ f i + 1) (j : ℕ) :
    stair g j ≤ stair f j + 1 := by
  by_cases hj : j < N
  · rw [stair_of_lt f hj (by omega), stair_of_lt g hj (by omega)]
    have := h ⟨N - 1 - j, by omega⟩
    omega
  · rw [stair_of_le f (by omega), stair_of_le g (by omega)]
    exact Nat.zero_le _

/-- The size of the staircase subtraction: the sum of the sequence is the size of the partition
plus the size `C(N,2)` of the staircase. -/
lemma sum_stair_add_choose {N : ℕ} {f : Fin N → ℕ} (hf : StrictMono f) :
    (∑ j ∈ range N, stair f j) + N.choose 2 = ∑ i : Fin N, f i := by
  classical
  set g : ℕ → ℕ := fun u => if h : u < N then f ⟨u, h⟩ else 0 with hg
  have hle : ∀ u, u < N → u ≤ g u := by
    intro u hu
    have h0 : 0 < N := by omega
    have := add_le_of_strictMono hf u ⟨0, h0⟩ ⟨u, hu⟩ (by change u = 0 + u; omega)
    simp only [hg, dite_eq_left hu]
    omega
  have hstair : ∀ j ∈ range N, stair f j = g (N - 1 - j) - (N - 1 - j) := by
    intro j hj
    rw [mem_range] at hj
    rw [stair_of_lt f hj (by omega)]
    simp only [hg, dite_eq_left (show N - 1 - j < N by omega)]
  calc (∑ j ∈ range N, stair f j) + N.choose 2
      = (∑ j ∈ range N, (fun u => g u - u) (N - 1 - j)) + N.choose 2 := by
        rw [sum_congr rfl hstair]
    _ = (∑ u ∈ range N, (g u - u)) + ∑ u ∈ range N, u := by
        rw [sum_range_reflect (fun u => g u - u) N, Nat.choose_two_right, sum_range_id]
    _ = ∑ u ∈ range N, g u := by
        rw [← sum_add_distrib]
        exact sum_congr rfl fun u hu => Nat.sub_add_cancel (hle u (mem_range.1 hu))
    _ = ∑ i : Fin N, f i := by
        rw [← Fin.sum_univ_eq_sum_range g N]
        exact sum_congr rfl fun i _ => by simp only [hg, dite_eq_left i.isLt]

/-! ### The weight potential -/

/-- The potential `ψ(v) = ∑_{j ≤ v/a} ⌊(v - ja)/d⌋`, with `d = a + b`. -/
def potential (a b v : ℕ) : ℕ := ∑ j ∈ range (v / a + 1), (v - a * j) / (a + b)

/-- Stepping down by `a` lowers the potential by one level. -/
lemma potential_add_left {a b : ℕ} (ha : 0 < a) (v : ℕ) :
    potential a b (v + a) = potential a b v + (v + a) / (a + b) := by
  have hdiv : (v + a) / a = v / a + 1 := Nat.add_div_right v ha
  simp only [potential, hdiv]
  rw [sum_range_succ' (fun j => (v + a - a * j) / (a + b)) (v / a + 1)]
  congr 1
  refine sum_congr rfl fun k _ => ?_
  have h1 : a * (k + 1) = a * k + a := by ring
  congr 1
  omega

/-- Stepping up by `b` raises the potential by the gap between the two floor functions. -/
lemma potential_add_right {a b : ℕ} (ha : 0 < a) (v : ℕ) :
    potential a b (v + b) + v / (a + b) = potential a b v + v / a := by
  have hd : 0 < a + b := by omega
  have hmod := Nat.div_add_mod v a
  have hmodlt : v % a < a := Nat.mod_lt _ ha
  set K := v / a with hK
  have hKM : K ≤ (v + b) / a + 1 := by
    have h0 : v / a ≤ (v + b) / a := Nat.div_le_div_right (by omega)
    omega
  have hvanish : ∀ j ∈ range ((v + b) / a + 1), j ∉ range K →
      (v + b - a * j) / (a + b) = 0 := by
    intro j _ hj
    rw [mem_range] at hj
    have h2 : a * K ≤ a * j := Nat.mul_le_mul_left a (by omega)
    exact Nat.div_eq_of_lt (by omega)
  have hsplit : ∑ j ∈ range K, (v + b - a * j) / (a + b)
      = ∑ j ∈ range ((v + b) / a + 1), (v + b - a * j) / (a + b) :=
    sum_subset (by intro x hx; rw [mem_range] at hx ⊢; omega) hvanish
  have hterm : ∀ j ∈ range K, (v + b - a * j) / (a + b)
      = (v - a * (j + 1)) / (a + b) + 1 := by
    intro j hj
    rw [mem_range] at hj
    have h3 : a * (j + 1) ≤ a * K := Nat.mul_le_mul_left a (by omega)
    have h4 : a * (j + 1) = a * j + a := by ring
    have h5 : v + b - a * j = v - a * (j + 1) + (a + b) := by omega
    rw [h5, Nat.add_div_right _ hd]
  have hA : potential a b (v + b) = K + ∑ j ∈ range K, (v - a * (j + 1)) / (a + b) := by
    simp only [potential]
    rw [← hsplit, sum_congr rfl hterm, sum_add_distrib, sum_const, card_range, smul_eq_mul,
      mul_one]
    ring
  have hB : potential a b v
      = (∑ j ∈ range K, (v - a * (j + 1)) / (a + b)) + v / (a + b) := by
    simp only [potential, ← hK]
    rw [sum_range_succ' (fun j => (v - a * j) / (a + b)) K]
    simp
  omega

/-! ### Vertex-disjoint cycle collections -/

/-- Congruent naturals that differ are at least `d = a + b` apart. -/
lemma add_le_of_cast_eq {a b v w : ℕ} (hvw : (v : ZMod (a + b)) = (w : ZMod (a + b)))
    (hlt : v < w) : v + (a + b) ≤ w := by
  have hmod : v ≡ w [MOD a + b] := (ZMod.natCast_eq_natCast_iff v w (a + b)).1 hvw
  have hdvd : (a + b) ∣ w - v := (Nat.modEq_iff_dvd' hlt.le).1 hmod
  have := Nat.le_of_dvd (by omega) hdvd
  omega

/-- Congruent naturals that differ lie on different levels. -/
lemma level_lt_level {a b : ℕ} (hd : 0 < a + b) {v w : ℕ}
    (hvw : (v : ZMod (a + b)) = (w : ZMod (a + b))) (hlt : v < w) :
    v / (a + b) < w / (a + b) := by
  have h1 : (v + (a + b)) / (a + b) ≤ w / (a + b) :=
    Nat.div_le_div_right (add_le_of_cast_eq hvw hlt)
  rw [Nat.add_div_right v hd] at h1
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) h1

/-- A finite collection of vertex-disjoint cycles in the graph on `ℕ` whose edges are
`v → v + b` and `v → v - a`: the occupied vertices together with the successor map. -/
structure CycleSystem (a b : ℕ) where
  /-- The vertices lying on one of the cycles. -/
  occupied : Finset ℕ
  /-- The next vertex along the cycle through a given vertex. -/
  succ : ℕ → ℕ
  /-- Every step is one of the two edges of the graph. -/
  step : ∀ v ∈ occupied, succ v = v + b ∨ a ≤ v ∧ succ v = v - a
  /-- The cycles stay inside the occupied set. -/
  succ_mem : ∀ v ∈ occupied, succ v ∈ occupied
  /-- The cycles are vertex-disjoint: distinct occupied vertices have distinct successors. -/
  succ_inj : ∀ v ∈ occupied, ∀ w ∈ occupied, succ v = succ w → v = w

namespace CycleSystem

variable {a b : ℕ} (X : CycleSystem a b)

/-- The successor advances the residue class modulo `d = a + b` by `b`. -/
lemma cast_succ {v : ℕ} (hv : v ∈ X.occupied) :
    ((X.succ v : ℕ) : ZMod (a + b)) = (v : ZMod (a + b)) + (b : ZMod (a + b)) := by
  have hz : (a : ZMod (a + b)) + (b : ZMod (a + b)) = 0 := by
    have h := ZMod.natCast_self (a + b)
    push_cast at h
    exact h
  rcases X.step v hv with h | ⟨hav, h⟩
  · rw [h]; push_cast; ring
  · rw [h, Nat.cast_sub hav]
    have hb : (b : ZMod (a + b)) = -(a : ZMod (a + b)) := by linear_combination hz
    rw [hb]; ring

/-- The occupied vertices in one residue class modulo `d = a + b`. -/
def classOf (c : ZMod (a + b)) : Finset ℕ := {v ∈ X.occupied | (v : ZMod (a + b)) = c}

/-- Membership in a residue class. -/
lemma mem_classOf {c : ZMod (a + b)} {v : ℕ} :
    v ∈ X.classOf c ↔ v ∈ X.occupied ∧ (v : ZMod (a + b)) = c := by
  simp [classOf]

/-- The successor sends the class `c` into the class `c + b`. -/
lemma succ_mem_classOf {c : ZMod (a + b)} {v : ℕ} (hv : v ∈ X.classOf c) :
    X.succ v ∈ X.classOf (c + b) := by
  rw [mem_classOf] at hv ⊢
  exact ⟨X.succ_mem v hv.1, by rw [X.cast_succ hv.1, hv.2]⟩

/-- Successors of congruent occupied vertices are ordered as the vertices are. -/
lemma succ_lt_succ {v w : ℕ} (hv : v ∈ X.occupied) (hw : w ∈ X.occupied)
    (hvw : (v : ZMod (a + b)) = (w : ZMod (a + b))) (hlt : v < w) : X.succ v < X.succ w := by
  by_contra hcon
  rw [Nat.not_lt] at hcon
  have hsv : X.succ v ≤ v + b := by rcases X.step v hv with h | ⟨_, h⟩ <;> omega
  have hd : v + (a + b) ≤ w := add_le_of_cast_eq hvw hlt
  rcases X.step w hw with h | ⟨haw, h⟩
  · omega
  · have heq : X.succ v = X.succ w := by omega
    have := X.succ_inj v hv w hw heq
    omega

/-- Each residue class carries at most as many occupied vertices as the next. -/
lemma card_classOf_le (c : ZMod (a + b)) : (X.classOf c).card ≤ (X.classOf (c + b)).card :=
  Finset.card_le_card_of_injOn X.succ (fun _ hv => X.succ_mem_classOf hv)
    (fun _ hv _ hw h => X.succ_inj _ (X.mem_classOf.1 hv).1 _ (X.mem_classOf.1 hw).1 h)

/-- Iterating the previous bound around the residue classes. -/
lemma card_classOf_le_mul (c : ZMod (a + b)) (k : ℕ) :
    (X.classOf c).card ≤ (X.classOf (c + (k : ZMod (a + b)) * (b : ZMod (a + b)))).card := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := X.card_classOf_le (c + (k : ZMod (a + b)) * (b : ZMod (a + b)))
    have heq : c + (k : ZMod (a + b)) * (b : ZMod (a + b)) + (b : ZMod (a + b))
        = c + ((k + 1 : ℕ) : ZMod (a + b)) * (b : ZMod (a + b)) := by push_cast; ring
    rw [heq] at h
    exact ih.trans h

/-- Every residue class is reached from every other by repeatedly adding `b`. -/
lemma exists_add_mul_eq (hab : Nat.Coprime a b) (hb : 0 < b) (c c' : ZMod (a + b)) :
    ∃ k : ℕ, c + (k : ZMod (a + b)) * (b : ZMod (a + b)) = c' := by
  have : NeZero (a + b) := ⟨by omega⟩
  have hcop : Nat.Coprime b (a + b) := Nat.coprime_add_self_right.2 hab.symm
  have hu : ((ZMod.unitOfCoprime b hcop : (ZMod (a + b))ˣ) : ZMod (a + b)) = (b : ZMod (a + b)) :=
    ZMod.coe_unitOfCoprime b hcop
  set u : (ZMod (a + b))ˣ := ZMod.unitOfCoprime b hcop with hudef
  obtain ⟨k, hk⟩ :=
    ZMod.natCast_zmod_surjective ((c' - c) * ((u⁻¹ : (ZMod (a + b))ˣ) : ZMod (a + b)))
  refine ⟨k, ?_⟩
  rw [hk, ← hu, mul_assoc, Units.inv_mul, mul_one]
  ring

/-- All residue classes carry the same number of occupied vertices. -/
lemma card_classOf_eq (hab : Nat.Coprime a b) (hb : 0 < b) (c c' : ZMod (a + b)) :
    (X.classOf c).card = (X.classOf c').card := by
  obtain ⟨k, hk⟩ := exists_add_mul_eq hab hb c c'
  obtain ⟨k', hk'⟩ := exists_add_mul_eq hab hb c' c
  have h1 := X.card_classOf_le_mul c k
  have h2 := X.card_classOf_le_mul c' k'
  rw [hk] at h1
  rw [hk'] at h2
  omega

/-- Every residue class has the size of the class of `0`: the common size `N` for which the
occupied set meets each class in exactly `N` points. -/
lemma card_classOf_eq_card_zero (hab : Nat.Coprime a b) (hb : 0 < b) (c : ZMod (a + b)) :
    (X.classOf c).card = (X.classOf 0).card := X.card_classOf_eq hab hb c 0

/-- The occupied set is the disjoint union of the `d = a + b` residue classes, all of the same
size: it has `dN` elements, `N` in each class. -/
lemma card_occupied (hab : Nat.Coprime a b) (hb : 0 < b) :
    X.occupied.card = (a + b) * (X.classOf 0).card := by
  have : NeZero (a + b) := ⟨by omega⟩
  have h1 : X.occupied.card
      = ∑ c : ZMod (a + b), {v ∈ X.occupied | ((v : ℕ) : ZMod (a + b)) = c}.card :=
    Finset.card_eq_sum_card_fiberwise fun v _ => Finset.mem_univ _
  have h2 : ∀ c : ZMod (a + b), {v ∈ X.occupied | ((v : ℕ) : ZMod (a + b)) = c}.card
      = (X.classOf 0).card := fun c => X.card_classOf_eq hab hb c 0
  rw [h1, Finset.sum_congr rfl fun c _ => h2 c, Finset.sum_const, Finset.card_univ, ZMod.card,
    smul_eq_mul]

/-- The successor map is order-preserving from one residue class to the next: it takes the
`i`-th smallest occupied vertex of the class `c` to the `i`-th smallest of the class `c + b`. -/
theorem succ_orderEmbOfFin {N : ℕ} (c : ZMod (a + b)) (h : (X.classOf c).card = N)
    (h' : (X.classOf (c + b)).card = N) (i : Fin N) :
    X.succ ((X.classOf c).orderEmbOfFin h i) = (X.classOf (c + b)).orderEmbOfFin h' i := by
  have key : (fun i => X.succ ((X.classOf c).orderEmbOfFin h i))
      = ⇑((X.classOf (c + b)).orderEmbOfFin h') := by
    refine Finset.orderEmbOfFin_unique h'
      (fun x => X.succ_mem_classOf (Finset.orderEmbOfFin_mem _ _ x)) ?_
    intro i j hij
    have hi := X.mem_classOf.1 (Finset.orderEmbOfFin_mem (X.classOf c) h i)
    have hj := X.mem_classOf.1 (Finset.orderEmbOfFin_mem (X.classOf c) h j)
    exact X.succ_lt_succ hi.1 hj.1 (by rw [hi.2, hj.2])
      (((X.classOf c).orderEmbOfFin h).strictMono hij)
  exact congrFun key i

/-- Two maps that carry a finset strictly monotonically into another finset of the same size
agree on it. -/
lemma eq_of_strictMonoOn {S T : Finset ℕ} {f g : ℕ → ℕ} (hST : T.card = S.card)
    (hf : ∀ v ∈ S, f v ∈ T) (hfm : ∀ v ∈ S, ∀ w ∈ S, v < w → f v < f w)
    (hg : ∀ v ∈ S, g v ∈ T) (hgm : ∀ v ∈ S, ∀ w ∈ S, v < w → g v < g w)
    {v : ℕ} (hv : v ∈ S) : f v = g v := by
  have hfe : (fun i => f ((S.orderEmbOfFin rfl) i)) = ⇑(T.orderEmbOfFin hST) :=
    Finset.orderEmbOfFin_unique hST (fun i => hf _ (Finset.orderEmbOfFin_mem _ _ i))
      (fun i j hij => hfm _ (Finset.orderEmbOfFin_mem _ _ i) _
        (Finset.orderEmbOfFin_mem _ _ j) ((S.orderEmbOfFin rfl).strictMono hij))
  have hge : (fun i => g ((S.orderEmbOfFin rfl) i)) = ⇑(T.orderEmbOfFin hST) :=
    Finset.orderEmbOfFin_unique hST (fun i => hg _ (Finset.orderEmbOfFin_mem _ _ i))
      (fun i j hij => hgm _ (Finset.orderEmbOfFin_mem _ _ i) _
        (Finset.orderEmbOfFin_mem _ _ j) ((S.orderEmbOfFin rfl).strictMono hij))
  obtain ⟨i, hi⟩ : ∃ i, (S.orderEmbOfFin rfl) i = v := by
    have hr : v ∈ Set.range ⇑(S.orderEmbOfFin (rfl : S.card = S.card)) := by
      rw [Finset.range_orderEmbOfFin]; exact hv
    exact hr
  rw [← hi]
  exact congrFun (hfe.trans hge.symm) i

/-- A cycle collection is determined by its occupied set. -/
theorem succ_eq_of_occupied_eq (Y : CycleSystem a b) (hab : Nat.Coprime a b) (hb : 0 < b)
    (hXY : X.occupied = Y.occupied) {v : ℕ} (hv : v ∈ X.occupied) : X.succ v = Y.succ v := by
  have hcls : ∀ c : ZMod (a + b), X.classOf c = Y.classOf c := by
    intro c; simp only [classOf, hXY]
  refine eq_of_strictMonoOn (S := X.classOf ((v : ℕ) : ZMod (a + b)))
    (T := X.classOf (((v : ℕ) : ZMod (a + b)) + b)) (X.card_classOf_eq hab hb _ _)
    (fun _ hw => X.succ_mem_classOf hw) ?_ ?_ ?_ (X.mem_classOf.2 ⟨hv, rfl⟩)
  · exact fun _ hw _ hw' hlt => X.succ_lt_succ (X.mem_classOf.1 hw).1 (X.mem_classOf.1 hw').1
      (by rw [(X.mem_classOf.1 hw).2, (X.mem_classOf.1 hw').2]) hlt
  · intro w hw
    rw [hcls] at hw ⊢
    exact Y.succ_mem_classOf hw
  · intro w hw w' hw' hlt
    rw [hcls] at hw hw'
    exact Y.succ_lt_succ (Y.mem_classOf.1 hw).1 (Y.mem_classOf.1 hw').1
      (by rw [(Y.mem_classOf.1 hw).2, (Y.mem_classOf.1 hw').2]) hlt

/-! ### The levels of the occupied vertices -/

/-- The levels `⌊v/d⌋` of the occupied vertices of one residue class, in increasing order. -/
def levels {N : ℕ} (c : ZMod (a + b)) (h : (X.classOf c).card = N) (i : Fin N) : ℕ :=
  (X.classOf c).orderEmbOfFin h i / (a + b)

/-- The level enumeration of a residue class is strictly increasing. -/
lemma strictMono_levels (hd : 0 < a + b) {N : ℕ} (c : ZMod (a + b))
    (h : (X.classOf c).card = N) : StrictMono (X.levels c h) := by
  intro i j hij
  have hi := X.mem_classOf.1 (Finset.orderEmbOfFin_mem (X.classOf c) h i)
  have hj := X.mem_classOf.1 (Finset.orderEmbOfFin_mem (X.classOf c) h j)
  exact level_lt_level hd (by rw [hi.2, hj.2]) (((X.classOf c).orderEmbOfFin h).strictMono hij)

/-- Out of a vertex whose residue is below `a` the level either stays put or drops by one. -/
lemma level_succ_of_mod_lt (hd : 0 < a + b) {v : ℕ} (hv : v ∈ X.occupied)
    (hr : v % (a + b) < a) :
    X.succ v / (a + b) = v / (a + b) ∨ X.succ v / (a + b) + 1 = v / (a + b) := by
  have hdm := Nat.div_add_mod v (a + b)
  have hz : (v % (a + b) + b) / (a + b) = 0 := Nat.div_eq_of_lt (by omega)
  rcases X.step v hv with h | ⟨hav, h⟩
  · left
    have hrw : v + b = (a + b) * (v / (a + b)) + (v % (a + b) + b) := by omega
    rw [h, hrw, Nat.mul_add_div hd, hz, Nat.add_zero]
  · right
    obtain ⟨q, hq⟩ : ∃ q, v / (a + b) = q + 1 := by
      refine ⟨v / (a + b) - 1, ?_⟩
      rcases Nat.eq_zero_or_pos (v / (a + b)) with h0 | h1
      · rw [h0] at hdm; omega
      · omega
    have hmul : (a + b) * (q + 1) = (a + b) * q + (a + b) := by ring
    have hrw : v - a = (a + b) * q + (v % (a + b) + b) := by rw [hq] at hdm; omega
    rw [h, hrw, Nat.mul_add_div hd, hz, Nat.add_zero, hq]

/-- Out of a vertex whose residue is at least `a` the level either stays put or rises by one. -/
lemma level_succ_of_le_mod (hd : 0 < a + b) {v : ℕ} (hv : v ∈ X.occupied)
    (hr : a ≤ v % (a + b)) :
    X.succ v / (a + b) = v / (a + b) ∨ X.succ v / (a + b) = v / (a + b) + 1 := by
  have hdm := Nat.div_add_mod v (a + b)
  have hlt := Nat.mod_lt v hd
  rcases X.step v hv with h | ⟨hav, h⟩
  · right
    have hz : (v % (a + b) + b) / (a + b) = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    have hrw : v + b = (a + b) * (v / (a + b)) + (v % (a + b) + b) := by omega
    rw [h, hrw, Nat.mul_add_div hd, hz]
  · left
    have hz : (v % (a + b) - a) / (a + b) = 0 := Nat.div_eq_of_lt (by omega)
    have hrw : v - a = (a + b) * (v / (a + b)) + (v % (a + b) - a) := by omega
    rw [h, hrw, Nat.mul_add_div hd, hz, Nat.add_zero]

/-- In a class whose residues are below `a`, each level of the next class is the corresponding
level or one less. -/
theorem levels_succ_of_mod_lt (hd : 0 < a + b) {N : ℕ} (c : ZMod (a + b))
    (h : (X.classOf c).card = N) (h' : (X.classOf (c + b)).card = N)
    (hr : ∀ v ∈ X.classOf c, v % (a + b) < a) (i : Fin N) :
    X.levels (c + b) h' i = X.levels c h i ∨ X.levels (c + b) h' i + 1 = X.levels c h i := by
  have hmem := Finset.orderEmbOfFin_mem (X.classOf c) h i
  have hstep := X.level_succ_of_mod_lt hd (X.mem_classOf.1 hmem).1 (hr _ hmem)
  rw [X.succ_orderEmbOfFin c h h' i] at hstep
  exact hstep

/-- In a class whose residues are at least `a`, each level of the next class is the
corresponding level or one more. -/
theorem levels_succ_of_le_mod (hd : 0 < a + b) {N : ℕ} (c : ZMod (a + b))
    (h : (X.classOf c).card = N) (h' : (X.classOf (c + b)).card = N)
    (hr : ∀ v ∈ X.classOf c, a ≤ v % (a + b)) (i : Fin N) :
    X.levels (c + b) h' i = X.levels c h i ∨ X.levels (c + b) h' i = X.levels c h i + 1 := by
  have hmem := Finset.orderEmbOfFin_mem (X.classOf c) h i
  have hstep := X.level_succ_of_le_mod hd (X.mem_classOf.1 hmem).1 (hr _ hmem)
  rw [X.succ_orderEmbOfFin c h h' i] at hstep
  exact hstep

/-! ### The staircase partitions of the residue classes -/

/-- The staircase partition of a residue class has at most `N` parts. -/
lemma isPartitionUpTo_stair_levels (hd : 0 < a + b) {N : ℕ} (c : ZMod (a + b))
    (h : (X.classOf c).card = N) : IsPartitionUpTo N (stair (X.levels c h)) :=
  isPartitionUpTo_stair (X.strictMono_levels hd c h)

/-- In a class whose residues are below `a`, the staircase partition of the next class is
obtained by removing a vertical strip, so the conjugates differ by a horizontal strip. -/
theorem conjPart_stair_horizontal (hd : 0 < a + b) {N : ℕ} (c : ZMod (a + b))
    (h : (X.classOf c).card = N) (h' : (X.classOf (c + b)).card = N)
    (hr : ∀ v ∈ X.classOf c, v % (a + b) < a) (i : ℕ) :
    conjPart (stair (X.levels (c + b) h')) i ≤ conjPart (stair (X.levels c h)) i ∧
      conjPart (stair (X.levels c h)) (i + 1) ≤ conjPart (stair (X.levels (c + b) h')) i := by
  have hpt : ∀ k : Fin N, X.levels (c + b) h' k ≤ X.levels c h k ∧
      X.levels c h k ≤ X.levels (c + b) h' k + 1 := by
    intro k
    rcases X.levels_succ_of_mod_lt hd c h h' hr k with hk | hk <;> omega
  exact conjPart_horizontal (X.isPartitionUpTo_stair_levels hd c h)
    (X.isPartitionUpTo_stair_levels hd (c + b) h')
    (fun j => stair_le_stair (fun k => (hpt k).1) j)
    (fun j => stair_le_stair_succ (fun k => (hpt k).2) j) i

/-! ### The weight of a cycle collection -/

/-- The `q`-exponent of the weight of the collection: the sum of `⌊v/a⌋` over the occupied
vertices leaving along an up-edge. -/
def weightExp : ℕ := ∑ v ∈ X.occupied, if X.succ v = v + b then v / a else 0

/-- The successor map permutes the occupied set. -/
lemma image_succ : X.occupied.image X.succ = X.occupied := by
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hw
    exact X.succ_mem v hv
  · exact le_of_eq
      (Finset.card_image_of_injOn fun v hv w hw hvw => X.succ_inj v hv w hw hvw).symm

/-- Reindexing a sum over the occupied set along the successor map. -/
lemma sum_comp_succ (F : ℕ → ℕ) : ∑ v ∈ X.occupied, F (X.succ v) = ∑ v ∈ X.occupied, F v := by
  rw [← Finset.sum_image (f := F) (g := X.succ)
    (fun v hv w hw hvw => X.succ_inj v hv w hw hvw), X.image_succ]

/-- The weight of the collection is the sum of the levels of its occupied vertices: the
potential telescopes around the cycles. -/
theorem weightExp_eq_sum_div (ha : 0 < a) (hb : 0 < b) :
    X.weightExp = ∑ v ∈ X.occupied, v / (a + b) := by
  have key : ∀ v ∈ X.occupied, (if X.succ v = v + b then v / a else 0) + potential a b v
      = v / (a + b) + potential a b (X.succ v) := by
    intro v hv
    rcases X.step v hv with h | ⟨hav, h⟩
    · rw [ite_eq_left h, h]
      have := potential_add_right (a := a) (b := b) ha v
      omega
    · rw [h, ite_eq_right (show ¬ v - a = v + b by omega)]
      obtain ⟨u, hu⟩ : ∃ u, v = u + a := ⟨v - a, by omega⟩
      subst hu
      have h2 := potential_add_left (a := a) (b := b) ha u
      rw [Nat.add_sub_cancel]
      omega
  have hsum : ∑ v ∈ X.occupied, ((if X.succ v = v + b then v / a else 0) + potential a b v)
      = ∑ v ∈ X.occupied, (v / (a + b) + potential a b (X.succ v)) :=
    Finset.sum_congr rfl key
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, X.sum_comp_succ (potential a b)] at hsum
  change (∑ v ∈ X.occupied, if X.succ v = v + b then v / a else 0)
    = ∑ v ∈ X.occupied, v / (a + b)
  exact Nat.add_right_cancel hsum

/-- The weight of the collection is the rank shift `γ_N = d\binom{N}{2}` plus the total size of
the `d` staircase partitions read off its residue classes. -/
theorem weightExp_eq_gammaShift_add [NeZero (a + b)] (ha : 0 < a) (hb : 0 < b) {N : ℕ}
    (hN : ∀ c : ZMod (a + b), (X.classOf c).card = N) :
    X.weightExp = Paths.gammaShift a b N
      + ∑ c : ZMod (a + b), ∑ j ∈ range N, stair (X.levels c (hN c)) j := by
  have hd : 0 < a + b := by omega
  have h1 : ∑ v ∈ X.occupied, v / (a + b)
      = ∑ c : ZMod (a + b), ∑ v ∈ X.classOf c, v / (a + b) :=
    (Finset.sum_fiberwise_of_maps_to (fun v _ => Finset.mem_univ ((v : ℕ) : ZMod (a + b)))
      fun v => v / (a + b)).symm
  have h2 : ∀ c : ZMod (a + b), ∑ v ∈ X.classOf c, v / (a + b)
      = ∑ i : Fin N, X.levels c (hN c) i := by
    intro c
    rw [← Finset.image_orderEmbOfFin_univ (X.classOf c) (hN c),
      Finset.sum_image fun i _ j _ hij => ((X.classOf c).orderEmbOfFin (hN c)).injective hij]
    rfl
  have h3 : ∀ c : ZMod (a + b), ∑ i : Fin N, X.levels c (hN c) i
      = (∑ j ∈ range N, stair (X.levels c (hN c)) j) + N.choose 2 := fun c =>
    (sum_stair_add_choose (X.strictMono_levels hd c (hN c))).symm
  rw [Paths.gammaShift, X.weightExp_eq_sum_div ha hb, h1,
    Finset.sum_congr rfl fun c _ => (h2 c).trans (h3 c), Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, ZMod.card, smul_eq_mul]
  exact Nat.add_comm _ _

end CycleSystem

/-! ### Row offsets and the profile -/

/-- The row offsets `⌊ib/a⌋` increase by the profile. -/
lemma succ_mul_div_eq (a b i : ℕ) : (i + 1) * b / a = i * b / a + HJO.Cylindric.profile a b i := by
  have h : i * b / a ≤ (i + 1) * b / a :=
    Nat.div_le_div_right (Nat.mul_le_mul_right b (Nat.le_succ i))
  simp only [HJO.Cylindric.profile]
  omega

/-! ### Conjugation and the size of a partition -/

/-- The conjugate of a partition vanishes at every index reaching its largest part. -/
lemma conjPart_eq_zero {N : ℕ} {l : ℕ → ℕ} (hl : IsPartitionUpTo N l) {i : ℕ} (h : l 0 ≤ i) :
    conjPart l i = 0 :=
  Nat.le_zero.1 ((conjPart_le_iff hl i 0).2 h)

/-- The parts of a partition exceeding `i` are exactly those whose index lies below the `i`-th
part of the conjugate. -/
lemma filter_lt_eq_range_conjPart {N : ℕ} {l : ℕ → ℕ} (hl : IsPartitionUpTo N l) (i : ℕ) :
    {k ∈ range N | i < l k} = range (conjPart l i) := by
  ext k
  simp only [mem_filter, mem_range]
  refine ⟨fun hk => ?_, fun hk => ⟨lt_of_lt_of_le hk (conjPart_le hl i), ?_⟩⟩
  · by_contra hcon
    exact absurd ((conjPart_le_iff hl i k).1 (by omega)) (by omega)
  · by_contra hcon
    exact absurd ((conjPart_le_iff hl i k).2 (by omega)) (by omega)

/-- Conjugation preserves the size of a partition: summing the conjugate over a range reaching
the largest part returns the sum of the parts. -/
lemma sum_range_conjPart {N M : ℕ} {l : ℕ → ℕ} (hl : IsPartitionUpTo N l) (hM : l 0 ≤ M) :
    ∑ i ∈ range M, conjPart l i = ∑ k ∈ range N, l k := by
  have h1 : ∀ i ∈ range M, conjPart l i = ∑ k ∈ range N, if i < l k then 1 else 0 := by
    intro i _
    rw [← Finset.card_filter, filter_lt_eq_range_conjPart hl i, card_range]
  rw [sum_congr rfl h1, sum_comm]
  refine sum_congr rfl fun k _ => ?_
  have hlk : l k ≤ M := le_trans (hl.antitone (Nat.zero_le k)) hM
  have h2 : {i ∈ range M | i < l k} = range (l k) := by
    ext i; simp only [mem_filter, mem_range]; omega
  rw [← Finset.card_filter, h2, card_range]

/-! ### Recovering a partition from its conjugate and its staircase -/

/-- Conjugation is injective on partitions. -/
lemma conjPart_injective {N N' : ℕ} {l m : ℕ → ℕ} (hl : IsPartitionUpTo N l)
    (hm : IsPartitionUpTo N' m) (h : conjPart l = conjPart m) : l = m := by
  funext j
  have h1 : m j ≤ l j := by
    have h2 := (conjPart_le_iff hl (l j) j).2 le_rfl
    rw [h] at h2
    exact (conjPart_le_iff hm (l j) j).1 h2
  have h3 : l j ≤ m j := by
    have h4 := (conjPart_le_iff hm (m j) j).2 le_rfl
    rw [← h] at h4
    exact (conjPart_le_iff hl (m j) j).1 h4
  omega

/-- A strictly increasing sequence is recovered from its staircase subtraction by adding the
staircase back. -/
lemma stair_add_val {N : ℕ} {f : Fin N → ℕ} (hf : StrictMono f) (j : ℕ) (hj : j < N)
    (h' : N - 1 - j < N) : stair f j + (N - 1 - j) = f ⟨N - 1 - j, h'⟩ := by
  have h0 : 0 < N := by omega
  have hfi : f ⟨0, h0⟩ + (N - 1 - j) ≤ f ⟨N - 1 - j, h'⟩ :=
    add_le_of_strictMono hf (N - 1 - j) ⟨0, h0⟩ ⟨N - 1 - j, h'⟩ (by simp)
  rw [stair_of_lt f hj h']
  omega

/-- The staircase subtraction is injective on strictly increasing sequences. -/
lemma stair_injective {N : ℕ} {f g : Fin N → ℕ} (hf : StrictMono f) (hg : StrictMono g)
    (h : stair f = stair g) : f = g := by
  funext i
  have hi : (i : ℕ) < N := i.isLt
  have hj : N - 1 - (i : ℕ) < N := by omega
  have h' : N - 1 - (N - 1 - (i : ℕ)) < N := by omega
  have e1 := stair_add_val hf (N - 1 - (i : ℕ)) hj h'
  have e2 := stair_add_val hg (N - 1 - (i : ℕ)) hj h'
  have hidx : (⟨N - 1 - (N - 1 - (i : ℕ)), h'⟩ : Fin N) = i := by
    apply Fin.val_injective
    change N - 1 - (N - 1 - (i : ℕ)) = (i : ℕ)
    omega
  rw [hidx] at e1 e2
  rw [h] at e1
  omega

/-! ### Reindexing sums over an initial segment -/

/-- The quotient and remainder of a number presented as `n q + s` with `s < n`. -/
lemma div_mod_eq_of_lt {n q s : ℕ} (hn : 0 < n) (hs : s < n) :
    (n * q + s) / n = q ∧ (n * q + s) % n = s :=
  ⟨by rw [Nat.mul_add_div hn, Nat.div_eq_of_lt hs, Nat.add_zero],
    by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hs]⟩

/-- Splitting an initial segment of length `m M` into `M` blocks of `m` consecutive numbers. -/
lemma sum_range_mul_split (m M : ℕ) (F : ℕ → ℕ) :
    ∑ w ∈ range (m * M), F w = ∑ x ∈ range M, ∑ r ∈ range m, F (r + m * x) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Nat.mul_succ, sum_range_add, ih, sum_range_succ]
    congr 1
    exact sum_congr rfl fun r _ => by rw [Nat.add_comm]

/-- Multiplying by `b` is injective on the residues modulo `a` when `a` and `b` are coprime. -/
lemma injOn_mul_mod {a b : ℕ} (hab : Nat.Coprime a b) :
    Set.InjOn (fun i => i * b % a) (range a : Finset ℕ) := by
  intro i hi j hj hij
  simp only [Finset.coe_range, Set.mem_Iio] at hi hj
  have hij' : i * b % a = j * b % a := hij
  have h2 : i % a = j % a := Nat.ModEq.cancel_right_of_coprime hab hij'
  rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at h2
  exact h2

/-- Multiplying by `b` permutes the residues modulo `a` when `a` and `b` are coprime. -/
lemma image_mul_mod {a b : ℕ} (hab : Nat.Coprime a b) (ha : 0 < a) :
    (range a).image (fun i => i * b % a) = range a := by
  refine Finset.eq_of_subset_of_card_le (fun r hr => ?_) (le_of_eq ?_)
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hr
    exact mem_range.2 (Nat.mod_lt _ ha)
  · exact (Finset.card_image_of_injOn (injOn_mul_mod hab)).symm

/-- Reindexing a double sum over rows and columns as a sum over the diagonal positions
`ib mod a + aj`. -/
lemma sum_range_diagPos {a b : ℕ} (hab : Nat.Coprime a b) (ha : 0 < a) (J : ℕ) (F : ℕ → ℕ) :
    ∑ i ∈ range a, ∑ j ∈ range J, F (i * b % a + a * j) = ∑ w ∈ range (a * J), F w := by
  calc ∑ i ∈ range a, ∑ j ∈ range J, F (i * b % a + a * j)
      = ∑ r ∈ (range a).image (fun i => i * b % a), ∑ j ∈ range J, F (r + a * j) :=
        (Finset.sum_image (f := fun r => ∑ j ∈ range J, F (r + a * j))
          (injOn_mul_mod hab)).symm
    _ = ∑ r ∈ range a, ∑ j ∈ range J, F (r + a * j) := by rw [image_mul_mod hab ha]
    _ = ∑ w ∈ range (a * J), F w := by rw [sum_range_mul_split, sum_comm]

/-- A sum over the residues modulo `n` written as a sum over an initial segment. -/
lemma sum_zmod_eq_sum_range (n : ℕ) [NeZero n] (g : ZMod n → ℕ) :
    ∑ c : ZMod n, g c = ∑ r ∈ range n, g (r : ZMod n) :=
  Finset.sum_nbij' (fun c : ZMod n => c.val) (fun r : ℕ => (r : ZMod n))
    (fun c _ => mem_range.2 (ZMod.val_lt c)) (fun _ _ => mem_univ _)
    (fun c _ => ZMod.natCast_rightInverse c) (fun _ hr => ZMod.val_cast_of_lt (mem_range.1 hr))
    (fun c _ => congrArg g (ZMod.natCast_rightInverse c).symm)

/-! ### Diagonal functions and the arrays they read off -/

/-- A diagonal function at `(a, b)` bounded by `N`: a function of the diagonal position that does
not increase along either edge displacement, is bounded by `N` and vanishes far out. -/
structure IsDiagFun (a b N : ℕ) (W : ℕ → ℕ) : Prop where
  /-- Moving the position up by `a` does not increase the value. -/
  step_left : ∀ w, W (w + a) ≤ W w
  /-- Moving the position up by `b` does not increase the value. -/
  step_right : ∀ w, W (w + b) ≤ W w
  /-- Every value is at most `N`. -/
  le_bound : ∀ w, W w ≤ N
  /-- The function vanishes at all large positions. -/
  vanish : ∃ B, ∀ w, B ≤ w → W w = 0

/-- The array read off a diagonal function: the entry in row `i` and column `j` is the value at
the diagonal position `ib mod a + aj`. -/
def cylOfDiag (a b : ℕ) (W : ℕ → ℕ) (i j : ℕ) : ℕ := W (i * b % a + a * j)

/-- Moving down `a` rows leaves the diagonal position unchanged. -/
lemma diagPos_add_row (a b i j : ℕ) : (i + a) * b % a + a * j = i * b % a + a * j := by
  rw [add_mul, Nat.add_mul_mod_self_left]

/-- Moving down one row and right `c_i` columns raises the diagonal position by `b`. -/
lemma diagPos_succ_row (a b i j : ℕ) :
    (i + 1) * b % a + a * (j + HJO.Cylindric.profile a b i) = i * b % a + a * j + b := by
  have hprof := succ_mul_div_eq a b i
  have h1 := Nat.mod_add_div (i * b) a
  have h2 := Nat.mod_add_div ((i + 1) * b) a
  rw [hprof, Nat.mul_add] at h2
  have h3 : (i + 1) * b = i * b + b := by ring
  rw [Nat.mul_add]
  omega

/-- Moving right one column raises the diagonal position by `a`. -/
lemma diagPos_succ_col (a b i j : ℕ) : i * b % a + a * (j + 1) = i * b % a + a * j + a := by
  rw [Nat.mul_add, Nat.mul_one, Nat.add_assoc]

/-- A diagonal position is at least its column index. -/
lemma le_diagPos {a : ℕ} (ha : 0 < a) (b i j : ℕ) : j ≤ i * b % a + a * j := by
  have := Nat.le_mul_of_pos_left j ha
  omega

/-- The array read off a diagonal function is a cylindric partition with the balanced profile. -/
theorem isCylindric_cylOfDiag {a b N : ℕ} (ha : 0 < a) {W : ℕ → ℕ} (hW : IsDiagFun a b N W) :
    HJO.Cylindric.IsCylindric a (HJO.Cylindric.profile a b) (cylOfDiag a b W) where
  antitone i := antitone_nat_of_succ_le fun j => by
    simp only [cylOfDiag, diagPos_succ_col]
    exact hW.step_left _
  eventually_zero i := by
    obtain ⟨B, hB⟩ := hW.vanish
    exact ⟨B, fun j hj => hB _ (le_trans hj (le_diagPos ha b i j))⟩
  periodic i j := by simp only [cylOfDiag, diagPos_add_row]
  outgoing i j := by
    simp only [cylOfDiag, diagPos_succ_row]
    exact hW.step_right _

/-- Every entry of the array read off a diagonal function is at most `N`. -/
theorem boundedBy_cylOfDiag {a b N : ℕ} {W : ℕ → ℕ} (hW : IsDiagFun a b N W) :
    HJO.Cylindric.BoundedBy N (cylOfDiag a b W) := fun _ _ => hW.le_bound _

/-- The volume of the array read off a diagonal function is the total of its values. -/
theorem cylVolume_cylOfDiag {a b N : ℕ} (hab : Nat.Coprime a b) (ha : 0 < a) {W : ℕ → ℕ}
    (hW : IsDiagFun a b N W) : HJO.Cylindric.cylVolume a (cylOfDiag a b W) = ∑ᶠ w, W w := by
  obtain ⟨B, hB⟩ := hW.vanish
  have hBa : B ≤ a * B := Nat.le_mul_of_pos_left B ha
  have hfin : ∀ i : ℕ, (∑ᶠ j : ℕ, cylOfDiag a b W i j)
      = ∑ j ∈ range B, cylOfDiag a b W i j := by
    intro i
    refine finsum_eq_finsetSum_of_support_subset _ fun j hj => ?_
    simp only [Function.mem_support] at hj
    rw [Finset.mem_coe, mem_range]
    by_contra hcon
    exact hj (hB _ (le_trans (by omega) (le_diagPos ha b i j)))
  calc HJO.Cylindric.cylVolume a (cylOfDiag a b W)
      = ∑ i ∈ range a, ∑ j ∈ range B, cylOfDiag a b W i j := by
        rw [HJO.Cylindric.cylVolume]; exact sum_congr rfl fun i _ => hfin i
    _ = ∑ w ∈ range (a * B), W w := sum_range_diagPos hab ha B W
    _ = ∑ᶠ w, W w := by
        refine (finsum_eq_finsetSum_of_support_subset _ fun w hw => ?_).symm
        simp only [Function.mem_support] at hw
        rw [Finset.mem_coe, mem_range]
        by_contra hcon
        exact hw (hB _ (by omega))

/-! ### The diagonal function of a cylindric partition -/

/-- An `a`-periodic family of rows is unchanged by adding a multiple of `a` to the row index. -/
lemma row_add_mul {a : ℕ} {l : ℕ → ℕ → ℕ} (hl : ∀ i j, l (i + a) j = l i j) (i n j : ℕ) :
    l (i + a * n) j = l i j := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.mul_succ, ← Nat.add_assoc, hl, ih]

/-- An `a`-periodic family of rows is determined by the row index modulo `a`. -/
lemma row_mod_eq {a : ℕ} {l : ℕ → ℕ → ℕ} (hl : ∀ i j, l (i + a) j = l i j) (i j : ℕ) :
    l (i % a) j = l i j := by
  conv_rhs => rw [← Nat.mod_add_div i a]
  exact (row_add_mul hl (i % a) (i / a) j).symm

/-- Every residue modulo `a` is the diagonal offset of some row below `a`. -/
lemma exists_lt_mul_mod {a b : ℕ} (hab : Nat.Coprime a b) (ha : 0 < a) (w : ℕ) :
    ∃ i < a, i * b % a = w % a := by
  have h : w % a ∈ (range a).image (fun i => i * b % a) := by
    rw [image_mul_mod hab ha]; exact mem_range.2 (Nat.mod_lt _ ha)
  obtain ⟨i, hi, hiw⟩ := Finset.mem_image.1 h
  exact ⟨i, mem_range.1 hi, hiw⟩

/-- The row of a diagonal position: the least row whose diagonal offset is `w` modulo `a`. -/
noncomputable def rowOf (a b w : ℕ) : ℕ := sInf {i | i * b % a = w % a}

/-- The row of a diagonal position has that position's diagonal offset. -/
lemma rowOf_mul_mod {a b : ℕ} (hab : Nat.Coprime a b) (ha : 0 < a) (w : ℕ) :
    rowOf a b w * b % a = w % a := by
  obtain ⟨i, _, hiw⟩ := exists_lt_mul_mod hab ha w
  have hne : {i | i * b % a = w % a}.Nonempty := ⟨i, hiw⟩
  exact Nat.sInf_mem hne

/-- The row of a diagonal position lies below `a`. -/
lemma rowOf_lt {a b : ℕ} (hab : Nat.Coprime a b) (ha : 0 < a) (w : ℕ) : rowOf a b w < a := by
  obtain ⟨i, hi, hiw⟩ := exists_lt_mul_mod hab ha w
  exact lt_of_le_of_lt (Nat.sInf_le hiw) hi

/-- Recovering a diagonal position from its row and column. -/
lemma diagPos_rowOf {a b : ℕ} (hab : Nat.Coprime a b) (ha : 0 < a) (w : ℕ) :
    rowOf a b w * b % a + a * (w / a) = w := by
  rw [rowOf_mul_mod hab ha]
  exact Nat.mod_add_div w a

/-- The row of a diagonal position depends only on the position modulo `a`. -/
lemma rowOf_congr (a b : ℕ) {w w' : ℕ} (h : w % a = w' % a) : rowOf a b w = rowOf a b w' := by
  simp only [rowOf, h]

/-- The diagonal offset of an entry is the position modulo `a`. -/
lemma diagPos_mod {a : ℕ} (ha : 0 < a) (b i j : ℕ) : (i * b % a + a * j) % a = i * b % a := by
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (Nat.mod_lt _ ha)]

/-- The column of the diagonal position of an entry is its column. -/
lemma diagPos_div {a : ℕ} (ha : 0 < a) (b i j : ℕ) : (i * b % a + a * j) / a = j := by
  rw [Nat.add_mul_div_left _ _ ha, Nat.div_eq_of_lt (Nat.mod_lt _ ha), Nat.zero_add]

/-- The row of the diagonal position of an entry is its row modulo `a`. -/
lemma rowOf_diagPos {a b : ℕ} (hab : Nat.Coprime a b) (ha : 0 < a) (i j : ℕ) :
    rowOf a b (i * b % a + a * j) = i % a := by
  have hmul : i % a * b % a = i * b % a := Nat.mod_mul_mod i b a
  have hpos : (i * b % a + a * j) % a = i * b % a := diagPos_mod ha b i j
  refine injOn_mul_mod hab ?_ ?_ ?_
  · exact Finset.mem_coe.2 (mem_range.2 (rowOf_lt hab ha _))
  · exact Finset.mem_coe.2 (mem_range.2 (Nat.mod_lt _ ha))
  · change rowOf a b (i * b % a + a * j) * b % a = i % a * b % a
    rw [rowOf_mul_mod hab ha, hmul, hpos]

/-- The diagonal function of an array: the value at the position `w` is the entry in the row of
`w` and the column `w / a`. -/
noncomputable def diagOfCyl (a b : ℕ) (l : ℕ → ℕ → ℕ) (w : ℕ) : ℕ := l (rowOf a b w) (w / a)

/-- At the diagonal position of an entry the diagonal function of an `a`-periodic array returns
that entry. -/
lemma diagOfCyl_diagPos {a b : ℕ} (hab : Nat.Coprime a b) (ha : 0 < a) {l : ℕ → ℕ → ℕ}
    (hl : ∀ i j, l (i + a) j = l i j) (i j : ℕ) :
    diagOfCyl a b l (i * b % a + a * j) = l i j := by
  simp only [diagOfCyl, rowOf_diagPos hab ha, diagPos_div ha]
  exact row_mod_eq hl i j

/-- Reading an array off its own diagonal function returns the array, provided its rows are
`a`-periodic. -/
theorem cylOfDiag_diagOfCyl {a b : ℕ} (hab : Nat.Coprime a b) (ha : 0 < a) {l : ℕ → ℕ → ℕ}
    (hl : ∀ i j, l (i + a) j = l i j) : cylOfDiag a b (diagOfCyl a b l) = l := by
  funext i j
  exact diagOfCyl_diagPos hab ha hl i j

/-- The diagonal function of the array read off a diagonal function is that function. -/
theorem diagOfCyl_cylOfDiag {a b : ℕ} (hab : Nat.Coprime a b) (ha : 0 < a) (W : ℕ → ℕ) :
    diagOfCyl a b (cylOfDiag a b W) = W := by
  funext w
  simp only [diagOfCyl, cylOfDiag, diagPos_rowOf hab ha w]

/-- The diagonal function of a cylindric partition bounded by `N` is a diagonal function bounded
by `N`: the outgoing inequality becomes the step by `b` and the row inequality the step by `a`. -/
theorem isDiagFun_diagOfCyl {a b N : ℕ} (hab : Nat.Coprime a b) (ha : 0 < a) {l : ℕ → ℕ → ℕ}
    (hl : HJO.Cylindric.IsCylindric a (HJO.Cylindric.profile a b) l)
    (hbd : HJO.Cylindric.BoundedBy N l) :
    IsDiagFun a b N (diagOfCyl a b l) where
  step_left w := by
    simp only [diagOfCyl, rowOf_congr a b (Nat.add_mod_right w a), Nat.add_div_right w ha]
    exact hl.antitone _ (Nat.le_succ _)
  step_right w := by
    have hw := diagPos_rowOf hab ha w
    have key : w + b = (rowOf a b w + 1) * b % a
        + a * (w / a + HJO.Cylindric.profile a b (rowOf a b w)) := by
      rw [diagPos_succ_row]; omega
    rw [key, diagOfCyl_diagPos hab ha hl.periodic]
    exact hl.outgoing _ _
  le_bound w := hbd _ _
  vanish := by
    choose J hJ using hl.eventually_zero
    refine ⟨a * ((range a).sup J + 1), fun w hw => ?_⟩
    refine hJ (rowOf a b w) (w / a) ?_
    have h1 : J (rowOf a b w) ≤ (range a).sup J :=
      Finset.le_sup (f := J) (mem_range.2 (rowOf_lt hab ha w))
    have h2 : (range a).sup J + 1 ≤ w / a :=
      (Nat.le_div_iff_mul_le ha).2 (by rw [Nat.mul_comm]; exact hw)
    omega

namespace CycleSystem

variable {a b : ℕ} (X : CycleSystem a b)

/-! ### The diagonal reading of a cycle collection -/

/-- Every occupied vertex of the residue class `c` has residue `c.val` modulo `d = a + b`. -/
lemma mod_eq_val_of_mem_classOf {c : ZMod (a + b)} {v : ℕ} (hv : v ∈ X.classOf c) :
    v % (a + b) = c.val := by
  rw [← (X.mem_classOf.1 hv).2, ZMod.val_natCast]

/-- In a class whose residues are at least `a`, the staircase partition of the next class is
obtained by adding a vertical strip, so the conjugates gain a horizontal strip. -/
theorem conjPart_stair_horizontal' (hd : 0 < a + b) {N : ℕ} (c : ZMod (a + b))
    (h : (X.classOf c).card = N) (h' : (X.classOf (c + b)).card = N)
    (hr : ∀ v ∈ X.classOf c, a ≤ v % (a + b)) (i : ℕ) :
    conjPart (stair (X.levels c h)) i ≤ conjPart (stair (X.levels (c + b) h')) i ∧
      conjPart (stair (X.levels (c + b) h')) (i + 1) ≤ conjPart (stair (X.levels c h)) i := by
  have hpt : ∀ k : Fin N, X.levels c h k ≤ X.levels (c + b) h' k ∧
      X.levels (c + b) h' k ≤ X.levels c h k + 1 := by
    intro k
    rcases X.levels_succ_of_le_mod hd c h h' hr k with hk | hk <;> omega
  exact conjPart_horizontal (X.isPartitionUpTo_stair_levels hd (c + b) h')
    (X.isPartitionUpTo_stair_levels hd c h)
    (fun j => stair_le_stair (fun k => (hpt k).1) j)
    (fun j => stair_le_stair_succ (fun k => (hpt k).2) j) i

/-- The diagonal step out of a class whose residue is below `a`. -/
lemma conjPart_step_lt (hd : 0 < a + b) {N : ℕ} {c : ZMod (a + b)} (hc : c.val < a)
    (h : (X.classOf c).card = N) (h' : (X.classOf (c + b)).card = N) (x : ℕ) :
    conjPart (stair (X.levels (c + b) h')) x ≤ conjPart (stair (X.levels c h)) x ∧
      conjPart (stair (X.levels c h)) (x + 1) ≤ conjPart (stair (X.levels (c + b) h')) x :=
  X.conjPart_stair_horizontal hd c h h'
    (fun _ hv => by rw [X.mod_eq_val_of_mem_classOf hv]; exact hc) x

/-- The diagonal step out of a class whose residue is at least `a`. -/
lemma conjPart_step_le (hd : 0 < a + b) {N : ℕ} {c : ZMod (a + b)} (hc : a ≤ c.val)
    (h : (X.classOf c).card = N) (h' : (X.classOf (c + b)).card = N) (x : ℕ) :
    conjPart (stair (X.levels c h)) x ≤ conjPart (stair (X.levels (c + b) h')) x ∧
      conjPart (stair (X.levels (c + b) h')) (x + 1) ≤ conjPart (stair (X.levels c h)) x :=
  X.conjPart_stair_horizontal' hd c h h'
    (fun _ hv => by rw [X.mod_eq_val_of_mem_classOf hv]; exact hc) x

/-- Passing from a class to the next one lowers the conjugate staircase, the level index rising
by one exactly when the residue of the class is at least `a`. -/
lemma conjPart_step (hd : 0 < a + b) {N : ℕ}
    (hN : ∀ c : ZMod (a + b), (X.classOf c).card = N) (c : ZMod (a + b)) (x y : ℕ)
    (h : (c.val < a ∧ y = x) ∨ (a ≤ c.val ∧ y = x + 1)) :
    conjPart (stair (X.levels (c + b) (hN (c + b)))) y
      ≤ conjPart (stair (X.levels c (hN c))) x := by
  rcases h with ⟨hc, hy⟩ | ⟨hc, hy⟩
  · rw [hy]; exact (X.conjPart_step_lt hd hc (hN c) (hN (c + b)) x).1
  · rw [hy]; exact (X.conjPart_step_le hd hc (hN c) (hN (c + b)) x).2

/-- Passing from a class to the previous one lowers the conjugate staircase, the level index
rising by one exactly when the residue of the class is below `a`. -/
lemma conjPart_step' (hd : 0 < a + b) {N : ℕ}
    (hN : ∀ c : ZMod (a + b), (X.classOf c).card = N) (c : ZMod (a + b)) (x y : ℕ)
    (h : (a ≤ c.val ∧ y = x) ∨ (c.val < a ∧ y = x + 1)) :
    conjPart (stair (X.levels c (hN c))) y
      ≤ conjPart (stair (X.levels (c + b) (hN (c + b)))) x := by
  rcases h with ⟨hc, hy⟩ | ⟨hc, hy⟩
  · rw [hy]; exact (X.conjPart_step_le hd hc (hN c) (hN (c + b)) x).1
  · rw [hy]; exact (X.conjPart_step_lt hd hc (hN c) (hN (c + b)) x).2

/-- The diagonal reading of the collection: the value at the position `w` is the `⌊w/d⌋`-th part
of the conjugate of the staircase partition of the residue class of `w`. -/
noncomputable def diagValue {N : ℕ} (hN : ∀ c : ZMod (a + b), (X.classOf c).card = N) (w : ℕ) :
    ℕ := conjPart (stair (X.levels ((w : ℕ) : ZMod (a + b)) (hN _))) (w / (a + b))

/-- The diagonal reading in terms of the residue class and the level of a position. -/
lemma diagValue_eq {N : ℕ} (hN : ∀ c : ZMod (a + b), (X.classOf c).card = N) {w : ℕ}
    {c : ZMod (a + b)} (hc : ((w : ℕ) : ZMod (a + b)) = c) {x : ℕ} (hx : w / (a + b) = x) :
    X.diagValue hN w = conjPart (stair (X.levels c (hN c))) x := by
  subst hc; subst hx; rfl

/-- Every value of the diagonal reading is at most `N`. -/
lemma diagValue_le (hd : 0 < a + b) {N : ℕ} (hN : ∀ c : ZMod (a + b), (X.classOf c).card = N)
    (w : ℕ) : X.diagValue hN w ≤ N :=
  conjPart_le (X.isPartitionUpTo_stair_levels hd _ (hN _)) _

/-- The residues `a` and `b` are opposite modulo `d = a + b`. -/
lemma natCast_add_eq_zero : ((a : ZMod (a + b))) + (b : ZMod (a + b)) = 0 := by
  have h := ZMod.natCast_self (a + b)
  push_cast at h
  exact h

/-- Stepping a diagonal position up by `b`, the edge `v → v + b` of the graph, does not increase
the value of the diagonal reading. -/
lemma diagValue_add_right (hd : 0 < a + b) {N : ℕ}
    (hN : ∀ c : ZMod (a + b), (X.classOf c).card = N) (w : ℕ) :
    X.diagValue hN (w + b) ≤ X.diagValue hN w := by
  have hcb : ((w + b : ℕ) : ZMod (a + b)) = ((w : ℕ) : ZMod (a + b)) + (b : ZMod (a + b)) := by
    push_cast; ring
  have hval : (((w : ℕ) : ZMod (a + b))).val = w % (a + b) := ZMod.val_natCast _ _
  have hmod : (a + b) * (w / (a + b)) + w % (a + b) = w := Nat.div_add_mod w (a + b)
  have hlt : w % (a + b) < a + b := Nat.mod_lt _ hd
  rw [X.diagValue_eq hN hcb (x := (w + b) / (a + b)) rfl,
    X.diagValue_eq hN (c := ((w : ℕ) : ZMod (a + b))) rfl (x := w / (a + b)) rfl]
  refine X.conjPart_step hd hN _ _ _ ?_
  rcases Nat.lt_or_ge (w % (a + b)) a with hcase | hcase
  · refine Or.inl ⟨by rw [hval]; exact hcase, ?_⟩
    have hw : w + b = (a + b) * (w / (a + b)) + (w % (a + b) + b) := by omega
    rw [hw, (div_mod_eq_of_lt hd (show w % (a + b) + b < a + b by omega)).1]
  · refine Or.inr ⟨by rw [hval]; exact hcase, ?_⟩
    have hw : w + b = (a + b) * (w / (a + b) + 1) + (w % (a + b) - a) := by
      have : (a + b) * (w / (a + b) + 1) = (a + b) * (w / (a + b)) + (a + b) := by ring
      omega
    rw [hw, (div_mod_eq_of_lt hd (show w % (a + b) - a < a + b by omega)).1]

/-- Stepping a diagonal position up by `a`, the edge `v → v - a` of the graph read backwards,
does not increase the value of the diagonal reading. -/
lemma diagValue_add_left (hd : 0 < a + b) {N : ℕ}
    (hN : ∀ c : ZMod (a + b), (X.classOf c).card = N) (w : ℕ) :
    X.diagValue hN (w + a) ≤ X.diagValue hN w := by
  have hcb : ((w : ℕ) : ZMod (a + b))
      = ((w + a : ℕ) : ZMod (a + b)) + (b : ZMod (a + b)) := by
    have h := natCast_add_eq_zero (a := a) (b := b)
    push_cast
    linear_combination -h
  have hval : (((w + a : ℕ) : ZMod (a + b))).val = (w + a) % (a + b) := ZMod.val_natCast _ _
  have hmod : (a + b) * (w / (a + b)) + w % (a + b) = w := Nat.div_add_mod w (a + b)
  have hlt : w % (a + b) < a + b := Nat.mod_lt _ hd
  rw [X.diagValue_eq hN (c := ((w + a : ℕ) : ZMod (a + b))) rfl (x := (w + a) / (a + b)) rfl,
    X.diagValue_eq hN hcb (x := w / (a + b)) rfl]
  refine X.conjPart_step' hd hN _ _ _ ?_
  rcases Nat.lt_or_ge (w % (a + b)) b with hcase | hcase
  · have hw : w + a = (a + b) * (w / (a + b)) + (w % (a + b) + a) := by omega
    obtain ⟨hq, hr⟩ := div_mod_eq_of_lt hd (show w % (a + b) + a < a + b by omega)
    exact Or.inl ⟨by rw [hval, hw, hr]; omega, by rw [hw, hq]⟩
  · have hw : w + a = (a + b) * (w / (a + b) + 1) + (w % (a + b) - b) := by
      have : (a + b) * (w / (a + b) + 1) = (a + b) * (w / (a + b)) + (a + b) := by ring
      omega
    obtain ⟨hq, hr⟩ := div_mod_eq_of_lt hd (show w % (a + b) - b < a + b by omega)
    exact Or.inr ⟨by rw [hval, hw, hr]; omega, by rw [hw, hq]⟩

/-- A common bound for the largest part of the staircase partition of every residue class. -/
lemma exists_stair_le [NeZero (a + b)] {N : ℕ}
    (hN : ∀ c : ZMod (a + b), (X.classOf c).card = N) :
    ∃ B, ∀ c : ZMod (a + b), stair (X.levels c (hN c)) 0 ≤ B :=
  ⟨(univ : Finset (ZMod (a + b))).sup fun c => stair (X.levels c (hN c)) 0,
    fun c => Finset.le_sup (f := fun c => stair (X.levels c (hN c)) 0) (mem_univ c)⟩

/-- The diagonal reading vanishes at every position beyond `d` times a bound on the staircase
partitions of the residue classes. -/
lemma diagValue_eq_zero (hd : 0 < a + b) {N B : ℕ}
    (hN : ∀ c : ZMod (a + b), (X.classOf c).card = N)
    (hB : ∀ c : ZMod (a + b), stair (X.levels c (hN c)) 0 ≤ B) {w : ℕ} (hw : (a + b) * B ≤ w) :
    X.diagValue hN w = 0 := by
  rw [X.diagValue_eq hN (c := ((w : ℕ) : ZMod (a + b))) rfl (x := w / (a + b)) rfl]
  refine conjPart_eq_zero (X.isPartitionUpTo_stair_levels hd _ (hN _)) ?_
  exact le_trans (hB _) ((Nat.le_div_iff_mul_le hd).2 (by rw [Nat.mul_comm]; exact hw))

/-- The diagonal reading of a cycle collection is a diagonal function bounded by `N`. -/
theorem isDiagFun_diagValue [NeZero (a + b)] (hd : 0 < a + b) {N : ℕ}
    (hN : ∀ c : ZMod (a + b), (X.classOf c).card = N) : IsDiagFun a b N (X.diagValue hN) where
  step_left := X.diagValue_add_left hd hN
  step_right := X.diagValue_add_right hd hN
  le_bound := X.diagValue_le hd hN
  vanish := by
    obtain ⟨B, hB⟩ := X.exists_stair_le hN
    exact ⟨(a + b) * B, fun _ hw => X.diagValue_eq_zero hd hN hB hw⟩

/-- The total of the diagonal reading is the total size of the `d` staircase partitions of the
residue classes. -/
theorem finsum_diagValue [NeZero (a + b)] (hd : 0 < a + b) {N : ℕ}
    (hN : ∀ c : ZMod (a + b), (X.classOf c).card = N) :
    (∑ᶠ w, X.diagValue hN w) = ∑ c : ZMod (a + b), ∑ k ∈ range N, stair (X.levels c (hN c)) k := by
  obtain ⟨B, hB⟩ := X.exists_stair_le hN
  have hterm : ∀ x : ℕ, ∀ r ∈ range (a + b), X.diagValue hN (r + (a + b) * x)
      = conjPart (stair (X.levels ((r : ℕ) : ZMod (a + b)) (hN _))) x := by
    intro x r hr
    rw [mem_range] at hr
    refine X.diagValue_eq hN ?_ ?_
    · rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero]
    · rw [Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt hr, Nat.zero_add]
  calc (∑ᶠ w, X.diagValue hN w)
      = ∑ w ∈ range ((a + b) * (B + 1)), X.diagValue hN w := by
        refine finsum_eq_finsetSum_of_support_subset _ fun w hw => ?_
        simp only [Function.mem_support] at hw
        rw [Finset.mem_coe, mem_range]
        by_contra hcon
        refine hw (X.diagValue_eq_zero hd hN hB ?_)
        have : (a + b) * B ≤ (a + b) * (B + 1) := Nat.mul_le_mul_left _ (by omega)
        omega
    _ = ∑ x ∈ range (B + 1), ∑ r ∈ range (a + b), X.diagValue hN (r + (a + b) * x) :=
        sum_range_mul_split _ _ _
    _ = ∑ x ∈ range (B + 1), ∑ c : ZMod (a + b),
          conjPart (stair (X.levels c (hN c))) x := by
        refine sum_congr rfl fun x _ => ?_
        rw [sum_congr rfl (hterm x)]
        exact (sum_zmod_eq_sum_range (a + b)
          (fun c => conjPart (stair (X.levels c (hN c))) x)).symm
    _ = ∑ c : ZMod (a + b), ∑ x ∈ range (B + 1),
          conjPart (stair (X.levels c (hN c))) x := sum_comm
    _ = ∑ c : ZMod (a + b), ∑ k ∈ range N, stair (X.levels c (hN c)) k :=
        sum_congr rfl fun c _ => sum_range_conjPart
          (X.isPartitionUpTo_stair_levels hd c (hN c)) (le_trans (hB c) (by omega))

/-! ### A collection is determined by its diagonal reading -/

/-- The diagonal reading at the position `c.val + dx` is the `x`-th part of the conjugate
staircase of the class `c`. -/
lemma diagValue_val_add [NeZero (a + b)] (hd : 0 < a + b) {N : ℕ}
    (hN : ∀ c : ZMod (a + b), (X.classOf c).card = N) (c : ZMod (a + b)) (x : ℕ) :
    X.diagValue hN (c.val + (a + b) * x) = conjPart (stair (X.levels c (hN c))) x := by
  refine X.diagValue_eq hN ?_ ?_
  · rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero]
    exact ZMod.natCast_rightInverse c
  · rw [Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt (ZMod.val_lt c), Nat.zero_add]

/-- The occupied vertices of a residue class are recovered from its levels. -/
lemma image_levels_eq_classOf [NeZero (a + b)] {N : ℕ} (c : ZMod (a + b))
    (h : (X.classOf c).card = N) :
    (univ : Finset (Fin N)).image (fun k => (a + b) * X.levels c h k + c.val) = X.classOf c := by
  refine Eq.trans ?_ (Finset.image_orderEmbOfFin_univ (X.classOf c) h)
  refine Finset.image_congr fun k _ => ?_
  have hmem := Finset.orderEmbOfFin_mem (X.classOf c) h k
  have hmod := X.mod_eq_val_of_mem_classOf hmem
  have hdm := Nat.div_add_mod ((X.classOf c).orderEmbOfFin h k) (a + b)
  simp only [levels]
  omega

/-- The occupied set is the union of the residue classes. -/
lemma occupied_eq_biUnion [NeZero (a + b)] :
    X.occupied = (univ : Finset (ZMod (a + b))).biUnion X.classOf := by
  ext v
  rw [Finset.mem_biUnion]
  refine ⟨fun hv => ⟨((v : ℕ) : ZMod (a + b)), mem_univ _, X.mem_classOf.2 ⟨hv, rfl⟩⟩, ?_⟩
  rintro ⟨c, -, hc⟩
  exact (X.mem_classOf.1 hc).1

/-- Two collections with the same diagonal reading have the same levels in every class. -/
theorem levels_eq_of_diagValue_eq [NeZero (a + b)] (hd : 0 < a + b) (Y : CycleSystem a b) {N : ℕ}
    (hN : ∀ c : ZMod (a + b), (X.classOf c).card = N)
    (hM : ∀ c : ZMod (a + b), (Y.classOf c).card = N)
    (h : X.diagValue hN = Y.diagValue hM) (c : ZMod (a + b)) :
    X.levels c (hN c) = Y.levels c (hM c) := by
  refine stair_injective (X.strictMono_levels hd c (hN c)) (Y.strictMono_levels hd c (hM c)) ?_
  refine conjPart_injective (isPartitionUpTo_stair (X.strictMono_levels hd c (hN c)))
    (isPartitionUpTo_stair (Y.strictMono_levels hd c (hM c))) ?_
  funext x
  rw [← X.diagValue_val_add hd hN c x, ← Y.diagValue_val_add hd hM c x, h]

/-- A collection is determined by its diagonal reading. -/
theorem occupied_eq_of_diagValue_eq [NeZero (a + b)] (hd : 0 < a + b) (Y : CycleSystem a b)
    {N : ℕ} (hN : ∀ c : ZMod (a + b), (X.classOf c).card = N)
    (hM : ∀ c : ZMod (a + b), (Y.classOf c).card = N)
    (h : X.diagValue hN = Y.diagValue hM) : X.occupied = Y.occupied := by
  rw [X.occupied_eq_biUnion, Y.occupied_eq_biUnion]
  refine Finset.biUnion_congr rfl fun c _ => ?_
  rw [← X.image_levels_eq_classOf c (hN c), ← Y.image_levels_eq_classOf c (hM c),
    X.levels_eq_of_diagValue_eq hd Y hN hM h c]

/-! ### The cylindric partition read off the diagonals -/

/-- The cylindric partition read off the diagonals of the collection: the entry in row `i` and
column `j` is the diagonal reading at the position `ib mod a + aj`. -/
noncomputable def cylOf {N : ℕ} (hN : ∀ c : ZMod (a + b), (X.classOf c).card = N) (i j : ℕ) :
    ℕ := cylOfDiag a b (X.diagValue hN) i j

/-- The diagonal reading of a collection presented as an array. -/
lemma cylOf_eq {N : ℕ} (hN : ∀ c : ZMod (a + b), (X.classOf c).card = N) :
    X.cylOf hN = cylOfDiag a b (X.diagValue hN) := rfl

/-- The diagonal reading of a cycle collection whose residue classes all carry `N` occupied
vertices is a cylindric partition with the balanced profile. -/
theorem isCylindric_cylOf [NeZero (a + b)] (ha : 0 < a) {N : ℕ}
    (hN : ∀ c : ZMod (a + b), (X.classOf c).card = N) :
    HJO.Cylindric.IsCylindric a (HJO.Cylindric.profile a b) (X.cylOf hN) :=
  isCylindric_cylOfDiag ha (X.isDiagFun_diagValue (by omega) hN)

/-- Every entry of the diagonal reading is at most `N`. -/
theorem boundedBy_cylOf [NeZero (a + b)] (hd : 0 < a + b) {N : ℕ}
    (hN : ∀ c : ZMod (a + b), (X.classOf c).card = N) :
    HJO.Cylindric.BoundedBy N (X.cylOf hN) :=
  boundedBy_cylOfDiag (X.isDiagFun_diagValue hd hN)

/-- The volume of the cylindric partition read off the diagonals is the total size of the `d`
staircase partitions of the residue classes. -/
theorem cylVolume_cylOf [NeZero (a + b)] (hab : Nat.Coprime a b) (ha : 0 < a) {N : ℕ}
    (hN : ∀ c : ZMod (a + b), (X.classOf c).card = N) :
    HJO.Cylindric.cylVolume a (X.cylOf hN)
      = ∑ c : ZMod (a + b), ∑ k ∈ range N, stair (X.levels c (hN c)) k := by
  rw [X.cylOf_eq hN, cylVolume_cylOfDiag hab ha (X.isDiagFun_diagValue (by omega) hN),
    X.finsum_diagValue (by omega) hN]

/-- A collection is determined by the cylindric partition read off its diagonals: the occupied
sets agree, and hence so do the successor maps. -/
theorem occupied_eq_of_cylOf_eq [NeZero (a + b)] (hab : Nat.Coprime a b) (ha : 0 < a)
    (Y : CycleSystem a b) {N : ℕ} (hN : ∀ c : ZMod (a + b), (X.classOf c).card = N)
    (hM : ∀ c : ZMod (a + b), (Y.classOf c).card = N) (h : X.cylOf hN = Y.cylOf hM) :
    X.occupied = Y.occupied := by
  refine X.occupied_eq_of_diagValue_eq (by omega) Y hN hM ?_
  rw [← diagOfCyl_cylOfDiag hab ha (X.diagValue hN),
    ← diagOfCyl_cylOfDiag hab ha (Y.diagValue hM), ← X.cylOf_eq hN, ← Y.cylOf_eq hM, h]

/-- The weight of a cycle collection is the rank shift `γ_N` plus the volume of the cylindric
partition read off its diagonals. -/
theorem weightExp_eq_gammaShift_add_cylVolume [NeZero (a + b)] (hab : Nat.Coprime a b)
    (ha : 0 < a) (hb : 0 < b) {N : ℕ}
    (hN : ∀ c : ZMod (a + b), (X.classOf c).card = N) :
    X.weightExp = Paths.gammaShift a b N + HJO.Cylindric.cylVolume a (X.cylOf hN) := by
  rw [X.cylVolume_cylOf hab ha hN, X.weightExp_eq_gammaShift_add ha hb hN]

end CycleSystem

/-! ### Recovering a collection from a diagonal function -/

/-- Conjugation is an involution on partitions. -/
lemma conjPart_conjPart {M : ℕ} {l : ℕ → ℕ} (hl : IsPartitionUpTo M l) :
    conjPart (conjPart l) = l := by
  funext i
  have key : ∀ j, conjPart (conjPart l) i ≤ j ↔ l i ≤ j := fun j =>
    (conjPart_le_iff (isPartitionUpTo_conjPart hl) i j).trans (conjPart_le_iff hl j i)
  have h1 := (key (l i)).2 le_rfl
  have h2 := (key (conjPart (conjPart l) i)).1 le_rfl
  omega

/-- Conjugation exchanges horizontal and vertical strips: from a horizontal strip between `m` and
`l` the conjugates differ by at most one in each part. -/
lemma conjPart_vertical {M M' : ℕ} {l m : ℕ → ℕ} (hl : IsPartitionUpTo M l)
    (hm : IsPartitionUpTo M' m) (h1 : ∀ x, m x ≤ l x) (h2 : ∀ x, l (x + 1) ≤ m x) (y : ℕ) :
    conjPart m y ≤ conjPart l y ∧ conjPart l y ≤ conjPart m y + 1 :=
  ⟨(conjPart_le_iff hm y _).2 (le_trans (h1 _) (apply_conjPart_le hl y)),
    (conjPart_le_iff hl y _).2 (le_trans (h2 _) (apply_conjPart_le hm y))⟩

/-- Moving a diagonal position up by `d = a + b` does not increase the value. -/
lemma IsDiagFun.step_add {a b N : ℕ} {W : ℕ → ℕ} (hW : IsDiagFun a b N W) (u : ℕ) :
    W (u + (a + b)) ≤ W u := by
  have h : u + (a + b) = u + a + b := by omega
  rw [h]
  exact le_trans (hW.step_right _) (hW.step_left u)

/-- The diagonal slice of a diagonal function in the residue class `c`: the values along the
positions congruent to `c`. -/
def diagSlice (a b : ℕ) (W : ℕ → ℕ) (c : ZMod (a + b)) (x : ℕ) : ℕ := W (c.val + (a + b) * x)

/-- Every diagonal slice is a partition. -/
lemma isPartitionUpTo_diagSlice {a b N : ℕ} {W : ℕ → ℕ} (hd : 0 < a + b)
    (hW : IsDiagFun a b N W) (c : ZMod (a + b)) :
    ∃ M, IsPartitionUpTo M (diagSlice a b W c) := by
  obtain ⟨B, hB⟩ := hW.vanish
  refine ⟨B, antitone_nat_of_succ_le fun x => ?_, fun x hx => hB _ ?_⟩
  · have h : c.val + (a + b) * (x + 1) = c.val + (a + b) * x + (a + b) := by ring
    simp only [diagSlice, h]
    exact hW.step_add _
  · have h2 : x ≤ (a + b) * x := Nat.le_mul_of_pos_left x hd
    omega

/-- The conjugate of a diagonal slice: a partition with at most `N` parts. -/
noncomputable def diagPart (a b : ℕ) (W : ℕ → ℕ) (c : ZMod (a + b)) : ℕ → ℕ :=
  conjPart (diagSlice a b W c)

/-- The conjugate diagonal slice has at most `N` parts. -/
lemma isPartitionUpTo_diagPart {a b N : ℕ} {W : ℕ → ℕ} (hd : 0 < a + b)
    (hW : IsDiagFun a b N W) (c : ZMod (a + b)) : IsPartitionUpTo N (diagPart a b W c) := by
  obtain ⟨M, hM⟩ := isPartitionUpTo_diagSlice hd hW c
  refine ⟨(isPartitionUpTo_conjPart hM).antitone, fun y hy => ?_⟩
  exact Nat.le_zero.1 ((conjPart_le_iff hM y 0).2 (le_trans (hW.le_bound _) hy))

/-- The levels of the residue class `c` recovered from a diagonal function: the conjugate
diagonal slice with the staircase added back. -/
noncomputable def diagLevel (a b N : ℕ) (W : ℕ → ℕ) (c : ZMod (a + b)) (i : ℕ) : ℕ :=
  diagPart a b W c (N - 1 - i) + i

/-- The recovered levels increase strictly. -/
lemma strictMono_diagLevel {a b N : ℕ} {W : ℕ → ℕ} (hd : 0 < a + b) (hW : IsDiagFun a b N W)
    (c : ZMod (a + b)) : StrictMono (diagLevel a b N W c) := by
  intro i i' hii
  have h := (isPartitionUpTo_diagPart hd hW c).antitone
    (show N - 1 - i' ≤ N - 1 - i by omega)
  simp only [diagLevel]
  omega

/-- The staircase subtraction of the recovered levels is the conjugate diagonal slice. -/
lemma stair_diagLevel {a b N : ℕ} {W : ℕ → ℕ} (hd : 0 < a + b) (hW : IsDiagFun a b N W)
    (c : ZMod (a + b)) :
    stair (fun k : Fin N => diagLevel a b N W c (k : ℕ)) = diagPart a b W c := by
  funext j
  by_cases hj : j < N
  · have h' : N - 1 - j < N := by omega
    rw [stair_of_lt _ hj h']
    have hval : N - 1 - (N - 1 - j) = j := by omega
    simp only [diagLevel, hval]
    omega
  · rw [stair_of_le _ (by omega)]
    exact ((isPartitionUpTo_diagPart hd hW c).vanish j (by omega)).symm

/-- The residue of the next class, when the residue of the class is below `a`. -/
lemma val_add_natCast_of_lt {a b : ℕ} [NeZero (a + b)] {c : ZMod (a + b)}
    (hc : c.val < a) : (c + (b : ZMod (a + b))).val = c.val + b := by
  rw [ZMod.val_add, ZMod.val_natCast, Nat.mod_eq_of_lt (show b < a + b by omega),
    Nat.mod_eq_of_lt (by omega)]

/-- The residue of the next class, when the residue of the class is at least `a`. -/
lemma val_add_natCast_of_le {a b : ℕ} [NeZero (a + b)] (ha : 0 < a) {c : ZMod (a + b)}
    (hc : a ≤ c.val) : (c + (b : ZMod (a + b))).val = c.val - a := by
  have hlt : c.val < a + b := ZMod.val_lt c
  rw [ZMod.val_add, ZMod.val_natCast, Nat.mod_eq_of_lt (show b < a + b by omega)]
  rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

/-- Below `a` the conjugate diagonal slice of the next class is contained in that of the class,
and the two differ by at most one in each part. -/
lemma diagPart_step_lt {a b N : ℕ} [NeZero (a + b)] {W : ℕ → ℕ}
    (hW : IsDiagFun a b N W) {c : ZMod (a + b)} (hc : c.val < a) (y : ℕ) :
    diagPart a b W (c + b) y ≤ diagPart a b W c y ∧
      diagPart a b W c y ≤ diagPart a b W (c + b) y + 1 := by
  have hd : 0 < a + b := by omega
  obtain ⟨M, hM⟩ := isPartitionUpTo_diagSlice hd hW c
  obtain ⟨M', hM'⟩ := isPartitionUpTo_diagSlice hd hW (c + b)
  have hval := val_add_natCast_of_lt hc
  refine conjPart_vertical hM hM' (fun x => ?_) (fun x => ?_) y
  · have h : (c + (b : ZMod (a + b))).val + (a + b) * x = c.val + (a + b) * x + b := by
      rw [hval]; ring
    simp only [diagSlice, h]
    exact hW.step_right _
  · have h : c.val + (a + b) * (x + 1) = (c + (b : ZMod (a + b))).val + (a + b) * x + a := by
      rw [hval]; ring
    simp only [diagSlice, h]
    exact hW.step_left _

/-- At or above `a` the conjugate diagonal slice of the class is contained in that of the next
one, and the two differ by at most one in each part. -/
lemma diagPart_step_le {a b N : ℕ} [NeZero (a + b)] (ha : 0 < a) {W : ℕ → ℕ}
    (hW : IsDiagFun a b N W) {c : ZMod (a + b)} (hc : a ≤ c.val) (y : ℕ) :
    diagPart a b W c y ≤ diagPart a b W (c + b) y ∧
      diagPart a b W (c + b) y ≤ diagPart a b W c y + 1 := by
  have hd : 0 < a + b := by omega
  obtain ⟨M, hM⟩ := isPartitionUpTo_diagSlice hd hW c
  obtain ⟨M', hM'⟩ := isPartitionUpTo_diagSlice hd hW (c + b)
  have hval := val_add_natCast_of_le ha hc
  refine conjPart_vertical hM' hM (fun x => ?_) (fun x => ?_) y
  · have h : c.val + (a + b) * x = (c + (b : ZMod (a + b))).val + (a + b) * x + a := by
      rw [hval]; omega
    simp only [diagSlice, h]
    exact hW.step_left _
  · have h : (c + (b : ZMod (a + b))).val + (a + b) * (x + 1) = c.val + (a + b) * x + b := by
      rw [hval]
      have : (a + b) * (x + 1) = (a + b) * x + (a + b) := by ring
      omega
    simp only [diagSlice, h]
    exact hW.step_right _

/-! ### The collection recovered from a diagonal function -/

/-- The occupied set recovered from a diagonal function: in each residue class the `N` levels of
that class. -/
noncomputable def diagOccupied (a b N : ℕ) [NeZero (a + b)] (W : ℕ → ℕ) : Finset ℕ :=
  (univ : Finset (ZMod (a + b))).biUnion fun c =>
    (univ : Finset (Fin N)).image fun k : Fin N => (a + b) * diagLevel a b N W c (k : ℕ) + c.val

/-- Membership in the recovered occupied set. -/
lemma mem_diagOccupied {a b N : ℕ} [NeZero (a + b)] (W : ℕ → ℕ) (v : ℕ) :
    v ∈ diagOccupied a b N W ↔
      ∃ (c : ZMod (a + b)) (k : ℕ), k < N ∧ v = (a + b) * diagLevel a b N W c k + c.val := by
  simp only [diagOccupied, Finset.mem_biUnion, Finset.mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨c, k, hk⟩
    exact ⟨c, (k : ℕ), k.isLt, hk.symm⟩
  · rintro ⟨c, k, hk, hv⟩
    exact ⟨c, ⟨k, hk⟩, hv.symm⟩

/-- The index of a level inside its residue class. -/
noncomputable def diagIndex (a b N : ℕ) (W : ℕ → ℕ) (c : ZMod (a + b)) (m : ℕ) : ℕ :=
  #{k ∈ range N | diagLevel a b N W c k < m}

/-- The index of the `k`-th level is `k`. -/
lemma diagIndex_diagLevel {a b N : ℕ} {W : ℕ → ℕ} (hd : 0 < a + b) (hW : IsDiagFun a b N W)
    (c : ZMod (a + b)) {k : ℕ} (hk : k < N) :
    diagIndex a b N W c (diagLevel a b N W c k) = k := by
  have hmono := strictMono_diagLevel hd hW c
  have hset : {k' ∈ range N | diagLevel a b N W c k' < diagLevel a b N W c k} = range k := by
    ext k'
    simp only [mem_filter, mem_range]
    exact ⟨fun h => hmono.lt_iff_lt.1 h.2, fun h => ⟨by omega, hmono (by omega)⟩⟩
  rw [diagIndex, hset, card_range]

/-- The successor map recovered from a diagonal function: the level of the same index in the next
residue class. -/
noncomputable def diagSucc (a b N : ℕ) [NeZero (a + b)] (W : ℕ → ℕ) (v : ℕ) : ℕ :=
  (a + b) * diagLevel a b N W (((v : ℕ) : ZMod (a + b)) + b)
      (diagIndex a b N W ((v : ℕ) : ZMod (a + b)) (v / (a + b)))
    + (((v : ℕ) : ZMod (a + b)) + b).val

/-- The residue class of a recovered occupied vertex. -/
lemma natCast_mul_add_val {a b : ℕ} [NeZero (a + b)] (c : ZMod (a + b)) (L : ℕ) :
    (((a + b) * L + c.val : ℕ) : ZMod (a + b)) = c := by
  rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, zero_add]
  exact ZMod.natCast_rightInverse c

/-- The level of a recovered occupied vertex. -/
lemma div_mul_add_val {a b : ℕ} [NeZero (a + b)] (hd : 0 < a + b) (c : ZMod (a + b)) (L : ℕ) :
    ((a + b) * L + c.val) / (a + b) = L := (div_mod_eq_of_lt hd (ZMod.val_lt c)).1

/-- A number written as `n q + r` with `r < n` determines `q` and `r`. -/
lemma eq_of_mul_add_eq {n L r L' r' : ℕ} (hn : 0 < n) (hr : r < n) (hr' : r' < n)
    (h : n * L + r = n * L' + r') : L = L' ∧ r = r' := by
  obtain ⟨h1, h2⟩ := div_mod_eq_of_lt hn hr
  obtain ⟨h3, h4⟩ := div_mod_eq_of_lt hn hr'
  rw [h] at h1 h2
  exact ⟨h1.symm.trans h3, h2.symm.trans h4⟩

/-- The recovered successor of a recovered occupied vertex is the level of the same index in the
next residue class. -/
lemma diagSucc_apply {a b N : ℕ} [NeZero (a + b)] (hd : 0 < a + b) {W : ℕ → ℕ}
    (hW : IsDiagFun a b N W) (c : ZMod (a + b)) {k : ℕ} (hk : k < N) :
    diagSucc a b N W ((a + b) * diagLevel a b N W c k + c.val)
      = (a + b) * diagLevel a b N W (c + b) k + (c + b).val := by
  simp only [diagSucc, natCast_mul_add_val, div_mul_add_val hd,
    diagIndex_diagLevel hd hW c hk]

/-- Along the recovered successor the level of a class either stays put or moves by one, so the
step is one of the two graph edges. -/
lemma diagSucc_step {a b N : ℕ} [NeZero (a + b)] (ha : 0 < a) (hb : 0 < b) {W : ℕ → ℕ}
    (hW : IsDiagFun a b N W) (c : ZMod (a + b)) {k : ℕ} (hk : k < N) :
    diagSucc a b N W ((a + b) * diagLevel a b N W c k + c.val)
        = (a + b) * diagLevel a b N W c k + c.val + b ∨
      a ≤ (a + b) * diagLevel a b N W c k + c.val ∧
        diagSucc a b N W ((a + b) * diagLevel a b N W c k + c.val)
          = (a + b) * diagLevel a b N W c k + c.val - a := by
  have hd : 0 < a + b := by omega
  have hcv : c.val < a + b := ZMod.val_lt c
  rw [diagSucc_apply hd hW c hk]
  rcases Nat.lt_or_ge c.val a with hc | hc
  · have hv := val_add_natCast_of_lt hc
    have hstep := diagPart_step_lt hW hc (N - 1 - k)
    have hL : diagLevel a b N W (c + b) k ≤ diagLevel a b N W c k ∧
        diagLevel a b N W c k ≤ diagLevel a b N W (c + b) k + 1 := by
      simp only [diagLevel]; omega
    rcases (show diagLevel a b N W (c + b) k = diagLevel a b N W c k ∨
        diagLevel a b N W c k = diagLevel a b N W (c + b) k + 1 from by omega) with h | h
    · left; rw [hv, h]; omega
    · have hmul : (a + b) * diagLevel a b N W c k
          = (a + b) * diagLevel a b N W (c + b) k + (a + b) := by rw [h]; ring
      exact Or.inr ⟨by omega, by rw [hv]; omega⟩
  · have hv := val_add_natCast_of_le ha hc
    have hstep := diagPart_step_le ha hW hc (N - 1 - k)
    have hL : diagLevel a b N W c k ≤ diagLevel a b N W (c + b) k ∧
        diagLevel a b N W (c + b) k ≤ diagLevel a b N W c k + 1 := by
      simp only [diagLevel]; omega
    rcases (show diagLevel a b N W (c + b) k = diagLevel a b N W c k ∨
        diagLevel a b N W (c + b) k = diagLevel a b N W c k + 1 from by omega) with h | h
    · exact Or.inr ⟨by omega, by rw [hv, h]; omega⟩
    · have hmul : (a + b) * diagLevel a b N W (c + b) k
          = (a + b) * diagLevel a b N W c k + (a + b) := by rw [h]; ring
      left; rw [hv]; omega

/-- The recovered successor of a recovered occupied vertex is occupied. -/
lemma diagSucc_mem {a b N : ℕ} [NeZero (a + b)] (hd : 0 < a + b) {W : ℕ → ℕ}
    (hW : IsDiagFun a b N W) (c : ZMod (a + b)) {k : ℕ} (hk : k < N) :
    diagSucc a b N W ((a + b) * diagLevel a b N W c k + c.val) ∈ diagOccupied a b N W := by
  rw [diagSucc_apply hd hW c hk]
  exact (mem_diagOccupied W _).2 ⟨c + b, k, hk, rfl⟩

/-- The recovered successor is injective on the recovered occupied set: the cycles are
vertex-disjoint. -/
lemma diagSucc_injOn {a b N : ℕ} [NeZero (a + b)] (hd : 0 < a + b) {W : ℕ → ℕ}
    (hW : IsDiagFun a b N W) : ∀ v ∈ diagOccupied a b N W, ∀ v' ∈ diagOccupied a b N W,
      diagSucc a b N W v = diagSucc a b N W v' → v = v' := by
  intro v hv v' hv' h
  obtain ⟨c, k, hk, rfl⟩ := (mem_diagOccupied W v).1 hv
  obtain ⟨c', k', hk', rfl⟩ := (mem_diagOccupied W v').1 hv'
  rw [diagSucc_apply hd hW c hk, diagSucc_apply hd hW c' hk'] at h
  obtain ⟨hL, hr⟩ := eq_of_mul_add_eq hd (ZMod.val_lt _) (ZMod.val_lt _) h
  have hcc : c = c' := add_right_cancel (ZMod.val_injective (a + b) hr)
  subst hcc
  have hkk : k = k' := (strictMono_diagLevel hd hW (c + (b : ZMod (a + b)))).injective hL
  subst hkk
  rfl

/-- The cycle collection recovered from a diagonal function bounded by `N`. -/
noncomputable def CycleSystem.ofDiag (a b N : ℕ) [NeZero (a + b)] (ha : 0 < a) (hb : 0 < b)
    (W : ℕ → ℕ) (hW : IsDiagFun a b N W) : CycleSystem a b where
  occupied := diagOccupied a b N W
  succ := diagSucc a b N W
  step := by
    intro v hv
    obtain ⟨c, k, hk, rfl⟩ := (mem_diagOccupied W v).1 hv
    exact diagSucc_step ha hb hW c hk
  succ_mem := by
    intro v hv
    obtain ⟨c, k, hk, rfl⟩ := (mem_diagOccupied W v).1 hv
    exact diagSucc_mem (by omega) hW c hk
  succ_inj := diagSucc_injOn (by omega) hW

/-- The residue classes of the recovered collection are the recovered levels. -/
theorem classOf_ofDiag {a b N : ℕ} [NeZero (a + b)] (ha : 0 < a) (hb : 0 < b) {W : ℕ → ℕ}
    (hW : IsDiagFun a b N W) (c : ZMod (a + b)) :
    (CycleSystem.ofDiag a b N ha hb W hW).classOf c = (univ : Finset (Fin N)).image
      fun k : Fin N => (a + b) * diagLevel a b N W c (k : ℕ) + c.val := by
  ext v
  rw [CycleSystem.mem_classOf, Finset.mem_image]
  constructor
  · rintro ⟨hv, hvc⟩
    obtain ⟨c', k, hk, rfl⟩ := (mem_diagOccupied W v).1 hv
    rw [natCast_mul_add_val] at hvc
    exact ⟨⟨k, hk⟩, mem_univ _, by rw [hvc]⟩
  · rintro ⟨k, -, rfl⟩
    exact ⟨(mem_diagOccupied W _).2 ⟨c, (k : ℕ), k.isLt, rfl⟩, natCast_mul_add_val c _⟩

/-- Each residue class of the recovered collection carries `N` occupied vertices. -/
theorem card_classOf_ofDiag {a b N : ℕ} [NeZero (a + b)] (ha : 0 < a) (hb : 0 < b) {W : ℕ → ℕ}
    (hW : IsDiagFun a b N W) (c : ZMod (a + b)) :
    ((CycleSystem.ofDiag a b N ha hb W hW).classOf c).card = N := by
  have hinj : Function.Injective
      fun k : Fin N => (a + b) * diagLevel a b N W c (k : ℕ) + c.val := by
    intro k k' hkk
    have hd : 0 < a + b := by omega
    obtain ⟨hL, -⟩ := eq_of_mul_add_eq hd (ZMod.val_lt c) (ZMod.val_lt c) hkk
    exact Fin.val_injective ((strictMono_diagLevel hd hW c).injective hL)
  rw [classOf_ofDiag ha hb hW c, Finset.card_image_of_injective _ hinj, card_univ,
    Fintype.card_fin]

/-- The levels of the recovered collection are the recovered levels. -/
theorem levels_ofDiag {a b N : ℕ} [NeZero (a + b)] (ha : 0 < a) (hb : 0 < b) {W : ℕ → ℕ}
    (hW : IsDiagFun a b N W)
    (hN : ∀ c : ZMod (a + b), ((CycleSystem.ofDiag a b N ha hb W hW).classOf c).card = N)
    (c : ZMod (a + b)) :
    (CycleSystem.ofDiag a b N ha hb W hW).levels c (hN c)
      = fun k : Fin N => diagLevel a b N W c (k : ℕ) := by
  have hd : 0 < a + b := by omega
  have hmem : ∀ k : Fin N, (a + b) * diagLevel a b N W c (k : ℕ) + c.val
      ∈ (CycleSystem.ofDiag a b N ha hb W hW).classOf c := by
    intro k
    rw [classOf_ofDiag ha hb hW c]
    exact Finset.mem_image.2 ⟨k, mem_univ _, rfl⟩
  have hmono : StrictMono fun k : Fin N => (a + b) * diagLevel a b N W c (k : ℕ) + c.val := by
    intro k k' hkk
    have hlt := strictMono_diagLevel hd hW c (Fin.lt_def.1 hkk)
    exact Nat.add_lt_add_right (mul_lt_mul_of_pos_left hlt hd) c.val
  have key := Finset.orderEmbOfFin_unique (hN c) hmem hmono
  funext k
  have hk : (a + b) * diagLevel a b N W c (k : ℕ) + c.val
      = (((CycleSystem.ofDiag a b N ha hb W hW).classOf c).orderEmbOfFin (hN c)) k :=
    congrFun key k
  simp only [CycleSystem.levels, ← hk]
  exact div_mul_add_val hd c _

/-- The diagonal reading of the recovered collection is the diagonal function it came from. -/
theorem diagValue_ofDiag {a b N : ℕ} [NeZero (a + b)] (ha : 0 < a) (hb : 0 < b) {W : ℕ → ℕ}
    (hW : IsDiagFun a b N W)
    (hN : ∀ c : ZMod (a + b), ((CycleSystem.ofDiag a b N ha hb W hW).classOf c).card = N) :
    (CycleSystem.ofDiag a b N ha hb W hW).diagValue hN = W := by
  have hd : 0 < a + b := by omega
  funext w
  rw [CycleSystem.diagValue_eq _ _ (c := ((w : ℕ) : ZMod (a + b))) rfl (x := w / (a + b)) rfl,
    levels_ofDiag ha hb hW hN, stair_diagLevel hd hW]
  obtain ⟨M, hM⟩ := isPartitionUpTo_diagSlice hd hW ((w : ℕ) : ZMod (a + b))
  rw [diagPart, conjPart_conjPart hM]
  have hval : (((w : ℕ) : ZMod (a + b))).val = w % (a + b) := ZMod.val_natCast _ _
  have hdm : (a + b) * (w / (a + b)) + w % (a + b) = w := Nat.div_add_mod w (a + b)
  simp only [diagSlice, hval]
  congr 1
  omega

/-- Every cylindric partition with the balanced profile whose entries are at most `N` is the
diagonal reading of a cycle collection each of whose residue classes carries `N` occupied
vertices, and the weight of that collection is the rank shift plus the volume. -/
theorem exists_cycleSystem_cylOf {a b N : ℕ} [NeZero (a + b)] (hab : Nat.Coprime a b)
    (ha : 0 < a) (hb : 0 < b) {l : ℕ → ℕ → ℕ}
    (hl : HJO.Cylindric.IsCylindric a (HJO.Cylindric.profile a b) l)
    (hbd : HJO.Cylindric.BoundedBy N l) :
    ∃ (X : CycleSystem a b) (hN : ∀ c : ZMod (a + b), (X.classOf c).card = N),
      X.cylOf hN = l ∧ X.weightExp = Paths.gammaShift a b N + HJO.Cylindric.cylVolume a l := by
  have hW := isDiagFun_diagOfCyl hab ha hl hbd
  have hN : ∀ c : ZMod (a + b),
      ((CycleSystem.ofDiag a b N ha hb (diagOfCyl a b l) hW).classOf c).card = N :=
    fun c => card_classOf_ofDiag ha hb hW c
  have hcyl : (CycleSystem.ofDiag a b N ha hb (diagOfCyl a b l) hW).cylOf hN = l := by
    rw [CycleSystem.cylOf_eq, diagValue_ofDiag ha hb hW hN,
      cylOfDiag_diagOfCyl hab ha hl.periodic]
  refine ⟨CycleSystem.ofDiag a b N ha hb (diagOfCyl a b l) hW, hN, hcyl, ?_⟩
  rw [CycleSystem.weightExp_eq_gammaShift_add_cylVolume _ hab ha hb hN, hcyl]

/-- Two collections with the same diagonal reading are the same collection: their occupied sets
agree, and so do their successor maps wherever those matter. -/
theorem CycleSystem.eq_of_cylOf_eq {a b N : ℕ} [NeZero (a + b)] (hab : Nat.Coprime a b)
    (ha : 0 < a) (hb : 0 < b) (X Y : CycleSystem a b)
    (hN : ∀ c : ZMod (a + b), (X.classOf c).card = N)
    (hM : ∀ c : ZMod (a + b), (Y.classOf c).card = N) (h : X.cylOf hN = Y.cylOf hM) :
    X.occupied = Y.occupied ∧ ∀ v ∈ X.occupied, X.succ v = Y.succ v := by
  have hocc := X.occupied_eq_of_cylOf_eq hab ha Y hN hM h
  exact ⟨hocc, fun _ hv => X.succ_eq_of_occupied_eq Y hab hb hocc hv⟩

end HJO.DetCoeff
