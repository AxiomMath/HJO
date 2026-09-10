/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import QSeriesLib.NumberTheory.QTheory.Basic
public import HJO.Paths.ReturnPath
public meta import HJO.Attr

/-! # The return-path identity

For coprime `1 < a < b` the finite HJO polynomial, shifted by the block hook count `κ_N`, is the
hook generating function of the `(aN, bN)`-paths that return to the diagonal after every block.

The proof runs through words of order filters. A word of `N` order filters of the gap set is the
same thing as a labelling of the gaps by sets of positions that grows along the two generator
steps, and under that dictionary the hook count of the concatenated path splits into the block
shift, the quadratic form at the label counts, and one ordered interaction per ordered pair of
positions. Visiting the gaps so that the `a`-predecessor and the `b`-successor of a gap come
first, the labellings with prescribed counts are enumerated, with their inversions, by a product
of Gaussian binomial coefficients, which is the generalised Gaussian multinomial.

Three results are taken as hypotheses: Huang's rank-one evaluation of the hook count and his
coercivity bound, and the good-traverse factorisation of Huang–Jiang–Oblomkov.
-/

@[expose] public section

open Finset NumericalSemigroup PowerSeries
open scoped QTheory

namespace HJO.ReturnPathSolves

variable {ι : Type*} [LinearOrder ι] {R : Type*} [CommSemiring R]

/-- The inversions of a selected subset `M` inside an ambient finite set `U`: the pairs
consisting of a selected element and a strictly larger unselected one. -/
def invCount (M U : Finset ι) : ℕ := #{x ∈ M ×ˢ (U \ M) | x.1 < x.2}

/-! ### Labellings of the gap set -/

/-- A labelling of the gap set: a set of labels attached to each gap. -/
abbrev Labelling (a b N : ℕ) := (finspan {a, b}).gaps → Finset (Fin N)

variable {a b N : ℕ}

/-- The labels at a natural number, read as empty off the gap set. -/
def lowLab (S : Labelling a b N) (j : ℕ) : Finset (Fin N) :=
  if h : j ∈ (finspan {a, b}).gaps then S ⟨j, h⟩ else ∅

/-- The labels at a natural number, read as everything off the gap set. -/
def upLab (S : Labelling a b N) (j : ℕ) : Finset (Fin N) :=
  if h : j ∈ (finspan {a, b}).gaps then S ⟨j, h⟩ else univ

/-- The inversions a labelling contributes at a gap: pairs of a label present at the gap but not
at its `a`-predecessor and a larger label absent at the gap but present at its `b`-successor. -/
def invAt (S : Labelling a b N) (g : (finspan {a, b}).gaps) : ℕ :=
  invCount (S g \ lowLab S ((g : ℕ) - a)) (upLab S ((g : ℕ) + b) \ lowLab S ((g : ℕ) - a))

/-- A labelling is a chain over `T`: at each gap in `T` its label set lies between those of its
two neighbours and has the prescribed size, and it is empty at every gap outside `T`. -/
def IsChainOn (T : Finset ℕ) (n : (finspan {a, b}).gaps → ℕ) (S : Labelling a b N) : Prop :=
  (∀ g : (finspan {a, b}).gaps, (g : ℕ) ∈ T →
      lowLab S ((g : ℕ) - a) ⊆ S g ∧ S g ⊆ upLab S ((g : ℕ) + b) ∧ #(S g) = n g) ∧
    ∀ g : (finspan {a, b}).gaps, (g : ℕ) ∉ T → S g = ∅

/-- Being a chain over `T` with prescribed label counts is decidable: it is a conjunction of
conditions on finitely many gaps, each an inclusion or a cardinality of `Finset`s. This is what
lets the chains over `T` be collected into a `Finset` of labellings and summed over. -/
instance instDecidableIsChainOn (T : Finset ℕ) (n : (finspan {a, b}).gaps → ℕ)
    (S : Labelling a b N) : Decidable (IsChainOn T n S) := by
  unfold IsChainOn; infer_instance

/-- The total number of inversions a labelling contributes over the gaps of `T`. -/
def chainWeight (T : Finset ℕ) (S : Labelling a b N) : ℕ :=
  ∑ g : (finspan {a, b}).gaps, if (g : ℕ) ∈ T then invAt S g else 0

/-- The generating function of the chains over `T` with prescribed label counts, graded by their
inversions. -/
def chainGF (q : R) (T : Finset ℕ) (N : ℕ) (n : (finspan {a, b}).gaps → ℕ) : R :=
  ∑ S ∈ {S : Labelling a b N | IsChainOn T n S}, q ^ chainWeight T S

/-- The Gaussian factor of the traverse at a gap: the choices of labels between the counts at the
`a`-predecessor and the `b`-successor. -/
def gaussAt (q : R) (a b N : ℕ) (n : (finspan {a, b}).gaps → ℕ) (g : ℕ) : R :=
  qChoose q ((Gaps.flag a b N n ((g : ℤ) + b) - HJO.extendNat n (g - a)))
    (HJO.extendNat n g - HJO.extendNat n (g - a))

/-- `T` is an initial segment of the traverse: with every gap it contains the two neighbours the
traverse visits first, its `a`-predecessor and its `b`-successor. -/
def IsTravInit (a b : ℕ) (T : Finset ℕ) : Prop :=
  T ⊆ (finspan {a, b}).gaps ∧ ∀ g ∈ T,
    (g - a ∈ (finspan {a, b}).gaps → g - a ∈ T) ∧ (g + b ∈ (finspan {a, b}).gaps → g + b ∈ T)

/-! ### Words of order filters -/

/-- The labelling attached to a word of sets of gaps: the labels at a gap are the positions of the
word whose set contains it. -/
def wordLab (a b : ℕ) {N : ℕ} (F : Fin N → Finset ℕ) : Labelling a b N :=
  fun g => {p : Fin N | (g : ℕ) ∈ F p}

/-- The label counts of a labelling, one natural number per gap. -/
def dims (S : Labelling a b N) : (finspan {a, b}).gaps → ℕ := fun g => #(S g)

/-! ### Gaussian binomials as quotients of q-Pochhammer symbols -/

/-- The self q-Pochhammer symbol has constant term one. -/
theorem constantCoeff_qPochhammer (j : ℕ) :
    PowerSeries.constantCoeff ((X; X)_j : ℤ⟦X⟧) = 1 := by
  rw [qPochhammer, map_prod]
  refine Finset.prod_eq_one fun i _ => ?_
  simp

/-- The self q-Pochhammer symbol is invertible, its inverse being the power series inverse. -/
theorem qPochhammer_mul_inv (j : ℕ) :
    ((X; X)_j : ℤ⟦X⟧) * invOfUnit (X; X)_j 1 = 1 :=
  PowerSeries.mul_invOfUnit _ 1 (by rw [constantCoeff_qPochhammer]; rfl)

/-- The Gaussian binomial coefficient as a q-Pochhammer quotient in the ring of formal power
series. -/
theorem qChoose_eq_qPochhammer_mul_inv {m k : ℕ} (hk : k ≤ m) :
    ((X; X)_m : ℤ⟦X⟧) * invOfUnit (X; X)_k 1 * invOfUnit (X; X)_(m - k) 1
      = qChoose (X : ℤ⟦X⟧) m k := by
  have h := qChoose_mul_qPochhammer_mul_qPochhammer (q := (X : ℤ⟦X⟧)) hk
  calc ((X; X)_m : ℤ⟦X⟧) * invOfUnit (X; X)_k 1 * invOfUnit (X; X)_(m - k) 1
      = qChoose (X : ℤ⟦X⟧) m k * (((X; X)_k : ℤ⟦X⟧) * invOfUnit (X; X)_k 1)
          * (((X; X)_(m - k) : ℤ⟦X⟧) * invOfUnit (X; X)_(m - k) 1) := by rw [← h]; ring
    _ = qChoose (X : ℤ⟦X⟧) m k := by rw [qPochhammer_mul_inv, qPochhammer_mul_inv, mul_one, mul_one]

/-! ### Nonnegativity of the quadratic form on the cone -/

/-- On the monotonicity cone the quadratic form is nonnegative, given Huang's coercivity bound. -/
theorem zero_le_Q (coercivity : HJO.Literature.HuangCoercivity) {a b : ℕ} (hco : a.Coprime b)
    (ha : 1 < a) (hab : a < b) {m : (finspan {a, b}).gaps → ℤ} (hm : m ∈ HJO.cone a b) :
    0 ≤ HJO.Q a b m := by
  have hf := GapPoset.frobeniusGap_mem a b hco ha (ha.trans hab)
  have hcard : 0 < ((finspan {a, b}).gaps.card : ℤ) := by
    have : (finspan {a, b}).gaps.Nonempty := ⟨_, hf⟩
    exact_mod_cast Finset.card_pos.mpr this
  have hbd := coercivity a b hco ha hab m hm ⟨Gaps.frobeniusGap a b, hf⟩
  nlinarith [sq_nonneg (m ⟨Gaps.frobeniusGap a b, hf⟩)]

/-! ### The index set of the finite series -/

/-- The cone points with all values at most `N`, as a finite set of natural gap vectors. -/
def coneFinset (a b N : ℕ) : Finset ((finspan {a, b}).gaps → ℕ) :=
  {n ∈ Fintype.piFinset fun _ : (finspan {a, b}).gaps => range (N + 1) |
    (∀ g h : (finspan {a, b}).gaps, (g : ℕ) + a = (h : ℕ) → n g ≤ n h) ∧
      ∀ g h : (finspan {a, b}).gaps, (g : ℕ) + b = (h : ℕ) → n g ≤ n h}

/-- Membership in `coneFinset` unfolded: values bounded by `N` and monotone along both steps. -/
theorem mem_coneFinset_iff {a b N : ℕ} (n : (finspan {a, b}).gaps → ℕ) :
    n ∈ coneFinset a b N ↔ (∀ g, n g ≤ N) ∧
      (∀ g h : (finspan {a, b}).gaps, (g : ℕ) + a = (h : ℕ) → n g ≤ n h) ∧
      ∀ g h : (finspan {a, b}).gaps, (g : ℕ) + b = (h : ℕ) → n g ≤ n h := by
  simp only [coneFinset, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range,
    Nat.lt_succ_iff]

/-- A vector of `coneFinset` gives, after casting, a point of the monotonicity cone. -/
theorem cast_mem_cone {a b N : ℕ} {n : (finspan {a, b}).gaps → ℕ} (hn : n ∈ coneFinset a b N) :
    (fun g => (n g : ℤ)) ∈ HJO.cone a b := by
  rw [mem_coneFinset_iff] at hn
  exact ⟨fun g => Int.natCast_nonneg _, fun i h => Nat.cast_le.mpr (hn.2.1 i ⟨_, h⟩ rfl),
    fun i h => Nat.cast_le.mpr (hn.2.2 i ⟨_, h⟩ rfl)⟩


/-- Off the gap set the natural extension of a gap vector vanishes. -/
theorem extendNat_of_notMem {a b : ℕ} (n : (finspan {a, b}).gaps → ℕ) {g : ℕ}
    (h : g ∉ (finspan {a, b}).gaps) : HJO.extendNat n g = 0 := by
  simp [HJO.extendNat, h]

/-- At a gap, the count at the `a`-predecessor is at most the count at the gap. -/
theorem extendNat_sub_le {a b N : ℕ} {n : (finspan {a, b}).gaps → ℕ} (hn : n ∈ coneFinset a b N)
    (g : (finspan {a, b}).gaps) : HJO.extendNat n ((g : ℕ) - a) ≤ n g := by
  rw [mem_coneFinset_iff] at hn
  by_cases h : (g : ℕ) - a ∈ (finspan {a, b}).gaps
  · have h1 : 1 ≤ (g : ℕ) - a := ReturnPath.one_le_of_mem_gaps h
    rw [GapPoset.extendNat_of_mem n h]
    exact hn.2.1 ⟨(g : ℕ) - a, h⟩ g (by change (g : ℕ) - a + a = (g : ℕ); omega)
  · rw [extendNat_of_notMem n h]
    exact Nat.zero_le _

/-- At a gap, the count is at most the flag value at the `b`-successor. -/
theorem le_flag {a b N : ℕ} {n : (finspan {a, b}).gaps → ℕ} (hn : n ∈ coneFinset a b N)
    (g : (finspan {a, b}).gaps) : n g ≤ Gaps.flag a b N n (((g : ℕ) : ℤ) + b) := by
  have hcast : (((g : ℕ) : ℤ) + b).toNat = (g : ℕ) + b := by omega
  have hneg : ¬ (((g : ℕ) : ℤ) + b < 0) := by omega
  rw [mem_coneFinset_iff] at hn
  simp only [Gaps.flag, hneg, ite_false, hcast]
  by_cases h : (g : ℕ) + b ∈ (finspan {a, b}).gaps
  · simp only [h, ite_true, GapPoset.extendNat_of_mem n h]
    exact hn.2.2 g ⟨(g : ℕ) + b, h⟩ rfl
  · simp only [h, ite_false]
    exact hn.1 g

/-- The Gaussian factors of the traverse multiply to the generalised Gaussian multinomial. -/
theorem prod_gaussAt_eq_multinomial (goodTraverse : External.GoodTraverse) {a b : ℕ}
    (hco : a.Coprime b) (ha : 1 < a) (hab : a < b) {N : ℕ} {n : (finspan {a, b}).gaps → ℕ}
    (hn : n ∈ coneFinset a b N) :
    ∏ g : (finspan {a, b}).gaps, gaussAt (X : ℤ⟦X⟧) a b N n (g : ℕ)
      = Gaps.multinomial a b N fun g => (n g : ℤ) := by
  have hf : HJO.extendNat n (Gaps.frobeniusGap a b) ≤ N := by
    by_cases h : Gaps.frobeniusGap a b ∈ (finspan {a, b}).gaps
    · rw [GapPoset.extendNat_of_mem n h]
      exact (mem_coneFinset_iff n).mp hn |>.1 _
    · rw [extendNat_of_notMem n h]
      exact Nat.zero_le _
  rw [goodTraverse a b hco ha hab N n (cast_mem_cone hn) hf]
  refine Finset.prod_congr rfl fun g _ => ?_
  have hlow := extendNat_sub_le hn g
  have hup := le_flag hn g
  have hng : HJO.extendNat n (g : ℕ) = n g := GapPoset.extendNat_of_mem n g.2
  rw [gaussAt, hng, ← qChoose_eq_qPochhammer_mul_inv (by omega),
    show Gaps.flag a b N n (((g : ℕ) : ℤ) + b) - HJO.extendNat n ((g : ℕ) - a)
        - (n g - HJO.extendNat n ((g : ℕ) - a))
      = Gaps.flag a b N n (((g : ℕ) : ℤ) + b) - n g from by omega]

/-- A sum over the gap set as a sum over the gap type. -/
theorem prod_gaps_type {M : Type*} [CommMonoid M] (a b : ℕ) (f : ℕ → M) :
    ∏ g : (finspan {a, b}).gaps, f (g : ℕ) = ∏ g ∈ (finspan {a, b}).gaps, f g :=
  (Finset.prod_subtype _ (fun _ => Iff.rfl) f).symm

/-- The finite series is a finite sum over the natural cone vectors bounded by `N`. -/
theorem finiteSeries_eq_sum {a b : ℕ} (hco : a.Coprime b) (ha : 1 < a) (hab : a < b) (N : ℕ) :
    Gaps.finiteSeries a b N
      = ∑ n ∈ coneFinset a b N, Gaps.multinomial a b N (fun g => (n g : ℤ))
          * X ^ (HJO.Q a b fun g => (n g : ℤ)).toNat := by
  have hf := GapPoset.frobeniusGap_mem a b hco ha (ha.trans hab)
  have hinj : ∀ m m' : (finspan {a, b}).gaps → ℕ,
      (fun g => ((m g : ℕ) : ℤ)) = (fun g => ((m' g : ℕ) : ℤ)) → m = m' := by
    intro m m' h
    exact funext fun g => Nat.cast_injective (congrFun h g)
  have hset : {m ∈ HJO.cone a b | HJO.extend m (Gaps.frobeniusGap a b) ≤ (N : ℤ)}
      = ↑((coneFinset a b N).image fun n g => ((n g : ℕ) : ℤ)) := by
    ext m
    simp only [Set.mem_ofPred_eq, Finset.coe_image, Set.mem_image, Finset.mem_coe]
    constructor
    · rintro ⟨hcone, hle⟩
      have hcone' := hcone
      rw [Gaps.cone_eq a b hco] at hcone'
      refine ⟨fun g => (m g).toNat, ?_, funext fun g => Int.toNat_of_nonneg (hcone'.1 g)⟩
      rw [mem_coneFinset_iff]
      rw [GapPoset.extend_of_mem m hf] at hle
      refine ⟨fun g => ?_, fun g h hgh => ?_, fun g h hgh => ?_⟩
      · have h1 := hcone'.2 g ⟨Gaps.frobeniusGap a b, hf⟩
          ((GapPoset.frobeniusGap_max a b hco ha hab).2 g g.2)
        omega
      · have := hcone'.2 g h ⟨1, 0, by omega⟩
        omega
      · have := hcone'.2 g h ⟨0, 1, by omega⟩
        omega
    · rintro ⟨n, hn, rfl⟩
      refine ⟨cast_mem_cone hn, ?_⟩
      rw [GapPoset.extend_of_mem _ hf]
      exact_mod_cast (mem_coneFinset_iff n).mp hn |>.1 _
  rw [Gaps.finiteSeries, hset, finsum_mem_coe_finset,
    Finset.sum_image fun m _ m' _ h => hinj m m' h]


/-! ### Gaussian binomial inversion counts -/


variable {ι : Type*} [LinearOrder ι] {R : Type*} [CommSemiring R]



/-- The inversions of `M` in `U`, counted one selected element at a time: each `p ∈ M`
contributes the number of unselected elements of `U` that exceed it. -/
theorem invCount_eq_sum (M U : Finset ι) :
    invCount M U = ∑ p ∈ M, #{r ∈ U \ M | p < r} := by
  rw [invCount, card_filter, sum_product]
  exact sum_congr rfl fun p _ => (card_filter _ _).symm

/-- The empty selection has no inversions. -/
@[simp]
theorem invCount_empty (U : Finset ι) : invCount (∅ : Finset ι) U = 0 := by
  simp [invCount]

/-- Enlarging the ambient set by an unselected element larger than everything already
present creates exactly one inversion for each selected element. -/
theorem invCount_insert_ambient {z : ι} {M U : Finset ι} (hzU : z ∉ U) (hMU : M ⊆ U)
    (hlt : ∀ y ∈ U, y < z) : invCount M (insert z U) = invCount M U + #M := by
  have hzM : z ∉ M := fun h => hzU (hMU h)
  have hzsub : z ∉ U \ M := fun h => hzU (mem_sdiff.mp h).1
  rw [invCount_eq_sum, invCount_eq_sum, insert_sdiff_of_notMem U hzM, card_eq_sum_ones M,
    ← sum_add_distrib]
  refine sum_congr rfl fun p hp => ?_
  have hpz : p < z := hlt p (hMU hp)
  simp only [filter_insert, hpz, ite_true]
  exact card_insert_of_notMem fun h => hzsub (mem_filter.mp h).1

/-- Enlarging both the ambient set and the selection by one element larger than everything
already present creates no new inversion. -/
theorem invCount_insert_both {z : ι} {M U : Finset ι} (hzU : z ∉ U) (hMU : M ⊆ U)
    (hlt : ∀ y ∈ U, y < z) : invCount (insert z M) (insert z U) = invCount M U := by
  have hzM : z ∉ M := fun h => hzU (hMU h)
  have hsdiff : insert z U \ insert z M = U \ M := by
    ext a
    simp only [mem_sdiff, mem_insert, not_or]
    refine ⟨fun ⟨h1, h2, h3⟩ => ⟨h1.resolve_left h2, h3⟩, fun ⟨h1, h2⟩ => ?_⟩
    exact ⟨Or.inr h1, fun h => hzU (h ▸ h1), h2⟩
  have hempty : {r ∈ U \ M | z < r} = ∅ :=
    filter_eq_empty_iff.mpr fun {r} hr => not_lt.mpr (hlt r (mem_sdiff.mp hr).1).le
  rw [invCount_eq_sum, invCount_eq_sum, hsdiff, sum_insert hzM, hempty, card_empty, zero_add]

/-- The inversion-generating function of the `k`-element subsets of a finite set of
cardinality `n` is the Gaussian binomial coefficient `qChoose q n k`. -/
theorem sum_pow_invCount_of_card (q : R) :
    ∀ (n : ℕ) (U : Finset ι), #U = n → ∀ k : ℕ,
      ∑ M ∈ U.powersetCard k, q ^ invCount M U = qChoose q #U k := by
  intro n
  induction n with
  | zero =>
    intro U hU k
    rw [card_eq_zero] at hU
    subst hU
    match k with
    | 0 => simp
    | j + 1 =>
      rw [powersetCard_eq_empty.mpr (by simp), sum_empty, card_empty, qChoose_zero_succ]
  | succ n ih =>
    intro U hU k
    have hne : U.Nonempty := card_pos.mp (by omega)
    obtain ⟨z, hzU, hzmax⟩ : ∃ z ∈ U, ∀ y ∈ U, y ≤ z :=
      ⟨U.max' hne, U.max'_mem hne, fun y hy => U.le_max' y hy⟩
    obtain ⟨U', hzU', hUeq, hU'card, hlt⟩ :
        ∃ U' : Finset ι, z ∉ U' ∧ insert z U' = U ∧ #U' = n ∧ ∀ y ∈ U', y < z :=
      ⟨U.erase z, notMem_erase z U, insert_erase hzU, by rw [card_erase_of_mem hzU]; omega,
        fun y hy => (hzmax y (mem_of_mem_erase hy)).lt_of_ne (ne_of_mem_erase hy)⟩
    match k with
    | 0 => simp
    | j + 1 =>
      have hdisj : Disjoint (U'.powersetCard (j + 1)) ((U'.powersetCard j).image (insert z)) := by
        refine disjoint_left.mpr fun {M} hM hM' => ?_
        obtain ⟨M', -, rfl⟩ := mem_image.mp hM'
        exact hzU' ((mem_powersetCard.mp hM).1 (mem_insert_self z M'))
      have hsplit : U.powersetCard (j + 1)
          = U'.powersetCard (j + 1) ∪ (U'.powersetCard j).image (insert z) := by
        rw [← hUeq]
        exact powersetCard_succ_insert hzU' j
      have h1 : ∑ M ∈ U'.powersetCard (j + 1), q ^ invCount M U
          = q ^ (j + 1) * ∑ M ∈ U'.powersetCard (j + 1), q ^ invCount M U' := by
        rw [mul_sum]
        refine sum_congr rfl fun M hM => ?_
        obtain ⟨hMU', hMcard⟩ := mem_powersetCard.mp hM
        rw [← hUeq, invCount_insert_ambient hzU' hMU' hlt, hMcard, pow_add, mul_comm]
      have h2 : ∑ M ∈ (U'.powersetCard j).image (insert z), q ^ invCount M U
          = ∑ M ∈ U'.powersetCard j, q ^ invCount M U' := by
        rw [sum_image ?inj]
        case inj =>
          intro x hx y hy h
          have hzx : z ∉ x := fun hh => hzU' ((mem_powersetCard.mp hx).1 hh)
          have hzy : z ∉ y := fun hh => hzU' ((mem_powersetCard.mp hy).1 hh)
          rw [← erase_insert hzx, ← erase_insert hzy, h]
        refine sum_congr rfl fun M hM => ?_
        rw [← hUeq, invCount_insert_both hzU' (mem_powersetCard.mp hM).1 hlt]
      have hcard : #U = #U' + 1 := by omega
      rw [hcard, qChoose_succ_succ, hsplit, sum_union hdisj, h1, h2, ih U' hU'card (j + 1),
        ih U' hU'card j, add_comm]

/-- The inversion-generating function of the `k`-element subsets of a finite set `U` is the
Gaussian binomial coefficient `qChoose q #U k`. -/
theorem sum_pow_invCount (q : R) (U : Finset ι) (k : ℕ) :
    ∑ M ∈ U.powersetCard k, q ^ invCount M U = qChoose q #U k :=
  sum_pow_invCount_of_card q #U U rfl k

/-- The inversion-generating function of the `k`-element subsets of `U` that contain a fixed
subset `L`, inversions being counted after deleting `L` from both, is the Gaussian binomial
coefficient of the reduced parameters. -/
theorem sum_pow_invCount_between (q : R) {L U : Finset ι} (hLU : L ⊆ U) {k : ℕ} (hk : #L ≤ k) :
    ∑ M ∈ {M ∈ U.powerset | L ⊆ M ∧ #M = k}, q ^ invCount (M \ L) (U \ L)
      = qChoose q (#U - #L) (k - #L) := by
  rw [← card_sdiff_of_subset hLU, ← sum_pow_invCount q (U \ L) (k - #L)]
  refine sum_nbij' (fun M => M \ L) (fun M => M ∪ L) ?_ ?_ ?_ ?_ ?_
  · intro M hM
    simp only [mem_filter, mem_powerset] at hM
    obtain ⟨hMU, hLM, hMcard⟩ := hM
    refine mem_powersetCard.mpr ⟨sdiff_subset_sdiff hMU le_rfl, ?_⟩
    rw [card_sdiff_of_subset hLM, hMcard]
  · intro M hM
    obtain ⟨hMUL, hMcard⟩ := mem_powersetCard.mp hM
    have hdisj : Disjoint M L := disjoint_left.mpr fun {a} ha => (mem_sdiff.mp (hMUL ha)).2
    simp only [mem_filter, mem_powerset]
    refine ⟨union_subset (hMUL.trans sdiff_subset) hLU, subset_union_right, ?_⟩
    rw [card_union_of_disjoint hdisj, hMcard]
    omega
  · intro M hM
    simp only [mem_filter, mem_powerset] at hM
    exact sdiff_union_of_subset hM.2.1
  · intro M hM
    have hdisj : Disjoint M L :=
      disjoint_left.mpr fun {a} ha => (mem_sdiff.mp ((mem_powersetCard.mp hM).1 ha)).2
    rw [union_sdiff_right, sdiff_eq_self_of_disjoint hdisj]
  · intro M _
    rfl


/-! ### The gap set -/


/-- A positive multiple of a generator is not a gap. -/
theorem notMem_gaps_of_dvd_left {a b m : ℕ} (hco : a.Coprime b) (hm : 0 < m) (h : a ∣ m) :
    m ∉ (finspan {a, b}).gaps := by
  obtain ⟨c, rfl⟩ := h
  rw [Gaps.mem_gaps_iff_not_exists a b hco, not_not]
  exact ⟨c, 0, by ring⟩

/-- A positive multiple of the second generator is not a gap. -/
theorem notMem_gaps_of_dvd_right {a b m : ℕ} (hco : a.Coprime b) (hm : 0 < m) (h : b ∣ m) :
    m ∉ (finspan {a, b}).gaps := by
  obtain ⟨c, rfl⟩ := h
  rw [Gaps.mem_gaps_iff_not_exists a b hco, not_not]
  exact ⟨0, c, by ring⟩

/-- The gap set is closed under subtracting a generator: if `g + a` is a gap then so is `g`. -/
theorem mem_gaps_of_add_left {a b g : ℕ} (hco : a.Coprime b)
    (h : g + a ∈ (finspan {a, b}).gaps) : g ∈ (finspan {a, b}).gaps := by
  rw [Gaps.mem_gaps_iff_not_exists a b hco] at h ⊢
  exact fun ⟨u, v, huv⟩ => h ⟨u + 1, v, by rw [Nat.succ_mul, ← huv]; ring⟩

/-- The gap set is closed under subtracting a generator: if `g + b` is a gap then so is `g`. -/
theorem mem_gaps_of_add_right {a b g : ℕ} (hco : a.Coprime b)
    (h : g + b ∈ (finspan {a, b}).gaps) : g ∈ (finspan {a, b}).gaps := by
  rw [Gaps.mem_gaps_iff_not_exists a b hco] at h ⊢
  exact fun ⟨u, v, huv⟩ => h ⟨u, v + 1, by rw [Nat.succ_mul, ← huv]; ring⟩

/-- At a gap, the `b`-successor leaves the gap set exactly when it becomes a multiple of `a`. -/
theorem add_right_notMem_gaps_iff {a b g : ℕ} (hco : a.Coprime b)
    (hg : g ∈ (finspan {a, b}).gaps) :
    g + b ∉ (finspan {a, b}).gaps ↔ a ∣ (g + b) := by
  refine ⟨fun h => ?_, fun h => notMem_gaps_of_dvd_left hco (by
    have := ReturnPath.one_le_of_mem_gaps hg; omega) h⟩
  rw [Gaps.mem_gaps_iff_not_exists a b hco, not_not] at h
  obtain ⟨u, v, huv⟩ := h
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · exact ⟨u, by rw [mul_comm]; simpa using huv.symm⟩
  · rw [Gaps.mem_gaps_iff_not_exists a b hco] at hg
    refine absurd ⟨u, v - 1, ?_⟩ hg
    have hv' : (v - 1) * b + b = v * b := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hv]
    omega

/-- At a gap, the `a`-successor leaves the gap set exactly when it becomes a multiple of `b`. -/
theorem add_left_notMem_gaps_iff {a b g : ℕ} (hco : a.Coprime b)
    (hg : g ∈ (finspan {a, b}).gaps) :
    g + a ∉ (finspan {a, b}).gaps ↔ b ∣ (g + a) := by
  refine ⟨fun h => ?_, fun h => notMem_gaps_of_dvd_right hco (by
    have := ReturnPath.one_le_of_mem_gaps hg; omega) h⟩
  rw [Gaps.mem_gaps_iff_not_exists a b hco, not_not] at h
  obtain ⟨u, v, huv⟩ := h
  rcases Nat.eq_zero_or_pos u with rfl | hu
  · exact ⟨v, by rw [mul_comm]; simpa using huv.symm⟩
  · rw [Gaps.mem_gaps_iff_not_exists a b hco] at hg
    refine absurd ⟨u - 1, v, ?_⟩ hg
    have hu' : (u - 1) * a + a = u * a := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hu]
    omega



/-- The ordered interaction of two order filters, counted as a set of gaps: those gaps of the
first filter that are minimal for the `a`-step, missing from the second filter, and whose
`b`-successor is either in the second filter or off the gap set. -/
def interCount (a b : ℕ) (F H : Finset ℕ) : ℕ :=
  #{g ∈ (finspan {a, b}).gaps | g ∈ F ∧ g - a ∉ F ∧ g ∉ H ∧
      (g + b ∈ H ∨ g + b ∉ (finspan {a, b}).gaps)}

/-- In an order filter, a gap whose `a`-predecessor lies in the filter lies in the filter. -/
theorem mem_of_sub_mem {a b : ℕ} {F : Finset ℕ} (hF : Gaps.IsOrderFilter a b F) {g : ℕ}
    (hg : g ∈ (finspan {a, b}).gaps) (hga : g - a ∈ F) : g ∈ F := by
  have h1 : 1 ≤ g - a := ReturnPath.one_le_of_mem_gaps (hF.1 hga)
  exact hF.2 _ hga g hg ⟨1, 0, by omega⟩

/-- In an order filter, the `b`-successor of a member stays in the filter whenever it is a gap. -/
theorem add_right_mem_of_mem {a b : ℕ} {H : Finset ℕ} (hH : Gaps.IsOrderFilter a b H) {g : ℕ}
    (hg : g ∈ H) (hgb : g + b ∈ (finspan {a, b}).gaps) : g + b ∈ H :=
  hH.2 _ hg _ hgb ⟨0, 1, by omega⟩

/-- The ordered interaction count is a sum over all gaps of a product of two indicators: the
`a`-minimality of the first filter and the `b`-step of the second. -/
theorem interCount_eq_sum {a b : ℕ} {F H : Finset ℕ} (hF : Gaps.IsOrderFilter a b F)
    (hH : Gaps.IsOrderFilter a b H) :
    (interCount a b F H : ℤ) = ∑ g ∈ (finspan {a, b}).gaps,
      ((if g ∈ F then (1 : ℤ) else 0) - (if g - a ∈ F then 1 else 0)) *
        (((if g + b ∈ H then (1 : ℤ) else 0)
            + (if g + b ∈ (finspan {a, b}).gaps then 0 else 1))
          - (if g ∈ H then 1 else 0)) := by
  rw [interCount, Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun g hg => ?_
  by_cases hgF : g ∈ F
  · by_cases hgaF : g - a ∈ F
    · simp [hgF, hgaF]
    · by_cases hgH : g ∈ H
      · by_cases hgbG : g + b ∈ (finspan {a, b}).gaps
        · have : g + b ∈ H := add_right_mem_of_mem hH hgH hgbG
          simp [hgF, hgaF, hgH, hgbG, this]
        · have : g + b ∉ H := fun h => hgbG (hH.1 h)
          simp [hgF, hgaF, hgH, hgbG, this]
      · by_cases hgbG : g + b ∈ (finspan {a, b}).gaps
        · by_cases hgbH : g + b ∈ H <;> simp [hgF, hgaF, hgH, hgbG, hgbH]
        · have : g + b ∉ H := fun h => hgbG (hH.1 h)
          simp [hgF, hgaF, hgH, hgbG, this]
  · have hgaF : g - a ∉ F := fun h => hgF (mem_of_sub_mem hF hg h)
    simp [hgF, hgaF]


/-- The Frobenius gap is the only gap whose `b`-successor is a multiple of `a` and whose
`a`-successor is not a gap. -/
theorem eq_frobeniusGap_of_add_notMem {a b g : ℕ} (hco : a.Coprime b) (ha : 1 < a) (hab : a < b)
    (hg : g ∈ (finspan {a, b}).gaps) (hdvd : a ∣ (g + b))
    (hna : g + a ∉ (finspan {a, b}).gaps) : g = Gaps.frobeniusGap a b := by
  have hb : 1 < b := ha.trans hab
  obtain ⟨v, hv⟩ : b ∣ g + a := (add_left_notMem_gaps_iff hco hg).mp hna
  have hgb : g + a + b = b * (v + 1) := by rw [hv]; ring
  have hdvd2 : a ∣ b * (v + 1) := by
    obtain ⟨k, hk⟩ := hdvd
    refine ⟨k + 1, ?_⟩
    have h2 : a * (k + 1) = a * k + a := by ring
    omega
  obtain ⟨m, hm⟩ : a ∣ v + 1 := hco.dvd_of_dvd_mul_left hdvd2
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · simp at hm
    · exact h
  rcases eq_or_lt_of_le hm1 with hm1' | hm2
  · rw [← hm1', mul_one] at hm
    have hbv : b * v = (a - 1) * b := by rw [mul_comm]; congr 1; omega
    have hsub := GapPoset.sub_one_mul_eq a b ha hb
    omega
  · have h3 : a * 2 ≤ a * m := Nat.mul_le_mul le_rfl hm2
    have hring : a * 2 = 2 * a := by ring
    have h4 : b * (2 * a) ≤ b * (v + 1) := Nat.mul_le_mul le_rfl (by omega)
    have h5 : b * (2 * a) = 2 * (a * b) := by ring
    have h6 : 0 < a * b := Nat.mul_pos (by omega) (by omega)
    have h7 : g + a + b ≤ a * b := ReturnPath.add_le_of_mem_gaps hco ha hg
    omega

/-- The gaps whose `b`-successor is a multiple of `a` and whose `a`-successor is not a gap form
the singleton consisting of the Frobenius gap. -/
theorem filter_boundary_eq_singleton {a b : ℕ} (hco : a.Coprime b) (ha : 1 < a) (hab : a < b) :
    {g ∈ (finspan {a, b}).gaps | (a ∣ (g + b)) ∧ g + a ∉ (finspan {a, b}).gaps}
      = {Gaps.frobeniusGap a b} := by
  have hb : 1 < b := ha.trans hab
  have hfab := GapPoset.frobeniusGap_add_add a b ha hb
  have hsub := GapPoset.sub_one_mul_eq a b ha hb
  refine Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_filter.mpr
    ⟨GapPoset.frobeniusGap_mem a b hco ha hb, ⟨b - 1, ?_⟩, ?_⟩, fun g hg => ?_⟩
  · have h1 : a * (b - 1) + a = a * b := by
      obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring
    omega
  · exact notMem_gaps_of_dvd_right hco (by omega) ⟨a - 1, by rw [mul_comm]; omega⟩
  · obtain ⟨hg1, hg2, hg3⟩ := Finset.mem_filter.mp hg
    exact eq_frobeniusGap_of_add_notMem hco ha hab hg1 hg2 hg3


/-- The boundary half of the interaction sum: only the Frobenius gap contributes to it. -/
theorem sum_boundary_eq {a b : ℕ} (hco : a.Coprime b) (ha : 1 < a) (hab : a < b)
    {F : Finset ℕ} (hF : Gaps.IsOrderFilter a b F) :
    ∑ g ∈ (finspan {a, b}).gaps,
        ((if g ∈ F then (1 : ℤ) else 0) - (if g - a ∈ F then 1 else 0)) *
          (if g + b ∈ (finspan {a, b}).gaps then 0 else 1)
      = if Gaps.frobeniusGap a b ∈ F then 1 else 0 := by
  have h1 : ∀ g ∈ (finspan {a, b}).gaps,
      ((if g ∈ F then (1 : ℤ) else 0) - (if g - a ∈ F then 1 else 0)) *
          (if g + b ∈ (finspan {a, b}).gaps then 0 else 1)
        = if a ∣ (g + b) then
            ((if g ∈ F then (1 : ℤ) else 0) - (if g - a ∈ F then 1 else 0)) else 0 := by
    intro g hg
    have hiff := add_right_notMem_gaps_iff hco hg
    by_cases hd : a ∣ (g + b)
    · have hgb : g + b ∉ (finspan {a, b}).gaps := hiff.mpr hd
      simp [hd, hgb]
    · have hgb : g + b ∈ (finspan {a, b}).gaps := not_not.mp fun hc => hd (hiff.mp hc)
      simp [hd, hgb]
  rw [Finset.sum_congr rfl h1, ← Finset.sum_filter, Finset.sum_sub_distrib]
  have hvan : ∀ x ∈ {g ∈ (finspan {a, b}).gaps | a ∣ (g + b)},
      x ∉ {g ∈ {g ∈ (finspan {a, b}).gaps | a ∣ (g + b)} | g - a ∈ (finspan {a, b}).gaps} →
        (if x - a ∈ F then (1 : ℤ) else 0) = 0 := by
    intro x hxX hxn
    have hxs : x - a ∉ (finspan {a, b}).gaps := fun hc => hxn (Finset.mem_filter.mpr ⟨hxX, hc⟩)
    have hxF : x - a ∉ F := fun hc => hxs (hF.1 hc)
    simp [hxF]
  have h2 : ∑ g ∈ {g ∈ (finspan {a, b}).gaps | a ∣ (g + b)}, (if g - a ∈ F then (1 : ℤ) else 0)
      = ∑ g ∈ {g ∈ {g ∈ (finspan {a, b}).gaps | a ∣ (g + b)} |
          g + a ∈ (finspan {a, b}).gaps}, (if g ∈ F then (1 : ℤ) else 0) := by
    rw [← Finset.sum_subset (Finset.filter_subset
      (fun g => g - a ∈ (finspan {a, b}).gaps) _) hvan]
    refine Finset.sum_nbij' (fun g => g - a) (fun g => g + a) ?_ ?_ ?_ ?_ (fun g _ => rfl)
    · intro g hg
      obtain ⟨hgX, hgs⟩ := Finset.mem_filter.mp hg
      obtain ⟨hgG, hgd⟩ := Finset.mem_filter.mp hgX
      have hga : a < g := by
        have := ReturnPath.one_le_of_mem_gaps hgs
        omega
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hgs, ?_⟩, ?_⟩
      · have h5 : g - a + b = g + b - a := by omega
        rw [h5]
        exact Nat.dvd_sub hgd dvd_rfl
      · rwa [Nat.sub_add_cancel hga.le]
    · intro g hg
      obtain ⟨hgX, hgs⟩ := Finset.mem_filter.mp hg
      obtain ⟨hgG, hgd⟩ := Finset.mem_filter.mp hgX
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hgs, ?_⟩, ?_⟩
      · have h5 : g + a + b = g + b + a := by omega
        rw [h5]
        exact dvd_add hgd dvd_rfl
      · rwa [Nat.add_sub_cancel]
    · intro g hg
      have hgs := (Finset.mem_filter.mp hg).2
      have := ReturnPath.one_le_of_mem_gaps hgs
      omega
    · exact fun g _ => Nat.add_sub_cancel g a
  have h3 := Finset.sum_filter_add_sum_filter_not
      {g ∈ (finspan {a, b}).gaps | a ∣ (g + b)} (fun g => g + a ∈ (finspan {a, b}).gaps)
      (fun g => if g ∈ F then (1 : ℤ) else 0)
  have h4 : {g ∈ {g ∈ (finspan {a, b}).gaps | a ∣ (g + b)} |
      g + a ∉ (finspan {a, b}).gaps} = {Gaps.frobeniusGap a b} := by
    rw [Finset.filter_filter]
    exact filter_boundary_eq_singleton hco ha hab
  rw [h2, ← h3, h4, Finset.sum_singleton]
  ring

/-- The interior half of the interaction sum, reindexed onto the gaps of the first filter: for
each such gap, whether its `a`-, `b`- and `(a+b)`-shifts and itself lie in the second filter. -/
theorem sum_interior_eq {a b : ℕ} (hco : a.Coprime b) {F H : Finset ℕ}
    (hF : Gaps.IsOrderFilter a b F) (hH : Gaps.IsOrderFilter a b H) :
    ∑ g ∈ (finspan {a, b}).gaps,
        ((if g ∈ F then (1 : ℤ) else 0) - (if g - a ∈ F then 1 else 0)) *
          ((if g + b ∈ H then (1 : ℤ) else 0) - (if g ∈ H then 1 else 0))
      = ∑ g ∈ F, ((if g + a ∈ H then (1 : ℤ) else 0) + (if g + b ∈ H then 1 else 0)
          - (if g ∈ H then 1 else 0) - (if g + a + b ∈ H then 1 else 0)) := by
  have hsplit : ∀ g ∈ (finspan {a, b}).gaps,
      ((if g ∈ F then (1 : ℤ) else 0) - (if g - a ∈ F then 1 else 0)) *
          ((if g + b ∈ H then (1 : ℤ) else 0) - (if g ∈ H then 1 else 0))
        = (if g ∈ F then ((if g + b ∈ H then (1 : ℤ) else 0) - (if g ∈ H then 1 else 0)) else 0)
          - (if g - a ∈ F then
              ((if g + b ∈ H then (1 : ℤ) else 0) - (if g ∈ H then 1 else 0)) else 0) := by
    intro g _
    split_ifs <;> ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib]
  have hA : ∑ g ∈ (finspan {a, b}).gaps,
      (if g ∈ F then ((if g + b ∈ H then (1 : ℤ) else 0) - (if g ∈ H then 1 else 0)) else 0)
      = ∑ g ∈ F, ((if g + b ∈ H then (1 : ℤ) else 0) - (if g ∈ H then 1 else 0)) := by
    rw [← Finset.sum_subset hF.1 fun x _ hx => by simp [hx]]
    exact Finset.sum_congr rfl fun g hg => by simp [hg]
  have hB : ∑ g ∈ (finspan {a, b}).gaps,
      (if g - a ∈ F then ((if g + b ∈ H then (1 : ℤ) else 0) - (if g ∈ H then 1 else 0)) else 0)
      = ∑ g ∈ F, ((if g + a + b ∈ H then (1 : ℤ) else 0) - (if g + a ∈ H then 1 else 0)) := by
    have hvan : ∀ x ∈ (finspan {a, b}).gaps,
        x ∉ {g ∈ (finspan {a, b}).gaps | g - a ∈ F} →
          (if x - a ∈ F then ((if x + b ∈ H then (1 : ℤ) else 0) - (if x ∈ H then 1 else 0))
            else 0) = 0 := by
      intro x hx hxn
      have hxF : x - a ∉ F := fun hc => hxn (Finset.mem_filter.mpr ⟨hx, hc⟩)
      simp [hxF]
    have hstep : ∑ g ∈ {g ∈ (finspan {a, b}).gaps | g - a ∈ F},
        (if g - a ∈ F then ((if g + b ∈ H then (1 : ℤ) else 0) - (if g ∈ H then 1 else 0)) else 0)
        = ∑ g ∈ {g ∈ (finspan {a, b}).gaps | g - a ∈ F},
            ((if g + b ∈ H then (1 : ℤ) else 0) - (if g ∈ H then 1 else 0)) :=
      Finset.sum_congr rfl fun g hg => by simp [(Finset.mem_filter.mp hg).2]
    rw [← Finset.sum_subset (Finset.filter_subset (fun g => g - a ∈ F) _) hvan, hstep]
    have hbij : ∑ g ∈ {g ∈ (finspan {a, b}).gaps | g - a ∈ F},
        ((if g + b ∈ H then (1 : ℤ) else 0) - (if g ∈ H then 1 else 0))
        = ∑ g ∈ {g ∈ F | g + a ∈ (finspan {a, b}).gaps},
            ((if g + a + b ∈ H then (1 : ℤ) else 0) - (if g + a ∈ H then 1 else 0)) := by
      refine Finset.sum_nbij' (fun g => g - a) (fun g => g + a) ?_ ?_ ?_ ?_ ?_
      · intro g hg
        obtain ⟨hgG, hgF⟩ := Finset.mem_filter.mp hg
        have hga : a < g := by
          have := ReturnPath.one_le_of_mem_gaps (hF.1 hgF)
          omega
        exact Finset.mem_filter.mpr ⟨hgF, by rwa [Nat.sub_add_cancel hga.le]⟩
      · intro g hg
        obtain ⟨hgF, hgG⟩ := Finset.mem_filter.mp hg
        exact Finset.mem_filter.mpr ⟨hgG, by rwa [Nat.add_sub_cancel]⟩
      · intro g hg
        have := ReturnPath.one_le_of_mem_gaps (hF.1 (Finset.mem_filter.mp hg).2)
        omega
      · exact fun g _ => Nat.add_sub_cancel g a
      · intro g hg
        have hgF := (Finset.mem_filter.mp hg).2
        have hga : a < g := by
          have := ReturnPath.one_le_of_mem_gaps (hF.1 hgF)
          omega
        rw [Nat.sub_add_cancel hga.le]
    rw [hbij]
    refine Finset.sum_subset (Finset.filter_subset _ _) fun x hxF hxn => ?_
    have hxa : x + a ∉ (finspan {a, b}).gaps := fun hc => hxn (Finset.mem_filter.mpr ⟨hxF, hc⟩)
    have hxab : x + a + b ∉ (finspan {a, b}).gaps := fun hc => hxa (mem_gaps_of_add_right hco hc)
    have h1 : x + a ∉ H := fun hc => hxa (hH.1 hc)
    have h2 : x + a + b ∉ H := fun hc => hxab (hH.1 hc)
    simp [h1, h2]
  rw [hA, hB, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun g _ => by ring

/-- The ordered interaction of two order filters is counted by the gaps of the first filter that
are `a`-minimal, missing from the second, and whose `b`-successor is in it or off the gap set. -/
theorem interCount_eq_orderedPart {a b : ℕ} (hco : a.Coprime b) (ha : 1 < a) (hab : a < b)
    {F H : Finset ℕ} (hF : Gaps.IsOrderFilter a b F) (hH : Gaps.IsOrderFilter a b H) :
    (interCount a b F H : ℤ) = ReturnPath.orderedPart a b F H := by
  have hsplit : ∀ g ∈ (finspan {a, b}).gaps,
      ((if g ∈ F then (1 : ℤ) else 0) - (if g - a ∈ F then 1 else 0)) *
          (((if g + b ∈ H then (1 : ℤ) else 0)
              + (if g + b ∈ (finspan {a, b}).gaps then 0 else 1))
            - (if g ∈ H then 1 else 0))
        = ((if g ∈ F then (1 : ℤ) else 0) - (if g - a ∈ F then 1 else 0)) *
            ((if g + b ∈ H then (1 : ℤ) else 0) - (if g ∈ H then 1 else 0))
          + ((if g ∈ F then (1 : ℤ) else 0) - (if g - a ∈ F then 1 else 0)) *
            (if g + b ∈ (finspan {a, b}).gaps then 0 else 1) := fun g _ => by ring
  rw [interCount_eq_sum hF hH, ReturnPath.orderedPart_eq, Finset.sum_congr rfl hsplit,
    Finset.sum_add_distrib, sum_interior_eq hco hF hH, sum_boundary_eq hco ha hab hF]
  ring





/-- Two naturals whose strict lower sets agree are equal. -/
theorem eq_of_lt_iff_lt {X Y : ℕ} (h : ∀ j, j < X ↔ j < Y) : X = Y := by
  have h1 := h X
  have h2 := h Y
  omega

/-- A downward-closed finite set of naturals is the range of its own cardinality. -/
theorem eq_range_card_of_downwardClosed {S : Finset ℕ}
    (hdc : ∀ k k' : ℕ, k' ≤ k → k ∈ S → k' ∈ S) : S = range #S := by
  refine (Finset.eq_of_subset_of_card_le (fun k hk => ?_) (by simp)).symm
  rw [mem_range] at hk
  by_contra hkS
  have hsub : S ⊆ range k := fun m hm =>
    mem_range.2 (by by_contra h; exact hkS (hdc m k (by omega) hm))
  have hcard := Finset.card_le_card hsub
  rw [card_range] at hcard
  omega

/-- If `g + k * b` is a gap then so is `g + k' * b` for every `k' ≤ k`. -/
theorem mem_gaps_of_le_mul_right {a b g : ℕ} (hco : a.Coprime b) :
    ∀ d k : ℕ, g + (k + d) * b ∈ (finspan {a, b}).gaps → g + k * b ∈ (finspan {a, b}).gaps := by
  intro d
  induction d with
  | zero => intro k h; simpa using h
  | succ n ih =>
    intro k h
    have h1 : g + (k + 1) * b ∈ (finspan {a, b}).gaps :=
      ih (k + 1) (by rw [show k + 1 + n = k + (n + 1) by omega]; exact h)
    exact mem_gaps_of_add_right hco (by rw [show g + k * b + b = g + (k + 1) * b by ring]; exact h1)

/-- If `g + j * a` is a gap then so is `g + j' * a` for every `j' ≤ j`. -/
theorem mem_gaps_of_le_mul_left {a b g : ℕ} (hco : a.Coprime b) :
    ∀ d j : ℕ, g + (j + d) * a ∈ (finspan {a, b}).gaps → g + j * a ∈ (finspan {a, b}).gaps := by
  intro d
  induction d with
  | zero => intro j h; simpa using h
  | succ n ih =>
    intro j h
    have h1 : g + (j + 1) * a ∈ (finspan {a, b}).gaps :=
      ih (j + 1) (by rw [show j + 1 + n = j + (n + 1) by omega]; exact h)
    exact mem_gaps_of_add_left hco (by rw [show g + j * a + a = g + (j + 1) * a by ring]; exact h1)

/-- The length of the `b`-chain of gaps starting at `g`: the number of `k < a` with `g + k * b`
still a gap. -/
def colUp (a b g : ℕ) : ℕ := #{k ∈ range a | g + k * b ∈ (finspan {a, b}).gaps}

/-- The length of the `a`-chain of gaps starting at `g`: the number of `j < b` with `g + j * a`
still a gap. -/
def rowUp (a b g : ℕ) : ℕ := #{j ∈ range b | g + j * a ∈ (finspan {a, b}).gaps}

/-- The `b`-chain of gaps starting at `g` is an initial segment of `range a`. -/
theorem filter_eq_range_colUp (a b g : ℕ) (hco : a.Coprime b) :
    {k ∈ range a | g + k * b ∈ (finspan {a, b}).gaps} = range (colUp a b g) := by
  refine eq_range_card_of_downwardClosed (fun k k' hk hmem => ?_)
  rw [mem_filter, mem_range] at hmem ⊢
  refine ⟨by omega, ?_⟩
  obtain ⟨d, rfl⟩ : ∃ d, k = k' + d := ⟨k - k', by omega⟩
  exact mem_gaps_of_le_mul_right hco d k' hmem.2

/-- The `a`-chain of gaps starting at `g` is an initial segment of `range b`. -/
theorem filter_eq_range_rowUp (a b g : ℕ) (hco : a.Coprime b) :
    {j ∈ range b | g + j * a ∈ (finspan {a, b}).gaps} = range (rowUp a b g) := by
  refine eq_range_card_of_downwardClosed (fun j j' hj hmem => ?_)
  rw [mem_filter, mem_range] at hmem ⊢
  refine ⟨by omega, ?_⟩
  obtain ⟨d, rfl⟩ : ∃ d, j = j' + d := ⟨j - j', by omega⟩
  exact mem_gaps_of_le_mul_left hco d j' hmem.2

/-- `k` is below `colUp a b g` exactly when `k < a` and `g + k * b` is still a gap. -/
theorem lt_colUp_iff {a b g k : ℕ} (hco : a.Coprime b) :
    k < colUp a b g ↔ k < a ∧ g + k * b ∈ (finspan {a, b}).gaps := by
  rw [← mem_range, ← filter_eq_range_colUp a b g hco, mem_filter, mem_range]

/-- `j` is below `rowUp a b g` exactly when `j < b` and `g + j * a` is still a gap. -/
theorem lt_rowUp_iff {a b g j : ℕ} (hco : a.Coprime b) :
    j < rowUp a b g ↔ j < b ∧ g + j * a ∈ (finspan {a, b}).gaps := by
  rw [← mem_range, ← filter_eq_range_rowUp a b g hco, mem_filter, mem_range]

/-- Every gap starts a nonempty `b`-chain. -/
theorem one_le_colUp {a b g : ℕ} (hco : a.Coprime b) (ha : 0 < a)
    (hg : g ∈ (finspan {a, b}).gaps) : 1 ≤ colUp a b g := by
  rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, lt_colUp_iff hco]
  exact ⟨ha, by simpa using hg⟩

/-- Every gap starts a nonempty `a`-chain. -/
theorem one_le_rowUp {a b g : ℕ} (hco : a.Coprime b) (hb : 0 < b)
    (hg : g ∈ (finspan {a, b}).gaps) : 1 ≤ rowUp a b g := by
  rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, lt_rowUp_iff hco]
  exact ⟨hb, by simpa using hg⟩

/-- Some step of the `b`-chain of a gap lands on a multiple of `a`. -/
theorem exists_lt_dvd_add_mul {a b g : ℕ} (hco : a.Coprime b) (ha : 0 < a) :
    ∃ j < a, a ∣ g + j * b := by
  obtain ⟨j, hja, hmod⟩ := GapPoset.exists_lt_mod_eq_mul a b hco ha ((a - 1) * g)
  refine ⟨j, hja, Nat.dvd_of_mod_eq_zero ?_⟩
  have ht : g + (a - 1) * g = a * g := by
    obtain ⟨c, rfl⟩ : ∃ c, a = c + 1 := ⟨a - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    ring
  have h0 : (g + (a - 1) * g) % a = 0 := by rw [ht]; exact Nat.mul_mod_right a g
  have hmod' : (g + (a - 1) * g) % a = (g + j * b) % a := Nat.ModEq.add_left g hmod
  rw [← hmod', h0]

/-- The `b`-chain of a gap stops before the `a`-th step. -/
theorem colUp_lt {a b g : ℕ} (hco : a.Coprime b) (ha : 0 < a)
    (hg : g ∈ (finspan {a, b}).gaps) : colUp a b g < a := by
  obtain ⟨j, hja, hdvd⟩ := exists_lt_dvd_add_mul (a := a) (b := b) (g := g) hco ha
  have hg1 : 1 ≤ g := ReturnPath.one_le_of_mem_gaps hg
  have hnot : g + j * b ∉ (finspan {a, b}).gaps :=
    notMem_gaps_of_dvd_left hco (by omega) hdvd
  have hj : ¬ j < colUp a b g := fun h => hnot ((lt_colUp_iff hco).mp h).2
  omega

/-- The `a`-chain of a gap stops before the `b`-th step. -/
theorem rowUp_lt {a b g : ℕ} (hco : a.Coprime b) (ha : 1 < a) (hb : 0 < b)
    (hg : g ∈ (finspan {a, b}).gaps) : rowUp a b g < b := by
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  by_contra hcon
  have hc : c < rowUp a (c + 1) g := by omega
  have hmem := ((lt_rowUp_iff hco).mp hc).2
  have h2 := ReturnPath.add_le_of_mem_gaps hco ha hmem
  have hmul : a * (c + 1) = c * a + a := by ring
  have hg1 : 1 ≤ g := ReturnPath.one_le_of_mem_gaps hg
  omega

/-- Subtracting `a` inside the gap set leaves the length of the `b`-chain unchanged. -/
theorem colUp_sub_eq {a b g : ℕ} (hco : a.Coprime b) (ha : 0 < a)
    (hg : g ∈ (finspan {a, b}).gaps) (hga : g - a ∈ (finspan {a, b}).gaps) :
    colUp a b (g - a) = colUp a b g := by
  have hga1 : 1 ≤ g - a := ReturnPath.one_le_of_mem_gaps hga
  have hc1 : 1 ≤ colUp a b g := one_le_colUp hco ha hg
  have hca : colUp a b g < a := colUp_lt hco ha hg
  have key : ∀ k, k < colUp a b g → k < colUp a b (g - a) := by
    intro k hk
    obtain ⟨hka, hmem⟩ := (lt_colUp_iff hco).mp hk
    refine (lt_colUp_iff hco).mpr ⟨hka, mem_gaps_of_add_left hco ?_⟩
    rw [show g - a + k * b + a = g + k * b by omega]
    exact hmem
  have h1 : colUp a b g ≤ colUp a b (g - a) := by
    by_contra hcon
    have := key _ (by omega : colUp a b (g - a) < colUp a b g)
    omega
  have hmem1 : g + (colUp a b g - 1) * b ∈ (finspan {a, b}).gaps :=
    ((lt_colUp_iff hco).mp (by omega : colUp a b g - 1 < colUp a b g)).2
  have hnot : g + colUp a b g * b ∉ (finspan {a, b}).gaps := fun h =>
    absurd ((lt_colUp_iff hco).mpr ⟨hca, h⟩) (by omega)
  have hmul : (colUp a b g - 1) * b + b = colUp a b g * b := by
    obtain ⟨d, hd⟩ : ∃ d, colUp a b g = d + 1 := ⟨colUp a b g - 1, by omega⟩
    rw [hd, Nat.add_sub_cancel]
    ring
  have heq : g + (colUp a b g - 1) * b + b = g + colUp a b g * b := by omega
  have hdvd : a ∣ g + colUp a b g * b := by
    have h := (add_right_notMem_gaps_iff hco hmem1).mp (by rw [heq]; exact hnot)
    rwa [heq] at h
  have hdvd2 : a ∣ g - a + colUp a b g * b := by
    have h := Nat.dvd_sub hdvd (dvd_refl a)
    rwa [show g + colUp a b g * b - a = g - a + colUp a b g * b by omega] at h
  have hnot2 : g - a + colUp a b g * b ∉ (finspan {a, b}).gaps :=
    notMem_gaps_of_dvd_left hco (by omega) hdvd2
  have h2 : ¬ colUp a b g < colUp a b (g - a) := fun h =>
    hnot2 ((lt_colUp_iff hco).mp h).2
  omega

/-- Subtracting `a` inside the gap set lengthens the `a`-chain by exactly one step. -/
theorem rowUp_sub_eq {a b g : ℕ} (hco : a.Coprime b) (ha : 1 < a) (hb : 0 < b)
    (hg : g ∈ (finspan {a, b}).gaps) (hga : g - a ∈ (finspan {a, b}).gaps) :
    rowUp a b (g - a) = rowUp a b g + 1 := by
  have hga1 : 1 ≤ g - a := ReturnPath.one_le_of_mem_gaps hga
  have hrb : rowUp a b g < b := rowUp_lt hco ha hb hg
  refine eq_of_lt_iff_lt (fun j => ?_)
  rw [lt_rowUp_iff hco]
  constructor
  · rintro ⟨hjb, hmem⟩
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · omega
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      have hmul : (i + 1) * a = i * a + a := by ring
      rw [show g - a + (i + 1) * a = g + i * a by omega] at hmem
      have : i < rowUp a b g := (lt_rowUp_iff hco).mpr ⟨by omega, hmem⟩
      omega
  · intro hj
    refine ⟨by omega, ?_⟩
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simpa using hga
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      have hmem := ((lt_rowUp_iff hco).mp (by omega : i < rowUp a b g)).2
      have hmul : (i + 1) * a = i * a + a := by ring
      rw [show g - a + (i + 1) * a = g + i * a by omega]
      exact hmem

/-- Adding `b` inside the gap set shortens the `b`-chain by exactly one step. -/
theorem colUp_add_eq {a b g : ℕ} (hco : a.Coprime b) (ha : 1 < a)
    (hg : g ∈ (finspan {a, b}).gaps) : colUp a b (g + b) = colUp a b g - 1 := by
  have hg1 : 1 ≤ g := ReturnPath.one_le_of_mem_gaps hg
  have hshift : ∀ k : ℕ, g + b + k * b = g + (k + 1) * b := fun k => by ring
  refine eq_of_lt_iff_lt (fun k => ?_)
  rw [lt_colUp_iff hco]
  constructor
  · rintro ⟨hka, hmem⟩
    rw [hshift k] at hmem
    have hk1 : k + 1 < a := by
      by_contra hcon
      rw [show k + 1 = a by omega] at hmem
      have h2 := ReturnPath.add_le_of_mem_gaps hco ha hmem
      omega
    have : k + 1 < colUp a b g := (lt_colUp_iff hco).mpr ⟨hk1, hmem⟩
    omega
  · intro hk
    obtain ⟨hk1a, hmem⟩ := (lt_colUp_iff hco).mp (by omega : k + 1 < colUp a b g)
    exact ⟨by omega, by rw [hshift k]; exact hmem⟩

/-- The traverse rank of a gap: it strictly decreases both on subtracting `a` and on adding `b`,
which orders the gap set so that both neighbours needed at a gap come earlier. -/
def travRank (a b g : ℕ) : ℕ := colUp a b g * (b + 1) - rowUp a b g

/-- Subtracting `a` inside the gap set strictly decreases the traverse rank. -/
theorem travRank_sub_lt {a b g : ℕ} (hco : a.Coprime b) (ha : 1 < a) (hab : a < b)
    (hg : g ∈ (finspan {a, b}).gaps) (hga : g - a ∈ (finspan {a, b}).gaps) :
    travRank a b (g - a) < travRank a b g := by
  have hb : 0 < b := by omega
  have hcol : colUp a b (g - a) = colUp a b g := colUp_sub_eq hco (by omega) hg hga
  have hrow : rowUp a b (g - a) = rowUp a b g + 1 := rowUp_sub_eq hco ha hb hg hga
  have hc1 : 1 ≤ colUp a b g := one_le_colUp hco (by omega) hg
  have hrb : rowUp a b g < b := rowUp_lt hco ha hb hg
  have hmul : b + 1 ≤ colUp a b g * (b + 1) := Nat.le_mul_of_pos_left _ hc1
  simp only [travRank, hcol, hrow]
  omega

/-- Adding `b` inside the gap set strictly decreases the traverse rank. -/
theorem travRank_add_lt {a b g : ℕ} (hco : a.Coprime b) (ha : 1 < a) (hab : a < b)
    (hg : g ∈ (finspan {a, b}).gaps) (hgb : g + b ∈ (finspan {a, b}).gaps) :
    travRank a b (g + b) < travRank a b g := by
  have hb : 0 < b := by omega
  have hc1 : 1 ≤ colUp a b g := one_le_colUp hco (by omega) hg
  have hrb : rowUp a b g < b := rowUp_lt hco ha hb hg
  have hrb' : rowUp a b (g + b) < b := rowUp_lt hco ha hb hgb
  obtain ⟨d, hd⟩ : ∃ d, colUp a b g = d + 1 := ⟨colUp a b g - 1, by omega⟩
  have hcol : colUp a b (g + b) = d := by
    rw [colUp_add_eq hco ha hg, hd, Nat.add_sub_cancel]
  have hmul : (d + 1) * (b + 1) = d * (b + 1) + (b + 1) := by ring
  simp only [travRank, hcol, hd]
  omega

/-- Any nonempty set of gaps has an element that is neither the `a`-predecessor nor the
`b`-successor of an element of the set. -/
theorem exists_travMax {a b : ℕ} (hco : a.Coprime b) (ha : 1 < a) (hab : a < b) {T : Finset ℕ}
    (hT : T ⊆ (finspan {a, b}).gaps) (hne : T.Nonempty) :
    ∃ g₀ ∈ T, g₀ + a ∉ T ∧ ∀ h ∈ T, h + b ≠ g₀ := by
  obtain ⟨g₀, hg₀T, hmax⟩ := Finset.exists_max_image T (travRank a b) hne
  refine ⟨g₀, hg₀T, fun hcon => ?_, fun h hhT hhb => ?_⟩
  · have h1 := travRank_sub_lt hco ha hab (hT hcon)
      (by rw [Nat.add_sub_cancel]; exact hT hg₀T)
    rw [Nat.add_sub_cancel] at h1
    exact absurd (hmax _ hcon) (by omega)
  · have h1 := travRank_add_lt hco ha hab (hT hhT) (by rw [hhb]; exact hT hg₀T)
    rw [hhb] at h1
    exact absurd (hmax h hhT) (by omega)



/-! ### The hook count of a word of order filters -/

/-- The label count of the labelling of a word of sets of gaps counts the positions containing the
gap. -/
theorem dims_wordLab {a b N : ℕ} (F : Fin N → Finset ℕ) (g : (finspan {a, b}).gaps) :
    dims (wordLab a b F) g = #{p ∈ (univ : Finset (Fin N)) | (g : ℕ) ∈ F p} := rfl

/-- The summed indicator vectors of a word of sets of gaps are its label counts. -/
theorem sum_filterVector_eq {a b N : ℕ} (F : Fin N → Finset ℕ) :
    ∑ p : Fin N, ReturnPath.filterVector a b (F p)
      = fun g => ((dims (wordLab a b F) g : ℕ) : ℤ) := by
  funext g
  rw [Finset.sum_apply]
  simp only [ReturnPath.filterVector, dims_wordLab]
  exact Finset.sum_boole _ _

/-- The label counts of a word of order filters form a cone vector bounded by the length of the
word. -/
theorem dims_mem_coneFinset {a b N : ℕ} (F : Fin N → Finset ℕ)
    (hF : ∀ p, Gaps.IsOrderFilter a b (F p)) : dims (wordLab a b F) ∈ coneFinset a b N := by
  have hstep : ∀ (c : ℕ), (∀ p : Fin N, ∀ g ∈ F p, ∀ h ∈ (finspan {a, b}).gaps,
      g + c = h → h ∈ F p) → ∀ g h : (finspan {a, b}).gaps, (g : ℕ) + c = (h : ℕ) →
      dims (wordLab a b F) g ≤ dims (wordLab a b F) h := by
    intro c hc g h hgh
    rw [dims_wordLab, dims_wordLab]
    refine Finset.card_le_card fun p hp => ?_
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, hc p (g : ℕ) hp.2 (h : ℕ) h.2 hgh⟩
  rw [mem_coneFinset_iff]
  refine ⟨fun g => ?_, hstep a fun p g hg h hh hgh => ?_, hstep b fun p g hg h hh hgh => ?_⟩
  · rw [dims_wordLab]
    calc #{p ∈ (univ : Finset (Fin N)) | (g : ℕ) ∈ F p} ≤ #(univ : Finset (Fin N)) :=
          Finset.card_filter_le _ _
      _ = N := by simp
  · exact (hF p).2 g hg h hh ⟨1, 0, by omega⟩
  · exact (hF p).2 g hg h hh ⟨0, 1, by omega⟩

/-- The hook count of a concatenation of primitive blocks splits into the block hook shift, the
quadratic form at the label counts, and the ordered interactions of the pairs of positions. -/
theorem hookCount_concat_split (rankOne : External.RankOneDinv)
    (coercivity : HJO.Literature.HuangCoercivity) {a b N : ℕ} (hco : a.Coprime b) (ha : 1 < a)
    (hab : a < b) (F : Fin N → Finset ℕ) (hF : ∀ p, Gaps.IsOrderFilter a b (F p)) :
    Paths.hookCount (ReturnPath.concat fun k => Primitive.primitivePath a b (F k))
      = Paths.kappaShift a b N
        + (HJO.Q a b fun g => ((dims (wordLab a b F) g : ℕ) : ℤ)).toNat
        + ∑ p : Fin N, ∑ r ∈ {r ∈ (univ : Finset (Fin N)) | p.val < r.val},
            interCount a b (F p) (F r) := by
  have hQ := ReturnPath.hookCount_concat_primitivePath_quadratic hco ha hab rankOne F hF
  rw [ReturnPath.wordWeight, sum_filterVector_eq F] at hQ
  have hint : ∑ p : Fin N, ∑ r ∈ {r ∈ (univ : Finset (Fin N)) | p.val < r.val},
      ReturnPath.orderedPart a b (F p) (F r)
      = ((∑ p : Fin N, ∑ r ∈ {r ∈ (univ : Finset (Fin N)) | p.val < r.val},
          interCount a b (F p) (F r) : ℕ) : ℤ) := by
    push_cast
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun r _ =>
      (interCount_eq_orderedPart hco ha hab (hF p) (hF r)).symm
  rw [hint] at hQ
  have hnn : 0 ≤ HJO.Q a b fun g => ((dims (wordLab a b F) g : ℕ) : ℤ) :=
    zero_le_Q coercivity hco ha hab (cast_mem_cone (dims_mem_coneFinset F hF))
  have htn : ((HJO.Q a b fun g => ((dims (wordLab a b F) g : ℕ) : ℤ)).toNat : ℤ)
      = HJO.Q a b fun g => ((dims (wordLab a b F) g : ℕ) : ℤ) := Int.toNat_of_nonneg hnn
  omega


/-! ### Peeling the traverse -/

/-! ### Peeling the last gap off a traverse -/

/-- If `g - a` and `g + b` are both gaps, then so is `g - a + b`. -/
theorem mem_gaps_sub_add_of {a b : ℕ} (hco : a.Coprime b) {g : ℕ}
    (hga : g - a ∈ (finspan {a, b}).gaps) (hgb : g + b ∈ (finspan {a, b}).gaps) :
    g - a + b ∈ (finspan {a, b}).gaps := by
  have h1 : 1 ≤ g - a := ReturnPath.one_le_of_mem_gaps hga
  rw [Gaps.mem_gaps_iff_not_exists a b hco]
  rw [Gaps.mem_gaps_iff_not_exists a b hco] at hgb
  rintro ⟨u, v, huv⟩
  refine hgb ⟨u + 1, v, ?_⟩
  have h2 : (u + 1) * a + v * b = u * a + v * b + a := by ring
  rw [h2, huv]
  omega

/-- Updating a labelling at one gap does not change the labels it reads at other naturals. -/
theorem lowLab_update (S : Labelling a b N) (g₀ : (finspan {a, b}).gaps) (M : Finset (Fin N))
    {j : ℕ} (hj : j ≠ (g₀ : ℕ)) : lowLab (Function.update S g₀ M) j = lowLab S j := by
  unfold lowLab
  by_cases h : j ∈ (finspan {a, b}).gaps
  · rw [dite_eq_left h, dite_eq_left h,
      Function.update_of_ne (fun he => hj (congrArg Subtype.val he)) M S]
  · rw [dite_eq_right h, dite_eq_right h]

/-- Updating a labelling at one gap does not change the labels it reads at other naturals. -/
theorem upLab_update (S : Labelling a b N) (g₀ : (finspan {a, b}).gaps) (M : Finset (Fin N))
    {j : ℕ} (hj : j ≠ (g₀ : ℕ)) : upLab (Function.update S g₀ M) j = upLab S j := by
  unfold upLab
  by_cases h : j ∈ (finspan {a, b}).gaps
  · rw [dite_eq_left h, dite_eq_left h,
      Function.update_of_ne (fun he => hj (congrArg Subtype.val he)) M S]
  · rw [dite_eq_right h, dite_eq_right h]

/-- Updating a labelling at one gap leaves the inversions at any gap none of whose three relevant
positions is the updated one. -/
theorem invAt_update (S : Labelling a b N) (g₀ : (finspan {a, b}).gaps) (M : Finset (Fin N))
    {g : (finspan {a, b}).gaps} (hg : g ≠ g₀) (hga : (g : ℕ) - a ≠ (g₀ : ℕ))
    (hgb : (g : ℕ) + b ≠ (g₀ : ℕ)) : invAt (Function.update S g₀ M) g = invAt S g := by
  rw [invAt, invAt, lowLab_update S g₀ M hga, upLab_update S g₀ M hgb,
    Function.update_of_ne hg M S]

/-- The empty traverse has exactly one chain, the empty labelling, of weight zero. -/
theorem chainGF_empty (q : R) (N : ℕ) (n : (finspan {a, b}).gaps → ℕ) :
    chainGF q (∅ : Finset ℕ) N n = 1 := by
  have hfil : ({S : Labelling a b N | IsChainOn (∅ : Finset ℕ) n S} :
      Finset (Labelling a b N)) = {(fun _ => ∅ : Labelling a b N)} := by
    refine eq_singleton_iff_unique_mem.mpr ⟨mem_filter.mpr ⟨mem_univ _, ?_⟩, ?_⟩
    · exact ⟨fun g hg => absurd hg (notMem_empty _), fun _ _ => rfl⟩
    · intro S hS
      obtain ⟨-, h2⟩ := (mem_filter.mp hS).2
      funext g
      exact h2 g (notMem_empty _)
  have hw : chainWeight (∅ : Finset ℕ) (fun _ => ∅ : Labelling a b N) = 0 := by
    simp [chainWeight]
  rw [chainGF, hfil, sum_singleton, hw, pow_zero]

/-- Removing a gap that the traverse visits last leaves an initial segment. -/
theorem isTravInit_erase {a b : ℕ} {T : Finset ℕ} (hT : IsTravInit a b T) {g₀ : ℕ}
    (hg₀ : g₀ ∈ T) (hmaxa : g₀ + a ∉ T) (hmaxb : ∀ h ∈ T, h + b ≠ g₀) :
    IsTravInit a b (T.erase g₀) := by
  have h1 : 1 ≤ g₀ := ReturnPath.one_le_of_mem_gaps (hT.1 hg₀)
  refine ⟨fun g hg => hT.1 (mem_of_mem_erase hg), fun g hg => ⟨fun hga => ?_, fun hgb => ?_⟩⟩
  · have hgT : g ∈ T := mem_of_mem_erase hg
    refine mem_erase.mpr ⟨?_, (hT.2 g hgT).1 hga⟩
    intro he
    exact hmaxa (by rw [show g₀ + a = g by omega]; exact hgT)
  · have hgT : g ∈ T := mem_of_mem_erase hg
    exact mem_erase.mpr ⟨hmaxb g hgT, (hT.2 g hgT).2 hgb⟩


/-- The three conditions a chain satisfies at a gap of its traverse. -/
theorem IsChainOn.mem {T : Finset ℕ} {n : (finspan {a, b}).gaps → ℕ} {S : Labelling a b N}
    (hS : IsChainOn T n S) {g : (finspan {a, b}).gaps} (hg : (g : ℕ) ∈ T) :
    lowLab S ((g : ℕ) - a) ⊆ S g ∧ S g ⊆ upLab S ((g : ℕ) + b) ∧ #(S g) = n g := hS.1 g hg

/-- A chain carries no labels at a gap outside its traverse. -/
theorem IsChainOn.notMem {T : Finset ℕ} {n : (finspan {a, b}).gaps → ℕ} {S : Labelling a b N}
    (hS : IsChainOn T n S) {g : (finspan {a, b}).gaps} (hg : (g : ℕ) ∉ T) : S g = ∅ := hS.2 g hg

/-- Peeling off the gap the traverse visits last multiplies the chain generating function by the
Gaussian factor there. -/
theorem chainGF_erase (q : R) {a b N : ℕ} (hco : a.Coprime b) (ha : 1 < a)
    (hgauss : ∀ L U : Finset (Fin N), L ⊆ U → ∀ k : ℕ, #L ≤ k →
      ∑ M ∈ {M ∈ U.powerset | L ⊆ M ∧ #M = k}, q ^ invCount (M \ L) (U \ L)
        = qChoose q (#U - #L) (k - #L))
    {T : Finset ℕ} (hT : IsTravInit a b T) {g₀ : ℕ} (hg₀ : g₀ ∈ T)
    (hmaxa : g₀ + a ∉ T) (hmaxb : ∀ h ∈ T, h + b ≠ g₀)
    {n : (finspan {a, b}).gaps → ℕ}
    (hmono : ∀ g h : (finspan {a, b}).gaps, (g : ℕ) + a = (h : ℕ) → n g ≤ n h) :
    chainGF q T N n = chainGF q (T.erase g₀) N n * gaussAt q a b N n g₀ := by
  have hb1 : 1 ≤ b := by
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · rw [Nat.coprime_zero_right] at hco; omega
    · exact hb
  have hg₀Γ : g₀ ∈ (finspan {a, b}).gaps := hT.1 hg₀
  obtain ⟨G₀, hG₀⟩ : ∃ G : (finspan {a, b}).gaps, (G : ℕ) = g₀ := ⟨⟨g₀, hg₀Γ⟩, rfl⟩
  have hg₀1 : 1 ≤ g₀ := ReturnPath.one_le_of_mem_gaps hg₀Γ
  have hnea' : g₀ - a ≠ g₀ := by omega
  have hneb' : g₀ + b ≠ g₀ := by omega
  have hnea : g₀ - a ≠ (G₀ : ℕ) := by rw [hG₀]; exact hnea'
  have hneb : g₀ + b ≠ (G₀ : ℕ) := by rw [hG₀]; exact hneb'
  have hcoe : ∀ g : (finspan {a, b}).gaps, (g : ℕ) = g₀ ↔ g = G₀ :=
    fun g => ⟨fun he => Subtype.ext (he.trans hG₀.symm), fun he => by rw [he, hG₀]⟩
  have hG₀T : (G₀ : ℕ) ∈ T := by rw [hG₀]; exact hg₀
  have hG₀T' : (G₀ : ℕ) ∉ T.erase g₀ := by rw [hG₀]; exact notMem_erase g₀ T
  have hnG₀ : HJO.extendNat n g₀ = n G₀ := by
    rw [HJO.extendNat, dite_eq_left hg₀Γ]
    exact congrArg n (Subtype.ext hG₀.symm)
  have key : ∀ g : (finspan {a, b}).gaps, (g : ℕ) ∈ T.erase g₀ →
      g ≠ G₀ ∧ (g : ℕ) - a ≠ (G₀ : ℕ) ∧ (g : ℕ) + b ≠ (G₀ : ℕ) := by
    intro g hg
    have hgT : (g : ℕ) ∈ T := mem_of_mem_erase hg
    have hne : (g : ℕ) ≠ g₀ := ne_of_mem_erase hg
    refine ⟨fun he => hne ((hcoe g).mpr he), ?_, ?_⟩
    · rw [hG₀]
      intro he
      exact hmaxa (by rw [show g₀ + a = (g : ℕ) by omega]; exact hgT)
    · rw [hG₀]
      exact hmaxb _ hgT
  have hlowT : g₀ - a ∈ (finspan {a, b}).gaps → g₀ - a ∈ T.erase g₀ := fun h =>
    mem_erase.mpr ⟨hnea', (hT.2 g₀ hg₀).1 h⟩
  have hupT : g₀ + b ∈ (finspan {a, b}).gaps → g₀ + b ∈ T.erase g₀ := fun h =>
    mem_erase.mpr ⟨hneb', (hT.2 g₀ hg₀).2 h⟩
  have hzero : ∀ S' : Labelling a b N, IsChainOn (T.erase g₀) n S' → S' G₀ = ∅ :=
    fun _ hS' => hS'.notMem hG₀T'
  have hcw : ∀ (X : Labelling a b N) (M : Finset (Fin N)),
      chainWeight (T.erase g₀) (Function.update X G₀ M) = chainWeight (T.erase g₀) X := by
    intro X M
    unfold chainWeight
    refine sum_congr rfl fun g _ => ?_
    by_cases hgT : (g : ℕ) ∈ T.erase g₀
    · obtain ⟨k1, k2, k3⟩ := key g hgT
      rw [ite_eq_left hgT, ite_eq_left hgT, invAt_update X G₀ M k1 k2 k3]
    · rw [ite_eq_right hgT, ite_eq_right hgT]
  have hsplit : ∀ X : Labelling a b N,
      chainWeight T X = chainWeight (T.erase g₀) X + invAt X G₀ := by
    intro X
    have hcong : ∀ g ∈ (univ : Finset (finspan {a, b}).gaps).erase G₀,
        (if (g : ℕ) ∈ T then invAt X g else 0)
          = (if (g : ℕ) ∈ T.erase g₀ then invAt X g else 0) := by
      intro g hg
      have hne : (g : ℕ) ≠ g₀ := fun he => ne_of_mem_erase hg ((hcoe g).mp he)
      by_cases hgT : (g : ℕ) ∈ T
      · rw [ite_eq_left hgT, ite_eq_left (mem_erase.mpr ⟨hne, hgT⟩)]
      · rw [ite_eq_right hgT, ite_eq_right (fun hc => hgT (mem_of_mem_erase hc))]
    unfold chainWeight
    rw [← add_sum_erase _ _ (mem_univ G₀), ← add_sum_erase _ _ (mem_univ G₀),
      sum_congr rfl hcong, ite_eq_left hG₀T, ite_eq_right hG₀T']
    omega
  have hcardL : ∀ S' : Labelling a b N, IsChainOn (T.erase g₀) n S' →
      #(lowLab S' (g₀ - a)) = HJO.extendNat n (g₀ - a) := by
    intro S' hS'
    by_cases h : g₀ - a ∈ (finspan {a, b}).gaps
    · rw [lowLab, dite_eq_left h, HJO.extendNat, dite_eq_left h]
      exact (hS'.mem (g := ⟨g₀ - a, h⟩) (hlowT h)).2.2
    · rw [lowLab, dite_eq_right h, HJO.extendNat, dite_eq_right h, card_empty]
  have hcardU : ∀ S' : Labelling a b N, IsChainOn (T.erase g₀) n S' →
      #(upLab S' (g₀ + b)) = Gaps.flag a b N n ((g₀ : ℤ) + b) := by
    intro S' hS'
    have hnn : ¬((g₀ : ℤ) + b < 0) := by omega
    have htn : ((g₀ : ℤ) + b).toNat = g₀ + b := by omega
    have hflag : Gaps.flag a b N n ((g₀ : ℤ) + b)
        = if g₀ + b ∈ (finspan {a, b}).gaps then HJO.extendNat n (g₀ + b) else N := by
      rw [Gaps.flag, ite_eq_right hnn, htn]
    by_cases h : g₀ + b ∈ (finspan {a, b}).gaps
    · rw [upLab, dite_eq_left h, hflag, ite_eq_left h, HJO.extendNat, dite_eq_left h]
      exact (hS'.mem (g := ⟨g₀ + b, h⟩) (hupT h)).2.2
    · rw [upLab, dite_eq_right h, hflag, ite_eq_right h, card_univ, Fintype.card_fin]
  have hsub : ∀ S' : Labelling a b N, IsChainOn (T.erase g₀) n S' →
      lowLab S' (g₀ - a) ⊆ upLab S' (g₀ + b) := by
    intro S' hS'
    by_cases hga : g₀ - a ∈ (finspan {a, b}).gaps
    · by_cases hgb : g₀ + b ∈ (finspan {a, b}).gaps
      · have h1 : 1 ≤ g₀ - a := ReturnPath.one_le_of_mem_gaps hga
        have hm : g₀ - a + b ∈ (finspan {a, b}).gaps := mem_gaps_sub_add_of hco hga hgb
        have e1 : g₀ - a + b = g₀ + b - a := by omega
        have s1 : S' ⟨g₀ - a, hga⟩ ⊆ upLab S' (g₀ - a + b) :=
          (hS'.mem (g := ⟨g₀ - a, hga⟩) (hlowT hga)).2.1
        have s2 : lowLab S' (g₀ + b - a) ⊆ S' ⟨g₀ + b, hgb⟩ :=
          (hS'.mem (g := ⟨g₀ + b, hgb⟩) (hupT hgb)).1
        rw [upLab, dite_eq_left hm] at s1
        rw [← e1, lowLab, dite_eq_left hm] at s2
        rw [lowLab, dite_eq_left hga, upLab, dite_eq_left hgb]
        exact s1.trans s2
      · rw [upLab, dite_eq_right hgb]
        exact subset_univ _
    · rw [lowLab, dite_eq_right hga]
      exact empty_subset _
  have hcardle : ∀ S' : Labelling a b N, IsChainOn (T.erase g₀) n S' →
      #(lowLab S' (g₀ - a)) ≤ n G₀ := by
    intro S' hS'
    rw [hcardL S' hS']
    by_cases h : g₀ - a ∈ (finspan {a, b}).gaps
    · have h1 : 1 ≤ g₀ - a := ReturnPath.one_le_of_mem_gaps h
      rw [HJO.extendNat, dite_eq_left h]
      exact hmono ⟨g₀ - a, h⟩ G₀ (by rw [hG₀]; change g₀ - a + a = g₀; omega)
    · rw [HJO.extendNat, dite_eq_right h]
      exact Nat.zero_le _
  have hmaps : ∀ S ∈ ({S : Labelling a b N | IsChainOn T n S} : Finset (Labelling a b N)),
      Function.update S G₀ (∅ : Finset (Fin N))
        ∈ ({S : Labelling a b N | IsChainOn (T.erase g₀) n S} : Finset (Labelling a b N)) := by
    intro S hS
    have hSc : IsChainOn T n S := (mem_filter.mp hS).2
    refine mem_filter.mpr ⟨mem_univ _, fun g hg => ?_, fun g hg => ?_⟩
    · obtain ⟨k1, k2, k3⟩ := key g hg
      rw [Function.update_of_ne k1, lowLab_update S G₀ _ k2, upLab_update S G₀ _ k3]
      exact hSc.mem (mem_of_mem_erase hg)
    · by_cases he : g = G₀
      · rw [he, Function.update_self]
      · rw [Function.update_of_ne he]
        exact hSc.notMem fun hc => hg (mem_erase.mpr ⟨fun hx => he ((hcoe g).mp hx), hc⟩)
  have hinner : ∀ S' ∈ ({S : Labelling a b N | IsChainOn (T.erase g₀) n S} :
        Finset (Labelling a b N)),
      ∑ S ∈ {S ∈ ({S : Labelling a b N | IsChainOn T n S} : Finset (Labelling a b N)) |
          Function.update S G₀ (∅ : Finset (Fin N)) = S'}, q ^ chainWeight T S
        = q ^ chainWeight (T.erase g₀) S' * gaussAt q a b N n g₀ := by
    intro S' hS'
    have hS'c : IsChainOn (T.erase g₀) n S' := (mem_filter.mp hS').2
    have hself : Function.update S' G₀ (∅ : Finset (Fin N)) = S' := by
      rw [← hzero S' hS'c, Function.update_eq_self]
    have hgg : gaussAt q a b N n g₀ = qChoose q
        (#(upLab S' (g₀ + b)) - #(lowLab S' (g₀ - a))) (n G₀ - #(lowLab S' (g₀ - a))) := by
      rw [gaussAt, hcardU S' hS'c, hcardL S' hS'c, hnG₀]
    rw [hgg, ← hgauss (lowLab S' (g₀ - a)) (upLab S' (g₀ + b)) (hsub S' hS'c) (n G₀)
      (hcardle S' hS'c), mul_sum]
    refine sum_nbij' (fun S => S G₀) (fun M => Function.update S' G₀ M) ?_ ?_ ?_ ?_ ?_
    · intro S hS
      obtain ⟨hSA, heq⟩ := mem_filter.mp hS
      have hSc : IsChainOn T n S := (mem_filter.mp hSA).2
      have hc := hSc.mem (g := G₀) hG₀T
      rw [hG₀] at hc
      obtain ⟨c1, c2, c3⟩ := hc
      have hL' : lowLab S' (g₀ - a) = lowLab S (g₀ - a) := by
        rw [← heq, lowLab_update S G₀ (∅ : Finset (Fin N)) hnea]
      have hU' : upLab S' (g₀ + b) = upLab S (g₀ + b) := by
        rw [← heq, upLab_update S G₀ (∅ : Finset (Fin N)) hneb]
      refine mem_filter.mpr ⟨mem_powerset.mpr ?_, ?_, c3⟩
      · rw [hU']; exact c2
      · rw [hL']; exact c1
    · intro M hM
      obtain ⟨hMU, hLM, hMcard⟩ := mem_filter.mp hM
      have hMU' : M ⊆ upLab S' (g₀ + b) := mem_powerset.mp hMU
      refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, fun g hgT => ?_, fun g hgT => ?_⟩, ?_⟩
      · by_cases he : g = G₀
        · rw [he, Function.update_self, hG₀, lowLab_update S' G₀ M hnea,
            upLab_update S' G₀ M hneb]
          exact ⟨hLM, hMU', hMcard⟩
        · have hgT' : (g : ℕ) ∈ T.erase g₀ :=
            mem_erase.mpr ⟨fun hx => he ((hcoe g).mp hx), hgT⟩
          obtain ⟨k1, k2, k3⟩ := key g hgT'
          rw [Function.update_of_ne k1, lowLab_update S' G₀ M k2, upLab_update S' G₀ M k3]
          exact hS'c.mem hgT'
      · have he : g ≠ G₀ := fun hx => hgT (by rw [hx]; exact hG₀T)
        rw [Function.update_of_ne he]
        exact hS'c.notMem fun hc => hgT (mem_of_mem_erase hc)
      · rw [Function.update_idem, hself]
    · intro S hS
      obtain ⟨-, heq⟩ := mem_filter.mp hS
      rw [← heq, Function.update_idem, Function.update_eq_self]
    · intro M _
      exact Function.update_self G₀ M S'
    · intro S hS
      obtain ⟨-, heq⟩ := mem_filter.mp hS
      have hL' : lowLab S' (g₀ - a) = lowLab S (g₀ - a) := by
        rw [← heq, lowLab_update S G₀ (∅ : Finset (Fin N)) hnea]
      have hU' : upLab S' (g₀ + b) = upLab S (g₀ + b) := by
        rw [← heq, upLab_update S G₀ (∅ : Finset (Fin N)) hneb]
      have hcws : chainWeight (T.erase g₀) S' = chainWeight (T.erase g₀) S := by
        rw [← heq]; exact hcw S ∅
      have hinv : invAt S G₀ = invCount (S G₀ \ lowLab S (g₀ - a))
          (upLab S (g₀ + b) \ lowLab S (g₀ - a)) := by rw [invAt, hG₀]
      rw [← pow_add, hsplit S, hL', hU', hcws, hinv]
  unfold chainGF
  rw [sum_mul, ← sum_fiberwise_of_maps_to hmaps fun S => q ^ chainWeight T S]
  exact sum_congr rfl hinner


/-- The order filters of the gap set form a finite type. -/
noncomputable instance instFintypeOrderFilter (a b : ℕ) :
    Fintype {G : Finset ℕ // Gaps.IsOrderFilter a b G} :=
  Set.Finite.fintype <| Set.Finite.subset
    ((finspan {a, b}).gaps.powerset : Finset (Finset ℕ)).finite_toSet
    fun _ hG => Finset.mem_coe.mpr (Finset.mem_powerset.mpr hG.1)


/-! ### Order filters from the two generator steps -/

/-- Upward closure under the two generator steps inside the gap set makes a set of gaps an order
filter. -/
theorem isOrderFilter_of_steps {a b : ℕ} (hco : a.Coprime b) {F : Finset ℕ}
    (hsub : F ⊆ (finspan {a, b}).gaps)
    (hstepa : ∀ g ∈ F, g + a ∈ (finspan {a, b}).gaps → g + a ∈ F)
    (hstepb : ∀ g ∈ F, g + b ∈ (finspan {a, b}).gaps → g + b ∈ F) :
    Gaps.IsOrderFilter a b F := by
  have key : ∀ u v : ℕ, ∀ g ∈ F, g + (u * a + v * b) ∈ (finspan {a, b}).gaps →
      g + (u * a + v * b) ∈ F := by
    intro u
    induction u with
    | zero =>
      intro v
      induction v with
      | zero => intro g hg _; simpa using hg
      | succ v ih =>
        intro g hg hmem
        have e : g + (0 * a + (v + 1) * b) = g + (0 * a + v * b) + b := by ring
        rw [e] at hmem ⊢
        exact hstepb _ (ih g hg (mem_gaps_of_add_right hco hmem)) hmem
    | succ u ih =>
      intro v g hg hmem
      have e : g + ((u + 1) * a + v * b) = g + (u * a + v * b) + a := by ring
      rw [e] at hmem ⊢
      exact hstepa _ (ih v g hg (mem_gaps_of_add_left hco hmem)) hmem
  refine ⟨hsub, fun g hg h hh hgh => ?_⟩
  obtain ⟨u, v, rfl⟩ := hgh
  exact key u v g hg hh

/-! ### Reading a labelling at a natural number -/

/-- At a gap the low reading of a labelling is the label set of the labelling. -/
theorem lowLab_of_mem (S : Labelling a b N) {j : ℕ} (hj : j ∈ (finspan {a, b}).gaps) :
    lowLab S j = S ⟨j, hj⟩ := by simp [lowLab, hj]

/-- At a gap the high reading of a labelling is the label set of the labelling. -/
theorem upLab_of_mem (S : Labelling a b N) {j : ℕ} (hj : j ∈ (finspan {a, b}).gaps) :
    upLab S j = S ⟨j, hj⟩ := by simp [upLab, hj]

/-- A position labels a gap in the labelling of a word exactly when its set contains the gap. -/
theorem mem_wordLab {F : Fin N → Finset ℕ} {g : (finspan {a, b}).gaps} {p : Fin N} :
    p ∈ wordLab a b F g ↔ (g : ℕ) ∈ F p := by simp [wordLab]

/-- The low reading of the labelling of a word: a position occurs exactly at those naturals that
are gaps and lie in its set. -/
theorem mem_lowLab_wordLab {F : Fin N → Finset ℕ} {j : ℕ} {p : Fin N} :
    p ∈ lowLab (wordLab a b F) j ↔ j ∈ (finspan {a, b}).gaps ∧ j ∈ F p := by
  unfold lowLab
  split_ifs with h
  · simp [wordLab, h]
  · simp [h]

/-- The high reading of the labelling of a word: a position occurs at a natural exactly when its
set contains it or the natural is not a gap. -/
theorem mem_upLab_wordLab {F : Fin N → Finset ℕ} {j : ℕ} {p : Fin N} :
    p ∈ upLab (wordLab a b F) j ↔ j ∈ F p ∨ j ∉ (finspan {a, b}).gaps := by
  unfold upLab
  split_ifs with h
  · simp [wordLab, h]
  · simp [h]

/-! ### The word attached to a labelling -/

/-- The word of sets of gaps attached to a labelling: the `p`-th set collects the gaps carrying
the label `p`. -/
def labWord (a b : ℕ) {N : ℕ} (S : Labelling a b N) (p : Fin N) : Finset ℕ :=
  {g ∈ (finspan {a, b}).gaps | p ∈ lowLab S g}

/-- A natural number lies in the `p`-th set of the word of a labelling exactly when it is a gap
labelled by `p`. -/
theorem mem_labWord {S : Labelling a b N} {p : Fin N} {j : ℕ} :
    j ∈ labWord a b S p ↔ ∃ h : j ∈ (finspan {a, b}).gaps, p ∈ S ⟨j, h⟩ := by
  simp only [labWord, Finset.mem_filter]
  exact ⟨fun ⟨hj, hp⟩ => ⟨hj, by rwa [lowLab_of_mem S hj] at hp⟩,
    fun ⟨hj, hp⟩ => ⟨hj, by rwa [lowLab_of_mem S hj]⟩⟩

/-- The sets of the word of a labelling consist of gaps. -/
theorem labWord_subset (S : Labelling a b N) (p : Fin N) :
    labWord a b S p ⊆ (finspan {a, b}).gaps := fun _ hj => (Finset.mem_filter.mp hj).1

/-! ### Chains and words -/

/-- The labelling of a word of order filters is a chain over the whole gap set. -/
theorem isChainOn_wordLab {a b N : ℕ} (F : Fin N → Finset ℕ)
    (hF : ∀ p, Gaps.IsOrderFilter a b (F p)) :
    IsChainOn (finspan {a, b}).gaps (dims (wordLab a b F)) (wordLab a b F) := by
  refine ⟨fun g _ => ⟨fun p hp => ?_, fun p hp => ?_, rfl⟩, fun g hg => absurd g.2 hg⟩
  · obtain ⟨hj, hpj⟩ := mem_lowLab_wordLab.mp hp
    have h0 : (g : ℕ) - a ≠ 0 := fun h => (finspan {a, b}).zero_notMem_gaps (h ▸ hj)
    exact mem_wordLab.mpr ((hF p).2 _ hpj _ g.2 ⟨1, 0, by omega⟩)
  · rw [mem_wordLab] at hp
    rw [mem_upLab_wordLab]
    by_cases hb : (g : ℕ) + b ∈ (finspan {a, b}).gaps
    · exact Or.inl ((hF p).2 _ hp _ hb ⟨0, 1, by ring⟩)
    · exact Or.inr hb

/-- The word of a chain consists of order filters. -/
theorem isOrderFilter_labWord {a b N : ℕ} (hco : a.Coprime b)
    {n : (finspan {a, b}).gaps → ℕ} {S : Labelling a b N}
    (hS : IsChainOn (finspan {a, b}).gaps n S) (p : Fin N) :
    Gaps.IsOrderFilter a b (labWord a b S p) := by
  refine isOrderFilter_of_steps hco (labWord_subset S p) (fun g hg hga => ?_) fun g hg hgb => ?_
  · obtain ⟨hgm, hp⟩ := mem_labWord.mp hg
    refine mem_labWord.mpr ⟨hga, (hS.1 ⟨g + a, hga⟩ hga).1 ?_⟩
    rw [show ((⟨g + a, hga⟩ : (finspan {a, b}).gaps) : ℕ) - a = g from by simp,
      lowLab_of_mem S hgm]
    exact hp
  · obtain ⟨hgm, hp⟩ := mem_labWord.mp hg
    have h2 := (hS.1 ⟨g, hgm⟩ hgm).2.1 hp
    rw [show ((⟨g, hgm⟩ : (finspan {a, b}).gaps) : ℕ) + b = g + b from rfl,
      upLab_of_mem S hgb] at h2
    exact mem_labWord.mpr ⟨hgb, h2⟩

/-! ### Counting the inversions of a word -/

/-- Removing a common lower part from a selected subset and its ambient set leaves the inversions
unchanged: they are the ordered pairs of a selected element and a larger element outside the
selection. -/
theorem invCount_sdiff {L M U : Finset ι} (hLM : L ⊆ M) :
    invCount (M \ L) (U \ L) = #{x ∈ (M \ L) ×ˢ (U \ M) | x.1 < x.2} := by
  have h : (U \ L) \ (M \ L) = U \ M := by
    ext x
    simp only [Finset.mem_sdiff]
    exact ⟨fun ⟨⟨hU, hL⟩, hn⟩ => ⟨hU, fun hM => hn ⟨hM, hL⟩⟩,
      fun ⟨hU, hM⟩ => ⟨⟨hU, fun hL => hM (hLM hL)⟩, fun h' => hM h'.1⟩⟩
  rw [invCount, h]

/-- The inversions the labelling of a word of order filters contributes at a gap: the ordered
pairs of positions where the gap enters the first set and leaves the second one. -/
theorem invAt_wordLab {a b N : ℕ} (F : Fin N → Finset ℕ)
    (hF : ∀ p, Gaps.IsOrderFilter a b (F p)) (g : (finspan {a, b}).gaps) :
    invAt (wordLab a b F) g = #{x ∈ (univ : Finset (Fin N × Fin N)) | x.1 < x.2 ∧
      (g : ℕ) ∈ F x.1 ∧ (g : ℕ) - a ∉ F x.1 ∧ (g : ℕ) ∉ F x.2 ∧
      ((g : ℕ) + b ∈ F x.2 ∨ (g : ℕ) + b ∉ (finspan {a, b}).gaps)} := by
  have hchain := (isChainOn_wordLab F hF).1 g g.2
  rw [invAt, invCount_sdiff hchain.1]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_sdiff, Finset.mem_univ, true_and,
    mem_wordLab, mem_lowLab_wordLab, mem_upLab_wordLab, not_and]
  exact ⟨fun ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩ => ⟨h5, h1, fun hm => h2 ((hF _).1 hm) hm, h4, h3⟩,
    fun ⟨h5, h1, h2, h3, h4⟩ => ⟨⟨⟨h1, fun _ hm => h2 hm⟩, h4, h3⟩, h5⟩⟩

/-- The inversions of the labelling of a word of order filters are the ordered interactions of the
pairs of positions of the word. -/
theorem chainWeight_wordLab {a b N : ℕ} (F : Fin N → Finset ℕ)
    (hF : ∀ p, Gaps.IsOrderFilter a b (F p)) :
    chainWeight (finspan {a, b}).gaps (wordLab a b F)
      = ∑ p : Fin N, ∑ r ∈ {r ∈ (univ : Finset (Fin N)) | p.val < r.val},
          interCount a b (F p) (F r) := by
  have h1 : chainWeight (finspan {a, b}).gaps (wordLab a b F)
      = ∑ g ∈ (finspan {a, b}).gaps, ∑ p : Fin N, ∑ r : Fin N,
        if p.val < r.val ∧ g ∈ F p ∧ g - a ∉ F p ∧ g ∉ F r ∧
          (g + b ∈ F r ∨ g + b ∉ (finspan {a, b}).gaps) then 1 else 0 := by
    rw [chainWeight, ← Finset.sum_coe_sort (finspan {a, b}).gaps]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [ite_eq_left g.2, invAt_wordLab F hF g, Finset.card_filter, Fintype.sum_prod_type]
    simp only [Fin.lt_def]
  have h2 : ∑ p : Fin N, ∑ r ∈ {r ∈ (univ : Finset (Fin N)) | p.val < r.val},
        interCount a b (F p) (F r)
      = ∑ p : Fin N, ∑ r : Fin N, ∑ g ∈ (finspan {a, b}).gaps,
        if p.val < r.val ∧ g ∈ F p ∧ g - a ∉ F p ∧ g ∉ F r ∧
          (g + b ∈ F r ∨ g + b ∉ (finspan {a, b}).gaps) then 1 else 0 := by
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [interCount, Finset.card_filter]
    by_cases h : p.val < r.val
    · rw [ite_eq_left h]
      exact Finset.sum_congr rfl fun g _ => by simp [h]
    · rw [ite_eq_right h]
      exact (Finset.sum_eq_zero fun g _ => by simp [h]).symm
  rw [h1, h2, Finset.sum_comm]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_comm

/-! ### Words of order filters are chains -/

/-- The word of the labelling of a word of order filters recovers the word. -/
theorem labWord_wordLab {a b N : ℕ} {F : Fin N → Finset ℕ}
    (hF : ∀ p, Gaps.IsOrderFilter a b (F p)) (p : Fin N) :
    labWord a b (wordLab a b F) p = F p := by
  ext j
  rw [mem_labWord]
  exact ⟨fun ⟨_, hp⟩ => mem_wordLab.mp hp, fun hj => ⟨(hF p).1 hj, mem_wordLab.mpr hj⟩⟩

/-- The labelling of the word of a labelling recovers the labelling. -/
theorem wordLab_labWord (S : Labelling a b N) : wordLab a b (labWord a b S) = S := by
  funext g
  ext p
  rw [mem_wordLab, mem_labWord]
  exact ⟨fun ⟨_, hp⟩ => hp, fun hp => ⟨g.2, hp⟩⟩

/-- Words of order filters with prescribed label counts are the chains with those counts. -/
theorem sum_words_eq_chainGF {R : Type*} [CommSemiring R] (q : R) {a b N : ℕ}
    (hco : a.Coprime b) (n : (finspan {a, b}).gaps → ℕ) :
    ∑ F ∈ {F : Fin N → {G : Finset ℕ // Gaps.IsOrderFilter a b G} |
        dims (wordLab a b fun p => (F p : Finset ℕ)) = n},
        q ^ chainWeight (finspan {a, b}).gaps (wordLab a b fun p => (F p : Finset ℕ))
      = chainGF q (finspan {a, b}).gaps N n := by
  rw [chainGF]
  refine Finset.sum_bij' (fun F _ => wordLab a b fun p => (F p : Finset ℕ))
    (fun S hS p => ⟨labWord a b S p,
      isOrderFilter_labWord hco (Finset.mem_filter.mp hS).2 p⟩)
    (fun F hF => Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Finset.mem_filter.mp hF).2 ▸ isChainOn_wordLab _ fun p => (F p).2⟩)
    (fun S hS => Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
    (fun F _ => funext fun p => Subtype.ext (labWord_wordLab (fun p => (F p).2) p))
    (fun S _ => wordLab_labWord S) fun F _ => rfl
  rw [show (fun p => ((⟨labWord a b S p, isOrderFilter_labWord hco
    (Finset.mem_filter.mp hS).2 p⟩ : {G : Finset ℕ // Gaps.IsOrderFilter a b G}) :
      Finset ℕ)) = labWord a b S from rfl, wordLab_labWord S]
  exact funext fun g => ((Finset.mem_filter.mp hS).2.1 g g.2).2.2



/-! ### The traverse product -/

/-- The whole gap set is an initial segment of the traverse. -/
theorem isTravInit_gaps (a b : ℕ) : IsTravInit a b (finspan {a, b}).gaps :=
  ⟨Finset.Subset.refl _, fun _ _ => ⟨fun h => h, fun h => h⟩⟩

/-- Over an initial segment of the traverse the chain generating function is the product of the
Gaussian factors, by induction on the number of gaps visited. -/
theorem chainGF_eq_prod_card {R : Type*} [CommSemiring R] (q : R) {a b : ℕ} (hco : a.Coprime b)
    (ha : 1 < a) (hab : a < b) {N : ℕ} {n : (finspan {a, b}).gaps → ℕ}
    (hmono : ∀ g h : (finspan {a, b}).gaps, (g : ℕ) + a = (h : ℕ) → n g ≤ n h) :
    ∀ m : ℕ, ∀ T : Finset ℕ, #T = m → IsTravInit a b T →
      chainGF q T N n = ∏ g ∈ T, gaussAt q a b N n g := by
  intro m
  induction m with
  | zero =>
    intro T hcard _
    rw [Finset.card_eq_zero.mp hcard, chainGF_empty, Finset.prod_empty]
  | succ m ih =>
    intro T hcard hinit
    obtain ⟨g₀, hg₀, hmaxa, hmaxb⟩ :=
      exists_travMax hco ha hab hinit.1 (Finset.card_pos.mp (by omega))
    rw [chainGF_erase q hco ha (fun _ _ hLU _ hk => sum_pow_invCount_between q hLU hk) hinit hg₀
        hmaxa hmaxb hmono,
      ih (T.erase g₀) (by rw [Finset.card_erase_of_mem hg₀]; omega)
        (isTravInit_erase hinit hg₀ hmaxa hmaxb),
      ← Finset.mul_prod_erase T _ hg₀]
    ring

/-- Over an initial segment of the traverse the chain generating function is the product of the
Gaussian factors. -/
theorem chainGF_eq_prod {R : Type*} [CommSemiring R] (q : R) {a b : ℕ} (hco : a.Coprime b)
    (ha : 1 < a) (hab : a < b) {N : ℕ} {n : (finspan {a, b}).gaps → ℕ}
    (hn : n ∈ coneFinset a b N) {T : Finset ℕ} (hT : IsTravInit a b T) :
    chainGF q T N n = ∏ g ∈ T, gaussAt q a b N n g :=
  chainGF_eq_prod_card q hco ha hab ((mem_coneFinset_iff n).mp hn).2.1 #T T rfl hT

/-! ### The filter-word expansion of the finite series -/

/-- The finite series expanded over words of order filters: a word contributes the quadratic form
at its label counts together with one ordered interaction per ordered pair of positions. -/
theorem finiteSeries_eq_sum_words (goodTraverse : External.GoodTraverse) {a b : ℕ}
    (hco : a.Coprime b) (ha : 1 < a) (hab : a < b) (N : ℕ) :
    Gaps.finiteSeries a b N
      = ∑ F : Fin N → {G : Finset ℕ // Gaps.IsOrderFilter a b G},
          (X : ℤ⟦X⟧) ^ ((HJO.Q a b fun g =>
              ((dims (wordLab a b fun p => (F p : Finset ℕ)) g : ℕ) : ℤ)).toNat
            + chainWeight (finspan {a, b}).gaps (wordLab a b fun p => (F p : Finset ℕ))) := by
  rw [finiteSeries_eq_sum hco ha hab N,
    ← Finset.sum_fiberwise_of_maps_to
      (g := fun F : Fin N → {G : Finset ℕ // Gaps.IsOrderFilter a b G} =>
        dims (wordLab a b fun p => (F p : Finset ℕ)))
      (fun F _ => dims_mem_coneFinset _ fun p => (F p).2) _]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hterm : ∀ F ∈ ({F | dims (wordLab a b fun p => (F p : Finset ℕ)) = n} :
        Finset (Fin N → {G : Finset ℕ // Gaps.IsOrderFilter a b G})),
      (X : ℤ⟦X⟧) ^ ((HJO.Q a b fun g =>
            ((dims (wordLab a b fun p => (F p : Finset ℕ)) g : ℕ) : ℤ)).toNat
          + chainWeight (finspan {a, b}).gaps (wordLab a b fun p => (F p : Finset ℕ)))
        = X ^ (HJO.Q a b fun g => ((n g : ℕ) : ℤ)).toNat
          * X ^ chainWeight (finspan {a, b}).gaps (wordLab a b fun p => (F p : Finset ℕ)) := by
    intro F hF
    rw [(Finset.mem_filter.mp hF).2, pow_add]
  have hsum : ∑ F ∈ ({F | dims (wordLab a b fun p => (F p : Finset ℕ)) = n} :
        Finset (Fin N → {G : Finset ℕ // Gaps.IsOrderFilter a b G})),
        (X : ℤ⟦X⟧) ^ ((HJO.Q a b fun g =>
            ((dims (wordLab a b fun p => (F p : Finset ℕ)) g : ℕ) : ℤ)).toNat
          + chainWeight (finspan {a, b}).gaps (wordLab a b fun p => (F p : Finset ℕ)))
      = ∑ F ∈ ({F | dims (wordLab a b fun p => (F p : Finset ℕ)) = n} :
        Finset (Fin N → {G : Finset ℕ // Gaps.IsOrderFilter a b G})),
        (X : ℤ⟦X⟧) ^ (HJO.Q a b fun g => ((n g : ℕ) : ℤ)).toNat
          * X ^ chainWeight (finspan {a, b}).gaps (wordLab a b fun p => (F p : Finset ℕ)) :=
    Finset.sum_congr rfl hterm
  rw [hsum, ← Finset.mul_sum, sum_words_eq_chainGF (X : ℤ⟦X⟧) hco n,
    chainGF_eq_prod (X : ℤ⟦X⟧) hco ha hab hn (isTravInit_gaps a b),
    ← prod_gaps_type a b (gaussAt (X : ℤ⟦X⟧) a b N n),
    prod_gaussAt_eq_multinomial goodTraverse hco ha hab hn, mul_comm]

/-! ### The return-path identity -/

/-- The return-path identity: the finite series, shifted by the block hook count, is the hook
generating function of the paths that return to the diagonal after every block. -/
@[hjo "prop_return"]
theorem pow_kappaShift_mul_finiteSeries (rankOne : External.RankOneDinv)
    (goodTraverse : External.GoodTraverse) (coercivity : HJO.Literature.HuangCoercivity)
    {a b : ℕ} (hco : a.Coprime b) (ha : 1 < a) (hab : a < b) (N : ℕ) :
    (X : ℤ⟦X⟧) ^ Paths.kappaShift a b N * Gaps.finiteSeries a b N
      = ∑ y ∈ {y ∈ (univ : Finset (Paths.Heights a b N)) | Paths.IsReturnPath y},
          X ^ Paths.hookCount y := by
  rw [ReturnPath.sum_pow_hookCount_returnPath hco ha (X : ℤ⟦X⟧),
    finiteSeries_eq_sum_words goodTraverse hco ha hab N, Finset.mul_sum]
  refine Finset.sum_congr rfl fun F _ => ?_
  rw [hookCount_concat_split rankOne coercivity hco ha hab _ fun p => (F p).2,
    chainWeight_wordLab _ fun p => (F p).2, ← pow_add, Nat.add_assoc]

end HJO.ReturnPathSolves
