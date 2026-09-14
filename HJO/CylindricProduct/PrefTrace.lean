/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CylindricProduct.Assembled
public import HJO.CylindricProduct.Commutation
public import HJO.CylindricProduct.PathSum
public import HJO.CylindricProduct.StepWord
public import HJO.Series.Summable
public meta import HJO.Attr

/-! # The slot-ordered reading of the cycle, and the sequences that survive its trace

`prod_slotPairs_mul_unboundedGF` compares two readings of the same cycle: the *slot-ordered* one,
which puts one grading `Q(q)` and one strip factor `Γ_±(1)` at each of the `d` slots of the step
word, and the *sorted* one of `transferKernel`, which collects the lowering factors, then one
grading `Q(q^d)`, then the raising factors. The first computes `C_c(q)` directly; the second is the
one the winding recursion evaluates; and the price of sorting is the crossing prefactor.

This file is the first step of the first half of that comparison: the slot-ordered word, and the
identification of the closed sequences of partitions that its trace actually sees.

* `slotKernel a b t` is the slot factor `Q(q) Γ_{ε_t}(1)`, raising or lowering as
  `IsRaising` prescribes at slot `t`, and `slotWord a b c` is the list of them for the step word
  shifted by `c` -- the shift being the one `transferKernel` performs to put a lowering slot
  last, and the one `slotPairs` already counts over.
* The slot-ordered word is **not** step-bounded: keeping one grading per slot forces the strip
  factors to carry the argument `1`, and `Γ_±(1)` is not divisible by any positive power of `q`.
  What it is instead is grade-bounded, one grading sitting in each factor, and that is the bound
  `PathSum`'s grade-bounded half is for.
* `RespectsWord` names the closed sequences the entries do not kill: at a raising slot the next
  partition contains this one by a horizontal strip and at a lowering slot the other way round,
  which is exactly the conclusion of `isHStrip_slice_of_isRaising` and
  `isHStrip_slice_of_not_isRaising` in their residue labelling.
* `ktrace_slotWord_eq_tsum` is the result: the trace of the slot-ordered word is the sum, over the
  sequences respecting the step word, of `q` to the total of their sizes.

The comparison has three parts, and all three are below: (a) the slice correspondence, (b) the
sorting induction, and (c) the count of interchanged pairs. The last section multiplies them into
`prod_slotPairs_mul_unboundedGF`.
-/

@[expose] public section

open Finset PowerSeries
open scoped QTheory Topology PowerSeries.DiscreteTopology

namespace HJO.CylindricProduct

/-! ### The slot factor and the slot-ordered word -/

/-- The **slot factor** of the slot-ordered reading of the cycle: the grading `Q(q)` followed by
the strip factor `IsRaising` prescribes at slot `t`, with the argument `1`. -/
noncomputable def slotKernel (a b t : ℕ) : Kernel :=
  kmul (grading X) (if IsRaising a b t then gammaPlus 1 else gammaMinus 1)

theorem slotKernel_apply (a b t : ℕ) (lam nu : Part) :
    slotKernel a b t lam nu
      = X ^ lam.size * (if IsRaising a b t then gammaPlus 1 lam nu else gammaMinus 1 lam nu) := by
  simp only [slotKernel, grading_kmul]
  by_cases h : IsRaising a b t <;> simp [h]

/-- The strip condition the slot factor is supported on: the numerator of the strip is the second
argument at a raising slot and the first at a lowering one. -/
def IsSlotStrip (a b t : ℕ) (lam nu : Part) : Prop :=
  (IsRaising a b t → IsHStrip nu lam) ∧ (¬ IsRaising a b t → IsHStrip lam nu)

noncomputable instance instDecidableIsSlotStrip (a b t : ℕ) (lam nu : Part) :
    Decidable (IsSlotStrip a b t lam nu) := Classical.dec _

theorem isSlotStrip_iff_of_isRaising {a b t : ℕ} (h : IsRaising a b t) (lam nu : Part) :
    IsSlotStrip a b t lam nu ↔ IsHStrip nu lam :=
  ⟨fun hs => hs.1 h, fun hs => ⟨fun _ => hs, fun hn => absurd h hn⟩⟩

theorem isSlotStrip_iff_of_not_isRaising {a b t : ℕ} (h : ¬ IsRaising a b t) (lam nu : Part) :
    IsSlotStrip a b t lam nu ↔ IsHStrip lam nu :=
  ⟨fun hs => hs.2 h, fun hs => ⟨fun hr => absurd hr h, fun _ => hs⟩⟩

theorem slotKernel_apply_eq_ite (a b t : ℕ) (lam nu : Part) :
    slotKernel a b t lam nu
      = X ^ lam.size * (if IsSlotStrip a b t lam nu then 1 else 0) := by
  rw [slotKernel_apply]
  refine congrArg (fun u => X ^ lam.size * u) ?_
  by_cases h : IsRaising a b t
  · rw [ite_eq_left h]
    by_cases hs : IsHStrip nu lam
    · rw [gammaPlus_of hs, one_pow, ite_eq_left ((isSlotStrip_iff_of_isRaising h lam nu).mpr hs)]
    · rw [gammaPlus_of_not hs,
        ite_eq_right fun hc => hs ((isSlotStrip_iff_of_isRaising h lam nu).mp hc)]
  · rw [ite_eq_right h]
    by_cases hs : IsHStrip lam nu
    · rw [gammaMinus_of hs, one_pow,
        ite_eq_left ((isSlotStrip_iff_of_not_isRaising h lam nu).mpr hs)]
    · rw [gammaMinus_of_not hs,
        ite_eq_right fun hc => hs ((isSlotStrip_iff_of_not_isRaising h lam nu).mp hc)]

/-- **The slot factor is grade-bounded.** It is *not* step-bounded: its strip factor carries the
argument `1`. -/
theorem gradeBdd_slotKernel (a b t : ℕ) : GradeBdd (slotKernel a b t) := fun lam nu =>
  ⟨_, slotKernel_apply a b t lam nu⟩

/-- The **slot-ordered word**: the `d = a + b` slot factors of the step word shifted by `c`, in
slot order. The shift is the one `transferKernel` performs, and the one `slotPairs` counts
over; none of what follows depends on it. -/
noncomputable def slotWord (a b c : ℕ) : List Kernel :=
  (List.range (a + b)).map fun t => slotKernel a b ((t + c) % (a + b))

@[simp] theorem length_slotWord (a b c : ℕ) : (slotWord a b c).length = a + b := by
  rw [slotWord, List.length_map, List.length_range]

theorem getElem_slotWord (a b c t : ℕ) (ht : t < (slotWord a b c).length) :
    (slotWord a b c)[t] = slotKernel a b ((t + c) % (a + b)) := by
  simp only [slotWord, List.getElem_map, List.getElem_range]

theorem gradeBdd_of_mem_slotWord {a b c : ℕ} {L : Kernel} (h : L ∈ slotWord a b c) :
    GradeBdd L := by
  rw [slotWord, List.mem_map] at h
  obtain ⟨t, -, rfl⟩ := h
  exact gradeBdd_slotKernel _ _ _

/-! ### The trace of the slot-ordered word -/

/-- **The trace of the slot-ordered word is a sum over closed cyclic sequences of partitions.**
The instance of `PathSum`'s grade-bounded primitive at the word the argument reads. -/
theorem ktrace_slotWord_eq_tsum_cycProd (a b c : ℕ) [NeZero (a + b)] :
    ktrace (klist (slotWord a b c))
      = ∑' cyc : Fin (a + b) → Part,
          cycProd (fun i : Fin (a + b) => slotKernel a b (((i : ℕ) + c) % (a + b))) cyc :=
  ktrace_klist_eq_tsum_cycProd_length_of_grade (length_slotWord a b c)
    (fun _ h => gradeBdd_of_mem_slotWord h) _
    fun i => by rw [List.get_eq_getElem, getElem_slotWord, Fin.val_cast]

/-- A closed sequence of partitions **respects the step word** when consecutive terms differ by a
horizontal strip in the direction the step word prescribes: at a raising slot the next partition
contains this one, at a lowering slot the other way round. These are the sequences of
`isHStrip_slice_of_isRaising` and `isHStrip_slice_of_not_isRaising`, read in their labelling by the
residues around the cycle. -/
def RespectsWord (a b c : ℕ) [NeZero (a + b)] (cyc : Fin (a + b) → Part) : Prop :=
  ∀ i : Fin (a + b), IsSlotStrip a b (((i : ℕ) + c) % (a + b)) (cyc i) (cyc (i + 1))

noncomputable instance instDecidableRespectsWord (a b c : ℕ) [NeZero (a + b)]
    (cyc : Fin (a + b) → Part) : Decidable (RespectsWord a b c cyc) := Classical.dec _

/-- **The entries of the slot-ordered cycle vanish off the sequences respecting the step word, and
on them the accumulated exponent is the total of the sizes.** The grading at each slot contributes
`q^{|λ^t|}` and the strip factor contributes `1`, so the whole cycle contributes `q^{∑_t |λ^t|}`. -/
theorem cycProd_slotKernel (a b c : ℕ) [NeZero (a + b)] (cyc : Fin (a + b) → Part) :
    cycProd (fun i : Fin (a + b) => slotKernel a b (((i : ℕ) + c) % (a + b))) cyc
      = if RespectsWord a b c cyc then X ^ ∑ i : Fin (a + b), (cyc i).size else 0 := by
  have hfac : ∀ i : Fin (a + b),
      slotKernel a b (((i : ℕ) + c) % (a + b)) (cyc i) (cyc (i + 1))
        = X ^ (cyc i).size
          * (if IsSlotStrip a b (((i : ℕ) + c) % (a + b)) (cyc i) (cyc (i + 1)) then 1 else 0) :=
    fun i => slotKernel_apply_eq_ite _ _ _ _ _
  rw [cycProd, Finset.prod_congr rfl fun i _ => hfac i, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, Finset.prod_boole]
  by_cases h : RespectsWord a b c cyc
  · rw [ite_eq_left h, ite_eq_left fun i (_ : i ∈ Finset.univ) => h i, mul_one]
  · rw [ite_eq_right h, ite_eq_right fun hcon => h fun i => hcon i (Finset.mem_univ i), mul_zero]

/-- **The trace of the slot-ordered word, as a sum over the sequences that respect the step word.**
This is the first step of the comparison `prod_slotPairs_mul_unboundedGF` makes: the trace of the
slot-ordered product is the sum, over the closed sequences whose consecutive terms differ by a
horizontal strip in the prescribed direction, of `q` to the total of their sizes. -/
theorem ktrace_slotWord_eq_tsum (a b c : ℕ) [NeZero (a + b)] :
    ktrace (klist (slotWord a b c))
      = ∑' cyc : ↥{cyc : Fin (a + b) → Part | RespectsWord a b c cyc},
          X ^ ∑ i : Fin (a + b), ((cyc : Fin (a + b) → Part) i).size := by
  have hsupp : Function.support
      (fun cyc : Fin (a + b) → Part =>
        cycProd (fun i : Fin (a + b) => slotKernel a b (((i : ℕ) + c) % (a + b))) cyc)
      ⊆ {cyc : Fin (a + b) → Part | RespectsWord a b c cyc} := by
    intro cyc hcyc
    by_contra h
    simp only [Set.mem_ofPred_eq] at h
    rw [Function.mem_support, cycProd_slotKernel, ite_eq_right h] at hcyc
    exact hcyc rfl
  rw [ktrace_slotWord_eq_tsum_cycProd, ← tsum_subtype_eq_of_support_subset hsupp]
  refine tsum_congr fun cyc => ?_
  have h2 : RespectsWord a b c (cyc : Fin (a + b) → Part) := cyc.2
  rw [cycProd_slotKernel, ite_eq_left h2]

/-! ### Associativity when only two of the three factors are bounded

`Algebra.lean`'s `kmul_assoc` asks all three factors to be step-bounded, and the strip factor
`Γ_±(1)` of a slot factor is not. What the interchange actually needs is a bound on *two* of the
three: a step-bounded second factor forces the intermediate partition towards the second argument
exactly as well as a step-bounded first factor forces it towards the first, so either the outer pair
or the inner pair suffices and the remaining factor may be arbitrary. -/

/-- A step-bounded **second** factor makes the intermediate sum summable, whatever the first factor
is: it forces the intermediate partition to lie near the second argument. -/
theorem summable_kmul_right {K L : Kernel} (hL : StepBdd L) (lam nu : Part) :
    Summable fun tau => K lam tau * L tau nu :=
  summable_of_dvd_of_finite (g := fun tau => sizeDist tau nu)
    (fun tau => Dvd.dvd.mul_left (hL tau nu) _)
    fun n => (finite_sizeDist_le nu n).subset fun tau htau => by
      simp only [Set.mem_ofPred_eq] at htau ⊢
      rwa [sizeDist_comm]

/-- A step-bounded **first** factor makes the intermediate sum summable, whatever the second factor
is. -/
theorem summable_kmul_left {K L : Kernel} (hK : StepBdd K) (lam nu : Part) :
    Summable fun tau => K lam tau * L tau nu :=
  summable_of_dvd_of_finite (g := fun tau => sizeDist lam tau)
    (fun tau => Dvd.dvd.mul_right (hK lam tau) _) (finite_sizeDist_le lam)

/-- A grade-bounded second factor makes the intermediate sum summable: it forces the size of the
intermediate partition outright. -/
theorem summable_kmul_gradeRight {K L : Kernel} (hL : GradeBdd L) (lam nu : Part) :
    Summable fun tau => K lam tau * L tau nu :=
  summable_of_dvd_of_finite (g := fun tau => tau.size)
    (fun tau => Dvd.dvd.mul_left (hL tau nu) _) finite_size_le

/-- The double family of a triple product is summable when the two **inner** factors are
step-bounded. -/
theorem summable_kmul_pair_mid {K L M : Kernel} (hL : StepBdd L) (hM : StepBdd M)
    (lam nu : Part) : Summable fun p : Part × Part => K lam p.1 * L p.1 p.2 * M p.2 nu := by
  refine summable_of_dvd_of_finite
    (g := fun p : Part × Part => sizeDist p.1 p.2 + sizeDist p.2 nu) (fun p => ?_) fun n => ?_
  · rw [show K lam p.1 * L p.1 p.2 * M p.2 nu = L p.1 p.2 * M p.2 nu * K lam p.1 from by ring,
      pow_add]
    exact Dvd.dvd.mul_right (mul_dvd_mul (hL p.1 p.2) (hM p.2 nu)) _
  · refine ((finite_sizeDist_le nu (n + n)).prod (finite_sizeDist_le nu n)).subset ?_
    rintro ⟨tau, sigma⟩ h
    simp only [Set.mem_ofPred_eq] at h
    have htri : sizeDist tau nu ≤ sizeDist tau sigma + sizeDist sigma nu :=
      sizeDist_le_add tau sigma nu
    refine Set.mk_mem_prod ?_ ?_
    · simp only [Set.mem_ofPred_eq]; rw [sizeDist_comm]; omega
    · simp only [Set.mem_ofPred_eq]; rw [sizeDist_comm]; omega

/-- The double family of a triple product is summable when the two **outer** factors are
step-bounded. -/
theorem summable_kmul_pair_outer {K L M : Kernel} (hK : StepBdd K) (hM : StepBdd M)
    (lam nu : Part) : Summable fun p : Part × Part => K lam p.1 * L p.1 p.2 * M p.2 nu := by
  refine summable_of_dvd_of_finite
    (g := fun p : Part × Part => sizeDist lam p.1 + sizeDist p.2 nu) (fun p => ?_) fun n => ?_
  · rw [show K lam p.1 * L p.1 p.2 * M p.2 nu = K lam p.1 * M p.2 nu * L p.1 p.2 from by ring,
      pow_add]
    exact Dvd.dvd.mul_right (mul_dvd_mul (hK lam p.1) (hM p.2 nu)) _
  · refine ((finite_sizeDist_le lam n).prod (finite_sizeDist_le nu n)).subset ?_
    rintro ⟨tau, sigma⟩ h
    simp only [Set.mem_ofPred_eq] at h
    refine Set.mk_mem_prod ?_ ?_
    · simp only [Set.mem_ofPred_eq]; omega
    · simp only [Set.mem_ofPred_eq]; rw [sizeDist_comm]; omega

/-- **Associativity from the three summability facts it uses.** Both bracketings are the sum of
`K(λ,τ)L(τ,σ)M(σ,ν)` over the pair of intermediate partitions. -/
theorem kmul_assoc_of_summable {K L M : Kernel}
    (hpair : ∀ lam nu, Summable fun p : Part × Part => K lam p.1 * L p.1 p.2 * M p.2 nu)
    (hleft : ∀ lam sigma, Summable fun tau => K lam tau * L tau sigma)
    (hright : ∀ tau nu, Summable fun sigma => L tau sigma * M sigma nu) :
    kmul (kmul K L) M = kmul K (kmul L M) := by
  funext lam nu
  have hfg : ∀ q : Part × Part,
      (fun p : Part × Part => K lam p.1 * L p.1 p.2 * M p.2 nu) ((Equiv.prodComm Part Part) q)
        = K lam q.2 * L q.2 q.1 * M q.1 nu := fun _ => rfl
  have hswap : Summable fun q : Part × Part => K lam q.2 * L q.2 q.1 * M q.1 nu :=
    ((Equiv.prodComm Part Part).summable_iff.mpr (hpair lam nu)).congr hfg
  have hl : kmul (kmul K L) M lam nu
      = ∑' p : Part × Part, K lam p.1 * L p.1 p.2 * M p.2 nu := by
    calc kmul (kmul K L) M lam nu
        = ∑' sigma, (∑' tau, K lam tau * L tau sigma) * M sigma nu := rfl
      _ = ∑' sigma, ∑' tau, K lam tau * L tau sigma * M sigma nu :=
          tsum_congr fun sigma => ((hleft lam sigma).tsum_mul_right (M sigma nu)).symm
      _ = ∑' q : Part × Part, K lam q.2 * L q.2 q.1 * M q.1 nu := hswap.tsum_prod.symm
      _ = ∑' p : Part × Part, K lam p.1 * L p.1 p.2 * M p.2 nu :=
          (tsum_congr fun q => (hfg q).symm).trans
            ((Equiv.prodComm Part Part).tsum_eq
              fun p : Part × Part => K lam p.1 * L p.1 p.2 * M p.2 nu)
  have hr : kmul K (kmul L M) lam nu
      = ∑' p : Part × Part, K lam p.1 * L p.1 p.2 * M p.2 nu := by
    calc kmul K (kmul L M) lam nu
        = ∑' tau, K lam tau * ∑' sigma, L tau sigma * M sigma nu := rfl
      _ = ∑' tau, ∑' sigma, K lam tau * L tau sigma * M sigma nu :=
          tsum_congr fun tau =>
            (((hright tau nu).tsum_mul_left (K lam tau)).symm.trans
              (tsum_congr fun sigma => (mul_assoc _ _ _).symm))
      _ = ∑' p : Part × Part, K lam p.1 * L p.1 p.2 * M p.2 nu := (hpair lam nu).tsum_prod.symm
  rw [hl, hr]

/-- **Associativity with the middle and last factors step-bounded**; the first is arbitrary, which
is what lets a `Γ_±(1)` stand at the head of a product. -/
theorem kmul_assoc_mid {K L M : Kernel} (hL : StepBdd L) (hM : StepBdd M) :
    kmul (kmul K L) M = kmul K (kmul L M) :=
  kmul_assoc_of_summable (fun _ _ => summable_kmul_pair_mid hL hM _ _)
    (fun _ _ => summable_kmul_right hL _ _) (fun _ _ => summable_kmul_right hM _ _)

/-- **Associativity with the first and last factors step-bounded**; the middle is arbitrary, which
is what lets a `Γ_±(1)` sit between a grading and a bounded tail. -/
theorem kmul_assoc_outer {K L M : Kernel} (hK : StepBdd K) (hM : StepBdd M) :
    kmul (kmul K L) M = kmul K (kmul L M) :=
  kmul_assoc_of_summable (fun _ _ => summable_kmul_pair_outer hK hM _ _)
    (fun _ _ => summable_kmul_left hK _ _) (fun _ _ => summable_kmul_right hM _ _)

/-- Two adjacent gradings merge, with no side condition: a diagonal kernel on the left just reads
off the diagonal entry. -/
theorem kmul_grading_grading (u v : ℤ⟦X⟧) :
    kmul (grading u) (grading v) = grading (u * v) := by
  funext lam nu
  rw [grading_kmul]
  by_cases h : lam = nu
  · subst h; rw [grading_diag, grading_diag, mul_pow]
  · rw [grading_of_ne h, grading_of_ne h, mul_zero]

/-- A scalar may be pushed from a product into its left factor, whatever the left factor is, as
soon as the right factor is step-bounded. -/
theorem mul_kmul_left {c : ℤ⟦X⟧} {A B N : Kernel} (h : ∀ mu mu', c * A mu mu' = B mu mu')
    (hN : StepBdd N) (lam nu : Part) : c * kmul A N lam nu = kmul B N lam nu := by
  rw [kmul, kmul, ← (summable_kmul_right hN lam nu).tsum_mul_left c]
  exact tsum_congr fun tau => by rw [← mul_assoc, h]

/-! ### The last slot of the rotated word is lowering

This is the whole point of the rotation `transferKernel` performs, and it is what keeps every
argument of every sorted *suffix* positive: the raising argument at slot `s` is `q^{d-1-s}`, so it
would degenerate to `q^0` exactly at `s = d - 1`. -/

/-- The rotation offset is a genuine minimum: some slot `d - 1 - r` is lowering, namely `r = d - 1`,
which points at slot `0`. -/
theorem sub_one_mem_rotSet {a b : ℕ} (hb : 0 < b) :
    (a + b - 1) ∈ {r | ¬ IsRaising a b (a + b - 1 - r)} := by
  have h0 : a + b - 1 - (a + b - 1) = 0 := by omega
  simp only [Set.mem_ofPred_eq, h0, IsRaising, Nat.zero_mul, Nat.zero_mod, not_le]
  omega

/-- Slot `d - 1 - r` is lowering at the rotation offset `r`. -/
theorem not_isRaising_sub_rotOffset {a b : ℕ} (hb : 0 < b) :
    ¬ IsRaising a b (a + b - 1 - rotOffset a b) :=
  Nat.sInf_mem ⟨_, sub_one_mem_rotSet hb⟩

/-- The rotation offset is below `d`. -/
theorem rotOffset_lt {a b : ℕ} (hb : 0 < b) : rotOffset a b < a + b :=
  lt_of_le_of_lt (Nat.sInf_le (sub_one_mem_rotSet hb)) (by omega)

/-- **Slot `d - 1` of the rotated word is lowering.** -/
theorem not_isRaising_rotSlot_last {a b : ℕ} (hb : 0 < b) :
    ¬ IsRaising a b (rotSlot a b (a + b - 1)) := by
  have hlt : rotOffset a b < a + b := rotOffset_lt hb
  have hmod : rotOffset a b % (a + b) = rotOffset a b := Nat.mod_eq_of_lt hlt
  have hval : rotSlot a b (a + b - 1) = a + b - 1 - rotOffset a b := by
    rw [rotSlot, hmod,
      show a + b - 1 + (a + b) - rotOffset a b = a + b - 1 - rotOffset a b + (a + b) from by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  rw [hval]
  exact not_isRaising_sub_rotOffset hb

/-! ### The slots of the rotated word from a given position on -/

/-- The lowering slots of the rotated step word at or after `k`, in increasing order. At `k = 0`
this is `loweringSlots`, the list `transferKernel` uses. -/
noncomputable def lowFrom (a b k : ℕ) : List ℕ :=
  ((Finset.Ico k (a + b)).filter fun s => ¬ IsRaising a b (rotSlot a b s)).sort (· ≤ ·)

/-- The raising slots of the rotated step word at or after `k`, in increasing order. -/
noncomputable def hiFrom (a b k : ℕ) : List ℕ :=
  ((Finset.Ico k (a + b)).filter fun s => IsRaising a b (rotSlot a b s)).sort (· ≤ ·)

theorem mem_lowFrom {a b k s : ℕ} (h : s ∈ lowFrom a b k) :
    k ≤ s ∧ s < a + b ∧ ¬ IsRaising a b (rotSlot a b s) := by
  rw [lowFrom, Finset.mem_sort, Finset.mem_filter, Finset.mem_Ico] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem mem_hiFrom {a b k s : ℕ} (h : s ∈ hiFrom a b k) :
    k ≤ s ∧ s < a + b ∧ IsRaising a b (rotSlot a b s) := by
  rw [hiFrom, Finset.mem_sort, Finset.mem_filter, Finset.mem_Ico] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- **A raising slot is never the last one**, so its argument `q^{d-1-s}` carries a positive power
of `q`. -/
theorem one_le_sub_of_mem_hiFrom {a b k s : ℕ} (hb : 0 < b) (h : s ∈ hiFrom a b k) :
    1 ≤ a + b - 1 - s := by
  obtain ⟨-, hs, hr⟩ := mem_hiFrom h
  have hne : s ≠ a + b - 1 := fun hh => (not_isRaising_rotSlot_last hb) (hh ▸ hr)
  omega

theorem Ico_eq_insert {k d : ℕ} (h : k < d) : Finset.Ico k d = insert k (Finset.Ico (k + 1) d) := by
  ext s
  simp only [Finset.mem_insert, Finset.mem_Ico]
  omega

theorem lowFrom_of_le {a b k : ℕ} (h : a + b ≤ k) : lowFrom a b k = [] := by
  rw [lowFrom, Finset.Ico_eq_empty (by omega), Finset.filter_empty, Finset.sort_empty]

theorem hiFrom_of_le {a b k : ℕ} (h : a + b ≤ k) : hiFrom a b k = [] := by
  rw [hiFrom, Finset.Ico_eq_empty (by omega), Finset.filter_empty, Finset.sort_empty]

theorem lowFrom_cons {a b k : ℕ} (h : k < a + b) (hk : ¬ IsRaising a b (rotSlot a b k)) :
    lowFrom a b k = k :: lowFrom a b (k + 1) := by
  rw [lowFrom, lowFrom, Ico_eq_insert h, Finset.filter_insert, ite_eq_left hk]
  refine Finset.sort_insert (h₁ := fun s hs => ?_) (h₂ := fun hs => ?_)
  · exact le_of_lt (by simpa using (Finset.mem_Ico.mp (Finset.mem_filter.mp hs).1).1)
  · exact absurd (Finset.mem_Ico.mp (Finset.mem_filter.mp hs).1).1 (by omega)

theorem lowFrom_succ {a b k : ℕ} (hk : IsRaising a b (rotSlot a b k)) :
    lowFrom a b k = lowFrom a b (k + 1) := by
  rcases le_or_gt (a + b) k with h | h
  · rw [lowFrom_of_le h, lowFrom_of_le (by omega)]
  · rw [lowFrom, lowFrom, Ico_eq_insert h, Finset.filter_insert, ite_eq_right (not_not_intro hk)]

theorem hiFrom_cons {a b k : ℕ} (h : k < a + b) (hk : IsRaising a b (rotSlot a b k)) :
    hiFrom a b k = k :: hiFrom a b (k + 1) := by
  rw [hiFrom, hiFrom, Ico_eq_insert h, Finset.filter_insert, ite_eq_left hk]
  refine Finset.sort_insert (h₁ := fun s hs => ?_) (h₂ := fun hs => ?_)
  · exact le_of_lt (by simpa using (Finset.mem_Ico.mp (Finset.mem_filter.mp hs).1).1)
  · exact absurd (Finset.mem_Ico.mp (Finset.mem_filter.mp hs).1).1 (by omega)

theorem hiFrom_succ {a b k : ℕ} (hk : ¬ IsRaising a b (rotSlot a b k)) :
    hiFrom a b k = hiFrom a b (k + 1) := by
  rcases le_or_gt (a + b) k with h | h
  · rw [hiFrom_of_le h, hiFrom_of_le (by omega)]
  · rw [hiFrom, hiFrom, Ico_eq_insert h, Finset.filter_insert, ite_eq_right hk]

theorem lowFrom_zero (a b : ℕ) : lowFrom a b 0 = loweringSlots a b := by
  rw [lowFrom, loweringSlots, Finset.range_eq_Ico]

theorem hiFrom_zero (a b : ℕ) : hiFrom a b 0 = raisingSlots a b := by
  rw [hiFrom, raisingSlots, Finset.range_eq_Ico]

/-! ### The sorted suffix, and that every one of its factors is a vertex operator -/

/-- The lowering block of the sorted word read from slot `k` on: `Γ_-(q^{s-k+1})` over the lowering
slots `s ≥ k`, in increasing order. -/
noncomputable def lowBlock (a b k : ℕ) : List Kernel :=
  (lowFrom a b k).map fun s => gammaMinus (X ^ (s - k + 1))

/-- The raising block of the sorted word read from slot `k` on: `Γ_+(q^{d-1-s})` over the raising
slots `s ≥ k`, in increasing order. These arguments do not depend on `k`. -/
noncomputable def hiBlock (a b k : ℕ) : List Kernel :=
  (hiFrom a b k).map fun s => gammaPlus (X ^ (a + b - 1 - s))

/-- **The sorted word read from slot `k` on**: the lowering block, the grading `Q(q^{d-k})`, then
the raising block. At `k = 0` this is the list of `transferKernel`, and at `k = d` it is the
identity kernel. -/
noncomputable def sortedFrom (a b k : ℕ) : List Kernel :=
  lowBlock a b k ++ grading (X ^ (a + b - k)) :: hiBlock a b k

theorem stepBdd_of_mem_sortedFrom {a b k : ℕ} (hb : 0 < b) {K : Kernel}
    (h : K ∈ sortedFrom a b k) : StepBdd K := by
  rw [sortedFrom, List.mem_append, List.mem_cons] at h
  rcases h with h | rfl | h
  · obtain ⟨s, -, rfl⟩ := List.mem_map.mp h
    exact StepBdd.gammaMinus (by omega)
  · exact StepBdd.grading _
  · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp h
    exact StepBdd.gammaPlus (one_le_sub_of_mem_hiFrom hb hs)

theorem stepBdd_klist_sortedFrom {a b : ℕ} (hb : 0 < b) (k : ℕ) :
    StepBdd (klist (sortedFrom a b k)) :=
  StepBdd.klist fun _ h => stepBdd_of_mem_sortedFrom hb h

theorem gradeBdd_klist_sortedFrom {a b : ℕ} (hb : 0 < b) {k : ℕ} (hk : k < a + b) :
    GradeBdd (klist (sortedFrom a b k)) :=
  GradeBdd.klist (fun _ h => stepBdd_of_mem_sortedFrom hb h)
    ⟨grading (X ^ (a + b - k)), by
      rw [sortedFrom]; exact List.mem_append_right _ List.mem_cons_self,
      GradeBdd.grading (by omega)⟩

/-! ### The slot-ordered suffix and the crossing prefactor -/

/-- The slot-ordered word read from slot `k` on, in the rotated labelling. -/
noncomputable def slotFrom (a b k : ℕ) : List Kernel :=
  (List.range' k (a + b - k)).map fun t => slotKernel a b (rotSlot a b t)

theorem slotFrom_of_le {a b k : ℕ} (h : a + b ≤ k) : slotFrom a b k = [] := by
  rw [slotFrom, show a + b - k = 0 from by omega]; rfl

theorem slotFrom_cons {a b k : ℕ} (h : k < a + b) :
    slotFrom a b k = slotKernel a b (rotSlot a b k) :: slotFrom a b (k + 1) := by
  rw [slotFrom, slotFrom, show a + b - k = a + b - (k + 1) + 1 from by omega, List.range'_succ]
  rfl

theorem gradeBdd_of_mem_slotFrom {a b k : ℕ} {K : Kernel} (h : K ∈ slotFrom a b k) :
    GradeBdd K := by
  rw [slotFrom, List.mem_map] at h
  obtain ⟨t, -, rfl⟩ := h
  exact gradeBdd_slotKernel _ _ _

/-- A grade-bounded factor on the left keeps the product grade-bounded. -/
theorem GradeBdd.kmul_gradeRight {K L : Kernel} (hK : GradeBdd K) (hL : GradeBdd L) :
    GradeBdd (kmul K L) := fun lam nu =>
  X_pow_dvd_tsum (summable_kmul_gradeRight hL lam nu) fun tau => Dvd.dvd.mul_right (hK lam tau) _

/-- **A nonempty product of grade-bounded kernels is grade-bounded.** This is the bound the
slot-ordered word has and the step bound it has not. -/
theorem gradeBdd_klist_of_grade {Ks : List Kernel} (hKs : ∀ K ∈ Ks, GradeBdd K) (hne : Ks ≠ []) :
    GradeBdd (klist Ks) := by
  induction Ks with
  | nil => exact absurd rfl hne
  | cons K Ks ih =>
    rw [klist_cons]
    rcases Ks with _ | ⟨L, Ls⟩
    · rw [klist_nil, kmul_kone]; exact hKs K List.mem_cons_self
    · exact GradeBdd.kmul_gradeRight (hKs K List.mem_cons_self)
        (ih (fun M hM => hKs M (List.mem_cons_of_mem _ hM)) (by simp))

/-- The one summability the slot factor at the head of the slot-ordered suffix needs: below `d` the
tail is a nonempty product of grade-bounded factors, and at `d` it is the identity kernel, which is
step-bounded. -/
theorem summable_slotKernel_klist_slotFrom {a b : ℕ} (t k : ℕ) (lam nu : Part) :
    Summable fun tau => slotKernel a b t lam tau * klist (slotFrom a b k) tau nu := by
  rcases le_or_gt (a + b) k with h | h
  · rw [slotFrom_of_le h, klist_nil]
    exact summable_kmul_right StepBdd.kone lam nu
  · exact summable_kmul_gradeRight
      (gradeBdd_klist_of_grade (fun _ hK => gradeBdd_of_mem_slotFrom hK)
        (by rw [slotFrom_cons h]; simp)) lam nu

/-- The crossing factors the sorting contributes at slot `k`: at a raising slot, one for each
lowering slot after it; at a lowering slot, none. -/
noncomputable def crossAt (a b k : ℕ) : ℤ⟦X⟧ :=
  if IsRaising a b (rotSlot a b k) then
    ((lowFrom a b (k + 1)).map fun s => (1 - X ^ (s - k) : ℤ⟦X⟧)).prod
  else 1

/-- The crossing prefactor of the sorting of the slot-ordered word from slot `k` on. -/
noncomputable def crossFrom (a b k : ℕ) : ℤ⟦X⟧ :=
  ((List.range' k (a + b - k)).map (crossAt a b)).prod

theorem crossFrom_of_le {a b k : ℕ} (h : a + b ≤ k) : crossFrom a b k = 1 := by
  rw [crossFrom, show a + b - k = 0 from by omega]; rfl

theorem crossFrom_cons {a b k : ℕ} (h : k < a + b) :
    crossFrom a b k = crossAt a b k * crossFrom a b (k + 1) := by
  rw [crossFrom, crossFrom, show a + b - k = a + b - (k + 1) + 1 from by omega, List.range'_succ]
  rfl

/-! ### The two moves the sorting makes -/

/-- The double family of a triple product is summable when the two **leading** factors are
step-bounded; the last is arbitrary. -/
theorem summable_kmul_pair_leftmid {K L M : Kernel} (hK : StepBdd K) (hL : StepBdd L)
    (lam nu : Part) : Summable fun p : Part × Part => K lam p.1 * L p.1 p.2 * M p.2 nu := by
  refine summable_of_dvd_of_finite
    (g := fun p : Part × Part => sizeDist lam p.1 + sizeDist p.1 p.2) (fun p => ?_) fun n => ?_
  · rw [pow_add]
    exact Dvd.dvd.mul_right (mul_dvd_mul (hK lam p.1) (hL p.1 p.2)) _
  · refine ((finite_sizeDist_le lam n).prod (finite_sizeDist_le lam (n + n))).subset ?_
    rintro ⟨tau, sigma⟩ h
    simp only [Set.mem_ofPred_eq] at h
    have htri : sizeDist lam sigma ≤ sizeDist lam tau + sizeDist tau sigma :=
      sizeDist_le_add lam tau sigma
    exact Set.mk_mem_prod (by simp only [Set.mem_ofPred_eq]; omega)
      (by simp only [Set.mem_ofPred_eq]; omega)

/-- **Associativity with the first two factors step-bounded**; the last is arbitrary, which is what
lets a `Γ_±(1)` sit at the tail of a product of bounded factors. -/
theorem kmul_assoc_leftmid {K L M : Kernel} (hK : StepBdd K) (hL : StepBdd L) :
    kmul (kmul K L) M = kmul K (kmul L M) :=
  kmul_assoc_of_summable (fun _ _ => summable_kmul_pair_leftmid hK hL _ _)
    (fun _ _ => summable_kmul_left hK _ _) (fun _ _ => summable_kmul_left hL _ _)

/-- **A list of step-bounded kernels may be cut off the front of any list.** `Algebra.lean`'s
`klist_append` asks the *second* part to be step-bounded too, which the tail of the slot-ordered
reading is not. -/
theorem klist_append_left {Ks Ls : List Kernel} (hKs : ∀ K ∈ Ks, StepBdd K) :
    klist (Ks ++ Ls) = kmul (klist Ks) (klist Ls) := by
  induction Ks with
  | nil => rw [List.nil_append, klist_nil, kone_kmul]
  | cons K Ks ih =>
    have hKs' : ∀ L ∈ Ks, StepBdd L := fun L hL => hKs L (List.mem_cons_of_mem _ hL)
    rw [List.cons_append, klist_cons, ih hKs', klist_cons,
      kmul_assoc_leftmid (hKs K List.mem_cons_self) (StepBdd.klist hKs')]

/-- Rewriting the tail of a product under a step-bounded head. -/
theorem klist_append_congr {Ks Ls Ls' : List Kernel} (hKs : ∀ K ∈ Ks, StepBdd K)
    (h : klist Ls = klist Ls') : klist (Ks ++ Ls) = klist (Ks ++ Ls') := by
  rw [klist_append_left hKs, klist_append_left hKs, h]

/-- A scalar may be pushed into the **right** factor of a product, as soon as the intermediate sum
converges. -/
theorem mul_kmul_right {c : ℤ⟦X⟧} {A B B' : Kernel} (h : ∀ mu mu', c * B mu mu' = B' mu mu')
    (hsum : ∀ lam nu, Summable fun tau => A lam tau * B tau nu) (lam nu : Part) :
    c * kmul A B lam nu = kmul A B' lam nu := by
  rw [kmul, kmul, ← (hsum lam nu).tsum_mul_left c]
  exact tsum_congr fun tau => by rw [← h, mul_left_comm]

/-- Two adjacent gradings inside a product merge; no side condition, since a diagonal kernel on the
left just reads off the diagonal entry. -/
theorem klist_grading_grading_cons (u v : ℤ⟦X⟧) (Ks : List Kernel) :
    klist (grading u :: grading v :: Ks) = klist (grading (u * v) :: Ks) := by
  funext lam nu
  rw [klist_cons, klist_cons, klist_cons, grading_kmul, grading_kmul, grading_kmul, ← mul_assoc,
    ← mul_pow]

/-- `Γ_+(1)` crosses a grading and comes out carrying the grading's argument. This is
`gammaPlus_kmul_grading` at `m = 0`. -/
theorem gammaPlus_one_kmul_grading (j : ℕ) :
    kmul (gammaPlus 1) (grading (X ^ j)) = kmul (grading (X ^ j)) (gammaPlus (X ^ j)) := by
  have h := gammaPlus_kmul_grading j 0
  rw [pow_zero, Nat.add_zero] at h
  exact h

/-- **Pushing a grading rightwards through lowering factors** raises each of their arguments by the
grading's own exponent and leaves the grading standing just past them. This is
`grading_kmul_gammaMinus`, iterated. -/
theorem grading_kmul_lowering (j : ℕ) (ms : List ℕ) {Ks : List Kernel}
    (hms : ∀ m ∈ ms, 1 ≤ m) (hKs : ∀ K ∈ Ks, StepBdd K) :
    kmul (grading (X ^ j)) (klist ((ms.map fun m => gammaMinus (X ^ m)) ++ Ks))
      = klist ((ms.map fun m => gammaMinus (X ^ (j + m))) ++ grading (X ^ j) :: Ks) := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    have hm : 1 ≤ m := hms m List.mem_cons_self
    have hms' : ∀ m' ∈ ms, 1 ≤ m' := fun m' hm' => hms m' (List.mem_cons_of_mem _ hm')
    have hN : StepBdd (klist ((ms.map fun m => gammaMinus (X ^ m)) ++ Ks)) :=
      StepBdd.klist fun K hK => by
        rcases List.mem_append.mp hK with h | h
        · obtain ⟨m', hm', rfl⟩ := List.mem_map.mp h
          exact StepBdd.gammaMinus (hms' m' hm')
        · exact hKs K h
    simp only [List.map_cons, List.cons_append, klist_cons]
    rw [← kmul_assoc_mid (StepBdd.gammaMinus hm) hN, grading_kmul_gammaMinus j m,
      kmul_assoc_outer (StepBdd.gammaMinus (by omega : 1 ≤ j + m)) hN, ih hms']

/-- **Moving `Γ_+(1)` rightwards past lowering factors** costs one factor `1 - q^m` per lowering
factor passed, `q^m` being that factor's argument. This is
`one_sub_mul_gammaPlus_kmul_gammaMinus`, iterated, and it is where the crossing prefactor comes
from. -/
theorem prod_mul_gammaPlus_one_past_lowering (ms : List ℕ) {Ks : List Kernel}
    (hms : ∀ m ∈ ms, 1 ≤ m) (hKs : ∀ K ∈ Ks, StepBdd K) (lam nu : Part) :
    (ms.map fun m => (1 - X ^ m : ℤ⟦X⟧)).prod
        * kmul (gammaPlus 1) (klist ((ms.map fun m => gammaMinus (X ^ m)) ++ Ks)) lam nu
      = klist ((ms.map fun m => gammaMinus (X ^ m)) ++ gammaPlus 1 :: Ks) lam nu := by
  induction ms generalizing lam nu with
  | nil => simp only [List.map_nil, List.prod_nil, List.nil_append, one_mul, klist_cons]
  | cons m ms ih =>
    have hm : 1 ≤ m := hms m List.mem_cons_self
    have hms' : ∀ m' ∈ ms, 1 ≤ m' := fun m' hm' => hms m' (List.mem_cons_of_mem _ hm')
    have hN : StepBdd (klist ((ms.map fun m => gammaMinus (X ^ m)) ++ Ks)) :=
      StepBdd.klist fun K hK => by
        rcases List.mem_append.mp hK with h | h
        · obtain ⟨m', hm', rfl⟩ := List.mem_map.mp h
          exact StepBdd.gammaMinus (hms' m' hm')
        · exact hKs K h
    have hcomm : ∀ mu mu' : Part,
        (1 - X ^ m : ℤ⟦X⟧) * kmul (gammaPlus 1) (gammaMinus (X ^ m)) mu mu'
          = kmul (gammaMinus (X ^ m)) (gammaPlus 1) mu mu' := by
      intro mu mu'
      have hc : constantCoeff ((1 : ℤ⟦X⟧) * X ^ m) = 0 := by
        rw [one_mul, map_pow, constantCoeff_X]
        exact zero_pow (by omega)
      simpa only [one_mul] using one_sub_mul_gammaPlus_kmul_gammaMinus hc mu mu'
    have step : (1 - X ^ m : ℤ⟦X⟧)
        * kmul (gammaPlus 1) (kmul (gammaMinus (X ^ m))
            (klist ((ms.map fun m => gammaMinus (X ^ m)) ++ Ks))) lam nu
          = kmul (gammaMinus (X ^ m)) (kmul (gammaPlus 1)
              (klist ((ms.map fun m => gammaMinus (X ^ m)) ++ Ks))) lam nu := by
      rw [← kmul_assoc_mid (StepBdd.gammaMinus hm) hN, mul_kmul_left hcomm hN,
        kmul_assoc_outer (StepBdd.gammaMinus hm) hN]
    simp only [List.map_cons, List.prod_cons, List.cons_append, klist_cons]
    rw [mul_comm (1 - X ^ m : ℤ⟦X⟧) _, mul_assoc, step]
    exact mul_kmul_right (fun mu mu' => ih hms' mu mu')
      (fun _ _ => summable_kmul_left (StepBdd.gammaMinus hm) _ _) lam nu

/-! ### One step of the sorting induction -/

theorem lowBlock_eq_map_map (a b k : ℕ) :
    lowBlock a b k = ((lowFrom a b k).map fun s => s - k + 1).map fun m => gammaMinus (X ^ m) := by
  rw [lowBlock, List.map_map]
  rfl

theorem one_le_of_mem_lowExp {a b k m : ℕ} (h : m ∈ (lowFrom a b k).map fun s => s - k + 1) :
    1 ≤ m := by
  obtain ⟨s, -, rfl⟩ := List.mem_map.mp h
  omega

theorem stepBdd_pushed_lowBlock (a b k : ℕ) :
    ∀ K ∈ (lowFrom a b (k + 1)).map fun s => gammaMinus (X ^ (s - k + 1)), StepBdd K := by
  intro K hK
  obtain ⟨s, -, rfl⟩ := List.mem_map.mp hK
  exact StepBdd.gammaMinus (by omega)

theorem push_lowBlock_succ (a b k : ℕ) :
    (((lowFrom a b (k + 1)).map fun s => s - (k + 1) + 1).map fun m => gammaMinus (X ^ (1 + m)))
      = (lowFrom a b (k + 1)).map fun s => gammaMinus (X ^ (s - k + 1)) := by
  rw [List.map_map]
  refine List.map_congr_left fun s hs => ?_
  have hks : k + 1 ≤ s := (mem_lowFrom hs).1
  simp only [Function.comp_apply]
  congr 2
  omega

theorem push_crossAt_succ (a b k : ℕ) :
    (((lowFrom a b (k + 1)).map fun s => s - (k + 1) + 1).map fun m => (1 - X ^ m : ℤ⟦X⟧))
      = (lowFrom a b (k + 1)).map fun s => (1 - X ^ (s - k) : ℤ⟦X⟧) := by
  rw [List.map_map]
  refine List.map_congr_left fun s hs => ?_
  have hks : k + 1 ≤ s := (mem_lowFrom hs).1
  simp only [Function.comp_apply]
  congr 2
  omega

/-- The sorted word from a **lowering** slot `k` on: one new lowering factor `Γ_-(q)` in front, the
grading raised from `q^{d-k-1}` to `q^{d-k}`, and every other lowering argument raised by one. -/
theorem sortedFrom_of_not_isRaising {a b k : ℕ} (hk : k < a + b)
    (hr : ¬ IsRaising a b (rotSlot a b k)) :
    sortedFrom a b k = gammaMinus (X ^ 1)
        :: (((lowFrom a b (k + 1)).map fun s => gammaMinus (X ^ (s - k + 1)))
          ++ grading (X ^ (a + b - k)) :: hiBlock a b (k + 1)) := by
  rw [sortedFrom, lowBlock, lowFrom_cons hk hr, List.map_cons, List.cons_append,
    show hiBlock a b k = hiBlock a b (k + 1) from by rw [hiBlock, hiBlock, hiFrom_succ hr],
    show k - k + 1 = 1 from by omega]

/-- The sorted word from a **raising** slot `k` on: one new raising factor `Γ_+(q^{d-1-k})` just
past the grading, and every lowering argument raised by one. -/
theorem sortedFrom_of_isRaising {a b k : ℕ} (hk : k < a + b)
    (hr : IsRaising a b (rotSlot a b k)) :
    sortedFrom a b k = ((lowFrom a b (k + 1)).map fun s => gammaMinus (X ^ (s - k + 1)))
        ++ grading (X ^ (a + b - k)) :: gammaPlus (X ^ (a + b - 1 - k)) :: hiBlock a b (k + 1) := by
  simp only [sortedFrom, lowBlock, hiBlock, lowFrom_succ hr, hiFrom_cons hk hr, List.map_cons]

/-- **One step of the sorting induction.** Prefixing the slot factor at slot `k` to the sorted word
read from `k + 1` on, and paying the crossing factors that slot contributes, gives the sorted word
read from `k` on.

Only sorted partial products are ever evaluated: the unsorted reading enters only as the single slot
factor standing at the head, and every factor of every product named below carries a positive power
of `q` except that one. That is what makes the induction legitimate at all -- and it is why the
suffixes, not the prefixes, are the right partial products: the raising argument at slot `s` is
`q^{d-1-s}`, which would degenerate to `q^0` exactly at the last slot, and the last slot is
lowering. -/
theorem crossAt_mul_kmul_slotKernel {a b : ℕ} (hb : 0 < b) {k : ℕ} (hk : k < a + b)
    (lam nu : Part) :
    crossAt a b k * kmul (slotKernel a b (rotSlot a b k)) (klist (sortedFrom a b (k + 1))) lam nu
      = klist (sortedFrom a b k) lam nu := by
  have hgX : (grading (X : ℤ⟦X⟧)) = grading (X ^ 1) := by rw [pow_one]
  have hlowms : ∀ m ∈ (lowFrom a b (k + 1)).map fun s => s - (k + 1) + 1, 1 ≤ m :=
    fun m hm => one_le_of_mem_lowExp hm
  have hhi : ∀ K ∈ hiBlock a b (k + 1), StepBdd K := by
    intro K hK
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hK
    exact StepBdd.gammaPlus (one_le_sub_of_mem_hiFrom hb hs)
  have hhiStep : StepBdd (klist (hiBlock a b (k + 1))) := StepBdd.klist hhi
  have hlowStep : ∀ K ∈ lowBlock a b (k + 1), StepBdd K := by
    intro K hK
    obtain ⟨s, -, rfl⟩ := List.mem_map.mp hK
    exact StepBdd.gammaMinus (by omega)
  have hN : StepBdd (klist (sortedFrom a b (k + 1))) := stepBdd_klist_sortedFrom hb _
  have hKs1 : ∀ K ∈ grading (X ^ (a + b - (k + 1))) :: hiBlock a b (k + 1), StepBdd K := by
    intro K hK
    rcases List.mem_cons.mp hK with rfl | hK
    · exact StepBdd.grading _
    · exact hhi K hK
  have hmerge : (X : ℤ⟦X⟧) ^ 1 * X ^ (a + b - (k + 1)) = X ^ (a + b - k) := by
    rw [← pow_add]
    congr 1
    omega
  by_cases hr : IsRaising a b (rotSlot a b k)
  · -- a raising slot: the strip factor must cross the whole lowering block
    have hkd : k + 1 < a + b := by
      have hne : k ≠ a + b - 1 := fun hh => (not_isRaising_rotSlot_last hb) (hh ▸ hr)
      omega
    have hKs2 : ∀ K ∈ grading (X ^ (a + b - (k + 1)))
        :: gammaPlus (X ^ (a + b - (k + 1))) :: hiBlock a b (k + 1), StepBdd K := by
      intro K hK
      rcases List.mem_cons.mp hK with rfl | hK
      · exact StepBdd.grading _
      rcases List.mem_cons.mp hK with rfl | hK
      · exact StepBdd.gammaPlus (by omega)
      · exact hhi K hK
    have hswap : klist (gammaPlus 1 :: grading (X ^ (a + b - (k + 1))) :: hiBlock a b (k + 1))
        = klist (grading (X ^ (a + b - (k + 1)))
            :: gammaPlus (X ^ (a + b - (k + 1))) :: hiBlock a b (k + 1)) := by
      simp only [klist_cons]
      rw [← kmul_assoc_mid (StepBdd.grading _) hhiStep, gammaPlus_one_kmul_grading,
        kmul_assoc_outer (StepBdd.grading _) hhiStep]
    have hinner : ∀ mu mu' : Part, crossAt a b k
        * kmul (gammaPlus 1) (klist (sortedFrom a b (k + 1))) mu mu'
          = klist (lowBlock a b (k + 1) ++ grading (X ^ (a + b - (k + 1)))
              :: gammaPlus (X ^ (a + b - (k + 1))) :: hiBlock a b (k + 1)) mu mu' := by
      intro mu mu'
      rw [crossAt, ite_eq_left hr, ← push_crossAt_succ, sortedFrom, lowBlock_eq_map_map,
        prod_mul_gammaPlus_one_past_lowering _ hlowms hKs1 mu mu', ← lowBlock_eq_map_map,
        klist_append_congr hlowStep hswap]
    rw [slotKernel, ite_eq_left hr, kmul_assoc_outer (StepBdd.grading X) hN,
      mul_kmul_right hinner (fun _ _ => summable_kmul_left (StepBdd.grading X) _ _) lam nu,
      hgX, lowBlock_eq_map_map, grading_kmul_lowering 1 _ hlowms hKs2, push_lowBlock_succ,
      klist_append_congr (stepBdd_pushed_lowBlock a b k) (klist_grading_grading_cons _ _ _),
      hmerge, sortedFrom_of_isRaising hk hr, show a + b - (k + 1) = a + b - 1 - k from by omega]
  · -- a lowering slot: the strip factor crosses only the grading
    have hg1 : (gammaMinus (1 : ℤ⟦X⟧)) = gammaMinus (X ^ 0) := by rw [pow_zero]
    rw [crossAt, ite_eq_right hr, one_mul, slotKernel, ite_eq_right hr, hgX, hg1,
      grading_kmul_gammaMinus 1 0, Nat.add_zero,
      kmul_assoc_outer (StepBdd.gammaMinus (le_refl 1)) hN, sortedFrom, lowBlock_eq_map_map,
      grading_kmul_lowering 1 _ hlowms hKs1, push_lowBlock_succ,
      klist_append_congr (stepBdd_pushed_lowBlock a b k) (klist_grading_grading_cons _ _ _),
      hmerge, sortedFrom_of_not_isRaising hk hr, klist_cons]

/-! ### The sorting induction, and the sorted word of `transferKernel` -/

theorem grading_one : grading (1 : ℤ⟦X⟧) = kone := by
  funext lam nu
  simp only [grading, kone, one_pow]

theorem klist_sortedFrom_of_le {a b k : ℕ} (h : a + b ≤ k) : klist (sortedFrom a b k) = kone := by
  rw [sortedFrom, lowBlock, hiBlock, lowFrom_of_le h, hiFrom_of_le h,
    show a + b - k = 0 from by omega]
  simp only [List.map_nil, List.nil_append, klist_cons, klist_nil, kmul_kone, pow_zero,
    grading_one]

/-- **The sorting induction.** Downward on the starting slot: the crossing prefactor of the suffix
from `k` on, times the slot-ordered reading of that suffix, is the sorted reading of it. -/
theorem crossFrom_mul_klist_slotFrom_aux {a b : ℕ} (hb : 0 < b) :
    ∀ n k : ℕ, a + b ≤ k + n → ∀ lam nu : Part,
      crossFrom a b k * klist (slotFrom a b k) lam nu = klist (sortedFrom a b k) lam nu := by
  intro n
  induction n with
  | zero =>
    intro k hk lam nu
    rw [crossFrom_of_le (by omega), slotFrom_of_le (by omega), klist_sortedFrom_of_le (by omega),
      one_mul, klist_nil]
  | succ n ih =>
    intro k hk lam nu
    rcases le_or_gt (a + b) k with h | h
    · rw [crossFrom_of_le h, slotFrom_of_le h, klist_sortedFrom_of_le h, one_mul, klist_nil]
    · rw [crossFrom_cons h, slotFrom_cons h, klist_cons, mul_assoc,
        mul_kmul_right (fun mu mu' => ih (k + 1) (by omega) mu mu')
          (fun _ _ => summable_slotKernel_klist_slotFrom _ _ _ _) lam nu,
        crossAt_mul_kmul_slotKernel hb h lam nu]

theorem crossFrom_mul_klist_slotFrom {a b : ℕ} (hb : 0 < b) (k : ℕ) (lam nu : Part) :
    crossFrom a b k * klist (slotFrom a b k) lam nu = klist (sortedFrom a b k) lam nu :=
  crossFrom_mul_klist_slotFrom_aux hb (a + b) k (by omega) lam nu

/-- **The sorted word from slot `0` on is `transferKernel`.** -/
theorem transferKernel_eq_klist_sortedFrom (a b : ℕ) :
    transferKernel a b = klist (sortedFrom a b 0) := by
  rw [transferKernel, sortedFrom, lowBlock, hiBlock, lowFrom_zero, hiFrom_zero]
  simp only [Nat.sub_zero]

/-- **The slot-ordered word from slot `0` on is the slot-ordered word at the shift
`transferKernel` uses.** -/
theorem slotFrom_zero {a b : ℕ} (hd : 0 < a + b) :
    slotFrom a b 0 = slotWord a b ((a + b) - rotOffset a b % (a + b)) := by
  rw [slotFrom, slotWord, Nat.sub_zero, List.range_eq_range']
  exact List.map_congr_left fun t _ => by rw [rotSlot_eq_add_mod hd]

theorem traceSummable_klist_slotFrom {a b k : ℕ} (h : k < a + b) :
    Summable fun lam => klist (slotFrom a b k) lam lam :=
  summable_of_dvd_of_finite (g := fun lam : Part => lam.size)
    (fun lam => gradeBdd_klist_of_grade (fun _ hK => gradeBdd_of_mem_slotFrom hK)
      (by rw [slotFrom_cons h]; simp) lam lam) finite_size_le

/-- **Parts (b) and (c) of the comparison, at the level of traces.** The crossing prefactor
times the trace of the slot-ordered reading is the trace of `transferKernel`. -/
theorem crossFrom_zero_mul_ktrace_slotWord {a b : ℕ} (hb : 0 < b) (hd : 0 < a + b) :
    crossFrom a b 0 * ktrace (klist (slotWord a b ((a + b) - rotOffset a b % (a + b))))
      = ktrace (transferKernel a b) := by
  rw [← slotFrom_zero hd, ktrace, ktrace,
    ← (traceSummable_klist_slotFrom hd).tsum_mul_left (crossFrom a b 0),
    transferKernel_eq_klist_sortedFrom]
  exact tsum_congr fun lam => crossFrom_mul_klist_slotFrom hb 0 lam lam

/-! ### The count of interchanged pairs

`slotPairs` is already the index set: the pairs the sorting interchanges are those with `s' < s`,
and `(slotPairs a b c).filter fun p => p.2 < p.1` is exactly the set `assembled_exponents`
consumes. -/

theorem prod_map_sort {M : Type*} [CommMonoid M] (s : Finset ℕ) (f : ℕ → M) :
    ((s.sort (· ≤ ·)).map f).prod = ∏ x ∈ s, f x := by
  rw [← Finset.prod_map_toList]
  exact List.Perm.prod_eq (List.Perm.map f (Finset.sort_perm_toList s (· ≤ ·)))

theorem prod_map_range {M : Type*} [CommMonoid M] (n : ℕ) (f : ℕ → M) :
    ((List.range n).map f).prod = ∏ x ∈ Finset.range n, f x := by
  rw [← Finset.sort_range n, prod_map_sort]

theorem lowFromFinset_eq {a b k : ℕ} :
    (Finset.Ico (k + 1) (a + b)).filter (fun s => ¬ IsRaising a b (rotSlot a b s))
      = ((Finset.range (a + b)).filter
          fun t => ¬ IsRaising a b (rotSlot a b t)).filter fun s => k < s := by
  ext s
  simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_range]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h2, h3⟩, by omega⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨by omega, h1⟩, h2⟩

/-- **The crossing prefactor is the product over the interchanged pairs.** The pairs the sorting
interchanges are the `(s, s')` with `s` lowering, `s'` raising and `s' < s`, which is
`(slotPairs a b c).filter fun p => p.2 < p.1` -- the index set `assembled_exponents` runs
over. -/
theorem crossFrom_zero_eq_prod_slotPairs {a b : ℕ} (hd : 0 < a + b) :
    crossFrom a b 0
      = ∏ p ∈ (slotPairs a b ((a + b) - rotOffset a b % (a + b))).filter fun p => p.2 < p.1,
          (1 - X ^ (p.1 - p.2) : ℤ⟦X⟧) := by
  classical
  have hset : slotPairs a b ((a + b) - rotOffset a b % (a + b))
      = ((Finset.range (a + b)).filter fun t => ¬ IsRaising a b (rotSlot a b t)) ×ˢ
        ((Finset.range (a + b)).filter fun t => IsRaising a b (rotSlot a b t)) := by
    simp only [slotPairs, rotSlot_eq_add_mod hd]
  rw [hset, Finset.prod_filter, Finset.prod_product_right]
  rw [crossFrom, Nat.sub_zero, ← List.range_eq_range', prod_map_range, Finset.prod_filter]
  refine Finset.prod_congr rfl fun k _ => ?_
  by_cases hr : IsRaising a b (rotSlot a b k)
  · rw [ite_eq_left hr, crossAt, ite_eq_left hr, lowFrom, prod_map_sort, lowFromFinset_eq,
      Finset.prod_filter]
  · rw [ite_eq_right hr, crossAt, ite_eq_right hr]

/-! ### Part (a): the slices of a diagonal function, read around the cycle

The correspondence part (a) needs runs `W ↦ fun i => slice hd hW (((i + c) a) mod d)`: the slices of
the diagonal function, read at the residues the step word visits. `isHStrip_slice_of_isRaising` and
`isHStrip_slice_of_not_isRaising` are stated in exactly that residue labelling. This section proves
that this map lands in the sequences respecting the step word and carries the volume to the total of
their sizes; the next section inverts it. -/

theorem isRaising_mod {a b t : ℕ} : IsRaising a b (t % (a + b)) ↔ IsRaising a b t := by
  rw [IsRaising, IsRaising, Nat.mod_mul_mod]

/-- Stepping the cycle position by one steps the slot by one, modulo `d`. -/
theorem val_add_one_modEq {n : ℕ} [NeZero n] (i : Fin n) :
    ((i + 1 : Fin n) : ℕ) ≡ (i : ℕ) + 1 [MOD n] :=
  calc ((i + 1 : Fin n) : ℕ) = ((i : ℕ) + ((1 : Fin n) : ℕ)) % n := Fin.val_add i 1
    _ ≡ (i : ℕ) + ((1 : Fin n) : ℕ) [MOD n] := Nat.mod_modEq _ _
    _ ≡ (i : ℕ) + 1 [MOD n] := Nat.ModEq.add_left _ (by rw [Fin.val_one']; exact Nat.mod_modEq 1 n)

/-- **The residue at the next cycle position is the residue the step lemmas
`isHStrip_slice_of_isRaising` and `isHStrip_slice_of_not_isRaising` produce at the next slot.** The
wrap-around of `Fin d` is invisible to the residue, which is what lets the slice correspondence be
stated on `Fin d` at all. -/
theorem slotIdx_succ {a b c : ℕ} [NeZero (a + b)] (i : Fin (a + b)) :
    (((i + 1 : Fin (a + b)) : ℕ) + c) * a % (a + b) = ((i : ℕ) + c + 1) * a % (a + b) := by
  have h := ((val_add_one_modEq i).add_right c).mul_right a
  rwa [show (i : ℕ) + 1 + c = (i : ℕ) + c + 1 from by omega] at h

/-- The **slices of a diagonal function read around the cycle**, at the residues the step word
shifted by `c` visits. -/
noncomputable def sliceCyc {a b : ℕ} (hd : 0 < a + b) {W : ℕ → ℕ} (hW : IsDiagFun a b W) (c : ℕ)
    (i : Fin (a + b)) : Part :=
  slice hd hW (((i : ℕ) + c) * a % (a + b))

/-- **The slices of a diagonal function respect the step word**: at a raising slot the next slice
contains this one and at a lowering slot the other way round. The two directions are
`isHStrip_slice_of_isRaising` and `isHStrip_slice_of_not_isRaising`. -/
theorem respectsWord_sliceCyc {a b : ℕ} (hd : 0 < a + b) [NeZero (a + b)] {W : ℕ → ℕ}
    (hW : IsDiagFun a b W) (c : ℕ) : RespectsWord a b c (sliceCyc hd hW c) := by
  intro i
  have hnext : sliceCyc hd hW c (i + 1) = slice hd hW (((i : ℕ) + c + 1) * a % (a + b)) := by
    rw [sliceCyc, slotIdx_succ]
  by_cases hr : IsRaising a b (((i : ℕ) + c) % (a + b))
  · rw [isSlotStrip_iff_of_isRaising hr, hnext, sliceCyc]
    exact isHStrip_slice_of_isRaising hd hW (isRaising_mod.mp hr)
  · rw [isSlotStrip_iff_of_not_isRaising hr, hnext, sliceCyc]
    exact isHStrip_slice_of_not_isRaising hd hW fun h => hr (isRaising_mod.mpr h)

/-! ### The slots are reindexed by multiplication by `a` -/

theorem coprime_add_left {a b : ℕ} (hco : Nat.Coprime a b) : Nat.Coprime (a + b) a := by
  rw [Nat.coprime_comm, Nat.add_comm, Nat.coprime_add_self_right]
  exact hco

/-- **The slot map is injective on the cycle positions.** `a` is coprime to `d`, so multiplication
by `a` is injective modulo `d`, and so is the shift by `c`. -/
theorem injOn_shift_mul_mod {a b : ℕ} (hco : Nat.Coprime a b) (c : ℕ) :
    ∀ t < a + b, ∀ t' < a + b, (t + c) * a % (a + b) = (t' + c) * a % (a + b) → t = t' := by
  intro t ht t' ht' h
  have h2 : t + c ≡ t' + c [MOD a + b] :=
    Nat.ModEq.cancel_right_of_coprime (coprime_add_left hco) h
  have h3 : t ≡ t' [MOD a + b] := Nat.ModEq.add_right_cancel' c h2
  rwa [Nat.ModEq, Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt ht'] at h3

/-- **The slot map permutes the residues**, so a sum over the cycle positions of a function of the
slot is the same sum over the slots. -/
theorem sum_shift_mul_mod {M : Type*} [AddCommMonoid M] {a b : ℕ} (hd : 0 < a + b)
    (hco : Nat.Coprime a b) (c : ℕ) (f : ℕ → M) :
    ∑ t ∈ range (a + b), f ((t + c) * a % (a + b)) = ∑ u ∈ range (a + b), f u := by
  classical
  have hinj : ∀ t ∈ range (a + b), ∀ t' ∈ range (a + b),
      (t + c) * a % (a + b) = (t' + c) * a % (a + b) → t = t' := fun t ht t' ht' h =>
    injOn_shift_mul_mod hco c t (mem_range.mp ht) t' (mem_range.mp ht') h
  have himg : (range (a + b)).image (fun t => (t + c) * a % (a + b)) = range (a + b) := by
    refine Finset.eq_of_subset_of_card_le (fun u hu => ?_) ?_
    · obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hu
      exact mem_range.mpr (Nat.mod_lt _ hd)
    · rw [Finset.card_image_of_injOn fun t ht t' ht' h =>
        hinj t (Finset.mem_coe.mp ht) t' (Finset.mem_coe.mp ht') h]
  conv_rhs => rw [← himg]
  rw [Finset.sum_image hinj]

/-- **The slice sizes total the volume.** The cycle visits every slot exactly once, so the total of
the sizes of the slices read around the cycle is `∑_w W w`, which by `cylVolume_eq_finsum` is the
volume of the cylindric partition. This is `sum_size_slice` in the cycle's labelling. -/
theorem sum_size_sliceCyc {a b : ℕ} (hd : 0 < a + b) [NeZero (a + b)] (hco : Nat.Coprime a b)
    {W : ℕ → ℕ} (hW : IsDiagFun a b W) (c : ℕ) :
    ∑ i : Fin (a + b), (sliceCyc hd hW c i).size = ∑ᶠ w, W w := by
  have h1 : ∑ i : Fin (a + b), (sliceCyc hd hW c i).size
      = ∑ t ∈ range (a + b), (slice hd hW ((t + c) * a % (a + b))).size :=
    Fin.sum_univ_eq_sum_range (fun t : ℕ => (slice hd hW ((t + c) * a % (a + b))).size) (a + b)
  rw [h1, sum_shift_mul_mod hd hco c fun u => (slice hd hW u).size, sum_size_slice hd hW]
/-! ### The inverse of the slice map

The map of the previous section is `W ↦ fun i => slice hd hW (r i)` at `r i = ((i + c) a) mod d`,
so its inverse must read the value of `W` at the position `w` off the slice sitting at the residue
`w mod d`. Which cycle position that is, is the inverse of `i ↦ r i`: multiplication by `a` is
invertible modulo `d` because `a` is coprime to `d`, so `slotPerm` is a permutation of the cycle
positions and `diagOfCyc` is the composite

    w ↦ (cyc (slotPerm.symm (w mod d))).parts (w / d).

That this lands in the diagonal functions is the converse of the two step lemmas
`isHStrip_slice_of_isRaising` and `isHStrip_slice_of_not_isRaising`, and it is one
case split: at a raising slot the step by `a` crosses the period and reads the *second* half of
`IsHStrip`, at a lowering slot it stays inside the period and reads the first. The step by `b` runs
the same analysis one cycle position *earlier*, since `r (i+1) + b ≡ r i` modulo `d`, which is why
`exists_add_one` is needed: the analysis at `w` is the analysis at the position whose successor
`slotPerm.symm (w mod d)` is. -/

/-- **The slot map as a permutation of the cycle positions**: `i ↦ ((i + c) a) mod d`, injective by
`injOn_shift_mul_mod` and hence bijective on a finite type. -/
noncomputable def slotPerm {a b : ℕ} (hd : 0 < a + b) (hco : Nat.Coprime a b) (c : ℕ) :
    Fin (a + b) ≃ Fin (a + b) :=
  Equiv.ofBijective (fun i => ⟨((i : ℕ) + c) * a % (a + b), Nat.mod_lt _ hd⟩)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨fun i i' h =>
        Fin.ext (injOn_shift_mul_mod hco c i i.isLt i' i'.isLt (congrArg Fin.val h)), rfl⟩)

theorem slotPerm_val {a b : ℕ} (hd : 0 < a + b) (hco : Nat.Coprime a b) (c : ℕ)
    (i : Fin (a + b)) : ((slotPerm hd hco c i : Fin (a + b)) : ℕ) = ((i : ℕ) + c) * a % (a + b) :=
  rfl

/-- The slot of the cycle position `slotPerm.symm t` is `t`. -/
theorem slotPerm_symm_val {a b : ℕ} (hd : 0 < a + b) (hco : Nat.Coprime a b) (c : ℕ)
    (t : Fin (a + b)) :
    ((((slotPerm hd hco c).symm t : Fin (a + b)) : ℕ) + c) * a % (a + b) = (t : ℕ) := by
  conv_rhs => rw [← Equiv.apply_symm_apply (slotPerm hd hco c) t]
  rfl

/-- The cycle position at a given slot is the one the slot map sends there. -/
theorem slotPerm_symm_eq {a b : ℕ} (hd : 0 < a + b) (hco : Nat.Coprime a b) (c : ℕ)
    {i t : Fin (a + b)} (h : (t : ℕ) = ((i : ℕ) + c) * a % (a + b)) :
    (slotPerm hd hco c).symm t = i := by
  rw [show t = slotPerm hd hco c i from Fin.ext (by rw [h, slotPerm_val]), Equiv.symm_apply_apply]

/-- The **diagonal function of a closed cycle of partitions**: the value at `w` is the part
indexed by `w / d` of the partition sitting at the cycle position whose slot is `w mod d`. This is
the inverse of `sliceCyc`. -/
noncomputable def diagOfCyc {a b : ℕ} (hd : 0 < a + b) (hco : Nat.Coprime a b) (c : ℕ)
    (cyc : Fin (a + b) → Part) (w : ℕ) : ℕ :=
  (cyc ((slotPerm hd hco c).symm ⟨w % (a + b), Nat.mod_lt w hd⟩)).parts (w / (a + b))

/-- **The defining computation of `diagOfCyc`**: writing the position as `d j + r` with `r` the slot
of the cycle position `i` reads the `j`-th part of `cyc i`. Every step estimate below is this
identity at two positions. -/
theorem diagOfCyc_of_eq {a b : ℕ} (hd : 0 < a + b) (hco : Nat.Coprime a b) (c : ℕ)
    (cyc : Fin (a + b) → Part) {w : ℕ} (i : Fin (a + b)) (j r : ℕ)
    (hri : r = ((i : ℕ) + c) * a % (a + b)) (hw : w = (a + b) * j + r) :
    diagOfCyc hd hco c cyc w = (cyc i).parts j := by
  have hr : r < a + b := by rw [hri]; exact Nat.mod_lt _ hd
  have hmod : w % (a + b) = r := by rw [hw, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
  have hdiv : w / (a + b) = j := by
    rw [hw, Nat.mul_add_div hd, Nat.div_eq_of_lt hr, Nat.add_zero]
  rw [diagOfCyc, hdiv,
    slotPerm_symm_eq hd hco c (t := ⟨w % (a + b), Nat.mod_lt w hd⟩) (i := i) (hmod.trans hri)]

/-- At a raising cycle position the next partition contains this one by a horizontal strip. -/
theorem isHStrip_of_respectsWord_of_isRaising {a b c : ℕ} [NeZero (a + b)]
    {cyc : Fin (a + b) → Part} (h : RespectsWord a b c cyc) {i : Fin (a + b)}
    (hr : b ≤ ((i : ℕ) + c) * a % (a + b)) : IsHStrip (cyc (i + 1)) (cyc i) :=
  (isSlotStrip_iff_of_isRaising (isRaising_mod.mpr hr) _ _).mp (h i)

/-- At a lowering cycle position this partition contains the next one by a horizontal strip. -/
theorem isHStrip_of_respectsWord_of_not_isRaising {a b c : ℕ} [NeZero (a + b)]
    {cyc : Fin (a + b) → Part} (h : RespectsWord a b c cyc) {i : Fin (a + b)}
    (hr : ¬ b ≤ ((i : ℕ) + c) * a % (a + b)) : IsHStrip (cyc i) (cyc (i + 1)) :=
  (isSlotStrip_iff_of_not_isRaising (fun hc => hr (isRaising_mod.mp hc)) _ _).mp (h i)

/-- At a raising cycle position the slot drops by `b`. -/
theorem slotVal_succ_of_isRaising {a b c : ℕ} [NeZero (a + b)] (hd : 0 < a + b) (i : Fin (a + b))
    (hr : b ≤ ((i : ℕ) + c) * a % (a + b)) :
    (((i + 1 : Fin (a + b)) : ℕ) + c) * a % (a + b) = ((i : ℕ) + c) * a % (a + b) - b := by
  rw [slotIdx_succ, succ_mul_mod_of_isRaising hd hr]

/-- At a lowering cycle position the slot advances by `a`. -/
theorem slotVal_succ_of_not_isRaising {a b c : ℕ} [NeZero (a + b)] (hd : 0 < a + b)
    (i : Fin (a + b)) (hr : ¬ b ≤ ((i : ℕ) + c) * a % (a + b)) :
    (((i + 1 : Fin (a + b)) : ℕ) + c) * a % (a + b) = ((i : ℕ) + c) * a % (a + b) + a := by
  rw [slotIdx_succ, succ_mul_mod_of_not_isRaising hd hr]

/-- **Advancing the position by `a` does not increase `diagOfCyc`.** At a raising cycle position
the step crosses the period, landing on the next part of the next partition, and the bound is the
second half of `IsHStrip`; at a lowering one it stays inside the period, landing on the same part of
the next partition, and the bound is the first half. -/
theorem diagOfCyc_step_left {a b c : ℕ} (hd : 0 < a + b) [NeZero (a + b)]
    (hco : Nat.Coprime a b) {cyc : Fin (a + b) → Part} (h : RespectsWord a b c cyc) (w : ℕ) :
    diagOfCyc hd hco c cyc (w + a) ≤ diagOfCyc hd hco c cyc w := by
  set i := (slotPerm hd hco c).symm ⟨w % (a + b), Nat.mod_lt w hd⟩ with hidef
  have hri : ((i : ℕ) + c) * a % (a + b) = w % (a + b) := slotPerm_symm_val hd hco c _
  have hs : w % (a + b) < a + b := Nat.mod_lt w hd
  have hw : (a + b) * (w / (a + b)) + w % (a + b) = w := Nat.div_add_mod w (a + b)
  have hWw : diagOfCyc hd hco c cyc w = (cyc i).parts (w / (a + b)) :=
    diagOfCyc_of_eq hd hco c cyc i _ _ hri.symm hw.symm
  by_cases hr : b ≤ ((i : ℕ) + c) * a % (a + b)
  · have hnext : ((i : ℕ) + c) * a % (a + b) - b
        = (((i + 1 : Fin (a + b)) : ℕ) + c) * a % (a + b) :=
      (slotVal_succ_of_isRaising hd i hr).symm
    have hWa : diagOfCyc hd hco c cyc (w + a) = (cyc (i + 1)).parts (w / (a + b) + 1) :=
      diagOfCyc_of_eq hd hco c cyc (i + 1) _ _ hnext
        (by rw [show (a + b) * (w / (a + b) + 1) = (a + b) * (w / (a + b)) + (a + b) from by ring]
            omega)
    rw [hWw, hWa]
    exact (isHStrip_of_respectsWord_of_isRaising h hr _).2
  · have hnext : ((i : ℕ) + c) * a % (a + b) + a
        = (((i + 1 : Fin (a + b)) : ℕ) + c) * a % (a + b) :=
      (slotVal_succ_of_not_isRaising hd i hr).symm
    have hWa : diagOfCyc hd hco c cyc (w + a) = (cyc (i + 1)).parts (w / (a + b)) :=
      diagOfCyc_of_eq hd hco c cyc (i + 1) _ _ hnext (by omega)
    rw [hWw, hWa]
    exact (isHStrip_of_respectsWord_of_not_isRaising h hr _).1

/-- Every cycle position is the successor of one, `i ↦ i + 1` being a bijection of `Fin d`. -/
theorem exists_add_one {n : ℕ} [NeZero n] (i : Fin n) : ∃ i₀ : Fin n, i₀ + 1 = i :=
  ⟨i - 1, by abel⟩

/-- **Advancing the position by `b` does not increase `diagOfCyc`.** The same case split as
`diagOfCyc_step_left`, run at the cycle position one *before* the one the position sits at: the
slots satisfy `r (i+1) + b ≡ r i` modulo `d`, so a step by `b` moves backwards along the cycle. At a
raising position it stays inside the period and the bound is the first half of `IsHStrip`; at a
lowering one it crosses the period and the bound is the second. -/
theorem diagOfCyc_step_right {a b c : ℕ} (hd : 0 < a + b) [NeZero (a + b)]
    (hco : Nat.Coprime a b) {cyc : Fin (a + b) → Part} (h : RespectsWord a b c cyc) (w : ℕ) :
    diagOfCyc hd hco c cyc (w + b) ≤ diagOfCyc hd hco c cyc w := by
  obtain ⟨i, hi⟩ := exists_add_one ((slotPerm hd hco c).symm ⟨w % (a + b), Nat.mod_lt w hd⟩)
  have hri : (((i + 1 : Fin (a + b)) : ℕ) + c) * a % (a + b) = w % (a + b) := by
    rw [hi]; exact slotPerm_symm_val hd hco c _
  have hs : w % (a + b) < a + b := Nat.mod_lt w hd
  have hw : (a + b) * (w / (a + b)) + w % (a + b) = w := Nat.div_add_mod w (a + b)
  have hWw : diagOfCyc hd hco c cyc w = (cyc (i + 1)).parts (w / (a + b)) :=
    diagOfCyc_of_eq hd hco c cyc (i + 1) _ _ hri.symm hw.symm
  by_cases hr : b ≤ ((i : ℕ) + c) * a % (a + b)
  · have h0 : ((i : ℕ) + c) * a % (a + b) = w % (a + b) + b := by
      have hstep := slotVal_succ_of_isRaising hd i hr
      rw [hri] at hstep
      omega
    have hWb : diagOfCyc hd hco c cyc (w + b) = (cyc i).parts (w / (a + b)) :=
      diagOfCyc_of_eq hd hco c cyc i _ _ rfl (by omega)
    rw [hWw, hWb]
    exact (isHStrip_of_respectsWord_of_isRaising h hr _).1
  · have h0 : ((i : ℕ) + c) * a % (a + b) + a = w % (a + b) := by
      have hstep := slotVal_succ_of_not_isRaising hd i hr
      rw [hri] at hstep
      omega
    have hWb : diagOfCyc hd hco c cyc (w + b) = (cyc i).parts (w / (a + b) + 1) :=
      diagOfCyc_of_eq hd hco c cyc i _ _ rfl
        (by rw [show (a + b) * (w / (a + b) + 1) = (a + b) * (w / (a + b)) + (a + b) from by ring]
            omega)
    rw [hWw, hWb]
    exact (isHStrip_of_respectsWord_of_not_isRaising h hr _).2

/-- **`diagOfCyc` is finitely supported**: each of the `d` partitions has finitely many nonzero
parts, so `d` times the largest of their bounds bounds the support. -/
theorem diagOfCyc_vanish {a b : ℕ} (hd : 0 < a + b) (hco : Nat.Coprime a b) (c : ℕ)
    (cyc : Fin (a + b) → Part) : ∃ B, ∀ w, B ≤ w → diagOfCyc hd hco c cyc w = 0 := by
  have hex : ∀ i : Fin (a + b), ∃ B, ∀ k, B ≤ k → (cyc i).parts k = 0 := fun i => (cyc i).vanish
  choose B hB using hex
  refine ⟨(a + b) * Finset.univ.sup B, fun w hw => ?_⟩
  rw [diagOfCyc]
  refine hB _ _ (le_trans (Finset.le_sup (f := B) (Finset.mem_univ _)) ?_)
  exact (Nat.le_div_iff_mul_le hd).mpr (by rw [Nat.mul_comm]; exact hw)

/-- **A cycle respecting the step word is the slice sequence of a diagonal function.** The converse
of `respectsWord_sliceCyc`, and the direction `isHStrip_slice_of_isRaising` and
`isHStrip_slice_of_not_isRaising` do not state: the two step conditions of `IsDiagFun` are the two
halves of the strip conditions, read at the raising and the lowering slots. -/
theorem isDiagFun_diagOfCyc {a b c : ℕ} (hd : 0 < a + b) [NeZero (a + b)]
    (hco : Nat.Coprime a b) {cyc : Fin (a + b) → Part} (h : RespectsWord a b c cyc) :
    IsDiagFun a b (diagOfCyc hd hco c cyc) :=
  ⟨diagOfCyc_step_left hd hco h, diagOfCyc_step_right hd hco h, diagOfCyc_vanish hd hco c cyc⟩

/-- Reading a diagonal function around the cycle and reassembling it recovers it: every position is
`d (w / d) + (w mod d)`, and the slot map hits `w mod d` at exactly one cycle position. -/
theorem diagOfCyc_sliceCyc {a b : ℕ} (hd : 0 < a + b) (hco : Nat.Coprime a b) {W : ℕ → ℕ}
    (hW : IsDiagFun a b W) (c : ℕ) : diagOfCyc hd hco c (sliceCyc hd hW c) = W := by
  funext w
  set i := (slotPerm hd hco c).symm ⟨w % (a + b), Nat.mod_lt w hd⟩ with hidef
  have hri : ((i : ℕ) + c) * a % (a + b) = w % (a + b) := slotPerm_symm_val hd hco c _
  have hw : (a + b) * (w / (a + b)) + w % (a + b) = w := Nat.div_add_mod w (a + b)
  rw [diagOfCyc_of_eq hd hco c _ i (w / (a + b)) (w % (a + b)) hri.symm hw.symm, sliceCyc,
    slice_parts, hri, show w % (a + b) + (a + b) * (w / (a + b)) = w from by omega]

/-- Reassembling a cycle into a diagonal function and slicing it recovers the cycle. -/
theorem sliceCyc_diagOfCyc {a b c : ℕ} (hd : 0 < a + b) [NeZero (a + b)] (hco : Nat.Coprime a b)
    {cyc : Fin (a + b) → Part} (h : RespectsWord a b c cyc) :
    sliceCyc hd (isDiagFun_diagOfCyc hd hco h) c = cyc := by
  funext i
  refine Part.ext (funext fun j => ?_)
  rw [sliceCyc, slice_parts]
  exact diagOfCyc_of_eq hd hco c cyc i j _ rfl (Nat.add_comm _ _)

/-- **The slice correspondence.** Reading a diagonal function at the residues the step word visits
is a bijection onto the closed cycles of partitions the slot-ordered trace sees. This is the strip
half of part (a); `sum_size_sliceCyc` is the exponent half. -/
noncomputable def cycEquiv {a b : ℕ} (hd : 0 < a + b) [NeZero (a + b)] (hco : Nat.Coprime a b)
    (c : ℕ) :
    {W : ℕ → ℕ // IsDiagFun a b W} ≃ ↥{cyc : Fin (a + b) → Part | RespectsWord a b c cyc} where
  toFun W := ⟨sliceCyc hd W.2 c, respectsWord_sliceCyc hd W.2 c⟩
  invFun cyc := ⟨diagOfCyc hd hco c cyc.1, isDiagFun_diagOfCyc hd hco cyc.2⟩
  left_inv W := Subtype.ext (diagOfCyc_sliceCyc hd hco W.2 c)
  right_inv cyc := Subtype.ext (sliceCyc_diagOfCyc hd hco cyc.2)

/-- **Part (a) of the comparison.** The sum the slot-ordered trace produces is the cylindric
series: the cycles respecting the step word are the slice sequences of the diagonal functions
(`cycEquiv`), their total size is the total of the diagonal function (`sum_size_sliceCyc`), and the
diagonal functions are the cylindric partitions of the balanced profile with their volume
(`cylDiagEquiv` and `cylVolume_eq_finsum`). The shift `c` is arbitrary, as it must be: the series
counts cylindric partitions and knows nothing about where the reading of the cycle starts. -/
theorem tsum_respectsWord_eq_unboundedGF {a b : ℕ} (hd : 0 < a + b) [NeZero (a + b)]
    (hco : Nat.Coprime a b) (ha : 0 < a) (c : ℕ) :
    ∑' cyc : ↥{cyc : Fin (a + b) → Part | RespectsWord a b c cyc},
        X ^ ∑ i : Fin (a + b), ((cyc : Fin (a + b) → Part) i).size
      = HJO.Cylindric.unboundedGF a b := by
  calc ∑' cyc : ↥{cyc : Fin (a + b) → Part | RespectsWord a b c cyc},
        (X : ℤ⟦X⟧) ^ ∑ i : Fin (a + b), ((cyc : Fin (a + b) → Part) i).size
      = ∑' W : {W : ℕ → ℕ // IsDiagFun a b W}, (X : ℤ⟦X⟧) ^ ∑ᶠ w, W.1 w := by
        rw [← Equiv.tsum_eq (cycEquiv hd hco c)
          fun cyc : ↥{cyc : Fin (a + b) → Part | RespectsWord a b c cyc} =>
            (X : ℤ⟦X⟧) ^ ∑ i : Fin (a + b), ((cyc : Fin (a + b) → Part) i).size]
        exact tsum_congr fun W =>
          congrArg (fun n => (X : ℤ⟦X⟧) ^ n) (sum_size_sliceCyc hd hco W.2 c)
    _ = HJO.Cylindric.unboundedGF a b := by
        rw [HJO.Cylindric.unboundedGF, ← Equiv.tsum_eq (cylDiagEquiv hco ha)
          fun W : {W : ℕ → ℕ // IsDiagFun a b W} => (X : ℤ⟦X⟧) ^ ∑ᶠ w, W.1 w]
        exact tsum_congr fun l =>
          congrArg (fun n => (X : ℤ⟦X⟧) ^ n) (cylVolume_eq_finsum hco ha l.2).symm

/-! ### Multiplying the three parts together

The three parts multiply together with no further work: part (a) rewrites the trace of the
slot-ordered word as `C_c(q)`, part (b) turns the crossing prefactor times that trace into the trace
of `transferKernel`, and part (c) names the prefactor as the product over the interchanged
pairs.

The identity in the source reads

    C_c(q) = (∏_{s lowering, s' raising, s' < s} (1 - q^{s-s'})^{-1}) Tr S

and the statement below is that identity multiplied through by the prefactor. In `ℤ⟦X⟧` the two
forms say the same thing -- each factor `1 - q^{s-s'}` has `s - s' ≥ 1` and so is a unit -- and the
inverse-free one is what `borodin_form_of_pref_trace` consumes. -/

/-- **The cylindric series is the sorted trace with the crossing prefactor.** With `d = a + b`, `S`
the sorted transfer kernel `transferKernel a b` and the slots those of its rotated word,

`(∏_{s lowering, s' raising, s' < s} (1 - q^{s-s'})) C_c(q) = Tr S`,

which is the identity of the source cleared of its inverses. The index set is `slotPairs` at the
rotation shift, cut down to the pairs the sorting actually interchanges: `p.1` runs over the
lowering slots, `p.2` over the raising ones, and the filter keeps `p.2 < p.1`. -/
@[hjo "lem_cyl_pref_trace"]
theorem prod_slotPairs_mul_unboundedGF {a b : ℕ} (hco : Nat.Coprime a b) (ha : 0 < a)
    (hb : 0 < b) :
    (∏ p ∈ (slotPairs a b ((a + b) - rotOffset a b % (a + b))).filter fun p => p.2 < p.1,
        (1 - X ^ (p.1 - p.2) : ℤ⟦X⟧)) * HJO.Cylindric.unboundedGF a b
      = ktrace (transferKernel a b) := by
  have hd : 0 < a + b := by omega
  have : NeZero (a + b) := ⟨by omega⟩
  rw [← crossFrom_zero_eq_prod_slotPairs hd, ← crossFrom_zero_mul_ktrace_slotWord hb hd,
    ktrace_slotWord_eq_tsum, tsum_respectsWord_eq_unboundedGF hd hco ha]

/-! ### Why the induction runs over suffixes, and which associativity it uses

**The invariant of the sorting induction is a suffix invariant, not a prefix one.** The prefix
invariant `A^{(k)}_+ = ∏_{s<k raising} Γ_+(q^{k-1-s})` carries the argument `q^0` exactly when slot
`k-1` is raising -- so a prefix partial product contains `Γ_+(1)`, which is not `StepBdd`, and the
constraint that only sorted partial products may be evaluated is violated *inside* the invariant
itself. The induction here runs over suffixes instead:

    T_k = P_k · A^{[k]}_- · Q(q^{d-k}) · A^{[k]}_+
    A^{[k]}_- = ∏_{k ≤ s < d, s lowering} Γ_-(q^{s-k+1}),
    A^{[k]}_+ = ∏_{k ≤ s < d, s raising} Γ_+(q^{d-1-s}),
    P_k       = ∏_{k ≤ s' < s < d, s lowering, s' raising} (1 - q^{s-s'})^{-1}

Here the raising argument `q^{d-1-s}` degenerates only at `s = d - 1`, and slot `d - 1` of the
rotated word is *lowering* -- that is what the rotation of `transferKernel` is for, and it is
`not_isRaising_rotSlot_last`. So every factor of every sorted suffix carries a positive power of
`q`, every sorted suffix is `StepBdd` (`stepBdd_klist_sortedFrom`), and the unsorted reading enters
only as the single slot factor at the head of the step.

**The associativity that induction needs is not `Algebra.lean`'s `kmul_assoc`.** That lemma and
`klist_append` ask *every* factor to be step-bounded, and the head slot factor never is.
`kmul_assoc_mid`, `kmul_assoc_outer`, `kmul_assoc_leftmid` and `klist_append_left` above ask for two
of the three, in each of the three positions, which is all the interchange actually uses. -/

end HJO.CylindricProduct
