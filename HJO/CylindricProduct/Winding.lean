/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CylindricProduct.Algebra
public import HJO.CylindricProduct.Commutation
public import HJO.CylindricProduct.SameCommute
public meta import HJO.Attr

/-! # The winding recursion

The trace of the winding shape

`F(y) = Tr(Γ_-(y_1) ⋯ Γ_-(y_b) Q(q^d) Γ_+(x_1) ⋯ Γ_+(x_a))`

satisfies `F(y) ∏_{i,j}(1 - x_i y_j) = F(q^d y)`. This file proves that recursion, one lowering
argument at a time, in the inverse-free form the rest of the development uses.

To raise the argument of one lowering factor by `q^d`:

* bring that factor to the head of the product, the lowering factors commuting with one another
  (`klist_lowList_toFront`, from `gammaMinus_kmul_comm`);
* rotate the head to the tail, which the trace permits (`ktrace_klist_rotate`, from
  `ktrace_kmul_comm`);
* move it back leftwards through the raising factors, each interchange costing one factor
  `1 - x_i y_j` (`cscale_klist_raiseList_snoc`, from `one_sub_mul_gammaPlus_kmul_gammaMinus`);
* move it leftwards across the grading, which raises its argument by `q^d`
  (`kmul_grading_gammaMinus_cons`, from `grading_kmul_gammaMinus`);
* and bring it back to where it started.

Each of those moves reassociates the bracketing of the product, which is why they need
`kmul_assoc`; and the `1 - x_i y_j` are power series standing in front of a kernel, which is what
`cscale` names and what `cscale_kmul_left` and `cscale_kmul_right` move past a product.

What is **not** here is the passage to the limit: iterating the recursion `K` times and letting
`K → ∞`, which is the step that turns `∏_{k < K}` into `∏_{k ≥ 0}` and evaluates the limit by
`selfQPochhammerInf_mul_ktrace_raising`. That is `HJO.CylindricProduct.WindingLimit`, which
combines this recursion with the evaluation at `0` proved in `HJO.CylindricProduct.TraceRaising`
and so states the winding identity itself.
-/

@[expose] public section

open Finset Filter PowerSeries
open scoped QTheory Topology PowerSeries.DiscreteTopology

namespace HJO.CylindricProduct

/-! ### Scaling a kernel by a power series -/

/-- **Scaling a kernel**: multiply every entry by a fixed power series. The factors
`(1 - x_iy_j)^{-1}` of the winding recursion stand in front of kernels, and this is the operation
that puts them there. -/
noncomputable def cscale (c : ℤ⟦X⟧) (K : Kernel) : Kernel := fun lam nu => c * K lam nu

@[simp] theorem cscale_apply (c : ℤ⟦X⟧) (K : Kernel) (lam nu : Part) :
    cscale c K lam nu = c * K lam nu := rfl

@[simp] theorem cscale_one (K : Kernel) : cscale 1 K = K := by
  funext lam nu; rw [cscale_apply, one_mul]

theorem cscale_cscale (c c' : ℤ⟦X⟧) (K : Kernel) :
    cscale c (cscale c' K) = cscale (c * c') K := by
  funext lam nu; rw [cscale_apply, cscale_apply, cscale_apply, mul_assoc]

theorem StepBdd.cscale {c : ℤ⟦X⟧} {K : Kernel} (hK : StepBdd K) :
    StepBdd (CylindricProduct.cscale c K) :=
  fun lam nu => Dvd.dvd.mul_left (hK lam nu) c

/-- A scalar in front of the right factor comes out of the product. -/
theorem cscale_kmul_right {c : ℤ⟦X⟧} {K L : Kernel} (hK : StepBdd K) (hL : StepBdd L) :
    kmul K (cscale c L) = cscale c (kmul K L) := by
  funext lam nu
  rw [cscale_apply, kmul, kmul, ← (summable_kmul hK hL lam nu).tsum_mul_left c]
  exact tsum_congr fun tau => by rw [cscale_apply]; ring

/-- A scalar in front of the left factor comes out of the product. -/
theorem cscale_kmul_left {c : ℤ⟦X⟧} {K L : Kernel} (hK : StepBdd K) (hL : StepBdd L) :
    kmul (cscale c K) L = cscale c (kmul K L) := by
  funext lam nu
  rw [cscale_apply, kmul, kmul, ← (summable_kmul hK hL lam nu).tsum_mul_left c]
  exact tsum_congr fun tau => by rw [cscale_apply]; ring

/-- A scalar in front of a kernel comes out of its trace. -/
theorem ktrace_cscale (c : ℤ⟦X⟧) {K : Kernel} (h : TraceSummable K) :
    ktrace (cscale c K) = c * ktrace K := by
  rw [ktrace, ktrace, ← h.tsum_mul_left c]
  exact tsum_congr fun lam => rfl

/-! ### The two lists of vertex operators -/

/-- The lowering kernels `Γ_-(q^m)` at the given exponents, in order. -/
noncomputable def lowList (ms : List ℕ) : List Kernel := ms.map fun m => gammaMinus (X ^ m)

/-- The raising kernels `Γ_+(q^p)` at the given exponents, in order. -/
noncomputable def raiseList (ps : List ℕ) : List Kernel := ps.map fun p => gammaPlus (X ^ p)

@[simp] theorem lowList_nil : lowList [] = [] := rfl

@[simp] theorem lowList_cons (m : ℕ) (ms : List ℕ) :
    lowList (m :: ms) = gammaMinus (X ^ m) :: lowList ms := rfl

theorem lowList_append (ms ns : List ℕ) : lowList (ms ++ ns) = lowList ms ++ lowList ns :=
  List.map_append

@[simp] theorem raiseList_nil : raiseList [] = [] := rfl

@[simp] theorem raiseList_cons (p : ℕ) (ps : List ℕ) :
    raiseList (p :: ps) = gammaPlus (X ^ p) :: raiseList ps := rfl

theorem isVertex_lowList {ms : List ℕ} (hms : ∀ m ∈ ms, 1 ≤ m) :
    ∀ K ∈ lowList ms, IsVertex K := by
  intro K hK
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hK
  exact IsVertex.minus m (hms m hm)

theorem isVertex_raiseList {ps : List ℕ} (hps : ∀ p ∈ ps, 1 ≤ p) :
    ∀ K ∈ raiseList ps, IsVertex K := by
  intro K hK
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hK
  exact IsVertex.plus p (hps p hp)

theorem stepBdd_lowList {ms : List ℕ} (hms : ∀ m ∈ ms, 1 ≤ m) :
    ∀ K ∈ lowList ms, StepBdd K := fun K hK => (isVertex_lowList hms K hK).stepBdd

theorem stepBdd_raiseList {ps : List ℕ} (hps : ∀ p ∈ ps, 1 ≤ p) :
    ∀ K ∈ raiseList ps, StepBdd K := fun K hK => (isVertex_raiseList hps K hK).stepBdd

/-- The factors of the winding shape are all vertex operators. -/
theorem isVertex_windList {d : ℕ} (hd : 1 ≤ d) {ms ps : List ℕ} (hms : ∀ m ∈ ms, 1 ≤ m)
    (hps : ∀ p ∈ ps, 1 ≤ p) :
    ∀ K ∈ lowList ms ++ grading (X ^ d) :: raiseList ps, IsVertex K := by
  intro K hK
  rcases List.mem_append.mp hK with h | h
  · exact isVertex_lowList hms K h
  · rcases List.mem_cons.mp h with rfl | h
    · exact IsVertex.grade d hd
    · exact isVertex_raiseList hps K h

theorem stepBdd_windList {d : ℕ} (hd : 1 ≤ d) {ms ps : List ℕ} (hms : ∀ m ∈ ms, 1 ≤ m)
    (hps : ∀ p ∈ ps, 1 ≤ p) :
    ∀ K ∈ lowList ms ++ grading (X ^ d) :: raiseList ps, StepBdd K :=
  fun K hK => (isVertex_windList hd hms hps K hK).stepBdd

/-! ### Moving a lowering factor leftwards through the raising factors -/

/-- The commutation relation at the arguments used here: `q^p q^m = q^{p+m}` has positive order as
soon as one of the exponents is positive. -/
theorem cscale_kmul_gammaPlus_gammaMinus (p m : ℕ) (h : 1 ≤ p + m) :
    cscale (1 - X ^ (p + m)) (kmul (gammaPlus (X ^ p)) (gammaMinus (X ^ m)))
      = kmul (gammaMinus (X ^ m)) (gammaPlus (X ^ p)) := by
  have hcc : constantCoeff ((X : ℤ⟦X⟧) ^ p * X ^ m) = 0 := by
    rw [← pow_add, map_pow, constantCoeff_X]
    exact zero_pow (by omega)
  funext mu nu
  rw [cscale_apply, pow_add]
  exact one_sub_mul_gammaPlus_kmul_gammaMinus hcc mu nu

/-- **A lowering factor moves leftwards through the raising factors**, at the cost of one factor
`1 - q^{p+m}` per interchange. Stated with the lowering factor at the tail of the list, which is
where the rotation of the trace puts it. -/
theorem cscale_klist_raiseList_snoc {m : ℕ} (hm : 1 ≤ m) {ps : List ℕ} (hps : ∀ p ∈ ps, 1 ≤ p) :
    cscale ((ps.map fun p => (1 - X ^ (p + m) : ℤ⟦X⟧)).prod)
        (klist (raiseList ps ++ [gammaMinus (X ^ m)]))
      = klist (gammaMinus (X ^ m) :: raiseList ps) := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    have hp : 1 ≤ p := hps p List.mem_cons_self
    have hps' : ∀ p' ∈ ps, 1 ≤ p' := fun p' hp' => hps p' (List.mem_cons_of_mem _ hp')
    have hRs : StepBdd (klist (raiseList ps)) := StepBdd.klist (stepBdd_raiseList hps')
    have hsnoc : StepBdd (klist (raiseList ps ++ [gammaMinus (X ^ m)])) :=
      StepBdd.klist fun K hK => by
        rcases List.mem_append.mp hK with h | h
        · exact stepBdd_raiseList hps' K h
        · rw [List.mem_singleton.mp h]; exact StepBdd.gammaMinus hm
    rw [raiseList_cons, List.cons_append, klist_cons, List.map_cons, List.prod_cons,
      ← cscale_cscale, ← cscale_kmul_right (StepBdd.gammaPlus hp) hsnoc, ih hps', klist_cons,
      ← kmul_assoc (StepBdd.gammaPlus hp) (StepBdd.gammaMinus hm) hRs,
      ← cscale_kmul_left (StepBdd.kmul (StepBdd.gammaPlus hp) (StepBdd.gammaMinus hm)) hRs,
      cscale_kmul_gammaPlus_gammaMinus p m (by omega),
      kmul_assoc (StepBdd.gammaMinus hm) (StepBdd.gammaPlus hp) hRs, ← klist_cons, ← klist_cons]

/-! ### Moving a lowering factor leftwards across the grading -/

/-- **A lowering factor moves leftwards across the grading**, its argument rising by `q^d`. -/
theorem kmul_grading_gammaMinus_cons {d m : ℕ} (hd : 1 ≤ d) (hm : 1 ≤ m) {B : Kernel}
    (hB : StepBdd B) :
    kmul (grading (X ^ d)) (kmul (gammaMinus (X ^ m)) B)
      = kmul (gammaMinus (X ^ (d + m))) (kmul (grading (X ^ d)) B) := by
  rw [← kmul_assoc (StepBdd.grading _) (StepBdd.gammaMinus hm) hB, grading_kmul_gammaMinus,
    kmul_assoc (StepBdd.gammaMinus (by omega : 1 ≤ d + m)) (StepBdd.grading _) hB]

/-! ### Moving a lowering factor to the head of the product -/

/-- **The lowering factors commute past one another**, so any one of them may be brought to the
head of the product. -/
theorem klist_lowList_toFront {n : ℕ} (hn : 1 ≤ n) {ms : List ℕ} (hms : ∀ m ∈ ms, 1 ≤ m)
    {Ts : List Kernel} (hTs : ∀ K ∈ Ts, StepBdd K) :
    klist (lowList ms ++ gammaMinus (X ^ n) :: Ts)
      = klist (gammaMinus (X ^ n) :: (lowList ms ++ Ts)) := by
  induction ms with
  | nil => rw [lowList_nil, List.nil_append, List.nil_append]
  | cons m ms ih =>
    have hm : 1 ≤ m := hms m List.mem_cons_self
    have hms' : ∀ m' ∈ ms, 1 ≤ m' := fun m' hm' => hms m' (List.mem_cons_of_mem _ hm')
    have hrest : StepBdd (klist (lowList ms ++ Ts)) :=
      StepBdd.klist fun K hK => by
        rcases List.mem_append.mp hK with h | h
        · exact stepBdd_lowList hms' K h
        · exact hTs K h
    rw [lowList_cons, List.cons_append, klist_cons, ih hms', klist_cons,
      ← kmul_assoc (StepBdd.gammaMinus hm) (StepBdd.gammaMinus hn) hrest,
      gammaMinus_kmul_comm m n,
      kmul_assoc (StepBdd.gammaMinus hn) (StepBdd.gammaMinus hm) hrest, ← klist_cons,
      ← klist_cons, List.cons_append]

/-! ### The winding trace and the recursion -/

/-- The trace of the winding shape: `b` lowering factors, then the grading, then `a` raising
factors. -/
noncomputable def windTrace (d : ℕ) (ms ps : List ℕ) : ℤ⟦X⟧ :=
  ktrace (klist (lowList ms ++ grading (X ^ d) :: raiseList ps))

/-- The winding shape has a trace: its factors are vertex operators and one of them is a
grading. -/
theorem traceSummable_windList {d : ℕ} (hd : 1 ≤ d) {ms ps : List ℕ} (hms : ∀ m ∈ ms, 1 ≤ m)
    (hps : ∀ p ∈ ps, 1 ≤ p) :
    TraceSummable (klist (lowList ms ++ grading (X ^ d) :: raiseList ps)) :=
  traceSummable_klist (isVertex_windList hd hms hps) hd
    (List.mem_append_right _ List.mem_cons_self)

/-- The winding shape read with one lowering factor at the head. -/
theorem windTrace_eq_head {d n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) {ms ps : List ℕ}
    (hms : ∀ m ∈ ms, 1 ≤ m) (hps : ∀ p ∈ ps, 1 ≤ p) {ns : List ℕ} (hns : ∀ m ∈ ns, 1 ≤ m) :
    windTrace d (ns ++ n :: ms) ps
      = ktrace (klist (gammaMinus (X ^ n) ::
          (lowList (ns ++ ms) ++ grading (X ^ d) :: raiseList ps))) := by
  rw [windTrace, lowList_append, lowList_cons, List.append_assoc, List.cons_append,
    klist_lowList_toFront hn hns (stepBdd_windList hd hms hps), lowList_append,
    List.append_assoc]

/-- **The winding recursion, one factor at a time.** Raising the argument of one lowering factor by
`q^d` costs the factors `1 - q^{p+m}` over the raising exponents `p`. -/
theorem prod_mul_windTrace_step {d m : ℕ} (hd : 1 ≤ d) (hm : 1 ≤ m) {ns ms ps : List ℕ}
    (hns : ∀ m' ∈ ns, 1 ≤ m') (hms : ∀ m' ∈ ms, 1 ≤ m') (hps : ∀ p ∈ ps, 1 ≤ p) :
    (ps.map fun p => (1 - X ^ (p + m) : ℤ⟦X⟧)).prod * windTrace d (ns ++ m :: ms) ps
      = windTrace d (ns ++ (d + m) :: ms) ps := by
  have hnm : ∀ m' ∈ ns ++ ms, 1 ≤ m' := fun m' hm' => by
    rcases List.mem_append.mp hm' with h | h
    · exact hns m' h
    · exact hms m' h
  have hV : ∀ K ∈ lowList (ns ++ ms) ++ grading (X ^ d) :: raiseList ps, StepBdd K :=
    stepBdd_windList hd hnm hps
  have hW : StepBdd (klist (lowList (ns ++ ms) ++ grading (X ^ d) :: raiseList ps)) :=
    StepBdd.klist hV
  have hRs : StepBdd (klist (raiseList ps)) := StepBdd.klist (stepBdd_raiseList hps)
  have hLs : StepBdd (klist (lowList (ns ++ ms))) := StepBdd.klist (stepBdd_lowList hnm)
  have hsnoc : StepBdd (klist (raiseList ps ++ [gammaMinus (X ^ m)])) :=
    StepBdd.klist fun K hK => by
      rcases List.mem_append.mp hK with h | h
      · exact stepBdd_raiseList hps K h
      · rw [List.mem_singleton.mp h]; exact StepBdd.gammaMinus hm
  -- the rotated product, with the lowering factor at the tail
  have hrot : ktrace (klist (gammaMinus (X ^ m) ::
        (lowList (ns ++ ms) ++ grading (X ^ d) :: raiseList ps)))
      = ktrace (klist ((lowList (ns ++ ms) ++ grading (X ^ d) :: raiseList ps) ++
          [gammaMinus (X ^ m)])) :=
    ktrace_klist_rotate (StepBdd.gammaMinus hm) hV
      ⟨grading (X ^ d), List.mem_append_right _ List.mem_cons_self, GradeBdd.grading hd⟩
  -- the rotated product, cut open at the grading
  have hcut : klist ((lowList (ns ++ ms) ++ grading (X ^ d) :: raiseList ps) ++
        [gammaMinus (X ^ m)])
      = kmul (klist (lowList (ns ++ ms)))
          (kmul (grading (X ^ d)) (klist (raiseList ps ++ [gammaMinus (X ^ m)]))) := by
    rw [List.append_assoc, List.cons_append,
      klist_append (stepBdd_lowList hnm) (fun K hK => by
        rcases List.mem_cons.mp hK with rfl | h
        · exact StepBdd.grading _
        · rcases List.mem_append.mp h with h' | h'
          · exact stepBdd_raiseList hps K h'
          · rw [List.mem_singleton.mp h']; exact StepBdd.gammaMinus hm),
      klist_cons]
  have hjoin : kmul (klist (lowList (ns ++ ms)))
        (kmul (gammaMinus (X ^ (d + m))) (kmul (grading (X ^ d)) (klist (raiseList ps))))
      = klist (gammaMinus (X ^ (d + m)) ::
          (lowList (ns ++ ms) ++ grading (X ^ d) :: raiseList ps)) := by
    rw [← klist_cons, ← klist_cons, ← klist_append (stepBdd_lowList hnm) (fun K hK => by
        rcases List.mem_cons.mp hK with rfl | h
        · exact StepBdd.gammaMinus (by omega : 1 ≤ d + m)
        · rcases List.mem_cons.mp h with rfl | h'
          · exact StepBdd.grading _
          · exact stepBdd_raiseList hps K h'),
      klist_lowList_toFront (by omega : 1 ≤ d + m) hnm (fun K hK => by
        rcases List.mem_cons.mp hK with rfl | h
        · exact StepBdd.grading _
        · exact stepBdd_raiseList hps K h)]
  rw [windTrace_eq_head hd hm hms hps hns, windTrace_eq_head hd (by omega : 1 ≤ d + m) hms hps hns,
    hrot, ← ktrace_cscale _ (traceSummable_klist (fun K hK => by
      rcases List.mem_append.mp hK with h | h
      · exact isVertex_windList hd hnm hps K h
      · rw [List.mem_singleton.mp h]; exact IsVertex.minus m hm) hd
      (List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self))),
    hcut, ← cscale_kmul_right hLs (StepBdd.kmul (StepBdd.grading _) hsnoc),
    ← cscale_kmul_right (StepBdd.grading _) hsnoc, cscale_klist_raiseList_snoc hm hps, klist_cons,
    kmul_grading_gammaMinus_cons hd hm hRs, hjoin]

/-- **The winding recursion.** Raising every lowering argument by `q^d` costs the factors
`1 - q^{p+m}` over all pairs of a raising exponent `p` and a lowering exponent `m`. This is the
recursion `F(y) ∏_{i,j}(1 - x_iy_j) = F(q^d y)`, stated with an explicit already-shifted prefix
`ns` so that the induction can process the lowering exponents one at a time. -/
theorem prod_mul_windTrace {d : ℕ} (hd : 1 ≤ d) {ns ms ps : List ℕ}
    (hns : ∀ m ∈ ns, 1 ≤ m) (hms : ∀ m ∈ ms, 1 ≤ m) (hps : ∀ p ∈ ps, 1 ≤ p) :
    (ms.map fun m => (ps.map fun p => (1 - X ^ (p + m) : ℤ⟦X⟧)).prod).prod
        * windTrace d (ns ++ ms) ps
      = windTrace d (ns ++ ms.map (d + ·)) ps := by
  induction ms generalizing ns with
  | nil => simp
  | cons m ms ih =>
    have hm : 1 ≤ m := hms m List.mem_cons_self
    have hms' : ∀ m' ∈ ms, 1 ≤ m' := fun m' hm' => hms m' (List.mem_cons_of_mem _ hm')
    have hns' : ∀ m' ∈ ns ++ [d + m], 1 ≤ m' := fun m' hm' => by
      rcases List.mem_append.mp hm' with h | h
      · exact hns m' h
      · rw [List.mem_singleton.mp h]; omega
    have hsplit : ns ++ (d + m) :: ms = (ns ++ [d + m]) ++ ms := by
      rw [List.append_assoc, List.singleton_append]
    have hsplit' : ns ++ (d + m) :: ms.map (d + ·) = (ns ++ [d + m]) ++ ms.map (d + ·) := by
      rw [List.append_assoc, List.singleton_append]
    have key : ∀ A B C : ℤ⟦X⟧, A * B * C = B * (A * C) := fun A B C => by ring
    rw [List.map_cons, List.prod_cons, List.map_cons, key,
      prod_mul_windTrace_step hd hm hns hms' hps, hsplit, ih hns' hms', hsplit']

end HJO.CylindricProduct
