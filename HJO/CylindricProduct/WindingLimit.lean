/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import QSeriesLib.NumberTheory.QTheory.Basic
public import HJO.CylindricProduct.TraceRaising
public import HJO.CylindricProduct.Winding
public meta import HJO.Attr

/-! # The winding trace evaluated: passing to the limit

`HJO.CylindricProduct.Winding` proves the recursion `F(y) ∏_{i,j}(1 - x_iy_j) = F(q^{d}y)` in the
inverse-free form `prod_mul_windTrace`, and `HJO.CylindricProduct.TraceRaising` evaluates the trace
with the lowering factors trivial. This file closes the gap between them: iterate the recursion and
use that the arguments are positive powers of `q`, so that `q^{dk}y → 0` coefficientwise. The
outcome is the winding identity itself, written without inverses:

`(q^{d}; q^{d})_∞ ∏_{i,j}(q^{p_i+m_j}; q^{d})_∞ Tr(Γ_-(q^{m_1})⋯Q(q^{d})⋯Γ_+(q^{p_a})) = 1`,

the infinite product `∏_{k ≥ 0}(1 - q^{dk}x_iy_j)` being exactly `(q^{p_i+m_j}; q^{d})_∞` at
`x_i = q^{p_i}` and `y_j = q^{m_j}`.

There is no limit of a sequence of power series here, and there need not be: `ℤ⟦X⟧` carries the
coefficientwise topology, so an identity holds as soon as it holds modulo `q^{n}` for every `n`,
and each `n` is settled by a *finite* number of steps of the recursion. Fix `n` and iterate the
recursion `n` times. Three congruences modulo `q^{n}` then meet:

* the accumulated prefactor of the `n` steps is the partial product `(q^{p+m}; q^{d})_n` for each
  pair of exponents, and a `q`-Pochhammer symbol agrees with its `n`-th partial product to the
  order of the first factor it omits (`X_pow_dvd_qPochhammerInf_sub_qPochhammer`, the
  generalisation of `X_pow_dvd_selfQPochhammerInf_sub_prod` to an arbitrary first exponent);
* the lowering arguments have been raised to `q^{dn+m}`, and a lowering factor whose argument is
  divisible by `q^{n}` is the identity modulo `q^{n}`: `Γ_-(q^{m}) = 1 + E` with `q^{m} ∣ E`,
  because a horizontal strip `λ/ν` with `λ ≠ ν` has `|ν| < |λ|` and the entry there carries at
  least one factor `q^{m}`;
* what is left when the lowering factors are dropped is the raising trace, and
  `selfQPochhammerInf_mul_ktrace_raising` says it is `(q^{d}; q^{d})_∞^{-1}`.

The assembly is the same shape as the final argument of `selfQPochhammerInf_mul_partGF`: a
divisibility in every degree, then `PowerSeries.ext`.
-/

@[expose] public section

open Finset Filter PowerSeries
open scoped QTheory Topology PowerSeries.DiscreteTopology

namespace HJO.CylindricProduct

/-! ### A lowering factor is the identity to the order of its argument -/

/-- **`Γ_-(q^{m})` is the identity kernel modulo `q^{m}`.** On the diagonal both are `1`; off it a
horizontal strip `λ/ν` with `λ ≠ ν` has `|ν| < |λ|`, so the entry `q^{m(|λ|-|ν|)}` carries at least
one factor `q^{m}`, and where there is no strip both entries vanish. -/
theorem X_pow_dvd_gammaMinus_sub_kone (m : ℕ) (lam nu : Part) :
    (X : ℤ⟦X⟧) ^ m ∣ gammaMinus (X ^ m) lam nu - kone lam nu := by
  by_cases h : IsHStrip lam nu
  · by_cases he : lam = nu
    · subst he
      rw [gammaMinus_of h, Nat.sub_self, pow_zero, kone, ite_eq_left rfl, sub_self]
      exact dvd_zero _
    · have hlt : nu.size < lam.size := by
        rcases Nat.lt_or_ge nu.size lam.size with hlt | hge
        · exact hlt
        · exact absurd (h.eq_of_size_le hge).symm he
      rw [gammaMinus_of h, kone, ite_eq_right he, sub_zero, ← pow_mul]
      exact pow_dvd_pow _ (Nat.le_mul_of_pos_right m (by omega))
  · have he : lam ≠ nu := fun hh => h (by rw [hh]; exact isHStrip_self nu)
    rw [gammaMinus_of_not h, kone, ite_eq_right he, sub_self]
    exact dvd_zero _

/-- **A lowering factor at a high exponent may be deleted.** Multiplying by `Γ_-(q^{m})` changes a
step-bounded kernel only modulo `q^{n}`, as soon as `n ≤ m`: the intermediate sum against
`Γ_-(q^{m}) - 1` has every term divisible by `q^{m}`. -/
theorem X_pow_dvd_kmul_gammaMinus_sub {n m : ℕ} (hm : 1 ≤ m) (hmn : n ≤ m) {B : Kernel}
    (hB : StepBdd B) (lam nu : Part) :
    (X : ℤ⟦X⟧) ^ n ∣ kmul (gammaMinus (X ^ m)) B lam nu - B lam nu := by
  have h1 : Summable fun tau => gammaMinus (X ^ m) lam tau * B tau nu :=
    summable_kmul (StepBdd.gammaMinus hm) hB lam nu
  have h2 : Summable fun tau => kone lam tau * B tau nu :=
    summable_kmul StepBdd.kone hB lam nu
  have hone : (∑' tau, kone lam tau * B tau nu) = B lam nu :=
    congrFun (congrFun (kone_kmul B) lam) nu
  have hsub : kmul (gammaMinus (X ^ m)) B lam nu - B lam nu
      = ∑' tau, (gammaMinus (X ^ m) lam tau - kone lam tau) * B tau nu := by
    rw [← hone, kmul, ← Summable.tsum_sub h1 h2]
    exact tsum_congr fun tau => (sub_mul _ _ _).symm
  rw [hsub]
  refine X_pow_dvd_tsum ((Summable.sub h1 h2).congr fun tau => (sub_mul _ _ _).symm)
    fun tau => Dvd.dvd.mul_right ?_ _
  exact dvd_trans (pow_dvd_pow _ hmn) (X_pow_dvd_gammaMinus_sub_kone m lam tau)

/-- **A whole block of lowering factors at high exponents may be deleted.** -/
theorem X_pow_dvd_klist_lowList_sub {n : ℕ} {ns : List ℕ} (hns1 : ∀ m ∈ ns, 1 ≤ m)
    (hnsn : ∀ m ∈ ns, n ≤ m) {Ws : List Kernel} (hW : ∀ K ∈ Ws, StepBdd K) (lam nu : Part) :
    (X : ℤ⟦X⟧) ^ n ∣ klist (lowList ns ++ Ws) lam nu - klist Ws lam nu := by
  induction ns with
  | nil =>
    rw [lowList_nil, List.nil_append, sub_self]
    exact dvd_zero _
  | cons m ns ih =>
    have hm1 : 1 ≤ m := hns1 m List.mem_cons_self
    have hmn : n ≤ m := hnsn m List.mem_cons_self
    have hns1' : ∀ m' ∈ ns, 1 ≤ m' := fun m' hm' => hns1 m' (List.mem_cons_of_mem _ hm')
    have hnsn' : ∀ m' ∈ ns, n ≤ m' := fun m' hm' => hnsn m' (List.mem_cons_of_mem _ hm')
    have hB : StepBdd (klist (lowList ns ++ Ws)) := StepBdd.klist fun K hK => by
      rcases List.mem_append.mp hK with h | h
      · exact stepBdd_lowList hns1' K h
      · exact hW K h
    rw [lowList_cons, List.cons_append, klist_cons]
    have hkey : kmul (gammaMinus (X ^ m)) (klist (lowList ns ++ Ws)) lam nu - klist Ws lam nu
        = (kmul (gammaMinus (X ^ m)) (klist (lowList ns ++ Ws)) lam nu
              - klist (lowList ns ++ Ws) lam nu)
            + (klist (lowList ns ++ Ws) lam nu - klist Ws lam nu) := by ring
    rw [hkey]
    exact dvd_add (X_pow_dvd_kmul_gammaMinus_sub hm1 hmn hB lam nu) (ih hns1' hnsn')

/-- **The winding trace with all its lowering arguments high is the raising trace, to that
order.** -/
theorem X_pow_dvd_windTrace_sub {d n : ℕ} (hd : 1 ≤ d) {ns ps : List ℕ}
    (hns1 : ∀ m ∈ ns, 1 ≤ m) (hnsn : ∀ m ∈ ns, n ≤ m) (hps : ∀ p ∈ ps, 1 ≤ p) :
    (X : ℤ⟦X⟧) ^ n ∣
      windTrace d ns ps - ktrace (klist (grading (X ^ d) :: raiseList ps)) := by
  have hW : ∀ K ∈ grading (X ^ d) :: raiseList ps, StepBdd K := fun K hK => by
    rcases List.mem_cons.mp hK with rfl | h
    · exact StepBdd.grading _
    · exact stepBdd_raiseList hps K h
  have hV : ∀ K ∈ grading (X ^ d) :: raiseList ps, IsVertex K := fun K hK => by
    rcases List.mem_cons.mp hK with rfl | h
    · exact IsVertex.grade d hd
    · exact isVertex_raiseList hps K h
  have hT1 : TraceSummable (klist (lowList ns ++ grading (X ^ d) :: raiseList ps)) :=
    traceSummable_windList hd hns1 hps
  have hT2 : TraceSummable (klist (grading (X ^ d) :: raiseList ps)) :=
    traceSummable_klist hV hd List.mem_cons_self
  have hsub : windTrace d ns ps - ktrace (klist (grading (X ^ d) :: raiseList ps))
      = ∑' lam, (klist (lowList ns ++ grading (X ^ d) :: raiseList ps) lam lam
          - klist (grading (X ^ d) :: raiseList ps) lam lam) :=
    (Summable.tsum_sub hT1 hT2).symm
  rw [hsub]
  exact X_pow_dvd_tsum (Summable.sub hT1 hT2)
    fun lam => X_pow_dvd_klist_lowList_sub hns1 hnsn hW lam lam

/-! ### Iterating the winding recursion -/

/-- **The winding recursion iterated `K` times.** Each step raises every lowering argument by
`q^{d}`, so after `K` steps the argument `q^{m}` has become `q^{dK+m}`; the prefactor accumulated
over the `K` steps is the partial `q`-Pochhammer symbol `(q^{p+m}; q^{d})_K` for each pair of a
raising exponent `p` and a lowering exponent `m`. -/
theorem qPochhammer_prod_mul_windTrace {d : ℕ} (hd : 1 ≤ d) {ms ps : List ℕ}
    (hms : ∀ m ∈ ms, 1 ≤ m) (hps : ∀ p ∈ ps, 1 ≤ p) (K : ℕ) :
    (ms.map fun m => (ps.map fun p => ((X ^ (p + m); X ^ d)_K : ℤ⟦X⟧)).prod).prod
        * windTrace d ms ps
      = windTrace d (ms.map (d * K + ·)) ps := by
  induction K with
  | zero =>
    have hinner : ∀ m : ℕ, (ps.map fun p => ((X ^ (p + m); X ^ d)_0 : ℤ⟦X⟧)).prod = 1 :=
      fun m => by simp
    have houter : (ms.map fun m => (ps.map fun p => ((X ^ (p + m); X ^ d)_0 : ℤ⟦X⟧)).prod).prod
        = 1 := by
      rw [List.map_congr_left fun m _ => hinner m]
      simp
    have hid : (ms.map fun x => d * 0 + x) = ms := by
      rw [show (fun x => d * 0 + x) = id from funext fun x => by simp]
      exact List.map_id ms
    rw [houter, one_mul, hid]
  | succ K ih =>
    have hms' : ∀ m ∈ ms.map (d * K + ·), 1 ≤ m := by
      intro m hm
      obtain ⟨m', hm', rfl⟩ := List.mem_map.mp hm
      exact le_trans (hms m' hm') (Nat.le_add_left _ _)
    have hstep := prod_mul_windTrace (ns := []) hd
      (fun m hm => absurd hm (List.not_mem_nil)) hms' hps
    rw [List.nil_append, List.nil_append] at hstep
    have hQ : ((ms.map (d * K + ·)).map fun m =>
          (ps.map fun p => (1 - X ^ (p + m) : ℤ⟦X⟧)).prod).prod
        = (ms.map fun m => (ps.map fun p => (1 - X ^ (p + (d * K + m)) : ℤ⟦X⟧)).prod).prod := by
      rw [List.map_map]
      rfl
    have hfac : ∀ m p : ℕ, ((X ^ (p + m); X ^ d)_(K + 1) : ℤ⟦X⟧)
        = ((X ^ (p + m); X ^ d)_K : ℤ⟦X⟧) * (1 - X ^ (p + (d * K + m))) := by
      intro m p
      have harg : (X : ℤ⟦X⟧) ^ (p + m) * ((X : ℤ⟦X⟧) ^ d) ^ K = X ^ (p + (d * K + m)) := by
        rw [← pow_mul, ← pow_add]
        congr 1
        omega
      rw [qPochhammer_succ', harg]
    have hsplit :
        (ms.map fun m => (ps.map fun p => ((X ^ (p + m); X ^ d)_(K + 1) : ℤ⟦X⟧)).prod).prod
          = (ms.map fun m => (ps.map fun p => ((X ^ (p + m); X ^ d)_K : ℤ⟦X⟧)).prod).prod
            * (ms.map fun m =>
                (ps.map fun p => (1 - X ^ (p + (d * K + m)) : ℤ⟦X⟧)).prod).prod := by
      rw [← List.prod_map_mul]
      refine congrArg List.prod (List.map_congr_left fun m _ => ?_)
      rw [← List.prod_map_mul]
      exact congrArg List.prod (List.map_congr_left fun p _ => hfac m p)
    have hmaps : (ms.map (d * K + ·)).map (d + ·) = ms.map (d * (K + 1) + ·) := by
      rw [List.map_map]
      exact congrArg (List.map · ms) (funext fun x => by
        simp only [Function.comp_apply]
        ring)
    calc (ms.map fun m => (ps.map fun p => ((X ^ (p + m); X ^ d)_(K + 1) : ℤ⟦X⟧)).prod).prod
            * windTrace d ms ps
        = ((ms.map (d * K + ·)).map fun m =>
              (ps.map fun p => (1 - X ^ (p + m) : ℤ⟦X⟧)).prod).prod
            * ((ms.map fun m => (ps.map fun p => ((X ^ (p + m); X ^ d)_K : ℤ⟦X⟧)).prod).prod
              * windTrace d ms ps) := by
          rw [hsplit, hQ]; ring
      _ = ((ms.map (d * K + ·)).map fun m =>
              (ps.map fun p => (1 - X ^ (p + m) : ℤ⟦X⟧)).prod).prod
            * windTrace d (ms.map (d * K + ·)) ps := by rw [ih]
      _ = windTrace d ((ms.map (d * K + ·)).map (d + ·)) ps := hstep
      _ = windTrace d (ms.map (d * (K + 1) + ·)) ps := by rw [hmaps]

/-! ### The tail of a `q`-Pochhammer symbol -/

/-- **A `q`-Pochhammer symbol agrees with its `K`-th partial product to the order of the first
factor it omits.** This is `X_pow_dvd_selfQPochhammerInf_sub_prod` with the first exponent `J`
freed from the base `d`. -/
theorem X_pow_dvd_qPochhammerInf_sub_qPochhammer {J d : ℕ} (hJ : 0 < J) (hd : 0 < d) (K : ℕ) :
    (X : ℤ⟦X⟧) ^ (J + d * K) ∣ ((X ^ J; X ^ d)_∞ : ℤ⟦X⟧) - (X ^ J; X ^ d)_K := by
  have hnil : IsTopologicallyNilpotent ((X : ℤ⟦X⟧) ^ d) :=
    (PowerSeries.DiscreteTopology.isTopologicallyNilpotent_X_pow d).mpr (by omega)
  have harg : (X : ℤ⟦X⟧) ^ J * ((X : ℤ⟦X⟧) ^ d) ^ K = X ^ (J + d * K) := by
    rw [← pow_mul, ← pow_add]
  obtain ⟨c, hc⟩ := X_pow_dvd_qPochhammerInf_sub_one (J := J + d * K)
    (Nat.lt_of_lt_of_le hJ (Nat.le_add_right _ _)) hd
  have hkey : ((X ^ (J + d * K); X ^ d)_∞ : ℤ⟦X⟧) = 1 + X ^ (J + d * K) * c := by
    rw [← hc]; ring
  rw [qPochhammerInf_eq_qPochhammer_mul_qPochhammerInf (a := (X : ℤ⟦X⟧) ^ J)
    (q := (X : ℤ⟦X⟧) ^ d) K hnil, harg, hkey]
  exact ⟨((X ^ J; X ^ d)_K : ℤ⟦X⟧) * c, by ring⟩

/-- A congruence in each factor of a finite product is a congruence in the product. -/
theorem X_pow_dvd_listProd_sub {α : Type*} {n : ℕ} (l : List α) (f g : α → ℤ⟦X⟧)
    (h : ∀ a ∈ l, (X : ℤ⟦X⟧) ^ n ∣ f a - g a) :
    (X : ℤ⟦X⟧) ^ n ∣ (l.map f).prod - (l.map g).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons]
    have h1 : (X : ℤ⟦X⟧) ^ n ∣ f a - g a := h a List.mem_cons_self
    have h2 := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    have hkey : f a * (l.map f).prod - g a * (l.map g).prod
        = (f a - g a) * (l.map f).prod + g a * ((l.map f).prod - (l.map g).prod) := by ring
    rw [hkey]
    exact dvd_add (h1.mul_right _) (h2.mul_left _)

/-! ### The winding identity -/

/-- The ring identity behind the assembly: an inverse `E` of the limit `S`, a prefactor `P`
congruent to its partial product `Q`, the `K`-step recursion `Q T = W`, and `W` congruent to `S`,
together make `E P T` congruent to `1`. -/
theorem X_pow_dvd_mul_mul_sub_one {n : ℕ} {E S P Q T W : ℤ⟦X⟧} (hES : E * S = 1)
    (hPQ : (X : ℤ⟦X⟧) ^ n ∣ P - Q) (hQT : Q * T = W) (hTS : (X : ℤ⟦X⟧) ^ n ∣ W - S) :
    (X : ℤ⟦X⟧) ^ n ∣ E * P * T - 1 := by
  obtain ⟨c1, hc1⟩ := hPQ
  obtain ⟨c2, hc2⟩ := hTS
  have e1 : P = Q + X ^ n * c1 := by rw [← hc1]; ring
  have e2 : W = S + X ^ n * c2 := by rw [← hc2]; ring
  refine ⟨E * T * c1 + E * c2, ?_⟩
  calc E * P * T - 1
      = E * (Q * T) - 1 + X ^ n * (E * T * c1) := by rw [e1]; ring
    _ = E * (S + X ^ n * c2) - 1 + X ^ n * (E * T * c1) := by rw [hQT, e2]
    _ = E * S - 1 + X ^ n * (E * T * c1 + E * c2) := by ring
    _ = X ^ n * (E * T * c1 + E * c2) := by rw [hES, sub_self, zero_add]

/-- **The winding identity** at the arguments the library uses: the lowering arguments are
`y_j = q^{m_j}` and the raising arguments `x_i = q^{p_i}`, with all exponents positive. Written
without inverses, the identity

`Tr(Γ_-(y_1)⋯Γ_-(y_b) Q(q^{d}) Γ_+(x_1)⋯Γ_+(x_a))
    = (q^{d}; q^{d})_∞^{-1} ∏_{k ≥ 0} ∏_{i,j}(1 - q^{dk}x_iy_j)^{-1}`

becomes the statement below, `∏_{k ≥ 0}(1 - q^{dk}q^{p+m})` being `(q^{p+m}; q^{d})_∞`. -/
@[hjo "lem_winding"]
theorem selfQPochhammerInf_mul_prod_qPochhammerInf_mul_windTrace {d : ℕ} (hd : 1 ≤ d)
    {ms ps : List ℕ} (hms : ∀ m ∈ ms, 1 ≤ m) (hps : ∀ p ∈ ps, 1 ≤ p) :
    ((X ^ d; X ^ d)_∞ : ℤ⟦X⟧)
        * (ms.map fun m => (ps.map fun p => ((X ^ (p + m); X ^ d)_∞ : ℤ⟦X⟧)).prod).prod
        * windTrace d ms ps = 1 := by
  have hES : ((X ^ d; X ^ d)_∞ : ℤ⟦X⟧)
      * ktrace (klist (grading (X ^ d) :: raiseList ps)) = 1 := by
    rw [show raiseList ps = (ps.map fun p => (X : ℤ⟦X⟧) ^ p).map gammaPlus from by
      rw [List.map_map]; rfl]
    exact selfQPochhammerInf_mul_ktrace_raising hd _
  have hdvd : ∀ n : ℕ, (X : ℤ⟦X⟧) ^ n ∣ ((X ^ d; X ^ d)_∞ : ℤ⟦X⟧)
      * (ms.map fun m => (ps.map fun p => ((X ^ (p + m); X ^ d)_∞ : ℤ⟦X⟧)).prod).prod
      * windTrace d ms ps - 1 := by
    intro n
    have hdn : n ≤ d * n := Nat.le_mul_of_pos_left n hd
    have hPQ : (X : ℤ⟦X⟧) ^ n ∣
        (ms.map fun m => (ps.map fun p => ((X ^ (p + m); X ^ d)_∞ : ℤ⟦X⟧)).prod).prod
          - (ms.map fun m => (ps.map fun p => ((X ^ (p + m); X ^ d)_n : ℤ⟦X⟧)).prod).prod := by
      refine X_pow_dvd_listProd_sub ms _ _ fun m hm => ?_
      refine X_pow_dvd_listProd_sub ps _ _ fun p hp => ?_
      have hm1 : 1 ≤ m := hms m hm
      have hp1 : 1 ≤ p := hps p hp
      exact dvd_trans (pow_dvd_pow _ (by omega))
        (X_pow_dvd_qPochhammerInf_sub_qPochhammer (J := p + m) (by omega) hd n)
    have hTS : (X : ℤ⟦X⟧) ^ n ∣ windTrace d (ms.map (d * n + ·)) ps
        - ktrace (klist (grading (X ^ d) :: raiseList ps)) := by
      refine X_pow_dvd_windTrace_sub hd ?_ ?_ hps
      · intro m hm
        obtain ⟨m', hm', rfl⟩ := List.mem_map.mp hm
        exact le_trans (hms m' hm') (Nat.le_add_left _ _)
      · intro m hm
        obtain ⟨m', hm', rfl⟩ := List.mem_map.mp hm
        omega
    exact X_pow_dvd_mul_mul_sub_one hES hPQ
      (qPochhammer_prod_mul_windTrace hd hms hps n) hTS
  refine sub_eq_zero.mp (PowerSeries.ext fun n => ?_)
  simpa using PowerSeries.X_pow_dvd_iff.mp (hdvd (n + 1)) n (by omega)

end HJO.CylindricProduct
