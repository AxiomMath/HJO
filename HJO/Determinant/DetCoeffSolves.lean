/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Determinant.DetEquation
public import HJO.Determinant.DetLimit
public import HJO.Series.Summable
public meta import HJO.Attr

/-! # The `z^N` coefficient of the determinant series

The coefficient of `z^N` in `𝒟(-z;q)` is `q^{γ_N}` times the volume generating function of the
cylindric partitions of the balanced profile whose entries are at most `N`.

Three ingredients meet here. The Leibniz expansion of `det(I - L_H)`, whose terms are indexed by
the permutations moving every vertex along an edge of the graph, contributes the monomial
`(-1)^{#cycles} q^{w}` for such a permutation, because a permutation whose cycles all have `d`
vertices has sign `(-1)^{dN - N}`; the number of cycles is `N`, since the order of an edge
permutation divides `d` while the length of each of its cycles is a multiple of `d`. The
weight-preserving bijection of `HJO.DetCoeff` turns the resulting sum over cycle collections
into a sum over bounded cylindric partitions, the rank shift `γ_N` factoring out. Finally the
truncated determinants converge, and in each `q`-degree the two sides agree as soon as the height
bound is large enough for every collection of that weight to fit on the path.

The comparison is run in the integral model `ℚ⟦q⟧[s]` of `HJO.DetLimit`, where extracting a
`q`-coefficient is `PowerSeries.coeff`, and pushed forward to `ℚ((q))` at the end.
-/

@[expose] public section

open Finset

namespace HJO.DetCoeffSolves

open DetCoeff DetEquation DetLimit Determinant

/-! ### The order of an edge permutation -/

/-- Iterating the successor map `k` times advances the residue class by `kb`. -/
lemma succ_iterate_mem_classOf {a b : ℕ} (X : CycleSystem a b) (k : ℕ) {c : ZMod (a + b)} {v : ℕ}
    (hv : v ∈ X.classOf c) :
    X.succ^[k] v ∈ X.classOf (c + (k : ZMod (a + b)) * (b : ZMod (a + b))) := by
  induction k with
  | zero => simpa using hv
  | succ k ih =>
      have h : c + ((k + 1 : ℕ) : ZMod (a + b)) * (b : ZMod (a + b))
          = c + (k : ZMod (a + b)) * (b : ZMod (a + b)) + (b : ZMod (a + b)) := by
        push_cast
        ring
      rw [Function.iterate_succ_apply', h]
      exact X.succ_mem_classOf ih

/-- Iterating the successor map preserves the order of two vertices in one residue class. -/
lemma succ_iterate_lt {a b : ℕ} (X : CycleSystem a b) (k : ℕ) {c : ZMod (a + b)} {v w : ℕ}
    (hv : v ∈ X.classOf c) (hw : w ∈ X.classOf c) (hvw : v < w) :
    X.succ^[k] v < X.succ^[k] w := by
  induction k with
  | zero => simpa using hvw
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      have h1 := X.mem_classOf.1 (succ_iterate_mem_classOf X k hv)
      have h2 := X.mem_classOf.1 (succ_iterate_mem_classOf X k hw)
      exact X.succ_lt_succ h1.1 h2.1 (by rw [h1.2, h2.2]) ih

/-- Every cycle of the collection closes up after `d = a + b` steps: the `d`-th iterate of the
successor map is a strictly increasing self-map of each residue class, hence the identity. -/
theorem succ_iterate_eq_self {a b : ℕ} (X : CycleSystem a b) {v : ℕ} (hv : v ∈ X.occupied) :
    X.succ^[a + b] v = v := by
  have hself : (((a + b : ℕ)) : ZMod (a + b)) = 0 := ZMod.natCast_self _
  have hmem : ∀ u ∈ X.classOf ((v : ℕ) : ZMod (a + b)),
      X.succ^[a + b] u ∈ X.classOf ((v : ℕ) : ZMod (a + b)) := by
    intro u hu
    have h := succ_iterate_mem_classOf X (a + b) hu
    rwa [hself, zero_mul, add_zero] at h
  exact CycleSystem.eq_of_strictMonoOn (f := X.succ^[a + b]) (g := id) rfl hmem
    (fun u hu w hw h => succ_iterate_lt X (a + b) hu hw h) (fun u hu => hu)
    (fun _ _ _ _ h => h) (X.mem_classOf.2 ⟨hv, rfl⟩)

/-- The powers of a permutation of the vertices are the iterates of its successor map. -/
lemma permSucc_iterate {H : ℕ} (σ : Equiv.Perm (Fin (H + 1))) (k : ℕ) :
    ∀ i : Fin (H + 1), (permSucc H σ)^[k] (i : ℕ) = (((σ ^ k) i : Fin (H + 1)) : ℕ) := by
  induction k with
  | zero => intro i; simp
  | succ k ih =>
      intro i
      rw [Function.iterate_succ_apply, permSucc_val, ih (σ i), pow_succ, Equiv.Perm.mul_apply]

/-- An edge permutation has order dividing `d = a + b`: each of its cycles closes up after `d`
steps. -/
theorem pow_eq_one_of_isEdgePerm {a b H : ℕ} {σ : Equiv.Perm (Fin (H + 1))}
    (hσ : IsEdgePerm a b H σ) : σ ^ (a + b) = 1 := by
  refine Equiv.ext fun i => ?_
  by_cases hi : i ∈ σ.support
  · have hv : (i : ℕ) ∈ (cycleSystemOfPerm a b H σ hσ).occupied :=
      Finset.mem_image.2 ⟨i, hi, rfl⟩
    have h := succ_iterate_eq_self (cycleSystemOfPerm a b H σ hσ) hv
    rw [show (cycleSystemOfPerm a b H σ hσ).succ = permSucc H σ from rfl,
      permSucc_iterate σ (a + b) i] at h
    exact Fin.val_injective h
  · exact Equiv.Perm.notMem_support.1 fun h =>
      hi (Equiv.Perm.support_pow_le σ (a + b) h)

/-- Every cycle of an edge permutation is itself an edge permutation. -/
lemma isEdgePerm_of_mem_cycleFactorsFinset {a b H : ℕ} {σ c : Equiv.Perm (Fin (H + 1))}
    (hσ : IsEdgePerm a b H σ) (hc : c ∈ σ.cycleFactorsFinset) : IsEdgePerm a b H c := by
  intro i hi
  rw [(Equiv.Perm.mem_cycleFactorsFinset_iff.1 hc).2 i hi]
  exact hσ i (Equiv.Perm.mem_cycleFactorsFinset_support_le hc hi)

/-- On its own support a cycle of a permutation has the same powers as the permutation. -/
lemma pow_apply_eq_of_mem_cycleFactorsFinset {H : ℕ} {σ c : Equiv.Perm (Fin (H + 1))}
    (hc : c ∈ σ.cycleFactorsFinset) (k : ℕ) :
    ∀ x ∈ c.support, (c ^ k) x = (σ ^ k) x := by
  induction k with
  | zero => intro x _; rfl
  | succ k ih =>
      intro x hx
      have hcx : c x = σ x := (Equiv.Perm.mem_cycleFactorsFinset_iff.1 hc).2 x hx
      rw [pow_succ, Equiv.Perm.mul_apply, pow_succ, Equiv.Perm.mul_apply, hcx]
      exact ih (σ x) (by rw [← hcx]; exact Equiv.Perm.apply_mem_support.2 hx)

/-- Every cycle of an edge permutation moves exactly `d = a + b` vertices: its length is a
multiple of `d` because it is a closed walk in the graph, and divides `d` because the order of an
edge permutation does. -/
theorem card_support_of_mem_cycleFactorsFinset {a b H : ℕ} (hab : Nat.Coprime a b) (hb : 0 < b)
    {σ c : Equiv.Perm (Fin (H + 1))} (hσ : IsEdgePerm a b H σ) (hc : c ∈ σ.cycleFactorsFinset) :
    c.support.card = a + b := by
  have hcyc : c.IsCycle := (Equiv.Perm.mem_cycleFactorsFinset_iff.1 hc).1
  refine Nat.dvd_antisymm ?_ (dvd_card_support_of_isEdgePerm a b H hab hb
    (isEdgePerm_of_mem_cycleFactorsFinset hσ hc))
  obtain ⟨x, hx, -⟩ := id hcyc
  rw [← Equiv.Perm.IsCycle.orderOf hcyc]
  refine orderOf_dvd_of_pow_eq_one ((hcyc.pow_eq_one_iff' hx).2 ?_)
  rw [pow_apply_eq_of_mem_cycleFactorsFinset hc (a + b) x (Equiv.Perm.mem_support.2 hx),
    pow_eq_one_of_isEdgePerm hσ]
  rfl

/-- An edge permutation moving `dN` vertices has exactly `N` cycles, all of length `d`. -/
theorem cycleType_eq_replicate {a b H N : ℕ} (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b)
    {σ : Equiv.Perm (Fin (H + 1))} (hσ : IsEdgePerm a b H σ)
    (hcard : σ.support.card = (a + b) * N) : σ.cycleType = Multiset.replicate N (a + b) := by
  have hall : ∀ n ∈ σ.cycleType, n = a + b := by
    intro n hn
    rw [Equiv.Perm.cycleType_def, Multiset.mem_map] at hn
    obtain ⟨c, hc, rfl⟩ := hn
    exact card_support_of_mem_cycleFactorsFinset hab hb hσ hc
  have hrep : σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) (a + b) :=
    Multiset.eq_replicate_card.2 hall
  have hsum : Multiset.card σ.cycleType * (a + b) = N * (a + b) := by
    rw [mul_comm N (a + b), ← hcard, ← Equiv.Perm.sum_cycleType, hrep, Multiset.sum_replicate,
      Multiset.card_replicate, smul_eq_mul]
  have hd : 0 < a + b := by omega
  rw [hrep, Nat.eq_of_mul_eq_mul_right hd hsum]

/-- The sign of an edge permutation moving `dN` vertices is `(-1)^{dN + N}`: it is a product of
`N` cycles of length `d`. -/
theorem sign_of_isEdgePerm {a b H N : ℕ} (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b)
    {σ : Equiv.Perm (Fin (H + 1))} (hσ : IsEdgePerm a b H σ)
    (hcard : σ.support.card = (a + b) * N) :
    Equiv.Perm.sign σ = (-1) ^ ((a + b) * N + N) := by
  rw [Equiv.Perm.sign_of_cycleType, cycleType_eq_replicate hab ha hb hσ hcard,
    Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul, mul_comm N (a + b)]

/-! ### The Leibniz expansion of the integral determinant -/

/-- The `q`-exponent of a Leibniz term, with the up-edge weights read where they sit. -/
lemma edgeExp_zero (a b H : ℕ) (σ : Equiv.Perm (Fin (H + 1))) :
    edgeExp a b H 0 σ = ∑ i ∈ σ.support, if (σ i : ℕ) = (i : ℕ) + b then (i : ℕ) / a else 0 := by
  simp only [edgeExp, add_zero]

/-- The graph carries no loop, so every diagonal entry of the integral model is `1`. -/
lemma intOneSub_apply_self (a b H : ℕ) (ha : 0 < a) (hb : 0 < b) (r : Fin (H + 1)) :
    (1 - intAdjacency a b H) r r = 1 := by
  have h1 : ¬ ((r : ℕ) = (r : ℕ) + b) := by omega
  have h2 : ¬ ((r : ℕ) = (r : ℕ) + a) := by omega
  rw [Matrix.sub_apply, Matrix.one_apply_eq, intAdjacency, Matrix.of_apply, ite_eq_right h1,
    ite_eq_right h2, sub_zero]

/-- Off the diagonal the integral model carries the negated edge weight. -/
lemma intOneSub_apply_of_ne (a b H : ℕ) {r c : Fin (H + 1)} (h : r ≠ c) :
    (1 - intAdjacency a b H) r c
      = -(if (c : ℕ) = (r : ℕ) + b then
            Polynomial.C (PowerSeries.X ^ ((r : ℕ) / a)) * Polynomial.X
          else if (r : ℕ) = (c : ℕ) + a then Polynomial.X else 0) := by
  rw [Matrix.sub_apply, Matrix.one_apply_ne h, intAdjacency, Matrix.of_apply, zero_sub]

/-- The Leibniz term of an edge permutation in the integral model is a monomial: its `s`-degree is
the number of vertices moved and its `q`-exponent is `edgeExp`. -/
theorem prod_intOneSub (a b H : ℕ) (ha : 0 < a) (hb : 0 < b) {σ : Equiv.Perm (Fin (H + 1))}
    (hσ : IsEdgePerm a b H σ) :
    ∏ i, (1 - intAdjacency a b H) i (σ i)
      = Polynomial.C ((-1) ^ σ.support.card * PowerSeries.X ^ edgeExp a b H 0 σ) *
          Polynomial.X ^ σ.support.card := by
  have hsub : ∏ i ∈ σ.support, (1 - intAdjacency a b H) i (σ i)
      = ∏ i, (1 - intAdjacency a b H) i (σ i) := by
    refine Finset.prod_subset (Finset.subset_univ _) fun i _ hi => ?_
    rw [not_not.1 (Equiv.Perm.mem_support.not.1 hi)]
    exact intOneSub_apply_self a b H ha hb i
  have hterm : ∀ i ∈ σ.support, (1 - intAdjacency a b H) i (σ i)
      = -(Polynomial.C
            (PowerSeries.X ^ (if (σ i : ℕ) = (i : ℕ) + b then (i : ℕ) / a else 0)) *
          Polynomial.X) := by
    intro i hi
    rw [intOneSub_apply_of_ne a b H (Equiv.Perm.mem_support.1 hi).symm]
    rcases hσ i hi with hup | hdown
    · rw [ite_eq_left hup, ite_eq_left hup]
    · have hnot : ¬ ((σ i : ℕ) = (i : ℕ) + b) := by omega
      rw [ite_eq_right hnot, ite_eq_right hnot, ite_eq_left hdown, pow_zero, map_one, one_mul]
  have hC : (∏ i ∈ σ.support, Polynomial.C
        ((PowerSeries.X : PowerSeries ℚ) ^ (if (σ i : ℕ) = (i : ℕ) + b then (i : ℕ) / a else 0)))
      = Polynomial.C ((PowerSeries.X : PowerSeries ℚ) ^ edgeExp a b H 0 σ) := by
    rw [edgeExp_zero, ← Finset.prod_pow_eq_pow_sum, map_prod]
  have hneg : ∀ (n : ℕ) (u : PowerSeries ℚ),
      Polynomial.C ((-1 : PowerSeries ℚ) ^ n * u) = (-1) ^ n * Polynomial.C u := by
    intro n u
    rw [map_mul, map_pow, map_neg, map_one]
  rw [← hsub, Finset.prod_congr rfl hterm, Finset.prod_neg, Finset.prod_mul_distrib,
    Finset.prod_const, hC, hneg]
  ring

/-- A permutation moving some vertex along a non-edge contributes nothing. -/
theorem prod_intOneSub_eq_zero (a b H : ℕ) {σ : Equiv.Perm (Fin (H + 1))}
    (hσ : ¬ IsEdgePerm a b H σ) : ∏ i, (1 - intAdjacency a b H) i (σ i) = 0 := by
  rw [IsEdgePerm] at hσ
  push Not at hσ
  obtain ⟨i, hi, hup, hdown⟩ := hσ
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  rw [intOneSub_apply_of_ne a b H (Equiv.Perm.mem_support.1 hi).symm, ite_eq_right hup,
    ite_eq_right hdown, neg_zero]

/-- The Leibniz expansion of a determinant over `ℚ⟦q⟧[s]`, with the permutation acting on the
columns. -/
theorem det_eq_sum_perm {n : ℕ} (M : Matrix (Fin n) (Fin n) (Polynomial (PowerSeries ℚ))) :
    M.det = ∑ σ : Equiv.Perm (Fin n),
      Polynomial.C ((Equiv.Perm.sign σ : ℤ) : PowerSeries ℚ) * ∏ i, M i (σ i) := by
  rw [← Matrix.det_transpose M, Matrix.det_apply']
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Polynomial.C_eq_intCast]
  simp only [Matrix.transpose_apply]

/-- Moving every vertex along an edge of the graph is decidable: it is a bounded quantification
over the support. -/
instance decidableIsEdgePerm (a b H : ℕ) (σ : Equiv.Perm (Fin (H + 1))) :
    Decidable (IsEdgePerm a b H σ) :=
  decidable_of_iff (∀ i ∈ σ.support, ((σ i : ℕ) = (i : ℕ) + b) ∨ ((i : ℕ) = (σ i : ℕ) + a)) Iff.rfl

/-- The permutations of the vertices `0, …, H` that move every vertex along an edge of the graph
and move `dN` of them in all: the collections of `N` vertex-disjoint cycles on the path. -/
def edgePerms (a b H N : ℕ) : Finset (Equiv.Perm (Fin (H + 1))) :=
  {σ ∈ univ | IsEdgePerm a b H σ ∧ σ.support.card = (a + b) * N}

/-- Membership in the set of edge permutations of `N` cycles. -/
lemma mem_edgePerms {a b H N : ℕ} {σ : Equiv.Perm (Fin (H + 1))} :
    σ ∈ edgePerms a b H N ↔ IsEdgePerm a b H σ ∧ σ.support.card = (a + b) * N := by
  simp [edgePerms]

/-- The `s^{dN}`-coefficient of `det(I - L_H)` in the integral model: the sign of a collection of
`N` cycles is `(-1)^N`, the `(-1)^{dN}` of the Leibniz term cancelling all but `N` of the `dN`
transpositions. -/
theorem coeff_intDet (a b H N : ℕ) (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b) :
    (intDet a b H).coeff ((a + b) * N)
      = (-1) ^ N * ∑ σ ∈ edgePerms a b H N, PowerSeries.X ^ edgeExp a b H 0 σ := by
  have hsq : ((-1 : PowerSeries ℚ)) ^ ((a + b) * N) * (-1) ^ ((a + b) * N) = 1 := by
    rw [← pow_add, ← two_mul]
    exact Even.neg_one_pow ⟨(a + b) * N, by ring⟩
  have hterm : ∀ σ ∈ edgePerms a b H N,
      (Polynomial.C ((Equiv.Perm.sign σ : ℤ) : PowerSeries ℚ) *
          ∏ i, (1 - intAdjacency a b H) i (σ i)).coeff ((a + b) * N)
        = (-1) ^ N * PowerSeries.X ^ edgeExp a b H 0 σ := by
    intro σ hσ
    obtain ⟨hedge, hcard⟩ := mem_edgePerms.1 hσ
    have hsign : ((Equiv.Perm.sign σ : ℤ) : PowerSeries ℚ) = (-1) ^ ((a + b) * N + N) := by
      rw [sign_of_isEdgePerm hab ha hb hedge hcard]
      push_cast
      ring
    have hcollect : ∀ u : PowerSeries ℚ, (-1 : PowerSeries ℚ) ^ ((a + b) * N) * (-1) ^ N *
        ((-1) ^ ((a + b) * N) * u) = (-1) ^ N * u := by
      intro u
      rw [show (-1 : PowerSeries ℚ) ^ ((a + b) * N) * (-1) ^ N * ((-1) ^ ((a + b) * N) * u)
        = ((-1) ^ ((a + b) * N) * (-1) ^ ((a + b) * N)) * ((-1) ^ N * u) from by ring, hsq, one_mul]
    rw [prod_intOneSub a b H ha hb hedge, hsign, ← mul_assoc, ← map_mul, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, hcard, ite_eq_left rfl, mul_one, pow_add, hcollect]
  have hzero : ∀ σ ∈ (univ : Finset (Equiv.Perm (Fin (H + 1)))), σ ∉ edgePerms a b H N →
      (Polynomial.C ((Equiv.Perm.sign σ : ℤ) : PowerSeries ℚ) *
        ∏ i, (1 - intAdjacency a b H) i (σ i)).coeff ((a + b) * N) = 0 := by
    intro σ _ hσ
    rw [Polynomial.coeff_C_mul]
    by_cases hedge : IsEdgePerm a b H σ
    · have hne : ¬ ((a + b) * N = σ.support.card) := fun h =>
        hσ (mem_edgePerms.2 ⟨hedge, h.symm⟩)
      rw [prod_intOneSub a b H ha hb hedge, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        ite_eq_right hne, mul_zero, mul_zero]
    · rw [prod_intOneSub_eq_zero a b H hedge, Polynomial.coeff_zero, mul_zero]
  rw [intDet, det_eq_sum_perm, Polynomial.finsetSum_coeff,
    ← Finset.sum_subset (Finset.subset_univ (edgePerms a b H N)) hzero,
    Finset.sum_congr rfl hterm, Finset.mul_sum]

/-! ### Cycle collections and permutations of the path -/

/-- The `q`-exponent of the Leibniz term of an edge permutation is the weight of the collection of
cycles it traces out. -/
theorem weightExp_cycleSystemOfPerm (a b H : ℕ) {σ : Equiv.Perm (Fin (H + 1))}
    (hσ : IsEdgePerm a b H σ) :
    (cycleSystemOfPerm a b H σ hσ).weightExp = edgeExp a b H 0 σ := by
  rw [CycleSystem.weightExp,
    show (cycleSystemOfPerm a b H σ hσ).occupied = σ.support.image Fin.val from rfl,
    Finset.sum_image fun x _ y _ h => Fin.val_injective h, edgeExp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (cycleSystemOfPerm a b H σ hσ).succ = permSucc H σ from rfl, permSucc_val, add_zero]

/-- Each residue class of the collection traced out by an edge permutation moving `dN` vertices
carries `N` occupied vertices. -/
theorem card_classOf_cycleSystemOfPerm (a b H N : ℕ) (hab : Nat.Coprime a b) (hb : 0 < b)
    {σ : Equiv.Perm (Fin (H + 1))} (hσ : IsEdgePerm a b H σ)
    (hcard : σ.support.card = (a + b) * N) (c : ZMod (a + b)) :
    ((cycleSystemOfPerm a b H σ hσ).classOf c).card = N := by
  have hd : 0 < a + b := by omega
  have hocc : (cycleSystemOfPerm a b H σ hσ).occupied.card = (a + b) * N := by
    rw [show (cycleSystemOfPerm a b H σ hσ).occupied = σ.support.image Fin.val from rfl,
      Finset.card_image_of_injective _ Fin.val_injective, hcard]
  have h := (cycleSystemOfPerm a b H σ hσ).card_occupied hab hb
  rw [hocc] at h
  rw [CycleSystem.card_classOf_eq_card_zero _ hab hb c, ← Nat.eq_of_mul_eq_mul_left hd h]

/-- The diagonal reading of a collection depends only on its occupied set. -/
theorem cylOf_congr {a b : ℕ} [NeZero (a + b)] {X Y : CycleSystem a b} {N : ℕ}
    (hN : ∀ c : ZMod (a + b), (X.classOf c).card = N)
    (hM : ∀ c : ZMod (a + b), (Y.classOf c).card = N) (h : X.occupied = Y.occupied) :
    X.cylOf hN = Y.cylOf hM := by
  have hcls : ∀ c : ZMod (a + b), X.classOf c = Y.classOf c := by
    intro c
    simp only [CycleSystem.classOf, h]
  have hemb : ∀ c : ZMod (a + b), ⇑((X.classOf c).orderEmbOfFin (hN c))
      = ⇑((Y.classOf c).orderEmbOfFin (hM c)) := by
    intro c
    refine Finset.orderEmbOfFin_unique (hM c) (fun i => ?_)
      ((X.classOf c).orderEmbOfFin (hN c)).strictMono
    rw [← hcls c]
    exact Finset.orderEmbOfFin_mem _ _ i
  have hlev : ∀ c : ZMod (a + b), X.levels c (hN c) = Y.levels c (hM c) := by
    intro c
    funext i
    simp only [CycleSystem.levels, hemb c]
  have hdv : X.diagValue hN = Y.diagValue hM := by
    funext w
    rw [X.diagValue_eq hN rfl rfl, Y.diagValue_eq hM rfl rfl, hlev]
  rw [X.cylOf_eq hN, Y.cylOf_eq hM, hdv]

/-- Every occupied vertex of a collection lies below `d` times one more than its weight. -/
theorem lt_of_mem_occupied {a b : ℕ} (X : CycleSystem a b) (ha : 0 < a) (hb : 0 < b) {v : ℕ}
    (hv : v ∈ X.occupied) : v < (a + b) * (X.weightExp + 1) := by
  have hd : 0 < a + b := by omega
  have hle : v / (a + b) ≤ X.weightExp := by
    rw [X.weightExp_eq_sum_div ha hb]
    exact Finset.single_le_sum (f := fun v => v / (a + b)) (fun _ _ => Nat.zero_le _) hv
  have hstep : (a + b) * (v / (a + b) + 1) ≤ (a + b) * (X.weightExp + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have hlt : v < (a + b) * (v / (a + b) + 1) := by
    rw [Nat.mul_succ]
    have h1 := Nat.div_add_mod v (a + b)
    have h2 : v % (a + b) < a + b := Nat.mod_lt _ hd
    omega
  omega

/-- The map on the vertices `0, …, H` given by the successor map of a collection of
vertex-disjoint cycles that fits on the path, extended by the identity off the occupied set. -/
def permFun {a b : ℕ} (H : ℕ) (X : CycleSystem a b) (hle : ∀ v ∈ X.occupied, v < H + 1)
    (i : Fin (H + 1)) : Fin (H + 1) :=
  if h : (i : ℕ) ∈ X.occupied then ⟨X.succ (i : ℕ), hle _ (X.succ_mem _ h)⟩ else i

/-- On an occupied vertex the map is the successor map. -/
lemma permFun_of_mem {a b : ℕ} (H : ℕ) (X : CycleSystem a b) (hle : ∀ v ∈ X.occupied, v < H + 1)
    {i : Fin (H + 1)} (hi : (i : ℕ) ∈ X.occupied) :
    ((permFun H X hle i : Fin (H + 1)) : ℕ) = X.succ (i : ℕ) := by
  rw [permFun, dite_eq_left hi]

/-- Off the occupied set the map is the identity. -/
lemma permFun_of_notMem {a b : ℕ} (H : ℕ) (X : CycleSystem a b)
    (hle : ∀ v ∈ X.occupied, v < H + 1) {i : Fin (H + 1)} (hi : (i : ℕ) ∉ X.occupied) :
    permFun H X hle i = i := by
  rw [permFun, dite_eq_right hi]

/-- The map is injective: the successor map is injective on the occupied set, which it preserves. -/
lemma permFun_injective {a b : ℕ} (H : ℕ) (X : CycleSystem a b)
    (hle : ∀ v ∈ X.occupied, v < H + 1) : Function.Injective (permFun H X hle) := by
  intro i j hij
  by_cases hi : (i : ℕ) ∈ X.occupied <;> by_cases hj : (j : ℕ) ∈ X.occupied
  · have h := congrArg Fin.val hij
    rw [permFun_of_mem H X hle hi, permFun_of_mem H X hle hj] at h
    exact Fin.val_injective (X.succ_inj _ hi _ hj h)
  · have h := congrArg Fin.val hij
    rw [permFun_of_mem H X hle hi, permFun_of_notMem H X hle hj] at h
    exact absurd (h ▸ X.succ_mem _ hi) hj
  · have h := congrArg Fin.val hij
    rw [permFun_of_notMem H X hle hi, permFun_of_mem H X hle hj] at h
    exact absurd (h ▸ X.succ_mem _ hj) hi
  · rwa [permFun_of_notMem H X hle hi, permFun_of_notMem H X hle hj] at hij

/-- The permutation of the vertices `0, …, H` traced out by a collection of vertex-disjoint cycles
that fits on the path: an injective self-map of a finite set is a permutation. -/
noncomputable def permOfCycleSystem {a b : ℕ} (H : ℕ) (X : CycleSystem a b)
    (hle : ∀ v ∈ X.occupied, v < H + 1) : Equiv.Perm (Fin (H + 1)) :=
  Equiv.ofBijective (permFun H X hle) (Finite.injective_iff_bijective.1 (permFun_injective H X hle))

/-- The permutation traced out by a collection acts as the successor map on an occupied vertex. -/
theorem permOfCycleSystem_apply {a b : ℕ} (H : ℕ) (X : CycleSystem a b)
    (hle : ∀ v ∈ X.occupied, v < H + 1) {i : Fin (H + 1)} (hi : (i : ℕ) ∈ X.occupied) :
    ((permOfCycleSystem H X hle i : Fin (H + 1)) : ℕ) = X.succ (i : ℕ) :=
  permFun_of_mem H X hle hi

/-- Off the occupied set the permutation traced out by a collection is the identity. -/
theorem permOfCycleSystem_apply_of_notMem {a b : ℕ} (H : ℕ) (X : CycleSystem a b)
    (hle : ∀ v ∈ X.occupied, v < H + 1) {i : Fin (H + 1)} (hi : (i : ℕ) ∉ X.occupied) :
    permOfCycleSystem H X hle i = i :=
  permFun_of_notMem H X hle hi

/-- The support of the permutation traced out by a collection is its occupied set. -/
theorem mem_support_permOfCycleSystem {a b : ℕ} (H : ℕ) (X : CycleSystem a b) (ha : 0 < a)
    (hb : 0 < b) (hle : ∀ v ∈ X.occupied, v < H + 1) (i : Fin (H + 1)) :
    i ∈ (permOfCycleSystem H X hle).support ↔ (i : ℕ) ∈ X.occupied := by
  rw [Equiv.Perm.mem_support]
  constructor
  · intro h
    by_contra hi
    exact h (permOfCycleSystem_apply_of_notMem H X hle hi)
  · intro hi h
    have hval : X.succ (i : ℕ) = (i : ℕ) := by
      rw [← permOfCycleSystem_apply H X hle hi, h]
    rcases X.step _ hi with hup | ⟨hav, hdown⟩ <;> omega

/-- The occupied set of the collection traced out by the permutation of a collection is the
collection's own occupied set. -/
theorem occupied_cycleSystemOfPerm_permOfCycleSystem {a b : ℕ} (H : ℕ) (X : CycleSystem a b)
    (ha : 0 < a) (hb : 0 < b) (hle : ∀ v ∈ X.occupied, v < H + 1) :
    (permOfCycleSystem H X hle).support.image Fin.val = X.occupied := by
  ext v
  rw [Finset.mem_image]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact (mem_support_permOfCycleSystem H X ha hb hle i).1 hi
  · intro hv
    exact ⟨⟨v, hle v hv⟩, (mem_support_permOfCycleSystem H X ha hb hle _).2 hv, rfl⟩

/-- The permutation traced out by a collection moves every vertex along an edge of the graph. -/
theorem isEdgePerm_permOfCycleSystem {a b : ℕ} (H : ℕ) (X : CycleSystem a b) (ha : 0 < a)
    (hb : 0 < b) (hle : ∀ v ∈ X.occupied, v < H + 1) :
    IsEdgePerm a b H (permOfCycleSystem H X hle) := by
  intro i hi
  have hocc := (mem_support_permOfCycleSystem H X ha hb hle i).1 hi
  rw [permOfCycleSystem_apply H X hle hocc]
  rcases X.step _ hocc with hup | ⟨hav, hdown⟩
  · exact Or.inl hup
  · exact Or.inr (by omega)

/-! ### The bijection with the bounded cylindric partitions -/

/-- The cylindric partitions of the balanced profile whose entries are at most `N`. -/
abbrev BddCyl (a b N : ℕ) : Type :=
  {l : ℕ → ℕ → ℕ //
    HJO.Cylindric.IsCylindric a (HJO.Cylindric.profile a b) l ∧ HJO.Cylindric.BoundedBy N l}

/-- The successor map of the collection traced out by an edge permutation. -/
lemma succ_cycleSystemOfPerm (a b H : ℕ) {σ : Equiv.Perm (Fin (H + 1))}
    (hσ : IsEdgePerm a b H σ) : (cycleSystemOfPerm a b H σ hσ).succ = permSucc H σ := rfl

/-- The occupied set of the collection traced out by an edge permutation. -/
lemma occupied_cycleSystemOfPerm (a b H : ℕ) {σ : Equiv.Perm (Fin (H + 1))}
    (hσ : IsEdgePerm a b H σ) :
    (cycleSystemOfPerm a b H σ hσ).occupied = σ.support.image Fin.val := rfl

/-- The edge permutations of `N` cycles whose Leibniz term carries the `q`-exponent `m`. -/
def edgePermsExp (a b H N m : ℕ) : Finset (Equiv.Perm (Fin (H + 1))) :=
  {σ ∈ edgePerms a b H N | edgeExp a b H 0 σ = m}

/-- Such a permutation moves every vertex along an edge. -/
lemma isEdgePerm_of_mem_edgePermsExp {a b H N m : ℕ} {σ : Equiv.Perm (Fin (H + 1))}
    (hσ : σ ∈ edgePermsExp a b H N m) : IsEdgePerm a b H σ :=
  (mem_edgePerms.1 (Finset.mem_filter.1 hσ).1).1

/-- Such a permutation moves `dN` vertices. -/
lemma card_support_of_mem_edgePermsExp {a b H N m : ℕ} {σ : Equiv.Perm (Fin (H + 1))}
    (hσ : σ ∈ edgePermsExp a b H N m) : σ.support.card = (a + b) * N :=
  (mem_edgePerms.1 (Finset.mem_filter.1 hσ).1).2

/-- Such a permutation has `q`-exponent `m`. -/
lemma edgeExp_of_mem_edgePermsExp {a b H N m : ℕ} {σ : Equiv.Perm (Fin (H + 1))}
    (hσ : σ ∈ edgePermsExp a b H N m) : edgeExp a b H 0 σ = m :=
  (Finset.mem_filter.1 hσ).2

/-- The diagonal reading is a bijection from the collections of `N` vertex-disjoint cycles of
weight `m` on the path `0, …, H` onto the cylindric partitions of the balanced profile with entries
at most `N` and volume `m - γ_N`, as soon as the path is long enough to carry every such
collection. -/
theorem card_edgePermsExp (a b H N m : ℕ) (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b)
    (hH : (a + b) * (m + 1) ≤ H + 1) (S : Finset (BddCyl a b N))
    (hS : ∀ l : BddCyl a b N,
      Paths.gammaShift a b N + HJO.Cylindric.cylVolume a l.val = m → l ∈ S) :
    (edgePermsExp a b H N m).card
      = #{l ∈ S | Paths.gammaShift a b N + HJO.Cylindric.cylVolume a l.val = m} := by
  have hd : 0 < a + b := by omega
  have : NeZero (a + b) := ⟨by omega⟩
  refine Finset.card_bij (fun σ hσ =>
    (⟨(cycleSystemOfPerm a b H σ (isEdgePerm_of_mem_edgePermsExp hσ)).cylOf
        (card_classOf_cycleSystemOfPerm a b H N hab hb (isEdgePerm_of_mem_edgePermsExp hσ)
          (card_support_of_mem_edgePermsExp hσ)),
      CycleSystem.isCylindric_cylOf _ ha _,
      CycleSystem.boundedBy_cylOf _ hd _⟩ : BddCyl a b N)) ?_ ?_ ?_
  · intro σ hσ
    have hedge := isEdgePerm_of_mem_edgePermsExp hσ
    have hNP := card_classOf_cycleSystemOfPerm a b H N hab hb hedge
      (card_support_of_mem_edgePermsExp hσ)
    have key : Paths.gammaShift a b N
        + HJO.Cylindric.cylVolume a ((cycleSystemOfPerm a b H σ hedge).cylOf hNP) = m := by
      rw [← CycleSystem.weightExp_eq_gammaShift_add_cylVolume _ hab ha hb hNP,
        weightExp_cycleSystemOfPerm a b H hedge, edgeExp_of_mem_edgePermsExp hσ]
    exact Finset.mem_filter.2 ⟨hS _ key, key⟩
  · intro σ₁ h₁ σ₂ h₂ heq
    obtain ⟨hocc, hsucc⟩ := CycleSystem.eq_of_cylOf_eq hab ha hb
      (cycleSystemOfPerm a b H σ₁ (isEdgePerm_of_mem_edgePermsExp h₁))
      (cycleSystemOfPerm a b H σ₂ (isEdgePerm_of_mem_edgePermsExp h₂))
      (card_classOf_cycleSystemOfPerm a b H N hab hb (isEdgePerm_of_mem_edgePermsExp h₁)
        (card_support_of_mem_edgePermsExp h₁))
      (card_classOf_cycleSystemOfPerm a b H N hab hb (isEdgePerm_of_mem_edgePermsExp h₂)
        (card_support_of_mem_edgePermsExp h₂))
      (Subtype.ext_iff.1 heq)
    rw [occupied_cycleSystemOfPerm, occupied_cycleSystemOfPerm] at hocc
    have hsupp : σ₁.support = σ₂.support := Finset.image_injective Fin.val_injective hocc
    refine Equiv.ext fun i => ?_
    by_cases hi : i ∈ σ₁.support
    · have h := hsucc (i : ℕ)
        (by rw [occupied_cycleSystemOfPerm]; exact Finset.mem_image.2 ⟨i, hi, rfl⟩)
      rw [succ_cycleSystemOfPerm, succ_cycleSystemOfPerm, permSucc_val, permSucc_val] at h
      exact Fin.val_injective h
    · rw [Equiv.Perm.notMem_support.1 hi, Equiv.Perm.notMem_support.1 (hsupp ▸ hi)]
  · intro l hl
    obtain ⟨X, hN, hcyl, hw⟩ := exists_cycleSystem_cylOf hab ha hb l.2.1 l.2.2
    have hwm : X.weightExp = m := by rw [hw, (Finset.mem_filter.1 hl).2]
    have hle : ∀ v ∈ X.occupied, v < H + 1 := by
      intro v hv
      have hlt := lt_of_mem_occupied X ha hb hv
      rw [hwm] at hlt
      omega
    have hedge : IsEdgePerm a b H (permOfCycleSystem H X hle) :=
      isEdgePerm_permOfCycleSystem H X ha hb hle
    have hoccP : (cycleSystemOfPerm a b H (permOfCycleSystem H X hle) hedge).occupied
        = X.occupied := occupied_cycleSystemOfPerm_permOfCycleSystem H X ha hb hle
    have hcard : (permOfCycleSystem H X hle).support.card = (a + b) * N := by
      rw [← Finset.card_image_of_injective (permOfCycleSystem H X hle).support Fin.val_injective,
        occupied_cycleSystemOfPerm_permOfCycleSystem H X ha hb hle, X.card_occupied hab hb, hN 0]
    have hexp : edgeExp a b H 0 (permOfCycleSystem H X hle) = m := by
      rw [← weightExp_cycleSystemOfPerm a b H hedge,
        CycleSystem.weightExp_eq_sum_div _ ha hb, hoccP, ← X.weightExp_eq_sum_div ha hb, hwm]
    refine ⟨permOfCycleSystem H X hle,
      Finset.mem_filter.2 ⟨mem_edgePerms.2 ⟨hedge, hcard⟩, hexp⟩, Subtype.ext ?_⟩
    exact (cylOf_congr (card_classOf_cycleSystemOfPerm a b H N hab hb hedge hcard) hN
      hoccP).trans hcyl

/-! ### The `q`-coefficients of the two sides -/

section BoundedGF

open scoped PowerSeries.DiscreteTopology

/-- The bounded cylindric partitions of volume below `y`, as a finite set: below a given volume
only finitely many cylinders of a fixed profile have all their entries bounded. -/
noncomputable def bddCylFinset (a b N y : ℕ) (ha : 0 < a) : Finset (BddCyl a b N) :=
  (Set.Finite.preimage Subtype.val_injective.injOn
    (Summable.finite_setOf_cylVolume_lt a N y (HJO.Cylindric.profile a b) ha)).toFinset

/-- Membership in the finite set of bounded cylindric partitions of volume below `y`. -/
lemma mem_bddCylFinset {a b N y : ℕ} (ha : 0 < a) (l : BddCyl a b N) :
    l ∈ bddCylFinset a b N y ha ↔ HJO.Cylindric.cylVolume a l.val < y := by
  rw [bddCylFinset, Set.Finite.mem_toFinset]
  exact ⟨fun h => h.2, fun h => ⟨l.2, h⟩⟩

/-- The volumes of the bounded cylindric partitions are unbounded, so their generating function is
a genuine sum. -/
lemma unbounded_cylVolume (a b N : ℕ) (ha : 0 < a) :
    Filter.Unbounded (HJO.Cylindric.cylVolume a ∘ Subtype.val
      (p := fun l => HJO.Cylindric.IsCylindric a (HJO.Cylindric.profile a b) l ∧
        HJO.Cylindric.BoundedBy N l)) :=
  Filter.Unbounded.comp_subtypeVal_iff.mpr fun y =>
    (Summable.finite_setOf_cylVolume_lt a N y (HJO.Cylindric.profile a b) ha).subset fun _ hl =>
      ⟨hl.1, not_le.mp hl.2⟩

/-- The `q^m` coefficient of the bounded cylindric series counts the cylindric partitions of
volume `m`. -/
theorem coeff_boundedGF (a b N m : ℕ) (ha : 0 < a) (S : Finset (BddCyl a b N))
    (hS : ∀ l ∉ S, m < HJO.Cylindric.cylVolume a l.val) :
    PowerSeries.coeff m (HJO.Cylindric.boundedGF a b N)
      = #{l ∈ S | HJO.Cylindric.cylVolume a l.val = m} := by
  have h := (unbounded_cylVolume a b N ha).coeff_tsum_eq_sum (fun _ => (1 : PowerSeries ℤ)) m S hS
    (q := PowerSeries.X) (by simp)
  simp only [one_mul, Function.comp_apply] at h
  rw [show HJO.Cylindric.boundedGF a b N = ∑' l : BddCyl a b N,
      (PowerSeries.X : PowerSeries ℤ) ^ HJO.Cylindric.cylVolume a l.val from rfl, h,
    Finset.sum_congr rfl fun l _ => PowerSeries.coeff_X_pow m (HJO.Cylindric.cylVolume a l.val),
    Finset.sum_boole]
  exact congrArg (fun s : Finset (BddCyl a b N) => (s.card : ℤ))
    (Finset.filter_congr fun l _ => eq_comm)

/-- The `q^m` coefficient of `q^{γ_N}` times the bounded cylindric series counts the cylindric
partitions whose volume, shifted by the rank shift, is `m`. -/
theorem coeff_gammaShift_mul_boundedGF (a b N m : ℕ) (ha : 0 < a) (S : Finset (BddCyl a b N))
    (hS : ∀ l ∉ S, m < HJO.Cylindric.cylVolume a l.val) :
    PowerSeries.coeff m ((PowerSeries.X : PowerSeries ℤ) ^ Paths.gammaShift a b N *
        HJO.Cylindric.boundedGF a b N)
      = #{l ∈ S | Paths.gammaShift a b N + HJO.Cylindric.cylVolume a l.val = m} := by
  rw [PowerSeries.coeff_X_pow_mul']
  split_ifs with hγ
  · rw [coeff_boundedGF a b N (m - Paths.gammaShift a b N) ha S fun l hl => by
      have h := hS l hl; omega]
    exact congrArg (fun s : Finset (BddCyl a b N) => (s.card : ℤ))
      (Finset.filter_congr fun l _ => by omega)
  · symm
    rw [Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    exact fun l _ => by omega

end BoundedGF

/-- The `q^m` coefficient of the `s^{dN}` coefficient of `det(I - L_H)` counts, with the sign
`(-1)^N`, the collections of `N` vertex-disjoint cycles of weight `m` on the path `0, …, H`. -/
theorem coeff_coeff_intDet (a b H N m : ℕ) (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b) :
    PowerSeries.coeff m ((intDet a b H).coeff ((a + b) * N))
      = (-1) ^ N * ((edgePermsExp a b H N m).card : ℚ) := by
  have hC : ((-1 : PowerSeries ℚ)) ^ N = PowerSeries.C ((-1 : ℚ) ^ N) := by
    rw [map_pow, map_neg, map_one]
  have hsum : ∑ σ ∈ edgePerms a b H N,
      PowerSeries.coeff m ((PowerSeries.X : PowerSeries ℚ) ^ edgeExp a b H 0 σ)
        = ((edgePermsExp a b H N m).card : ℚ) := by
    rw [Finset.sum_congr rfl fun σ _ => PowerSeries.coeff_X_pow m (edgeExp a b H 0 σ),
      Finset.sum_boole, edgePermsExp]
    exact congrArg (fun s : Finset (Equiv.Perm (Fin (H + 1))) => (s.card : ℚ))
      (Finset.filter_congr fun σ _ => eq_comm)
  rw [coeff_intDet a b H N hab ha hb, hC, PowerSeries.coeff_C_mul, map_sum, hsum]

/-- The stabilised `q`-series of the `s^{dN}` coefficient of the determinant is `(-1)^N q^{γ_N}`
times the volume generating function of the bounded cylindric partitions: in each `q`-degree the
truncated determinant is already that count, as soon as the path carries every collection of that
weight. -/
theorem limCoeff_eq (a b N : ℕ) (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b) :
    limCoeff a b ((a + b) * N) = (-1) ^ N * PowerSeries.map (Int.castRingHom ℚ)
      ((PowerSeries.X : PowerSeries ℤ) ^ Paths.gammaShift a b N *
        HJO.Cylindric.boundedGF a b N) := by
  refine PowerSeries.ext fun m => ?_
  have hC : ((-1 : PowerSeries ℚ)) ^ N = PowerSeries.C ((-1 : ℚ) ^ N) := by
    rw [map_pow, map_neg, map_one]
  have hmul : a * (m + 1) ≤ (a + b) * (m + 1) := Nat.mul_le_mul_right _ (Nat.le_add_right a b)
  have hH1 : a * (m + 1) + b ≤ (a + b) * (m + 1) + a + b := by omega
  have hH2 : (a + b) * (m + 1) ≤ (a + b) * (m + 1) + a + b + 1 := by omega
  have hS : ∀ l : BddCyl a b N,
      Paths.gammaShift a b N + HJO.Cylindric.cylVolume a l.val = m →
      l ∈ bddCylFinset a b N (m + 1) ha := fun l hl => (mem_bddCylFinset ha l).2 (by omega)
  have hS' : ∀ l ∉ bddCylFinset a b N (m + 1) ha, m < HJO.Cylindric.cylVolume a l.val := by
    intro l hl
    have h := (mem_bddCylFinset (a := a) (b := b) (N := N) (y := m + 1) ha l).not.1 hl
    omega
  rw [coeff_limCoeff a b ((a + b) * N) m ha hb hH1,
    coeff_coeff_intDet a b ((a + b) * (m + 1) + a + b) N m hab ha hb, hC,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_map,
    coeff_gammaShift_mul_boundedGF a b N m ha _ hS',
    card_edgePermsExp a b ((a + b) * (m + 1) + a + b) N m hab ha hb hH2 _ hS]
  rw [eq_intCast, Int.cast_natCast]

/-- The two inclusions of `q`-series into `ℚ((q))` agree. -/
lemma qOfRat_map (f : PowerSeries ℤ) :
    qOfRat (PowerSeries.map (Int.castRingHom ℚ) f) = qOfInt f := rfl

section Limit

open scoped PowerSeries.WithPiTopology

/-- **The determinant counts bounded cylinders.** For coprime `a` and `b`, the coefficient of `z^N`
in `𝒟(-z;q)` is `q^{γ_N}` times the volume generating function of the cylindric partitions of the
balanced profile whose entries are at most `N`. -/
@[hjo "prop_det_coeff"]
theorem coeff_rescale_neg_one_detSeries (a b N : ℕ) (hab : Nat.Coprime a b) (ha : 0 < a)
    (hb : 0 < b) :
    PowerSeries.coeff N (PowerSeries.rescale (-1) (detSeries a b))
      = qVar ^ Paths.gammaShift a b N * qOfInt (HJO.Cylindric.boundedGF a b N) := by
  have hsq : ((-1 : LaurentSeries ℚ)) ^ N * (-1) ^ N = 1 := by
    rw [← pow_add, ← two_mul]
    exact Even.neg_one_pow ⟨N, by ring⟩
  have hlim : detSeries a b = detLimit a b :=
    (tendsto_detTrunc_detLimit a b ha hb).limUnder_eq
  rw [PowerSeries.coeff_rescale, hlim, detLimit, PowerSeries.coeff_mk,
    limCoeff_eq a b N hab ha hb, map_mul, map_pow, map_neg, map_one, qOfRat_map, map_mul, map_pow,
    ← mul_assoc, hsq, one_mul, ← qVar]

end Limit

end HJO.DetCoeffSolves
