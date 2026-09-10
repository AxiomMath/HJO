/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NoncommRing
public import HJO.Symmetric.SymmetricFunctions
public meta import HJO.Attr

/-! # The differential-order filtration and its normalised commutators

The differential order of Definition `HasDiffOrderAtMost` is a filtration of the algebra of
`K`-linear endomorphisms of `Lambda K`: composition adds orders, and a commutator drops one
below the sum. That drop is what makes the set `Rees` of `ℏ`-series with `ℏ ^ j`-coefficient
of order at most `j` closed under `M⁻¹` times a commutator, with `M = (1 - q) * ℏ`.
-/

@[expose] public section

open Finset

namespace HJO.ReesClosed

open HJO.Sym

section DiffOrder

variable {K : Type*} [CommRing K]

/-- The iterated partial derivative `∂ / ∂p_{i₁ + 1} ⋯ ∂ / ∂p_{iⱼ + 1}` along a list of
indices, as a `K`-linear endomorphism of `Lambda K`. -/
noncomputable def pderivProd (K : Type*) [CommRing K] (l : List ℕ) :
    Module.End K (Lambda K) :=
  (l.map (pderivEnd K)).prod

/-- The `K`-submodule of endomorphisms of `Lambda K` of differential order at most `n`, of
which `HasDiffOrderAtMost n` is the membership predicate. -/
noncomputable def diffOrder (K : Type*) [CommRing K] (n : ℕ) :
    Submodule K (Module.End K (Lambda K)) :=
  Submodule.span K {Q : Module.End K (Lambda K) | ∃ (f : Lambda K) (l : List ℕ),
    l.length ≤ n ∧ Q = LinearMap.mulLeft K f * pderivProd K l}

/-- Having differential order at most `n` is membership in `diffOrder K n`. -/
theorem hasDiffOrderAtMost_iff_mem {n : ℕ} {P : Module.End K (Lambda K)} :
    HasDiffOrderAtMost n P ↔ P ∈ diffOrder K n := Iff.rfl

/-- A generator of `diffOrder K n`: a multiplication operator composed with at most `n`
partial derivatives. -/
theorem mulLeft_mul_pderivProd_mem {n : ℕ} (f : Lambda K) {l : List ℕ} (hl : l.length ≤ n) :
    LinearMap.mulLeft K f * pderivProd K l ∈ diffOrder K n :=
  Submodule.subset_span ⟨f, l, hl, rfl⟩

/-- Multiplication operators have differential order zero. -/
theorem mulLeft_mem_diffOrder_zero (f : Lambda K) :
    LinearMap.mulLeft K f ∈ diffOrder K 0 := by
  have : LinearMap.mulLeft K f = LinearMap.mulLeft K f * pderivProd K [] := by
    simp [pderivProd]
  rw [this]
  exact mulLeft_mul_pderivProd_mem f (le_refl 0)

/-- The differential-order filtration is monotone. -/
theorem diffOrder_mono {m n : ℕ} (h : m ≤ n) : diffOrder K m ≤ diffOrder K n :=
  Submodule.span_mono fun _ ⟨f, l, hl, hQ⟩ => ⟨f, l, hl.trans h, hQ⟩

/-- The empty list gives the identity operator. -/
@[simp] theorem pderivProd_nil : pderivProd K [] = 1 := by simp [pderivProd]

/-- Splitting off the first index of an iterated partial derivative. -/
theorem pderivProd_cons (i : ℕ) (l : List ℕ) :
    pderivProd K (i :: l) = pderivEnd K i * pderivProd K l := by
  simp [pderivProd]

/-- Concatenating index lists composes the iterated partial derivatives. -/
theorem pderivProd_append (l m : List ℕ) :
    pderivProd K (l ++ m) = pderivProd K l * pderivProd K m := by
  simp [pderivProd, List.prod_append]

/-- Mixed partial derivatives of a polynomial in countably many variables commute. -/
theorem pderiv_pderiv_comm (i j : ℕ) (p : Lambda K) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j p)
      = MvPolynomial.pderiv j (MvPolynomial.pderiv i p) := by
  classical
  ext m
  rw [MvPolynomial.coeff_pderiv, MvPolynomial.coeff_pderiv, MvPolynomial.coeff_pderiv,
    MvPolynomial.coeff_pderiv]
  rcases eq_or_ne i j with rfl | hij
  · rfl
  · have h1 : (m + Finsupp.single i 1 : ℕ →₀ ℕ) j = m j := by
      simp [hij]
    have h2 : (m + Finsupp.single j 1 : ℕ →₀ ℕ) i = m i := by
      simp [Ne.symm hij]
    rw [add_right_comm, h1, h2]
    ring

/-- The partial derivative endomorphisms commute with one another. -/
theorem pderivEnd_comm (i j : ℕ) :
    pderivEnd K i * pderivEnd K j = pderivEnd K j * pderivEnd K i :=
  LinearMap.ext fun p => by simpa [pderivEnd] using pderiv_pderiv_comm i j p

/-- Any two iterated partial derivatives commute. -/
theorem pderivProd_commute (l m : List ℕ) :
    Commute (pderivProd K l) (pderivProd K m) := by
  simp only [pderivProd]
  refine Commute.list_prod_left _ _ fun x hx => Commute.list_prod_right _ _ fun y hy => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hy
  exact pderivEnd_comm (K := K) i j

/-- The Leibniz rule: moving a partial derivative past a multiplication operator produces the
derivative of the multiplier. -/
theorem pderivEnd_mul_mulLeft (i : ℕ) (f : Lambda K) :
    pderivEnd K i * LinearMap.mulLeft K f
      = LinearMap.mulLeft K f * pderivEnd K i
        + LinearMap.mulLeft K (MvPolynomial.pderiv i f) :=
  LinearMap.ext fun g => by
    have h : MvPolynomial.pderiv i (f * g)
        = f * MvPolynomial.pderiv i g + MvPolynomial.pderiv i f * g := by
      rw [MvPolynomial.pderiv_mul]; ring
    simpa [pderivEnd] using h

/-- Composing with a multiplication operator on the left does not raise the differential
order. -/
theorem mulLeft_mul_mem (f : Lambda K) {n : ℕ} {P : Module.End K (Lambda K)}
    (hP : P ∈ diffOrder K n) : LinearMap.mulLeft K f * P ∈ diffOrder K n := by
  refine Submodule.span_induction
    (p := fun Q _ => LinearMap.mulLeft K f * Q ∈ diffOrder K n) ?_ (by simp) ?_ ?_ hP
  · rintro Q ⟨g, l, hl, rfl⟩
    have h : LinearMap.mulLeft K f * (LinearMap.mulLeft K g * pderivProd K l)
        = LinearMap.mulLeft K (f * g) * pderivProd K l := by
      rw [← mul_assoc]
      congr 1
      ext x
      simp
    rw [h]
    exact mulLeft_mul_pderivProd_mem _ hl
  · intro x y _ _ hx hy
    rw [mul_add]
    exact Submodule.add_mem _ hx hy
  · intro a x _ hx
    rw [mul_smul_comm]
    exact Submodule.smul_mem _ _ hx

/-- Composing with an iterated partial derivative on the right raises the differential order by
at most the number of derivatives. -/
theorem mul_pderivProd_mem {n : ℕ} {P : Module.End K (Lambda K)} (hP : P ∈ diffOrder K n)
    (m : List ℕ) : P * pderivProd K m ∈ diffOrder K (n + m.length) := by
  refine Submodule.span_induction
    (p := fun Q _ => Q * pderivProd K m ∈ diffOrder K (n + m.length)) ?_ (by simp) ?_ ?_ hP
  · rintro Q ⟨g, l, hl, rfl⟩
    rw [mul_assoc, ← pderivProd_append]
    exact mulLeft_mul_pderivProd_mem _ (by simp only [List.length_append]; omega)
  · intro x y _ _ hx hy
    rw [add_mul]
    exact Submodule.add_mem _ hx hy
  · intro a x _ hx
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ _ hx

/-- Composing with a single partial derivative on the left raises the differential order by at
most one. -/
theorem pderivEnd_mul_mem (i : ℕ) {n : ℕ} {P : Module.End K (Lambda K)}
    (hP : P ∈ diffOrder K n) : pderivEnd K i * P ∈ diffOrder K (n + 1) := by
  refine Submodule.span_induction
    (p := fun Q _ => pderivEnd K i * Q ∈ diffOrder K (n + 1)) ?_ (by simp) ?_ ?_ hP
  · rintro Q ⟨g, l, hl, rfl⟩
    have h : pderivEnd K i * (LinearMap.mulLeft K g * pderivProd K l)
        = LinearMap.mulLeft K g * pderivProd K (i :: l)
          + LinearMap.mulLeft K (MvPolynomial.pderiv i g) * pderivProd K l := by
      rw [← mul_assoc, pderivEnd_mul_mulLeft, pderivProd_cons, add_mul, mul_assoc]
    rw [h]
    exact Submodule.add_mem _
      (mulLeft_mul_pderivProd_mem _ (by simp only [List.length_cons]; omega))
      (diffOrder_mono (Nat.le_succ n) (mulLeft_mul_pderivProd_mem _ hl))
  · intro x y _ _ hx hy
    rw [mul_add]
    exact Submodule.add_mem _ hx hy
  · intro a x _ hx
    rw [mul_smul_comm]
    exact Submodule.smul_mem _ _ hx

/-- The commutator of an iterated partial derivative of length at most `n + 1` with a
multiplication operator has differential order at most `n`: each Leibniz step trades one
derivative for a multiplication. -/
theorem pderivProd_commutator_mulLeft (l : List ℕ) :
    ∀ (n : ℕ) (f : Lambda K), l.length ≤ n + 1 →
      pderivProd K l * LinearMap.mulLeft K f - LinearMap.mulLeft K f * pderivProd K l
        ∈ diffOrder K n := by
  induction l with
  | nil => intro n f _; simp
  | cons i t ih =>
    intro n f hl
    have ht : t.length ≤ n := by simpa using hl
    have hsplit : pderivProd K (i :: t) * LinearMap.mulLeft K f
        - LinearMap.mulLeft K f * pderivProd K (i :: t)
        = pderivEnd K i * (pderivProd K t * LinearMap.mulLeft K f
            - LinearMap.mulLeft K f * pderivProd K t)
          + (pderivEnd K i * LinearMap.mulLeft K f
            - LinearMap.mulLeft K f * pderivEnd K i) * pderivProd K t := by
      rw [pderivProd_cons]; noncomm_ring
    rw [hsplit, pderivEnd_mul_mulLeft, add_sub_cancel_left]
    refine Submodule.add_mem _ ?_ (diffOrder_mono ht (mulLeft_mul_pderivProd_mem _ le_rfl))
    match n with
    | 0 =>
      have : t = [] := by cases t with | nil => rfl | cons a s => simp at ht
      subst this
      simp
    | m + 1 => exact pderivEnd_mul_mem i (ih m f (by omega))

/-- Multiplication operators commute, so the commutator of two operators of differential order
zero vanishes. -/
theorem commutator_eq_zero_of_diffOrder_zero {P Q : Module.End K (Lambda K)}
    (hP : P ∈ diffOrder K 0) (hQ : Q ∈ diffOrder K 0) : P * Q - Q * P = 0 := by
  refine Submodule.span_induction₂ (p := fun P Q _ _ => P * Q - Q * P = 0) ?_ (by simp) (by simp)
    ?_ ?_ ?_ ?_ hP hQ
  · rintro P Q ⟨f, l, hl, rfl⟩ ⟨g, m, hm, rfl⟩
    have hl' : l = [] := by cases l with | nil => rfl | cons a s => simp at hl
    have hm' : m = [] := by cases m with | nil => rfl | cons a s => simp at hm
    subst hl'; subst hm'
    simp only [pderivProd_nil, mul_one, sub_eq_zero]
    exact LinearMap.ext fun x => by simp [mul_left_comm]
  · intro x y z _ _ _ hx hy; rw [add_mul, mul_add, ← sub_add_sub_comm, hx, hy, add_zero]
  · intro x y z _ _ _ hy hz; rw [mul_add, add_mul, ← sub_add_sub_comm, hy, hz, add_zero]
  · intro a x y _ _ h; rw [smul_mul_assoc, mul_smul_comm, ← smul_sub, h, smul_zero]
  · intro a x y _ _ h; rw [smul_mul_assoc, mul_smul_comm, ← smul_sub, h, smul_zero]

/-- The heart of the filtration: operators of differential orders `r` and `s` compose to order
at most `r + s`, but their commutator drops to `r + s - 1`, the top-order symbols cancelling. -/
theorem commutator_mem_diffOrder {n r s : ℕ} (hrs : r + s ≤ n + 1)
    {P Q : Module.End K (Lambda K)} (hP : P ∈ diffOrder K r) (hQ : Q ∈ diffOrder K s) :
    P * Q - Q * P ∈ diffOrder K n := by
  refine Submodule.span_induction₂ (p := fun P Q _ _ => P * Q - Q * P ∈ diffOrder K n)
    ?_ (by simp) (by simp) ?_ ?_ ?_ ?_ hP hQ
  · rintro P Q ⟨f, l, hl, rfl⟩ ⟨g, m, hm, rfl⟩
    set F := LinearMap.mulLeft K f with hF
    set G := LinearMap.mulLeft K g with hG
    set A := pderivProd K l with hA
    set B := pderivProd K m with hB
    have hFG : F * G = G * F := LinearMap.ext fun x => by simp [hF, hG, mul_left_comm]
    have hAB : A * B = B * A := pderivProd_commute l m
    have key : F * A * (G * B) - G * B * (F * A)
        = F * (A * G - G * A) * B - G * (B * F - F * B) * A
          + (F * G * (A * B) - G * F * (B * A)) := by noncomm_ring
    rw [key, hFG, hAB, sub_self, add_zero]
    refine Submodule.sub_mem _ ?_ ?_
    · match r, hl with
      | 0, hl =>
        have : l = [] := by cases l with | nil => rfl | cons a s => simp at hl
        subst this
        simp [hA]
      | r + 1, hl =>
        have h1 : A * G - G * A ∈ diffOrder K r :=
          pderivProd_commutator_mulLeft l r g (by omega)
        have h2 : F * (A * G - G * A) * B ∈ diffOrder K (r + m.length) :=
          mul_pderivProd_mem (mulLeft_mul_mem f h1) m
        exact diffOrder_mono (by omega) h2
    · match s, hm with
      | 0, hm =>
        have : m = [] := by cases m with | nil => rfl | cons a t => simp at hm
        subst this
        simp [hB]
      | s + 1, hm =>
        have h1 : B * F - F * B ∈ diffOrder K s :=
          pderivProd_commutator_mulLeft m s f (by omega)
        have h2 : G * (B * F - F * B) * A ∈ diffOrder K (s + l.length) :=
          mul_pderivProd_mem (mulLeft_mul_mem g h1) l
        exact diffOrder_mono (by omega) h2
  · intro x y z _ _ _ hx hy
    rw [add_mul, mul_add, ← sub_add_sub_comm]
    exact Submodule.add_mem _ hx hy
  · intro x y z _ _ _ hy hz
    rw [mul_add, add_mul, ← sub_add_sub_comm]
    exact Submodule.add_mem _ hy hz
  · intro a x y _ _ h
    rw [smul_mul_assoc, mul_smul_comm, ← smul_sub]
    exact Submodule.smul_mem _ _ h
  · intro a x y _ _ h
    rw [smul_mul_assoc, mul_smul_comm, ← smul_sub]
    exact Submodule.smul_mem _ _ h

/-- The commutator order bound stated through the differential-order predicate: a commutator of
operators of orders `r` and `s` has order at most `r + s - 1`. -/
theorem hasDiffOrderAtMost_commutator {n r s : ℕ} (hrs : r + s ≤ n + 1)
    {P Q : Module.End K (Lambda K)} (hP : HasDiffOrderAtMost r P)
    (hQ : HasDiffOrderAtMost s Q) : HasDiffOrderAtMost n (P * Q - Q * P) :=
  commutator_mem_diffOrder hrs hP hQ

end DiffOrder

section Rees

variable {L : Type*} [Field L]

/-- A doubly indexed family supported in `[0, N) × [0, N)` sums the same over the square as
over the antidiagonals below `2 * N`. -/
theorem sum_antidiagonal_eq_sum_product {M : Type*} [AddCommMonoid M] (F : ℕ → ℕ → M) (N : ℕ)
    (hF : ∀ i j : ℕ, N ≤ i ∨ N ≤ j → F i j = 0) :
    ∑ n ∈ range (2 * N), ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, F p.1 p.2
      = ∑ p ∈ range N ×ˢ range N, F p.1 p.2 := by
  classical
  have hdisj : Set.PairwiseDisjoint (↑(range (2 * N)) : Set ℕ)
      (fun n => Finset.HasAntidiagonal.antidiagonal n : ℕ → Finset (ℕ × ℕ)) := by
    intro a _ b _ hab
    simp only [Function.onFun, Finset.disjoint_left]
    intro p hpa hpb
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hpa hpb
    exact absurd (hpa.symm.trans hpb) hab
  rw [← Finset.sum_biUnion hdisj]
  refine (Finset.sum_subset ?_ ?_).symm
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_range] at hp
    exact Finset.mem_biUnion.mpr ⟨p.1 + p.2, Finset.mem_range.mpr (by omega),
      Finset.HasAntidiagonal.mem_antidiagonal.mpr rfl⟩
  · intro p _ hp
    simp only [Finset.mem_product, Finset.mem_range, not_and_or, not_lt] at hp
    exact hF p.1 p.2 hp

/-- The zero operator lies in the order filtration. -/
theorem zero_mem_rees (u : L) : (0 : Module.End L (Lambda L)) ∈ Rees u :=
  ⟨fun _ => 0, fun _ => Submodule.zero_mem _, fun _ => ⟨0, fun _ _ => rfl, by simp⟩⟩

/-- A terminating `ℏ`-expansion of `P g` may be padded out to any longer range. -/
theorem expansion_extend {u : L} {P : Module.End L (Lambda L)}
    {Pc : ℕ → Module.End L (Lambda L)} {g : Lambda L} {m M : ℕ} (hm : m ≤ M)
    (hz : ∀ j, m ≤ j → Pc j g = 0)
    (hsum : P g = ∑ j ∈ range m, (1 - u) ^ j • Pc j g) :
    P g = ∑ j ∈ range M, (1 - u) ^ j • Pc j g := by
  rw [hsum]
  refine Finset.sum_subset
    (Finset.range_subset.mpr fun x hx => Finset.mem_range.mpr (lt_of_lt_of_le hx hm))
    fun j _ hj => ?_
  rw [hz j (by simpa using hj), smul_zero]

/-- The order filtration is closed under normalised commutators: if `P` and `Q` admit
`ℏ`-expansions with the `ℏ ^ j`-coefficient of differential order at most `j`, then so does
`M⁻¹ (P Q - Q P)` for `M = (1 - q) * (1 - u)`. The `ℏ ^ j`-coefficient of the commutator is a
sum of commutators `[Pᵣ, Q_s]` with `r + s = j + 1`, each of differential order at most `j`,
and dividing by `M` shifts that back into place. -/
@[hjo "lem_rees_closed"]
theorem smul_commutator_mem_rees (q u : L) {P Q : Module.End L (Lambda L)}
    (hP : P ∈ Rees u) (hQ : Q ∈ Rees u) :
    ((1 - q) * (1 - u))⁻¹ • (P * Q - Q * P) ∈ Rees u := by
  rcases eq_or_ne (1 - u : L) 0 with hu | hu
  · rw [hu, mul_zero, inv_zero, zero_smul]
    exact zero_mem_rees u
  rcases eq_or_ne (1 - q : L) 0 with hq | hq
  · rw [hq, zero_mul, inv_zero, zero_smul]
    exact zero_mem_rees u
  obtain ⟨Pc, hPord, hPsum⟩ := hP
  obtain ⟨Qc, hQord, hQsum⟩ := hQ
  choose np hnpz hnpsum using hPsum
  choose nq hnqz hnqsum using hQsum
  refine ⟨fun m => (1 - q)⁻¹ • ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (m + 1),
    (Pc p.1 * Qc p.2 - Qc p.2 * Pc p.1), ?_, ?_⟩
  · intro m
    rw [hasDiffOrderAtMost_iff_mem]
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun p hp => ?_)
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    exact commutator_mem_diffOrder (by omega) (hPord p.1) (hQord p.2)
  · intro f
    obtain ⟨K₀, h1, h2, h3, h4⟩ : ∃ K₀ : ℕ, np f ≤ K₀ ∧ nq f ≤ K₀ ∧
        (∀ j < nq f, np (Qc j f) ≤ K₀) ∧ (∀ i < np f, nq (Pc i f) ≤ K₀) := by
      refine ⟨max (max (np f) (nq f))
        (max ((range (nq f)).sup fun j => np (Qc j f))
          ((range (np f)).sup fun i => nq (Pc i f))), le_trans (le_max_left _ _) (le_max_left _ _),
        le_trans (le_max_right _ _) (le_max_left _ _), fun j hj => ?_, fun i hi => ?_⟩
      · exact le_trans (Finset.le_sup (f := fun j => np (Qc j f)) (Finset.mem_range.mpr hj))
          (le_trans (le_max_left _ _) (le_max_right _ _))
      · exact le_trans (Finset.le_sup (f := fun i => nq (Pc i f)) (Finset.mem_range.mpr hi))
          (le_trans (le_max_right _ _) (le_max_right _ _))
    have hzero : ∀ i j : ℕ, K₀ + 1 ≤ i ∨ K₀ + 1 ≤ j →
        (Pc i * Qc j - Qc j * Pc i) f = 0 := by
      intro i j hij
      have e1 : Pc i (Qc j f) = 0 := by
        rcases lt_or_ge j (nq f) with hj | hj
        · have hi : K₀ + 1 ≤ i := by rcases hij with hi | hj' <;> omega
          exact hnpz (Qc j f) i (by have := h3 j hj; omega)
        · rw [hnqz f j hj, map_zero]
      have e2 : Qc j (Pc i f) = 0 := by
        rcases lt_or_ge i (np f) with hi | hi
        · have hj : K₀ + 1 ≤ j := by rcases hij with hi' | hj <;> omega
          exact hnqz (Pc i f) j (by have := h4 i hi; omega)
        · rw [hnpz f i hi, map_zero]
      rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, e1, e2, sub_zero]
    have hPQ : ∀ j ∈ range (K₀ + 1), P (Qc j f)
        = ∑ i ∈ range (K₀ + 1), (1 - u) ^ i • Pc i (Qc j f) := by
      intro j _
      rcases lt_or_ge j (nq f) with hj | hj
      · exact expansion_extend (by have := h3 j hj; omega) (hnpz (Qc j f)) (hnpsum (Qc j f))
      · rw [hnqz f j hj]
        simp
    have hQP : ∀ i ∈ range (K₀ + 1), Q (Pc i f)
        = ∑ j ∈ range (K₀ + 1), (1 - u) ^ j • Qc j (Pc i f) := by
      intro i _
      rcases lt_or_ge i (np f) with hi | hi
      · exact expansion_extend (by have := h4 i hi; omega) (hnqz (Pc i f)) (hnqsum (Pc i f))
      · rw [hnpz f i hi]
        simp
    have hQ0 : Q f = ∑ j ∈ range (K₀ + 1), (1 - u) ^ j • Qc j f :=
      expansion_extend (by omega) (hnqz f) (hnqsum f)
    have hP0 : P f = ∑ i ∈ range (K₀ + 1), (1 - u) ^ i • Pc i f :=
      expansion_extend (by omega) (hnpz f) (hnpsum f)
    have hA : P (Q f) = ∑ i ∈ range (K₀ + 1), ∑ j ∈ range (K₀ + 1),
        (1 - u) ^ (i + j) • Pc i (Qc j f) := by
      rw [hQ0, map_sum, Finset.sum_comm]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [map_smul, hPQ j hj, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, ← pow_add, add_comm j i]
    have hB : Q (P f) = ∑ i ∈ range (K₀ + 1), ∑ j ∈ range (K₀ + 1),
        (1 - u) ^ (i + j) • Qc j (Pc i f) := by
      rw [hP0, map_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [map_smul, hQP i hi, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_smul, ← pow_add]
    have hlhs : (P * Q - Q * P) f = ∑ i ∈ range (K₀ + 1), ∑ j ∈ range (K₀ + 1),
        (1 - u) ^ (i + j) • ((Pc i * Qc j - Qc j * Pc i) f) := by
      rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, hA, hB,
        ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← smul_sub, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply]
    have hsq : ∑ i ∈ range (K₀ + 1), ∑ j ∈ range (K₀ + 1),
          (1 - u) ^ (i + j) • ((Pc i * Qc j - Qc j * Pc i) f)
        = ∑ n ∈ range (2 * (K₀ + 1)), ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
            (1 - u) ^ (p.1 + p.2) • ((Pc p.1 * Qc p.2 - Qc p.2 * Pc p.1) f) := by
      rw [← Finset.sum_product']
      exact (sum_antidiagonal_eq_sum_product
        (fun i j => (1 - u) ^ (i + j) • ((Pc i * Qc j - Qc j * Pc i) f)) (K₀ + 1)
        fun i j hij => by rw [hzero i j hij, smul_zero]).symm
    have hin : ∀ n : ℕ, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
          (1 - u) ^ (p.1 + p.2) • ((Pc p.1 * Qc p.2 - Qc p.2 * Pc p.1) f)
        = (1 - u) ^ n • ((∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
            (Pc p.1 * Qc p.2 - Qc p.2 * Pc p.1)) f) := by
      intro n
      rw [LinearMap.sum_apply, Finset.smul_sum]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      rw [hp]
    refine ⟨2 * K₀ + 1, fun j hj => ?_, ?_⟩
    · rw [LinearMap.smul_apply, LinearMap.sum_apply,
        Finset.sum_eq_zero fun p hp => hzero p.1 p.2
          (by rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp; omega), smul_zero]
    · rw [LinearMap.smul_apply, hlhs, hsq,
        Finset.sum_congr rfl fun n (_ : n ∈ range (2 * (K₀ + 1))) => hin n,
        show 2 * (K₀ + 1) = 2 * K₀ + 1 + 1 from by ring, Finset.sum_range_succ']
      have hz0 : ((∑ p ∈ Finset.HasAntidiagonal.antidiagonal 0,
          (Pc p.1 * Qc p.2 - Qc p.2 * Pc p.1)) : Module.End L (Lambda L)) = 0 := by
        rw [Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
        exact commutator_eq_zero_of_diffOrder_zero (hPord 0) (hQord 0)
      rw [hz0, LinearMap.zero_apply, smul_zero, add_zero, Finset.smul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [LinearMap.smul_apply]
      simp only [smul_smul]
      congr 1
      field_simp
      ring

end Rees

end HJO.ReesClosed
