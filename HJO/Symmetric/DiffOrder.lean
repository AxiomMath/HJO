/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Symmetric.ReesRegular
public import HJO.Symmetric.DopRees
public meta import HJO.Attr

/-! # The differential order of an operator, measured by iterated commutators

An operator on the ring of symmetric functions is a differential operator of order at most `n`
exactly when its `(n + 1)`-fold iterated commutator with multiplication operators vanishes. This
file takes that characterisation as the definition of `HasDiffOrder` and establishes the
filtration properties: order zero is multiplication, composition adds orders, a commutator drops
one below the sum, and everything already recognised by the spanning-set predicate
`HasDiffOrderAtMost` is recognised here too.

Unlike a definition by a span of multiplication operators times iterated partial derivatives, this
one is insensitive to how many of the generators an operator involves: the derivation sending every
`p_k` to `1` has order one here, although it lies in no span of finitely many partial derivatives.
That is what lets the basic operators be expanded in `ℏ = 1 - u` with the coefficient of `ℏ ^ j` of
order `j`, the grading being by the number of derivatives rather than by the degree in `w`.
-/

@[expose] public section

open Finset

namespace HJO.DiffOrder

open HJO.Sym HJO.ReesClosed

/-! ### The commutator with a multiplication operator -/

section Ad

variable {K : Type*} [CommRing K]

/-- The commutator with multiplication by `g`, as a `K`-linear operator on the algebra of
`K`-linear endomorphisms of `Lambda K`. -/
noncomputable def ad (g : Lambda K) : Module.End K (Lambda K) →ₗ[K] Module.End K (Lambda K) where
  toFun P := LinearMap.mulLeft K g * P - P * LinearMap.mulLeft K g
  map_add' P Q := by simp only [mul_add, add_mul]; abel
  map_smul' a P := by
    simp only [RingHom.id_apply, mul_smul_comm, smul_mul_assoc, smul_sub]

/-- The commutator with a multiplication operator, written out. -/
theorem ad_def (g : Lambda K) (P : Module.End K (Lambda K)) :
    ad g P = LinearMap.mulLeft K g * P - P * LinearMap.mulLeft K g := rfl

/-- The value of a commutator with a multiplication operator on a symmetric function. -/
theorem ad_apply (g : Lambda K) (P : Module.End K (Lambda K)) (f : Lambda K) :
    ad g P f = g * P f - P (g * f) := rfl

/-- The commutator of the zero operator with a multiplication operator vanishes. -/
theorem ad_zero_op (g : Lambda K) : ad g (0 : Module.End K (Lambda K)) = 0 := map_zero (ad g)

/-- The commutator with a multiplication operator is additive. -/
theorem ad_add (g : Lambda K) (P Q : Module.End K (Lambda K)) :
    ad g (P + Q) = ad g P + ad g Q := map_add (ad g) P Q

/-- The commutator with a multiplication operator respects differences. -/
theorem ad_sub (g : Lambda K) (P Q : Module.End K (Lambda K)) :
    ad g (P - Q) = ad g P - ad g Q := map_sub (ad g) P Q

/-- The commutator with a multiplication operator respects scalars. -/
theorem ad_smul (g : Lambda K) (a : K) (P : Module.End K (Lambda K)) :
    ad g (a • P) = a • ad g P := map_smul (ad g) a P

/-- The commutator with a multiplication operator is a derivation of the operator algebra. -/
theorem ad_mul (g : Lambda K) (P Q : Module.End K (Lambda K)) :
    ad g (P * Q) = ad g P * Q + P * ad g Q := by
  simp only [ad_def]
  noncomm_ring

end Ad

/-! ### The order filtration -/

section Order

variable {K : Type*} [CommRing K]

/-- An operator has differential order at most `n` when its `(n + 1)`-fold iterated commutator
with multiplication operators vanishes: for `n = 0` every single commutator vanishes, and for
`n + 1` every commutator has differential order at most `n`. -/
@[hjo "def_diff_order"]
def HasDiffOrder : ℕ → Module.End K (Lambda K) → Prop
  | 0, P => ∀ g : Lambda K, ad g P = 0
  | n + 1, P => ∀ g : Lambda K, HasDiffOrder n (ad g P)

/-- Differential order zero is the vanishing of every commutator with a multiplication
operator. -/
theorem hasDiffOrder_zero_def {P : Module.End K (Lambda K)} :
    HasDiffOrder 0 P ↔ ∀ g : Lambda K, ad g P = 0 := Iff.rfl

/-- Differential order at most `n + 1` is differential order at most `n` for every commutator
with a multiplication operator. -/
theorem hasDiffOrder_succ_def {n : ℕ} {P : Module.End K (Lambda K)} :
    HasDiffOrder (n + 1) P ↔ ∀ g : Lambda K, HasDiffOrder n (ad g P) := Iff.rfl

/-- The zero operator has every differential order. -/
theorem hasDiffOrder_zero (n : ℕ) : HasDiffOrder n (0 : Module.End K (Lambda K)) := by
  induction n with
  | zero => exact fun g => ad_zero_op g
  | succ n ih => exact fun g => by rw [ad_zero_op]; exact ih

/-- A sum of two operators of differential order at most `n` has differential order at
most `n`. -/
theorem hasDiffOrder_add {n : ℕ} {P Q : Module.End K (Lambda K)} (hP : HasDiffOrder n P)
    (hQ : HasDiffOrder n Q) : HasDiffOrder n (P + Q) := by
  induction n generalizing P Q with
  | zero => exact fun g => by rw [ad_add, hP g, hQ g, add_zero]
  | succ n ih => exact fun g => by rw [ad_add]; exact ih (hP g) (hQ g)

/-- A scalar multiple of an operator of differential order at most `n` has differential order at
most `n`. -/
theorem hasDiffOrder_smul {n : ℕ} (a : K) {P : Module.End K (Lambda K)}
    (hP : HasDiffOrder n P) : HasDiffOrder n (a • P) := by
  induction n generalizing P with
  | zero => exact fun g => by rw [ad_smul, hP g, smul_zero]
  | succ n ih => exact fun g => by rw [ad_smul]; exact ih (hP g)

/-- The negative of an operator of differential order at most `n` has differential order at
most `n`. -/
theorem hasDiffOrder_neg {n : ℕ} {P : Module.End K (Lambda K)} (hP : HasDiffOrder n P) :
    HasDiffOrder n (-P) := by
  have h : -P = (-1 : K) • P := by rw [neg_smul, one_smul]
  rw [h]
  exact hasDiffOrder_smul _ hP

/-- A difference of two operators of differential order at most `n` has differential order at
most `n`. -/
theorem hasDiffOrder_sub {n : ℕ} {P Q : Module.End K (Lambda K)} (hP : HasDiffOrder n P)
    (hQ : HasDiffOrder n Q) : HasDiffOrder n (P - Q) := by
  rw [sub_eq_add_neg]
  exact hasDiffOrder_add hP (hasDiffOrder_neg hQ)

/-- A finite sum of operators of differential order at most `n` has differential order at
most `n`. -/
theorem hasDiffOrder_sum {ι : Type*} {n : ℕ} {s : Finset ι} {F : ι → Module.End K (Lambda K)}
    (h : ∀ i ∈ s, HasDiffOrder n (F i)) : HasDiffOrder n (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simpa using hasDiffOrder_zero n
  | cons a s ha ih =>
    rw [Finset.sum_cons]
    exact hasDiffOrder_add (h a (by simp)) (ih fun i hi => h i (by simp [hi]))

/-- Differential order at most `n` implies differential order at most `n + 1`. -/
theorem hasDiffOrder_succ {n : ℕ} {P : Module.End K (Lambda K)} (hP : HasDiffOrder n P) :
    HasDiffOrder (n + 1) P := by
  induction n generalizing P with
  | zero => exact fun g => by rw [hP g]; exact hasDiffOrder_zero 0
  | succ n ih => exact fun g => ih (hP g)

/-- The differential-order filtration is monotone. -/
theorem hasDiffOrder_mono {m n : ℕ} (h : m ≤ n) {P : Module.End K (Lambda K)}
    (hP : HasDiffOrder m P) : HasDiffOrder n P := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction k with
  | zero => simpa using hP
  | succ k ih => exact hasDiffOrder_succ ih

/-! ### Order zero is multiplication -/

/-- A multiplication operator has differential order zero: multiplication operators commute. -/
theorem hasDiffOrder_mulLeft (h : Lambda K) : HasDiffOrder 0 (LinearMap.mulLeft K h) := by
  intro g
  refine LinearMap.ext fun f => ?_
  rw [ad_apply, LinearMap.mulLeft_apply, LinearMap.mulLeft_apply, LinearMap.zero_apply,
    mul_left_comm, sub_self]

/-- An operator of differential order zero is multiplication by its value on `1`. -/
theorem eq_mulLeft_of_hasDiffOrder_zero {P : Module.End K (Lambda K)} (hP : HasDiffOrder 0 P) :
    P = LinearMap.mulLeft K (P 1) := by
  refine LinearMap.ext fun f => ?_
  have h := congrArg (fun Q : Module.End K (Lambda K) => Q 1) (hP f)
  simp only [LinearMap.zero_apply, ad_apply, mul_one] at h
  rw [LinearMap.mulLeft_apply, mul_comm]
  exact (sub_eq_zero.mp h).symm

/-- The operators of differential order zero are exactly the multiplication operators. -/
theorem hasDiffOrder_zero_iff_exists_mulLeft {P : Module.End K (Lambda K)} :
    HasDiffOrder 0 P ↔ ∃ g : Lambda K, P = LinearMap.mulLeft K g :=
  ⟨fun h => ⟨P 1, eq_mulLeft_of_hasDiffOrder_zero h⟩,
    fun ⟨g, hg⟩ => hg ▸ hasDiffOrder_mulLeft g⟩

/-- Two operators of differential order zero commute, being multiplication operators. -/
theorem commute_of_hasDiffOrder_zero {P Q : Module.End K (Lambda K)} (hP : HasDiffOrder 0 P)
    (hQ : HasDiffOrder 0 Q) : P * Q = Q * P := by
  obtain ⟨a, rfl⟩ := hasDiffOrder_zero_iff_exists_mulLeft.mp hP
  obtain ⟨b, rfl⟩ := hasDiffOrder_zero_iff_exists_mulLeft.mp hQ
  exact LinearMap.ext fun x => by simp [mul_left_comm]

/-! ### The total derivation has order one -/

/-- The derivation sending every generator `p_k` to `1` has differential order one: its
commutator with multiplication by `g` is multiplication by the total derivative of `g`, up to
sign. This operator has no differential order in the spanning-set sense, so the two notions
genuinely differ. -/
theorem hasDiffOrder_one_totalDeriv : HasDiffOrder 1 (ReesRegular.totalDeriv K) := by
  intro g
  have h : ad g (ReesRegular.totalDeriv K)
      = -LinearMap.mulLeft K (ReesRegular.totalDeriv K g) := by
    rw [ad_def, ← ReesRegular.totalDeriv_commutator g]
    abel
  rw [h]
  exact hasDiffOrder_neg (hasDiffOrder_mulLeft _)

/-! ### Composition and the commutator drop -/

private theorem hasDiffOrder_mul_aux : ∀ n r s : ℕ, r + s ≤ n →
    ∀ {P Q : Module.End K (Lambda K)}, HasDiffOrder r P → HasDiffOrder s Q →
      ∀ m : ℕ, r + s ≤ m → HasDiffOrder m (P * Q) := by
  intro n
  induction n with
  | zero =>
    intro r s hrs P Q hP hQ m _
    obtain ⟨rfl, rfl⟩ : r = 0 ∧ s = 0 := by omega
    refine hasDiffOrder_mono (Nat.zero_le m) ?_
    exact fun g => by rw [ad_mul, hP g, hQ g, zero_mul, mul_zero, add_zero]
  | succ n ih =>
    intro r s hrs P Q hP hQ m hm
    rcases Nat.eq_zero_or_pos (r + s) with h0 | hpos
    · obtain ⟨rfl, rfl⟩ : r = 0 ∧ s = 0 := by omega
      refine hasDiffOrder_mono (Nat.zero_le m) ?_
      exact fun g => by rw [ad_mul, hP g, hQ g, zero_mul, mul_zero, add_zero]
    · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      intro g
      rw [ad_mul]
      refine hasDiffOrder_add ?_ ?_
      · rcases r with _ | r'
        · rw [show ad g P = 0 from hP g, zero_mul]
          exact hasDiffOrder_zero m'
        · exact ih r' s (by omega) (hP g) hQ m' (by omega)
      · rcases s with _ | s'
        · rw [show ad g Q = 0 from hQ g, mul_zero]
          exact hasDiffOrder_zero m'
        · exact ih r s' (by omega) hP (hQ g) m' (by omega)

/-- Composition adds differential orders. -/
theorem hasDiffOrder_mul {r s : ℕ} {P Q : Module.End K (Lambda K)} (hP : HasDiffOrder r P)
    (hQ : HasDiffOrder s Q) : HasDiffOrder (r + s) (P * Q) :=
  hasDiffOrder_mul_aux (r + s) r s le_rfl hP hQ (r + s) le_rfl

/-- Composition adds differential orders, stated against an upper bound. -/
theorem hasDiffOrder_mul_of_le {m r s : ℕ} (hm : r + s ≤ m) {P Q : Module.End K (Lambda K)}
    (hP : HasDiffOrder r P) (hQ : HasDiffOrder s Q) : HasDiffOrder m (P * Q) :=
  hasDiffOrder_mul_aux (r + s) r s le_rfl hP hQ m hm

/-- The commutator of operators of differential orders summing to at most one has differential
order zero: it is a difference of two products of commuting multiplication operators. -/
theorem hasDiffOrder_commutator_zero {r s : ℕ} (hrs : r + s ≤ 1)
    {P Q : Module.End K (Lambda K)} (hP : HasDiffOrder r P) (hQ : HasDiffOrder s Q) :
    HasDiffOrder 0 (P * Q - Q * P) := by
  intro g
  rw [ad_sub, ad_mul, ad_mul]
  have e1 : ad g P * Q = Q * ad g P := by
    rcases r with _ | r'
    · rw [show ad g P = 0 from hP g, zero_mul, mul_zero]
    · obtain ⟨rfl, rfl⟩ : r' = 0 ∧ s = 0 := by omega
      exact commute_of_hasDiffOrder_zero (hP g) hQ
  have e2 : P * ad g Q = ad g Q * P := by
    rcases s with _ | s'
    · rw [show ad g Q = 0 from hQ g, zero_mul, mul_zero]
    · obtain ⟨rfl, rfl⟩ : s' = 0 ∧ r = 0 := by omega
      exact (commute_of_hasDiffOrder_zero (hQ g) hP).symm
  rw [e1, e2]
  abel

private theorem hasDiffOrder_commutator_aux : ∀ n r s : ℕ, r + s ≤ n + 1 →
    ∀ {P Q : Module.End K (Lambda K)}, HasDiffOrder r P → HasDiffOrder s Q →
      ∀ m : ℕ, r + s ≤ m + 1 → HasDiffOrder m (P * Q - Q * P) := by
  intro n
  induction n with
  | zero =>
    intro r s hrs P Q hP hQ m _
    exact hasDiffOrder_mono (Nat.zero_le m) (hasDiffOrder_commutator_zero hrs hP hQ)
  | succ n ih =>
    intro r s hrs P Q hP hQ m hm
    rcases m with _ | m'
    · exact hasDiffOrder_commutator_zero (by omega) hP hQ
    · intro g
      rw [ad_sub, ad_mul, ad_mul]
      have hsplit : ad g P * Q + P * ad g Q - (ad g Q * P + Q * ad g P)
          = (ad g P * Q - Q * ad g P) + (P * ad g Q - ad g Q * P) := by abel
      rw [hsplit]
      refine hasDiffOrder_add ?_ ?_
      · rcases r with _ | r'
        · rw [show ad g P = 0 from hP g, zero_mul, mul_zero, sub_zero]
          exact hasDiffOrder_zero m'
        · exact ih r' s (by omega) (hP g) hQ m' (by omega)
      · rcases s with _ | s'
        · rw [show ad g Q = 0 from hQ g, zero_mul, mul_zero, sub_zero]
          exact hasDiffOrder_zero m'
        · exact ih r s' (by omega) hP (hQ g) m' (by omega)

/-- The commutator drop: operators of differential orders `r` and `s` compose to order `r + s`,
but their commutator has order at most `r + s - 1`, the top-order terms cancelling by the Jacobi
identity for the commutator with a multiplication operator. -/
theorem hasDiffOrder_commutator {n r s : ℕ} (hrs : r + s ≤ n + 1)
    {P Q : Module.End K (Lambda K)} (hP : HasDiffOrder r P) (hQ : HasDiffOrder s Q) :
    HasDiffOrder n (P * Q - Q * P) :=
  hasDiffOrder_commutator_aux n r s hrs hP hQ n hrs

/-! ### The spanning-set filtration is contained in this one -/

/-- A partial derivative has differential order one. -/
theorem hasDiffOrder_pderivEnd (i : ℕ) : HasDiffOrder 1 (pderivEnd K i) := by
  intro g
  have h : ad g (pderivEnd K i) = -LinearMap.mulLeft K (MvPolynomial.pderiv i g) := by
    rw [ad_def, pderivEnd_mul_mulLeft]
    abel
  rw [h]
  exact hasDiffOrder_neg (hasDiffOrder_mulLeft _)

/-- An iterated partial derivative has differential order the number of derivatives taken. -/
theorem hasDiffOrder_pderivProd (l : List ℕ) : HasDiffOrder l.length (pderivProd K l) := by
  induction l with
  | nil =>
    have h1 : (1 : Module.End K (Lambda K)) = LinearMap.mulLeft K (1 : Lambda K) :=
      LinearMap.ext fun x => by simp
    rw [List.length_nil, pderivProd_nil, h1]
    exact hasDiffOrder_mulLeft _
  | cons i t ih =>
    rw [pderivProd_cons]
    refine hasDiffOrder_mul_of_le ?_ (hasDiffOrder_pderivEnd i) ih
    rw [List.length_cons]
    omega

/-- Everything the spanning-set predicate recognises as of differential order at most `n` has
differential order at most `n` here: a multiplication operator has order zero, each partial
derivative order one, and the filtration is closed under sums and scalars. -/
theorem hasDiffOrder_of_hasDiffOrderAtMost {n : ℕ} {P : Module.End K (Lambda K)}
    (hP : HasDiffOrderAtMost n P) : HasDiffOrder n P := by
  rw [hasDiffOrderAtMost_iff_mem] at hP
  refine Submodule.span_induction (p := fun Q _ => HasDiffOrder n Q) ?_ (hasDiffOrder_zero n)
    ?_ ?_ hP
  · rintro Q ⟨f, l, hl, rfl⟩
    exact hasDiffOrder_mul_of_le (by omega) (hasDiffOrder_mulLeft f) (hasDiffOrder_pderivProd l)
  · intro x y _ _ hx hy
    exact hasDiffOrder_add hx hy
  · intro a x _ hx
    exact hasDiffOrder_smul a hx

end Order

/-! ### The weighted degree of a symmetric function -/

section WeightedDegree

variable {K : Type*} [CommRing K]

/-- The degree of a symmetric function in the grading where the generator `p_{i+1}` counts for
`i + 1`. A partial derivative in `p_{i+1}` lowers it by `i + 1`. -/
noncomputable def wtDeg (f : Lambda K) : ℕ :=
  MvPolynomial.weightedTotalDegree (fun i : ℕ => i + 1) f

/-- The weight of a monomial occurring in `f` is at most the weighted degree of `f`. -/
theorem weight_le_wtDeg {f : Lambda K} {m : ℕ →₀ ℕ} (hm : m ∈ f.support) :
    Finsupp.weight (fun i : ℕ => i + 1) m ≤ wtDeg f :=
  MvPolynomial.le_weightedTotalDegree _ hm

/-- A bound on the weight of every monomial of `f` bounds the weighted degree of `f`. -/
theorem wtDeg_le {f : Lambda K} {n : ℕ}
    (h : ∀ m ∈ f.support, Finsupp.weight (fun i : ℕ => i + 1) m ≤ n) : wtDeg f ≤ n :=
  Finset.sup_le h

/-- The weighted degree of a sum is at most the larger of the two weighted degrees. -/
theorem wtDeg_add_le (f g : Lambda K) : wtDeg (f + g) ≤ max (wtDeg f) (wtDeg g) := by
  refine wtDeg_le fun m hm => ?_
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_add] at hm
  by_cases hf : MvPolynomial.coeff m f = 0
  · have hg : MvPolynomial.coeff m g ≠ 0 := fun h => hm (by rw [hf, h, add_zero])
    exact le_trans (weight_le_wtDeg (MvPolynomial.mem_support_iff.mpr hg)) (le_max_right _ _)
  · exact le_trans (weight_le_wtDeg (MvPolynomial.mem_support_iff.mpr hf)) (le_max_left _ _)

/-- Scaling does not raise the weighted degree. -/
theorem wtDeg_smul_le (a : K) (f : Lambda K) : wtDeg (a • f) ≤ wtDeg f :=
  wtDeg_le fun _ hm => weight_le_wtDeg (MvPolynomial.support_smul hm)

/-- The weighted degree of a product is at most the sum of the weighted degrees. -/
theorem wtDeg_mul_le (f g : Lambda K) : wtDeg (f * g) ≤ wtDeg f + wtDeg g := by
  refine wtDeg_le fun m hm => ?_
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_mul] at hm
  obtain ⟨p, hp, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  have h1 : MvPolynomial.coeff p.1 f ≠ 0 := fun h => hne (by rw [h, zero_mul])
  have h2 : MvPolynomial.coeff p.2 g ≠ 0 := fun h => hne (by rw [h, mul_zero])
  have hw : Finsupp.weight (fun i : ℕ => i + 1) (p.1 + p.2)
      = Finsupp.weight (fun i : ℕ => i + 1) p.1 + Finsupp.weight (fun i : ℕ => i + 1) p.2 :=
    map_add _ _ _
  rw [← hp, hw]
  exact add_le_add (weight_le_wtDeg (MvPolynomial.mem_support_iff.mpr h1))
    (weight_le_wtDeg (MvPolynomial.mem_support_iff.mpr h2))

/-- Restoring the generator `p_{i+1}` to a monomial of `pderiv i f` gives a monomial of `f`, whose
weight is larger by `i + 1`. -/
theorem weight_add_succ_le_wtDeg {i : ℕ} {f : Lambda K} {m : ℕ →₀ ℕ}
    (hm : m ∈ (MvPolynomial.pderiv i f).support) :
    Finsupp.weight (fun j : ℕ => j + 1) m + (i + 1) ≤ wtDeg f := by
  have hco : MvPolynomial.coeff (m + Finsupp.single i 1) f ≠ 0 := by
    intro h
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_pderiv, h, zero_mul] at hm
    exact hm rfl
  have h := weight_le_wtDeg (f := f) (MvPolynomial.mem_support_iff.mpr hco)
  rwa [map_add, Finsupp.weight_single, one_smul] at h

/-- Below weight `i + 1` the partial derivative in the generator `p_{i+1}` vanishes. -/
theorem pderiv_eq_zero_of_wtDeg_lt {i : ℕ} {f : Lambda K} (h : wtDeg f < i + 1) :
    MvPolynomial.pderiv i f = 0 := by
  by_contra hne
  obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.mp hne
  have := weight_add_succ_le_wtDeg (i := i) (f := f) (MvPolynomial.mem_support_iff.mpr hm)
  omega

/-- Differentiating in the generator `p_{i+1}` lowers the weighted degree by `i + 1`. -/
theorem wtDeg_pderiv_le {i n : ℕ} {f : Lambda K} (h : wtDeg f ≤ n + (i + 1)) :
    wtDeg (MvPolynomial.pderiv i f) ≤ n :=
  wtDeg_le fun _ hm => by
    have := weight_add_succ_le_wtDeg (i := i) (f := f) hm
    omega

/-! ### Recognising the order from bounded degrees -/

/-- An operator that agrees, on the symmetric functions of any prescribed bounded weighted degree,
with some operator of differential order at most `n`, itself has differential order at most `n`:
each iterated commutator with multiplication operators consumes only a bounded amount of degree. -/
theorem hasDiffOrder_of_locally (n : ℕ) {P : Module.End K (Lambda K)}
    (h : ∀ N : ℕ, ∃ P' : Module.End K (Lambda K), HasDiffOrder n P' ∧
      ∀ f : Lambda K, wtDeg f < N → P f = P' f) : HasDiffOrder n P := by
  induction n generalizing P with
  | zero =>
    intro g
    refine LinearMap.ext fun f => ?_
    obtain ⟨P', hP', hagree⟩ := h (wtDeg g + wtDeg f + 1)
    have hgf : wtDeg (g * f) < wtDeg g + wtDeg f + 1 := by
      have := wtDeg_mul_le g f; omega
    rw [LinearMap.zero_apply, ad_apply, hagree f (by omega), hagree (g * f) hgf, ← ad_apply,
      hP' g, LinearMap.zero_apply]
  | succ n ih =>
    intro g
    refine ih fun N => ?_
    obtain ⟨P', hP', hagree⟩ := h (N + wtDeg g)
    refine ⟨ad g P', hP' g, fun f hf => ?_⟩
    have hgf : wtDeg (g * f) < N + wtDeg g := by
      have := wtDeg_mul_le g f; omega
    rw [ad_apply, ad_apply, hagree f (by omega), hagree (g * f) hgf]

end WeightedDegree

/-! ### The order filtration on `ℏ`-series -/

section Rees

variable {L : Type*} [Field L]

/-- The order-filtered algebra of operators built on the commutator filtration: those `P` admitting
an expansion `P = ∑_{j ≥ 0} ℏ ^ j * P j` in `ℏ = 1 - u` whose `ℏ ^ j`-coefficient has differential
order at most `j`. Convergence on each fixed symmetric function is rendered as termination there. -/
def ReesComm (u : L) : Set (Module.End L (Lambda L)) :=
  {P | ∃ Q : ℕ → Module.End L (Lambda L), (∀ j, HasDiffOrder j (Q j)) ∧
    ∀ f : Lambda L, ∃ N : ℕ, (∀ j, N ≤ j → Q j f = 0) ∧
      P f = ∑ j ∈ range N, (1 - u) ^ j • Q j f}

/-- Everything the spanning-set filtration recognises is recognised here, so the order filtration
of the span sense is contained in this one. -/
theorem rees_subset_reesComm (u : L) : Rees u ⊆ ReesComm u := by
  rintro P ⟨Q, hord, hsum⟩
  exact ⟨Q, fun j => hasDiffOrder_of_hasDiffOrderAtMost (hord j), hsum⟩

end Rees

/-! ### The basic operators, graded by the number of derivatives -/

section Graded

open HJO.DopRees

section Scalars

variable {K : Type*} [CommRing K]

/-- The finite geometric series splitting the deformation parameter `ℏ = 1 - u` off `1 - u ^ n`. -/
theorem one_sub_mul_geomSum (u : K) (n : ℕ) :
    (1 - u) * ∑ t ∈ range n, u ^ t = 1 - u ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, mul_add, ih]; ring

/-- The scalar of the plethystic displacement with one factor of `ℏ = 1 - u` removed. -/
def shiftScalarRed (q u : K) (i : ℕ) : K := (1 - q ^ (i + 1)) * ∑ t ∈ range (i + 1), u ^ t

/-- The chain-rule weight of the displacement with one factor of `ℏ = 1 - u` removed. -/
def chainScalarRed (q u : K) (i : ℕ) : K := ((i : K) + 1) * shiftScalarRed q u i

end Scalars

variable {L : Type*} [Field L]

/-- The scalar of the displacement is `ℏ` times its reduced form: each power of `w` costs exactly
one power of the deformation parameter. -/
theorem shiftScalar_eq (q u : L) (i : ℕ) :
    shiftScalar q u i = (1 - u) * shiftScalarRed q u i := by
  simp only [shiftScalar, shiftScalarRed]
  rw [← one_sub_mul_geomSum u (i + 1)]
  ring

/-- The chain-rule weight is `ℏ` times its reduced form. -/
theorem chainScalar_eq (q u : L) (i : ℕ) :
    chainScalar q u i = (1 - u) * chainScalarRed q u i := by
  simp only [chainScalar, chainScalarRed, shiftScalar_eq]
  ring

/-- The part of the coefficient of `wᵈ` of the plethystic displacement carrying exactly `j` partial
derivatives, with the `j` accompanying factors of `ℏ = 1 - u` removed. The chain rule in `w` trades
one power of `w` for one derivative, so `d` is the total weight of the derivatives taken. -/
noncomputable def gradedCoeff (q u : L) : ℕ → ℕ → Module.End L (Lambda L)
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | j + 1, m + 1 => ((m : L) + 1)⁻¹ • ∑ i ∈ range (m + 1),
      chainScalarRed q u i • (gradedCoeff q u j (m - i) * pderivEnd L i)

/-- With no derivatives and no shift the graded coefficient is the identity. -/
theorem gradedCoeff_zero_zero (q u : L) : gradedCoeff q u 0 0 = 1 := rfl

/-- With no derivatives a positive power of `w` cannot be reached. -/
theorem gradedCoeff_zero_succ (q u : L) (d : ℕ) : gradedCoeff q u 0 (d + 1) = 0 := rfl

/-- Taking a derivative costs a power of `w`, so the constant coefficient has no derivative part. -/
theorem gradedCoeff_succ_zero (q u : L) (j : ℕ) : gradedCoeff q u (j + 1) 0 = 0 := rfl

/-- The chain rule for the graded coefficients: one derivative is peeled off, its index `i`
consuming `i + 1` of the degree in `w`. -/
theorem gradedCoeff_succ_succ (q u : L) (j m : ℕ) :
    gradedCoeff q u (j + 1) (m + 1) = ((m : L) + 1)⁻¹ • ∑ i ∈ range (m + 1),
      chainScalarRed q u i • (gradedCoeff q u j (m - i) * pderivEnd L i) := rfl

/-- With more derivatives than the degree in `w` allows, the graded coefficient vanishes. -/
theorem gradedCoeff_eq_zero_of_lt (q u : L) : ∀ j d : ℕ, d < j → gradedCoeff q u j d = 0 := by
  intro j
  induction j with
  | zero => intro d hd; omega
  | succ j ih =>
    intro d hd
    match d with
    | 0 => exact gradedCoeff_succ_zero q u j
    | m + 1 =>
      rw [gradedCoeff_succ_succ]
      refine smul_eq_zero_of_right _ (Finset.sum_eq_zero fun i hi => ?_)
      simp only [Finset.mem_range] at hi
      rw [ih (m - i) (by omega), zero_mul, smul_zero]

/-- The graded coefficient is a finite combination of `j` partial derivatives with polynomial
multipliers, hence of differential order at most `j` even in the spanning-set sense. -/
theorem gradedCoeff_mem_diffOrder (q u : L) :
    ∀ j d : ℕ, gradedCoeff q u j d ∈ diffOrder L j := by
  intro j
  induction j with
  | zero =>
    intro d
    match d with
    | 0 =>
      have h1 : (1 : Module.End L (Lambda L)) = LinearMap.mulLeft L (1 : Lambda L) :=
        LinearMap.ext fun x => by simp
      rw [gradedCoeff_zero_zero, h1]
      exact mulLeft_mem_diffOrder_zero _
    | m + 1 =>
      rw [gradedCoeff_zero_succ]
      exact Submodule.zero_mem _
  | succ j ih =>
    intro d
    match d with
    | 0 =>
      rw [gradedCoeff_succ_zero]
      exact Submodule.zero_mem _
    | m + 1 =>
      rw [gradedCoeff_succ_succ]
      refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_)
      have hlist : pderivProd L [i] = pderivEnd L i := by simp [pderivProd_cons]
      rw [← hlist]
      exact diffOrder_mono (by simp only [List.length_singleton]; omega)
        (mul_pderivProd_mem (ih (m - i)) [i])

/-- The graded coefficient has differential order at most `j` in the commutator sense. -/
theorem hasDiffOrder_gradedCoeff (q u : L) (j d : ℕ) :
    HasDiffOrder j (gradedCoeff q u j d) :=
  hasDiffOrder_of_hasDiffOrderAtMost (gradedCoeff_mem_diffOrder q u j d)

/-- The graded coefficient of degree `d` lowers the weighted degree by `d`, so it kills every
symmetric function of weighted degree below `d`. -/
theorem gradedCoeff_apply_eq_zero (q u : L) :
    ∀ (j d : ℕ) (f : Lambda L), wtDeg f < d → gradedCoeff q u j d f = 0 := by
  intro j
  induction j with
  | zero =>
    intro d f h
    match d with
    | 0 => omega
    | m + 1 => rw [gradedCoeff_zero_succ]; simp
  | succ j ih =>
    intro d f h
    match d with
    | 0 => omega
    | m + 1 =>
      have hz : ∀ i ∈ range (m + 1),
          (chainScalarRed q u i • (gradedCoeff q u j (m - i) * pderivEnd L i)) f = 0 := by
        intro i hi
        simp only [Finset.mem_range] at hi
        rw [LinearMap.smul_apply, Module.End.mul_apply,
          show pderivEnd L i f = MvPolynomial.pderiv i f from rfl]
        rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hi) with rfl | hlt
        · have hz0 : MvPolynomial.pderiv i f = 0 := pderiv_eq_zero_of_wtDeg_lt (by omega)
          rw [hz0, map_zero, smul_zero]
        · have hlt2 : wtDeg (MvPolynomial.pderiv i f) < m - i := by
            have := wtDeg_pderiv_le (i := i) (n := m - i - 1) (f := f) (by omega)
            omega
          rw [ih (m - i) (MvPolynomial.pderiv i f) hlt2, smul_zero]
      rw [gradedCoeff_succ_succ, LinearMap.smul_apply, LinearMap.sum_apply,
        Finset.sum_eq_zero hz, smul_zero]

section RationalAlgebra

variable [Algebra ℚ L]

/-- The coefficient of `wᵈ` of the displacement, graded by the number of derivatives: the part with
`j` derivatives carries exactly `j` powers of `ℏ = 1 - u`. -/
theorem shiftCoeff_eq_sum_gradedCoeff (q u : L) (d : ℕ) :
    shiftCoeff q u d = ∑ j ∈ range (d + 1), (1 - u) ^ j • gradedCoeff q u j d := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    match d with
    | 0 => rw [shiftCoeff_zero, Finset.sum_range_one, gradedCoeff_zero_zero, pow_zero, one_smul]
    | m + 1 =>
      have hchar : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
      have hne : ((m : L) + 1) ≠ 0 := by
        have h : ((m + 1 : ℕ) : L) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)
        push_cast at h
        exact h
      have key : shiftCoeff q u (m + 1)
          = ((m : L) + 1)⁻¹ • ∑ i ∈ range (m + 1), chainScalar q u i •
              (shiftCoeff q u (m - i) * pderivEnd L i) := by
        rw [← succ_smul_shiftCoeff_eq, smul_smul, inv_mul_cancel₀ hne, one_smul]
      have hext : ∀ i ∈ range (m + 1), shiftCoeff q u (m - i)
          = ∑ j ∈ range (m + 1), (1 - u) ^ j • gradedCoeff q u j (m - i) := by
        intro i hi
        simp only [Finset.mem_range] at hi
        have hsub : range (m - i + 1) ⊆ range (m + 1) := Finset.range_subset_range.mpr (by omega)
        rw [ih (m - i) (by omega)]
        refine Finset.sum_subset hsub fun j _ hj => ?_
        simp only [Finset.mem_range, not_lt] at hj
        rw [gradedCoeff_eq_zero_of_lt q u j (m - i) (by omega), smul_zero]
      have step : ∀ i ∈ range (m + 1),
          chainScalar q u i • (shiftCoeff q u (m - i) * pderivEnd L i)
          = ∑ j ∈ range (m + 1), (1 - u) ^ (j + 1) •
              (chainScalarRed q u i • (gradedCoeff q u j (m - i) * pderivEnd L i)) := by
        intro i hi
        rw [hext i hi, chainScalar_eq, Finset.sum_mul, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_mul_assoc, smul_smul, smul_smul]
        congr 1
        ring
      have hrhs : ∑ j ∈ range (m + 1 + 1), (1 - u) ^ j • gradedCoeff q u j (m + 1)
          = ∑ j ∈ range (m + 1), (1 - u) ^ (j + 1) • gradedCoeff q u (j + 1) (m + 1) := by
        rw [Finset.sum_range_succ', gradedCoeff_zero_succ, smul_zero, add_zero]
      rw [key, Finset.sum_congr rfl step, Finset.sum_comm, hrhs, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [gradedCoeff_succ_succ, ← Finset.smul_sum, smul_comm]

/-- The `ℏ ^ j`-coefficient of the basic operator `Dop q u k`, truncated to the pieces of degree
below `N` in `w`. -/
noncomputable def dopGradedTrunc (q u : L) (k j N : ℕ) : Module.End L (Lambda L) :=
  ∑ d ∈ range N, LinearMap.mulLeft L ((-1) ^ (k + d) * elemSymm L (k + d)) * gradedCoeff q u j d

/-- Every truncation has differential order at most `j`. -/
theorem hasDiffOrder_dopGradedTrunc (q u : L) (k j N : ℕ) :
    HasDiffOrder j (dopGradedTrunc q u k j N) := by
  rw [dopGradedTrunc]
  exact hasDiffOrder_sum fun d _ =>
    hasDiffOrder_mul_of_le (by omega) (hasDiffOrder_mulLeft _) (hasDiffOrder_gradedCoeff q u j d)

/-- Two truncations agree on a symmetric function once both reach past its weighted degree. -/
theorem dopGradedTrunc_apply_of_lt (q u : L) (k j : ℕ) {N : ℕ} {f : Lambda L} (hN : wtDeg f < N) :
    dopGradedTrunc q u k j N f = dopGradedTrunc q u k j (wtDeg f + 1) f := by
  have hsub : range (wtDeg f + 1) ⊆ range N := Finset.range_subset_range.mpr (by omega)
  simp only [dopGradedTrunc, LinearMap.sum_apply]
  refine (Finset.sum_subset hsub fun d _ hd => ?_).symm
  simp only [Finset.mem_range, not_lt] at hd
  rw [Module.End.mul_apply, gradedCoeff_apply_eq_zero q u j d f (by omega), map_zero]

/-- The `ℏ ^ j`-coefficient of the basic operator `Dop q u k`: the sum over all degrees `d` in `w`
of the multiplier paired with that degree, composed with the part of the `wᵈ`-coefficient carrying
`j` derivatives. The sum is locally finite, the term of degree `d` lowering the weighted degree
by `d`. -/
noncomputable def dopGraded (q u : L) (k j : ℕ) : Module.End L (Lambda L) where
  toFun f := dopGradedTrunc q u k j (wtDeg f + 1) f
  map_add' f g := by
    change dopGradedTrunc q u k j (wtDeg (f + g) + 1) (f + g)
        = dopGradedTrunc q u k j (wtDeg f + 1) f + dopGradedTrunc q u k j (wtDeg g + 1) g
    rw [← dopGradedTrunc_apply_of_lt q u k j
        (show wtDeg (f + g) < max (wtDeg f) (wtDeg g) + 1 from by
          have := wtDeg_add_le f g; omega),
      ← dopGradedTrunc_apply_of_lt (f := f) q u k j
        (show wtDeg f < max (wtDeg f) (wtDeg g) + 1 from by omega),
      ← dopGradedTrunc_apply_of_lt (f := g) q u k j
        (show wtDeg g < max (wtDeg f) (wtDeg g) + 1 from by omega),
      map_add]
  map_smul' a f := by
    change dopGradedTrunc q u k j (wtDeg (a • f) + 1) (a • f)
        = a • dopGradedTrunc q u k j (wtDeg f + 1) f
    rw [← dopGradedTrunc_apply_of_lt (f := a • f) q u k j
      (show wtDeg (a • f) < wtDeg f + 1 from by have := wtDeg_smul_le a f; omega), map_smul]

/-- The `ℏ ^ j`-coefficient agrees with any truncation reaching past the weighted degree. -/
theorem dopGraded_apply (q u : L) (k j : ℕ) {N : ℕ} {f : Lambda L} (hN : wtDeg f < N) :
    dopGraded q u k j f = dopGradedTrunc q u k j N f :=
  (dopGradedTrunc_apply_of_lt q u k j hN).symm

/-- The `ℏ ^ j`-coefficient has differential order at most `j`: on the symmetric functions of any
bounded weighted degree it agrees with a truncation, a finite sum of multiplication operators
composed with `j` partial derivatives. This is the step that the spanning-set predicate cannot
take, the honest coefficient being a locally finite sum over all the generators. -/
theorem hasDiffOrder_dopGraded (q u : L) (k j : ℕ) : HasDiffOrder j (dopGraded q u k j) :=
  hasDiffOrder_of_locally j fun N =>
    ⟨dopGradedTrunc q u k j N, hasDiffOrder_dopGradedTrunc q u k j N,
      fun _ hf => dopGraded_apply q u k j hf⟩

/-- Beyond the weighted degree of `f` the graded coefficients kill `f`, so the expansion of a basic
operator terminates on every symmetric function. -/
theorem dopGraded_apply_eq_zero (q u : L) (k j : ℕ) (f : Lambda L) (hj : wtDeg f < j) :
    dopGraded q u k j f = 0 := by
  rw [dopGraded_apply q u k j (show wtDeg f < wtDeg f + 1 from by omega), dopGradedTrunc,
    LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun d hd => ?_
  simp only [Finset.mem_range] at hd
  rw [Module.End.mul_apply, gradedCoeff_eq_zero_of_lt q u j d (by omega), LinearMap.zero_apply,
    map_zero]

/-- The `ℏ`-expansion of a basic operator on a symmetric function, graded by the number of
derivatives: the sum terminates at the weighted degree of the argument. -/
theorem dop_apply_eq_sum_dopGraded (q u : L) (k : ℕ) (f : Lambda L) :
    Dop q u k f = ∑ j ∈ range (wtDeg f + 1), (1 - u) ^ j • dopGraded q u k j f := by
  obtain ⟨M, hMd, hMw⟩ : ∃ M : ℕ, (plethShift q u f).natDegree < M ∧ wtDeg f + 1 ≤ M :=
    ⟨max ((plethShift q u f).natDegree + 1) (wtDeg f + 1), by omega, by omega⟩
  have hMw' : wtDeg f < M := by omega
  have hsc : ∀ d ∈ range M, shiftCoeff q u d f
      = ∑ j ∈ range M, (1 - u) ^ j • gradedCoeff q u j d f := by
    intro d hd
    simp only [Finset.mem_range] at hd
    have h1 : shiftCoeff q u d f = ∑ j ∈ range (d + 1), (1 - u) ^ j • gradedCoeff q u j d f := by
      rw [shiftCoeff_eq_sum_gradedCoeff q u d, LinearMap.sum_apply]
      simp only [LinearMap.smul_apply]
    have hsub : range (d + 1) ⊆ range M := Finset.range_subset_range.mpr (by omega)
    rw [h1]
    refine Finset.sum_subset hsub fun j _ hj => ?_
    simp only [Finset.mem_range, not_lt] at hj
    rw [gradedCoeff_eq_zero_of_lt q u j d (by omega), LinearMap.zero_apply, smul_zero]
  have hdp : ∀ d ∈ range M, dopPiece q u k d f
      = ∑ j ∈ range M, (1 - u) ^ j •
          (((-1) ^ (k + d) * elemSymm L (k + d)) * gradedCoeff q u j d f) := by
    intro d hd
    rw [dopPiece_apply, ← shiftCoeff_apply, hsc d hd, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => mul_smul_comm _ _ _
  have hper : ∀ j ∈ range M,
      ∑ d ∈ range M, (1 - u) ^ j •
          (((-1) ^ (k + d) * elemSymm L (k + d)) * gradedCoeff q u j d f)
      = (1 - u) ^ j • dopGraded q u k j f := by
    intro j _
    rw [← Finset.smul_sum, dopGraded_apply q u k j hMw', dopGradedTrunc, LinearMap.sum_apply]
    simp only [Module.End.mul_apply, LinearMap.mulLeft_apply]
  have hsub : range (wtDeg f + 1) ⊆ range M := Finset.range_subset_range.mpr (by omega)
  rw [dop_apply_eq_sum q u k f hMd, Finset.sum_congr rfl hdp, Finset.sum_comm,
    Finset.sum_congr rfl hper]
  refine (Finset.sum_subset hsub fun j _ hjn => ?_).symm
  simp only [Finset.mem_range, not_lt] at hjn
  rw [dopGraded_apply_eq_zero q u k j f (by omega), smul_zero]

/-- The basic operators lie in the order filtration built on the commutator definition, with the
honest grading: the coefficient of `ℏ ^ j` is the part carrying `j` derivatives, a locally finite
sum over all the generators, and it has differential order at most `j`. -/
theorem dop_mem_reesComm (q u : L) (k : ℕ) : Dop q u k ∈ ReesComm u :=
  ⟨fun j => dopGraded q u k j, fun j => hasDiffOrder_dopGraded q u k j, fun f =>
    ⟨wtDeg f + 1, fun j hj => dopGraded_apply_eq_zero q u k j f (by omega),
      dop_apply_eq_sum_dopGraded q u k f⟩⟩

end RationalAlgebra

end Graded

/-! ### Tracking the coefficient ring -/

section Reg

open HJO.ReesRegular

/-- Differential order at most `n` over the coefficient ring `R`: the iterated-commutator
condition, together with the requirement that the operator carry symmetric functions with
coefficients in `R` to symmetric functions with coefficients in `R`. -/
def HasDiffOrderReg (R : Type*) [CommRing R] {L : Type*} [CommRing L] [Algebra R L] (n : ℕ)
    (P : Module.End L (Lambda L)) : Prop :=
  HasDiffOrder n P ∧ ∀ f ∈ regSub R L, P f ∈ regSub R L

variable {R : Type*} [CommRing R] {L : Type*} [CommRing L] [Algebra R L]

/-- The symmetric functions with coefficients in `R` contain `1`. -/
theorem one_mem_regSub : (1 : Lambda L) ∈ regSub R L := by
  simpa using coeffInc_mem_regSub (L := L) (1 : Lambda R)

/-- The symmetric functions with coefficients in `R` are closed under multiplication. -/
theorem mul_mem_regSub {x y : Lambda L} (hx : x ∈ regSub R L) (hy : y ∈ regSub R L) :
    x * y ∈ regSub R L := by
  obtain ⟨a, rfl⟩ := mem_regSub.mp hx
  obtain ⟨b, rfl⟩ := mem_regSub.mp hy
  rw [← map_mul]
  exact coeffInc_mem_regSub _

/-- Powers of `-1` have coefficients in `R`. -/
theorem neg_one_pow_mem_regSub (n : ℕ) : (-1 : Lambda L) ^ n ∈ regSub R L := by
  have h : (-1 : Lambda L) ^ n = coeffInc R L ((-1 : Lambda R) ^ n) := by
    rw [map_pow, map_neg, map_one]
  rw [h]
  exact coeffInc_mem_regSub _

/-- The power sums have coefficients in `R`. -/
theorem powerSum_mem_regSub (k : ℕ) : powerSum L k ∈ regSub R L := by
  have h : powerSum L k = coeffInc R L (powerSum R k) := by
    rw [coeffInc_apply, powerSum, powerSum, MvPolynomial.map_X]
  rw [h]
  exact coeffInc_mem_regSub _

/-- A partial derivative preserves the symmetric functions with coefficients in `R`. -/
theorem pderivEnd_mem_regSub (i : ℕ) {x : Lambda L} (hx : x ∈ regSub R L) :
    pderivEnd L i x ∈ regSub R L := by
  obtain ⟨g, rfl⟩ := mem_regSub.mp hx
  rw [show pderivEnd L i (coeffInc R L g) = MvPolynomial.pderiv i (coeffInc R L g) from rfl,
    pderiv_coeffInc]
  exact coeffInc_mem_regSub _

/-- The zero operator has every differential order over the coefficient ring. -/
theorem hasDiffOrderReg_zero (n : ℕ) : HasDiffOrderReg R n (0 : Module.End L (Lambda L)) :=
  ⟨hasDiffOrder_zero n, fun _ _ => by rw [LinearMap.zero_apply]; exact Submodule.zero_mem _⟩

/-- The filtration over the coefficient ring is monotone. -/
theorem hasDiffOrderReg_mono {m n : ℕ} (h : m ≤ n) {P : Module.End L (Lambda L)}
    (hP : HasDiffOrderReg R m P) : HasDiffOrderReg R n P :=
  ⟨hasDiffOrder_mono h hP.1, hP.2⟩

/-- Sums stay in the filtration over the coefficient ring. -/
theorem hasDiffOrderReg_add {n : ℕ} {P Q : Module.End L (Lambda L)}
    (hP : HasDiffOrderReg R n P) (hQ : HasDiffOrderReg R n Q) : HasDiffOrderReg R n (P + Q) :=
  ⟨hasDiffOrder_add hP.1 hQ.1, fun f hf => by
    rw [LinearMap.add_apply]
    exact Submodule.add_mem _ (hP.2 f hf) (hQ.2 f hf)⟩

/-- Scaling by an element of the coefficient ring stays in the filtration over it. -/
theorem hasDiffOrderReg_smul {n : ℕ} (a : R) {P : Module.End L (Lambda L)}
    (hP : HasDiffOrderReg R n P) : HasDiffOrderReg R n (algebraMap R L a • P) :=
  ⟨hasDiffOrder_smul _ hP.1, fun f hf => by
    rw [LinearMap.smul_apply, algebraMap_smul_eq]
    exact Submodule.smul_mem _ _ (hP.2 f hf)⟩

/-- A finite sum stays in the filtration over the coefficient ring. -/
theorem hasDiffOrderReg_sum {ι : Type*} {n : ℕ} {s : Finset ι} {F : ι → Module.End L (Lambda L)}
    (h : ∀ i ∈ s, HasDiffOrderReg R n (F i)) : HasDiffOrderReg R n (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simpa using hasDiffOrderReg_zero n
  | cons a s ha ih =>
    rw [Finset.sum_cons]
    exact hasDiffOrderReg_add (h a (by simp)) (ih fun i hi => h i (by simp [hi]))

/-- Composition adds differential orders over the coefficient ring. -/
theorem hasDiffOrderReg_mul {r s : ℕ} {P Q : Module.End L (Lambda L)}
    (hP : HasDiffOrderReg R r P) (hQ : HasDiffOrderReg R s Q) :
    HasDiffOrderReg R (r + s) (P * Q) :=
  ⟨hasDiffOrder_mul hP.1 hQ.1, fun f hf => by
    rw [Module.End.mul_apply]
    exact hP.2 _ (hQ.2 f hf)⟩

/-- The commutator drop over the coefficient ring. -/
theorem hasDiffOrderReg_commutator {n r s : ℕ} (hrs : r + s ≤ n + 1)
    {P Q : Module.End L (Lambda L)} (hP : HasDiffOrderReg R r P) (hQ : HasDiffOrderReg R s Q) :
    HasDiffOrderReg R n (P * Q - Q * P) :=
  ⟨hasDiffOrder_commutator hrs hP.1 hQ.1, fun f hf => by
    rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply]
    exact Submodule.sub_mem _ (hP.2 _ (hQ.2 f hf)) (hQ.2 _ (hP.2 f hf))⟩

/-- The operators of differential order zero over the coefficient ring are exactly the
multiplications by a symmetric function with coefficients in `R`. -/
theorem exists_mulLeft_of_hasDiffOrderReg_zero {P : Module.End L (Lambda L)}
    (hP : HasDiffOrderReg R 0 P) : ∃ g : Lambda R, P = LinearMap.mulLeft L (coeffInc R L g) := by
  obtain ⟨g, hg⟩ := mem_regSub.mp (hP.2 1 one_mem_regSub)
  exact ⟨g, by rw [eq_mulLeft_of_hasDiffOrder_zero hP.1, hg]⟩

end Reg

section RegRees

open HJO.ReesRegular

/-- The order-filtered algebra of operators with coefficients over `R`, built on the commutator
filtration: those `P` admitting an expansion `P = ∑_{j ≥ 0} ℏ ^ j * P j` in `ℏ = 1 - u` whose
`ℏ ^ j`-coefficient has differential order at most `j` and is defined over `R`. -/
@[hjo "def_rees"]
def ReesRegComm (R : Type*) [CommRing R] (L : Type*) [Field L] [Algebra R L] (u : R) :
    Set (Module.End L (Lambda L)) :=
  {P | ∃ Q : ℕ → Module.End L (Lambda L), (∀ j, HasDiffOrderReg R j (Q j)) ∧
    ∀ f : Lambda L, ∃ N : ℕ, (∀ j, N ≤ j → Q j f = 0) ∧
      P f = ∑ j ∈ range N, (1 - algebraMap R L u) ^ j • Q j f}

variable {R : Type*} [CommRing R] {L : Type*} [Field L] [Algebra R L]

/-- Tracking the coefficient ring refines the commutator filtration. -/
theorem reesRegComm_subset_reesComm (u : R) :
    ReesRegComm R L u ⊆ ReesComm (algebraMap R L u) := by
  rintro P ⟨Q, hord, hsum⟩
  exact ⟨Q, fun j => (hord j).1, hsum⟩

/-- An operator of the filtration over the coefficient ring carries symmetric functions with
coefficients in `R` to symmetric functions with coefficients in `R`. -/
theorem apply_mem_regSub_of_mem_reesRegComm {u : R} {P : Module.End L (Lambda L)}
    (hP : P ∈ ReesRegComm R L u) {x : Lambda L} (hx : x ∈ regSub R L) : P x ∈ regSub R L := by
  obtain ⟨Q, hord, hsum⟩ := hP
  obtain ⟨N, -, heq⟩ := hsum x
  rw [heq]
  refine Submodule.sum_mem _ fun j _ => ?_
  have hpow : ((1 : L) - algebraMap R L u) ^ j = algebraMap R L ((1 - u) ^ j) := by
    rw [map_pow, map_sub, map_one]
  rw [hpow, algebraMap_smul_eq]
  exact Submodule.smul_mem _ _ ((hord j).2 x hx)

end RegRees

section RegDop

open HJO.ReesRegular HJO.DopRees

variable {R : Type*} [CommRing R] [Algebra ℚ R] {L : Type*} [Field L] [Algebra ℚ L]
  [Algebra R L] [IsScalarTower ℚ R L]

/-- A rational constant is defined over the coefficient ring, that ring being a `ℚ`-algebra
compatible with the base. -/
theorem C_algebraMap_rat_mem_regSub (x : ℚ) :
    MvPolynomial.C (algebraMap ℚ L x) ∈ regSub R L := by
  have h : MvPolynomial.C (algebraMap ℚ L x)
      = coeffInc R L (MvPolynomial.C (algebraMap ℚ R x)) := by
    rw [coeffInc_apply, MvPolynomial.map_C, ← IsScalarTower.algebraMap_apply]
  rw [h]
  exact coeffInc_mem_regSub _

/-- The elementary symmetric functions have coefficients in the coefficient ring: Newton's identity
expresses them in the power sums with rational coefficients. -/
theorem elemSymm_mem_regSub (n : ℕ) : elemSymm L n ∈ regSub R L := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 =>
      rw [elemSymm]
      exact one_mem_regSub
    | m + 1 =>
      rw [elemSymm]
      refine mul_mem_regSub (C_algebraMap_rat_mem_regSub _) (Submodule.sum_mem _ fun k hk => ?_)
      simp only [Finset.mem_range] at hk
      exact mul_mem_regSub (mul_mem_regSub (neg_one_pow_mem_regSub _) (powerSum_mem_regSub _))
        (ih (m - k) (by omega))

/-- The inverse of a positive natural number comes from the coefficient ring. -/
theorem algebraMap_inv_natCast_succ (m : ℕ) :
    algebraMap R L (algebraMap ℚ R ((m + 1 : ℚ)⁻¹)) = ((m : L) + 1)⁻¹ := by
  rw [← IsScalarTower.algebraMap_apply, map_inv₀, map_add, map_natCast, map_one]

omit [Algebra ℚ R] [Algebra ℚ L] [IsScalarTower ℚ R L] in
/-- The reduced chain-rule weight of parameters from the coefficient ring lies in that ring. -/
theorem chainScalarRed_algebraMap (q u : R) (i : ℕ) :
    chainScalarRed (algebraMap R L q) (algebraMap R L u) i
      = algebraMap R L (chainScalarRed q u i) := by
  simp only [chainScalarRed, shiftScalarRed, map_mul, map_add, map_sub, map_one, map_pow,
    map_sum, map_natCast]

/-- The graded coefficients of a displacement with parameters in the coefficient ring preserve the
symmetric functions with coefficients in `R`: their scalars are the reduced chain-rule weights and
the inverses of natural numbers, all defined over `R`. -/
theorem gradedCoeff_mem_regSub (q u : R) : ∀ (j d : ℕ) {x : Lambda L}, x ∈ regSub R L →
    gradedCoeff (algebraMap R L q) (algebraMap R L u) j d x ∈ regSub R L := by
  intro j
  induction j with
  | zero =>
    intro d x hx
    match d with
    | 0 => rw [gradedCoeff_zero_zero]; simpa using hx
    | m + 1 => rw [gradedCoeff_zero_succ]; simp
  | succ j ih =>
    intro d x hx
    match d with
    | 0 => rw [gradedCoeff_succ_zero]; simp
    | m + 1 =>
      rw [gradedCoeff_succ_succ, LinearMap.smul_apply, LinearMap.sum_apply,
        ← algebraMap_inv_natCast_succ (R := R) m, algebraMap_smul_eq]
      refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => ?_)
      rw [LinearMap.smul_apply, chainScalarRed_algebraMap, algebraMap_smul_eq]
      refine Submodule.smul_mem _ _ ?_
      rw [Module.End.mul_apply]
      exact ih (m - i) (pderivEnd_mem_regSub i hx)

/-- The `ℏ ^ j`-coefficient of a basic operator with parameters in the coefficient ring preserves
the symmetric functions with coefficients in `R`. -/
theorem dopGraded_mem_regSub (q u : R) (k j : ℕ) {x : Lambda L} (hx : x ∈ regSub R L) :
    dopGraded (algebraMap R L q) (algebraMap R L u) k j x ∈ regSub R L := by
  rw [dopGraded_apply _ _ k j (show wtDeg x < wtDeg x + 1 from by omega), dopGradedTrunc,
    LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun d _ => ?_
  rw [Module.End.mul_apply, LinearMap.mulLeft_apply]
  exact mul_mem_regSub (mul_mem_regSub (neg_one_pow_mem_regSub _) (elemSymm_mem_regSub _))
    (gradedCoeff_mem_regSub q u j d hx)

/-- The basic operators with parameters in the coefficient ring lie in the order filtration over
that ring built on the commutator definition: the coefficient of `ℏ ^ j` in the expansion by number
of derivatives has differential order at most `j` and is defined over `R`. -/
@[hjo "lem_dop_rees"]
theorem dop_mem_reesRegComm (q u : R) (k : ℕ) :
    Dop (algebraMap R L q) (algebraMap R L u) k ∈ ReesRegComm R L u :=
  ⟨fun j => dopGraded (algebraMap R L q) (algebraMap R L u) k j,
    fun j => ⟨hasDiffOrder_dopGraded _ _ k j, fun _ hf => dopGraded_mem_regSub q u k j hf⟩,
    fun f => ⟨wtDeg f + 1, fun j hj => dopGraded_apply_eq_zero _ _ k j f (by omega),
      dop_apply_eq_sum_dopGraded _ _ k f⟩⟩

end RegDop

end HJO.DiffOrder
