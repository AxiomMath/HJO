/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Symmetric.AxisFree
public meta import HJO.Attr

/-! # The degree grading of the operators on symmetric functions

The chain that proves the shuffle element `(-1)^{N(b+1)} Θ(C_α 1) 1` homogeneous of degree `bN`,
which is the first of the two clauses of `HJO.External.Shuffle`. That clause is not quoted from the
literature; only the expansion over parking functions is, and
`HJO.ShuffleNarrowed` states the quoted half alone.

The vocabulary is `ShiftsDegree`: an endomorphism of `Lambda K` shifts degree by `c ∈ ℤ` when it
carries `Λ_d` into `Λ_{d+c}` for every `d`, with `Λ_e` read as the zero subspace for `e < 0`. That
reading is `LambdaCompInt`, the graded pieces re-indexed by `ℤ`. Shifts compose, and the
endomorphisms shifting a fixed degree form a subspace, which is what lets the commutator defining
the slope operators be handled one summand at a time.

Two gradings are then transported along algebra homomorphisms out of `Lambda K`, by the single
lemma `mem_of_mem_lambdaComp`: it needs of the target only a `ℤ`-indexed family of submodules
containing `1` in index `0` and multiplicative in the index, and of the homomorphism only that it
send the generator `p_{i+1}` into index `i + 1`. Its first use is `PolyComp`, the grading of
`Polynomial (Lambda K)` in which the displacement variable `w = z⁻¹` has degree `-1`; that makes
both plethystic displacements graded, and pairing off a displacement against a graded family then
gives the degree shifts of `Dop` and of `Cop`. Its second use is `degreeShifting` itself, which is
where free generation by the axis generators enters: `IsSlopeHom` pins a slope homomorphism only on
the axis generators, so nothing at all is known about `Θ f` for general `f` without
`HJO.Sym.axisSub_bijective`. Composing `Θ` with the axis substitution gives a homomorphism sending
`p_{i+1}` to `Q_{a(i+1), b(i+1)}`, and the degree shift of the slope operators is an induction along
the recursion defining them.

The only hypotheses on the parameters are the two that free generation needs, that `v = q u` is
nonzero and not a root of unity, and they enter exactly at the slope homomorphism.
-/

@[expose] public section

open Finset MvPolynomial

namespace HJO.Sym

section CommRing

variable {K : Type*} [CommRing K]

/-! ### The graded pieces at an integer degree -/

/-- The graded piece of `Lambda K` at an integer degree: `Λ_e` for `e ≥ 0`, and the zero
subspace for `e < 0`, which is the convention of reading `Λ_e` as `0` below
degree zero. -/
noncomputable def LambdaCompInt (K : Type*) [CommRing K] (e : ℤ) : Submodule K (Lambda K) :=
  if 0 ≤ e then LambdaComp K e.toNat else ⊥

theorem lambdaCompInt_natCast (K : Type*) [CommRing K] (d : ℕ) :
    LambdaCompInt K (d : ℤ) = LambdaComp K d := by
  rw [LambdaCompInt]
  split_ifs with h
  · rw [Int.toNat_natCast]
  · exact absurd (Int.natCast_nonneg d) h

theorem eq_zero_of_mem_lambdaCompInt {e : ℤ} (he : e < 0) {f : Lambda K}
    (hf : f ∈ LambdaCompInt K e) : f = 0 := by
  rw [LambdaCompInt] at hf
  split_ifs at hf with h
  · exact absurd h (by omega)
  · simpa using hf

theorem lambdaCompInt_zero (K : Type*) [CommRing K] :
    LambdaCompInt K 0 = LambdaComp K 0 := by
  rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) by norm_num, lambdaCompInt_natCast]

theorem one_mem_lambdaCompInt (K : Type*) [CommRing K] : (1 : Lambda K) ∈ LambdaCompInt K 0 := by
  rw [lambdaCompInt_zero, mem_lambdaComp]
  exact isWeightedHomogeneous_one K _

theorem mul_mem_lambdaCompInt {c c' : ℤ} {f g : Lambda K} (hf : f ∈ LambdaCompInt K c)
    (hg : g ∈ LambdaCompInt K c') : f * g ∈ LambdaCompInt K (c + c') := by
  rcases lt_or_ge c 0 with hc | hc
  · rw [eq_zero_of_mem_lambdaCompInt hc hf, zero_mul]; exact zero_mem _
  rcases lt_or_ge c' 0 with hc' | hc'
  · rw [eq_zero_of_mem_lambdaCompInt hc' hg, mul_zero]; exact zero_mem _
  lift c to ℕ using hc with d
  lift c' to ℕ using hc' with d'
  rw [lambdaCompInt_natCast] at hf hg
  rw [← Nat.cast_add, lambdaCompInt_natCast]
  exact mul_mem_lambdaComp hf hg

/-- The power sum `p_{i+1}` is the generator `i`, homogeneous of degree `i + 1`. -/
theorem powerSum_mem_lambdaComp (K : Type*) [CommRing K] (i : ℕ) :
    powerSum K (i + 1) ∈ LambdaComp K (i + 1) := by
  rw [mem_lambdaComp, powerSum, Nat.add_sub_cancel]
  exact isWeightedHomogeneous_X K _ i

/-- A constant is homogeneous of degree zero. -/
theorem C_mem_lambdaComp (K : Type*) [CommRing K] (r : K) :
    (MvPolynomial.C r : Lambda K) ∈ LambdaComp K 0 :=
  isWeightedHomogeneous_C _ _

/-- A power of `-1` is homogeneous of degree zero. -/
theorem neg_one_pow_mem_lambdaComp (K : Type*) [CommRing K] (m : ℕ) :
    ((-1 : Lambda K) ^ m) ∈ LambdaComp K 0 := by
  rw [show ((-1 : Lambda K)) = MvPolynomial.C (-1 : K) by simp, ← MvPolynomial.C_pow]
  exact C_mem_lambdaComp K _

/-! ### Transporting the grading along an algebra homomorphism -/

section Graded

variable {A : Type*} [Ring A] [Algebra K A]

/-- **A graded target receives the grading of `Lambda K`.** Let `G` be a family of
`K`-submodules of a `K`-algebra `A`, indexed by `ℤ`, containing `1` in index `0` and
multiplicative in the index. An algebra homomorphism `φ : Lambda K → A` sending each generator
`p_{i+1}` into `G (i + 1)` then sends `Λ_d` into `G d`: a homogeneous element of degree `d` is a
`K`-combination of monomials whose generators' weights sum to `d`. -/
theorem mem_of_mem_lambdaComp (G : ℤ → Submodule K A) (hone : (1 : A) ∈ G 0)
    (hmul : ∀ {c c' : ℤ} {x y : A}, x ∈ G c → y ∈ G c' → x * y ∈ G (c + c'))
    (φ : Lambda K →ₐ[K] A) (hgen : ∀ i : ℕ, φ (MvPolynomial.X i) ∈ G ((i : ℤ) + 1))
    {d : ℕ} {f : Lambda K} (hf : f ∈ LambdaComp K d) : φ f ∈ G (d : ℤ) := by
  have hpow : ∀ (x : A) (c : ℤ) (k : ℕ), x ∈ G c → x ^ k ∈ G ((k : ℤ) * c) := by
    intro x c k hx
    induction k with
    | zero => simpa using hone
    | succ n ih =>
      have h2 := hmul ih hx
      rw [show ((n : ℤ) * c + c) = ((n + 1 : ℕ) : ℤ) * c by push_cast; ring] at h2
      rw [pow_succ]
      exact h2
  have hprod : ∀ (s : Finset ℕ) (c : ℕ → ℕ),
      φ (∏ i ∈ s, (MvPolynomial.X i : Lambda K) ^ c i) ∈
        G (∑ i ∈ s, (c i : ℤ) * ((i : ℤ) + 1)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; simpa using hone
    | insert a s ha ih =>
      intro c
      rw [Finset.prod_insert ha, Finset.sum_insert ha, map_mul, map_pow]
      exact hmul (hpow _ _ _ (hgen a)) (ih c)
  refine IsWeightedHomogeneous.induction_on (motive := fun p _ => φ p ∈ G (d : ℤ)) ?_ ?_ ?_
    (mem_lambdaComp.1 hf)
  · rw [map_zero]; exact zero_mem _
  · intro p q _ _ hp hq
    rw [map_add]
    exact add_mem hp hq
  · intro e r hr
    have hC : φ (MvPolynomial.C r) = algebraMap K A r := by
      rw [← MvPolynomial.algebraMap_eq]; exact φ.commutes r
    have hw : ∑ i ∈ e.support, ((e i : ℤ) * ((i : ℤ) + 1)) = (d : ℤ) := by
      rw [← hr, Finsupp.weight_apply, Finsupp.sum, Nat.cast_sum]
      exact Finset.sum_congr rfl fun i _ => by push_cast [smul_eq_mul]; ring
    rw [monomial_eq, map_mul, hC, ← Algebra.smul_def]
    refine Submodule.smul_mem _ r ?_
    rw [Finsupp.prod, ← hw]
    exact hprod e.support e

end Graded

/-! ### Degree-shifting endomorphisms -/

/-- **A degree-shifting endomorphism.** A `K`-linear endomorphism `D` of `Lambda K` *shifts
degree by* `c ∈ ℤ` if it carries `Λ_d` into `Λ_{d+c}` for every `d ≥ 0`, with `Λ_e` read as the
zero subspace for `e < 0`. -/
@[hjo "def_degree_shifting"]
def ShiftsDegree (c : ℤ) (D : Module.End K (Lambda K)) : Prop :=
  ∀ d : ℕ, ∀ f ∈ LambdaComp K d, D f ∈ LambdaCompInt K ((d : ℤ) + c)

/-- **Degree shifts compose.** A composite of endomorphisms shifting by `c` and by `c'` shifts by
`c + c'`: the inner map lands in `Λ_{d+c'}` and the outer one carries that into `Λ_{d+c'+c}`,
the intermediate piece being the zero subspace when `d + c' < 0`. -/
@[hjo "lem_degree_shifting_comp"]
theorem ShiftsDegree.comp {c c' : ℤ} {D D' : Module.End K (Lambda K)} (hD : ShiftsDegree c D)
    (hD' : ShiftsDegree c' D') : ShiftsDegree (c + c') (D * D') := by
  intro d f hf
  have h1 := hD' d f hf
  change D (D' f) ∈ _
  rcases lt_or_ge ((d : ℤ) + c') 0 with h | h
  · rw [eq_zero_of_mem_lambdaCompInt h h1, map_zero]
    exact zero_mem _
  · obtain ⟨e, he⟩ : ∃ e : ℕ, ((d : ℤ) + c') = (e : ℤ) :=
      ⟨((d : ℤ) + c').toNat, (Int.toNat_of_nonneg h).symm⟩
    rw [he, lambdaCompInt_natCast] at h1
    have h2 := hD e _ h1
    rwa [show (e : ℤ) + c = (d : ℤ) + (c + c') by omega] at h2

/-- **The ℕ-graded reading of a nonnegative degree shift.** For `D` shifting degree by `c : ℕ`
and `f ∈ Λ_d`, the image `D f` lies in `Λ_{d+c}` with the piece indexed by a natural number. The
two readings are definitionally equal, so the body is the application itself; the lemma exists
because `LambdaCompInt` does not unfold at reducible transparency, which is what `simp` and `rw`
work at, so without it the ℕ-form is reachable only by a bare application whose index has to match
syntactically. -/
theorem ShiftsDegree.apply_mem_lambdaComp {c : ℕ} {D : Module.End K (Lambda K)}
    (hD : ShiftsDegree (c : ℤ) D) {d : ℕ} {f : Lambda K} (hf : f ∈ LambdaComp K d) :
    D f ∈ LambdaComp K (d + c) := hD d f hf

/-- The identity shifts degree by zero. -/
theorem shiftsDegree_one : ShiftsDegree (0 : ℤ) (1 : Module.End K (Lambda K)) := by
  intro d f hf
  rw [add_zero, lambdaCompInt_natCast]
  exact hf

/-- **The endomorphisms shifting a fixed degree form a subspace.** Each `Λ_e` is a `K`-subspace,
read as the zero subspace below degree zero, so the endomorphisms carrying `Λ_d` into `Λ_{d+c}`
for every `d` contain `0` and are closed under addition and under the `K`-action. -/
@[hjo "lem_degree_shifting_linear"]
noncomputable def degreeShifting (K : Type*) [CommRing K] (c : ℤ) :
    Submodule K (Module.End K (Lambda K)) where
  carrier := {D | ShiftsDegree c D}
  zero_mem' := by intro d f _; rw [LinearMap.zero_apply]; exact zero_mem _
  add_mem' := by
    intro D D' hD hD' d f hf
    rw [LinearMap.add_apply]
    exact add_mem (hD d f hf) (hD' d f hf)
  smul_mem' := by
    intro r D hD d f hf
    rw [LinearMap.smul_apply]
    exact Submodule.smul_mem _ r (hD d f hf)

theorem mem_degreeShifting {c : ℤ} {D : Module.End K (Lambda K)} :
    D ∈ degreeShifting K c ↔ ShiftsDegree c D := Iff.rfl

/-- **A scalar multiple of a commutator shifts the sum of the two degrees.** Both composites
`D D'` and `D' D` shift by `c + c'`, and the endomorphisms shifting a fixed degree form a
subspace, so it absorbs their difference and the scalar. This is the shape of every recursive
step of the slope operators, whose value is a normalised commutator of two halves of a split. -/
theorem smul_commutator_shiftsDegree {c c' : ℤ} (r : K) {D D' : Module.End K (Lambda K)}
    (hD : ShiftsDegree c D) (hD' : ShiftsDegree c' D') :
    ShiftsDegree (c + c') (r • (D * D' - D' * D)) := by
  refine Submodule.smul_mem (degreeShifting K (c + c')) r (sub_mem (hD.comp hD') ?_)
  rw [mem_degreeShifting, add_comm c c']
  exact hD'.comp hD

/-! ### The grading of the displacement polynomials -/

/-- The graded pieces of `Polynomial (Lambda K)`, the ambient ring of the plethystic
displacements, for the grading in which the variable `w = z⁻¹` has degree `-1`: a polynomial lies
in the piece of degree `d` when its coefficient of `wʲ` lies in `Λ_{d-j}` for every `j`. -/
noncomputable def PolyComp (K : Type*) [CommRing K] (d : ℤ) :
    Submodule K (Polynomial (Lambda K)) where
  carrier := {P | ∀ j : ℕ, P.coeff j ∈ LambdaCompInt K (d - j)}
  zero_mem' := by intro j; rw [Polynomial.coeff_zero]; exact zero_mem _
  add_mem' := by
    intro P Q hP hQ j
    rw [Polynomial.coeff_add]
    exact add_mem (hP j) (hQ j)
  smul_mem' := by
    intro r P hP j
    rw [Polynomial.coeff_smul]
    exact Submodule.smul_mem _ r (hP j)

theorem mem_polyComp {d : ℤ} {P : Polynomial (Lambda K)} :
    P ∈ PolyComp K d ↔ ∀ j : ℕ, P.coeff j ∈ LambdaCompInt K (d - j) := Iff.rfl

theorem one_mem_polyComp (K : Type*) [CommRing K] :
    (1 : Polynomial (Lambda K)) ∈ PolyComp K 0 := by
  intro j
  rw [Polynomial.coeff_one]
  split_ifs with h
  · subst h
    simpa using one_mem_lambdaCompInt K
  · exact zero_mem _

theorem mul_mem_polyComp {d d' : ℤ} {P Q : Polynomial (Lambda K)} (hP : P ∈ PolyComp K d)
    (hQ : Q ∈ PolyComp K d') : P * Q ∈ PolyComp K (d + d') := by
  intro n
  rw [Polynomial.coeff_mul]
  refine Submodule.sum_mem _ fun x hx => ?_
  have hx' : x.1 + x.2 = n := Finset.mem_antidiagonal.1 hx
  have h := mul_mem_lambdaCompInt (hP x.1) (hQ x.2)
  rwa [show d - (x.1 : ℤ) + (d' - (x.2 : ℤ)) = d + d' - (n : ℤ) by
    rw [← hx']; push_cast; ring] at h

theorem C_mem_polyComp {d : ℤ} {g : Lambda K} (hg : g ∈ LambdaCompInt K d) :
    Polynomial.C g ∈ PolyComp K d := by
  intro j
  rw [Polynomial.coeff_C]
  split_ifs with h
  · subst h
    simpa using hg
  · exact zero_mem _

theorem X_pow_mem_polyComp (K : Type*) [CommRing K] (n : ℕ) :
    (Polynomial.X ^ n : Polynomial (Lambda K)) ∈ PolyComp K (n : ℤ) := by
  intro j
  rw [Polynomial.coeff_X_pow]
  split_ifs with h
  · subst h
    simpa using one_mem_lambdaCompInt K
  · exact zero_mem _

/-- **Pairing off the displacement.** If `P` has displacement degree `d` and the family `c` has
`c j ∈ Λ_{e+j}` for every `j`, then pairing `P` against `c` lands in `Λ_{d+e}`: the term at `j`
is a product of an element of `Λ_{d-j}` by one of `Λ_{e+j}`. -/
theorem coeffPairing_mem_lambdaCompInt {e d : ℤ} {c : ℕ → Lambda K}
    (hc : ∀ j : ℕ, c j ∈ LambdaCompInt K (e + j)) {P : Polynomial (Lambda K)}
    (hP : P ∈ PolyComp K d) : coeffPairing c P ∈ LambdaCompInt K (d + e) := by
  change P.sum (fun j A => A * c j) ∈ _
  rw [Polynomial.sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  have h := mul_mem_lambdaCompInt (hP j) (hc j)
  rwa [show d - (j : ℤ) + (e + (j : ℤ)) = d + e by ring] at h

/-! ### The plethystic displacements are graded -/

/-- **The plethystic displacement is graded.** For `f ∈ Λ_d` the coefficient of `wʲ` in
`f[X + M/z]` lies in `Λ_{d-j}`: the displacement is an algebra homomorphism sending the generator
`p_{i+1}` to `p_{i+1} + M_{i+1} w^{i+1}`, whose two terms have displacement degree `i + 1`. -/
theorem plethShift_mem_polyComp (q u : K) {d : ℕ} {f : Lambda K} (hf : f ∈ LambdaComp K d) :
    plethShift q u f ∈ PolyComp K (d : ℤ) := by
  refine mem_of_mem_lambdaComp (PolyComp K) (one_mem_polyComp K)
    (fun hx hy => mul_mem_polyComp hx hy) (plethShift q u) (fun i => ?_) hf
  rw [plethShift, MvPolynomial.aeval_X]
  have hcast : ((i : ℤ) + 1) = ((i + 1 : ℕ) : ℤ) := by push_cast; ring
  refine add_mem (C_mem_polyComp ?_) ?_
  · rw [hcast, lambdaCompInt_natCast]
    exact powerSum_mem_lambdaComp K i
  · have hC : (MvPolynomial.C ((1 - q ^ (i + 1)) * (1 - u ^ (i + 1))) : Lambda K) ∈
        LambdaCompInt K 0 := by
      rw [lambdaCompInt_zero]
      exact C_mem_lambdaComp K _
    have h := mul_mem_polyComp (C_mem_polyComp hC) (X_pow_mem_polyComp K (i + 1))
    rwa [zero_add, ← hcast] at h

/-- **The creation displacement is graded.** For `f ∈ Λ_d` the coefficient of `wʲ` in
`f[X - (1-q⁻¹)/z]` lies in `Λ_{d-j}`, by the same reading of the generators as for
`plethShift`. -/
theorem plethCreate_mem_polyComp {L : Type*} [Field L] [Algebra ℚ L] (q : L) {d : ℕ}
    {f : Lambda L} (hf : f ∈ LambdaComp L d) : plethCreate q f ∈ PolyComp L (d : ℤ) := by
  refine mem_of_mem_lambdaComp (PolyComp L) (one_mem_polyComp L)
    (fun hx hy => mul_mem_polyComp hx hy) (plethCreate q) (fun i => ?_) hf
  rw [plethCreate, MvPolynomial.aeval_X]
  have hcast : ((i : ℤ) + 1) = ((i + 1 : ℕ) : ℤ) := by push_cast; ring
  refine sub_mem (C_mem_polyComp ?_) ?_
  · rw [hcast, lambdaCompInt_natCast]
    exact powerSum_mem_lambdaComp L i
  · have hC : (MvPolynomial.C (1 - (q ^ (i + 1))⁻¹) : Lambda L) ∈ LambdaCompInt L 0 := by
      rw [lambdaCompInt_zero]
      exact C_mem_lambdaComp L _
    have h := mul_mem_polyComp (C_mem_polyComp hC) (X_pow_mem_polyComp L (i + 1))
    rwa [zero_add, ← hcast] at h

end CommRing

section Newton

variable {K : Type*} [CommRing K] [Algebra ℚ K]

/-- **Homogeneity of the elementary symmetric functions.** Newton's identity writes `e_n` as a
combination of the products `p_k e_{n-k}`, whose parts sum to `n`. This is
`HJO.Sym.elemSymm_mem_lambdaComp`. `HJO.PhiE.isWeightedHomogeneous_elemSymm` is the same fact for
`degWeight` and `HJO.Bglx.isWeightedHomogeneous_elemSymm` is it at the weight used here; the Newton
argument is repeated rather than importing either, which would make this file depend on a part of
the library it is otherwise independent of.

The statement is exactly `e_n ∈ Λ_n`. -/
@[hjo "lem_esymm_component"]
theorem elemSymm_mem_lambdaComp (K : Type*) [CommRing K] [Algebra ℚ K] (n : ℕ) :
    elemSymm K n ∈ LambdaComp K n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rw [elemSymm, mem_lambdaComp]; exact isWeightedHomogeneous_one K _
    | m + 1 =>
      rw [elemSymm, mem_lambdaComp]
      refine IsWeightedHomogeneous.C_mul (IsWeightedHomogeneous.sum _ _ _ fun k hk => ?_) _
      rw [Finset.mem_range, Nat.lt_succ_iff] at hk
      have h1 : IsWeightedHomogeneous (fun i => i + 1)
          ((-1 : Lambda K) ^ k * powerSum K (k + 1)) (k + 1) := by
        have h0 : IsWeightedHomogeneous (fun i => i + 1) ((-1 : Lambda K) ^ k) 0 :=
          mem_lambdaComp.1 (neg_one_pow_mem_lambdaComp K k)
        have h1 : IsWeightedHomogeneous (fun i => i + 1) (powerSum K (k + 1)) (k + 1) :=
          mem_lambdaComp.1 (powerSum_mem_lambdaComp K k)
        simpa using h0.mul h1
      have h2 : IsWeightedHomogeneous (fun i => i + 1) (elemSymm K (m - k)) (m - k) :=
        mem_lambdaComp.1 (ih (m - k) (by omega))
      have h3 : k + 1 + (m - k) = m + 1 := by omega
      exact h3 ▸ h1.mul h2

/-- **The basic operators shift degree.** For `f ∈ Λ_d` the operator `Dop q u k` pairs the
coefficient of `wʲ` in `f[X + M/z]`, which lies in `Λ_{d-j}`, against `(-1)^{k+j} e_{k+j}`, which
lies in `Λ_{k+j}`; every term of the pairing therefore lies in `Λ_{d+k}`. -/
@[hjo "lem_dop_degree_shift"]
theorem dop_shiftsDegree (q u : K) (k : ℕ) : ShiftsDegree (k : ℤ) (Dop q u k) := by
  intro d f hf
  change coeffPairing (fun j => (-1) ^ (k + j) * elemSymm K (k + j)) (plethShift q u f) ∈ _
  refine coeffPairing_mem_lambdaCompInt (e := (k : ℤ)) (fun j => ?_)
    (plethShift_mem_polyComp q u hf)
  have hsign : ((-1 : Lambda K) ^ (k + j)) ∈ LambdaCompInt K 0 := by
    rw [lambdaCompInt_zero]
    exact neg_one_pow_mem_lambdaComp K (k + j)
  have he : elemSymm K (k + j) ∈ LambdaCompInt K ((k + j : ℕ) : ℤ) := by
    rw [lambdaCompInt_natCast]
    exact elemSymm_mem_lambdaComp K (k + j)
  have h := mul_mem_lambdaCompInt hsign he
  rwa [zero_add, show ((k + j : ℕ) : ℤ) = (k : ℤ) + (j : ℤ) by push_cast; ring] at h

end Newton

section Field

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **The creation operators shift degree by the index.** For `f ∈ Λ_d` the operator `Cop q r`
pairs the coefficient of `wʲ` in `f[X - (1-q⁻¹)/z]`, which lies in `Λ_{d-j}`, against the scalar
multiple of `h_{r+j}`, which lies in `Λ_{r+j}`; every term of the pairing therefore lies in
`Λ_{d+r}`. It is usually stated for `r ≥ 1`; the argument needs no positivity, the prefactor
`(-q)^{1-r}` being a constant at every `r`. -/
@[hjo "lem_cop_degree_shift"]
theorem cop_shiftsDegree (q : L) (r : ℕ) : ShiftsDegree (r : ℤ) (Cop q r) := by
  intro d f hf
  change coeffPairing (fun j => MvPolynomial.C ((-q) ^ (1 - (r : ℤ))) * completeHomog L (r + j))
    (plethCreate q f) ∈ _
  refine coeffPairing_mem_lambdaCompInt (e := (r : ℤ)) (fun j => ?_)
    (plethCreate_mem_polyComp q hf)
  have hpre : (MvPolynomial.C ((-q) ^ (1 - (r : ℤ))) : Lambda L) ∈ LambdaCompInt L 0 := by
    rw [lambdaCompInt_zero]
    exact C_mem_lambdaComp L _
  have hh : completeHomog L (r + j) ∈ LambdaCompInt L ((r + j : ℕ) : ℤ) := by
    rw [lambdaCompInt_natCast]
    exact completeHomog_mem_lambdaComp L (r + j)
  have h := mul_mem_lambdaCompInt hpre hh
  rwa [zero_add, show ((r + j : ℕ) : ℤ) = (r : ℤ) + (j : ℤ) by push_cast; ring] at h

/-- **Every stage of the fuelled recursion shifts degree by its second index.** Induction on the
fuel, uniform in both indices: at zero fuel and at width one the stage is the basic operator
`D_n`, and a further unit of fuel produces a normalised commutator of the two halves of the split
of `(m, n)`, whose second indices `n - s` and `s` add up to `n` because `s = (Split m n).2` never
exceeds `n`. No step asks anything of the first index, so no positivity and no coprimality enter.
-/
theorem qopAux_shiftsDegree (q u : L) (fuel m n : ℕ) :
    ShiftsDegree (n : ℤ) (QopAux q u fuel m n) := by
  induction fuel generalizing m n with
  | zero => rw [qopAux_zero]; exact dop_shiftsDegree q u n
  | succ fuel ih =>
    rw [qopAux_succ_def]
    split_ifs with hm
    · exact dop_shiftsDegree q u n
    · have h := smul_commutator_shiftsDegree ((1 - q) * (1 - u))⁻¹ (ih (m - splitFst m n)
        (n - (Split m n).2)) (ih (splitFst m n) (Split m n).2)
      rwa [show ((n - (Split m n).2 : ℕ) : ℤ) + (((Split m n).2 : ℕ) : ℤ) = (n : ℤ) by
        have := split_snd_le m n; omega] at h

/-- **The primitive evaluator shifts degree by the second index.** -/
theorem qopPrim_shiftsDegree (q u : L) (m n : ℕ) : ShiftsDegree (n : ℤ) (QopPrim q u m n) :=
  qopAux_shiftsDegree q u m m n

/-- **The slope operators shift degree by the second index.** `Q_{m,n}` carries `Λ_d` into
`Λ_{d+n}` for every `d ≥ 0`. Each of the three branches of `Qop` is either the basic operator
`D_n` or a normalised commutator of primitive evaluators at the two halves of a split, whose
second indices `n - s` and `s` add up to `n` because `s` never exceeds `n`.

The statement is usually made for `m ≥ 1` together with `n ≥ 1 or m = 1`. Neither is needed: the
degree count uses only the bound on a split's second entry, which holds at every pair, so the
statement here is unconditional and also covers the totalised values at `m = 0` and at `n = 0`. -/
@[hjo "lem_qop_degree_shift"]
theorem qop_shiftsDegree (q u : L) (m n : ℕ) : ShiftsDegree (n : ℤ) (Qop q u m n) := by
  rw [Qop]
  split_ifs
  · exact dop_shiftsDegree q u n
  · exact qopPrim_shiftsDegree q u m n
  · have h := smul_commutator_shiftsDegree ((1 - q) * (1 - u))⁻¹
      (qopPrim_shiftsDegree q u (m - (slopeSplit m n).1) (n - (slopeSplit m n).2))
      (qopPrim_shiftsDegree q u (slopeSplit m n).1 (slopeSplit m n).2)
    rwa [show ((n - (slopeSplit m n).2 : ℕ) : ℤ) + (((slopeSplit m n).2 : ℕ) : ℤ) = (n : ℤ) by
      have := slopeSplit_snd_le m n; omega] at h

/-- **A composite creation operator shifts degree by the size.** Induction on the parts: the
composite of the creation operators of the parts shifts by the sum of the parts. -/
@[hjo "lem_cop_comp_degree_shift"]
theorem copComp_shiftsDegree (q : L) {α : List ℕ} {N : ℕ} (hα : α.sum = N) :
    ShiftsDegree (N : ℤ) (CopComp q α) := by
  subst hα
  induction α with
  | nil =>
    rw [show CopComp q ([] : List ℕ) = 1 from by rw [CopComp, List.map_nil, List.prod_nil]]
    simpa using shiftsDegree_one (K := L)
  | cons a α ih =>
    rw [show CopComp q (a :: α) = Cop q a * CopComp q α from by
      rw [CopComp, CopComp, List.map_cons, List.prod_cons]]
    have h := (cop_shiftsDegree q a).comp ih
    rwa [show (a : ℤ) + ((α.sum : ℕ) : ℤ) = (((a :: α).sum : ℕ) : ℤ) by
      rw [List.sum_cons]; push_cast; ring] at h

/-- **The creation seed is homogeneous.** The unit lies in `Λ_0`, and `Cop_α` shifts degree by the
size of `α`. -/
@[hjo "lem_creation_seed_component"]
theorem copComp_one_mem_lambdaComp (q : L) {α : List ℕ} {N : ℕ} (hα : α.sum = N) :
    CopComp q α 1 ∈ LambdaComp L N := by
  have h1 : (1 : Lambda L) ∈ LambdaComp L 0 := by
    rw [mem_lambdaComp]; exact isWeightedHomogeneous_one L _
  simpa using (copComp_shiftsDegree q hα).apply_mem_lambdaComp h1

/-- **A slope homomorphism scales degree shifts by the second index.** For `f ∈ Λ_d` the operator
`Θ f` shifts degree by `b * d`. This is where free generation by the axis generators enters:
`IsSlopeHom` pins `Θ` only on the axis generators, so `axisSub_bijective` is what makes `Θ f`
known at all. Composing `Θ` with the axis substitution gives an algebra homomorphism sending the
generator `p_{i+1}` to `Q_{a(i+1), b(i+1)}`, which shifts degree by `b(i+1)`.

The `b ≥ 1` is carried in the statement but unused: `qop_shiftsDegree` holds at every
slope, so the degree count never needs the index to be positive. -/
@[hjo "lem_slope_hom_degree_shift"]
theorem isSlopeHom_shiftsDegree [CharZero L] {a b : ℕ} {q u : L} (_hb : 0 < b)
    (hv0 : q * u ≠ 0) (hv1 : ∀ j : ℕ, (q * u) ^ (j + 1) ≠ 1)
    {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)} (hΘ : IsSlopeHom a b q u Θ) {d : ℕ}
    {f : Lambda L} (hf : f ∈ LambdaComp L d) : ShiftsDegree ((b : ℤ) * d) (Θ f) := by
  obtain ⟨g, hg, hgf⟩ := exists_mem_lambdaComp_axisSub_eq hv0 hv1 d hf
  have key : (Θ.comp (axisSub (q * u))) g ∈ degreeShifting L ((b : ℤ) * d) := by
    refine mem_of_mem_lambdaComp (fun c => degreeShifting L ((b : ℤ) * c)) ?_ ?_ _ ?_ hg
    · rw [mul_zero]
      exact shiftsDegree_one
    · intro c c' x y hx hy
      have h := (mem_degreeShifting.1 hx).comp (mem_degreeShifting.1 hy)
      rw [mem_degreeShifting, mul_add]
      exact h
    · intro i
      rw [mem_degreeShifting, AlgHom.coe_comp, Function.comp_apply, axisSub_X,
        hΘ (i + 1) (Nat.succ_pos i)]
      have h := qop_shiftsDegree q u (a * (i + 1)) (b * (i + 1))
      rwa [show ((b * (i + 1) : ℕ) : ℤ) = (b : ℤ) * ((i : ℤ) + 1) by push_cast; ring] at h
  rw [mem_degreeShifting, AlgHom.coe_comp, Function.comp_apply, hgf] at key
  exact key

/-- **The shuffle element is homogeneous of degree `bN`.** The creation seed `C_α 1` lies in
`Λ_N`, so `Θ (C_α 1)` shifts degree by `bN`, and the unit it is applied to lies in `Λ_0`. This is
the first conjunct of `HJO.External.Shuffle`, which is proved rather than quoted. -/
@[hjo "lem_shuffle_homogeneous"]
theorem shuffle_mem_lambdaComp [CharZero L] {a b : ℕ} {q u : L} (hb : 0 < b) (hv0 : q * u ≠ 0)
    (hv1 : ∀ j : ℕ, (q * u) ^ (j + 1) ≠ 1)
    {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)} (hΘ : IsSlopeHom a b q u Θ) {α : List ℕ}
    {N : ℕ} (hα : α.sum = N) :
    (-1 : L) ^ (N * (b + 1)) • Θ (CopComp q α 1) 1 ∈ LambdaComp L (b * N) := by
  have h1 : (1 : Lambda L) ∈ LambdaComp L 0 := by
    rw [mem_lambdaComp]; exact isWeightedHomogeneous_one L _
  have h := isSlopeHom_shiftsDegree hb hv0 hv1 hΘ (copComp_one_mem_lambdaComp q hα) 0 1 h1
  rw [show ((0 : ℕ) : ℤ) + (b : ℤ) * (N : ℤ) = ((b * N : ℕ) : ℤ) by push_cast; ring,
    lambdaCompInt_natCast] at h
  exact Submodule.smul_mem _ _ h

attribute [hjo "lem_asc_shuffle_homogeneous"] shuffle_mem_lambdaComp

end Field

end HJO.Sym
