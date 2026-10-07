/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.Grading
public import HJO.Shuffle.SweepModule
public meta import HJO.Attr

/-! # The degree grading of the sweep's total space

Mellit's Section 3.7 completes the modules `V_k` of `HJO.Sweep.piece` with respect to the grading
in which `p_r` has degree `r` and each `y_i` has degree `1` (`HJO.Sweep.pieceHat`). This file is
that grading, on the total space `HJO.Sweep.Total` inside which every `V_k` is realised: the graded
pieces, their multiplicativity, the transport of the grading along an algebra homomorphism out of
the total space, and the three substitutions of the section that preserve it.

## The shape of the grading

`HJO.Sweep.Total L = MvPolynomial ℕ Λ` carries *two* sets of generators of different degrees — the
auxiliary variables `y_j`, which are the polynomial variables, and the power sums `p_r`, which sit
inside the coefficient ring. So the degree-`d` piece cannot be a weighted homogeneous submodule of
`MvPolynomial ℕ Λ` for any weight on the `y_j` alone. It is defined here coefficientwise: `F` is
homogeneous of degree `d` when, for every `y`-monomial `m`, the coefficient of `m` in `F` lies in
the graded piece `Λ_{d - |m|}` of `HJO.Sym.LambdaComp`, with `|m|` the total degree of `m` and with
`Λ_e` read as the zero subspace for `e < 0` — the convention `HJO.Sym.LambdaCompInt` already fixes.

## Main definitions

* `HJO.Sweep.TotalComp` — the graded piece of degree `d`, and `HJO.Sweep.TotalCompInt` its reading
  at an integer degree.

## Main results

* `HJO.Sweep.mul_mem_totalComp` and `HJO.Sweep.one_mem_totalComp` — the grading is multiplicative.
* `HJO.Sweep.mem_of_mem_totalComp` — the transport: a `𝕜`-algebra homomorphism out of the total
  space carries the piece of degree `d` into index `d` of any `ℤ`-indexed family of submodules that
  contains `1` in index `0`, multiplies, receives each `y_j` in index `1` and each `p_{r}` in index
  `r`. This is `HJO.Sym.mem_of_mem_lambdaComp` for the coefficients plus a product over the
  `y`-monomial.
* `HJO.Sweep.qshift_mem_totalComp`, `HJO.Sweep.qshiftNeg_mem_totalComp`,
  `HJO.Sweep.cycleShift_mem_totalComp` — `τ_{k,i}`, `τ^-_{k,i}` and `cy_{k+1}` are homogeneous of
  degree `0`. These are what `HJO.Sweep.hatFracDplusStar` reads when it extends `d^*_+` to the
  completion, and the reason the extension is componentwise.

## What is *not* here

The unit shift `ϑ` of `HJO.Sweep.unitShiftTotal` does **not** preserve this grading — it sends `p_r`
to `p_r + 1`, lowering degree — which is the reason the two shifts of Section 3.7 are given
different domains: `τ^*` acts on the completion and `τ` only on the localization of the polynomial
ring. So no lemma below mentions it.

## References

A. Mellit, *Toric braids and `(m,n)`-parking functions*, §3.7, for `HJO.Sweep.pieceHat` and
`HJO.Sweep.hatFracDplusStar`.
-/

@[expose] public section

namespace HJO.Sweep

open MvPolynomial

section CommRingBase

variable {L : Type*} [CommRing L]

/-! ### The graded pieces -/

/-- **The graded piece of degree `d` of the total space**, for the grading of
`HJO.Sweep.pieceHat` in which `p_r` has degree `r` and each `y_i` has degree `1`: those `F` all
of whose `y`-monomials `m` carry a coefficient homogeneous of degree `d - |m|` in `Λ`.

The condition is stated on every `m` at once, with `HJO.Sym.LambdaCompInt` reading `Λ_e` as the
zero subspace for `e < 0`; so it says both that the coefficient is homogeneous of the complementary
degree and that no `y`-monomial of degree greater than `d` occurs. -/
noncomputable def TotalComp (L : Type*) [CommRing L] (d : ℕ) : Submodule L (Total L) where
  carrier := {F | ∀ m : ℕ →₀ ℕ,
    MvPolynomial.coeff m F ∈ Sym.LambdaCompInt L ((d : ℤ) - (m.degree : ℤ))}
  add_mem' {F G} hF hG m := by
    rw [MvPolynomial.coeff_add]; exact add_mem (hF m) (hG m)
  zero_mem' m := by rw [MvPolynomial.coeff_zero]; exact zero_mem _
  smul_mem' r F hF m := by
    rw [MvPolynomial.coeff_smul]; exact Submodule.smul_mem _ r (hF m)

theorem mem_totalComp {d : ℕ} {F : Total L} :
    F ∈ TotalComp L d ↔ ∀ m : ℕ →₀ ℕ,
      MvPolynomial.coeff m F ∈ Sym.LambdaCompInt L ((d : ℤ) - (m.degree : ℤ)) := Iff.rfl

/-- **A `y`-monomial with a homogeneous coefficient is homogeneous**, of the sum of the two
degrees. -/
theorem monomial_mem_totalComp {e : ℕ} {a : Sym.Lambda L} (ha : a ∈ Sym.LambdaComp L e)
    (m : ℕ →₀ ℕ) : (MvPolynomial.monomial m a : Total L) ∈ TotalComp L (e + m.degree) := by
  intro m'
  rw [MvPolynomial.coeff_monomial]
  split_ifs with h
  · subst h
    rw [show ((e + m.degree : ℕ) : ℤ) - (m.degree : ℤ) = (e : ℤ) by push_cast; ring,
      Sym.lambdaCompInt_natCast]
    exact ha
  · exact zero_mem _

/-- **The graded pieces multiply.** Coefficientwise: a coefficient of the product is a sum over the
antidiagonal, and the two `Λ`-degrees add to the complement of the total `y`-degree. -/
theorem mul_mem_totalComp {a b : ℕ} {F G : Total L} (hF : F ∈ TotalComp L a)
    (hG : G ∈ TotalComp L b) : F * G ∈ TotalComp L (a + b) := by
  intro m
  rw [MvPolynomial.coeff_mul]
  refine Submodule.sum_mem _ fun x hx => ?_
  have hx' : x.1 + x.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
  have h := Sym.mul_mem_lambdaCompInt (hF x.1) (hG x.2)
  have hd : (m.degree : ℤ) = (x.1.degree : ℤ) + (x.2.degree : ℤ) := by
    rw [← hx', map_add]; push_cast; ring
  rw [show ((a : ℤ) - x.1.degree) + ((b : ℤ) - x.2.degree)
      = ((a + b : ℕ) : ℤ) - (m.degree : ℤ) by rw [hd]; push_cast; ring] at h
  exact h

/-- **The unit is homogeneous of degree zero.** -/
theorem one_mem_totalComp (L : Type*) [CommRing L] : (1 : Total L) ∈ TotalComp L 0 := by
  have h := monomial_mem_totalComp (e := 0) (Sym.one_mem_lambdaComp L) (0 : ℕ →₀ ℕ)
  simpa using h

/-- **A homogeneous symmetric function is homogeneous of the same degree in the total space.** -/
theorem C_mem_totalComp {d : ℕ} {a : Sym.Lambda L} (ha : a ∈ Sym.LambdaComp L d) :
    (MvPolynomial.C a : Total L) ∈ TotalComp L d := by
  have h := monomial_mem_totalComp ha (0 : ℕ →₀ ℕ)
  simpa using h

/-- **Each auxiliary variable has degree one.** -/
theorem X_mem_totalComp (L : Type*) [CommRing L] (j : ℕ) :
    (MvPolynomial.X j : Total L) ∈ TotalComp L 1 := by
  have h := monomial_mem_totalComp (e := 0) (Sym.one_mem_lambdaComp L) (Finsupp.single j 1)
  simpa [MvPolynomial.X] using h

/-- **The `y_j` has degree one.** -/
theorem auxVar_mem_totalComp (L : Type*) [CommRing L] (j : ℕ) :
    (auxVar j : Total L) ∈ TotalComp L 1 := X_mem_totalComp L (j - 1)

/-- **The power sum `p_{i+1}` has degree `i + 1`.** -/
theorem powerSum_mem_totalComp (L : Type*) [CommRing L] (i : ℕ) :
    (MvPolynomial.C (Sym.powerSum L (i + 1)) : Total L) ∈ TotalComp L (i + 1) :=
  C_mem_totalComp (Sym.powerSum_mem_lambdaComp L i)

/-- **Powers multiply the degree.** -/
theorem pow_mem_totalComp {d : ℕ} {F : Total L} (hF : F ∈ TotalComp L d) (n : ℕ) :
    F ^ n ∈ TotalComp L (n * d) := by
  induction n with
  | zero => simpa using one_mem_totalComp L
  | succ n ih =>
    rw [pow_succ, show (n + 1) * d = n * d + d from by ring]
    exact mul_mem_totalComp ih hF

/-! ### The graded pieces at an integer degree -/

/-- The graded piece of the total space at an integer degree, the zero subspace below degree zero.
This is `HJO.Sym.LambdaCompInt`'s convention one level up, and it is what the transport below needs
in order to speak of a single `ℤ`-indexed family. -/
noncomputable def TotalCompInt (L : Type*) [CommRing L] (c : ℤ) : Submodule L (Total L) :=
  if 0 ≤ c then TotalComp L c.toNat else ⊥

theorem totalCompInt_natCast (L : Type*) [CommRing L] (d : ℕ) :
    TotalCompInt L (d : ℤ) = TotalComp L d := by
  rw [TotalCompInt]
  split_ifs with h
  · rw [Int.toNat_natCast]
  · exact absurd (Int.natCast_nonneg d) h

theorem eq_zero_of_mem_totalCompInt {c : ℤ} (hc : c < 0) {F : Total L}
    (hF : F ∈ TotalCompInt L c) : F = 0 := by
  rw [TotalCompInt] at hF
  split_ifs at hF with h
  · exact absurd h (by omega)
  · simpa using hF

theorem one_mem_totalCompInt (L : Type*) [CommRing L] : (1 : Total L) ∈ TotalCompInt L 0 := by
  rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) by norm_num, totalCompInt_natCast]
  exact one_mem_totalComp L

theorem mul_mem_totalCompInt {c c' : ℤ} {F G : Total L} (hF : F ∈ TotalCompInt L c)
    (hG : G ∈ TotalCompInt L c') : F * G ∈ TotalCompInt L (c + c') := by
  rcases lt_or_ge c 0 with hc | hc
  · rw [eq_zero_of_mem_totalCompInt hc hF, zero_mul]; exact zero_mem _
  rcases lt_or_ge c' 0 with hc' | hc'
  · rw [eq_zero_of_mem_totalCompInt hc' hG, mul_zero]; exact zero_mem _
  lift c to ℕ using hc with d
  lift c' to ℕ using hc' with d'
  rw [totalCompInt_natCast] at hF hG
  rw [← Nat.cast_add, totalCompInt_natCast]
  exact mul_mem_totalComp hF hG

theorem C_mem_totalCompInt {c : ℤ} {a : Sym.Lambda L} (ha : a ∈ Sym.LambdaCompInt L c) :
    (MvPolynomial.C a : Total L) ∈ TotalCompInt L c := by
  rcases lt_or_ge c 0 with hc | hc
  · rw [Sym.eq_zero_of_mem_lambdaCompInt hc ha, map_zero]; exact zero_mem _
  lift c to ℕ using hc with d
  rw [Sym.lambdaCompInt_natCast] at ha
  rw [totalCompInt_natCast]
  exact C_mem_totalComp ha

/-! ### Transporting the grading along an algebra homomorphism -/

section Graded

variable {A : Type*} [Ring A] [Algebra L A]

/-- **A graded target receives the grading of the total space.** The companion of
`HJO.Sym.mem_of_mem_lambdaComp` one level up: of the target it needs only a `ℤ`-indexed family `G`
of submodules with `1 ∈ G 0` and `G c · G c' ⊆ G (c + c')`, and of the homomorphism only that it
send each auxiliary variable into `G 1` and each power sum `p_{i+1}` into `G (i+1)`.

The proof writes `F` as its sum over `y`-monomials, `F = ∑_m C(F_m) y^m`; the coefficient `F_m` is
homogeneous of degree `d - |m|` in `Λ`, so `HJO.Sym.mem_of_mem_lambdaComp` applied to `φ ∘ C` puts
`φ(C(F_m))` in `G (d - |m|)`, while the monomial contributes `G |m|`. -/
theorem mem_of_mem_totalComp (G : ℤ → Submodule L A) (hone : (1 : A) ∈ G 0)
    (hmul : ∀ {c c' : ℤ} {x y : A}, x ∈ G c → y ∈ G c' → x * y ∈ G (c + c'))
    (φ : Total L →ₐ[L] A) (hY : ∀ j : ℕ, φ (MvPolynomial.X j) ∈ G 1)
    (hP : ∀ i : ℕ, φ (MvPolynomial.C (Sym.powerSum L (i + 1))) ∈ G ((i : ℤ) + 1))
    {d : ℕ} {F : Total L} (hF : F ∈ TotalComp L d) : φ F ∈ G (d : ℤ) := by
  classical
  have hpow : ∀ (x : A) (c : ℤ) (k : ℕ), x ∈ G c → x ^ k ∈ G ((k : ℤ) * c) := by
    intro x c k hx
    induction k with
    | zero => simpa using hone
    | succ n ih =>
      have h2 := hmul ih hx
      rw [show ((n : ℤ) * c + c) = ((n + 1 : ℕ) : ℤ) * c by push_cast; ring] at h2
      rw [pow_succ]
      exact h2
  have hC : ∀ (c : ℤ) (a : Sym.Lambda L), a ∈ Sym.LambdaCompInt L c →
      φ (MvPolynomial.C a) ∈ G c := by
    intro c a ha
    rcases lt_or_ge c 0 with hc | hc
    · rw [Sym.eq_zero_of_mem_lambdaCompInt hc ha, map_zero]
      rw [map_zero]
      exact Submodule.zero_mem (G c)
    lift c to ℕ using hc with e
    rw [Sym.lambdaCompInt_natCast] at ha
    have hψ : ∀ i : ℕ, (φ.comp (IsScalarTower.toAlgHom L (Sym.Lambda L) (Total L)))
        (MvPolynomial.X i) ∈ G ((i : ℤ) + 1) := by
      intro i
      have h := hP i
      rwa [show (MvPolynomial.C (Sym.powerSum L (i + 1)) : Total L)
        = (IsScalarTower.toAlgHom L (Sym.Lambda L) (Total L)) (MvPolynomial.X i) by
          simp [Sym.powerSum]] at h
    exact Sym.mem_of_mem_lambdaComp G hone hmul _ hψ ha
  have hprodX : ∀ (s : Finset ℕ) (c : ℕ → ℕ),
      φ (∏ j ∈ s, (MvPolynomial.X j : Total L) ^ c j) ∈ G (∑ j ∈ s, (c j : ℤ)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; simpa using hone
    | insert a s ha ih =>
      intro c
      rw [Finset.prod_insert ha, Finset.sum_insert ha, map_mul, map_pow]
      have h2 := hmul (hpow _ 1 (c a) (hY a)) (ih c)
      rwa [mul_one] at h2
  have hmon : ∀ m : ℕ →₀ ℕ,
      φ (MvPolynomial.monomial m (1 : Sym.Lambda L)) ∈ G ((m.degree : ℤ)) := by
    intro m
    have hprod : (MvPolynomial.monomial m (1 : Sym.Lambda L) : Total L)
        = ∏ j ∈ m.support, (MvPolynomial.X j : Total L) ^ m j := by
      rw [MvPolynomial.monomial_eq, map_one, one_mul, Finsupp.prod]
    have hdeg : ∑ j ∈ m.support, ((m j : ℕ) : ℤ) = (m.degree : ℤ) := by
      rw [Finsupp.degree_apply, Nat.cast_sum]
    rw [hprod, ← hdeg]
    exact hprodX m.support m
  have hFsum : F = ∑ m ∈ F.support, MvPolynomial.C (MvPolynomial.coeff m F) *
      MvPolynomial.monomial m (1 : Sym.Lambda L) := by
    conv_lhs => rw [F.as_sum]
    exact Finset.sum_congr rfl fun m _ => by rw [MvPolynomial.C_mul_monomial, mul_one]
  rw [hFsum, map_sum]
  refine Submodule.sum_mem _ fun m _ => ?_
  rw [map_mul]
  have h3 := hmul (hC _ _ (hF m)) (hmon m)
  rwa [show ((d : ℤ) - (m.degree : ℤ) + (m.degree : ℤ)) = (d : ℤ) by ring] at h3

end Graded

end CommRingBase

/-! ### The three degree-preserving substitutions -/

section Field

variable {L : Type*} [Field L]

/-- **A scalar of `𝕜` has degree zero.** -/
theorem scal_mem_totalComp (x : L) : (scal x : Total L) ∈ TotalComp L 0 :=
  C_mem_totalComp (Sym.C_mem_lambdaComp L x)

/-- **`τ_{k,i}` is homogeneous of degree zero.** It fixes each `y_j`, of degree `1`, and sends
`p_r` to `p_r + (q^r-1)y_i^r`, both terms of degree `r`. This is what lets
`HJO.Sweep.hatFracDplusStar` read it on the completion. -/
theorem qshift_mem_totalComp (q : L) (i : ℕ) {d : ℕ} {F : Total L} (hF : F ∈ TotalComp L d) :
    qshift q i F ∈ TotalComp L d := by
  have h := mem_of_mem_totalComp (TotalCompInt L) (one_mem_totalCompInt L)
    (fun {_ _ _ _} hx hy => mul_mem_totalCompInt hx hy) (qshift q i) (fun j => by
      rw [qshift_auxVar, show (1 : ℤ) = ((1 : ℕ) : ℤ) by norm_num, totalCompInt_natCast]
      exact X_mem_totalComp L j) (fun n => by
      rw [qshift_powerSum, show ((n : ℤ) + 1) = (((n + 1 : ℕ)) : ℤ) by push_cast; ring,
        totalCompInt_natCast]
      refine add_mem (powerSum_mem_totalComp L n) ?_
      have h2 := mul_mem_totalComp (scal_mem_totalComp (q ^ (n + 1) - 1))
        (pow_mem_totalComp (auxVar_mem_totalComp L i) (n + 1))
      simpa using h2) hF
  rwa [totalCompInt_natCast] at h

/-- **`τ^-_{k,i}` is homogeneous of degree zero**, the same computation with the added letter
negated. -/
theorem qshiftNeg_mem_totalComp (q : L) (i : ℕ) {d : ℕ} {F : Total L} (hF : F ∈ TotalComp L d) :
    qshiftNeg q i F ∈ TotalComp L d := by
  have h := mem_of_mem_totalComp (TotalCompInt L) (one_mem_totalCompInt L)
    (fun {_ _ _ _} hx hy => mul_mem_totalCompInt hx hy) (qshiftNeg q i) (fun j => by
      rw [qshiftNeg_auxVar, show (1 : ℤ) = ((1 : ℕ) : ℤ) by norm_num, totalCompInt_natCast]
      exact X_mem_totalComp L j) (fun n => by
      rw [qshiftNeg_powerSum, show ((n : ℤ) + 1) = (((n + 1 : ℕ)) : ℤ) by push_cast; ring,
        totalCompInt_natCast]
      refine sub_mem (powerSum_mem_totalComp L n) ?_
      have h2 := mul_mem_totalComp (scal_mem_totalComp (q ^ (n + 1) - 1))
        (pow_mem_totalComp (auxVar_mem_totalComp L i) (n + 1))
      simpa using h2) hF
  rwa [totalCompInt_natCast] at h

/-- **`cy_{k+1}` is homogeneous of degree zero.** It fixes every `p_r`, being `Λ`-linear, and sends
each `y_j` to `y_{j+1}`, to `u y_1` or to itself — all of degree `1`, the scalar `u` costing
nothing. -/
theorem cycleShift_mem_totalComp (u : L) (k : ℕ) {d : ℕ} {F : Total L} (hF : F ∈ TotalComp L d) :
    cycleShift u k F ∈ TotalComp L d := by
  have h := mem_of_mem_totalComp (TotalCompInt L) (one_mem_totalCompInt L)
    (fun {_ _ _ _} hx hy => mul_mem_totalCompInt hx hy)
    ((cycleShift u k).restrictScalars L) (fun j => by
      rw [show (1 : ℤ) = ((1 : ℕ) : ℤ) by norm_num, totalCompInt_natCast]
      change cycleShift u k (MvPolynomial.X j : Total L) ∈ TotalComp L 1
      rw [cycleShift, MvPolynomial.aeval_X]
      split_ifs
      · exact X_mem_totalComp L _
      · have h2 := mul_mem_totalComp (scal_mem_totalComp u) (X_mem_totalComp L 0)
        simpa using h2
      · exact X_mem_totalComp L _) (fun n => by
      rw [show ((n : ℤ) + 1) = (((n + 1 : ℕ)) : ℤ) by push_cast; ring, totalCompInt_natCast]
      change cycleShift u k (MvPolynomial.C (Sym.powerSum L (n + 1)) : Total L) ∈ _
      rw [show (MvPolynomial.C (Sym.powerSum L (n + 1)) : Total L)
        = algebraMap (Sym.Lambda L) (Total L) (Sym.powerSum L (n + 1)) from rfl,
        AlgHom.commutes]
      exact powerSum_mem_totalComp L n) hF
  rwa [totalCompInt_natCast] at h

end Field

end HJO.Sweep

end
