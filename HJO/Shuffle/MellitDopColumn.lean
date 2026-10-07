/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.MellitDopKernel
public import HJO.Shuffle.MellitVertexStepClosed
public meta import HJO.Attr

/-! # The diagonal of the two-variable generating object, and the `(a,1)` column at `b = 0`

The `(a,1)` column of Mellit's induction asks, at `b = 0` and a general `f ∈ Λ`, for the identity

`M · ∑_{l ≥ 0} (qu)^l D_{1+l}(D_{-l} f) = D_1(D_0 f) - D_0(D_1 f)`,  `M = (1-q)(1-u)`,

in the integer-indexed basic operators `D_n` of `HJO.Sym.DopInt`. This file proves it, and with it
the `b = 0` clause of `HJO.Sweep.ColumnCommutes` at every `f`.

## What the proof runs on

Two products of basic operators differ only by the interaction of one displacement with the
*other's* exponential factor, so both are read off the single two-variable object

`f[X + M/y₁ + M/y₂] · Ω(y₁) · Ω(y₂)`,

which is symmetric in `y₁, y₂`. Only its diagonal `a + b = 1` is needed, and only through two
properties:

* the **unfolding**, `D_i(D_{1-i}f) = ∑_{r ≥ 0} λ_r θ_{i-1+r}`, where `λ` is the kernel
  `HJO.Sym.mkernel` of the displacement and `θ_s` is the diagonal coefficient — this is the
  `M`-alphabet analogue of `HJO.Sym.bop_bop`;
* the **reflection** `θ_s = θ_{-1-s}`, which is `φ_{a,b} = φ_{b,a}` on that diagonal.

**The two-variable object is never built as a Laurent series.** The displacement produces only
non-negative powers of `y = z⁻¹` and `Ω` only non-negative powers of `z`, so each coefficient
`θ_s` is a *finite* sum and `θ_s` is defined directly as `∑_b D_{s+1}(δ(f)_b) c_{-s+b}`. What the
symmetry needs is only that the doubly displaced `f` is fixed by the interchange of the two
variables of `Λ[y₁][y₂]`, which is `HJO.Sym.swapPP_plethShiftSq`; none of
`HJO.Sym.LaurentZW`, `HJO.Sym.bpairSeries` or the Hahn-series machinery of the
Haglund--Morse--Zabrocki block is used or duplicated.

**The Jing relation is not the tool, and its `M`-analogue would not be enough.**
`HJO.Sym.bop_pair_antisymm` is about `HJO.Sym.Bop`, whose displacement alphabet is `1 - q`; `D_n`
displaces by `M = (1-q)(1-u)`, whose commutation kernel `(1-x)(1-qux)/((1-qx)(1-ux))` is a ratio
of *quadratics*, so clearing denominators gives a four-term relation rather than Jing's two-term
one. More to the point, every such relation is a *finite* combination of the `D_mD_n`, while the
identity here has an infinite (degreewise finite) sum on its left: on a fixed `f` the coefficients
`θ` cannot be recovered from finitely many products, so the reflection symmetry of the two-variable
object is genuinely needed.

## Main definitions

* `HJO.Sym.swapPP` — the interchange of the two variables of `R[y₁][y₂]`.
* `HJO.Sym.plethShiftSq` — the double displacement `f[X + M/y₁ + M/y₂]`.
* `HJO.Sym.dopDiag` — the diagonal family `θ_s`.
* `HJO.Sym.ccoef` — the bookkeeping coefficients `c_n = ∑_{l ≤ n}(qu)^l λ_{n-l} = h_n - h_{n-1}`.

## Main results

* `HJO.Sym.coeff_plethShift_coeff_plethShift_comm` — `δ(δ(f)_b)_i = δ(δ(f)_i)_b`.
* `HJO.Sym.dopDiag_reflect` — the reflection `θ_s = θ_{-1-s}`.
* `HJO.Sym.dopInt_dopInt_eq_sum_mkernel_dopDiag` — the unfolding.
* `HJO.Sym.smul_sum_pow_smul_dopInt_dopInt` — the identity.
* `HJO.Sweep.columnCommutes_zero_at` — the `b = 0` clause of `HJO.Sweep.ColumnCommutes`, at every
  `f`, with no hypothesis beyond `q ≠ 0`, `u ≠ 0`, `q ≠ 1`.
* `HJO.Sweep.lhsSlope_two_one` — the clause of `HJO.Mellit.lhsRewrite_sweepWitness` at the slope
  `(2,1)`, at a general `f`, extending the degree-`≤ 2` case
  `HJO.Sweep.lhsSlopeAt_two_one_of_deg_le_two`. This one does carry `M ≠ 0`, because
  `HJO.Sym.Qop` defines `Q_{2,1}` by dividing by `M`.
* `HJO.Sweep.columnCommutes_of_forall_succ` — `HJO.Sweep.ColumnCommutes` follows from its clauses
  at `b ≥ 1` alone.

## Genericity

The `D_n`-algebra identity carries **no hypothesis at all** on `q` and `u`, and in particular not
`M ≠ 0`: `M` appears as a coefficient because every member of the kernel above the zeroth carries it
(`HJO.Sym.mkernel_succ`), and the proof cancels against that factor rather than dividing. The three
exclusions on the sweep-module clause are inherited from the translation
`HJO.Sweep.columnCommutes_zero_at_iff_dopInt`.

## Cross-check

At `f = e_2` the clause is also proved by a completely independent route
(`HJO.Sweep.columnCommutes_zero_at_elemSymm_two`: the `Λ` side through `HJO.Sym.Qop`'s commutator
and five `D`-values, the sweep side through `T` and two Hall--Littlewood values). The general
statement proved here agrees with it, which is evidence that the identity is the true one and not an
artefact of the bookkeeping.

## What is *not* here

`HJO.Sweep.ColumnCommutes` quantifies over all `b`; only `b = 0` is proved here, so only the slope
`(2,1)` of the column is closed. The general clause `M ψ_{b+1} = ψ_b D_0 - D_0 ψ_b` is an identity
among `b + 2` basic operators, which the two-variable object does not reach; it is proved by an
induction on `b` in `HJO/Shuffle/MellitColumnChainTelescope.lean`. The general-`b` closed form of
`ψ_b` inside the `D_n`-algebra is not here either; it is a translation of the sweep side, not a
step towards the commutation.
-/

@[expose] public section

namespace HJO.Sym

/-! ### Exchanging the two variables of a doubly iterated polynomial ring -/

section Swap

variable (R : Type*) [CommRing R]

/-- **Exchanging the two variables of `R[y₁][y₂]`.** The ring homomorphism sending the outer
variable `y₂` to the inner one `y₁ = C(X)` and moving the coefficients, polynomials in `y₁`, into
polynomials in `y₂`. It fixes `C(C a)` for every `a ∈ R`, so it is the interchange of the two
variables and nothing else. -/
noncomputable def swapPP : Polynomial (Polynomial R) →+* Polynomial (Polynomial R) :=
  Polynomial.eval₂RingHom (Polynomial.mapRingHom (Polynomial.C : R →+* Polynomial R))
    (Polynomial.C Polynomial.X)

variable {R}

@[simp] theorem swapPP_C_C (a : R) :
    swapPP R (Polynomial.C (Polynomial.C a)) = Polynomial.C (Polynomial.C a) := by
  rw [swapPP, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Polynomial.coe_mapRingHom,
    Polynomial.map_C]

@[simp] theorem swapPP_C_X :
    swapPP R (Polynomial.C Polynomial.X) = Polynomial.X := by
  rw [swapPP, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Polynomial.coe_mapRingHom,
    Polynomial.map_X]

@[simp] theorem swapPP_X :
    swapPP R (Polynomial.X : Polynomial (Polynomial R)) = Polynomial.C Polynomial.X := by
  rw [swapPP, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]

/-- **The interchange on coefficients**: the coefficient of `y₁^i y₂^b` of `swapPP F` is the
coefficient of `y₁^b y₂^i` of `F`. -/
theorem coeff_coeff_swapPP (F : Polynomial (Polynomial R)) (i b : ℕ) :
    ((swapPP R F).coeff b).coeff i = ((F.coeff i).coeff b) := by
  induction F using Polynomial.induction_on' with
  | add P Q hP hQ =>
    rw [map_add, Polynomial.coeff_add, Polynomial.coeff_add, hP, hQ, Polynomial.coeff_add,
      Polynomial.coeff_add]
  | monomial n A =>
    have h1 : swapPP R (Polynomial.monomial n A)
        = Polynomial.map (Polynomial.C : R →+* Polynomial R) A
          * Polynomial.C (Polynomial.X ^ n) := by
      rw [← Polynomial.C_mul_X_pow_eq_monomial, swapPP, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow,
        Polynomial.coe_mapRingHom, ← Polynomial.C_pow]
    rw [h1, Polynomial.coeff_mul_C, Polynomial.coeff_map, Polynomial.coeff_monomial]
    rcases eq_or_ne n i with rfl | h
    · rw [ite_eq_left rfl, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, ite_eq_left rfl,
        mul_one]
    · rw [ite_eq_right h, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        ite_eq_right (fun hc => h hc.symm), mul_zero, Polynomial.coeff_zero]

end Swap

/-! ### The double displacement is symmetric -/

section Double

variable {K : Type*} [Field K] [Algebra ℚ K]

/-- **The double displacement**, `f[X + M/y₁ + M/y₂]`: the displacement of `HJO.Sym.plethShift`
applied
twice, once to the whole element and once to every coefficient, so that the inner variable of the
result is the second copy. -/
noncomputable def plethShiftSq (q u : K) : Lambda K →+* Polynomial (Polynomial (Lambda K)) :=
  (Polynomial.mapRingHom (plethShift q u : Lambda K →+* Polynomial (Lambda K))).comp
    (plethShift q u : Lambda K →+* Polynomial (Lambda K))

omit [Algebra ℚ K] in
theorem coeff_coeff_plethShiftSq (q u : K) (f : Lambda K) (i b : ℕ) :
    ((plethShiftSq q u f).coeff b).coeff i
      = (plethShift q u ((plethShift q u f).coeff b)).coeff i := by
  rw [plethShiftSq, RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.coeff_map]
  rfl

omit [Algebra ℚ K] in
/-- **The double displacement is symmetric in the two variables**: it adds `M/y₁` and `M/y₂` to
the alphabet, and the two contributions do not interfere. -/
theorem swapPP_plethShiftSq (q u : K) (f : Lambda K) :
    swapPP (Lambda K) (plethShiftSq q u f) = plethShiftSq q u f := by
  have h : (swapPP (Lambda K)).comp (plethShiftSq q u) = plethShiftSq q u := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
    · have hval : plethShiftSq q u (MvPolynomial.C a : Lambda K)
          = Polynomial.C (Polynomial.C (MvPolynomial.C a : Lambda K)) := by
        rw [plethShiftSq, RingHom.comp_apply, RingHom.coe_coe, plethShift_C,
          Polynomial.coe_mapRingHom, Polynomial.map_C, RingHom.coe_coe, plethShift_C]
      rw [RingHom.comp_apply, hval, swapPP_C_C]
    · have hXp : (MvPolynomial.X i : Lambda K) = powerSum K (i + 1) :=
        (Bglx.powerSum_succ_eq_X i).symm
      have hP : plethShift q u (powerSum K (i + 1))
          = Polynomial.C (powerSum K (i + 1))
            + Polynomial.C (MvPolynomial.C ((1 - q ^ (i + 1)) * (1 - u ^ (i + 1))))
              * Polynomial.X ^ (i + 1) := plethShift_powerSum q (by omega)
      have hval : plethShiftSq q u (powerSum K (i + 1))
          = Polynomial.C (Polynomial.C (powerSum K (i + 1)))
            + Polynomial.C (Polynomial.C
                (MvPolynomial.C ((1 - q ^ (i + 1)) * (1 - u ^ (i + 1)))))
              * (Polynomial.C Polynomial.X) ^ (i + 1)
            + Polynomial.C (Polynomial.C
                (MvPolynomial.C ((1 - q ^ (i + 1)) * (1 - u ^ (i + 1)))))
              * Polynomial.X ^ (i + 1) := by
        rw [plethShiftSq, RingHom.comp_apply, RingHom.coe_coe, hP, Polynomial.coe_mapRingHom,
          Polynomial.map_add, Polynomial.map_C, Polynomial.map_mul, Polynomial.map_C,
          Polynomial.map_pow, Polynomial.map_X]
        simp only [RingHom.coe_coe]
        rw [hP, plethShift_C, Polynomial.C_add, Polynomial.C_mul, Polynomial.C_pow]
      rw [RingHom.comp_apply, hXp, hval]
      simp only [map_add, map_mul, map_pow, swapPP_C_C, swapPP_C_X, swapPP_X]
      ring
  exact congrArg (fun g : Lambda K →+* Polynomial (Polynomial (Lambda K)) => g f) h

omit [Algebra ℚ K] in
/-- **The coefficients of the double displacement are symmetric**:
`δ(δ(f)_b)_i = δ(δ(f)_i)_b` for all `i, b`. This is the only input the reflection symmetry of
diagonal family `HJO.Sym.dopDiag` needs. -/
theorem coeff_plethShift_coeff_plethShift_comm (q u : K) (f : Lambda K) (i b : ℕ) :
    (plethShift q u ((plethShift q u f).coeff b)).coeff i
      = (plethShift q u ((plethShift q u f).coeff i)).coeff b := by
  have h1 := coeff_coeff_swapPP (plethShiftSq q u f) i b
  rw [swapPP_plethShiftSq] at h1
  rw [← coeff_coeff_plethShiftSq, ← coeff_coeff_plethShiftSq]
  exact h1

end Double

/-! ### Two pieces of scalar bookkeeping -/

section Bookkeeping

variable {K : Type*} [CommRing K] {M : Type*} [AddCommGroup M] [Module K M]

/-- The coefficients `c_n = ∑_{l ≤ n}(qu)^l λ_{n-l}`, in the closed form
`HJO.Sym.sum_pow_mul_mkernel` puts them in: `c_0 = 1` and `c_{n+1} = h_{n+1} - h_n`. -/
def ccoef (q u : K) : ℕ → K
  | 0 => 1
  | n + 1 => hsym2 q u (n + 1) - hsym2 q u n

@[simp] theorem ccoef_zero (q u : K) : ccoef q u 0 = 1 := rfl

@[simp] theorem ccoef_succ (q u : K) (n : ℕ) :
    ccoef q u (n + 1) = hsym2 q u (n + 1) - hsym2 q u n := rfl

theorem ccoef_eq_sum (q u : K) (n : ℕ) :
    ccoef q u n = ∑ l ∈ Finset.range (n + 1), (q * u) ^ l * mkernel q u (n - l) := by
  match n with
  | 0 => simp
  | t + 1 => rw [ccoef_succ, ← sum_pow_mul_mkernel q u t]

/-- **The recursion the grouping runs on**: `c_{n+1} = λ_{n+1} + qu·c_n`. -/
theorem ccoef_succ_eq (q u : K) (n : ℕ) :
    ccoef q u (n + 1) = mkernel q u (n + 1) + q * u * ccoef q u n := by
  match n with
  | 0 =>
    rw [ccoef_succ, ccoef_zero, mkernel_succ, hsym2_zero, hsym2_one]
    ring
  | t + 1 =>
    rw [ccoef_succ, ccoef_succ, mkernel_succ,
      show t + 1 + 1 = t + 2 from rfl, hsym2_add_two q u t]
    ring

/-- **The telescoping bookkeeping.** For every family `θ : ℕ → M`,

`∑_{j ≤ N} h_j (θ_j - θ_{j+1}) = ∑_{n ≤ N} c_n θ_n - h_N θ_{N+1}`,

an identity with no hypothesis at all; the boundary term is carried rather than dropped. -/
theorem sum_hsym2_smul_sub (q u : K) (θ : ℕ → M) (N : ℕ) :
    ∑ j ∈ Finset.range (N + 1), hsym2 q u j • (θ j - θ (j + 1))
      = (∑ n ∈ Finset.range (N + 1), ccoef q u n • θ n) - hsym2 q u N • θ (N + 1) := by
  induction N with
  | zero =>
    rw [Finset.sum_range_one, Finset.sum_range_one, hsym2_zero, ccoef_zero, smul_sub]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih,
      Finset.sum_range_succ (f := fun n => ccoef q u n • θ n) (n := N + 1),
      ccoef_succ, sub_smul, smul_sub]
    abel

/-- **The grouping.** If `θ : ℕ → M` vanishes above `N`, then for all `L, R ≥ N`

`∑_{l ≤ L}(qu)^l ∑_{r ≤ R} λ_r θ_{l+r} = ∑_{n ≤ N} c_n θ_n`,

the double sum collapsing onto the diagonal. The induction is on `N`, with `θ` universally
quantified: splitting off `l = 0` leaves the same sum for the shifted family `θ(·+1)`, which
vanishes
one step lower, and the two bookkeeping coefficients then match by
`HJO.Sym.ccoef_succ_eq`. -/
theorem sum_pow_smul_sum_mkernel_smul (q u : K) :
    ∀ (N : ℕ) (θ : ℕ → M), (∀ n : ℕ, N < n → θ n = 0) →
      ∀ L R : ℕ, N ≤ L → N ≤ R →
      (∑ l ∈ Finset.range (L + 1), (q * u) ^ l •
          ∑ r ∈ Finset.range (R + 1), mkernel q u r • θ (l + r))
        = ∑ n ∈ Finset.range (N + 1), ccoef q u n • θ n := by
  intro N
  induction N with
  | zero =>
    intro θ hθ L R _ _
    rw [Finset.sum_range_one, ccoef_zero, one_smul,
      Finset.sum_eq_single_of_mem 0 (Finset.mem_range.2 (Nat.succ_pos L)) ?_]
    · rw [pow_zero, one_smul,
        Finset.sum_eq_single_of_mem 0 (Finset.mem_range.2 (Nat.succ_pos R)) ?_]
      · rw [Nat.add_zero, mkernel_zero, one_smul]
      · intro r _ hr
        rw [Nat.zero_add, hθ r (by omega), smul_zero]
    · intro l _ hl
      rw [Finset.sum_eq_zero ?_, smul_zero]
      intro r _
      rw [hθ (l + r) (by omega), smul_zero]
  | succ N ih =>
    intro θ hθ L R hL hR
    obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
    have hIH := ih (fun n => θ (n + 1)) (fun n hn => hθ (n + 1) (by omega)) L' R (by omega)
      (by omega)
    have hshift : (∑ l ∈ Finset.range (L' + 1), (q * u) ^ (l + 1) •
          ∑ r ∈ Finset.range (R + 1), mkernel q u r • θ (l + 1 + r))
        = ∑ j ∈ Finset.range (N + 1), (q * u * ccoef q u j) • θ (j + 1) := by
      have h1 : (∑ l ∈ Finset.range (L' + 1), (q * u) ^ (l + 1) •
            ∑ r ∈ Finset.range (R + 1), mkernel q u r • θ (l + 1 + r))
          = (q * u) • ∑ l ∈ Finset.range (L' + 1), (q * u) ^ l •
            ∑ r ∈ Finset.range (R + 1), mkernel q u r • θ (l + r + 1) := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [pow_succ, mul_comm ((q * u) ^ l) (q * u), ← smul_assoc]
        refine congrArg _ (Finset.sum_congr rfl fun r _ => ?_)
        rw [show l + 1 + r = l + r + 1 from by omega]
      rw [h1, hIH, Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [smul_smul]
    have htrim : (∑ r ∈ Finset.range (R + 1), mkernel q u r • θ (0 + r))
        = ∑ r ∈ Finset.range (N + 2), mkernel q u r • θ r := by
      simp only [Nat.zero_add]
      have hsub : Finset.range (N + 2) ⊆ Finset.range (R + 1) := fun x hx =>
        Finset.mem_range.2 (by
          have := Finset.mem_range.1 hx
          omega)
      refine (Finset.sum_subset hsub ?_).symm
      intro r _ hr
      rw [Finset.mem_range, not_lt] at hr
      rw [hθ r (by omega), smul_zero]
    rw [Finset.sum_range_succ' (fun l => (q * u) ^ l •
        ∑ r ∈ Finset.range (R + 1), mkernel q u r • θ (l + r)) (L' + 1), hshift, pow_zero,
      one_smul, htrim, show N + 1 + 1 = N + 2 from rfl,
      Finset.sum_range_succ' (fun n => ccoef q u n • θ n) (N + 1),
      Finset.sum_range_succ' (fun r => mkernel q u r • θ r) (N + 1),
      mkernel_zero, ccoef_zero, ← add_assoc, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← add_smul, ccoef_succ_eq q u j]
    congr 1
    ring

end Bookkeeping

/-! ### The diagonal of the two-variable generating object -/

section Diag

variable {K : Type*} [Field K] [Algebra ℚ K]

/-- **The diagonal family** `θ_s = φ_{1+s, -s}(f)` of the two-variable generating object
`f[X + M/y₁ + M/y₂]·Ω(y₁)·Ω(y₂)`, written without ever naming that object: it is

`θ_s = ∑_b D_{s+1}(δ(f)_b) · c_{-s+b}`,

where `δ` is the displacement of `HJO.Sym.plethShift`, `D` the integer-indexed basic operator
`HJO.Sym.DopInt` of `HJO.Sym.DopInt`, and `c` the alternating elementary family
`HJO.Sym.esymmSigned`. The sum is over a range covering the degree of `δ(f)`, so it is finite by
construction. -/
noncomputable def dopDiag (q u : K) (f : Lambda K) (s : ℤ) : Lambda K :=
  ∑ b ∈ Finset.range ((plethShift q u f).natDegree + 1),
    DopInt q u (s + 1) ((plethShift q u f).coeff b) * esymmSigned K (-s + (b : ℤ))

/-- Any range covering the degree of `δ(f)` computes the diagonal family. -/
theorem dopDiag_eq_sum_range (q u : K) (f : Lambda K) (s : ℤ) {T : ℕ}
    (hT : (plethShift q u f).natDegree < T) :
    dopDiag q u f s = ∑ b ∈ Finset.range T,
      DopInt q u (s + 1) ((plethShift q u f).coeff b) * esymmSigned K (-s + (b : ℤ)) := by
  have hsub : Finset.range ((plethShift q u f).natDegree + 1) ⊆ Finset.range T := fun x hx =>
    Finset.mem_range.2 (by
      have := Finset.mem_range.1 hx
      omega)
  refine Finset.sum_subset hsub ?_
  intro b _ hb
  rw [Finset.mem_range, not_lt] at hb
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), map_zero, zero_mul]

/-- **The diagonal family vanishes above the degree of `δ(f)`**: every term carries `c_{-s+b}` with
`b ≤ natDegree δ(f) < s`, and the alternating elementary family vanishes below `0`. -/
theorem dopDiag_eq_zero_of_lt (q u : K) (f : Lambda K) {s : ℤ}
    (hs : ((plethShift q u f).natDegree : ℤ) < s) : dopDiag q u f s = 0 := by
  refine Finset.sum_eq_zero fun b hb => ?_
  rw [Finset.mem_range, Nat.lt_succ_iff] at hb
  have hbz : (b : ℤ) ≤ ((plethShift q u f).natDegree : ℤ) := by exact_mod_cast hb
  rw [esymmSigned_of_neg (by omega : -s + (b : ℤ) < 0), mul_zero]

omit [Algebra ℚ K] in
/-- A bound covering both indices of the double displacement of `f`. -/
theorem exists_natDegree_bound (q u : K) (f : Lambda K) : ∃ T : ℕ,
    (plethShift q u f).natDegree < T ∧
      ∀ b i : ℕ, T ≤ i → (plethShift q u ((plethShift q u f).coeff b)).coeff i = 0 := by
  classical
  set N := (plethShift q u f).natDegree with hN
  set S := (Finset.range (N + 1)).sup
    (fun b => (plethShift q u ((plethShift q u f).coeff b)).natDegree) with hS
  refine ⟨max (N + 1) (S + 1), by omega, fun b i hi => ?_⟩
  by_cases hb : b ≤ N
  · have hle : (plethShift q u ((plethShift q u f).coeff b)).natDegree ≤ S :=
      Finset.le_sup (f := fun b => (plethShift q u ((plethShift q u f).coeff b)).natDegree)
        (Finset.mem_range.2 (by omega))
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (show N < b by omega), map_zero,
      Polynomial.coeff_zero]

/-- The diagonal family as an explicit double sum over the coefficients of the double
displacement. -/
theorem dopDiag_eq_double_sum (q u : K) (f : Lambda K) {T : ℕ}
    (hT1 : (plethShift q u f).natDegree < T)
    (hT2 : ∀ b i : ℕ, T ≤ i → (plethShift q u ((plethShift q u f).coeff b)).coeff i = 0)
    (s : ℤ) :
    dopDiag q u f s
      = ∑ b ∈ Finset.range T, ∑ i ∈ Finset.range T,
          (plethShift q u ((plethShift q u f).coeff b)).coeff i
            * esymmSigned K (s + 1 + (i : ℤ)) * esymmSigned K (-s + (b : ℤ)) := by
  rw [dopDiag_eq_sum_range q u f s hT1]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [show DopInt q u (s + 1) ((plethShift q u f).coeff b)
      = ∑ i ∈ Finset.range T, (plethShift q u ((plethShift q u f).coeff b)).coeff i
          * esymmSigned K (s + 1 + (i : ℤ)) from
    coeffPairing_eq_sum_range _ _ (fun i hi => hT2 b i hi), Finset.sum_mul]

/-- **The diagonal family is symmetric under the reflection `s ↦ -1-s`.** This is the symmetry
`φ_{a,b} = φ_{b,a}` of the two-variable generating object read on the diagonal `a + b = 1`, and
it is
the *only* genuinely two-variable input the column identity needs. It rests on
`HJO.Sym.coeff_plethShift_coeff_plethShift_comm`. -/
theorem dopDiag_reflect (q u : K) (f : Lambda K) (s : ℤ) :
    dopDiag q u f s = dopDiag q u f (-1 - s) := by
  obtain ⟨T, hT1, hT2⟩ := exists_natDegree_bound q u f
  rw [dopDiag_eq_double_sum q u f hT1 hT2 s, dopDiag_eq_double_sum q u f hT1 hT2 (-1 - s)]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ => ?_
  rw [coeff_plethShift_coeff_plethShift_comm q u f i b,
    show -(-1 - s) + (i : ℤ) = s + 1 + (i : ℤ) from by ring,
    show -1 - s + 1 + (b : ℤ) = -s + (b : ℤ) from by ring]
  ring

/-- **The product of two basic operators, expanded on the diagonal family**: for every `i ≥ 0`,

`D_i(D_{1-i}f) = ∑_{r ≥ 0} λ_r θ_{i-1+r}`,

with `λ` the kernel `HJO.Sym.mkernel` and `θ` the diagonal family. This is the `M`-alphabet
analogue of `HJO.Sym.bop_bop`, obtained not from a two-variable Laurent series but from the
single unfolding
rule `HJO.Sym.dopInt_mul_esymmSigned` applied to each coefficient of `δ(f)`. -/
theorem dopInt_dopInt_eq_sum_mkernel_dopDiag (q u : K) (f : Lambda K) {T : ℕ}
    (hT : (plethShift q u f).natDegree < T) (i : ℕ) {R : ℕ} (hR : T ≤ R) :
    DopInt q u (i : ℤ) (DopInt q u (1 - (i : ℤ)) f)
      = ∑ r ∈ Finset.range (R + 1),
          MvPolynomial.C (mkernel q u r) * dopDiag q u f ((i : ℤ) - 1 + (r : ℤ)) := by
  have hF : ∀ b : ℕ, T ≤ b → (plethShift q u f).coeff b = 0 := fun b hb =>
    Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have h1 : DopInt q u (1 - (i : ℤ)) f
      = ∑ b ∈ Finset.range T,
        (plethShift q u f).coeff b * esymmSigned K (1 - (i : ℤ) + (b : ℤ)) :=
    coeffPairing_eq_sum_range _ _ hF
  have hterm : ∀ b ∈ Finset.range T,
      DopInt q u (i : ℤ) ((plethShift q u f).coeff b * esymmSigned K (1 - (i : ℤ) + (b : ℤ)))
        = ∑ r ∈ Finset.range (R + 1), MvPolynomial.C (mkernel q u r)
            * esymmSigned K (1 - (i : ℤ) + (b : ℤ) - (r : ℤ))
            * DopInt q u ((i : ℤ) + (r : ℤ)) ((plethShift q u f).coeff b) := by
    intro b hb
    rw [Finset.mem_range] at hb
    exact dopInt_mul_esymmSigned q u (i : ℤ) (1 - (i : ℤ) + (b : ℤ)) R (by omega) _
  rw [h1, map_sum, Finset.sum_congr rfl hterm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [dopDiag_eq_sum_range q u f ((i : ℤ) - 1 + (r : ℤ)) hT, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [show (i : ℤ) - 1 + (r : ℤ) + 1 = (i : ℤ) + (r : ℤ) from by ring,
    show -((i : ℤ) - 1 + (r : ℤ)) = 1 - (i : ℤ) - (r : ℤ) from by ring,
    show 1 - (i : ℤ) - (r : ℤ) + (b : ℤ) = 1 - (i : ℤ) + (b : ℤ) - (r : ℤ) from by ring]
  ring

/-! ### The identity -/

/-- **The `(a,1)` column's identity in the `D_n`-algebra.** For every `f ∈ Λ` and every range
covering the degree of `δ(f)`,

`M · ∑_{l ≥ 0} (qu)^l D_{1+l}(D_{-l} f) = D_1(D_0 f) - D_0(D_1 f)`, `M = (1-q)(1-u)`.

**No hypothesis on `q` or `u`, and in particular no `M ≠ 0`.** The `M` enters as the factor every
member of the kernel above the zeroth carries (`HJO.Sym.mkernel_succ`), so the identity holds with
`M` as a coefficient and is proved by cancelling it against that factor, never by dividing.

The proof is: expand each `D_iD_{1-i}f` on the diagonal family `θ` of the two-variable generating
object (`HJO.Sym.dopInt_dopInt_eq_sum_mkernel_dopDiag`); collapse the resulting double sum onto the
diagonal (`HJO.Sym.sum_pow_smul_sum_mkernel_smul`); and on the other side use the reflection
symmetry
`θ_s = θ_{-1-s}` (`HJO.Sym.dopDiag_reflect`) to kill the `r = 0` term and
`HJO.Sym.sum_hsym2_smul_sub` to telescope what is left. Both sides become `M ∑_n c_n θ_n` with
same coefficients `HJO.Sym.ccoef`, the scalar identity behind that being
`HJO.Sym.sum_pow_mul_mkernel`. -/
@[hjo "lem_mellit_column_dop_zero"]
theorem smul_sum_pow_smul_dopInt_dopInt (q u : K) (f : Lambda K) {T : ℕ}
    (hT : (plethShift q u f).natDegree < T) {R : ℕ} (hR : T ≤ R) :
    ((1 - q) * (1 - u)) • (∑ l ∈ Finset.range (R + 1), ((q * u) ^ l) •
        DopInt q u (1 + (l : ℤ)) (DopInt q u (-(l : ℤ)) f))
      = DopInt q u 1 (DopInt q u 0 f) - DopInt q u 0 (DopInt q u 1 f) := by
  have hNR : (plethShift q u f).natDegree < R := by omega
  have hθvan : ∀ n : ℕ, (plethShift q u f).natDegree < n → dopDiag q u f (n : ℤ) = 0 :=
    fun n hn => dopDiag_eq_zero_of_lt q u f (by exact_mod_cast hn)
  -- (A) the left-hand sum collapses onto the diagonal
  have hA : (∑ l ∈ Finset.range (R + 1), ((q * u) ^ l) •
        DopInt q u (1 + (l : ℤ)) (DopInt q u (-(l : ℤ)) f))
      = ∑ n ∈ Finset.range ((plethShift q u f).natDegree + 1),
          ccoef q u n • dopDiag q u f (n : ℤ) := by
    have hrow : ∀ l : ℕ, DopInt q u (1 + (l : ℤ)) (DopInt q u (-(l : ℤ)) f)
        = ∑ r ∈ Finset.range (R + 1),
          mkernel q u r • dopDiag q u f ((l + r : ℕ) : ℤ) := by
      intro l
      have h := dopInt_dopInt_eq_sum_mkernel_dopDiag q u f hT (1 + l) hR
      rw [show ((1 + l : ℕ) : ℤ) = 1 + (l : ℤ) from by push_cast; ring,
        show (1 : ℤ) - (1 + (l : ℤ)) = -(l : ℤ) from by ring] at h
      rw [h]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [MvPolynomial.smul_eq_C_mul]
      congr 2
      push_cast
      ring
    rw [Finset.sum_congr rfl (fun l (_ : l ∈ Finset.range (R + 1)) => by rw [hrow l])]
    exact sum_pow_smul_sum_mkernel_smul q u ((plethShift q u f).natDegree)
      (fun n => dopDiag q u f (n : ℤ)) hθvan R R (le_of_lt hNR) (le_of_lt hNR)
  -- (B) and (C): the two right-hand operators
  have hB : DopInt q u 1 (DopInt q u 0 f)
      = ∑ r ∈ Finset.range (R + 1), mkernel q u r • dopDiag q u f (r : ℤ) := by
    have h := dopInt_dopInt_eq_sum_mkernel_dopDiag q u f hT 1 hR
    rw [Nat.cast_one, show (1 : ℤ) - 1 = 0 from by ring] at h
    rw [h]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [MvPolynomial.smul_eq_C_mul, zero_add]
  have hC : DopInt q u 0 (DopInt q u 1 f)
      = ∑ r ∈ Finset.range (R + 1), mkernel q u r • dopDiag q u f ((r : ℤ) - 1) := by
    have h := dopInt_dopInt_eq_sum_mkernel_dopDiag q u f hT 0 hR
    rw [Nat.cast_zero, show (1 : ℤ) - 0 = 1 from by ring] at h
    rw [h]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [MvPolynomial.smul_eq_C_mul]
    exact congrArg (fun t : ℤ => MvPolynomial.C (mkernel q u r) * dopDiag q u f t) (by ring)
  -- (D) the difference, with the `r = 0` term killed by the reflection
  have hrefl0 : dopDiag q u f (-1) = dopDiag q u f 0 := by
    have h := dopDiag_reflect q u f (-1)
    rwa [show (-1 : ℤ) - -1 = 0 from by ring] at h
  have hD : DopInt q u 1 (DopInt q u 0 f) - DopInt q u 0 (DopInt q u 1 f)
      = ∑ j ∈ Finset.range R, mkernel q u (j + 1) •
          (dopDiag q u f (((j + 1 : ℕ)) : ℤ) - dopDiag q u f (j : ℤ)) := by
    rw [hB, hC, ← Finset.sum_sub_distrib,
      Finset.sum_congr rfl (fun r (_ : r ∈ Finset.range (R + 1)) =>
        (smul_sub (mkernel q u r) (dopDiag q u f (r : ℤ)) (dopDiag q u f ((r : ℤ) - 1))).symm),
      Finset.sum_range_succ' (fun r => mkernel q u r •
        (dopDiag q u f (r : ℤ) - dopDiag q u f ((r : ℤ) - 1))) R,
      show mkernel q u 0
            • (dopDiag q u f ((0 : ℕ) : ℤ) - dopDiag q u f (((0 : ℕ) : ℤ) - 1))
          = 0 from by
        rw [Nat.cast_zero, show (0 : ℤ) - 1 = -1 from by ring, hrefl0, sub_self, smul_zero],
      add_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) from by push_cast; ring]
  -- (E) the telescope
  have hE : (∑ j ∈ Finset.range R, mkernel q u (j + 1) •
        (dopDiag q u f (((j + 1 : ℕ)) : ℤ) - dopDiag q u f (j : ℤ)))
      = ((1 - q) * (1 - u)) • ∑ j ∈ Finset.range R, hsym2 q u j •
          (dopDiag q u f (j : ℤ) - dopDiag q u f (((j + 1 : ℕ)) : ℤ)) := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mkernel_succ, neg_mul, neg_smul, ← smul_neg, neg_sub, smul_smul]
  have hF : (∑ j ∈ Finset.range R, hsym2 q u j •
        (dopDiag q u f (j : ℤ) - dopDiag q u f (((j + 1 : ℕ)) : ℤ)))
      = ∑ n ∈ Finset.range ((plethShift q u f).natDegree + 1),
          ccoef q u n • dopDiag q u f (n : ℤ) := by
    have hsub : Finset.range ((plethShift q u f).natDegree + 1) ⊆ Finset.range R := fun x hx =>
      Finset.mem_range.2 (by
        have := Finset.mem_range.1 hx
        omega)
    rw [← Finset.sum_subset hsub ?_]
    · have h := sum_hsym2_smul_sub q u (fun n : ℕ => dopDiag q u f (n : ℤ))
        ((plethShift q u f).natDegree)
      rw [hθvan ((plethShift q u f).natDegree + 1) (by omega), smul_zero, sub_zero] at h
      exact h
    · intro j _ hj
      rw [Finset.mem_range, not_lt] at hj
      rw [hθvan j (by omega), hθvan (j + 1) (by omega), sub_zero, smul_zero]
  rw [hA, hD, hE, hF]

end Diag

end HJO.Sym

/-! ### The `b = 0` clause of the `(a,1)` column, at a general `f` -/

namespace HJO.Sweep

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-- **`HJO.Sweep.ColumnCommutes` holds at `b = 0`, for every `f ∈ Λ`:**

`M·ψ_1 f = ψ_0(D_0 f) - d_-(d^*_+(ψ_0 f))`.

`HJO.Sweep.columnCommutes_zero_at_iff_dopInt` turns this into the identity
`M·∑_{l ≥ 0}(qu)^lD_{1+l}(D_{-l}f) = D_1(D_0f) - D_0(D_1f)` inside the `D_n`-algebra, and that
`HJO.Sym.smul_sum_pow_smul_dopInt_dopInt`.

This generalises the cases `f = e_1` (`HJO.Sweep.columnCommutes_at_elemSymm_one`) and `f = e_2`
(`HJO.Sweep.columnCommutes_zero_at_elemSymm_two`), both of which also carry `M ≠ 0`.
**`M ≠ 0` is not needed**: the `D_n`-algebra identity has `M` as a coefficient, matching the
factor `M` that every member of the displacement's kernel above the zeroth carries. The three
exclusions that remain,
`q ≠ 0`, `u ≠ 0` and `q ≠ 1`, are inherited from the translation
(`HJO.Sweep.psiCol_one_eq_sum_dopInt`) and from `HJO.Sweep.zop`'s scalar `q/(1-q)`. -/
@[hjo "lem_mellit_column_dop_zero"]
theorem columnCommutes_zero_at (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) (f : Sym.Lambda L) :
    ((1 - q) * (1 - u)) • psiCol q u 1 f
      = psiCol q u 0 (Sym.Dop q u 0 f) - dminus q 1 (dplusStar q u 0 (psiCol q u 0 f)) := by
  obtain ⟨R₀, hR₀⟩ := exists_forall_bopExt_dplusStar_coeff_eq_zero q u 0
    (dplusStar q u 0 (MvPolynomial.C f : Total L))
  set T : ℕ := (Sym.plethShift q u f).natDegree + 1 with hTdef
  have h1 : Sym.Dop q u 1 = Sym.DopInt q u 1 := by
    rw [← Sym.dopInt_natCast q u 1, Nat.cast_one]
  have h0 : Sym.Dop q u 0 = Sym.DopInt q u 0 := by
    rw [← Sym.dopInt_natCast q u 0, Nat.cast_zero]
  rw [columnCommutes_zero_at_iff_dopInt hq0 hu0 hq1 (max R₀ T) f
    (hR₀ (max R₀ T) (le_max_left _ _)), h1, h0]
  exact Sym.smul_sum_pow_smul_dopInt_dopInt q u f (by omega) (le_max_right R₀ T)

/-- **The clause of `HJO.Mellit.lhsRewrite_sweepWitness` at the slope `(2,1)`, at a general `f`:**
`ψ_1 f = ι(Q_{2,1}f)`.

This is the `b = 0` commutation read against `HJO.Sym.Qop`'s recursion
`Q_{2,1} = M^{-1}(Q_{1,1}D_0 - D_0Q_{1,1})` (`HJO.Sweep.qop_succ_succ_one`) with `Q_{1,1} = D_1`;
it is the `c = 0` step of `HJO.Sweep.psiCol_eq_qop_of_columnCommutes`, which needs only the
clause at `b = 0` and not the whole of `HJO.Sweep.ColumnCommutes`.

`M ≠ 0` enters here and nowhere earlier: `Q_{2,1}` is *defined* by dividing by `M`, so it is
`HJO.Sym.Qop`'s normalisation and not an artefact. The degree-`≤ 2` case is
`HJO.Sweep.lhsSlopeAt_two_one_of_deg_le_two`. -/
theorem psiCol_one_eq_qop (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1)
    (hM : (1 - q) * (1 - u) ≠ 0) (f : Sym.Lambda L) :
    psiCol q u 1 f = MvPolynomial.C (Sym.Qop q u 2 1 f) := by
  have h0 : ∀ g : Sym.Lambda L, psiCol q u 0 g = MvPolynomial.C (Sym.Qop q u (0 + 1) 1 g) :=
    fun g => by rw [psiCol_zero, Sym.qop_one]
  have hstep := columnCommutes_zero_at hq0 hu0 hq1 f
  rw [h0 f, h0 (Sym.Dop q u 0 f), ← dop_zero_eq_dminus_dplusStar] at hstep
  have hgoal : ((1 - q) * (1 - u)) • psiCol q u (0 + 1) f
      = ((1 - q) * (1 - u)) • (MvPolynomial.C (Sym.Qop q u (0 + 2) 1 f) : Total L) := by
    rw [hstep, qop_succ_succ_one, LinearMap.smul_apply, LinearMap.sub_apply,
      Module.End.mul_apply, Module.End.mul_apply, C_smul, smul_inv_smul₀ hM, map_sub]
  exact smul_right_injective (Total L) hM hgoal

/-- **The `(2,1)` clause of `HJO.Mellit.lhsRewrite_sweepWitness` at a general `f`.**

This is one slope of `HJO.Mellit.lhsRewrite_sweepWitness`, which is the clause at a *general*
slope and is not proved here. -/
theorem lhsSlope_two_one (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1)
    (hM : (1 - q) * (1 - u) ≠ 0) : Mellit.LhsSlope q u 2 1 := fun f =>
  (lhsSlopeAt_succ_one_iff_psiCol q u 1 f).mpr (psiCol_one_eq_qop hq0 hu0 hq1 hM f).symm

/-- **The `(a,1)` column reduced to `b ≥ 1`.** `HJO.Sweep.ColumnCommutes` quantifies over all
`b`; the clause at `b = 0` is proved here at every `f`, so the clauses at `b ≥ 1` suffice.

`ψ_{b+1}` and `ψ_b` involve `b + 2` basic operators, and the commutation at `b ≥ 1` is an identity
among them: the two-variable generating object used here settles `b = 0` only, and the general
clause needs the symmetry of the `(b+2)`-variable object. -/
theorem columnCommutes_of_forall_succ (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1)
    (h : ∀ (b : ℕ) (f : Sym.Lambda L),
      ((1 - q) * (1 - u)) • psiCol q u (b + 1 + 1) f
        = psiCol q u (b + 1) (Sym.Dop q u 0 f)
          - dminus q 1 (dplusStar q u 0 (psiCol q u (b + 1) f))) :
    ColumnCommutes q u := by
  intro b f
  match b with
  | 0 => exact columnCommutes_zero_at hq0 hu0 hq1 f
  | t + 1 => exact h t f

end HJO.Sweep
