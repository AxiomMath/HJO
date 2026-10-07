/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Collinear.OmegaBarDop
public import HJO.CarlssonMellit.Bop
public import HJO.Shuffle.LhsOpDefs
public import HJO.Ascent.TransportShuffle

/-! # The `Λ` side of the base-slope value: `ω̄` carries `B_r` to `C_r`

The base slope `(1,1)` of `HJO.Mellit.lhsRewrite_sweepWitness` at the vacuum is Carlsson--Mellit's
computation `∇C_α(1) = 𝒩ω̄C_α(1)` read backwards. Two facts on `Λ` alone enter it, and they are
proved here.

* **`ω̄` carries the Hall--Littlewood operator to the creation operator**:
  `ω̄(B_r f) = (-q)^{r-1} C_r(ω̄ f)` (`HJO.Sym.cop_omegaBar`, in the form
  `C_r(ω̄ f) = (-q)^{1-r} ω̄(B_r f)`). The two displacements `f[X-(q-1)/z]` and `f[X-(1-q^{-1})/z]`
  are exchanged by `ω̄` coefficientwise (`HJO.Sym.map_plethHallLittlewood_omegaBar`), and
  `ω̄((-1)^n e_n) = h_n`. This is the identity `ω̄B_α(1) ∝ C_α(1)` that Carlsson--Mellit use in
  their proof of the compositional shuffle conjecture.
* **A Macdonald conjugator preserves degree** (`HJO.Sym.IsMacdonaldConjugator.mem_lambdaComp`),
  given `(1-q)(1-u) ≠ 0`: it carries `D_k` to `Q_{k+1,k}`, both of which shift degree by `k`, and
  the vectors `D_{k_1}⋯D_{k_r}(1)` span `Λ`.

## Main results

* `HJO.Sym.map_plethHallLittlewood_omegaBar`, `HJO.Sym.cop_omegaBar`.
* `HJO.Sym.qop_word_apply_one_mem_lambdaComp`, `HJO.Sym.IsMacdonaldConjugator.mem_lambdaComp`.

## References

* E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31**
  (2018), the proof of the theorem `∇C_α(1) = D_α` (Theorem 7.5 of arXiv:1508.06239), whose last
  line is `𝒩(q^{|α|-k}(-1)^kB_α(1)) = 𝒩ω̄C_α(1)`.
-/

@[expose] public section

namespace HJO.Sym

/-! ### `ω̄` exchanges the two creation displacements -/

section OmegaBop

variable {L : Type*} [Field L] [Algebra ℚ L]

omit [Algebra ℚ L] in
/-- **`ω̄` intertwines the two creation displacements.** Applying `ω̄` to every coefficient of
`f[X - (q-1)/z]` gives `(ω̄f)[X - (1-q^{-1})/z]`. -/
theorem map_plethHallLittlewood_omegaBar {σ : L ≃+* L} {q : L} (hq : σ q = q⁻¹)
    (f : Lambda L) :
    (plethHallLittlewood q f).map (omegaBar σ) = plethCreate q (omegaBar σ f) := by
  have key : (Polynomial.mapRingHom (omegaBar σ)).comp
        (plethHallLittlewood q : Lambda L →+* Polynomial (Lambda L))
      = ((plethCreate q : Lambda L →+* Polynomial (Lambda L))).comp
        (omegaBar σ : Lambda L →+* Lambda L) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
    · rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.coe_coe, RingHom.coe_coe,
        plethHallLittlewood_C, omegaBar_C, HJO.Ascent.plethCreate_C, Polynomial.coe_mapRingHom,
        Polynomial.map_C, omegaBar_C]
    · have hp : omegaBar σ (powerSum L (i + 1)) = -MvPolynomial.X i := by
        rw [powerSum, Nat.add_sub_cancel]; exact omegaBar_X σ i
      have hs : σ (1 - q ^ (i + 1)) = 1 - (q ^ (i + 1))⁻¹ := by
        rw [map_sub, map_one, map_pow, hq, inv_pow]
      rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.coe_coe, RingHom.coe_coe,
        plethHallLittlewood_X, Polynomial.coe_mapRingHom, Polynomial.map_add, Polynomial.map_mul,
        Polynomial.map_C, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, omegaBar_C,
        hp, hs, omegaBar_X]
      simp only [map_neg, HJO.CreationSeeds.plethCreate_X, powerSum, Nat.add_sub_cancel]
      ring
  exact congrArg (fun g : Lambda L →+* Polynomial (Lambda L) => g f) key

omit [Field L] [Algebra ℚ L] in
/-- A scalar on the paired family comes out of the pairing. -/
theorem coeffPairing_family_C_mul {K : Type*} [CommRing K] (c : K) (a : ℕ → Lambda K)
    (P : Polynomial (Lambda K)) :
    coeffPairing (fun j => MvPolynomial.C c * a j) P = c • coeffPairing a P := by
  change (P.sum fun j A => A * (MvPolynomial.C c * a j)) = c • P.sum fun j A => A * a j
  rw [Polynomial.sum, Polynomial.sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [MvPolynomial.smul_eq_C_mul]
  ring

/-- **`ω̄` carries the Hall--Littlewood operator to the creation operator**:
`C_r(ω̄f) = (-q)^{1-r} ω̄(B_rf)`, for every `r ≥ 0`. -/
theorem cop_omegaBar {σ : L ≃+* L} {q : L} (hq : σ q = q⁻¹) (r : ℕ) (f : Lambda L) :
    Cop q r (omegaBar σ f) = (-q) ^ (1 - (r : ℤ)) • omegaBar σ (Bop q r f) := by
  have hfam : (fun j : ℕ => omegaBar σ (elemSymmAlt L ((r : ℤ) + (j : ℤ))))
      = fun j => completeHomog L (r + j) := by
    funext j
    rw [show ((r : ℤ) + (j : ℤ)) = ((r + j : ℕ) : ℤ) by push_cast; ring, elemSymmAlt_natCast,
      omegaBar_neg_one_pow_mul_elemSymm]
  have hB : omegaBar σ (Bop q r f)
      = coeffPairing (fun j => completeHomog L (r + j)) (plethCreate q (omegaBar σ f)) := by
    change omegaBar σ (coeffPairing (fun j : ℕ => elemSymmAlt L ((r : ℤ) + (j : ℤ)))
      (plethHallLittlewood q f)) = _
    rw [map_coeffPairing, hfam, map_plethHallLittlewood_omegaBar hq]
  rw [hB]
  exact coeffPairing_family_C_mul _ _ _

end OmegaBop

/-! ### A Macdonald conjugator preserves degree -/

section Degree

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-- A word in the basic operators, applied to `1`, is homogeneous of degree the sum of the
indices. -/
theorem dop_word_apply_one_mem_lambdaComp (q u : L) :
    ∀ w : List ℕ, (w.map (Dop q u)).prod (1 : Lambda L) ∈ LambdaComp L w.sum := by
  intro w
  induction w with
  | nil =>
    simp only [List.map_nil, List.prod_nil, Module.End.one_apply, List.sum_nil]
    rw [mem_lambdaComp]; exact MvPolynomial.isWeightedHomogeneous_one L _
  | cons k w ih =>
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, List.sum_cons]
    have h := (dop_shiftsDegree q u k).apply_mem_lambdaComp ih
    rwa [Nat.add_comm] at h

/-- A word in the slope operators `Q_{k+1,k}`, applied to `1`, is homogeneous of degree the sum of
the indices. -/
theorem qop_word_apply_one_mem_lambdaComp (q u : L) :
    ∀ w : List ℕ, (w.map fun k => Qop q u (k + 1) k).prod (1 : Lambda L) ∈ LambdaComp L w.sum := by
  intro w
  induction w with
  | nil =>
    simp only [List.map_nil, List.prod_nil, Module.End.one_apply, List.sum_nil]
    rw [mem_lambdaComp]; exact MvPolynomial.isWeightedHomogeneous_one L _
  | cons k w ih =>
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, List.sum_cons]
    have h := (qop_shiftsDegree q u (k + 1) k).apply_mem_lambdaComp ih
    rwa [Nat.add_comm] at h

/-- **A Macdonald conjugator with `∇1 = 1` preserves each homogeneous component**, given
`(1-q)(1-u) ≠ 0`. It carries `D_k` to `Q_{k+1,k}` (`HJO.Sym.qop_succ_apply_of_clauses`), both of
which shift degree by `k`, so it carries each `D_{k_1}⋯D_{k_r}(1)` into the component of degree
`k_1 + ⋯ + k_r`; and those vectors span `Λ` (`HJO.Sym.dopOrbit_eq_top`). -/
theorem IsMacdonaldConjugator.mem_lambdaComp {nabla : Module.End L (Lambda L)}
    (h : IsMacdonaldConjugator q u nabla) (hone : nabla 1 = 1) (hM : (1 - q) * (1 - u) ≠ 0) :
    ∀ n : ℕ, ∀ f ∈ LambdaComp L n, nabla f ∈ LambdaComp L n := by
  have hword : ∀ w : List ℕ, nabla ((w.map (Dop q u)).prod 1)
      = (w.map fun k => Qop q u (k + 1) k).prod 1 := by
    intro w
    induction w with
    | nil => simpa using hone
    | cons k w ih =>
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
      rw [← qop_succ_apply_of_clauses h.map_dop_zero h.map_elemSymm_one_mul hM, ih]
  have key : ∀ g ∈ dopOrbit q u, ∀ n : ℕ,
      nabla (MvPolynomial.weightedHomogeneousComponent (fun i => i + 1) n g) ∈ LambdaComp L n := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, rfl⟩ := hx
      intro n
      have hmem := dop_word_apply_one_mem_lambdaComp q u w
      rw [MvPolynomial.weightedHomogeneousComponent_of_mem hmem]
      split_ifs with hn
      · subst hn; rw [hword]; exact qop_word_apply_one_mem_lambdaComp q u w
      · rw [map_zero]; exact zero_mem _
    | zero => intro n; rw [map_zero, map_zero]; exact zero_mem _
    | add x y _ _ hx hy => intro n; rw [map_add, map_add]; exact add_mem (hx n) (hy n)
    | smul c x _ hx => intro n; rw [map_smul, map_smul]; exact Submodule.smul_mem _ c (hx n)
  intro n f hf
  have hf' : f ∈ dopOrbit q u := by rw [dopOrbit_eq_top]; trivial
  have := key f hf' n
  simpa [MvPolynomial.weightedHomogeneousComponent_of_mem hf] using this

end Degree

end HJO.Sym
