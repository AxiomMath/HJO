/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepAppendWidth
public import HJO.Shuffle.ColouringStep

/-! # The `1 × 2` instance of `HJO.Mellit.SweepAppend`, evaluated: true iff `q ≠ 1`

`HJO.Mellit.not_sweepAppend_one_left` refutes `HJO.Mellit.SweepAppend` at `q = 1` by showing that
one type-`C` event kills the sweep word. That leaves a question a refutation on its own cannot
answer: is `HJO.Mellit.dsc` at that colouring zero for *every* `q`, in which case the identity
would be wrong for a reason having nothing to do with the scalar? This file settles it by
**evaluating both sides** at the smallest instance with a corner in it — `α = []`, `A = 1`,
`(a,b) = (1,2)` — and finds them equal at every `q ≠ 1`.

## The left side, unconditionally

`HJO.Mellit.aboveReturnPaths 1 2 1 (1)` is the singleton `{HJO.Mellit.baseEx}`
(`HJO.Mellit.aboveReturnPaths_one_two`): an above-diagonal `(1,2)`-path has `ŷ_0 = 0` and
`ŷ_1 = 2`, and `HJO.Paths.Heights 1 2 1` has nothing else in it
(`HJO.Mellit.eq_baseEx`). The sweep word of that path above `HJO.Mellit.sepLevel 1 1 = 3/2` is two
events, peeled one at a time by `HJO.Mellit.partialSweepWord_eq_sweepOperator_mul`, so no
rank listing is ever computed:

* `(0,2)`, of rank `4`: type `A`, width `0`, operator `d_+^{(0)}`;
* `(0,1)`, of rank `2`: type `C`, width `1`, `a_{P̂} = 0`, operator `Δ^{(1)}`.

The ranks, event types, widths and right counts are all read off the explicit path by `decide`.
So `HJO.Mellit.dsc_one_two_eq`: `D_{3/2,c_{(1)}} = Δ^{(1)}(d_+^{(0)}(1))`, with no hypothesis on
`q` at all. At `q = 1` that is `0`, which is `HJO.Mellit.dsc_one_eq_zero` again by another route.

## The corner operator on `y_1`

What remains is one computation in `HJO.Sweep.corner`, done here in full:
`HJO.Sweep.corner_one_X_zero`, `Δ^{(1)}(y_1) = -y_1^2` for `q ≠ 1`. The two composites are
`d_-^{(2)}d_+^{(1)}(y_1) = e_1y_1` and `d_+^{(0)}d_-^{(1)}(y_1) = e_1y_1 + (q-1)y_1^2`; they agree
except for the single term `(q-1)y_1^2`, and `(q-1)^{-1}` cancels it. The term comes from `τ_{1,1}`
of `HJO.Sweep.qshift` substituting the letter `(q-1)y_1` into `p_1 = e_1`
(`HJO.Sweep.dplus_zero_C_elemSymm_one`), which is exactly the residue `HJO.Sweep.corner_one_one`
sees on the vacuum. On the way: `d_+^{(1)}(y_1) = -y_1y_2` because `T_1` fixes the symmetric product
`y_1y_2` (`HJO.Sweep.dplus_one_X_zero`), and `d_-^{(2)}(y_1y_2) = -e_1y_1` by the coefficient
extraction of `HJO.Sweep.dminus` on one monomial (`HJO.Sweep.dminus_two_X_zero_mul_X_one`).

Both `HJO.Sweep.corner_one_one` (`Δ^{(1)}(1) = -y_1`) and `HJO.Sweep.corner_one_X_zero` are
instances of `Δ^{(1)}(y_1^m) = -y_1^{m+1}`, which is what makes
`HJO.Mellit.replOneTotal_one_left`'s `(-y_1)^b` the value of the `1 × b` sweep for every `b`. Only
`m ≤ 1` is proved here, which is what the `b = 2` instance needs.

## What this settles

`HJO.Mellit.sweepAppend_nil_one_one_two` is the `append` field's identity written out at
`α = []`, `A = 1`, `(a,b) = (1,2)` and proved for `q ≠ 1`. With
`HJO.Mellit.not_sweepAppend_one_left` at the same parameters, the two together say that the
hypothesis `HJO.Mellit.SweepAppend` is missing is `q ≠ 1`, and that nothing else at this instance is
wrong: the sign `(-1)^{(a-1)A}`, the scalar `(qu)^{1-A}`, `HJO.Mellit.sepLevel`,
`HJO.Mellit.stageTotal` and the path form of
`HJO.Mellit.isAdmissibleColouring_and_sum_sweepChar_eq_smul_dsc` are all confirmed against the sweep
process itself, at a nonempty colouring and without assuming `SweepAppend`.
-/

@[expose] public section

open Finset

namespace HJO.Sym

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- `e_1 = p_1`: Newton's identity at `n = 1`, where the sum has one term. -/
theorem elemSymm_one_eq_powerSum : Sym.elemSymm L 1 = Sym.powerSum L 1 := by
  rw [Sym.elemSymm]
  simp [Sym.elemSymm]

end HJO.Sym

namespace HJO.Sweep

variable {L : Type*} [Field L] [Algebra ℚ L] (q : L)

omit [Algebra ℚ L] q in
theorem monomial_single_one_eq_X (n : ℕ) :
    (MvPolynomial.monomial (Finsupp.single n 1) 1 : Total L) = MvPolynomial.X n := by
  rw [← MvPolynomial.X_pow_eq_monomial, pow_one]

omit [Algebra ℚ L] q in
theorem monomial_X_zero_X_one :
    (MvPolynomial.X 0 * MvPolynomial.X 1 : Total L)
      = MvPolynomial.monomial (Finsupp.single 0 1 + Finsupp.single 1 1) 1 := by
  rw [← monomial_single_one_eq_X (L := L) 0, ← monomial_single_one_eq_X (L := L) 1,
    MvPolynomial.monomial_mul, mul_one]

omit [Algebra ℚ L] q in
/-- `∂_1(y_1y_2) = 0`: the product is symmetric in the two variables. -/
theorem dividedDiff_one_X_zero_mul_X_one :
    dividedDiff 1 ((MvPolynomial.X 0 * MvPolynomial.X 1 : Total L)) = 0 :=
  (dividedDiff_unique le_rfl (by
    rw [mul_zero, map_mul, swapAux_X, swapAux_X]
    norm_num [mul_comm])).symm

omit [Algebra ℚ L] q in
/-- `∂_1(y_2y_1) = 0`. -/
theorem dividedDiff_one_X_one_mul_X_zero :
    dividedDiff 1 ((MvPolynomial.X 1 * MvPolynomial.X 0 : Total L)) = 0 := by
  rw [mul_comm]; exact dividedDiff_one_X_zero_mul_X_one

omit [Algebra ℚ L] in
/-- **`d_+^{(1)}(y_1) = -y_1y_2`.** The train `T_1` fixes `y_1y_2`, which is symmetric. -/
theorem dplus_one_X_zero :
    dplus q 1 (MvPolynomial.X 0 : Total L) = -(MvPolynomial.X 0 * MvPolynomial.X 1) := by
  rw [dplus]
  simp only [LinearMap.neg_apply, LinearMap.coe_comp, Function.comp_apply,
    AlgHom.toLinearMap_apply, LinearMap.mulLeft_apply]
  rw [qshift_auxVar, auxVar_two, trainUpEnd_one_two, braidEnd, LinearMap.restrictScalars_apply,
    braid_apply, dividedDiff_one_X_one_mul_X_zero, mul_zero, add_zero, map_mul,
    swapAux_X, swapAux_X]
  norm_num [Equiv.swap_apply_left, Equiv.swap_apply_right, mul_comm]

/-- **`d_-^{(2)}(y_1y_2) = -e_1y_1`.** -/
theorem dminus_two_X_zero_mul_X_one :
    dminus q 2 ((MvPolynomial.X 0 * MvPolynomial.X 1 : Total L))
      = -(MvPolynomial.C (Sym.elemSymm L 1) * MvPolynomial.X 0) := by
  have hd1 : (Finsupp.single 0 1 + Finsupp.single 1 1 : ℕ →₀ ℕ) 1 = 1 := by simp
  have hde : Finsupp.erase 1 (Finsupp.single 0 1 + Finsupp.single 1 1 : ℕ →₀ ℕ)
      = Finsupp.single 0 1 := by
    ext j
    rcases eq_or_ne j 1 with rfl | hj
    · simp
    · simp
  rw [dminus, LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
    LinearMap.restrictScalars_apply, map_mul, qshiftNeg_auxVar, qshiftNeg_auxVar,
    monomial_X_zero_X_one, show (2 : ℕ) - 1 = 1 from rfl, lowerCoeff_monomial, hd1, hde,
    monomial_single_one_eq_X]
  ring

/-- **`d_-^{(1)}(y_1) = -e_1`.** -/
theorem dminus_one_X_zero :
    dminus q 1 (MvPolynomial.X 0 : Total L) = -MvPolynomial.C (Sym.elemSymm L 1) := by
  have h := dminus_auxVar_pow q 0 1
  rw [auxVar, pow_one, pow_one] at h
  simpa using h

/-- **`d_+^{(0)}(e_1) = -y_1e_1 - (q-1)y_1^2`.** The `τ_{1,1}` of `HJO.Sweep.qshift` puts the letter
`(q-1)y_1` into `p_1 = e_1`, and that extra term is what survives the corner difference. -/
theorem dplus_zero_C_elemSymm_one :
    dplus q 0 (MvPolynomial.C (Sym.elemSymm L 1) : Total L)
      = -(MvPolynomial.X 0 * MvPolynomial.C (Sym.elemSymm L 1))
        - scal (q - 1) * MvPolynomial.X 0 ^ 2 := by
  rw [show Sym.elemSymm L 1 = Sym.powerSum L (0 + 1) from
      by rw [Nat.zero_add]; exact Sym.elemSymm_one_eq_powerSum, dplus]
  simp only [LinearMap.neg_apply, LinearMap.coe_comp, Function.comp_apply,
    AlgHom.toLinearMap_apply, LinearMap.mulLeft_apply]
  rw [qshift_powerSum, Mellit.trainUpEnd_one_one, Module.End.one_apply]
  simp only [auxVar, Nat.add_sub_cancel]
  ring_nf

/-- **`Δ^{(1)}(y_1) = -y_1^2`**, for `q ≠ 1`. The two composites `d_-d_+` and `d_+d_-` agree except
for the single term `(q-1)y_1^2` that `τ_{1,1}` contributes, and `(q-1)^{-1}` cancels it. -/
theorem corner_one_X_zero (hq : q ≠ 1) :
    corner q 1 (MvPolynomial.X 0 : Total L) = -(MvPolynomial.X 0 ^ 2) := by
  have hq1 : q - 1 ≠ 0 := sub_ne_zero.2 hq
  have hsc : (scal ((q - 1)⁻¹) : Total L) * scal (q - 1) = 1 := by
    rw [scal, scal, ← map_mul, ← map_mul, inv_mul_cancel₀ hq1, map_one, map_one]
  have hbr : (dminus q (1 + 1) * dplus q 1 - dplus q (1 - 1) * dminus q 1)
        (MvPolynomial.X 0 : Total L)
      = -(scal (q - 1) * (MvPolynomial.X 0 : Total L) ^ 2) := by
    rw [show (1 : ℕ) + 1 = 2 from rfl, show (1 : ℕ) - 1 = 0 from rfl,
      LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
      dplus_one_X_zero, map_neg, dminus_two_X_zero_mul_X_one, dminus_one_X_zero,
      map_neg, dplus_zero_C_elemSymm_one]
    ring
  rw [corner, ite_eq_right (one_ne_zero (α := ℕ)), LinearMap.smul_apply, hbr, smul_neg,
    smul_eq_scal_mul, ← mul_assoc, hsc, one_mul]

end HJO.Sweep

namespace HJO.Mellit

open HJO.Sweep Paths

theorem eventType_baseEx_zero_one : eventType baseEx ((0, 1) : ℕ × ℕ) = EventType.C := by decide
theorem eventType_baseEx_zero_two : eventType baseEx ((0, 2) : ℕ × ℕ) = EventType.A := by decide
theorem sweepWidth_baseEx_zero_one : sweepWidth baseEx ((0, 1) : ℕ × ℕ) = 1 := by decide
theorem sweepWidth_baseEx_zero_two : sweepWidth baseEx ((0, 2) : ℕ × ℕ) = 0 := by decide
theorem sweepRight_baseEx_zero_one : sweepRight baseEx ((0, 1) : ℕ × ℕ) = 0 := by decide

theorem mem_sweptRegion_baseEx_zero_one : ((0, 1) : ℕ × ℕ) ∈ sweptRegion baseEx := by decide
theorem mem_sweptRegion_baseEx_zero_two : ((0, 2) : ℕ × ℕ) ∈ sweptRegion baseEx := by decide

theorem pointRank_baseEx_zero_one : pointRank 1 2 1 ((0, 1) : ℕ × ℕ) = 2 := by decide
theorem pointRank_baseEx_zero_two : pointRank 1 2 1 ((0, 2) : ℕ × ℕ) = 4 := by decide

theorem pointRank_ne_three : ∀ Q ∈ Iic 1 ×ˢ Iic 2, pointRank 1 2 1 Q ≠ 3 := by decide

theorem pointRank_le_four : ∀ Q ∈ sweptRegion baseEx, pointRank 1 2 1 Q ≤ 4 := by decide

/-- The above-diagonal path of the `1 × 2` rectangle is forced. -/
theorem eq_baseEx {y : Heights 1 2 1} (hy : IsAboveDiagonal y) : y = baseEx := by
  have h0 : ht y 0 = 0 := hy.1
  have h1 : ht y 1 = 2 := by simpa using hy.2.1
  funext r
  have hlt := r.isLt
  have hr : (r : ℕ) = 0 ∨ (r : ℕ) = 1 := by omega
  apply Fin.val_injective
  rw [← ht_coe y r, ← ht_coe baseEx r]
  rcases hr with hr | hr <;> rw [hr]
  · rw [h0]; decide
  · rw [h1]; decide

theorem aboveReturnPaths_one_two : aboveReturnPaths 1 2 1 [1] = {baseEx} :=
  Finset.eq_singleton_iff_unique_mem.2
    ⟨mem_aboveReturnPaths_iff.2 hasAboveReturns_baseEx,
      fun _ hy => eq_baseEx (mem_aboveReturnPaths_iff.1 hy).1⟩

section Eval

variable {L : Type*} [Field L] [Algebra ℚ L]

theorem partialSweepWord_baseEx_high (q u : L) :
    partialSweepWord q u baseEx (9 / 2 : ℚ) = 1 := by
  refine partialSweepWord_of_forall_le q u baseEx _ fun P hP => ?_
  have h : pointRank 1 2 1 P ≤ 4 := pointRank_le_four P hP
  have : ((pointRank 1 2 1 P : ℤ) : ℚ) ≤ ((4 : ℤ) : ℚ) := by exact_mod_cast h
  push_cast at this ⊢
  linarith

theorem partialSweepWord_baseEx_mid (q u : L) :
    partialSweepWord q u baseEx (5 / 2 : ℚ) = dplus q 0 := by
  rw [partialSweepWord_eq_sweepOperator_mul q u one_pos (P := ((0, 2) : ℕ × ℕ))
      (ηhi := (9 / 2 : ℚ)) ⟨4, by norm_num⟩
      (by rw [pointRank_baseEx_zero_two]; norm_num)
      (by rw [pointRank_baseEx_zero_two]; norm_num)
      ?iso mem_sweptRegion_baseEx_zero_two,
    partialSweepWord_baseEx_high, mul_one, sweepOperator, eventType_baseEx_zero_two,
    sweepWidth_baseEx_zero_two]
  case iso =>
    intro Q hQ1 hQ2 hl hu
    have h3 : (3 : ℤ) ≤ pointRank 1 2 1 Q := by
      by_contra hc
      have h : pointRank 1 2 1 Q ≤ (2 : ℤ) := by omega
      have : ((pointRank 1 2 1 Q : ℤ) : ℚ) ≤ ((2 : ℤ) : ℚ) := by exact_mod_cast h
      push_cast at this
      linarith
    have h4 : pointRank 1 2 1 Q ≤ 4 := by
      by_contra hc
      have h : (5 : ℤ) ≤ pointRank 1 2 1 Q := by omega
      have : ((5 : ℤ) : ℚ) ≤ ((pointRank 1 2 1 Q : ℤ) : ℚ) := by exact_mod_cast h
      push_cast at this
      linarith
    have hne := pointRank_ne_three Q (Finset.mem_product.2 ⟨Finset.mem_Iic.2 (by omega),
      Finset.mem_Iic.2 (by omega)⟩)
    rw [pointRank_baseEx_zero_two]
    omega

theorem partialSweepWord_baseEx (q u : L) :
    partialSweepWord q u baseEx (sepLevel 1 1) = corner q 1 * dplus q 0 := by
  have hsep : sepLevel 1 1 = (3 / 2 : ℚ) := by rw [sepLevel]; norm_num
  rw [hsep, partialSweepWord_eq_sweepOperator_mul q u one_pos (P := ((0, 1) : ℕ × ℕ))
      (ηhi := (5 / 2 : ℚ)) ⟨2, by norm_num⟩
      (by rw [pointRank_baseEx_zero_one]; norm_num)
      (by rw [pointRank_baseEx_zero_one]; norm_num)
      ?iso mem_sweptRegion_baseEx_zero_one,
    partialSweepWord_baseEx_mid, sweepOperator, eventType_baseEx_zero_one,
    sweepWidth_baseEx_zero_one, sweepRight_baseEx_zero_one]
  · norm_num
  case iso =>
    intro Q hQ1 hQ2 hl hu
    have h2 : (2 : ℤ) ≤ pointRank 1 2 1 Q := by
      by_contra hc
      have h : pointRank 1 2 1 Q ≤ (1 : ℤ) := by omega
      have : ((pointRank 1 2 1 Q : ℤ) : ℚ) ≤ ((1 : ℤ) : ℚ) := by exact_mod_cast h
      push_cast at this
      linarith
    have h2' : pointRank 1 2 1 Q ≤ 2 := by
      by_contra hc
      have h : (3 : ℤ) ≤ pointRank 1 2 1 Q := by omega
      have : ((3 : ℤ) : ℚ) ≤ ((pointRank 1 2 1 Q : ℤ) : ℚ) := by exact_mod_cast h
      push_cast at this
      linarith
    rw [pointRank_baseEx_zero_one]
    omega

/-- **The invariant of the `1 × 2` rectangle at `c_{(1)}`, evaluated.** Unconditional in `q`. -/
theorem dsc_one_two_eq (q u : L) :
    dsc q u 1 2 1 (sepLevel 1 1) (compColouring 1 2 [1])
      = corner q 1 (dplus q 0 (1 : Total L)) := by
  rw [dsc_compColouring_eq_sum_partialSweepWord q u (isAdmissibleLevel_sepLevel 1 1)
      (separatesDiagonal_sepLevel' 1 2 1) (Nat.coprime_one_left 2) one_pos two_pos
      (by simp) (by simp),
    aboveReturnPaths_one_two, Finset.sum_singleton, partialSweepWord_baseEx,
    Module.End.mul_apply]


/-! ### The instance of `HJO.Mellit.SweepAppend` that fails at `q = 1` holds at every other `q` -/

/-- **`HJO.Mellit.SweepAppend` at `α = []`, `A = 1`, `(a,b) = (1,2)`, verbatim, and it is TRUE for
every `q ≠ 1`.** Both sides are `y_1^2`: the left by `HJO.Mellit.dsc_one_two_eq` and
`HJO.Sweep.corner_one_X_zero`, the right by `HJO.Mellit.dsc_empty_eq_one` and
`HJO.Mellit.stageTotal_one_left`. The scalar `(-1)^{(a-1)A}(qu)^{1-A}` of the `append` field is `1`
here, so no sign is being hidden.

Read with `HJO.Mellit.not_sweepAppend_one_left` this localises the defect exactly: the identity is
false at `q = 1` and true at every other scalar, so what `HJO.Mellit.SweepAppend` is missing at this
instance is the hypothesis `q ≠ 1` and nothing else. In particular the vanishing of
`HJO.Mellit.dsc_one_eq_zero` is not a symptom of the identity being wrong — the sign, the level, the
stage and `HJO.Mellit.isAdmissibleColouring_and_sum_sweepChar_eq_smul_dsc`'s path form all check out
here against the sweep itself. -/
theorem sweepAppend_nil_one_one_two (q u : L) (hq : q ≠ 1) :
    dsc q u 1 2 (([] : List ℕ).sum + 1) (sepLevel 1 (([] : List ℕ).sum + 1))
        (compColouring 1 2 ([] ++ [1]))
      = ((-1 : L) ^ ((1 - 1) * 1) * (q * u) ^ (1 - ((1 : ℕ) : ℤ))) •
          stageTotal q u 1 2 ([] : List ℕ).length 1
            (dsc q u 1 2 ([] : List ℕ).sum (sepLevel 1 ([] : List ℕ).sum)
              (compColouring 1 2 ([] : List ℕ))) := by
  have hc : compColouring 1 2 ([] : List ℕ) = (∅ : Finset (ℕ × ℕ)) := by simp [compColouring]
  have hone : dsc q u 1 2 0 (sepLevel 1 0) (compColouring 1 2 ([] : List ℕ)) = (1 : Total L) := by
    rw [hc]
    exact dsc_empty_eq_one q u (isAdmissibleLevel_sepLevel 1 0)
      (separatesDiagonal_sepLevel' 1 2 0) (Nat.coprime_one_left 2) one_pos two_pos
  simp only [List.sum_nil, List.length_nil, List.nil_append, Nat.zero_add]
  rw [hone, stageTotal_one_left q u two_pos, dsc_one_two_eq q u, dplus_zero_one, map_neg,
    corner_one_X_zero q hq]
  norm_num [auxVar]

end Eval

end HJO.Mellit

end
