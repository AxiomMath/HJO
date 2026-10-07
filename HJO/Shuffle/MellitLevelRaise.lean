/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.MellitNestTransfer

/-! # The level-raising operator, evaluated — and the factorization refuted

`HJO.Mellit.constantCoeff_lowerRun_stageWordTotal_append`
(`HJO/Shuffle/MellitLhsCompInduction.lean`) reduces an induction on the composition to a single
question, which its own docstring poses:

> does `ct ∘ d_-^ℓ ∘ (d_-^{(ℓ+1)}G_{ℓ+1,A})` factor through `ct ∘ d_-^ℓ`?

**It does not, and this file exhibits the witness.** No answer can be read off the *slope* side:
`HJO/Shuffle/MellitNestTransfer.lean` shows the iterated application and the doubled slope are both
free. What is proved here is the question itself, by evaluating the level-raising operator.

## The shape of the obstruction, independent of the slope

`HJO.Sweep.constantCoeff_lowerRun_stageTotal_eq_zero_of_factors` is the linear-algebra content, at
**every** `(a,b)`, every `ℓ` and every `A`: a factorization through `ct ∘ d_-^ℓ` forces the
composite to vanish on `ker(ct ∘ d_-^ℓ)`. So one element of that kernel on which the composite is
nonzero refutes the factorization outright.

At `ℓ = 1` the kernel of `ct ∘ d_-^{(1)}` on `V_1` is already nonzero in the *lowest* degree where
it can be: `d_-^{(1)}(Ce_1) = qe_1` and `d_-^{(1)}(y_1) = -e_1`, so

`F_0 = Ce_1 + qy_1`   (`HJO.Sweep.levelKernelOne`)

is killed (`HJO.Sweep.constantCoeff_lowerRun_one_levelKernelOne`). This is `a`- and `b`-independent:
`d_-` knows nothing about the slope.

## The evaluation

`HJO.Sweep.stageTotal_one_apply` puts the stage at `A = 1` in the form it is computed in — no `Z`
factor at all, `G_{k+1,1} = (-1)^{a-1}T_{k+1↘1}Ξ_{a,b}(-y_1d^*_+)` — at every `(a,b)` and every `k`,
and `HJO.Sweep.dplusStar_one_levelKernelOne` evaluates its innermost factor on the witness:

`-y_1d^*_+F_0 = -(Ce_1)y_1 - (q-1)uy_1^2 - qy_1y_2`.

Everything to that point is slope-independent, and what is left between it and the answer is exactly
`Ξ_{a,b}` read on the grading `2`. That is
`HJO.Sweep.lowerRun_two_stageTotal_levelKernelOne`, which holds at **every** `(a,b)`: it is the
precise remaining input, stated on one explicit vector.

At `(a,b) = (1,1)`, where `Ξ_{1,1} = 1` (`HJO.Sweep.slopeOperator_one_one`), the whole chain is
computed: the descending train is the single letter `T_1`, `d_-^{(2)}` and `d_-^{(1)}` are read by
`HJO.Sweep.dminus_auxVar_pow_mul` and `HJO.Sweep.dminus_auxVar_pow_mul_C` against the
Hall--Littlewood operators, and the answer is

`ct(d_-^{(1)}d_-^{(2)}G_{2,1}(F_0)) = u(1-q)e_2`
  (`HJO.Sweep.constantCoeff_lowerRun_two_stageTotal_levelKernelOne`).

Both `e_1^2` coefficients cancel identically and the surviving scalar is `u(1-q)` — **the same
scalar `u(q-1)` that `HJO.Mellit.theta_copComp_one_one` carries on the doubled-slope term**, up to
sign.
So the factorization fails by exactly the quantity the two-part clause has and the singleton clause
does not.

`HJO.Sweep.not_exists_factorization_one_one` is the refutation. Its hypotheses are `u ≠ 0` and
`q ≠ 1` — exactly the two parameters at which the defect `u(1-q)e_2` is `0`, so neither is
removable. Both are genericity the left-hand side already uses: `HJO.Sweep.lhsSlope_two_odd` asks
for `u ≠ 0` and `q ≠ 1` among its four hypotheses.

## What this does *not* settle

`(a,b) = (1,1)` is **outside** the range of the `hlhs` binder of
`HJO.Mellit.shuffle_of_lhs_and_induction`, which quantifies over coprime `1 < a < b`. The
computation above is the slope-independent half plus the `Ξ = 1` instance; the in-range slopes need
`Ξ_{a,b}` on the grading `2`, and `HJO.Sweep.slopeOperator_two_three` is computed only on the
grading `1`. So what is refuted here is the factorization *as posed*, not the factorization
restricted to the slopes `hlhs` ranges over.

## Genericity

`HJO.Sweep.stageTotal_one_apply`, `HJO.Sweep.trainDownEnd_two_one`,
`HJO.Sweep.dplusStar_one_levelKernelOne`, the two `d_-` bridges,
`HJO.Sweep.constantCoeff_lowerRun_one_levelKernelOne`,
`HJO.Sweep.constantCoeff_lowerRun_two_stageTotal_levelKernelOne` and
`HJO.Sweep.constantCoeff_lowerRun_stageTotal_eq_zero_of_factors`: **none** — not even `q ≠ 0`. Only
the final refutation needs `u ≠ 0` and `q ≠ 1`, and it needs them because at `u = 0` and at `q = 1`
the defect genuinely is `0`: there the factorization question is *not* refuted by this witness, and
the evaluation says the composite kills `F_0`.
-/

@[expose] public section

namespace HJO.Sweep

open HJO.Sym

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-! ### Two elementary facts about the graded pieces and the scalars -/

omit [Algebra ℚ L] in
theorem C_mem_piece (f : Sym.Lambda L) (k : ℕ) : (MvPolynomial.C f : Total L) ∈ piece L k := by
  rw [← MvPolynomial.algebraMap_eq]
  exact (piece L k).algebraMap_mem f

omit [Algebra ℚ L] in
theorem scal_mul_eq_smul_total (x : L) (F : Total L) : (scal x : Total L) * F = x • F := by
  rw [scal_eq_algebraMap, Algebra.smul_def]

omit [Algebra ℚ L] in
theorem scal_mul_C (x : L) (f : Sym.Lambda L) :
    (scal x : Total L) * MvPolynomial.C f = MvPolynomial.C (x • f) := by
  rw [MvPolynomial.smul_eq_C_mul, scal, ← MvPolynomial.C_mul]

/-! ### The stage at one part carries no `Z` factor -/

/-- **`G_{k+1,1} = (-1)^{a-1}T_{k+1↘1}Ξ_{a,b}(-y_1d^*_+)`.** At `A = 1` the replicated letter of
`HJO.Mellit.stageTotal` occurs to the power `0`, so the stage is the descending train after the
slope operator after the one-letter prefix `-y_1d^*_+`, and no `Z` — hence no `(qu)^{-1}` beyond the
slope word's own — occurs. Unconditional, at every `(a,b)` and every grading. -/
theorem stageTotal_one_apply (q u : L) (a b k : ℕ) (F : Total L) :
    Mellit.stageTotal q u a b k 1 F
      = ((-1 : L) ^ (a - 1)) • trainDownEnd q (k + 1) 1
          (slopeOperator q u (k + 1) a b (-((auxVar 1 : Total L) * dplusStar q u k F))) := by
  rw [Mellit.stageTotal, Nat.sub_self, pow_zero, one_mul, Module.End.mul_apply,
    Mellit.replOneTotal]
  simp only [LinearMap.smul_apply, Module.End.mul_apply, LinearMap.neg_apply,
    LinearMap.mulLeft_apply, map_smul]

omit [Algebra ℚ L] in
/-- **`T_{2↘1} = T_1`.** The descending train from the grading `2` is the single letter. -/
theorem trainDownEnd_two_one (q : L) : trainDownEnd q 2 1 = braidEnd q 1 := by
  rw [trainDownEnd, Braid.trainDown, Braid.descendingWord]
  norm_num

omit [Algebra ℚ L] in
/-- `T_i` as an `L`-linear map, read off. -/
theorem braidEnd_apply' (q : L) (i : ℕ) (F : Total L) :
    braidEnd q i F = swapAux L i F + scal (q - 1) * (auxVar i : Total L) * dividedDiff i F := by
  rw [braidEnd, LinearMap.restrictScalars_apply, braid_apply]

/-! ### The two lowering bridges, in the shape this computation reads them -/

/-- `d_-^{(2)}(Cf·y_1^my_2^i) = C(B_if)·y_1^m`: the extraction at the grading `2` reads the
`y_2`-degree and leaves the `y_1`-degree alone. -/
theorem dminus_two_term (q : L) (i m : ℕ) (f : Sym.Lambda L) :
    dminus q 2 (MvPolynomial.C f * ((auxVar 1 : Total L) ^ m * (auxVar 2 : Total L) ^ i))
      = MvPolynomial.C (Sym.Bop q (i : ℤ) f) * (auxVar 1 : Total L) ^ m := by
  have hmem : ((auxVar 1 : Total L) ^ m * MvPolynomial.C f) ∈ piece L 1 :=
    mul_mem (pow_mem (auxVar_mem_piece le_rfl le_rfl) m) (C_mem_piece f 1)
  have h : dminus q 2 ((auxVar 2 : Total L) ^ i * ((auxVar 1 : Total L) ^ m * MvPolynomial.C f))
      = (auxVar 1 : Total L) ^ m * MvPolynomial.C (Sym.Bop q (i : ℤ) f) := by
    simpa using (dminus_auxVar_pow_mul q 1 i hmem).trans (bopExt_auxVar_pow_mul_C q i m f)
  rw [show (MvPolynomial.C f : Total L) * ((auxVar 1 : Total L) ^ m * (auxVar 2 : Total L) ^ i)
      = (auxVar 2 : Total L) ^ i * ((auxVar 1 : Total L) ^ m * MvPolynomial.C f) from by ring, h]
  ring

/-! ### The witness in the kernel of `ct ∘ d_-^{(1)}` -/

/-- **`F_0 = Ce_1 + qy_1`**, the lowest-degree element of `V_1` that `ct ∘ d_-^{(1)}` kills. -/
noncomputable def levelKernelOne (q : L) : Total L :=
  MvPolynomial.C (Sym.elemSymm L 1) + q • (auxVar 1 : Total L)

theorem levelKernelOne_mem_piece (q : L) : levelKernelOne q ∈ piece L 1 := by
  rw [levelKernelOne, ← scal_mul_eq_smul_total]
  exact add_mem (C_mem_piece _ _) (mul_mem (C_mem_piece _ _) (auxVar_mem_piece le_rfl le_rfl))

/-- **`ct(d_-^{(1)}F_0) = 0`.** `B_0e_1 = qe_1` and `B_1 1 = -e_1`, and the two cancel.
Unconditional. -/
@[hjo "not_mellit_level_raise_factors"]
theorem constantCoeff_lowerRun_one_levelKernelOne (q : L) :
    MvPolynomial.constantCoeff (Mellit.lowerRun q 1 (levelKernelOne q)) = 0 := by
  have hrun : Mellit.lowerRun q 1 (levelKernelOne q) = dminus q 1 (levelKernelOne q) := by
    rw [Mellit.lowerRun, Mellit.lowerRun, Module.End.mul_apply, Module.End.one_apply]
  have h1 : dminus q 1 (MvPolynomial.C (Sym.elemSymm L 1) : Total L)
      = MvPolynomial.C (Sym.Bop q ((0 : ℕ) : ℤ) (Sym.elemSymm L 1)) := by
    simpa using dminus_one_auxVar_pow_mul_C q 0 (Sym.elemSymm L 1)
  have h2 : dminus q 1 ((auxVar 1 : Total L))
      = MvPolynomial.C (Sym.Bop q ((1 : ℕ) : ℤ) (1 : Sym.Lambda L)) := by
    simpa using dminus_one_auxVar_pow_mul_C q 1 (1 : Sym.Lambda L)
  have halt1 : Sym.elemSymmAlt L (1 : ℤ) = -Sym.elemSymm L 1 := by
    rw [show (1 : ℤ) = ((1 : ℕ) : ℤ) from rfl, Sym.elemSymmAlt_natCast]; simp
  rw [hrun, levelKernelOne, map_add, map_smul, h1, h2, ← scal_mul_eq_smul_total]
  simp only [scal, map_add, map_mul, MvPolynomial.constantCoeff_C]
  rw [show ((0 : ℕ) : ℤ) = 0 from rfl, show ((1 : ℕ) : ℤ) = 1 from rfl,
    Sym.bop_zero_elemSymm_one, Sym.bop_one, halt1]
  ring

/-! ### The slope-independent half of the level-raising operator -/

/-- **`d^*_+F_0 = Ce_1 + (q-1)uy_1 + qy_2`.** The plethystic shift adds the letter `(q-1)y_2` to
`e_1 = p_1` and the cycle wraps that letter round to `uy_1`; the `y_1` of `F_0` itself moves up to
`y_2`. Unconditional. -/
theorem dplusStar_one_levelKernelOne (q u : L) :
    dplusStar q u 1 (levelKernelOne q)
      = MvPolynomial.C (Sym.elemSymm L 1) + scal ((q - 1) * u) * (auxVar 1 : Total L)
        + scal q * (auxVar 2 : Total L) := by
  have hE : (MvPolynomial.C (Sym.elemSymm L 1) : Total L)
      = MvPolynomial.C (Sym.powerSum L (0 + 1)) := by
    rw [Sym.elemSymm_one L]
  have h1 : dplusStar q u 1 (MvPolynomial.C (Sym.elemSymm L 1) : Total L)
      = MvPolynomial.C (Sym.elemSymm L 1) + scal ((q - 1) * u) * (auxVar 1 : Total L) := by
    rw [dplusStar_apply, hE, show (1 : ℕ) + 1 = 2 from rfl, qshift_powerSum, map_add, map_mul,
      map_pow, cycleShift_C, cycleShift_scal,
      show (auxVar 2 : Total L) = auxVar (1 + 1) from rfl, cycleShift_auxVar_last,
      ← Sym.elemSymm_one L]
    simp only [zero_add, pow_one, scal_mul]
    ring
  have h2 : dplusStar q u 1 (auxVar 1 : Total L) = (auxVar 2 : Total L) := by
    simpa using dplusStar_auxVar_pow q u (i := 1) (k := 1) le_rfl le_rfl 1
  rw [levelKernelOne, map_add, map_smul, h1, h2, ← scal_mul_eq_smul_total]

/-! ### The whole chain at `(a,b) = (1,1)` -/

/-- The argument the slope operator is handed, on the witness:
`-y_1d^*_+F_0 = -(Ce_1)y_1 - (q-1)uy_1^2 - qy_1y_2`. Unconditional. -/
theorem slopeArg_levelKernelOne (q u : L) :
    -((auxVar 1 : Total L) * dplusStar q u 1 (levelKernelOne q))
      = -(MvPolynomial.C (Sym.elemSymm L 1) * (auxVar 1 : Total L))
        - scal ((q - 1) * u) * (auxVar 1 : Total L) ^ 2
        - scal q * ((auxVar 1 : Total L) * (auxVar 2 : Total L)) := by
  rw [dplusStar_one_levelKernelOne]
  ring

/-! ### `T_1` on the three monomials the argument is built from -/

omit [Algebra ℚ L] in
theorem swapAux_one_auxVar_two : swapAux L 1 (auxVar 2 : Total L) = (auxVar 1 : Total L) := by
  rw [show (auxVar 2 : Total L) = MvPolynomial.X 1 from rfl, swapAux_X, Nat.sub_self,
    Equiv.swap_apply_right]
  rfl

omit [Algebra ℚ L] in
theorem braidEnd_one_C_mul_auxVar_one (q : L) (f : Sym.Lambda L) :
    braidEnd q 1 (MvPolynomial.C f * (auxVar 1 : Total L))
      = MvPolynomial.C f * (auxVar 2 : Total L)
        - scal (q - 1) * ((auxVar 1 : Total L) * MvPolynomial.C f) := by
  have hd : dividedDiff 1 (MvPolynomial.C f * (auxVar 1 : Total L)) = -MvPolynomial.C f := by
    refine (dividedDiff_unique le_rfl ?_).symm
    rw [map_mul, swapAux_C, swapAux_auxVar_self le_rfl,
      show (MvPolynomial.X 1 - MvPolynomial.X (1 - 1) : Total L)
        = (auxVar 2 : Total L) - (auxVar 1 : Total L) from rfl]
    ring
  rw [braidEnd_apply', map_mul, swapAux_C, swapAux_auxVar_self le_rfl, hd]
  ring

omit [Algebra ℚ L] in
theorem braidEnd_one_auxVar_one_sq (q : L) :
    braidEnd q 1 ((auxVar 1 : Total L) ^ 2)
      = (auxVar 2 : Total L) ^ 2
        - scal (q - 1) *
            ((auxVar 1 : Total L) * ((auxVar 1 : Total L) + (auxVar 2 : Total L))) := by
  have hd : dividedDiff 1 ((auxVar 1 : Total L) ^ 2)
      = -((auxVar 1 : Total L) + (auxVar 2 : Total L)) := by
    refine (dividedDiff_unique le_rfl ?_).symm
    rw [map_pow, swapAux_auxVar_self le_rfl,
      show (MvPolynomial.X 1 - MvPolynomial.X (1 - 1) : Total L)
        = (auxVar 2 : Total L) - (auxVar 1 : Total L) from rfl]
    ring
  rw [braidEnd_apply', map_pow, swapAux_auxVar_self le_rfl, hd]
  ring

omit [Algebra ℚ L] in
theorem braidEnd_one_auxVar_one_mul_auxVar_two (q : L) :
    braidEnd q 1 ((auxVar 1 : Total L) * (auxVar 2 : Total L))
      = (auxVar 1 : Total L) * (auxVar 2 : Total L) := by
  have hd : dividedDiff 1 ((auxVar 1 : Total L) * (auxVar 2 : Total L)) = 0 := by
    refine (dividedDiff_unique le_rfl ?_).symm
    rw [map_mul, swapAux_auxVar_self le_rfl, swapAux_one_auxVar_two]
    ring
  rw [braidEnd_apply', map_mul, swapAux_auxVar_self le_rfl, swapAux_one_auxVar_two, hd]
  ring

/-- `T_1` on the argument, expanded on the monomial basis of the grading `2`. The scalars are kept
outside the `Λ`-coefficient, so that the `L`-linearity of `d_-` reads them off unchanged. -/
theorem braidEnd_one_slopeArg_levelKernelOne (q u : L) :
    braidEnd q 1 (-((auxVar 1 : Total L) * dplusStar q u 1 (levelKernelOne q)))
      = (-1 : L) • (MvPolynomial.C (Sym.elemSymm L 1)
            * ((auxVar 1 : Total L) ^ 0 * (auxVar 2 : Total L) ^ 1))
        + (q - 1) • (MvPolynomial.C (Sym.elemSymm L 1)
            * ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 0))
        + (-((q - 1) * u)) • (MvPolynomial.C (1 : Sym.Lambda L)
            * ((auxVar 1 : Total L) ^ 0 * (auxVar 2 : Total L) ^ 2))
        + ((q - 1) ^ 2 * u) • (MvPolynomial.C (1 : Sym.Lambda L)
            * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 0))
        + ((q - 1) ^ 2 * u - q) • (MvPolynomial.C (1 : Sym.Lambda L)
            * ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 1)) := by
  have hsc1 : (scal ((q - 1) * u) : Total L) * (auxVar 1 : Total L) ^ 2
      = ((q - 1) * u) • ((auxVar 1 : Total L) ^ 2) := scal_mul_eq_smul_total _ _
  have hsc2 : (scal q : Total L) * ((auxVar 1 : Total L) * (auxVar 2 : Total L))
      = q • ((auxVar 1 : Total L) * (auxVar 2 : Total L)) := scal_mul_eq_smul_total _ _
  rw [slopeArg_levelKernelOne, hsc1, hsc2, map_sub, map_sub, map_neg, map_smul, map_smul,
    braidEnd_one_C_mul_auxVar_one, braidEnd_one_auxVar_one_sq,
    braidEnd_one_auxVar_one_mul_auxVar_two]
  simp only [← scal_mul_eq_smul_total, scal, map_sub, map_mul, map_neg, map_one, map_pow]
  ring

/-- `d_-^{(1)}(Cf·y_1^m) = C(B_mf)`, the bridge in the order this computation produces. -/
theorem dminus_one_term (q : L) (m : ℕ) (f : Sym.Lambda L) :
    dminus q 1 (MvPolynomial.C f * (auxVar 1 : Total L) ^ m)
      = MvPolynomial.C (Sym.Bop q (m : ℤ) f) := by
  rw [mul_comm]
  exact dminus_one_auxVar_pow_mul_C q m f

/-- **`d_-^{(2)}T_1(-y_1d^*_+F_0)`** at `(a,b) = (1,1)`, an element of the grading `1`:
`Ce_1^2 + (q-1)(1-u)Ce_2 + (q(q-1) + q - (q-1)^2u)(Ce_1)y_1 + (q-1)^2u·y_1^2`. -/
theorem dminus_two_braidEnd_one_slopeArg (q u : L) :
    dminus q 2 (braidEnd q 1 (-((auxVar 1 : Total L) * dplusStar q u 1 (levelKernelOne q))))
      = MvPolynomial.C (Sym.elemSymm L 1 * Sym.elemSymm L 1) * (auxVar 1 : Total L) ^ 0
        + ((q - 1) * (1 - u)) •
            (MvPolynomial.C (Sym.elemSymm L 2) * (auxVar 1 : Total L) ^ 0)
        + (q * (q - 1) + q - (q - 1) ^ 2 * u) •
            (MvPolynomial.C (Sym.elemSymm L 1) * (auxVar 1 : Total L) ^ 1)
        + ((q - 1) ^ 2 * u) • (MvPolynomial.C (1 : Sym.Lambda L) * (auxVar 1 : Total L) ^ 2) := by
  have halt0 : Sym.elemSymmAlt L (0 : ℤ) = 1 := Sym.elemSymmAlt_zero
  have halt1 : Sym.elemSymmAlt L (1 : ℤ) = -Sym.elemSymm L 1 := by
    rw [show (1 : ℤ) = ((1 : ℕ) : ℤ) from by norm_num, Sym.elemSymmAlt_natCast]
    simp
  have halt2 : Sym.elemSymmAlt L (2 : ℤ) = Sym.elemSymm L 2 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from by norm_num, Sym.elemSymmAlt_natCast]
    simp
  rw [braidEnd_one_slopeArg_levelKernelOne, map_add, map_add, map_add, map_add,
    map_smul, map_smul, map_smul, map_smul, map_smul,
    dminus_two_term, dminus_two_term, dminus_two_term, dminus_two_term, dminus_two_term]
  simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
  rw [Sym.bop_one_elemSymm_one, Sym.bop_zero_elemSymm_one, Sym.bop_one, Sym.bop_one, Sym.bop_one,
    halt0, halt1, halt2]
  simp only [← scal_mul_eq_smul_total, scal, map_sub, map_add, map_mul, map_neg, map_one, map_pow]
  ring

/-- **The level-raising operator, evaluated at `(a,b) = (1,1)`, `ℓ = A = 1`:**
`d_-^{(1)}d_-^{(2)}G_{2,1}(F_0) = C(u(1-q)e_2)`. The `e_1^2` and `e_1e_2`-free parts cancel
identically. Unconditional. -/
theorem dminus_one_dminus_two_stage_levelKernelOne (q u : L) :
    dminus q 1 (dminus q 2
        (braidEnd q 1 (-((auxVar 1 : Total L) * dplusStar q u 1 (levelKernelOne q)))))
      = MvPolynomial.C ((u * (1 - q)) • Sym.elemSymm L 2) := by
  have halt2 : Sym.elemSymmAlt L (2 : ℤ) = Sym.elemSymm L 2 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from by norm_num, Sym.elemSymmAlt_natCast]
    simp
  have hb0sq : Sym.Bop q (0 : ℤ) (Sym.elemSymm L 1 * Sym.elemSymm L 1)
      = (1 - 2 * ((1 - q) * (1 - (0 : L)))) • (Sym.elemSymm L 1 * Sym.elemSymm L 1)
        + ((1 - q) * (1 - (0 : L))) ^ 2 • Sym.elemSymm L 2 := by
    rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from by norm_num, Sym.bop_natCast,
      Sym.dop_zero_elemSymm_one_sq]
  have hb0e2 : Sym.Bop q (0 : ℤ) (Sym.elemSymm L 2)
      = Sym.elemSymm L 2 - (1 - q) • (Sym.elemSymm L 1 * Sym.elemSymm L 1)
        - (q * (1 - q)) • Sym.elemSymm L 2 := by
    rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from by norm_num]
    exact Sym.bop_zero_elemSymm_two q
  rw [dminus_two_braidEnd_one_slopeArg, map_add, map_add, map_add,
    map_smul, map_smul, map_smul,
    dminus_one_term, dminus_one_term, dminus_one_term, dminus_one_term]
  simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
  rw [hb0sq, hb0e2, Sym.bop_one_elemSymm_one, Sym.bop_one, halt2]
  simp only [← scal_mul_eq_smul_total, scal_mul_C, ← map_add]
  congr 1
  simp only [MvPolynomial.smul_eq_C_mul, map_sub, map_add, map_mul, map_one, map_pow,
    map_ofNat, map_zero]
  ring

/-- **The level-raising evaluation at `(a,b) = (1,1)`, `ℓ = A = 1`:**

`ct(d_-^{(1)}d_-^{(2)}G_{2,1}(F_0)) = u(1-q)e_2`.

The `e_1^2` coefficient cancels identically; the surviving scalar is `u(1-q)`. Unconditional --
no `q ≠ 0`, no `q ≠ 1`, no `u ≠ 0`. -/
@[hjo "not_mellit_level_raise_factors"]
theorem constantCoeff_lowerRun_two_stageTotal_levelKernelOne (q u : L) :
    MvPolynomial.constantCoeff
        (Mellit.lowerRun q 2 (Mellit.stageTotal q u 1 1 1 1 (levelKernelOne q)))
      = (u * (1 - q)) • Sym.elemSymm L 2 := by
  have hstage : Mellit.stageTotal q u 1 1 1 1 (levelKernelOne q)
      = braidEnd q 1 (-((auxVar 1 : Total L) * dplusStar q u 1 (levelKernelOne q))) := by
    rw [stageTotal_one_apply, Nat.sub_self, pow_zero, one_smul,
      show (1 : ℕ) + 1 = 2 from rfl, trainDownEnd_two_one, slopeOperator_one_one,
      Module.End.one_apply]
  have hrun : ∀ F : Total L, Mellit.lowerRun q 2 F = dminus q 1 (dminus q 2 F) := by
    intro F
    rw [Mellit.lowerRun, Module.End.mul_apply, Mellit.lowerRun, Module.End.mul_apply,
      Mellit.lowerRun, Module.End.one_apply]
  rw [hstage, hrun, dminus_one_dminus_two_stage_levelKernelOne, MvPolynomial.constantCoeff_C]

/-! ### The residual at a general slope: everything but `Ξ_{a,b}` -/

/-- `d_-^2` on the grading `2`, read off: `HJO.Mellit.lowerRun` at `2` is `d_-^{(1)}d_-^{(2)}`. -/
theorem lowerRun_two_apply (q : L) (F : Total L) :
    Mellit.lowerRun q 2 F = dminus q 1 (dminus q 2 F) := by
  rw [Mellit.lowerRun, Module.End.mul_apply, Mellit.lowerRun, Module.End.mul_apply,
    Mellit.lowerRun, Module.End.one_apply]

/-- **The precise remaining input, at every slope.** For every `(a,b)`, the composite of the
clause's right-hand side on the kernel witness is `Ξ_{a,b}` read on the grading `2`, applied to ONE
explicit vector, under `T_1` and two lowerings:

`d_-^2G_{2,1}(F_0)`
  `= (-1)^{a-1}d_-^{(1)}d_-^{(2)}T_1Ξ^{(2)}_{a,b}(-(Ce_1)y_1 - (q-1)uy_1^2 - qy_1y_2)`.

Nothing on the left of `Ξ_{a,b}` depends on the slope, and nothing on its right does either: the
`(-1)^{a-1}` of `HJO.Mellit.replOneTotal`, the descending train `T_{2↘1} = T_1`, the prefix
`-y_1d^*_+` and the witness are all slope-free. Unconditional. -/
theorem lowerRun_two_stageTotal_levelKernelOne (q u : L) (a b : ℕ) :
    Mellit.lowerRun q 2 (Mellit.stageTotal q u a b 1 1 (levelKernelOne q))
      = ((-1 : L) ^ (a - 1)) • dminus q 1 (dminus q 2 (braidEnd q 1
          (slopeOperator q u 2 a b
            (-(MvPolynomial.C (Sym.elemSymm L 1) * (auxVar 1 : Total L))
              - scal ((q - 1) * u) * (auxVar 1 : Total L) ^ 2
              - scal q * ((auxVar 1 : Total L) * (auxVar 2 : Total L)))))) := by
  rw [stageTotal_one_apply, show (1 : ℕ) + 1 = 2 from rfl, trainDownEnd_two_one, map_smul,
    lowerRun_two_apply, slopeArg_levelKernelOne]

/-! ### The refutation -/

/-- **A factorization through `ct ∘ d_-^ℓ` forces the composite to vanish on its kernel.** Linear
algebra, at every `(a,b)`, every `ℓ` and every `A`, with no hypothesis on `q` or `u`: the value at
`F = 0` pins `φ(0) = 0`. This is what makes one witness decisive. -/
@[hjo "not_mellit_level_raise_factors"]
theorem constantCoeff_lowerRun_stageTotal_eq_zero_of_factors {a b l A : ℕ}
    {φ : Sym.Lambda L → Sym.Lambda L}
    (hφ : ∀ F ∈ piece L l, MvPolynomial.constantCoeff
        (Mellit.lowerRun q (l + 1) (Mellit.stageTotal q u a b l A F))
      = φ (MvPolynomial.constantCoeff (Mellit.lowerRun q l F)))
    {F : Total L} (hF : F ∈ piece L l)
    (h0 : MvPolynomial.constantCoeff (Mellit.lowerRun q l F) = 0) :
    MvPolynomial.constantCoeff
      (Mellit.lowerRun q (l + 1) (Mellit.stageTotal q u a b l A F)) = 0 := by
  have hz := hφ 0 (zero_mem _)
  simp only [map_zero] at hz
  rw [hφ F hF, h0, ← hz]

/-- **`ct ∘ d_-^ℓ ∘ (d_-^{(ℓ+1)}G_{ℓ+1,A})` does NOT factor through `ct ∘ d_-^ℓ`**, at `ℓ = A = 1`
and `(a,b) = (1,1)`.

The witness is `F_0 = Ce_1 + qy_1`: it lies in `V_1`, `ct(d_-^{(1)}F_0) = 0`, and
`ct(d_-^{(1)}d_-^{(2)}G_{2,1}F_0) = u(1-q)e_2 ≠ 0`. Any `φ` would have to send `0` both to `0`
(from `F = 0`) and to `u(1-q)e_2`.

The two hypotheses are exactly where the defect lives: at `u = 0` and at `q = 1` it vanishes. Both
are genericity the left-hand side already uses. -/
@[hjo "not_mellit_level_raise_factors"]
theorem not_exists_factorization_one_one (hu : u ≠ 0) (hq1 : q ≠ 1) :
    ¬ ∃ φ : Sym.Lambda L → Sym.Lambda L, ∀ F ∈ piece L 1,
      MvPolynomial.constantCoeff (Mellit.lowerRun q 2 (Mellit.stageTotal q u 1 1 1 1 F))
        = φ (MvPolynomial.constantCoeff (Mellit.lowerRun q 1 F)) := by
  rintro ⟨φ, hφ⟩
  have hφ' : ∀ F ∈ piece L 1, MvPolynomial.constantCoeff
      (Mellit.lowerRun q (1 + 1) (Mellit.stageTotal q u 1 1 1 1 F))
      = φ (MvPolynomial.constantCoeff (Mellit.lowerRun q 1 F)) := by
    simpa using hφ
  have h := constantCoeff_lowerRun_stageTotal_eq_zero_of_factors hφ'
    (levelKernelOne_mem_piece q) (constantCoeff_lowerRun_one_levelKernelOne q)
  rw [show (1 : ℕ) + 1 = 2 from rfl,
    constantCoeff_lowerRun_two_stageTotal_levelKernelOne q u] at h
  rcases smul_eq_zero.1 h with hc | he
  · rcases mul_eq_zero.1 hc with h1 | h2
    · exact hu h1
    · exact hq1 (sub_eq_zero.1 h2).symm
  · exact Sym.elemSymm_succ_ne_zero 1 he

end HJO.Sweep

end
