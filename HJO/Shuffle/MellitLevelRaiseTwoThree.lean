/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.MellitLevelRaiseRow
public import HJO.Shuffle.MellitStraightMonomial

/-! # The value-based factorization FAILS inside `1 < a < b`, at `(a,b) = (2,3)`

`HJO.Sweep.not_exists_factorization_one_one` (`HJO/Shuffle/MellitLevelRaise.lean`) refuted the
factorization question of `HJO.Mellit.constantCoeff_lowerRun_stageWordTotal_append` at the **unit**
slope `(a,b) = (1,1)`, which is *outside* the range `1 < a < b` the `hlhs` binder of
`HJO.Mellit.shuffle_of_lhs_and_induction` quantifies over. This file settles the range, at its
smallest coprime point `(a,b) = (2,3)`, by computing the composite outright.

## The value

`HJO.Sweep.constantCoeff_lowerRun_two_stageTotal_levelKernelOne_two_three`: for `q ≠ 0`, `u ≠ 0`
and `q ≠ 1`,

`ct(d_-^{(1)}d_-^{(2)}G_{2,1}(F_0)) = u(q-1)·[e_2^2 + (q+u-1)e_1e_3 + (q^2+qu-q+u^2-u)e_4]`

on the kernel witness `F_0 = Ce_1 + qy_1` of `HJO.Sweep.levelKernelOne`. The leading coefficient is
`1` — the `e_2^2` term is *undeformed* — so the whole value is nonzero as soon as `u(q-1)` is, which
is exactly the two exclusions the `(1,1)` refutation already spends.

The chain, all of it in this file, is: `HJO.Sweep.slopeOperator_two_three_apply` reads the assembly
`Ξ^{(2)}_{2,3} = (-y_1)(qu)^{-1}z_1^{(2)}(-y_1)` of `HJO.Sweep.slopeOperator_two_odd` on a vector;
`HJO.Sweep.braidInvEnd_one_neg_auxVar_one_mul_slopeArgTwo` applies the train `T_1^{-1}` of
`z_1^{(2)}`, turning three monomials into five; `HJO.Sweep.zCommTwo_monomial'` turns each into the
grading-one defect `HJO.Sweep.zDefect`, whose five needed values are already evaluated; and
`HJO.Sweep.constantCoeff_lowerRun_two_C_mul_monomial` reads the result against seven compositions
`B_jB_m` of Hall--Littlewood operators, evaluated here in the `e`-basis off the known `D`-values.

## The refutation

`HJO.Sweep.not_exists_factorization_two_three`: at `(a,b) = (2,3)`, `ℓ = A = 1`, the composite
`ct ∘ d_-^ℓ ∘ (d_-^{(ℓ+1)}G_{ℓ+1,A})` does **not** factor through `ct ∘ d_-^ℓ`. As at the unit
slope, one witness settles it: `F_0` lies in `ker(ct ∘ d_-^{(1)})`
(`HJO.Sweep.constantCoeff_lowerRun_one_levelKernelOne`) and
`HJO.Sweep.constantCoeff_lowerRun_stageTotal_eq_zero_of_factors` says a factorization would force
the composite to vanish there.

The nonvanishing is `HJO.Sym.elemSymm_two_sq_add_smul_ne_zero`, by the same route as the earlier
`HJO.Sym.elemSymm_one_sq_add_smul_elemSymm_two_ne_zero`: the substitution `p_k ↦ e_k` is injective
over a field of characteristic zero (`HJO.Sym.elemSymmSub_injective`), so a relation among the
`e`-monomials `e_2^2`, `e_1e_3`, `e_4` pulls back to one among the free generators `p_2^2`,
`p_1p_3`, `p_4`, where the coefficient of `p_2^2` is `1`. So the defect is nonzero at **every**
`q` and `u` inside the exclusions, not merely at a numeric point.

## Genericity: the three exclusions are real, none is an artefact

`q ≠ 0`, `u ≠ 0` and `q ≠ 1`, and no others: not `M ≠ 0`, not `qu ≠ 1`, not
`∀ r, IsUnit (q^{r+1} - 1)`. All three are forced, and by the inverse-becomes-zero hazard rather
than only by the answer's scalar:

* at `q = 0` and at `u = 0` the letter `(qu)^{-1}z_1` of `HJO.Sweep.slopeOperator` has
  `(qu)^{-1} = 0` in a field, so `Ξ^{(2)}_{2,3}` is the **zero map** and the composite kills `F_0`;
* at `q = 1` the scalar `q^2/(1-q)` of `HJO.Sweep.zop` is `0`, so `z_1^{(2)}` is the zero map, with
  the same consequence;
* and `q = 0` is needed a second time by the train `T_1^{-1} = (T_1 + (q-1))/q`.

At each of those three parameters the defect genuinely **is** `0`: there the factorization is not
refuted by this witness, and a clause asserting otherwise would be *false*, not vacuous. Everything
in this file upstream of the final value carries the inverses symbolically and has no hypothesis;
the hypotheses enter exactly where `q · q^{-1}` and `u · u^{-1}` are cancelled.

## Implementation notes

This settles the value-based factorization inside `1 < a < b`, at one point of it. It does **not**
prove the `hlhs` binder of `HJO.Mellit.shuffle_of_lhs_and_induction`, which is quantified over all
coprime `1 < a < b` and every composition; nor the `hind` binder. Both are proved elsewhere, by
other routes. What it does settle is that the *value*-carrying induction on the composition fails
for `hlhs`: the route not refuted is the separate observation, in
`HJO/Shuffle/MellitLhsCompInduction.lean`, that the two sides peel at opposite ends, so an
induction carrying the whole accumulated creation operator rather than its value is not refuted by
this.

## References

This file concerns `HJO.Sweep.slopeOperator`, `HJO.Sweep.zop`, `HJO.Sym.Bop`, `HJO.Sym.DopInt`,
`HJO.Sym.Qop`. Transcribing A. Mellit, *Toric braids and `(m, n)`-parking functions*, §3.
-/

@[expose] public section

namespace HJO.Sym
variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}


/-! ### The Hall--Littlewood values the `(2,3)` composite reads

`HJO.Sym.bop_natCast` reads `B_m` as the basic operator `D_m` at `u = 0`, so every value below is a
known `D`-value specialised there. -/

/-- `B_k(1) = (-1)^ke_k`, the vacuum value at a natural index. -/
theorem bop_natCast_one (q : L) (k : ℕ) :
    Bop q ((k : ℕ) : ℤ) (1 : Lambda L) = (-1) ^ k * elemSymm L k := by
  rw [bop_one, elemSymmAlt_natCast]

/-- `B_2(e_1^2) = e_1^2e_2 - 2(1-q)e_1e_3 + (1-q)^2e_4`, the Pieri rule
`HJO.Sym.dop_elemSymm_one_mul` at `k = 2`, `f = e_1`, `u = 0`. -/
theorem bop_two_elemSymm_one_sq (q : L) :
    Bop q ((2 : ℕ) : ℤ) (elemSymm L 1 * elemSymm L 1)
      = elemSymm L 1 * (elemSymm L 1 * elemSymm L 2)
        - (2 * (1 - q)) • (elemSymm L 1 * elemSymm L 3)
        + ((1 - q) ^ 2) • elemSymm L 4 := by
  rw [bop_natCast, dop_elemSymm_one_mul q 0 2 (elemSymm L 1), dop_two_elemSymm_one,
    dop_three_elemSymm_one]
  simp only [MvPolynomial.smul_eq_C_mul, map_sub, map_mul, map_one, map_pow, map_ofNat, map_zero]
  ring

/-- `B_2(e_2) = e_2^2 - (1-q)e_1e_3 - q(1-q)e_4`, off `HJO.Sym.dop_two_elemSymm_two` at `u = 0`.
The `e_2^2` here is what carries the defect's leading term. -/
theorem bop_two_elemSymm_two' (q : L) :
    Bop q ((2 : ℕ) : ℤ) (elemSymm L 2)
      = elemSymm L 2 * elemSymm L 2 - (1 - q) • (elemSymm L 1 * elemSymm L 3)
        - (q * (1 - q)) • elemSymm L 4 := by
  rw [bop_natCast, dop_two_elemSymm_two]
  simp only [MvPolynomial.smul_eq_C_mul, map_sub, map_add, map_mul, map_one, map_zero]
  ring

/-- `B_3(e_1) = -e_1e_3 + (1-q)e_4`, off `HJO.Sym.dop_three_elemSymm_one` at `u = 0`. -/
theorem bop_three_elemSymm_one (q : L) :
    Bop q ((3 : ℕ) : ℤ) (elemSymm L 1)
      = -(elemSymm L 1 * elemSymm L 3) + (1 - q) • elemSymm L 4 := by
  rw [bop_natCast, dop_three_elemSymm_one]
  simp only [MvPolynomial.smul_eq_C_mul, map_sub, map_mul, map_one, map_zero]
  ring

/-- `B_0(e_1) = qe_1`: the known `D_0(e_1) = (1-M)e_1` at `u = 0`, where `M = 1-q`. -/
theorem bop_zero_elemSymm_one' (q : L) :
    Bop q ((0 : ℕ) : ℤ) (elemSymm L 1) = q • elemSymm L 1 := by
  rw [bop_natCast, dop_zero_elemSymm_one]
  simp only [MvPolynomial.smul_eq_C_mul, map_sub, map_mul, map_one, map_zero]
  ring

/-- `B_1(e_1) = -e_1^2 + (1-q)e_2`, off `HJO.Sym.dop_one_elemSymm_one` at `u = 0`. -/
theorem bop_one_elemSymm_one' (q : L) :
    Bop q ((1 : ℕ) : ℤ) (elemSymm L 1)
      = -(elemSymm L 1 * elemSymm L 1) + (1 - q) • elemSymm L 2 := by
  rw [bop_natCast, dop_one_elemSymm_one]
  simp only [MvPolynomial.smul_eq_C_mul, map_sub, map_mul, map_one, map_zero]
  ring

/-- `B_0(e_2) = e_2 - (1-q)e_1^2 - q(1-q)e_2`, off `HJO.Sym.dop_zero_elemSymm_two` at `u = 0`. -/
theorem bop_zero_elemSymm_two' (q : L) :
    Bop q ((0 : ℕ) : ℤ) (elemSymm L 2)
      = elemSymm L 2 - (1 - q) • (elemSymm L 1 * elemSymm L 1)
        - (q * (1 - q)) • elemSymm L 2 := by
  rw [bop_natCast, dop_zero_elemSymm_two]
  simp only [MvPolynomial.smul_eq_C_mul, map_sub, map_add, map_mul, map_one, map_zero]
  ring

/-- `B_0(e_1^2) = (1-2(1-q))e_1^2 + (1-q)^2e_2`, off `HJO.Sym.dop_zero_elemSymm_one_sq` at
`u = 0`. -/
theorem bop_zero_elemSymm_one_sq (q : L) :
    Bop q ((0 : ℕ) : ℤ) (elemSymm L 1 * elemSymm L 1)
      = (1 - 2 * (1 - q)) • (elemSymm L 1 * elemSymm L 1) + ((1 - q) ^ 2) • elemSymm L 2 := by
  rw [bop_natCast, dop_zero_elemSymm_one_sq]
  simp only [MvPolynomial.smul_eq_C_mul, map_sub, map_mul, map_one, map_pow, map_ofNat, map_zero]
  ring

/-- `B_2(B_1e_1)`, the one composition already computed as a composition:
`HJO.Sym.dop_two_dop_one_elemSymm_one` at `u = 0`. -/
theorem bop_two_bop_one_elemSymm_one (q : L) :
    Bop q ((2 : ℕ) : ℤ) (Bop q ((1 : ℕ) : ℤ) (elemSymm L 1))
      = -(elemSymm L 1 * elemSymm L 1 * elemSymm L 2) + (1 - q) • (elemSymm L 2 * elemSymm L 2)
        + (2 * (1 - q) - (1 - q) ^ 2) • (elemSymm L 1 * elemSymm L 3)
        - ((1 + q) * (1 - q) ^ 2) • elemSymm L 4 := by
  rw [bop_natCast, bop_natCast, dop_two_dop_one_elemSymm_one]
  simp only [MvPolynomial.smul_eq_C_mul, map_sub, map_add, map_mul, map_one, map_pow,
    map_ofNat, map_zero]
  ring



/-! ### `e_2^2`, `e_1e_3` and `e_4` are linearly independent -/

/-- **`e_2^2 + ce_1e_3 + de_4 ≠ 0` for every pair of scalars.** The substitution `p_k ↦ e_k` is
injective over a field of characteristic zero (`HJO.Sym.elemSymmSub_injective`), so a relation among
these three `e`-monomials pulls back to one among the free generators `p_2^2`, `p_1p_3`, `p_4`, and
the coefficient of `p_2^2` there is `1`.

This is the exact analogue of the earlier `HJO.Sym.elemSymm_one_sq_add_smul_elemSymm_two_ne_zero`,
one degree up, and it is what makes the `(2,3)` refutation hold at **every** `q` and `u` inside its
three exclusions rather than at a numeric point. -/
@[hjo "lem_sym_elem_two_sq_ne_zero"]
theorem elemSymm_two_sq_add_smul_ne_zero (c d : L) :
    elemSymm L 2 * elemSymm L 2 + c • (elemSymm L 1 * elemSymm L 3)
      + d • elemSymm L 4 ≠ 0 := by
  intro h
  have hpre : elemSymmSub L (MvPolynomial.X 1 * MvPolynomial.X 1
      + c • (MvPolynomial.X 0 * MvPolynomial.X 2) + d • MvPolynomial.X 3)
      = elemSymm L 2 * elemSymm L 2 + c • (elemSymm L 1 * elemSymm L 3)
        + d • elemSymm L 4 := by
    simp only [map_add, map_mul, map_smul, elemSymmSub_X]
  have hzero : (MvPolynomial.X 1 * MvPolynomial.X 1
      + c • (MvPolynomial.X 0 * MvPolynomial.X 2) + d • MvPolynomial.X 3 : Lambda L) = 0 :=
    elemSymmSub_injective L (by rw [hpre, h, map_zero])
  have hev := congrArg (MvPolynomial.aeval fun i : ℕ => if i = 1 then (1 : L) else 0) hzero
  simp at hev

end HJO.Sym

namespace HJO.Sweep
open HJO.Sym
variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}



/-! ### The train `T_1^{-1}` of `z_1^{(2)}` on the argument -/

/-- **`T_1^{-1}(-y_1·slopeArgTwo)`**, the whole train of `z_1^{(2)}` applied to the argument of the
slope operator: three monomials in, five out, each already in the shape
`HJO.Sweep.zCommTwo_monomial'` reads.

The factor `q^{-1}` is pulled outside and **nothing is cancelled against it**, so there is no
hypothesis here: at `q = 0` both sides are the zero map's value. -/
theorem braidInvEnd_one_neg_auxVar_one_mul_slopeArgTwo (q u : L) :
    braidInvEnd q 1 (-((auxVar 1 : Total L) * slopeArgTwo q u))
      = q⁻¹ • (MvPolynomial.C (Sym.elemSymm L 1)
            * ((auxVar 1 : Total L) ^ 0 * (auxVar 2 : Total L) ^ 2)
          + MvPolynomial.C ((-(q - 1)) • Sym.elemSymm L 1)
            * ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 1)
          + MvPolynomial.C (((q - 1) * u) • (1 : Sym.Lambda L))
            * ((auxVar 1 : Total L) ^ 0 * (auxVar 2 : Total L) ^ 3)
          + MvPolynomial.C ((q - (q - 1) ^ 2 * u) • (1 : Sym.Lambda L))
            * ((auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ 2)
          + MvPolynomial.C ((-((q - 1) ^ 2 * u)) • (1 : Sym.Lambda L))
            * ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1)) := by
  rw [show -((auxVar 1 : Total L) * slopeArgTwo q u)
      = MvPolynomial.C (Sym.elemSymm L 1) * (auxVar 1 : Total L) ^ 2
        + scal ((q - 1) * u) * (auxVar 1 : Total L) ^ 3
        + scal q * ((auxVar 1 : Total L) ^ 2 * auxVar 2) from by rw [slopeArgTwo]; ring,
    map_add, map_add, braidInvEnd_C_mul, braidInvEnd_scal_mul, braidInvEnd_scal_mul,
    braidInvEnd_one_auxVar_one_sq, braidInvEnd_one_auxVar_one_cube,
    braidInvEnd_one_auxVar_one_sq_mul_two]
  simp only [← scal_mul_eq_smul_total]
  simp only [MvPolynomial.smul_eq_C_mul, scal, map_mul, map_sub, map_neg, map_one, map_pow]
  ring

/-- **The commutator half of `z_1^{(2)}` on the argument**, term by term: each of the five monomials
goes to a spectator power of `y_2` times the grading-one defect `HJO.Sweep.zDefect` at the
monomial's `y_2`-exponent. Unconditional. -/
theorem zCommTwo_braidInvEnd_one_neg_auxVar_one_mul_slopeArgTwo (q u : L) :
    zCommTwo q u (braidInvEnd q 1 (-((auxVar 1 : Total L) * slopeArgTwo q u)))
      = q⁻¹ • (zDefect q u 2 (Sym.elemSymm L 1)
          + (-(q - 1)) • ((auxVar 2 : Total L) * zDefect q u 1 (Sym.elemSymm L 1))
          + ((q - 1) * u) • zDefect q u 3 (1 : Sym.Lambda L)
          + (q - (q - 1) ^ 2 * u) • ((auxVar 2 : Total L) * zDefect q u 2 (1 : Sym.Lambda L))
          + (-((q - 1) ^ 2 * u))
              • ((auxVar 2 : Total L) ^ 2 * zDefect q u 1 (1 : Sym.Lambda L))) := by
  rw [braidInvEnd_one_neg_auxVar_one_mul_slopeArgTwo, map_smul, map_add, map_add, map_add, map_add,
    zCommTwo_monomial', zCommTwo_monomial', zCommTwo_monomial', zCommTwo_monomial',
    zCommTwo_monomial', zDefect_smul, zDefect_smul, zDefect_smul, zDefect_smul]
  simp only [mul_smul_comm, pow_zero, pow_one, one_mul]




/-! ### Linearity of the functional -/


theorem constantCoeff_lowerRun_two_smul (q : L) (c : L) (F : Total L) :
    MvPolynomial.constantCoeff (Mellit.lowerRun q 2 (c • F))
      = c • MvPolynomial.constantCoeff (Mellit.lowerRun q 2 F) := by
  rw [map_smul, ← scal_mul_eq_smul_total, map_mul, scal, MvPolynomial.constantCoeff_C,
    ← MvPolynomial.smul_eq_C_mul]

theorem constantCoeff_lowerRun_two_add (q : L) (F G : Total L) :
    MvPolynomial.constantCoeff (Mellit.lowerRun q 2 (F + G))
      = MvPolynomial.constantCoeff (Mellit.lowerRun q 2 F)
        + MvPolynomial.constantCoeff (Mellit.lowerRun q 2 G) := by
  rw [map_add, map_add]



/-! ### The slope operator of the row at `(2,3)`, on a vector -/

/-- **`Ξ^{(2)}_{2,3}(F) = -(qu)^{-1}\frac{q^2}{1-q}·y_1·zCommTwo(T_1^{-1}(-y_1F))`.** The assembly
`HJO.Sweep.slopeOperator_two_odd` at `K = 2`, `k = 1`, with `HJO.Sweep.zopOneStar_two_eq` reading
the single `z` letter. Both inverse scalars are carried symbolically, so there is no hypothesis. -/
theorem slopeOperator_two_three_apply (q u : L) (F : Total L) :
    slopeOperator q u 2 2 3 F
      = -(((q * u)⁻¹ * (q ^ 2 / (1 - q)))
          • ((auxVar 1 : Total L)
              * zCommTwo q u (braidInvEnd q 1 (-((auxVar 1 : Total L) * F))))) := by
  have h : slopeOperator q u 2 2 3
      = (-LinearMap.mulLeft L (auxVar 1 : Total L)) ^ 1
          * ((q * u)⁻¹ • zopOneStar q u 2)
          * (-LinearMap.mulLeft L (auxVar 1 : Total L)) ^ 1 := by
    simpa using slopeOperator_two_odd q u 2 1
  rw [h]
  simp only [pow_one, Module.End.mul_apply, LinearMap.smul_apply, zopOneStar_two_eq,
    LinearMap.neg_apply, LinearMap.mulLeft_apply, smul_smul, mul_smul_comm, smul_neg]




private theorem exp1 (q u : L) :
    (auxVar 1 : Total L) * zDefect q u 2 (Sym.elemSymm L 1)
      = ((q - 1) * u) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 0
            * MvPolynomial.C (Sym.elemSymm L 1 * Sym.elemSymm L 1))
        + ((q - 1) ^ 2 * u) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 0
            * MvPolynomial.C (Sym.elemSymm L 2))
        + (-((q - 1) * u ^ 2)) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 0
            * MvPolynomial.C (Sym.elemSymm L 1)) := by
  rw [zDefect_two_elemSymm_one]
  simp only [← scal_mul_eq_smul_total]
  simp only [scal, map_mul, map_sub, map_neg, map_one, map_pow]
  ring

private theorem exp2 (q u : L) :
    (auxVar 1 : Total L) * ((-(q - 1)) • ((auxVar 2 : Total L) * zDefect q u 1 (Sym.elemSymm L 1)))
      = (q * (q - 1) ^ 2 * u) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1
            * MvPolynomial.C (Sym.elemSymm L 1)) := by
  rw [zDefect_one_elemSymm_one]
  simp only [← scal_mul_eq_smul_total]
  simp only [scal, map_mul, map_sub, map_neg, map_one, map_pow]
  ring

private theorem exp3 (q u : L) :
    (auxVar 1 : Total L) * (((q - 1) * u) • zDefect q u 3 (1 : Sym.Lambda L))
      = (-((q - 1) ^ 2 * u ^ 2)) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 0
            * MvPolynomial.C (Sym.elemSymm L 2))
        + ((q - 1) ^ 2 * u ^ 3) • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 0
            * MvPolynomial.C (Sym.elemSymm L 1))
        + (-((q - 1) ^ 2 * u ^ 4)) • ((auxVar 1 : Total L) ^ 4 * (auxVar 2 : Total L) ^ 0
            * MvPolynomial.C (1 : Sym.Lambda L)) := by
  rw [zDefect_three_one]
  simp only [← scal_mul_eq_smul_total]
  simp only [scal, map_mul, map_sub, map_neg, map_one, map_pow]
  ring

private theorem exp4 (q u : L) :
    (auxVar 1 : Total L)
        * ((q - (q - 1) ^ 2 * u) • ((auxVar 2 : Total L) * zDefect q u 2 (1 : Sym.Lambda L)))
      = ((q - (q - 1) ^ 2 * u) * ((q - 1) * u))
            • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 1
              * MvPolynomial.C (Sym.elemSymm L 1))
        + (-((q - (q - 1) ^ 2 * u) * ((q - 1) * u ^ 2)))
            • ((auxVar 1 : Total L) ^ 3 * (auxVar 2 : Total L) ^ 1
              * MvPolynomial.C (1 : Sym.Lambda L)) := by
  rw [zDefect_two_one]
  simp only [← scal_mul_eq_smul_total]
  simp only [scal, map_mul, map_sub, map_neg, map_one, map_pow]
  ring

private theorem exp5 (q u : L) :
    (auxVar 1 : Total L)
        * ((-((q - 1) ^ 2 * u)) • ((auxVar 2 : Total L) ^ 2 * zDefect q u 1 (1 : Sym.Lambda L)))
      = ((q - 1) ^ 3 * u ^ 2) • ((auxVar 1 : Total L) ^ 2 * (auxVar 2 : Total L) ^ 2
            * MvPolynomial.C (1 : Sym.Lambda L)) := by
  rw [zDefect_one_one]
  simp only [← scal_mul_eq_smul_total]
  simp only [scal, map_mul, map_sub, map_neg, map_one, map_pow]
  ring

/-- **The composite, as seven compositions of Hall--Littlewood operators.** Every operator of the
sweep has been discharged: what is left is a `Λ`-side expression `∑ c·B_jB_m(g)` with `j` the
`y_1`-exponent and `m` the `y_2`-exponent of the monomial it came from.

Unconditional — the `q^{-1}` is the one `HJO.Sweep.braidInvEnd_one_neg_auxVar_one_mul_slopeArgTwo`
pulled out, and it is still not cancelled. -/
theorem constantCoeff_lowerRun_two_auxVar_one_mul_zCommTwo (q u : L) :
    MvPolynomial.constantCoeff (Mellit.lowerRun q 2 ((auxVar 1 : Total L)
        * zCommTwo q u (braidInvEnd q 1 (-((auxVar 1 : Total L) * slopeArgTwo q u)))))
      = q⁻¹ • (((q - 1) * u)
            • Sym.Bop q ((2 : ℕ) : ℤ) (Sym.Bop q ((0 : ℕ) : ℤ)
                (Sym.elemSymm L 1 * Sym.elemSymm L 1))
          + ((q - 1) ^ 2 * u - (q - 1) ^ 2 * u ^ 2)
            • Sym.Bop q ((2 : ℕ) : ℤ) (Sym.Bop q ((0 : ℕ) : ℤ) (Sym.elemSymm L 2))
          + (-((q - 1) * u ^ 2) + (q - 1) ^ 2 * u ^ 3)
            • Sym.Bop q ((3 : ℕ) : ℤ) (Sym.Bop q ((0 : ℕ) : ℤ) (Sym.elemSymm L 1))
          + (-((q - 1) ^ 2 * u ^ 4))
            • Sym.Bop q ((4 : ℕ) : ℤ) (Sym.Bop q ((0 : ℕ) : ℤ) (1 : Sym.Lambda L))
          + (q * (q - 1) ^ 2 * u + (q - (q - 1) ^ 2 * u) * ((q - 1) * u))
            • Sym.Bop q ((2 : ℕ) : ℤ) (Sym.Bop q ((1 : ℕ) : ℤ) (Sym.elemSymm L 1))
          + (-((q - (q - 1) ^ 2 * u) * ((q - 1) * u ^ 2)))
            • Sym.Bop q ((3 : ℕ) : ℤ) (Sym.Bop q ((1 : ℕ) : ℤ) (1 : Sym.Lambda L))
          + ((q - 1) ^ 3 * u ^ 2)
            • Sym.Bop q ((2 : ℕ) : ℤ) (Sym.Bop q ((2 : ℕ) : ℤ) (1 : Sym.Lambda L))) := by
  rw [zCommTwo_braidInvEnd_one_neg_auxVar_one_mul_slopeArgTwo, mul_smul_comm,
    constantCoeff_lowerRun_two_smul]
  refine congrArg (fun x => q⁻¹ • x) ?_
  rw [mul_add, mul_add, mul_add, mul_add, exp1, exp2, exp3, exp4, exp5]
  simp only [constantCoeff_lowerRun_two_add, constantCoeff_lowerRun_two_smul,
    constantCoeff_lowerRun_two_C_mul_monomial]
  module


omit [Algebra ℚ L] in
theorem constantCoeff_smul (c : L) (F : Total L) :
    MvPolynomial.constantCoeff (c • F) = c • MvPolynomial.constantCoeff F := by
  rw [← scal_mul_eq_smul_total, map_mul, scal, MvPolynomial.constantCoeff_C,
    ← MvPolynomial.smul_eq_C_mul]

theorem constantCoeff_lowerRun_two_neg_smul (q c : L) (F : Total L) :
    MvPolynomial.constantCoeff (Mellit.lowerRun q 2 (-(c • F)))
      = -(c • MvPolynomial.constantCoeff (Mellit.lowerRun q 2 F)) := by
  rw [map_neg, map_neg, constantCoeff_lowerRun_two_smul]


/-! ### The value, and the refutation -/

/-- **The level-raising evaluation at `(a,b) = (2,3)`, `ℓ = A = 1`:**

`ct(d_-^{(1)}d_-^{(2)}G_{2,1}(F_0)) = u(q-1)[e_2^2 + (q+u-1)e_1e_3 + (q^2+qu-q+u^2-u)e_4]`.

The `e_1^4` and `e_1^2e_2` coefficients cancel identically; the `e_2^2` coefficient is undeformed,
so the surviving scalar is `u(q-1)` exactly.

**The three hypotheses are all real.** They are where the inverse scalars are cancelled against the
parameters: at `q = 0` and at `u = 0` the letter `(qu)^{-1}z_1` is the zero map, at `q = 1` the
scalar `q^2/(1-q)` of `HJO.Sweep.zop` is `0` and `z_1^{(2)}` is the zero map, and `q = 0` is needed
again by `T_1^{-1} = (T_1+(q-1))/q`. At each of the three the value genuinely is `0`. -/
@[hjo "not_mellit_level_raise_factors_two_three"]
theorem constantCoeff_lowerRun_two_stageTotal_levelKernelOne_two_three
    (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    MvPolynomial.constantCoeff
        (Mellit.lowerRun q 2 (Mellit.stageTotal q u 2 3 1 1 (levelKernelOne q)))
      = (u * (q - 1)) • (Sym.elemSymm L 2 * Sym.elemSymm L 2
          + (q + u - 1) • (Sym.elemSymm L 1 * Sym.elemSymm L 3)
          + (q ^ 2 + q * u - q + u ^ 2 - u) • Sym.elemSymm L 4) := by
  have h1q : (1 : L) - q ≠ 0 := sub_ne_zero.2 (Ne.symm hq1)
  have b01 : Sym.Bop q ((0 : ℕ) : ℤ) (1 : Sym.Lambda L) = 1 := by
    rw [Sym.bop_natCast_one]; simp [Sym.elemSymm_zero]
  have b11 : Sym.Bop q ((1 : ℕ) : ℤ) (1 : Sym.Lambda L) = -Sym.elemSymm L 1 := by
    rw [Sym.bop_natCast_one]; simp
  have b21 : Sym.Bop q ((2 : ℕ) : ℤ) (1 : Sym.Lambda L) = Sym.elemSymm L 2 := by
    rw [Sym.bop_natCast_one]; simp
  have b41 : Sym.Bop q ((4 : ℕ) : ℤ) (1 : Sym.Lambda L) = Sym.elemSymm L 4 := by
    rw [Sym.bop_natCast_one]
    norm_num
  have hs : ((q * u)⁻¹ * (q ^ 2 / (1 - q)) * q⁻¹) * (u * (1 - q)) = 1 := by
    field_simp
  rw [lowerRun_two_stageTotal_levelKernelOne_of_slope, slopeOperator_two_three_apply,
    constantCoeff_smul, constantCoeff_lowerRun_two_neg_smul,
    constantCoeff_lowerRun_two_auxVar_one_mul_zCommTwo, smul_smul,
    show ((-1 : L) ^ (2 - 1)) = -1 from by norm_num, neg_one_smul, neg_neg]
  rw [show (((q - 1) * u)
        • Sym.Bop q ((2 : ℕ) : ℤ) (Sym.Bop q ((0 : ℕ) : ℤ)
            (Sym.elemSymm L 1 * Sym.elemSymm L 1))
      + ((q - 1) ^ 2 * u - (q - 1) ^ 2 * u ^ 2)
        • Sym.Bop q ((2 : ℕ) : ℤ) (Sym.Bop q ((0 : ℕ) : ℤ) (Sym.elemSymm L 2))
      + (-((q - 1) * u ^ 2) + (q - 1) ^ 2 * u ^ 3)
        • Sym.Bop q ((3 : ℕ) : ℤ) (Sym.Bop q ((0 : ℕ) : ℤ) (Sym.elemSymm L 1))
      + (-((q - 1) ^ 2 * u ^ 4))
        • Sym.Bop q ((4 : ℕ) : ℤ) (Sym.Bop q ((0 : ℕ) : ℤ) (1 : Sym.Lambda L))
      + (q * (q - 1) ^ 2 * u + (q - (q - 1) ^ 2 * u) * ((q - 1) * u))
        • Sym.Bop q ((2 : ℕ) : ℤ) (Sym.Bop q ((1 : ℕ) : ℤ) (Sym.elemSymm L 1))
      + (-((q - (q - 1) ^ 2 * u) * ((q - 1) * u ^ 2)))
        • Sym.Bop q ((3 : ℕ) : ℤ) (Sym.Bop q ((1 : ℕ) : ℤ) (1 : Sym.Lambda L))
      + ((q - 1) ^ 3 * u ^ 2)
        • Sym.Bop q ((2 : ℕ) : ℤ) (Sym.Bop q ((2 : ℕ) : ℤ) (1 : Sym.Lambda L)))
      = (u * (1 - q)) • ((u * (q - 1)) • (Sym.elemSymm L 2 * Sym.elemSymm L 2
          + (q + u - 1) • (Sym.elemSymm L 1 * Sym.elemSymm L 3)
          + (q ^ 2 + q * u - q + u ^ 2 - u) • Sym.elemSymm L 4)) from by
    rw [Sym.bop_zero_elemSymm_one_sq, Sym.bop_zero_elemSymm_two', Sym.bop_zero_elemSymm_one',
      b01, b11, b21]
    simp only [map_add, map_sub, map_smul, map_neg]
    simp only [Sym.bop_two_elemSymm_one_sq, Sym.bop_two_elemSymm_two',
      Sym.bop_three_elemSymm_one, Sym.bop_two_bop_one_elemSymm_one, b41]
    simp only [MvPolynomial.smul_eq_C_mul, map_sub, map_add, map_neg, map_mul, map_one, map_pow,
      map_ofNat]
    ring,
    smul_smul, hs, one_smul]


/-- **`ct ∘ d_-^ℓ ∘ (d_-^{(ℓ+1)}G_{ℓ+1,A})` does NOT factor through `ct ∘ d_-^ℓ`**, at `ℓ = A = 1`
and `(a,b) = (2,3)` — a point **inside** the range `1 < a < b` that the `hlhs` binder of
`HJO.Mellit.shuffle_of_lhs_and_induction` quantifies over.

The witness is again `F_0 = Ce_1 + qy_1`: it lies in `V_1`, `ct(d_-^{(1)}F_0) = 0`, and the
composite sends it to `u(q-1)[e_2^2 + ⋯] ≠ 0`. Any `φ` would have to send `0` both to `0` (from
`F = 0`, by `HJO.Sweep.constantCoeff_lowerRun_stageTotal_eq_zero_of_factors`) and to that.

So the **value**-based induction on the composition is refuted for `hlhs`, not merely unproved:
this is the in-range companion of `HJO.Sweep.not_exists_factorization_one_one`. It does not prove
`hlhs`, which ranges over all coprime `1 < a < b` and every composition. -/
@[hjo "not_mellit_level_raise_factors_two_three"]
theorem not_exists_factorization_two_three (hq0 : q ≠ 0) (hu : u ≠ 0) (hq1 : q ≠ 1) :
    ¬ ∃ φ : Sym.Lambda L → Sym.Lambda L, ∀ F ∈ piece L 1,
      MvPolynomial.constantCoeff (Mellit.lowerRun q 2 (Mellit.stageTotal q u 2 3 1 1 F))
        = φ (MvPolynomial.constantCoeff (Mellit.lowerRun q 1 F)) := by
  rintro ⟨φ, hφ⟩
  have hφ' : ∀ F ∈ piece L 1, MvPolynomial.constantCoeff
      (Mellit.lowerRun q (1 + 1) (Mellit.stageTotal q u 2 3 1 1 F))
      = φ (MvPolynomial.constantCoeff (Mellit.lowerRun q 1 F)) := by
    simpa using hφ
  have h := constantCoeff_lowerRun_stageTotal_eq_zero_of_factors hφ'
    (levelKernelOne_mem_piece q) (constantCoeff_lowerRun_one_levelKernelOne q)
  rw [show (1 : ℕ) + 1 = 2 from rfl,
    constantCoeff_lowerRun_two_stageTotal_levelKernelOne_two_three hq0 hu hq1] at h
  rcases smul_eq_zero.1 h with hc | he
  · rcases mul_eq_zero.1 hc with h1 | h2
    · exact hu h1
    · exact hq1 (sub_eq_zero.1 h2)
  · exact Sym.elemSymm_two_sq_add_smul_ne_zero _ _ he

end HJO.Sweep

end
