/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.LoweringSumClosed
public import HJO.Shuffle.MellitAssembly
public import HJO.Shuffle.SweepWordTransport
public meta import HJO.Attr

/-! # The sweep hypothesis of the shuffle assembly is discharged

`HJO.Mellit.shuffle_of_three` concludes `HJO.External.Shuffle L` from exactly three hypotheses:
`LhsComputes`, `MellitInduction` at the sweep witness, and `SweepComputes`, each asked for under the
constraints `MellitInput` itself provides — `AlgebraicIndependent ℤ ![q, u]`, `Nat.Coprime a b`,
`1 < a`, `a < b` — and no others. This file discharges the third of them, so that
`HJO.External.Shuffle L` now follows from the remaining two
(`HJO.Mellit.shuffle_of_lhs_and_induction`).

`HJO.Mellit.sweepComputes` of `HJO.CarlssonMellit.LoweringSumClosed` is
`HJO.Mellit.sweepComputes` under three conditions on the parameter — `q ≠ 0` from collecting the
scalars of `HJO.Mellit.sweepOperator`, `q ≠ 1` from `HJO.Mellit.map_constantCoeff_markedWordOp'` at
a nonempty marking, and `∀ r, IsUnit (q ^ (r + 1) - 1)` from
`HJO.Dyck.auxZeroMap_eq_pathCharSeries_of_isSigmaCharacter` — and all three follow from the
algebraic independence the assembly already carries, by the route `HJO.PhiPoly.eq_of_aeval_eq` that
`HJO.Mellit.ne_zero_of_algebraicIndependent_fst` takes for `q ≠ 0`: a relation on `q` alone is a
polynomial in `MvPolynomial (Fin 2) ℤ` that the independence forces to be zero, and the polynomials
`X₀ - 1` and `X₀ ^ (r + 1) - 1` are not.

Also here: `HJO.Mellit.constantCoeff_psiWord_one_mem_lambdaComp_and_map_eq_sweepChar`, which
`HJO.Shuffle.SweepWordTransport` proves modulo `HJO.Mellit.map_constantCoeff_markedWordOp'` and
which that lemma now discharges.

## Main results

* `HJO.Mellit.sub_one_ne_zero_of_algebraicIndependent_fst`,
  `HJO.Mellit.isUnit_pow_sub_one_of_algebraicIndependent_fst`: the two conditions on `q` beyond
  `q ≠ 0`, from the algebraic independence.
* `HJO.Mellit.constantCoeff_psiWord_one_mem_lambdaComp_and_map_eq_sweepChar`:
  `HJO.Mellit.constantCoeff_psiWord_one_mem_lambdaComp_and_map_eq_sweepChar`.
* `HJO.Mellit.sweepComputes_of_algebraicIndependent`: the `hsc` hypothesis of
  `HJO.Mellit.shuffle_of_three`, in exactly its shape.
* `HJO.Mellit.shuffle_of_lhs_and_induction`: `HJO.External.Shuffle L` from the two hypotheses that
  remain.

## References

E. Carlsson and A. Mellit,
*A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018) 661--697.
-/

@[expose] public section

namespace HJO.Mellit

open ParkingFunctions Paths Sweep

/-! ### The conditions on the parameter, from the algebraic independence -/

/-- `AlgebraicIndependent ℤ ![q, u]` forces `q - 1 ≠ 0`: otherwise `X₀ - 1` evaluates to `0`, so it
is the zero polynomial, which it is not. The companion of
`HJO.Mellit.ne_zero_of_algebraicIndependent_fst`, by the same route. -/
theorem sub_one_ne_zero_of_algebraicIndependent_fst {K : Type*} [Field K] {q u : K}
    (hqu : AlgebraicIndependent ℤ ![q, u]) : q - 1 ≠ 0 := fun h0 => by
  have hz : (MvPolynomial.X 0 - 1 : MvPolynomial (Fin 2) ℤ) = 0 :=
    PhiPoly.eq_of_aeval_eq hqu (by simpa using h0)
  have hz' := congrArg (MvPolynomial.aeval ![(0 : ℤ), 0]) hz
  simp at hz'

/-- `AlgebraicIndependent ℤ ![q, u]` forces every `q ^ (r + 1) - 1` to be a unit: in a field that is
`q ^ (r + 1) - 1 ≠ 0`, and otherwise `X₀ ^ (r + 1) - 1` evaluates to `0`, so it is the zero
polynomial, which it is not — its value at `![0, 0]` is `-1`. This is
`HJO.Dyck.auxZeroMap_eq_pathCharSeries_of_isSigmaCharacter`'s hypothesis, through the bijectivity of
`θ`. -/
theorem isUnit_pow_sub_one_of_algebraicIndependent_fst {K : Type*} [Field K] {q u : K}
    (hqu : AlgebraicIndependent ℤ ![q, u]) (r : ℕ) : IsUnit (q ^ (r + 1) - 1) := by
  refine isUnit_iff_ne_zero.2 fun h0 => ?_
  have hz : (MvPolynomial.X 0 ^ (r + 1) - 1 : MvPolynomial (Fin 2) ℤ) = 0 :=
    PhiPoly.eq_of_aeval_eq hqu (by simpa using h0)
  have hz' := congrArg (MvPolynomial.aeval ![(0 : ℤ), 0]) hz
  simp at hz'

/-! ### The word of a path above the diagonal computes its character -/

variable {L : Type*} [Field L] [Algebra ℚ L] [CharZero L] {a b N : ℕ}

/-- **The sweep process computes the character**,
`HJO.Mellit.constantCoeff_psiWord_one_mem_lambdaComp_and_map_eq_sweepChar`: for an above-diagonal
`(aN, bN)`-path `P̂` and a realisation `ι`, the element `f = (Ψ_{P̂}(P_M) ∘ ⋯ ∘ Ψ_{P̂}(P_1))(1)` of
`Λ` is homogeneous of degree `bN` and `ι(f) = χ(P̂)`.

This is `HJO.Mellit.constantCoeff_psiWord_one_mem_lambdaComp_and_map_eq_sweepChar_of_cor46_alone`
with its hypothesis discharged by `HJO.Dyck.isLoweringSum`, through
`HJO.Dyck.realisation_constantCoeff_markedWordOp'` and `HJO.Mellit.map_constantCoeff_markedWordOp'`.
The three conditions on `q` are those of `HJO.Mellit.sweepComputes`; `q ≠ 1` cannot be dropped,
`HJO.Mellit.map_constantCoeff_markedWordOp'` being false without it at a nonempty marking. -/
@[hjo "lem_sweep_char_word"]
theorem constantCoeff_psiWord_one_mem_lambdaComp_and_map_eq_sweepChar (q : L) (hq0 : q ≠ 0)
    (hq1 : q ≠ 1) (hqu : ∀ r : ℕ, IsUnit (q ^ (r + 1) - 1)) {y : Heights a b N}
    (hy : IsAboveDiagonal y) {ι : Sym.Lambda L →ₐ[L] Sym.AlphabetSeries L}
    (hι : Sym.IsRealisation ι) :
    MvPolynomial.constantCoeff (psiWord q y (1 : Total L)) ∈ Sym.LambdaComp L (b * N) ∧
      ι (MvPolynomial.constantCoeff (psiWord q y (1 : Total L))) = sweepChar q y :=
  constantCoeff_psiWord_one_mem_lambdaComp_and_map_eq_sweepChar_of_cor46_alone q hy hι
    fun {_} x T _ hx hT => map_constantCoeff_markedWordOp' q hq0 hq1 hqu hι x T hx hT

end HJO.Mellit

namespace HJO.Mellit

variable {L : Type*} [Field L] [Algebra ℚ L]

/-! ### The sweep hypothesis of the shuffle assembly -/

/-- **The `SweepComputes` hypothesis of `HJO.Mellit.shuffle_of_three`, discharged**, in exactly the
shape that theorem asks for it.

`HJO.Mellit.sweepComputes` needs `q ≠ 0`, `q ≠ 1` and `∀ r, IsUnit (q ^ (r + 1) - 1)`, and the
algebraic independence supplies all three; `CharZero L` comes from `Algebra ℚ L` on a field, the
structure map out of `ℚ` being injective. Nothing is asked of `a`, `b` or of the coprimality. -/
theorem sweepComputes_of_algebraicIndependent (q u : L) (hqu : AlgebraicIndependent ℤ ![q, u])
    (a b : ℕ) : SweepComputes q u a b := by
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  exact sweepComputes q u (ne_zero_of_algebraicIndependent_fst hqu)
    (sub_ne_zero.1 (sub_one_ne_zero_of_algebraicIndependent_fst hqu))
    (isUnit_pow_sub_one_of_algebraicIndependent_fst hqu)

/-- **`HJO.External.Shuffle` from the two hypotheses that remain.** `HJO.Mellit.shuffle_of_three`
asks for `LhsComputes`, `MellitInduction` at the sweep witness and `SweepComputes`; the third is now
a theorem, so the residual of the shuffle side is the first two. -/
theorem shuffle_of_lhs_and_induction
    (hlhs : ∀ q u : L, AlgebraicIndependent ℤ ![q, u] → ∀ a b : ℕ, Nat.Coprime a b → 1 < a →
      a < b → LhsComputes q u a b)
    (hind : ∀ q u : L, AlgebraicIndependent ℤ ![q, u] → ∀ a b : ℕ, Nat.Coprime a b → 1 < a →
      a < b → MellitInduction (sweepWitness q u a b) a b) :
    HJO.External.Shuffle L :=
  shuffle_of_three hlhs hind
    fun q u hqu a b _ _ _ => sweepComputes_of_algebraicIndependent q u hqu a b

end HJO.Mellit
