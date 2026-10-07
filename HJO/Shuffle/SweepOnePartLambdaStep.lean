/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.LhsPairOnePartReduction
public import HJO.Shuffle.MellitQopThreeFour
public import HJO.Shuffle.MellitVertexStepClosed
public import HJO.Shuffle.SweepReplicatedNoValueRecursion

/-! # The one-part sweep step, evaluated at the `Λ` level: `D_1D_2` on the value, plus two defects

`HJO.Mellit.lhsAt_two_three_singleton_iff_bop` (`HJO/Shuffle/SweepReplicatedIterate.lean`)
reduces the `hlhs` clause at the one-part composition `[A]` and `(a,b) = (2,3)` to

  `Θ(h_A)(1) = V_A`,   `V_A = HJO.Mellit.onePartSweepValue q u A = -ct(d_-^{(1)}G_A)`,

and `HJO.Mellit.stageWordTotal_singleton_succ` makes the sweep side a one-step recursion
`G_{A+2} = Z^{(1)}_{2,3}(G_{A+1})` on the **vector** `G_A ∈ V_1 = Λ[y_1]`. What was missing was that
step at the `Λ` level: `HJO.Sweep.replicatedTotal_two_three_zero_of_mem_piece` expands only the
outer `z_1` of `Z^{(1)}_{2,3} = (qu)^{-1}y_1z_1y_1^2z_1`, and its answer still names `d^*_+`, `d_-`
and `HJO.Sweep.bopExt` on the total space.

## The evaluation

One known fact does all the work: `HJO.Sweep.dminus_auxVar_pow_mul_dplusStar_C`
(`HJO.Sweep.dop_eq_neg_dminusCM_auxVar_pow_dplusStar`) says `d_-^{(1)}(y_1^ld^*_+(Cg)) = C(D_lg)` —
the **basic** operator of `HJO.Sym.DopInt` at the index `l`, at every `l ≥ 0`. So the two branches
of `HJO.Sweep.zopOneStar_one_of_mem_piece` become, after `y_1^l·` and `ct∘d_-^{(1)}`:

* `ct(d_-^{(1)}(y_1^ld^*_+(C(B_mg)))) = D_l(B_mg)`, that fact verbatim;
* `ct(d_-^{(1)}(y_1^lB_m(d^*_+(Cg)))) = T_{l,m}(g)`, which is `HJO.Sweep.twistDop`: the *same*
  expression with the Hall--Littlewood operator of `HJO.Sym.Bop` inserted between the displacement
  and the lowering. `HJO.Sweep.dop_eq_constantCoeff_dminus_one` records that `D_l` is `T_{l,m}` with
  no `B_m` in it, so the difference of the two branches is a commutator `[D_l, B_m]` read at the
  `y_1`-degree `m` and at nothing else.

`HJO.Sweep.constantCoeff_dminus_one_auxVar_pow_mul_zopOneStar_one_of_mem_piece` is therefore, for
every `F ∈ V_1` and every `l`, with **no hypothesis on `q` or `u`**:

  `ct(d_-^{(1)}(y_1^lz_1F)) = q/(1-q)·( D_l(ct(d_-^{(1)}F)) - ∑_m T_{l,m}(F_m) )`,

whose first summand is a function of the *value* `ct(d_-^{(1)}F)` alone while the second reads the
vector `(F_m)_m` degree by degree. Composing it at `l = 2` and `l = 1` — the two powers of `y_1` in
the replicated letter — gives
`HJO.Sweep.constantCoeff_dminus_one_replicatedTotal_two_three_zero_split`:

  `ct(d_-^{(1)}Z^{(1)}_{2,3}F) = (qu)^{-1}(q/(1-q))^2·D_1(D_2(ct(d_-^{(1)}F))) - (two defects)`.

**The value-only part of the step is `D_1D_2`.** That is worth saying out loud.
`HJO.Sym.split_two_three` gives `Split 2 3 = (1,1)`, so `HJO.Sym.qop_two_three_eq_bracket_dop` reads
`Q_{2,3} = M^{-1}(D_2D_1 - D_1D_2)`: the step produces exactly one of the two terms of the
commutator that defines the operator the clause's creation side is built from, and the defects carry
the rest. It also localises `HJO.Sweep.not_exists_factorization_replicated_two_three`, which says
the step is not a function of the value: the failure sits in the two defect sums, whose summands
`T_{l,m}` depend on the `y_1`-degree `m` and so cannot be read off `∑_m B_m(F_m)`.

## What this buys for the one-part family

`HJO.Mellit.onePartSweepValue_succ` is the recursion on the value, at every `A`, again with no
hypothesis on `q` or `u`:

  `V_{A+2} = cγ·D_1(D_2(V_{A+1})) + cγ·D_1(Δ²_{A+1}) + c·Δ¹_{A+1}`,

with `c = (qu)^{-1}q/(1-q)`, `γ = q/(1-q)`, `Δ²_A = HJO.Mellit.onePartDefectTwo q u A` and
`Δ¹_A = HJO.Mellit.onePartDefectOne q u A` the two defect sums at the stage word.

`HJO.Mellit.forall_lhsAt_two_three_singleton_succ_of_creation_of_axis` then closes the induction
**on the sweep side**: `∀ A, LhsAt q u 2 3 Θ [A+1]` follows from ONE hypothesis, that the creation
side obeys the same recursion,

  `Θ(h_{A+2})(1) = cγ·D_1(D_2(Θ(h_{A+1})(1))) + cγ·D_1(Δ²_{A+1}) + c·Δ¹_{A+1}`   for every `A`,

the base case at `[1]` being `HJO.Mellit.lhsAt_two_three_one_of_axis`. So the residual of
the whole one-part family is exactly that one family of identities: a statement about `Θ(h_m)(1)` at
two consecutive `m`, with no composition, no stage word and no sweep operator on its left-hand side.

## What is NOT proved, with the quantifier named

* **`∀ A, LhsAt q u 2 3 Θ [A]` is NOT proved**, and nothing here is an instance of the clause. The
  creation-side step is discharged at **no** `A ≥ 1`. `HJO.Mellit.creation_step_zero_of_axis`
  verifies it at `A = 0` only, and that verification is a *consequence* of the two already-decided
  instances `[1]` and `[2]`: it shows the hypothesis is satisfiable and correctly shaped, not that
  the recursion is right on its own.
* **`A = 3` is not decided.** `HJO.Mellit.onePartSweepValue_succ` at `A = 1` expresses `V_3` through
  `V_2` and the two defects at `[2]`, and the defects are evaluated at **no** `A` at all — `Δ¹_A`
  and `Δ²_A` are named, not computed. At `A = 2` that needs the eleven `y_1`-monomials of `G_2` and
  `z_1` on each, the computation `HJO/Shuffle/SweepStageWordTwoThreeTwoValue.lean` runs at the
  nine-hundred-line scale one step earlier.
* **Nothing here says the clause is false anywhere**; no two evaluated values are compared.
* No defect is shown to be nonzero, and no closed form in `A` is claimed or suggested: `V_A` has
  `2, 9, 26` `e`-monomials at `A = 1, 2, 3` and there is none to be had.

## Consistency checks

Two pairs, each arriving at a value computed by a route that shares no lemma with this file's.

* `HJO.Sweep.constantCoeff_dminus_one_auxVar_sq_mul_zopOneStar_one_C_elemSymm_one` and
  `..._of_step`, the same `Prop` by `rfl` at `..._eq`: one `z_1` letter at `l = 2` on `Ce_1`. The
  direct route runs `HJO.Sweep.zopOneStar_one_C_elemSymm_one` (`z_1(Ce_1) = q(1-q)uy_1`) and one
  `B_3(1)`; the route through the step evaluates `D_2(B_0e_1) - T_{2,0}(e_1)`, where the two
  `e_1e_2` terms cancel and `-q(1-q)ue_3` is what is left. This is what pins the index `2` of `D_2`
  in the split: `D_3` there would leave a different answer.
* `HJO.Sweep.constantCoeff_dminus_one_replicatedTotal_levelKernelOne_of_split` and
  `HJO.Sweep.constantCoeff_dminus_one_replicatedTotal_levelKernelOne`, the same `Prop` by `rfl` at
  `..._eq`: the whole replicated letter on the refutation's witness `F_0 = Ce_1 + qy_1`. The direct
  route goes through `z_1` on `quy_1^3` and the three values `B_2e_2`, `B_3e_1`, `B_41`; this one
  through `D_1(e_3)` at `(q,u)` and at `(q,0)` — `HJO.Sym.dop_one_elemSymm_three` twice, the second
  via `HJO.Sym.bop_natCast` — and their difference is divisible by `u(1-q)`, which is where the
  scalar `(qu)^{-1}q/(1-q)` is spent. A sign on the defect sum, or `D_2` in place of `D_1` on the
  outer letter, would separate them.

`HJO.Sweep.constantCoeff_dminus_one_replicatedTotal_two_three_zero_split` and
`HJO.Mellit.onePartSweepValue_succ` are *derived* from the two checked statements by `module` and
one rewrite of `HJO.Sweep.constantCoeff_dminus_one_of_mem_piece`, so they need no third check: Lean
composes them.

## Genericity

**Everything down to and including `HJO.Mellit.onePartSweepValue_succ` is unconditional** — no
hypothesis on `q` or `u` anywhere. The three scalars that are the inverse-becomes-zero hazard,
`(qu)^{-1}` of `HJO.Sweep.slopeOperator` and `q/(1-q)` of `HJO.Sweep.zop` twice, are carried
symbolically on both sides: at `q = 0`, `u = 0` or `q = 1` one of them is `0` in a field, the letter
being evaluated is the zero map, and the identities read `0 = 0` rather than becoming false. The
membership `F ∈ V_1` is not decoration: `HJO.Sweep.constantCoeff_dminus_one_of_mem_piece` and
`HJO.Sweep.zopOneStar_one_of_mem_piece` both spend it, and off `V_1` the `y_1`-degree is not the
whole exponent of a monomial.

`HJO.Mellit.lhsAt_two_three_singleton_succ_of_creation` and
`HJO.Mellit.forall_lhsAt_two_three_singleton_succ_of_creation`: `q ≠ 0`, `u ≠ 0`, `q ≠ 1`, verbatim
`HJO.Mellit.lhsAt_two_three_singleton_iff_bop`'s, and spent only on turning the clause into the
equation `Θ(h_A)(1) = V_A`; the recursion itself needs none of them. They are the same three values
at which the step's own scalars would collapse, so nothing is excluded twice over.

`HJO.Mellit.forall_lhsAt_two_three_singleton_succ_of_creation_of_axis`: those plus
`M = (1-q)(1-u) ≠ 0` — hence also `u ≠ 1` — and `qu ≠ 0`, `qu ≠ 1`, every one of them
`HJO.Mellit.lhsAt_two_three_one_of_axis`'s and none of them this file's.

`HJO.Mellit.creation_step_zero_of_axis`: those plus `qu + 1 ≠ 0`, which is
`HJO.Mellit.lhsAt_two_three_two_of_axis`'s and is where the degree-two axis expansion is solved for
`Θ(h_2)`.

`HJO.Sweep.twistDop_two_zero_elemSymm_one`, `HJO.Sweep.sum_twistDop_C`: **none**.
`HJO.Sweep.constantCoeff_dminus_one_auxVar_sq_mul_zopOneStar_one_C_elemSymm_one` and its two
companions: `q ≠ 1` alone, the `q/(1-q)` of `HJO.Sweep.zop`, cancelled against the bracket's factor
`1 - q`.

`HJO.Sweep.constantCoeff_dminus_one_replicatedTotal_levelKernelOne_of_split`: `q ≠ 0`, `u ≠ 0`,
`q ≠ 1`, verbatim those of the statement it reproves — deliberately, so that the `rfl` check
typechecks. At each of the three the letter really is the zero map, so these are the hazard and not
decoration.

`(2,3)` is coprime with `1 < a < b`, the range the `hlhs` binder of
`HJO.Mellit.shuffle_of_lhs_and_induction` quantifies over.

The statements here are values of `HJO.Mellit.replicatedLetter`, `HJO.Sweep.zop`, `HJO.Sym.Bop`,
`HJO.Sweep.bopExt` and `HJO.Sym.DopInt`, and a reduction of the `hlhs` clause rather than an
instance of it; the clause itself is `HJO.Mellit.lhsRewrite_sweepWitness`'s business.

## References

The definitions and results this file rests on: `HJO.Mellit.lhsRewrite_sweepWitness`,
`HJO.Mellit.stage`, `HJO.Mellit.replicatedLetter`, `HJO.Sweep.zop`, `HJO.Sweep.slopeOperator`,
`HJO.Sym.Bop`, `HJO.Sweep.bopExt`, `HJO.Sweep.dplusStar`, `HJO.Sweep.dminus`, `HJO.Sym.DopInt`,
`HJO.Sym.Qop`, `HJO.Sym.IsSlopeHom`, `HJO.Sym.completeHomog`, `HJO.Sym.elemSymm`,
`HJO.Sweep.dop_eq_neg_dminusCM_auxVar_pow_dplusStar`.
-/

-- Every computation below closes on a polynomial identity in the `e`-monomials and the scalars
-- `C q`, `C u`, normalised by one shared rewrite set; which members of it fire depends on the
-- monomial, so some are unused in each individual proof. This is the arrangement of
-- `HJO/Shuffle/SweepReplicatedNoValueRecursion.lean`, and its linter exemption too.
set_option linter.unusedSimpArgs false

@[expose] public section

namespace HJO.Sweep

open Finset HJO.Sym HJO.Mellit

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-! ### The twisted basic operator -/

/-- **`T_{l,m}`: the basic operator of `HJO.Sym.DopInt` with one Hall--Littlewood operator
inserted.**

`ct(d_-^{(1)}(y_1^l·B_m(d^*_+(Cg))))`, the second branch of `HJO.Sweep.zopOneStar_one_of_mem_piece`
read after `l` raises and the lowering projection. `HJO.Sweep.dop_eq_constantCoeff_dminus_one` says
`D_l` is this very expression with the `B_m` of `HJO.Sweep.bopExt` deleted, so
`D_l(B_mg) - T_{l,m}(g)` is a commutator and nothing else.

`m` ranges over `ℤ` because `HJO.Sym.Bop` does; the consumers instantiate at a `y_1`-degree. -/
noncomputable def twistDop (q u : L) (l : ℕ) (m : ℤ) (g : Lambda L) : Lambda L :=
  MvPolynomial.constantCoeff
    (dminus q 1 ((auxVar 1 : Total L) ^ l *
      bopExt q m (dplusStar q u 0 (MvPolynomial.C g : Total L))))

/-- **`D_l(g) = ct(d_-^{(1)}(y_1^ld^*_+(Cg)))`.** The
`HJO.Sweep.dop_eq_neg_dminusCM_auxVar_pow_dplusStar` family
`HJO.Sweep.dminus_auxVar_pow_mul_dplusStar_C` with the `MvPolynomial.C` stripped, so that it can be
compared letter for letter with `HJO.Sweep.twistDop`. Unconditional. -/
theorem dop_eq_constantCoeff_dminus_one (q u : L) (l : ℕ) (g : Lambda L) :
    Dop q u l g
      = MvPolynomial.constantCoeff
          (dminus q 1 ((auxVar 1 : Total L) ^ l *
            dplusStar q u 0 (MvPolynomial.C g : Total L))) := by
  rw [dminus_auxVar_pow_mul_dplusStar_C, MvPolynomial.constantCoeff_C]

/-- `T_{l,m}` is homogeneous of degree one in its argument: every factor of it is `L`-linear. -/
theorem twistDop_smul (q u : L) (l : ℕ) (m : ℤ) (x : L) (g : Lambda L) :
    twistDop q u l m (x • g) = x • twistDop q u l m g := by
  rw [twistDop, twistDop, C_smul_total, map_smul, map_smul, mul_smul_comm, map_smul,
    constantCoeff_smul]

/-- `T_{l,m}(0) = 0`, which is what lets a defect sum over an empty support be read as a value. -/
theorem twistDop_zero (q u : L) (l : ℕ) (m : ℤ) : twistDop q u l m (0 : Lambda L) = 0 := by
  rw [twistDop]
  simp

/-- **The defect sum at a single monomial of `V_1` is one value of `T_{l,m}`.**

The support of `y_1^mCa` is `{single 0 m}` when `a ≠ 0` and empty otherwise, and in the second case
both sides are `0` by `HJO.Sweep.twistDop_zero` — so no hypothesis `a ≠ 0` is needed and the
statement is unconditional. This is what makes the two checks below cheap: their witnesses have one
monomial each after the inner `z_1`. -/
theorem sum_twistDop_auxVar_pow_mul_C (q u : L) (l m : ℕ) (a : Lambda L) :
    ∑ d ∈ ((auxVar 1 : Total L) ^ m * MvPolynomial.C a).support,
        twistDop q u l ((d 0 : ℕ) : ℤ)
          (MvPolynomial.coeff d ((auxVar 1 : Total L) ^ m * MvPolynomial.C a))
      = twistDop q u l (m : ℤ) a := by
  have hmon : ((auxVar 1 : Total L) ^ m * MvPolynomial.C a)
      = MvPolynomial.monomial (Finsupp.single 0 m) a := by
    rw [auxVar, Nat.sub_self, MvPolynomial.X_pow_eq_monomial, mul_comm,
      MvPolynomial.C_mul_monomial, mul_one]
  rcases eq_or_ne a 0 with rfl | ha
  · rw [hmon]
    simp [twistDop_zero]
  · classical
    rw [hmon, MvPolynomial.support_monomial, ite_eq_right ha, Finset.sum_singleton]
    simp [MvPolynomial.coeff_monomial]

/-! ### One `z_1` letter, at the `Λ` level -/

/-- **ONE `z_1` LETTER AT THE `Λ` LEVEL, at every `l` and on all of `V_1`:**

  `ct(d_-^{(1)}(y_1^lz_1F)) = q/(1-q)·( D_l(ct(d_-^{(1)}F)) - ∑_m T_{l,m}(F_m) )`.

`HJO.Sweep.zopOneStar_one_of_mem_piece` gives `z_1F` as a sum over the `y_1`-monomials of `F` of two
branches; `HJO.Sweep.dop_eq_constantCoeff_dminus_one` turns the first into `D_l(B_mF_m)` and
`HJO.Sweep.twistDop` names the second, and `∑_m B_mF_m` is the value `ct(d_-^{(1)}F)` by
`HJO.Sweep.constantCoeff_dminus_one_of_mem_piece`. So the first summand is a function of the
**value** and the second reads the **vector**: the split is exactly where
`HJO.Sweep.not_exists_factorization_replicated_two_three` says the obstruction lives.

Every operator on the right is an operator on `Λ` — `HJO.Sym.DopInt`, `HJO.Sym.Bop` — with no train,
no substitution on the total space and no index above `2`.

`F ∈ V_1` is spent twice, by `HJO.Sweep.zopOneStar_one_of_mem_piece` and by
`HJO.Sweep.constantCoeff_dminus_one_of_mem_piece`. **No hypothesis on `q` or `u`:** the scalar
`q/(1-q)` of `HJO.Sweep.zop` is carried symbolically, so at `q = 1` both sides are `0`. -/
theorem constantCoeff_dminus_one_auxVar_pow_mul_zopOneStar_one_of_mem_piece (q u : L) (l : ℕ)
    {F : Total L} (hF : F ∈ piece L 1) :
    MvPolynomial.constantCoeff (dminus q 1 ((auxVar 1 : Total L) ^ l * zopOneStar q u 1 F))
      = (q / (1 - q)) •
          (Dop q u l (MvPolynomial.constantCoeff (dminus q 1 F))
            - ∑ d ∈ F.support, twistDop q u l ((d 0 : ℕ) : ℤ) (MvPolynomial.coeff d F)) := by
  have key : ∀ d ∈ F.support,
      MvPolynomial.constantCoeff (dminus q 1 ((auxVar 1 : Total L) ^ l *
          (dplusStar q u 0
              (MvPolynomial.C (Bop q ((d 0 : ℕ) : ℤ) (MvPolynomial.coeff d F)))
            - bopExt q ((d 0 : ℕ) : ℤ)
                (dplusStar q u 0 (MvPolynomial.C (MvPolynomial.coeff d F) : Total L)))))
        = Dop q u l (Bop q ((d 0 : ℕ) : ℤ) (MvPolynomial.coeff d F))
          - twistDop q u l ((d 0 : ℕ) : ℤ) (MvPolynomial.coeff d F) := by
    intro d _
    rw [mul_sub, map_sub, map_sub, ← dop_eq_constantCoeff_dminus_one, twistDop]
  have hDop : ∑ d ∈ F.support, Dop q u l (Bop q ((d 0 : ℕ) : ℤ) (MvPolynomial.coeff d F))
      = Dop q u l (MvPolynomial.constantCoeff (dminus q 1 F)) := by
    rw [constantCoeff_dminus_one_of_mem_piece q hF, map_sum]
  rw [zopOneStar_one_of_mem_piece q u hF, mul_smul_comm, map_smul, constantCoeff_smul,
    Finset.mul_sum, map_sum, map_sum, Finset.sum_congr rfl key, Finset.sum_sub_distrib, hDop]

/-! ### The replicated letter, with the outer `z_1` at the `Λ` level -/

/-- **THE OUTER LETTER OF `Z^{(1)}_{2,3}` AT THE `Λ` LEVEL:**

`ct(d_-^{(1)}Z^{(1)}_{2,3}F) = (qu)^{-1}q/(1-q)·(D_1(ct(d_-^{(1)}(y_1^2z_1F))) - ∑_j T_{1,j}(H_j))`,

  `H = y_1^2z_1F`.

`HJO.Sweep.replicatedTotal_two_three_zero_of_mem_piece` expands the outer `z_1` of
`(qu)^{-1}y_1z_1y_1^2z_1` over the monomials of `H`, and
`HJO.Sweep.auxVar_sq_mul_zopOneStar_one_mem_piece` is the membership `H ∈ V_1` that lets the same
two identifications be made there: `D_1` on the first branch — the outer `y_1` is the single power
in `d_-^{(1)}(y_1d^*_+(C·))` — and `HJO.Sweep.twistDop` at `l = 1` on the second.

The intermediate `H` is not eliminated here;
`HJO.Sweep.constantCoeff_dminus_one_replicatedTotal_two_three_zero_split` does that with the
previous theorem at `l = 2`. **No hypothesis on `q` or `u`.**
-/
theorem constantCoeff_dminus_one_replicatedTotal_two_three_zero_of_mem_piece (q u : L)
    {F : Total L} (hF : F ∈ piece L 1) :
    MvPolynomial.constantCoeff (dminus q 1 (replicatedTotal q u 2 3 0 F))
      = ((q * u)⁻¹ * (q / (1 - q))) •
          (Dop q u 1 (MvPolynomial.constantCoeff
              (dminus q 1 ((auxVar 1 : Total L) ^ 2 * zopOneStar q u 1 F)))
            - ∑ d ∈ ((auxVar 1 : Total L) ^ 2 * zopOneStar q u 1 F).support,
                twistDop q u 1 ((d 0 : ℕ) : ℤ)
                  (MvPolynomial.coeff d
                    ((auxVar 1 : Total L) ^ 2 * zopOneStar q u 1 F))) := by
  have hHmem : ((auxVar 1 : Total L) ^ 2 * zopOneStar q u 1 F) ∈ piece L 1 :=
    auxVar_sq_mul_zopOneStar_one_mem_piece q u hF
  have key : ∀ d ∈ ((auxVar 1 : Total L) ^ 2 * zopOneStar q u 1 F).support,
      MvPolynomial.constantCoeff (dminus q 1 ((auxVar 1 : Total L) *
          (dplusStar q u 0
              (MvPolynomial.C (Bop q ((d 0 : ℕ) : ℤ)
                (MvPolynomial.coeff d ((auxVar 1 : Total L) ^ 2 * zopOneStar q u 1 F))))
            - bopExt q ((d 0 : ℕ) : ℤ)
                (dplusStar q u 0 (MvPolynomial.C (MvPolynomial.coeff d
                  ((auxVar 1 : Total L) ^ 2 * zopOneStar q u 1 F)) : Total L)))))
        = Dop q u 1 (Bop q ((d 0 : ℕ) : ℤ)
            (MvPolynomial.coeff d ((auxVar 1 : Total L) ^ 2 * zopOneStar q u 1 F)))
          - twistDop q u 1 ((d 0 : ℕ) : ℤ)
              (MvPolynomial.coeff d ((auxVar 1 : Total L) ^ 2 * zopOneStar q u 1 F)) := by
    intro d _
    rw [show (auxVar 1 : Total L) = (auxVar 1 : Total L) ^ 1 from (pow_one _).symm, mul_sub,
      map_sub, map_sub, ← dop_eq_constantCoeff_dminus_one, twistDop]
  have hDop : ∑ d ∈ ((auxVar 1 : Total L) ^ 2 * zopOneStar q u 1 F).support,
        Dop q u 1 (Bop q ((d 0 : ℕ) : ℤ)
          (MvPolynomial.coeff d ((auxVar 1 : Total L) ^ 2 * zopOneStar q u 1 F)))
      = Dop q u 1 (MvPolynomial.constantCoeff
          (dminus q 1 ((auxVar 1 : Total L) ^ 2 * zopOneStar q u 1 F))) := by
    rw [constantCoeff_dminus_one_of_mem_piece q hHmem, map_sum]
  rw [replicatedTotal_two_three_zero_of_mem_piece q u hF, map_smul, constantCoeff_smul,
    Finset.mul_sum, map_sum, map_sum, Finset.sum_congr rfl key, Finset.sum_sub_distrib, hDop]

/-- **THE STEP IN SPLIT FORM:**

  `ct(d_-^{(1)}Z^{(1)}_{2,3}F)
     = cγ·D_1(D_2(ct(d_-^{(1)}F))) - cγ·D_1(∑_m T_{2,m}(F_m)) - c·∑_j T_{1,j}(H_j)`,

`c = (qu)^{-1}q/(1-q)`, `γ = q/(1-q)`, `H = y_1^2z_1F`. The previous two theorems composed, by
`module` on the scalars.

**The value-only part of the replicated letter is `D_1D_2`** — and
`HJO.Sym.qop_two_three_eq_bracket_dop` reads `Q_{2,3} = M^{-1}(D_2D_1 - D_1D_2)`, so the step
produces one of the two terms of the very commutator the creation side of the clause is built from.
The other two summands are the defects, and they read the vector: `T_{2,m}` at the `y_1`-degrees of
`F` and `T_{1,j}` at those of `y_1^2z_1F`.

**No hypothesis on `q` or `u`**, `F ∈ V_1` excepted. -/
theorem constantCoeff_dminus_one_replicatedTotal_two_three_zero_split (q u : L) {F : Total L}
    (hF : F ∈ piece L 1) :
    MvPolynomial.constantCoeff (dminus q 1 (replicatedTotal q u 2 3 0 F))
      = ((q * u)⁻¹ * (q / (1 - q)) ^ 2) •
            Dop q u 1 (Dop q u 2 (MvPolynomial.constantCoeff (dminus q 1 F)))
        - ((q * u)⁻¹ * (q / (1 - q)) ^ 2) •
            Dop q u 1 (∑ d ∈ F.support,
              twistDop q u 2 ((d 0 : ℕ) : ℤ) (MvPolynomial.coeff d F))
        - ((q * u)⁻¹ * (q / (1 - q))) •
            ∑ d ∈ ((auxVar 1 : Total L) ^ 2 * zopOneStar q u 1 F).support,
              twistDop q u 1 ((d 0 : ℕ) : ℤ)
                (MvPolynomial.coeff d ((auxVar 1 : Total L) ^ 2 * zopOneStar q u 1 F)) := by
  rw [constantCoeff_dminus_one_replicatedTotal_two_three_zero_of_mem_piece q u hF,
    constantCoeff_dminus_one_auxVar_pow_mul_zopOneStar_one_of_mem_piece q u 2 hF, map_smul,
    map_sub]
  module

end HJO.Sweep

namespace HJO.Mellit

open Finset HJO.Sym HJO.Sweep

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-! ### The two defects of the one-part family -/

/-- **The inner defect of the one-part step at `[A]`:** `Δ²_A = ∑_m T_{2,m}((G_A)_m)`, the sum over
the `y_1`-monomials of the one-part stage word of `HJO.Sweep.twistDop` at `l = 2`.

This is the part of `HJO.Sweep.constantCoeff_dminus_one_replicatedTotal_two_three_zero_split` that
reads the vector rather than the value. Named, **not evaluated**: no closed form for it is proved at
any `A`. -/
noncomputable def onePartDefectTwo (q u : L) (A : ℕ) : Lambda L :=
  ∑ d ∈ (stageWordTotal q u 2 3 [A] : Total L).support,
    twistDop q u 2 ((d 0 : ℕ) : ℤ)
      (MvPolynomial.coeff d (stageWordTotal q u 2 3 [A] : Total L))

/-- **The outer defect of the one-part step at `[A]`:** `Δ¹_A = ∑_j T_{1,j}((y_1^2z_1G_A)_j)`.

The companion of `HJO.Mellit.onePartDefectTwo` at the outer letter; it reads the vector one `z_1`
further in, which is why it cannot be folded into the inner one. Named, **not evaluated**. -/
noncomputable def onePartDefectOne (q u : L) (A : ℕ) : Lambda L :=
  ∑ d ∈ ((auxVar 1 : Total L) ^ 2 *
      zopOneStar q u 1 (stageWordTotal q u 2 3 [A])).support,
    twistDop q u 1 ((d 0 : ℕ) : ℤ)
      (MvPolynomial.coeff d ((auxVar 1 : Total L) ^ 2 *
        zopOneStar q u 1 (stageWordTotal q u 2 3 [A])))

/-- **`V_A = -ct(d_-^{(1)}G_A)`.** `HJO.Mellit.onePartSweepValue` is defined as the negated
Hall--Littlewood sum over the monomials of the one-part stage word, and
`HJO.Sweep.constantCoeff_dminus_one_of_mem_piece` is that sum — the membership being
`HJO.Mellit.stageWordTotal_singleton_mem_piece`. Unconditional; this is the only place the sign of
the clause's sweep side enters the recursion below. -/
theorem onePartSweepValue_eq_neg_constantCoeff (q u : L) (A : ℕ) :
    onePartSweepValue q u A
      = -MvPolynomial.constantCoeff (dminus q 1 (stageWordTotal q u 2 3 [A])) := by
  rw [onePartSweepValue,
    constantCoeff_dminus_one_of_mem_piece q (stageWordTotal_singleton_mem_piece q u 2 3 A)]

/-- **THE ONE-PART RECURSION, CARRYING THE VECTOR**, at every `A` and with no hypothesis:

  `V_{A+2} = cγ·D_1(D_2(V_{A+1})) + cγ·D_1(Δ²_{A+1}) + c·Δ¹_{A+1}`,

`c = (qu)^{-1}q/(1-q)`, `γ = q/(1-q)`. `HJO.Mellit.stageWordTotal_singleton_succ` turns `G_{A+2}`
into one replicated letter on `G_{A+1}`, and
`HJO.Sweep.constantCoeff_dminus_one_replicatedTotal_two_three_zero_split` evaluates that letter.

`HJO.Sweep.not_exists_factorization_replicated_two_three` says no recursion on the values alone
exists; this is the recursion that does, and it shows precisely what the extra datum is — the two
defect sums, which read `G_{A+1}` degree by degree and are evaluated at no `A`.

The offset is the truncated subtraction in `HJO.Mellit.stage`: the letter is applied `A - 1` times,
so the step is from `[A+1]` to `[A+2]` and `[0]` is outside it (and outside the `hlhs` binder, whose
parts are positive). -/
theorem onePartSweepValue_succ (q u : L) (A : ℕ) :
    onePartSweepValue q u (A + 2)
      = ((q * u)⁻¹ * (q / (1 - q)) ^ 2) •
            Dop q u 1 (Dop q u 2 (onePartSweepValue q u (A + 1)))
        + ((q * u)⁻¹ * (q / (1 - q)) ^ 2) • Dop q u 1 (onePartDefectTwo q u (A + 1))
        + ((q * u)⁻¹ * (q / (1 - q))) • onePartDefectOne q u (A + 1) := by
  rw [onePartSweepValue_eq_neg_constantCoeff q u (A + 2), stageWordTotal_singleton_succ,
    constantCoeff_dminus_one_replicatedTotal_two_three_zero_split q u
      (stageWordTotal_singleton_mem_piece q u 2 3 (A + 1)),
    onePartSweepValue_eq_neg_constantCoeff q u (A + 1), onePartDefectTwo, onePartDefectOne,
    map_neg, map_neg]
  module

/-- **THE INDUCTION STEP OF THE ONE-PART FAMILY, with the creation side's obligation named.**

From the clause at `[A+1]` and the single identity

  `Θ(h_{A+2})(1) = cγ·D_1(D_2(Θ(h_{A+1})(1))) + cγ·D_1(Δ²_{A+1}) + c·Δ¹_{A+1}`,

the clause at `[A+2]`. The sweep side is fully discharged: `HJO.Mellit.onePartSweepValue_succ` is a
theorem, so what `hstep` asks is exactly that the creation side satisfy the sweep side's own
recursion, with the defects as given data. **Nothing about a composition of length two, and nothing
about the stage word, occurs in `hstep`.**

`hstep` is not discharged here at any `A`. `HJO.Mellit.creation_step_zero_of_axis` verifies it at
`A = 0` from the two decided instances.

Genericity: `q ≠ 0`, `u ≠ 0`, `q ≠ 1`, verbatim
`HJO.Mellit.lhsAt_two_three_singleton_iff_bop`'s and spent only on the clause-to-value equivalence;
the recursion needs none of them. -/
theorem lhsAt_two_three_singleton_succ_of_creation (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1)
    (A : ℕ) {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)}
    (hA : LhsAt q u 2 3 Θ [A + 1])
    (hstep : Θ (completeHomog L (A + 2)) 1
      = ((q * u)⁻¹ * (q / (1 - q)) ^ 2) •
            Dop q u 1 (Dop q u 2 (Θ (completeHomog L (A + 1)) 1))
        + ((q * u)⁻¹ * (q / (1 - q)) ^ 2) • Dop q u 1 (onePartDefectTwo q u (A + 1))
        + ((q * u)⁻¹ * (q / (1 - q))) • onePartDefectOne q u (A + 1)) :
    LhsAt q u 2 3 Θ [A + 2] := by
  refine (lhsAt_two_three_singleton_iff_onePartSweepValue hq0 hu0 hq1 (A + 2) Θ).2 ?_
  rw [hstep, (lhsAt_two_three_singleton_iff_onePartSweepValue hq0 hu0 hq1 (A + 1) Θ).1 hA,
    onePartSweepValue_succ]

/-! ### The induction assembled: the sweep side is discharged -/

/-- **THE ONE-PART FAMILY AT EVERY `A ≥ 1`, FROM THE CREATION-SIDE STEP ALONE.**

The induction of `HJO.Mellit.lhsAt_two_three_singleton_succ_of_creation` run from the base case: the
clause at `[1]` plus the step identity at every `A` gives `∀ A, LhsAt q u 2 3 Θ [A+1]`. The sweep
side of the one-part binder is therefore **completely discharged**, and what remains of the family
is the one hypothesis `hstep`, a family of identities between values of `Θ` at `h_m` for two
consecutive `m` and two explicit elements of `Λ`.

`A ≥ 1` is not a restriction: `[0]` is not a composition with positive parts, and
`HJO.Mellit.LhsComputes` quantifies only over those.

Genericity: `q ≠ 0`, `u ≠ 0`, `q ≠ 1`. -/
theorem forall_lhsAt_two_three_singleton_succ_of_creation (hq0 : q ≠ 0) (hu0 : u ≠ 0)
    (hq1 : q ≠ 1) {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)} (hbase : LhsAt q u 2 3 Θ [1])
    (hstep : ∀ A : ℕ, Θ (completeHomog L (A + 2)) 1
      = ((q * u)⁻¹ * (q / (1 - q)) ^ 2) •
            Dop q u 1 (Dop q u 2 (Θ (completeHomog L (A + 1)) 1))
        + ((q * u)⁻¹ * (q / (1 - q)) ^ 2) • Dop q u 1 (onePartDefectTwo q u (A + 1))
        + ((q * u)⁻¹ * (q / (1 - q))) • onePartDefectOne q u (A + 1)) :
    ∀ A : ℕ, LhsAt q u 2 3 Θ [A + 1] := by
  intro A
  induction A with
  | zero => exact hbase
  | succ n ih =>
    exact lhsAt_two_three_singleton_succ_of_creation hq0 hu0 hq1 n ih (hstep n)

/-- **The same with the base case discharged**, so that `hstep` is the *only* hypothesis about the
clause left: `HJO.Mellit.lhsAt_two_three_one_of_axis` is the `[1]` instance.

Genericity: `M = (1-q)(1-u) ≠ 0`, `q ≠ 0`, `u ≠ 0`, `q ≠ 1`, `qu ≠ 0`, `qu ≠ 1` — the union of the
previous theorem's three and the base case's, and nothing of this file's own. -/
theorem forall_lhsAt_two_three_singleton_succ_of_creation_of_axis (hM : (1 - q) * (1 - u) ≠ 0)
    (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) (hv0 : q * u ≠ 0) (hv1 : q * u ≠ 1)
    {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)} (hΘ : IsSlopeHom 2 3 q u Θ)
    (hstep : ∀ A : ℕ, Θ (completeHomog L (A + 2)) 1
      = ((q * u)⁻¹ * (q / (1 - q)) ^ 2) •
            Dop q u 1 (Dop q u 2 (Θ (completeHomog L (A + 1)) 1))
        + ((q * u)⁻¹ * (q / (1 - q)) ^ 2) • Dop q u 1 (onePartDefectTwo q u (A + 1))
        + ((q * u)⁻¹ * (q / (1 - q))) • onePartDefectOne q u (A + 1)) :
    ∀ A : ℕ, LhsAt q u 2 3 Θ [A + 1] :=
  forall_lhsAt_two_three_singleton_succ_of_creation hq0 hu0 hq1
    (lhsAt_two_three_one_of_axis hM hq0 hu0 hq1 hv0 hv1 hΘ) hstep

/-- **The step hypothesis holds at `A = 0`.**

`Θ(h_1)(1) = V_1` and `Θ(h_2)(1) = V_2` are the two decided one-part instances
(`HJO.Mellit.lhsAt_two_three_one_of_axis`, `HJO.Mellit.lhsAt_two_three_two_of_axis`), and
`HJO.Mellit.onePartSweepValue_succ` at `A = 0` relates `V_2` to `V_1` and the defects at `[1]`.

**This is a non-vacuity statement, not a check on the recursion.** It is *derived* from
`HJO.Mellit.onePartSweepValue_succ`, so a sign error in that recursion would be reproduced here
rather than exposed; what it does establish is that the hypothesis of
`HJO.Mellit.forall_lhsAt_two_three_singleton_succ_of_creation` is satisfiable and correctly shaped
at the one index where both sides of the clause are known. The checks on the recursion itself are
the two checks at the end of this file.

Genericity: `M ≠ 0`, `q ≠ 0`, `u ≠ 0`, `q ≠ 1`, `qu ≠ 0`, `qu ≠ 1`, `qu + 1 ≠ 0`, the last being
`HJO.Mellit.lhsAt_two_three_two_of_axis`'s. -/
theorem creation_step_zero_of_axis (hM : (1 - q) * (1 - u) ≠ 0) (hq0 : q ≠ 0) (hu0 : u ≠ 0)
    (hq1 : q ≠ 1) (hv0 : q * u ≠ 0) (hv1 : q * u ≠ 1) (hvn : q * u + 1 ≠ 0)
    {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)} (hΘ : IsSlopeHom 2 3 q u Θ) :
    Θ (completeHomog L (0 + 2)) 1
      = ((q * u)⁻¹ * (q / (1 - q)) ^ 2) •
            Dop q u 1 (Dop q u 2 (Θ (completeHomog L (0 + 1)) 1))
        + ((q * u)⁻¹ * (q / (1 - q)) ^ 2) • Dop q u 1 (onePartDefectTwo q u (0 + 1))
        + ((q * u)⁻¹ * (q / (1 - q))) • onePartDefectOne q u (0 + 1) := by
  have h1 := (lhsAt_two_three_singleton_iff_onePartSweepValue hq0 hu0 hq1 1 Θ).1
    (lhsAt_two_three_one_of_axis hM hq0 hu0 hq1 hv0 hv1 hΘ)
  have h2 := (lhsAt_two_three_singleton_iff_onePartSweepValue hq0 hu0 hq1 2 Θ).1
    (lhsAt_two_three_two_of_axis hM hq0 hu0 hq1 hv0 hv1 hvn hΘ)
  rw [show (0 : ℕ) + 2 = 2 from rfl, show (0 : ℕ) + 1 = 1 from rfl, h1, h2,
    onePartSweepValue_succ q u 0]

end HJO.Mellit

namespace HJO.Sweep

open Finset HJO.Sym HJO.Mellit

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-! ### Consistency checks -/

/-- **`T_{2,0}(e_1) = qB_2(e_1) - (q-1)ue_3`, written out.**

`d^*_+(Ce_1) = Ce_1 + (q-1)uy_1` (`HJO.Sweep.dplusStar_C_elemSymm_one_expand`), so `B_0` meets the
two `y_1`-degrees `0` and `1` and the lowering then reads `B_2` and `B_3`; `B_0e_1 = qe_1`
(`HJO.Sym.bop_zero_elemSymm_one'`), `B_01 = 1`, `B_31 = -e_3`, and `B_2e_1 = D_2e_1` at `u = 0`
(`HJO.Sym.bop_natCast`, `HJO.Sym.dop_two_elemSymm_one`).

Unconditional. This is the one value of `HJO.Sweep.twistDop` computed in this file, and it exists
for the check below. -/
theorem twistDop_two_zero_elemSymm_one (q u : L) :
    twistDop q u 2 (0 : ℤ) (elemSymm L 1)
      = q • (elemSymm L 1 * elemSymm L 2) - (q * (1 - q)) • elemSymm L 3
        - ((q - 1) * u) • elemSymm L 3 := by
  have hb0 : Bop q (0 : ℤ) (1 : Lambda L) = 1 := by
    rw [← Nat.cast_zero, bop_natCast_one, elemSymm_zero]; ring
  have hbe1 : Bop q (0 : ℤ) (elemSymm L 1) = q • elemSymm L 1 := by
    rw [← Nat.cast_zero]; exact bop_zero_elemSymm_one' q
  have hmul : (auxVar 1 : Total L) ^ 2 * ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (1 : Lambda L))
      = (auxVar 1 : Total L) ^ 3 * MvPolynomial.C (1 : Lambda L) := by ring
  rw [twistDop, dplusStar_C_elemSymm_one_expand, map_add, bopExt_C, map_smul,
    bopExt_auxVar_pow_mul_C, hb0, mul_add, mul_smul_comm, hmul, map_add, map_smul, map_add,
    constantCoeff_smul, dminus_one_auxVar_pow_mul_C, dminus_one_auxVar_pow_mul_C,
    MvPolynomial.constantCoeff_C, MvPolynomial.constantCoeff_C, hbe1,
    map_smul, bop_natCast, bop_natCast, dop_two_elemSymm_one, dop_apply_one]
  simp only [MvPolynomial.smul_eq_C_mul, map_sub, map_add, map_neg, map_mul, map_one, map_pow,
    map_zero, map_ofNat]
  ring

/-- **The defect sum at a constant of the total space:** the `m = 0` case of
`HJO.Sweep.sum_twistDop_auxVar_pow_mul_C`, stated at `Ca` rather than at `y_1^0Ca`. Unconditional.
-/
theorem sum_twistDop_C (q u : L) (l : ℕ) (a : Lambda L) :
    ∑ d ∈ (MvPolynomial.C a : Total L).support,
        twistDop q u l ((d 0 : ℕ) : ℤ) (MvPolynomial.coeff d (MvPolynomial.C a : Total L))
      = twistDop q u l (0 : ℤ) a := by
  have h := sum_twistDop_auxVar_pow_mul_C q u l 0 a
  simpa using h

/-- **CHECK ON THE ONE-LETTER STEP, computed directly.**
`ct(d_-^{(1)}(y_1^2z_1(Ce_1))) = -q(1-q)u·e_3`, off
`HJO.Sweep.zopOneStar_one_C_elemSymm_one` (`z_1(Ce_1) = q(1-q)uy_1`) and `B_31 = -e_3`. Nothing of
`HJO.Sweep.twistDop`, of `HJO.Sym.DopInt` or of this file's step occurs in the proof.

Genericity: `q ≠ 1`, the `q/(1-q)` of `HJO.Sweep.zop`, already cancelled inside that value. -/
theorem constantCoeff_dminus_one_auxVar_sq_mul_zopOneStar_one_C_elemSymm_one (hq1 : q ≠ 1) :
    MvPolynomial.constantCoeff (dminus q 1 ((auxVar 1 : Total L) ^ 2 *
        zopOneStar q u 1 (MvPolynomial.C (elemSymm L 1))))
      = (-(q * ((1 - q) * u))) • elemSymm L 3 := by
  have hmul : (auxVar 1 : Total L) ^ 2 * ((auxVar 1 : Total L) ^ 1 * MvPolynomial.C (1 : Lambda L))
      = (auxVar 1 : Total L) ^ 3 * MvPolynomial.C (1 : Lambda L) := by ring
  rw [zopOneStar_one_C_elemSymm_one hq1, mul_smul_comm, mul_smul_comm, hmul, map_smul,
    constantCoeff_smul, map_smul, constantCoeff_smul, dminus_one_auxVar_pow_mul_C,
    MvPolynomial.constantCoeff_C, bop_natCast_one, smul_smul]
  simp only [MvPolynomial.smul_eq_C_mul, map_neg, map_sub, map_mul, map_one, map_pow, map_ofNat]
  ring

/-- **THE SAME VALUE, re-derived through the `Λ`-level step at `l = 2`.**

`HJO.Sweep.constantCoeff_dminus_one_auxVar_pow_mul_zopOneStar_one_of_mem_piece` at `l = 2` and
`F = Ce_1` gives `q/(1-q)·(D_2(B_0e_1) - T_{2,0}(e_1))`, and the two routes agree only because the
`e_1e_2` terms of `D_2(qe_1)` and of `HJO.Sweep.twistDop_two_zero_elemSymm_one` cancel and the `e_3`
coefficients combine to `-q(1-q)u/(q/(1-q))`. **The index `2` of `D_2` is what this pins**: the
split of the replicated letter reads `D_2` on the inner letter and `D_1` on the outer one, and `D_3`
here would leave a different `e_3` coefficient.

Genericity: `q ≠ 1`, as the direct route — deliberately the same list, so that the `rfl` check below
typechecks. -/
theorem constantCoeff_dminus_one_auxVar_sq_mul_zopOneStar_one_C_elemSymm_one_of_step
    (hq1 : q ≠ 1) :
    MvPolynomial.constantCoeff (dminus q 1 ((auxVar 1 : Total L) ^ 2 *
        zopOneStar q u 1 (MvPolynomial.C (elemSymm L 1))))
      = (-(q * ((1 - q) * u))) • elemSymm L 3 := by
  have h1q : (1 : L) - q ≠ 0 := sub_ne_zero.2 (Ne.symm hq1)
  rw [constantCoeff_dminus_one_auxVar_pow_mul_zopOneStar_one_of_mem_piece q u 2
      (C_mem_piece (elemSymm L 1) 1), sum_twistDop_C, twistDop_two_zero_elemSymm_one,
    show (MvPolynomial.C (elemSymm L 1) : Total L)
        = (auxVar 1 : Total L) ^ 0 * MvPolynomial.C (elemSymm L 1) from by rw [pow_zero, one_mul],
    dminus_one_auxVar_pow_mul_C, MvPolynomial.constantCoeff_C, bop_zero_elemSymm_one', map_smul,
    dop_two_elemSymm_one]
  refine smul_right_injective (Lambda L) h1q ?_
  dsimp only
  rw [smul_smul, show (1 - q) * (q / (1 - q)) = q from by field_simp]
  simp only [MvPolynomial.smul_eq_C_mul, map_sub, map_add, map_neg, map_mul, map_one, map_pow,
    map_ofNat]
  ring

/-- **The two routes state the same `Prop`.** `rfl` between two proofs typechecks only if their
statements — and their hypothesis lists — are identical. -/
theorem constantCoeff_dminus_one_auxVar_sq_mul_zopOneStar_one_C_elemSymm_one_eq (hq1 : q ≠ 1) :
    constantCoeff_dminus_one_auxVar_sq_mul_zopOneStar_one_C_elemSymm_one (L := L) (u := u) hq1
      = constantCoeff_dminus_one_auxVar_sq_mul_zopOneStar_one_C_elemSymm_one_of_step hq1 := rfl


/-- **CHECK ON THE WHOLE REPLICATED LETTER: the refutation's defect, re-derived through the step.**

`ct(d_-^{(1)}Z^{(1)}_{2,3}(F_0)) = qu[e_2^2 + (q+u-1)e_1e_3 + (q^2+qu-q+u^2-u)e_4]` at
`F_0 = Ce_1 + qy_1` (`HJO.Sweep.levelKernelOne`), the value
`HJO.Sweep.constantCoeff_dminus_one_replicatedTotal_levelKernelOne` computes through `z_1` on
`quy_1^3` and the three Hall--Littlewood values `B_2e_2`, `B_3e_1`, `B_41`.

This route shares none of that.
`HJO.Sweep.constantCoeff_dminus_one_replicatedTotal_two_three_zero_of_mem_piece` reduces the letter
to `D_1` on `ct(d_-^{(1)}(y_1^2z_1F_0))` minus one value of `HJO.Sweep.twistDop`;
`HJO.Sweep.zopOneStar_one_levelKernelOne` collapses the inner `z_1` to the single monomial `quy_1`,
so the defect sum has one term, `T_{1,3}(qu) = quB_1(B_31)`; and the answer is
`q/(1-q)·(B_1e_3 - D_1e_3)` with `B_1e_3 = D_1e_3` read at `u = 0` (`HJO.Sym.bop_natCast`).
`HJO.Sym.dop_one_elemSymm_three` at `(q,u)` and at `(q,0)` differ by `u(1-q)` times the bracket
above, and `(1-q)` is what the scalar `q/(1-q)` cancels — which is the only place `q ≠ 1` is spent.

**So a sign on the defect sum, or `D_2` in place of `D_1` on the outer letter, or `(qu)^{-1}`
mis-placed, would each separate the two routes.**

Genericity: `q ≠ 0`, `u ≠ 0`, `q ≠ 1`, verbatim those of the direct statement, so that the `rfl`
check typechecks. -/
theorem constantCoeff_dminus_one_replicatedTotal_levelKernelOne_of_split (hq0 : q ≠ 0)
    (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    MvPolynomial.constantCoeff (dminus q 1 (replicatedTotal q u 2 3 0 (levelKernelOne q)))
      = (q * u) • (elemSymm L 2 * elemSymm L 2
          + (q + u - 1) • (elemSymm L 1 * elemSymm L 3)
          + (q ^ 2 + q * u - q + u ^ 2 - u) • elemSymm L 4) := by
  have hqu : q * u ≠ 0 := mul_ne_zero hq0 hu0
  have h1q : (1 : L) - q ≠ 0 := sub_ne_zero.2 (Ne.symm hq1)
  have hH : (auxVar 1 : Total L) ^ 2 * zopOneStar q u 1 (levelKernelOne q)
      = (auxVar 1 : Total L) ^ 3 * MvPolynomial.C ((q * u) • (1 : Lambda L)) := by
    rw [zopOneStar_one_levelKernelOne hq1, C_smul_total, mul_smul_comm, mul_smul_comm,
      MvPolynomial.C_1, mul_one]
    congr 1
  have hb3 : Bop q ((3 : ℕ) : ℤ) (1 : Lambda L) = -elemSymm L 3 := by
    rw [bop_natCast_one]; ring
  have hval : ∀ v : L, Dop q v 1 (-elemSymm L 3)
      = -((((1 - q) * (1 - v)) • (elemSymm L 2 * elemSymm L 2)
          + (-1 + (q + v) * ((1 - q) * (1 - v))) • (elemSymm L 1 * elemSymm L 3)
          + ((q ^ 2 + q * v + v ^ 2) * ((1 - q) * (1 - v))) • elemSymm L 4)) := by
    intro v
    rw [map_neg, dop_one_elemSymm_three]
  have htw : twistDop q u 1 ((3 : ℕ) : ℤ) ((q * u) • (1 : Lambda L))
      = (q * u) • Dop q 0 1 (-elemSymm L 3) := by
    rw [twistDop_smul, twistDop, dplusStar_C_one, bopExt_C, dminus_one_auxVar_pow_mul_C,
      MvPolynomial.constantCoeff_C, hb3, bop_natCast]
  rw [constantCoeff_dminus_one_replicatedTotal_two_three_zero_of_mem_piece q u
      (levelKernelOne_mem_piece q), hH, sum_twistDop_auxVar_pow_mul_C, htw,
    dminus_one_auxVar_pow_mul_C, MvPolynomial.constantCoeff_C, map_smul, hb3, map_smul,
    ← smul_sub, smul_smul,
    show (q * u)⁻¹ * (q / (1 - q)) * (q * u) = q / (1 - q) from by field_simp,
    hval, hval]
  refine smul_right_injective (Lambda L) h1q ?_
  dsimp only
  rw [smul_smul, show (1 - q) * (q / (1 - q)) = q from by field_simp]
  simp only [MvPolynomial.smul_eq_C_mul, map_sub, map_add, map_neg, map_mul, map_one, map_pow,
    map_zero, map_ofNat]
  ring

/-- **The two routes to the refutation's defect state the same `Prop`**, hypothesis lists included.
The right-hand side is `HJO.Sweep.constantCoeff_dminus_one_replicatedTotal_levelKernelOne`, proved
with no `HJO.Sym.DopInt` operator anywhere in it. -/
theorem constantCoeff_dminus_one_replicatedTotal_levelKernelOne_of_split_eq (hq0 : q ≠ 0)
    (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    constantCoeff_dminus_one_replicatedTotal_levelKernelOne_of_split (L := L) hq0 hu0 hq1
      = constantCoeff_dminus_one_replicatedTotal_levelKernelOne hq0 hu0 hq1 := rfl

end HJO.Sweep

end
