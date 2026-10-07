/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.MellitTwoPartTwoThree
public import HJO.Shuffle.SweepReplicatedIterate

/-! # The two-part family at `(2,3)`: the sweep side, evaluated

`HJO.Mellit.lhsAt_two_three_pair_iff` reduces the `hlhs` clause at a two-part composition `[A,B]`
and `(a,b) = (2,3)` to an equation whose right-hand side is
`ct(lowerRun q 2 (stageWordTotal q u 2 3 [A,B]))`. **Apart from the decided `(1,1)`, that sweep side
is not evaluated elsewhere.** This file evaluates it: at every `(A,B)` as a finite sum of
compositions of Hall--Littlewood operators, closed in `A` at `B = 1`, and with a recursion in `B`
whose step is likewise closed.

Nothing here is an equivalence. Every main result is a value or a recursion between values.

## What is evaluated

* **The length-two reading tool.** `HJO.Sweep.constantCoeff_lowerRun_two_of_mem_piece`:
  `ct(d_-^{(1)}d_-^{(2)}G) = ∑_{m,n}B_m(B_n(G_{mn}))` for every `G ∈ V_2`, the `y_1`-exponent read
  outermost. This is the length-two analogue of the length-one
  `HJO.Sweep.constantCoeff_dminus_one_of_mem_piece`, and it is what extending the clause from one
  part to two needs.
  `HJO.Sweep.constantCoeff_lowerRun_two_auxVar_pow_mul_of_mem_piece_one` is the same reading with
  two spectator powers in front.

* **`z_1` at the grading `2`, on the whole of `V_2`.** `HJO.Sweep.zCommTwo_of_mem_piece` and
  `HJO.Sweep.zopOneStar_two_of_mem_piece`: each `y_1^my_2^n`-monomial contributes `y_2^m` times the
  *grading-one* defect `HJO.Sweep.zDefect` at `n`. So `z_1` one grading up reads the same element of
  `V_1` that `z_1` at the grading `1` does, at every input rather than at a monomial
  (`HJO.Sweep.zCommTwo_monomial'` is the monomial case).

* **The whole tail of the clause, once.**
  `HJO.Sweep.constantCoeff_lowerRun_two_auxVar_one_mul_zCommTwo_of_mem_piece`:
  `ct(d_-^{(1)}d_-^{(2)}(y_1·zCommTwo(H))) = ∑_{m,n}∑_j B_{j+1}(B_m(zDefect_n(H_{mn})_j))` for every
  `H ∈ V_2`. Both main values below are this engine at one vector.

* **The value at `[A,1]`, at every `A`.**
  `HJO.Sweep.constantCoeff_lowerRun_two_stageWordTotal_pair_one`, unconditional, with the vector
  `HJO.Sweep.pairArgTwo q u A = T_1^{-1}(y_1^2d^*_+{}^{(1)}G_{1,A}(1))`. Every operator of the sweep
  is gone from the right: no train-as-sweep-word, no braid representation, no replication family, no
  stage, no slope operator, no `z`. What is left is `HJO.Sym.Bop` on `Λ` and, inside
  `HJO.Sweep.zDefect`, `d^*_+{}^{(0)}` and `HJO.Sweep.bopExt` — exactly the residual of the
  one-part evaluation `HJO.Mellit.lhsAt_two_three_singleton_iff_bop`, one part further along.

* **The recursion in `B`, evaluated.** `HJO.Mellit.stageWordTotal_pair_succ` (unconditional, at
  every `(a,b)`) peels one replicated letter off the second part, and
  `HJO.Sweep.constantCoeff_lowerRun_two_stageWordTotal_pair_succ` evaluates the step in the same
  shape as the base, with one extra `q^{-1}` from `HJO.Mellit.replicatedLetter`.
  `HJO.Sweep.constantCoeff_lowerRun_two_replicatedTotal_two_three_one_of_mem_piece` is where the
  step's leading braid letter is killed against `HJO.Sweep.dminus_dminus_braid`, as the stage's
  descending train is in `HJO.Sweep.lowerRun_two_stageTotal_one_of_slope`.

* **The sweep side at every `(A,B)` as a double Hall--Littlewood sum**,
  `HJO.Sweep.constantCoeff_lowerRun_two_stageWordTotal_pair`, the reading tool at the family
  `HJO.Mellit.stageWordTotal_pair_mem_piece` puts in `V_2`.

## Consistency checks

`HJO.Sweep.constantCoeff_lowerRun_two_stageWordTotal_two_three_of_pair` re-derives the **decided**
`(1,1)` value *through* the general reduction, and
`HJO.Sweep.constantCoeff_lowerRun_two_stageWordTotal_two_three_of_pair_eq` checks by `rfl` that its
statement is literally that of `HJO.Sweep.constantCoeff_lowerRun_two_stageWordTotal_two_three` —
which `rfl` can do only if the two `Prop`s are identical. The scalar the general reduction produces
carries **no** sign, and it has to meet that value's `-((q-1)u)` to give exactly `q`; it does.

`HJO.Sweep.sum_bop_zDefect_pairArgTwo_one` is the second check, on the *support-sum* machinery
rather than the scalar: the engine at `HJO.Sweep.pairArgTwo q u 1` is checked against
`HJO.Sweep.constantCoeff_lowerRun_two_auxVar_one_mul_zCommTwo_seedArgTwo`, whose five compositions
come from pushing two monomials through `HJO.Sweep.zCommTwo_monomial'` one at a time, with no
support sum anywhere. An index swapped, or an off-by-one in the `j+1`, would leave it unprovable.

## What is NOT claimed

* **No closed formula in the parts, and none is expected.** On the one-part family the value is
  homogeneous of degree `3A` with `2, 9, 26` `e`-monomials at `A = 1, 2, 3`; a recursion is the
  right target and a formula is not.
* **The recursion carries the vector, not the value** — which
  `HJO.Sweep.not_exists_factorization_replicated_two_three` shows is necessary:
  `ct ∘ d_-^{(1)} ∘ Z^{(1)}_{2,3}` does not factor through `ct ∘ d_-^{(1)}`, so no recursion on
  constant coefficients alone exists.
* **No new numeric decided point.** `HJO.Sweep.pairArgTwo q u A` and
  `HJO.Sweep.pairArgSucc q u A B` are not expanded in `e`-monomials at any `A ≥ 2` or `B ≥ 2`: that
  would need `d^*_+{}^{(1)}` and `T_1^{-1}` on the eleven monomials of
  `HJO.Mellit.stageWordTotal_two_three_two`, then the `HJO.Sweep.zDefect` values, then the `B`-word
  table in the `e`-basis. The machinery for it is all here; the table is not.
* `HJO.Sweep.pairArgTwo` and `HJO.Sweep.pairArgSucc` still carry `T_1^{-1}`, `d^*_+{}^{(1)}` and (in
  the latter) the inner `z_1^{(2)}`. The last is expanded by
  `HJO.Sweep.zopOneStar_two_of_mem_piece`; a general closed form for `T_1^{-1}(y_1^ay_2^b)` at
  arbitrary `(a,b)` is not proved here and is the one remaining gap in making the vectors explicit.

## Genericity

**Every main result of this file is unconditional**, and that is not an accident of bookkeeping:
all four inverses of the word are carried symbolically, so at a bad parameter both sides are `0`
rather than the statement being false. The hypotheses appear only where a *consumer* cancels
`q·q^{-1}` or `u·u^{-1}`, which is `HJO.Sweep.pairArgTwo_one`,
`HJO.Sweep.sum_bop_zDefect_pairArgTwo_one` and
`HJO.Sweep.constantCoeff_lowerRun_two_stageWordTotal_two_three_of_pair`, each carrying `q ≠ 0`,
`u ≠ 0`, `q ≠ 1` and nothing else. Which letter needs which:

* `q ≠ 0` — the `q^{-a_P̂}` of `HJO.Mellit.sweepOperator`, the `q^{-1}` of
  `HJO.Mellit.replicatedLetter`, and the train `T_1^{-1} = (T_1 + (q-1))/q`;
* `u ≠ 0` and `q ≠ 0` together — the `(qu)^{-1}` of `HJO.Sweep.slopeOperator`, which in a field is
  the **zero map** at `qu = 0`;
* `q ≠ 1` — the `q^2/(1-q)` of `HJO.Sweep.zop`, likewise the zero map at `q = 1`.

At each of those parameters the sweep side genuinely collapses, so a clause asserting otherwise
there is **false, not vacuous**. Not needed anywhere in this file: `M = (1-q)(1-u) ≠ 0`, `u ≠ 1`,
`qu ≠ 1`, `qu + 1 ≠ 0`, positivity of `A` or `B`.

## References

Declarations involved: `HJO.Mellit.lhsRewrite_sweepWitness`,
`HJO.Mellit.isAdmissibleColouring_and_sum_sweepChar_eq_smul_dsc`, `HJO.Mellit.stage`,
`HJO.Mellit.replicatedLetter`, `HJO.Sweep.zop`, `HJO.Sweep.slopeOperator`, `HJO.Sweep.dminus`,
`HJO.Sweep.dminus_dminus_braid`, `HJO.Sym.Bop`, `HJO.Sweep.bopExt`, `HJO.Sweep.dplusStar`,
`HJO.Sweep.piece`. Transcribing A. Mellit, *Toric braids and `(m, n)`-parking functions*, §3.
-/

@[expose] public section

namespace HJO.Sweep

open HJO.Sym HJO.Mellit

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-! ### The monomials of `V_2` -/

omit [Algebra ℚ L] in
/-- Every monomial of an element of `V_2` is `y_1^my_2^n`. -/
theorem exists_pair_of_mem_piece_two {G : Total L} (hG : G ∈ piece L 2) {d : ℕ →₀ ℕ}
    (hd : d ∈ G.support) : ∃ m n : ℕ, d = Finsupp.single 0 m + Finsupp.single 1 n := by
  rw [piece, MvPolynomial.mem_supported] at hG
  refine ⟨d 0, d 1, Finsupp.ext fun j => ?_⟩
  rcases eq_or_ne j 0 with rfl | h0
  · simp
  rcases eq_or_ne j 1 with rfl | h1
  · simp
  have hzero : (Finsupp.single 0 (d 0) + Finsupp.single 1 (d 1) : ℕ →₀ ℕ) j = 0 := by
    simp [Ne.symm h0, Ne.symm h1]
  rw [hzero]
  by_contra h
  have hmem : j ∈ G.vars := MvPolynomial.mem_vars_iff_mem_support j |>.2
    ⟨d, hd, Finsupp.mem_support_iff.2 h⟩
  have := hG hmem
  simp only [Set.mem_Iio] at this
  omega

omit [Algebra ℚ L] in
/-- A `y`-monomial of `V_2` written as `y_1^my_2^n` times a constant. -/
theorem monomial_pair_eq (m n : ℕ) (c : Sym.Lambda L) :
    (MvPolynomial.monomial (Finsupp.single 0 m + Finsupp.single 1 n) c : Total L)
      = (auxVar 1 : Total L) ^ m * (auxVar 2 : Total L) ^ n * MvPolynomial.C c := by
  rw [auxVar, auxVar, Nat.sub_self, show (2 : ℕ) - 1 = 1 from rfl,
    MvPolynomial.X_pow_eq_monomial, MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul,
    one_mul, mul_comm, MvPolynomial.C_mul_monomial, mul_one]

/-! ### `ct ∘ d_-^{(1)}d_-^{(2)}` on a general element of `V_2` -/

/-- **`ct(d_-^{(1)}d_-^{(2)}G) = ∑_{m,n} B_m(B_n(G_{mn}))` for `G = ∑ G_{mn}y_1^my_2^n ∈ V_2`.**

The length-two analogue of `HJO.Sweep.constantCoeff_dminus_one_of_mem_piece`: the double lowering
on a monomial of `V_2` is two Hall--Littlewood operators of `HJO.Sym.Bop` with the `y_1`-exponent
outermost (`HJO.Sweep.constantCoeff_lowerRun_two_C_mul_monomial`, which is
`HJO.Sweep.dminus_dminus_braid`'s monomial computation read through `ct`), and the sum is over
`G.support`, which for an element of `V_2` is a set of pairs of exponents at `y_1, y_2` alone
(`HJO.Sweep.exists_pair_of_mem_piece_two`).

`G ∈ V_2` is not decoration: on a monomial carrying `y_3` the pair `(d 0, d 1)` is not the whole
exponent and `HJO.Sweep.dminus_dminus_auxVar_pow_mul` does not apply.

No hypothesis on `q` or `u`. -/
theorem constantCoeff_lowerRun_two_of_mem_piece (q : L) {G : Total L} (hG : G ∈ piece L 2) :
    MvPolynomial.constantCoeff (Mellit.lowerRun q 2 G)
      = ∑ d ∈ G.support, Sym.Bop q ((d 0 : ℕ) : ℤ)
          (Sym.Bop q ((d 1 : ℕ) : ℤ) (MvPolynomial.coeff d G)) := by
  conv_lhs => rw [G.as_sum]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  obtain ⟨m, n, rfl⟩ := exists_pair_of_mem_piece_two hG hd
  rw [monomial_pair_eq, constantCoeff_lowerRun_two_C_mul_monomial]
  simp

/-- **`ct(d_-^{(1)}d_-^{(2)}(y_1^ay_2^bZ)) = ∑_j B_{j+a}(B_b(Z_j))` for `Z = ∑_j Z_jy_1^j ∈ V_1`.**

The reading tool the two-part evaluation needs: the spectator powers `y_1^a`, `y_2^b` add to the
two indices, the `y_1`-side one picking up the `y_1`-degree of `Z` and the `y_2`-side one not.
Unconditional. -/
theorem constantCoeff_lowerRun_two_auxVar_pow_mul_of_mem_piece_one (q : L) (a b : ℕ)
    {Z : Total L} (hZ : Z ∈ piece L 1) :
    MvPolynomial.constantCoeff (Mellit.lowerRun q 2
        ((auxVar 1 : Total L) ^ a * (auxVar 2 : Total L) ^ b * Z))
      = ∑ e ∈ Z.support, Sym.Bop q (((e 0 + a : ℕ) : ℤ))
          (Sym.Bop q ((b : ℕ) : ℤ) (MvPolynomial.coeff e Z)) := by
  conv_lhs => rw [Z.as_sum]
  rw [Finset.mul_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  obtain ⟨j, rfl⟩ := exists_single_zero_of_mem_piece_one hZ he
  have hsingle : (MvPolynomial.monomial (Finsupp.single 0 j)
        (MvPolynomial.coeff (Finsupp.single 0 j) Z) : Total L)
      = (auxVar 1 : Total L) ^ j
        * MvPolynomial.C (MvPolynomial.coeff (Finsupp.single 0 j) Z) := by
    rw [auxVar, Nat.sub_self, MvPolynomial.X_pow_eq_monomial, mul_comm,
      MvPolynomial.C_mul_monomial, mul_one]
  have hmon : (auxVar 1 : Total L) ^ a * (auxVar 2 : Total L) ^ b
        * MvPolynomial.monomial (Finsupp.single 0 j) (MvPolynomial.coeff (Finsupp.single 0 j) Z)
      = (auxVar 1 : Total L) ^ (j + a) * (auxVar 2 : Total L) ^ b
        * MvPolynomial.C (MvPolynomial.coeff (Finsupp.single 0 j) Z) := by
    rw [hsingle, pow_add]
    ring
  rw [hmon, constantCoeff_lowerRun_two_C_mul_monomial, Finsupp.single_eq_same]

/-! ### `z_1`'s commutator on a general element of `V_2` -/

/-- **The commutator half of `z_1^{(2)}` on the whole of `V_2`.** The level-two analogue of
`HJO.Sweep.zopOneStar_one_of_mem_piece`: each `y_1^my_2^n`-monomial of `G` contributes the
grading-one defect `HJO.Sweep.zDefect` at the `y_2`-exponent `n`, with the `y_1`-exponent `m`
riding through as a spectator power of `y_2` — `HJO.Sweep.zCommTwo_monomial'` — and the sum is over
`G.support`, an element of `V_2` having only `y_1, y_2`-monomials.

So `z_1` at the grading `2` reads exactly the same element of `V_1` as `z_1` at the grading `1`
does, at every input rather than at a monomial. No hypothesis on `q` or `u`. -/
theorem zCommTwo_of_mem_piece (q u : L) {G : Total L} (hG : G ∈ piece L 2) :
    zCommTwo q u G
      = ∑ d ∈ G.support, (auxVar 2 : Total L) ^ (d 0)
          * zDefect q u (d 1) (MvPolynomial.coeff d G) := by
  conv_lhs => rw [G.as_sum]
  rw [map_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  obtain ⟨m, n, rfl⟩ := exists_pair_of_mem_piece_two hG hd
  rw [show (MvPolynomial.monomial (Finsupp.single 0 m + Finsupp.single 1 n)
        (MvPolynomial.coeff (Finsupp.single 0 m + Finsupp.single 1 n) G) : Total L)
      = MvPolynomial.C (MvPolynomial.coeff (Finsupp.single 0 m + Finsupp.single 1 n) G)
        * ((auxVar 1 : Total L) ^ m * (auxVar 2 : Total L) ^ n) from by
      rw [monomial_pair_eq]; ring,
    zCommTwo_monomial']
  simp

/-- **The defect lives in `V_1`.** Both halves do: `d^*_+{}^{(0)}` carries a constant into `V_1`
(`HJO.Sweep.dplusStar_zero_C_mem_piece_one`) and `HJO.Sweep.bopExt` preserves the grading. -/
theorem zDefect_mem_piece_one (q u : L) (n : ℕ) (A : Sym.Lambda L) :
    zDefect q u n A ∈ piece L 1 :=
  sub_mem (dplusStar_zero_C_mem_piece_one q u _)
    (bopExt_mem_piece q _ (dplusStar_zero_C_mem_piece_one q u A))

/-- **`z_1`'s commutator preserves `V_2`.** Read off `HJO.Sweep.zCommTwo_of_mem_piece`: every term
is a power of `y_2` times an element of `V_1`. This is the closure fact that lets the evaluation be
applied to the output of a previous step. -/
theorem zCommTwo_mem_piece_two (q u : L) {G : Total L} (hG : G ∈ piece L 2) :
    zCommTwo q u G ∈ piece L 2 := by
  rw [zCommTwo_of_mem_piece q u hG]
  refine sum_mem fun d _ => mul_mem (pow_mem (auxVar_mem_piece (by omega) le_rfl) _) ?_
  exact piece_mono (by omega) (zDefect_mem_piece_one q u _ _)

end HJO.Sweep

namespace HJO.Mellit

open HJO.Sym HJO.Sweep

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-! ### The two-part stage word and its recursion -/

/-- **`G_{2,B}G_{1,A}(1)` is the stage word at `[A,B]`.** One step of
`HJO.Mellit.stageWordTotal_append`; unconditional, at every `(a,b)` and every `A, B`. -/
theorem stageWordTotal_pair (q u : L) (a b A B : ℕ) :
    stageWordTotal q u a b [A, B]
      = stageTotal q u a b 1 B (stageWordTotal q u a b [A]) := by
  have h := stageWordTotal_append q u a b [A] B
  rwa [show ([A] ++ [B] : List ℕ) = [A, B] from rfl, List.length_cons, List.length_nil,
    Nat.zero_add] at h

/-- **`G_{2,B+2}G_{1,A}(1) = Z^{(2)}_{a,b}(G_{2,B+1}G_{1,A}(1))`**: the recursion in the **second**
part, the level-two analogue of `HJO.Mellit.stageWordTotal_singleton_succ`. The two-part stage word
at `[A,B+2]` is one replicated letter of `HJO.Mellit.replicatedLetter`, read at the grading `1`, on
the two-part stage word at `[A,B+1]`.

The offset is necessary and not cosmetic, for the same reason as in the one-part family: the power
in `HJO.Mellit.stage` is `B - 1` with the truncated subtraction, so the step from `[A,0]` to `[A,1]`
applies no letter at all.

Unconditional, at every `(a,b)` and every `A, B`. -/
theorem stageWordTotal_pair_succ (q u : L) (a b A B : ℕ) :
    stageWordTotal q u a b [A, B + 2]
      = replicatedTotal q u a b 1 (stageWordTotal q u a b [A, B + 1]) := by
  rw [stageWordTotal_pair, stageWordTotal_pair, stageTotal, stageTotal,
    show B + 2 - 1 = (B + 1 - 1) + 1 from by omega, pow_succ']
  rfl

/-- **The whole two-part family lives in `V_2`.** `HJO.Mellit.stageTotal_mem_piece` raises the
grading by exactly one and `HJO.Mellit.stageWordTotal_singleton_mem_piece` puts the one-part family
in `V_1`. Unconditional. -/
theorem stageWordTotal_pair_mem_piece (q u : L) (a b A B : ℕ) :
    stageWordTotal q u a b [A, B] ∈ piece L 2 := by
  rw [stageWordTotal_pair]
  exact stageTotal_mem_piece q u a b 1 B (stageWordTotal_singleton_mem_piece q u a b A)

end HJO.Mellit

namespace HJO.Sweep

open HJO.Sym HJO.Mellit

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-! ### The vector the level-two slope operator is read on -/

/-- **The argument of the second-stage slope operator at a one-part composition**,
`T_1^{-1}(y_1^2d^*_+{}^{(1)}G_{1,A}(1))`.

This is `HJO.Sweep.seedArgTwo`'s role at a general part: the composite
`HJO.Mellit.lowerRun q 2 ∘ G_{2,1}` on `V_1` reads `Ξ^{(2)}_{2,3}` on `-y_1d^*_+{}^{(1)}G`
(`HJO.Sweep.lowerRun_two_stageTotal_one_of_slope`), and `HJO.Sweep.slopeOperator_two_three_apply`
multiplies by `-y_1` again and applies the train `T_1^{-1}` before the single `z` letter — so this
is exactly the element of `V_2` that `z_1^{(2)}` meets.

Unconditional: the `q^{-1}` of the train is carried symbolically inside `HJO.Sweep.braidInvEnd`. -/
noncomputable def pairArgTwo (q u : L) (A : ℕ) : Total L :=
  braidInvEnd q 1
    ((auxVar 1 : Total L) ^ 2 * dplusStar q u 1 (Mellit.stageWordTotal q u 2 3 [A]))

theorem pairArgTwo_mem_piece (q u : L) (A : ℕ) : pairArgTwo q u A ∈ piece L 2 := by
  have h : ((auxVar 1 : Total L) ^ 2
      * dplusStar q u 1 (Mellit.stageWordTotal q u 2 3 [A])) ∈ piece L 2 :=
    mul_mem (pow_mem (auxVar_mem_piece le_rfl (by omega)) 2)
      (dplusStar_mem_piece q u (Mellit.stageWordTotal_singleton_mem_piece q u 2 3 A))
  exact braidInv_mem_piece q (by omega) h

/-- **`HJO.Sweep.pairArgTwo q u 1` is the earlier `T_1^{-1}(-y_1·seedArgTwo)`.** The general
argument at `A = 1` is the one the decided `(1,1)` computation uses:
`HJO.Sweep.neg_auxVar_one_mul_dplusStar_one_stageTotal` says
`-y_1d^*_+{}^{(1)}(G_{1,1}(1)) = seedArgTwo`, so `y_1^2d^*_+{}^{(1)}(G_{1,1}(1)) = -y_1·seedArgTwo`.

Genericity: `q ≠ 0`, `u ≠ 0`, `q ≠ 1`, all three the seed's own
(`HJO.Sweep.stageTotal_two_three_zero_one_one`), each an inverse that becomes the zero map. -/
theorem pairArgTwo_one (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    pairArgTwo q u 1 = braidInvEnd q 1 (-((auxVar 1 : Total L) * seedArgTwo q u)) := by
  have h := neg_auxVar_one_mul_dplusStar_one_stageTotal (L := L) hq0 hu0 hq1
  rw [pairArgTwo, Mellit.stageWordTotal_singleton,
    show (auxVar 1 : Total L) ^ 2 * dplusStar q u 1 (Mellit.stageTotal q u 2 3 0 1 (1 : Total L))
      = -((auxVar 1 : Total L)
          * -((auxVar 1 : Total L) * dplusStar q u 1
              (Mellit.stageTotal q u 2 3 0 1 (1 : Total L)))) from by ring,
    h]

/-! ### The second stage on a general element of `V_1`, with the braid letter gone -/

/-- **`d_-^2G_{2,1}(G) = (qu)^{-1}\frac{q^2}{1-q}·d_-^2(y_1·zCommTwo(T_1^{-1}(y_1^2d^*_+G)))`
at every `G ∈ V_1`.**

`HJO.Sweep.lowerRun_two_stageTotal_one_of_slope` kills the descending train `T_{2↘1}` against the
double lowering (`HJO.Sweep.dminus_dminus_braid`) and leaves `Ξ^{(2)}_{2,3}` on
`-y_1d^*_+{}^{(1)}G`; `HJO.Sweep.slopeOperator_two_three_apply` unfolds that assembly, and the two
minus signs of `-y_1·(-y_1d^*_+{}^{(1)}G)` and of `(-1)^{a-1}` at `a = 2` cancel against each other,
so **no sign survives**.

Unconditional: `(qu)^{-1}` and `q^2/(1-q)` are carried symbolically, so at `qu = 0` or `q = 1` this
reads `0 = 0` rather than being false. The hypotheses enter only where a consumer cancels them. -/
theorem lowerRun_two_stageTotal_two_three_one_of_mem_piece (q u : L) {G : Total L}
    (hG : G ∈ piece L 1) :
    Mellit.lowerRun q 2 (Mellit.stageTotal q u 2 3 1 1 G)
      = ((q * u)⁻¹ * (q ^ 2 / (1 - q))) • Mellit.lowerRun q 2 ((auxVar 1 : Total L)
          * zCommTwo q u (braidInvEnd q 1
              ((auxVar 1 : Total L) ^ 2 * dplusStar q u 1 G))) := by
  have harg : -((auxVar 1 : Total L) * -((auxVar 1 : Total L) * dplusStar q u 1 G))
      = (auxVar 1 : Total L) ^ 2 * dplusStar q u 1 G := by ring
  rw [lowerRun_two_stageTotal_one_of_slope q u 2 3 hG, slopeOperator_two_three_apply, harg,
    show ((-1 : L) ^ (2 - 1)) = -1 from by norm_num, map_neg, map_smul, smul_neg, neg_smul,
    one_smul, neg_neg]

/-! ### The evaluation engine: `ct ∘ d_-^{(1)}d_-^{(2)} ∘ y_1 ∘ zCommTwo` on all of `V_2` -/

/-- **`ct(d_-^{(1)}d_-^{(2)}(y_1·zCommTwo(H))) = ∑_{m,n}∑_j B_{j+1}(B_m(zDefect_n(H_{mn})_j))` for
every `H ∈ V_2`.**

This is the whole tail of the two-part clause, evaluated once and for all: the outer sum is over the
`y_1^my_2^n`-monomials of `H` with coefficients `H_{mn}`, the inner over the `y_1`-expansion of the
grading-one defect `HJO.Sweep.zDefect q u n H_{mn}`, and the two indices `j+1` and `m` are the
`y_1`- and `y_2`-exponents the double lowering reads.

Three earlier facts and nothing else: `HJO.Sweep.zCommTwo_of_mem_piece` turns the single `z` letter
at the grading `2` into a sum of spectator powers of `y_2` times the grading-one defect,
`HJO.Sweep.zDefect_mem_piece_one` puts each defect in `V_1`, and
`HJO.Sweep.constantCoeff_lowerRun_two_auxVar_pow_mul_of_mem_piece_one` reads the double lowering
against `HJO.Sym.Bop`. The `+1` in the outer index is the single spectator `y_1` in front.

Unconditional, and `H ∈ V_2` is the only hypothesis. -/
theorem constantCoeff_lowerRun_two_auxVar_one_mul_zCommTwo_of_mem_piece (q u : L) {H : Total L}
    (hH : H ∈ piece L 2) :
    MvPolynomial.constantCoeff (Mellit.lowerRun q 2 ((auxVar 1 : Total L) * zCommTwo q u H))
      = ∑ d ∈ H.support,
          ∑ e ∈ (zDefect q u (d 1) (MvPolynomial.coeff d H)).support,
            Sym.Bop q (((e 0 + 1 : ℕ) : ℤ))
              (Sym.Bop q ((d 0 : ℕ) : ℤ)
                (MvPolynomial.coeff e (zDefect q u (d 1) (MvPolynomial.coeff d H)))) := by
  rw [zCommTwo_of_mem_piece q u hH, Finset.mul_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [show (auxVar 1 : Total L)
        * ((auxVar 2 : Total L) ^ (d 0) * zDefect q u (d 1) (MvPolynomial.coeff d H))
      = (auxVar 1 : Total L) ^ 1 * (auxVar 2 : Total L) ^ (d 0)
        * zDefect q u (d 1) (MvPolynomial.coeff d H) from by ring,
    constantCoeff_lowerRun_two_auxVar_pow_mul_of_mem_piece_one q 1 (d 0)
      (zDefect_mem_piece_one q u (d 1) _)]

/-- **CROSS-CHECK of the support-sum machinery against the monomial computation.**

At `H = HJO.Sweep.pairArgTwo q u 1` the engine
`HJO.Sweep.constantCoeff_lowerRun_two_auxVar_one_mul_zCommTwo_of_mem_piece` is evaluated by
`HJO.Sweep.constantCoeff_lowerRun_two_auxVar_one_mul_zCommTwo_seedArgTwo`, whose five
compositions of Hall--Littlewood operators come from a *different* route: there the two
monomials of `T_1^{-1}(-y_1·seedArgTwo)` are pushed through `HJO.Sweep.zCommTwo_monomial'` and the
five named `HJO.Sweep.zDefect` values one at a time, and no support sum occurs anywhere.

So this is not a restatement: it is the check that
`HJO.Sweep.zCommTwo_of_mem_piece`,
`HJO.Sweep.constantCoeff_lowerRun_two_auxVar_pow_mul_of_mem_piece_one` and
`HJO.Sweep.zDefect_mem_piece_one` — the three tools the general `[A,1]` evaluation runs on — return
the *same* element of `Λ` as the monomial computation, indices, shifts and widths included. An
off-by-one in the `j+1`, or the two `B`-indices swapped, would leave it unprovable.

Genericity: `q ≠ 0`, `u ≠ 0`, `q ≠ 1`, which is `HJO.Sweep.pairArgTwo_one`'s (the seed's). -/
theorem sum_bop_zDefect_pairArgTwo_one (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    ∑ d ∈ (pairArgTwo q u 1 : Total L).support,
        ∑ e ∈ (zDefect q u (d 1) (MvPolynomial.coeff d (pairArgTwo q u 1))).support,
          Sym.Bop q (((e 0 + 1 : ℕ) : ℤ))
            (Sym.Bop q ((d 0 : ℕ) : ℤ)
              (MvPolynomial.coeff e (zDefect q u (d 1)
                (MvPolynomial.coeff d (pairArgTwo q u 1)))))
      = (-((q - 1) * u)) •
          (Bop q ((2 : ℕ) : ℤ) (Bop q ((2 : ℕ) : ℤ) (elemSymm L 1 * elemSymm L 1))
            + (q - 1) • Bop q ((2 : ℕ) : ℤ) (Bop q ((2 : ℕ) : ℤ) (elemSymm L 2))
            - u • Bop q ((3 : ℕ) : ℤ) (Bop q ((2 : ℕ) : ℤ) (elemSymm L 1))
            - u • Bop q ((2 : ℕ) : ℤ) (Bop q ((3 : ℕ) : ℤ) (elemSymm L 1))
            + u ^ 2 • Bop q ((3 : ℕ) : ℤ) (Bop q ((3 : ℕ) : ℤ) (1 : Lambda L))) := by
  rw [← constantCoeff_lowerRun_two_auxVar_one_mul_zCommTwo_of_mem_piece q u
      (pairArgTwo_mem_piece q u 1),
    pairArgTwo_one hq0 hu0 hq1,
    constantCoeff_lowerRun_two_auxVar_one_mul_zCommTwo_seedArgTwo hq0]

/-! ### The sweep side at `[A,1]`, at every part `A` -/

/-- **`ct(d_-^{(1)}d_-^{(2)}(G_{2,1}G_{1,A}(1)))` at EVERY `A`, with every sweep operator gone.**

The two-part `hlhs` clause's sweep side at the composition `[A,1]` and `(a,b) = (2,3)`:

`ct(d_-^2G_{2,1}G_{1,A}(1))
  = (qu)^{-1}\frac{q^2}{1-q}·∑_{(m,n)}∑_j B_{j+1}(B_m(zDefect_n(P_{mn})_j))`,

the outer sum over the `y_1^my_2^n`-monomials of `HJO.Sweep.pairArgTwo q u A` with coefficients
`P_{mn}`, and the inner over the `y_1`-expansion of the grading-one defect
`HJO.Sweep.zDefect q u n P_{mn}` — `B_·` being `HJO.Sym.Bop` on `Λ` and `zDefect` the failure of
`B_n` to commute with the one-letter displacement `d^*_+{}^{(0)}`.

**Nothing on the right is a sweep operator.** No train, no braid representation, no replication
family, no stage, no slope operator, no `z`; the only operators left are `HJO.Sym.Bop` on `Λ` and,
inside `HJO.Sweep.zDefect`, `d^*_+{}^{(0)}` and `HJO.Sweep.bopExt`. Those are exactly the residual
operators of the one-part evaluation
`HJO.Mellit.lhsAt_two_three_singleton_iff_bop`, so this is the same *kind* of answer, one part
further along. `HJO.Sweep.pairArgTwo` still carries `T_1^{-1}` and `d^*_+{}^{(1)}`, both explicit.

The three ingredients: `HJO.Mellit.stageWordTotal_pair` peels the second stage,
`HJO.Sweep.lowerRun_two_stageTotal_two_three_one_of_mem_piece` discharges the stage and the slope
operator, `HJO.Sweep.zCommTwo_of_mem_piece` evaluates the single `z` letter at the grading `2`, and
`HJO.Sweep.constantCoeff_lowerRun_two_auxVar_pow_mul_of_mem_piece_one` reads the double lowering.

**Unconditional — no hypothesis on `q`, `u` or `A`, and in particular `A` need not be positive.**
Every inverse is carried symbolically: at `qu = 0` the letter `(qu)^{-1}z_1` of
`HJO.Sweep.slopeOperator` is the zero map, at `q = 1` the scalar `q^2/(1-q)` of `HJO.Sweep.zop` is
`0`, and at `q = 0` the train's `q^{-1}` collapses — at each of those the two sides are both `0`
rather than the statement being false. A consumer that cancels `q·q^{-1}` or `u·u^{-1}` pays
`q ≠ 0`, `u ≠ 0`, `q ≠ 1` there, as
`HJO.Sweep.constantCoeff_lowerRun_two_stageWordTotal_two_three_of_pair` does. -/
theorem constantCoeff_lowerRun_two_stageWordTotal_pair_one (q u : L) (A : ℕ) :
    MvPolynomial.constantCoeff (Mellit.lowerRun q 2 (Mellit.stageWordTotal q u 2 3 [A, 1]))
      = ((q * u)⁻¹ * (q ^ 2 / (1 - q))) •
          ∑ d ∈ (pairArgTwo q u A).support,
            ∑ e ∈ (zDefect q u (d 1) (MvPolynomial.coeff d (pairArgTwo q u A))).support,
              Sym.Bop q (((e 0 + 1 : ℕ) : ℤ))
                (Sym.Bop q ((d 0 : ℕ) : ℤ)
                  (MvPolynomial.coeff e (zDefect q u (d 1)
                    (MvPolynomial.coeff d (pairArgTwo q u A))))) := by
  rw [Mellit.stageWordTotal_pair, lowerRun_two_stageTotal_two_three_one_of_mem_piece q u
      (Mellit.stageWordTotal_singleton_mem_piece q u 2 3 A),
    constantCoeff_smul, ← pairArgTwo,
    constantCoeff_lowerRun_two_auxVar_one_mul_zCommTwo_of_mem_piece q u
      (pairArgTwo_mem_piece q u A)]

/-! ### The consistency check: the decided `(1,1)` value, re-derived through the general formula -/

/-- **THE CONSISTENCY CHECK: the decided `(1,1)` value, re-derived *through* the general `[A,1]`
formula.**

Word for word
`HJO.Sweep.constantCoeff_lowerRun_two_stageWordTotal_two_three`, but reached by running
`HJO.Sweep.lowerRun_two_stageTotal_two_three_one_of_mem_piece` — the general-`A` reduction — at
`A = 1` and then citing the five-composition evaluation
`HJO.Sweep.constantCoeff_lowerRun_two_auxVar_one_mul_zCommTwo_seedArgTwo`. That the two statements
are literally the same `Prop` is checked by
`HJO.Sweep.constantCoeff_lowerRun_two_stageWordTotal_two_three_of_pair_eq` below, which typechecks
only if they are.

This is where a sign, an index, a shift or a width error in the general reduction would show: the
scalar it produces is `(qu)^{-1}\frac{q^2}{1-q}` with no `(-1)`, and it has to meet that
value's `-((q-1)u)` to give exactly `q`. It does.

Genericity: `q ≠ 0`, `u ≠ 0`, `q ≠ 1`, verbatim those of
`HJO.Sweep.constantCoeff_lowerRun_two_stageWordTotal_two_three`. -/
theorem constantCoeff_lowerRun_two_stageWordTotal_two_three_of_pair (hq0 : q ≠ 0) (hu0 : u ≠ 0)
    (hq1 : q ≠ 1) :
    MvPolynomial.constantCoeff (Mellit.lowerRun q 2 (Mellit.stageWordTotal q u 2 3 [1, 1]))
      = q • (Bop q ((2 : ℕ) : ℤ) (Bop q ((2 : ℕ) : ℤ) (elemSymm L 1 * elemSymm L 1))
          + (q - 1) • Bop q ((2 : ℕ) : ℤ) (Bop q ((2 : ℕ) : ℤ) (elemSymm L 2))
          - u • Bop q ((3 : ℕ) : ℤ) (Bop q ((2 : ℕ) : ℤ) (elemSymm L 1))
          - u • Bop q ((2 : ℕ) : ℤ) (Bop q ((3 : ℕ) : ℤ) (elemSymm L 1))
          + u ^ 2 • Bop q ((3 : ℕ) : ℤ) (Bop q ((3 : ℕ) : ℤ) (1 : Lambda L))) := by
  have h1q : (1 : L) - q ≠ 0 := sub_ne_zero.2 (Ne.symm hq1)
  have hs : ((q * u)⁻¹ * (q ^ 2 / (1 - q))) * -((q - 1) * u) = q := by field_simp; ring
  rw [Mellit.stageWordTotal_pair, lowerRun_two_stageTotal_two_three_one_of_mem_piece q u
      (Mellit.stageWordTotal_singleton_mem_piece q u 2 3 1),
    constantCoeff_smul, ← pairArgTwo, pairArgTwo_one hq0 hu0 hq1,
    constantCoeff_lowerRun_two_auxVar_one_mul_zCommTwo_seedArgTwo hq0, smul_smul, hs]

/-- **The two routes to the `(1,1)` sweep value are the same `Prop`.** `rfl` can typecheck here only
if the statement of `HJO.Sweep.constantCoeff_lowerRun_two_stageWordTotal_two_three_of_pair` — proved
through the general `[A,1]` reduction — is *identical* to that of
`HJO.Sweep.constantCoeff_lowerRun_two_stageWordTotal_two_three`, hypotheses and all. Stronger than
comparing the printed coefficients by eye. -/
theorem constantCoeff_lowerRun_two_stageWordTotal_two_three_of_pair_eq (hq0 : q ≠ 0) (hu0 : u ≠ 0)
    (hq1 : q ≠ 1) :
    constantCoeff_lowerRun_two_stageWordTotal_two_three_of_pair (L := L) hq0 hu0 hq1
      = constantCoeff_lowerRun_two_stageWordTotal_two_three (L := L) hq0 hu0 hq1 :=
  rfl

/-! ### The step in the second part: `Z^{(2)}_{2,3}` with both `z` letters evaluated -/

omit [Algebra ℚ L] in
/-- `T_i^{-1}` preserves `V_k` for `i < k`, `HJO.Sweep.braidInv_mem_piece` at the `L`-linear
spelling. -/
theorem braidInvEnd_mem_piece (q : L) {i k : ℕ} (hik : i < k) {F : Total L}
    (hF : F ∈ piece L k) : braidInvEnd q i F ∈ piece L k :=
  braidInv_mem_piece q hik hF

omit [Algebra ℚ L] in
/-- `T_i` preserves `V_k` for `1 ≤ i < k`, `HJO.Sweep.braid_mem_piece` at the `L`-linear
spelling. -/
theorem braidEnd_mem_piece (q : L) {i k : ℕ} (h1 : 1 ≤ i) (hik : i < k) {F : Total L}
    (hF : F ∈ piece L k) : braidEnd q i F ∈ piece L k :=
  braid_mem_piece q h1 hik hF

/-- **`z_1^{(2)}` on the whole of `V_2`, with every operator of the sweep gone.**

The level-two analogue of `HJO.Sweep.zopOneStar_one_of_mem_piece`: `HJO.Sweep.zop` at `k = 2` is
`q^2/(1-q)` times the commutator after the single train letter `T_1^{-1}`
(`HJO.Sweep.zopOneStar_two_eq`), and `HJO.Sweep.zCommTwo_of_mem_piece` evaluates the commutator on
each `y_1^my_2^n`-monomial of `T_1^{-1}G` as `y_2^m` times the grading-one defect
`HJO.Sweep.zDefect` at `n`.

`G ∈ V_2` is what makes the support a set of `(y_1, y_2)`-exponent pairs; the membership travels
through the train by `HJO.Sweep.braidInvEnd_mem_piece`.

No hypothesis on `q` or `u`: both `q^2/(1-q)` and the `q^{-1}` of the train are symbolic, so at
`q = 1` or `q = 0` this reads `0 = 0`. -/
theorem zopOneStar_two_of_mem_piece (q u : L) {G : Total L} (hG : G ∈ piece L 2) :
    zopOneStar q u 2 G
      = (q ^ 2 / (1 - q)) • ∑ d ∈ (braidInvEnd q 1 G).support,
          (auxVar 2 : Total L) ^ (d 0)
            * zDefect q u (d 1) (MvPolynomial.coeff d (braidInvEnd q 1 G)) := by
  rw [zopOneStar_two_eq]
  simp only [LinearMap.smul_apply, Module.End.mul_apply]
  rw [zCommTwo_of_mem_piece q u (braidInvEnd_mem_piece q (by omega) hG)]

/-- **`Z^{(2)}_{2,3}` on a vector, as one word in `T_1`, `T_1^{-1}`, `y_1` and the two `z`
letters.**

`HJO.Mellit.replicatedLetter` at the grading `1` is `q^{-1}T_{2↘1}Ω(2;2,3)T_{1↗2}`, and both trains
are the single braid letter `T_1` (`HJO.Sweep.trainDownEnd_two_one`,
`HJO.Sweep.trainUpEnd_one_two`); `HJO.Mellit.replTwoTotal` at `a = 2` is
`-Ξ^{(2)}_{2,3}(-y_1z_1^{(2)})`, and `HJO.Sweep.slopeOperator_two_three_apply` reads `Ξ^{(2)}_{2,3}`
as `-(qu)^{-1}\frac{q^2}{1-q}y_1·zCommTwo·T_1^{-1}·(-y_1)`.

**All four signs cancel** — the `(-1)^{a-1}` at `a = 2`, the `-y_1z_1` of `HJO.Mellit.replTwoTotal`,
and the two of the slope assembly — so no sign survives; this is the level-one fact
`HJO.Sweep.replicatedTotal_two_three_zero_eq`'s three-sign cancellation, one grading up and with the
two trains no longer empty.

Unconditional. -/
private theorem slope_two_three_auxVar_mul (q u : L) (Z : Total L) :
    slopeOperator q u 2 2 3 ((auxVar 1 : Total L) * Z)
      = ((q * u)⁻¹ * (q ^ 2 / (1 - q))) • ((auxVar 1 : Total L)
          * zCommTwo q u (braidInvEnd q 1 ((auxVar 1 : Total L) ^ 2 * Z))) := by
  rw [slopeOperator_two_three_apply,
    show -((auxVar 1 : Total L) * ((auxVar 1 : Total L) * Z))
      = -((auxVar 1 : Total L) ^ 2 * Z) from by ring,
    map_neg, map_neg, mul_neg, smul_neg, neg_neg]

theorem replicatedTotal_two_three_one_apply (q u : L) (F : Total L) :
    Mellit.replicatedTotal q u 2 3 1 F
      = (q⁻¹ * ((q * u)⁻¹ * (q ^ 2 / (1 - q)))) •
          braidEnd q 1 ((auxVar 1 : Total L) * zCommTwo q u (braidInvEnd q 1
            ((auxVar 1 : Total L) ^ 2 * zopOneStar q u 2 (braidEnd q 1 F)))) := by
  rw [Mellit.replicatedTotal, show (1 : ℕ) + 1 = 2 from rfl, trainDownEnd_two_one,
    trainUpEnd_one_two]
  simp only [LinearMap.smul_apply, Module.End.mul_apply, Mellit.replTwoTotal,
    LinearMap.neg_apply, LinearMap.mulLeft_apply, show (2 - 1 : ℕ) = 1 from rfl, pow_one,
    map_neg, neg_neg, neg_smul, one_smul, show (1 : ℕ) + 1 = 2 from rfl,
    slope_two_three_auxVar_mul, map_smul, smul_smul, Nat.cast_one, zpow_neg, zpow_one]

/-- **The outer braid letter of the step is invisible to the clause.** For `F ∈ V_2`,

`ct(d_-^{(1)}d_-^{(2)}(Z^{(2)}_{2,3}F))
  = q^{-1}(qu)^{-1}\frac{q^2}{1-q}·ct(d_-^2(y_1·zCommTwo(T_1^{-1}(y_1^2z_1^{(2)}(T_1F)))))`,

the leading `T_1` of `HJO.Mellit.replicatedTotal_two_three_one_apply` having been killed by
`HJO.Sweep.dminus_dminus_braid` exactly as the stage's descending train
is in `HJO.Sweep.lowerRun_two_stageTotal_one_of_slope`. The *inner* `T_1` and the `T_1^{-1}` are not
killed and remain.

This is the sharpening the `B ≥ 2` recursion needs: with
`HJO.Mellit.stageWordTotal_pair_succ` it removes one of the three braid letters at every step of the
second part. Unconditional. -/
theorem constantCoeff_lowerRun_two_replicatedTotal_two_three_one_of_mem_piece (q u : L)
    {F : Total L} (hF : F ∈ piece L 2) :
    MvPolynomial.constantCoeff (Mellit.lowerRun q 2 (Mellit.replicatedTotal q u 2 3 1 F))
      = (q⁻¹ * ((q * u)⁻¹ * (q ^ 2 / (1 - q)))) •
          MvPolynomial.constantCoeff (Mellit.lowerRun q 2 ((auxVar 1 : Total L)
            * zCommTwo q u (braidInvEnd q 1
                ((auxVar 1 : Total L) ^ 2 * zopOneStar q u 2 (braidEnd q 1 F))))) := by
  have hinner : ((auxVar 1 : Total L) ^ 2 * zopOneStar q u 2 (braidEnd q 1 F)) ∈ piece L 2 :=
    mul_mem (pow_mem (auxVar_mem_piece le_rfl (by omega)) 2)
      (zopOneStar_mem_piece q u (by omega) (braidEnd_mem_piece q le_rfl (by omega) hF))
  have hmem : ((auxVar 1 : Total L) * zCommTwo q u (braidInvEnd q 1
      ((auxVar 1 : Total L) ^ 2 * zopOneStar q u 2 (braidEnd q 1 F)))) ∈ piece L 2 :=
    mul_mem (auxVar_mem_piece le_rfl (by omega))
      (zCommTwo_mem_piece_two q u (braidInvEnd_mem_piece q (by omega) hinner))
  rw [replicatedTotal_two_three_one_apply, map_smul, constantCoeff_smul, lowerRun_two_apply,
    show braidEnd q 1 ((auxVar 1 : Total L) * zCommTwo q u (braidInvEnd q 1
        ((auxVar 1 : Total L) ^ 2 * zopOneStar q u 2 (braidEnd q 1 F))))
      = braid q 1 ((auxVar 1 : Total L) * zCommTwo q u (braidInvEnd q 1
        ((auxVar 1 : Total L) ^ 2 * zopOneStar q u 2 (braidEnd q 1 F)))) from rfl,
    dminus_dminus_braid q 0 hmem, ← lowerRun_two_apply]

/-! ### The sweep side at every two-part composition -/

/-- **`ct(d_-^{(1)}d_-^{(2)}(G_{2,B}G_{1,A}(1))) = ∑_{m,n}B_m(B_n(P_{mn}))` at EVERY `(A,B)`**, with
`P_{mn}` the `y_1^my_2^n`-coefficients of the two-part stage word.

The whole `ℓ = 2` run of lowering operators of
`HJO.Mellit.isAdmissibleColouring_and_sum_sweepChar_eq_smul_dsc` is discharged into finitely many
compositions of two Hall--Littlewood operators of `HJO.Sym.Bop` on `Λ`, the `y_1`-exponent read
outermost: `HJO.Mellit.stageWordTotal_pair_mem_piece` puts the family in `V_2` and
`HJO.Sweep.constantCoeff_lowerRun_two_of_mem_piece` reads it.

**Unconditional, at every `A` and every `B`, and the parts need not be positive.** Nothing here is
an equivalence and nothing is assumed: this is the value.

What it does *not* do is expand the stage word — that is the recursion
`HJO.Mellit.stageWordTotal_pair_succ` with the step
`HJO.Sweep.replicatedTotal_two_three_one_apply`, whose two `z` letters are evaluated by
`HJO.Sweep.zopOneStar_two_of_mem_piece` and `HJO.Sweep.zCommTwo_of_mem_piece`. So this is a decision
procedure for each fixed `(A,B)`, and at `B = 1` it is closed in `A` by
`HJO.Sweep.constantCoeff_lowerRun_two_stageWordTotal_pair_one`. -/
theorem constantCoeff_lowerRun_two_stageWordTotal_pair (q u : L) (A B : ℕ) :
    MvPolynomial.constantCoeff (Mellit.lowerRun q 2 (Mellit.stageWordTotal q u 2 3 [A, B]))
      = ∑ d ∈ (Mellit.stageWordTotal q u 2 3 [A, B] : Total L).support,
          Sym.Bop q ((d 0 : ℕ) : ℤ) (Sym.Bop q ((d 1 : ℕ) : ℤ)
            (MvPolynomial.coeff d (Mellit.stageWordTotal q u 2 3 [A, B] : Total L))) :=
  constantCoeff_lowerRun_two_of_mem_piece q (Mellit.stageWordTotal_pair_mem_piece q u 2 3 A B)

/-! ### The recursion in the second part, evaluated -/

/-- **The vector `z_1^{(2)}` is read on at the step from `[A,B+1]` to `[A,B+2]`**,
`T_1^{-1}(y_1^2z_1^{(2)}(T_1(G_{2,B+1}G_{1,A}(1))))`.

The analogue of `HJO.Sweep.pairArgTwo` for the *step* rather than the base: the same position in the
word, with the stage's `d^*_+{}^{(1)}` replaced by the replicated letter's inner
`T_1` followed by `z_1^{(2)}`. Unconditional. -/
noncomputable def pairArgSucc (q u : L) (A B : ℕ) : Total L :=
  braidInvEnd q 1 ((auxVar 1 : Total L) ^ 2 *
    zopOneStar q u 2 (braidEnd q 1 (Mellit.stageWordTotal q u 2 3 [A, B + 1])))

theorem pairArgSucc_mem_piece (q u : L) (A B : ℕ) : pairArgSucc q u A B ∈ piece L 2 :=
  braidInvEnd_mem_piece q (by omega)
    (mul_mem (pow_mem (auxVar_mem_piece le_rfl (by omega)) 2)
      (zopOneStar_mem_piece q u (by omega) (braidEnd_mem_piece q le_rfl (by omega)
        (Mellit.stageWordTotal_pair_mem_piece q u 2 3 A (B + 1)))))

/-- **THE RECURSION IN THE SECOND PART, EVALUATED — at every `A` and every `B`.**

`ct(d_-^2(G_{2,B+2}G_{1,A}(1)))
  = q^{-1}(qu)^{-1}\frac{q^2}{1-q}·∑_{(m,n)}∑_j B_{j+1}(B_m(zDefect_n(S_{mn})_j))`,

the sums over the `y_1^my_2^n`-monomials of `HJO.Sweep.pairArgSucc q u A B` with coefficients
`S_{mn}` and over the `y_1`-expansion of `HJO.Sweep.zDefect q u n S_{mn}` — the *same* shape as the
base case `HJO.Sweep.constantCoeff_lowerRun_two_stageWordTotal_pair_one`, with the scalar carrying
one extra `q^{-1}` (the replicated letter's `q^{-k}` of `HJO.Mellit.replicatedLetter` at `k = 1`).

Three things happen here and none of them is a restatement. `HJO.Mellit.stageWordTotal_pair_succ`
peels one replicated letter off the second part;
`HJO.Sweep.constantCoeff_lowerRun_two_replicatedTotal_two_three_one_of_mem_piece` kills that
letter's *leading* braid factor against `HJO.Sweep.dminus_dminus_braid` and unfolds the slope
assembly; and `HJO.Sweep.constantCoeff_lowerRun_two_auxVar_one_mul_zCommTwo_of_mem_piece` evaluates
the outer `z` letter and the double lowering together. What remains of the sweep on the right is
the *inner* `z_1^{(2)}`, inside `HJO.Sweep.pairArgSucc`, and
`HJO.Sweep.zopOneStar_two_of_mem_piece` turns that into `Λ`-level data too — so with
`HJO.Sweep.constantCoeff_lowerRun_two_stageWordTotal_pair_one` as the base this is a decision
procedure for the two-part family at **every** `(A,B)`.

**What is NOT claimed.** This is a recursion carrying the *vector*
`G_{2,B+1}G_{1,A}(1)`, not its constant coefficient, which is exactly what
`HJO.Sweep.not_exists_factorization_replicated_two_three` shows is necessary: no recursion on the
values alone exists. Nothing here asserts a closed form in `B`, and none is expected — the one-part
family already has `2, 9, 26` `e`-monomials at `A = 1, 2, 3`.

**Unconditional**: no hypothesis on `q`, `u`, `A` or `B`, and the parts need not be positive. All
three inverses (`q^{-1}` of `HJO.Mellit.replicatedLetter`, `(qu)^{-1}` of `HJO.Sweep.slopeOperator`,
`q^2/(1-q)` of `HJO.Sweep.zop`) are carried symbolically, so at `q = 0`, `u = 0` or `q = 1` both
sides are `0` rather than the statement being false. -/
theorem constantCoeff_lowerRun_two_stageWordTotal_pair_succ (q u : L) (A B : ℕ) :
    MvPolynomial.constantCoeff (Mellit.lowerRun q 2 (Mellit.stageWordTotal q u 2 3 [A, B + 2]))
      = (q⁻¹ * ((q * u)⁻¹ * (q ^ 2 / (1 - q)))) •
          ∑ d ∈ (pairArgSucc q u A B : Total L).support,
            ∑ e ∈ (zDefect q u (d 1) (MvPolynomial.coeff d (pairArgSucc q u A B))).support,
              Sym.Bop q (((e 0 + 1 : ℕ) : ℤ))
                (Sym.Bop q ((d 0 : ℕ) : ℤ)
                  (MvPolynomial.coeff e (zDefect q u (d 1)
                    (MvPolynomial.coeff d (pairArgSucc q u A B))))) := by
  rw [Mellit.stageWordTotal_pair_succ,
    constantCoeff_lowerRun_two_replicatedTotal_two_three_one_of_mem_piece q u
      (Mellit.stageWordTotal_pair_mem_piece q u 2 3 A (B + 1)),
    ← pairArgSucc,
    constantCoeff_lowerRun_two_auxVar_one_mul_zCommTwo_of_mem_piece q u
      (pairArgSucc_mem_piece q u A B)]

end HJO.Sweep

end
