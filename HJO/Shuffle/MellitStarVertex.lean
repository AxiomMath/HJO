/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.MellitZopOneV1
public import HJO.CMStructure.StarElemSymm
public import HJO.Shuffle.Euclid
public import HJO.Shuffle.SweepAppendWidth
public meta import HJO.Attr

/-! # The vertex relation between `d^*_+` and the Hall--Littlewood operators

`HJO/Shuffle/MellitLhsSlopeMediant.lean` records that the mediant induction for the
general-slope gluing identity is circular, and gives the reason: writing `P := y_1d^*_+{}^{(0)}d_-`
and `N := d_-^{(2)}d^*_+{}^{(1)}`, the letter pair `YZ` of `HJO.Sweep.slopeOperator` is
`-(qu)^{-1}(P - y_1N)`, so **only the difference** `P - y_1N` was known to lie in the monoid the two
letters generate, and `N` therefore carried no information the mediant factorisation did not
already have.

This file removes that obstruction. It proves one new identity — the *vertex relation* — and from
it `P` alone lies in the two-letter monoid on `V_1`.

## The identity

`HJO.Sweep.dplusStar_C_elemSymm_succ_add` is the elementary half: the one-letter displacement
`d^*_+{}^{(k)}` of `HJO.Sweep.dplusStar` satisfies, on the elementary symmetric functions,

`d^*_+(Ce_{n+1}) + uy_1·d^*_+(Ce_n) = Ce_{n+1} + quy_1·Ce_n`.

This is the telescoping of `HJO.Sweep.dplusStar_C_elemSymm`, and nothing more: the sum
`S_n = ∑_{i<n}(-uy_1)^{i+1}Ce_{n-1-i}` satisfies `S_{n+1} + uy_1S_n = -uy_1Ce_n`, every other term
cancelling in pairs.

In generating-function form it says that the alternating elementary series
`Ω(t) = ∑_n (-1)^n e_n t^n` — which is the series `HJO.Sym.Bop` pairs against — is carried by
`d^*_+` to `Ω(t)·(1 - tquy_1)/(1 - tuy_1)`: the displacement multiplies `Ω` by the ratio of its own
two virtual letters `quy_1` and `uy_1`. That ratio is the whole content, and it is where the two
parameters enter asymmetrically.

## Main results

* `HJO.Sweep.dplusStar_C_elemSymm_succ_add` — the telescoping of `HJO.Sweep.dplusStar_C_elemSymm`,
  the scalar half.
* `HJO.Sweep.alphabetShift_neg_pos_bopExt_sub` — **the vertex relation**, for a shift adding one
  letter and removing another. `HJO.Sweep.alphabetShift_bopExt` in both its directions
  (`HJO.Sweep.alphabetShift_bopExt`, `HJO.Sweep.bopExt_alphabetShift_neg`), composed; the two
  one-letter corrections have no closed form separately but the *cleared* combination does.
* `HJO.Sweep.dplusStar_C_bop_sub` — the same for the two letters `d^*_+` carries, `quy_1` and
  `uy_1`.
* `HJO.Sweep.starComm_one_auxVar_mul_of_mem_piece` — the two halves of `HJO.Sweep.zop` at `k = 1`
  against multiplication by `y_1`, on the whole of `V_1`, **with no hypothesis on `q` or `u`**.
* `HJO.Sweep.auxVar_mul_dplusStar_dminus_of_mem_piece_one`, and its usable form
  `HJO.Sweep.zopOneStar_one_auxVar_mul_of_mem_piece` — **the `P` term in the two letters.**
* `HJO.Sweep.slopeOperator_mediant_rev_apply` — the mediant step on the *reverse* word, with the `P`
  term extracted; an unconditional identity, no residual hypothesis.
* `HJO.Sweep.dplusStar_C_elemSymmAlt_sub`, `HJO.Sweep.dplusStar_C_elemSymm_two_add_of_vertex` — the
  `A = 1` case, and the cross-check that it reproves the telescoping by a route that never reads
  `HJO.Sweep.dplusStar_C_elemSymm`.

## What this changes, and what it does not

`HJO/Shuffle/MellitLhsSlopeMediant.lean` records that with `P = y_1d^*_+{}^{(0)}d_-^{(1)}` and
`N = d_-^{(2)}d^*_+{}^{(1)}` **only the difference `P - y_1N` lies in the monoid the two letters
`Y = -(y_1·)` and `Z = (qu)^{-1}z_1` generate**, and concludes that `N` carries no information the
mediant factorisation does not already have. On `V_1` the first clause is now false:

`P = qu·YZ - ZY`   (`HJO.Sweep.auxVar_mul_dplusStar_dminus_of_mem_piece_one`),

so `P` alone is a quadratic word in the two letters. The new input is not word combinatorics; it is
`HJO.Sweep.alphabetShift_bopExt` applied to the two letters of `d^*_+`.

**It does not close the mediant step, and the reason is worth stating.**
Reading `P = qu·YZ - ZY` as a rewriting rule `ZY = qu·YZ - P` straightens any word in `Y, Z` to a
combination of the *straight* monomials `Y^aZ^b` together with words containing `P = Φπ`, whose
matrix elements `π(·)Φ` factor into products of smaller ones — which the induction hypothesis
supplies. So the whole family of clauses is equivalent to evaluating the straight matrix elements
`πY^aZ^bΦ`. Their two boundary rows *are* slope words — `Y^a = Ξ_{1,a+1}` and `Z^b = Ξ_{b+1,1}` by
`HJO.Mellit.slopeEval_one_left` and `HJO.Mellit.slopeEval_one_right` — but only one of the two rows
is a theorem:

* `πY^aΦ = (-1)^aQ_{1,a+1}` is `HJO.Mellit.lhsSlope_one_left`, proved;
* `πZ^bΦ = Q_{b+1,1}` is the clause at `(b+1,1)`, which is the **`(a,1)` column recorded as not
  treated** at `HJO/Shuffle/MellitLhsSlopeMediant.lean`. So the straightening *needs*
  that column, which answers the question left open there: it is not optional.

For `a, b ≥ 1` the straight monomials are not slope words at all, and the natural guess that they
are the slope operator at the corresponding possibly-non-coprime slope is **false**:
`πYZΦ(1) = -e_2` whereas `-Q_{2,2}(1) = -e_1^2 - (68/77)e_2` at `(q,u) = (3/7,5/11)`, by exact
rational arithmetic.  So the doubled slope is not reachable from width-1 straight monomials, and
`HJO.Sweep.exists_slopeActions` — the replicated actions at grading `k` — is where it has to come
from.

**And the residual of the mediant step is equivalent to its conclusion, not weaker than it.** With
the clause at both parents, `HJO.Sweep.slopeOperator_mediant_rev_apply` gives the sweep side at the
mediant as `qu·πΞ_pYZΞ_rΦ` minus `±C(Q_pQ_rf)`; solving, `πΞ_pYZΞ_rΦ` is determined by the clause at
the mediant and determines it. That is the same shape as
`HJO.Mellit.nTermGlue_iff_lhsSlope`: an equivalence, not a reduction.
What is *not* an equivalence is `HJO.Sweep.starComm_one_auxVar_mul_of_mem_piece` itself: it is an
unconditional identity about `d^*_+` and `HJO.Sym.Bop`, proved, and it holds at every `q` and `u`.

## Genericity

`HJO.Sweep.dplusStar_C_elemSymm_succ_add`, `HJO.Sweep.alphabetShift_neg_pos_bopExt_sub`,
`HJO.Sweep.dplusStar_C_bop_sub` and `HJO.Sweep.starComm_one_auxVar_mul_of_mem_piece` need **no
hypothesis on `q` or `u`**: both sides are polynomial expressions with every scalar carried
symbolically. At `u = 0` the telescoping degenerates to `d^*_+(Ce_{n+1}) = Ce_{n+1}`, true because
the displacement letter vanishes; at `q = 1` it reads
`d^*_+(Ce_{n+1}) + uy_1d^*_+(Ce_n) = Ce_{n+1} + uy_1Ce_n`, again true. So neither degenerate value
is an exclusion for those four.

`q ≠ 1` **is** a real exclusion for the two `z_1` forms, and not an artefact: the scalar
`q^k/(1-q)` of `HJO.Sweep.zop` is `0` at `q = 1` in this field, so `z_1 = 0` there while the `P`
term does not vanish.
`q ≠ 0` and `u ≠ 0` are spent in `HJO.Sweep.slopeOperator_mediant_rev_apply` only on cancelling
`HJO.Sweep.slopeOperator`'s `(qu)^{-1}` against the `qu` the split produces, which is why that
statement carries no inverse. No hypothesis on `u - 1` appears anywhere in this file.

## References

A. Mellit, *Toric braids and
`(m, n)`-parking functions*, §3.
-/

@[expose] public section

namespace HJO.Sweep

variable {L : Type*} [Field L] [Algebra ℚ L]

/-! ### The telescoping of the one-letter displacement on `e_n` -/

/-- **The displacement's recursion on the elementary symmetric functions.** For every level `k` and
every `n`,

`d^*_+{}^{(k)}(Ce_{n+1}) + uy_1·d^*_+{}^{(k)}(Ce_n) = Ce_{n+1} + quy_1·Ce_n`,

with `uy_1 = HJO.Sweep.starLetter u` the displacement letter of `HJO.Sweep.dplusStar_C_elemSymm`.

The proof is the telescoping of that expansion and nothing else: with
`S_n = ∑_{i<n}(-uy_1)^{i+1}Ce_{n-1-i}` the expansion is `d^*_+(Ce_n) = Ce_n - (q-1)S_n`, and
`S_{n+1} + uy_1S_n = -uy_1Ce_n` because the `i`-th term of `uy_1S_n` cancels the `(i+1)`-st term of
`S_{n+1}`, leaving only `S_{n+1}`'s `i = 0` term.

Read as generating functions this says `d^*_+(Ω(t)) = Ω(t)(1-tquy_1)/(1-tuy_1)` for the alternating
series `Ω(t) = ∑_n(-1)^ne_nt^n` of `HJO.Sym.elemSymmAlt`, which is the series `HJO.Sym.Bop` pairs
against; that is what makes it the scalar half of the vertex relation for `HJO.Sym.Bop`.

**No hypothesis on `q` or `u`.** -/
theorem dplusStar_C_elemSymm_succ_add (q u : L) (k n : ℕ) :
    dplusStar q u k (MvPolynomial.C (Sym.elemSymm L (n + 1)))
        + starLetter u * dplusStar q u k (MvPolynomial.C (Sym.elemSymm L n))
      = MvPolynomial.C (Sym.elemSymm L (n + 1))
        + scal q * starLetter u * MvPolynomial.C (Sym.elemSymm L n) := by
  have hS : (∑ i ∈ Finset.range (n + 1),
          (-starLetter u) ^ (i + 1) * MvPolynomial.C (Sym.elemSymm L (n + 1 - 1 - i)))
        + starLetter u * ∑ i ∈ Finset.range n,
            (-starLetter u) ^ (i + 1) * MvPolynomial.C (Sym.elemSymm L (n - 1 - i))
        = -(starLetter u * MvPolynomial.C (Sym.elemSymm L n)) := by
    have hterm : ∀ i ∈ Finset.range n,
        (-starLetter u) ^ (i + 1 + 1) * MvPolynomial.C (Sym.elemSymm L (n + 1 - 1 - (i + 1)))
          + starLetter u *
            ((-starLetter u) ^ (i + 1) * MvPolynomial.C (Sym.elemSymm L (n - 1 - i))) = 0 := by
      intro i _
      rw [show n + 1 - 1 - (i + 1) = n - 1 - i from by omega, pow_succ]
      ring
    rw [Finset.sum_range_succ' (fun i =>
        (-starLetter u) ^ (i + 1) * MvPolynomial.C (Sym.elemSymm L (n + 1 - 1 - i))) n,
      Finset.mul_sum, add_right_comm, ← Finset.sum_add_distrib,
      Finset.sum_congr rfl hterm, Finset.sum_const_zero, zero_add]
    simp
  have hq : (scal q : Total L) = 1 + scal (q - 1) := by
    rw [scal_sub, scal_one]
    ring
  rw [dplusStar_C_elemSymm, dplusStar_C_elemSymm]
  linear_combination (-(scal (q - 1) : Total L)) * hS
    + (-(starLetter u * MvPolynomial.C (Sym.elemSymm L n) : Total L)) * hq

/-! ### The vertex relation for a two-letter displacement -/

/-- **The vertex relation, for a shift that adds one letter `v` and removes one letter `w`.**

`HJO.Sweep.alphabetShift_bopExt` says a *one*-letter shift conjugates the Hall--Littlewood family by
a single correction: `HJO.Sweep.alphabetShift_bopExt` is `Γ₊(v)B_i = (B_i - vB_{i-1})Γ₊(v)` and
`HJO.Sweep.bopExt_alphabetShift_neg` is `B_iΓ₊(-w) = Γ₊(-w)(B_i - wB_{i-1})`. Composing the two —
which is exactly the shape of `d^*_+` on the constants, `HJO.Sweep.dplusStar_C_eq_starGamma` — the
two corrections do not compose to a closed form for `ΓB_i` alone, but they do for the **cleared**
combination:

`Γ(B_i) - w·Γ(B_{i-1}) = B_i(Γ) - v·B_{i-1}(Γ)`,   `Γ = Γ₊(-w)∘Γ₊(v)`.

In generating functions this is `Γ·B(t)·(1 - tw) = (1 - tv)·B(t)·Γ`, i.e. the shift multiplies the
Jing operator by the ratio of its own two letters; the ratio is a *rational* function of `t`, and
clearing its denominator is what makes the statement a finite identity between four terms rather
than an infinite sum.

Both hypotheses are that the letters are free of the alphabet, which is what
`HJO.Sweep.alphabetShift_bopExt` asks of each separately.

**No hypothesis on `q`.** -/
theorem alphabetShift_neg_pos_bopExt_sub (q : L) (i : ℤ) {v w : Total L}
    (hv : v ∈ auxSubalg L) (hw : w ∈ auxSubalg L) (G : Total L) :
    alphabetShift (fun r => -w ^ r) (alphabetShift (fun r => v ^ r) (bopExt q i G))
        - w * alphabetShift (fun r => -w ^ r)
            (alphabetShift (fun r => v ^ r) (bopExt q (i - 1) G))
      = bopExt q i
          (alphabetShift (fun r => -w ^ r) (alphabetShift (fun r => v ^ r) G))
        - v * bopExt q (i - 1)
            (alphabetShift (fun r => -w ^ r) (alphabetShift (fun r => v ^ r) G)) := by
  have hA : ∀ j : ℤ, alphabetShift (fun r => v ^ r) (bopExt q j G)
      = bopExt q j (alphabetShift (fun r => v ^ r) G)
        - v * bopExt q (j - 1) (alphabetShift (fun r => v ^ r) G) :=
    fun j => alphabetShift_bopExt q j hv G
  have hC : ∀ (j : ℤ) (H : Total L),
      bopExt q j (alphabetShift (fun r => -w ^ r) H)
        = alphabetShift (fun r => -w ^ r) (bopExt q j H)
          - w * alphabetShift (fun r => -w ^ r) (bopExt q (j - 1) H) := by
    intro j H
    rw [bopExt_alphabetShift_neg q j hw H, map_sub, map_mul,
      alphabetShift_of_mem_auxSubalg _ hw]
  have hmul : ∀ x : Total L,
      alphabetShift (fun r => -w ^ r) (v * x) = v * alphabetShift (fun r => -w ^ r) x := by
    intro x
    rw [map_mul, alphabetShift_of_mem_auxSubalg _ hv]
  rw [hA i, hA (i - 1), map_sub, map_sub, hmul, hmul,
    hC i (alphabetShift (fun r => v ^ r) G), hC (i - 1) (alphabetShift (fun r => v ^ r) G)]
  ring

/-- **The vertex relation for `d^*_+` and the Hall--Littlewood operators**, on the constants:

`d^*_+(CB_iA) - uy_1·d^*_+(CB_{i-1}A) = B_i(d^*_+(CA)) - quy_1·B_{i-1}(d^*_+(CA))`,

with `B_i` on the right the coefficientwise extension `HJO.Sweep.bopExt` of `HJO.Sym.Bop`. This is
`HJO.Sweep.alphabetShift_neg_pos_bopExt_sub` at the two letters `d^*_+` actually carries,
`v = quy_1` and `w = uy_1` (`HJO.Sweep.dplusStar_C_eq_starGamma`), read through
`HJO.Sweep.bopExt_C`.

**This is the identity the general-slope gluing identity was missing**, and it is why: it says the
failure of `B_m` to commute with the displacement — which is exactly what
`HJO.Sweep.zopOneStar_one_auxVar_pow_mul_C` computes `z_1` to be — is *itself* expressible in the
`B`'s and the letter, with no second commutator. See
`HJO.Sweep.auxVar_mul_dplusStar_dminus_of_mem_piece_one`.

**No hypothesis on `q` or `u`**: every scalar is carried symbolically. -/
theorem dplusStar_C_bop_sub (q u : L) (i : ℤ) (A : Sym.Lambda L) :
    dplusStar q u 0 (MvPolynomial.C (Sym.Bop q i A))
        - starLetter u * dplusStar q u 0 (MvPolynomial.C (Sym.Bop q (i - 1) A))
      = bopExt q i (dplusStar q u 0 (MvPolynomial.C A))
        - scal q * starLetter u * bopExt q (i - 1) (dplusStar q u 0 (MvPolynomial.C A)) := by
  have hw : starLetter u ∈ auxSubalg L := starLetter_mem_auxSubalg u
  have hv : scal q * starLetter u ∈ auxSubalg L :=
    mul_mem (Subalgebra.algebraMap_mem _ q) hw
  have hstar : ∀ f : Sym.Lambda L, dplusStar q u 0 (MvPolynomial.C f)
      = alphabetShift (fun r => -starLetter u ^ r)
          (alphabetShift (fun r => (scal q * starLetter u) ^ r) (MvPolynomial.C f)) := by
    intro f
    rw [dplusStar_C_eq_starGamma, starGammaNeg_apply, starGammaQ_apply]
  rw [hstar, hstar, hstar, ← bopExt_C, ← bopExt_C]
  exact alphabetShift_neg_pos_bopExt_sub q i hv hw (MvPolynomial.C A)

/-! ### The starred commutator against multiplication by `y_1`, on `V_1` -/

/-- **The vertex relation as the two halves of `z_1`, on a monomial of `V_1`.** With
`P := d^*_+{}^{(0)}d_-^{(1)}` and `N := d_-^{(2)}d^*_+{}^{(1)}` the two halves of `HJO.Sweep.zop` at
`k = 1`,

`(P - N)(y_1·y_1^mCA) = uy_1·P(y_1^mCA) - quy_1·N(y_1^mCA)`.

The two evaluations `HJO.Sweep.dminus_one_auxVar_pow_mul_C` and
`HJO.Sweep.dminus_two_dplusStar_one_auxVar_pow_mul_C` turn the two halves into
`d^*_+(CB_mA)` and `B_m(d^*_+(CA))`, and then this *is*
`HJO.Sweep.dplusStar_C_bop_sub` at `i = m+1`.

**No hypothesis on `q` or `u`.** -/
theorem starComm_one_auxVar_mul_auxVar_pow_mul_C (q u : L) (m : ℕ) (A : Sym.Lambda L) :
    dplusStar q u 0 (dminus q 1 ((auxVar 1 : Total L) *
          ((auxVar 1 : Total L) ^ m * MvPolynomial.C A)))
        - dminus q 2 (dplusStar q u 1 ((auxVar 1 : Total L) *
            ((auxVar 1 : Total L) ^ m * MvPolynomial.C A)))
      = starLetter u * dplusStar q u 0
            (dminus q 1 ((auxVar 1 : Total L) ^ m * MvPolynomial.C A))
        - scal q * starLetter u * dminus q 2
            (dplusStar q u 1 ((auxVar 1 : Total L) ^ m * MvPolynomial.C A)) := by
  have hpow : (auxVar 1 : Total L) * ((auxVar 1 : Total L) ^ m * MvPolynomial.C A)
      = (auxVar 1 : Total L) ^ (m + 1) * MvPolynomial.C A := by
    rw [pow_succ']
    ring
  have hcast : ((m : ℤ) + 1) - 1 = (m : ℤ) := by ring
  rw [hpow, dminus_one_auxVar_pow_mul_C, dminus_one_auxVar_pow_mul_C,
    dminus_two_dplusStar_one_auxVar_pow_mul_C, dminus_two_dplusStar_one_auxVar_pow_mul_C,
    show (((m + 1 : ℕ) : ℤ)) = (m : ℤ) + 1 from by push_cast; ring]
  have h := dplusStar_C_bop_sub q u ((m : ℤ) + 1) A
  rw [hcast] at h
  linear_combination h

/-- **The vertex relation on the whole of `V_1`**, `G = ∑_m G_my_1^m` with `G_m ∈ Λ`:

`(P - N)(y_1G) = uy_1·P(G) - quy_1·N(G)`,

`P = d^*_+{}^{(0)}d_-^{(1)}`, `N = d_-^{(2)}d^*_+{}^{(1)}`. Every monomial of `G ∈ V_1` is a power
of `y_1` (`HJO.Sweep.exists_single_zero_of_mem_piece_one`) and both sides are additive, so this is
`HJO.Sweep.starComm_one_auxVar_mul_auxVar_pow_mul_C` summed over `G.support`.

`G ∈ V_1` is not decoration: `N`'s inner `d^*_+{}^{(1)}` sends `y_1` to `y_2`, which is the variable
its outer `d_-^{(2)}` extracts in, and on a monomial already carrying `y_2` the evaluation used
above fails.

**No hypothesis on `q` or `u`.** -/
theorem starComm_one_auxVar_mul_of_mem_piece (q u : L) {G : Total L} (hG : G ∈ piece L 1) :
    dplusStar q u 0 (dminus q 1 ((auxVar 1 : Total L) * G))
        - dminus q 2 (dplusStar q u 1 ((auxVar 1 : Total L) * G))
      = starLetter u * dplusStar q u 0 (dminus q 1 G)
        - scal q * starLetter u * dminus q 2 (dplusStar q u 1 G) := by
  have hmon : ∀ (m : ℕ) (a : Sym.Lambda L),
      (auxVar 1 : Total L) ^ m * MvPolynomial.C a
        = MvPolynomial.monomial (Finsupp.single 0 m) a := by
    intro m a
    rw [auxVar, Nat.sub_self, MvPolynomial.X_pow_eq_monomial, mul_comm,
      MvPolynomial.C_mul_monomial, mul_one]
  conv_lhs => rw [G.as_sum]
  conv_rhs => rw [G.as_sum]
  rw [Finset.mul_sum, map_sum, map_sum, map_sum, map_sum, map_sum, map_sum, map_sum, map_sum,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun d hd => ?_
  obtain ⟨m, rfl⟩ := exists_single_zero_of_mem_piece_one hG hd
  rw [← hmon m (MvPolynomial.coeff (Finsupp.single 0 m) G)]
  exact starComm_one_auxVar_mul_auxVar_pow_mul_C q u m _

/-! ### The `P` term lies in the monoid the two letters of the slope word generate -/

/-- **`quy_1·d^*_+{}^{(0)}(d_-^{(1)}G) = z_1(y_1G) - quy_1·z_1(G)` on `V_1`.**

This is the point of the file. `HJO/Shuffle/MellitLhsSlopeMediant.lean` records, as the reason
the mediant induction for the general-slope gluing identity is circular, that with
`P = y_1d^*_+{}^{(0)}d_-^{(1)}` and `N = d_-^{(2)}d^*_+{}^{(1)}` **only the difference `P - y_1N`
lies in the monoid the two letters `Y = -(y_1·)` and `Z = (qu)^{-1}z_1` of
`HJO.Sweep.slopeOperator` generate**, so that `N` carries no information beyond the letters, and
neither `P` nor `y_1N` alone is constrained by the word combinatorics.

On `V_1` that is no longer so. In the letters it reads

`P = qu·YZ - ZY`,

so the `P` term of the mediant step — the term the induction hypothesis consumes — *is* a quadratic
word in `Y` and `Z`. The input is the vertex relation
`HJO.Sweep.starComm_one_auxVar_mul_of_mem_piece`, which is not a consequence of the word
combinatorics: it is `HJO.Sweep.alphabetShift_bopExt` applied to the two letters of `d^*_+`.

**`q ≠ 1` is a real exclusion, not an artefact.** The scalar `q/(1-q)` of `HJO.Sweep.zop` is `0` at
`q = 1` in this field, so `z_1 = 0` there and the left side is `uy_1·d^*_+(d_-G)`, which does not
vanish — at `G = y_1` it is `uy_1·d^*_+(C e_1) ≠ 0`. What fails at `q = 1` is not this identity but
`HJO.Sweep.zop` itself, whose whole scalar degenerates; the vertex relation
`HJO.Sweep.starComm_one_auxVar_mul_of_mem_piece` it is derived from needs no hypothesis.
`q ≠ 0` is **not** needed, and neither is any hypothesis on `u`. -/
theorem auxVar_mul_dplusStar_dminus_of_mem_piece_one {q u : L} (hq1 : q ≠ 1) {G : Total L}
    (hG : G ∈ piece L 1) :
    scal q * starLetter u * dplusStar q u 0 (dminus q 1 G)
      = zopOneStar q u 1 ((auxVar 1 : Total L) * G)
        - scal q * starLetter u * zopOneStar q u 1 G := by
  have h1q : (1 : L) - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq1)
  have hz : ∀ X : Total L, zopOneStar q u 1 X
      = scal (q / (1 - q)) *
          (dplusStar q u 0 (dminus q 1 X) - dminus q 2 (dplusStar q u 1 X)) := by
    intro X
    rw [zopOneStar, show trainUpEnd q 1 1 = 1 from Braid.trainUp_self _ _ 1, mul_one]
    simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.mul_apply, pow_one,
      Nat.sub_self]
    rw [Algebra.smul_def, ← scal_eq_algebraMap]
  have hc : (scal (q / (1 - q)) : Total L) - scal q * scal (q / (1 - q)) = scal q := by
    rw [← scal_mul, ← scal_sub]
    congr 1
    field_simp
  rw [hz, hz, starComm_one_auxVar_mul_of_mem_piece q u hG]
  linear_combination (-(starLetter u * dplusStar q u 0 (dminus q 1 G))) * hc

/-- **`z_1(y_1G) = quy_1·(z_1G + d^*_+{}^{(0)}(d_-^{(1)}G))` on `V_1`**, the usable form of
`HJO.Sweep.auxVar_mul_dplusStar_dminus_of_mem_piece_one`: moving one letter `y_1` inside `z_1` costs
exactly the `P` term. Same hypothesis, `q ≠ 1`. -/
theorem zopOneStar_one_auxVar_mul_of_mem_piece {q u : L} (hq1 : q ≠ 1) {G : Total L}
    (hG : G ∈ piece L 1) :
    zopOneStar q u 1 ((auxVar 1 : Total L) * G)
      = scal (q * u) * (auxVar 1 : Total L) *
        (zopOneStar q u 1 G + dplusStar q u 0 (dminus q 1 G)) := by
  have h := auxVar_mul_dplusStar_dminus_of_mem_piece_one (u := u) hq1 hG
  have hw : (scal q * starLetter u : Total L) = scal (q * u) * (auxVar 1 : Total L) := by
    rw [starLetter, scal_mul]
    ring
  rw [hw] at h
  linear_combination -h

/-! ### The mediant step of the slope operator, on the reverse word -/

/-- **The mediant step computed on the *reverse* word, with the `P` term extracted.**

For two positive coprime pairs with `r_1p_2 = p_1r_2 + 1`, `HJO.Mellit.slopeWord_mediant_rev`
(`HJO.Mellit.slopeEval_mediant_rev`) factors the slope operator at the mediant as
`Ξ_{p+r} = Ξ_p·Z·Y·Ξ_r` — the parent *innermost*, which is the order
`HJO.Mellit.dminus_slopeOperator_mediant` does not use. On that word the letter `Y` is applied
*before* `Z`, so the argument of `Z` is `y_1·Ξ_rX` and
`HJO.Sweep.zopOneStar_one_auxVar_mul_of_mem_piece` applies, splitting it into

`Ξ_{p+r}(X) = -Ξ_p(y_1·z_1(Ξ_rX)) - Ξ_p(y_1·d^*_+{}^{(0)}(d_-^{(1)}(Ξ_rX)))`.

The second summand is the `P` term at `r`, and `y_1d^*_+{}^{(0)}(d_-^{(1)}·)` is exactly how the
general clause wraps its input — so under `d_-` it is consumed by the clause at `r` and then at `p`,
producing the composite `Q_pQ_r` in **that** order. The first summand is the single residual word
`Ξ_pYZΞ_r`, and it is the whole of what the mediant step still needs.

Compare `HJO.Mellit.dminus_slopeOperator_mediant`, which is the same step on the forward word and
produces `Q_rQ_p` with residual `Ξ_rYNΞ_p`. That residual was shown there to be equivalent to the
conclusion, `N` carrying no information; the residual here is a word in the two letters only.

**Genericity: `q ∉ {0,1}` and `u ≠ 0`.** `q ≠ 1` comes from
`HJO.Sweep.zopOneStar_one_auxVar_mul_of_mem_piece`, and `q ≠ 0`, `u ≠ 0` are spent only on
cancelling `HJO.Sweep.slopeOperator`'s `(qu)^{-1}` against the `qu` the split produces — so the
statement carries no inverse at all. -/
theorem slopeOperator_mediant_rev_apply {q u : L} (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1)
    {p₁ p₂ r₁ r₂ : ℕ} (hp₁ : 1 ≤ p₁) (hp₂ : 1 ≤ p₂) (hr₁ : 1 ≤ r₁) (hr₂ : 1 ≤ r₂)
    (hdet : r₁ * p₂ = p₁ * r₂ + 1) (hcp : Nat.Coprime p₁ p₂) (hcr : Nat.Coprime r₁ r₂)
    {X : Total L} (hX : X ∈ piece L 1) :
    slopeOperator q u 1 (p₁ + r₁) (p₂ + r₂) X
      = -slopeOperator q u 1 p₁ p₂ ((auxVar 1 : Total L) *
            zopOneStar q u 1 (slopeOperator q u 1 r₁ r₂ X))
        - slopeOperator q u 1 p₁ p₂ ((auxVar 1 : Total L) *
            dplusStar q u 0 (dminus q 1 (slopeOperator q u 1 r₁ r₂ X))) := by
  have hqu : q * u ≠ 0 := mul_ne_zero hq0 hu0
  have hW : slopeOperator q u 1 r₁ r₂ X ∈ piece L 1 :=
    slopeOperator_mem_piece q u le_rfl hX
  have hmed : slopeOperator q u 1 (p₁ + r₁) (p₂ + r₂)
      = slopeOperator q u 1 p₁ p₂ * (((q * u)⁻¹ • zop q u 1 1)
          * ((-LinearMap.mulLeft L (auxVar 1 : Total L)) * slopeOperator q u 1 r₁ r₂)) := by
    rw [slopeOperator_eq_slopeEval, slopeOperator_eq_slopeEval, slopeOperator_eq_slopeEval]
    exact Mellit.slopeEval_mediant_rev _ _ hp₁ hp₂ hr₁ hr₂ hdet hcp hcr
  rw [hmed]
  simp only [Module.End.mul_apply, LinearMap.neg_apply, LinearMap.mulLeft_apply,
    LinearMap.smul_apply, zop_one]
  rw [map_neg, zopOneStar_one_auxVar_mul_of_mem_piece hq1 hW, smul_neg,
    show (scal (q * u) : Total L) = algebraMap L (Total L) (q * u) from rfl,
    ← Algebra.smul_def, smul_mul_assoc, smul_smul, inv_mul_cancel₀ hqu, one_smul, map_neg,
    mul_add, map_add]
  ring

/-- **The vertex relation at `A = 1`: the displacement on the alternating elementary series.**

`B_i(1)` and `B_i` applied coefficientwise to `d^*_+(C1) = 1` are both the coefficient of the
alternating series `Ω(t) = ∑_n(-1)^ne_nt^n` at `i` (`HJO.Sym.bop_one`, `HJO.Sweep.bopExt_one`), so
`HJO.Sweep.dplusStar_C_bop_sub` at `A = 1` is

`d^*_+(CΩ_i) - uy_1·d^*_+(CΩ_{i-1}) = CΩ_i - quy_1·CΩ_{i-1}`,

the generating-function statement `d^*_+(Ω(t))(1 - tuy_1) = Ω(t)(1 - tquy_1)` read coefficientwise.
Stated at every **integer** `i`, where the series vanishes below `0`. -/
theorem dplusStar_C_elemSymmAlt_sub (q u : L) (i : ℤ) :
    dplusStar q u 0 (MvPolynomial.C (Sym.elemSymmAlt L i))
        - starLetter u * dplusStar q u 0 (MvPolynomial.C (Sym.elemSymmAlt L (i - 1)))
      = MvPolynomial.C (Sym.elemSymmAlt L i)
        - scal q * starLetter u * MvPolynomial.C (Sym.elemSymmAlt L (i - 1)) := by
  have h1 : dplusStar q u 0 (MvPolynomial.C (1 : Sym.Lambda L)) = (1 : Total L) := by
    rw [MvPolynomial.C_1, dplusStar_map_one]
  have h := dplusStar_C_bop_sub q u i (1 : Sym.Lambda L)
  rwa [Sym.bop_one, Sym.bop_one, h1, bopExt_one, bopExt_one] at h

/-- **Cross-check: the vertex relation reproves the telescoping at `n = 1`.**

`HJO.Sweep.dplusStar_C_elemSymm_succ_add` at `k = 0`, `n = 1` says
`d^*_+(Ce_2) + uy_1d^*_+(Ce_1) = Ce_2 + quy_1Ce_1`. That is `HJO.Sweep.dplusStar_C_elemSymmAlt_sub`
at `i = 2`, where `Ω_2 = e_2` and `Ω_1 = -e_1`, and the two minus signs of the `Ω`-form become the
two plus signs of the `e`-form.

Nothing in this proof touches `HJO.Sweep.dplusStar_C_elemSymm` — the route is through
`HJO.Sweep.alphabetShift_bopExt` and `HJO.Sym.Bop` instead — so it is an independent check of the
two letters, of the index `i-1`, and of which of the two carries the `q`: swapping `uy_1` and
`quy_1` fails here. -/
theorem dplusStar_C_elemSymm_two_add_of_vertex (q u : L) :
    dplusStar q u 0 (MvPolynomial.C (Sym.elemSymm L 2))
        + starLetter u * dplusStar q u 0 (MvPolynomial.C (Sym.elemSymm L 1))
      = MvPolynomial.C (Sym.elemSymm L 2)
        + scal q * starLetter u * MvPolynomial.C (Sym.elemSymm L 1) := by
  have h := dplusStar_C_elemSymmAlt_sub q u 2
  rw [show (2 : ℤ) - 1 = ((1 : ℕ) : ℤ) from by norm_num,
    show (2 : ℤ) = ((2 : ℕ) : ℤ) from by norm_num,
    Sym.elemSymmAlt_natCast, Sym.elemSymmAlt_natCast] at h
  norm_num only [pow_one, pow_two, neg_mul, neg_neg, one_mul, map_neg, map_one] at h
  linear_combination h

end HJO.Sweep
