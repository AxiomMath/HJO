/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepWidthThreeFour
public import HJO.CMStructure.StarEasy

/-! # The ascending train on an arbitrary monomial: the general branching formula

`HJO/Shuffle/SweepBraidMonomial.lean` computes the single braid letter `T_i` at every index and
every pair of exponents, and `HJO/Shuffle/SweepTrainWidth.lean` and
`HJO/Shuffle/SweepWidthThreeFour.lean` evaluate the ascending train `T_{1↗k+1}` on three
special shapes — a symmetric vector, a symmetric vector times `y_{k+1}`, and `y_{k+1}^2`. This file
removes the restriction to special shapes: it gives the train on an **arbitrary** monomial, at every
width, by peeling the train's last letter.

## The general branching step

`T_{1↗k+1}` peels as `T_{1↗k}∘T_k` (`HJO.Sweep.cmAscWord_one_succ_apply`), and `T_k` moves only
`y_k` and `y_{k+1}`. So for any `P` symmetric in those two variables — in particular any polynomial
in `y_1, …, y_{k-1}` — the whole train on `P·y_k^{a_k}y_{k+1}^{a_{k+1}}` is a sum of **shorter**
trains, one per term of the single letter's closed form, with the surviving power of `y_{k+1}`
pulled outside because `T_1, …, T_{k-1}` all fix it:

* `HJO.Sweep.cmAscWord_one_succ_mul_auxVar_pow_mul_auxVar_pow'`, the ascending ordering
  `a_k = a ≤ a_{k+1} = a + c`;
* `HJO.Sweep.cmAscWord_one_succ_mul_auxVar_pow_mul_auxVar_pow`, the descending ordering
  `a_k = a + c ≥ a_{k+1} = a`, which differs only in the sign of the correction.

Every monomial is of one of those two shapes, so the two statements together are a complete
reduction of the width-`k+1` train on any monomial to width-`k` trains on monomials, and iterating
them `k` times evaluates the train outright. That is the general branching formula: the shapes
already computed are the cases where the correction sum is empty (`c = 0`, the symmetric case) or
has one term (`c = 1`, the adjacent pair).

## The power family, in closed recursive form

The shape the sweep meets is `y_{k+1}^n` (times a symmetric factor, which rides through). Writing
`F_k^{(n)} = T_{1↗k+1}(y_{k+1}^n)`, the branching step collapses to a single recursion in which the
leading branch has already absorbed its `q`:

* `HJO.Sweep.cmAscWord_one_succ_auxVar_last_pow_succ`:
  `F_k^{(n+1)} = qF_{k-1}^{(n+1)} + (q-1)∑_{j<n}y_{k+1}^{n-j}F_{k-1}^{(j+1)}`;
* `HJO.Sweep.cmAscWord_one_succ_auxVar_last_pow_succ_sub`, the same content with the sum eliminated:
  `F_k^{(n+1)} - y_{k+1}F_k^{(n)} = qF_{k-1}^{(n+1)} - y_{k+1}F_{k-1}^{(n)}`.

The second is a two-term recurrence with no sum in it at all, and with `F_k^{(0)} = 1` it determines
every `F_k^{(n)}` by a double induction. It is the finite shape of the generating-function identity
`∑_nF_k^{(n)}z^n = 1 + \frac{y_1z}{1-y_1z}∏_{i=2}^{k+1}\frac{q-y_iz}{1-y_iz}`, whose coefficient
extraction is the explicit monomial sum of
`HJO/Shuffle/SweepTrainMonomialClosed.lean`.

## The agreement checks

Each of the three earlier shapes is re-derived here from the general statements, which is the check
that the general formula is the right one:

* the symmetric case `n = 0`, `HJO.Sweep.cmAscWord_one_auxVar_last_pow_zero_check`, where the train
  is the identity;
* `n = 1`, `HJO.Sweep.cmAscWord_one_auxVar_last_pow_one_check`, which must reproduce
  `HJO.Sweep.cmAscWord_one_auxVar_last`'s `q^k y_1`;
* `n = 2`, `HJO.Sweep.cmAscWord_one_auxVar_last_sq_check`, which feeds the width-`k` value of
  `HJO.Sweep.cmAscWord_one_auxVar_last_sq` into the recursion and gets its width-`k+1` value
  out. A general formula disagreeing with that one would be wrong, and this is the statement that
  says it does not.

## The other extreme: excess on the bottom variable

`HJO.Sweep.cmAscWord_one_auxVar_one_pow` is the complementary shape `y_1^n`, where every letter but
the first is the identity and the whole train is a single letter. Together with the branching step
these are the two ends of the monomial: excess at the top, which cascades, and excess at the bottom,
which does not move at all.

## Genericity

Nothing here reads a hypothesis on `q`, and nothing here mentions `u`. Every statement is a
polynomial identity in `q`: the braid letter of `HJO.Sweep.braid` is a polynomial in `q`, the train
is a product of such letters, and no inverse of anything occurs. In particular all of these hold at
`q = 0` and at `q = 1`, unlike every statement about `HJO.Sweep.corner`, which carries
`HJO.Sweep.corner`'s literal `(q-1)^{-1}`. The index hypotheses are the definitions' own range
condition `1 ≤ i` on `s_i` and `∂_i`, discharged by `omega` at each use.

## References

A. Mellit, *Toric braids and `(m,n)`-parking functions*, §3.2.
-/

@[expose] public section

namespace HJO.Sweep

open MvPolynomial

section Field

variable {L : Type*} [Field L] {q : L}

/-! ### The letters below the top fix the top variable -/

/-- Every letter of `T_{1↗k}` fixes a power of `y_{k+1}`: the letter `T_j` moves only `y_j, y_{j+1}`
and `j + 1 ≤ k < k + 1` throughout. This is what lets the branching step pull the surviving power of
the top variable outside the shorter train. -/
theorem swapAux_auxVar_add_two_pow {m : ℕ} (e : ℕ) {j : ℕ} (hj2 : j ≤ m) :
    swapAux L j ((auxVar (m + 2) : Total L) ^ e) = (auxVar (m + 2) : Total L) ^ e := by
  rw [map_pow, swapAux_auxVar_of_ne (by omega) (by omega) (by omega)]

/-- `T_{1↗k}(y_{k+1}^e·G) = y_{k+1}^e·T_{1↗k}G`, the pull-out step of the branching formula. -/
theorem cmAscWord_one_auxVar_add_two_pow_mul (q : L) (m e : ℕ) (G : Total L) :
    cmAscWord q 1 m ((auxVar (m + 2) : Total L) ^ e * G)
      = (auxVar (m + 2) : Total L) ^ e * cmAscWord q 1 m G :=
  cmAscWord_mul_of_swapAux_eq q (by omega)
    (fun _ _ hj2 => swapAux_auxVar_add_two_pow e hj2) G

/-! ### The general branching step, both orderings of the top pair -/

/-- **The general branching formula, ascending ordering.** For any `P` with `s_kP = P` and all
exponents `a, c`,

`T_{1↗k+1}(P·y_k^ay_{k+1}^{a+c})
  = y_{k+1}^a·T_{1↗k}(P·y_k^{a+c})
    + (q-1)∑_{j<c}y_{k+1}^{a+c-1-j}·T_{1↗k}(P·y_k^{a+1+j})`.

The width-`k+1` train on an arbitrary monomial becomes `c + 1` width-`k` trains on monomials. Three
facts combine: the train gives up its last letter (`HJO.Sweep.cmAscWord_one_succ_apply`), that
letter is `HJO.Sweep.braid_auxVar_pow_mul_auxVar_pow'` on the top pair and passes `P`
(`s_k`-invariant) through (`HJO.Sweep.braid_mul_of_swapAux_eq`), and the shorter train passes every
power of `y_{k+1}` through (`HJO.Sweep.cmAscWord_one_auxVar_add_two_pow_mul`).

Unconditional in `q`, and `c = 0` recovers the symmetric case: the sum is empty and the train just
moves the pair's common power across. -/
theorem cmAscWord_one_succ_mul_auxVar_pow_mul_auxVar_pow' (q : L) (m : ℕ) {P : Total L}
    (hP : swapAux L (m + 1) P = P) (a c : ℕ) :
    cmAscWord q 1 (m + 1)
        (P * (auxVar (m + 1) : Total L) ^ a * (auxVar (m + 2) : Total L) ^ (a + c))
      = (auxVar (m + 2) : Total L) ^ a
          * cmAscWord q 1 m (P * (auxVar (m + 1) : Total L) ^ (a + c))
        + scal (q - 1) * ∑ j ∈ Finset.range c,
            (auxVar (m + 2) : Total L) ^ (a + c - 1 - j)
              * cmAscWord q 1 m (P * (auxVar (m + 1) : Total L) ^ (a + 1 + j)) := by
  have hterm : ∀ j ∈ Finset.range c,
      (auxVar (m + 2) : Total L) ^ (a + c - 1 - j) * (P * (auxVar (m + 1) : Total L) ^ (a + 1 + j))
        = P * ((auxVar (m + 1) : Total L) ^ (a + 1) * (auxVar (m + 2) : Total L) ^ a
            * ((auxVar (m + 1) : Total L) ^ j * (auxVar (m + 2) : Total L) ^ (c - 1 - j))) := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [show a + c - 1 - j = a + (c - 1 - j) by omega, pow_add, pow_add]
    ring
  have harg : P * ((auxVar (m + 1) : Total L) ^ (a + c) * (auxVar (m + 2) : Total L) ^ a
        + scal (q - 1) * ((auxVar (m + 1) : Total L) ^ (a + 1)
            * (auxVar (m + 2) : Total L) ^ a
            * ∑ j ∈ Finset.range c,
                (auxVar (m + 1) : Total L) ^ j * (auxVar (m + 2) : Total L) ^ (c - 1 - j)))
      = (auxVar (m + 2) : Total L) ^ a * (P * (auxVar (m + 1) : Total L) ^ (a + c))
        + scal (q - 1) * ∑ j ∈ Finset.range c,
            (auxVar (m + 2) : Total L) ^ (a + c - 1 - j)
              * (P * (auxVar (m + 1) : Total L) ^ (a + 1 + j)) := by
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, Finset.mul_sum]
    ring
  rw [show P * (auxVar (m + 1) : Total L) ^ a * (auxVar (m + 2) : Total L) ^ (a + c)
        = P * ((auxVar (m + 1) : Total L) ^ a * (auxVar (m + 2) : Total L) ^ (a + c)) by ring,
    cmAscWord_one_succ_apply, braid_mul_of_swapAux_eq q hP,
    braid_auxVar_pow_mul_auxVar_pow' q (i := m + 1) (by omega) a c, harg, map_add,
    cmAscWord_scal_mul, map_sum]
  simp only [cmAscWord_one_auxVar_add_two_pow_mul]

/-- **The general branching formula, descending ordering.** For any `P` with `s_kP = P`,

`T_{1↗k+1}(P·y_k^{a+c}y_{k+1}^a)
  = y_{k+1}^{a+c}·T_{1↗k}(P·y_k^a)
    - (q-1)∑_{j<c}y_{k+1}^{a+c-1-j}·T_{1↗k}(P·y_k^{a+1+j})`.

The companion of `HJO.Sweep.cmAscWord_one_succ_mul_auxVar_pow_mul_auxVar_pow'`, differing from it
only in the sign of the correction and in which power of `y_{k+1}` the leading term carries: the
letter read here is `HJO.Sweep.braid_auxVar_pow_mul_auxVar_pow`. Every monomial has its top pair in
one of the two orderings, so the two statements are a complete reduction. Unconditional in `q`. -/
theorem cmAscWord_one_succ_mul_auxVar_pow_mul_auxVar_pow (q : L) (m : ℕ) {P : Total L}
    (hP : swapAux L (m + 1) P = P) (a c : ℕ) :
    cmAscWord q 1 (m + 1)
        (P * (auxVar (m + 1) : Total L) ^ (a + c) * (auxVar (m + 2) : Total L) ^ a)
      = (auxVar (m + 2) : Total L) ^ (a + c)
          * cmAscWord q 1 m (P * (auxVar (m + 1) : Total L) ^ a)
        - scal (q - 1) * ∑ j ∈ Finset.range c,
            (auxVar (m + 2) : Total L) ^ (a + c - 1 - j)
              * cmAscWord q 1 m (P * (auxVar (m + 1) : Total L) ^ (a + 1 + j)) := by
  have hterm : ∀ j ∈ Finset.range c,
      (auxVar (m + 2) : Total L) ^ (a + c - 1 - j) * (P * (auxVar (m + 1) : Total L) ^ (a + 1 + j))
        = P * ((auxVar (m + 1) : Total L) ^ (a + 1) * (auxVar (m + 2) : Total L) ^ a
            * ((auxVar (m + 1) : Total L) ^ j * (auxVar (m + 2) : Total L) ^ (c - 1 - j))) := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [show a + c - 1 - j = a + (c - 1 - j) by omega, pow_add, pow_add]
    ring
  have harg : P * ((auxVar (m + 1) : Total L) ^ a * (auxVar (m + 2) : Total L) ^ (a + c)
        - scal (q - 1) * ((auxVar (m + 1) : Total L) ^ (a + 1)
            * (auxVar (m + 2) : Total L) ^ a
            * ∑ j ∈ Finset.range c,
                (auxVar (m + 1) : Total L) ^ j * (auxVar (m + 2) : Total L) ^ (c - 1 - j)))
      = (auxVar (m + 2) : Total L) ^ (a + c) * (P * (auxVar (m + 1) : Total L) ^ a)
        - scal (q - 1) * ∑ j ∈ Finset.range c,
            (auxVar (m + 2) : Total L) ^ (a + c - 1 - j)
              * (P * (auxVar (m + 1) : Total L) ^ (a + 1 + j)) := by
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, Finset.mul_sum]
    ring
  rw [show P * (auxVar (m + 1) : Total L) ^ (a + c) * (auxVar (m + 2) : Total L) ^ a
        = P * ((auxVar (m + 1) : Total L) ^ (a + c) * (auxVar (m + 2) : Total L) ^ a) by ring,
    cmAscWord_one_succ_apply, braid_mul_of_swapAux_eq q hP,
    braid_auxVar_pow_mul_auxVar_pow q (i := m + 1) (by omega) a c, harg, map_sub,
    cmAscWord_scal_mul, map_sum]
  simp only [cmAscWord_one_auxVar_add_two_pow_mul]

/-! ### The power of the top variable: the recursion in closed form -/

/-- **The branching recursion on a power of the top variable**:
`T_{1↗k+1}(y_{k+1}^{n+1}) = qT_{1↗k}(y_k^{n+1}) + (q-1)∑_{j<n}y_{k+1}^{n-j}T_{1↗k}(y_k^{j+1})`, at
every width and every exponent, for every `q`.

`HJO.Sweep.cmAscWord_one_succ_mul_auxVar_pow_mul_auxVar_pow'` at `P = 1`, `a = 0`, `c = n+1`, with
the sum's top term — which is `T_{1↗k}(y_k^{n+1})` again, the power of `y_{k+1}` in it being zero —
folded into the leading term. That fold is where the `q` comes from: `1 + (q-1) = q`.

So the whole branching of the train on a power of its top variable is one recursion in the width,
carrying every smaller exponent along. At `n = 0` the sum is empty and this is the cascade
`F_k^{(1)} = qF_{k-1}^{(1)}` of `HJO.Sweep.cmAscWord_one_auxVar_last`; at `n = 1` it has one term
and is the branching of `HJO.Sweep.cmAscWord_one_auxVar_last_sq`. Unconditional in `q`. -/
theorem cmAscWord_one_succ_auxVar_last_pow_succ (q : L) (m n : ℕ) :
    cmAscWord q 1 (m + 1) ((auxVar (m + 2) : Total L) ^ (n + 1))
      = scal q * cmAscWord q 1 m ((auxVar (m + 1) : Total L) ^ (n + 1))
        + scal (q - 1) * ∑ j ∈ Finset.range n,
            (auxVar (m + 2) : Total L) ^ (n - j)
              * cmAscWord q 1 m ((auxVar (m + 1) : Total L) ^ (j + 1)) := by
  have hsw : swapAux L (m + 1) (1 : Total L) = 1 := map_one _
  have h := cmAscWord_one_succ_mul_auxVar_pow_mul_auxVar_pow' q m hsw 0 (n + 1)
  simp only [pow_zero, one_mul, zero_add, Nat.add_sub_cancel] at h
  have hq : (scal q : Total L) = 1 + scal (q - 1) := by
    rw [← scal_one (L := L), ← scal_add]
    congr 1
    ring
  have hfix : (∑ j ∈ Finset.range (n + 1), (auxVar (m + 2) : Total L) ^ (n - j)
        * cmAscWord q 1 m ((auxVar (m + 1) : Total L) ^ (1 + j)))
      = (∑ j ∈ Finset.range n, (auxVar (m + 2) : Total L) ^ (n - j)
          * cmAscWord q 1 m ((auxVar (m + 1) : Total L) ^ (j + 1)))
        + cmAscWord q 1 m ((auxVar (m + 1) : Total L) ^ (n + 1)) := by
    rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, one_mul, Nat.add_comm 1 n]
    exact congrArg (· + _) (Finset.sum_congr rfl fun j _ => by rw [Nat.add_comm 1 j])
  rw [h, hfix, hq]
  ring

/-- **`T_{1↗k+1}(y_{k+1}^{n+1}) - y_{k+1}T_{1↗k+1}(y_{k+1}^n) = qT_{1↗k}(y_k^{n+1}) -
y_{k+1}T_{1↗k}(y_k^n)`**, at every width and every exponent, for every `q`: the branching recursion
with the sum eliminated.

Subtracting `y_{k+1}` times `HJO.Sweep.cmAscWord_one_succ_auxVar_last_pow_succ` at `n` from the same
statement at `n+1` cancels the correction sums against each other and leaves a **two-term
recurrence**: the train on `y_{k+1}^{n+1}` is determined by the train on `y_{k+1}^n` at the same
width and two shorter trains. With `T_{1↗k+1}1 = 1` (`HJO.Sweep.cmAscWord_map_one`) and
`T_{1↗1} = 1` (`HJO.Sweep.cmAscWord_self_pred`) this determines every value by a double induction
and no sums appear anywhere in it.

It is the finite form of the generating-function identity
`(1-y_{k+1}z)(Φ_k - 1) = (q-y_{k+1}z)(Φ_{k-1} - 1)` for `Φ_k = ∑_nT_{1↗k+1}(y_{k+1}^n)z^n`, from
which the explicit monomial expansion is read off. Unconditional in `q`. -/
theorem cmAscWord_one_succ_auxVar_last_pow_succ_sub (q : L) (m n : ℕ) :
    cmAscWord q 1 (m + 1) ((auxVar (m + 2) : Total L) ^ (n + 1))
        - (auxVar (m + 2) : Total L) * cmAscWord q 1 (m + 1) ((auxVar (m + 2) : Total L) ^ n)
      = scal q * cmAscWord q 1 m ((auxVar (m + 1) : Total L) ^ (n + 1))
        - (auxVar (m + 2) : Total L) * cmAscWord q 1 m ((auxVar (m + 1) : Total L) ^ n) := by
  have hone : (scal (q - 1) : Total L) = scal q - 1 := by
    rw [← scal_one (L := L), ← scal_sub]
  cases n with
  | zero =>
    have h1 : cmAscWord q 1 (m + 1) ((auxVar (m + 2) : Total L) ^ 0) = 1 := by
      rw [pow_zero, cmAscWord_map_one q (by omega)]
    have h2 : cmAscWord q 1 m ((auxVar (m + 1) : Total L) ^ 0) = 1 := by
      rw [pow_zero, cmAscWord_map_one q (by omega)]
    rw [h1, h2, cmAscWord_one_succ_auxVar_last_pow_succ q m 0]
    simp
  | succ n =>
    have hsplit : (∑ j ∈ Finset.range (n + 1),
          (auxVar (m + 2) : Total L) ^ (n + 1 - j)
            * cmAscWord q 1 m ((auxVar (m + 1) : Total L) ^ (j + 1)))
        = (auxVar (m + 2) : Total L) * (∑ j ∈ Finset.range n,
            (auxVar (m + 2) : Total L) ^ (n - j)
              * cmAscWord q 1 m ((auxVar (m + 1) : Total L) ^ (j + 1)))
          + (auxVar (m + 2) : Total L)
            * cmAscWord q 1 m ((auxVar (m + 1) : Total L) ^ (n + 1)) := by
      rw [Finset.sum_range_succ, Finset.mul_sum]
      congr 1
      · refine Finset.sum_congr rfl fun j hj => ?_
        rw [Finset.mem_range] at hj
        rw [show n + 1 - j = (n - j) + 1 by omega, pow_succ]
        ring
      · rw [Nat.add_sub_cancel_left, pow_one]
    rw [cmAscWord_one_succ_auxVar_last_pow_succ q m (n + 1),
      cmAscWord_one_succ_auxVar_last_pow_succ q m n, hsplit, hone]
    ring

/-! ### The agreement checks against the three earlier shapes -/

/-- **Agreement at `n = 0`, the symmetric case.** The branching recursion's own base: the train is
the identity on `1`, at every width, which is
`HJO.Sweep.cmAscWord_one_eq_self_of_swapAux_eq` for this argument. -/
theorem cmAscWord_one_auxVar_last_pow_zero_check (q : L) (m : ℕ) :
    cmAscWord q 1 (m + 1) ((auxVar (m + 2) : Total L) ^ 0) = 1 := by
  rw [pow_zero, cmAscWord_map_one q (by omega)]

/-- **Agreement at `n = 1`.** The recursion of
`HJO.Sweep.cmAscWord_one_succ_auxVar_last_pow_succ` at `n = 0` says the train on `y_{k+1}` is `q`
times the shorter train on `y_k`, and `HJO.Sweep.cmAscWord_one_auxVar_last` evaluates
both sides: `q^{k+1}y_1 = q·q^ky_1`. A recursion emitting the wrong power of `q` — in particular one
reading the letter as multiplication by `q` on the symmetric part as well — would fail here. -/
theorem cmAscWord_one_auxVar_last_pow_one_check (q : L) (m : ℕ) :
    cmAscWord q 1 (m + 1) ((auxVar (m + 2) : Total L) ^ 1)
        = scal q * cmAscWord q 1 m ((auxVar (m + 1) : Total L) ^ 1)
      ∧ cmAscWord q 1 (m + 1) ((auxVar (m + 2) : Total L) ^ 1)
        = scal (q ^ (m + 1)) * (auxVar 1 : Total L) := by
  have hrec := cmAscWord_one_succ_auxVar_last_pow_succ q m (L := L) 0
  simp only [Finset.range_zero, Finset.sum_empty, mul_zero, add_zero, zero_add] at hrec
  refine ⟨by simpa using hrec, ?_⟩
  rw [pow_one, show m + 2 = (m + 1) + 1 from rfl, cmAscWord_one_auxVar_last q (m + 1)]

/-- **Agreement at `n = 2`, the first branching shape.** Feeding the width-`k` value of
`HJO.Sweep.cmAscWord_one_auxVar_last_sq` and of `HJO.Sweep.cmAscWord_one_auxVar_last` into the
right-hand side of `HJO.Sweep.cmAscWord_one_succ_auxVar_last_pow_succ` at `n = 1` returns the
width-`k+1` value of `HJO.Sweep.cmAscWord_one_auxVar_last_sq`.

This is the decisive check: a general formula disagreeing with
`HJO.Sweep.cmAscWord_one_auxVar_last_sq` is wrong. The two coefficients it pins are the `q^{k+1}` on
the leading square and the *single* `q^k` shared by every term of the correction — the recursion
multiplies the accumulated terms by `q` while the newly arriving one already carries `q^k`. -/
theorem cmAscWord_one_auxVar_last_sq_check (q : L) (m : ℕ) :
    scal q * cmAscWord q 1 m ((auxVar (m + 1) : Total L) ^ 2)
        + scal (q - 1) * ((auxVar (m + 2) : Total L)
            * cmAscWord q 1 m ((auxVar (m + 1) : Total L) ^ 1))
      = scal (q ^ (m + 1)) * (auxVar 1 : Total L) ^ 2
        + scal ((q - 1) * q ^ m) * ((auxVar 1 : Total L)
            * ∑ j ∈ Finset.range (m + 1), (auxVar (j + 2) : Total L)) := by
  have hpow : ∀ n : ℕ, (scal (q ^ n) : Total L) = scal q ^ n := by
    intro n
    rw [scal, scal, ← map_pow, ← map_pow]
  cases m with
  | zero =>
    have h0 : cmAscWord q 1 0 = (1 : Module.End L (Total L)) := cmAscWord_self_pred q 0
    rw [h0, Finset.sum_range_one]
    simp only [Module.End.one_apply, pow_one, pow_zero, mul_one, Nat.zero_add]
    ring
  | succ m =>
    have hlast := cmAscWord_one_auxVar_last q (L := L) (m + 1)
    have hsq := cmAscWord_one_auxVar_last_sq q (L := L) m
    have he : m + 1 + 1 = m + 2 := by omega
    rw [he] at hlast
    rw [pow_one, he, hlast, hsq]
    conv_rhs => rw [Finset.sum_range_succ]
    simp only [scal_mul, hpow]
    ring

/-! ### The other extreme: excess on the bottom variable -/

/-- **`T_{1↗k+1}(y_1^n) = y_2^n - (q-1)y_1∑_{j<n}y_1^jy_2^{n-1-j}`** for every `k ≥ 1`, every `n`
and every `q`.

The complement of the branching step. A power of `y_1` is fixed by every letter `T_2, …, T_k` — each
moves a pair of variables not containing `y_1` — so the whole train is the single letter `T_1`, read
off `HJO.Sweep.braid_auxVar_pow_mul_auxVar_pow` at `b = 0`. No cascade and no power of `q`: the
excess is already at the bottom and has nowhere to walk to. At `n = 0` both sides are `1`, and at
`n = 1` this is `T_1(y_1) = y_2 - (q-1)y_1`. -/
theorem cmAscWord_one_auxVar_one_pow (q : L) {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    cmAscWord q 1 k ((auxVar 1 : Total L) ^ n)
      = (auxVar 2 : Total L) ^ n
        - scal (q - 1) * ((auxVar 1 : Total L)
            * ∑ j ∈ Finset.range n,
                (auxVar 1 : Total L) ^ j * (auxVar 2 : Total L) ^ (n - 1 - j)) := by
  have hfix : ∀ j, 2 ≤ j → j ≤ k →
      swapAux L j ((auxVar 1 : Total L) ^ n) = (auxVar 1 : Total L) ^ n := by
    intro j hj1 _
    rw [map_pow, swapAux_auxVar_of_ne (by omega) (by omega) (by omega)]
  have hsplit : cmAscWord q 1 k = cmAscWord q 1 1 * cmAscWord q 2 k := by
    rw [cmAscWord_split q (c := 1) (by omega) hk]
  have htail : cmAscWord q 2 k ((auxVar 1 : Total L) ^ n) = (auxVar 1 : Total L) ^ n := by
    have h := cmAscWord_mul_of_swapAux_eq q (a := 2) (b := k) (by omega) hfix 1
    rwa [mul_one, cmAscWord_map_one q (by omega), mul_one] at h
  have hone : cmAscWord q 1 1 ((auxVar 1 : Total L) ^ n)
      = braid q 1 ((auxVar 1 : Total L) ^ n) := by
    rw [cmAscWord_self q 1]
    rfl
  have hletter := braid_auxVar_pow_mul_auxVar_pow q (i := 1) (L := L) le_rfl 0 n
  simp only [pow_zero, one_mul, mul_one, zero_add, pow_one,
    show (1 : ℕ) + 1 = 2 from by norm_num] at hletter
  calc cmAscWord q 1 k ((auxVar 1 : Total L) ^ n)
      = cmAscWord q 1 1 (cmAscWord q 2 k ((auxVar 1 : Total L) ^ n)) := by rw [hsplit]; rfl
    _ = braid q 1 ((auxVar 1 : Total L) ^ n) := by rw [htail, hone]
    _ = _ := by rw [hletter]

end Field

end HJO.Sweep

end
