/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Collinear.HAlphabet
public import HJO.Shuffle.MellitLhsCompInduction

/-! # Newton's identity for the axis generators: `h_A` on `U_1, …, U_A`

`HJO.Sym.adjoin_axisGen_eq_top` says the axis generators of `HJO.Sym.axisGen` generate `Λ`, and
`HJO.Sym.axisSub_bijective` says they generate it *freely*, so every `h_A` is a polynomial in
`U_1, …, U_A` — but no expansion was available above degree two, where
`HJO.Sym.elemSymm_two_eq_axisGen` gives `(v+1)e_2 = U_1^2 + vU_2`. Computing one degree at a time
is hopeless: the expansion of `h_A` has one monomial per partition of `A` (see the term counts
below), so there is no short *closed* form to write down.

What there is instead is a **one-step recursion**, and it is the content of this file:

  `(1 - v^A) h_A = (v - 1)v^{A-1} ∑_{s=1}^{A} h_{A-s} U_s`,   `v = qu`.

This is Newton's identity with the axis generators in place of the power sums. It determines every
`h_A` from `h_0 = 1` by one convolution, and — since the sum reads `h_{A-s}`, not the expansion of
`h_{A-s}` — it is a recursion in one variable with no auxiliary family.

## The route

The two halves of the identity are already in `HJO/Collinear/HAlphabet.lean`.

* `HJO.Sym.completeHomog_of_add` is the Cauchy product: if `χ(p_j) = φ(p_j) + ψ(p_j)` on every
  generator then `χ(h_n) = ∑_{s} φ(h_{n-s})ψ(h_s)`. Applied to the *identity* map split as
  "scale `p_j` by `v^j`" plus `HJO.Sym.plethDilate` — which is exactly the split
  `1 = v^j + (1 - v^j)` on each generator — it gives
  `HJO.Sym.completeHomog_eq_sum_plethDilate`, an unconditional convolution with no inverse in it.

* `HJO.Sym.sum_alternating_pow_completeHomog_mul_elemSymm` with
  `HJO.Sym.completeHomog_dilate` identifies the dilated `h_k` with the axis generator:
  `plethDilate v (h_k) = (v-1)v^{k-1} U_k` for `k ≥ 1`. Substituting it and peeling the `s = 0`
  term — which is `v^A h_A`, the only place the recursion's own left side appears — gives
  `HJO.Sym.completeHomog_smul_eq_sum_axisGen`.

## What is checked against what

`HJO.Sym.completeHomog_two_smul_eq_axisGen` derives the degree-two case from
`HJO.Sym.elemSymm_two_eq_axisGen` and `HJO.Sym.completeHomog_two_add_elemSymm_two` — the *existing*
degree-two expansion, which knows nothing about the convolution — and
`HJO.Sym.completeHomog_two_smul_eq_axisGen_of_recursion` derives it from the recursion above. The
two agree, which is the consistency check on the recursion's normalisation: a sign or an off-by-one
in the peeled `s = 0` term would separate them.

## Genericity

`HJO.Sym.diagScale_pow_completeHomog` and `HJO.Sym.completeHomog_eq_sum_plethDilate`: **none**.
Both are identities of polynomial expressions in `v`, with no inverse anywhere, and they hold at
`v = 0` and `v = 1` as well.

`HJO.Sym.completeHomog_smul_eq_sum_axisGen`, `HJO.Sym.completeHomog_two_smul_eq_axisGen` and
`HJO.Sym.completeHomog_two_smul_eq_axisGen_of_recursion`: `v ≠ 0` and `v ≠ 1`, both
`HJO.Sym.axisGen_one`'s and `HJO.Sym.sum_alternating_pow_completeHomog_mul_elemSymm`'s. They are the
inverse-becomes-zero hazard of `HJO.Sym.axisGen`, whose normalising scalar is `v/(v-1)`: in a field
`0⁻¹ = 0`, so at `v = 1` that scalar collapses and `U_k` is the zero element
(`HJO.Sym.axisGen_eq_zero`), and at `v = 0` the plethystic substitution inside `HJO.Sym.axisGen`
sends every `p_j` to `-p_j`. At either value the statements below are false rather than vacuous, so
the hypotheses are carried in the statement and not hidden in a definition. At `v = qu` they read
`q ≠ 0`, `u ≠ 0` and `qu ≠ 1`.

The recursion needs no hypothesis beyond those: the scalar `1 - v^A` on the left is *not* inverted,
so `v^A = 1` makes the identity trivially true rather than false, and it is only when one wants
`h_A` itself that `v` must avoid the `A`-th roots of unity — which is exactly what
`HJO.Sym.adjoin_axisGen_eq_top` already spends.

## What this does not give

There is no compact closed form in `A`, and the recursion is the honest answer rather than a step
towards one. Run outside Lean, it expands `h_A` into `1, 2, 3, 5, 7, 11, 15` monomials in the `U_k`
at `A = 1, …, 7` — the partition numbers `p(A)`, with no cancellation — over the common denominator
`∏_{k=2}^{A}(1 + v + ⋯ + v^{k-1})`. So the expansion is dense in the partitions of `A`, and a
statement quantified over `A` has to be the recursion or nothing.

## References

This file is about `HJO.Sym.axisGen`, `HJO.Sym.completeHomog` and `HJO.Sym.elemSymm`, and proves
`HJO.Sym.sum_alternating_pow_completeHomog_mul_elemSymm`,
`HJO.Sym.sum_alternating_completeHomog_mul_elemSymm`, `HJO.Sym.axisGen_one` and
`HJO.Sym.axisSub_bijective`.
-/

@[expose] public section

namespace HJO.Sym

open Finset

variable {L : Type*} [Field L] [Algebra ℚ L]

/-! ### The scaling half of the split -/

/-- **`h_m` under the substitution `p_j ↦ v^j p_j` is `v^m h_m`.** The substitution is diagonal and
`h_m` is weighted homogeneous of degree `m` (`HJO.Sym.completeHomog_mem_lambdaComp`), so
`HJO.Sym.diagScale_pow_smul_of_mem_lambdaComp` at the trivial diagonal reads off the single scalar.

No hypothesis on `v`; at `v = 0` both sides are `0` for `m ≥ 1`. -/
theorem diagScale_pow_completeHomog (v : L) (m : ℕ) :
    diagScale (fun i => v ^ (i + 1)) (completeHomog L m)
      = MvPolynomial.C (v ^ m) * completeHomog L m := by
  have h1 : (fun i : ℕ => v ^ (i + 1)) = fun i : ℕ => v ^ (i + 1) * (1 : L) := by
    funext i; rw [mul_one]
  have hid : diagScale (fun _ : ℕ => (1 : L)) = AlgHom.id L (Lambda L) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    rw [diagScale, MvPolynomial.aeval_X, MvPolynomial.C_1, one_mul, AlgHom.id_apply]
  rw [h1, diagScale_pow_smul_of_mem_lambdaComp v _ (completeHomog_mem_lambdaComp L m), hid]
  rfl

/-! ### The unconditional convolution -/

/-- **`h_A = ∑_{s=0}^{A} v^{A-s} h_{A-s} · (dilate v)(h_s)`.**

The identity map on `Λ` sends `p_j` to `v^j p_j + (1 - v^j) p_j`, the first summand being
`HJO.Sym.diagScale_pow_completeHomog`'s substitution and the second `HJO.Sym.plethDilate`. So
`HJO.Sym.completeHomog_of_add` — the Cauchy product of the two `h`-series — applies with `χ` the
identity, and the convolution is an expansion of `h_A` itself rather than of its image.

**No hypothesis on `v`, and no inverse in the statement.** This is the form the recursion below is
extracted from, and it is the reason the recursion inherits nothing from `HJO.Sym.axisGen`'s
normalisation except through the axis generators it names. -/
theorem completeHomog_eq_sum_plethDilate (v : L) (A : ℕ) :
    completeHomog L A
      = ∑ s ∈ range (A + 1), MvPolynomial.C (v ^ (A - s)) * completeHomog L (A - s) *
          plethDilate v (completeHomog L s) := by
  have hadd : ∀ i : ℕ, (AlgHom.id L (Lambda L)) (MvPolynomial.X i)
      = (diagScale (fun j => v ^ (j + 1))) (MvPolynomial.X i)
        + (plethDilate v) (MvPolynomial.X i) := by
    intro i
    rw [AlgHom.id_apply, diagScale, MvPolynomial.aeval_X, plethDilate_X, MvPolynomial.C_sub,
      MvPolynomial.C_1]
    ring
  have h := completeHomog_of_add (K := L) (R := Lambda L)
    (diagScale (fun j => v ^ (j + 1))) (plethDilate v) (AlgHom.id L (Lambda L)) hadd A
  rw [AlgHom.id_apply] at h
  rw [h]
  exact Finset.sum_congr rfl fun s _ => by rw [diagScale_pow_completeHomog v (A - s)]

/-! ### Newton's identity for the axis generators -/

/-- **`(1 - v^A) h_A = (v-1)v^{A-1} ∑_{s=1}^{A} h_{A-s} U_s`** — the one-step recursion that
determines `h_A` on the axis generators of `HJO.Sym.axisGen`.

`HJO.Sym.completeHomog_eq_sum_plethDilate` is the convolution; `plethDilate v (h_s)` is
`(v-1)v^{s-1} U_s` for `s ≥ 1` by `HJO.Sym.completeHomog_dilate` and
`HJO.Sym.sum_alternating_pow_completeHomog_mul_elemSymm`; and the `s = 0` term is `v^A h_A`, which
moved to the left is the scalar `1 - v^A`. The weights collapse because
`v^{A-s}·(v-1)v^{s-1} = (v-1)v^{A-1}` for every `1 ≤ s ≤ A`, so one scalar comes out of the whole
sum.

The sum is written over `range A` with the shift `s ↦ s+1`, which is the same range `1, …, A`; at
`A = 0` it is empty and both sides are `0`.

Genericity: `v ≠ 0` and `v ≠ 1`, `HJO.Sym.sum_alternating_pow_completeHomog_mul_elemSymm`'s, each
the inverse-becomes-zero hazard of `HJO.Sym.axisGen`'s scalar `v/(v-1)`; at `v = qu` they read
`q ≠ 0`, `u ≠ 0`, `qu ≠ 1`. Nothing here inverts `1 - v^A`. -/
theorem completeHomog_smul_eq_sum_axisGen {v : L} (hv0 : v ≠ 0) (hv1 : v ≠ 1) (A : ℕ) :
    (1 - v ^ A) • completeHomog L A
      = ((v - 1) * v ^ (A - 1)) •
          ∑ s ∈ range A, completeHomog L (A - (s + 1)) * axisGen v (s + 1) := by
  rw [MvPolynomial.smul_eq_C_mul]
  have hW : ∀ k : ℕ, 1 ≤ k → plethDilate v (completeHomog L k)
      = MvPolynomial.C ((v - 1) * v ^ (k - 1)) * axisGen v k := fun k hk => by
    rw [completeHomog_dilate v (plethDilate v) (plethDilate_X v) k,
      sum_alternating_pow_completeHomog_mul_elemSymm hv0 hv1 hk]
  have hterm : ∀ s ∈ range A,
      MvPolynomial.C (v ^ (A - (s + 1))) * completeHomog L (A - (s + 1)) *
          plethDilate v (completeHomog L (s + 1))
        = MvPolynomial.C ((v - 1) * v ^ (A - 1)) *
          (completeHomog L (A - (s + 1)) * axisGen v (s + 1)) := by
    intro s hs
    rw [hW (s + 1) (by omega), Nat.add_sub_cancel]
    have hexp : v ^ (A - (s + 1)) * ((v - 1) * v ^ s) = (v - 1) * v ^ (A - 1) := by
      have hsA : A - (s + 1) + s = A - 1 := by have := Finset.mem_range.1 hs; omega
      rw [show (v - 1) * v ^ (A - 1)
          = (v - 1) * (v ^ (A - (s + 1)) * v ^ s) from by rw [← pow_add, hsA]]
      ring
    calc MvPolynomial.C (v ^ (A - (s + 1))) * completeHomog L (A - (s + 1)) *
            (MvPolynomial.C ((v - 1) * v ^ s) * axisGen v (s + 1))
        = MvPolynomial.C (v ^ (A - (s + 1))) * MvPolynomial.C ((v - 1) * v ^ s) *
            (completeHomog L (A - (s + 1)) * axisGen v (s + 1)) := by ring
      _ = MvPolynomial.C ((v - 1) * v ^ (A - 1)) *
            (completeHomog L (A - (s + 1)) * axisGen v (s + 1)) := by
          rw [← MvPolynomial.C_mul, hexp]
  have hm := completeHomog_eq_sum_plethDilate (L := L) v A
  rw [Finset.sum_range_succ', Nat.sub_zero, CopPower.completeHomog_zero, map_one, mul_one,
    Finset.sum_congr rfl hterm, ← Finset.mul_sum] at hm
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_sub, MvPolynomial.C_1]
  linear_combination hm

/-! ### Degree two, twice -/

/-- **`(v+1)h_2 = v(U_1^2 - U_2)`**, from the *existing* degree-two data.

`HJO.Sym.elemSymm_two_eq_axisGen` gives `(v+1)e_2 = e_1^2 + vU_2`,
`HJO.Sym.completeHomog_two_add_elemSymm_two` gives `h_2 = e_1^2 - e_2`, and
`HJO.Sym.axisGen_one` gives `U_1 = -e_1`, so `U_1^2 = e_1^2`. Nothing about the convolution enters,
which is what makes this an independent check on
`HJO.Sym.completeHomog_two_smul_eq_axisGen_of_recursion`.

The scalar `v + 1` is not inverted here; a form solved for `h_2` would need `v ≠ -1` as well.

Genericity: `v ≠ 0`, `v ≠ 1`, `HJO.Sym.axisGen_one`'s. -/
theorem completeHomog_two_smul_eq_axisGen {v : L} (hv0 : v ≠ 0) (hv1 : v ≠ 1) :
    (v + 1) • completeHomog L 2 = v • (axisGen v 1 ^ 2 - axisGen v 2) := by
  have hA := elemSymm_two_eq_axisGen (L := L) hv0 hv1
  have hB := completeHomog_two_add_elemSymm_two L
  have hC : (MvPolynomial.C (v + 1) : Lambda L) = MvPolynomial.C v + 1 := by
    rw [MvPolynomial.C_add, MvPolynomial.C_1]
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, axisGen_one hv0 hv1]
  linear_combination (MvPolynomial.C (v + 1) : Lambda L) * hB - hA + (elemSymm L 1 ^ 2) * hC

/-- **The same degree-two identity, read off the recursion.** At `A = 2` the sum of
`HJO.Sym.completeHomog_smul_eq_sum_axisGen` has the two terms `h_1U_1` and `h_0U_2 = U_2`, and
`HJO.Sym.axisGen_one` turns `h_1 = e_1` into `-U_1`; the scalar `1 - v^2` factors as `(1-v)(1+v)`
against the recursion's `(v-1)v`, and cancelling the `1 - v` — which is where `v ≠ 1` is spent a
second time — leaves `(v+1)h_2 = v(U_1^2 - U_2)`.

That this agrees with `HJO.Sym.completeHomog_two_smul_eq_axisGen`, proved from the existing
degree-two expansion by a route that never mentions the convolution, is the consistency check on the
recursion: a lost sign, or an off-by-one in the peeled `s = 0` term, would show up here.

Genericity: `v ≠ 0`, `v ≠ 1`. -/
theorem completeHomog_two_smul_eq_axisGen_of_recursion {v : L} (hv0 : v ≠ 0) (hv1 : v ≠ 1) :
    (v + 1) • completeHomog L 2 = v • (axisGen v 1 ^ 2 - axisGen v 2) := by
  have h := completeHomog_smul_eq_sum_axisGen (L := L) hv0 hv1 2
  rw [Finset.sum_range_succ, Finset.sum_range_one] at h
  rw [show (2 : ℕ) - (0 + 1) = 1 from rfl, show (2 : ℕ) - (1 + 1) = 0 from rfl,
    CopPower.completeHomog_zero, one_mul,
    show completeHomog L 1 = -axisGen v 1 from by
      rw [axisGen_one hv0 hv1, neg_neg, CopPower.completeHomog_one, CopPower.powerSum_one,
        elemSymm_one_eq_X],
    show (0 + 1 : ℕ) = 1 from rfl, show (1 + 1 : ℕ) = 2 from rfl,
    show -axisGen v 1 * axisGen v 1 + axisGen v 2
      = -(axisGen v 1 ^ 2 - axisGen v 2) from by ring,
    smul_neg, ← neg_smul, show -((v - 1) * v ^ 1) = (1 - v) * v from by ring] at h
  have hv : (1 : L) - v ≠ 0 := sub_ne_zero_of_ne fun hc => hv1 hc.symm
  refine smul_right_injective (Lambda L) hv ?_
  change (1 - v) • ((v + 1) • completeHomog L 2)
    = (1 - v) • (v • (axisGen v 1 ^ 2 - axisGen v 2))
  rw [smul_smul, smul_smul, show (1 - v) * (v + 1) = 1 - v ^ 2 from by ring, h]

end HJO.Sym
