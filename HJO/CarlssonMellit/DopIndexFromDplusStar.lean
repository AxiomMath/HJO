/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.DopFromDplusStar
public import HJO.Shuffle.MellitShiftGenerators
public import HJO.Shuffle.MellitNablaConjStarRefuted
public meta import HJO.Attr

/-! # The basic operator of index `n`, read in the module `V_*`

The general-`n` companion of `HJO.Sweep.dop_one_eq_neg_dminusCM_dplusStar`: for every `n ≥ 1` and
every `f ∈ Λ = V_0`, `ι(D_nf) = -d_-(y_1^{n-1}d^*_+(ι f))`, with the single lowering operator of
`HJO.Sweep.dminusCM` at index `1` and no condition whatsoever on `q` or `u`.

**The index is raised by a power of `y_1`, not by further raising operators.** `D_n` pairs the
`j`-th displacement coefficient `f_{[j]}` of `HJO.Sym.shiftCoeff` against `(-1)^{n+j}e_{n+j}`, and
what `d_-` pairs `y_1^i` against is `(-1)^ie_{i+1}`; so reading the displacement's `w^j`-coefficient
off the monomial `y_1^{j+n-1}` is what meets `e_{n+j}` with the sign `(-1)^{n+j-1}`, which is the
global minus. Multiplying by `y_1^{n-1}` before the *one* extraction is therefore the whole of the
step from `n = 1`, and `τ^-_{1,1}` fixes `y_1`, so the factor rides through the substitution
untouched and the displacement identity of `HJO.Sweep.qshiftNeg_cycleShift_qshift_C` is reused
verbatim.

## The proposed form with iterated `d^*_+` is refuted here

The proposed form
`ι(D_nf) = -d_-^{(n)}((d^*_+)^{n-1}(ι f))` is **false**, in both of its readings, already
at `n = 2`, `f = 1`: `HJO.Sweep.dop_two_one_ne_neg_dminusCM_dplusStar` and
`HJO.Sweep.dop_two_one_ne_neg_dminusCM_dplusStar_two`. The refutation is the cheapest one available.
`d^*_+` is built from two algebra homomorphisms, so it fixes the unit
(`HJO.Sweep.dplusStar_one`) and *every* number of applications of it to `ι 1` gives `ι 1` back;
`d_-(1) = e_1` by `HJO.Sweep.dminusCM_one`, whatever the index; and `D_2(1) = e_2` by
`HJO.Sym.dop_apply_one`. So the proposed right-hand side is `-e_1` and the left-hand side is `e_2`,
which the sign extraction `ε_±` of `HJO.Sym.signExtract` separates: `ε_±(e_2) = 1` while
`ε_±(-e_1) = -1`.

Two further facts about that form, recorded because they say *why* it fails rather than only that it
does. Its `n = 1` case is not `HJO.Sweep.dop_one_eq_neg_dminusCM_dplusStar`: with `(d^*_+)^0` the
right-hand side never sees `u` at all, whereas `D_1p_1 = -p_1e_1 + (1-q)(1-u)e_2` does. And for
`n ≥ 2` it is not even an identity between elements of `V_0`: `d_-^{(n)}` extracts the
`y_n`-expansion, so the `y_1, …, y_{n-1}` introduced by the `n-1` raising operators survive into the
value, while `ι(D_nf)` is a constant. An extra `d^*_+` adds a *letter* to the alphabet; what
`D_{n+1}` needs over `D_n` is a shift of the *pairing index*, and those are different operations.

## Main results

* `HJO.Sweep.dop_succ_eq_neg_dminusCM_auxVar_pow_dplusStar`: `ι(D_{m+1}f) = -d_-(y_1^md^*_+(ι f))`.
* `HJO.Sweep.dop_eq_neg_dminusCM_auxVar_pow_dplusStar`: the same, indexed as `n ≥ 1`.
* `HJO.Sweep.dop_succ_eq_dminus_auxVar_pow_dplusStar`: the same in the modified convention
  `HJO.Sweep.dminus`, where the sign disappears: `ι(D_{m+1}f) = d^♭_-(y_1^{m+1}d^*_+(ι f))`.
* `HJO.Sweep.dop_two_one_ne_neg_dminusCM_dplusStar`, and `..._two`: the refutation of the proposed
  form, in both readings of `(d^*_+)^{n-1}`.

## Implementation notes

**Which `d_-`.** The statements below use `HJO.Sweep.dminusCM`, Carlsson and Mellit's own lowering
operator, which pairs `F_j` with `e_{j+1}`; that is the operator the `n = 1` case
`HJO.Sweep.dop_one_eq_neg_dminusCM_dplusStar` uses. It is *not* `HJO.Sweep.dminus`, the modified
`d^♭_-` of `HJO.Sweep.dminus`, which pairs `F_j` with `e_j`. The translation is one power of `y_1`
(`HJO.Sweep.dminusCM_eq_neg_dminus_auxVar_mul`), which is why the modified form of the identity
carries `y_1^{m+1}` and no sign.

**No side condition, and in particular nothing at `q, u ∈ {0, 1}`.** Every constant in sight is a
polynomial in `q` and `u`: the substitutions of `HJO.Sweep.qshift` and `HJO.Sweep.qshiftNeg` attach
`q^r - 1`, the cyclic shift attaches `u`, and `HJO.Sym.plethShift` attaches `(1-q^r)(1-u^r)`.
Nothing is inverted, so the identity below is stated for all `q u : L` and holds at the degenerate
values `q, u ∈ {0, 1}`. It is not vacuous there either: at `q = u = 1` both substitutions degenerate
to the identity and the identity reads `D_nf = (-1)^ne_nf`, which is `f` times
`HJO.Sym.dop_apply_one`.

## References

The lemma `HJO.Sweep.dop_eq_neg_dminusCM_auxVar_pow_dplusStar` and its `n = 1`
case `HJO.Sweep.dop_one_eq_neg_dminusCM_dplusStar`, using the definitions `HJO.Sym.DopInt`,
`HJO.Sym.shiftCoeff`, `HJO.Sym.plethShift`, `HJO.Sweep.dminusCM`, `HJO.Sweep.dminus`,
`HJO.Sweep.dplusStar`, `HJO.Sym.signExtract`.
-/

@[expose] public section

open Finset

namespace HJO.Sweep

section DopIndexFromDplusStar

variable {L : Type*} [Field L] [Algebra ℚ L]

/-! ### Two facts about pairing against a family -/

omit [Algebra ℚ L] in
/-- **A power of `w` shifts the family.** The case `g = 1` of
`HJO.Sym.coeffPairing_C_mul_X_pow_mul`, in the shape the displacement is met in below. -/
theorem coeffPairing_X_pow_mul (m : ℕ) (c d : ℕ → Sym.Lambda L) (hd : ∀ i : ℕ, d i = c (i + m))
    (P : Polynomial (Sym.Lambda L)) :
    Sym.coeffPairing c (Polynomial.X ^ m * P) = Sym.coeffPairing d P := by
  have h : (Polynomial.X : Polynomial (Sym.Lambda L)) ^ m * P
      = Polynomial.C (1 : Sym.Lambda L) * Polynomial.X ^ m * P := by
    rw [map_one, one_mul]
  rw [h, Sym.coeffPairing_C_mul_X_pow_mul (1 : Sym.Lambda L) P m c d hd, one_mul]

omit [Algebra ℚ L] in
/-- **Negating the family negates the pairing.** Both sides are the same finite sum over any range
covering the support of `P`. -/
theorem coeffPairing_neg_family (c d : ℕ → Sym.Lambda L) (h : ∀ i : ℕ, c i = -d i)
    (P : Polynomial (Sym.Lambda L)) :
    Sym.coeffPairing c P = -Sym.coeffPairing d P := by
  have hzero : ∀ j : ℕ, P.natDegree + 1 ≤ j → P.coeff j = 0 := fun j hj =>
    Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  rw [Sym.coeffPairing_eq_sum_range _ _ hzero, Sym.coeffPairing_eq_sum_range _ _ hzero,
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ => by rw [h j, mul_neg]

/-! ### The identity -/

/-- **`ι(D_{m+1}f) = -d_-(y_1^md^*_+(ι f))`**, the corrected form of
`HJO.Sweep.dop_eq_neg_dminusCM_auxVar_pow_dplusStar`.

At `m = 0` this is `HJO.Sweep.dop_one_eq_neg_dminusCM_dplusStar`. The step is the factor `y_1^m`:
`τ^-_{1,1}` fixes `y_1`, so the three substitutions still compose to the plethystic displacement
transported along `w ↦ y_1` (`HJO.Sweep.qshiftNeg_cycleShift_qshift_C`) and the factor rides through
untouched; the extraction of `d_-` then reads the `w^j`-coefficient off `y_1^{j+m}` and so meets
`(-1)^{j+m}e_{j+m+1}`, which is the negative of the `(m+1)`-indexed family
`(-1)^{(m+1)+j}e_{(m+1)+j}` of `HJO.Sym.DopInt`.

No condition on `q` or `u`: nothing here divides. -/
theorem dop_succ_eq_neg_dminusCM_auxVar_pow_dplusStar (q u : L) (m : ℕ) (f : Sym.Lambda L) :
    MvPolynomial.C (Sym.Dop q u (m + 1) f)
      = -dminusCM q 1 ((auxVar 1 : Total L) ^ m *
          dplusStar q u 0 (MvPolynomial.C f : Total L)) := by
  have hav : (auxVar 1 : Total L) = MvPolynomial.X 0 := by rw [auxVar, Nat.sub_self]
  have hRHS : dminusCM q 1 ((auxVar 1 : Total L) ^ m *
        dplusStar q u 0 (MvPolynomial.C f : Total L))
      = lowerCoeffShift L 0 (Polynomial.aeval (MvPolynomial.X 0 : Total L)
          (Polynomial.X ^ m * Sym.plethShift q u f)) := by
    have hpoly : Polynomial.aeval (MvPolynomial.X 0 : Total L)
          (Polynomial.X ^ m * Sym.plethShift q u f)
        = (MvPolynomial.X 0 : Total L) ^ m *
          Polynomial.aeval (MvPolynomial.X 0 : Total L) (Sym.plethShift q u f) := by
      rw [map_mul, map_pow, Polynomial.aeval_X]
    rw [hpoly]
    change lowerCoeffShift L 0 (qshiftNeg q 1 ((auxVar 1 : Total L) ^ m *
      cycleShift u 0 (qshift q 1 (MvPolynomial.C f : Total L)))) = _
    rw [map_mul, map_pow, hav, qshiftNeg_auxVar, qshiftNeg_cycleShift_qshift_C]
  have hfam : Sym.coeffPairing
        (fun i : ℕ => (-1 : Sym.Lambda L) ^ (i + m) * Sym.elemSymm L (i + m + 1))
        (Sym.plethShift q u f) = -Sym.Dop q u (m + 1) f := by
    rw [Sym.dop_apply]
    refine coeffPairing_neg_family _ _ (fun i => ?_) _
    rw [show m + 1 + i = i + m + 1 from by omega, pow_succ]
    ring
  rw [hRHS, lowerCoeffShift_zero_aeval,
    coeffPairing_X_pow_mul m (fun j : ℕ => (-1 : Sym.Lambda L) ^ j * Sym.elemSymm L (j + 1))
      (fun i : ℕ => (-1 : Sym.Lambda L) ^ (i + m) * Sym.elemSymm L (i + m + 1))
      (fun _ => rfl),
    hfam, map_neg, neg_neg]

/-- **`ι(D_nf) = -d_-(y_1^{n-1}d^*_+(ι f))` for `n ≥ 1`**, the statement of
`HJO.Sweep.dop_succ_eq_neg_dminusCM_auxVar_pow_dplusStar` indexed from `1`. -/
@[hjo "lem_cm_dop_dminus_dplusstar"]
theorem dop_eq_neg_dminusCM_auxVar_pow_dplusStar (q u : L) {n : ℕ} (hn : 1 ≤ n)
    (f : Sym.Lambda L) :
    MvPolynomial.C (Sym.Dop q u n f)
      = -dminusCM q 1 ((auxVar 1 : Total L) ^ (n - 1) *
          dplusStar q u 0 (MvPolynomial.C f : Total L)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [show 1 + m - 1 = m from by omega, show 1 + m = m + 1 from Nat.add_comm 1 m]
  exact dop_succ_eq_neg_dminusCM_auxVar_pow_dplusStar q u m f

/-- **The identity in the modified convention**: `ι(D_{m+1}f) = d^♭_-(y_1^{m+1}d^*_+(ι f))`, with
the `d^♭_-` of `HJO.Sweep.dminus` and no sign.

The two lowering operators differ by one power of `y_1` and a sign
(`HJO.Sweep.dminusCM_eq_neg_dminus_auxVar_mul`), so absorbing the power into the operator is exactly
what removes the minus. This is the form that makes the index bookkeeping visible: the modified
extraction pairs `y_1^i` with `e_i`, and `D_{m+1}` reads the `j`-th displacement coefficient against
`e_{m+1+j}`, which is the `y_1`-exponent `j + m + 1` the left factor supplies. -/
theorem dop_succ_eq_dminus_auxVar_pow_dplusStar (q u : L) (m : ℕ) (f : Sym.Lambda L) :
    MvPolynomial.C (Sym.Dop q u (m + 1) f)
      = dminus q 1 ((auxVar 1 : Total L) ^ (m + 1) *
          dplusStar q u 0 (MvPolynomial.C f : Total L)) := by
  have hbridge := dminusCM_eq_neg_dminus_auxVar_mul q 0
    ((auxVar 1 : Total L) ^ m * dplusStar q u 0 (MvPolynomial.C f : Total L))
  norm_num at hbridge
  rw [dop_succ_eq_neg_dminusCM_auxVar_pow_dplusStar, hbridge, neg_neg, ← mul_assoc,
    show (auxVar 1 : Total L) * (auxVar 1 : Total L) ^ m = (auxVar 1 : Total L) ^ (m + 1) from by
      rw [pow_succ]; ring]

/-! ### The proposed form with iterated `d^*_+` is false -/

omit [Algebra ℚ L] in
/-- `d^*_+` fixes the unit, being a composite of two algebra homomorphisms. So does every iterate of
it, which is what makes `f = 1` refute the proposed form at every reading of `(d^*_+)^{n-1}`. -/
theorem dplusStar_one (q u : L) (k : ℕ) : dplusStar q u k (1 : Total L) = 1 := by
  rw [dplusStar_apply, map_one, map_one]

/-- **`ε_±` separates `e_2` from `-e_1`.** The sign extraction of `HJO.Sym.signExtract` is `1` on
`e_2` (`HJO.Sym.signExtract_elemSymm_two`) and `1` on `e_1 = p_1`, so were the two equal the base
field would satisfy `1 = -1`; it is a `ℚ`-algebra. -/
theorem elemSymm_two_ne_neg_elemSymm_one : Sym.elemSymm L 2 ≠ -Sym.elemSymm L 1 := by
  intro h
  have hchar : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  have hX : Sym.signExtract L (MvPolynomial.X 0 : Sym.Lambda L) = 1 := by simp [Sym.signExtract]
  have h2 := congrArg (Sym.signExtract L) h
  rw [Sym.signExtract_elemSymm_two, map_neg, Sym.elemSymm_one_eq_X, hX] at h2
  have h3 : (2 : L) = 0 := by linear_combination h2
  exact absurd h3 (by norm_num)

/-- **The proposed right-hand side is wrong, in its literal reading.** At `n = 2`,
`f = 1` the value of `-d_-^{(2)}((d^*_+)^1(ι 1))` is `-ι(e_1)` while `ι(D_2 1) = ι(e_2)`.

`d^*_+` fixes `1`, `d_-` sends `1` to `e_1` at every index, and `D_2 1 = e_2`; the two symmetric
functions are separated by `ε_±`. -/
theorem dop_two_one_ne_neg_dminusCM_dplusStar (q u : L) :
    MvPolynomial.C (Sym.Dop q u 2 (1 : Sym.Lambda L))
      ≠ -dminusCM q 2 (dplusStar q u 0 (MvPolynomial.C (1 : Sym.Lambda L) : Total L)) := by
  intro h
  have hd2 : dminusCM q 2 (1 : Total L) = MvPolynomial.C (Sym.elemSymm L 1) := dminusCM_one q 1
  rw [MvPolynomial.C_1, dplusStar_one, hd2, Sym.dop_apply_one, ← map_neg] at h
  have h2 : (-1 : Sym.Lambda L) ^ 2 * Sym.elemSymm L 2 = -Sym.elemSymm L 1 :=
    MvPolynomial.C_injective ℕ (Sym.Lambda L) h
  rw [show (-1 : Sym.Lambda L) ^ 2 = 1 from by ring, one_mul] at h2
  exact elemSymm_two_ne_neg_elemSymm_one h2

/-- **And it is wrong in the other reading too**, where `(d^*_+)^{n-1}` is read as the `n`
applications the `n = 1` case would need: `-d_-^{(2)}((d^*_+)^2(ι 1))` is also `-ι(e_1)`,
since `d^*_+` fixes the unit however often it is applied. -/
theorem dop_two_one_ne_neg_dminusCM_dplusStar_two (q u : L) :
    MvPolynomial.C (Sym.Dop q u 2 (1 : Sym.Lambda L))
      ≠ -dminusCM q 2 (dplusStar q u 1
          (dplusStar q u 0 (MvPolynomial.C (1 : Sym.Lambda L) : Total L))) := by
  intro h
  rw [MvPolynomial.C_1, dplusStar_one, dplusStar_one] at h
  exact dop_two_one_ne_neg_dminusCM_dplusStar q u (by rw [MvPolynomial.C_1, dplusStar_one]; exact h)

end DopIndexFromDplusStar

end HJO.Sweep
