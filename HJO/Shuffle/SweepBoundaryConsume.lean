/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepBoundaryWidthSharp
public import HJO.Shuffle.CornerClosedForm
public import HJO.CMStructure.YBraid
public meta import HJO.Attr

/-!
# The round boundary: the staircase is **consumed**, not commuted

Four routes through the inter-round boundary are refuted, each with a witness: re-blocking
(`HJO.Sweep.not_dplus_shiftAux_mul_of_mem_piece`), carrying the correction outward
(`HJO.Mellit.not_tailRoundWord_stairWord_bound`), round-local passing, and — sharply —
commutation at the one-unit-weaker bound
(`HJO.Mellit.not_sweepOperatorShifted_stairWord_of_add_le`). Every one of those asks for the
staircase to come out of the layer **unchanged**, as `S' ∘ TL` reached from `TL ∘ S` by a
commutation. This file does the opposite: it evaluates `TL ∘ S` directly, and the staircase does
not come out at all.

## The identity

For every `m` and every `v ∈ V_{m+1}`, whenever `q ≠ 0` and `q ≠ 1`,

`Δ^{(m+1)}(S_{0,m} v) = -q^m · y_1 v`,

where `S_{0,m} = HJO.Sweep.stairWord q 1 0 m` is the staircase at `δ = 1`, the descending word
`T_m T_{m-1} ⋯ T_1` — `HJO.Mellit.stairWord_one_one_zero` is its height-one case. The right-hand
side carries **no staircase**: the arriving correction has been absorbed into a single power of `q`,
and `-y_1·` is the tail's own operator at width `1`
(`HJO.Sweep.corner_eq_neg_cmAscWord_auxVar_mul` at `m = 0`). That is
`HJO.Sweep.corner_stairWord_consume` below, and in two-block form, with the base's block carried
along untouched, `HJO.Sweep.corner_stairWord_consume_shiftAux`.

## Why this is the case commutation cannot reach, and not an easier one

`HJO.Sweep.corner_stairWord` passes a staircase through `Δ^{(n)}` under `c + m + δ + 1 ≤ n`, i.e.
`n ≥ m + δ + 1` at offset `0`. The identity here is read at

`n = m + δ`

exactly — one unit *below* what commutation needs, and by
`HJO.Mellit.not_sweepOperatorShifted_stairWord_of_add_le` that unit cannot be recovered: at
`δ = m = 1`, `n = 2` the commuted identity is **false** on `y_1`, for every `q ≠ 1`. So the two
statements are not competing proofs of one fact. They cover complementary ranges of `n`, and the
round boundary lands in the range commutation does not have.

The mechanism is one relation of the braid system, `HJO.Sweep.braid_auxVar_succ_mul_braid`
(`HJO.Sweep.cmAscWord_mul_mulLeft_auxVar_mul_stairWord`): `T_i(y_{i+1}T_iF) = qy_iF`, which in the
endomorphism monoid is `HJO.Sweep.braidEnd_mul_mulLeft_auxVar_succ_mul_braidEnd`. Each letter of the
staircase meets the matching letter of the ascending word `T_{[1,m]}` that
`HJO.Sweep.corner_eq_neg_cmAscWord_auxVar_mul` puts in front of the corner, and the pair collapses
to `q` times a multiplication operator one index lower. Running that `m` times is
`HJO.Sweep.cmAscWord_mul_mulLeft_auxVar_mul_stairWord`, an identity of endomorphisms with **no
hypothesis on `q` and none on the vector** — the two conditions of the corner identity come only
from the closed form it is fed into.

## What this does and does not settle

The identity is `δ = 1` throughout. At `δ ≥ 2` the same computation leaves a residual braid word
behind rather than a scalar, so the absorption is partial and the statement below does not
generalise as it stands; `δ = 1` is the shape the `a = 1` band identity was closed with, and on the
smallest instance with `1 < a < b` and a genuine tail it is the whole story at one of the four
ordered pairs (`HJO.Mellit.card_tailLiveSteps_baseTwoThreeB_const`).

What the round boundary additionally needs, and what this file does **not** supply, is the
arithmetic that the operator index at the arrival point really is `m + 1`: the tail's own width
there must be `1` and the base's live count `β` must equal the arriving staircase's height `m`. That
is a statement about the two rectangles, not about the operators, and it is where the remaining
obstruction lives.

## References

A. Mellit, *Toric braids and `(m, n)`-parking functions*, sections 4 and 6, for
`HJO.Sweep.stairWord`, `HJO.Sweep.corner`, `HJO.Sweep.cmAscWord_mul_mulLeft_auxVar_mul_stairWord`,
`HJO.Sweep.cmAscWord_split` and `HJO.Mellit.sweepOperator`.
-/

@[expose] public section

namespace HJO.Sweep

open Finset

variable {L : Type*} [Field L] [Algebra ℚ L] {q : L}

/-! ### The staircase at `δ = 1` stays inside the graded piece -/

omit [Algebra ℚ L] in
/-- **The staircase at `δ = 1` preserves `V_k` as soon as its top letter is inside**:
`S_{c,m} = T_{c+m} ⋯ T_{c+1}` is a word in `T_{c+1}, …, T_{c+m}`, and each of those maps `V_k` to
`V_k` for `c + m < k` (`HJO.Sweep.braid_mem_piece`). -/
theorem stairWord_one_mem_piece (q : L) (k c : ℕ) :
    ∀ m : ℕ, c + m < k → ∀ {v : Total L}, v ∈ piece L k → stairWord q 1 c m v ∈ piece L k := by
  intro m
  induction m with
  | zero => intro _ v hv; simpa using hv
  | succ n ih =>
    intro hn v hv
    rw [stairWord_succ_apply, cmAscWord_self]
    exact braid_mem_piece q (by omega) (by omega) (ih (by omega) hv)

/-! ### THE ABSORPTION, as an identity of endomorphisms -/

omit [Algebra ℚ L] in
/-- **THE STAIRCASE IS EATEN BY THE ASCENDING WORD OF THE CORNER'S CLOSED FORM.** For every `m`,

`T_{[1,c+m]} ∘ y_{c+m+1}· ∘ S_{c,m} = q^m · T_{[1,c]} ∘ y_{c+1}·`

as endomorphisms of the total space, where `S_{c,m} = HJO.Sweep.stairWord q 1 c m` is the staircase
at `δ = 1`, the descending word `T_{c+m} ⋯ T_{c+1}`. **No hypothesis on `q`, and none on the
vector**: this is `m` applications of the one braid relation
`HJO.Sweep.braidEnd_mul_mulLeft_auxVar_succ_mul_braidEnd`, each of which consumes the outermost
letter `T_{c+m}` of the ascending word against the outermost letter of the staircase and lowers the
multiplication operator by one index. The absorption stops exactly when the staircase runs out, at
`y_{c+1}`, which is why the **offset** is what decides the index the identity lands on.

This is the whole computational content of the round-boundary absorption. The corner operator enters
only through `HJO.Sweep.corner_eq_neg_cmAscWord_auxVar_mul`, which is what puts
`T_{[1,m]}(y_{m+1}·)` in front of `Δ^{(m+1)}`. -/
@[hjo "lem_cm_braid_y_conj"]
theorem cmAscWord_mul_mulLeft_auxVar_mul_stairWord (q : L) (c m : ℕ) :
    cmAscWord q 1 (c + m) * LinearMap.mulLeft L (auxVar (c + m + 1) : Total L)
        * stairWord q 1 c m
      = q ^ m • (cmAscWord q 1 c * LinearMap.mulLeft L (auxVar (c + 1) : Total L)) := by
  induction m with
  | zero => rw [stairWord_zero, pow_zero, one_smul, mul_one, Nat.add_zero]
  | succ n ih =>
    have hsplit : cmAscWord q 1 (c + (n + 1))
        = cmAscWord q 1 (c + n) * braidEnd q (c + n + 1) := by
      rw [cmAscWord_split q (a := 1) (b := c + (n + 1)) (c := c + n) (by omega) (by omega),
        show c + n + 1 = c + (n + 1) from by omega, cmAscWord_self]
    have hstair : stairWord q 1 c (n + 1) = braidEnd q (c + n + 1) * stairWord q 1 c n := by
      rw [stairWord_succ, cmAscWord_self]
    have hy : braidEnd q (c + n + 1) * LinearMap.mulLeft L (auxVar (c + n + 1 + 1) : Total L)
        * braidEnd q (c + n + 1) = q • LinearMap.mulLeft L (auxVar (c + n + 1) : Total L) :=
      braidEnd_mul_mulLeft_auxVar_succ_mul_braidEnd q (by omega)
    calc cmAscWord q 1 (c + (n + 1))
            * LinearMap.mulLeft L (auxVar (c + (n + 1) + 1) : Total L) * stairWord q 1 c (n + 1)
        = cmAscWord q 1 (c + n) * (braidEnd q (c + n + 1)
            * LinearMap.mulLeft L (auxVar (c + n + 1 + 1) : Total L) * braidEnd q (c + n + 1))
            * stairWord q 1 c n := by
          rw [hsplit, hstair, show c + (n + 1) + 1 = c + n + 1 + 1 from by omega]
          simp only [mul_assoc]
      _ = q • (cmAscWord q 1 (c + n) * LinearMap.mulLeft L (auxVar (c + n + 1) : Total L)
            * stairWord q 1 c n) := by
          rw [hy, mul_smul_comm, smul_mul_assoc]
      _ = q ^ (n + 1) • (cmAscWord q 1 c * LinearMap.mulLeft L (auxVar (c + 1) : Total L)) := by
          rw [ih, smul_smul, ← pow_succ']

/-- **THE CONSUMING IDENTITY, in closed form.** For every offset `c`, every height `m` and every
`v ∈ V_{c+m+1}`, whenever `q ≠ 0` and `q ≠ 1`,

`Δ^{(c+m+1)}(S_{c,m} v) = -q^m · T_{[1,c]}(y_{c+1} v)`,

with `S_{c,m} = HJO.Sweep.stairWord q 1 c m` the staircase at `δ = 1`, the descending word
`T_{c+m} ⋯ T_{c+1}`. The right-hand side carries **no staircase**: the arriving correction has been
absorbed into the single scalar `q^m`, and what is left is the closed form of
`HJO.Sweep.corner_eq_neg_cmAscWord_auxVar_mul` read at the index `c + 1` rather than `c + m + 1` —
that is, the operator at an index **lowered by exactly the height of the staircase it ate**.

Read against `HJO.Sweep.corner_stairWord`, which needs `c + m + δ + 1 ≤ n` to *commute* the
staircase out, this is the index `n = c + m + δ` one unit lower, and
`HJO.Mellit.not_sweepOperatorShifted_stairWord_of_add_le` shows commutation there is false. So the
two statements are not competing proofs of one fact; they cover complementary ranges of `n`, and the
round boundary lands in the range commutation does not have.

Both hypotheses come from the closed form
`HJO.Sweep.corner_eq_neg_cmAscWord_auxVar_mul`: `q ≠ 1` for the `(q-1)^{-1}` of `HJO.Sweep.corner`,
`q ≠ 0` for the commutator identity
`HJO.Sweep.dplus_dminus_sub_dminus_dplus` it divides. The absorption itself
(`HJO.Sweep.cmAscWord_mul_mulLeft_auxVar_mul_stairWord`) needs neither. -/
@[hjo "lem_sweep_corner_stair_consume"]
theorem corner_stairWord_consume (hq0 : q ≠ 0) (hq1 : q ≠ 1) (c m : ℕ) {v : Total L}
    (hv : v ∈ piece L (c + m + 1)) :
    corner q (c + m + 1) (stairWord q 1 c m v)
      = -(q ^ m • cmAscWord q 1 c ((auxVar (c + 1) : Total L) * v)) := by
  have hmem : stairWord q 1 c m v ∈ piece L (c + m + 1) :=
    stairWord_one_mem_piece q (c + m + 1) c m (by omega) hv
  rw [corner_eq_neg_cmAscWord_auxVar_mul hq0 hq1 (c + m) hmem]
  congr 1
  have h := congrArg (fun T : Module.End L (Total L) => T v)
    (cmAscWord_mul_mulLeft_auxVar_mul_stairWord q c m)
  simpa only [Module.End.mul_apply, LinearMap.mulLeft_apply, LinearMap.smul_apply] using h

/-- **THE CONSUMING IDENTITY AS A STATEMENT ABOUT THE TAIL'S OWN OPERATOR.** On the tail's own
graded piece `V_{c+1}` — which is where the tail's own partially computed vector lives — the closed
form of `HJO.Sweep.corner_stairWord_consume` **is** the corner operator at the tail's own index:

`Δ^{(c+m+1)}(S_{c,m} v) = q^m · Δ^{(c+1)}(v)` for `v ∈ V_{c+1}`.

This is the shape the round boundary asks for. The raised operator of
`HJO.Mellit.sweepOperatorShifted` at a type-`C` tail point is read at `k^w(p) + β`; if the arriving
staircase has **offset `c = k^w(p) - 1` and height `m = β`**, then precomposing with it returns the
tail's *own* event operator at its own width, times `q^β`, and the correction is gone. Neither
condition is supplied here: they are statements about the two rectangles, not about the operators.

The hypothesis `v ∈ V_{c+1}` is sharp and not a convenience — on the larger piece `V_{c+m+1}` the
right-hand side is the closed form of `HJO.Sweep.corner_stairWord_consume` and is **not**
`q^mΔ^{(c+1)}v`, since `Δ^{(c+1)}` is only the multiplication-and-word of its closed form on the
piece it is read on. -/
@[hjo "lem_sweep_corner_stair_consume"]
theorem corner_stairWord_consume_of_mem_piece (hq0 : q ≠ 0) (hq1 : q ≠ 1) (c m : ℕ) {v : Total L}
    (hv : v ∈ piece L (c + 1)) :
    corner q (c + m + 1) (stairWord q 1 c m v) = q ^ m • corner q (c + 1) v := by
  have hv' : v ∈ piece L (c + m + 1) := piece_mono (by omega) hv
  rw [corner_stairWord_consume hq0 hq1 c m hv',
    corner_eq_neg_cmAscWord_auxVar_mul hq0 hq1 c hv, smul_neg]

/-- **The corner at width `1` is multiplication by `-y_1` on all of `V_1`.** The lemma
`HJO.Sweep.corner_one_auxVar_mul` states this on `y_1V_1` and `HJO.Sweep.corner_one_one` at the
constant `1`; this is the two together, read off
`HJO.Sweep.corner_eq_neg_cmAscWord_auxVar_mul` at `m = 0`, where the ascending word `T_{[1,0]}` is
empty (`HJO.Sweep.cmAscWord_one_zero`). -/
theorem corner_one_eq_neg_auxVar_mul (hq0 : q ≠ 0) (hq1 : q ≠ 1) {v : Total L}
    (hv : v ∈ piece L 1) : corner q 1 v = -((auxVar 1 : Total L) * v) := by
  have h := corner_eq_neg_cmAscWord_auxVar_mul hq0 hq1 0 (by simpa using hv)
  rwa [cmAscWord_one_zero, Module.End.one_apply, Nat.zero_add] at h

omit [Algebra ℚ L] in
/-- **`Σ_δ` carries `V_k` into `V_{k+δ}`**, the membership the module docstring of
`HJO.Sweep.shiftAux` records and no earlier statement had: renaming `y_i ↦ y_{i+δ}` moves every
variable of `F` up by `δ`, so a variable below `k` lands below `k + δ`. -/
theorem shiftAux_mem_piece (δ : ℕ) {k : ℕ} {F : Total L} (hF : F ∈ piece L k) :
    shiftAux L δ F ∈ piece L (k + δ) := by
  rw [piece, MvPolynomial.mem_supported] at hF ⊢
  intro j hj
  have hj0 : j ∈ (MvPolynomial.rename (· + δ) F : Total L).vars := by
    simpa [shiftAux] using hj
  obtain ⟨i, hi, rfl⟩ :=
    Finset.mem_image.1 (MvPolynomial.vars_rename (fun i : ℕ => i + δ) F hj0)
  have hik : i ∈ Set.Iio k := hF hi
  simp only [Set.mem_Iio] at hik ⊢
  omega

/-- **THE CONSUMING IDENTITY IN TWO-BLOCK FORM, at the offset the boundary hands over.** The
staircase `S_{0,m}` at `δ = 1` and offset `0` is absorbed on a vector in the two-block form the base
layer produces, `g·Σ_1F` with `g` a `Λ`-free vector of `V_1` and `F ∈ V_k` for `k ≤ m`:

`Δ^{(m+1)}(S_{0,m}(g·Σ_1F)) = q^m · (Δ^{(1)}g)·Σ_1F`.

The tail's own operator lands on the tail's own **low** block and the base's high block is carried
along untouched — and the output is back in the same two-block form, which is what makes the
statement usable in an induction along a layer rather than only at one point.

**`g` is not required to be `Λ`-free.** That is a real difference from the base layer's transport
`HJO.Sweep.corner_shiftAux_mul`, which needs `g ∈ HJO.Sweep.auxSubalg L` — there the low block is
carried through `d_±`, whose `qshift` reads `Λ`; here nothing reads `Λ` at all, the whole
computation being the braid relation `HJO.Sweep.cmAscWord_mul_mulLeft_auxVar_mul_stairWord` and a
multiplication. So the `Λ`-freeness that
`HJO.Sweep.exists_mul_shiftAux_of_monomial` forces on the low block is spare for this step.

This is the very configuration `HJO.Mellit.not_sweepOperatorShifted_stairWord_of_add_le` refutes for
commutation: there `m = 1`, `k = 0`, `g = y_1`, `F = 1`, and
`HJO.Sweep.X_zero_eq_mul_shiftAux` records that `y_1` is of exactly this shape. -/
@[hjo "lem_sweep_corner_stair_consume"]
theorem corner_stairWord_consume_shiftAux (hq0 : q ≠ 0) (hq1 : q ≠ 1) {k m : ℕ} (hkm : k ≤ m)
    {g : Total L} (hgp : g ∈ piece L 1) {F : Total L} (hF : F ∈ piece L k) :
    corner q (m + 1) (stairWord q 1 0 m (g * shiftAux L 1 F))
      = q ^ m • ((corner q 1 g) * shiftAux L 1 F) := by
  have hshift : shiftAux L 1 F ∈ piece L (k + 1) := shiftAux_mem_piece 1 hF
  have hv : g * shiftAux L 1 F ∈ piece L (0 + m + 1) := by
    rw [Nat.zero_add]
    exact Subalgebra.mul_mem _ (piece_mono (by omega) hgp) (piece_mono (by omega) hshift)
  have h := corner_stairWord_consume hq0 hq1 0 m hv
  rw [Nat.zero_add] at h
  rw [h, cmAscWord_one_zero, Module.End.one_apply, Nat.zero_add,
    corner_one_eq_neg_auxVar_mul hq0 hq1 hgp, neg_mul, smul_neg, mul_assoc]

/-! ### THE WALL: rules `A` and `B` admit NO consuming statement

The absorption is a property of the **corner** operator and of nothing else. Rule `C` is a
commutator, and it is the cancellation between its two halves that lets the top variable `y_n`
disappear; rules `A` and `B` read that variable directly — `d_+` multiplies by `y_{n+1}` after the
staircase has already acted, and `d_-` extracts the coefficient in `y_n`, which is exactly the
variable the staircase has moved material into. Neither can be repaired by a scalar.

The two refutations below are at the same point as
`HJO.Mellit.not_sweepOperatorShifted_stairWord_of_add_le` — offset `0`, height `1`, `δ = 1`, so the
arriving staircase is the single letter `T_1` — and they refute **every** scalar, not merely every
power of `q`. -/

section NoConsume

/-- **RULE `B` DOES NOT ABSORB THE STAIRCASE.** For every `q ≠ 1` and **every** scalar `x`,

`d^♭_-{}^{(2)}(S_{0,1}y_1) = -e_1 + (1-q)y_1` while `x · d^♭_-{}^{(1)}(y_1) = -xe_1`.

The left side carries the monomial `y_1` with coefficient `1 - q` and the right side is a pure
element of `Λ`, so no scalar — in particular no power of `q` — relates them. The reason is
structural: `d^♭_-{}^{(n)}` extracts the coefficient in `y_n`, and the staircase's top letter
`T_{n-1}` moves `y_n`; the same collision as `HJO.Sweep.not_dminus_braid_width`, which refutes
*commutation* at this point. So rule `B` neither commutes past the arriving staircase nor consumes
it. -/
@[hjo "lem_sweep_corner_stair_consume"]
theorem not_dminus_stairWord_consume (hq : q ≠ 1) (x : L) :
    dminus q 2 (stairWord q 1 0 1 (MvPolynomial.X 0 : Total L))
      ≠ x • dminus q 1 (MvPolynomial.X 0 : Total L) := by
  rw [stairWord_one, Nat.zero_add, cmAscWord_self, braidEnd, LinearMap.restrictScalars_apply,
    braid_one_X_zero, map_add, dminus_scal_mul, dminus_two_X_zero q, dminus_two_X_one,
    dminus_one_X_zero]
  intro h
  have hne : ¬ ((0 : ℕ →₀ ℕ) = Finsupp.single 0 1) := by
    intro hh; exact absurd (congrArg (fun f : ℕ →₀ ℕ => f 0) hh) (by simp)
  have hc := congrArg (MvPolynomial.coeff (Finsupp.single 0 1)) h
  rw [show (scal (1 - q) : Total L) * MvPolynomial.X 0
        = MvPolynomial.monomial (Finsupp.single 0 1) (MvPolynomial.C (1 - q)) from by
      rw [← monomial_single_one_eq_X (L := L) 0, scal, MvPolynomial.C_mul_monomial, mul_one]] at hc
  simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_neg, MvPolynomial.coeff_C,
    MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial, hne, ite_false, ite_true, neg_zero,
    zero_add, smul_zero] at hc
  exact (sub_ne_zero.2 (Ne.symm hq)) (MvPolynomial.C_eq_zero.1 hc)

omit [Algebra ℚ L] in
/-- **RULE `A` DOES NOT ABSORB THE STAIRCASE.** For every `q ≠ 0` and **every** scalar `x`,

`d^♭_+{}^{(2)}(S_{0,1}y_1) = -qy_1y_3 - q(1-q)y_1y_2` while `x · d^♭_+{}^{(1)}(y_1) = -xy_1y_2`.

The left side carries `y_3` and the right side cannot: `d^♭_+{}^{(n)}` multiplies by `y_{n+1}` and
raises the word to `T_{1↗n+1}`, both *after* the staircase has acted, so the variable it introduces
sits above everything the staircase can reach and no scalar removes it. This is the rule-`A`
analogue of `HJO.Sweep.not_corner_braid_width`, and unlike rule `C` there is no commutator to cancel
the offending term. -/
@[hjo "lem_sweep_corner_stair_consume"]
theorem not_dplus_stairWord_consume (hq : q ≠ 0) (x : L) :
    dplus q 2 (stairWord q 1 0 1 (MvPolynomial.X 0 : Total L))
      ≠ x • dplus q 1 (MvPolynomial.X 0 : Total L) := by
  rw [stairWord_one, Nat.zero_add, cmAscWord_self, braidEnd, LinearMap.restrictScalars_apply,
    braid_one_X_zero, map_add, dplus_scal_mul, dplus_two_X_zero, dplus_two_X_one, dplus_one_X_zero]
  intro h
  have hne1 : ¬ ((Finsupp.single 0 1 + Finsupp.single 1 1 : ℕ →₀ ℕ)
      = Finsupp.single 0 1 + Finsupp.single 2 1) := by
    intro hh; exact absurd (congrArg (fun f : ℕ →₀ ℕ => f 2) hh) (by simp)
  have hc := congrArg (MvPolynomial.coeff (Finsupp.single 0 1 + Finsupp.single 2 1)) h
  rw [show (scal q : Total L) * (MvPolynomial.X 0 * MvPolynomial.X 2 : Total L)
        = MvPolynomial.monomial (Finsupp.single 0 1 + Finsupp.single 2 1)
            (MvPolynomial.C q) from by
      rw [← monomial_single_one_eq_X (L := L) 0, ← monomial_single_one_eq_X (L := L) 2,
        MvPolynomial.monomial_mul, mul_one, scal, MvPolynomial.C_mul_monomial, mul_one],
    show (scal (1 - q) : Total L) * -(scal q * (MvPolynomial.X 0 * MvPolynomial.X 1 : Total L))
        = -(MvPolynomial.monomial (Finsupp.single 0 1 + Finsupp.single 1 1)
            (MvPolynomial.C ((1 - q) * q))) from by
      rw [mul_neg, ← mul_assoc, ← scal_mul, ← monomial_single_one_eq_X (L := L) 0,
        ← monomial_single_one_eq_X (L := L) 1, MvPolynomial.monomial_mul, mul_one, scal,
        MvPolynomial.C_mul_monomial, mul_one],
    show (MvPolynomial.X 0 * MvPolynomial.X 1 : Total L)
        = MvPolynomial.monomial (Finsupp.single 0 1 + Finsupp.single 1 1) 1 from by
      rw [← monomial_single_one_eq_X (L := L) 0, ← monomial_single_one_eq_X (L := L) 1,
        MvPolynomial.monomial_mul, mul_one]] at hc
  simp only [MvPolynomial.coeff_neg, MvPolynomial.coeff_add, MvPolynomial.coeff_smul,
    MvPolynomial.coeff_monomial, hne1, ite_false, ite_true, neg_zero, add_zero, smul_zero,
    neg_eq_zero] at hc
  exact hq (MvPolynomial.C_eq_zero.1 hc)

end NoConsume

end HJO.Sweep

/-! ### THE REFUTED COMMUTATION, ANSWERED AT ITS OWN WITNESS -/

namespace HJO.Mellit

open HJO.Sweep HJO.Paths Finset

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-- **The tail's own event operator at the witness point is `Δ^{(1)}`**: rule `C` at width `1` with
`HJO.Paths.sweepRight` equal to `0`, so the rule-`C` scalar `q^{-a_P}` is `1` and **no hypothesis on
`q` is spent** — in particular not `q ≠ 0`, which a nonzero exponent would have forced through an
inverse. The shift-`β` version is `HJO.Mellit.sweepOperatorShifted_baseTwoThreeB_zero_two`, which at
`β = 1` is `Δ^{(2)}`. -/
theorem sweepOperator_baseTwoThreeB_zero_two :
    sweepOperator q u baseTwoThreeB ((0, 2) : ℕ × ℕ) = corner q 1 := by
  rw [← sweepOperatorShifted_zero,
    sweepOperatorShifted_of_eventType_C baseTwoThreeB 0 eventType_baseTwoThreeB_zero_two,
    sweepRight_baseTwoThreeB_zero_two, sweepWidth_baseTwoThreeB_zero_two]
  norm_num

/-- **THE FOURTH CLOSED ROUTE, ANSWERED.** At the point where
`HJO.Mellit.not_sweepOperatorShifted_stairWord_of_add_le` shows the round-boundary commutation to be
**false** — the type-`C` point `(0,2)` of round `4` of `z = w = HJO.Mellit.baseTwoThreeB`, read at
`HJO.Paths.sweepWidth w p + β_4 = 2`, the whole layer of that round
(`HJO.Mellit.tailRound_four_baseTwoThreeB`) — the arriving staircase is instead **consumed**:

`Φ^{ext}_{(0,2)}(S_{0,1} v) = q · Φ^{w}_{(0,2)}(v)` for every `v ∈ V_1`.

The raised operator `Δ^{(2)}` precomposed with the arriving `S_{0,1} = T_1` **is** the tail's own
event operator `Δ^{(1)}` at its own width, times `q^{β_4}`. The correction does not come out of the
layer, which is why no commutation could produce it, and the identity is
`HJO.Sweep.corner_stairWord_consume_of_mem_piece` at `c = 0`, `m = 1`.

The three numbers the general identity asks for are all supplied here by the geometry: `δ_4 = 1`
(`HJO.Mellit.card_tailLiveSteps_baseTwoThreeB_const`), the offset is `0` because round `5` is empty
so the staircase from round `6` arrives unmoved, and `k^w(0,2) = 1` with
`β_4 = #(HJO.Paths.baseLiveSteps z 4) = 1`
(`HJO.Mellit.card_baseLiveSteps_baseTwoThreeB_four`), so `m = β_4` and `c = k^w - 1`. -/
@[hjo "lem_sweep_corner_stair_consume"]
theorem sweepOperatorShifted_stairWord_consume_baseTwoThreeB (hq0 : q ≠ 0) (hq1 : q ≠ 1)
    {v : Total L} (hv : v ∈ piece L 1) :
    sweepOperatorShifted q u baseTwoThreeB ((0, 2) : ℕ × ℕ) 1 (stairWord q 1 0 1 v)
      = q • sweepOperator q u baseTwoThreeB ((0, 2) : ℕ × ℕ) v := by
  rw [sweepOperatorShifted_baseTwoThreeB_zero_two, sweepOperator_baseTwoThreeB_zero_two,
    show (2 : ℕ) = 0 + 1 + 1 from rfl,
    corner_stairWord_consume_of_mem_piece hq0 hq1 0 1 (by simpa using hv), pow_one, Nat.zero_add]

end HJO.Mellit
