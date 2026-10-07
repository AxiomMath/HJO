/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.MellitVertexStepGeneral
public meta import HJO.Attr

/-! # `D_0` inside the sweep module, and what the `(a,1)` column's commutation really is

`HJO/Shuffle/MellitVertexStepGeneral.lean` proves the `(a,1)` column of
`HJO.Mellit.lhsRewrite_sweepWitness` at `f = e_1`, for every `a`. The column at a **general** `f`
can be formulated as a commutation: writing
`ψ_b(f) = d_-^{(1)}(Z^b(Φf))` for the sweep side of the column at the slope `(b+1,1)`, with
`Φf = y_1d^*_+{}^{(0)}(ιf)` (`HJO.Sweep.psiCol`),

`M·ψ_{b+1} = ψ_b∘D_0 - D_0∘ψ_b`,   `M = (1-q)(1-u)`   (`HJO.Sweep.ColumnCommutes`).

**This file makes that formulation statable inside the sweep module, and then shows it is an
equivalence and not a reduction.**

## `D_0` is the `n = 0` member of the known family

The identity `HJO.Sweep.dop_eq_neg_dminusCM_auxVar_pow_dplusStar` reads
`ι(D_{m+1}f) = d_-^{(1)}(y_1^{m+1}d^*_+{}^{(0)}(ιf))`
(`HJO.Sweep.dop_succ_eq_dminus_auxVar_pow_dplusStar`) for every `m ≥ 0`. Deleting the power of `y_1`
gives `D_0`:

`ι(D_0f) = d_-^{(1)}(d^*_+{}^{(0)}(ιf))`   (`HJO.Sweep.dop_zero_eq_dminus_dplusStar`),

with **no condition on `q` or `u`** — both sides are the pairing of the coefficients of `f[X + M/z]`
against `(-1)^je_j`, the right one because `d_-`'s unshifted extraction is that pairing
(`HJO.Sweep.lowerCoeff_zero_aeval`, the companion of
`HJO.Sweep.lowerCoeffShift_zero_aeval`, which pairs against `(-1)^je_{j+1}` instead). Cross-checked
against the known value: `HJO.Sweep.dop_zero_elemSymm_one_of_sweep` recomputes
`HJO.Sym.dop_zero_elemSymm_one` through this route.

Its consequence is the one the commutation needs: writing `A = d^*_+{}^{(0)}d_-^{(1)}`
for the second summand of `HJO.Sweep.vertexStep`, **`A` is a lift of `D_0` along `Φ`** —
`A(Φf) = Φ(D_0f)` (`HJO.Sweep.dplusStar_dminus_dplusStar_C`) — and `A` computes `D_0` on `V_0`
outright. So the commutation can be stated with no slope operator in it at all, which is
`HJO.Sweep.ColumnCommutes`. The statement is
`HJO.Sweep.dop_zero_eq_dminus_dplusStar`.

## The commutation is EQUIVALENT to the column it serves

`HJO.Sweep.columnCommutes_iff`: for `M ≠ 0`,

**`ColumnCommutes q u ↔ ∀ b, HJO.Mellit.LhsSlope q u (b+1) 1`.**

Forwards is an induction whose base is `ψ_0 = ι∘D_1` (`HJO.Sweep.psiCol_zero`, unconditional, from
the identity above) and whose step is `HJO.Sym.Qop`'s own recursion on the column,
`Q_{b+2,1} = M^{-1}(Q_{b+1,1}D_0 - D_0Q_{b+1,1})` (`HJO.Sweep.qop_succ_succ_one`, off
`HJO.Sym.split_snd_one`). Backwards is that same recursion read the other way. Only `M ≠ 0` is
needed in either direction — strictly less than the `q ≠ 0`, `u ≠ 0`, `q ≠ 1` the column's
evaluations carry.

**So the commutation is not independent input.** It is the column restated in the sweep module: a
proof of it would prove the column, and the column proves it. What the restatement buys is that
`HJO.Sym.Qop` and its recursion are gone, so the statement is now about `Z`, `d^*_+` and `d_-` only
and the vertex relations can be brought to bear; what it does not buy is a weaker hypothesis to
discharge.

## What breaks the circle, and two routes that do not

A `b`-free operator identity would break it, and the obvious candidate is false. At `b = 0` the
commutation is exactly

`M·d_-(y_1Tv) = d_-(y_1Av) - d_-(A(y_1v))`

read at `v = Φf` (`HJO.Sweep.columnCommutes_zero_iff_wideAt`). Asked of **every** `v ∈ V_1` — the
`b`-free strengthening — it fails, at `v = y_1`, with defect exactly `ι(e_2 - e_1^2)`, free of both
parameters (`HJO.Sweep.wideAt_auxVar_defect`, `HJO.Sweep.not_wideAt_auxVar`). And `y_1` is
not in the image of `Φ`, whose degree-one part is the line through
`Φ(e_1) = ιe_1 + (q-1)uy_1`; on that line the `e_1^2` defect cancels identically. So the identity is
a property of the plethystic shift's image, not of the sweep algebra, and there is no `V_1`-wide
relation to prove instead.

The second route is telescoping. The commutation's second term is `d_-(y_1T^bAΦf)`, with the `A`
to the **right** of `T^b` — it arrives as `Φ∘D_0`. Moving it left, which would turn the family into
one identity applied to `T^bΦf`, costs `[T^b, A]`, and already

`[T,A](Φe_1) = quM·(ιe_1 + qy_1) ≠ 0`
(`HJO.Sweep.vertexStep_dplusStar_dminus_comm_dplusStar_C_elemSymm_one`,
`HJO.Sweep.vertexStep_dplusStar_dminus_ne`).

Since `HJO.Sweep.zop` at `k = 1` makes `T = (1-q)^{-1}(A - qN)` with
`N = d_-^{(2)}d^*_+{}^{(1)}`, that says `[N,A] ≠ 0`: **the commutator of the two orders of `B_m`
against `d^*_+` does not vanish, so this route needs it as further input**, and it is the same pair
of operators the truncation obstruction of `MellitVertexStepGeneral.lean` is about.

## The `f = e_1` evidence is degenerate

`HJO.Sweep.columnCommutes_at_elemSymm_one`: the commutation does hold at `f = e_1`, at every `b` —
the cross-check against the column at `f = e_1`. But it holds there for a reason that tests nothing:
`D_0(e_1) = (1-M)e_1` is a **scalar** multiple (`HJO.Sym.dop_zero_elemSymm_one`), so the second
term's argument `D_0f` is not a new argument, and the identity collapses onto the
`Λ`-side recursion. The commutation's content is how `ψ_b` moves between *different* arguments, and
the first `f` that probes it is one with `D_0f ∉ Lf` — the smallest being `f = e_2`, where
`D_0(e_2) = e_2 - Me_1^2 - (q+u)Me_2` (`HJO.Sym.dop_zero_elemSymm_two`) leaves the line.

## Implementation notes

The results proved outright here are `HJO.Sweep.dop_zero_eq_dminus_dplusStar` (the identity) and
`HJO.Sweep.dplusStar_dminus_dplusStar_C` (its consequence `A∘Φ = Φ∘D_0`). Everything else here is
either an equivalence between two statements not proved in this file (the commutation is
`HJO.Sweep.columnCommutes`) or a refutation of a route to one.
`HJO.Mellit.lhsRewrite_sweepWitness` is proved elsewhere, by a different route
(`HJO.Mellit.lhsRewrite_sweepWitness`, `HJO/Shuffle/ShuffleClosed.lean`).
-/

@[expose] public section

namespace HJO.Sweep

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-! ### `D_0` is the `n = 0` member of the `d_-y_1^{n-1}d^*_+` family -/

/-- `d_-`'s unshifted extraction on a power of `y_1`: the single surviving term carries
`(-1)^je_j`. The companion of `HJO.Sweep.lowerCoeffShift_zero_X_pow`, which pairs with `e_{j+1}`. -/
theorem lowerCoeff_zero_X_pow (j : ℕ) :
    lowerCoeff L 0 ((MvPolynomial.X 0 : Total L) ^ j)
      = (-1 : Total L) ^ j * MvPolynomial.C (Sym.elemSymm L j) := by
  have hpow : ((MvPolynomial.X 0 : Total L)) ^ j
      = MvPolynomial.monomial (Finsupp.single 0 j) 1 := MvPolynomial.X_pow_eq_monomial
  rw [hpow, lowerCoeff_monomial]
  simp

/-- **`d_-`'s unshifted extraction is the pairing against `(-1)^je_j`.** -/
theorem lowerCoeff_zero_aeval (P : Polynomial (Sym.Lambda L)) :
    lowerCoeff L 0 (Polynomial.aeval (MvPolynomial.X 0 : Total L) P)
      = MvPolynomial.C (Sym.coeffPairing (fun j => (-1) ^ j * Sym.elemSymm L j) P) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add]; rw [hP, hQ]
  | monomial j a =>
    have hsmul : (algebraMap (Sym.Lambda L) (Total L) a) * (MvPolynomial.X 0 : Total L) ^ j
        = a • ((MvPolynomial.X 0 : Total L) ^ j) := (Algebra.smul_def a _).symm
    have hneg : ((-1 : Total L)) = MvPolynomial.C (-1 : Sym.Lambda L) := by simp
    rw [Polynomial.aeval_monomial, hsmul, map_smul, lowerCoeff_zero_X_pow,
      Sym.coeffPairing_monomial, Algebra.smul_def, hneg, ← map_pow, ← map_mul,
      MvPolynomial.algebraMap_eq, ← map_mul]

/-- **`ι(D_0f) = d_-^{(1)}(d^*_+{}^{(0)}(ι f))`.**

The `n = 0` member of the family whose `n ≥ 1` half is
`HJO.Sweep.dop_eq_neg_dminusCM_auxVar_pow_dplusStar`, read in the
modified convention of `HJO.Sweep.dop_succ_eq_dminus_auxVar_pow_dplusStar`, where
`ι(D_{m+1}f) = d_-^{(1)}(y_1^{m+1}d^*_+(ι f))`: here the power of `y_1` is absent, and so is the
sign. Both sides are the pairing of the coefficients of `f[X + M/z]` against `(-1)^je_j` --- the
left by `HJO.Sym.DopInt` at `k = 0`, the right because `d_-`'s extraction pairs `y_1^j` with
`(-1)^je_j` (`HJO.Sweep.lowerCoeff_zero_aeval`) and the three substitutions making up `d_-d^*_+`
compose to that displacement transported along `w ↦ y_1`
(`HJO.Sweep.qshiftNeg_cycleShift_qshift_C`).

No condition on `q` or `u`: nothing here divides. -/
@[hjo "lem_mellit_dop_zero_sweep"]
theorem dop_zero_eq_dminus_dplusStar (q u : L) (f : Sym.Lambda L) :
    (MvPolynomial.C (Sym.Dop q u 0 f) : Total L)
      = dminus q 1 (dplusStar q u 0 (MvPolynomial.C f : Total L)) := by
  have hstep : dminus q 1 (dplusStar q u 0 (MvPolynomial.C f : Total L))
      = lowerCoeff L 0 (Polynomial.aeval (MvPolynomial.X 0 : Total L)
          (Sym.plethShift q u f)) := by
    change lowerCoeff L 0
      (qshiftNeg q 1 (cycleShift u 0 (qshift q 1 (MvPolynomial.C f : Total L)))) = _
    rw [qshiftNeg_cycleShift_qshift_C]
  rw [hstep, lowerCoeff_zero_aeval, Sym.dop_apply]
  simp

/-- **`d^*_+{}^{(0)}d_-^{(1)}` is a lift of `D_0` along `Φ = d^*_+{}^{(0)}ι`:**
`A(Φf) = Φ(D_0f)`, where `A = d^*_+{}^{(0)}d_-^{(1)}` is the second summand of
`HJO.Sweep.vertexStep`. Immediate from `HJO.Sweep.dop_zero_eq_dminus_dplusStar`. -/
@[hjo "lem_mellit_dop_zero_sweep"]
theorem dplusStar_dminus_dplusStar_C (q u : L) (f : Sym.Lambda L) :
    dplusStar q u 0 (dminus q 1 (dplusStar q u 0 (MvPolynomial.C f : Total L)))
      = dplusStar q u 0 (MvPolynomial.C (Sym.Dop q u 0 f) : Total L) := by
  rw [← dop_zero_eq_dminus_dplusStar]

/-! ### The `(a,1)` column as a family of maps, and the commutation -/

/-- **The sweep side of the `(a,1)` column at the slope `(b+1,1)`:**
`ψ_b(f) = d_-^{(1)}(Z^b(Φ f))`, with `Z` the second letter of `HJO.Sweep.slopeOperator` and
`Φ f = y_1d^*_+{}^{(0)}(ι f)`.

`HJO.Sweep.slopeOperator_one_succ_one` identifies `Ξ_{b+1,1}` with `HJO.Sweep.straightMonomial`
at `a = 0`, and the sign `(-1)^{1+1}` of `HJO.Mellit.LhsSlopeAt` is trivial on this column, so the
clause at `(b+1,1)` is exactly `ψ_b(f) = ι(Q_{b+1,1}f)`
(`HJO.Sweep.lhsSlopeAt_succ_one_iff_psiCol`). -/
noncomputable def psiCol (q u : L) (b : ℕ) (f : Sym.Lambda L) : Total L :=
  dminus q 1 (straightMonomial q u 0 b (Mellit.slopeArg q u f))

/-- `ψ_0 = ι∘D_1`, unconditionally: at `b = 0` the straight monomial is the identity and
`HJO.Sweep.dop_succ_eq_dminus_auxVar_pow_dplusStar` at `m = 0` reads
`ι(D_1f) = d_-^{(1)}(y_1d^*_+(ι f))`, which is `HJO.Mellit.slopeArg` verbatim. -/
theorem psiCol_zero (q u : L) (f : Sym.Lambda L) :
    psiCol q u 0 f = MvPolynomial.C (Sym.Dop q u 1 f) := by
  rw [psiCol, straightMonomial, pow_zero, pow_zero, mul_one, Module.End.one_apply,
    Mellit.slopeArg_def, dop_succ_eq_dminus_auxVar_pow_dplusStar q u 0 f, pow_one]

/-- The clause of `HJO.Mellit.lhsRewrite_sweepWitness` at `(b+1,1)` and one `f`, in terms of `ψ`. -/
theorem lhsSlopeAt_succ_one_iff_psiCol (q u : L) (b : ℕ) (f : Sym.Lambda L) :
    Mellit.LhsSlopeAt q u (b + 1) 1 f
      ↔ (MvPolynomial.C (Sym.Qop q u (b + 1) 1 f) : Total L) = psiCol q u b f := by
  rw [Mellit.LhsSlopeAt, slopeOperator_one_succ_one, psiCol]
  norm_num

/-- **The commutation the `(a,1)` column at a general `f` asks for:**
`M·ψ_{b+1} = ψ_b∘D_0 - D_0∘ψ_b`, with `M = (1-q)(1-u)`.

`D_0` is applied to the value `ψ_bf` --- which lies in `V_0 = ι(Λ)` --- through
`HJO.Sweep.dop_zero_eq_dminus_dplusStar`, so the statement lives entirely in the sweep module and
mentions no slope operator. That is the whole point of the formulation: the `Λ`-side recursion
`Q_{b+2,1} = M^{-1}(Q_{b+1,1}D_0 - D_0Q_{b+1,1})` of `HJO.Sym.Qop` has been traded for a relation
between the iterates of the vertex step and `d^*_+d_-`. -/
def ColumnCommutes (q u : L) : Prop :=
  ∀ (b : ℕ) (f : Sym.Lambda L),
    ((1 - q) * (1 - u)) • psiCol q u (b + 1) f
      = psiCol q u b (Sym.Dop q u 0 f) - dminus q 1 (dplusStar q u 0 (psiCol q u b f))

/-- `HJO.Sym.Qop`'s recursion on the `(a,1)` column:
`Q_{b+2,1} = M^{-1}(Q_{b+1,1}D_0 - D_0Q_{b+1,1})`, `Split (b+2) 1` being `(1,0)`
(`HJO.Sym.split_snd_one`) and `Q_{1,0}` being `D_0`. -/
theorem qop_succ_succ_one (q u : L) (b : ℕ) :
    Sym.Qop q u (b + 2) 1
      = ((1 - q) * (1 - u))⁻¹ •
          (Sym.Qop q u (b + 1) 1 * Sym.Dop q u 0 - Sym.Dop q u 0 * Sym.Qop q u (b + 1) 1) := by
  have hlt : 1 < b + 2 := by omega
  rw [Sym.qop_of_coprime q u hlt (Nat.coprime_one_right _), Sym.split_snd_one]
  simp only [Nat.sub_zero]
  rw [Sym.qop_of_le_one q u 0 (le_refl 1),
    show b + 2 - 1 = b + 1 from by omega]

/-- **The commutation gives the whole `(a,1)` column at a general `f`.**

Induction on `b`: the base is `HJO.Sweep.psiCol_zero` against `Q_{1,1} = D_1`, and the step is the
commutation read against `HJO.Sweep.qop_succ_succ_one`, the value `D_0(ψ_bf)` being supplied by
`HJO.Sweep.dop_zero_eq_dminus_dplusStar`. -/
theorem psiCol_eq_qop_of_columnCommutes (hM : (1 - q) * (1 - u) ≠ 0)
    (hC : ColumnCommutes q u) (b : ℕ) (f : Sym.Lambda L) :
    psiCol q u b f = MvPolynomial.C (Sym.Qop q u (b + 1) 1 f) := by
  induction b generalizing f with
  | zero => rw [psiCol_zero, Sym.qop_one]
  | succ c ih =>
      have hstep := hC c f
      rw [ih f, ih (Sym.Dop q u 0 f), ← dop_zero_eq_dminus_dplusStar] at hstep
      have hgoal : ((1 - q) * (1 - u)) • psiCol q u (c + 1) f
          = ((1 - q) * (1 - u)) • (MvPolynomial.C (Sym.Qop q u (c + 2) 1 f) : Total L) := by
        rw [hstep, qop_succ_succ_one, LinearMap.smul_apply, LinearMap.sub_apply,
          Module.End.mul_apply, Module.End.mul_apply, C_smul, smul_inv_smul₀ hM, map_sub]
      exact smul_right_injective (Total L) hM hgoal

/-- **The clause of `HJO.Mellit.lhsRewrite_sweepWitness` on the whole `(a,1)` column, at a general
`f`, from the commutation.** -/
theorem lhsSlope_succ_one_of_columnCommutes (hM : (1 - q) * (1 - u) ≠ 0)
    (hC : ColumnCommutes q u) (b : ℕ) : Mellit.LhsSlope q u (b + 1) 1 :=
  fun f => (lhsSlopeAt_succ_one_iff_psiCol q u b f).mpr
    (psiCol_eq_qop_of_columnCommutes hM hC b f).symm

/-- **And conversely**: the column at a general `f` gives the commutation back, so the commutation
is not independent input. -/
theorem columnCommutes_of_psiCol_eq_qop (hM : (1 - q) * (1 - u) ≠ 0)
    (h : ∀ (b : ℕ) (f : Sym.Lambda L), psiCol q u b f = MvPolynomial.C (Sym.Qop q u (b + 1) 1 f)) :
    ColumnCommutes q u := by
  intro b f
  rw [h (b + 1) f, h b (Sym.Dop q u 0 f), h b f, ← dop_zero_eq_dminus_dplusStar,
    qop_succ_succ_one, LinearMap.smul_apply, LinearMap.sub_apply, Module.End.mul_apply,
    Module.End.mul_apply, C_smul, smul_inv_smul₀ hM, map_sub]

/-- **The commutation is EQUIVALENT to the `(a,1)` column at a general `f`.** -/
theorem columnCommutes_iff (hM : (1 - q) * (1 - u) ≠ 0) :
    ColumnCommutes q u ↔ ∀ b : ℕ, Mellit.LhsSlope q u (b + 1) 1 := by
  refine ⟨fun hC b => lhsSlope_succ_one_of_columnCommutes hM hC b, fun h => ?_⟩
  refine columnCommutes_of_psiCol_eq_qop hM fun b f => ?_
  exact ((lhsSlopeAt_succ_one_iff_psiCol q u b f).mp (h b f)).symm

/-! ### Cross-checks: the known values, recomputed through `D_0` in the sweep module -/

/-- `ψ_b` is `L`-linear in `f`. -/
theorem psiCol_smul (q u : L) (b : ℕ) (c : L) (f : Sym.Lambda L) :
    psiCol q u b (c • f) = c • psiCol q u b f := by
  rw [psiCol, psiCol, Mellit.slopeArg_smul, map_smul, map_smul]

/-- **Cross-check on `HJO.Sweep.dop_zero_eq_dminus_dplusStar`: it recomputes the known
`HJO.Sym.dop_zero_elemSymm_one`.** `d_-^{(1)}(d^*_+(ιe_1))` is `q·ιe_1 - (q-1)u·ιe_1` off
`HJO.Sweep.dplusStar_C_elemSymm_one` and the two values `B_0(e_1) = qe_1`, `d_-(y_1) = -ιe_1`,
and `q - (q-1)u = 1 - M`. That lemma computes the same scalar from `HJO.Sym.DopInt`'s kernel
directly, so the two routes agree and the `n = 0` reading is not an indexing slip. -/
theorem dop_zero_elemSymm_one_of_sweep (q u : L) :
    Sym.Dop q u 0 (Sym.elemSymm L 1) = (1 - (1 - q) * (1 - u)) • Sym.elemSymm L 1 := by
  have hCe : dminus q 1 (MvPolynomial.C (Sym.elemSymm L 1) : Total L)
      = q • (MvPolynomial.C (Sym.elemSymm L 1) : Total L) := by
    have h := dminus_one_auxVar_pow_mul_C q 0 (Sym.elemSymm L 1)
    rw [pow_zero, one_mul, Nat.cast_zero, Sym.bop_zero_elemSymm_one, C_C_mul] at h
    exact h
  have hy1 : dminus q 1 (auxVar 1 : Total L)
      = -(MvPolynomial.C (Sym.elemSymm L 1) : Total L) := by
    have h := dminus_auxVar_pow q 0 1
    norm_num at h
    linear_combination h
  have h := dop_zero_eq_dminus_dplusStar q u (Sym.elemSymm L 1)
  rw [dplusStar_C_elemSymm_one_smul, map_add, map_smul, hCe, hy1] at h
  refine MvPolynomial.C_injective ℕ (Sym.Lambda L) ?_
  rw [h, C_smul]
  match_scalars
  ring

/-! ### `ψ` in the two letters, and the `V_1`-wide identity behind the commutation -/

/-- `ψ_b(f) = d_-^{(1)}(y_1T^b(d^*_+{}^{(0)}(ι f)))`, the closed form of
`HJO.Sweep.straightMonomial_slopeArg` at `a = 0`. -/
theorem psiCol_eq (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) (b : ℕ) (f : Sym.Lambda L) :
    psiCol q u b f
      = dminus q 1 ((auxVar 1 : Total L)
          * (vertexStep q u ^ b) (dplusStar q u 0 (MvPolynomial.C f : Total L))) := by
  rw [psiCol, straightMonomial_slopeArg hq0 hu0 hq1 0 b, pow_zero, one_smul, pow_one]

/-- **The `V_1`-wide identity whose restriction to the image of `Φ` is the commutation at `b = 0`**
(`HJO.Sweep.columnCommutes_zero_iff_wideAt`):

`M·d_-(y_1Tv) = d_-(y_1Av) - d_-(A(y_1v))`,   `A = d^*_+{}^{(0)}d_-^{(1)}`.

At `v = Φf` the three terms are `M·ψ_1f`, `ψ_0(D_0f)` and `D_0(ψ_0f)`, because `A` lifts `D_0`
along `Φ` (`HJO.Sweep.dplusStar_dminus_dplusStar_C`) and computes it on `V_0`
(`HJO.Sweep.dop_zero_eq_dminus_dplusStar`). Off that image it is a **strictly stronger**
statement, and a false one: `HJO.Sweep.not_wideAt_auxVar`. -/
def WideAt (q u : L) (v : Total L) : Prop :=
  ((1 - q) * (1 - u)) • dminus q 1 ((auxVar 1 : Total L) * vertexStep q u v)
    = dminus q 1 ((auxVar 1 : Total L) * dplusStar q u 0 (dminus q 1 v))
      - dminus q 1 (dplusStar q u 0 (dminus q 1 ((auxVar 1 : Total L) * v)))

/-- **The commutation at `b = 0` IS the `V_1`-wide identity restricted to the image of `Φ`.** -/
theorem columnCommutes_zero_iff_wideAt (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    (∀ f : Sym.Lambda L, ((1 - q) * (1 - u)) • psiCol q u 1 f
        = psiCol q u 0 (Sym.Dop q u 0 f) - dminus q 1 (dplusStar q u 0 (psiCol q u 0 f)))
      ↔ ∀ f : Sym.Lambda L, WideAt q u (dplusStar q u 0 (MvPolynomial.C f : Total L)) := by
  refine forall_congr' fun f => ?_
  rw [psiCol_eq hq0 hu0 hq1 1 f, psiCol_eq hq0 hu0 hq1 0 (Sym.Dop q u 0 f),
    psiCol_eq hq0 hu0 hq1 0 f, pow_zero, pow_one, Module.End.one_apply, Module.End.one_apply,
    ← dplusStar_dminus_dplusStar_C, WideAt]

/-- **The `V_1`-wide identity is FALSE**, at `v = y_1`, with defect exactly `ι(e_2 - e_1^2)` --- no
condition on `q` or `u` beyond the `q ≠ 1` the vertex step's value on `y_1` carries, and the defect
free of both parameters.

`T(y_1) = -ιe_1 + uy_1` (`HJO.Sweep.vertexStep_auxVar`), `A(y_1) = -d^*_+(ιe_1)` and
`A(y_1^2) = d^*_+(ιe_2)`, so the three terms are `M·ι(e_1^2 + (q+u-1)e_2)`, `ι(e_1^2 - Me_2)` and
`ι(D_0e_2)` --- the last by `HJO.Sweep.dop_zero_eq_dminus_dplusStar`, which is what makes
`HJO.Sym.dop_zero_elemSymm_two` readable here at all --- and they do not match.

`y_1` is not in the image of `Φ`: the degree-one part of that image is the line spanned by
`Φ(e_1) = ιe_1 + (q-1)uy_1`, whose `ιe_1`-component is never zero. So this refutes the
`V_1`-wide strengthening without touching the commutation itself. -/
theorem wideAt_auxVar_defect (hq1 : q ≠ 1) :
    ((1 - q) * (1 - u)) • dminus q 1 ((auxVar 1 : Total L) * vertexStep q u (auxVar 1))
        - (dminus q 1 ((auxVar 1 : Total L)
              * dplusStar q u 0 (dminus q 1 (auxVar 1 : Total L)))
          - dminus q 1 (dplusStar q u 0
              (dminus q 1 ((auxVar 1 : Total L) * (auxVar 1 : Total L)))))
      = MvPolynomial.C (Sym.elemSymm L 2 - Sym.elemSymm L 1 * Sym.elemSymm L 1) := by
  have hy1 : dminus q 1 (auxVar 1 : Total L)
      = -(MvPolynomial.C (Sym.elemSymm L 1) : Total L) := by
    have h := dminus_auxVar_pow q 0 1
    norm_num at h
    linear_combination h
  have hy2 : dminus q 1 ((auxVar 1 : Total L) * (auxVar 1 : Total L))
      = (MvPolynomial.C (Sym.elemSymm L 2) : Total L) := by
    have h := dminus_auxVar_pow q 0 2
    norm_num at h
    rw [show (auxVar 1 : Total L) * (auxVar 1 : Total L) = (auxVar 1 : Total L) ^ 2 from by ring]
    linear_combination h
  have hy1e1 : dminus q 1 ((auxVar 1 : Total L) * MvPolynomial.C (Sym.elemSymm L 1))
      = MvPolynomial.C (Sym.Bop q (1 : ℤ) (Sym.elemSymm L 1)) := by
    rw [show (auxVar 1 : Total L) * MvPolynomial.C (Sym.elemSymm L 1)
        = (auxVar 1 : Total L) ^ 1 * MvPolynomial.C (Sym.elemSymm L 1) from by rw [pow_one],
      dminus_one_auxVar_pow_mul_C, Nat.cast_one]
  -- the first term, `d_-(y_1T(y_1)) = ι(e_1^2 + (q+u-1)e_2)`
  have h1 : dminus q 1 ((auxVar 1 : Total L) * vertexStep q u (auxVar 1))
      = MvPolynomial.C (Sym.elemSymm L 1 * Sym.elemSymm L 1
          + MvPolynomial.C (q + u - 1) * Sym.elemSymm L 2) := by
    have hexp : (auxVar 1 : Total L) * vertexStep q u (auxVar 1)
        = -((auxVar 1 : Total L) * MvPolynomial.C (Sym.elemSymm L 1))
          + u • ((auxVar 1 : Total L) * (auxVar 1 : Total L)) := by
      rw [vertexStep_auxVar hq1]
      simp only [smul_eq_scal_mul]
      ring
    rw [hexp, map_add, map_neg, map_smul, hy1e1, hy2, Sym.bop_one_elemSymm_one,
      ← C_smul, ← map_neg, ← map_add]
    refine congrArg MvPolynomial.C ?_
    simp only [MvPolynomial.smul_eq_C_mul, map_sub, map_add, map_one]
    ring
  -- the second term, `d_-(y_1A(y_1)) = ι(e_1^2 - Me_2)`
  have h2 : dminus q 1 ((auxVar 1 : Total L)
        * dplusStar q u 0 (dminus q 1 (auxVar 1 : Total L)))
      = MvPolynomial.C (Sym.elemSymm L 1 * Sym.elemSymm L 1
          - MvPolynomial.C ((1 - q) * (1 - u)) * Sym.elemSymm L 2) := by
    have hexp : (auxVar 1 : Total L) * dplusStar q u 0 (dminus q 1 (auxVar 1 : Total L))
        = -((auxVar 1 : Total L) * MvPolynomial.C (Sym.elemSymm L 1))
          - ((q - 1) * u) • ((auxVar 1 : Total L) * (auxVar 1 : Total L)) := by
      rw [hy1, map_neg, dplusStar_C_elemSymm_one_smul]
      simp only [smul_eq_scal_mul]
      ring
    rw [hexp, map_sub, map_neg, map_smul, hy1e1, hy2, Sym.bop_one_elemSymm_one,
      ← C_smul, ← map_neg, ← map_sub]
    refine congrArg MvPolynomial.C ?_
    simp only [MvPolynomial.smul_eq_C_mul, map_sub, map_mul, map_one]
    ring
  -- the third term, `d_-(A(y_1^2)) = ι(D_0e_2)`
  have h3 : dminus q 1 (dplusStar q u 0
        (dminus q 1 ((auxVar 1 : Total L) * (auxVar 1 : Total L))))
      = MvPolynomial.C (Sym.Dop q u 0 (Sym.elemSymm L 2)) := by
    rw [hy2, ← dop_zero_eq_dminus_dplusStar]
  rw [h1, h2, h3, Sym.dop_zero_elemSymm_two, ← C_smul, ← map_sub, ← map_sub]
  refine congrArg MvPolynomial.C ?_
  simp only [MvPolynomial.smul_eq_C_mul, map_sub, map_add, map_mul, map_one]
  ring

/-- **`¬WideAt q u y_1`**, off `HJO.Sweep.wideAt_auxVar_defect`: the defect `ι(e_2 - e_1^2)` is
nonzero because `e_1^2` and `e_2` are linearly independent
(`HJO.Sym.elemSymm_one_sq_add_smul_elemSymm_two_ne_zero` at `c = -1`). -/
theorem not_wideAt_auxVar (hq1 : q ≠ 1) : ¬ WideAt q u (auxVar 1 : Total L) := by
  intro h
  have hz := wideAt_auxVar_defect (q := q) (u := u) hq1
  rw [WideAt] at h
  rw [h, sub_self] at hz
  have hL : Sym.elemSymm L 2 - Sym.elemSymm L 1 * Sym.elemSymm L 1 = 0 :=
    MvPolynomial.C_eq_zero.mp hz.symm
  refine Sym.elemSymm_one_sq_add_smul_elemSymm_two_ne_zero (-1 : L) ?_
  rw [neg_smul, one_smul]
  linear_combination -hL

/-! ### The commutation at `f = e_1`, and why that evidence is weaker than it looks -/

/-- **Cross-check: the commutation holds at `f = e_1`, at every `b`.**

The earlier `HJO.Sweep.dminus_straightMonomial_slopeArg_elemSymm_one_eq_C` gives
`ψ_b(e_1) = ι(Q_{b+1,1}e_1)` at every `b`, and
`HJO.Sweep.dop_zero_eq_dminus_dplusStar` turns the third term into `ι(D_0(Q_{b+1,1}e_1))`, so the
three terms are exactly the three of `HJO.Sym.Qop`'s recursion `HJO.Sweep.qop_succ_succ_one` read at
`e_1`.

**And that is why `f = e_1` is weak evidence for `HJO.Sweep.ColumnCommutes`.** What the second term
needs is `ψ_b` at `D_0f`, a *different* argument; at `f = e_1` it is not different, because
`D_0(e_1) = (1-M)e_1` is a scalar multiple (`HJO.Sym.dop_zero_elemSymm_one`). So the column at this
one `f` closes both slots at once and the commutation degenerates to the `Λ`-side recursion, testing
nothing about how `ψ_b` moves between arguments. The first `f` at which it does is one with
`D_0f ∉ Lf`. -/
theorem columnCommutes_at_elemSymm_one (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1)
    (hM : (1 - q) * (1 - u) ≠ 0) (b : ℕ) :
    ((1 - q) * (1 - u)) • psiCol q u (b + 1) (Sym.elemSymm L 1)
      = psiCol q u b (Sym.Dop q u 0 (Sym.elemSymm L 1))
        - dminus q 1 (dplusStar q u 0 (psiCol q u b (Sym.elemSymm L 1))) := by
  have hval : ∀ c : ℕ, psiCol q u c (Sym.elemSymm L 1)
      = MvPolynomial.C (Sym.Qop q u (c + 1) 1 (Sym.elemSymm L 1)) := fun c =>
    dminus_straightMonomial_slopeArg_elemSymm_one_eq_C hq0 hu0 hq1 hM c
  rw [hval (b + 1), hval b, Sym.dop_zero_elemSymm_one, psiCol_smul, hval b,
    ← dop_zero_eq_dminus_dplusStar, ← C_smul, ← C_smul, ← map_sub,
    show b + 1 + 1 = b + 2 from rfl, qop_succ_succ_one, LinearMap.smul_apply,
    LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, smul_inv_smul₀ hM]
  refine congrArg MvPolynomial.C ?_
  rw [Sym.dop_zero_elemSymm_one, map_smul]

/-! ### `d^*_+d_-` does not commute with the vertex step -/

/-- **`[T, A]Φ(e_1) = quM·(ιe_1 + qy_1) ≠ 0`**, where `A = d^*_+{}^{(0)}d_-^{(1)}` is the lift of
`D_0` of `HJO.Sweep.dplusStar_dminus_dplusStar_C` and `T` is the vertex step.

The whole computation is on the two-dimensional `span(ιe_1, y_1)`: `Φ(e_1) = ιe_1 + (q-1)uy_1` is an
eigenvector of `A` with eigenvalue `1 - M`, while `T` is triangular with eigenvalues `q` and `u`
(`HJO.Sweep.vertexStep_C_elemSymm_one`, `HJO.Sweep.vertexStep_auxVar`), and the two do not commute
on it.

**This is what kills the telescoping route to `HJO.Sweep.ColumnCommutes`.** The commutation reads
`M·d_-(y_1T^{b+1}Φf) = d_-(y_1T^bAΦf) - d_-(A(y_1T^bΦf))` --- the `A` of the first term sits to the
*right* of `T^b`, because it arrives as `Φ∘D_0`. Moving it to the left, which is what would turn the
statement into one `b`-free identity applied to `T^bΦf`, costs exactly `[T^b, A]`; and already
`[T, A]` is nonzero on the image of `Φ`. Since `T = (1-q)^{-1}(A - qN)` with
`N = d_-^{(2)}d^*_+{}^{(1)}` the second half of `HJO.Sweep.zop`, this says `[N, A] ≠ 0`: **the
commutator of the two orders of `B_m` against the plethystic shift does not vanish, so this route
needs it as further input.** -/
theorem vertexStep_dplusStar_dminus_comm_dplusStar_C_elemSymm_one (hq1 : q ≠ 1) :
    vertexStep q u (dplusStar q u 0 (dminus q 1
          (dplusStar q u 0 (MvPolynomial.C (Sym.elemSymm L 1) : Total L))))
        - dplusStar q u 0 (dminus q 1 (vertexStep q u
            (dplusStar q u 0 (MvPolynomial.C (Sym.elemSymm L 1) : Total L))))
      = (q * u * ((1 - q) * (1 - u)))
          • ((MvPolynomial.C (Sym.elemSymm L 1) : Total L) + q • (auxVar 1 : Total L)) := by
  have hCe : dminus q 1 (MvPolynomial.C (Sym.elemSymm L 1) : Total L)
      = q • (MvPolynomial.C (Sym.elemSymm L 1) : Total L) := by
    have h := dminus_one_auxVar_pow_mul_C q 0 (Sym.elemSymm L 1)
    rw [pow_zero, one_mul, Nat.cast_zero, Sym.bop_zero_elemSymm_one, C_C_mul] at h
    exact h
  have hy1 : dminus q 1 (auxVar 1 : Total L)
      = -(MvPolynomial.C (Sym.elemSymm L 1) : Total L) := by
    have h := dminus_auxVar_pow q 0 1
    norm_num at h
    linear_combination h
  have hphi : dplusStar q u 0 (MvPolynomial.C (Sym.elemSymm L 1) : Total L)
      = (MvPolynomial.C (Sym.elemSymm L 1) : Total L) + ((q - 1) * u) • (auxVar 1 : Total L) :=
    dplusStar_C_elemSymm_one_smul q u 0
  have hdphi : dminus q 1 (dplusStar q u 0 (MvPolynomial.C (Sym.elemSymm L 1) : Total L))
      = (q - (q - 1) * u) • (MvPolynomial.C (Sym.elemSymm L 1) : Total L) := by
    rw [hphi, map_add, map_smul, hCe, hy1]
    match_scalars
    ring
  have hTphi : vertexStep q u (dplusStar q u 0 (MvPolynomial.C (Sym.elemSymm L 1) : Total L))
      = (q - (q - 1) * u) • (MvPolynomial.C (Sym.elemSymm L 1) : Total L)
        + ((q - 1) * u * u) • (auxVar 1 : Total L) := by
    rw [hphi, map_add, map_smul, vertexStep_C_elemSymm_one hq1, vertexStep_auxVar hq1]
    match_scalars <;> ring
  have hdT : dminus q 1 (vertexStep q u
        (dplusStar q u 0 (MvPolynomial.C (Sym.elemSymm L 1) : Total L)))
      = ((q - (q - 1) * u) * q - (q - 1) * u * u)
          • (MvPolynomial.C (Sym.elemSymm L 1) : Total L) := by
    rw [hTphi, map_add, map_smul, map_smul, hCe, hy1]
    match_scalars
    ring
  have hAphi : dplusStar q u 0 (dminus q 1
        (dplusStar q u 0 (MvPolynomial.C (Sym.elemSymm L 1) : Total L)))
      = (q - (q - 1) * u) • ((MvPolynomial.C (Sym.elemSymm L 1) : Total L)
          + ((q - 1) * u) • (auxVar 1 : Total L)) := by
    rw [hdphi, map_smul, hphi]
  have hATphi : dplusStar q u 0 (dminus q 1 (vertexStep q u
        (dplusStar q u 0 (MvPolynomial.C (Sym.elemSymm L 1) : Total L))))
      = ((q - (q - 1) * u) * q - (q - 1) * u * u)
          • ((MvPolynomial.C (Sym.elemSymm L 1) : Total L)
            + ((q - 1) * u) • (auxVar 1 : Total L)) := by
    rw [hdT, map_smul, hphi]
  rw [hAphi, hATphi, map_smul, map_add, map_smul, vertexStep_C_elemSymm_one hq1,
    vertexStep_auxVar hq1]
  match_scalars <;> ring

/-- **`A = d^*_+{}^{(0)}d_-^{(1)}` does not commute with the vertex step on the image of `Φ`.** The
value is `HJO.Sweep.vertexStep_dplusStar_dminus_comm_dplusStar_C_elemSymm_one`, and it is nonzero
because `ιe_1` and `y_1` are linearly independent over the scalars, which
`MvPolynomial.coeff 0` reads off. The three exclusions are exactly the ones the `(a,1)` column
carries, and `q ≠ 1` is inherited from the vertex step's two values. -/
theorem vertexStep_dplusStar_dminus_ne (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1)
    (hM : (1 - q) * (1 - u) ≠ 0) :
    vertexStep q u (dplusStar q u 0 (dminus q 1
        (dplusStar q u 0 (MvPolynomial.C (Sym.elemSymm L 1) : Total L))))
      ≠ dplusStar q u 0 (dminus q 1 (vertexStep q u
          (dplusStar q u 0 (MvPolynomial.C (Sym.elemSymm L 1) : Total L)))) := by
  intro h
  have hz := vertexStep_dplusStar_dminus_comm_dplusStar_C_elemSymm_one (q := q) (u := u) hq1
  rw [h, sub_self] at hz
  have hav : (auxVar 1 : Total L) = MvPolynomial.X 0 := by rw [auxVar, Nat.sub_self]
  have hc := congrArg (MvPolynomial.coeff (0 : ℕ →₀ ℕ)) hz
  rw [hav] at hc
  simp only [MvPolynomial.coeff_zero, MvPolynomial.coeff_smul, MvPolynomial.coeff_add,
    MvPolynomial.coeff_C, MvPolynomial.coeff_X] at hc
  have hne : (q * u * ((1 - q) * (1 - u))) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hq0 hu0) hM
  have he1 : (Sym.elemSymm L 1) ≠ 0 := by
    rw [Sym.elemSymm_one_eq_X]
    exact MvPolynomial.X_ne_zero 0
  refine he1 ?_
  have h2 : (q * u * ((1 - q) * (1 - u))) • (Sym.elemSymm L 1) = 0 := by
    simpa using hc.symm
  rcases smul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 hne
  · exact h3

end HJO.Sweep
