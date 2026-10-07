/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepWitnessLhsSingleton
public import HJO.Shuffle.SweepComputesClosed
public import HJO.Classical.IotaPmonomial

/-! # `HJO.Mellit.LhsComputes` is false at `(q, u) = (1,1)`, `(0,1)` and `(1,0)`

`HJO.Mellit.LhsComputes` carries no hypothesis on `q` or `u`, and
`HJO/Shuffle/SweepWitnessLhsSingleton.lean` records that a degenerate regime therefore
sits inside its statement, together with the obligation it creates: any proof must either exclude
`qu ∈ {0, 1}` by hand or refute `∀ k ≥ 1, Q_{ak,bk} = 0` there. This file settles that obligation in
the negative direction. The regime is not merely awkward, it is **false**: at `1 < a` and at each of
the three parameter points `(q, u) = (1,1)`, `(0,1)`, `(1,0)`, `HJO.Mellit.LhsComputes q u a b` is
refuted (`HJO.Mellit.not_lhsComputes_of_degenerate`), and with it the `LhsRewrite` clause of
`HJO.Mellit.MellitInput` at the sweep witness
(`HJO.Mellit.not_lhsRewrite_sweepWitness_of_degenerate`).

## The mechanism, which needs no sweep operator at all

Two degeneracies coincide at these points, and the refutation is the collision between them.

* `HJO.Sym.Qop`'s normalisation is `M⁻¹` with `M = (1 - q)(1 - u)`, so at `q = 1` or at `u = 1` --
  and `0⁻¹ = 0` in a field -- **every** slope operator of a slope with first entry `> 1` is the zero
  map: `HJO.Sym.qop_eq_zero_of_one_lt`. With `1 < a` that is every `Q_{ak,bk}`, `k ≥ 1`. This is
  the same defect class as `HJO.Mellit.not_sweepAppend_one_left`
  (`HJO/Shuffle/SweepAppendRefuted.lean`), where `HJO.Sweep.corner`'s `(q-1)⁻¹` vanishes.
* `HJO.Sym.axisGen`'s scalar is `v/(v - 1)` with `v = qu`, which vanishes at `v = 0` and at `v = 1`,
  so there the prescription defining `HJO.Sym.IsSlopeHom` mentions `Θ` nowhere
  (`HJO.Sym.isSlopeHom_iff_of_degenerate`).

At a point where both happen, the prescription reads `0 = 0` and **every** `L`-algebra homomorphism
`Λ → End(Λ)` is a slope homomorphism at `(a, b)`. But the right-hand side of the clause does not
mention `Θ` -- that is the whole content of `HJO.Mellit.lhsRewrite_sweepWitness_iff_lhsComputes` --
so the clause forces `ι(Θ(C_α 1)\,1)` to be *independent of `Θ`*, and it is not. Two slope
homomorphisms at `α = (1)`, where `C_1(1) = e_1 = p_1` by `HJO.Mellit.copComp_one_apply_one` and
`HJO.Sym.elemSymm_one`:

* `HJO.Sym.constHom` reads the constant term, and `p_1` has none, so its value is `0`;
* `Algebra.lmul L (Λ L)`, multiplication, sends `p_1` to the operator `f ↦ p_1 f`, whose value at
  the unit is `p_1` itself, and `ι(p_1) ≠ 0` for every realisation --
  `HJO.Sym.realisation_powerSum_ne_zero`, directly off the two coefficient conditions of
  `HJO.Sym.IsRealisation`.

So the clause asserts `0 = ±ι(p_1)`. No sweep operator, no `HJO.Sweep.lowerRun` and no
`HJO.Mellit.stageWordTotal` is evaluated anywhere in the argument: the two instances share their
right-hand side, whatever it is, and are subtracted from each other.

Non-vacuity is part of the refutation and not an afterthought. `LhsComputes` opens with `∀ ι`, so a
regime with no realisation in it would be satisfied trivially; `HJO.Sym.realisationStd` is the
honest realisation `p_k ↦ ∑_i x_i^k`, built from the `ℕ`-valued
`HJO.Sym.powerSumSeries` of `HJO/Classical/IotaPmonomial.lean`, and
`HJO.Sym.isRealisation_realisationStd` is an unconditional construction of one.

## The whole degenerate regime, not just three points

`HJO.Mellit.lhsComputes_iff_of_degenerate` is the sharp form: at `qu ∈ {0, 1}`,

`LhsComputes q u a b ↔ ∃ k ≥ 1, Q_{ak,bk} ≠ 0`,

i.e. the clause is true there **exactly when it is vacuous**, because a nonzero `Q_{ak,bk}` is
precisely an obstruction to any `Θ` being a slope homomorphism at all. So the two alternatives the
singleton file's note offers -- "exclude `v ∈ {0,1}` by hand or refute `∀ k ≥ 1, Q_{ak,bk} = 0`
there" -- are not alternatives: refuting the vanishing does not rescue the clause, it merely empties
it. The regime must be excluded by hypothesis, and only the first alternative exists.

## The three points, and why `1 < a` is needed

Both degeneracies at once means `qu ∈ {0, 1}` **and** `(1 - q)(1 - u) = 0`, which over a field is
exactly `(q, u) ∈ {(1,1), (1,0), (0,1)}`. At `a = 1` the argument stops: `Q_{1,bk} = D_{bk}` by
`HJO.Sym.qop_one` carries no `M⁻¹`, so the vanishing is not available and nothing here says whether
a slope homomorphism exists at all. The target shape of the residual carries `1 < a`, so this costs
nothing.

## What this costs: the statement, not the main argument

`HJO.Mellit.shuffle_of_lhs_and_induction` (`HJO/Shuffle/SweepComputesClosed.lean`) asks for
`LhsComputes` only under `AlgebraicIndependent ℤ ![q, u]`, and that hypothesis excludes all three
points -- `HJO.Mellit.not_degenerate_of_algebraicIndependent`, from
`HJO.Mellit.sub_one_ne_zero_of_algebraicIndependent_fst` and its companion for the second
coordinate. So the main argument is untouched and the consumer is unaffected. What is refuted is the
*stated* generality of the residual: `LhsComputes` as written is not a theorem, no route can prove
it, and the genericity that `HJO.Mellit.MellitInput` carries has to be threaded into the residual's
own statement. That is a defect of the statement, of exactly the kind
`HJO.Mellit.not_sweepAppend_one_left` exhibits in `HJO.Mellit.SweepAppend`.

The complement is worth recording. `HJO.Mellit.not_mellitInput_unrestricted`
(`HJO/Shuffle/MellitAtZero.lean`) refutes the unrestricted interface using
`MellitInduction`, `Rem41` and `RhsSumsAgree`, and its docstring says of the fourth clause
"`LhsRewrite` is not used" (`HJO/Shuffle/MellitAtZero.lean`). Its parameter point is
`q = 0`, `u = 1`, `(a, b) = (2, 3)` -- one of the three points here. So the fourth clause is false
there too, and at the sweep witness it is false *by itself*: the conjunction is not needed.

## Relation to `HJO.Mellit.lhsRewrite_sweepWitness`

These are refutations of a residual's stated generality, and
`HJO.Mellit.lhsRewrite_sweepWitness` is stated inside the ambient genericity. -/

@[expose] public section

namespace HJO.Sym

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L} {a b : ℕ}

/-! ### The slope operators vanish where their normalisation blows up -/

/-- **The primitive evaluator vanishes when `M = (1 - q)(1 - u)` does.** Above the base case the
recursion of `HJO.Sym.Qop` is `M⁻¹` times a commutator, and `0⁻¹ = 0` in a field, so the whole
commutator is discarded without being evaluated. -/
theorem qopPrim_eq_zero_of_one_lt (hM : (1 - q) * (1 - u) = 0) {m : ℕ} (hm : 1 < m) (n : ℕ) :
    QopPrim q u m n = 0 := by
  rw [qopPrim_of_one_lt q u n hm, hM, inv_zero, zero_smul]

/-- **Every slope operator of a slope with first entry `> 1` vanishes at `q = 1` and at `u = 1`.**
Both branches of `HJO.Sym.Qop` above its base case carry the factor `M⁻¹`, the coprime one through
`HJO.Sym.qopPrim_eq_zero_of_one_lt` and the noncoprime one outright. -/
theorem qop_eq_zero_of_one_lt (hM : (1 - q) * (1 - u) = 0) {m : ℕ} (hm : 1 < m) (n : ℕ) :
    Qop q u m n = 0 := by
  rw [Qop]
  split_ifs with h1 h2
  · exact absurd h1 (by omega)
  · exact qopPrim_eq_zero_of_one_lt hM hm n
  · rw [hM, inv_zero, zero_smul]

/-! ### The honest realisation exists -/

/-- **The realisation `p_k ↦ ∑_i x_i^k`**, the `ℕ`-valued `HJO.Sym.powerSumSeries` pushed into the
base ring. `HJO.Sym.IsRealisation` is a *predicate* on a homomorphism, so every statement
quantifying over realisations is vacuous until one is produced; this is one. -/
noncomputable def realisationStd (K : Type*) [CommRing K] : Lambda K →ₐ[K] AlphabetSeries K :=
  MvPolynomial.aeval fun i => MvPowerSeries.map (Nat.castRingHom K) (powerSumSeries (i + 1))

theorem realisationStd_powerSum (K : Type*) [CommRing K] (k : ℕ) :
    realisationStd K (powerSum K (k + 1))
      = MvPowerSeries.map (Nat.castRingHom K) (powerSumSeries (k + 1)) := by
  rw [powerSum, Nat.add_sub_cancel, realisationStd, MvPolynomial.aeval_X]

/-- **`HJO.Sym.realisationStd` is a realisation.** Both coefficient conditions of
`HJO.Sym.IsRealisation` are the two coefficient facts of `HJO.Sym.powerSumSeries`, cast into `K`. -/
theorem isRealisation_realisationStd (K : Type*) [CommRing K] :
    IsRealisation (realisationStd K) where
  coeff_pow k i := by
    rw [realisationStd_powerSum, MvPowerSeries.coeff_map, coeff_powerSumSeries_of_mem ⟨i, rfl⟩]
    exact map_one _
  coeff_of_ne k d hd := by
    rw [realisationStd_powerSum, MvPowerSeries.coeff_map,
      coeff_powerSumSeries_of_notMem (not_exists.2 hd)]
    exact map_zero _

/-- **A realisation does not kill a power sum.** The monomial `x_0^{k+1}` occurs in `ι(p_{k+1})`
with coefficient `1`, and `1 ≠ 0`. This is the non-triviality the refutation below spends, and it
needs no property of `ι` beyond `HJO.Sym.IsRealisation` itself. -/
theorem realisation_powerSum_ne_zero {K : Type*} [CommRing K] [Nontrivial K]
    {ι : Lambda K →ₐ[K] AlphabetSeries K} (hι : IsRealisation ι) (k : ℕ) :
    ι (powerSum K (k + 1)) ≠ 0 := fun h => by
  have h1 := hι.coeff_pow k 0
  rw [h, map_zero] at h1
  exact zero_ne_one h1

/-- The constant-term homomorphism kills every power sum: a generator has no constant term. -/
theorem constHom_powerSum (k : ℕ) : constHom L (powerSum L k) = 0 := by
  rw [constHom, AlgHom.coe_comp, Function.comp_apply, powerSum, MvPolynomial.aeval_X]
  exact map_zero _

end HJO.Sym

namespace HJO.Mellit

open HJO.Sym HJO.Sweep

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L} {a b : ℕ}

/-! ### The parameter points at which both degeneracies happen -/

/-- `AlgebraicIndependent ℤ ![q, u]` forces `u - 1 ≠ 0`: otherwise `X₁ - 1` evaluates to `0`, so it
is the zero polynomial, which it is not. The second-coordinate companion of
`HJO.Mellit.sub_one_ne_zero_of_algebraicIndependent_fst`. -/
theorem sub_one_ne_zero_of_algebraicIndependent_snd {K : Type*} [Field K] {q u : K}
    (hqu : AlgebraicIndependent ℤ ![q, u]) : u - 1 ≠ 0 := fun h0 => by
  have hz : (MvPolynomial.X 1 - 1 : MvPolynomial (Fin 2) ℤ) = 0 :=
    PhiPoly.eq_of_aeval_eq hqu (by simpa using h0)
  have hz' := congrArg (MvPolynomial.aeval ![(0 : ℤ), 0]) hz
  simp at hz'

/-- **Algebraic independence excludes the refuted regime.** So the refutation below costs the
*stated* generality of `HJO.Mellit.LhsComputes` and not the main argument: every consumer, down to
`HJO.Mellit.shuffle_of_lhs_and_induction`, asks for the residual under this hypothesis. -/
theorem not_degenerate_of_algebraicIndependent {K : Type*} [Field K] {q u : K}
    (hqu : AlgebraicIndependent ℤ ![q, u]) : (1 - q) * (1 - u) ≠ 0 := by
  refine mul_ne_zero (fun h0 => ?_) (fun h0 => ?_)
  · exact sub_one_ne_zero_of_algebraicIndependent_fst hqu (by rw [← neg_sub]; rw [h0]; ring)
  · exact sub_one_ne_zero_of_algebraicIndependent_snd hqu (by rw [← neg_sub]; rw [h0]; ring)

/-! ### The refutation -/

/-- **`HJO.Mellit.LhsComputes` is false at a degenerate parameter as soon as a slope homomorphism
exists there.**

`hdeg` makes `HJO.Sym.IsSlopeHom` a condition free of `Θ`
(`HJO.Sym.isSlopeHom_iff_of_degenerate`), and `hzero` is exactly that condition; so at these
parameters *every* algebra homomorphism is a slope homomorphism. The clause's right-hand side does
not mention `Θ`, so reading the clause at `α = (1)` twice -- once at `HJO.Sym.constHom`, once at
multiplication -- equates `0` with `±ι(p_1)`, and `HJO.Sym.realisation_powerSum_ne_zero` refutes
that.

The sweep side is never evaluated: the two instances share it and cancel. -/
theorem not_lhsComputes_of_qop_eq_zero (hdeg : q * u = 0 ∨ q * u = 1)
    (hzero : ∀ k : ℕ, 0 < k → Qop q u (a * k) (b * k) = 0) : ¬ LhsComputes q u a b := by
  intro h
  have hc : IsSlopeHom a b q u (constHom L) := (isSlopeHom_iff_of_degenerate hdeg _).2 hzero
  have hl : IsSlopeHom a b q u (Algebra.lmul L (Lambda L)) :=
    (isSlopeHom_iff_of_degenerate hdeg _).2 hzero
  have key := (h (realisationStd L) (isRealisation_realisationStd L) (constHom L) hc 1 Nat.one_pos
      [1] (by simp) (by simp)).trans
    (h (realisationStd L) (isRealisation_realisationStd L) (Algebra.lmul L (Lambda L)) hl 1
      Nat.one_pos [1] (by simp) (by simp)).symm
  rw [copComp_one_apply_one, elemSymm_one, constHom_powerSum, LinearMap.zero_apply, map_zero,
    smul_zero, show (Algebra.lmul L (Lambda L)) (powerSum L 1) 1 = powerSum L 1 * 1 from rfl,
    mul_one] at key
  have hcne : ((-1 : L) ^ (1 * (b + 1))) ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)
  have h0 : realisationStd L (powerSum L 1) = 0 := by
    have hinv := (inv_smul_smul₀ hcne (realisationStd L (powerSum L 1))).symm
    rw [← key, smul_zero] at hinv
    exact hinv
  exact realisation_powerSum_ne_zero (isRealisation_realisationStd L) 0 h0

/-- **The whole degenerate regime, decided.** At `qu ∈ {0, 1}` the clause is true exactly when it is
*vacuous*: if some `Q_{ak,bk}` is nonzero there is no slope homomorphism at all
(`HJO.Sym.isSlopeHom_iff_of_degenerate`) and the clause holds with no content, and if they all
vanish the clause is refuted by `HJO.Mellit.not_lhsComputes_of_qop_eq_zero`.

This discharges the obligation recorded at `HJO/Shuffle/SweepWitnessLhsSingleton.lean`,
and the answer is that its two alternatives are not alternatives: one cannot "refute
`∀ k ≥ 1, Q_{ak,bk} = 0`" *and* keep the clause, because the clause is false wherever that condition
holds and vacuous wherever it fails. The degenerate regime has to be excluded by hypothesis. -/
theorem lhsComputes_iff_of_degenerate (hdeg : q * u = 0 ∨ q * u = 1) :
    LhsComputes q u a b ↔ ∃ k : ℕ, 0 < k ∧ Qop q u (a * k) (b * k) ≠ 0 := by
  constructor
  · intro h
    by_contra hne
    refine not_lhsComputes_of_qop_eq_zero hdeg (fun k hk => ?_) h
    by_contra hk0
    exact hne ⟨k, hk, hk0⟩
  · rintro ⟨k, hk, hne⟩ ι hι Θ hΘ N hN α hpos hsum
    exact absurd ((isSlopeHom_iff_of_degenerate hdeg Θ).1 hΘ k hk) hne

/-- **`HJO.Mellit.LhsComputes` is false wherever both degeneracies happen and `1 < a`.** The
normalisation `M = (1 - q)(1 - u)` of `HJO.Sym.Qop` vanishing makes every `Q_{ak,bk}` the zero map
(`HJO.Sym.qop_eq_zero_of_one_lt`, where `1 < a` is spent), which is the hypothesis of
`HJO.Mellit.not_lhsComputes_of_qop_eq_zero`. -/
theorem not_lhsComputes_of_degenerate (hdeg : q * u = 0 ∨ q * u = 1)
    (hM : (1 - q) * (1 - u) = 0) (ha : 1 < a) : ¬ LhsComputes q u a b :=
  not_lhsComputes_of_qop_eq_zero hdeg fun _ hk =>
    qop_eq_zero_of_one_lt hM (lt_of_lt_of_le ha (Nat.le_mul_of_pos_right a hk)) _

/-- **`HJO.Mellit.LhsComputes` is false at `q = u = 1`.** -/
theorem not_lhsComputes_one_one (L : Type*) [Field L] [Algebra ℚ L] {a b : ℕ} (ha : 1 < a) :
    ¬ LhsComputes (1 : L) 1 a b :=
  not_lhsComputes_of_degenerate (Or.inr (one_mul 1)) (by ring) ha

/-- **`HJO.Mellit.LhsComputes` is false at `q = 0`, `u = 1`** -- the parameter point at which
`HJO.Mellit.not_mellitInput_unrestricted` already refutes the other three clauses of
`HJO.Mellit.MellitInput`, and which its proof reaches without using this one. -/
theorem not_lhsComputes_zero_one (L : Type*) [Field L] [Algebra ℚ L] {a b : ℕ} (ha : 1 < a) :
    ¬ LhsComputes (0 : L) 1 a b :=
  not_lhsComputes_of_degenerate (Or.inl (zero_mul 1)) (by ring) ha

/-- **`HJO.Mellit.LhsComputes` is false at `q = 1`, `u = 0`.** -/
theorem not_lhsComputes_one_zero (L : Type*) [Field L] [Algebra ℚ L] {a b : ℕ} (ha : 1 < a) :
    ¬ LhsComputes (1 : L) 0 a b :=
  not_lhsComputes_of_degenerate (Or.inl (mul_zero 1)) (by ring) ha

/-- **The `LhsRewrite` clause is false at the sweep witness at these parameters.** Through the
equivalence `HJO.Mellit.lhsRewrite_sweepWitness_iff_lhsComputes`, which carries no hypothesis on
`q` or `u` either: so `HJO.Mellit.sweepWitness` does not satisfy the clause of
`HJO.Mellit.MellitInput` at a degenerate parameter, and the clause's own genericity -- not merely
the residual's -- is load-bearing. -/
theorem not_lhsRewrite_sweepWitness_of_degenerate (hdeg : q * u = 0 ∨ q * u = 1)
    (hM : (1 - q) * (1 - u) = 0) (hab : Nat.Coprime a b) (ha : 1 < a) (hb : 0 < b) :
    ¬ LhsRewrite (sweepWitness q u a b) a b := fun h =>
  not_lhsComputes_of_degenerate hdeg hM ha
    ((lhsRewrite_sweepWitness_iff_lhsComputes hab (by omega) hb).1 h)

/-- The clause at the witness at `q = u = 1`, `(a, b) = (2, 3)`: a named instance, so that the
refutation is checkable at fixed numerals with no hypothesis at all. -/
theorem not_lhsRewrite_sweepWitness_one_one (L : Type*) [Field L] [Algebra ℚ L] :
    ¬ LhsRewrite (sweepWitness (1 : L) 1 2 3) 2 3 :=
  not_lhsRewrite_sweepWitness_of_degenerate (Or.inr (one_mul 1)) (by ring) (by decide) (by decide)
    (by decide)

end HJO.Mellit
