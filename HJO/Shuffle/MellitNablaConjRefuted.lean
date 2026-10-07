/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CMStructure.AtildeMixed
public import HJO.CarlssonMellit.ConjugationBottom
public import HJO.CarlssonMellit.TildeConjExists
public import HJO.Collinear.Commutation
public meta import HJO.Attr

/-! # The `Φ_c` form of `HJO.Sweep.conj_intertwines` is false, and the witness is `d₋d^*₊`

The conjugation-intertwining statement proved as `HJO.Sweep.conj_intertwines` (with the
conjugation operator and the star swap) has a first form, the `Φ_c` form, which says: for `∇` a
Macdonald conjugator and `Φ_c` the
algebra endomorphism of `Ã` sending `d₊` at the vertex `k` to `-(qu)^{-1}z_1d₊` and fixing every
idempotent, every `T_i`, `d₋` and `d^*₊`, the operators `∇L∇^{-1}` and `Φ_c(L)` agree on `V_0 = Λ`
for every `L ∈ e_0Ãe_0`.

**That is refuted here, at `L = d₋d^*₊`.** `Φ_c` fixes `d₋` and it fixes `d^*₊`, so it fixes that
`L`; the claim at that one element is therefore that `∇` *commutes* with the operator `L` acts by on
`V_0`, and that operator is `-D_1` (`HJO.Sweep.dop_one_eq_neg_dminusCM_dplusStar`). So the `Φ_c`
form asserts `∇D_1 = D_1∇` on `Λ`, and
`HJO.Sym.not_comm_dop_one` below shows no Macdonald conjugator does that whenever `M ≠ 0`.

## The refutation needs almost nothing

`HJO.Sym.IsMacdonaldConjugator` already pins `∇(e_1f) = -D_1(∇f)`, i.e. `D_1∇ = -∇(e_1·)`. Feeding
`∇D_1 = D_1∇` into that and cancelling the injective `∇` gives `D_1 = -(e_1·)` on `Λ` — the basic
operator of index one would be a multiplication operator. That is refuted by the commutator
`HJO.Sym.dop_elemSymm_one_mul`, `D_k(e_1f) = e_1D_kf + M·D_{k+1}f` (`HJO.Sym.dop_elemSymm_one_mul`),
read at `k = 1` and `f = 1`: the two `D_1`-terms cancel identically and what is left is
`M·D_2(1) = 0`, while `D_2(1) = e_2 ≠ 0`. Only `∇` injective, the one conjugator clause, and `M ≠ 0`
are used — no homogeneity, no `∇1 = 1`, and nothing about `HJO.Standing.dpaStructure_param`.

## What this says about the `Φ_c` form, and what it does not

The *intent* of the `Φ_c` form survives; its statement does not. Conjugation by `∇` does realise an
endomorphism of the algebra, but not this one: at `L = d₋d₊`, whose action on `V_0` is
multiplication by `e_1`, the conjugator clause gives `∇(e_1·)∇^{-1} = -D_1`, which is the action of
`d₋d^*₊`. So on the two witnesses conjugation by `∇` sends `d₊ ↦ d^*₊`, which is the letterwise
clause of `HJO.Sweep.IsConjugationOperator`, and *not* `d₊ ↦ -(qu)^{-1}z_1d₊`. So it is the
choice of `Φ_c` on the right-hand side that is wrong. `Φ_c` is the endomorphism the *bigrading*
statement `HJO.Dyck.Tilde.rel_biHomogeneous` needs, and that one is fine: `Φ_c` really does shift
the bigrading, which is a statement about `Ã` alone and says nothing about `∇`.

The gap between the two is exactly one letter. `Φ_c(d₊)` at the vertex `k` is `q^k·y_1d^*₊`
(`HJO.Dyck.Tilde.Atilde.conjTwist_dPlus_eq_smul_yElt_mul_dPlusStar` below, from the third mixed
relation of `HJO.Dyck.Tilde.Atilde`), whereas conjugation by `∇` produces the bare `d^*₊`. So a
repaired statement has to either use the star swap of `HJO.Dyck.Tilde.Atilde.exists_isStarSwap` in
place of `Φ_c`, or carry the factor `q^ky_1` explicitly on one side.

## Main results

* `HJO.Sym.not_dop_one_eq_neg_elemSymm_one_mul` — `D_1` is not multiplication by `-e_1`.
* `HJO.Sym.not_comm_dop_one` — no Macdonald conjugator commutes with `D_1`.
* `HJO.Sweep.not_nablaConj_dminus_dPlusStar` — the `Φ_c` form itself, refuted at `L = d₋d^*₊`.
* `HJO.Dyck.Tilde.Atilde.conjTwist_dPlus_eq_smul_yElt_mul_dPlusStar` — `Φ_c(d₊) = q^k·y_1d^*₊` at
  the scalar, the identity a proof of the `Φ_c` form needs, and which is easily misstated.

## References

The statement `HJO.Sweep.conj_intertwines` is modelled on A. Mellit, *Toric braids and
`(m, n)`-parking functions*, Section 3.7.
-/

@[expose] public section

namespace HJO.Sym

section Field

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-- **`D_k(1) = (-1)^k e_k`.** The displacement of a constant is that constant, so only the
`w^0`-piece of the extraction survives, and there it is multiplication by `(-1)^ke_k`. This is the
`k`-indexed form of `HJO.Sym.dop_one_apply_one`, which is its case `k = 1`. -/
theorem dop_apply_one (q u : L) (k : ℕ) :
    Dop q u k (1 : Lambda L) = (-1) ^ k * elemSymm L k := by
  rw [DopRees.dop_apply_eq_sum q u k 1 (N := 1) (by rw [map_one]; simp), Finset.sum_range_one,
    DopRees.dopPiece_apply, map_one]
  simp

/-- `e_2 = (p_1e_1 - p_2)/2`, the second elementary symmetric function written on the generators. -/
theorem elemSymm_two_eq :
    elemSymm L 2 = MvPolynomial.C (algebraMap ℚ L (2⁻¹ : ℚ)) *
      ((MvPolynomial.X 0 : Lambda L) * MvPolynomial.X 0 - MvPolynomial.X 1) := by
  have h0 : elemSymm L 0 = 1 := by rw [elemSymm]
  have hp1 : powerSum L (0 + 1) = (MvPolynomial.X 0 : Lambda L) := rfl
  have hp2 : powerSum L (1 + 1) = (MvPolynomial.X 1 : Lambda L) := rfl
  rw [show (2 : ℕ) = 1 + 1 from rfl, elemSymm, Finset.sum_range_succ, Finset.sum_range_one,
    elemSymm_one_eq_X, h0, hp1, hp2, show (((1 : ℕ) : ℚ) + 1) = 2 from by norm_num]
  ring

/-- **`e_2 ≠ 0`.** Specialising the alphabet to the single letter `p_2 = 1`, `p_r = 0` otherwise
sends `e_2` to `-1/2`, which is nonzero because `ℚ` embeds in `L`. -/
theorem elemSymm_two_ne_zero : elemSymm L 2 ≠ 0 := by
  have hchar : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  intro h
  have hv := congrArg
    (MvPolynomial.aeval (fun i : ℕ => if i = 1 then (1 : L) else 0)) h
  rw [elemSymm_two_eq] at hv
  simp only [map_mul, map_sub, MvPolynomial.aeval_C, MvPolynomial.aeval_X, map_zero] at hv
  norm_num at hv

/-- **`D_1` is not multiplication by `-e_1`.** Were it, the commutator identity
`HJO.Sym.dop_elemSymm_one_mul` at `k = 1` and `f = 1` would read `-e_1e_1 = e_1(-e_1) + M·D_2(1)`,
forcing `M·e_2 = 0`. -/
theorem not_dop_one_eq_neg_elemSymm_one_mul (hM : (1 - q) * (1 - u) ≠ 0) :
    ¬ ∀ f : Lambda L, Dop q u 1 f = -(elemSymm L 1 * f) := by
  intro h
  have hcomm := dop_elemSymm_one_mul q u 1 (1 : Lambda L)
  rw [h (elemSymm L 1 * 1), h (1 : Lambda L), dop_apply_one q u 2, mul_one,
    show -(elemSymm L 1 * elemSymm L 1) = elemSymm L 1 * -elemSymm L 1 from by ring] at hcomm
  have hzero : ((1 - q) * (1 - u)) • ((-1 : Lambda L) ^ 2 * elemSymm L 2) = 0 := by
    linear_combination (norm := module) -hcomm
  rw [smul_eq_zero] at hzero
  rcases hzero with hz | hz
  · exact hM (by simpa using hz)
  · exact elemSymm_two_ne_zero (by simpa using hz)

/-- **No Macdonald conjugator commutes with `D_1`.** The conjugator clause
`∇(e_1f) = -D_1(∇f)` reads backwards as `D_1(∇f) = -∇(e_1f)`; if also `∇(D_1f) = D_1(∇f)` then
`∇(D_1f) = ∇(-(e_1f))`, and `∇` is injective, so `D_1` would be multiplication by `-e_1`. -/
theorem not_comm_dop_one {nabla : Module.End L (Lambda L)}
    (hM : (1 - q) * (1 - u) ≠ 0) (h : IsMacdonaldConjugator q u nabla) :
    ¬ ∀ f : Lambda L, nabla (Dop q u 1 f) = Dop q u 1 (nabla f) := by
  intro hc
  refine not_dop_one_eq_neg_elemSymm_one_mul hM fun f => ?_
  refine h.bijective.injective ?_
  rw [hc f, h.dop_one_apply f, map_neg]

end Field

end HJO.Sym

namespace HJO.Sweep

open HJO.Sym

section Field

variable {L : Type*} [Field L] [Algebra ℚ L]

omit [Algebra ℚ L] in
/-- **The inclusion of `Λ` as the zeroth summand is injective**, so an identity between elements of
`V_*` in its image is an identity in `Λ`. -/
theorem vzero_injective : Function.Injective (vzero L) := by
  intro f g hfg
  rw [vzero_apply, vzero_apply] at hfg
  have h2 := congrArg (fun x : Vstar L => ((toPiece L 0 x : pieceSub L 0) : Total L)) hfg
  simp only [toPiece_ofPiece, coe_zeroPiece] at h2
  exact MvPolynomial.C_injective _ _ h2

variable {q u : L}

/-- **`d₋d^*₊` acts on `V_0` as `-D_1`**, read through the action of `Ã` rather than through the
assembled endomorphisms of `V_*`: `HJO.Sweep.dop_one_eq_neg_dminusCM_dplusStar` in the shape the
`Ã`-action of `HJO.Sweep.exists_action_atilde` produces it. -/
theorem action_dMinus_mul_dPlusStar_vzero [Invertible q] [Invertible (q - 1)]
    {ρ : Dyck.Tilde.Atilde L q u →ₐ[L] Module.End L (Vstar L)}
    (hρd : ∀ k : ℕ, ρ (Dyck.Tilde.Atilde.dMinus L q u k) = lowerVstar (dminusPiece q) k)
    (hρs : ∀ k : ℕ,
      ρ (Dyck.Tilde.Atilde.dPlusStar L q u k) = raiseVstar (dplusStarPiece q u) k)
    (f : Lambda L) :
    ρ (Dyck.Tilde.Atilde.dMinus L q u 0 * Dyck.Tilde.Atilde.dPlusStar L q u 0) (vzero L f)
      = vzero L (-Dop q u 1 f) := by
  have hlanded := dminusVstar_dplusStarVstar_vzero q u f
  rw [vzero_apply, dplusStarVstar_ofPiece, dminusVstar_ofPiece] at hlanded
  rw [map_mul, Module.End.mul_apply, hρd, hρs, vzero_apply, raiseVstar_ofPiece,
    lowerVstar_ofPiece]
  exact hlanded

/-- **The `Φ_c` form of `HJO.Sweep.conj_intertwines` is FALSE.** Refuted at `L = d₋d^*₊`, which lies
in the degree-zero part `e_0Ãe_0` and which every endomorphism fixing `d₋` and `d^*₊` — in
particular `Φ_c` — fixes.

Its conclusion is stated here inverse-free: `∇L∇^{-1} = Φ(L)` on `V_0` says exactly that
whenever `L` carries `f` to `g` on `V_0`, `Φ(L)` carries `∇f` to `∇g`. At this `L` both sides act by
`-D_1`, so the assertion collapses to `∇D_1 = D_1∇`, which `HJO.Sym.not_comm_dop_one` refutes.

The hypotheses are only those any reading of the statement must grant: the conjugator, `M ≠ 0`
(which `HJO.Sym.exists_isMacdonaldConjugator` and
`HJO.Sweep.conjugation_eq_signGrading_conjugator_omegaBar` both already carry), the two `Ã`-action
clauses at `d₋` and `d^*₊`, and that `Φ` fixes those two generators. -/
theorem not_nablaConj_dminus_dPlusStar [Invertible q] [Invertible (q - 1)]
    {nabla : Module.End L (Lambda L)} (hM : (1 - q) * (1 - u) ≠ 0)
    (hnab : IsMacdonaldConjugator q u nabla)
    {ρ : Dyck.Tilde.Atilde L q u →ₐ[L] Module.End L (Vstar L)}
    (hρd : ∀ k : ℕ, ρ (Dyck.Tilde.Atilde.dMinus L q u k) = lowerVstar (dminusPiece q) k)
    (hρs : ∀ k : ℕ,
      ρ (Dyck.Tilde.Atilde.dPlusStar L q u k) = raiseVstar (dplusStarPiece q u) k)
    {Φ : Dyck.Tilde.Atilde L q u →ₐ[L] Dyck.Tilde.Atilde L q u}
    (hΦd : Φ (Dyck.Tilde.Atilde.dMinus L q u 0) = Dyck.Tilde.Atilde.dMinus L q u 0)
    (hΦs : Φ (Dyck.Tilde.Atilde.dPlusStar L q u 0) = Dyck.Tilde.Atilde.dPlusStar L q u 0) :
    ¬ ∀ f g : Lambda L,
        ρ (Dyck.Tilde.Atilde.dMinus L q u 0 * Dyck.Tilde.Atilde.dPlusStar L q u 0) (vzero L f)
            = vzero L g →
          ρ (Φ (Dyck.Tilde.Atilde.dMinus L q u 0 * Dyck.Tilde.Atilde.dPlusStar L q u 0))
              (vzero L (nabla f)) = vzero L (nabla g) := by
  intro hnode
  refine not_comm_dop_one hM hnab fun f => ?_
  have hfix : Φ (Dyck.Tilde.Atilde.dMinus L q u 0 * Dyck.Tilde.Atilde.dPlusStar L q u 0)
      = Dyck.Tilde.Atilde.dMinus L q u 0 * Dyck.Tilde.Atilde.dPlusStar L q u 0 := by
    rw [map_mul, hΦd, hΦs]
  have hstep := hnode f (-Dop q u 1 f)
    (action_dMinus_mul_dPlusStar_vzero hρd hρs f)
  rw [hfix, action_dMinus_mul_dPlusStar_vzero hρd hρs (nabla f)] at hstep
  have := vzero_injective hstep
  rw [map_neg] at this
  exact (neg_injective this).symm

/-- **The refutation bites the `Φ_c` that exists**, not merely a hypothetical one: the two
hypotheses on `Φ` are discharged verbatim by `HJO.Dyck.Tilde.Atilde.conjTwist_dMinus` and
`HJO.Dyck.Tilde.Atilde.conjTwist_dPlusStar`, at every scalar `c`. Since the scalar is unconstrained,
no choice of it — the `-(qu)^{-1}` included — rescues the `Φ_c` form.

The remaining hypotheses are all satisfiable together: `ρ` with these two clauses is
`HJO.Sweep.exists_action_atilde`, the star swap is `HJO.Dyck.Tilde.Atilde.exists_isStarSwap`, and
`∇` with `M ≠ 0` is `HJO.Sym.exists_isMacdonaldConjugator`. So this is a refutation and not a
vacuous negation. -/
theorem not_nablaConj_conjTwist [Invertible q] [Invertible (q - 1)]
    {nabla : Module.End L (Lambda L)} (hM : (1 - q) * (1 - u) ≠ 0)
    (hnab : IsMacdonaldConjugator q u nabla)
    {ρ : Dyck.Tilde.Atilde L q u →ₐ[L] Module.End L (Vstar L)}
    (hρd : ∀ k : ℕ, ρ (Dyck.Tilde.Atilde.dMinus L q u k) = lowerVstar (dminusPiece q) k)
    (hρs : ∀ k : ℕ,
      ρ (Dyck.Tilde.Atilde.dPlusStar L q u k) = raiseVstar (dplusStarPiece q u) k)
    {bar : L ≃+* L} {σ : Dyck.Tilde.Atilde L q u →+ Dyck.Tilde.Atilde L q u}
    (hsw : Dyck.IsStarSwap q bar (Dyck.Tilde.Atilde.e L q u) (Dyck.Tilde.Atilde.dPlus L q u)
      (Dyck.Tilde.Atilde.dPlusStar L q u) (Dyck.Tilde.Atilde.dMinus L q u)
      (Dyck.Tilde.Atilde.Tg L q u) σ)
    (hbar : bar q = ⅟q) (c : L) :
    ¬ ∀ f g : Lambda L,
        ρ (Dyck.Tilde.Atilde.dMinus L q u 0 * Dyck.Tilde.Atilde.dPlusStar L q u 0) (vzero L f)
            = vzero L g →
          ρ (Dyck.Tilde.Atilde.conjTwist hsw hbar c
                (Dyck.Tilde.Atilde.dMinus L q u 0 * Dyck.Tilde.Atilde.dPlusStar L q u 0))
              (vzero L (nabla f)) = vzero L (nabla g) :=
  not_nablaConj_dminus_dPlusStar hM hnab hρd hρs
    (Dyck.Tilde.Atilde.conjTwist_dMinus hsw hbar c 0)
    (Dyck.Tilde.Atilde.conjTwist_dPlusStar hsw hbar c 0)

end Field

end HJO.Sweep

namespace HJO.Dyck.Tilde.Atilde

section Scalar

variable {K : Type*} [CommRing K] {q u : K} [Invertible q] [Invertible (q - 1)]
  [Invertible (q * u)] {bar : K ≃+* K} {σ : Atilde K q u →+ Atilde K q u}
  (h : IsStarSwap q bar (e K q u) (dPlus K q u) (dPlusStar K q u) (dMinus K q u) (Tg K q u) σ)
  (hbar : bar q = ⅟q)

include h hbar

/-- **`Φ_c(d₊) = q^k·y_1d^*₊` at the scalar `-(qu)^{-1}`.** The conjugator's generator
value is `c·z_1d₊`, and the third mixed relation of `HJO.Dyck.Tilde.Atilde` — `HJO.Sweep.mixed_top`,
`z_1d₊ = -(uq^{k+1})·y_1d^*₊` — turns it into a multiple of `y_1d^*₊`; at `c = -(qu)^{-1}` the
scalar collapses to `q^k`.

This is the identity a proof of the `Φ_c` form needs at its rewriting step; writing the letter as
`-q^kd^*₊` instead drops the `y_1` and flips the sign. The `y_1` is not cosmetic — it is precisely
the discrepancy that makes the `Φ_c` form false, since conjugation by `∇` produces the bare `d^*₊`.
Note also that the relation lives in `Ã` itself, not merely in the action on `V_k`, so an appeal to
`HJO.Sweep.zopOneStar_dplus`, a statement about the action, is stronger than it needs to be. -/
theorem conjTwist_dPlus_eq_smul_yElt_mul_dPlusStar (k : ℕ) :
    conjTwist h hbar (-⅟(q * u)) (dPlus K q u k)
      = (q ^ k) • (yElt K q u (k + 1) 1 * dPlusStar K q u k) := by
  have htop : zElt K q u (k + 1) 1 * dPlus K q u k
      = -((u * q ^ (k + 1)) • (yElt K q u (k + 1) 1 * dPlusStar K q u k)) := by
    have := mixed_top (K := K) (q := q) (u := u) k
    linear_combination (norm := module) this
  have hscal : -((-⅟(q * u) : K) * (u * q ^ (k + 1))) = q ^ k := by
    rw [neg_mul, neg_neg, show u * q ^ (k + 1) = (q * u) * q ^ k from by ring, ← mul_assoc,
      invOf_mul_self, one_mul]
  rw [conjTwist_dPlus, htop, smul_neg, smul_smul, ← neg_smul, hscal]

end Scalar

end HJO.Dyck.Tilde.Atilde

end
