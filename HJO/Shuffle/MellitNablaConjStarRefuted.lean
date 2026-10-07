/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.StarFlipExists
public import HJO.Collinear.OmegaBarDop
public import HJO.Shuffle.MellitNablaConjRefuted
public meta import HJO.Attr

/-! # The star-swap form of `HJO.Sweep.conj_intertwines` with `∇` is false too, again at `d₋d^*₊`

`HJO.Shuffle.MellitNablaConjRefuted` refutes the first form of the conjugation-intertwining
statement, which uses the twisting endomorphism `Φ_c` of
`HJO.Dyck.Tilde.Atilde.exists_conjTwist_of_bar`. The natural repair replaces `Φ_c` with the
**star swap** `σ` of `HJO.Dyck.Tilde.Atilde.exists_isStarSwap`: for `∇` a Macdonald conjugator, the
repaired statement says that `∇L∇^{-1}` and `σ(L)` agree on `V_0 = Λ` for every `L` in `e_0Ãe_0`.

**That is refuted here, at the same `L = d₋d^*₊`.** The repair fixes one
direction and breaks the other.

## The witness

`σ` fixes `d₋` and exchanges `d₊` with `d^*₊`, so `σ(d₋d^*₊) = d₋d₊`. Now
`HJO.Sweep.dop_one_eq_neg_dminusCM_dplusStar` says `d₋d^*₊` acts on `V_0` as `-D_1`, and
`HJO.Sweep.dminusCM_cmDPlus_C` says `d₋d₊` acts as multiplication by `e_1`. So at this one `L` the
repaired statement asserts

  `∇(-D_1f) = e_1∇f`  for every `f ∈ Λ`.

But `HJO.Sym.IsMacdonaldConjugator` already pins `∇(D^*_1f) = e_1∇f`, so cancelling the injective
`∇` gives `D^*_1 = -D_1` on `Λ` — and `HJO.Sym.not_dopStar_one_eq_neg_dop_one` below shows that
forces `M = 0`.

A check of the *other* witness alone, `L = d₋d₊`, does not see this: there the statement reads
`∇(e_1f) = -D_1(∇f)` and is exactly the second conjugator clause. Conjugation by `∇` does carry
`e_1·` to `-D_1`; what it does **not** do is carry `-D_1` back to `e_1·`, because the clause that
lands on `e_1·` starts from `D^*_1` and not from `D_1`. The star swap, being an involution, demands
both directions, and the second one is false.

## Why `D^*_1 ≠ -D_1`, and why the gap is exactly `ω̄`

`HJO.Sym.omegaBar_dop` says `ω̄(D_kf) = D^*_k(ω̄f)`. Reading that at
`k = 1`, `f = e_1` and using `ω̄(e_1) = -e_1` (`e_1` is the power sum `p_1`, which `ω̄` negates),
`D^*_1 = -D_1` would say `ω̄` *fixes* `D_1e_1`. But
`D_1e_1 = -e_1^2 + M\,e_2` by `HJO.Sym.dop_elemSymm_one_mul`, and `ω̄` fixes `e_1^2` while sending
`M\,e_2` to `\bar M\,ω̄(e_2)`; the sign extraction `ε_±` of `HJO.Sym.signExtract` separates the two,
being `1` on `e_2` and `0` on `ω̄(e_2)`. So `M = 0`.

That computation also names the correct repair. The V_0-realisation of the star swap is not `∇`: by
`HJO.Sweep.conjugation_eq_signGrading_conjugator_omegaBar` a
conjugation operator of `HJO.Sweep.IsConjugationOperator` acts on `V_0` as `f ↦ ε_±(∇(ω̄f))`, and
the `ω̄` is precisely what converts `D_1` into `D^*_1`. A `∇`-shaped statement cannot state this:
`σ` is bar-*semilinear* (`HJO.Dyck.IsStarSwap.map_smul`) while `∇` is `L`-linear, and
`HJO.Sweep.not_nablaConj_starSwap_smul` below shows the statement fails on scalars for that reason
alone, before any witness is chosen.

## What is *not* claimed

Nothing here refutes `HJO.Sweep.IsConjugationOperator`'s letterwise clause `𝒩d₊ = d^*₊𝒩`, and
nothing here refutes the statement with `𝒩` in place of `∇`. That form is
`HJO.Sweep.conj_intertwines` (`HJO/Shuffle/MellitConjIntertwine.lean`); extending the letterwise
clauses to all of `Ã` there needs, in addition, the clause of `HJO.Sweep.IsConjugationOperator` at
the loops `T_i`.

## Main results

* `HJO.Sym.not_dopStar_one_eq_neg_dop_one` — `D^*_1` is not `-D_1`.
* `HJO.Sweep.action_dMinus_mul_dPlus_vzero` — `d₋d₊` acts on `V_0` as `e_1·`, in the shape the
  `Ã`-action of `HJO.Sweep.exists_action_atilde` produces it.
* `HJO.Sweep.not_nablaConj_starSwap_dminus_dPlusStar` — the repaired statement, refuted at
  `L = d₋d^*₊`.
* `HJO.Sweep.not_nablaConj_starSwap_smul` — the independent semilinearity obstruction.

## References

A. Mellit, *Toric braids and `(m,n)`-parking functions*, arXiv:1604.07456, §3.7, Proposition 3.10:
`∇L∇^{-1} = N(L)` on `Λ` for `L ∈ e_0𝔸_{q,t}e_0`.
-/

@[expose] public section

namespace HJO.Sym

/-! ### `ω̄` and the sign extraction on the second elementary function -/

section OmegaBarTwo

variable {L : Type*} [Field L] [Algebra ℚ L]

omit [Algebra ℚ L] in
/-- `ω̄` moves a scalar multiple by the bar: `ω̄(cf) = c̄ ω̄(f)`. The scalar action on `Λ` is
multiplication by a constant, and `HJO.Sym.omegaBar_C` moves the constant. -/
theorem omegaBar_smul (bar : L ≃+* L) (c : L) (f : Lambda L) :
    omegaBar bar (c • f) = bar c • omegaBar bar f := by
  rw [MvPolynomial.smul_eq_C_mul, map_mul, omegaBar_C, MvPolynomial.smul_eq_C_mul]

/-- **`ω̄(e_2) = (p_1^2 + p_2)/2`**, the companion of `HJO.Sym.elemSymm_two_eq`: `ω̄` negates each
power sum and fixes the rational coefficient, so the minus sign inside `e_2` becomes a plus. It is
the same element as `h_2`, but written on the generators, which is what the sign extraction below
reads. -/
theorem omegaBar_elemSymm_two (bar : L ≃+* L) :
    omegaBar bar (elemSymm L 2) = MvPolynomial.C (algebraMap ℚ L (2⁻¹ : ℚ)) *
      ((MvPolynomial.X 0 : Lambda L) * MvPolynomial.X 0 + MvPolynomial.X 1) := by
  have hQ : bar (algebraMap ℚ L (2⁻¹ : ℚ)) = algebraMap ℚ L (2⁻¹ : ℚ) :=
    RingHom.map_rat_algebraMap (bar : L →+* L) _
  rw [elemSymm_two_eq, map_mul, omegaBar_C, hQ, map_sub, map_mul, omegaBar_X, omegaBar_X]
  ring

/-- `1/2` times `2` is `1`, read in `L` through `ℚ`. -/
private theorem algebraMap_half_mul_two : (algebraMap ℚ L (2⁻¹ : ℚ)) * 2 = 1 := by
  rw [show (2 : L) = algebraMap ℚ L (2 : ℚ) by simp, ← map_mul,
    show ((2 : ℚ)⁻¹ * 2 : ℚ) = 1 by norm_num, map_one]

/-- **`ε_±(e_2) = 1`.** The sign extraction of `HJO.Sym.signExtract` sends `p_1 ↦ 1` and `p_2 ↦ -1`,
so `(p_1^2 - p_2)/2` goes to `(1 + 1)/2`. -/
theorem signExtract_elemSymm_two : signExtract L (elemSymm L 2) = 1 := by
  have hC : signExtract L (MvPolynomial.C (algebraMap ℚ L (2⁻¹ : ℚ)) : Lambda L)
      = algebraMap ℚ L (2⁻¹ : ℚ) := by simp [signExtract]
  have hX0 : signExtract L (MvPolynomial.X 0 : Lambda L) = 1 := by simp [signExtract]
  have hX1 : signExtract L (MvPolynomial.X 1 : Lambda L) = -1 := by simp [signExtract]
  rw [elemSymm_two_eq, map_mul, map_sub, map_mul, hC, hX0, hX1,
    show (1 : L) * 1 - -1 = 2 by ring]
  exact algebraMap_half_mul_two

/-- **`ε_±(ω̄(e_2)) = 0`.** The same extraction on `(p_1^2 + p_2)/2` gives `(1 - 1)/2`. This is the
single arithmetical fact that separates `D^*_1` from `-D_1`. -/
theorem signExtract_omegaBar_elemSymm_two (bar : L ≃+* L) :
    signExtract L (omegaBar bar (elemSymm L 2)) = 0 := by
  have hC : signExtract L (MvPolynomial.C (algebraMap ℚ L (2⁻¹ : ℚ)) : Lambda L)
      = algebraMap ℚ L (2⁻¹ : ℚ) := by simp [signExtract]
  have hX0 : signExtract L (MvPolynomial.X 0 : Lambda L) = 1 := by simp [signExtract]
  have hX1 : signExtract L (MvPolynomial.X 1 : Lambda L) = -1 := by simp [signExtract]
  rw [omegaBar_elemSymm_two, map_mul, map_add, map_mul, hC, hX0, hX1]
  ring

end OmegaBarTwo

/-! ### The starred basic operator of index one is not the negative of the unstarred one -/

section DopStarOne

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-- **`D_1e_1 = -e_1^2 + M\,e_2`**, the value `HJO.Sym.dop_elemSymm_one_mul` takes at `k = 1`,
`f = 1`, with `HJO.Sym.dop_apply_one` evaluating the two constants. -/
theorem dop_one_elemSymm_one (q u : L) :
    Dop q u 1 (elemSymm L 1)
      = -(elemSymm L 1 * elemSymm L 1) + ((1 - q) * (1 - u)) • elemSymm L 2 := by
  have h1 := dop_elemSymm_one_mul q u 1 (1 : Lambda L)
  rw [mul_one, dop_apply_one q u 1, dop_apply_one q u 2, pow_one,
    show ((-1 : Lambda L)) ^ 2 = 1 from by ring, one_mul] at h1
  rw [h1, neg_one_mul, mul_neg]

/-- **`D^*_1` is not `-D_1`.** By `HJO.Sym.omegaBar_dop`, `ω̄(D_1f) = D^*_1(ω̄f)`; were
`D^*_1 = -D_1` this would read `ω̄(D_1f) = -D_1(ω̄f)`, and at `f = e_1`, where `ω̄(e_1) = -e_1`
because `e_1` is the power sum `p_1`, it says `ω̄` fixes `D_1e_1`. With
`D_1e_1 = -e_1^2 + M e_2` and `ω̄(e_1^2) = e_1^2` that is `M̄ ω̄(e_2) = M e_2`, and the sign
extraction `ε_±` of `HJO.Sym.signExtract` — `0` on `ω̄(e_2)` and `1` on `e_2` — turns it into
`M = 0`.

The hypotheses are exactly `HJO.Sym.paramInvLambda` on the two parameters. Nothing about the *value*
of `M̄` is used: the left-hand side is killed by `ε_±(ω̄(e_2)) = 0` whatever the scalar is. -/
theorem not_dopStar_one_eq_neg_dop_one {bar : L ≃+* L} (hq : bar q = q⁻¹) (hu : bar u = u⁻¹)
    (hM : (1 - q) * (1 - u) ≠ 0) :
    ¬ ∀ f : Lambda L, DopStar q u 1 f = -Dop q u 1 f := by
  intro h
  have he1 : omegaBar bar (elemSymm L 1) = -elemSymm L 1 := by
    rw [elemSymm_one_eq_X, omegaBar_X]
  have hkey : omegaBar bar (Dop q u 1 (elemSymm L 1)) = Dop q u 1 (elemSymm L 1) := by
    rw [omegaBar_dop hq hu 1, h, he1, map_neg, neg_neg]
  rw [dop_one_elemSymm_one, map_add, map_neg, map_mul, he1, omegaBar_smul, neg_mul_neg] at hkey
  have hcancel : bar ((1 - q) * (1 - u)) • omegaBar bar (elemSymm L 2)
      = ((1 - q) * (1 - u)) • elemSymm L 2 := by
    have := hkey
    linear_combination (norm := module) this
  have hε := congrArg (signExtract L) hcancel
  rw [map_smul, map_smul, signExtract_omegaBar_elemSymm_two, signExtract_elemSymm_two,
    smul_eq_mul, smul_eq_mul, mul_zero, mul_one] at hε
  exact hM hε.symm

end DopStarOne

end HJO.Sym

namespace HJO.Sweep

open HJO.Sym

section Field

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-- **`d₋d₊` acts on `V_0` as multiplication by `e_1`**, read through the action of `Ã` rather than
through the assembled endomorphisms of `V_*`: `HJO.Sweep.dminusCM_cmDPlus_C` in the shape
the `Ã`-action of `HJO.Sweep.exists_action_atilde` produces it. This is the exact companion of
`HJO.Sweep.action_dMinus_mul_dPlusStar_vzero`, which does the same for `d₋d^*₊` and `-D_1`. -/
theorem action_dMinus_mul_dPlus_vzero [Invertible q] [Invertible (q - 1)]
    {ρ : Dyck.Tilde.Atilde L q u →ₐ[L] Module.End L (Vstar L)}
    (hρd : ∀ k : ℕ, ρ (Dyck.Tilde.Atilde.dMinus L q u k) = lowerVstar (dminusPiece q) k)
    (hρp : ∀ k : ℕ, ρ (Dyck.Tilde.Atilde.dPlus L q u k) = raiseVstar (cmDPlusPiece q) k)
    (f : Lambda L) :
    ρ (Dyck.Tilde.Atilde.dMinus L q u 0 * Dyck.Tilde.Atilde.dPlus L q u 0) (vzero L f)
      = vzero L (elemSymm L 1 * f) := by
  have hlanded := dminusVstar_cmDPlusVstar_vzero q f
  rw [vzero_apply, cmDPlusVstar_ofPiece, dminusVstar_ofPiece] at hlanded
  rw [map_mul, Module.End.mul_apply, hρd, hρp, vzero_apply, raiseVstar_ofPiece,
    lowerVstar_ofPiece]
  exact hlanded

/-- **The star-swap form of `HJO.Sweep.conj_intertwines` with `∇` is FALSE.** Refuted at
`L = d₋d^*₊`, the same element that refuted the `Φ_c` form — the repair changes which of the two
directions fails, not whether one does.

The conclusion is stated inverse-free, exactly as in
`HJO.Sweep.not_nablaConj_dminus_dPlusStar`: `∇L∇^{-1} = σ(L)` on `V_0` says that whenever `L`
carries `f` to `g` on `V_0`, `σ(L)` carries `∇f` to `∇g`. That implication form is *weaker* than an
equality of operators, since it constrains nothing where `L` leaves `V_0`, so refuting it refutes
every reading of the statement.

`σ` fixes `d₋` and sends `d^*₊` to `d₊`, so `σ(L) = d₋d₊`, which acts on `V_0` as `e_1·`; `L` itself
acts as `-D_1`. So the statement says `∇(-D_1f) = e_1∇f`, while
`HJO.Sym.IsMacdonaldConjugator` says `∇(D^*_1f) = e_1∇f`. Injectivity of `∇` then forces
`D^*_1 = -D_1`, which `HJO.Sym.not_dopStar_one_eq_neg_dop_one` refutes.

Every hypothesis is satisfiable simultaneously, so this is a refutation and not a vacuous negation:
`ρ` with these three clauses is `HJO.Sweep.exists_action_atilde`, `σ` is
`HJO.Dyck.Tilde.Atilde.exists_isStarSwap`, and `∇` with `M ≠ 0` is
`HJO.Sym.exists_isMacdonaldConjugator`. Only one clause of the conjugator is spent — the one on
`D^*_1` — together with injectivity; no homogeneity, no `∇1 = 1`, and nothing from
`HJO.Standing.dpaStructure_param`. -/
theorem not_nablaConj_starSwap_dminus_dPlusStar [Invertible q] [Invertible (q - 1)]
    {bar : L ≃+* L} (hq : bar q = q⁻¹) (hu : bar u = u⁻¹) (hM : (1 - q) * (1 - u) ≠ 0)
    {nabla : Module.End L (Lambda L)} (hnab : IsMacdonaldConjugator q u nabla)
    {ρ : Dyck.Tilde.Atilde L q u →ₐ[L] Module.End L (Vstar L)}
    (hρd : ∀ k : ℕ, ρ (Dyck.Tilde.Atilde.dMinus L q u k) = lowerVstar (dminusPiece q) k)
    (hρp : ∀ k : ℕ, ρ (Dyck.Tilde.Atilde.dPlus L q u k) = raiseVstar (cmDPlusPiece q) k)
    (hρs : ∀ k : ℕ,
      ρ (Dyck.Tilde.Atilde.dPlusStar L q u k) = raiseVstar (dplusStarPiece q u) k)
    {sw : Dyck.Tilde.Atilde L q u →+ Dyck.Tilde.Atilde L q u}
    (hsw : Dyck.IsStarSwap q bar (Dyck.Tilde.Atilde.e L q u) (Dyck.Tilde.Atilde.dPlus L q u)
      (Dyck.Tilde.Atilde.dPlusStar L q u) (Dyck.Tilde.Atilde.dMinus L q u)
      (Dyck.Tilde.Atilde.Tg L q u) sw) :
    ¬ ∀ f g : Lambda L,
        ρ (Dyck.Tilde.Atilde.dMinus L q u 0 * Dyck.Tilde.Atilde.dPlusStar L q u 0) (vzero L f)
            = vzero L g →
          ρ (sw (Dyck.Tilde.Atilde.dMinus L q u 0 * Dyck.Tilde.Atilde.dPlusStar L q u 0))
              (vzero L (nabla f)) = vzero L (nabla g) := by
  intro hnode
  refine not_dopStar_one_eq_neg_dop_one hq hu hM fun f => ?_
  have hswap : sw (Dyck.Tilde.Atilde.dMinus L q u 0 * Dyck.Tilde.Atilde.dPlusStar L q u 0)
      = Dyck.Tilde.Atilde.dMinus L q u 0 * Dyck.Tilde.Atilde.dPlus L q u 0 := by
    rw [hsw.map_mul, hsw.map_dMinus, hsw.map_dPlusStar]
  have hstep := hnode f (-Dop q u 1 f)
    (action_dMinus_mul_dPlusStar_vzero hρd hρs f)
  rw [hswap, action_dMinus_mul_dPlus_vzero hρd hρp (nabla f)] at hstep
  have h1 := vzero_injective hstep
  refine hnab.bijective.injective ?_
  rw [hnab.map_dopStar_one f, h1]

omit [Algebra ℚ L] in
/-- **The statement fails on scalars, for a reason independent of any witness.** `σ` is
bar-semilinear (`HJO.Dyck.IsStarSwap.map_smul`) while `∇` and `ρ` are `L`-linear, so reading the
statement at `cL` and
at `L` forces `c̄` and `c` to agree on `∇g`.

Stated as an implication rather than as a negation because it is the mechanism and not yet a
contradiction: `HJO.Sweep.not_nablaConj_starSwap_smul` below closes it. With `bar q = q⁻¹` this says
`q⁻¹` and `q` act alike on `∇g`, so the statement forces `q^2 = 1` as soon as `∇g ≠ 0`. No repair
that keeps an `L`-linear `∇` on the left of a semilinear `σ` can survive this;
`HJO.Sweep.conjugation_eq_signGrading_conjugator_omegaBar` supplies the semilinear replacement
`f ↦ ε_±(∇(ω̄f))`. -/
theorem bar_smul_eq_of_nablaConj_starSwap [Invertible q] [Invertible (q - 1)]
    {bar : L ≃+* L} {nabla : Module.End L (Lambda L)}
    {ρ : Dyck.Tilde.Atilde L q u →ₐ[L] Module.End L (Vstar L)}
    {sw : Dyck.Tilde.Atilde L q u →+ Dyck.Tilde.Atilde L q u}
    (hsw : Dyck.IsStarSwap q bar (Dyck.Tilde.Atilde.e L q u) (Dyck.Tilde.Atilde.dPlus L q u)
      (Dyck.Tilde.Atilde.dPlusStar L q u) (Dyck.Tilde.Atilde.dMinus L q u)
      (Dyck.Tilde.Atilde.Tg L q u) sw)
    (hnode : ∀ (x : Dyck.Tilde.Atilde L q u) (f g : Lambda L),
      ρ x (vzero L f) = vzero L g → ρ (sw x) (vzero L (nabla f)) = vzero L (nabla g))
    {x : Dyck.Tilde.Atilde L q u} {f g : Lambda L} (hx : ρ x (vzero L f) = vzero L g) (c : L) :
    bar c • nabla g = c • nabla g := by
  have h0 := hnode x f g hx
  have hx' : ρ (c • x) (vzero L f) = vzero L (c • g) := by
    rw [map_smul, LinearMap.smul_apply, hx, map_smul]
  have h1 := hnode (c • x) f (c • g) hx'
  rw [hsw.map_smul, map_smul, LinearMap.smul_apply, h0, map_smul,
    ← map_smul (vzero L)] at h1
  exact vzero_injective h1

/-- **The repaired statement is false on scalars too.** Instantiating
`HJO.Sweep.bar_smul_eq_of_nablaConj_starSwap` at `c = q`, at the element `d₋d^*₊` and at `f = 1`,
where `g = -D_1(1) = e_1`, gives `q⁻¹∇e_1 = q∇e_1`; `∇` is injective and `e_1 = p_1 ≠ 0`, so
`q⁻¹ = q`.

This is a *second*, independent defect of the statement, and it is a defect of shape rather than of
witness: it would survive any choice of which elements of `e_0Ãe_0` the statement quantifies over,
as long as that set is closed under scaling. Restricting the statement to words would evade this
one — and
would not evade `HJO.Sweep.not_nablaConj_starSwap_dminus_dPlusStar`, whose witness is a word. -/
theorem not_nablaConj_starSwap_smul [Invertible q] [Invertible (q - 1)]
    {bar : L ≃+* L} (hq : bar q = q⁻¹) (hq2 : q⁻¹ ≠ q)
    {nabla : Module.End L (Lambda L)} (hnab : IsMacdonaldConjugator q u nabla)
    {ρ : Dyck.Tilde.Atilde L q u →ₐ[L] Module.End L (Vstar L)}
    (hρd : ∀ k : ℕ, ρ (Dyck.Tilde.Atilde.dMinus L q u k) = lowerVstar (dminusPiece q) k)
    (hρs : ∀ k : ℕ,
      ρ (Dyck.Tilde.Atilde.dPlusStar L q u k) = raiseVstar (dplusStarPiece q u) k)
    {sw : Dyck.Tilde.Atilde L q u →+ Dyck.Tilde.Atilde L q u}
    (hsw : Dyck.IsStarSwap q bar (Dyck.Tilde.Atilde.e L q u) (Dyck.Tilde.Atilde.dPlus L q u)
      (Dyck.Tilde.Atilde.dPlusStar L q u) (Dyck.Tilde.Atilde.dMinus L q u)
      (Dyck.Tilde.Atilde.Tg L q u) sw) :
    ¬ ∀ (x : Dyck.Tilde.Atilde L q u) (f g : Lambda L),
        ρ x (vzero L f) = vzero L g → ρ (sw x) (vzero L (nabla f)) = vzero L (nabla g) := by
  intro hnode
  have hg : -Dop q u 1 (1 : Lambda L) = elemSymm L 1 := by
    rw [dop_apply_one q u 1, pow_one, neg_mul, one_mul, neg_neg]
  have hmain := bar_smul_eq_of_nablaConj_starSwap hsw hnode
    (action_dMinus_mul_dPlusStar_vzero hρd hρs (1 : Lambda L)) q
  rw [hg, hq] at hmain
  have hne : nabla (elemSymm L 1) ≠ 0 := by
    intro h0
    have : elemSymm L 1 = 0 := hnab.bijective.injective (by rw [h0, map_zero])
    rw [elemSymm_one_eq_X] at this
    exact MvPolynomial.X_ne_zero 0 this
  have hzero : (q⁻¹ - q) • nabla (elemSymm L 1) = 0 := by
    rw [sub_smul, hmain, sub_self]
  refine hne ?_
  have h2 : (q⁻¹ - q)⁻¹ • ((q⁻¹ - q) • nabla (elemSymm L 1))
      = (q⁻¹ - q)⁻¹ • (0 : Lambda L) := congrArg _ hzero
  rwa [smul_zero, smul_smul, inv_mul_cancel₀ (sub_ne_zero_of_ne hq2), one_smul] at h2

/-- **The refutation is not vacuous: the action and the star swap it refutes both exist.** Every
hypothesis of `HJO.Sweep.not_nablaConj_starSwap_dminus_dPlusStar` is discharged here at once —
`ρ` by `HJO.Sweep.exists_action_atilde` and `σ` by
`HJO.Dyck.Tilde.Atilde.exists_isStarSwap` — so what comes out is an
actual pair for which the repaired statement's conclusion is false, and not the negation of an
unsatisfiable hypothesis. The conjugator is left as a hypothesis because
`HJO.Sym.exists_isMacdonaldConjugator` supplies it at its own side conditions.

The hypotheses on the bar are `HJO.Sym.paramInvLambda` exactly: it inverts `q` and `u` and is an
involution. `[Invertible u]` is what the star swap needs for the third mixed relation, and
`q + 1 ≠ 0` is what the action needs; `M ≠ 0` is what `HJO.Sym.exists_isMacdonaldConjugator` and
`HJO.Sweep.conjugation_eq_signGrading_conjugator_omegaBar` already carry. `bar q = q⁻¹` and the
`bar q = ⅟q` that `exists_isStarSwap` asks for are two terms for one element, bridged by
`invOf_eq_inv`. -/
theorem not_nablaConj_starSwap_exists [Invertible q] [Invertible (q - 1)] [Invertible u]
    {bar : L ≃+* L} (hq : bar q = q⁻¹) (hu : bar u = u⁻¹) (hbb : ∀ c : L, bar (bar c) = c)
    (hM : (1 - q) * (1 - u) ≠ 0) (hq1 : q + 1 ≠ 0)
    {nabla : Module.End L (Lambda L)} (hnab : IsMacdonaldConjugator q u nabla) :
    ∃ (ρ : Dyck.Tilde.Atilde L q u →ₐ[L] Module.End L (Vstar L))
      (sw : Dyck.Tilde.Atilde L q u →+ Dyck.Tilde.Atilde L q u),
      Dyck.IsStarSwap q bar (Dyck.Tilde.Atilde.e L q u) (Dyck.Tilde.Atilde.dPlus L q u)
          (Dyck.Tilde.Atilde.dPlusStar L q u) (Dyck.Tilde.Atilde.dMinus L q u)
          (Dyck.Tilde.Atilde.Tg L q u) sw
        ∧ ¬ ∀ f g : Lambda L,
            ρ (Dyck.Tilde.Atilde.dMinus L q u 0 * Dyck.Tilde.Atilde.dPlusStar L q u 0)
                  (vzero L f) = vzero L g →
              ρ (sw (Dyck.Tilde.Atilde.dMinus L q u 0 * Dyck.Tilde.Atilde.dPlusStar L q u 0))
                  (vzero L (nabla f)) = vzero L (nabla g) := by
  obtain ⟨ρ, -, -, hρd, hρp, hρs⟩ := exists_action_atilde q u hq1
  obtain ⟨sw, hsw⟩ := Dyck.Tilde.Atilde.exists_isStarSwap (bar := bar)
    (by rw [hq, invOf_eq_inv]) (by rw [hu, invOf_eq_inv]) hbb
  exact ⟨ρ, sw, hsw,
    not_nablaConj_starSwap_dminus_dPlusStar hq hu hM hnab hρd hρp hρs hsw⟩

end Field

end HJO.Sweep

end
