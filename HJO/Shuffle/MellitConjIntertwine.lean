/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.ConjugationBottomExists
public import HJO.CMStructure.ConjugationExists
public import HJO.Shuffle.MellitNablaConjStarRefuted
public meta import HJO.Attr

/-! # The conjugation operator realises the star swap on all of `Ã`

The intertwining `HJO.Sweep.conj_intertwines` has two natural `∇`-forms and both are false: with
the twisting endomorphism `Φ_c` (`HJO.Sweep.not_nablaConj_dminus_dPlusStar`,
`HJO/Shuffle/MellitNablaConjRefuted.lean`) and with the star swap `σ`
(`HJO.Sweep.not_nablaConj_starSwap_dminus_dPlusStar`,
`HJO/Shuffle/MellitNablaConjStarRefuted.lean`). **Both refutations are refutations of the
operator on the left, not of the twist on the right**: they kill `∇`, the Macdonald conjugator, and
each does so at `L = d₋d^*₊`.

This file states and proves the intertwining with a different operator on the left —
the **conjugation operator** `𝒩` of `HJO.Sweep.IsConjugationOperator`, whose action on `V_0` is
`f ↦ ε_±(∇(ω̄f))` by `HJO.Sweep.conjugation_eq_signGrading_conjugator_omegaBar`. The
twist stays the star swap `σ` of `HJO.Dyck.Tilde.Atilde.exists_isStarSwap`.

## The statement

`HJO.Sweep.conj_intertwines`: for `𝒩` a conjugation operator over the bar `bar`, `σ` a star swap of
`Ã` over the *same* `bar`, and `ρ` an action of `Ã` on `V_*` of the shape
`HJO.Sweep.exists_action_atilde` supplies,

  `𝒩(ρ(x)F) = ρ(σ x)(𝒩F)`   for every `x ∈ Ã` and every `F ∈ V_*`.

Since `𝒩` is an involution this is `𝒩ρ(x)𝒩^{-1} = ρ(σ x)`, the intended conclusion, and it is
proved on all of `Ã` and all of `V_*` rather than on `e_0Ãe_0` and `V_0` — there is no `e_0Ãe_0`
object in this library (only the one-sided `HJO.Dyck.Tilde.Atilde.atildeE0`), and the stronger
form is what the induction produces. `HJO.Sweep.conj_starSwap_vzero` is the specialisation to
`V_0` in the exact implication shape the two refutations negate, so the three statements are
directly comparable.

## Why the two defects of the `∇`/`σ` form are gone

* **The witness.** The refutation ran `σ(d₋d^*₊) = d₋d₊` against `HJO.Sym.IsMacdonaldConjugator`,
  whose clause landing on `e_1·` starts from `D^*_1` and not from `D_1`, forcing `D^*_1 = -D_1`. For
  `𝒩` the corresponding two facts are *both already proved*, in `ConjugationBottom`:
  `HJO.Sweep.conj_vzero_elemSymm_one_mul` (the `d₋d₊` direction) and
  `HJO.Sweep.conj_vzero_neg_dop_one` (the `d₋d^*₊` direction). The `ω̄` inside
  `f ↦ ε_±(∇(ω̄f))` is exactly what converts `D_1` into `D^*_1`, which is the gap the refutation
  measured. Both witnesses are discharged here explicitly:
  `HJO.Sweep.conj_starSwap_dminus_dPlusStar` and `HJO.Sweep.conj_starSwap_dminus_dPlus`.
* **The semilinearity.** `HJO.Sweep.not_nablaConj_starSwap_smul` refutes the `∇` form on scalars
  alone, `σ` being bar-semilinear while `∇` is `L`-linear. `𝒩` is bar-semilinear too
  (`IsConjugationOperator.map_smul`) over the *same* bar, so the two semilinearities cancel: that is
  the `grade0` case of the induction below, and it needs `bar` on both sides to close.

## The two clauses at `e_k` and at the loops

Extending letterwise clauses to the whole algebra is an induction over the generators of `Ã` —
`e_k`, `d₋`, `d₊`, `d^*₊` and the loops `T_i` — so it needs a clause at every generator. Beside the
`d₋` and `d₊` clauses, `HJO.Sweep.IsConjugationOperator` supplies the two others:

* that `𝒩` **preserves each summand** `V_k` (`IsConjugationOperator.map_piece`, read on all of
  `V_*` as `HJO.Sweep.IsConjugationOperator.pieceProj_comm`). This is the `e_k` case, and it is also
  what makes the `d^*₊` case available at all: the reverse clause `𝒩d^*₊ = d₊𝒩` is derived from
  `𝒩𝒩 = id` and needs the argument of the substitution to lie in a summand
  (`HJO.Sweep.conj_dplusStar_ofPiece_of_eq`, the level-`k` form of
  `HJO.Sweep.conj_dplusStar_vzero_of_eq`);
* the clause at the **loops**, `𝒩T_i = T̂_i𝒩` (`IsConjugationOperator.map_loop`), the star swap
  carrying each loop to the polynomial inverse of `HJO.Dyck.braidInvGen` and *not* fixing it.

The theorems below take the two as the hypotheses `hproj` and `hT`, in the form the induction
reads them: `hproj` is `HJO.Sweep.IsConjugationOperator.pieceProj_comm`, and `hT` is
`IsConjugationOperator.map_loop` read through the images of the loops under `ρ` and `σ`.

The two clauses cost nothing on either side. `HJO.Sweep.pieceProj_comm_of_intertwines` and
`HJO.Sweep.isConjugationOperator_of_intertwines` show that the conclusion *implies* both, so given
the other five clauses the statement is **equivalent** to them. And the existence statement gets
them for free: `HJO.Sweep.exists_conj_intertwines_of_evalOne` proves that the transport of
`HJO.Sweep.exists_isConjugationOperator` — `HJO.Sweep.exists_isConjugationOperator_of_evalOne`, run
on the same two kernel containments and nothing else — satisfies the full intertwining outright,
with no induction.

## Main results

* `HJO.Sweep.conj_dplusStar_ofPiece_of_eq` — `𝒩d^*₊ = d₊𝒩` at the `k`-th summand.
* `HJO.Sweep.conj_intertwines` — **the intertwining**: `𝒩ρ(x) = ρ(σx)𝒩` for every `x ∈ Ã`.
* `HJO.Sweep.conj_starSwap_vzero` — the same on `V_0`, in the shape the refutations negate.
* `HJO.Sweep.conj_starSwap_dminus_dPlusStar`, `HJO.Sweep.conj_starSwap_dminus_dPlus` — the two
  witnesses, the first being the one that refutes both `∇`-forms.
* `HJO.Sweep.pieceProj_comm_of_intertwines`, `HJO.Sweep.isConjugationOperator_of_intertwines` — the
  converse: the intertwining implies the summand and loop clauses, and with antilinearity,
  involutivity and `𝒩1 = 1` it implies `HJO.Sweep.IsConjugationOperator` in full.
* `HJO.Sweep.exists_conj_intertwines_of_evalOne` — the transport satisfies the intertwining, so
  every clause is free on the existence side.

## References

A. Mellit, *Toric braids and `(m,n)`-parking functions*, arXiv:1604.07456, §3.7, Proposition 3.10:
`∇L∇^{-1} = N(L)` on `Λ` for `L ∈ e_0𝔸_{q,t}e_0`.
-/

@[expose] public section

namespace HJO.Sweep

open HJO.Sym

/-! ### Reading the three arrow families off a point of `V_*` -/

section Apply

variable {L : Type*} [CommRing L]

/-- The raising family, applied to an arbitrary point of `V_*`: it reads the `k`-th summand and
lands in the `(k+1)`-st. This is the definition unfolded, and it is what lets a clause of
`HJO.Sweep.IsConjugationOperator` — stated at `ofPiece` — be applied to a point with no summand
hypothesis. -/
theorem raiseVstar_apply (U : ∀ k : ℕ, pieceSub L k →ₗ[L] pieceSub L (k + 1)) (k : ℕ)
    (F : Vstar L) : raiseVstar U k F = ofPiece L (k + 1) (U k (toPiece L k F)) := rfl

/-- The lowering family, applied to an arbitrary point of `V_*`. -/
theorem lowerVstar_apply (D : ∀ k : ℕ, pieceSub L (k + 1) →ₗ[L] pieceSub L k) (k : ℕ)
    (F : Vstar L) : lowerVstar D k F = ofPiece L k (D k (toPiece L (k + 1) F)) := rfl

end Apply

/-! ### The reverse starred clause at an arbitrary summand -/

section Reverse

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L} {bar : L ≃+* L}
  {N : Vstar L →+ Vstar L}

/-- **`𝒩d^*₊ = d₊𝒩` on the `k`-th summand, wherever `𝒩` maps it there.** This is
`HJO.Sweep.conj_dplusStar_vzero_of_eq` with `V_0` replaced by an arbitrary `V_k`: the
step "`𝒩𝒩 = id` and `𝒩d₊ = d^*₊𝒩` give `𝒩d^*₊ = d₊𝒩`", with the hypothesis that step needs, namely
that the substitution `F := 𝒩F` lands in a summand.

The generalisation is what the induction of `HJO.Sweep.conj_intertwines` consumes: the letter `d^*₊`
occurs inside a word at every level, not only at the bottom. -/
theorem conj_dplusStar_ofPiece_of_eq (hN : IsConjugationOperator q u bar N) {k : ℕ}
    {F G : pieceSub L k} (hFG : N (ofPiece L k F) = ofPiece L k G) :
    N (dplusStarVstar q u (ofPiece L k F)) = cmDPlusVstar q (ofPiece L k G) := by
  have hGF : N (ofPiece L k G) = ofPiece L k F := by rw [← hFG, hN.involutive]
  have hstep : N (cmDPlusVstar q (ofPiece L k G)) = dplusStarVstar q u (ofPiece L k F) := by
    rw [hN.map_dplus k G, hGF]
  rw [← hstep, hN.involutive]

end Reverse

/-! ### The intertwining -/

section Intertwine

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L} [Invertible q] [Invertible (q - 1)]
  {bar : L ≃+* L} {N : Vstar L →+ Vstar L}
  {ρ : Dyck.Tilde.Atilde L q u →ₐ[L] Module.End L (Vstar L)}
  {sw : Dyck.Tilde.Atilde L q u →+ Dyck.Tilde.Atilde L q u}

/-- **With the conjugation operator in place of the Macdonald
conjugator.** For `𝒩` a conjugation operator of `HJO.Sweep.IsConjugationOperator` over the bar
`bar`, `σ` a star swap of `Ã` over the same bar, and `ρ` an action of `Ã` on `V_*` of the shape
`HJO.Sweep.exists_action_atilde` supplies,

  `𝒩(ρ(x)F) = ρ(σ x)(𝒩F)`   for every `x ∈ Ã`, `F ∈ V_*`,

which for the involution `𝒩` is `𝒩ρ(x)𝒩^{-1} = ρ(σ x)`: conjugation by `𝒩` realises the star swap
on the whole algebra and not merely on the two elements
`HJO.Sweep.conjugation_eq_signGrading_conjugator_omegaBar` pins.

Two letterwise hypotheses are carried in the form the induction reads them: `hproj`, that `𝒩`
commutes with each projection, which is the summand clause of `HJO.Sweep.IsConjugationOperator`
(`HJO.Sweep.IsConjugationOperator.pieceProj_comm`), and `hT`, the clause at the loops, which is
`IsConjugationOperator.map_loop` read through the images of the loops under `ρ` and `σ`. They are
not extra strength — the conclusion implies both (`HJO.Sweep.pieceProj_comm_of_intertwines`, and
`hT` by reading the conclusion at `x = T_i`) — and they are free on the existence side
(`HJO.Sweep.exists_conj_intertwines_of_evalOne`).

The proof is the induction over the generators of `Ã`: every `x` is `mk w` for a `w` in the free
algebra on the five generator families, by `RingQuot.mkAlgHom_surjective`, and

* `grade0` is where the two bar-semilinearities cancel — the defect that
  `HJO.Sweep.not_nablaConj_starSwap_smul` turns into `q^2 = 1` for an `L`-linear `∇`;
* `vertex` is `hproj`, `down` is `map_dminus`, `up` is `map_dplus`, `upStar` is
  `HJO.Sweep.conj_dplusStar_ofPiece_of_eq` and `braid` is `hT`, each read at the summand `hproj`
  puts `𝒩F` in;
* `mul` and `add` are multiplicativity and additivity of `ρ` and of `σ`.

No hypothesis on the parameters beyond `HJO.Dyck.Tilde.Atilde`'s own `Invertible q` and
`Invertible (q-1)` is used: in particular `M = (1-q)(1-u) ≠ 0` is *not* used, unlike in both
refutations, and `u` need not be invertible — `[Invertible u]` is what *producing* a star swap needs
(`HJO.Dyck.Tilde.Atilde.exists_isStarSwap`), not what using one needs. -/
@[hjo "lem_mellit_ns_nabla_conj"]
theorem conj_intertwines (hN : IsConjugationOperator q u bar N)
    (hproj : ∀ (k : ℕ) (F : Vstar L), N (pieceProj L k F) = pieceProj L k (N F))
    (hρe : ∀ k : ℕ, ρ (Dyck.Tilde.Atilde.e L q u k) = pieceProj L k)
    (hρd : ∀ k : ℕ, ρ (Dyck.Tilde.Atilde.dMinus L q u k) = lowerVstar (dminusPiece q) k)
    (hρp : ∀ k : ℕ, ρ (Dyck.Tilde.Atilde.dPlus L q u k) = raiseVstar (cmDPlusPiece q) k)
    (hρs : ∀ k : ℕ,
      ρ (Dyck.Tilde.Atilde.dPlusStar L q u k) = raiseVstar (dplusStarPiece q u) k)
    (hsw : Dyck.IsStarSwap q bar (Dyck.Tilde.Atilde.e L q u) (Dyck.Tilde.Atilde.dPlus L q u)
      (Dyck.Tilde.Atilde.dPlusStar L q u) (Dyck.Tilde.Atilde.dMinus L q u)
      (Dyck.Tilde.Atilde.Tg L q u) sw)
    (hT : ∀ (k i : ℕ) (F : Vstar L), N (ρ (Dyck.Tilde.Atilde.Tg L q u k i) F)
      = ρ (sw (Dyck.Tilde.Atilde.Tg L q u k i)) (N F))
    (x : Dyck.Tilde.Atilde L q u) (F : Vstar L) :
    N (ρ x F) = ρ (sw x) (N F) := by
  suffices h : ∀ w : FreeAlgebra L Dyck.Tilde.Gen, ∀ G : Vstar L,
      N (ρ (Dyck.Tilde.Atilde.mk L q u w) G)
        = ρ (sw (Dyck.Tilde.Atilde.mk L q u w)) (N G) by
    obtain ⟨w, rfl⟩ := RingQuot.mkAlgHom_surjective L (Dyck.Tilde.Rel L q u) x
    exact h w F
  intro w
  induction w using FreeAlgebra.induction with
  | grade0 r =>
    intro G
    have hm : Dyck.Tilde.Atilde.mk L q u (algebraMap L (FreeAlgebra L Dyck.Tilde.Gen) r)
        = r • (1 : Dyck.Tilde.Atilde L q u) := by
      rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
    rw [hm, map_smul, hsw.map_smul, hsw.map_one, map_smul, map_one, LinearMap.smul_apply,
      Module.End.one_apply, hN.map_smul, LinearMap.smul_apply, Module.End.one_apply]
  | grade1 g =>
    cases g with
    | vertex k =>
      intro G
      change N (ρ (Dyck.Tilde.Atilde.e L q u k) G)
        = ρ (sw (Dyck.Tilde.Atilde.e L q u k)) (N G)
      rw [hsw.map_e, hρe, hproj]
    | up k =>
      intro G
      change N (ρ (Dyck.Tilde.Atilde.dPlus L q u k) G)
        = ρ (sw (Dyck.Tilde.Atilde.dPlus L q u k)) (N G)
      rw [hsw.map_dPlus, hρp, hρs, raiseVstar_apply, raiseVstar_apply,
        ← cmDPlusVstar_ofPiece, hN.map_dplus k, ← pieceProj_apply, hproj, pieceProj_apply,
        dplusStarVstar_ofPiece]
    | upStar k =>
      intro G
      change N (ρ (Dyck.Tilde.Atilde.dPlusStar L q u k) G)
        = ρ (sw (Dyck.Tilde.Atilde.dPlusStar L q u k)) (N G)
      rw [hsw.map_dPlusStar, hρs, hρp, raiseVstar_apply, raiseVstar_apply,
        ← dplusStarVstar_ofPiece,
        conj_dplusStar_ofPiece_of_eq hN
          (show N (ofPiece L k (toPiece L k G)) = ofPiece L k (toPiece L k (N G)) by
            rw [← pieceProj_apply, hproj, pieceProj_apply]),
        cmDPlusVstar_ofPiece]
    | down k =>
      intro G
      change N (ρ (Dyck.Tilde.Atilde.dMinus L q u k) G)
        = ρ (sw (Dyck.Tilde.Atilde.dMinus L q u k)) (N G)
      rw [hsw.map_dMinus, hρd, lowerVstar_apply, lowerVstar_apply,
        ← dminusVstar_ofPiece, hN.map_dminus k, ← pieceProj_apply, hproj, pieceProj_apply,
        dminusVstar_ofPiece]
    | braid k i =>
      intro G
      exact hT k i G
  | mul a b ha hb =>
    intro G
    rw [map_mul, map_mul, Module.End.mul_apply, ha, hb, hsw.map_mul, map_mul,
      Module.End.mul_apply]
  | add a b ha hb =>
    intro G
    rw [map_add, map_add, LinearMap.add_apply, map_add, ha, hb, map_add, map_add,
      LinearMap.add_apply]

/-- **The intertwining on `V_0`, in the implication shape the two refutations negate.**
`𝒩ρ(x)𝒩^{-1} = σ(x)` on `V_0` says that whenever `x` carries `f` to `g` there, `σ(x)` carries `𝒩f`
to `𝒩g`; this is that
statement, with `∇` replaced by `𝒩`. Compare `HJO.Sweep.not_nablaConj_dminus_dPlusStar` and
`HJO.Sweep.not_nablaConj_starSwap_dminus_dPlusStar`, which are the same implication with `∇` and are
false. -/
theorem conj_starSwap_vzero (hN : IsConjugationOperator q u bar N)
    (hproj : ∀ (k : ℕ) (F : Vstar L), N (pieceProj L k F) = pieceProj L k (N F))
    (hρe : ∀ k : ℕ, ρ (Dyck.Tilde.Atilde.e L q u k) = pieceProj L k)
    (hρd : ∀ k : ℕ, ρ (Dyck.Tilde.Atilde.dMinus L q u k) = lowerVstar (dminusPiece q) k)
    (hρp : ∀ k : ℕ, ρ (Dyck.Tilde.Atilde.dPlus L q u k) = raiseVstar (cmDPlusPiece q) k)
    (hρs : ∀ k : ℕ,
      ρ (Dyck.Tilde.Atilde.dPlusStar L q u k) = raiseVstar (dplusStarPiece q u) k)
    (hsw : Dyck.IsStarSwap q bar (Dyck.Tilde.Atilde.e L q u) (Dyck.Tilde.Atilde.dPlus L q u)
      (Dyck.Tilde.Atilde.dPlusStar L q u) (Dyck.Tilde.Atilde.dMinus L q u)
      (Dyck.Tilde.Atilde.Tg L q u) sw)
    (hT : ∀ (k i : ℕ) (F : Vstar L), N (ρ (Dyck.Tilde.Atilde.Tg L q u k i) F)
      = ρ (sw (Dyck.Tilde.Atilde.Tg L q u k i)) (N F))
    (x : Dyck.Tilde.Atilde L q u) {f g : Lambda L} (hx : ρ x (vzero L f) = vzero L g) :
    ρ (sw x) (N (vzero L f)) = N (vzero L g) := by
  rw [← conj_intertwines hN hproj hρe hρd hρp hρs hsw hT x, hx]

/-- **The witness that refutes both `∇`-forms of the statement, discharged.** At `x = d₋d^*₊`, which
acts on `V_0` as `-D_1` (`HJO.Sweep.dop_one_eq_neg_dminusCM_dplusStar`) while `σ(x) = d₋d₊` acts as
`e_1·` (`HJO.Sweep.dminusCM_cmDPlus_C`), the statement reads `𝒩(-D_1f) = e_1·𝒩f`. For the Macdonald
conjugator that forced `D^*_1 = -D_1` and so `M = 0`
(`HJO.Sweep.not_nablaConj_starSwap_dminus_dPlusStar`); for the conjugation operator it is
`HJO.Sweep.conj_vzero_neg_dop_one`, already proved, the `ω̄` inside `f ↦ ε_±(∇(ω̄f))` supplying
exactly the `D_1 ↦ D^*_1` that the refutation showed was missing. -/
theorem conj_starSwap_dminus_dPlusStar (hN : IsConjugationOperator q u bar N)
    (hproj : ∀ (k : ℕ) (F : Vstar L), N (pieceProj L k F) = pieceProj L k (N F))
    (hρe : ∀ k : ℕ, ρ (Dyck.Tilde.Atilde.e L q u k) = pieceProj L k)
    (hρd : ∀ k : ℕ, ρ (Dyck.Tilde.Atilde.dMinus L q u k) = lowerVstar (dminusPiece q) k)
    (hρp : ∀ k : ℕ, ρ (Dyck.Tilde.Atilde.dPlus L q u k) = raiseVstar (cmDPlusPiece q) k)
    (hρs : ∀ k : ℕ,
      ρ (Dyck.Tilde.Atilde.dPlusStar L q u k) = raiseVstar (dplusStarPiece q u) k)
    (hsw : Dyck.IsStarSwap q bar (Dyck.Tilde.Atilde.e L q u) (Dyck.Tilde.Atilde.dPlus L q u)
      (Dyck.Tilde.Atilde.dPlusStar L q u) (Dyck.Tilde.Atilde.dMinus L q u)
      (Dyck.Tilde.Atilde.Tg L q u) sw)
    (hT : ∀ (k i : ℕ) (F : Vstar L), N (ρ (Dyck.Tilde.Atilde.Tg L q u k i) F)
      = ρ (sw (Dyck.Tilde.Atilde.Tg L q u k i)) (N F))
    (f : Lambda L) :
    ρ (Dyck.Tilde.Atilde.dMinus L q u 0 * Dyck.Tilde.Atilde.dPlus L q u 0)
        (N (vzero L f)) = N (vzero L (-Dop q u 1 f)) := by
  have hswap : sw (Dyck.Tilde.Atilde.dMinus L q u 0 * Dyck.Tilde.Atilde.dPlusStar L q u 0)
      = Dyck.Tilde.Atilde.dMinus L q u 0 * Dyck.Tilde.Atilde.dPlus L q u 0 := by
    rw [hsw.map_mul, hsw.map_dMinus, hsw.map_dPlusStar]
  rw [← hswap]
  exact conj_starSwap_vzero hN hproj hρe hρd hρp hρs hsw hT _
    (action_dMinus_mul_dPlusStar_vzero hρd hρs f)

/-- **The other witness.** At `x = d₋d₊`, acting on `V_0` as
`e_1·`, with `σ(x) = d₋d^*₊` acting as `-D_1`, the statement reads `𝒩(e_1f) = -D_1𝒩f`. This is the
direction the `∇` form gets right; it is `HJO.Sweep.conj_vzero_elemSymm_one_mul` for `𝒩`, and it is
recorded here because checking this witness alone does not distinguish `𝒩` from `∇`: only the
other one does. -/
theorem conj_starSwap_dminus_dPlus (hN : IsConjugationOperator q u bar N)
    (hproj : ∀ (k : ℕ) (F : Vstar L), N (pieceProj L k F) = pieceProj L k (N F))
    (hρe : ∀ k : ℕ, ρ (Dyck.Tilde.Atilde.e L q u k) = pieceProj L k)
    (hρd : ∀ k : ℕ, ρ (Dyck.Tilde.Atilde.dMinus L q u k) = lowerVstar (dminusPiece q) k)
    (hρp : ∀ k : ℕ, ρ (Dyck.Tilde.Atilde.dPlus L q u k) = raiseVstar (cmDPlusPiece q) k)
    (hρs : ∀ k : ℕ,
      ρ (Dyck.Tilde.Atilde.dPlusStar L q u k) = raiseVstar (dplusStarPiece q u) k)
    (hsw : Dyck.IsStarSwap q bar (Dyck.Tilde.Atilde.e L q u) (Dyck.Tilde.Atilde.dPlus L q u)
      (Dyck.Tilde.Atilde.dPlusStar L q u) (Dyck.Tilde.Atilde.dMinus L q u)
      (Dyck.Tilde.Atilde.Tg L q u) sw)
    (hT : ∀ (k i : ℕ) (F : Vstar L), N (ρ (Dyck.Tilde.Atilde.Tg L q u k i) F)
      = ρ (sw (Dyck.Tilde.Atilde.Tg L q u k i)) (N F))
    (f : Lambda L) :
    ρ (Dyck.Tilde.Atilde.dMinus L q u 0 * Dyck.Tilde.Atilde.dPlusStar L q u 0)
        (N (vzero L f)) = N (vzero L (elemSymm L 1 * f)) := by
  have hswap : sw (Dyck.Tilde.Atilde.dMinus L q u 0 * Dyck.Tilde.Atilde.dPlus L q u 0)
      = Dyck.Tilde.Atilde.dMinus L q u 0 * Dyck.Tilde.Atilde.dPlusStar L q u 0 := by
    rw [hsw.map_mul, hsw.map_dMinus, hsw.map_dPlus]
  rw [← hswap]
  exact conj_starSwap_vzero hN hproj hρe hρd hρp hρs hsw hT _
    (action_dMinus_mul_dPlus_vzero hρd hρp f)

end Intertwine

/-! ### The converse: the intertwining implies the two extra clauses, and
`HJO.Sweep.IsConjugationOperator` -/

section Converse

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L} [Invertible q] [Invertible (q - 1)]
  {bar : L ≃+* L} {N : Vstar L →+ Vstar L}
  {ρ : Dyck.Tilde.Atilde L q u →ₐ[L] Module.End L (Vstar L)}
  {sw : Dyck.Tilde.Atilde L q u →+ Dyck.Tilde.Atilde L q u}

variable (hint : ∀ (x : Dyck.Tilde.Atilde L q u) (F : Vstar L), N (ρ x F) = ρ (sw x) (N F))
  (hρe : ∀ k : ℕ, ρ (Dyck.Tilde.Atilde.e L q u k) = pieceProj L k)
  (hswe : ∀ k : ℕ, sw (Dyck.Tilde.Atilde.e L q u k) = Dyck.Tilde.Atilde.e L q u k)

include hint hρe hswe

omit [Algebra ℚ L] in
/-- **The intertwining forces `𝒩` to preserve each summand**: read it at `x = e_k`, whose image
under `ρ` is the projection onto `V_k` and which the star swap fixes. So `hproj` is not an extra
assumption of `HJO.Sweep.conj_intertwines` but a *consequence* of its conclusion; it is the summand
clause of `HJO.Sweep.IsConjugationOperator`. -/
theorem pieceProj_comm_of_intertwines (k : ℕ) (F : Vstar L) :
    N (pieceProj L k F) = pieceProj L k (N F) := by
  have h := hint (Dyck.Tilde.Atilde.e L q u k) F
  rwa [hρe, hswe, hρe] at h

omit [Algebra ℚ L] in
/-- **`𝒩` lands in the summand it started in.** The form the two clauses of
`HJO.Sweep.IsConjugationOperator` need: `𝒩(ofPiece k F)` is itself an `ofPiece k`. -/
theorem ofPiece_eq_of_intertwines (k : ℕ) (F : pieceSub L k) :
    N (ofPiece L k F) = ofPiece L k (toPiece L k (N (ofPiece L k F))) := by
  have h := pieceProj_comm_of_intertwines hint hρe hswe k (ofPiece L k F)
  rwa [pieceProj_ofPiece, pieceProj_apply] at h

/-- **The intertwining, with the three clauses that do not mention the algebra, is
`HJO.Sweep.IsConjugationOperator`.** Together with `HJO.Sweep.conj_intertwines` this makes the
statement *equivalent* to `hproj` and `hT` given antilinearity, involutivity and `𝒩1 = 1`: the
intertwining is exactly the letterwise clauses at all five generator families, which
`HJO.Sweep.IsConjugationOperator` states at `d₋`, `d₊`, `e_k` (the summand clause) and the loops,
the `d^*₊` one following from `𝒩𝒩 = id`. The loops are read through `hρT`, their image under `ρ`,
and `hswT`, the clause `σ(T_i) = T̂_i` of a star swap. -/
theorem isConjugationOperator_of_intertwines
    (hρd : ∀ k : ℕ, ρ (Dyck.Tilde.Atilde.dMinus L q u k) = lowerVstar (dminusPiece q) k)
    (hρp : ∀ k : ℕ, ρ (Dyck.Tilde.Atilde.dPlus L q u k) = raiseVstar (cmDPlusPiece q) k)
    (hρs : ∀ k : ℕ,
      ρ (Dyck.Tilde.Atilde.dPlusStar L q u k) = raiseVstar (dplusStarPiece q u) k)
    (hswd : ∀ k : ℕ, sw (Dyck.Tilde.Atilde.dMinus L q u k) = Dyck.Tilde.Atilde.dMinus L q u k)
    (hswp : ∀ k : ℕ, sw (Dyck.Tilde.Atilde.dPlus L q u k) = Dyck.Tilde.Atilde.dPlusStar L q u k)
    (hρT : ∀ k i : ℕ, ρ (Dyck.Tilde.Atilde.Tg L q u k i) = loopVstar (braidModPiece q) k i)
    (hswT : ∀ {k i : ℕ}, i + 2 ≤ k → sw (Dyck.Tilde.Atilde.Tg L q u k i)
      = Dyck.tinvOf q ⅟q (Dyck.Tilde.Atilde.Tg L q u k i) (Dyck.Tilde.Atilde.e L q u k))
    (hsmul : ∀ (c : L) (F : Vstar L), N (c • F) = bar c • N F)
    (hinv : ∀ F : Vstar L, N (N F) = F) (hone : N (oneVstar L) = oneVstar L) :
    IsConjugationOperator q u bar N where
  map_smul := hsmul
  involutive := hinv
  map_one := hone
  map_dminus k F := by
    have h := hint (Dyck.Tilde.Atilde.dMinus L q u k) (ofPiece L (k + 1) F)
    rw [hρd, hswd, hρd, lowerVstar_ofPiece, ← dminusVstar_ofPiece,
      ofPiece_eq_of_intertwines hint hρe hswe (k + 1) F, lowerVstar_ofPiece,
      ← dminusVstar_ofPiece, ← ofPiece_eq_of_intertwines hint hρe hswe (k + 1) F] at h
    exact h
  map_dplus k F := by
    have h := hint (Dyck.Tilde.Atilde.dPlus L q u k) (ofPiece L k F)
    rw [hρp, hswp, hρs, raiseVstar_ofPiece, ← cmDPlusVstar_ofPiece,
      ofPiece_eq_of_intertwines hint hρe hswe k F, raiseVstar_ofPiece,
      ← dplusStarVstar_ofPiece, ← ofPiece_eq_of_intertwines hint hρe hswe k F] at h
    exact h
  map_piece k F := ⟨_, ofPiece_eq_of_intertwines hint hρe hswe k F⟩
  map_loop {k i} hik F := by
    have h := hint (Dyck.Tilde.Atilde.Tg L q u k i) F
    rw [hswT hik, hρT, Dyck.tinvOf, map_smul, map_add, map_smul, hρT, hρe, invOf_eq_inv] at h
    exact h

end Converse

/-! ### The intertwining is free on the existence side -/

section Transport

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L} [Invertible q] [Invertible (q - 1)]
  {bar : L ≃+* L}

omit [Algebra ℚ L] in
/-- **The transport of `HJO.Sweep.exists_isConjugationOperator` satisfies the full intertwining
outright.**

Run on exactly the inputs of `HJO.Sweep.exists_isConjugationOperator_of_evalOne` — the action, a
star swap, surjectivity of `fe_0 ↦ f(1)` from `Ã𝟏_0`, and `Ã𝟏_0 ∩ ker ⊆ I𝟏_0` — `F ↦ σ(x_F)(1)`
intertwines `ρ` with `σ` on all of `Ã`, with no clause added to `HJO.Sweep.IsConjugationOperator`
and no induction over generators: it is one line of `HJO.Sweep.evalOne_mul`, because `ρ(x)F` has the
preimage `x·x_F`.

This is what makes the summand and loop clauses of `HJO.Sweep.IsConjugationOperator` cost
the *existence* statement nothing: they are necessary for `HJO.Sweep.conj_intertwines`
(`HJO.Sweep.pieceProj_comm_of_intertwines`), and the transport satisfies them outright, the loop
clause being the star swap's `map_T` read through the action.

The two containments are hypotheses here; both are proved in
`HJO/CMStructure/Thm73Closed.lean` (`HJO.Sweep.exists_mem_atildeE0_evalOne_eq` and
`HJO.Sweep.atildeE0_inf_ker_evalOne_eq`), where `HJO.Sweep.exists_isConjugationOperator` is
proved. The three clauses returned beside the intertwining are
the ones that do not mention the algebra; `HJO.Sweep.isConjugationOperator_of_intertwines` turns the
package into `HJO.Sweep.IsConjugationOperator`. -/
theorem exists_conj_intertwines_of_evalOne
    (ρ : Dyck.Tilde.Atilde L q u →ₐ[L] Module.End L (Vstar L))
    {σA : Dyck.Tilde.Atilde L q u →+ Dyck.Tilde.Atilde L q u}
    (hρe : ∀ k : ℕ, ρ (Dyck.Tilde.Atilde.e L q u k) = pieceProj L k)
    (hρup : ∀ k : ℕ, ρ (Dyck.Tilde.Atilde.dPlus L q u k) = raiseVstar (cmDPlusPiece q) k)
    (hρupStar : ∀ k : ℕ,
      ρ (Dyck.Tilde.Atilde.dPlusStar L q u k) = raiseVstar (dplusStarPiece q u) k)
    (h : Dyck.IsStarSwap q bar (Dyck.Tilde.Atilde.e L q u) (Dyck.Tilde.Atilde.dPlus L q u)
      (Dyck.Tilde.Atilde.dPlusStar L q u) (Dyck.Tilde.Atilde.dMinus L q u)
      (Dyck.Tilde.Atilde.Tg L q u) σA)
    (hsurj : ∀ F : Vstar L, ∃ x ∈ Dyck.Tilde.Atilde.atildeE0 L q u, evalOne ρ x = F)
    (hker : Dyck.Tilde.Atilde.atildeE0 L q u ⊓ LinearMap.ker (evalOne ρ)
      ≤ Dyck.Tilde.Atilde.kernelIdealE0 L q u) :
    ∃ N : Vstar L →+ Vstar L,
      (∀ (c : L) (F : Vstar L), N (c • F) = bar c • N F)
      ∧ (∀ F : Vstar L, N (N F) = F)
      ∧ N (oneVstar L) = oneVstar L
      ∧ ∀ (x : Dyck.Tilde.Atilde L q u) (F : Vstar L), N (ρ x F) = ρ (σA x) (N F) := by
  choose sec hsecmem hsecval using hsurj
  have hrep : ∀ (F : Vstar L) (x : Dyck.Tilde.Atilde L q u),
      x ∈ Dyck.Tilde.Atilde.atildeE0 L q u → evalOne ρ x = F →
      evalOne ρ (σA (sec F)) = evalOne ρ (σA x) := fun F x hx hxval =>
    evalOne_starSwap_congr ρ hρe hρup hρupStar h hker (hsecmem F) hx (by rw [hsecval, hxval])
  have hadd : ∀ F G : Vstar L, evalOne ρ (σA (sec (F + G)))
      = evalOne ρ (σA (sec F)) + evalOne ρ (σA (sec G)) := by
    intro F G
    rw [hrep (F + G) (sec F + sec G) (add_mem (hsecmem F) (hsecmem G))
      (by rw [map_add, hsecval, hsecval]), map_add, map_add]
  refine ⟨AddMonoidHom.mk' (fun F => evalOne ρ (σA (sec F))) hadd, ?_, ?_, ?_, ?_⟩
  · intro c F
    change evalOne ρ (σA (sec (c • F))) = bar c • evalOne ρ (σA (sec F))
    rw [hrep (c • F) (c • sec F) (Submodule.smul_mem _ c (hsecmem F))
      (by rw [map_smul, hsecval]), h.map_smul, map_smul]
  · intro F
    change evalOne ρ (σA (sec (evalOne ρ (σA (sec F))))) = F
    rw [hrep (evalOne ρ (σA (sec F))) (σA (sec F))
      (Dyck.Tilde.Atilde.IsStarSwap.mem_atildeE0 h (hsecmem F)) rfl, h.involutive, hsecval]
  · change evalOne ρ (σA (sec (oneVstar L))) = oneVstar L
    rw [hrep (oneVstar L) (Dyck.Tilde.Atilde.e L q u 0) Dyck.Tilde.Atilde.e_zero_mem_atildeE0
      (evalOne_e_zero ρ hρe), h.map_e, evalOne_e_zero ρ hρe]
  · intro x F
    change evalOne ρ (σA (sec (ρ x F))) = ρ (σA x) (evalOne ρ (σA (sec F)))
    rw [hrep (ρ x F) (x * sec F) (Dyck.Tilde.Atilde.mul_mem_atildeE0 x (hsecmem F))
      (by rw [evalOne_mul, hsecval]), h.map_mul, evalOne_mul]

end Transport

/-! ### The intertwining's `V_0` content, unconditionally -/

section Bottom

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L} {σ : L ≃+* L}
  {nabla : Module.End L (Lambda L)} (hnabla : IsMacdonaldConjugator q u nabla)
  (hcomp : ∀ n : ℕ, ∀ f ∈ LambdaComp L n, nabla f ∈ LambdaComp L n)

include hnabla hcomp

/-- **The intertwining at the refuting witness `L = d₋d^*₊`, with no hypothesis about a conjugation
operator.** By `HJO.Sweep.conjugation_eq_signGrading_conjugator_omegaBar` a conjugation operator
acts on `V_0` as `M : f ↦ ε_±(∇(ω̄f))`, and `d₋d^*₊` acts there as `-D_1` while `σ(d₋d^*₊) = d₋d₊`
acts as `e_1·` (`HJO.Sweep.dop_one_eq_neg_dminusCM_dplusStar`, `HJO.Sweep.dminusCM_cmDPlus_C`). So
the statement at that witness says `M(-D_1f) = e_1·Mf`, and that is *true outright*: it is
`HJO.Sweep.signGrading_conjugator_omegaBar_dop_one` with the sign moved across.

This is the statement whose `∇`-shaped analogue `∇(-D_1f) = e_1∇f` is
`HJO.Sweep.not_nablaConj_starSwap_dminus_dPlusStar`, i.e. FALSE whenever `M ≠ 0`. The whole
difference is the `ω̄`, which turns `D_1` into `D^*_1` by `HJO.Sym.omegaBar_dop` and so feeds the
conjugator clause that actually lands on `e_1·`.

Its value here is that it needs no conjugation operator: only a Macdonald conjugator preserving the
components, which `HJO.Sym.exists_isMacdonaldConjugator` supplies. So the content of the statement
at the witness that refutes both `∇`-forms is *unconditionally true*, and the statement of
`HJO.Sweep.conj_intertwines` is not a negation dressed up as a theorem. The companion direction,
at `L = d₋d₊`, is `HJO.Sweep.signGrading_conjugator_omegaBar_elemSymm_one_mul`. -/
theorem signGrading_conjugator_omegaBar_neg_dop_one (hq : σ q = q⁻¹) (hu : σ u = u⁻¹)
    (f : Lambda L) :
    signGrading L (nabla (omegaBar σ (-Dop q u 1 f)))
      = elemSymm L 1 * signGrading L (nabla (omegaBar σ f)) := by
  rw [map_neg, map_neg, map_neg,
    signGrading_conjugator_omegaBar_dop_one hnabla hcomp hq hu, neg_neg]

end Bottom

end HJO.Sweep

end
