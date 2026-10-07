/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CMStructure.DminusSqBraid
public import HJO.CMStructure.EvalReduction
public import HJO.CMStructure.GammaBop
public import HJO.CMStructure.HbTwist
public import HJO.CMStructure.StarEasy
public import HJO.CMStructure.StarZrelShift
public import HJO.CMStructure.TwistedStarMult
public meta import HJO.Attr

/-! # The first starred commutator relation

`HJO.Sweep.dminusCM_starCommCM_braidInv`: for `k ≥ 2`, on `V_k`,
`d_-(d^*_+d_- - d_-d^*_+)T_{k-1}^{-1} = q^{-1}(d^*_+d_- - d_-d^*_+)d_-`.

## Main results

* `HJO.Sweep.dminusCM_starCommCM_braidInv`: the relation.
* `HJO.Sweep.starConj1`: the operator
  `A = d^*_+d_-^2 - (q+1)d_-d^*_+d_- + qd_-^2d^*_+`.
* `HJO.Sweep.starConj1_auxVar_pow`: **the evaluation**, the display
  `A(y_{k-1}^ay_k^b) = Γ_+(-uy_1)(uy_1(1-q)(B_aB_{b+1} - qB_{a+1}B_b))(1)`.
* `HJO.Sweep.starConj1_auxVar_pow_add_swap`: the evaluation is antisymmetric in `(a, b)`, which is
  `HJO.Sym.bop_pair_antisymm` read through `HJO.Sweep.bopExt_pair_antisymm`.
* `HJO.Sweep.starConj1_of_swapAux_eq`: `A` vanishes on the elements symmetric in `y_{k-1}, y_k`.
* `HJO.Sweep.starConj1_braid_add_q`: `A(T_{k-1}+q) = 0`, the reduced form of the relation.

## The three stages

The relation is `A(T_{k-1}+q) = 0` with `A = Cd_- - qd_-C` for `C` the starred commutator, and the
proof has three stages: the intertwining of the twisted multiplications and the corner
shifts reduce `A` to the monomials `y_{k-1}^ay_k^b`; there the three composites collapse, by three
uses of `HJO.Sweep.alphabetShift_bopExt`, to `Γ_+(-uy_1)(uy_1(1-q)(B_aB_{b+1} - qB_{a+1}B_b))(1)`;
and that bracket is antisymmetric in `a` and `b`.

`A` carries **one** starred raising, so the intertwining is
`∗_{0,k+2} → ∗_{1,k+1}` and the corner multiplier is `y_i ↦ y_{i+1}`; the two-variable
reduction `HJO.Sweep.eq_of_agree_auxVar_pow_two` is instantiated at `T c = σ_{1,k+1}(c)` and
`S i = y_{i+1}`, and its corner range `1 ≤ i ≤ k` is exactly the `i < k-1`. At `i = k+1`
the innermost `d_-` of the first term would have to pass `y_{k+1}` on `V_{k+1}`, which it does not,
so the range is exact.

The evaluation is where `Γ_+` enters, and it enters as a *pair* of one-letter shifts: on the
constants `d^*_+` adds the virtual alphabet `quy_1 - uy_1` (`HJO.Sweep.dplusStar_C_eq_starGamma`),
and `HJO.Sweep.alphabetShift_bopExt` is stated for a single letter. So the three composites are
pushed through `HJO.Sweep.starGammaQ` at the letter `quy_1` and `HJO.Sweep.starGammaPos` at `uy_1`,
each term coming out as `Γ_+(-uy_1)` of a product of two factors `B_{a+1} - cuy_1B_a` with
`c ∈ {1, q}`, all the `B`-words with two letters cancel, as does the one with none,
and what is left is the displayed bracket.

## `q + 1 ≠ 0`, and why the equivalence needs a hypothesis too

The usual proof says the statement "is equivalent to `A(T_{k-1}+q) = 0`" after "multiplying by
`q - 1 = (T_{k-1}-1) + (q - T_{k-1})`". Both halves of that equivalence cost a hypothesis.

Write `Δ := d^*_+d_-^2 + qd_-^2d^*_+ - d_-d^*_+d_-(T_{k-1}+q)`, so that the relation is `Δ = 0`
(this is the relation multiplied by `qT_{k-1}`, using `T_{k-1}^{-1} = (T_{k-1}+q-1)/q`). Then

* `Δ(T_{k-1}-1) = 0` unconditionally: `d_-^2T_{k-1} = d_-^2` is `HJO.Sweep.dminusCM_dminusCM_braid`,
  `d^*_+T_{k-1} = T_kd^*_+` is `HJO.Sweep.dplusStar_braidInv` (`HJO.Sweep.dplusStar_braid`) — at
  `i = k-1 < k`, inside its range — and `(T+q)(T-1) = 0` is the quadratic relation. This input
  is easy to overlook, and without it the stated equivalence is false in both directions.
* `A(T_{k-1}+q) = (1+q)Δ`, by the same two facts. So `A(T_{k-1}+q) = 0` gives `Δ = 0` only when
  `1 + q ≠ 0`, and at `q = -1` it gives nothing at all: there `T_{k-1}` is unipotent, the image of
  `T_{k-1}-1` sits inside the symmetric elements, and the two subspaces `A` is known to kill do not
  span `V_k`.

So `hq1 : q + 1 ≠ 0` is carried by the relation below, alongside the `hq : q ≠ 0` that
`T_{k-1}^{-1}` and `q^{-1}` need. It is the price of this route, not of the statement: the reduced
form `HJO.Sweep.starConj1_braid_add_q` is proved here for every `q`. The usual route pays a
different price — dividing by `q - 1` needs `q ≠ 1` — so it is not hypothesis-free either.

Every use instantiates it at `AlgebraicIndependent ℤ ![q, u]`, where `q` is transcendental over
`ℤ` and both hypotheses hold.

## Which convention

All-Carlsson--Mellit: `d_-` is `HJO.Sweep.dminusCM`, not the
modified `d^♭_-`, and `d^*_+` is `HJO.Sweep.dplusStar`. The commutator is `HJO.Sweep.starCommCM`,
the one `HJO.Sweep.starCommCM_cmDPlus` already uses, so no second reading of `C` enters the
library.

The symmetric-element step divides by `2`, which is free: `L` is a `ℚ`-algebra, hence of
characteristic zero.

## References

The lemma `HJO.Sweep.dminusCM_starCommCM_braidInv`, using `HJO.Sweep.piece`, `HJO.Sweep.braid`,
`HJO.Sweep.dminusCM` and `HJO.Sweep.dplusStar`, proved from `HJO.Sweep.braid_braid_apply`,
`HJO.Sweep.braid_sub_self`, `HJO.Sweep.dplusStar_twistedActionMult`,
`HJO.Sweep.dminusCM_twistedActionMult`, `HJO.Sweep.dplusStar_braidInv`,
`HJO.Sweep.alphabetShift_bopExt`, `HJO.Sym.bop_pair_antisymm` and
`HJO.Sweep.exists_basis_vstar_prod_bop`, and consumed by `HJO.Sweep.exists_isDpaAction_star`.
Transcribing E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, §5.
-/

@[expose] public section

namespace HJO.Sweep

/-! ### The letter the starred raising operator adds -/

section Letter

variable {L : Type*} [Field L]

/-- The letter `uy_1` that `d^*_+` wraps the undilated letter of its substitution to. -/
noncomputable def starLetter (u : L) : Total L := scal u * auxVar 1

theorem scal_mem_auxSubalg (x : L) : (scal x : Total L) ∈ auxSubalg L :=
  (auxSubalg L).algebraMap_mem x

theorem starLetter_mem_auxSubalg (u : L) : starLetter u ∈ auxSubalg L :=
  mul_mem (scal_mem_auxSubalg u) (auxVar_mem_auxSubalg 1)

theorem starLetter_mem_piece (u : L) (m : ℕ) (hm : 1 ≤ m) : starLetter u ∈ piece L m :=
  mul_mem (scal_mem_piece u m) (auxVar_mem_piece (le_refl 1) hm)

/-- **`Γ₊(uy_1)`**, the one-letter shift at the letter `d^*_+` wraps. -/
noncomputable def starGammaPos (u : L) : Total L →ₐ[L] Total L :=
  alphabetShift fun r => starLetter u ^ r

/-- **`Γ₊(-uy_1)`**, the inverse shift; this is the operator the evaluation displays in
front of the bracket. -/
noncomputable def starGammaNeg (u : L) : Total L →ₐ[L] Total L :=
  alphabetShift fun r => -(starLetter u ^ r)

/-- **`Γ₊(quy_1)`**, the one-letter shift at the *dilated* letter: `d^*_+` adds the virtual alphabet
`quy_1 - uy_1`, whose two letters are this one and `uy_1`. -/
noncomputable def starGammaQ (q u : L) : Total L →ₐ[L] Total L :=
  alphabetShift fun r => (scal q * starLetter u) ^ r

theorem starGammaPos_apply (u : L) (F : Total L) :
    starGammaPos u F = alphabetShift (fun r => starLetter u ^ r) F := rfl

theorem starGammaNeg_apply (u : L) (F : Total L) :
    starGammaNeg u F = alphabetShift (fun r => -(starLetter u ^ r)) F := rfl

theorem starGammaQ_apply (q u : L) (F : Total L) :
    starGammaQ q u F = alphabetShift (fun r => (scal q * starLetter u) ^ r) F := rfl

@[simp]
theorem starGammaNeg_scal (u x : L) : starGammaNeg u (scal x : Total L) = scal x :=
  alphabetShift_scal _ x

theorem starGammaNeg_starGammaPos (u : L) (F : Total L) :
    starGammaNeg u (starGammaPos u F) = F :=
  alphabetShift_neg_alphabetShift (fun r => pow_mem (starLetter_mem_auxSubalg u) r) F

/-- **`d^*_+` on a constant is the shift by the virtual alphabet `quy_1 - uy_1`.** Both sides are
`𝕜`-algebra maps out of `Λ`, and on `p_{r+1}` both give
`p_{r+1} + (q^{r+1}-1)(uy_1)^{r+1}` — the value `HJO.Sweep.dplusStarAlg_C_powerSum` computes. The
level is not read: on the constants `d^*_+` is the same substitution at every `k`. -/
theorem dplusStar_C_eq_starGamma [Algebra ℚ L] (q u : L) (k : ℕ) (f : Sym.Lambda L) :
    dplusStar q u k (MvPolynomial.C f) = starGammaNeg u (starGammaQ q u (MvPolynomial.C f)) := by
  have hsum : ∀ r : ℕ, (fun r => (scal q * starLetter u) ^ r) r
      + (fun r => -(starLetter u ^ r)) r = scal (q ^ r - 1) * starLetter u ^ r := by
    intro r
    simp only [mul_pow, scal_sub, scal_one, scal_pow]
    ring
  have hcomp : starGammaNeg u (starGammaQ q u (MvPolynomial.C f))
      = alphabetShift (fun r => scal (q ^ r - 1) * starLetter u ^ r) (MvPolynomial.C f) := by
    rw [starGammaNeg, starGammaQ,
      alphabetShift_alphabetShift_of_mem_auxSubalg
        (P := fun r => (scal q * starLetter u) ^ r) (Q := fun r => -(starLetter u ^ r))
        (fun r => pow_mem (mul_mem (scal_mem_auxSubalg q) (starLetter_mem_auxSubalg u)) r)
        (MvPolynomial.C f)]
    exact congrArg (fun P : ℕ → Total L => alphabetShift P (MvPolynomial.C f)) (funext hsum)
  have key : (dplusStarAlg q u k).comp (IsScalarTower.toAlgHom L (Sym.Lambda L) (Total L))
      = (alphabetShift fun r => scal (q ^ r - 1) * starLetter u ^ r).comp
        (IsScalarTower.toAlgHom L (Sym.Lambda L) (Total L)) := by
    refine MvPolynomial.algHom_ext fun r => ?_
    have hC : (IsScalarTower.toAlgHom L (Sym.Lambda L) (Total L)) (MvPolynomial.X r)
        = MvPolynomial.C (Sym.powerSum L (r + 1)) := by
      rw [IsScalarTower.coe_toAlgHom', MvPolynomial.algebraMap_eq,
        show (MvPolynomial.X r : Sym.Lambda L) = Sym.powerSum L (r + 1) from by
          rw [Sym.powerSum, Nat.add_sub_cancel]]
    rw [AlgHom.comp_apply, AlgHom.comp_apply, hC, dplusStarAlg_C_powerSum, alphabetShift_powerSum,
      starLetter]
  rw [hcomp, ← dplusStarAlg_eq_dplusStar]
  exact congrArg (fun g : Sym.Lambda L →ₐ[L] Total L => g f) key

end Letter

/-! ### Two linearity facts about the Hall--Littlewood operators -/

section BopLinear

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **`B_r` is linear over everything free of the alphabet.** `HJO.Sym.isLinearMap_bop`'s
`𝕜[y]`-linearity (`HJO.Sweep.bopExt_monomial_mul`) upgraded from a monomial to the whole subalgebra
the `y`-variables generate, which is what the evaluation needs in order to move the letter `uy_1`
past the operators. -/
theorem bopExt_auxSubalg_mul (q : L) (r : ℤ) {Z : Total L} (hZ : Z ∈ auxSubalg L) (F : Total L) :
    bopExt q r (Z * F) = Z * bopExt q r F := by
  have key : ∀ F : Total L, bopExt q r (Z * F) = Z * bopExt q r F := by
    refine Algebra.adjoin_induction
      (p := fun Z _ => ∀ F : Total L, bopExt q r (Z * F) = Z * bopExt q r F) ?_ ?_ ?_ ?_ hZ
    · rintro _ ⟨j, rfl⟩ F
      rw [show (MvPolynomial.X j : Total L) = MvPolynomial.monomial (Finsupp.single j 1) 1 from by
        rw [← MvPolynomial.X_pow_eq_monomial, pow_one], bopExt_monomial_mul]
    · intro x F
      rw [← Algebra.smul_def, map_smul, Algebra.smul_def]
    · intro x y _ _ hx hy F
      rw [add_mul, map_add, hx, hy, add_mul]
    · intro x y _ _ hx hy F
      rw [mul_assoc, hx (y * F), hy F, mul_assoc]
  exact key F

/-- **The shift of a two-letter `B`-word on the unit**, fully expanded: applying
`HJO.Sweep.alphabetShift_bopExt` twice to `B_iB_j(1)` turns each factor into `B_· - wB_{·-1}`, the
shift fixing `1`. This is the step of using `HJO.Sweep.alphabetShift_bopExt` three times to move
each shift to the right. -/
theorem alphabetShift_bopExt_one (q : L) {w : Total L} (hw : w ∈ auxSubalg L) (j : ℤ) :
    alphabetShift (fun r => w ^ r) (bopExt q j (1 : Total L))
      = bopExt q j 1 - w * bopExt q (j - 1) 1 := by
  rw [alphabetShift_bopExt q j hw, map_one]

theorem alphabetShift_bopExt_bopExt_one (q : L) {w : Total L} (hw : w ∈ auxSubalg L) (i j : ℤ) :
    alphabetShift (fun r => w ^ r) (bopExt q i (bopExt q j (1 : Total L)))
      = bopExt q i (bopExt q j 1) - w * bopExt q i (bopExt q (j - 1) 1)
        - w * bopExt q (i - 1) (bopExt q j 1)
        + w * (w * bopExt q (i - 1) (bopExt q (j - 1) 1)) := by
  rw [alphabetShift_bopExt q i hw, alphabetShift_bopExt_one q hw, map_sub, map_sub,
    bopExt_auxSubalg_mul q i hw, bopExt_auxSubalg_mul q (i - 1) hw]
  ring

end BopLinear

/-! ### The operator `A` -/

section Operator

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **`A = d^*_+d_-^2 - (q+1)d_-d^*_+d_- + qd_-^2d^*_+`**, the operator the proof of
`HJO.Sweep.dminusCM_starCommCM_braidInv` reduces the statement to. On `V_{k+2}` it lands in
`V_{k+1}`; the range `k ≥ 2` is read as `k + 2`, so that `k-1` is `k+1` and `k-2` is `k` and nothing
is truncated. -/
noncomputable def starConj1 (q u : L) (k : ℕ) : Module.End L (Total L) :=
  dplusStar q u k * dminusCM q (k + 1) * dminusCM q (k + 2)
    - (1 + q) • (dminusCM q (k + 2) * dplusStar q u (k + 1) * dminusCM q (k + 2))
    + q • (dminusCM q (k + 2) * dminusCM q (k + 3) * dplusStar q u (k + 2))

theorem starConj1_apply (q u : L) (k : ℕ) (F : Total L) :
    starConj1 q u k F
      = dplusStar q u k (dminusCM q (k + 1) (dminusCM q (k + 2) F))
        - (1 + q) • dminusCM q (k + 2) (dplusStar q u (k + 1) (dminusCM q (k + 2) F))
        + q • dminusCM q (k + 2) (dminusCM q (k + 3) (dplusStar q u (k + 2) F)) := rfl

omit [Algebra ℚ L] in
/-- The `𝕜`-linear combination of `B`-words that the three composites of `A` reduce to, with the
`B`-words left free: the identity `ring` verifies once the three shifts have been moved to the
right. The two factors of each product differ only in whether the letter is `quy_1` or `uy_1`, and
the words with two letters and the word with none both cancel. -/
private theorem starConj1_cancel (q : L) (w P P' P'' P''' : Total L) :
    (P - scal q * w * P' - scal q * w * P''
        + scal q * w * (scal q * w * P'''))
      - (1 + scal q) * (P - scal q * w * P' - w * (P'' - scal q * w * P'''))
      + scal q * (P - w * P' - w * P'' + w * (w * P'''))
      = w * ((1 - scal q) * (P'' - scal q * P')) := by
  ring

/-- **The evaluation, the display.** For every `a, b`,

`A(y_{k+1}^ay_{k+2}^b) = Γ_+(-uy_1)(uy_1(1-q)(B_aB_{b+1} - qB_{a+1}B_b))(1)`.

The two double lowerings are `HJO.Sweep.dminusCM_dminusCM_auxVar_pow_mul` at `H = 1`
(`HJO.Sweep.dminusCM_dminusCM_auxVar_pow_mul`), the middle term is
`HJO.Sweep.dminusCM_auxVar_pow_mul` twice with the corner shift of `HJO.Sweep.dplusStar_braidInv` in
between, and the three shifts are moved to the right by `HJO.Sweep.alphabetShift_bopExt` for the two
added letters and `HJO.Sweep.bopExt_alphabetShift_neg` for the subtracted one. What is left is
`HJO.Sweep.starConj1_cancel`. -/
theorem starConj1_auxVar_pow (q u : L) (k a b : ℕ) :
    starConj1 q u k ((auxVar (k + 1) : Total L) ^ a * (auxVar (k + 2) : Total L) ^ b)
      = starGammaNeg u (starLetter u * (scal (1 - q) *
          (bopExt q (a : ℤ) (bopExt q ((b : ℤ) + 1) 1)
            - scal q * bopExt q ((a : ℤ) + 1) (bopExt q (b : ℤ) 1)))) := by
  have hai : ((a : ℤ) + 1 - 1) = (a : ℤ) := by ring
  have hbi : ((b : ℤ) + 1 - 1) = (b : ℤ) := by ring
  have hwmem : starLetter u ∈ auxSubalg L := starLetter_mem_auxSubalg u
  have hvmem : scal q * starLetter u ∈ auxSubalg L :=
    mul_mem (scal_mem_auxSubalg q) hwmem
  have hA : ∀ j : ℕ, (auxVar (j + 1) : Total L) = MvPolynomial.X j := fun j => by
    rw [auxVar, Nat.add_sub_cancel]
  -- the two double lowerings, at `H = 1`
  have hdd : dminusCM q (k + 1) (dminusCM q (k + 2)
        ((auxVar (k + 1) : Total L) ^ a * (auxVar (k + 2) : Total L) ^ b))
      = bopExt q ((a : ℤ) + 1) (bopExt q ((b : ℤ) + 1) 1) := by
    have h := dminusCM_dminusCM_auxVar_pow_mul q k a b (H := (1 : Total L)) (one_mem _)
    rwa [mul_one] at h
  have hstar3 : dplusStar q u (k + 2)
        ((auxVar (k + 1) : Total L) ^ a * (auxVar (k + 2) : Total L) ^ b)
      = (auxVar (k + 2) : Total L) ^ a * (auxVar (k + 3) : Total L) ^ b := by
    have hx1 : dplusStarAlg q u (k + 2) (auxVar (k + 1) : Total L) = auxVar (k + 2) := by
      rw [hA k, dplusStarAlg_X_of_lt q u (show k < k + 2 by omega), ← hA (k + 1)]
    have hx2 : dplusStarAlg q u (k + 2) (auxVar (k + 2) : Total L) = auxVar (k + 3) := by
      rw [hA (k + 1), dplusStarAlg_X_of_lt q u (show k + 1 < k + 2 by omega), ← hA (k + 2)]
    rw [← dplusStarAlg_eq_dplusStar, map_mul, map_pow, map_pow, hx1, hx2]
  have hdd3 : dminusCM q (k + 2) (dminusCM q (k + 3)
        ((auxVar (k + 2) : Total L) ^ a * (auxVar (k + 3) : Total L) ^ b))
      = bopExt q ((a : ℤ) + 1) (bopExt q ((b : ℤ) + 1) 1) := by
    have h := dminusCM_dminusCM_auxVar_pow_mul q (k + 1) a b (H := (1 : Total L)) (one_mem _)
    rwa [mul_one] at h
  -- the middle term
  have hpull : ∀ r : ℤ, bopExt q r ((auxVar (k + 1) : Total L) ^ a)
      = (auxVar (k + 1) : Total L) ^ a * bopExt q r 1 := fun r => by
    have h := bopExt_auxSubalg_mul q r (pow_mem (auxVar_mem_auxSubalg (k + 1)) a) (1 : Total L)
    rwa [mul_one] at h
  have hd2 : dminusCM q (k + 2)
        ((auxVar (k + 1) : Total L) ^ a * (auxVar (k + 2) : Total L) ^ b)
      = -((auxVar (k + 1) : Total L) ^ a * bopExt q ((b : ℤ) + 1) 1) := by
    have hre : ((auxVar (k + 1) : Total L) ^ a * (auxVar (k + 2) : Total L) ^ b)
        = (auxVar (k + 2) : Total L) ^ b * (auxVar (k + 1) : Total L) ^ a := by ring
    have h : dminusCM q (k + 2) ((auxVar (k + 2) : Total L) ^ b
          * (auxVar (k + 1) : Total L) ^ a)
        = -bopExt q ((b : ℤ) + 1) ((auxVar (k + 1) : Total L) ^ a) :=
      dminusCM_auxVar_pow_mul q (k + 1) b (pow_mem (auxVar_mem_piece (by omega) (le_refl _)) a)
    rw [hre, h, hpull]
  have hs2 : dplusStar q u (k + 1) ((auxVar (k + 1) : Total L) ^ a
        * bopExt q ((b : ℤ) + 1) 1)
      = (auxVar (k + 2) : Total L) ^ a * dplusStar q u (k + 1) (bopExt q ((b : ℤ) + 1) 1) := by
    have hstep : ∀ G : Total L, dplusStar q u (k + 1) ((auxVar (k + 1) : Total L) * G)
        = (auxVar (k + 2) : Total L) * dplusStar q u (k + 1) G := fun G =>
      dplusStar_auxVar_mul q u (by omega) (le_refl (k + 1)) G
    exact map_auxVar_pow_mul_of_map_auxVar_mul hstep a _
  have hmemV : dplusStar q u (k + 1) (bopExt q ((b : ℤ) + 1) (1 : Total L)) ∈ piece L (k + 1) := by
    rw [bopExt_one, dplusStar_C_eq_starGamma, starGammaNeg_apply, starGammaQ_apply]
    refine alphabetShift_mem_piece
      (fun r => neg_mem (pow_mem (starLetter_mem_piece u (k + 1) (by omega)) r)) ?_
    exact alphabetShift_mem_piece
      (fun r => pow_mem (mul_mem (scal_mem_piece q _)
        (starLetter_mem_piece u (k + 1) (by omega))) r) (Subalgebra.algebraMap_mem _ _)
  have hd2' : dminusCM q (k + 2) ((auxVar (k + 2) : Total L) ^ a
        * dplusStar q u (k + 1) (bopExt q ((b : ℤ) + 1) 1))
      = -bopExt q ((a : ℤ) + 1) (dplusStar q u (k + 1) (bopExt q ((b : ℤ) + 1) 1)) :=
    dminusCM_auxVar_pow_mul q (k + 1) a hmemV
  -- the three shifts moved to the right
  have ht1 : dplusStar q u k (bopExt q ((a : ℤ) + 1) (bopExt q ((b : ℤ) + 1) (1 : Total L)))
      = starGammaNeg u (starGammaQ q u (bopExt q ((a : ℤ) + 1) (bopExt q ((b : ℤ) + 1) 1))) := by
    rw [show bopExt q ((a : ℤ) + 1) (bopExt q ((b : ℤ) + 1) (1 : Total L))
        = MvPolynomial.C (Sym.Bop q ((a : ℤ) + 1) (Sym.elemSymmAlt L ((b : ℤ) + 1))) from by
      rw [bopExt_one, bopExt_C], dplusStar_C_eq_starGamma]
  have ht2 : dplusStar q u (k + 1) (bopExt q ((b : ℤ) + 1) (1 : Total L))
      = starGammaNeg u (starGammaQ q u (bopExt q ((b : ℤ) + 1) 1)) := by
    rw [bopExt_one, dplusStar_C_eq_starGamma]
  have hX1 : starGammaQ q u (bopExt q ((a : ℤ) + 1) (bopExt q ((b : ℤ) + 1) (1 : Total L)))
      = bopExt q ((a : ℤ) + 1) (bopExt q ((b : ℤ) + 1) 1)
        - scal q * starLetter u * bopExt q ((a : ℤ) + 1) (bopExt q (b : ℤ) 1)
        - scal q * starLetter u * bopExt q (a : ℤ) (bopExt q ((b : ℤ) + 1) 1)
        + scal q * starLetter u
          * (scal q * starLetter u * bopExt q (a : ℤ) (bopExt q (b : ℤ) 1)) := by
    have h := alphabetShift_bopExt_bopExt_one q hvmem ((a : ℤ) + 1) ((b : ℤ) + 1)
    rw [hai, hbi] at h
    rw [starGammaQ_apply]
    exact h
  have hX3 : starGammaPos u (bopExt q ((a : ℤ) + 1) (bopExt q ((b : ℤ) + 1) (1 : Total L)))
      = bopExt q ((a : ℤ) + 1) (bopExt q ((b : ℤ) + 1) 1)
        - starLetter u * bopExt q ((a : ℤ) + 1) (bopExt q (b : ℤ) 1)
        - starLetter u * bopExt q (a : ℤ) (bopExt q ((b : ℤ) + 1) 1)
        + starLetter u * (starLetter u * bopExt q (a : ℤ) (bopExt q (b : ℤ) 1)) := by
    have h := alphabetShift_bopExt_bopExt_one q hwmem ((a : ℤ) + 1) ((b : ℤ) + 1)
    rw [hai, hbi] at h
    rw [starGammaPos_apply]
    exact h
  have hXW : starGammaQ q u (bopExt q ((b : ℤ) + 1) (1 : Total L))
      = bopExt q ((b : ℤ) + 1) 1 - scal q * starLetter u * bopExt q (b : ℤ) 1 := by
    have h := alphabetShift_bopExt_one q hvmem ((b : ℤ) + 1)
    rw [hbi] at h
    rw [starGammaQ_apply]
    exact h
  have hmove : ∀ Y : Total L, bopExt q ((a : ℤ) + 1) (starGammaNeg u Y)
      = starGammaNeg u (bopExt q ((a : ℤ) + 1) Y - starLetter u * bopExt q (a : ℤ) Y) := by
    intro Y
    have h := bopExt_alphabetShift_neg q ((a : ℤ) + 1) hwmem Y
    rw [hai] at h
    rw [starGammaNeg_apply, starGammaNeg_apply]
    exact h
  have hexp : ∀ i : ℤ, bopExt q i (bopExt q ((b : ℤ) + 1) (1 : Total L)
        - scal q * starLetter u * bopExt q (b : ℤ) 1)
      = bopExt q i (bopExt q ((b : ℤ) + 1) 1)
        - scal q * starLetter u * bopExt q i (bopExt q (b : ℤ) 1) := fun i => by
    rw [map_sub, bopExt_auxSubalg_mul q i hvmem]
  -- the three terms
  have hterm1 : dplusStar q u k (dminusCM q (k + 1) (dminusCM q (k + 2)
        ((auxVar (k + 1) : Total L) ^ a * (auxVar (k + 2) : Total L) ^ b)))
      = starGammaNeg u (bopExt q ((a : ℤ) + 1) (bopExt q ((b : ℤ) + 1) 1)
          - scal q * starLetter u * bopExt q ((a : ℤ) + 1) (bopExt q (b : ℤ) 1)
          - scal q * starLetter u * bopExt q (a : ℤ) (bopExt q ((b : ℤ) + 1) 1)
          + scal q * starLetter u
            * (scal q * starLetter u * bopExt q (a : ℤ) (bopExt q (b : ℤ) 1))) := by
    rw [hdd, ht1, hX1]
  have hterm2 : dminusCM q (k + 2) (dplusStar q u (k + 1) (dminusCM q (k + 2)
        ((auxVar (k + 1) : Total L) ^ a * (auxVar (k + 2) : Total L) ^ b)))
      = starGammaNeg u ((bopExt q ((a : ℤ) + 1) (bopExt q ((b : ℤ) + 1) 1)
            - scal q * starLetter u * bopExt q ((a : ℤ) + 1) (bopExt q (b : ℤ) 1))
          - starLetter u * (bopExt q (a : ℤ) (bopExt q ((b : ℤ) + 1) 1)
            - scal q * starLetter u * bopExt q (a : ℤ) (bopExt q (b : ℤ) 1))) := by
    rw [hd2, map_neg, hs2, map_neg, hd2', neg_neg, ht2, hmove, hXW, hexp, hexp]
  have hterm3 : dminusCM q (k + 2) (dminusCM q (k + 3) (dplusStar q u (k + 2)
        ((auxVar (k + 1) : Total L) ^ a * (auxVar (k + 2) : Total L) ^ b)))
      = starGammaNeg u (bopExt q ((a : ℤ) + 1) (bopExt q ((b : ℤ) + 1) 1)
          - starLetter u * bopExt q ((a : ℤ) + 1) (bopExt q (b : ℤ) 1)
          - starLetter u * bopExt q (a : ℤ) (bopExt q ((b : ℤ) + 1) 1)
          + starLetter u * (starLetter u * bopExt q (a : ℤ) (bopExt q (b : ℤ) 1))) := by
    rw [hstar3, hdd3, ← hX3]
    exact (starGammaNeg_starGammaPos u _).symm
  rw [starConj1_apply, hterm1, hterm2, hterm3, ← scal_mul_eq_smul, ← scal_mul_eq_smul]
  have hkey := starConj1_cancel q (starGammaNeg u (starLetter u))
    (starGammaNeg u (bopExt q ((a : ℤ) + 1) (bopExt q ((b : ℤ) + 1) 1)))
    (starGammaNeg u (bopExt q ((a : ℤ) + 1) (bopExt q (b : ℤ) 1)))
    (starGammaNeg u (bopExt q (a : ℤ) (bopExt q ((b : ℤ) + 1) 1)))
    (starGammaNeg u (bopExt q (a : ℤ) (bopExt q (b : ℤ) 1)))
  simp only [map_sub, map_add, map_mul, map_one, starGammaNeg_scal, scal_add, scal_sub, scal_one]
  linear_combination hkey

/-- **The evaluation is antisymmetric in `(a, b)`.** This is `HJO.Sym.bop_pair_antisymm`, read
through `HJO.Sweep.bopExt_pair_antisymm` at `(a-1, b-1)`: the displayed bracket
`B_aB_{b+1} - qB_{a+1}B_b` is the Haglund--Morse--Zabrocki combination, and the relation says
exactly that interchanging `a` and `b` negates it. -/
theorem starConj1_auxVar_pow_add_swap (q u : L) (k a b : ℕ) :
    starConj1 q u k ((auxVar (k + 1) : Total L) ^ a * (auxVar (k + 2) : Total L) ^ b)
        + starConj1 q u k ((auxVar (k + 1) : Total L) ^ b * (auxVar (k + 2) : Total L) ^ a)
      = 0 := by
  have hanti := bopExt_pair_antisymm q ((a : ℤ) - 1) ((b : ℤ) - 1) (1 : Total L)
  rw [show (a : ℤ) - 1 + 2 = (a : ℤ) + 1 from by ring,
    show (b : ℤ) - 1 + 1 = (b : ℤ) from by ring,
    show (a : ℤ) - 1 + 1 = (a : ℤ) from by ring,
    show (b : ℤ) - 1 + 2 = (b : ℤ) + 1 from by ring] at hanti
  simp only [← scal_mul_eq_smul] at hanti
  have hzero : starLetter u * (scal (1 - q) *
          (bopExt q (a : ℤ) (bopExt q ((b : ℤ) + 1) 1)
            - scal q * bopExt q ((a : ℤ) + 1) (bopExt q (b : ℤ) 1)))
        + starLetter u * (scal (1 - q) *
          (bopExt q (b : ℤ) (bopExt q ((a : ℤ) + 1) 1)
            - scal q * bopExt q ((b : ℤ) + 1) (bopExt q (a : ℤ) 1))) = 0 := by
    linear_combination (-(starLetter u * scal (1 - q)) : Total L) * hanti
  rw [starConj1_auxVar_pow, starConj1_auxVar_pow, ← map_add, hzero, map_zero]

end Operator

/-! ### The hypotheses of the reduction -/

section Reduction

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **The intertwining of the twisted multiplications.** `A` carries `∗_{0,k+2}` to `∗_{1,k+1}`: it
carries one starred raising, which moves the index of the twist up by one
(`HJO.Sweep.dplusStar_twistedActionMult`), and three lowerings, which leave it alone
(`HJO.Sweep.dminusCM_twistedActionMult`). -/
theorem starConj1_twist_mul (q u : L) (k : ℕ) (c : Sym.Lambda L) (G : Total L) :
    starConj1 q u k (twist L q (k + 2) c * G)
      = twistedMult q u 1 (k + 1) (MvPolynomial.C c) * starConj1 q u k G := by
  have hc : (twist L q (k + 2) c : Total L) * G
      = twistedActionMult L q u 0 (k + 2) (MvPolynomial.C c) G := by
    rw [twistedActionMult_apply, twistedMult_C]
  have hm2 : ∀ H : Total L,
      dminusCM q (k + 2) (twistedActionMult L q u 0 (k + 2) (MvPolynomial.C c) H)
        = twistedActionMult L q u 0 (k + 1) (MvPolynomial.C c) (dminusCM q (k + 2) H) :=
    fun H => dminusCM_twistedActionMult_C q u (show 0 ≤ k + 1 by omega) c H
  have hm1 : ∀ H : Total L,
      dminusCM q (k + 1) (twistedActionMult L q u 0 (k + 1) (MvPolynomial.C c) H)
        = twistedActionMult L q u 0 k (MvPolynomial.C c) (dminusCM q (k + 1) H) :=
    fun H => dminusCM_twistedActionMult_C q u (Nat.zero_le k) c H
  have hp0 : ∀ H : Total L,
      dplusStar q u k (twistedActionMult L q u 0 k (MvPolynomial.C c) H)
        = twistedActionMult L q u 1 (k + 1) (MvPolynomial.C c) (dplusStar q u k H) :=
    fun H => dplusStar_twistedActionMult q u (Nat.zero_le k) c H
  have hp1 : ∀ H : Total L,
      dplusStar q u (k + 1) (twistedActionMult L q u 0 (k + 1) (MvPolynomial.C c) H)
        = twistedActionMult L q u 1 (k + 2) (MvPolynomial.C c) (dplusStar q u (k + 1) H) :=
    fun H => dplusStar_twistedActionMult q u (show 0 ≤ k + 1 by omega) c H
  have hp2 : ∀ H : Total L,
      dplusStar q u (k + 2) (twistedActionMult L q u 0 (k + 2) (MvPolynomial.C c) H)
        = twistedActionMult L q u 1 (k + 3) (MvPolynomial.C c) (dplusStar q u (k + 2) H) :=
    fun H => dplusStar_twistedActionMult q u (show 0 ≤ k + 2 by omega) c H
  have hn2 : ∀ H : Total L,
      dminusCM q (k + 2) (twistedActionMult L q u 1 (k + 2) (MvPolynomial.C c) H)
        = twistedActionMult L q u 1 (k + 1) (MvPolynomial.C c) (dminusCM q (k + 2) H) :=
    fun H => dminusCM_twistedActionMult_C q u (show 1 ≤ k + 1 by omega) c H
  have hn3 : ∀ H : Total L,
      dminusCM q (k + 3) (twistedActionMult L q u 1 (k + 3) (MvPolynomial.C c) H)
        = twistedActionMult L q u 1 (k + 2) (MvPolynomial.C c) (dminusCM q (k + 3) H) :=
    fun H => dminusCM_twistedActionMult_C q u (show 1 ≤ k + 2 by omega) c H
  rw [starConj1_apply, starConj1_apply, hc, hm2, hm1, hp0, hp1, hn2, hp2, hn3, hn2]
  simp only [twistedActionMult_apply, ← scal_mul_eq_smul]
  ring

/-- **The corner shifts.** `A` carries `y_i` to `y_{i+1}` for `1 ≤ i ≤ k`, one starred raising
shifting the index once and the lowerings not at all. The range is exact: at `i = k+1` the second
lowering of the first term would have to pass `y_{k+1}` on `V_{k+1}`, which
`HJO.Sweep.dminusCM_auxVar_mul` does not allow. -/
theorem starConj1_auxVar_mul (q u : L) {i k : ℕ} (hi : 1 ≤ i) (hik : i ≤ k) (G : Total L) :
    starConj1 q u k ((auxVar i : Total L) * G) = auxVar (i + 1) * starConj1 q u k G := by
  have hd1 : ∀ j : ℕ, 1 ≤ j → j ≤ k + 1 → ∀ H : Total L,
      dminusCM q (k + 2) ((auxVar j : Total L) * H) = auxVar j * dminusCM q (k + 2) H :=
    fun j hj hjk H => dminusCM_auxVar_mul q hj hjk H
  have hd0 : ∀ j : ℕ, 1 ≤ j → j ≤ k → ∀ H : Total L,
      dminusCM q (k + 1) ((auxVar j : Total L) * H) = auxVar j * dminusCM q (k + 1) H :=
    fun j hj hjk H => dminusCM_auxVar_mul q hj hjk H
  have hd3 : ∀ j : ℕ, 1 ≤ j → j ≤ k + 2 → ∀ H : Total L,
      dminusCM q (k + 3) ((auxVar j : Total L) * H) = auxVar j * dminusCM q (k + 3) H :=
    fun j hj hjk H => dminusCM_auxVar_mul q hj hjk H
  rw [starConj1_apply, starConj1_apply, hd1 i hi (by omega), hd0 i hi hik,
    dplusStar_auxVar_mul q u hi hik, dplusStar_auxVar_mul q u hi (show i ≤ k + 1 by omega),
    hd1 (i + 1) (by omega) (by omega), dplusStar_auxVar_mul q u hi (show i ≤ k + 2 by omega),
    hd3 (i + 1) (by omega) (by omega), hd1 (i + 1) (by omega) (by omega)]
  simp only [← scal_mul_eq_smul]
  ring

omit [Algebra ℚ L] in
/-- **`(T_i + q)F` is symmetric in `y_i` and `y_{i+1}`**, which is `HJO.Sweep.braid_sub_self` read
as a statement about the image: expanding `T_i = s_i + (q-1)y_i∂_i` and using that `∂_iF` is
`s_i`-fixed (`HJO.Sweep.swapAux_dividedDiff`), the defect is `(1 - q)` times
`(y_{i+1}-y_i)∂_iF - (F - s_iF)`, which `dividedDiff_spec` kills. -/
theorem swapAux_braid_add_q (q : L) (i : ℕ) (F : Total L) :
    swapAux L i (braid q i F + scal q * F) = braid q i F + scal q * F := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [map_add, swapAux_zero, map_mul, swapAux_zero, swapAux_zero]
  have hD := dividedDiff_spec i F
  have hsy : swapAux L i (MvPolynomial.X (i - 1) : Total L) = MvPolynomial.X i := by
    rw [swapAux_X, Equiv.swap_apply_left]
  have hy : (auxVar i : Total L) = MvPolynomial.X (i - 1) := rfl
  rw [braid_apply, hy]
  simp only [map_add, map_mul, map_sub, map_one, swapAux_scal, swapAux_swapAux,
    swapAux_dividedDiff, hsy, scal_sub, scal_one]
  linear_combination (scal q - 1 : Total L) * hD

/-- `s_i` as a `𝕜`-linear endomorphism of the total space; the reduction lemma takes `𝕜`-linear
maps, and `HJO.Sweep.swapAux` is an algebra equivalence over `Λ`. -/
noncomputable def swapAuxEnd (L : Type*) [Field L] (i : ℕ) : Module.End L (Total L) :=
  ((swapAux L i).toAlgHom.restrictScalars L).toLinearMap

omit [Algebra ℚ L] in
theorem swapAuxEnd_apply (i : ℕ) (F : Total L) : swapAuxEnd L i F = swapAux L i F := rfl

/-- **`A` vanishes on the elements of `V_{k+2}` symmetric in `y_{k+1}` and `y_{k+2}`.**

`A(1 + s_{k+1})` and `0` both intertwine the twisted multiplications with the multiplier
`σ_{1,k+1}(c)` and shift the corners `y_1, …, y_k` by `y_i ↦ y_{i+1}` — `s_{k+1}` fixes
`tw_{k+2}(c)` (`HJO.Sweep.swapAux_twist`) and each `y_i` with `i ≤ k` — so by
`HJO.Sweep.eq_of_agree_auxVar_pow_two` it is enough that they agree on the monomials
`y_{k+1}^ay_{k+2}^b`, and there `1 + s_{k+1}` symmetrises and
`HJO.Sweep.starConj1_auxVar_pow_add_swap` applies. Halving is free, `L` being a `ℚ`-algebra. -/
theorem starConj1_of_swapAux_eq (q u : L) {k : ℕ} {F : Total L} (hF : F ∈ piece L (k + 2))
    (hsym : swapAux L (k + 1) F = F) : starConj1 q u k F = 0 := by
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  have hkey : (starConj1 q u k * (swapAuxEnd L (k + 1) + 1)) F
      = (0 : Module.End L (Total L)) F := by
    refine eq_of_agree_auxVar_pow_two q u
      (T := fun c => twistedMult q u 1 (k + 1) (MvPolynomial.C c))
      (S := fun i => auxVar (i + 1)) (fun c G => ?_) (fun c G => by simp)
      (fun i hi hik G => ?_) (fun i hi hik G => by simp) (fun a b => ?_) hF
    · have hsw : swapAux L (k + 1) (twist L q (k + 2) c) = twist L q (k + 2) c :=
        swapAux_twist q (by omega) (by omega) c
      simp only [Module.End.mul_apply, LinearMap.add_apply, Module.End.one_apply, swapAuxEnd_apply]
      rw [map_mul, hsw, ← mul_add, starConj1_twist_mul]
    · have hsw : swapAux L (k + 1) (auxVar i : Total L) = auxVar i :=
        swapAux_auxVar_of_ne hi (by omega) (by omega)
      simp only [Module.End.mul_apply, LinearMap.add_apply, Module.End.one_apply, swapAuxEnd_apply]
      rw [map_mul, hsw, ← mul_add, starConj1_auxVar_mul q u hi hik]
    · have hs1 : swapAux L (k + 1) (auxVar (k + 1) : Total L) = auxVar (k + 2) :=
        swapAux_auxVar_self (by omega)
      have hs2 : swapAux L (k + 1) (auxVar (k + 2) : Total L) = auxVar (k + 1) :=
        swapAux_auxVar_succ (by omega)
      have hswap : swapAux L (k + 1)
            ((auxVar (k + 1) : Total L) ^ a * (auxVar (k + 2) : Total L) ^ b)
          = (auxVar (k + 1) : Total L) ^ b * (auxVar (k + 2) : Total L) ^ a := by
        rw [map_mul, map_pow, map_pow, hs1, hs2]
        ring
      simp only [Module.End.mul_apply, LinearMap.add_apply, Module.End.one_apply, swapAuxEnd_apply,
        LinearMap.zero_apply]
      rw [hswap, map_add, add_comm]
      exact starConj1_auxVar_pow_add_swap q u k a b
  simp only [Module.End.mul_apply, LinearMap.add_apply, Module.End.one_apply, swapAuxEnd_apply,
    LinearMap.zero_apply, hsym] at hkey
  rw [map_add] at hkey
  have h2 : (2 : L) • starConj1 q u k F = 0 := by
    rw [two_smul L]
    exact hkey
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

/-- **`A(T_{k+1}+q) = 0`**, the reduced form of `HJO.Sweep.dminusCM_starCommCM_braidInv`: the
image of `T_{k+1}+q` consists of the elements symmetric in `y_{k+1}` and `y_{k+2}`
(`HJO.Sweep.swapAux_braid_add_q`), and `A` vanishes on those. No hypothesis on `q`. -/
theorem starConj1_braid_add_q (q u : L) {k : ℕ} {F : Total L} (hF : F ∈ piece L (k + 2)) :
    starConj1 q u k (braid q (k + 1) F + scal q * F) = 0 :=
  starConj1_of_swapAux_eq q u
    (add_mem (braid_mem_piece q (by omega) (by omega) hF)
      (mul_mem (scal_mem_piece q (k + 2)) hF))
    (swapAux_braid_add_q q (k + 1) F)

end Reduction

/-! ### The relation -/

section Node

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **The first starred commutator relation.** For `k ≥ 2`, on `V_k`,

`d_-(d^*_+d_- - d_-d^*_+)T_{k-1}^{-1} = q^{-1}(d^*_+d_- - d_-d^*_+)d_-`,

read at `k = m + 2`, so that the hypothesis `k ≥ 2` is carried by the shape of the index. The
commutator is `HJO.Sweep.starCommCM`, the operators are `HJO.Sweep.dminusCM`,
`HJO.Sweep.dplusStar` and `HJO.Sweep.braidInv` (`HJO.Sweep.braid`), each at
the graded piece its argument lives at.

`F ∈ V_{m+2}` is load-bearing — the reduction to the monomials `y_{m+1}^ay_{m+2}^b` is a statement
about `V_{m+2}`. So are the two hypotheses on `q`: `q ≠ 0` is what makes `T_{m+1}^{-1}` an inverse
and `q^{-1}` the scalar named, and `q + 1 ≠ 0` is what turns the reduced form
`A(T_{m+1}+q) = 0` back into the relation — see the module docstring, where both are accounted for.

Three steps. `HJO.Sweep.starConj1_braid_add_q` is `A(T_{m+1}+q) = 0`; `d_-^2T_{m+1} = d_-^2`
(`HJO.Sweep.dminusCM_dminusCM_braid`) kills the braid operator in the first and third terms of `A`,
the third after `d^*_+T_{m+1} = T_{m+2}d^*_+` (`HJO.Sweep.dplusStar_braidInv`) has moved it past the
raising; and what is left is `(1+q)` times the relation. -/
@[hjo "lem_cm_star_conjrel1"]
theorem dminusCM_starCommCM_braidInv (q u : L) (hq : q ≠ 0) (hq1 : q + 1 ≠ 0) {k : ℕ}
    {F : Total L} (hF : F ∈ piece L (k + 2)) :
    dminusCM q (k + 2) (starCommCM q u (k + 2) (braidInv q (k + 1) F))
      = q⁻¹ • starCommCM q u (k + 1) (dminusCM q (k + 2) F) := by
  have hC2 : ∀ X : Total L, starCommCM q u (k + 2) X
      = dplusStar q u (k + 1) (dminusCM q (k + 2) X)
        - dminusCM q (k + 3) (dplusStar q u (k + 2) X) :=
    fun X => starCommCM_succ_apply q u (k + 1) X
  have hC1 : ∀ X : Total L, starCommCM q u (k + 1) X
      = dplusStar q u k (dminusCM q (k + 1) X)
        - dminusCM q (k + 2) (dplusStar q u (k + 1) X) :=
    fun X => starCommCM_succ_apply q u k X
  set G := braidInv q (k + 1) F with hGdef
  have hGmem : G ∈ piece L (k + 2) := braidInv_mem_piece q (by omega) hF
  have hFG : braid q (k + 1) G = F := braid_braidInv q hq (k + 1) F
  -- the first term of `A` does not see the braid operator
  have h1 : dplusStar q u k (dminusCM q (k + 1) (dminusCM q (k + 2) (braid q (k + 1) G)))
      = dplusStar q u k (dminusCM q (k + 1) (dminusCM q (k + 2) G)) := by
    rw [dminusCM_dminusCM_braid q k hGmem]
  -- nor does the third, once the raising has carried it up
  have h2 : dminusCM q (k + 2) (dminusCM q (k + 3) (dplusStar q u (k + 2) (braid q (k + 1) G)))
      = dminusCM q (k + 2) (dminusCM q (k + 3) (dplusStar q u (k + 2) G)) := by
    rw [dplusStar_braid q u (show 1 ≤ k + 1 by omega) (show k + 1 < k + 2 by omega),
      dminusCM_dminusCM_braid q (k + 1) (dplusStar_mem_piece q u hGmem)]
  have hA := starConj1_braid_add_q q u hGmem
  rw [map_add, scal_mul_eq_smul, map_smul, starConj1_apply, starConj1_apply, h1, h2] at hA
  simp only [← scal_mul_eq_smul, scal_add, scal_one] at hA
  rw [hC2, hC1, map_sub, ← hFG, h1, ← scal_mul_eq_smul]
  set tp := dplusStar q u k (dminusCM q (k + 1) (dminusCM q (k + 2) G)) with htp
  set tq0 := dminusCM q (k + 2) (dplusStar q u (k + 1) (dminusCM q (k + 2) G)) with htq0
  set tr := dminusCM q (k + 2) (dminusCM q (k + 3) (dplusStar q u (k + 2) G)) with htr
  set tq1 := dminusCM q (k + 2) (dplusStar q u (k + 1)
    (dminusCM q (k + 2) (braid q (k + 1) G))) with htq1
  have hcollect : (q + 1) • (tp - tq1 - scal q * tq0 + scal q * tr) = 0 := by
    rw [← scal_mul_eq_smul, scal_add, scal_one]
    linear_combination hA
  have hdiv := (smul_eq_zero.mp hcollect).resolve_left hq1
  have hqq : (scal q⁻¹ : Total L) * scal q = 1 := by
    rw [← scal_mul, inv_mul_cancel₀ hq, scal_one]
  have hE : tp - tq1 = scal q * (tq0 - tr) := by linear_combination hdiv
  rw [hE, ← mul_assoc, hqq, one_mul]

end Node

end HJO.Sweep
