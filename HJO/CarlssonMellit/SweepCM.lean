/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import HJO.Shuffle.SweepModule
public meta import HJO.Attr

/-! # Carlsson and Mellit's own lowering operator, the alphabet scaling, and the graded sum

Three objects of Carlsson and Mellit's construction live on the module family of
`HJO.Shuffle.SweepModule` and are not among the operators built there: Carlsson and Mellit's *own*
lowering operator `d_-`, which pairs the `y_k`-coefficients against the elementary functions one
index higher than the modified operator does; the scaling `θ_k` of the alphabet by `q - 1`; and the
graded sum `V_*`, on which the Dyck path algebra acts.

## Main definitions

* `HJO.Sweep.lowerCoeffShift`, `HJO.Sweep.dminusCM`: `d_-` of `HJO.Sweep.dminusCM`.
* `HJO.Sweep.theta`: `θ_k`.
* `HJO.Sweep.Vstar`: `V_* = ⨁_k V_k`.

## Implementation notes

**`d_-` and `d^♭_-` are different operators.** Writing `τ^-_{k,k}(F) = ∑_j F_j y_k^j`, the modified
operator `d^♭_-` of `HJO.Sweep.dminus` is `∑_j (-1)^j e_j F_j` and is `HJO.Sweep.dminus`; the
unmodified `d_-` of `HJO.Sweep.dminusCM` is `∑_j (-1)^j e_{j+1} F_j`, one index up in the
elementary function and *not* in the sign. That single shift is the whole difference, and it is why
this file mirrors `HJO.Sweep.lowerCoeff` rather than reusing it.
`HJO.Sweep.dminusCM_eq_neg_dminus_auxVar_mul` relates the two by `d_-F = -d^♭_-(y_kF)`.

`θ_k` does not depend on `k`, exactly as `HJO.Sweep.qshift` does not: the `θ_k` is the
restriction to `V_k` of the one endomorphism of the total space that scales `p_r` by `q^r - 1` and
fixes every auxiliary variable. The scalar is `q^r - 1` and not `(q-1)^r`, for the reason recorded
on `qshift`: the plethystic alphabet `(q-1)X` is the virtual alphabet `qX - X`, whose `r`-th power
sum is `q^r - 1`. The plethysm `F[X/(q-1)]` is the image under the inverse, which exists once every
`q^r - 1` is a unit; that hypothesis belongs on the lemmas that invert.

**`V_*` is the direct sum and not the union.** The graded pieces `HJO.Sweep.piece` are *nested*
(`HJO.Sweep.piece_mono`), so their union is all of `HJO.Sweep.Total`, whereas `V_* = ⨁_{k ≥ 0} V_k`
has one independent summand per `k` — which is what lets the Dyck path
algebra act on it with `e_k` the projection onto the `k`-th summand and `d_±` moving between
adjacent summands. `HJO.Sweep.Total` is the ambient space in which each `V_k` is realised, so that
every operator is an endomorphism of one space; it is not this direct sum, and a statement about
`V_*` must name `Vstar`.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, arXiv:1508.06239: Section 4,
"Raising and lowering operators", for `d_-` and the spaces `V_k` (and, in its subsection
"Characteristic functions of partial Dyck paths", the plethysms `F[(q-1)X]` and `F[X/(q-1)]`), and
the introduction for the direct sum `V_* = ⨁_{k ≥ 0} V_k` with its involution. These are the
definitions `HJO.Sweep.dminusCM`, `HJO.Sweep.theta` and `HJO.Sweep.Vstar`.
-/

@[expose] public section

namespace HJO.Sweep

/-! ### The graded sum -/

/-- **The graded sum** `V_* = ⨁_{k ≥ 0} V_k`, on which the Dyck path algebra acts:
one independent summand for each `k`, with `e_k` the projection onto the `k`-th and `d_±` the maps
between adjacent ones. The summands are the `L`-submodules `HJO.Sweep.pieceSub k` of the total
space.

This is *not* `HJO.Sweep.Total`, and not the union of the pieces: the pieces are nested, so their
union is the whole of `Total`. `Total` is the one space in which every `V_k` is realised and every
operator of `HJO.Shuffle.SweepModule` is an endomorphism; `Vstar` is the direct sum the algebra acts
on. -/
@[hjo "def_cm_vstar"]
abbrev Vstar (L : Type*) [CommRing L] : Type _ := DirectSum ℕ fun k => pieceSub L k

section CommRingBase

variable {L : Type*} [CommRing L]

/-- The inclusion of the `k`-th graded piece as the `k`-th summand of `V_*`. -/
noncomputable def ofPiece (L : Type*) [CommRing L] (k : ℕ) : pieceSub L k →ₗ[L] Vstar L :=
  DirectSum.lof L ℕ (fun k => pieceSub L k) k

/-- The projection of `V_*` onto the `k`-th summand, the `e_k` read as a map. -/
noncomputable def toPiece (L : Type*) [CommRing L] (k : ℕ) : Vstar L →ₗ[L] pieceSub L k :=
  DirectSum.component L ℕ (fun k => pieceSub L k) k

/-- The summands of `V_*` are independent: the projection onto the `k`-th summand kills the image
of every other one. This is what distinguishes the direct sum from the union of the nested pieces,
in which the same element lies in every piece from some point on. -/
@[simp]
theorem toPiece_ofPiece_of_ne {k l : ℕ} (h : l ≠ k) (F : pieceSub L l) :
    toPiece L k (ofPiece L l F) = 0 := by
  rw [toPiece, ofPiece, DirectSum.component.of]
  simp only [h, ↓reduceDIte]

/-- The projection recovers its own summand. -/
@[simp]
theorem toPiece_ofPiece (k : ℕ) (F : pieceSub L k) : toPiece L k (ofPiece L k F) = F := by
  rw [toPiece, ofPiece, DirectSum.component.of]
  simp

end CommRingBase

/-! ### The scaling of the alphabet -/

section Theta

variable {L : Type*} [CommRing L]

/-- **The scaling of the alphabet by `q - 1`.** `HJO.Sweep.theta`: the
`𝕜[y]`-algebra endomorphism `θ_k` of `V_k` with `θ_k(p_r) = (q^r - 1)p_r` for every `r ≥ 1`, the
plethysm `F[(q-1)X]`.

**The scalar is `q^r - 1` and not `(q-1)^r`**: the plethystic `(q-1)X` is the virtual alphabet
`qX - X`, in whose λ-ring `p_r(q-1) = q^r - 1`. This is the same reading of the same letter that
`HJO.Sweep.qshift` records, and under the monomial reading the statements of this part of the
library are false.

On the total space the definition does not depend on `k`, as `qshift`'s does not:
`θ_k` is the restriction of this one endomorphism to `V_k`. -/
@[hjo "def_cm_theta"]
noncomputable def theta (q : L) : Total L →ₐ[L] Total L :=
  MvPolynomial.aevalTower
    (MvPolynomial.aeval fun j : ℕ =>
      (algebraMap L (Total L) (q ^ (j + 1) - 1) * MvPolynomial.C (MvPolynomial.X j) : Total L))
    MvPolynomial.X

/-- **The defining property of `θ_k`**: it scales the power sum `p_{r+1}` by `q^{r+1} - 1`. -/
@[hjo "def_cm_theta"]
theorem theta_powerSum (q : L) (r : ℕ) :
    theta q (MvPolynomial.C (Sym.powerSum L (r + 1)))
      = algebraMap L (Total L) (q ^ (r + 1) - 1) *
        MvPolynomial.C (Sym.powerSum L (r + 1)) := by
  simp [theta, Sym.powerSum]

/-- `θ_k` fixes every auxiliary variable, so it is a `𝕜[y]`-algebra map: it moves the alphabet and
nothing else. -/
@[hjo "def_cm_theta", simp]
theorem theta_auxVar (q : L) (j : ℕ) :
    theta q (MvPolynomial.X j : Total L) = MvPolynomial.X j := by
  simp [theta]

/-- At `q = 1` the scaling is the zero map on every power sum: the virtual alphabet `qX - X` is
empty there. This separates `θ` from the substitutions of `HJO.Sweep.qshift`, which are the identity
at `q = 1`, and it is why the inverse `F[X/(q-1)]` needs `q^r - 1` invertible. -/
theorem theta_one_powerSum (r : ℕ) :
    theta (1 : L) (MvPolynomial.C (Sym.powerSum L (r + 1))) = 0 := by
  rw [theta_powerSum, one_pow, sub_self, map_zero, zero_mul]

end Theta

/-! ### Carlsson and Mellit's own lowering operator -/

section DminusCM

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- The coefficient extraction of the unmodified `d_-`: on the `Λ`-basis of `y`-monomials it sends
`y^d` to `(-1)^{d_j} e_{d_j + 1}` times `y^d` with the exponent of `y_{j+1}` deleted.

This is `HJO.Sweep.lowerCoeff` with the elementary function one index up and the sign unchanged,
which is the one difference between `HJO.Sweep.dminusCM` and `HJO.Sweep.dminus`. -/
noncomputable def lowerCoeffShift (L : Type*) [Field L] [Algebra ℚ L] (j : ℕ) :
    Total L →ₗ[Sym.Lambda L] Total L :=
  (MvPolynomial.basisMonomials ℕ (Sym.Lambda L)).constr (Sym.Lambda L) fun d =>
    (-1 : Total L) ^ d j * MvPolynomial.C (Sym.elemSymm L (d j + 1)) *
      MvPolynomial.monomial (Finsupp.erase j d) 1

/-- `lowerCoeffShift` on a `y`-monomial, read off. -/
theorem lowerCoeffShift_monomial (j : ℕ) (d : ℕ →₀ ℕ) :
    lowerCoeffShift L j (MvPolynomial.monomial d 1)
      = (-1 : Total L) ^ d j * MvPolynomial.C (Sym.elemSymm L (d j + 1)) *
        MvPolynomial.monomial (Finsupp.erase j d) 1 := by
  have hb : (MvPolynomial.basisMonomials ℕ (Sym.Lambda L)) d
      = MvPolynomial.monomial d 1 := congrFun (MvPolynomial.coe_basisMonomials ℕ _) d
  rw [lowerCoeffShift, ← hb]
  exact Module.Basis.constr_basis _ _ _ _

/-- **Carlsson and Mellit's lowering operator `d_-`.** `HJO.Sweep.dminusCM`: for `k ≥ 1`
and `F ∈ V_k`, writing `τ^-_{k,k}(F) = ∑_j F_j y_k^j` with `F_j ∈ V_{k-1}`, the value is
`∑_j (-1)^j e_{j+1} F_j`.

It is not `HJO.Sweep.dminus`, which is the modified operator `d^♭_-` of `HJO.Sweep.dminus` and
pairs `F_j` with `e_j` rather than `e_{j+1}`. -/
@[hjo "def_cm_dminus"]
noncomputable def dminusCM (q : L) (k : ℕ) : Module.End L (Total L) :=
  (lowerCoeffShift L (k - 1)).restrictScalars L ∘ₗ (qshiftNeg q k).toLinearMap

/-- **`d_-(y_k^m) = (-1)^m e_{m+1}`**, the defining formula of the lowering operator read on a power
of the last variable: `τ^-_{k,k}` fixes the auxiliary variables, so the single surviving term is the
one at `j = m`, and the elementary function it carries is `e_{m+1}`.

At `m = 0` this is `d_-(1) = e_1`, whereas the modified operator gives `d^♭_-(1) = e_0 = 1`: the two
operators are separated already on the unit, which is the value check on the index shift. -/
@[hjo "def_cm_dminus"]
theorem dminusCM_auxVar_pow (q : L) (k m : ℕ) :
    dminusCM q (k + 1) ((auxVar (k + 1) : Total L) ^ m)
      = (-1 : Total L) ^ m * MvPolynomial.C (Sym.elemSymm L (m + 1)) := by
  have hav : (auxVar (k + 1) : Total L) = MvPolynomial.X k := by
    rw [auxVar, Nat.add_sub_cancel]
  have hpow : ((MvPolynomial.X k : Total L)) ^ m = MvPolynomial.monomial (Finsupp.single k m) 1 :=
    MvPolynomial.X_pow_eq_monomial
  rw [hav, dminusCM, LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
    LinearMap.restrictScalars_apply, map_pow, qshiftNeg_auxVar, hpow, Nat.add_sub_cancel,
    lowerCoeffShift_monomial]
  simp

/-- The two lowering operators disagree on the unit: `d_-(1) = e_1 = p_1` while
`d^♭_-(1) = e_0 = 1`. So `HJO.Sweep.dminusCM` and `HJO.Sweep.dminus` are different operators, and
the index shift in `lowerCoeffShift` is not a transcription slip. -/
theorem dminusCM_one (q : L) (k : ℕ) :
    dminusCM q (k + 1) (1 : Total L) = MvPolynomial.C (Sym.elemSymm L 1) := by
  have h := dminusCM_auxVar_pow q k 0
  rw [pow_zero] at h
  rw [h, pow_zero, one_mul]

end DminusCM

end HJO.Sweep
