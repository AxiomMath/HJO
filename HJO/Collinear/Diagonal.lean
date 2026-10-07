/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Collinear.ConjPsi
public import HJO.Collinear.DopStarPair
public meta import HJO.Attr

/-! # The diagonal slope operators

The diagonal is the base case of the Euclidean descent: a coprime pair reaches `(1,1)`, and there
neither of the two lattice steps applies. What replaces them is that every diagonal slope operator
is a conjugated multiplication.

The recursion `Q_{k,k} = M⁻¹(Q_{k-1,k} D₀ - D₀ Q_{k-1,k})` puts `Q_{k,k}` in terms of the ray above
the diagonal, which `conj_psi` identifies with the starred basic operators, scaled: `Q_{k-1,k}` is
`-(qu)^{1-k}` times the `∇`-conjugate of `D*_k`. Since `∇` commutes with `D₀`, the bracket is the
`∇`-conjugate of the commutator `D₀D*_k - D*_kD₀`, and that commutator is multiplication by
`M (qu)^{k-1} U_k`. The two scalars cancel against `M⁻¹` and `-(qu)^{1-k}`, leaving
`Q_{k,k} = ∇ ∘ (U_k ·) ∘ ∇⁻¹`.

Diagonal operators therefore commute, because multiplications by elements of a commutative ring do
and conjugation is an algebra automorphism of `End_𝕜(Λ)`. That is the base case the Euclidean
descent of `collinear_commute_of_diag` needs, so with this file the collinear commutation reduces to
the two existence statements: a Macdonald conjugator and an index shift.

The hypotheses. `M ≠ 0` is carried because the route divides by `M`, and it cannot be dropped: at
`u = 1` the identity map of `Λ` satisfies every clause of `IsMacdonaldConjugator` while the slope
operators above width one do not survive. Over a general field `q u ≠ 0` and `q u ≠ 1` are needed as
well — the first because the conjugation on the ray above the diagonal accumulates powers of
`(qu)⁻¹` and because `M̃ = (qu)⁻¹M`, the second because the axis generators are defined by dividing
by `qu - 1`. Working in `ℚ(q,u)` gives both for free; the algebraic independence the quoted
collinear statement already carries supplies them, so nothing downstream pays for them.

The commutation statement itself is not false at `M = 0`: all the operators in sight commute
there. It carries `M ≠ 0` because its only route is through the conjugation, and discharging it
would need a second argument at `M = 0` resting on a value of `M⁻¹` that the definition of the
slope operators does not fix.
-/

@[expose] public section

namespace HJO.Sym

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L} {nabla : Module.End L (Lambda L)}

/-- **The diagonal slope operators are conjugated multiplications, inverse-free form.** For every
`k ≥ 1` and every `f ∈ Λ`, `Q_{k,k}(∇ f) = ∇(U_k f)`.

At `k = 1` this is the conjugator's second clause together with `U₁ = -e₁`. For `k ≥ 2` the
recursion on the diagonal reduces it to the commutator of `D₀` with `D*_k`, which
`dop_zero_dopStar_commutator` evaluates as multiplication by `M (qu)^{k-1} U_k`; the scalar
`-(qu)^{1-k}` of `conj_psi` and the `M⁻¹` of the recursion cancel it exactly. -/
theorem qop_diag_apply_nabla (h : IsMacdonaldConjugator q u nabla)
    (hM : (1 - q) * (1 - u) ≠ 0) (hv0 : q * u ≠ 0) (hv1 : q * u ≠ 1) :
    ∀ k : ℕ, 1 ≤ k → ∀ f : Lambda L,
      Qop q u k k (nabla f) = nabla (axisGen (q * u) k * f) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    intro f
    rw [qop_one, axisGen_one hv0 hv1, neg_mul, map_neg, h.dop_one_apply f]
  | succ k hk _ =>
    intro f
    have hk1 : k + 1 - 1 = k := by omega
    have hvk : ((q * u) ^ k) ≠ 0 := pow_ne_zero _ hv0
    -- the two halves of the bracket, both through the starred conjugation
    have hpsi : ∀ g : Lambda L, Qop q u k (k + 1) (nabla g)
        = -(((q * u) ^ k)⁻¹ • nabla (DopStar q u (k + 1) g)) :=
      qop_pred_apply_nabla h hM hv0 k hk
    have hT1 : Qop q u k (k + 1) (Dop q u 0 (nabla f))
        = -(((q * u) ^ k)⁻¹ • nabla (DopStar q u (k + 1) (Dop q u 0 f))) := by
      rw [← h.map_dop_zero f, hpsi (Dop q u 0 f)]
    have hT2 : Dop q u 0 (Qop q u k (k + 1) (nabla f))
        = -(((q * u) ^ k)⁻¹ • nabla (Dop q u 0 (DopStar q u (k + 1) f))) := by
      rw [hpsi f, map_neg, map_smul, h.map_dop_zero]
    -- the bracket is the conjugate of the commutator
    have hrec := LinearMap.congr_fun (qop_diag_rec q u (show 2 ≤ k + 1 by omega)) (nabla f)
    rw [hk1] at hrec
    simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.mul_apply] at hrec
    have hbr : -(((q * u) ^ k)⁻¹ • nabla (DopStar q u (k + 1) (Dop q u 0 f)))
        - -(((q * u) ^ k)⁻¹ • nabla (Dop q u 0 (DopStar q u (k + 1) f)))
        = ((q * u) ^ k)⁻¹ • nabla (Dop q u 0 (DopStar q u (k + 1) f)
            - DopStar q u (k + 1) (Dop q u 0 f)) := by
      rw [map_sub, smul_sub]
      abel
    rw [hrec, hT1, hT2, hbr,
      dop_zero_dopStar_commutator q u hv0 hv1 (show 1 ≤ k + 1 by omega) f, hk1,
      show MvPolynomial.C ((1 - q) * (1 - u) * (q * u) ^ k) * axisGen (q * u) (k + 1) * f
          = ((1 - q) * (1 - u) * (q * u) ^ k) • (axisGen (q * u) (k + 1) * f) from by
        rw [MvPolynomial.smul_eq_C_mul, mul_assoc],
      map_smul, smul_smul, smul_smul,
      show ((1 - q) * (1 - u))⁻¹ * ((q * u) ^ k)⁻¹ * ((1 - q) * (1 - u) * (q * u) ^ k)
          = (((1 - q) * (1 - u))⁻¹ * ((1 - q) * (1 - u)))
            * (((q * u) ^ k)⁻¹ * (q * u) ^ k) from by ring,
      inv_mul_cancel₀ hM, inv_mul_cancel₀ hvk, one_mul, one_smul]

/-- **The diagonal slope operators are conjugated multiplications.** For a Macdonald conjugator
`∇` with `M ≠ 0`, `q u ≠ 0` and `q u ≠ 1`, every `k ≥ 1` and every `f ∈ Λ`,

  `Q_{k,k} f = ∇(U_k · ∇⁻¹ f)`. -/
@[hjo "lem_qop_diag_conj"]
theorem qop_diag_conj (h : IsMacdonaldConjugator q u nabla) (hM : (1 - q) * (1 - u) ≠ 0)
    (hv0 : q * u ≠ 0) (hv1 : q * u ≠ 1) {k : ℕ} (hk : 1 ≤ k) (f : Lambda L) :
    Qop q u k k f
      = nabla (axisGen (q * u) k
          * (LinearEquiv.ofBijective nabla h.bijective).symm f) := by
  have hf : nabla ((LinearEquiv.ofBijective nabla h.bijective).symm f) = f :=
    (LinearEquiv.ofBijective nabla h.bijective).apply_symm_apply f
  have hkey := qop_diag_apply_nabla h hM hv0 hv1 k hk
    ((LinearEquiv.ofBijective nabla h.bijective).symm f)
  rwa [hf] at hkey

/-- **The diagonal slope operators commute.** For `M ≠ 0`, `q u ≠ 0` and `q u ≠ 1`, and given that
a Macdonald conjugator exists, `Q_{k,k}` and `Q_{l,l}` commute for all `k, l ≥ 1`.

Both are `∇`-conjugates of multiplications by axis generators, `Λ` is commutative, and conjugation
by a bijective linear map is an algebra automorphism of `End_𝕜(Λ)`.

The existence of the conjugator is a hypothesis rather than an appeal to
`exists_isMacdonaldConjugator`, because that theorem is itself conditional on the existence of a
modified Macdonald family. One may invoke existence outright; here it is carried,
which costs its only use nothing, since the Euclidean descent of `collinear_commute_of_diag`
takes the conjugator as a hypothesis already. -/
@[hjo "lem_qop_diag_commute"]
theorem qop_diag_commute (hM : (1 - q) * (1 - u) ≠ 0) (hv0 : q * u ≠ 0) (hv1 : q * u ≠ 1)
    (hconj : ∃ nabla : Module.End L (Lambda L), IsMacdonaldConjugator q u nabla)
    {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) :
    Commute (Qop q u k k) (Qop q u l l) := by
  obtain ⟨nabla, h⟩ := hconj
  refine LinearMap.ext fun x => ?_
  obtain ⟨g, rfl⟩ := h.bijective.surjective x
  simp only [Module.End.mul_apply]
  rw [qop_diag_apply_nabla h hM hv0 hv1 l hl g,
    qop_diag_apply_nabla h hM hv0 hv1 k hk (axisGen (q * u) l * g),
    qop_diag_apply_nabla h hM hv0 hv1 k hk g,
    qop_diag_apply_nabla h hM hv0 hv1 l hl (axisGen (q * u) k * g),
    ← mul_assoc, ← mul_assoc, mul_comm (axisGen (q * u) k) (axisGen (q * u) l)]

end HJO.Sym

/-! ### The collinear commutation, from the two existence statements alone

`HJO.CollinearNarrowed.collinearCommute_of_diag` takes three hypotheses: a Macdonald conjugator,
an index shift, and the diagonal base case. The base case is discharged from the first of them
together with the genericity the quoted statement already carries, so the collinear input follows
from the two existence statements alone.
-/

namespace HJO.CollinearNarrowed

open HJO.Sym

/-- **The narrowed collinear input, from the two structural data.** Composing with
`collinearCommutation` this supplies `HJO.External.CollinearCommutation`, so the collinear
commutation holds modulo exactly two existence statements: a Macdonald conjugator and an
index shift.

The three parameter conditions the diagonal base case needs -- `M ≠ 0`, `q u ≠ 0` and `q u ≠ 1` --
all come from the algebraic independence the quoted statement is stated at, so none of them
survives into the conclusion. -/
theorem collinearCommute_of_structures {L : Type*} [Field L] [Algebra ℚ L]
    (hconj : ∀ q u : L, AlgebraicIndependent ℤ ![q, u] →
      ∃ nabla : Module.End L (Lambda L), IsMacdonaldConjugator q u nabla)
    (hshift : ∀ q u : L, AlgebraicIndependent ℤ ![q, u] →
      ∃ S : DopAlgebra q u →ₐ[L] DopAlgebra q u, IsIndexShift q u S) :
    CollinearCommute L :=
  collinearCommute_of_diag hconj hshift fun q u hqu k l hk hl =>
    qop_diag_commute (one_sub_mul_one_sub_ne_zero_of_algebraicIndependent hqu)
      (mul_ne_zero_of_algebraicIndependent hqu)
      (by simpa using pow_succ_ne_one_of_algebraicIndependent hqu 0)
      (hconj q u hqu) hk hl

end HJO.CollinearNarrowed
