/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Macdonald.Conjugator
public meta import HJO.Attr

/-! # The two remaining recursions of the slope operators, and the starred conjugation

Two more instances of the uniform recursion `Sym.qop_rec`, both read off the split of the
primitive pair, and the conjugation identity they drive.

The pair `(a, a + 1)` is coprime, so it is its own primitive pair, and its split is `(1, 1)`;
`qop_lower_rec` is the recursion there,

  `Q_{a,a+1} = M⁻¹ (Q_{a-1,a} D_1 - D_1 Q_{a-1,a})`,   `M = (1 - q)(1 - u)`.

The diagonal pair `(k, k)` has primitive pair `(1, 1)`, whose primitive split is `(1, 0)` by the
width-one clause of `Sym.primitiveSplit`, so `qop_diag_rec` reads

  `Q_{k,k} = M⁻¹ (Q_{k-1,k} D_0 - D_0 Q_{k-1,k})`.

Neither statement cases on coprimality: each is `Sym.qop_rec` with its split computed.

The ray *above* the diagonal is then the `∇`-conjugate of the **starred** basic operators, scaled
by `-(q u)^{1-k}`:

  `Q_{k-1,k} f = -(q u)^{1-k} ∇(D*_k(∇⁻¹ f))`,   `k ≥ 2`,

which is `conj_psi`, the mirror of `conj_phi` on the ray below the diagonal -- where the conjugate
is of the *unstarred* `D_k` and carries no scalar at all. `qop_pred_apply_nabla` is the same
identity in the inverse-free form the induction runs in. That induction goes along
`qop_lower_rec`, and each step feeds the starred commutation
`D*_k(e₁ f) = e₁ D*_k f - M̃ D*_{k+1} f` of `Sym.dopStar_elemSymm_one_mul` through the commutator
with `D_1`, the conjugator turning multiplication by `e₁` into `-D_1` and `D*_1` into
multiplication by `e₁`. Its base case is `dop_two_apply_nabla`, the same starred commutation at
`k = 1` with both of those clauses substituted.

## Parameter hypotheses

Dividing by `M = (1 - q)(1 - u)` at every step of the recursion is the hypothesis `M ≠ 0`. It cannot
be dropped: at `u = 1` the identity map is a Macdonald conjugator, while the slope operators of
first index above one all vanish, so the identity would there assert `0 = -e₁`.

The hypothesis `q u ≠ 0` is needed *on top of* that. It enters
through the scalar identity `M̃ = (q u)⁻¹ M` between the starred and unstarred parameter products,
which is what makes the negative power of `q u` appear at all and what the induction advances that
power by, one factor per step; the identity fails at `q = 0`, where its left side is `1 - u⁻¹` and
its right side is `0`, and symmetrically at `u = 0`. It is also what makes the inverse power
`(q u)^{-a}` in the statement mean anything. Working in `ℚ(q, u)` it holds for free.
-/

@[expose] public section

namespace HJO.Sym

/-! ### The two parameter products against each other -/

/-- **The starred parameter product is the unstarred one over `q u`:**
`M̃ = (1 - q⁻¹)(1 - u⁻¹) = M (q u)⁻¹` for `M = (1 - q)(1 - u)`. Each factor contributes one
inversion, `1 - q⁻¹ = -(1 - q) q⁻¹`, and the two signs cancel. Both parameters must be nonzero:
at `q = 0` the left side is `1 - u⁻¹` and the right side is `0`. -/
theorem paramProduct_inv_eq_mul_inv {K : Type*} [Field K] {q u : K} (hq : q ≠ 0) (hu : u ≠ 0) :
    paramProduct q⁻¹ u⁻¹ = (1 - q) * (1 - u) * (q * u)⁻¹ := by
  have h : paramProduct q⁻¹ u⁻¹ = (1 - q⁻¹) * (1 - u⁻¹) := rfl
  rw [h]
  field_simp
  ring

/-- **The starred parameter product against the inverse of the unstarred one:**
`M⁻¹ M̃ = (q u)⁻¹`. This is `paramProduct_inv_eq_mul_inv` with the factor `M` cancelled, and it is
the single scalar fact the induction of `qop_pred_apply_nabla` advances the power of `q u` by. -/
theorem inv_mul_paramProduct_inv {K : Type*} [Field K] {q u : K} (hq : q ≠ 0) (hu : u ≠ 0)
    (hM : (1 - q) * (1 - u) ≠ 0) :
    ((1 - q) * (1 - u))⁻¹ * paramProduct q⁻¹ u⁻¹ = (q * u)⁻¹ := by
  rw [paramProduct_inv_eq_mul_inv hq hu, ← mul_assoc, inv_mul_cancel₀ hM, one_mul]

variable {L : Type*} [Field L] [Algebra ℚ L]

/-! ### The recursion on the ray above the diagonal, and on the diagonal -/

/-- **The recursion on the ray above the diagonal.** For `a ≥ 2`,
`Q_{a,a+1} = M⁻¹ (Q_{a-1,a} D_1 - D_1 Q_{a-1,a})`, a normalised commutator. The pair `(a, a + 1)` is
coprime, so it is its own primitive pair, and its split is `(1, 1)` by `split_succ_one`; the
complementary pair is therefore `(a - 1, a)` and `Q_{1,1} = D_1`. -/
@[hjo "lem_qop_lower_rec"]
theorem qop_lower_rec (q u : L) {a : ℕ} (ha : 2 ≤ a) :
    Qop q u a (a + 1) = ((1 - q) * (1 - u))⁻¹ •
      (Qop q u (a - 1) a * Dop q u 1 - Dop q u 1 * Qop q u (a - 1) a) := by
  have hcop : Nat.Coprime a (a + 1) := by
    rw [Nat.add_comm]
    exact Nat.coprime_add_self_right.mpr (Nat.coprime_one_right a)
  have hsplit : slopeSplit a (a + 1) = (1, 1) := by
    rw [slopeSplit_eq_split (by omega) hcop, split_succ_one ha]
  have hsub : a + 1 - 1 = a := by omega
  rw [qop_rec q u (by omega) (by omega), hsplit]
  dsimp only
  rw [hsub, qop_one]

/-- **The recursion on the diagonal.** For `k ≥ 2`,
`Q_{k,k} = M⁻¹ (Q_{k-1,k} D_0 - D_0 Q_{k-1,k})`. The primitive pair of `(k, k)` is `(1, 1)`, whose
primitive split is `(1, 0)` by the width-one clause of `primitiveSplit`; the complementary pair is
therefore `(k - 1, k)` and `Q_{1,0} = D_0`. This is the one place the second entry of a split
vanishes, which is why the recursion is stated on the split of the primitive pair rather than on a
bounded search at `(k, k)`, where the Bezout equation has no solution. -/
@[hjo "lem_qop_diag_rec"]
theorem qop_diag_rec (q u : L) {k : ℕ} (hk : 2 ≤ k) :
    Qop q u k k = ((1 - q) * (1 - u))⁻¹ •
      (Qop q u (k - 1) k * Dop q u 0 - Dop q u 0 * Qop q u (k - 1) k) := by
  have hdiv : k / Nat.gcd k k = 1 := by rw [Nat.gcd_self k, Nat.div_self (by omega)]
  have hsplit : slopeSplit k k = (1, 0) := by
    rw [slopeSplit, hdiv, primitiveSplit_fst_one]
  rw [qop_rec q u (by omega) (by omega), hsplit]
  dsimp only
  rw [Nat.sub_zero, qop_one]

/-! ### Conjugation on the ray above the diagonal -/

section Conjugator

variable {q u : L} {nabla : Module.End L (Lambda L)}

/-- **The second basic operator against the conjugator.** For a Macdonald conjugator `∇` with
`M ≠ 0` and both parameters nonzero, `D_2(∇ f) = -(q u)⁻¹ ∇(D*_2 f)`.

Apply `∇` to the starred commutation `D*_1(e₁ f) = e₁ D*_1 f - M̃ D*_2 f` of
`dopStar_elemSymm_one_mul`. On the left the conjugator turns `D*_1` into multiplication by `e₁`
and then `e₁` into `-D_1`, giving `-e₁ D_1(∇ f)`; on the right it gives
`-D_1(e₁ ∇f) - M̃ ∇(D*_2 f)`, and the unstarred commutation
`D_1(e₁ ∇f) = e₁ D_1(∇f) + M D_2(∇f)` of `dop_elemSymm_one_mul` cancels the term `e₁ D_1(∇f)`
from both sides. What is left is `M D_2(∇f) = -M̃ ∇(D*_2 f)`, and `M̃ = M (q u)⁻¹`. -/
theorem dop_two_apply_nabla (h : IsMacdonaldConjugator q u nabla)
    (hM : (1 - q) * (1 - u) ≠ 0) (hq : q ≠ 0) (hu : u ≠ 0) (f : Lambda L) :
    Dop q u 2 (nabla f) = -((q * u)⁻¹ • nabla (DopStar q u 2 f)) := by
  have hcancel : ∀ X Y Z : Lambda L, -(X + Y) - Z = -X → Y = -Z :=
    fun _ _ _ hxyz => by linear_combination -hxyz
  have h1 : nabla (DopStar q u 1 (elemSymm L 1 * f))
      = -(elemSymm L 1 * Dop q u 1 (nabla f)) := by
    rw [h.map_dopStar_one, h.map_elemSymm_one_mul, mul_neg]
  rw [dopStar_elemSymm_one_mul q u 1 f, show (1 : ℕ) + 1 = 2 from rfl, map_sub, map_smul,
    h.map_elemSymm_one_mul, h.map_dopStar_one, dop_elemSymm_one_mul q u 1 (nabla f),
    show (1 : ℕ) + 1 = 2 from rfl] at h1
  have h2 := hcancel _ _ _ h1
  have h3 := congrArg (fun z : Lambda L => ((1 - q) * (1 - u))⁻¹ • z) h2
  simp only [smul_neg, smul_smul, inv_mul_cancel₀ hM, one_smul] at h3
  rw [h3, inv_mul_paramProduct_inv hq hu hM]

/-- **The ray above the diagonal is a starred conjugate, inverse-free form.** For a Macdonald
conjugator `∇` with `M ≠ 0` and `q u ≠ 0`, every `a ≥ 1` and every `f ∈ Λ`,
`Q_{a,a+1}(∇ f) = -(q u)^{-a} ∇(D*_{a+1} f)`.

Induction on `a` from `1`, where the claim is `dop_two_apply_nabla` because `Q_{1,2} = D_2`. The
step runs the recursion `qop_lower_rec` at `a + 1`, whose commutator is against `D_1`: the
conjugator turns `D_1(∇ g)` into `∇(-(e₁ g))`, so the inductive hypothesis evaluates both halves,
one at `-(e₁ f)` and one after `D_1`, and their difference is
`(q u)^{-a} ∇(D*_{a+1}(e₁ f) - e₁ D*_{a+1} f) = -(q u)^{-a} M̃ ∇(D*_{a+2} f)`
by the starred commutation. Dividing by `M` and using `M̃ = M (q u)⁻¹` turns `(q u)^{-a} M̃ M⁻¹`
into `(q u)^{-(a+1)}`, which is where both parameter hypotheses are spent. -/
theorem qop_pred_apply_nabla (h : IsMacdonaldConjugator q u nabla)
    (hM : (1 - q) * (1 - u) ≠ 0) (hv0 : q * u ≠ 0) :
    ∀ a : ℕ, 1 ≤ a → ∀ f : Lambda L,
      Qop q u a (a + 1) (nabla f) = -(((q * u) ^ a)⁻¹ • nabla (DopStar q u (a + 1) f)) := by
  have hq : q ≠ 0 := left_ne_zero_of_mul hv0
  have hu : u ≠ 0 := right_ne_zero_of_mul hv0
  have hd1 : ∀ g : Lambda L, Dop q u 1 (nabla g) = nabla (-(elemSymm L 1 * g)) := fun g => by
    rw [map_neg]
    exact h.dop_one_apply g
  intro a ha
  induction a, ha using Nat.le_induction with
  | base =>
    intro f
    rw [show (1 : ℕ) + 1 = 2 from rfl, qop_one, pow_one]
    exact dop_two_apply_nabla h hM hq hu f
  | succ a ha ih =>
    intro f
    have hT1 : Qop q u a (a + 1) (Dop q u 1 (nabla f))
        = ((q * u) ^ a)⁻¹ • nabla (DopStar q u (a + 1) (elemSymm L 1 * f)) := by
      rw [hd1 f, ih (-(elemSymm L 1 * f)), map_neg, map_neg, smul_neg, neg_neg]
    have hT2 : Dop q u 1 (Qop q u a (a + 1) (nabla f))
        = ((q * u) ^ a)⁻¹ • nabla (elemSymm L 1 * DopStar q u (a + 1) f) := by
      rw [ih f, map_neg, map_smul, hd1 (DopStar q u (a + 1) f), map_neg, smul_neg, neg_neg]
    have hsc : ((1 - q) * (1 - u))⁻¹ * (((q * u) ^ a)⁻¹ * paramProduct q⁻¹ u⁻¹)
        = ((q * u) ^ (a + 1))⁻¹ := by
      rw [show ((1 - q) * (1 - u))⁻¹ * (((q * u) ^ a)⁻¹ * paramProduct q⁻¹ u⁻¹)
            = ((q * u) ^ a)⁻¹ * (((1 - q) * (1 - u))⁻¹ * paramProduct q⁻¹ u⁻¹) from by
          ring, inv_mul_paramProduct_inv hq hu hM, pow_succ, ← mul_inv]
    have hrec := LinearMap.congr_fun (qop_lower_rec q u (show 2 ≤ a + 1 by omega)) (nabla f)
    rw [Nat.add_sub_cancel] at hrec
    simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.mul_apply] at hrec
    rw [hrec, hT1, hT2, ← smul_sub, ← map_sub, dopStar_elemSymm_one_mul q u (a + 1) f,
      sub_sub_cancel_left, map_neg, map_smul]
    simp only [smul_neg, smul_smul, hsc]

/-- **The ray above the diagonal is a starred conjugate.** For a Macdonald conjugator `∇` with
`M ≠ 0` and `q u ≠ 0`, every `k ≥ 2` and every `f ∈ Λ`,

  `Q_{k-1,k} f = -(q u)^{1-k} ∇(D*_k(∇⁻¹ f))`.

This is `qop_pred_apply_nabla` at `a = k - 1` evaluated at `∇⁻¹ f`, the inverse being the
`LinearEquiv` the conjugator's bijectivity supplies. It is the mirror of `conj_phi`, which
conjugates the *unstarred* `D_k` onto the ray `(k + 1, k)` below the diagonal with no scalar. -/
@[hjo "lem_conj_psi"]
theorem conj_psi (h : IsMacdonaldConjugator q u nabla) (hM : (1 - q) * (1 - u) ≠ 0)
    (hv0 : q * u ≠ 0) {k : ℕ} (hk : 2 ≤ k) (f : Lambda L) :
    Qop q u (k - 1) k f
      = -(((q * u) ^ (k - 1))⁻¹ •
          nabla (DopStar q u k ((LinearEquiv.ofBijective nabla h.bijective).symm f))) := by
  have hf : nabla ((LinearEquiv.ofBijective nabla h.bijective).symm f) = f :=
    (LinearEquiv.ofBijective nabla h.bijective).apply_symm_apply f
  have hk1 : k - 1 + 1 = k := by omega
  have hkey := qop_pred_apply_nabla h hM hv0 (k - 1) (by omega)
    ((LinearEquiv.ofBijective nabla h.bijective).symm f)
  rw [hk1, hf] at hkey
  exact hkey

end Conjugator

end HJO.Sym
