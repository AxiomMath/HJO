/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.MellitLhsCompInduction
public import HJO.Shuffle.MellitStraightMonomial
public import HJO.Shuffle.SlopeActions
public meta import HJO.Attr

/-! # The collinear slope needs no bridge, and `HJO.Sweep.exists_slopeActions` cannot supply one

`HJO.Mellit.qop_double_apply_one_of_lhsWord` (`HJO/Shuffle/MellitLhsCompInduction.lean`) shows
that the clause of `HJO.Mellit.lhsRewrite_sweepWitness` at the two-part composition `α = (1,1)`
names `Q_{2a,2b}`, the slope operator at the **doubled**, hence non-coprime, slope. One might
conclude from this, and from the failure of the width-one straight monomials
(`HJO/Shuffle/MellitStraightMonomial.lean`), that the doubled slope "has to come from
`HJO.Sweep.exists_slopeActions`". **That conclusion is wrong, in both directions**, and this file
proves both halves. What does hold is that the doubled slope occurs in the clause and is not a
width-one straight monomial. What fails is the claim about where it must come from.

## The doubled slope is already a commutator of two *coprime* slope operators

`HJO.Sym.Qop`'s own non-coprime branch is not an opaque extension: it *is* a reduction to the
coprime regime. `HJO.Sym.qop_eq_bracket` reads `Q_{m,n} = M^{-1}[Q_{m-r,n-s}, Q_{r,s}]` with
`(r,s) = \mathrm{slopeSplit}(m,n)` and **both** `(r,s)` and `(m-r,n-s)` coprime
(`HJO.Sym.slopeSplit_spec`). What this file adds is that at a collinear multiple the split is the
split of the *primitive* pair and therefore does not move with the multiplicity:

* `HJO.Sym.slopeSplit_mul` — `\mathrm{slopeSplit}(ak, bk) = \mathrm{primitiveSplit}(a,b)` for every
  `k ≥ 1` and coprime `(a,b)`.
* `HJO.Sym.qop_collinear_eq_bracket` — hence for `k ≥ 2`,
  `Q_{ak,bk} = M^{-1}[Q_{ak-r, bk-s}, Q_{r,s}]` with `(r,s) = \mathrm{primitiveSplit}(a,b)`, one
  fixed coprime slope, and `(ak-r, bk-s)` coprime as well
  (`HJO.Sym.coprime_collinear_complement`).

So `Θ(U_k) = Q_{ak,bk}` — which is what `HJO.Sym.IsSlopeHom` asserts at every `k ≥ 1`, non-coprime
indices included — is a commutator of coprime slope operators, computed inside the `D_n`-algebra on
`Λ`, with no replicated action anywhere. `HJO.Mellit.qop_double_apply_one_of_lhsWord_coprime` is the
clause at `α = (1,1)` with the doubled-slope term replaced by that commutator, so that every
operator in it is at a coprime slope.

The price is visible in the indices. `HJO.Mellit.LhsAt` at `α` reads `Θ(C_α 1)`, and `C_α 1` has
degree `N = α.sum` (`HJO.Sym.copComp_shiftsDegree`), so expanding it in the axis generators uses
`U_k` for `k ≤ N` and hence `Q_{ak,bk}` for `k ≤ N`; the complement `(ak - r, bk - s)` has first
coordinate `ak - r > (k-1)a`, because `r < a`. So the coprime slopes the clause needs grow
**linearly in the size `N` of the composition**. The coprime hierarchy is therefore not made
unnecessary by this reduction; it is made unbounded.

## `HJO.Sweep.exists_slopeActions` carries no information at a non-coprime index

`HJO.Sweep.exists_slopeActions` attaches actions to *all* of `ℕ²` only as a totalisation. Every
clause of its conclusion beyond "is an action" constrains the family at a **coprime** index: the two
axis pairs are coprime, and in a unimodular pair both members and their mediant are coprime
(`HJO.Mellit.IsUnimodular.coprime_fst`, `_coprime_snd`, `_coprime_mediant`). Consequently:

* `HJO.Sweep.slopeFamilySpec_coprimeMod` — a family satisfying the conclusion may be replaced, at
  every non-coprime index at once, by the base pair, and it still satisfies the whole conclusion.
* `HJO.Sweep.qop_eq_of_slopeActions_bridge` — therefore any map `F` from an action to an
  endomorphism of `Λ` that computes `Q_{m,n}` from the family's value at a non-coprime `(m,n)`
  forces `Q_{m,n}` to be **one and the same operator** at every non-coprime slope.
* `HJO.Sweep.qop_collinear_apply_one_eq_zero_of_slopeActions_bridge` — along one fixed ray the same
  collapse forces `Q_{2a,2b}(1) = 0`, for every `a` and every `b ≥ 1`.
* `HJO.Sweep.not_slopeActions_bridge` — and that is false: `Q_{2,2}` and `Q_{2,4}` differ, the first
  landing the vacuum in `Λ_2` on a nonzero element and the second in `Λ_4`.

That is the witness. It does not say the sweep module is irrelevant to `LhsComputes`; it says the
*index* `(ka,kb)` of the family is not where the doubled slope lives, so a bridge written at that
index is a bridge to the base pair, which does not mention `a` or `b` at all.

## Genericity

The arithmetic and `HJO.Sym.qop_collinear_eq_bracket` carry **nothing** on `q`, `u` or `M`: they are
rearrangements of `HJO.Sym.Qop`'s own branch. `HJO.Mellit.qop_double_apply_one_of_lhsWord_coprime`
inherits `qu ≠ 0` and `qu ≠ 1` from the clause it rewrites. `HJO.Sweep.not_slopeActions_bridge`
needs `M ≠ 0`, which is `HJO.Sym.qop_two_two_apply_one`'s.

## Implementation notes

`HJO.Mellit.lhsRewrite_sweepWitness` is not proved here; this file shows that its doubled-slope
term needs no input from `HJO.Sweep.exists_slopeActions`, and what replaces such an input.

## References

This file concerns the slope operators `HJO.Sym.Qop`, the slope homomorphisms of
`HJO.Sym.IsSlopeHom`, and the slope actions of `HJO.Sweep.exists_slopeActions`.
-/

@[expose] public section

namespace HJO.Sym

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L} {a b k : ℕ}

/-! ### A collinear multiple is never coprime, and its split is the primitive one -/

/-- **A proper collinear multiple is never coprime.** The gcd of `(ak, bk)` is
`k·\gcd(a,b)`, so `k` divides it, and `k ≥ 2`. Nothing at all is needed of `a` and `b`. -/
theorem not_coprime_mul_right (hk : 2 ≤ k) : ¬ Nat.Coprime (a * k) (b * k) := by
  intro h
  rw [Nat.Coprime, Nat.gcd_mul_right] at h
  have hd : k ∣ 1 := ⟨Nat.gcd a b, by rw [Nat.mul_comm]; exact h.symm⟩
  exact absurd (Nat.dvd_one.1 hd) (by omega)

/-- `1 < ak` for `1 < a` and `2 ≤ k`, in the form the bounds of `HJO.Sym.Qop`'s branch want. -/
theorem one_lt_mul_of_one_lt (ha : 1 < a) (hk : 2 ≤ k) : 1 < a * k :=
  lt_of_lt_of_le (by omega : (1 : ℕ) < a * 2) (Nat.mul_le_mul (le_refl a) hk)

/-- **The split of a collinear multiple is the split of the primitive pair**, for every
multiplicity `k ≥ 1`. `HJO.Sym.Qop`'s non-coprime branch splits the primitive pair and never the
multiplied one, so the split it uses at `(ak, bk)` is *independent of `k`*. -/
theorem slopeSplit_mul (hab : Nat.Coprime a b) (hk : 0 < k) :
    slopeSplit (a * k) (b * k) = primitiveSplit a b := by
  have hg : Nat.gcd (a * k) (b * k) = k := by
    rw [Nat.gcd_mul_right, hab, Nat.one_mul]
  rw [slopeSplit, hg, Nat.mul_div_cancel _ hk, Nat.mul_div_cancel _ hk]

/-! ### The slope operator at a collinear multiple, in coprime terms -/

/-- **Both slopes of the collinear bracket are coprime.** The fixed one is the primitive split of
`(a,b)`; the moving one is its complement in `(ak, bk)`. -/
theorem coprime_collinear_split (ha : 1 < a) (hb : 0 < b) (hab : Nat.Coprime a b) (hk : 2 ≤ k) :
    Nat.Coprime (primitiveSplit a b).1 (primitiveSplit a b).2 := by
  have h := slopeSplit_spec (m := a * k) (n := b * k) (one_lt_mul_of_one_lt ha hk)
    (Nat.mul_pos hb (by omega)) (not_coprime_mul_right hk)
  rw [slopeSplit_mul hab (by omega)] at h
  exact h.2.2.2.2.2.1

/-- **The complement of the collinear split is coprime.** This is what keeps the reduction inside
the coprime regime: `Q_{ak,bk}` is a commutator of two operators neither of which re-enters
`HJO.Sym.Qop`'s non-coprime branch. -/
theorem coprime_collinear_complement (ha : 1 < a) (hb : 0 < b) (hab : Nat.Coprime a b)
    (hk : 2 ≤ k) :
    Nat.Coprime (a * k - (primitiveSplit a b).1) (b * k - (primitiveSplit a b).2) := by
  have h := slopeSplit_spec (m := a * k) (n := b * k) (one_lt_mul_of_one_lt ha hk)
    (Nat.mul_pos hb (by omega)) (not_coprime_mul_right hk)
  rw [slopeSplit_mul hab (by omega)] at h
  exact h.2.2.2.2.2.2

/-- **The slope operator at a collinear multiple is a commutator of two coprime slope operators.**

For coprime `(a,b)` with `a ≥ 2` and `b ≥ 1` and every multiplicity `k ≥ 2`, writing
`(r,s) = \mathrm{primitiveSplit}(a,b)`,

`Q_{ak,bk} = M^{-1}(Q_{ak-r,bk-s}Q_{r,s} - Q_{r,s}Q_{ak-r,bk-s})`,   `M = (1-q)(1-u)`,

and both `(r,s)` and `(ak-r, bk-s)` are coprime
(`HJO.Sym.coprime_collinear_split`, `HJO.Sym.coprime_collinear_complement`). Unconditional in
`q` and `u`: this is `HJO.Sym.Qop`'s own non-coprime branch with the split identified.

**The consequence for `HJO.Mellit.lhsRewrite_sweepWitness`.** `HJO.Sym.IsSlopeHom` sends `U_k` to
`Q_{ak,bk}`, so the non-coprime collinear values a slope homomorphism carries are not new data —
they are determined by the coprime slopes `(r,s)` and `(ak-r, bk-s)`. No replicated action is needed
to supply them. -/
@[hjo "lem_qop_collinear_bracket"]
theorem qop_collinear_eq_bracket (q u : L) (ha : 1 < a) (hb : 0 < b) (hab : Nat.Coprime a b)
    (hk : 2 ≤ k) :
    Qop q u (a * k) (b * k) = ((1 - q) * (1 - u))⁻¹ •
      (Qop q u (a * k - (primitiveSplit a b).1) (b * k - (primitiveSplit a b).2) *
          Qop q u (primitiveSplit a b).1 (primitiveSplit a b).2 -
        Qop q u (primitiveSplit a b).1 (primitiveSplit a b).2 *
          Qop q u (a * k - (primitiveSplit a b).1) (b * k - (primitiveSplit a b).2)) := by
  rw [qop_eq_bracket q u (m := a * k) (n := b * k) (one_lt_mul_of_one_lt ha hk)
    (Nat.mul_pos hb (by omega)) (not_coprime_mul_right hk), slopeSplit_mul hab (by omega)]

/-! ### Two non-coprime slopes whose operators differ -/

/-- **`Q_{2,4} = M^{-1}[D_3, D_1]`.** `(2,4)` is not coprime, its primitive pair is `(1,2)` and
`\mathrm{primitiveSplit}(1,2) = (1,1)`, so the bracket is at `(2-1, 4-1) = (1,3)` and `(1,1)`, and
both of those have first index `1`, where `Q_{1,n} = D_n`. -/
theorem qop_two_four (q u : L) :
    Qop q u 2 4 = ((1 - q) * (1 - u))⁻¹ • (Dop q u 3 * Dop q u 1 - Dop q u 1 * Dop q u 3) := by
  have hnc : ¬ Nat.Coprime 2 4 := by decide
  have hsplit : slopeSplit 2 4 = ((1 : ℕ), (1 : ℕ)) := by
    rw [slopeSplit, show Nat.gcd 2 4 = 2 from rfl, show (2 : ℕ) / 2 = 1 from rfl,
      show (4 : ℕ) / 2 = 2 from rfl, primitiveSplit]
    norm_num
  rw [qop_of_not_coprime q u (by norm_num) hnc, hsplit]
  norm_num [qopPrim_of_le_one q u _ (le_refl 1)]

/-- **`Q_{2,2} ≠ Q_{2,4}`**, at every `q, u` with `M ≠ 0`.

Both slopes are non-coprime, so a bridge from `HJO.Sweep.exists_slopeActions` written at the index
of the slope would have to make the two operators equal (`HJO.Sweep.qop_eq_of_slopeActions_bridge`).
They are not: `HJO.Sym.qop_shiftsDegree` puts `Q_{2,2}(1)` in `Λ_2` and `Q_{2,4}(1)` in `Λ_4`, and
`HJO.Sym.qop_two_two_apply_one` makes the first `e_1^2 + (q+u)e_2`, which is nonzero for every
scalar (`HJO.Sym.elemSymm_one_sq_add_smul_elemSymm_two_ne_zero`). -/
theorem qop_two_two_ne_qop_two_four (hM : (1 - q) * (1 - u) ≠ 0) :
    Qop q u 2 2 ≠ Qop q u 2 4 := by
  intro h
  have h2 : Qop q u 2 2 (1 : Lambda L) ∈ LambdaComp L (0 + 2) :=
    (qop_shiftsDegree q u 2 2).apply_mem_lambdaComp (one_mem_lambdaComp L)
  have h4 : Qop q u 2 2 (1 : Lambda L) ∈ LambdaComp L (0 + 4) := by
    rw [h]
    exact (qop_shiftsDegree q u 2 4).apply_mem_lambdaComp (one_mem_lambdaComp L)
  have hne : Qop q u 2 2 (1 : Lambda L) ≠ 0 := by
    rw [qop_two_two_apply_one hM]
    exact elemSymm_one_sq_add_smul_elemSymm_two_ne_zero (q + u)
  exact absurd (MvPolynomial.IsWeightedHomogeneous.inj_right hne (mem_lambdaComp.1 h2)
    (mem_lambdaComp.1 h4)) (by norm_num)

/-- **Two collinear multiples of the same positive pair cannot have the same slope operator unless
it kills the vacuum.** `HJO.Sym.qop_shiftsDegree` puts `Q_{2a,2b}(1)` in `Λ_{2b}` and `Q_{3a,3b}(1)`
in `Λ_{3b}`, and `2b ≠ 3b` for `b ≥ 1`; a nonzero element of `Λ` is weighted-homogeneous of at most
one degree. No hypothesis on `q`, `u` or `M`, and none on `a`. -/
theorem qop_collinear_apply_one_eq_zero_of_eq (hb : 0 < b)
    (h : Qop q u (a * 2) (b * 2) = Qop q u (a * 3) (b * 3)) :
    Qop q u (a * 2) (b * 2) (1 : Lambda L) = 0 := by
  by_contra hne
  have h2 : Qop q u (a * 2) (b * 2) (1 : Lambda L) ∈ LambdaComp L (0 + b * 2) :=
    (qop_shiftsDegree q u (a * 2) (b * 2)).apply_mem_lambdaComp (one_mem_lambdaComp L)
  have h3 : Qop q u (a * 2) (b * 2) (1 : Lambda L) ∈ LambdaComp L (0 + b * 3) := by
    rw [h]
    exact (qop_shiftsDegree q u (a * 3) (b * 3)).apply_mem_lambdaComp (one_mem_lambdaComp L)
  exact absurd (MvPolynomial.IsWeightedHomogeneous.inj_right hne (mem_lambdaComp.1 h2)
    (mem_lambdaComp.1 h3)) (by omega)

end HJO.Sym

namespace HJO.Mellit

open HJO.Sym

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L} {a b : ℕ}

/-- **The clause at `α = (1,1)`, with every slope operator in it at a coprime slope.**

`HJO.Mellit.qop_double_apply_one_of_lhsWord` reads the clause of
`HJO.Mellit.lhsRewrite_sweepWitness` at the two-part composition and finds `Q_{2a,2b}` in it.
`HJO.Sym.qop_collinear_eq_bracket` at `k = 2` replaces that operator by
`M^{-1}[Q_{2a-r,2b-s}, Q_{r,s}]` with `(r,s)` the primitive split of `(a,b)` and both slopes
coprime. So the clause at `α = (1,1)` is an identity purely among
*coprime* slope operators — at `(a,b)`, at `(r,s)`, and at `(2a-r, 2b-s)` — and the doubled slope is
not an extra unknown.

What it is not is an identity among slope operators applied *to the vacuum*: `Q_{a,b}` appears
applied to `Q_{a,b}(1)`, and the commutator applies `Q_{2a-r,2b-s}` to `Q_{r,s}(1)`. That, and not
the non-coprimality, is what `HJO.Mellit.LhsComputes` asks for beyond its singleton case. -/
theorem qop_double_apply_one_of_lhsWord_coprime (hv0 : q * u ≠ 0) (hv1 : q * u ≠ 1)
    (ha : 1 < a) (hb : 0 < b) (hab : Nat.Coprime a b)
    {Θ : Lambda L →ₐ[L] Module.End L (Lambda L)} (hΘ : IsSlopeHom a b q u Θ)
    (h : LhsWord q u a b) :
    (u + 1) • Qop q u a b (Qop q u a b (1 : Lambda L))
        + (u * (q - 1)) • (((1 - q) * (1 - u))⁻¹ •
            (Qop q u (a * 2 - (primitiveSplit a b).1) (b * 2 - (primitiveSplit a b).2) *
                Qop q u (primitiveSplit a b).1 (primitiveSplit a b).2 -
              Qop q u (primitiveSplit a b).1 (primitiveSplit a b).2 *
                Qop q u (a * 2 - (primitiveSplit a b).1) (b * 2 - (primitiveSplit a b).2)))
            (1 : Lambda L)
      = (q * u + 1) •
          MvPolynomial.constantCoeff (lowerRun q 2 (stageWordTotal q u a b [1, 1])) := by
  rw [← qop_collinear_eq_bracket q u ha hb hab (le_refl 2)]
  exact qop_double_apply_one_of_lhsWord hv0 hv1 hΘ h

/-! ### Every index the slope-action family is constrained at is coprime -/

/-- **The left member of a unimodular pair is coprime.** `\gcd(m_1,n_1)` divides both `m_2n_1` and
`m_1n_2`, whose difference is `1`. -/
theorem IsUnimodular.coprime_fst {p p' : ℕ × ℕ} (h : IsUnimodular p p') :
    Nat.Coprime p.1 p.2 := by
  refine Nat.dvd_one.1 ?_
  have h1 : Nat.gcd p.1 p.2 ∣ p'.1 * p.2 := Dvd.dvd.mul_left (Nat.gcd_dvd_right _ _) _
  have h2 : Nat.gcd p.1 p.2 ∣ p.1 * p'.2 := Dvd.dvd.mul_right (Nat.gcd_dvd_left _ _) _
  have h3 := Nat.dvd_sub h1 h2
  rw [IsUnimodular] at h
  rwa [h, Nat.add_sub_cancel_left] at h3

/-- **The right member of a unimodular pair is coprime**, by the same subtraction. -/
theorem IsUnimodular.coprime_snd {p p' : ℕ × ℕ} (h : IsUnimodular p p') :
    Nat.Coprime p'.1 p'.2 := by
  refine Nat.dvd_one.1 ?_
  have h1 : Nat.gcd p'.1 p'.2 ∣ p'.1 * p.2 := Dvd.dvd.mul_right (Nat.gcd_dvd_left _ _) _
  have h2 : Nat.gcd p'.1 p'.2 ∣ p.1 * p'.2 := Dvd.dvd.mul_left (Nat.gcd_dvd_right _ _) _
  have h3 := Nat.dvd_sub h1 h2
  rw [IsUnimodular] at h
  rwa [h, Nat.add_sub_cancel_left] at h3

/-- **The mediant of a unimodular pair is coprime**: `d` dividing `m_1+m_2` and `n_1+n_2` divides
`m_2(n_1+n_2) - n_2(m_1+m_2) = m_2n_1 - m_1n_2 = 1`. This is why `HJO.Sweep.exists_slopeActions`'s
replication clause never mentions the family at a non-coprime index. -/
theorem IsUnimodular.coprime_mediant {p p' : ℕ × ℕ} (h : IsUnimodular p p') :
    Nat.Coprime (p.1 + p'.1) (p.2 + p'.2) := by
  refine Nat.dvd_one.1 ?_
  have h1 : Nat.gcd (p.1 + p'.1) (p.2 + p'.2) ∣ p'.1 * (p.2 + p'.2) :=
    Dvd.dvd.mul_left (Nat.gcd_dvd_right _ _) _
  have h2 : Nat.gcd (p.1 + p'.1) (p.2 + p'.2) ∣ p'.2 * (p.1 + p'.1) :=
    Dvd.dvd.mul_left (Nat.gcd_dvd_left _ _) _
  have h3 := Nat.dvd_sub h1 h2
  rw [show p'.1 * (p.2 + p'.2) = p'.1 * p.2 + p'.1 * p'.2 from by ring,
    show p'.2 * (p.1 + p'.1) = p.1 * p'.2 + p'.1 * p'.2 from by ring] at h3
  rw [IsUnimodular] at h
  rw [h] at h3
  rwa [show p.1 * p'.2 + 1 + p'.1 * p'.2 - (p.1 * p'.2 + p'.1 * p'.2) = 1 from by omega] at h3

end HJO.Mellit

namespace HJO.Sweep

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L} [Invertible q] [Invertible (q - 1)]
  {ρb : Dyck.Aq L q →ₐ[L] Module.End L (Vstar L)}
  {ρb' : Dyck.AqInv L q →ₐ[L] Module.End L (Vstar L)}

/-- **The conclusion of `HJO.Sweep.exists_slopeActions`, named.** Transcribed verbatim, so that
`HJO.Sweep.exists_slopeFamilySpec` — which is `HJO.Sweep.exists_slopeActions` restated — fails to
typecheck if this drifts from it. -/
def SlopeFamilySpec (q : L) [Invertible q] [Invertible (q - 1)] (u c : L)
    (ρb : Dyck.Aq L q →ₐ[L] Module.End L (Vstar L))
    (ρb' : Dyck.AqInv L q →ₐ[L] Module.End L (Vstar L))
    (R : ℕ × ℕ → (Dyck.Aq L q →ₐ[L] Module.End L (Vstar L)))
    (R' : ℕ × ℕ → (Dyck.AqInv L q →ₐ[L] Module.End L (Vstar L))) : Prop :=
  R (0, 1) = ρb ∧ R' (0, 1) = ρb' ∧ R (1, 0) = ρb ∧ R' (1, 0) = ρb'
    ∧ (∀ p : ℕ × ℕ, IsDpaAction q (R p))
    ∧ (∀ p : ℕ × ℕ, IsDpaAction ⅟q (R' p))
    ∧ (∀ p p' : ℕ × ℕ, Mellit.IsUnimodular p p' →
        IsIntertwinedPair q u (R p) (R' p')
          ∧ IsReplicated c (R p) (R' p') (R (p.1 + p'.1, p.2 + p'.2))
          ∧ IsReplicatedStar (R p) (R' p') (R' (p.1 + p'.1, p.2 + p'.2)))
    ∧ (∀ m n : ℕ, Nat.Coprime m n → (m, n) ≠ (0, 1) → (m, n) ≠ (1, 0) →
        ∃ p p' : ℕ × ℕ, Mellit.IsUnimodular p p' ∧ m = p.1 + p'.1 ∧ n = p.2 + p'.2
          ∧ IsIntertwinedPair q u (R p) (R' p')
          ∧ IsReplicated c (R p) (R' p') (R (m, n))
          ∧ IsReplicatedStar (R p) (R' p') (R' (m, n)))

omit [Algebra ℚ L] in
/-- **`HJO.Sweep.exists_slopeActions`, in the named form.** -/
theorem exists_slopeFamilySpec (h : IsIntertwinedPair q u ρb ρb') (c : L) :
    ∃ R R', SlopeFamilySpec q u c ρb ρb' R R' :=
  exists_slopeActions h c

/-! ### The family may be trivialised at every non-coprime index at once -/

open scoped Classical in
/-- **A family re-set to a fixed value at every non-coprime index.** -/
noncomputable def coprimeMod {X : Type*} (R : ℕ × ℕ → X) (x₀ : X) : ℕ × ℕ → X :=
  fun p => if Nat.Coprime p.1 p.2 then R p else x₀

theorem coprimeMod_of_coprime {X : Type*} (R : ℕ × ℕ → X) (x₀ : X) {p : ℕ × ℕ}
    (h : Nat.Coprime p.1 p.2) : coprimeMod R x₀ p = R p := by
  classical
  rw [coprimeMod]
  exact ite_eq_left_of_eq_true _ _ (eq_true h)

theorem coprimeMod_of_not_coprime {X : Type*} (R : ℕ × ℕ → X) (x₀ : X) {p : ℕ × ℕ}
    (h : ¬ Nat.Coprime p.1 p.2) : coprimeMod R x₀ p = x₀ := by
  classical
  rw [coprimeMod]
  exact ite_eq_right_of_eq_false _ _ (eq_false h)

omit [Algebra ℚ L] in
/-- **Every conclusion of `HJO.Sweep.exists_slopeActions` survives trivialising the family at every
non-coprime index.**

The only clause asserted at an arbitrary index is `IsDpaAction`, which the base pair satisfies
(being the family's own value at `(0,1)`). Every other clause names the family at the two axis
pairs, at the members of a unimodular pair, at their mediant, or at an explicitly coprime `(m,n)` —
and all of those are coprime (`HJO.Mellit.IsUnimodular.coprime_fst`, `_coprime_snd`,
`_coprime_mediant`).

So the value of a slope-action family at a non-coprime index is *unconstrained by that theorem*: no
consequence of `HJO.Sweep.exists_slopeActions` distinguishes it from the base pair. -/
theorem slopeFamilySpec_coprimeMod {c : L}
    {R : ℕ × ℕ → (Dyck.Aq L q →ₐ[L] Module.End L (Vstar L))}
    {R' : ℕ × ℕ → (Dyck.AqInv L q →ₐ[L] Module.End L (Vstar L))}
    (h : SlopeFamilySpec q u c ρb ρb' R R') :
    SlopeFamilySpec q u c ρb ρb' (coprimeMod R ρb) (coprimeMod R' ρb') := by
  obtain ⟨h01, h01', h10, h10', hA, hA', hUni, hCop⟩ := h
  have hc01 : Nat.Coprime ((0, 1) : ℕ × ℕ).1 ((0, 1) : ℕ × ℕ).2 := by decide
  have hc10 : Nat.Coprime ((1, 0) : ℕ × ℕ).1 ((1, 0) : ℕ × ℕ).2 := by decide
  refine ⟨by rw [coprimeMod_of_coprime _ _ hc01, h01],
    by rw [coprimeMod_of_coprime _ _ hc01, h01'],
    by rw [coprimeMod_of_coprime _ _ hc10, h10],
    by rw [coprimeMod_of_coprime _ _ hc10, h10'], ?_, ?_, ?_, ?_⟩
  · intro p
    by_cases hp : Nat.Coprime p.1 p.2
    · rw [coprimeMod_of_coprime _ _ hp]; exact hA p
    · rw [coprimeMod_of_not_coprime _ _ hp, ← h01]; exact hA _
  · intro p
    by_cases hp : Nat.Coprime p.1 p.2
    · rw [coprimeMod_of_coprime _ _ hp]; exact hA' p
    · rw [coprimeMod_of_not_coprime _ _ hp, ← h01']; exact hA' _
  · intro p p' hu
    rw [coprimeMod_of_coprime _ _ hu.coprime_fst, coprimeMod_of_coprime _ _ hu.coprime_snd,
      coprimeMod_of_coprime R ρb (p := (p.1 + p'.1, p.2 + p'.2)) hu.coprime_mediant,
      coprimeMod_of_coprime R' ρb' (p := (p.1 + p'.1, p.2 + p'.2)) hu.coprime_mediant]
    exact hUni p p' hu
  · intro m n hmn h1 h2
    obtain ⟨p, p', hu, hm, hn, hi, hr, hrs⟩ := hCop m n hmn h1 h2
    refine ⟨p, p', hu, hm, hn, ?_, ?_, ?_⟩
    · rw [coprimeMod_of_coprime _ _ hu.coprime_fst, coprimeMod_of_coprime _ _ hu.coprime_snd]
      exact hi
    · rw [coprimeMod_of_coprime _ _ hu.coprime_fst, coprimeMod_of_coprime _ _ hu.coprime_snd,
        coprimeMod_of_coprime R ρb (p := (m, n)) hmn]
      exact hr
    · rw [coprimeMod_of_coprime _ _ hu.coprime_fst, coprimeMod_of_coprime _ _ hu.coprime_snd,
        coprimeMod_of_coprime R' ρb' (p := (m, n)) hmn]
      exact hrs

omit [Algebra ℚ L] in
/-- **`HJO.Sweep.exists_slopeActions` has a witness that is the base pair at every non-coprime
index.** -/
theorem exists_slopeFamilySpec_base_of_not_coprime (h : IsIntertwinedPair q u ρb ρb') (c : L) :
    ∃ R R', SlopeFamilySpec q u c ρb ρb' R R' ∧
      ∀ m n : ℕ, ¬ Nat.Coprime m n → R (m, n) = ρb ∧ R' (m, n) = ρb' := by
  obtain ⟨R, R', hspec⟩ := exists_slopeFamilySpec h c
  exact ⟨coprimeMod R ρb, coprimeMod R' ρb', slopeFamilySpec_coprimeMod hspec,
    fun m n hmn => ⟨coprimeMod_of_not_coprime R ρb (p := (m, n)) hmn,
      coprimeMod_of_not_coprime R' ρb' (p := (m, n)) hmn⟩⟩

/-! ### Hence no bridge at the index of the slope -/

/-- **Any bridge from the slope-action family to `Q` at a non-coprime index collapses `Q`.**

Suppose a map `F` from an action of `𝔸_q` on `V_*` to an endomorphism of `Λ` satisfies
`F(ρ_{m,n}) = Q_{m,n}` at every non-coprime `(m,n)`, for every family `ρ` that
`HJO.Sweep.exists_slopeActions` produces. Then `Q_{m,n} = Q_{m',n'}` for **every** pair of
non-coprime slopes: both sides are `F(ρ^♭)`, by
`HJO.Sweep.exists_slopeFamilySpec_base_of_not_coprime`.

This is the precise sense in which the replicated actions cannot supply the doubled slope. The
family's index is not the carrier of the collinear information — grading of `V_*` is — so a bridge
written at the index `(ka, kb)` reads the base pair, which mentions neither `a` nor `b`. -/
theorem qop_eq_of_slopeActions_bridge (h : IsIntertwinedPair q u ρb ρb') (c : L)
    (F : (Dyck.Aq L q →ₐ[L] Module.End L (Vstar L)) → Module.End L (Sym.Lambda L))
    (hF : ∀ (R : ℕ × ℕ → (Dyck.Aq L q →ₐ[L] Module.End L (Vstar L)))
        (R' : ℕ × ℕ → (Dyck.AqInv L q →ₐ[L] Module.End L (Vstar L))),
        SlopeFamilySpec q u c ρb ρb' R R' →
        ∀ m n : ℕ, ¬ Nat.Coprime m n → F (R (m, n)) = Sym.Qop q u m n)
    {m n m' n' : ℕ} (hmn : ¬ Nat.Coprime m n) (hmn' : ¬ Nat.Coprime m' n') :
    Sym.Qop q u m n = Sym.Qop q u m' n' := by
  obtain ⟨R, R', hspec, hbase⟩ := exists_slopeFamilySpec_base_of_not_coprime h c
  rw [← hF R R' hspec m n hmn, ← hF R R' hspec m' n' hmn', (hbase m n hmn).1,
    (hbase m' n' hmn').1]

/-- **A bridge forces the doubled slope to kill the vacuum, on every ray.**

`HJO.Sweep.qop_eq_of_slopeActions_bridge` applied at `(2a, 2b)` and `(3a, 3b)` — both non-coprime,
for every `a` and every `b ≥ 1` — makes the two collinear operators equal, and
`HJO.Sym.qop_collinear_apply_one_eq_zero_of_eq` then forces `Q_{2a,2b}(1) = 0`.

This is the form of the refutation that applies to a bridge written only along one fixed ray
`(ka, kb)`, `k ≥ 2`, at a coprime `(a,b)` — the shape the `hlhs` leg would want,
`HJO.Sym.IsSlopeHom` quantifying over `k` at a fixed slope. It is false already at `(a,b) = (1,1)`,
where `Q_{2,2}(1) = e_1^2 + (q+u)e_2 ≠ 0` (`HJO.Sym.qop_two_two_apply_one`). -/
theorem qop_collinear_apply_one_eq_zero_of_slopeActions_bridge
    (h : IsIntertwinedPair q u ρb ρb') (c : L)
    (F : (Dyck.Aq L q →ₐ[L] Module.End L (Vstar L)) → Module.End L (Sym.Lambda L))
    (hF : ∀ (R : ℕ × ℕ → (Dyck.Aq L q →ₐ[L] Module.End L (Vstar L)))
        (R' : ℕ × ℕ → (Dyck.AqInv L q →ₐ[L] Module.End L (Vstar L))),
        SlopeFamilySpec q u c ρb ρb' R R' →
        ∀ m n : ℕ, ¬ Nat.Coprime m n → F (R (m, n)) = Sym.Qop q u m n)
    {a b : ℕ} (hb : 0 < b) :
    Sym.Qop q u (a * 2) (b * 2) (1 : Sym.Lambda L) = 0 :=
  Sym.qop_collinear_apply_one_eq_zero_of_eq hb
    (qop_eq_of_slopeActions_bridge h c F hF (Sym.not_coprime_mul_right (le_refl 2))
      (Sym.not_coprime_mul_right (by omega)))

/-- **No such bridge exists.** `Q_{2,2} ≠ Q_{2,4}` (`HJO.Sym.qop_two_two_ne_qop_two_four`), and both
slopes are non-coprime, so the collapse of `HJO.Sweep.qop_eq_of_slopeActions_bridge` is absurd.

**What this establishes.** A hypothesised lemma of the form "`HJO.Sweep.exists_slopeActions` gives
`Q_{ka,kb}` from `ρ_{ka,kb}`" is not merely unproved: it is false, uniformly in the parameters, for
every candidate `F` at once. Any genuine use of the replicated actions on the `hlhs` leg must read
the *grading* of `V_*`, not the index of the family — and `HJO.Sym.qop_collinear_eq_bracket` shows
it need not read them at all, the collinear slope being a commutator of two coprime ones. -/
theorem not_slopeActions_bridge (hM : (1 - q) * (1 - u) ≠ 0)
    (h : IsIntertwinedPair q u ρb ρb') (c : L)
    (F : (Dyck.Aq L q →ₐ[L] Module.End L (Vstar L)) → Module.End L (Sym.Lambda L)) :
    ¬ (∀ (R : ℕ × ℕ → (Dyck.Aq L q →ₐ[L] Module.End L (Vstar L)))
        (R' : ℕ × ℕ → (Dyck.AqInv L q →ₐ[L] Module.End L (Vstar L))),
        SlopeFamilySpec q u c ρb ρb' R R' →
        ∀ m n : ℕ, ¬ Nat.Coprime m n → F (R (m, n)) = Sym.Qop q u m n) := fun hF =>
  Sym.qop_two_two_ne_qop_two_four hM
    (qop_eq_of_slopeActions_bridge h c F hF (by decide) (by decide))

end HJO.Sweep

end
