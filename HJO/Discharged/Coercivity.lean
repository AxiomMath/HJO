/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Coercivity.Basic
public import HJO.Defs
public meta import HJO.Attr

/-! # Huang's coercivity bound is not an assumption

`HJO.Literature.HuangCoercivity` states the effective positive definiteness of the quadratic form
on the monotonicity cone: `n_g^2 ≤ |G| Q(𝐧)` at every gap `g`. It is proved here.

The route is as follows. `HJO.Coercivity.sum_layerMult_sq_le_q` bounds the quadratic form
below by the sum of the squared layer multiplicities, and is itself unconditional -- the rank-one
identity it rests on is `HJO.ExternalDischarged.rankOneDinv` and the nonnegativity of the polarised
form is `HJO.CrossDinv.bilin_nonneg`. Over the subsets that occur as a layer the multiplicities sum
to the Frobenius coordinate, by `HJO.Coercivity.sum_layerMult`, and there are at most `|G|` of them,
by `HJO.Coercivity.card_filter_one_le_layerMult_le`; Cauchy-Schwarz in the form
`HJO.Coercivity.sq_sum_le_card_mul_sum_sq_int` then gives `n_f^2 ≤ |G| ∑_E m_E(𝐧)^2`. Since the
Frobenius coordinate dominates every coordinate on the cone, and every coordinate is nonnegative
there, `n_g^2 ≤ n_f^2` closes it.
-/

@[expose] public section

open Finset NumericalSemigroup

namespace HJO.CoercivityDischarged

open HJO.Coercivity

/-- The subsets of the gap type that occur as a layer of `𝐧`, i.e. those with a positive
multiplicity. Off this set both the multiplicities and their squares vanish. -/
private noncomputable def occurring {a b : ℕ} (n : (finspan {a, b}).gaps → ℤ) :
    Finset (Finset (finspan {a, b}).gaps) :=
  {E : Finset (finspan {a, b}).gaps | 1 ≤ Defs.layerMult a b n E}

/-- A sum of multiplicities over all subsets is the sum over the occurring ones: a subset that is
not a layer has multiplicity zero, and so contributes zero to any sum of a function killing it. -/
private theorem sum_occurring {a b : ℕ} (n : (finspan {a, b}).gaps → ℤ) (f : ℕ → ℤ)
    (hf : f 0 = 0) :
    ∑ E ∈ occurring n, f (Defs.layerMult a b n E)
      = ∑ E : Finset (finspan {a, b}).gaps, f (Defs.layerMult a b n E) := by
  refine Finset.sum_subset (Finset.filter_subset _ _) fun E _ hE => ?_
  rw [show Defs.layerMult a b n E = 0 from by
        simpa only [occurring, Finset.mem_filter, Finset.mem_univ, true_and, Nat.one_le_iff_ne_zero,
          not_not] using hE,
    hf]

/-- **Coercivity at the Frobenius gap.** `n_f^2 ≤ |G| Q(𝐧)` on the monotonicity cone: the
multiplicities of the occurring layers sum to `n_f`, they number at most `|G|`, and Cauchy-Schwarz
bounds the square of their sum by `|G|` times the sum of their squares, which
`HJO.Coercivity.sum_layerMult_sq_le_q` bounds by the quadratic form. -/
theorem sq_extend_frobeniusGap_le {a b : ℕ} (hco : a.Coprime b) (ha : 1 < a) (hab : a < b)
    {n : (finspan {a, b}).gaps → ℤ} (hn : n ∈ HJO.cone a b) :
    HJO.extend n (Gaps.frobeniusGap a b) ^ 2
      ≤ ((finspan {a, b}).gaps.card : ℤ) * HJO.Q a b n := by
  set G : ℤ := ((finspan {a, b}).gaps.card : ℤ) with hG
  set S : ℤ := ∑ E : Finset (finspan {a, b}).gaps, (Defs.layerMult a b n E : ℤ) ^ 2 with hS
  have hG0 : 0 ≤ G := by positivity
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun E _ => sq_nonneg _
  -- Cauchy-Schwarz over the occurring layers.
  have hcs := sq_sum_le_card_mul_sum_sq_int (occurring n)
    fun E => (Defs.layerMult a b n E : ℤ)
  rw [sum_occurring n (fun k => (k : ℤ)) (by simp),
    sum_occurring n (fun k => (k : ℤ) ^ 2) (by simp), sum_layerMult hn, ← hS] at hcs
  -- The occurring layers number at most `|G|`.
  have hcard : ((occurring n).card : ℤ) ≤ G :=
    Int.ofNat_le.mpr (card_filter_one_le_layerMult_le hco ha hab n)
  calc HJO.extend n (Gaps.frobeniusGap a b) ^ 2
      ≤ ((occurring n).card : ℤ) * S := hcs
    _ ≤ G * S := mul_le_mul_of_nonneg_right hcard hS0
    _ ≤ G * HJO.Q a b n :=
        mul_le_mul_of_nonneg_left (sum_layerMult_sq_le_q hco ha hab hn) hG0

/-- **`HuangCoercivity` is not an assumption.** The coercivity bound `n_g^2 ≤ |G| Q(𝐧)` holds at
every gap: on the monotonicity cone `0 ≤ n_g ≤ n_f` by `HJO.GoodTraverse.extend_le_frobenius`, so
the bound at the Frobenius gap implies the bound everywhere. -/
theorem huangCoercivity : HJO.Literature.HuangCoercivity := by
  intro a b hco ha hab n hn i
  have hnf : n i ≤ HJO.extend n (Gaps.frobeniusGap a b) := by
    have h1 := GoodTraverse.extend_le_frobenius hco ha hab hn i.2
    rwa [← HJO.extend_subtype n i] at h1
  have h0 : 0 ≤ n i := hn.1 i
  refine le_trans ?_ (sq_extend_frobeniusGap_le hco ha hab hn)
  exact pow_le_pow_left₀ h0 hnf 2

end HJO.CoercivityDischarged
