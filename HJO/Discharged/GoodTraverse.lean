/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Defs
public import HJO.Series.FiniteCanonical
public import HJO.GoodTraverse.Basic
public meta import HJO.Attr

/-! # The good-traverse factorisation is not an assumption

`HJO.External.GoodTraverse` states that on the monotonicity cone with `n_f ≤ N` the generalised
Gaussian multinomial factors over the gaps, the factor at `g` being the ordinary Gaussian binomial
in the flag values. It is proved here from the results in `HJO/GoodTraverse/`.

The last of those is `HJO.GoodTraverse.reduced_traverse`, which equates

`(q)_N / (q)_{N - n_f} ∏_g (q)_{n_g - n_{g-a-b}} / (q)_{n_g - n_{g-b}}`

with `∏_g (q)_{n̂_{g+b} - n_{g-a}} / (q)_{n̂_{g+b} - n_g}` --- the assumption's right-hand side with
the middle factor `1 / (q)_{n_g - n_{g-a}}` removed. Restoring that factor to both sides is a
regrouping of the two products, so all that remains is to recognise the left-hand side as the
multinomial. `HJO.FiniteCanonical.multinomial_eq` puts the guarded integer multinomial into its
natural-vector form, which is legitimate exactly under the assumption's own hypothesis `n_f ≤ N`,
and there the gap product is the product of the three factors of `HJO.multiplicand` with their
guards discharged: on the cone every difference `n_g - n_{g-s}` at a semigroup element `s` is
nonnegative, by `HJO.GoodTraverse.extendNat_sub_le`, so each guarded integer index is the
truncated natural one.
-/

@[expose] public section

open Finset NumericalSemigroup PowerSeries
open scoped QTheory

namespace HJO.GoodTraverseDischarged

open HJO.GoodTraverse

/-- The gap product of the multinomial, with the guards of `HJO.multiplicand` discharged: on the
monotonicity cone the three differences at `a + b`, `a` and `b` are nonnegative, so each guarded
integer `q`-factorial index is the truncated natural one. -/
theorem multiplicand_eq {a b : ℕ} (hco : a.Coprime b) {n : (finspan {a, b}).gaps → ℕ}
    (hn : (fun g => (n g : ℤ)) ∈ HJO.cone a b) (g : (finspan {a, b}).gaps) :
    HJO.multiplicand ((finspan {a, b}).gaps) a b (fun j => (n j : ℤ)) g
      = ((X; X)_(n g - HJO.extendNat n ((g : ℕ) - (a + b))) : ℤ⟦X⟧) *
          invOfUnit (X; X)_(n g - HJO.extendNat n ((g : ℕ) - a)) 1 *
          invOfUnit (X; X)_(n g - HJO.extendNat n ((g : ℕ) - b)) 1 := by
  have hgcd := gcd_pair_eq_one hco
  have hsub : ∀ s : ℕ, s ∈ finspan {a, b} → HJO.extendNat n ((g : ℕ) - s) ≤ n g := by
    intro s hs
    have h := extendNat_sub_le hco hn g.2 hs
    rwa [← HJO.extendNat_subtype n g] at h
  have h1 := hsub (a + b) (add_mem_finspan (Gaps.mem_finspan_left hgcd)
    (Gaps.mem_finspan_right hgcd))
  have h2 := hsub a (Gaps.mem_finspan_left hgcd)
  have h3 := hsub b (Gaps.mem_finspan_right hgcd)
  rw [HJO.multiplicand, HJO.extendedSelfQPochhammer, HJO.extendedSelfQPochhammerInv,
    HJO.extendedSelfQPochhammerInv]
  simp only [extend_natCast]
  rw [ite_eq_left (by omega : (0 : ℤ) ≤ (n g : ℤ) - (HJO.extendNat n ((g : ℕ) - (a + b)) : ℤ)),
    ite_eq_left (by omega : (0 : ℤ) ≤ (n g : ℤ) - (HJO.extendNat n ((g : ℕ) - a) : ℤ)),
    ite_eq_left (by omega : (0 : ℤ) ≤ (n g : ℤ) - (HJO.extendNat n ((g : ℕ) - b) : ℤ)),
    show ((n g : ℤ) - (HJO.extendNat n ((g : ℕ) - (a + b)) : ℤ)).toNat
        = n g - HJO.extendNat n ((g : ℕ) - (a + b)) from by omega,
    show ((n g : ℤ) - (HJO.extendNat n ((g : ℕ) - a) : ℤ)).toNat
        = n g - HJO.extendNat n ((g : ℕ) - a) from by omega,
    show ((n g : ℤ) - (HJO.extendNat n ((g : ℕ) - b) : ℤ)).toNat
        = n g - HJO.extendNat n ((g : ℕ) - b) from by omega]

/-- **`GoodTraverse` is not an assumption.** The generalised Gaussian multinomial factors over the
gaps as the assumption states, at every coprime pair with `1 < a < b`, every rank `N` and every
cone point with `n_f ≤ N`. -/
theorem goodTraverse : HJO.External.GoodTraverse := by
  intro a b hco ha hab N n hn hfN
  -- The assumption's right-hand side is the endgame's, with the middle factor restored.
  have hsplit : ∏ g : (finspan {a, b}).gaps,
        (((X; X)_(Gaps.flag a b N n (((g : ℕ) : ℤ) + b) -
            HJO.extendNat n ((g : ℕ) - a)) : ℤ⟦X⟧) *
          invOfUnit (X; X)_(n g - HJO.extendNat n ((g : ℕ) - a)) 1 *
          invOfUnit (X; X)_(Gaps.flag a b N n (((g : ℕ) : ℤ) + b) - n g) 1)
      = (∏ g : (finspan {a, b}).gaps,
            (((X; X)_(Gaps.flag a b N n (((g : ℕ) : ℤ) + b) -
                HJO.extendNat n ((g : ℕ) - a)) : ℤ⟦X⟧) *
              invOfUnit (X; X)_(Gaps.flag a b N n (((g : ℕ) : ℤ) + b) - n g) 1)) *
          ∏ g : (finspan {a, b}).gaps,
            invOfUnit ((X; X)_(n g - HJO.extendNat n ((g : ℕ) - a)) : ℤ⟦X⟧) 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun g _ => by ring
  rw [hsplit, ← reduced_traverse hco ha hab N n,
    show (fun g => (n g : ℤ)) = FiniteCanonical.toInt n from rfl,
    FiniteCanonical.multinomial_eq N n hfN, HJO.Finite.gaussianMultinomial,
    ← FiniteCanonical.frobeniusGap_eq,
    Finset.prod_congr rfl fun g (_ : g ∈ Finset.univ) => multiplicand_eq hco hn g]
  -- What is left is the same regrouping, read on the other side.
  have hcomb : (∏ g : (finspan {a, b}).gaps,
        (((X; X)_(n g - HJO.extendNat n ((g : ℕ) - (a + b))) : ℤ⟦X⟧) *
          invOfUnit (X; X)_(n g - HJO.extendNat n ((g : ℕ) - b)) 1)) *
      (∏ g : (finspan {a, b}).gaps,
        invOfUnit ((X; X)_(n g - HJO.extendNat n ((g : ℕ) - a)) : ℤ⟦X⟧) 1)
      = ∏ g : (finspan {a, b}).gaps,
        (((X; X)_(n g - HJO.extendNat n ((g : ℕ) - (a + b))) : ℤ⟦X⟧) *
          invOfUnit (X; X)_(n g - HJO.extendNat n ((g : ℕ) - a)) 1 *
          invOfUnit (X; X)_(n g - HJO.extendNat n ((g : ℕ) - b)) 1) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun g _ => by ring
  rw [← hcomb]
  ring

end HJO.GoodTraverseDischarged
