/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import QSeriesLib.NumberTheory.QTheory.Basic
public import QSeriesLib.RingTheory.PowerSeries.Inverse
public import HJO.Defs
public import HJO.Series.GapPoset

/-! # The `ℕ`-valued and `ℤ`-valued presentations of the HJO polynomial agree

`HJO.Finite.poly` sums over `ℕ`-valued gap vectors, `HJO.Gaps.finiteSeries` over `ℤ`-valued
ones. Casting is a bijection between the two index sets, because the monotonicity cone forces
every coordinate to be nonnegative, so the two polynomials are equal unconditionally.

The two multinomials, on the other hand, genuinely differ. `HJO.Finite.gaussianMultinomial`
divides by `(q)_{N - n_f}` with *truncated* natural subtraction and no guard, so off the range
`n_f ≤ N` its middle factor is the inverse of `(q)_0 = 1`, a unit; `HJO.Gaps.multinomial`
guards the integer difference and is identically `0` there. The functions agree on `n_f ≤ N`
and need not agree outside that range. Equality can still hold outside it when the common gap
product vanishes. The index set of `poly` cuts out the range `n_f ≤ N`, which is why `poly_eq`
needs no hypothesis while `multinomial_eq` requires that bound for its general equality.
-/

@[expose] public section

open Finset NumericalSemigroup PowerSeries
open scoped QTheory PowerSeries.DiscreteTopology

local notation "gaps(" a ", " b ")" => NumericalSemigroup.gaps (NumericalSemigroup.finspan {a, b})

namespace HJO.FiniteCanonical

/-! ### Casting a natural gap vector to an integer one -/

/-- The coordinatewise cast of a natural gap vector to an integer one. -/
def toInt {a b : ℕ} (n : gaps(a, b) → ℕ) : gaps(a, b) → ℤ := fun i => (n i : ℤ)

/-- The coordinatewise cast of a natural gap vector to an integer one is injective. -/
theorem toInt_injective {a b : ℕ} : Function.Injective (toInt (a := a) (b := b)) := fun _ _ h =>
  funext fun i => Nat.cast_injective (congrFun h i)

/-- Casting commutes with the zero-extension off the gap set. -/
theorem extend_toInt {a b : ℕ} (n : gaps(a, b) → ℕ) (i : ℕ) :
    HJO.extend (toInt n) i = (HJO.extendNat n i : ℤ) := by
  rw [HJO.extend, HJO.extendNat]; split <;> simp [toInt]

/-- The Frobenius gap of `⟨a, b⟩` is `a * b - a - b`, on the nose. -/
theorem frobeniusGap_eq {a b : ℕ} : Gaps.frobeniusGap a b = a * b - a - b := rfl

/-! ### The multinomials agree on `n_f ≤ N`, but can differ outside it -/

/-- On the range `n_f ≤ N` the guarded integer multinomial and the truncated natural one agree. -/
theorem multinomial_eq {a b : ℕ} (N : ℕ) (n : gaps(a, b) → ℕ)
    (h : HJO.extendNat n (a * b - a - b) ≤ N) :
    Gaps.multinomial a b N (toInt n) = HJO.Finite.gaussianMultinomial a b N n := by
  have htn : ((N : ℤ) - (HJO.extendNat n (a * b - a - b) : ℤ)).toNat
      = N - HJO.extendNat n (a * b - a - b) := by omega
  rw [Gaps.multinomial, HJO.Finite.gaussianMultinomial,
    HJO.extendedSelfQPochhammerInv, frobeniusGap_eq, extend_toInt, ite_eq_left (by omega), htn]
  rfl

/-- Off that range the guarded multinomial is identically zero: the hypothesis of
`multinomial_eq` cannot be dropped. -/
theorem multinomial_eq_zero_of_lt {a b : ℕ} (N : ℕ) (n : gaps(a, b) → ℕ)
    (h : N < HJO.extendNat n (a * b - a - b)) : Gaps.multinomial a b N (toInt n) = 0 := by
  rw [Gaps.multinomial, frobeniusGap_eq, extend_toInt, HJO.extendedSelfQPochhammerInv,
    ite_eq_right (by omega)]
  ring

/-- When `N < m`, truncated subtraction makes the inverse Pochhammer factor the inverse of
`(q)_0 = 1`, with constant coefficient `1`. For `m = n_f`, this contrasts with the zero
middle factor of the guarded multinomial. It does not imply that the entire natural
multinomial is nonzero: the common gap product can vanish. -/
theorem constantCoeff_invOfUnit_selfQPochhammer_sub {N m : ℕ} (h : N < m) :
    constantCoeff (invOfUnit ((X; X)_(N - m) : ℤ⟦X⟧) 1) = 1 := by
  rw [Nat.sub_eq_zero_of_le h.le]; simp

/-! ### The polynomials, which agree unconditionally -/

/-- The two presentations of the finite HJO polynomial are equal, with no hypothesis: the index
set of `HJO.Finite.poly` is carried bijectively onto that of `HJO.Gaps.finiteSeries` by
`toInt`, and the two multinomials agree on it. -/
theorem poly_eq (a b N : ℕ) : HJO.Finite.poly a b N = Gaps.finiteSeries a b N := by
  have himg : toInt (a := a) (b := b) ''
        {n | toInt n ∈ HJO.cone a b ∧ HJO.extendNat n (a * b - a - b) ≤ N}
      = {n ∈ HJO.cone a b | HJO.extend n (Gaps.frobeniusGap a b) ≤ (N : ℤ)} := by
    ext m
    constructor
    · rintro ⟨n, ⟨hcone, hfr⟩, rfl⟩
      exact ⟨hcone, by rw [frobeniusGap_eq, extend_toInt]; exact_mod_cast hfr⟩
    · rintro ⟨hcone, hfr⟩
      have hup : toInt (fun i => (m i).toNat) = m := by
        funext i; simp only [toInt]; have := hcone.1 i; omega
      refine ⟨fun i => (m i).toNat, ⟨by rw [hup]; exact hcone, ?_⟩, hup⟩
      have h2 := extend_toInt (a := a) (b := b) (fun i => (m i).toNat) (a * b - a - b)
      rw [hup] at h2
      rw [frobeniusGap_eq] at hfr
      omega
  rw [Gaps.finiteSeries, ← himg, finsum_mem_image toInt_injective.injOn, HJO.Finite.poly]
  refine finsum_mem_congr (Set.ext fun n => Iff.rfl) fun n hn => ?_
  rw [multinomial_eq N n hn.2]
  rfl

/-- The index set of `HJO.Finite.poly` is finite, so its `finsum` is an honest `Finset` sum. A
`finsum` is zero by definition on infinite support, so without this `poly` says nothing.

This is the `ℕ`-valued reading of `HJO.GapPoset.finite_coneNat_frobeniusGap_le`; the two
statements differ only by `HJO.Gaps.frobeniusGap a b = a * b - a - b`, which is `rfl`.

Deliberately NOT named `HJO.Finite.finite_index`, which is the name the challenge file gives this
statement: that name is the *contract*, and `Solution/Basic.lean` is what must carry it. A library
declaration under the contract name collides with the solution's and there is then nothing for the
comparator to compare. -/
theorem finite_index (a b N : ℕ) (hco : Nat.Coprime a b) (ha : 1 < a) (hab : a < b) :
    {n : gaps(a, b) → ℕ |
      (fun i => (n i : ℤ)) ∈ HJO.cone a b ∧ HJO.extendNat n (a * b - a - b) ≤ N}.Finite :=
  HJO.GapPoset.finite_coneNat_frobeniusGap_le a b N hco ha hab

end HJO.FiniteCanonical

end
