/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepModule
public meta import HJO.Attr

/-! # The twisting homomorphism `tw_k : Λ → V_k`

The Carlsson--Mellit layer needs the substitution of the virtual alphabet `(q-1)(y_1 + ⋯ + y_k)`
into a symmetric function: the `K`-algebra homomorphism `tw_k : Λ → V_k` with

`tw_k(p_r) = p_r + (q^r - 1)(y_1^r + ⋯ + y_k^r)`

for every `r ≥ 1`. On the power sums the virtual alphabet contributes `p_r[(q-1)y] = (q^r-1)y^r` at
each auxiliary variable, which is the formula above; so `tw_k(F) = F[X + (q-1)(y_1 + ⋯ + y_k)]`, as
stated.

## Main definitions

* `HJO.Sweep.twist`: `tw_k`, as a homomorphism into the total space `V_* = Λ[y_1, y_2, …]`.
* `HJO.Sweep.twistToPiece`: the same map with its codomain corestricted to `V_k`.

## Main results

* `HJO.Sweep.twist_powerSum`: the defining formula, for every `r ≥ 1`.
* `HJO.Sweep.twist_mem_piece`: the image lies in `V_k`, which is what makes the corestriction exist.

## Implementation notes

**It is not `θ_k`.** `HJO.Sweep.theta` is the endomorphism of `V_k`
sending `p_r` to `(q^r - 1)p_r`: a different domain and a different formula. Both are often written
`θ_k` with no disambiguation; the roman name here is the disambiguation, and the two maps are
both used downstream.

**The primary definition lands in the total space, and the corestriction is a corollary.** This is
the one-total-space convention of `HJO.Shuffle.SweepModule`: `V_k` is the subalgebra
`HJO.Sweep.piece L k` of `V_* = Λ[y_1, y_2, …]`, so a map *into* `V_k` is a map into `V_*` together
with a range statement. Stating it the other way round would put a coercion in every rewrite of the
defining formula, and the formula is what every consumer uses.

**The scalar is written `C (C (q^r - 1))` rather than a scalar action.** An `L`-smul would need the
scalar tower at every membership step of `twist_mem_piece`; as a product of two `algebraMap` images
the membership is `Subalgebra.mul_mem` and nothing else. This is also the shape
`HJO.Sym.plethShiftW_X` uses for the same kind of formula.

## References

This file defines `HJO.Sweep.twist`, used for the Dyck path algebra and its involution.
-/

@[expose] public section

namespace HJO.Sweep

section Twist

variable {L : Type*} [CommRing L]

/-- **The twisting homomorphism** `tw_k : Λ → V_k`: the `L`-algebra homomorphism sending the power
sum `p_r` to `p_r + (q^r - 1)(y_1^r + ⋯ + y_k^r)`, that is, `F ↦ F[X + (q-1)(y_1 + ⋯ + y_k)]`. It
is stated into the total space `V_*`; `twist_mem_piece` places its image in `V_k` and
`twistToPiece` is the corestriction. -/
@[hjo "def_cm_twist_hom"]
noncomputable def twist (L : Type*) [CommRing L] (q : L) (k : ℕ) : Sym.Lambda L →ₐ[L] Total L :=
  MvPolynomial.aeval fun j =>
    MvPolynomial.C (Sym.powerSum L (j + 1)) +
      MvPolynomial.C (MvPolynomial.C (q ^ (j + 1) - 1)) *
        ∑ i ∈ Finset.Icc 1 k, (auxVar i : Total L) ^ (j + 1)

/-- The value of `tw_k` on the generator `j` of `Λ`, which stands for `p_{j+1}`. -/
theorem twist_X (q : L) (k j : ℕ) :
    twist L q k (MvPolynomial.X j) =
      MvPolynomial.C (Sym.powerSum L (j + 1)) +
        MvPolynomial.C (MvPolynomial.C (q ^ (j + 1) - 1)) *
          ∑ i ∈ Finset.Icc 1 k, (auxVar i : Total L) ^ (j + 1) := by
  rw [twist, MvPolynomial.aeval_X]

/-- **The defining property of `tw_k`**: `tw_k(p_r) = p_r + (q^r - 1)(y_1^r + ⋯ + y_k^r)` for every
`r ≥ 1`, with nothing truncated. -/
@[hjo "def_cm_twist_hom"]
theorem twist_powerSum (q : L) (k : ℕ) {r : ℕ} (hr : 0 < r) :
    twist L q k (Sym.powerSum L r) =
      MvPolynomial.C (Sym.powerSum L r) +
        MvPolynomial.C (MvPolynomial.C (q ^ r - 1)) *
          ∑ i ∈ Finset.Icc 1 k, (auxVar i : Total L) ^ r := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  have hX : Sym.powerSum L (m + 1) = MvPolynomial.X m := by
    rw [Sym.powerSum, Nat.add_sub_cancel]
  rw [hX, twist_X, hX]

/-- `tw_k` of a constant is that constant. -/
@[simp]
theorem twist_C (q : L) (k : ℕ) (a : L) :
    twist L q k (MvPolynomial.C a) = MvPolynomial.C (MvPolynomial.C a) := by
  rw [twist, MvPolynomial.aeval_C]
  rfl

/-- **The image of `tw_k` lies in `V_k`**: only the auxiliary variables `y_1, …, y_k` occur, so the
stated codomain is correct. -/
@[hjo "def_cm_twist_hom"]
theorem twist_mem_piece (q : L) (k : ℕ) (f : Sym.Lambda L) : twist L q k f ∈ piece L k := by
  induction f using MvPolynomial.induction_on with
  | C a => rw [twist_C]; exact Subalgebra.algebraMap_mem _ _
  | add p r hp hr => rw [map_add]; exact Subalgebra.add_mem _ hp hr
  | mul_X p n hp =>
    rw [map_mul, twist_X]
    refine Subalgebra.mul_mem _ hp (Subalgebra.add_mem _ (Subalgebra.algebraMap_mem _ _)
      (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (Subalgebra.sum_mem _ ?_)))
    intro i hi
    rw [Finset.mem_Icc] at hi
    exact Subalgebra.pow_mem _ (auxVar_mem_piece hi.1 hi.2) _

/-- **`tw_k` as a homomorphism `Λ → V_k`**, with the codomain stated in its definition. -/
@[hjo "def_cm_twist_hom"]
noncomputable def twistToPiece (L : Type*) [CommRing L] (q : L) (k : ℕ) :
    Sym.Lambda L →ₐ[L] ((piece L k).restrictScalars L) :=
  (twist L q k).codRestrict ((piece L k).restrictScalars L) (twist_mem_piece q k)

@[simp]
theorem coe_twistToPiece (q : L) (k : ℕ) (f : Sym.Lambda L) :
    (twistToPiece L q k f : Total L) = twist L q k f := rfl

end Twist

end HJO.Sweep
