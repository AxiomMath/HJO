/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CMStructure.StarEasy
public import HJO.Shuffle.CMRaising
public meta import HJO.Attr

/-! # The raising operator on the vacuum

`HJO.Sweep.dplus_dplusIter`: for every `k ≥ 0`, `d_+^{k+1}(1) = -y_1 d^*_+ d_+^{k}(1)` in `V_{k+1}`,
with `d_+` the raising operator of `HJO.Sweep.dplus` and `d^*_+` the starred one
of `HJO.Sweep.dplusStar`. The tower `d_+^{k}(1)` is `HJO.Sweep.dplusIter`.

## The content is a closed form, not a quotient computation

A natural proof of this identity routes through the structure theorem
`HJO.Standing.dpaStructure_param`: it reads the identity off the second family of generators of the
submodule `𝓘` of
`HJO.Dyck.Tilde.Atilde.mellitKernel`, "evaluated on the vacuum", those generators being annihilated
in `V_*` by `HJO.Sweep.dminus_dplusStar_map_one` and generating the whole kernel by
`HJO.Standing.dpaStructure_param`.

That route does not prove this statement, and none of those three results is needed for it. Two
things go wrong with it.

* The generator family is `(d_+ + q^{k}y_1d^*_+)d^{*k}_+𝟏_0`, so what it gives on the vacuum carries
  the factor `q^{k}`: `HJO.Sweep.dminus_dplusStar_map_one` states exactly
  `d^♭_+(1) + q^{k}y_1d^*_+(1) = 0` in `V_{k+1}`, with `1` the *unit* of `V_k`. The statement here
  carries no `q^{k}`.
* The two are not the same identity, because the vector is not the same. The generator family
  evaluates `d_+` at `d^{*k}_+𝟏_0`, whose image in `V_k` is the unit `1`, whereas this statement
  evaluates it at `d_+^{k}(1)`, and those differ: `HJO.Sweep.dplusIter_eq_smul_auxVarProd` below
  gives `d_+^{k}(1) = (-1)^{k}y_1y_2⋯y_k`, which is the unit only at `k = 0`.

Both statements are true, and at `k = 0` they coincide. Away from `k = 0` the missing `q^{k}` is
exactly what the change of vector accounts for.

What this file proves instead is the closed form of the tower, from which the identity is immediate:
`τ_{k+1,k+1}` fixes every auxiliary variable, the ascending train `T_{1↗k+1}` fixes the product
`y_1⋯y_{k+1}` because that product is symmetric in each adjacent pair, and `cy_{k+1}` shifts `y_j`
to `y_{j+1}` for `j ≤ k`. So `d_+` multiplies the tower by `-y_{k+1}` up to the train, `d^*_+`
shifts its letters up by one, and multiplying by `-y_1` puts the missing bottom letter back.

## `auxVarProd` is not `HJO.Sweep.auxProd`

`HJO/Shuffle/MellitShiftGenerators.lean` already has `HJO.Sweep.auxProd`, the multiplier
`∏_{i≤k}(y_i - 1)` of the unit shift `τ_k`. The product needed here is `∏_{i≤k}y_i` itself, a
different element, so it gets a different name rather than a second spelling of that one.

## Main results

* `HJO.Sweep.dplusIter_eq_smul_auxVarProd` — `d_+^{k}(1) = (-1)^{k}y_1y_2⋯y_k`.
* `HJO.Sweep.dplus_dplusIter`.

## References

This file proves `HJO.Sweep.dplus_dplusIter`, a step of the sweep process.
-/

@[expose] public section

namespace HJO.Sweep

section Field

variable {L : Type*} [Field L]

/-- The product `y_1y_2⋯y_k` of the first `k` auxiliary variables, which is `X_0X_1⋯X_{k-1}` in the
index convention of `HJO.Sweep.auxVar`. Not `HJO.Sweep.auxProd`, which is `∏_{i≤k}(y_i - 1)`. -/
noncomputable def auxVarProd (L : Type*) [Field L] (k : ℕ) : Total L :=
  ∏ j ∈ Finset.range k, (MvPolynomial.X j : Total L)

theorem auxVarProd_zero : auxVarProd L 0 = 1 := by
  rw [auxVarProd, Finset.range_zero, Finset.prod_empty]

/-- `y_1⋯y_{k+1} = (y_1⋯y_k)y_{k+1}`, the top letter split off. -/
theorem auxVarProd_succ (k : ℕ) :
    auxVarProd L (k + 1) = auxVarProd L k * (auxVar (k + 1) : Total L) := by
  rw [auxVarProd, auxVarProd, Finset.prod_range_succ, auxVar, Nat.add_sub_cancel]

/-- `y_1⋯y_{k+1} = y_1(y_2⋯y_{k+1})`, the bottom letter split off. -/
theorem auxVarProd_succ' (k : ℕ) :
    auxVarProd L (k + 1)
      = (auxVar 1 : Total L) * ∏ j ∈ Finset.range k, (MvPolynomial.X (j + 1) : Total L) := by
  rw [auxVarProd, Finset.prod_range_succ', auxVar, mul_comm]

/-- **`s_i` fixes `y_1⋯y_{k+1}` for `i ≤ k`.** The transposition permutes the two factors `y_i` and
`y_{i+1}`, both of which occur in the product; at the unread index `0` it is the identity. -/
theorem swapAux_auxVarProd {i k : ℕ} (hik : i ≤ k) :
    swapAux L i (auxVarProd L (k + 1)) = auxVarProd L (k + 1) := by
  rw [auxVarProd, map_prod]
  simp only [swapAux_X]
  refine Equiv.Perm.prod_comp (Equiv.swap (i - 1) i) (Finset.range (k + 1)) _ ?_
  intro a ha
  simp only [Set.mem_ofPred_eq] at ha
  simp only [Finset.coe_range, Set.mem_Iio]
  rcases eq_or_ne a (i - 1) with rfl | h1
  · omega
  rcases eq_or_ne a i with rfl | h2
  · omega
  · exact absurd (Equiv.swap_apply_of_ne_of_ne h1 h2) ha

/-- A word in the braid operators fixes anything every one of its letters fixes. -/
theorem prod_map_braidEnd_apply_of_swapAux_eq (q : L) (l : List ℕ) {F : Total L}
    (h : ∀ i ∈ l, swapAux L i F = F) : ((l.map (braidEnd q)).prod) F = F := by
  induction l with
  | nil => simp
  | cons i t ih =>
    rw [List.map_cons, List.prod_cons]
    change braidEnd q i (((t.map (braidEnd q)).prod) F) = F
    rw [ih fun j hj => h j (List.mem_cons_of_mem _ hj)]
    exact braid_of_swapAux_eq q (h i List.mem_cons_self)

/-- **The ascending train `T_{1↗k+1}` fixes `y_1⋯y_{k+1}`.** Its letters are `T_1, …, T_k`, and each
fixes the product by `HJO.Sweep.swapAux_auxVarProd` and `HJO.Sweep.braid_of_swapAux_eq`. -/
theorem trainUpEnd_auxVarProd (q : L) (k : ℕ) :
    trainUpEnd q 1 (k + 1) (auxVarProd L (k + 1)) = auxVarProd L (k + 1) := by
  rw [trainUpEnd, Braid.trainUp_one_eq_prod _ _ _ (by omega), Nat.add_sub_cancel]
  refine prod_map_braidEnd_apply_of_swapAux_eq q _ fun i hi => ?_
  rw [List.mem_range'_1] at hi
  exact swapAux_auxVarProd (by omega)

/-- **`τ_{m,m}` fixes `y_1⋯y_k`**, being an algebra map fixing every auxiliary variable. -/
theorem qshift_auxVarProd (q : L) (m k : ℕ) :
    qshift q m (auxVarProd L k) = auxVarProd L k := by
  rw [auxVarProd, map_prod]
  exact Finset.prod_congr rfl fun j _ => qshift_auxVar q m j

/-- **`cy_{k+1}` shifts every letter of `y_1⋯y_k` up by one.** The wrapping letter `y_{k+1}` does
not occur in the product, so no `u` appears. -/
theorem cycleShift_auxVarProd (u : L) (k : ℕ) :
    cycleShift u k (auxVarProd L k)
      = ∏ j ∈ Finset.range k, (MvPolynomial.X (j + 1) : Total L) := by
  rw [auxVarProd, map_prod]
  exact Finset.prod_congr rfl fun j hj => cycleShift_X_of_lt u (Finset.mem_range.1 hj)

/-- **`d_+(y_1⋯y_k) = -y_1⋯y_{k+1}`.** The one computation the tower needs: `τ_{k+1,k+1}` fixes the
product (`HJO.Sweep.qshift_auxVarProd`), the new letter `y_{k+1}` extends it to `y_1⋯y_{k+1}`, and
the ascending train fixes that extended product (`HJO.Sweep.trainUpEnd_auxVarProd`), leaving only
the sign of `HJO.Sweep.dplus`. -/
theorem dplus_auxVarProd (q : L) (k : ℕ) :
    dplus q k (auxVarProd L k) = -auxVarProd L (k + 1) := by
  rw [dplus_apply, qshift_auxVarProd, mul_comm, ← auxVarProd_succ, trainUpEnd_auxVarProd]

/-- **`d_+^{k}(1) = (-1)^{k}y_1y_2⋯y_k`.** The closed form of the vacuum tower of
`HJO.Sweep.dplus`, by induction from `HJO.Sweep.dplus_auxVarProd`; the sign accumulates. -/
theorem dplusIter_eq_smul_auxVarProd (q : L) (k : ℕ) :
    dplusIter q k = ((-1 : L) ^ k) • auxVarProd L k := by
  induction k with
  | zero => rw [dplusIter, auxVarProd_zero, pow_zero, one_smul]
  | succ k ih =>
    rw [dplusIter, ih, map_smul, dplus_auxVarProd, smul_neg, pow_succ,
      show ((-1 : L) ^ k * (-1)) = -((-1 : L) ^ k) by ring, neg_smul]

/-- **The raising operator on the vacuum.** For every `k ≥ 0`,
`d_+^{k+1}(1) = -y_1 d^*_+ d_+^{k}(1)` in `V_{k+1}`, with `d_+` the raising operator of
`HJO.Sweep.dplus` and `d^*_+` the starred raising operator of `HJO.Sweep.dplusStar`.

Both sides are computed from `HJO.Sweep.dplusIter_eq_smul_auxVarProd`. The left side is
`(-1)^{k+1}y_1⋯y_{k+1}`. On the right, `τ_{k+1,k+1}` fixes `y_1⋯y_k` and `cy_{k+1}` shifts it to
`y_2⋯y_{k+1}`, so `d^*_+d_+^{k}(1) = (-1)^{k}y_2⋯y_{k+1}`, and multiplying by `-y_1` restores the
bottom letter and the sign.

No hypothesis on `q` or `u` is carried, and none is needed: `u` does not occur in either side, since
`cy_{k+1}` only wraps the letter `y_{k+1}`, which `d_+^{k}(1)` does not contain. -/
@[hjo "lem_mellit_dplus_kernel"]
theorem dplus_dplusIter (q u : L) (k : ℕ) :
    dplus q k (dplusIter q k) = -((auxVar 1 : Total L) * dplusStar q u k (dplusIter q k)) := by
  rw [dplusIter_eq_smul_auxVarProd, map_smul, map_smul, dplus_auxVarProd, dplusStar_apply,
    qshift_auxVarProd, cycleShift_auxVarProd, mul_smul_comm, ← auxVarProd_succ', smul_neg]

end Field

end HJO.Sweep

end
