/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.SweepCM
public import HJO.Shuffle.CMRaising
public import HJO.Shuffle.MellitShiftGenerators
public meta import HJO.Attr

/-! # The transport of the modified generators

Mellit's sweep operators `d^♭_±` are not Carlsson and Mellit's `d_±`, and the marked-word lemma the
reduction quotes is stated in the latter. The intertwiner that repairs this is multiplication by
`(-1)^k y_1 ⋯ y_k` on `V_k` — the `Y_k` — which is the identity on `V_0`, so a word
starting and ending at `V_0` has the same value at `1` in both pairs.

## Main definitions

* `HJO.Sweep.transportScalar`: the scalar `(-1)^k y_1 ⋯ y_k`.
* `HJO.Sweep.transport`: the transport `Y_k`, multiplication by it (`HJO.Sweep.transport`).

## Main results

* `HJO.Sweep.braid_transport`: `T_i Y_k = Y_k T_i` (`HJO.Sweep.braid_transport`).
* `HJO.Sweep.dminus_transport`: `d^♭_-(Y_k F) = Y_{k-1}(d_- F)` (`HJO.Sweep.dminus_transport`).
* `HJO.Sweep.dplus_transport`: `d^♭_+(Y_k F) = Y_{k+1}(d_+ F)` (`HJO.Sweep.dplus_transport`).

## Implementation notes

**Nothing new is proved about the extractions.** The arithmetic content of
`HJO.Sweep.dminus_transport` is already proved twice over. The index shift is
`HJO.Sweep.dminusCM_eq_neg_dminus_auxVar_mul`, resting on
`HJO.Sweep.lowerCoeff_auxVar_mul`: multiplying by the last variable raises the exponent of
`y_{k+1}` that the extraction reads by one, which turns `e_j` into `e_{j+1}` — the one difference
between `HJO.Sweep.dminus` and `HJO.Sweep.dminusCM` — and flips the sign, because the sign the
extraction carries is `(-1)` to that same exponent. That the remaining factor `(-1)^k y_1 ⋯ y_k`
reads none of `y_{k+1}` is `HJO.Sweep.lowerCoeff_mul_of_mem_piece`, applied to
`HJO.Sweep.transportScalar_mem_piece`. The bookkeeping with `G_0 = 0` and
`G_{j+1} = (-1)^k y_1 ⋯ y_{k-1} F_j` is those two facts and the splitting
`Y_{k+1} = -(Y_k ∘ (y_{k+1} ·))`.

**The index ranges.** The commutation `T_i Y_k = Y_k T_i` is usually stated for `k ≥ 2` and
`1 ≤ i ≤ k-1`; in `HJO.Sweep.braid_transport` the hypotheses are `1 ≤ i` and `i + 1 ≤ k`, the same
condition with no truncated subtraction (and `k ≥ 2` is then a consequence rather than an
assumption). `d^♭_-(Y_k F) = Y_{k-1}(d_- F)` is usually stated for `k ≥ 1`; in
`HJO.Sweep.dminus_transport` the index is written `k + 1`, so that `Y_{k-1}` is `Y_k` and again
nothing is subtracted in `ℕ`.

**Which raising operator.** `HJO.Sweep.dplus` carries a sign and a factor of
`y_{k+1}` that `HJO.Sweep.cmDPlus` does not, and
`HJO.Sweep.dplus_eq_neg_cmDPlus` is the bridge between them. That extra factor `y_{k+1}` is exactly
what turns `Y_k` into `-Y_{k+1}`, which is the sign the proof of
`HJO.Sweep.dplus_transport` cancels against the sign of `d^♭_+`.

## References

Transcribing A. Mellit, *Toric braids and `(m, n)`-parking functions*, the remark
replacing the generators.
-/

@[expose] public section

open Finset

namespace HJO.Sweep

/-! ### The transport -/

section CommRingBase

variable {L : Type*} [CommRing L]

/-- `y_{j+1}` is the auxiliary variable `X j`, the shift being the `1`-based indexing of
`HJO.Sweep.auxVar`. -/
theorem auxVar_succ (j : ℕ) : (auxVar (j + 1) : Total L) = MvPolynomial.X j := by
  rw [auxVar, Nat.add_sub_cancel]

/-- The scalar `(-1)^k y_1 y_2 ⋯ y_k` the transport multiplies by, the empty product at `k = 0`
being `1`. -/
noncomputable def transportScalar (L : Type*) [CommRing L] (k : ℕ) : Total L :=
  (-1) ^ k * ∏ j ∈ Finset.range k, (auxVar (j + 1) : Total L)

/-- **The transport of the modified generators.** `HJO.Sweep.transport`: for
`k ≥ 0`, the `Λ`-linear endomorphism `Y_k` of `V_k` with `Y_k(F) = (-1)^k y_1 y_2 ⋯ y_k F`, the
product of the variables being empty at `k = 0`, so that `Y_0` is the identity of `V_0`
(`HJO.Sweep.transport_zero`).

Stated on the total space, in the one-total-space convention of `HJO/Shuffle/SweepModule.lean`: the
scalar lies in `V_k` (`HJO.Sweep.transportScalar_mem_piece`), so the restriction to `V_k` is an
endomorphism of `V_k`, which is the map in question. `Λ`-linearity is the linearity used at the
type-`C` step of `HJO.Mellit.constantCoeff_psiWord_one_mem_lambdaComp_and_map_eq_sweepChar`, where
`Y_k` is pulled through `(q-1)^{-1}`. -/
@[hjo "def_sweep_transport"]
noncomputable def transport (L : Type*) [CommRing L] (k : ℕ) :
    Total L →ₗ[Sym.Lambda L] Total L :=
  LinearMap.mulLeft (Sym.Lambda L) (transportScalar L k)

@[simp]
theorem transport_apply (k : ℕ) (F : Total L) : transport L k F = transportScalar L k * F := rfl

@[simp]
theorem transportScalar_zero : transportScalar L 0 = 1 := by simp [transportScalar]

/-- **`Y_0` is the identity of `V_0`.** The closing clause of `HJO.Sweep.transport`, and
what makes a word from `V_0` to `V_0` have the same value in both pairs of generators. -/
@[simp]
theorem transport_zero (F : Total L) : transport L 0 F = F := by
  rw [transport_apply, transportScalar_zero, one_mul]

/-- The recursion `(-1)^{k+1} y_1 ⋯ y_{k+1} = -((-1)^k y_1 ⋯ y_k) y_{k+1}`. -/
theorem transportScalar_succ (k : ℕ) :
    transportScalar L (k + 1) = -(transportScalar L k * (auxVar (k + 1) : Total L)) := by
  rw [transportScalar, transportScalar, Finset.prod_range_succ, pow_succ]
  ring

/-- The transport scalar lies in `V_k`: it is a product of `y_1, …, y_k`. -/
theorem transportScalar_mem_piece (k : ℕ) : transportScalar L k ∈ piece L k := by
  refine Subalgebra.mul_mem _ (pow_mem (neg_mem (one_mem _)) k)
    (Subalgebra.prod_mem _ fun j hj => ?_)
  exact auxVar_mem_piece (by omega) (by have := mem_range.1 hj; omega)

/-- **The adjacent transposition fixes the transport scalar.** For `1 ≤ i` and `i + 1 ≤ k` the
product `y_1 ⋯ y_k` contains both `y_i` and `y_{i+1}`, so interchanging them leaves it alone; the
sign is a constant. This is the whole content of `HJO.Sweep.braid_transport`. -/
theorem swapAux_transportScalar {i k : ℕ} (hi : 1 ≤ i) (hik : i + 1 ≤ k) :
    swapAux L i (transportScalar L k) = transportScalar L k := by
  classical
  have himg : (Finset.range k).image (Equiv.swap (i - 1) i) = Finset.range k := by
    refine Finset.eq_of_subset_of_card_le (fun m hm => ?_) ?_
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hm
      rw [mem_range] at hj ⊢
      rcases eq_or_ne j (i - 1) with rfl | h1
      · rw [Equiv.swap_apply_left]; omega
      rcases eq_or_ne j i with rfl | h2
      · rw [Equiv.swap_apply_right]; omega
      · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]; exact hj
    · rw [Finset.card_image_of_injective _ (Equiv.swap (i - 1) i).injective]
  rw [transportScalar, map_mul, map_pow, map_neg, map_one, map_prod]
  refine congrArg _ ?_
  calc ∏ j ∈ Finset.range k, swapAux L i (auxVar (j + 1) : Total L)
      = ∏ j ∈ Finset.range k, (MvPolynomial.X (Equiv.swap (i - 1) i j) : Total L) :=
        Finset.prod_congr rfl fun j _ => by rw [auxVar_succ, swapAux_X]
    _ = ∏ m ∈ (Finset.range k).image (Equiv.swap (i - 1) i), (MvPolynomial.X m : Total L) :=
        (Finset.prod_image fun x _ y _ h => (Equiv.swap (i - 1) i).injective h).symm
    _ = ∏ j ∈ Finset.range k, (auxVar (j + 1) : Total L) := by
        rw [himg]
        exact Finset.prod_congr rfl fun j _ => (auxVar_succ j).symm

end CommRingBase

/-! ### The transport of the raising operator -/

section Operators

variable {L : Type*} [Field L]

/-- **The braid operators commute with the transport.**
`HJO.Sweep.braid_transport`: `T_i(Y_k F) = Y_k(T_i F)` for `1 ≤ i ≤ k-1`, here written
`1 ≤ i` and `i + 1 ≤ k`.

`T_i` is linear over anything `s_i` fixes (`HJO.Sweep.braid_mul_of_swapAux_eq`) and `s_i` fixes the
transport scalar, so there is nothing else to check. -/
@[hjo "lem_sweep_transport_braid"]
theorem braid_transport (q : L) {k i : ℕ} (hi : 1 ≤ i) (hik : i + 1 ≤ k) (F : Total L) :
    braid q i (transport L k F) = transport L k (braid q i F) := by
  rw [transport_apply, transport_apply]
  exact braid_mul_of_swapAux_eq q (swapAux_transportScalar hi hik) F

/-- Adding the letter `(q-1)y_i` fixes the transport scalar, being an algebra homomorphism that
fixes every auxiliary variable. -/
theorem qshift_transportScalar (q : L) (i k : ℕ) :
    qshift q i (transportScalar L k) = transportScalar L k := by
  rw [transportScalar, map_mul, map_pow, map_neg, map_one, map_prod]
  exact congrArg _ (Finset.prod_congr rfl fun j _ => by
    rw [auxVar_succ, qshift_auxVar])

/-- Subtracting the letter `(q-1)y_i` fixes the transport scalar, for the same reason. -/
theorem qshiftNeg_transportScalar (q : L) (i k : ℕ) :
    qshiftNeg q i (transportScalar L k) = transportScalar L k := by
  rw [transportScalar, map_mul, map_pow, map_neg, map_one, map_prod]
  exact congrArg _ (Finset.prod_congr rfl fun j _ => by
    rw [auxVar_succ, qshiftNeg_auxVar])

/-- **The transport carries the raising operator to the modified one.**
`HJO.Sweep.dplus_transport`: `d^♭_+(Y_k F) = Y_{k+1}(d_+ F)`, with `d^♭_+` the raising operator of
`HJO.Sweep.dplus` and `d_+` that of `HJO.Sweep.cmDPlus`.

By `HJO.Sweep.dplus_eq_neg_cmDPlus` the sweep operator is `-d_+ ∘ (y_{k+1}·)`, and
`y_{k+1}(-1)^k y_1 ⋯ y_k = -(-1)^{k+1}y_1 ⋯ y_{k+1}`, so the extra factor turns `Y_k` into
`-Y_{k+1}` and the two signs cancel. What remains is that `d_+` is linear over the transport
scalar of index `k+1`: the substitution `τ_{k+1,k+1}` fixes it and each letter `T_1, …, T_k` of the
word commutes past it by `HJO.Sweep.swapAux_transportScalar`. -/
@[hjo "lem_sweep_transport_dplus"]
theorem dplus_transport (q : L) (k : ℕ) (F : Total L) :
    dplus q k (transport L k F) = transport L (k + 1) (cmDPlus q k F) := by
  have hmul : ∀ H : Total L,
      cmDPlus q k (transportScalar L (k + 1) * H)
        = transportScalar L (k + 1) * cmDPlus q k H := fun H => by
    rw [cmDPlus_apply, cmDPlus_apply, map_mul, qshift_transportScalar,
      cmAscWord_mul_of_swapAux_eq q (by omega)
        (fun j hj1 hj2 => swapAux_transportScalar hj1 (by omega))]
  have hy : (auxVar (k + 1) : Total L) * (transportScalar L k * F)
      = -(transportScalar L (k + 1) * F) := by
    rw [transportScalar_succ]
    ring
  rw [dplus_eq_neg_cmDPlus, LinearMap.neg_apply, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.mulLeft_apply, transport_apply, hy, map_neg, hmul, transport_apply, neg_neg]

end Operators

/-! ### The transport of the lowering operator -/

section Newton

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **The lowering operator is linear over the transport scalar of the lower index.** The scalar
`(-1)^k y_1 ⋯ y_k` lies in `V_k` and so reads none of `y_{k+1}`, which is what justifies
pulling `(-1)^k y_1 ⋯ y_{k-1}` out of the sum `∑_j (-1)^{j+1} e_{j+1} G_{j+1}`. Both halves
of `d^♭_-` respect it: `τ^-_{k+1,k+1}` fixes it (`HJO.Sweep.qshiftNeg_transportScalar`), and the
coefficient extraction is linear over anything in `V_k`
(`HJO.Sweep.lowerCoeff_mul_of_mem_piece`). -/
theorem dminus_transportScalar_mul (q : L) (k : ℕ) (G : Total L) :
    dminus q (k + 1) (transportScalar L k * G) = transportScalar L k * dminus q (k + 1) G := by
  rw [dminus_succ_apply, dminus_succ_apply, map_mul, qshiftNeg_transportScalar,
    lowerCoeff_mul_of_mem_piece (transportScalar_mem_piece k)]

/-- **The transport carries the lowering operator to the modified one.**
`HJO.Sweep.dminus_transport`: `d^♭_-(Y_k F) = Y_{k-1}(d_- F)`, with `d^♭_-` the operator of
`HJO.Sweep.dminus` and `d_-` that of `HJO.Sweep.dminusCM`; the index is written `k + 1`, so
`Y_{k-1}` is `Y_k` and nothing is subtracted in `ℕ`.

The bookkeeping — `τ^-_{k,k}(Y_kF)` has `G_0 = 0` and
`G_{j+1} = (-1)^k y_1 ⋯ y_{k-1} F_j`, whence `d^♭_-(G) = ∑_j (-1)^{j+1} e_{j+1} G_{j+1}` — is two
earlier identities meeting. Splitting `Y_{k+1}` as `-(Y_k ∘ (y_{k+1} ·))`
(`HJO.Sweep.transportScalar_succ`), the outer factor passes through `d^♭_-` by
`HJO.Sweep.dminus_transportScalar_mul` and the inner one is exactly the index shift
`HJO.Sweep.dminusCM_eq_neg_dminus_auxVar_mul`: multiplying by the last
variable raises the exponent the extraction reads by one, turning `e_j` into `e_{j+1}` and flipping
the sign. The two signs then cancel. -/
@[hjo "lem_sweep_transport_dminus"]
theorem dminus_transport (q : L) (k : ℕ) (F : Total L) :
    dminus q (k + 1) (transport L (k + 1) F) = transport L k (dminusCM q (k + 1) F) := by
  have hsplit : transportScalar L (k + 1) * F
      = -(transportScalar L k * ((auxVar (k + 1) : Total L) * F)) := by
    rw [transportScalar_succ]
    ring
  have hshift : dminus q (k + 1) ((auxVar (k + 1) : Total L) * F) = -dminusCM q (k + 1) F := by
    rw [dminusCM_eq_neg_dminus_auxVar_mul q k F, neg_neg]
  rw [transport_apply, transport_apply, hsplit, map_neg, dminus_transportScalar_mul, hshift]
  ring

end Newton

end HJO.Sweep
