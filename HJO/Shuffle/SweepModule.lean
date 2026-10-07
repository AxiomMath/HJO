/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidTrain
public import HJO.Shuffle.SlopeWord
public import HJO.Symmetric.SymmetricFunctions
public import Mathlib.Algebra.Algebra.Subalgebra.Tower
public import Mathlib.Tactic.LinearCombination
public meta import HJO.Attr

/-! # The Carlsson–Mellit graded module and the operators of the sweep

The whole of Mellit's Sections 2–6 acts on the family `V_k = Λ ⊗_𝕜 𝕜[y_1, …, y_k]` of
`HJO.Sweep.piece`. This file builds that family **inside one total space** and the seven operators
the sweep and the conjugate side name on it: the two virtual-alphabet substitutions `τ_{k,i}` and
`τ^-_{k,i}`, the divided difference `∂_i`, the braid operator `T_i`, the lowering and raising
operators `d_-` and `d_+`, the corner operator `Δ`, the cyclic shift `cy_{k+1}`, the conjugate
raising operator `d^*_+` and the conjugate commuting operators `z_i`.

## Why one total space

`HJO.Mellit.sweepOperator` reads: "`Φ_{P̂}(P)` is the `𝕜`-linear map from `V_k` to
`V_{k'}`, where `k = k_{P̂}(P)`", with `k'` one of `k-1`, `k`, `k+1` according to the event type at
`P`; and `HJO.Mellit.sweepWord` composes those maps along the swept region, the width `k` changing
at every type-A and type-B event. A family of *types* `V : ℕ → Type` therefore makes the sweep word
a dependently typed composite whose intermediate types are computed from the path — the sharpest
hazard of this layer. So `V_k` is realised here as a *submodule* `HJO.Sweep.piece k` of the single
space `HJO.Sweep.Total L = Λ[y_1, y_2, …]`, every operator is an endomorphism of that one space, and
the domains and codomains become membership statements. The sweep word is then an
ordinary product in `Module.End`.

## Main definitions

* `HJO.Sweep.Total`: the total space `V_* = Λ[y_1, y_2, …]`, with `HJO.Sweep.piece k` its
  subalgebra `V_k` on the first `k` auxiliary variables and `HJO.Sweep.pieceSub k` the same object
  as an `L`-submodule.
* `HJO.Sweep.qshift`, `HJO.Sweep.qshiftNeg`: `τ_{k,i}` and `τ^-_{k,i}`.
* `HJO.Sweep.dividedDiff`: `∂_i`; `HJO.Sweep.braid`: `T_i`; `HJO.Sweep.braidInv`: `T_i^{-1}`.
* `HJO.Sweep.dminus`, `HJO.Sweep.dplus`, `HJO.Sweep.corner`: `d_-`, `d_+`, `Δ`.
* `HJO.Sweep.cycleShift`, `HJO.Sweep.dplusStar`, `HJO.Sweep.zop`: `cy_{k+1}`, `d^*_+`, `z_i`.

## Implementation notes

`Total L` is `MvPolynomial ℕ (Sym.Lambda L)`: polynomials in the auxiliary variables with
coefficients in the ring `Λ = HJO.Sym.Lambda L` of symmetric functions. The auxiliary variable
`y_i`, for
`i ≥ 1`, is `MvPolynomial.X (i - 1)`; the truncated subtraction is the convention
`HJO.Sym.powerSum` already uses for `p_r`, and it makes `y_0` the same variable as `y_1`, which no
statement below reads. With the auxiliary variables *outside* and `Λ` in the coefficient ring,
`τ_{k,i}` is an `HJO.Sym.Lambda`-prescription extended by the identity on the `y`, i.e. a single
`MvPolynomial.aevalTower`, and `∂_i` and `T_i` are `Λ`-linear.

`V_k` can also be presented as the *per-`k`* type `Lambda (MvPolynomial (Fin k) K)`; that
presentation and this one are the same object read two ways — `piece k` is the image of
`AuxLambda L k` under the evident inclusion — but the per-`k` type is not the right shape for
`HJO.Mellit.sweepOperator`, for the reason above. The faithfulness question, "is this
`Λ ⊗_𝕜 𝕜[y_1,…,y_k]`?", is answered by
`HJO.Sweep.pieceTensorAlgEquiv` (`HJO/Shuffle/SweepPiece.lean`), which exhibits the tensor
product on the nose.

The divided difference departs from the letter deliberately. `HJO.Sweep.dividedDiffₗ` sends
`V_k` into `Λ ⊗_𝕜 𝕜(y_1, …, y_k)` — the *fraction field* — and `HJO.Sweep.dividedDiff_mem_piece`
then says the value is a polynomial. Here `∂_i F` is constructed directly as the polynomial
quotient, from the divisibility `(y_{i+1} - y_i) ∣ F - s_i F` proved by induction on `F`, and the
fraction-field lemma becomes the pair `HJO.Sweep.dividedDiff_spec` — which pins `∂_i F` as *the*
quotient, so that nothing weaker than the object has been defined — and
`HJO.Sweep.dividedDiff_mem_piece` — the grading, which is the lemma's own content. Going through the
fraction field would add a second ambient ring that no statement below mentions.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, §5, and A. Mellit,
*Toric braids and `(m,n)`-parking functions*, §§3.2, 3.6.
-/

@[expose] public section

namespace HJO.Sweep

open MvPolynomial

/-! ### The total space and its graded pieces -/

/-- The total space `V_* = Λ[y_1, y_2, …]` of the sweep: polynomials in countably many auxiliary
variables with coefficients in the ring of symmetric functions. The `V_k` is the
subalgebra `piece k` of those elements using only `y_1, …, y_k`, and every operator of the sweep is
an endomorphism of this one space. -/
abbrev Total (L : Type*) [CommRing L] : Type _ := MvPolynomial ℕ (Sym.Lambda L)

section CommRingBase

variable {L : Type*} [CommRing L]

/-- The auxiliary variable `y_i`, for `i ≥ 1`. The truncated subtraction in the
index is the convention `HJO.Sym.powerSum` uses for `p_r`: it makes `y_0` the same variable as
`y_1`, and no statement below reads `y_0`. -/
noncomputable def auxVar (i : ℕ) : Total L := MvPolynomial.X (i - 1)

/-- `y_1` is the variable `X 0`, the index convention of `HJO.Sweep.auxVar`. -/
theorem auxVar_one : (auxVar 1 : Total L) = MvPolynomial.X 0 := rfl

/-- `y_2` is the variable `X 1`. -/
theorem auxVar_two : (auxVar 2 : Total L) = MvPolynomial.X 1 := rfl

/-- The graded piece `V_k = Λ ⊗_𝕜 𝕜[y_1, …, y_k]`, realised inside `Total L` as the
`Λ`-subalgebra of the elements using only the auxiliary variables `y_1, …, y_k`.

That this subalgebra *is* the tensor product, and not merely a module containing a copy
of it, is `HJO.Sweep.pieceTensorAlgEquiv`: a `Λ`-algebra isomorphism
`piece L k ≃ₐ[Λ] Λ ⊗[L] L[y_1, …, y_k]`. So the two factors of the formula are the
ring `HJO.Sym.Lambda` of symmetric functions and a polynomial ring in exactly `k` variables,
tensored over the base `L`, and nothing weaker has been defined. -/
@[hjo "def_sweep_module"]
noncomputable def piece (L : Type*) [CommRing L] (k : ℕ) :
    Subalgebra (Sym.Lambda L) (Total L) :=
  MvPolynomial.supported (Sym.Lambda L) (Set.Iio k)

/-- The graded piece `V_k` as an `L`-submodule of the total space, the shape in which the
operators' domains and codomains are stated: every operator below is `L`-linear, and only some of
them are `Λ`-linear. -/
noncomputable def pieceSub (L : Type*) [CommRing L] (k : ℕ) : Submodule L (Total L) :=
  ((piece L k).restrictScalars L).toSubmodule

/-- `y_i` lies in `V_k` as soon as `1 ≤ i ≤ k`. -/
theorem auxVar_mem_piece {i k : ℕ} (h1 : 1 ≤ i) (hk : i ≤ k) :
    (auxVar i : Total L) ∈ piece L k := by
  rw [piece, MvPolynomial.supported_eq_adjoin_X]
  exact Algebra.subset_adjoin ⟨i - 1, by simp only [Set.mem_Iio]; omega, rfl⟩

/-- The graded pieces increase with `k`. -/
theorem piece_mono {k l : ℕ} (h : k ≤ l) : piece L k ≤ piece L l :=
  MvPolynomial.supported_mono (Set.Iio_subset_Iio h)

/-! ### The adjacent transposition of two auxiliary variables -/

/-- **The adjacent transposition of two auxiliary variables.** The `Λ`-algebra automorphism `s_i`
of the total space interchanging `y_i` and `y_{i+1}` and fixing every other auxiliary variable,
the `s_i` of `HJO.Sweep.swapAux`, `HJO.Sweep.dividedDiffₗ` and `HJO.Sweep.braid`. On `V_k`, for
`1 ≤ i ≤ k - 1`, it restricts to the `Λ`-algebra automorphism of `V_k`
(`swapAux_mem_piece`); the restriction is what `HJO.Sweep.swapAux` names, and the extension to the
total space by the same rename on the unread variables is the one-total-space convention of this
file.

The same automorphism can be presented on the
*other* model of `V_k`, `Lambda (MvPolynomial (Fin k) K)`, with the auxiliary variables inside the
coefficient ring. That is a second encoding of one object, and the layer's encoding is this one —
auxiliary variables outside, `Λ` in the coefficients — so it is defined here once. -/
@[hjo "def_cm_swap"]
noncomputable def swapAux (L : Type*) [CommRing L] (i : ℕ) : Total L ≃ₐ[Sym.Lambda L] Total L :=
  MvPolynomial.renameEquiv (Sym.Lambda L) (Equiv.swap (i - 1) i)

theorem swapAux_X (i j : ℕ) :
    swapAux L i (MvPolynomial.X j) = MvPolynomial.X (Equiv.swap (i - 1) i j) := by
  simp [swapAux]

theorem swapAux_C (i : ℕ) (a : Sym.Lambda L) :
    swapAux L i (MvPolynomial.C a) = MvPolynomial.C a := by
  simp [swapAux]

/-- `s_i` interchanges `y_i` and `y_{i+1}`, for `i ≥ 1`. -/
@[hjo "def_cm_swap"]
theorem swapAux_auxVar_self {i : ℕ} (hi : 1 ≤ i) :
    swapAux L i (auxVar i) = (auxVar (i + 1) : Total L) := by
  have h : i + 1 - 1 = i := by omega
  rw [auxVar, auxVar, h, swapAux_X, Equiv.swap_apply_left]

/-- At the unread index `0` the transposition is the identity, `y_0` being `y_1`. -/
theorem swapAux_zero (F : Total L) : swapAux L 0 F = F := by
  have h : (swapAux L 0).toAlgHom = AlgHom.id (Sym.Lambda L) (Total L) := by
    refine MvPolynomial.algHom_ext fun n => ?_
    simp only [AlgHom.id_apply, AlgEquiv.coe_toAlgHom]
    rw [swapAux_X]
    simp
  exact congrArg (fun f : Total L →ₐ[Sym.Lambda L] Total L => f F) h

/-- `s_i` is an involution. -/
theorem swapAux_swapAux (i : ℕ) (F : Total L) : swapAux L i (swapAux L i F) = F := by
  have : (swapAux L i).toAlgHom.comp (swapAux L i).toAlgHom = AlgHom.id _ _ := by
    refine MvPolynomial.algHom_ext fun n => ?_
    simp only [AlgHom.comp_apply, AlgHom.id_apply, AlgEquiv.coe_toAlgHom]
    rw [swapAux_X, swapAux_X, Equiv.swap_apply_self]
  exact congrArg (fun f : Total L →ₐ[Sym.Lambda L] Total L => f F) this

/-! ### The divided difference

`HJO.Sweep.dividedDiffₗ` divides inside `Λ ⊗ 𝕜(y_1, …, y_k)`;
`HJO.Sweep.dividedDiff_mem_piece` then says the quotient is a polynomial. Here the divisibility is
proved first, by induction on `F`, and the quotient is taken in the polynomial ring itself. -/

/-- **`y_{i+1} - y_i` divides `F - s_i F`.** The content of `HJO.Sweep.dividedDiff_mem_piece`,
proved by induction on `F`: the set of `F` with this property contains the constants, is closed
under addition, and is closed under multiplication by an auxiliary variable, because
`F y_n - s_i(F) y_{σ n} = (F - s_iF) y_n + s_iF (y_n - y_{σ n})` and the second factor is `0` or
`±(y_{i+1} - y_i)`. -/
theorem sub_dvd_sub_swapAux (i : ℕ) (F : Total L) :
    (MvPolynomial.X i - MvPolynomial.X (i - 1) : Total L) ∣ F - swapAux L i F := by
  induction F using MvPolynomial.induction_on with
  | C a => rw [swapAux_C, sub_self]; exact dvd_zero _
  | add p q hp hq =>
    have h : p + q - swapAux L i (p + q) = (p - swapAux L i p) + (q - swapAux L i q) := by
      rw [map_add]; ring
    rw [h]; exact dvd_add hp hq
  | mul_X p n hp =>
    have hstep : p * MvPolynomial.X n - swapAux L i (p * MvPolynomial.X n)
        = (p - swapAux L i p) * MvPolynomial.X n
          + swapAux L i p * (MvPolynomial.X n - MvPolynomial.X (Equiv.swap (i - 1) i n)) := by
      rw [map_mul, swapAux_X]; ring
    rw [hstep]
    refine dvd_add (Dvd.dvd.mul_right hp _) (Dvd.dvd.mul_left ?_ _)
    rcases eq_or_ne n (i - 1) with rfl | hn1
    · rw [Equiv.swap_apply_left]; exact ⟨-1, by ring⟩
    rcases eq_or_ne n i with rfl | hn2
    · rw [Equiv.swap_apply_right]
    · rw [Equiv.swap_apply_of_ne_of_ne hn1 hn2, sub_self]; exact dvd_zero _

/-- **The divided difference `∂_i`.** `HJO.Sweep.dividedDiffₗ`: the quotient
`(F - s_i F)/(y_{i+1} - y_i)`, taken here in the polynomial ring itself rather than in
`Λ ⊗ 𝕜(y_1, …, y_k)`, the divisibility being `sub_dvd_sub_swapAux`. It is pinned as *the* quotient
by `dividedDiff_spec`, since `y_{i+1} - y_i` is not a zero divisor. -/
noncomputable def dividedDiff (i : ℕ) (F : Total L) : Total L :=
  if 1 ≤ i then (sub_dvd_sub_swapAux i F).choose else 0

/-- **`∂_i` is the divided difference.** `(y_{i+1} - y_i) ∂_i F = F - s_i F`: the identity that
makes `dividedDiff` the quotient and not merely some polynomial. It holds at the unread
index `0` as well, both sides being `0` there, which is what lets `dividedDiffₗ` be a linear map
with no side condition. -/
theorem dividedDiff_spec (i : ℕ) (F : Total L) :
    (MvPolynomial.X i - MvPolynomial.X (i - 1) : Total L) * dividedDiff i F
      = F - swapAux L i F := by
  rw [dividedDiff]
  split_ifs with h
  · exact ((sub_dvd_sub_swapAux i F).choose_spec).symm
  · have hi : i = 0 := by omega
    subst hi
    rw [swapAux_zero, mul_zero, sub_self]

/-- `s_i` maps `V_k` into itself as soon as `1 ≤ i ≤ k - 1`, since it permutes two of the first
`k` auxiliary variables and fixes the rest. -/
theorem swapAux_mem_piece {i k : ℕ} (h1 : 1 ≤ i) (hik : i < k) {F : Total L}
    (hF : F ∈ piece L k) : swapAux L i F ∈ piece L k := by
  have hswap : ∀ j : ℕ, j < k → Equiv.swap (i - 1) i j < k := by
    intro j hj
    rcases eq_or_ne j (i - 1) with rfl | hn1
    · rw [Equiv.swap_apply_left]; omega
    rcases eq_or_ne j i with rfl | hn2
    · rw [Equiv.swap_apply_right]; omega
    · rw [Equiv.swap_apply_of_ne_of_ne hn1 hn2]; omega
  have hgen : (MvPolynomial.X '' Set.Iio k : Set (Total L)) ⊆
      ↑((piece L k).comap (swapAux L i).toAlgHom) := by
    rintro _ ⟨j, hj, rfl⟩
    refine (Subalgebra.mem_comap _ _ _).2 ?_
    simp only [AlgEquiv.coe_toAlgHom, swapAux_X]
    rw [piece, MvPolynomial.supported_eq_adjoin_X]
    exact Algebra.subset_adjoin ⟨Equiv.swap (i - 1) i j, hswap j hj, rfl⟩
  have hle := (Algebra.adjoin_le hgen : Algebra.adjoin (Sym.Lambda L) _ ≤ _)
  rw [← MvPolynomial.supported_eq_adjoin_X, ← piece] at hle
  exact (Subalgebra.mem_comap _ _ _).1 (hle hF)

end CommRingBase

/-! ### The divided difference is linear, and stays in `V_k`

Everything from here on is over the coefficient field `𝕜 = ℚ(q, u)` of the construction: the field
hypothesis is what makes `y_{i+1} - y_i` a non-zero-divisor, hence what turns
`dividedDiff_spec` into a characterisation and makes `∂_i` linear. -/

section Field

variable {L : Type*} [Field L]

/-- `y_{i+1} - y_i` is nonzero, for `i ≥ 1`. -/
theorem auxVar_sub_ne_zero {i : ℕ} (hi : 1 ≤ i) :
    (MvPolynomial.X i - MvPolynomial.X (i - 1) : Total L) ≠ 0 := by
  refine sub_ne_zero.2 fun h => ?_
  have := MvPolynomial.X_injective (R := Sym.Lambda L) h
  omega

/-- **`∂_i F` is the only polynomial with `(y_{i+1} - y_i) G = F - s_i F`.** -/
theorem dividedDiff_unique {i : ℕ} (hi : 1 ≤ i) {F G : Total L}
    (h : (MvPolynomial.X i - MvPolynomial.X (i - 1) : Total L) * G = F - swapAux L i F) :
    G = dividedDiff i F :=
  mul_left_cancel₀ (auxVar_sub_ne_zero hi) (h.trans (dividedDiff_spec i F).symm)

/-- At the unread index `0` the divided difference is `0`. -/
theorem dividedDiff_zero_index (F : Total L) : dividedDiff 0 F = 0 := by
  simp [dividedDiff]

/-- `∂_i` is additive, at every index. -/
theorem dividedDiff_add (i : ℕ) (F G : Total L) :
    dividedDiff i (F + G) = dividedDiff i F + dividedDiff i G := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [dividedDiff_zero_index, dividedDiff_zero_index, dividedDiff_zero_index, add_zero]
  · exact (dividedDiff_unique hi
      (by rw [mul_add, dividedDiff_spec, dividedDiff_spec, map_add]; ring)).symm

/-- `∂_i` is `Λ`-linear: it commutes with multiplication by a symmetric function. -/
theorem dividedDiff_C_mul (i : ℕ) (c : Sym.Lambda L) (F : Total L) :
    dividedDiff i (MvPolynomial.C c * F) = MvPolynomial.C c * dividedDiff i F := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [dividedDiff_zero_index, dividedDiff_zero_index, mul_zero]
  refine (dividedDiff_unique hi ?_).symm
  rw [map_mul, swapAux_C, ← mul_sub, ← dividedDiff_spec i F]
  ring

/-- **The divided difference `∂_i`, as a `Λ`-linear map.** `HJO.Sweep.dividedDiffₗ`
read as a map: `∂_i F = (F - s_i F)/(y_{i+1} - y_i)`, `Λ`-linear in `F` because the quotient by a
non-zero-divisor is unique. The standard definition has `∂_i` on `V_k` only for `k ≥ 2` and
`1 ≤ i ≤ k-1`; here it is one endomorphism of the total space for each `i`, the unread index `0`
being sent to the zero map so that no side condition is carried, and the range condition reappears
as the hypothesis of `dividedDiff_mem_piece`. -/
@[hjo "def_sweep_divided"]
noncomputable def dividedDiffₗ (i : ℕ) : Total L →ₗ[Sym.Lambda L] Total L where
  toFun := dividedDiff i
  map_add' := dividedDiff_add i
  map_smul' c F := by
    simp only [RingHom.id_apply, Algebra.smul_def, MvPolynomial.algebraMap_eq]
    exact dividedDiff_C_mul i c F

@[simp]
theorem dividedDiffₗ_apply (i : ℕ) (F : Total L) : dividedDiffₗ i F = dividedDiff i F := rfl

/-- The retraction of the total space onto the polynomials in the first `k` auxiliary variables,
sending `y_j` to itself for `j ≤ k` and to `0` beyond. It is a section of the inclusion of `V_k`,
which is what makes the grading of `∂_i` a cancellation. -/
noncomputable def retract (L : Type*) [Field L] (k : ℕ) :
    Total L →ₐ[Sym.Lambda L] MvPolynomial (Set.Iio k) (Sym.Lambda L) :=
  MvPolynomial.aeval fun n => if h : n ∈ Set.Iio k then MvPolynomial.X ⟨n, h⟩ else 0

theorem retract_rename (k : ℕ) (F : MvPolynomial (Set.Iio k) (Sym.Lambda L)) :
    retract L k (MvPolynomial.rename Subtype.val F) = F := by
  have h : (retract L k).comp (MvPolynomial.rename Subtype.val) = AlgHom.id _ _ := by
    refine MvPolynomial.algHom_ext fun n => ?_
    simp only [AlgHom.comp_apply, AlgHom.id_apply, MvPolynomial.rename_X, retract,
      MvPolynomial.aeval_X]
    split_ifs with h
    · rfl
    · exact absurd n.2 h
  exact congrArg (fun f : MvPolynomial (Set.Iio k) (Sym.Lambda L) →ₐ[Sym.Lambda L] _ => f F) h

/-- **`∂_i` lands in `V_k`.** `HJO.Sweep.dividedDiff_mem_piece`: for `k ≥ 2`,
`1 ≤ i ≤ k-1` and `F ∈ V_k`, `∂_i F ∈ V_k`.

In this presentation the "is a polynomial" half of that lemma is built into `dividedDiff` —
`sub_dvd_sub_swapAux` is the divisibility the proof establishes — and what remains is
the grading, proved here by applying the retraction `retract L k` to
`(y_{i+1} - y_i) ∂_i F = F - s_i F` and cancelling `y_{i+1} - y_i`. -/
@[hjo "lem_sweep_divided_poly"]
theorem dividedDiff_mem_piece {i k : ℕ} (h1 : 1 ≤ i) (hik : i < k) {F : Total L}
    (hF : F ∈ piece L k) : dividedDiff i F ∈ piece L k := by
  set D : Total L := MvPolynomial.X i - MvPolynomial.X (i - 1) with hD
  have hi1 : (i - 1 : ℕ) ∈ Set.Iio k := by simp only [Set.mem_Iio]; omega
  have hi2 : i ∈ Set.Iio k := by simp only [Set.mem_Iio]; omega
  set D₀ : MvPolynomial (Set.Iio k) (Sym.Lambda L) :=
    MvPolynomial.X ⟨i, hi2⟩ - MvPolynomial.X ⟨i - 1, hi1⟩ with hD₀
  have hDr : MvPolynomial.rename Subtype.val D₀ = D := by
    rw [hD₀, hD, map_sub, MvPolynomial.rename_X, MvPolynomial.rename_X]
  have hH : F - swapAux L i F ∈ piece L k :=
    sub_mem hF (swapAux_mem_piece h1 hik hF)
  rw [piece, MvPolynomial.supported_eq_range_rename, AlgHom.mem_range] at hH ⊢
  obtain ⟨H₀, hH₀⟩ := hH
  refine ⟨retract L k (dividedDiff i F), ?_⟩
  have key : D * MvPolynomial.rename Subtype.val (retract L k (dividedDiff i F))
      = D * dividedDiff i F := by
    have h1' : retract L k D * retract L k (dividedDiff i F) = H₀ := by
      rw [← map_mul, dividedDiff_spec, ← hH₀, retract_rename]
    have h2' : retract L k D = D₀ := by rw [← hDr, retract_rename]
    rw [h2'] at h1'
    calc D * MvPolynomial.rename Subtype.val (retract L k (dividedDiff i F))
        = MvPolynomial.rename Subtype.val (D₀ * retract L k (dividedDiff i F)) := by
          rw [map_mul, hDr]
      _ = MvPolynomial.rename Subtype.val H₀ := by rw [h1']
      _ = F - swapAux L i F := hH₀
      _ = D * dividedDiff i F := (dividedDiff_spec i F).symm
  exact mul_left_cancel₀ (auxVar_sub_ne_zero h1) key

/-! ### The braid operator and its inverse -/

/-- A scalar of `𝕜` read in the total space: the doubly constant polynomial. -/
noncomputable def scal (x : L) : Total L := MvPolynomial.C (MvPolynomial.C x)

theorem scal_eq_algebraMap (x : L) : (scal x : Total L) = algebraMap L (Total L) x := rfl

@[simp] theorem scal_add (x y : L) : (scal (x + y) : Total L) = scal x + scal y := by
  simp [scal]

@[simp] theorem scal_mul (x y : L) : (scal (x * y) : Total L) = scal x * scal y := by
  simp [scal]

@[simp] theorem scal_one : (scal (1 : L) : Total L) = 1 := by simp [scal]

@[simp] theorem scal_zero : (scal (0 : L) : Total L) = 0 := by simp [scal]

@[simp] theorem scal_neg (x : L) : (scal (-x) : Total L) = -scal x := by simp [scal]

@[simp] theorem scal_sub (x y : L) : (scal (x - y) : Total L) = scal x - scal y := by
  simp [scal]

/-- `s_i` fixes a scalar. -/
@[simp] theorem swapAux_scal (i : ℕ) (x : L) : swapAux L i (scal x) = scal x := by
  rw [scal, swapAux_C]

/-- `∂_i` commutes with a scalar. -/
theorem dividedDiff_scal_mul (i : ℕ) (x : L) (F : Total L) :
    dividedDiff i (scal x * F) = scal x * dividedDiff i F :=
  dividedDiff_C_mul i _ F

/-- `s_i` negates `y_{i+1} - y_i`. -/
theorem swapAux_sub (i : ℕ) :
    swapAux L i (MvPolynomial.X i - MvPolynomial.X (i - 1))
      = -(MvPolynomial.X i - MvPolynomial.X (i - 1) : Total L) := by
  rw [map_sub, swapAux_X, swapAux_X, Equiv.swap_apply_right, Equiv.swap_apply_left]
  ring

/-- **`HJO.Sweep.swapAux_dividedDiff`: `∂_i F` is symmetric in `y_i` and `y_{i+1}`.**
`s_i(∂_i F) = ∂_i F`. The index-`0` corner is handled by the case split below: `∂_0` is read at
`y_0 = y_1` by `HJO.Sweep.auxVar`'s convention, where the statement is trivial. -/
@[hjo "lem_dem_divided_symmetric", hjo "lem_cm_divided_symmetric"]
theorem swapAux_dividedDiff (i : ℕ) (F : Total L) :
    swapAux L i (dividedDiff i F) = dividedDiff i F := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [dividedDiff_zero_index, map_zero]
  refine mul_left_cancel₀ (auxVar_sub_ne_zero hi) ?_
  have hD := dividedDiff_spec i F
  have h := congrArg (swapAux L i) hD
  rw [map_mul, swapAux_sub, map_sub, swapAux_swapAux] at h
  linear_combination -h - hD

/-- **`∂_i` is antisymmetric under `s_i`.** -/
theorem dividedDiff_swapAux (i : ℕ) (F : Total L) :
    dividedDiff i (swapAux L i F) = -dividedDiff i F := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [dividedDiff_zero_index, dividedDiff_zero_index, neg_zero]
  refine (dividedDiff_unique hi ?_).symm
  rw [swapAux_swapAux, mul_neg, dividedDiff_spec]
  ring

/-- **`∂_i(y_i ∂_i F) = -∂_i F`.** The one further identity the Hecke relation needs: `∂_i F` is
`s_i`-symmetric, so multiplying it by `y_i` and differencing divides out. -/
theorem dividedDiff_auxVar_mul (i : ℕ) (F : Total L) :
    dividedDiff i (auxVar i * dividedDiff i F) = -dividedDiff i F := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [dividedDiff_zero_index]
  refine (dividedDiff_unique hi ?_).symm
  rw [map_mul, swapAux_dividedDiff, auxVar, swapAux_X, Equiv.swap_apply_left]
  ring

/-- **The braid operator `T_i`.** `HJO.Sweep.braid`:
`T_i F = s_i F + (q-1) y_i ∂_i F`, a `Λ`-linear endomorphism of the total space. It is
Mellit's (§3.2) `((q-1)y_iF + (y_{i+1}-qy_i)s_iF)/(y_{i+1}-y_i)` rewritten into the form above,
which by `dividedDiff_mem_piece` visibly lands in `V_k`. The unread index `0` gives the identity.

The same formula is often read with a larger codomain: `T_i` as a map from `V_k` to
`Λ ⊗_𝕜 𝕜(y_1, …, y_k)`, the ring in which the quotient `∂_i` visibly makes sense before one knows
it is polynomial. Here `∂_i` is taken in the polynomial ring itself — `dividedDiff`, pinned by
`dividedDiff_spec` — so the value is an element of the total space, and `braid_mem_piece` improves
the codomain to `V_k`; the stronger codomain is what is proved. -/
@[hjo "def_sweep_braid", hjo "def_cm_demazure"]
noncomputable def braid (q : L) (i : ℕ) : Total L →ₗ[Sym.Lambda L] Total L :=
  (swapAux L i).toLinearMap +
    LinearMap.mulLeft (Sym.Lambda L) (scal (q - 1) * auxVar i) ∘ₗ dividedDiffₗ i

@[hjo "def_cm_demazure"]
theorem braid_apply (q : L) (i : ℕ) (F : Total L) :
    braid q i F = swapAux L i F + scal (q - 1) * auxVar i * dividedDiff i F := by
  simp only [braid, LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.mulLeft_apply, dividedDiffₗ_apply, AlgEquiv.toLinearMap_apply, mul_assoc]

/-- At the unread index `0` the braid operator is the identity: `s_0` is and `∂_0` vanishes. -/
theorem braid_zero_index (q : L) (F : Total L) : braid q 0 F = F := by
  rw [braid_apply, swapAux_zero, dividedDiff_zero_index, mul_zero, add_zero]

/-- `T_i` commutes with a scalar, being `Λ`-linear. -/
theorem braid_scal_mul (q : L) (i : ℕ) (x : L) (F : Total L) :
    braid q i (scal x * F) = scal x * braid q i F := by
  have h := (braid q i).map_smul (MvPolynomial.C x : Sym.Lambda L) F
  simpa [Algebra.smul_def, MvPolynomial.algebraMap_eq, scal] using h

/-- **The Hecke relation `T_i^2 = (1-q)T_i + q`.** This is the relation the proof of
`HJO.Sweep.isBraidSystem_braidEnd` uses to invert `T_i`: it writes it as `(T_i - 1)(T_i + q) = 0`.
It follows by expansion from `dividedDiff_spec`, `swapAux_dividedDiff`, `dividedDiff_swapAux` and
`dividedDiff_auxVar_mul`. -/
@[hjo "lem_cm_demazure_quadratic"]
theorem braid_braid_apply (q : L) (i : ℕ) (F : Total L) :
    braid q i (braid q i F) = scal (1 - q) * braid q i F + scal q * F := by
  have hD : (MvPolynomial.X i - MvPolynomial.X (i - 1) : Total L) * dividedDiff i F
      = F - swapAux L i F := dividedDiff_spec i F
  have hy : (auxVar i : Total L) = MvPolynomial.X (i - 1) := rfl
  have hsy : swapAux L i (auxVar i) = (MvPolynomial.X i : Total L) := by
    rw [hy, swapAux_X, Equiv.swap_apply_left]
  have hkey : dividedDiff i (scal (q - 1) * auxVar i * dividedDiff i F)
      = -(scal (q - 1) * dividedDiff i F) := by
    rw [mul_assoc, dividedDiff_scal_mul, dividedDiff_auxVar_mul, mul_neg]
  rw [braid_apply, braid_apply, map_add, swapAux_swapAux, map_mul, map_mul,
    swapAux_scal, hsy, swapAux_dividedDiff, dividedDiff_add, dividedDiff_swapAux,
    hkey]
  have h1 : (scal (1 - q) : Total L) = -scal (q - 1) := by
    rw [show (1 : L) - q = -(q - 1) by ring, scal_neg]
  have h2 : (scal q : Total L) = 1 + scal (q - 1) := by
    rw [← scal_one (L := L), ← scal_add]
    congr 1
    ring
  rw [h1, h2, hy]
  linear_combination (scal (q - 1) : Total L) * hD

/-- **`T_i` is an endomorphism of `V_k`** for `1 ≤ i ≤ k - 1`, which is the domain and codomain
of Mellit's definition, and an improvement on the larger codomain `Λ ⊗_𝕜 𝕜(y_1, …, y_k)`.
This is the remark that expanding
`(q-1)y_i(F - s_iF) + (y_{i+1}-y_i)s_iF` gives the form above, which by
`HJO.Sweep.dividedDiff_mem_piece` visibly lands in `V_k`, read on this presentation: `s_i F`
is in `V_k` by `swapAux_mem_piece`, `∂_i F` by `dividedDiff_mem_piece`, `y_i` by `auxVar_mem_piece`
since `i ≤ k`, and `V_k` is a subalgebra. -/
@[hjo "def_cm_demazure", hjo "lem_cm_demazure_poly"]
theorem braid_mem_piece (q : L) {i k : ℕ} (h1 : 1 ≤ i) (hik : i < k) {F : Total L}
    (hF : F ∈ piece L k) : braid q i F ∈ piece L k := by
  rw [braid_apply]
  refine add_mem (swapAux_mem_piece h1 hik hF) (mul_mem (mul_mem ?_ ?_) ?_)
  · have hs : (scal (q - 1) : Total L)
        = algebraMap (Sym.Lambda L) (Total L) (MvPolynomial.C (q - 1)) := rfl
    rw [hs]
    exact (piece L k).algebraMap_mem _
  · exact auxVar_mem_piece h1 hik.le
  · exact dividedDiff_mem_piece h1 hik hF

/-- **The inverse of the braid operator.** The proof of `HJO.Sweep.isBraidSystem_braidEnd`
exhibits it: `T_i^{-1} = (T_i + (q-1))/q`, which is an inverse because `(T_i - 1)(T_i + q) = 0`. -/
noncomputable def braidInv (q : L) (i : ℕ) : Total L →ₗ[Sym.Lambda L] Total L :=
  LinearMap.mulLeft (Sym.Lambda L) (scal q⁻¹) ∘ₗ
    (braid q i + LinearMap.mulLeft (Sym.Lambda L) (scal (q - 1)))

theorem braidInv_apply (q : L) (i : ℕ) (F : Total L) :
    braidInv q i F = scal q⁻¹ * (braid q i F + scal (q - 1) * F) := by
  simp only [braidInv, LinearMap.coe_comp, Function.comp_apply, LinearMap.add_apply,
    LinearMap.mulLeft_apply]

/-- **`T_i` is invertible.** Half of `HJO.Sweep.isBraidSystem_braidEnd`, and the half the
descending trains and `HJO.Sweep.zop` consume: `T_i^{-1} = (T_i + (q-1))/q` is a two-sided inverse
as soon as `q ≠ 0`. -/
@[hjo "lem_cm_demazure_invertible"]
theorem braid_braidInv (q : L) (hq : q ≠ 0) (i : ℕ) (F : Total L) :
    braid q i (braidInv q i F) = F := by
  have hqi : (scal q⁻¹ : Total L) * scal q = 1 := by
    rw [← scal_mul, inv_mul_cancel₀ hq, scal_one]
  have hq' : (scal (1 - q) : Total L) + scal (q - 1) = 0 := by
    rw [← scal_add]; norm_num
  rw [braidInv_apply, braid_scal_mul, map_add, braid_scal_mul, braid_braid_apply]
  linear_combination (scal q⁻¹ * braid q i F : Total L) * hq' + F * hqi

theorem braidInv_braid (q : L) (hq : q ≠ 0) (i : ℕ) (F : Total L) :
    braidInv q i (braid q i F) = F := by
  have hqi : (scal q⁻¹ : Total L) * scal q = 1 := by
    rw [← scal_mul, inv_mul_cancel₀ hq, scal_one]
  have hq' : (scal (1 - q) : Total L) + scal (q - 1) = 0 := by
    rw [← scal_add]; norm_num
  rw [braidInv_apply, braid_braid_apply]
  linear_combination (scal q⁻¹ * braid q i F : Total L) * hq' + F * hqi

end Field

/-! ### The two virtual-alphabet substitutions, and the operators built from them

Everything here also needs `ℚ ⊆ 𝕜`, since the elementary symmetric functions `d_-` pairs against
are defined by Newton's identities. -/

section Operators

variable {L : Type*} [Field L]

/-- **Adding the letter `(q-1)y_i`.** `HJO.Sweep.qshift`: the `𝕜[y]`-algebra
endomorphism `τ_{k,i}` of `V_k` with `τ_{k,i}(p_r) = p_r + (q^r - 1) y_i^r` for every `r ≥ 1`,
Mellit's `F[X + (q-1)y_i]`.

**The exponent is `q^r - 1` and not `(q-1)^r`**, and this is not
cosmetic: Mellit's `(q-1)y_i` is the *virtual* alphabet `qy_i - y_i`, in whose λ-ring
`p_r(q - 1) = q^r - 1`. Under the monomial reading `p_r ↦ p_r + (q-1)^r y_i^r` two statements below
are false, `HJO.Sweep.dminus_dminus_braid` at `k = 2` on `F = y_1^2` and `HJO.Sym.bop_pair_antisymm`
at `m = n = 1` on `f = 1`.

On the total space the definition does not depend on `k`: the `τ_{k,i}` is the
restriction of this one endomorphism to `V_k`. -/
@[hjo "def_cm_qshift"]
noncomputable def qshift (q : L) (i : ℕ) : Total L →ₐ[L] Total L :=
  MvPolynomial.aevalTower
    (MvPolynomial.aeval fun j : ℕ =>
      (MvPolynomial.C (MvPolynomial.X j) + scal (q ^ (j + 1) - 1) * auxVar i ^ (j + 1) : Total L))
    MvPolynomial.X

/-- **Subtracting the letter `(q-1)y_i`.** `HJO.Sweep.qshiftNeg`: the `𝕜[y]`-algebra
endomorphism `τ^-_{k,i}` with `τ^-_{k,i}(p_r) = p_r - (q^r - 1) y_i^r`, Mellit's
`F[X - (q-1)y_i]`. The virtual reading of the letter is the one recorded on `qshift`. -/
@[hjo "def_cm_qshift_neg"]
noncomputable def qshiftNeg (q : L) (i : ℕ) : Total L →ₐ[L] Total L :=
  MvPolynomial.aevalTower
    (MvPolynomial.aeval fun j : ℕ =>
      (MvPolynomial.C (MvPolynomial.X j) - scal (q ^ (j + 1) - 1) * auxVar i ^ (j + 1) : Total L))
    MvPolynomial.X

theorem qshift_powerSum (q : L) (i r : ℕ) :
    qshift q i (MvPolynomial.C (Sym.powerSum L (r + 1)))
      = MvPolynomial.C (Sym.powerSum L (r + 1)) + scal (q ^ (r + 1) - 1) * auxVar i ^ (r + 1) := by
  simp [qshift, Sym.powerSum]

theorem qshiftNeg_powerSum (q : L) (i r : ℕ) :
    qshiftNeg q i (MvPolynomial.C (Sym.powerSum L (r + 1)))
      = MvPolynomial.C (Sym.powerSum L (r + 1)) - scal (q ^ (r + 1) - 1) * auxVar i ^ (r + 1) := by
  simp [qshiftNeg, Sym.powerSum]

theorem qshift_auxVar (q : L) (i j : ℕ) :
    qshift q i (MvPolynomial.X j : Total L) = MvPolynomial.X j := by
  simp [qshift]

theorem qshiftNeg_auxVar (q : L) (i j : ℕ) :
    qshiftNeg q i (MvPolynomial.X j : Total L) = MvPolynomial.X j := by
  simp [qshiftNeg]

/-! #### The braid system on the total space -/

/-- The braid operator as an `L`-linear endomorphism, the shape in which the trains and the
operators below compose it. -/
noncomputable def braidEnd (q : L) (i : ℕ) : Module.End L (Total L) :=
  (braid q i).restrictScalars L

/-- The inverse braid operator as an `L`-linear endomorphism. -/
noncomputable def braidInvEnd (q : L) (i : ℕ) : Module.End L (Total L) :=
  (braidInv q i).restrictScalars L

/-- **`T_i T_i^{-1} = T_i^{-1} T_i = 1` in the endomorphism monoid.** The invertibility half of
`HJO.Sweep.isBraidSystem_braidEnd`, in the form `HJO.Braid.IsBraidSystem` asks for. -/
theorem braidEnd_mul_braidInvEnd (q : L) (hq : q ≠ 0) (i : ℕ) :
    braidEnd q i * braidInvEnd q i = 1 := by
  refine LinearMap.ext fun F => ?_
  simpa [braidEnd, braidInvEnd] using braid_braidInv q hq i F

theorem braidInvEnd_mul_braidEnd (q : L) (hq : q ≠ 0) (i : ℕ) :
    braidInvEnd q i * braidEnd q i = 1 := by
  refine LinearMap.ext fun F => ?_
  simpa [braidEnd, braidInvEnd] using braidInv_braid q hq i F

/-- The ascending train `T_{1↗k} = T_1 T_2 ⋯ T_{k-1}` of the braid operators on the total space. -/
noncomputable def trainUpEnd (q : L) (a b : ℕ) : Module.End L (Total L) :=
  Braid.trainUp (braidEnd q) (braidInvEnd q) a b

/-- The descending train `T_{k↘1} = T_{k-1} ⋯ T_1` of the braid operators on the total space. -/
noncomputable def trainDownEnd (q : L) (a b : ℕ) : Module.End L (Total L) :=
  Braid.trainDown (braidEnd q) (braidInvEnd q) a b

/-! #### The lowering, raising and corner operators -/

section Newton

variable [Algebra ℚ L]

/-- The coefficient extraction that `d_-` performs: on the `Λ`-basis of `y`-monomials it sends
`y^d` to `(-1)^{d_j} e_{d_j}` times `y^d` with the exponent of `y_{j+1}` deleted. This is the
coefficient of `y_{j+1}^0` in the product of `y^d` with `∑_{n ≥ 0} (-1)^n e_n y_{j+1}^{-n}`. -/
noncomputable def lowerCoeff (L : Type*) [Field L] [Algebra ℚ L] (j : ℕ) :
    Total L →ₗ[Sym.Lambda L] Total L :=
  (MvPolynomial.basisMonomials ℕ (Sym.Lambda L)).constr (Sym.Lambda L) fun d =>
    (-1 : Total L) ^ d j * MvPolynomial.C (Sym.elemSymm L (d j)) *
      MvPolynomial.monomial (Finsupp.erase j d) 1

/-- `lowerCoeff` on a `y`-monomial: the coefficient extraction, read off. -/
theorem lowerCoeff_monomial (j : ℕ) (d : ℕ →₀ ℕ) :
    lowerCoeff L j (MvPolynomial.monomial d 1)
      = (-1 : Total L) ^ d j * MvPolynomial.C (Sym.elemSymm L (d j)) *
        MvPolynomial.monomial (Finsupp.erase j d) 1 := by
  have hb : (MvPolynomial.basisMonomials ℕ (Sym.Lambda L)) d
      = MvPolynomial.monomial d 1 := congrFun (MvPolynomial.coe_basisMonomials ℕ _) d
  rw [lowerCoeff, ← hb]
  exact Module.Basis.constr_basis _ _ _ _

/-- **The lowering operator `d_-`.** `HJO.Sweep.dminus`: for `k ≥ 1`, the
`𝕜`-linear map from `V_k` to `V_{k-1}` sending `F` to the coefficient of `y_k^0` in
`τ^-_{k,k}(F) ∑_{n ≥ 0} (-1)^n e_n y_k^{-n}`.

Expanded on the `y`-monomials that is `∑_m (-1)^m e_m A_m` where `τ^-_{k,k}(F) = ∑_m A_m y_k^m`,
which is what `lowerCoeff` computes; the series `∑_n (-1)^n e_n y_k^{-n}` is Mellit's
`Exp[-y_k^{-1}X]` and only finitely many of its terms meet any given power of `y_k`, since
`τ^-_{k,k}(F)` is a polynomial.

That expanded form `∑_j (-1)^j e_j F_j` is verbatim `HJO.Sweep.dminus`, the
*modified* lowering operator `d^♭_-`, which is therefore this same declaration and not a second
one: the operator has two spellings, a coefficient extraction against
`Exp[-y_k^{-1}X]` and the expanded sum, and the
two spellings agree. It is `HJO.Sweep.dminusCM` that differs — that one pairs `F_j` with `e_{j+1}`
rather than `e_j`, and is a different operator with its own declaration. -/
@[hjo "def_sweep_dminus", hjo "def_vmod_dminus_mod"]
noncomputable def dminus (q : L) (k : ℕ) : Module.End L (Total L) :=
  (lowerCoeff L (k - 1)).restrictScalars L ∘ₗ (qshiftNeg q k).toLinearMap

/-- **`d_-(y_k^m) = (-1)^m e_m`**, the lowering operator read on a power of
the last variable: `τ^-_{k,k}` fixes the auxiliary variables, so the coefficient of `y_k^0` in
`y_k^m ∑_n (-1)^n e_n y_k^{-n}` is the single term `n = m`. -/
theorem dminus_auxVar_pow (q : L) (k m : ℕ) :
    dminus q (k + 1) ((auxVar (k + 1) : Total L) ^ m)
      = (-1 : Total L) ^ m * MvPolynomial.C (Sym.elemSymm L m) := by
  have hav : (auxVar (k + 1) : Total L) = MvPolynomial.X k := by
    rw [auxVar, Nat.add_sub_cancel]
  have hpow : ((MvPolynomial.X k : Total L)) ^ m = MvPolynomial.monomial (Finsupp.single k m) 1 :=
    MvPolynomial.X_pow_eq_monomial
  rw [hav, dminus, LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
    LinearMap.restrictScalars_apply, map_pow, qshiftNeg_auxVar, hpow, Nat.add_sub_cancel,
    lowerCoeff_monomial]
  simp

/-- **The raising operator `d_+`.** `HJO.Sweep.dplus`: for `k ≥ 0`, the `𝕜`-linear
map from `V_k` to `V_{k+1}` with `d_+ F = -T_1 T_2 ⋯ T_k (y_{k+1} τ_{k+1,k+1}(F))`. The word
`T_1 ⋯ T_k` is the ascending train `T_{1↗k+1}`. -/
@[hjo "def_sweep_dplus"]
noncomputable def dplus (q : L) (k : ℕ) : Module.End L (Total L) :=
  -(trainUpEnd q 1 (k + 1) ∘ₗ
    (LinearMap.mulLeft L (auxVar (k + 1)) ∘ₗ (qshift q (k + 1)).toLinearMap))

/-- **The corner operator `Δ`.** `HJO.Sweep.corner`: for `k ≥ 1` the `𝕜`-linear
endomorphism `(d_-d_+ - d_+d_-)/(q-1)` of `V_k`, and for `k = 0` the endomorphism
`d_-d_+/(q-1)`. The indices record which graded piece each factor is read on: on `V_k` the
composite `d_-d_+` is `d_-` of index `k+1` after `d_+` of index `k`, and `d_+d_-` is `d_+` of index
`k-1` after `d_-` of index `k`. -/
@[hjo "def_sweep_corner"]
noncomputable def corner (q : L) (k : ℕ) : Module.End L (Total L) :=
  (q - 1)⁻¹ • (if k = 0 then dminus q 1 * dplus q 0
    else dminus q (k + 1) * dplus q k - dplus q (k - 1) * dminus q k)

/-! #### The conjugate side: the cyclic shift, `d^*_+` and the `z_i` -/

/-- **The cyclic shift of the letters.** `HJO.Sweep.cycleShift`: for `k ≥ 0`,
`cy_{k+1}` is the `Λ`-algebra automorphism of `V_{k+1}` with `cy_{k+1}(y_i) = y_{i+1}` for
`1 ≤ i ≤ k` and `cy_{k+1}(y_{k+1}) = u y_1`. On the total space it is extended by the identity on
the variables beyond `y_{k+1}`, a convention no statement below reads: only the restriction to
`V_{k+1}` is the map.

This one automorphism serves both as `γ_k` inside the starred raising operator and as
`γ_{k+1}` on its own, so that `d^*_+` has a single definition.
It is named once here, after its codomain `V_{k+1}`. -/
@[hjo "def_mellit_gamma"]
noncomputable def cycleShift (u : L) (k : ℕ) : Total L →ₐ[Sym.Lambda L] Total L :=
  MvPolynomial.aeval fun j : ℕ =>
    if j < k then (MvPolynomial.X (j + 1) : Total L)
    else if j = k then scal u * MvPolynomial.X 0 else MvPolynomial.X j

/-- **The conjugate raising operator `d^*_+`.**
`HJO.Sweep.dplusStar`: for `k ≥ 0`, the `𝕜`-linear map from `V_k` to `V_{k+1}` with
`d^*_+ F = cy_{k+1}(τ_{k+1,k+1}(F))`.

**One operator, two settings.** The `d^*_+` of the Dyck path algebra of Carlsson and Mellit and
the `d^*_+` in the setting of Mellit's Section 3.2 have the same formula, so both are this one
constant. -/
@[hjo "def_cm_dplus_star"]
noncomputable def dplusStar (q u : L) (k : ℕ) : Module.End L (Total L) :=
  (cycleShift u k).toLinearMap.restrictScalars L ∘ₗ (qshift q (k + 1)).toLinearMap

omit [Algebra ℚ L] in
/-- **`cy_{k+1}` shifts the letters:** `cy_{k+1}(y_i) = y_{i+1}` for `1 ≤ i ≤ k`. -/
theorem cycleShift_auxVar (u : L) {i k : ℕ} (h1 : 1 ≤ i) (hk : i ≤ k) :
    cycleShift u k (auxVar i : Total L) = auxVar (i + 1) := by
  have h : i - 1 < k := by omega
  have h2 : i + 1 - 1 = i := by omega
  have h3 : i - 1 + 1 = i := by omega
  rw [auxVar, auxVar, h2, cycleShift, MvPolynomial.aeval_X]
  simp [h, h3]

omit [Algebra ℚ L] in
/-- **`cy_{k+1}` wraps the last letter round:** `cy_{k+1}(y_{k+1}) = u y_1`. -/
theorem cycleShift_auxVar_last (u : L) (k : ℕ) :
    cycleShift u k (auxVar (k + 1) : Total L) = scal u * auxVar 1 := by
  rw [auxVar, auxVar, Nat.add_sub_cancel, cycleShift, MvPolynomial.aeval_X]
  simp

omit [Algebra ℚ L] in
/-- **`d^*_+ F = cy_{k+1}(τ_{k+1,k+1}(F))`**, the formula read off. -/
theorem dplusStar_apply (q u : L) (k : ℕ) (F : Total L) :
    dplusStar q u k F = cycleShift u k (qshift q (k + 1) F) := rfl

omit [Algebra ℚ L] in
/-- **`d_+ F = -T_1 T_2 ⋯ T_k (y_{k+1} τ_{k+1,k+1}(F))`**, the formula read off. -/
theorem dplus_apply (q : L) (k : ℕ) (F : Total L) :
    dplus q k F = -trainUpEnd q 1 (k + 1) (auxVar (k + 1) * qshift q (k + 1) F) := rfl

/-- **`d_- F` is `lowerCoeff` of `τ^-_{k,k}(F)`**, the formula read off. -/
theorem dminus_apply (q : L) (k : ℕ) (F : Total L) :
    dminus q k F = lowerCoeff L (k - 1) (qshiftNeg q k F) := rfl

/-- **`Δ = (d_-d_+ - d_+d_-)/(q-1)` on `V_k` for `k ≥ 1`**, the formula read off. -/
theorem corner_of_pos (q : L) {k : ℕ} (hk : k ≠ 0) :
    corner q k = (q - 1)⁻¹ • (dminus q (k + 1) * dplus q k - dplus q (k - 1) * dminus q k) := by
  rw [corner]
  simp [hk]

/-- **`Δ = d_-d_+/(q-1)` on `V_0`**, the second clause read off. -/
theorem corner_zero (q : L) : corner q 0 = (q - 1)⁻¹ • (dminus q 1 * dplus q 0) := by
  rw [corner]
  simp

/-- **`z_1` on `V_k`**, the `q^k/(1-q) (d^*_+ d_- - d_- d^*_+) T^*_{k↘1}` of
`HJO.Sweep.zop`. The indices again record the graded piece each factor is read on.

Mellit's `T^*_{k↘1}` is the word `T_{k-1}^{-1} T_{k-2}^{-1} ⋯ T_1^{-1}`, which is
`trainUpEnd q k 1`: the ascending train read at `a = k > b = 1`, by
`HJO.Braid.trainUp_inv_eq_trainDown`. A starred Mellit symbol is the *other*
train, not the inverse of the same one — the reverse word `T_1^{-1} ⋯ T_{k-1}^{-1}` is
`HJO.Sweep.zopOne`, and `HJO.Sweep.zopOne_mul_braidEnd` shows it does not satisfy the relation
`HJO.Braid.BraidMonoid` demands of `z_1`. -/
noncomputable def zopOneStar (q u : L) (k : ℕ) : Module.End L (Total L) :=
  (q ^ k / (1 - q)) •
    ((dplusStar q u (k - 1) * dminus q k - dminus q (k + 1) * dplusStar q u k) *
      trainUpEnd q k 1)

/-- **The wrong-word `z_1`**, kept only as the witness that the word is load-bearing: the operator
`q^k/(1-q) (d^*_+ d_- - d_- d^*_+) T_{1↘k}`, whose train is the descending train `T_{1↘k}` that
`HJO.Braid.trainDown` gives at `a = 1 < b = k`, the word `T_1^{-1} T_2^{-1} ⋯ T_{k-1}^{-1}`.

This is the reverse of the word `HJO.Sweep.zop` asks for, and misreading Mellit's `T^*_{k↘1}` as
`T^{-1}_{k↘1}` gives this operator instead of
`HJO.Sweep.zopOneStar`. The difference is not a variant spelling:
`HJO.Sweep.zopOne_mul_braidEnd` proves `z_1T_j = T_{j+2}z_1` for this operator, because here the
shift of the commutator and the shift of the train add rather than cancel. Nothing in the
library reads it except that theorem. -/
noncomputable def zopOne (q u : L) (k : ℕ) : Module.End L (Total L) :=
  (q ^ k / (1 - q)) •
    ((dplusStar q u (k - 1) * dminus q k - dminus q (k + 1) * dplusStar q u k) *
      trainDownEnd q 1 k)

/-- **The conjugate commuting operators `z_i`.** `HJO.Sweep.zop`: for `k ≥ 1`,
`z_1 = q^k/(1-q) (d^*_+ d_- - d_- d^*_+) T^*_{k↘1}` on `V_k`, and `z_{i+1} = q^{-1} T_i z_i T_i`
for `1 ≤ i ≤ k-1`.

`T^*_{k↘1}` is `trainUpEnd q k 1`, the word `T_{k-1}^{-1} ⋯ T_1^{-1}`; the inverses exist by
`braidEnd_mul_braidInvEnd`, which is the invertibility half of `HJO.Sweep.isBraidSystem_braidEnd`.
The index `0` is not read and is sent to `0`. -/
@[hjo "def_mellit_z"]
noncomputable def zop (q u : L) (k : ℕ) : ℕ → Module.End L (Total L)
  | 0 => 0
  | 1 => zopOneStar q u k
  | (i + 2) => q⁻¹ • (braidEnd q (i + 1) * zop q u k (i + 1) * braidEnd q (i + 1))

/-- **`z_1` is the displayed operator.** -/
theorem zop_one (q u : L) (k : ℕ) : zop q u k 1 = zopOneStar q u k := rfl

/-- **`z_{i+1} = q^{-1} T_i z_i T_i`**, the recursion read off. -/
theorem zop_succ (q u : L) (k i : ℕ) :
    zop q u k (i + 2) = q⁻¹ • (braidEnd q (i + 1) * zop q u k (i + 1) * braidEnd q (i + 1)) :=
  rfl

/-- **The slope operator `Ξ_{m,n}`.** `HJO.Sweep.slopeOperator`: for coprime
`m, n ≥ 1` and `k ≥ 1`, the endomorphism of `V_k` obtained from the word `β_{m,n}` by replacing each
letter `y` by multiplication by `-y_1` and each letter `z` by `(qu)^{-1} z_1`, and composing the
factors in the order in which they are written.

The order is load-bearing and is the one `HJO.Mellit.slopeWord` fixes: its head is `λ(m+n-2)` and
its last letter `λ(1)`, and `List.prod` in `Module.End` composes so that the head is the outermost
factor — which is "the order in which they are written". This is the image of `β_{m,n}` under the
rank-one case of `HJO.Sweep.braidRep`, in which no `T_i` occurs and no square root of `q` is needed,
which is why it can be written here without the braid monoid. -/
@[hjo "def_mellit_slope_operator"]
noncomputable def slopeOperator (q u : L) (k m n : ℕ) : Module.End L (Total L) :=
  ((Mellit.slopeWord m n).map fun l =>
    match l with
    | Mellit.SlopeLetter.y => -LinearMap.mulLeft L (auxVar 1 : Total L)
    | Mellit.SlopeLetter.z => (q * u)⁻¹ • zop q u k 1).prod

/-- At `(m, n) = (1, 1)` the slope word is empty and the slope operator is the identity. -/
theorem slopeOperator_one_one (q u : L) (k : ℕ) : slopeOperator q u k 1 1 = 1 := by
  simp [slopeOperator, Mellit.slopeWord]

end Newton

end Operators


end HJO.Sweep
