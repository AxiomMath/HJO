/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.LhsOpDefs
public import HJO.Shuffle.LhsOpIntertwiner

/-! # At the base slope the conjugated left-hand operator is a multiplication

Let `∇` be the Macdonald conjugator normalised by `∇1 = 1`. At the base slope `(1,1)` the
operator `lhsOp 1 1 α : f ↦ ct(d_-^ℓ G_ℓ ⋯ G_1(Cf))` satisfies `lhsOp 1 1 α ∘ ∇ = ∇ ∘ (g·)` for
some `g ∈ Λ`, namely `g = ct(d_-^ℓ W_ℓ ⋯ W_1(1))` for the word `W` below.

The proof is Mellit's (§3.7). Mellit's `N` fixes `d_-`, `d^*_+` and the loops, and sends `d_+`
out of `V_k` to `(qu)^{-1}z_1d_+ = -q^ky_1d^*_+`; it induces `∇'` on `V_* = ⨁_k V_k` with
`∇'L = N(L)∇'`, and `∇' = ∇` on `V_0`. So the two `(1,1)` letters are images under `N`:
`Ω(1;1,1) = -y_1d^*_+ = N(q^{-k}d_+)` out of `V_k`, and, on `V_{k+1}`,
`Ω(2;1,1) = -y_1z_1 = N((q-1)^{-1}(d_-d_+ - q\,d_+d_-)T^*_{k+1↘1})`, using
`z_1d_+ = -uq^{j+1}y_1d^*_+` twice, `d_-y_1 = y_1d_-` and the definition of `z_1`. Hence
`∇' ∘ W = G ∘ ∇'` for the stage word `G` and a word `W` in `d_-`, `d_+` and the loops
only. Every such word is linear for
the twisted action `f ⋆ F = f[X + (q-1)(y_1 + ⋯ + y_k)]·F` of `Λ` on `V_k`, which on `V_0` is
multiplication; so `ct ∘ d_-^ℓ ∘ W ∘ C` is multiplication by its value at `1`.

## Main definitions

* `HJO.Mellit.LhsDesign.baseMulShift`: the twisted action's alphabet shift.
* `HJO.Mellit.LhsDesign.baseMulTwo`, `HJO.Mellit.LhsDesign.baseMulStage`,
  `HJO.Mellit.LhsDesign.baseMulWord`: the preimages under `N` of `Ω(2;1,1)`, of the stage
  `G_{k+1,A}` and of the stage word.

## Main results

* `HJO.Mellit.LhsDesign.replTwoTotal_one_one_eq`, `HJO.Mellit.LhsDesign.replOneTotal_one_one_eq`:
  the two `(1,1)` letters as images under `N`.
* `HJO.Mellit.LhsDesign.baseMulIntertwines_of_isNablaPrime`: Mellit's `∇'`
  (`HJO.Sweep.IsNablaPrime`, which exists by `HJO.Sweep.exists_isNablaPrime_param`) satisfies
  these relations.
* `HJO.Mellit.LhsDesign.lhsOp_one_one_of_intertwines`: the conjugated operator is a
  multiplication, given any family with the relations of `∇'` restricting to `∇` on `V_0`.
* `HJO.Mellit.LhsDesign.lhsOp_one_one_isMul`: the statement at the standing field.

## Implementation notes

The twisted linearity holds on the whole total space, not only on the pieces, so only the
intertwining needs piece membership. The positivity of the parts of `α` is not used.

## References

* [A. Mellit, *Toric braids and (m,n)-parking functions*][mellit2016], §3.7.
-/

@[expose] public section

namespace HJO.Mellit.LhsDesign

open HJO.Sym HJO.Sweep HJO.Ascent MvPolynomial

/-! ### The twisted `Λ`-action on the total space -/

section Twist

variable {L : Type*} [Field L]

/-- The alphabet shift `f ↦ f[X + (q-1)(y_1 + ⋯ + y_k)]`, from `Λ` into the total space. -/
noncomputable abbrev baseMulShift (q : L) (k : ℕ) : Sym.Lambda L →ₐ[L] Total L :=
  letterShiftSum (fun j => q ^ (j + 1) - 1) k

/-- On `V_0` the alphabet shift is the inclusion of `Λ` as constants. -/
theorem baseMulShift_zero (q : L) (f : Sym.Lambda L) : baseMulShift q 0 f = C f := by
  have : baseMulShift q 0 = IsScalarTower.toAlgHom L (Sym.Lambda L) (Total L) := by
    refine MvPolynomial.algHom_ext fun j => ?_
    simp [letterShiftSum]
  rw [this]
  rfl

/-- The shift `qshift q (k + 1)` carries the alphabet shift at `k` to the one at `k + 1`. -/
theorem qshift_baseMulShift (q : L) (k : ℕ) (f : Sym.Lambda L) :
    qshift q (k + 1) (baseMulShift q k f) = baseMulShift q (k + 1) f := by
  have key : (qshift q (k + 1)).comp (baseMulShift q k) = baseMulShift q (k + 1) := by
    refine MvPolynomial.algHom_ext fun j => ?_
    simp [letterShiftSum, qshift, scal, Finset.sum_range_succ, auxVar]
    ring
  exact DFunLike.congr_fun key f

/-- The shift `qshiftNeg q (k + 1)` carries the alphabet shift at `k + 1` to the one at `k`. -/
theorem qshiftNeg_baseMulShift (q : L) (k : ℕ) (f : Sym.Lambda L) :
    qshiftNeg q (k + 1) (baseMulShift q (k + 1) f) = baseMulShift q k f := by
  have key : (qshiftNeg q (k + 1)).comp (baseMulShift q (k + 1)) = baseMulShift q k := by
    refine MvPolynomial.algHom_ext fun j => ?_
    simp [letterShiftSum, qshiftNeg, scal, Finset.sum_range_succ, auxVar]
    ring
  exact DFunLike.congr_fun key f

/-- The alphabet shift `f[X + (q-1)(y_1 + ⋯ + y_k)]` lies in `V_k`. -/
theorem baseMulShift_mem_piece (q : L) (k : ℕ) (f : Sym.Lambda L) :
    baseMulShift q k f ∈ piece L k := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]
    exact (piece L k).algebraMap_mem _
  | add p r hp hr =>
    rw [map_add]
    exact add_mem hp hr
  | mul_X p j hp =>
    rw [map_mul]
    refine mul_mem hp ?_
    simp only [letterShiftSum, aeval_X]
    refine add_mem ?_ (mul_mem ?_ (sum_mem fun i hi => pow_mem ?_ _))
    · exact piece_mono (Nat.zero_le k) (C_mem_piece_zero _)
    · exact (piece L k).algebraMap_mem _
    · rw [show (X i : Total L) = auxVar (i + 1) by rw [auxVar, Nat.add_sub_cancel]]
      exact auxVar_mem_piece (by omega) (by simpa using hi)

/-- For `i + 1 ≤ k`, the alphabet shift at `k` is fixed by the transposition `swapAux L i`. -/
theorem swapAux_baseMulShift (q : L) {i k : ℕ} (hik : i + 1 ≤ k) (f : Sym.Lambda L) :
    swapAux L i (baseMulShift q k f) = baseMulShift q k f := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · exact swapAux_zero _
  set A : Total L →ₐ[L] Total L := (swapAux L i).toAlgHom.restrictScalars L
  have hAapp : ∀ G : Total L, A G = swapAux L i G := fun _ => rfl
  have key : A.comp (baseMulShift q k) = baseMulShift q k := by
    refine MvPolynomial.algHom_ext fun j => ?_
    have hsum : swapAux L i (∑ m ∈ Finset.range k, (X m : Total L) ^ (j + 1))
        = ∑ m ∈ Finset.range k, (X m : Total L) ^ (j + 1) := by
      rw [map_sum]
      refine Finset.sum_equiv (Equiv.swap (i - 1) i) (fun m => ?_) (fun m _ => ?_)
      · simp only [Finset.mem_range]
        rcases eq_or_ne m (i - 1) with rfl | h1
        · rw [Equiv.swap_apply_left]
          omega
        rcases eq_or_ne m i with rfl | h2
        · rw [Equiv.swap_apply_right]
          omega
        · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
      · rw [map_pow, swapAux_X]
    simp only [AlgHom.comp_apply, hAapp, letterShiftSum, aeval_X, map_add, map_mul, hsum,
      swapAux_C, swapAux_scal]
  exact DFunLike.congr_fun key f

end Twist

/-! ### Two closure properties of operators on the total space -/

section Closure

variable {L : Type*} [Field L]

/-- An operator `A` carries `V_k` into `V_{k'}` and is intertwined with `A'` by the family `N`:
`N_{k'} ∘ A = A' ∘ N_k` on `V_k`. -/
def BaseMulCarries (N : ℕ → Module.End L (Total L)) (k k' : ℕ) (A A' : Module.End L (Total L)) :
    Prop :=
  ∀ F ∈ piece L k, A F ∈ piece L k' ∧ N k' (A F) = A' (N k F)

/-- An operator `A` is linear for the twisted `Λ`-actions `f ⋆ F = f[X + (q-1)(y_1+⋯+y_k)]·F`
on the source and `f[X + (q-1)(y_1+⋯+y_{k'})]·F` on the target. -/
def BaseMulTwisted (q : L) (k k' : ℕ) (A : Module.End L (Total L)) : Prop :=
  ∀ (f : Sym.Lambda L) (F : Total L), A (baseMulShift q k f * F) = baseMulShift q k' f * A F

namespace BaseMulCarries

variable {N : ℕ → Module.End L (Total L)} {k k' k'' : ℕ} {A A' B B' : Module.End L (Total L)}

/-- Intertwined operators compose: `B * A` is intertwined with `B' * A'`. -/
theorem mul (hA : BaseMulCarries N k k' A A') (hB : BaseMulCarries N k' k'' B B') :
    BaseMulCarries N k k'' (B * A) (B' * A') := fun F hF =>
  ⟨(hB _ (hA F hF).1).1, by
    rw [Module.End.mul_apply, Module.End.mul_apply, (hB _ (hA F hF).1).2, (hA F hF).2]⟩

/-- The sum `A + B` is intertwined with `A' + B'`. -/
theorem add (hA : BaseMulCarries N k k' A A') (hB : BaseMulCarries N k k' B B') :
    BaseMulCarries N k k' (A + B) (A' + B') := fun F hF =>
  ⟨add_mem (hA F hF).1 (hB F hF).1, by
    rw [LinearMap.add_apply, LinearMap.add_apply, map_add, (hA F hF).2, (hB F hF).2]⟩

/-- The scalar multiple `c • A` is intertwined with `c • A'`. -/
theorem smul (c : L) (hA : BaseMulCarries N k k' A A') :
    BaseMulCarries N k k' (c • A) (c • A') := fun F hF =>
  ⟨by
    rw [LinearMap.smul_apply, ← algebraMap_smul (Sym.Lambda L) c]
    exact (piece L k').smul_mem (hA F hF).1 _, by
    rw [LinearMap.smul_apply, LinearMap.smul_apply, map_smul, (hA F hF).2]⟩

/-- The negation `-A` is intertwined with `-A'`. -/
theorem neg (hA : BaseMulCarries N k k' A A') : BaseMulCarries N k k' (-A) (-A') := by
  simpa using hA.smul (-1)

/-- The difference `A - B` is intertwined with `A' - B'`. -/
theorem sub (hA : BaseMulCarries N k k' A A') (hB : BaseMulCarries N k k' B B') :
    BaseMulCarries N k k' (A - B) (A' - B') := by
  simpa [sub_eq_add_neg] using hA.add hB.neg

/-- The identity on `V_k` is intertwined with the identity. -/
theorem one : BaseMulCarries N k k 1 1 :=
  fun _ hF => ⟨hF, rfl⟩

/-- If `A` on `V_k` is intertwined with `A'`, then `A ^ n` is intertwined with `A' ^ n`. -/
theorem pow (hA : BaseMulCarries N k k A A') :
    ∀ n : ℕ, BaseMulCarries N k k (A ^ n) (A' ^ n)
  | 0 => by simpa using (one : BaseMulCarries N k k 1 1)
  | n + 1 => by
    rw [pow_succ, pow_succ]
    exact hA.mul (pow hA n)

end BaseMulCarries

namespace BaseMulTwisted

variable {q : L} {k k' k'' : ℕ} {A B : Module.End L (Total L)}

/-- A composite of twisted-linear operators is twisted-linear. -/
theorem mul (hA : BaseMulTwisted q k k' A) (hB : BaseMulTwisted q k' k'' B) :
    BaseMulTwisted q k k'' (B * A) := fun f F => by
  rw [Module.End.mul_apply, Module.End.mul_apply, hA, hB]

/-- A sum of twisted-linear operators is twisted-linear. -/
theorem add (hA : BaseMulTwisted q k k' A) (hB : BaseMulTwisted q k k' B) :
    BaseMulTwisted q k k' (A + B) := fun f F => by
  rw [LinearMap.add_apply, LinearMap.add_apply, hA, hB, mul_add]

/-- A scalar multiple of a twisted-linear operator is twisted-linear. -/
theorem smul (c : L) (hA : BaseMulTwisted q k k' A) : BaseMulTwisted q k k' (c • A) :=
  fun f F => by rw [LinearMap.smul_apply, LinearMap.smul_apply, hA, mul_smul_comm]

/-- The negation of a twisted-linear operator is twisted-linear. -/
theorem neg (hA : BaseMulTwisted q k k' A) : BaseMulTwisted q k k' (-A) := by
  simpa using hA.smul (-1)

/-- A difference of twisted-linear operators is twisted-linear. -/
theorem sub (hA : BaseMulTwisted q k k' A) (hB : BaseMulTwisted q k k' B) :
    BaseMulTwisted q k k' (A - B) := by
  simpa [sub_eq_add_neg] using hA.add hB.neg

/-- The identity is twisted-linear from `V_k` to `V_k`. -/
theorem one : BaseMulTwisted q k k 1 := fun _ _ => rfl

/-- Every power of a twisted-linear operator from `V_k` to `V_k` is twisted-linear. -/
theorem pow (hA : BaseMulTwisted q k k A) : ∀ n : ℕ, BaseMulTwisted q k k (A ^ n)
  | 0 => by simpa using (one : BaseMulTwisted q k k 1)
  | n + 1 => by
    rw [pow_succ]
    exact hA.mul (pow hA n)

end BaseMulTwisted

/-- A list product of letters each satisfying a property closed under `1` and products. -/
theorem baseMul_prod_of {P : Module.End L (Total L) → Prop} (h1 : P 1)
    (hmul : ∀ A B, P A → P B → P (A * B)) {T : ℕ → Module.End L (Total L)} :
    ∀ l : List ℕ, (∀ i ∈ l, P (T i)) → P ((l.map T).prod)
  | [], _ => by simpa using h1
  | i :: l, h => by
    rw [List.map_cons, List.prod_cons]
    exact hmul _ _ (h i (List.mem_cons_self ..))
      (baseMul_prod_of h1 hmul l fun j hj => h j (List.mem_cons_of_mem i hj))

/-- Both trains satisfy a property closed under `1` and products as soon as every letter of index
below `m` and its inverse do, and the endpoints are at most `m`. -/
theorem baseMul_trains_of {q : L} {m : ℕ} {P : Module.End L (Total L) → Prop} (h1 : P 1)
    (hmul : ∀ A B, P A → P B → P (A * B)) (hT : ∀ i, i < m → P (braidEnd q i))
    (hTi : ∀ i, i < m → P (braidInvEnd q i)) {a b : ℕ} (ha : a ≤ m) (hb : b ≤ m) :
    P (trainUpEnd q a b) ∧ P (trainDownEnd q a b) := by
  rw [trainUpEnd, Braid.trainUp, trainDownEnd, Braid.trainDown]
  constructor <;> split_ifs
  all_goals first
    | exact baseMul_prod_of h1 hmul _ fun i hi => hT i (by
        simp only [List.mem_reverse, List.mem_range'_1] at hi; omega)
    | exact baseMul_prod_of h1 hmul _ fun i hi => hTi i (by
        simp only [List.mem_reverse, List.mem_range'_1] at hi; omega)

/-- `T_i^{-1} = q^{-1}(T_i + (q-1))` as endomorphisms. -/
theorem braidInvEnd_eq (q : L) (i : ℕ) :
    braidInvEnd q i = q⁻¹ • (braidEnd q i + (q - 1) • 1) := by
  refine LinearMap.ext fun F => ?_
  change braidInv q i F = _
  rw [braidInv_apply, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.one_apply, scal_eq_algebraMap, scal_eq_algebraMap,
    ← Algebra.smul_def, ← Algebra.smul_def]
  rfl

end Closure

/-! ### The letters are linear for the twisted action -/

section TwistedLetters

variable {L : Type*} [Field L] {q : L}

/-- For `i < m`, the loop `T_i` is twisted-linear on `V_m`. -/
theorem baseMulTwisted_braidEnd {i m : ℕ} (him : i < m) : BaseMulTwisted q m m (braidEnd q i) :=
  fun f F => braid_symmetric_mul q (swapAux_baseMulShift q him f) F

/-- For `i < m`, the inverse loop `T_i^{-1}` is twisted-linear on `V_m`. -/
theorem baseMulTwisted_braidInvEnd {i m : ℕ} (him : i < m) :
    BaseMulTwisted q m m (braidInvEnd q i) := by
  rw [braidInvEnd_eq]
  exact ((baseMulTwisted_braidEnd him).add (BaseMulTwisted.one.smul _)).smul _

/-- For `a, b ≤ m`, both trains from `a` to `b` are twisted-linear on `V_m`. -/
theorem baseMulTwisted_trains {m a b : ℕ} (ha : a ≤ m) (hb : b ≤ m) :
    BaseMulTwisted q m m (trainUpEnd q a b) ∧ BaseMulTwisted q m m (trainDownEnd q a b) :=
  baseMul_trains_of BaseMulTwisted.one (fun _ _ hA hB => hB.mul hA)
    (fun _ hi => baseMulTwisted_braidEnd hi) (fun _ hi => baseMulTwisted_braidInvEnd hi) ha hb

/-- The raising operator `d_+` is twisted-linear from `V_k` to `V_{k+1}`. -/
theorem baseMulTwisted_dplus (k : ℕ) : BaseMulTwisted q k (k + 1) (dplus q k) := fun f F => by
  rw [dplus_apply, dplus_apply, map_mul (qshift q (k + 1)), qshift_baseMulShift, mul_left_comm,
    (baseMulTwisted_trains (m := k + 1) (by omega) le_rfl).1, mul_neg]

variable [Algebra ℚ L]

/-- The lowering operator `d_-` is twisted-linear from `V_{k+1}` to `V_k`. -/
theorem baseMulTwisted_dminus (k : ℕ) : BaseMulTwisted q (k + 1) k (dminus q (k + 1)) :=
  fun f F => by
  rw [dminus_apply, dminus_apply, map_mul, qshiftNeg_baseMulShift, Nat.add_sub_cancel,
    lowerCoeff_mul_of_mem_piece (baseMulShift_mem_piece q k f)]

end TwistedLetters

/-! ### The pulled-back stage word -/

section Word

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- The word `(q-1)^{-1}(d_-d_+ - q\,d_+d_-)T^*_{k+1↘1}` on `V_{k+1}`, whose image under Mellit's
`N` is `-y_1z_1`. -/
noncomputable def baseMulTwo (q : L) (k : ℕ) : Module.End L (Total L) :=
  (q - 1)⁻¹ • (dminus q (k + 2) * dplus q (k + 1) - q • (dplus q k * dminus q (k + 1))) *
    trainUpEnd q (k + 1) 1

/-- The stage `(q^{-k}T_{k+1↘1}W_kT_{1↗k+1})^{A-1}T_{k+1↘1}q^{-k}d_+` from `V_k` to `V_{k+1}`,
whose image under Mellit's `N` is the `(1,1)` stage `G_{k+1,A}`. -/
noncomputable def baseMulStage (q : L) (k A : ℕ) : Module.End L (Total L) :=
  (q ^ (-(k : ℤ)) • (trainDownEnd q (k + 1) 1 * baseMulTwo q k * trainUpEnd q 1 (k + 1))) ^ (A - 1)
    * (trainDownEnd q (k + 1) 1 * (q ^ (-(k : ℤ)) • dplus q k))

/-- The stage word `W_ℓ ⋯ W_{k+1}` from grading `k`, the preimage under `N` of
`HJO.Mellit.LhsDesign.stageFromEnd` at `(1,1)`. -/
noncomputable def baseMulWord (q : L) : ℕ → List ℕ → Module.End L (Total L)
  | _, [] => 1
  | k, A :: α => baseMulWord q (k + 1) α * baseMulStage q k A

/-- The word `baseMulTwo q k` is twisted-linear on `V_{k+1}`. -/
theorem baseMulTwisted_baseMulTwo (q : L) (k : ℕ) :
    BaseMulTwisted q (k + 1) (k + 1) (baseMulTwo q k) :=
  (baseMulTwisted_trains (q := q) (m := k + 1) le_rfl (by omega)).1.mul
    ((((baseMulTwisted_dplus (k + 1)).mul (baseMulTwisted_dminus (k + 1))).sub
      (((baseMulTwisted_dminus k).mul (baseMulTwisted_dplus k)).smul q)).smul _)

/-- The stage `baseMulStage q k A` is twisted-linear from `V_k` to `V_{k+1}`. -/
theorem baseMulTwisted_baseMulStage (q : L) (k A : ℕ) :
    BaseMulTwisted q k (k + 1) (baseMulStage q k A) := by
  have hD : BaseMulTwisted q (k + 1) (k + 1) (trainDownEnd q (k + 1) 1) :=
    (baseMulTwisted_trains (m := k + 1) le_rfl (by omega)).2
  have hU : BaseMulTwisted q (k + 1) (k + 1) (trainUpEnd q 1 (k + 1)) :=
    (baseMulTwisted_trains (m := k + 1) (by omega) le_rfl).1
  have hR : BaseMulTwisted q (k + 1) (k + 1)
      (q ^ (-(k : ℤ)) • (trainDownEnd q (k + 1) 1 * baseMulTwo q k * trainUpEnd q 1 (k + 1))) :=
    ((hU.mul (baseMulTwisted_baseMulTwo q k)).mul hD).smul _
  have hO : BaseMulTwisted q k (k + 1)
      (trainDownEnd q (k + 1) 1 * (q ^ (-(k : ℤ)) • dplus q k)) :=
    ((baseMulTwisted_dplus k).smul _).mul hD
  exact hO.mul (hR.pow _)

/-- The stage word `baseMulWord q k α` is twisted-linear from `V_k` to `V_{k+ℓ(α)}`. -/
theorem baseMulTwisted_baseMulWord (q : L) :
    ∀ (α : List ℕ) (k : ℕ), BaseMulTwisted q k (k + α.length) (baseMulWord q k α)
  | [], k => by simpa [baseMulWord] using (BaseMulTwisted.one : BaseMulTwisted q k k 1)
  | A :: α, k => by
    have h := (baseMulTwisted_baseMulStage q k A).mul (baseMulTwisted_baseMulWord q α (k + 1))
    rwa [show k + 1 + α.length = k + (A :: α).length by simp; omega] at h

/-- The lowering run `d_-^n` is twisted-linear from `V_n` to `V_0`. -/
theorem baseMulTwisted_lowerRun (q : L) :
    ∀ n : ℕ, BaseMulTwisted q n 0 (lowerRun q n)
  | 0 => BaseMulTwisted.one
  | n + 1 => (baseMulTwisted_dminus n).mul (baseMulTwisted_lowerRun q n)

end Word

/-! ### The pulled-back word is carried to the stage word by an intertwiner -/

section Carry

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- The relations Mellit's `∇'` satisfies on the pieces, read on the total space through a family
`N_k` of endomorphisms (`N_k` standing for `∇'` on `V_k`): it commutes with `d_-` and with the
loops `T_i`, and `N(d_+) = -q^k y_1 d^*_+` out of `V_k`. -/
structure BaseMulIntertwines (q u : L) (N : ℕ → Module.End L (Total L)) : Prop where
  map_dminus : ∀ (k : ℕ) (F : Total L), F ∈ piece L (k + 1) →
    N k (dminus q (k + 1) F) = dminus q (k + 1) (N (k + 1) F)
  map_dplus : ∀ (k : ℕ) (F : Total L), F ∈ piece L k →
    N (k + 1) (dplus q k F) = -(q ^ k • ((auxVar 1 : Total L) * dplusStar q u k (N k F)))
  map_braid : ∀ (k i : ℕ) (F : Total L), i + 2 ≤ k → F ∈ piece L k →
    N k (braid q (i + 1) F) = braid q (i + 1) (N k F)

namespace BaseMulIntertwines

variable {q u : L} {N : ℕ → Module.End L (Total L)} (hN : BaseMulIntertwines q u N)
include hN

/-- The lowering operator `d_-` from `V_{k+1}` to `V_k` is intertwined with itself. -/
theorem carries_dminus (k : ℕ) :
    BaseMulCarries N (k + 1) k (dminus q (k + 1)) (dminus q (k + 1)) := fun F hF =>
  ⟨by simpa using dminus_mem_piece q (k + 1) hF, hN.map_dminus k F hF⟩

/-- The raising operator `d_+` from `V_k` to `V_{k+1}` is intertwined with `-q^ky_1d^*_+`. -/
theorem carries_dplus (k : ℕ) :
    BaseMulCarries N k (k + 1) (dplus q k)
      (-(q ^ k • (LinearMap.mulLeft L (auxVar 1 : Total L) * dplusStar q u k))) := fun F hF =>
  ⟨dplus_mem_piece q k hF, hN.map_dplus k F hF⟩

/-- For `i < m`, the loop `T_i` on `V_m` is intertwined with itself. -/
theorem carries_braidEnd {i m : ℕ} (him : i < m) :
    BaseMulCarries N m m (braidEnd q i) (braidEnd q i) := fun F hF => by
  refine ⟨braid_mem_piece_of_lt q him hF, ?_⟩
  rcases i with _ | i
  · change N m (braid q 0 F) = braid q 0 (N m F)
    rw [braid_zero_index, braid_zero_index]
  · exact hN.map_braid m i F (by omega) hF

/-- For `i < m`, the inverse loop `T_i^{-1}` on `V_m` is intertwined with itself. -/
theorem carries_braidInvEnd {i m : ℕ} (him : i < m) :
    BaseMulCarries N m m (braidInvEnd q i) (braidInvEnd q i) := by
  rw [braidInvEnd_eq]
  exact ((hN.carries_braidEnd him).add (BaseMulCarries.one.smul _)).smul _

/-- For `a, b ≤ m`, both trains from `a` to `b` on `V_m` are intertwined with themselves. -/
theorem carries_trains {m a b : ℕ} (ha : a ≤ m) (hb : b ≤ m) :
    BaseMulCarries N m m (trainUpEnd q a b) (trainUpEnd q a b) ∧
      BaseMulCarries N m m (trainDownEnd q a b) (trainDownEnd q a b) :=
  baseMul_trains_of (P := fun A => BaseMulCarries N m m A A) BaseMulCarries.one
    (fun _ _ hA hB => hB.mul hA) (fun _ hi => hN.carries_braidEnd hi)
    (fun _ hi => hN.carries_braidInvEnd hi) ha hb

end BaseMulIntertwines

/-- **`Ω(2;1,1) = -y_1z_1` is the image of `(q-1)^{-1}(d_-d_+ - q\,d_+d_-)T^*_{k+1↘1}`**, with
`N(d_+) = -q^jy_1d^*_+` substituted at both raising arrows. -/
theorem replTwoTotal_one_one_eq (q u : L) (k : ℕ) :
    replTwoTotal q u 1 1 k = (q - 1)⁻¹ •
      (dminus q (k + 2) *
          -(q ^ (k + 1) • (LinearMap.mulLeft L (auxVar 1 : Total L) * dplusStar q u (k + 1))) -
        q • (-(q ^ k • (LinearMap.mulLeft L (auxVar 1 : Total L) * dplusStar q u k)) *
          dminus q (k + 1))) * trainUpEnd q (k + 1) 1 := by
  refine LinearMap.ext fun F => ?_
  simp only [replTwoTotal, slopeOperator_one_one, zopOneStar, Nat.sub_self, pow_zero, one_smul,
    one_mul, Nat.add_sub_cancel, LinearMap.neg_apply, LinearMap.smul_apply, Module.End.mul_apply,
    LinearMap.sub_apply, LinearMap.mulLeft_apply, map_neg, map_smul]
  rw [HJO.Sweep.dminus_auxVar_mul q (k := k + 1) le_rfl (by omega), mul_sub,
    show (1 - q : L) = -(q - 1) by ring, div_neg, div_eq_mul_inv]
  module

/-- `Ω(1;1,1) = -y_1d^*_+` is `q^{-k}` times `N(d_+) = -q^ky_1d^*_+`. -/
theorem replOneTotal_one_one_eq {q : L} (hq : q ≠ 0) (u : L) (k : ℕ) :
    replOneTotal q u 1 1 k = q ^ (-(k : ℤ)) •
      -(q ^ k • (LinearMap.mulLeft L (auxVar 1 : Total L) * dplusStar q u k)) := by
  rw [smul_neg, smul_smul, ← zpow_natCast, ← zpow_add₀ hq, neg_add_cancel, zpow_zero, one_smul]
  simp [replOneTotal, slopeOperator_one_one]

namespace BaseMulIntertwines

variable {q u : L} {N : ℕ → Module.End L (Total L)} (hN : BaseMulIntertwines q u N)
include hN

/-- On `V_{k+1}`, the word `baseMulTwo q k` is intertwined with `Ω(2;1,1)`. -/
theorem carries_two (k : ℕ) :
    BaseMulCarries N (k + 1) (k + 1) (baseMulTwo q k) (replTwoTotal q u 1 1 k) := by
  rw [replTwoTotal_one_one_eq]
  have hT := (hN.carries_trains (m := k + 1) (a := k + 1) (b := 1) le_rfl (by omega)).1
  have h1 := (hN.carries_dplus (k + 1)).mul (hN.carries_dminus (k + 1))
  have h2 := (hN.carries_dminus k).mul (hN.carries_dplus k)
  exact hT.mul ((h1.sub (h2.smul q)).smul _)

/-- For `q ≠ 0`, the stage `baseMulStage q k A` from `V_k` to `V_{k+1}` is intertwined with the
`(1,1)` stage `G_{k+1,A}`. -/
theorem carries_stage (hq : q ≠ 0) (k A : ℕ) :
    BaseMulCarries N k (k + 1) (baseMulStage q k A) (stageTotal q u 1 1 k A) := by
  have hD := (hN.carries_trains (m := k + 1) (a := k + 1) (b := 1) le_rfl (by omega)).2
  have hU := (hN.carries_trains (m := k + 1) (a := 1) (b := k + 1) (by omega) le_rfl).1
  have hR : BaseMulCarries N (k + 1) (k + 1)
      (q ^ (-(k : ℤ)) • (trainDownEnd q (k + 1) 1 * baseMulTwo q k * trainUpEnd q 1 (k + 1)))
      (replicatedTotal q u 1 1 k) :=
    (hU.mul ((hN.carries_two k).mul hD)).smul _
  have hO : BaseMulCarries N k (k + 1)
      (trainDownEnd q (k + 1) 1 * (q ^ (-(k : ℤ)) • dplus q k))
      (trainDownEnd q (k + 1) 1 * replOneTotal q u 1 1 k) := by
    rw [replOneTotal_one_one_eq hq]
    exact ((hN.carries_dplus k).smul _).mul hD
  exact hO.mul (hR.pow _)

/-- For `q ≠ 0`, the word `baseMulWord q k α` from `V_k` to `V_{k+ℓ(α)}` is intertwined with the
`(1,1)` stage word `stageFromEnd q u 1 1 k α`. -/
theorem carries_word (hq : q ≠ 0) :
    ∀ (α : List ℕ) (k : ℕ),
      BaseMulCarries N k (k + α.length) (baseMulWord q k α) (stageFromEnd q u 1 1 k α)
  | [], k => by
    simpa [baseMulWord, stageFromEnd] using (BaseMulCarries.one : BaseMulCarries N k k 1 1)
  | A :: α, k => by
    have h := (hN.carries_stage hq k A).mul (carries_word hq α (k + 1))
    rwa [show k + 1 + α.length = k + (A :: α).length by simp; omega] at h

/-- The lowering run `d_-^n` from `V_n` to `V_0` is intertwined with itself. -/
theorem carries_lowerRun : ∀ n : ℕ, BaseMulCarries N n 0 (lowerRun q n) (lowerRun q n)
  | 0 => BaseMulCarries.one
  | n + 1 => (hN.carries_dminus n).mul (carries_lowerRun n)

end BaseMulIntertwines

/-- **At the base slope the left-hand operator is conjugate to a multiplication**, given any
family `N_k` with the relations of Mellit's `∇'` that restricts to `∇` on `V_0`:
`lhsOp 1 1 α (∇f) = ∇(g·f)` with `g = ct(d_-^ℓ W_ℓ ⋯ W_1(1))`. The stage word is the image under
`N` of the word `HJO.Mellit.LhsDesign.baseMulWord` in `d_-`, `d_+` and the loops, and that word is
linear for the twisted `Λ`-action, which on `V_0` is multiplication. -/
theorem lhsOp_one_one_of_intertwines {q u : L} (hq : q ≠ 0) {N : ℕ → Module.End L (Total L)}
    (hN : BaseMulIntertwines q u N) {nabla : Module.End L (Sym.Lambda L)}
    (hN0 : ∀ f : Sym.Lambda L, N 0 (C f) = C (nabla f)) (α : List ℕ) (f : Sym.Lambda L) :
    lhsOp q u 1 1 α (nabla f)
      = nabla (constantCoeff (lowerRun q α.length (baseMulWord q 0 α 1)) * f) := by
  have hW := hN.carries_word hq α 0
  rw [zero_add] at hW
  have hc := hW.mul (hN.carries_lowerRun α.length)
  have hTW := baseMulTwisted_baseMulWord q α 0
  rw [zero_add] at hTW
  have hT := hTW.mul (baseMulTwisted_lowerRun q α.length)
  obtain ⟨hmem, heq⟩ := hc (C f) (C_mem_piece_zero f)
  obtain ⟨x, hx⟩ := exists_C_eq_of_mem_piece_zero hmem
  have hlhs : lhsOp q u 1 1 α (nabla f)
      = constantCoeff ((lowerRun q α.length * stageFromEnd q u 1 1 0 α) (C (nabla f))) := rfl
  rw [hlhs, ← hN0, ← heq, ← hx, hN0, constantCoeff_C]
  congr 1
  have hY := hT f 1
  rw [mul_one, baseMulShift_zero] at hY
  have : C x = C f * (lowerRun q α.length * baseMulWord q 0 α) 1 := by rw [hx, ← hY]
  have h2 := congrArg constantCoeff this
  rw [constantCoeff_C, map_mul, constantCoeff_C] at h2
  rw [h2, mul_comm]
  rfl

end Carry

/-! ### Mellit's `∇'` supplies the relations -/

section NablaPrime

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-- **Mellit's `∇'` satisfies the relations read here.** A family realising Mellit's `N` piece by
piece (`HJO.Sweep.IsNablaPrime`) sends `d_+` out of `V_k` to `(qu)^{-1}z_1d_+`, which is
`-q^ky_1d^*_+` (`HJO.Sweep.zopOneStar_dplus`). -/
theorem baseMulIntertwines_of_isNablaPrime {nabla : Module.End L (Sym.Lambda L)}
    {N : ℕ → Module.End L (Total L)} (hN : IsNablaPrime q u nabla N) (hq : q ≠ 0) (hq1 : q ≠ 1)
    (hu : u ≠ 0) : BaseMulIntertwines q u N where
  map_dminus k _ hF := hN.map_dminus k hF
  map_dplus k F hF := by
    rw [hN.map_dplus k hF, zopOneStar_dplus q u hq hq1 (hN.mem_piece k hF), smul_smul,
      show (q * u)⁻¹ * -(u * q ^ (k + 1)) = -q ^ k by field_simp; ring, neg_smul]
  map_braid k _ F hik hF := hN.map_braid (by omega) (by omega) hF

end NablaPrime

/-! ### The standing field -/

section Standing

variable (K : Type*) [Field K] [Algebra ParamRing K] [IsFractionRing ParamRing K] [Algebra ℚ K]

local notation "𝗊" => paramQ K
local notation "𝗎" => paramU K

/-- **At the base slope the conjugated operator is a multiplication**, at every composition:
for the Macdonald conjugator normalised by `∇1 = 1`, `lhsOp 1 1 α ∘ ∇ = ∇ ∘ (g·)` for some
`g ∈ Λ`. -/
theorem exists_lhsOp_one_one_nabla_eq_mul {nabla : Module.End K (Sym.Lambda K)}
    (hnab : IsMacdonaldConjugator 𝗊 𝗎 nabla) (hone : nabla 1 = 1) (α : List ℕ) :
    ∃ g : Sym.Lambda K, ∀ f : Sym.Lambda K, lhsOp 𝗊 𝗎 1 1 α (nabla f) = nabla (g * f) := by
  obtain ⟨N, hN⟩ := Sweep.exists_isNablaPrime_param K hnab hone
  have hq1 : 𝗊 ≠ 1 := by simpa using HJO.Standing.paramQ_pow_succ_ne_one K 0
  exact ⟨_, lhsOp_one_one_of_intertwines (HJO.Standing.paramQ_ne_zero K)
    (baseMulIntertwines_of_isNablaPrime hN (HJO.Standing.paramQ_ne_zero K) hq1
      (HJO.Standing.paramU_ne_zero K)) hN.map_C α⟩

set_option linter.unusedVariables false in
/-- **At the base slope the conjugated operator is a multiplication.** For a composition `α`,
`∇^{-1} ∘ lhsOp 1 1 α ∘ ∇` is multiplication by some `g ∈ Λ`. -/
theorem lhsOp_one_one_isMul {nabla : Module.End K (Sym.Lambda K)}
    (hnab : IsMacdonaldConjugator 𝗊 𝗎 nabla) (hone : nabla 1 = 1) (α : List ℕ)
    (hpos : ∀ x ∈ α, 0 < x) :
    ∃ g : Sym.Lambda K, ∀ f : Sym.Lambda K, lhsOp 𝗊 𝗎 1 1 α (nabla f) = nabla (g * f) :=
  exists_lhsOp_one_one_nabla_eq_mul K hnab hone α

end Standing

end HJO.Mellit.LhsDesign
