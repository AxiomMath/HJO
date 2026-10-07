/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidAppendPart
public import HJO.Shuffle.SlopeBraid
public meta import HJO.Attr

/-! # Counting the loop letters of a braid, and the failure of the naive append identity

`HJO.Braid.BraidMonoid` presents `𝔹_k^+(𝕋_0)` on the letters `T_i`, `T̄_i`, `y_1`, `z_1`. Every one
of its relation families — and the tenth family that cuts the alphabet down to the rank — preserves
the number of `y_1` and `z_1` letters in a word. So there is a monoid homomorphism
`𝔹_k^+(𝕋_0) → (ℕ, +)`, a homomorphism out of that monoid that is not a representation, and it is
enough to refute the append identity in its naive form, with the appended part `β_{k+1} = A`; the
corrected form is `HJO.Braid.IsAppendSetup.specialBraid_eq_appendRhs`.

## Main definitions

* `HJO.Braid.weightHom` — the homomorphism `𝔹_k^+(𝕋_0) →* Multiplicative ℕ`, for `k ≥ 1`.
* `HJO.Braid.letterCount` — its additive reading, `ℓ : 𝔹_k^+(𝕋_0) → ℕ`.
* `HJO.Braid.appendRhs` — the right-hand side of the append identity
  `HJO.Braid.IsAppendSetup.specialBraid_eq_appendRhs`.

## Main results

* `HJO.Braid.letterCount_braidGenY`, `HJO.Braid.letterCount_braidGenZ` — `ℓ(y_i) = ℓ(z_i) = 1` for
  `i ≥ 1`; `HJO.Braid.letterCount_braidTrainUp`, `HJO.Braid.letterCount_braidTrainDown` — a train
  weighs nothing; `HJO.Braid.letterCount_braidYtilde` — `ℓ(ỹ_i) = 1`.
* `HJO.Braid.letterCount_braidStep` — **one move of `HJO.Braid.braidStep` contributes exactly one
  letter**, whichever wall is crossed and whatever the two ranks are.
* `HJO.Braid.letterCount_braidWord` — `ℓ(b_{i_1,…,i_l}(w)) = l`, and
  `HJO.Braid.letterCount_specialBraid` — `ℓ(B_{s,v,α}) = ∑_i (α_i - 1)`.
* `HJO.Braid.letterCount_phiPlusStar` — `ℓ ∘ φ*₊ = ℓ`: the index-raising homomorphism of
  `HJO.Braid.phiPlusStar` is weight-preserving.
* `HJO.Braid.letterCount_slopeBraid` — `ℓ(b_{m,n}) = m + n - 2`, the length of
  `HJO.Mellit.slopeWord`.
* `HJO.Braid.letterCount_appendRhs` — the weight of that right-hand side.
* `HJO.Braid.eq_one_and_add_eq_two_of_specialBraid_eq_appendRhs` — **the refutation.** If the
  identity of `HJO.Braid.IsAppendSetup.specialBraid_eq_appendRhs` holds with the appended part
  `β_{k+1} = A` then `A = 1` and `a + b = 2`; so for every other `(A, a, b)` it fails, at every
  rank, for every tuple, with no hypothesis on the data beyond `β_{k+1} = A`.
* `HJO.Braid.specialBraid_ne_appendRhs` — the same read as a disequality.
* `HJO.Braid.letterCount_specialBraid_eq_letterCount_appendRhs_iff` — **the repair.** The two
  weights agree precisely when `β_{k+1} = A(a+b) - 1`, which is Mellit's own count.

## The defect, and its repair

The naive append identity adjoins to special-braid data `(v, α)` of rank `k` one further point with
`β_{k+1} = A` and claims

`B_{s,w,β} = (T_{k+1↘1} b_{a,b} y_1z_1 T_{1↗k+1})^{A-1} T_{k+1↘1} b_{a,b} φ*₊(B_{s,v,α}) T_{1↘k+1}`.

Weigh both sides. The left is `∑_i(β_i - 1) = ℓ(B_{s,v,α}) + (A - 1)`, one letter per move. The
right is `ℓ(B_{s,v,α}) + (A-1)(a+b) + (a+b-2)`, since `ℓ(b_{a,b}) = a+b-2` and `y_1z_1` adds two.
The two differ by `(A-1)(a+b-1) + (a+b-2)`, which vanishes only at `A = 1`, `a = b = 1`.

The hypothesis is what is wrong, not the displayed word. In Mellit, §6, the one-strand braid
`b^{(A)}_{a,b} = (b_{a,b}y_1z_1)^{A-1}b_{a,b}` is said to cross the horizontal and vertical walls
`Ab - 1` and `Aa - 1` times, "so it is the braid corresponding to the composition with one part
`(A)`" — a total of `A(a+b) - 2` crossings, hence `A(a+b) - 1` positions on the antidiagonal. So
`A` is the number of *turns* and the part is `β_{k+1} = A(a+b) - 1`; the naive `β_{k+1} = A`
conflates the two. `HJO.Braid.letterCount_specialBraid_eq_letterCount_appendRhs_iff` is that repair,
and it is the only value of `β_{k+1}` the weight admits.

Two further defects of the naive statement are recorded in
`HJO/Shuffle/BraidAppendPart.lean`: `a` and `b` are not bound by the hypotheses at all (its user
`HJO.Mellit.braidRep_specialBraid_dplusIter` supplies `s = b/a - ε`), and the domination
hypothesis is too weak for the step its proof attributes to
`HJO.Braid.specialBraid_mul_trainDown_one`.

## Implementation notes

The weight is stated on `Multiplicative ℕ` because `Con.lift` wants a monoid, and read back into
`ℕ` by `HJO.Braid.letterCount`, which is what every statement below uses. The hypothesis `1 ≤ k`
is genuine and not bureaucracy: at `k = 0` the letters `y_1` and `z_1` are out of rank, so
`HJO.Braid.BraidRel.out_of_rank` sends them to the identity and no nonzero weight descends —
`𝔹_0^+(𝕋_0)` is trivial (`HJO.Braid.braidMonoid_zero`).

## References

The append identity `HJO.Braid.IsAppendSetup.specialBraid_eq_appendRhs` and its naive form, using
`HJO.Braid.BraidMonoid`, `HJO.Braid.braidGenT`, `HJO.Braid.specialBraid`, `HJO.Braid.phiPlusStar`,
`HJO.Braid.slopeBraid`, `HJO.Braid.trainUp`, `HJO.Braid.trainDown`. A. Mellit, *Toric braids and
`(m, n)`-parking functions*, §6.
-/

@[expose] public section

open Finset

namespace HJO.Braid

/-! ### The weight of a letter -/

/-- **The weight of a letter of `HJO.Braid.yWord`'s free monoid**: the two loop letters weigh one
each, the braid letters nothing. -/
def weightLetter : Letter → Multiplicative ℕ
  | Letter.T _ => 1
  | Letter.Tbar _ => 1
  | Letter.y1 => Multiplicative.ofAdd 1
  | Letter.z1 => Multiplicative.ofAdd 1

/-- The weight of a word of `F_k`: the number of `y_1` and `z_1` letters in it. -/
def weightWord : FreeMonoid Letter →* Multiplicative ℕ := FreeMonoid.lift weightLetter

@[simp]
theorem weightLetter_T (i : ℕ) : weightLetter (Letter.T i) = 1 := rfl

@[simp]
theorem weightLetter_Tbar (i : ℕ) : weightLetter (Letter.Tbar i) = 1 := rfl

theorem weightLetter_y1 : weightLetter Letter.y1 = Multiplicative.ofAdd 1 := rfl

theorem weightLetter_z1 : weightLetter Letter.z1 = Multiplicative.ofAdd 1 := rfl

@[simp]
theorem weightWord_of (c : Letter) : weightWord (FreeMonoid.of c) = weightLetter c := rfl

@[simp]
theorem weightWord_T (i : ℕ) : weightWord (FreeMonoid.of (Letter.T i)) = 1 := rfl

@[simp]
theorem weightWord_Tbar (i : ℕ) : weightWord (FreeMonoid.of (Letter.Tbar i)) = 1 := rfl

/-- **`𝗒_i` weighs one**, for `i ≥ 1`: the recursion `𝗒_{i+1} = T̄_i𝗒_iT̄_i` of `HJO.Braid.yWord`
wraps only braid letters around it. -/
theorem weightWord_yWord : ∀ i, 1 ≤ i → weightWord (yWord i) = Multiplicative.ofAdd 1
  | 1, _ => rfl
  | (i + 2), _ => by
    rw [yWord_succ, map_mul, map_mul, weightWord_yWord (i + 1) (by omega), weightWord_Tbar,
      one_mul, mul_one]

/-- **`𝗓_i` weighs one**, for `i ≥ 1`. -/
theorem weightWord_zWord : ∀ i, 1 ≤ i → weightWord (zWord i) = Multiplicative.ofAdd 1
  | 1, _ => rfl
  | (i + 2), _ => by
    rw [zWord_succ, map_mul, map_mul, weightWord_zWord (i + 1) (by omega), weightWord_T,
      one_mul, mul_one]

/-! ### The weight descends to the quotient -/

/-- **Every relation of `HJO.Braid.BraidMonoid` preserves the weight**, at every rank `k ≥ 1`.

The two cancellations, the braid relation and far commutation are between braid letters and weigh
nothing on either side; the `T`-commutations move a weight-one word past a weight-zero letter; the
internal commutations are between two weight-one words; and the mixed relation
`𝗓_1T_1𝗒_1T̄_1 = T̄_1𝗒_1T̄_1𝗓_1` has one `y` and one `z` on each side. The tenth family,
`HJO.Braid.BraidRel.out_of_rank`, is where `1 ≤ k` is used: it fires only on braid letters once
the rank is positive, because `y_1` and `z_1` are then in rank. -/
theorem weightWord_respects {k : ℕ} (hk : 1 ≤ k) {x y : FreeMonoid Letter} (h : BraidRel k x y) :
    weightWord x = weightWord y := by
  cases h with
  | mul_inv i _ _ => simp
  | inv_mul i _ _ => simp
  | braid i _ _ => simp
  | far_comm i j _ _ _ => simp
  | yWord_comm_T i j hi _ _ _ _ _ =>
    rw [map_mul, map_mul, weightWord_yWord i hi, weightWord_T, one_mul, mul_one]
  | zWord_comm_T i j hi _ _ _ _ _ =>
    rw [map_mul, map_mul, weightWord_zWord i hi, weightWord_T, one_mul, mul_one]
  | yWord_comm i j hi _ hj _ =>
    rw [map_mul, map_mul, weightWord_yWord i hi, weightWord_yWord j hj]
  | zWord_comm i j hi _ hj _ =>
    rw [map_mul, map_mul, weightWord_zWord i hi, weightWord_zWord j hj]
  | zy _ =>
    simp only [map_mul, weightWord_T, weightWord_Tbar, weightWord_yWord 1 le_rfl,
      weightWord_zWord 1 le_rfl, one_mul, mul_one]
  | out_of_rank c hc =>
    cases c with
    | T i => simp
    | Tbar i => simp
    | y1 => exact absurd hk hc
    | z1 => exact absurd hk hc

/-- **The weight homomorphism of `HJO.Braid.BraidMonoid`**, `𝔹_k^+(𝕋_0) →* Multiplicative ℕ`, for
`k ≥ 1`. -/
def weightHom (k : ℕ) (hk : 1 ≤ k) : BraidMonoid k →* Multiplicative ℕ :=
  Con.lift _ weightWord
    (Con.conGen_le.2 fun _x _y hxy => (Con.ker_rel _).2 (weightWord_respects hk hxy))

@[simp]
theorem weightHom_apply (k : ℕ) (hk : 1 ≤ k) (x : FreeMonoid Letter) :
    weightHom k hk (toBraidMonoid k x) = weightWord x :=
  Con.lift_coe _ _

/-- **The letter count `ℓ` of an element of `𝔹_k^+(𝕋_0)`**: the number of `y`/`z` letters in any
word naming it, which the relations make well defined. -/
def letterCount (k : ℕ) (hk : 1 ≤ k) (x : BraidMonoid k) : ℕ :=
  Multiplicative.toAdd (weightHom k hk x)

@[simp]
theorem letterCount_one (k : ℕ) (hk : 1 ≤ k) : letterCount k hk 1 = 0 := by
  rw [letterCount, map_one]
  rfl

theorem letterCount_mul {k : ℕ} (hk : 1 ≤ k) (x y : BraidMonoid k) :
    letterCount k hk (x * y) = letterCount k hk x + letterCount k hk y := by
  rw [letterCount, letterCount, letterCount, map_mul]
  rfl

theorem letterCount_pow {k : ℕ} (hk : 1 ≤ k) (x : BraidMonoid k) (n : ℕ) :
    letterCount k hk (x ^ n) = n * letterCount k hk x := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, letterCount_mul, ih, Nat.succ_mul]

/-! ### The weight of each named element -/

@[simp]
theorem letterCount_braidGenT {k : ℕ} (hk : 1 ≤ k) (i : ℕ) :
    letterCount k hk (braidGenT k i) = 0 := by
  rw [letterCount, braidGenT, weightHom_apply, weightWord_T]
  rfl

@[simp]
theorem letterCount_braidGenTinv {k : ℕ} (hk : 1 ≤ k) (i : ℕ) :
    letterCount k hk (braidGenTinv k i) = 0 := by
  rw [letterCount, braidGenTinv, weightHom_apply, weightWord_Tbar]
  rfl

/-- **`ℓ(y_i) = 1`** for `i ≥ 1`, which is `HJO.Braid.braidGenT` read through the weight. -/
theorem letterCount_braidGenY {k : ℕ} (hk : 1 ≤ k) {i : ℕ} (hi : 1 ≤ i) :
    letterCount k hk (braidGenY k i) = 1 := by
  rw [letterCount, braidGenY, weightHom_apply, weightWord_yWord i hi]
  rfl

/-- **`ℓ(z_i) = 1`** for `i ≥ 1`. -/
theorem letterCount_braidGenZ {k : ℕ} (hk : 1 ≤ k) {i : ℕ} (hi : 1 ≤ i) :
    letterCount k hk (braidGenZ k i) = 1 := by
  rw [letterCount, braidGenZ, weightHom_apply, weightWord_zWord i hi]
  rfl

theorem letterCount_prod_eq_zero {k : ℕ} (hk : 1 ≤ k) {α : Type*} (l : List α)
    (f : α → BraidMonoid k) (hf : ∀ x, letterCount k hk (f x) = 0) :
    letterCount k hk ((l.map f).prod) = 0 := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.map_cons, List.prod_cons, letterCount_mul, hf a, ih]

/-- **A train weighs nothing**: `HJO.Braid.trainUp` is a word in the braid letters alone. -/
@[simp]
theorem letterCount_braidTrainUp {k : ℕ} (hk : 1 ≤ k) (a b : ℕ) :
    letterCount k hk (braidTrainUp k a b) = 0 := by
  rw [braidTrainUp, trainUp]
  split
  · rw [ascendingWord]
    exact letterCount_prod_eq_zero hk _ _ (letterCount_braidGenT hk)
  · rw [descendingWord]
    exact letterCount_prod_eq_zero hk _ _ (letterCount_braidGenTinv hk)

/-- **A train weighs nothing**: `HJO.Braid.trainDown` is a word in the braid letters alone. -/
@[simp]
theorem letterCount_braidTrainDown {k : ℕ} (hk : 1 ≤ k) (a b : ℕ) :
    letterCount k hk (braidTrainDown k a b) = 0 := by
  rw [braidTrainDown, trainDown]
  split
  · rw [descendingWord]
    exact letterCount_prod_eq_zero hk _ _ (letterCount_braidGenT hk)
  · rw [ascendingWord]
    exact letterCount_prod_eq_zero hk _ _ (letterCount_braidGenTinv hk)

/-- **`ℓ(ỹ_i) = 1`**: `HJO.Braid.braidYtilde` is `y_k` conjugated by trains, so it weighs what `y_k`
weighs, at every index `i` including the ones outside the range. -/
@[simp]
theorem letterCount_braidYtilde {k : ℕ} (hk : 1 ≤ k) (i : ℕ) :
    letterCount k hk (braidYtilde k i) = 1 := by
  rw [braidYtilde, letterCount_mul, letterCount_mul, letterCount_mul,
    letterCount_braidTrainDown, letterCount_braidTrainUp, letterCount_braidTrainUp,
    letterCount_braidGenY hk hk]

/-! ### The weight of a braid of moves -/

/-- **One move contributes exactly one letter.** `HJO.Braid.braidStep` is a descending train, which
weighs nothing, followed by a single `z_a` or `ỹ_a`; the rank `a` is positive by
`HJO.Braid.entryRank_pos`, so the `z` branch is a genuine generator and not the junk `z_0`. -/
@[simp]
theorem letterCount_braidStep {θ : ℚ} {k : ℕ} (hk : 1 ≤ k) (w : Fin k → ℚ) (i : Fin k) :
    letterCount k hk (braidStep θ w i) = 1 := by
  rw [braidStep, letterCount_mul, letterCount_braidTrainDown, zero_add]
  split
  · exact letterCount_braidGenZ hk (entryRank_pos w i)
  · exact letterCount_braidYtilde hk _

/-- **The braid of a sequence of moves weighs its length**: `HJO.Braid.braidWord` contributes one
letter per move. -/
theorem letterCount_braidWord {θ : ℚ} {k : ℕ} (hk : 1 ≤ k) (w : Fin k → ℚ) :
    ∀ l : List (Fin k), letterCount k hk (braidWord θ w l) = l.length
  | [] => by simp
  | (i :: l) => by
    rw [braidWord_cons, letterCount_mul, letterCount_braidStep, letterCount_braidWord hk w l,
      List.length_cons]
    omega

/-- **`ℓ(B_{s,v,α}) = ∑_i (α_i - 1)`**: the special braid of `HJO.Braid.specialBraid` weighs the
total number of moves. -/
theorem letterCount_specialBraid {θ : ℚ} {k : ℕ} (hk : 1 ≤ k) (v : Fin k → ℚ) (α : Fin k → ℕ) :
    letterCount k hk (specialBraid θ v α) = ∑ i : Fin k, (α i - 1) := by
  rw [specialBraid, letterCount_braidWord hk, length_specialMoveList]

/-! ### The weight of the slope braid, and of the index-raising homomorphism -/

/-- **`ℓ(b_{m,n}) = m + n - 2`**: `HJO.Braid.slopeBraid` reads each letter of the slope word as a
loop generator, so it weighs the length of `HJO.Mellit.slopeWord`. -/
theorem letterCount_slopeBraid {k : ℕ} (hk : 1 ≤ k) (m n : ℕ) :
    letterCount k hk (slopeBraid k m n) = m + n - 2 := by
  rw [slopeBraid, ← Mellit.length_slopeWord m n]
  induction Mellit.slopeWord m n with
  | nil => simp
  | cons c l ih =>
    rw [List.map_cons, List.prod_cons, letterCount_mul, ih, List.length_cons]
    cases c with
    | y => rw [letterCount_braidGenY hk le_rfl]; omega
    | z => rw [letterCount_braidGenZ hk le_rfl]; omega

/-- **`φ*₊` preserves the weight**: `HJO.Braid.phiPlusStar` sends each braid letter to a braid
letter and each loop letter to a loop generator, so the two homomorphisms out of `𝔹_k^+(𝕋_0)` agree
on the letters and hence, by `HJO.Braid.monoidHom_ext`, everywhere. -/
theorem weightHom_comp_phiPlusStar {k : ℕ} (hk : 1 ≤ k) :
    (weightHom (k + 1) (by omega)).comp (phiPlusStar k hk) = weightHom k hk := by
  refine monoidHom_ext fun c => ?_
  rw [MonoidHom.comp_apply, phiPlusStar_apply, phiPlusFree_of, weightHom_apply, weightWord_of]
  cases c with
  | T i =>
    rw [weightLetter_T]
    by_cases h : i = 0
    · rw [h, phiPlusLetter_T_zero, map_one]
    · rw [phiPlusLetter_T (by omega), braidGenT, weightHom_apply, weightWord_T]
  | Tbar i =>
    rw [weightLetter_Tbar]
    by_cases h : i = 0
    · rw [h, phiPlusLetter_Tbar_zero, map_one]
    · rw [phiPlusLetter_Tbar (by omega), braidGenTinv, weightHom_apply, weightWord_Tbar]
  | y1 =>
    rw [weightLetter_y1, show phiPlusLetter k Letter.y1 = braidGenY (k + 1) 2 from rfl,
      braidGenY, weightHom_apply, weightWord_yWord 2 (by omega)]
  | z1 =>
    rw [weightLetter_z1, show phiPlusLetter k Letter.z1 = braidGenZ (k + 1) 2 from rfl,
      braidGenZ, weightHom_apply, weightWord_zWord 2 (by omega)]

/-- **`ℓ ∘ φ*₊ = ℓ`**, the additive reading of `HJO.Braid.weightHom_comp_phiPlusStar`. -/
theorem letterCount_phiPlusStar {k : ℕ} (hk : 1 ≤ k) (x : BraidMonoid k) :
    letterCount (k + 1) (by omega) (phiPlusStar k hk x) = letterCount k hk x :=
  congrArg Multiplicative.toAdd (DFunLike.congr_fun (weightHom_comp_phiPlusStar hk) x)

/-! ### The right-hand side, and the refutation -/

/-- **The right-hand side of `HJO.Braid.IsAppendSetup.specialBraid_eq_appendRhs`**,

`(T_{k+1↘1} b_{a,b} y_1z_1 T_{1↗k+1})^{A-1} T_{k+1↘1} b_{a,b} φ*₊(B_{s,v,α}) T_{1↘k+1}`,

with `b_{a,b}` taken at rank `k+1`. The outer trains are those of the identity: ascending inside the
power, descending at the end. -/
def appendRhs (θ : ℚ) {k : ℕ} (hk : 1 ≤ k) (A a b : ℕ) (v : Fin k → ℚ) (α : Fin k → ℕ) :
    BraidMonoid (k + 1) :=
  (braidTrainDown (k + 1) (k + 1) 1 * slopeBraid (k + 1) a b * braidGenY (k + 1) 1 *
      braidGenZ (k + 1) 1 * braidTrainUp (k + 1) 1 (k + 1)) ^ (A - 1) *
    braidTrainDown (k + 1) (k + 1) 1 * slopeBraid (k + 1) a b *
      phiPlusStar k hk (specialBraid θ v α) * braidTrainDown (k + 1) 1 (k + 1)

/-- **The weight of the right-hand side**: each of the `A-1` rounds weighs `a+b` — the
`a+b-2` letters of `b_{a,b}` and the two of `y_1z_1` — the `b_{a,b}` of the last factor weighs
`a+b-2`, and `φ*₊(B_{s,v,α})` weighs what `B_{s,v,α}` does. Every train weighs nothing. -/
theorem letterCount_appendRhs {θ : ℚ} {k : ℕ} (hk : 1 ≤ k) {A a b : ℕ} (hab : 2 ≤ a + b)
    (v : Fin k → ℚ) (α : Fin k → ℕ) :
    letterCount (k + 1) (by omega) (appendRhs θ hk A a b v α)
      = (A - 1) * (a + b) + (a + b - 2) + ∑ i : Fin k, (α i - 1) := by
  have hround : letterCount (k + 1) (show 1 ≤ k + 1 by omega)
      (braidTrainDown (k + 1) (k + 1) 1 * slopeBraid (k + 1) a b * braidGenY (k + 1) 1 *
        braidGenZ (k + 1) 1 * braidTrainUp (k + 1) 1 (k + 1)) = a + b := by
    rw [letterCount_mul, letterCount_mul, letterCount_mul, letterCount_mul,
      letterCount_braidTrainDown, letterCount_braidTrainUp, letterCount_slopeBraid,
      letterCount_braidGenY _ le_rfl, letterCount_braidGenZ _ le_rfl]
    omega
  rw [appendRhs, letterCount_mul, letterCount_mul, letterCount_mul, letterCount_mul,
    letterCount_pow, hround, letterCount_braidTrainDown, letterCount_braidTrainDown,
    letterCount_slopeBraid, letterCount_phiPlusStar hk, letterCount_specialBraid hk v α]
  omega

/-- **The weight of the left-hand side.** `B_{s,w,β}` for the appended data weighs
`(β_0 - 1) + ∑_i(α_i - 1)`, `HJO.Braid.specialBraid` contributing one letter per move.

The appended point is the index `0` here and not `k+1`; see the module docstring of
`HJO/Shuffle/BraidAppendPart.lean` for why the `w_{k+1}` of the naive statement is a value and
not an index. -/
theorem letterCount_specialBraid_succ {θ : ℚ} {k : ℕ} (w : Fin (k + 1) → ℚ)
    (β : Fin (k + 1) → ℕ) :
    letterCount (k + 1) (by omega) (specialBraid θ w β)
      = (β 0 - 1) + ∑ i : Fin k, (β i.succ - 1) := by
  rw [letterCount_specialBraid (by omega), Fin.sum_univ_succ]

/-- **`ℓ` is not the trivial invariant**, which is what makes the refutation below say anything:
`y_1 ≠ 1` in `𝔹_k^+(𝕋_0)` for every `k ≥ 1`. At `k = 0` this is false
(`HJO.Braid.braidMonoid_zero`), which is why the weight needs `1 ≤ k`. -/
theorem braidGenY_ne_one {k : ℕ} (hk : 1 ≤ k) : braidGenY k 1 ≠ 1 := fun h => by
  have := letterCount_braidGenY hk (le_refl 1)
  rw [h, letterCount_one] at this
  exact absurd this (by omega)

/-- **The separator: `ℓ(RHS) - ℓ(LHS) = (A-1)(a+b-1) + (a+b-2)`.**

The right-hand side of `HJO.Braid.IsAppendSetup.specialBraid_eq_appendRhs` carries exactly
that many loop letters more than `B_{s,w,β}` does. Every term is accounted for: the left side weighs
one letter per move, `∑_i(β_i - 1) = (A-1) + ∑_i(α_i - 1)`; the right weighs `a+b` per round,
`a+b-2` for the trailing slope braid, and `ℓ(B_{s,v,α})` for the conjugated factor. -/
theorem letterCount_appendRhs_eq_add_separator {θ : ℚ} {k : ℕ} (hk : 1 ≤ k) {A a b : ℕ}
    (hab : 2 ≤ a + b) (w : Fin (k + 1) → ℚ) (β : Fin (k + 1) → ℕ) (hβ : β 0 = A) :
    letterCount (k + 1) (by omega) (appendRhs θ hk A a b (w ∘ Fin.succ) (β ∘ Fin.succ))
      = letterCount (k + 1) (by omega) (specialBraid θ w β)
          + ((A - 1) * (a + b - 1) + (a + b - 2)) := by
  rw [letterCount_specialBraid_succ, letterCount_appendRhs hk hab, hβ]
  simp only [Function.comp_apply]
  have key : (A - 1) * (a + b - 1) + (A - 1) = (A - 1) * (a + b) := by
    conv_rhs => rw [show a + b = (a + b - 1) + 1 from by omega]
    rw [Nat.mul_add, mul_one]
  omega

/-- **The naive append identity is false.**

If the displayed identity of `HJO.Braid.IsAppendSetup.specialBraid_eq_appendRhs` holds for the
appended data `(w, β)` with `β_{k+1} = A` — the hypothesis of the naive form — then `A = 1` and
`a + b = 2`, i.e. `a = b = 1` and the appended point makes no move at all. So the identity fails for
every other `(A, a, b)`, at every rank, for every tuple `w`, and with no hypothesis on the data
beyond `β_0 = A`: the two sides carry different numbers of loop letters, and `HJO.Braid.letterCount`
is a monoid homomorphism.

The separator is `ℓ(RHS) - ℓ(LHS) = (A-1)(a+b-1) + (a+b-2)`, visible in the proof. -/
theorem eq_one_and_add_eq_two_of_specialBraid_eq_appendRhs {θ : ℚ} {k : ℕ} (hk : 1 ≤ k)
    {A a b : ℕ} (hA : 1 ≤ A) (hab : 2 ≤ a + b) (w : Fin (k + 1) → ℚ) (β : Fin (k + 1) → ℕ)
    (hβ : β 0 = A)
    (h : specialBraid θ w β = appendRhs θ hk A a b (w ∘ Fin.succ) (β ∘ Fin.succ)) :
    A = 1 ∧ a + b = 2 := by
  have hcount := congrArg (letterCount (k + 1) (show 1 ≤ k + 1 by omega)) h
  rw [letterCount_specialBraid_succ, letterCount_appendRhs hk hab] at hcount
  simp only [Function.comp_apply] at hcount
  rw [hβ] at hcount
  -- `(A-1)*(a+b)` is the only nonlinear term; abstract it, keeping the one bound that matters
  have hge : (A - 1) * 2 ≤ (A - 1) * (a + b) := Nat.mul_le_mul_left _ hab
  obtain ⟨m, hm⟩ : ∃ m, (A - 1) * (a + b) = m := ⟨_, rfl⟩
  rw [hm] at hcount hge
  omega

/-- **The refutation as a disequality**: unless `A = 1` and `a = b = 1`, the identity of
`HJO.Braid.IsAppendSetup.specialBraid_eq_appendRhs` with `β_{k+1} = A` is false. -/
theorem specialBraid_ne_appendRhs {θ : ℚ} {k : ℕ} (hk : 1 ≤ k) {A a b : ℕ} (hA : 1 ≤ A)
    (hab : 2 ≤ a + b) (hne : ¬(A = 1 ∧ a + b = 2)) (w : Fin (k + 1) → ℚ) (β : Fin (k + 1) → ℕ)
    (hβ : β 0 = A) :
    specialBraid θ w β ≠ appendRhs θ hk A a b (w ∘ Fin.succ) (β ∘ Fin.succ) := fun h =>
  hne (eq_one_and_add_eq_two_of_specialBraid_eq_appendRhs hk hA hab w β hβ h)

/-- **The repair, and the only one the weight admits.** The two sides of
`HJO.Braid.IsAppendSetup.specialBraid_eq_appendRhs` carry the same number of loop letters precisely
when the appended part is `β_{k+1} = A(a+b) - 1`, not `A`.

That is Mellit's own count: his one-strand braid `(b_{a,b}y_1z_1)^{A-1}b_{a,b}` crosses the two
walls `Ab - 1` and `Aa - 1` times, so it performs `A(a+b) - 2` moves and its point meets the
antidiagonal `A(a+b) - 1` times, which is what `HJO.Braid.IsSpecialBraidData` calls the part. `A` is
the number of turns.

This is a necessary condition, not the identity itself: matching weights does not make the two
elements equal. It is what fixes the hypothesis so that the geometric proof can be attempted at all.
-/
theorem letterCount_specialBraid_eq_letterCount_appendRhs_iff {θ : ℚ} {k : ℕ} (hk : 1 ≤ k)
    {A a b : ℕ} (hA : 1 ≤ A) (hab : 2 ≤ a + b) (w : Fin (k + 1) → ℚ) (β : Fin (k + 1) → ℕ)
    (hβ : 1 ≤ β 0) :
    letterCount (k + 1) (by omega) (specialBraid θ w β)
        = letterCount (k + 1) (by omega) (appendRhs θ hk A a b (w ∘ Fin.succ) (β ∘ Fin.succ))
      ↔ β 0 = A * (a + b) - 1 := by
  rw [letterCount_specialBraid_succ, letterCount_appendRhs hk hab]
  simp only [Function.comp_apply]
  -- `A·(a+b) = (A-1)·(a+b) + (a+b)`, which is what turns the weight equation into the repair
  have hAc : A * (a + b) = (A - 1) * (a + b) + (a + b) := by
    cases A with
    | zero => omega
    | succ A' => rw [Nat.succ_sub_one, Nat.add_mul, one_mul]
  obtain ⟨m, hm⟩ : ∃ m, (A - 1) * (a + b) = m := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, a + b = c := ⟨_, rfl⟩
  rw [hm, hc] at hAc
  rw [hm, hc]
  omega

end HJO.Braid

end
